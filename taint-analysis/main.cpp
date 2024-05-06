#include <filesystem>

#include "llvm_utils.h"
#include "pch.h"
#include "taint_visitor.h"
#include "SVF-LLVM/LLVMUtil.h"
#include "SVF-LLVM/ICFGBuilder.h"
#include "SVFIR/SVFVariables.h"
#include "llvm/Support/CommandLine.h"
#include "spdlog/sinks/basic_file_sink.h"
#include "spdlog/sinks/daily_file_sink.h"
#include "SVF-LLVM/SVFIRBuilder.h"
#include "WPA/Andersen.h"
#include "k-alias-analysis/kaa.h"

#include "ver.h"

using namespace llvm;

cl::opt<std::string> ir_file(cl::Positional, cl::Required, cl::desc("IR file to run analysis on"));
cl::opt<bool> debug_mode("d", cl::desc("Enable debug logs"), cl::init(false));
cl::opt<std::string> entry_point("e", cl::desc("Entry point function"));
cl::opt<std::string> entry_point_file("f", cl::desc("Entry point function list"));
cl::opt<bool> enable_indirect_calls("i", cl::desc("Enable indirect calls"));
cl::opt<bool> dump_inst("x", cl::desc("Dump llvm instructions instead of running analysis"), cl::init(false));
cl::opt<bool> dump_svf("s", cl::desc("Dump svf instructions instead of running analysis"), cl::init(false));
cl::opt<bool> flow_sensitive_pta("fspta", cl::desc("Run flow sensitive pointer analysis"), cl::init(true));
cl::opt<int> max_depth("md", cl::desc("Maximum depth for k-alias-analysis"), cl::init(2));
cl::opt<bool> field_sensitive("fs", cl::desc("Field sensitivity for pointer analysis"), cl::init(false));

std::set<std::string> read_file(std::string filename)
{
    std::ifstream is{filename};
    if (!is.is_open())
    {
        SPDLOG_ERROR("Failed to open file");
        return {};
    }

    std::set<std::string> result{};
    std::string f;
    while (std::getline(is, f))
    {
        if (!f.size())
            continue;
        result.insert(f);
    }
    std::cout << "read: " << filename << "\n";
    for (auto &f : result)
    {
        std::cout << "  " << f << "\n";
    }
    return result;
}

void run_on_sorted_bb(SVF::ICFG *icfg, const SVF::SVFFunction *func, ktaint::TaintVisitor &tv)
{
    auto llvm_value = SVF::LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(func);
    auto llvm_func = dyn_cast<llvm::Function>(llvm_value);
    if (!llvm_func)
    {
        SPDLOG_ERROR("Failed to get the function for {}", func->getName());
    }
    auto bbs = kutils::get_traversal_order(llvm_func);

    SVF::ICFGNode *prev = nullptr;
    for (auto bb_list : bbs)
    {
        SPDLOG_TRACE("SCC begin");
        for (auto bb : bb_list)
        {
            SPDLOG_TRACE("BB begin");
            for (auto &inst : bb->getInstList())
            {
                if (inst.isDebugOrPseudoInst())
                    continue;

                auto svf_value = SVF::LLVMModuleSet::getLLVMModuleSet()->getSVFValue(&inst);
                if (!svf_value)
                {
                    SPDLOG_TRACE("Could not find SVF value for: {}", kutils::value_as_string(&inst));
                    continue;
                }
                auto svf_inst = dyn_cast<SVF::SVFInstruction>(svf_value);
                if (!svf_inst)
                {
                    SPDLOG_TRACE("Could not find SVF inst for: {}", kutils::value_as_string(&inst));
                    continue;
                }
                auto curr = icfg->getICFGNode(svf_inst);
                if (!curr)
                {
                    SPDLOG_TRACE("Could not find ICFG node for: {}", kutils::value_as_string(&inst));
                    continue;
                }

                if (curr == prev)
                {
                    SPDLOG_TRACE("Got the same node as prev for {}", kutils::value_as_string(&inst));
                }
                else
                {
                    if (dump_inst)
                    {
                        if (dump_svf)
                        {
                            SPDLOG_DEBUG("{}", curr->toString());
                        }
                        else
                        {
                            SPDLOG_DEBUG("{} @ {}", kutils::value_as_string(&inst),
                                         kutils::debug_loc_as_string(&(inst.getDebugLoc())));
                        }
                    }
                    else
                    {
                        tv.visit(curr);
                    }
                }

                prev = curr;
            }
        }
    }
}

void analyze(const std::string &ir_file, const std::set<std::string> &entry_points)
{
    auto svf_module = SVF::LLVMModuleSet::getLLVMModuleSet()->buildSVFModule({ir_file});
    SVF::SVFIRBuilder builder(svf_module);
    SPDLOG_TRACE("Building SVFIR");
    auto pag = builder.build();
    auto icfg = pag->getICFG();

    // auto andersen_pta = [pag]() -> SVF::PointerAnalysis *
    // {
    //     if (flow_sensitive_pta)
    //     {
    //         SPDLOG_INFO("Using flow sensitive pointer analysis");
    //         return new SVF::FlowSensitive(pag);
    //     }
    //     else
    //     {
    //         SPDLOG_INFO("Using andersen wavediff pointer analysis");
    //         return new SVF::AndersenWaveDiff(pag, SVF::PointerAnalysis::PTATY::AndersenWaveDiff_WPA, false);
    //     }
    // }();

    // andersen_pta->disablePrintStat();
    // SPDLOG_TRACE("Running points to analysis");
    // if (!dump_inst)
    // {
    //     andersen_pta->analyze();

    //     auto callgraph = andersen_pta->getPTACallGraph();
    //     SPDLOG_TRACE("Updating callgraph");
    //     builder.updateCallGraph(callgraph);
    //     if (enable_indirect_calls)
    //     {
    //         icfg->updateCallGraph(callgraph);
    //     }
    // }

    int total_results = 0;
    for (auto entry_point : entry_points)
    {
        SPDLOG_INFO("Analyzing the entry point: '{}'", entry_point);
        // auto pa =
        auto entry_func = svf_module->getSVFFunction(entry_point);
        if (!entry_func)
        {
            SPDLOG_ERROR("Failed to get the entry point function");
            return;
        }

        auto entry_node = icfg->getFunEntryICFGNode(entry_func);
        if (!entry_node)
        {
            SPDLOG_ERROR("Failed to get the function entry node");
            return;
        }

        auto params = entry_node->getFormalParms();

        std::unordered_set<SVF::NodeID> tainted_nodes;

        kaa::AliasAnalysis kaa{pag, max_depth, field_sensitive};
        ktaint::State state{kaa, *icfg, *pag};
        for (auto i = 0; i < params.size(); i++)
        {
            auto node = params[i]->getId();
            state.taint_state.mark_as_tainted(node, ktaint::TaintInfo(i, node, "<root>"));
        }

        ktaint::TaintVisitor tv{
            state, entry_func, [icfg](const SVF::SVFFunction *f, ktaint::TaintVisitor &tv)
            {
                run_on_sorted_bb(icfg, f, tv);
            }};

        run_on_sorted_bb(icfg, entry_func, tv);

        auto result = tv.get_result();
        total_results += result.size();
        SPDLOG_INFO("Result size: {}", result.size());
        for (auto &r : result)
        {
            SPDLOG_INFO("{}", r.to_string(pag));
        }
    }

    SPDLOG_INFO("Total results: {}", total_results);

    // SVF::SCCDetection<SVF::ICFG> d{*icfg};
}

int main(int argc, char **argv)
{
    SPDLOG_INFO("Build time: {}", BUILDTIME);

    cl::ParseCommandLineOptions(argc, argv);

    spdlog::set_level(spdlog::level::trace);
    if (!debug_mode)
    {
        // We don't want global filter
        for (auto &s : spdlog::default_logger()->sinks())
        {
            s->set_level(spdlog::level::debug);
        }
    }
    auto log_file = fmt::format("/tmp/taint-logs/{:%d-%m-%Y-%H-%M-%S}.log", std::chrono::system_clock::now());
    auto file_sink2 = std::make_shared<spdlog::sinks::basic_file_sink_mt>(log_file);
    spdlog::default_logger()->sinks().push_back(file_sink2);
    file_sink2->set_level(spdlog::level::trace);

    std::set<std::string> functions;
    if (!entry_point.empty())
    {
        functions.insert(entry_point);
    }
    else
    {
        functions = read_file(entry_point_file);
    }

    SPDLOG_INFO("Configuration options:");
    SPDLOG_INFO("\tmax_depth:       {}", max_depth);
    SPDLOG_INFO("\tfield sensitive: {}", field_sensitive);
    analyze(ir_file.getValue(), functions);
    spdlog::default_logger()->flush();
    SPDLOG_INFO("Logs saved at: {}", log_file);
    auto dst = "/tmp/a.log";
    if (std::filesystem::copy_file(log_file, dst, std::filesystem::copy_options::overwrite_existing))
    {
        SPDLOG_TRACE("Log saved at: {}", dst);
    }
    return 0;
}
