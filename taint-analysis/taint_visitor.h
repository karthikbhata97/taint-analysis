//
// Created by karth on 1/19/2024.
//

#ifndef TAINT_VISITOR_H
#define TAINT_VISITOR_H

#include "pch.h"
#include <llvm/IR/Value.h>
#include <llvm/IR/InstVisitor.h>
#include <llvm/Analysis/AliasSetTracker.h>
#include <unordered_set>
#include <Graphs/ICFGNode.h>
#include <SVF-LLVM/BasicTypes.h>
#include <SVFIR/SVFStatements.h>
#include <WPA/WPAPass.h>
#include "k-alias-analysis/kaa.h"

#include <optional>

namespace ktaint
{
    struct TaintSource
    {
        SVF::NodeID node;
        std::string stmt;
    };

    class TaintInfo
    {
        int source;
        std::vector<TaintSource> source_inst;

    public:
        TaintInfo(int tsource, SVF::NodeID inst, std::string stmt) : source(tsource)
        {
            source_inst.push_back({inst, stmt});
        }

        void add(SVF::NodeID inst, std::string stmt)
        {
            source_inst.push_back({inst, stmt});
        }

        std::optional<SVF::NodeID> last_source() const;

        std::string to_string(SVF::SVFIR *pag) const;
    };

    class TaintState
    {
        std::unordered_map<SVF::NodeID, TaintInfo> m_tainted_values;
        std::unordered_map<SVF::NodeID, TaintInfo> m_tainted_pointers;

    public:
        std::optional<TaintInfo> is_tainted(SVF::NodeID value) const;

        std::optional<TaintInfo> is_points_to_tainted(SVF::NodeID value) const;

        void mark_as_tainted(SVF::NodeID value, TaintInfo info);

        void mark_as_pts_tainted(SVF::NodeID value, TaintInfo info);

        void remove_taint(SVF::NodeID node);

        void remove_pts_taint(SVF::NodeID node);
    };

    struct State
    {
        TaintState taint_state;
        // SVF::PointerAnalysis& m_pointer_analysis;
        kaa::AliasAnalysis &m_alias_analysis;
        SVF::ICFG &m_icfg;
        SVF::SVFIR &m_svfir;

        explicit State(kaa::AliasAnalysis &alias_analysis, SVF::ICFG &icfg, SVF::SVFIR &svfir) : m_alias_analysis(alias_analysis), m_icfg(icfg), m_svfir(svfir)
        {
        }
    };

    struct CallPoint
    {
        const SVF::SVFFunction *m_func;
        std::string m_debug_info;
        std::vector<SVF::NodeID> m_tainted_args;

        CallPoint(const SVF::SVFFunction *func, std::string debug_info,
                  std::vector<SVF::NodeID> tainted_args) : m_func(func), m_debug_info(debug_info),
                                                           m_tainted_args(tainted_args)
        {
        }

        std::string to_string() const;

        std::string name() const;
    };

    class CallStack
    {
        std::vector<CallPoint> m_call_stack{};

    public:
        void push(CallPoint cp);

        CallPoint &back();

        std::string to_string() const;

        std::string to_string_names() const;

        std::size_t size() const;
    };

    class TaintResult
    {
    public:
        enum class Type
        {
            Deref,
            InsecureCallArg
        };

    private:
        Type m_type;
        TaintInfo m_info;
        std::string m_debug_loc;
        CallStack m_call_stack;
        const SVF::SVFInstruction *m_inst;

    public:
        TaintResult(Type type, TaintInfo info, std::string debug_loc, CallStack call_stack,
                    const SVF::SVFInstruction *inst) : m_info(info),
                                                       m_type(type), m_debug_loc(debug_loc), m_call_stack(call_stack),
                                                       m_inst(inst)
        {
        }

        std::string to_string(SVF::SVFIR *pag) const;
    };

    struct RetInfo
    {
        enum class TaintType
        {
            None,
            Tainted,
            PtsTainted
        };

        TaintType taint_type;
        std::optional<TaintInfo> taint_info;
        SVF::NodeID inst;

        explicit RetInfo(TaintType ttaint_type, std::optional<TaintInfo> ttaint_info,
                         SVF::NodeID tinst) : taint_info(ttaint_info),
                                              taint_type(ttaint_type), inst(tinst)
        {
        }

        RetInfo() : taint_type(TaintType::None)
        {
        }
    };

    class TaintVisitor : public llvm::InstVisitor<TaintVisitor>
    {
        int m_instructions_count{};
        State m_state;
        std::vector<TaintResult> m_result{};
        RetInfo m_ret_info{};

        using OnCallCallback = std::function<void(const SVF::SVFFunction *, TaintVisitor &)>;
        OnCallCallback m_on_call_callback;

        CallStack m_call_stack{};
        std::unordered_set<llvm::Instruction *> m_visited{};

    public:
        explicit TaintVisitor(State &state, const SVF::SVFFunction *entry,
                              OnCallCallback on_call_callback) : m_state(state),
                                                                 m_on_call_callback(on_call_callback)
        {
            m_call_stack.push({entry, "Unknown", {}});
        }

        void analyze(SVF::ICFGNode *node);

        // void visitMemcpyCallInst(llvm::CallInst& call);

        void mark_as_tainted(SVF::NodeID dst, SVF::NodeID src, std::string stmt, TaintInfo value);

        void visitLoadStmt(const SVF::LoadStmt *stmt);

        void visitStoreStmt(const SVF::StoreStmt *stmt);

        void visitCopyStmt(const SVF::CopyStmt *stmt);

        void visitBinaryOpStmt(const SVF::BinaryOPStmt *stmt);

        void visitGepStmt(const SVF::GepStmt *stmt);

        void visitRetStmt(const SVF::RetPE *stmt);

        void visitPhiStmt(const SVF::PhiStmt *stmt);

        void visitStmt(const SVF::SVFStmt *stmt);

        void visitIntraBlock(SVF::IntraICFGNode *node);

        void visitCallStmt(const SVF::CallPE *node);

        void visitFunExitBlock(SVF::FunExitICFGNode *node);

        void visitMemCpyCallBlock(SVF::CallICFGNode *call_node);

        void remove_taint(SVF::NodeID node);

        void remove_pts_taint(SVF::NodeID node);

        void visitVmCheckAccessRights(SVF::CallICFGNode *call_node);

        void visitMobjGetVa(SVF::CallICFGNode *call_node);

        void visitPhysToVirt(SVF::CallICFGNode *call_node);

        void visitReturningTaintedPtr(SVF::CallICFGNode *call_node);

        void visitTestAlias(SVF::CallICFGNode *call_node);

        void visitPrintPts(SVF::CallICFGNode *call_node);

        void visitCallBlock(SVF::CallICFGNode *node);

        void visit(SVF::ICFGNode *node);

        std::vector<TaintResult> get_result();

        State &get_state();

        RetInfo get_ret_info() const;

    private:
        void save_tainted_sink(TaintResult::Type type, TaintInfo info, const SVF::SVFInstruction *site);

        // TaintVisitor fork_for_call(llvm::CallInst& call);

        // void merge_on_call(TaintVisitor& tv);

        static bool is_memcpy(llvm::Function *func);

        TaintVisitor fork_for_call(const SVF::SVFFunction *f, const SVF::CallICFGNode *call_node);

        void merge_on_call(TaintVisitor &tv);
    };
}

#endif // TAINT_VISITOR_H
