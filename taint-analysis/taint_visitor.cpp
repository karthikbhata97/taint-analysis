//
// Created by karth on 1/19/2024.
//

#include "taint_visitor.h"

#include <queue>

#include "llvm_utils.h"
#include <sstream>
#include <SVF-LLVM/LLVMModule.h>
#include <SVFIR/SVFStatements.h>

namespace ktaint
{
    std::optional<SVF::NodeID> TaintInfo::last_source() const
    {
        auto size = source_inst.size();
        if (size < 2)
        {
            return std::nullopt;
        }
        return source_inst[size - 2].node;
    }

    std::string TaintInfo::to_string(SVF::SVFIR *pag) const
    {
        std::stringstream ss;
        ss << "Source Argument: " + std::to_string(source) << "\n";
        for (auto val : source_inst)
        {
            // llvm::Instruction* inst = llvm::dyn_cast<llvm::Instruction>(val);
            SVF::SVFVar *node_ptr{};
            if (pag)
            {
                node_ptr = pag->getGNode(val.node);
            }
            std::string debug_loc{};
            if (!node_ptr)
            {
                debug_loc = fmt::format("From {} @ {}", val.node, val.stmt);
            }
            else
            {
                debug_loc = fmt::format("From {} @ {}", node_ptr->toString(), val.stmt);
            }
            ss << " => " << val.node << " @ " << debug_loc << "\n";
        }
        return ss.str();
    }

    std::optional<TaintInfo> TaintState::is_tainted(SVF::NodeID value) const
    {
        if (m_tainted_values.contains(value))
        {
            // SPDLOG_TRACE("IsTainted({}) => Yes", value);
            return m_tainted_values.at(value);
        }

        // SPDLOG_TRACE("IsTainted({}) => No", value);
        return std::nullopt;
    }

    std::optional<TaintInfo> TaintState::is_points_to_tainted(SVF::NodeID value) const
    {
        if (m_tainted_pointers.contains(value))
        {
            return m_tainted_pointers.at(value);
        }

        return std::nullopt;
    }

    void TaintState::mark_as_tainted(SVF::NodeID value, TaintInfo info)
    {
        m_tainted_values.insert({value, info});
    }

    void TaintState::mark_as_pts_tainted(SVF::NodeID value, TaintInfo info)
    {
        m_tainted_pointers.insert({value, info});
    }

    void TaintState::remove_taint(SVF::NodeID node)
    {
        m_tainted_values.erase(node);
    }

    void TaintState::remove_pts_taint(SVF::NodeID node)
    {
        m_tainted_pointers.erase(node);
    }

    std::string CallPoint::to_string() const
    {
        return fmt::format("{} @ {} `[{}]`", m_func->getName(), m_debug_info, fmt::join(m_tainted_args, ", "));
    }

    std::string CallPoint::name() const
    {
        return m_func->getName();
    }

    std::string TaintResult::to_string(SVF::SVFIR *pag) const
    {
        std::stringstream ss;
        switch (m_type)
        {
        case Type::Deref:
            ss << "[Deref]";
            break;
        case Type::InsecureCallArg:
            ss << "[InsecureCallArg]";
            break;
        }

        ss << "\n----callstack_begin----\n";
        ss << " " << m_info.to_string(pag) << "\n";
        ss << fmt::format("Callstack (size: {}): {}\n", m_call_stack.size(), m_call_stack.to_string_names());
        ss << m_call_stack.to_string();
        ss << "\n\nON: " << m_inst->toString() << "\n";
        ss << "\n----callstack_end----\n";
        ss << " -> " << m_debug_loc << "\n";
        return ss.str();
    }

    void CallStack::push(CallPoint cp)
    {
        m_call_stack.push_back(cp);
    }

    CallPoint &CallStack::back()
    {
        return m_call_stack.back();
    }

    std::string CallStack::to_string() const
    {
        std::string result{};
        int off = 0;
        std::for_each(m_call_stack.begin(), m_call_stack.end(), [&off, &result](const CallPoint &cp)
                      {
            result += fmt::format("\ns#{}-> {}", off, cp.to_string());
            off++; });
        return result;
    }

    std::string CallStack::to_string_names() const
    {
        std::string result{"BEGIN"};
        std::for_each(m_call_stack.begin(), m_call_stack.end(), [&result](const CallPoint &cp)
                      { result = fmt::format("{} -> {}", result, cp.m_func->getName()); });
        return result;
    }

    std::size_t CallStack::size() const
    {
        return m_call_stack.size();
    }

    void TaintVisitor::analyze(SVF::ICFGNode *node)
    {
        std::unordered_map<SVF::ICFGNode *, int> reach_count{};

        // DFS across the branches
        std::stack<SVF::ICFGNode *> stack;
        stack.push(node);

        // We want to perform a flow + context sensitive analysis (no path sensitivity, this can be explored later).
        // This means, when we arrive at a node, if there are more inward edges, and if we have not reached here before,
        // many times, we just don't continue. This means, when we reach here the last time, we have made sure all the
        // flows, coming here are traversed.
        while (!stack.empty())
        {
            // Get the next node to traverse
            auto node = stack.top();
            stack.pop();

            reach_count[node] += 1;

            // If we have multiple incoming edges and we have not traversed all of those paths, then, drop this flow.
            if (node->getInEdges().size() != reach_count[node])
            {
                // Drop this node, get the next node from the queue

                // This should not happen!
                if (stack.empty())
                {
                    SPDLOG_ERROR("No paths to traverse, before proceeding! Possible loop found");
                    // Let's continue with the same node to prevent the deadlock situation.
                    // Ok, this does not work, because stack.empty only happens when there are no more paths to explore
                    // If there is another alternate path yet to explore, we will end up skipping this and continuing
                    // to that.
                    // SVF::SCCDetection<>
                    // What do we want?
                    // => Get the topological ordered SCCs at a function level
                    return;
                }

                node = stack.top();
                stack.pop();
                continue;
            }

            // Meat
            visit(node);

            // Push all the successors
            for (auto edge : node->getOutEdges())
            {
                stack.push(edge->getDstNode());
            }
        }
    }

    void TaintVisitor::mark_as_tainted(SVF::NodeID dst, SVF::NodeID src, std::string stmt, TaintInfo value)
    {
        value.add(dst, stmt);
        SPDLOG_TRACE("taint_copy ({} <= {})", dst, src);
        m_state.taint_state.mark_as_tainted(dst, value);
    }

    // void TaintVisitor::visitMemcpyCallInst(llvm::CallInst& call) {
    //     auto src = call.getArgOperand(1);
    //     auto dst = call.getArgOperand(0);
    //     SPDLOG_TRACE("Memcpy ({} <= {})", kutils::value_as_string(dst), kutils::value_as_string(src));
    //
    //     // memcpy essentially does load(srd) => store(dst). Hence check if there is a tainted deref
    //
    //     // Check if src is tainted
    //     if (auto info = m_state.taint_state.is_tainted(src); info.has_value()) {
    //         SPDLOG_TRACE("Memcpy src is tainted ({})", kutils::value_as_string(src));
    //         save_tainted_sink(TaintResult::Type::Deref, info.value(), call);
    //     }
    //
    //     // Check if dst is tainted
    //     if (auto info = m_state.taint_state.is_tainted(dst); info.has_value()) {
    //         SPDLOG_TRACE("Memcpy dst is tainted ({})", kutils::value_as_string(dst));
    //         save_tainted_sink(TaintResult::Type::Deref, info.value(), call);
    //     }
    //
    //     copy_taint_info(dst, src);
    // }

    void TaintVisitor::visitLoadStmt(const SVF::LoadStmt *stmt)
    {
        auto src = stmt->getRHSVarID();
        auto dst = stmt->getLHSVarID();

        if (auto info = m_state.taint_state.is_tainted(src); info.has_value())
        {
            SPDLOG_TRACE("Load source is tainted. Taint being dereferenced!");
            auto inst = stmt->getInst();

            save_tainted_sink(TaintResult::Type::Deref, info.value(), inst);

            // Note: Ideally we should propagate this taint further. But we see a lot of results if there is a bug
            // or a false postitive in the taint! Ignore for now.
            // mark_as_tainted(dst, src, info.value());
        }
        else
        {
            if (auto info = m_state.taint_state.is_points_to_tainted(src); info)
            {
                SPDLOG_TRACE("Loading tainted data");
                mark_as_tainted(dst, src, stmt->toString(), info.value());
            }

            // for (auto node : m_state.m_pointer_analysis.getPts(src))
            // {
            //     if (auto info = m_state.taint_state.is_tainted(node); info.has_value())
            //     {
            //         SPDLOG_TRACE("Loading tainted data");
            //         mark_as_tainted(dst, node, stmt->toString(), info.value());
            //     }
            // }
        }
    }

    void TaintVisitor::visitStoreStmt(const SVF::StoreStmt *stmt)
    {
        auto src = stmt->getRHSVarID();
        auto dst = stmt->getLHSVarID();

        if (auto info = m_state.taint_state.is_tainted(dst); info.has_value())
        {
            SPDLOG_TRACE("Load source is tainted. Taint being dereferenced!");
            auto inst = stmt->getInst();

            save_tainted_sink(TaintResult::Type::Deref, info.value(), inst);
        }
        else if (auto info = m_state.taint_state.is_tainted(src); info.has_value())
        {
            // src is tainted. Mark all the pts of dst as tainted
            SPDLOG_TRACE("Storing tainted data");
            // for (auto node : m_state.m_pointer_analysis.getPts(dst))
            // {
            //     mark_as_tainted(node, src, stmt->toString(), info.value());
            // }
            for (auto node : m_state.m_alias_analysis.get_aliases(dst))
            {
                m_state.taint_state.mark_as_pts_tainted(node, info.value());
            }
        }
    }

    void TaintVisitor::visitCopyStmt(const SVF::CopyStmt *stmt)
    {
        auto src = stmt->getRHSVarID();
        auto dst = stmt->getLHSVarID();
        if (auto info = m_state.taint_state.is_tainted(src); info.has_value())
        {
            SPDLOG_TRACE("Copy of taint");
            mark_as_tainted(dst, src, stmt->toString(), info.value());
        }
    }

    void TaintVisitor::visitBinaryOpStmt(const SVF::BinaryOPStmt *stmt)
    {
        for (auto op : stmt->getOpndVars())
        {
            if (auto info = m_state.taint_state.is_tainted(op->getId()); info.has_value())
            {
                SPDLOG_TRACE("BinaryOp of taint");
                mark_as_tainted(stmt->getResID(), op->getId(), stmt->toString(), info.value());
                return;
            }
        }
    }

    void TaintVisitor::visitGepStmt(const SVF::GepStmt *stmt)
    {
        auto dst = stmt->getLHSVarID();
        auto src = stmt->getRHSVarID();
        if (auto info = m_state.taint_state.is_tainted(src); info.has_value())
        {
            SPDLOG_TRACE("Gep tainted base");
            mark_as_tainted(dst, src, stmt->toString(), info.value());
            return;
        }

        for (auto item : stmt->getOffsetVarAndGepTypePairVec())
        {
            if (auto info = m_state.taint_state.is_tainted(item.first->getId()); info.has_value())
            {
                SPDLOG_TRACE("Gep tainted offset");
                mark_as_tainted(dst, item.first->getId(), stmt->toString(), info.value());
                return;
            }
        }
    }

    void TaintVisitor::visitRetStmt(const SVF::RetPE *stmt)
    {
        // SPDLOG_INFO("Reached ret stmt");
        assert(false);
    }

    void TaintVisitor::visitPhiStmt(const SVF::PhiStmt *stmt)
    {
        // SPDLOG_INFO("Visiting PhiStmt: {}", stmt->toString());
        auto dst = stmt->getRes()->getId();
        for (auto op : stmt->getOpndVars())
        {
            if (auto info = m_state.taint_state.is_tainted(op->getId()); info.has_value())
            {
                mark_as_tainted(dst, op->getId(), stmt->toString(), info.value());

                // If this is a function return, forward taint
                if (stmt->isFunctionRetPhi())
                {
                    m_ret_info = RetInfo{RetInfo::TaintType::Tainted, info.value(), op->getId()};
                }
            }
            else if (auto info = m_state.taint_state.is_points_to_tainted(op->getId()); info.has_value())
            {
                m_state.taint_state.mark_as_pts_tainted(dst, info.value());
            }
        }
    }

    void TaintVisitor::visitStmt(const SVF::SVFStmt *stmt)
    {
        // SPDLOG_TRACE("Stmt: {}", stmt->toString());
        auto kind = (SVF::SVFStmt::PEDGEK)stmt->getEdgeKind();
        switch (kind)
        {
        case SVF::SVFStmt::Load:
            SPDLOG_TRACE("Visit load statment");
            visitLoadStmt(SVF::SVFUtil::dyn_cast<SVF::LoadStmt>(stmt));
            break;
        case SVF::SVFStmt::Store:
            SPDLOG_TRACE("Visit store statment");
            visitStoreStmt(SVF::SVFUtil::dyn_cast<SVF::StoreStmt>(stmt));
            break;
        case SVF::SVFStmt::Copy:
            visitCopyStmt(SVF::SVFUtil::dyn_cast<SVF::CopyStmt>(stmt));
            break;
        case SVF::SVFStmt::BinaryOp:
            visitBinaryOpStmt(SVF::SVFUtil::dyn_cast<SVF::BinaryOPStmt>(stmt));
            break;
        case SVF::SVFStmt::Gep:
            visitGepStmt(SVF::SVFUtil::dyn_cast<SVF::GepStmt>(stmt));
            break;
        case SVF::SVFStmt::Call:
            // visitCallStmt(SVF::SVFUtil::dyn_cast<SVF::CallPE>(stmt));
            break;
        case SVF::SVFStmt::Ret:
            visitRetStmt(SVF::SVFUtil::dyn_cast<SVF::RetPE>(stmt));
            break;
        case SVF::SVFStmt::Phi:
            visitPhiStmt(SVF::SVFUtil::dyn_cast<SVF::PhiStmt>(stmt));
            break;
        default:
            SPDLOG_TRACE("Unhandled statment kind: {}", kind);
        }
    }

    void TaintVisitor::visitIntraBlock(SVF::IntraICFGNode *node)
    {
        auto stmts = node->getSVFStmts();
        if (stmts.empty())
        {
            if (node->getInst()->isRetInst())
            {
                // Propagate on return
                auto out_edges = node->getOutEdges();
                assert(out_edges.size() == 1);
                for (auto edge : out_edges)
                {
                    auto fun_exit_block = SVF::SVFUtil::dyn_cast<SVF::FunExitICFGNode>(edge->getDstNode());
                    if (fun_exit_block)
                    {
                        visitFunExitBlock(fun_exit_block);
                    }
                    else
                    {
                        SPDLOG_INFO("Could not get the function exit node");
                    }
                }
            }
        }
        else
        {
            for (auto stmt : stmts)
            {
                visitStmt(stmt);
            }
        }
    }

    void TaintVisitor::visitCallBlock(SVF::CallICFGNode *call_node)
    {
        auto ret_node = call_node->getRetICFGNode();
        static std::vector<std::string> skip_functions{
            "assert", "trace", "mutex_lock", "panic", "malloc", "free", "realloc", "calloc",
            "mutex_lock", "mutex_unlock", "condvar_wait", "condvar_signal"};

        static std::vector<std::string> sink_functions{
            "malloc", "free", "realloc", "calloc"};

        // SPDLOG_TRACE("{} out edges at callsite: {}", call_node->getOutEdges().size(), call_node->toString());
        for (auto edge : call_node->getOutEdges())
        {
            auto fun_entry_block = edge->getDstNode();

            bool is_memcpy_call = false;
            bool is_overflow_call = false;

            auto llvm_value = SVF::LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(call_node->getCallSite());
            if (llvm_value)
            {
                auto llvm_inst = llvm::dyn_cast<llvm::CallInst>(llvm_value);
                if (llvm_inst)
                {
                    auto target = llvm_inst->getCalledFunction();
                    if (target)
                    {
                        is_memcpy_call = is_memcpy(target);
                        auto fname = target->getName().str();
                        is_overflow_call = fname.find("with.overflow") != fname.npos;
                    }
                }
            }

            if (!SVF::SVFUtil::isa<SVF::FunEntryICFGNode>(fun_entry_block))
            {
                SPDLOG_TRACE("Not a function entry node. Skipping!");

                if (is_memcpy_call)
                {
                    SPDLOG_TRACE("Memcpy invoked");
                    visitMemCpyCallBlock(call_node);
                }
                if (is_overflow_call)
                {
                    // Here, since we are not handling the external call, the taint does not propagate, which is also
                    // what we want.
                    SPDLOG_TRACE("Overflow call invoked");
                }

                continue;
            }

            auto callee = fun_entry_block->getFun();
            auto fname = callee->getName();

            // Check if the callee is one of the sinks, and if it consumes a tainted argument
            // malloc(size) -> size is tainted?
            if (std::find(sink_functions.begin(), sink_functions.end(), fname) != sink_functions.end())
            {
                auto params = call_node->getActualParms();
                for (auto p : params)
                {
                    if (auto info = m_state.taint_state.is_tainted(p->getId()); info.has_value())
                    {
                        auto stmt = call_node->getSVFStmts().front();
                        auto inst = stmt->getInst();
                        save_tainted_sink(TaintResult::Type::InsecureCallArg, info.value(), inst);
                    }
                }
            }

            for (auto skip : skip_functions)
            {
                if (fname.find(skip) != fname.npos)
                {
                    SPDLOG_TRACE("Skipping {}", fname);
                    return;
                }
            }

            if (callee->isDeclaration())
            {
                SPDLOG_TRACE("Ignoring declaration: {}", callee->getName());
                return;
            }

            if (fname == "vm_check_access_rights")
            {
                visitVmCheckAccessRights(call_node);
                continue;
            }
            else if (fname == "mobj_get_va")
            {
                visitMobjGetVa(call_node);
                continue;
            }
            else if (fname == "phys_to_virt")
            {
                visitPhysToVirt(call_node);
                continue;
            }

            auto tv = fork_for_call(callee, call_node);
            SPDLOG_INFO("Entering: {}", tv.m_call_stack.to_string_names());
            m_on_call_callback(callee, tv);
            merge_on_call(tv);
            SPDLOG_INFO("Exiting: {}", tv.m_call_stack.to_string_names());

            auto ret = tv.get_ret_info();
            switch (ret.taint_type)
            {
            case RetInfo::TaintType::Tainted:
                SPDLOG_INFO("Return is tainted");
                for (auto stmt : ret_node->getSVFStmts())
                {
                    auto ret_stmt = SVF::SVFUtil::dyn_cast<SVF::RetPE>(stmt);
                    if (ret_stmt)
                    {
                        SPDLOG_TRACE("Marking return value as tainted");
                        mark_as_tainted(ret_stmt->getLHSVarID(), ret.inst, ret_stmt->toString(),
                                        ret.taint_info.value());
                    }
                }
                break;
            default:
                break;
            }
        }
    }

    void TaintVisitor::visitFunExitBlock(SVF::FunExitICFGNode *node)
    {
        for (auto stmt : node->getSVFStmts())
        {
            visitStmt(stmt);
        }
    }

    void TaintVisitor::visitMemCpyCallBlock(SVF::CallICFGNode *call_node)
    {
        auto params = call_node->getActualParms();
        if (params.size() != 4)
        {
            SPDLOG_ERROR("Invalid arguments at memcpy!");
            return;
        }
        auto src = params[1]->getId();
        auto dst = params[0]->getId();

        if (auto info = m_state.taint_state.is_points_to_tainted(src); info)
        {
            m_state.taint_state.mark_as_pts_tainted(dst, info.value());
        }
        // for (auto src_node : m_state.m_pointer_analysis.getPts(src))
        // {
        //     if (auto info = m_state.taint_state.is_tainted(src_node); info.has_value())
        //     {
        //         for (auto dst_node : m_state.m_pointer_analysis.getPts(dst))
        //         {
        //             mark_as_tainted(dst_node, src_node, call_node->toString(), info.value());
        //             return;
        //         }
        //     }
        // }
    }

    void TaintVisitor::remove_taint(SVF::NodeID node)
    {
        SPDLOG_TRACE("Removing taint for: {}", node);
        m_state.taint_state.remove_taint(node);
    }

    void TaintVisitor::remove_pts_taint(SVF::NodeID node)
    {
        SPDLOG_TRACE("Removing pts taint for: {}", node);
        m_state.taint_state.remove_pts_taint(node);
    }

    void TaintVisitor::visitVmCheckAccessRights(SVF::CallICFGNode *call_node)
    {
        auto params = call_node->getActualParms();
        constexpr auto ptr_param_num = 2;
        constexpr auto size_param_num = 3;
        if (params.size() <= ptr_param_num || params.size() <= size_param_num)
        {
            SPDLOG_ERROR("Insufficient params for vm_check_access_rights!");
            return;
        }

        // If pointer is tainted, mark it as not tainted anymore
        // If it points to tainted, mark all the aliases as not pointing to tainted anymore
        // TODO: Issue: *a = tainted; if(check(tainted)) return; malloc(*a)
        // Here check fuction validates tainted is fine (thus we remove taint from tainted). But we do not know how to
        // mark a as not pointing to tainted anymore. (We can do a use of tainted and in all stores, we can mark the
        // aliases as not pointing to taint anymore)
        auto ptr_param = params[ptr_param_num]->getId();
        if (auto info = m_state.taint_state.is_tainted(ptr_param); info.has_value())
        {
            remove_taint(ptr_param);
        }

        if (auto info = m_state.taint_state.is_points_to_tainted(ptr_param); info.has_value())
        {
            for (auto a : m_state.m_alias_analysis.get_aliases(ptr_param))
            {
                remove_pts_taint(a);
            }
        }

        auto size_param = params[size_param_num]->getId();
        if (auto info = m_state.taint_state.is_tainted(size_param); info.has_value())
        {
            remove_taint(size_param);
        }

        if (auto info = m_state.taint_state.is_points_to_tainted(size_param); info.has_value())
        {
            for (auto a : m_state.m_alias_analysis.get_aliases(size_param))
            {
                remove_pts_taint(a);
            }
        }
    }

    void TaintVisitor::visitMobjGetVa(SVF::CallICFGNode *call_node)
    {
        visitReturningTaintedPtr(call_node);
    }

    void TaintVisitor::visitPhysToVirt(SVF::CallICFGNode *call_node)
    {
        visitReturningTaintedPtr(call_node);
    }

    void TaintVisitor::visitReturningTaintedPtr(SVF::CallICFGNode *call_node)
    {
        // Mark the return value as tainted
        auto ret_node = call_node->getRetICFGNode();
        if (!ret_node)
            return;

        for (auto stmt : ret_node->getSVFStmts())
        {
            auto ret_stmt = SVF::SVFUtil::dyn_cast<SVF::RetPE>(stmt);
            if (ret_stmt)
            {
                SPDLOG_TRACE("Marking return value as tainted");
                m_state.taint_state.mark_as_pts_tainted(ret_stmt->getLHSVarID(), TaintInfo{-1, ret_node->getActualRet()->getId(), ret_stmt->toString()});
            }
        }
    }

    void TaintVisitor::visitTestAlias(SVF::CallICFGNode *call_node)
    {
        auto ptr = call_node->getActualParms()[0]->getId();
        SPDLOG_INFO("test_alias: {}", call_node->toString());
        if (auto info = m_state.taint_state.is_tainted(ptr); info.has_value())
        {
            SPDLOG_INFO("Node is tainted: {}", info.value().to_string(&m_state.m_svfir));
        }
        else
        {
            SPDLOG_INFO("Node not tainted");
        }
    }

    // void TaintVisitor::visitPrintPts(SVF::CallICFGNode* call_node) {
    //     auto ptr = call_node->getActualParms()[0]->getId();
    //     SPDLOG_INFO("print_pts: {}", call_node->toString());
    //     auto pts = m_state.m_pointer_analysis.getPts(ptr);
    //     std::vector<SVF::NodeID> v;
    //     for (auto pt : pts)  { v.push_back(pt); }
    //     SPDLOG_INFO("PTS: {}", fmt::join(v, ", "));
    // }

    void TaintVisitor::visit(SVF::ICFGNode *node)
    {
        SPDLOG_TRACE("ICFGNode: {}", node->toString());
        m_instructions_count++;

        auto kind = (SVF::ICFGNode::ICFGNodeK)node->getNodeKind();
        switch (kind)
        {
        case SVF::ICFGNode::GlobalBlock:
            break;
        case SVF::ICFGNode::IntraBlock:
            visitIntraBlock(SVF::SVFUtil::dyn_cast<SVF::IntraICFGNode>(node));
            break;
        case SVF::ICFGNode::FunCallBlock:
            visitCallBlock(SVF::SVFUtil::dyn_cast<SVF::CallICFGNode>(node));
            break;
        case SVF::ICFGNode::FunEntryBlock:
            break;
        case SVF::ICFGNode::FunExitBlock:
            visitFunExitBlock(SVF::SVFUtil::dyn_cast<SVF::FunExitICFGNode>(node));
            break;
        case SVF::ICFGNode::FunRetBlock:
            break;
        }
    }

    std::vector<TaintResult> TaintVisitor::get_result()
    {
        SPDLOG_TRACE("Total instructions: {} for {}", m_instructions_count, m_call_stack.back().name());

        return m_result;
    }

    State &TaintVisitor::get_state()
    {
        return m_state;
    }

    RetInfo TaintVisitor::get_ret_info() const
    {
        return m_ret_info;
    }

    void TaintVisitor::save_tainted_sink(TaintResult::Type type, TaintInfo info, const SVF::SVFInstruction *site)
    {
        SPDLOG_INFO("taint_visitor: Deref at {}", site->toString());
        auto debug_loc = site->toString();
        SPDLOG_INFO("Call stack: {}", m_call_stack.to_string());
        m_result.emplace_back(type, info, debug_loc, m_call_stack, site);
    }

    // TaintVisitor TaintVisitor::fork_for_call(llvm::CallInst& call) {
    //     auto tv = *this;
    //     tv.m_instructions_count = 0;
    //     auto called_func = call.getCalledFunction();
    //     auto arg_count = call.arg_size();
    //     // Copy taint from arg operand to argument
    //     // This needs to be refactored to get context-sensitiveness
    //     for (auto i = 0; i < arg_count; i++) {
    //         if (auto info = m_state.taint_state.is_tainted(call.getArgOperand(i)); info.has_value()) {
    //             tv.mark_as_tainted(called_func->getArg(i), info.value(), call.getArgOperand(i));
    //         } else if (auto info = m_state.taint_state.is_points_to_tainted(call.getArgOperand(i)); info.has_value()) {
    //             tv.mark_as_pts_tainted(called_func->getArg(i), info.value(), call.getArgOperand(i));
    //         }
    //     }
    //
    //     auto& debug_loc = call.getDebugLoc();
    //     auto debug_info = kutils::debug_loc_as_string(&debug_loc);
    //     SPDLOG_TRACE("Calling {} @ {}", called_func->getName(), debug_info);
    //     tv.m_result.clear();
    //     tv.m_call_stack.push({called_func, debug_info});
    //     return tv;
    // }
    //
    // void TaintVisitor::merge_on_call(TaintVisitor& tv) {
    //     auto result = tv.get_result();
    //     m_result.insert(m_result.end(), result.begin(), result.end());
    // }

    bool TaintVisitor::is_memcpy(llvm::Function *func)
    {
        auto name = func->getName().str();
        if (name.find("llvm.memcpy") != name.npos)
        {
            return true;
        }

        return false;
    }

    TaintVisitor TaintVisitor::fork_for_call(const SVF::SVFFunction *f, const SVF::CallICFGNode *call_node)
    {
        auto tv = *this;
        tv.m_instructions_count = 0;

        auto entry_block = m_state.m_icfg.getFunEntryICFGNode(f);
        auto &formal_params = entry_block->getFormalParms();
        auto &actual_params = call_node->getActualParms();

        for (auto i = 0; i < formal_params.size(); i++)
        {
            if (m_state.taint_state.is_tainted(formal_params[i]->getId()))
            {
                SPDLOG_ERROR("Argument {} already taitned!", i);
            }
        }

        std::vector<SVF::NodeID> taitned_args;
        for (auto i = 0; i < actual_params.size(); i++)
        {
            if (auto info = m_state.taint_state.is_tainted(actual_params[i]->getId()); info.has_value())
            {
                SPDLOG_TRACE("Propagating taint (arg: {})", i);
                taitned_args.push_back(i);
                if (i >= formal_params.size())
                {
                    SPDLOG_ERROR("Vararg function call. Skipping arg {}", i);
                    continue;
                }
                tv.mark_as_tainted(formal_params[i]->getId(), actual_params[i]->getId(), call_node->toString(),
                                   info.value());
            }
        }
        SPDLOG_INFO("Total tainted args: {} for {}", taitned_args.size(), f->getName());

        auto debug_info = call_node->getRetICFGNode()->toString();
        SPDLOG_TRACE("Calling {} @ {}", f->getName(), debug_info);
        tv.m_result.clear();
        tv.m_call_stack.push(CallPoint{f, debug_info, taitned_args});
        return tv;
    }

    void TaintVisitor::merge_on_call(TaintVisitor &tv)
    {
        auto result = tv.get_result();
        m_result.insert(m_result.end(), result.begin(), result.end());
    }
}
