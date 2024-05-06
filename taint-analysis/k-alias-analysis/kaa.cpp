#include "kaa.h"
#include "../pch.h"
#include "Util/Casting.h"

namespace kaa
{
  struct WalkState
  {
    // All the aliases to the given node
    std::unordered_set<SVF::NodeID> &result;

    // All the visited nodes along the walk
    std::unordered_set<SVF::NodeID> &visited;

    // If we see a node at depth 0, we say that we found an alias
    int current_depth{};

    // Configuration driving the walk
    const int max_depth{};

    // Configuration driving field sensitivity
    const bool field_sensitive{};

    // Offset from base pointer
    SVF::APOffset offset{};

    // True if the offset is constant. Once a pointer goes through variable gep this should be false.
    bool is_const_offset = true;

    // This is the function within which we have to walk
    // When walking down, we set it to parent's value
    // When walking up, we can only walk to the parent's function, not any other
    // If we are in the same context, we can walk up or down in any ways
    // If we are in a different context, we can only walk down in any ways
    // Note: We are walking down all possible paths first!
    const SVF::SVFFunction *context;

    WalkState(std::unordered_set<SVF::NodeID> &tresult,
              std::unordered_set<SVF::NodeID> &tvisited,
              const int tmax_depth, const bool tfield_sensitive,
              const SVF::SVFFunction *context) : result{tresult}, visited{tvisited}, current_depth{0},
                                                 max_depth{tmax_depth}, field_sensitive{tfield_sensitive},
                                                 context{context}
    {
    }
  };

  // A GEP statement can be a part of an extapi (eg: memcpy) and it cannot give a constant offset value
  // Ref: https://github.com/SVF-tools/SVF/blob/78d4f6e7ffe6a4b0f2b1886e522ee5c4b8db5270/svf/lib/MemoryModel/AccessPath.cpp#L120
  // Thus, checking here if a gep belongs to a call in an external API.
  bool is_ext_call(const SVF::GepStmt *gep)
  {
    auto inst = gep->getInst();

    if (!inst)
    {
      // Looks like we don't have the instruction for the GEP. Guess it is an external call
      return true;
    }

    auto call_inst = SVF::SVFUtil::dyn_cast<SVF::SVFCallInst>(inst);
    if (call_inst)
    {
      auto called_fun = call_inst->getCalledFunction();
      if (called_fun)
      {
        if (SVF::ExtAPI::getExtAPI()->is_ext(called_fun))
        {
          return true;
        }
      }
    }

    return false;
  }
  void find_aliases_from_pag(WalkState walk_state, SVF::SVFVar *node)
  {
    if (walk_state.visited.contains(node->getId()))
      return;

    if (walk_state.current_depth == 0)
    {
      if (!walk_state.field_sensitive || (walk_state.offset == 0 && walk_state.is_const_offset))
        walk_state.result.insert(node->getId());
    }

    // Mark the current node as visited
    walk_state.visited.insert(node->getId());

    // Walk down
    auto out_edges = node->getOutEdges();
    for (auto edge : out_edges)
    {
      auto child = edge->getDstNode();
      if (walk_state.visited.contains(child->getId()))
        continue;

      auto new_walk_state = walk_state;
      auto kind = (SVF::SVFStmt::PEDGEK)edge->getEdgeKind();

      switch (kind)
      {
      case SVF::SVFStmt::Store:
      {
        // *child = node;
        // We are being stored into one pointer

        // If we are a max depth already, let's just skip
        if (new_walk_state.current_depth == new_walk_state.max_depth)
        {
          SPDLOG_INFO("Reached max depth of stores");
          continue;
        }

        new_walk_state.current_depth++;
        break;
      }

      case SVF::SVFStmt::Load:
      {
        // child = *node;

        // Here we are loading the pointer we are analyzing. We don't want to look into it anymore
        if (new_walk_state.current_depth == 0)
          continue;

        new_walk_state.current_depth--;

        break;
      }

      case SVF::SVFStmt::Gep:
      {
        // child = node + offset
        auto gep = SVF::SVFUtil::dyn_cast<SVF::GepStmt>(edge);
        if (!gep)
        {
          SPDLOG_WARN("GEP statement is null");
          continue;
        }

        // GEP is happening in a call to external function
        if (is_ext_call(gep))
        {
          continue;
        }

        // If the offset is not a constant, we simply mark it.
        // Otherwise, update the offset.
        if (!new_walk_state.is_const_offset || !gep->isConstantOffset())
        {
          new_walk_state.is_const_offset = false;
        }
        else
        {
          new_walk_state.offset += gep->accumulateConstantByteOffset();
        }

        break;
      }

      case SVF::SVFStmt::Copy:
      case SVF::SVFStmt::Call:
        break;

      case SVF::SVFStmt::Addr:
      default:
        continue;
      }

      find_aliases_from_pag(new_walk_state, child);
    }

    // Walk the back edges
    auto in_edges = node->getInEdges();
    for (auto edge : in_edges)
    {
      auto parent = edge->getSrcNode();
      if (walk_state.visited.contains(parent->getId()))
        continue;

      // We don't want to walk into different context
      if (node->getFunction() != walk_state.context && parent->getFunction() != node->getFunction())
        continue;

      auto new_walk_state = walk_state;
      auto kind = (SVF::SVFStmt::PEDGEK)edge->getEdgeKind();

      switch (kind)
      {
      case SVF::SVFStmt::Load:
      {
        // node = *parent => *parent = node
        if (new_walk_state.current_depth == new_walk_state.max_depth)
          continue;

        new_walk_state.current_depth++;

        break;
      }

      case SVF::SVFStmt::Store:
      {
        // *parent = node
        if (new_walk_state.current_depth == 0)
          continue;

        new_walk_state.current_depth--;

        break;
      }

      case SVF::SVFStmt::Gep:
      {
        // node = parent + offset
        auto gep = SVF::SVFUtil::dyn_cast<SVF::GepStmt>(edge);
        if (!gep)
        {
          SPDLOG_WARN("GEP statement is null");
          continue;
        }

        // GEP is happening in a call to external function
        if (is_ext_call(gep))
        {
          continue;
        }

        // If the offset is not a constant, we simply mark it.
        // Otherwise, update the offset.
        if (!new_walk_state.is_const_offset || !gep->isConstantOffset())
        {
          new_walk_state.is_const_offset = false;
        }
        else
        {
          new_walk_state.offset -= gep->accumulateConstantByteOffset();
        }

        break;
      }

      case SVF::SVFStmt::Copy:
      case SVF::SVFStmt::Call:
        break;

      default:
        continue;
      }

      new_walk_state.context = parent->getFunction();
      find_aliases_from_pag(new_walk_state, parent);
    }
  }

  std::unordered_set<SVF::NodeID> AliasAnalysis::get_aliases(SVF::NodeID src)
  {
    std::unordered_set<SVF::NodeID> result{};
    std::unordered_set<SVF::NodeID> visited{};
    auto node = pag_->getGNode(src);
    SPDLOG_INFO("[kaa] BEGIN AliasAnalysis on {}", node->toString());
    auto context = node->getFunction();
    WalkState ws{result, visited, max_depth_, field_sensitive_, context};
    find_aliases_from_pag(ws, node);
    SPDLOG_INFO("[kaa] END AliasAnalysis on {} | Result size: {}", node->toString(), result.size());

    return result;
  }
} // namespace kaa
