#pragma once
#include <unordered_set>
#include "SVFIR/SVFType.h"
#include "SVFIR/SVFIR.h"

namespace kaa
{
  class AliasAnalysis
  {
  private:
    const int max_depth_;
    const bool field_sensitive_;
    const SVF::SVFIR *pag_;

  public:
    AliasAnalysis(const SVF::SVFIR *pag,
                  const int max_depth, const bool field_sensitive) : pag_{pag},
                                                                     max_depth_{max_depth},
                                                                     field_sensitive_{field_sensitive} {}
    std::unordered_set<SVF::NodeID> get_aliases(SVF::NodeID src);
  };

}