#ifndef SLSTAR_SPATIAL_EQ_PROPAGATION_TACTIC_H_
#define SLSTAR_SPATIAL_EQ_PROPAGATION_TACTIC_H_

#include "util/params.h"
class ast_manager;
class tactic;


#include <set>
#include <unordered_set>
#include <unordered_map>
#include <memory>

using equality_bin = std::shared_ptr<std::set<expr*>>;
using equality_bin_map = std::unordered_map<std::string, equality_bin>;
using equality_bin_map_ref = std::shared_ptr<equality_bin_map>;

tactic * mk_slstar_spatial_eq_propagation_tactic(ast_manager & m, equality_bin_map_ref eq_bins, params_ref const & p = params_ref());


#endif
 
