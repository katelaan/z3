#ifndef SLSTAR_REDUCE_TACTIC_H_
#define SLSTAR_REDUCE_TACTIC_H_

#include "util/params.h"
class ast_manager;
class tactic;
class probe;

tactic * mk_slstar_reduce_tactic(ast_manager & m, params_ref const & p = params_ref());

probe * mk_is_slstar_probe();

#endif
