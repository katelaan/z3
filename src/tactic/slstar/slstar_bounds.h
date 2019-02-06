#include "ast/slstar_decl_plugin.h"
#include "ast/slstar/slstar_encoder.h"

class slstar_bound_computation {
private:
    ast_manager & m;
    slstar_util& util;

    bool noncall_conjunct_bounds(expr * in, expr *& out);
    sl_bounds noncall_conjunct_bounds(goal_ref const & g);
    void count_src_symbols(expr * ex, sl_bounds * ret);
    void count_non_null_const(sl_bounds & ret, std::list<expr*> & consts);
    void calc_spatial_bounds(goal_ref const & g, sl_bounds & ret);
    void calc_bounds_max(sl_bounds & a_ret, sl_bounds & b);
    void calc_nondata_bounds_non_spatial(sl_bounds & ret, app * t);
    void calc_bounds_spatial(sl_bounds & ret, app * t);
    
public:
    sl_bounds calc_bounds(goal_ref const & g);
    slstar_bound_computation(ast_manager & m, slstar_util& util);
};