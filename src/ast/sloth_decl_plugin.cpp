#include "ast/sloth_decl_plugin.h"
void sloth_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {

}

decl_plugin * sloth_decl_plugin::mk_fresh() {
    return alloc(sloth_decl_plugin);
}

sort * sloth_decl_plugin::mk_sloth_sort() {
    //TODOsl
    //parameter ps[0] = { };
    sort_size sz;
    sz = sort_size::mk_very_big(); // TODO: refine
    return m_manager->mk_sort(symbol("Sloth"), sort_info(m_family_id, SLOTH_SORT, sz, 0, NULL));
    //return m_manager->mk_sort(symbol("Sloth"), sort_info(m_family_id, SLOTH_SORT, sz, 0, ps));
}

sort * sloth_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    switch (k) {
    case SLOTH_SORT:
        return mk_sloth_sort();
    default:
        m_manager->raise_exception("unknown separation logic theory sort");
        return nullptr;
    }
}

func_decl * sloth_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range) {
    m_manager->raise_exception("unsupported separation logic operator");
    return nullptr;
}
