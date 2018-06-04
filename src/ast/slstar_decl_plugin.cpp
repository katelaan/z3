#include "ast/slstar_decl_plugin.h"
void slstar_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {

}

void slstar_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    //sort_names.push_back(builtin_name("Tree", SLSTAR_TREE));
}

decl_plugin * slstar_decl_plugin::mk_fresh() {
    return alloc(slstar_decl_plugin);
}

sort * slstar_decl_plugin::mk_slstar_tree() {
    //TODOsl
    //parameter ps[0] = { };
    sort_size sz;
    sz = sort_size::mk_very_big(); // TODO: refine
    return m_manager->mk_sort(symbol("Tree"), sort_info(m_family_id, SLSTAR_TREE, sz, 0, NULL));
    //return m_manager->mk_sort(symbol("Tree"), sort_info(m_family_id, SLSTAR_TREE, sz, 0, ps));
}

sort * slstar_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    switch (k) {
    case SLSTAR_TREE:
        return mk_slstar_tree();
    default:
        m_manager->raise_exception("unknown separation logic theory sort");
        return nullptr;
    }
}

func_decl * slstar_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range) {
    m_manager->raise_exception("unsupported separation logic operator");
    return nullptr;
}
