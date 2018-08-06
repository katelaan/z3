#include "ast/slstar/slstar_converter.h"

slstar_converter::slstar_converter(ast_manager & m) : m(m), util(m), m_arrayutil(m), m_boolrw(m) {
    auto fid = m.mk_family_id("arith");
    m_int_sort = m.mk_sort(fid, INT_SORT);
    m.inc_ref(m_int_sort);

    vector<parameter> params;
    params.push_back(parameter(m_int_sort)); //TODOsl configurable LocSort
    params.push_back(parameter(m.mk_bool_sort()));
    fid = m.mk_family_id("array");
    m_array_sort = m.mk_sort(fid, ARRAY_SORT, params.size(), params.c_ptr());
    m.inc_ref(m_array_sort);
}

slstar_converter::~slstar_converter() {
    if(m_array_sort) m.dec_ref(m_array_sort);
    if(m_int_sort) m.dec_ref(m_int_sort);
}

app * slstar_converter::mk_fresh_array(char const * prefix) {
    return m.mk_fresh_const(prefix,m_array_sort);
}

app * slstar_converter::mk_empty_array() {
    return m_arrayutil.mk_empty_set(m_int_sort);
}

app * slstar_converter::mk_single_element_array(expr * x) {
    app * tmp = mk_empty_array();
    expr * args[3] = {tmp, x, m.mk_true()};
    return m_arrayutil.mk_store(3, args);
}

app * slstar_converter::mk_is_empty(expr * set){
    return m.mk_eq(set, mk_empty_array());
}

app * slstar_converter::mk_is_element(expr * x, expr * set){
    expr * args[2] = {set, x};
    return m_arrayutil.mk_select(2, args);
}

app * slstar_converter::mk_subset_eq(expr * lhs, expr * rhs) {
    //TODOsl
    //app * tmp = m.mk_implies(m.mk_true(), m.mk_true());
    //tmp->get_decl(); 
    sort *domain[2] = {m.mk_bool_sort(), m.mk_bool_sort()};
    func_decl * f = m.get_basic_decl_plugin()->mk_func_decl(OP_IMPLIES, 0, nullptr, 2, domain, nullptr); 
    expr * args[2] = {lhs, rhs};
    return m_arrayutil.mk_map(f, 2, args);
}

app * slstar_converter::mk_union(expr * lhs, expr * rhs) {
    sort *domain[2] = {m.mk_bool_sort(), m.mk_bool_sort()};
    func_decl * f = m.get_basic_decl_plugin()->mk_func_decl(OP_OR, 0, nullptr, 2, domain, nullptr); 
    expr * args[2] = {lhs, rhs};
    return m_arrayutil.mk_map(f, 2, args);
}

app * slstar_converter::mk_intersect(expr * lhs, expr * rhs) {
    sort *domain[2] = {m.mk_bool_sort(), m.mk_bool_sort()};
    func_decl * f = m.get_basic_decl_plugin()->mk_func_decl(OP_AND, 0, nullptr, 2, domain, nullptr); 
    expr * args[2] = {lhs, rhs};
    return m_arrayutil.mk_map(f, 2, args);
}

void slstar_converter::add_pred(expr * ex, expr * const * args, unsigned num) {
    SASSERT(is_app(ex));
    app * t = to_app(ex);
    t->
}
void slstar_converter::add_floc(expr * ex, expr * const * args, unsigned num) {

}
void slstar_converter::add_fdat(expr * ex, expr * const * args, unsigned num) {

}
void slstar_converter::add_ptox(expr * ex, expr * const * args, unsigned num) {

}
void slstar_converter::add_sep(expr * ex, expr * const * args, unsigned num) {

}
void slstar_converter::add_neg_app(expr * ex, expr * const * args, unsigned num) {

}
void slstar_converter::add_app(expr * ex, expr * const * args, unsigned num) {

}
void slstar_converter::add_and(expr * ex, expr * const * args, unsigned num) {

}
void slstar_converter::add_or(expr * ex, expr * const * args, unsigned num) {

}