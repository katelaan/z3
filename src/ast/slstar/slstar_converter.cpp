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

void slstar_converter::mk_fresh_array(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    result = m.mk_eq(m.mk_fresh_const("Y",m_array_sort) , m.mk_fresh_const("X",m_array_sort)) ;
}