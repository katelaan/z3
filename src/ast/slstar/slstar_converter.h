#ifndef SLSTAR_CONVERTER_H_
#define SLSTAR_CONVERTER_H_

#include "ast/ast.h"
#include "util/obj_hashtable.h"
#include "util/ref_util.h"
#include "ast/slstar_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/dl_decl_plugin.h"
#include "ast/pb_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/bool_rewriter.h"

class slstar_converter {

protected:
    ast_manager            & m;
    slstar_util              util;
    array_util               m_arrayutil;
    bool_rewriter            m_boolrw;

    sort                   * m_array_sort;
    sort                   * m_int_sort;
public:
    slstar_converter(ast_manager & m);
    ~slstar_converter();

    app * mk_fresh_array(char const * prefix);
    app * mk_empty_array();

    app * mk_single_element_array(expr * x);
    app * mk_is_empty(expr * set);
    app * mk_is_element(expr * x, expr * set);

    app * mk_subset_eq(expr * lhs, expr * rhs);
    app * mk_union(expr * lhs, expr * rhs);
    app * mk_intersect(expr * lhs, expr * rhs);
};

#endif //SLSTAR_CONVERTER_H_