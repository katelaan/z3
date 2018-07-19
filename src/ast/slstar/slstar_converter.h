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

    void mk_fresh_array(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
};

#endif //SLSTAR_CONVERTER_H_