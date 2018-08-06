#ifndef SLSTAR_CONVERTER_H_
#define SLSTAR_CONVERTER_H_

#include <map>
#include <set>
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

class sl_enc{
public:
    app * A;
    app* B;
    std::set<app*> Z;
};

class slstar_converter {

protected:
    ast_manager            & m;
    bool_rewriter            m_boolrw;

    sort                   * m_array_sort;
    sort                   * m_int_sort;
    std::map<app*,sl_enc*>   encoding;    
public:
    slstar_util              util;
    array_util               m_arrayutil;

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


    void add_pred(expr * ex, expr * const * args, unsigned num);

    void add_floc(expr * ex, expr * const * args, unsigned num);  /* T_N^s */  
    void add_fdat(expr * ex, expr * const * args, unsigned num);  /* T_N^s */ 
    void add_ptox(expr * ex, expr * const * args, unsigned num);  /* T_N^s */ 
    void add_sep(expr * ex, expr * const * args, unsigned num);   /* T_N^s */

    void add_neg_app(expr * ex, expr * const * args, unsigned num); /* T_N^b */        
    void add_app(expr * ex, expr * const * args, unsigned num);     /* T_N^b */  
    void add_and(expr * ex, expr * const * args, unsigned num);     /* T_N^b */  
    void add_or(expr * ex, expr * const * args, unsigned num);      /* T_N^b */ 
};

#endif //SLSTAR_CONVERTER_H_ 