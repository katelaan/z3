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

class sl_enc;

struct sl_bounds {
    int n_list = -1;
    int n_tree = -1;

    bool is_def() {
        return (n_list != -1) && (n_tree != -1);
    }

    void define() {
        n_list = 0;
        n_tree = 0;
    }
};

class slstar_encoder {

protected:
    ast_manager            & m;
    bool_rewriter            m_boolrw;

    sort                   * m_array_sort;
    sort                   * m_int_sort;

    func_decl              * f_next;
    func_decl              * f_dat;
    func_decl              * f_left;
    func_decl              * f_right;

    std::map<expr*,sl_enc*>   encoding;
public:
    slstar_util              util;
    array_util               m_arrayutil;

    slstar_encoder(ast_manager & m);
    ~slstar_encoder();
    void operator()(sl_bounds bd, expr * current, expr_ref & new_ex);

    app * mk_fresh_array(char const * prefix);
    app * mk_empty_array();

    app * mk_single_element_array(expr * x);
    app * mk_set_remove_element(expr * x, expr * set);
    app * mk_is_empty(expr * set);
    app * mk_is_element(expr * x, expr * set);

    app * mk_subset_eq(expr * lhs, expr * rhs);
    app * mk_union(expr * const *args, unsigned num);
    app * mk_intersect(expr * lhs, expr * rhs);

    app * mk_encoded_loc(expr * ex);
    app * mk_gobal_constraints(expr * ex);

    void reset();
    void encode(expr * ex);

    void add_pred(expr * ex, expr * const * args, unsigned num);
    void add_const(expr * ex);
    void add_floc_fdat(expr * ex, expr * const * args, unsigned num);  /* T_N^s */
    void add_pton(expr * ex, expr * const * args, unsigned num);  /* T_N^s */
    void add_ptol(expr * ex, expr * const * args, unsigned num);  /* T_N^s */
    void add_ptor(expr * ex, expr * const * args, unsigned num);  /* T_N^s */
    void add_ptod(expr * ex, expr * const * args, unsigned num);  /* T_N^s */
    void add_ptolr(expr * ex, expr * const * args, unsigned num);  /* T_N^s */
    void add_sep(expr * ex, expr * const * args, unsigned num);   /* T_N^s */

    void add_not(expr * ex, expr * const * args, unsigned num);     /* T_N^b */
    void add_app(expr * ex, expr * const * args, unsigned num);     /* T_N^b */
    void add_and(expr * ex, expr * const * args, unsigned num);     /* T_N^b */
    void add_or(expr * ex, expr * const * args, unsigned num);     /* T_N^b */

private:
    bool is_any_spatial(expr * const * args, unsigned num);
};

class sl_enc{
public:
    expr * A;
    expr * B;
    expr * Yn;
    expr * Yl;
    expr * Yr;
    expr * Yd;
    std::set<expr*> Z;
    bool is_spatial;

    sl_enc(ast_manager & m, slstar_encoder & enc);
    ~sl_enc();
private:

    ast_manager            & m;
    slstar_encoder         & enc;
    void mk_fresh_Y();
    void inc_ref();
    void dec_ref();
    friend class slstar_encoder;
};

#endif //SLSTAR_CONVERTER_H_ 