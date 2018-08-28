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

    bool contains_calls = false;

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
    sl_bounds                bounds;

    sort                   * m_array_sort = nullptr;
    sort                   * m_int_sort = nullptr;

    func_decl              * f_next = nullptr;
    func_decl              * f_dat = nullptr;
    func_decl              * f_left = nullptr;
    func_decl              * f_right = nullptr;

    std::map<expr*,sl_enc*>  encoding;
    std::map<expr*,app*>     locencoding;
#if defined(Z3DEBUG)
    std::set<expr*>          encodedlocs;
#endif
    std::vector<expr*>       list_locs;
    std::vector<expr*>       tree_locs;

    expr                   * Xn = nullptr;
    expr                   * Xl = nullptr;
    expr                   * Xr = nullptr;
    expr                   * Xd = nullptr;
    app                    * enc_null = nullptr;
public:
    slstar_util              util;
    array_util               m_arrayutil;

    slstar_encoder(ast_manager & m);
    ~slstar_encoder();

    app * mk_fresh_array(char const * prefix);
    app * mk_empty_array();
    app * mk_full_array();

    app * mk_set_from_elements(expr * const * elem, unsigned num );
    app * mk_set_remove_element(expr * x, expr * set);
    app * mk_is_empty(expr * set);
    app * mk_is_element(expr * x, expr * set);

    app * mk_subset_eq(expr * lhs, expr * rhs);
    app * mk_union(expr * const *args, unsigned num);
    app * mk_intersect(expr * lhs, expr * rhs);

    app * mk_encoded_loc(expr * ex);
    app * mk_global_constraints();

    app * mk_isstop(expr * xenc, std::vector<expr*> & stops);
    app * mk_is_successor_tree(expr * x, expr * y);
    app * mk_is_successor_list(expr * x, expr * y);
    app * mk_defineY_tree(sl_enc * enc, expr * Z);
    app * mk_defineY_list(sl_enc * enc, expr * Z);
    app * mk_reach1(expr * Z, 
        std::vector<func_decl*> & prev_reach, 
        std::vector<expr*> & xlocs, 
        std::vector<expr*> & stops,
        decl_kind k);
    app * mk_reachN(std::vector<func_decl*> & prev_reach, std::vector<expr*> & xlocs);
    app * mk_reachability_list(expr * Z, std::vector<func_decl*> & prev_reach, std::vector<expr*> & stops);
    app * mk_reachability_tree(expr * Z, std::vector<func_decl*> & prev_reach, std::vector<expr*> & stops);
    app * mk_emptyZ(expr * xenc, std::vector<expr*> & xlocs, std::vector<expr*> & stops);
    app * mk_footprint(expr * xenc,
        expr * Z, 
        std::vector<expr*> & xlocs, 
        std::vector<func_decl*> & prev_reach, 
        std::vector<expr*> & stops);
    app * mk_all_succs_different_list(expr * xi, expr * xj);
    app * mk_all_succs_different_tree(expr * xi, expr * xj);
    app * mk_oneparent_list(expr * Z, std::vector<expr*> & xlocs);
    app * mk_oneparent_tree(expr * Z, std::vector<expr*> & xlocs);
    app * mk_structure_list(expr * xenc, 
        expr * Z, 
        std::vector<expr*> & xlocs, 
        std::vector<func_decl*> & prev_reach, 
        std::vector<expr*> & stops);
    app * mk_structure_tree(expr * xenc, 
        expr * Z, 
        std::vector<expr*> & xlocs, 
        std::vector<func_decl*> & prev_reach, 
        std::vector<expr*> & stops);
    app * mk_stopseq(expr * xenc, std::vector<expr*> & stops);
    app * mk_stopsoccur_list(expr * xenc, expr * Z, std::vector<expr*> & xlocs, std::vector<expr*> & stops );
    app * mk_stopsoccur_tree(expr * xenc, expr * Z, std::vector<expr*> & xlocs, std::vector<expr*> & stops );
    app * mk_stopleaves_list(expr * Z, std::vector<expr*> & xlocs, std::vector<expr*> & stops );
    app * mk_stopleaves_tree(expr * Z, std::vector<expr*> & xlocs, std::vector<expr*> & stops );
    app * mk_Rn_f(func_decl * f, func_decl * rn, expr * x, expr * y, expr * Z);
    app * mk_fstop_tree(expr * xp, expr * s, func_decl * f, expr * Z, std::vector<expr*> & xlocs, 
        std::vector<func_decl*> & prev_reach);
    app * mk_ordered_tree(expr * Z, 
        std::vector<expr*> & xlocs, 
        std::vector<expr*> & stops,
        std::vector<func_decl*> & prev_reach);
    app * mk_is_location(expr* xenc, std::vector<expr*> & xlocs);
    app * mk_bdata(expr * P, expr * Z, func_decl * f, std::vector<expr*> & xlocs, 
        std::vector<func_decl*> & prev_reach);
    app * mk_udata(expr * P, expr * Z, std::vector<expr*> & xlocs);

    void clear_enc_dict();
    void clear_loc_vars();
    void clear_X_vector();

    void prepare(sl_bounds bd);
    void encode_top(expr * current, expr_ref & new_ex);
    void encode(expr * ex);

    void add_tree(expr * ex, expr * const * args, unsigned num);
    void add_list(expr * ex, expr * const * args, unsigned num);
    void add_const(expr * ex);
    void add_floc_fdat(expr * ex, expr * const * args, unsigned num);  /* T_N^s */
    void add_eq(expr * ex, expr * const * args, unsigned num);         /* T_N^s */
    void add_distinct(expr * ex, expr * const * args, unsigned num);   /* T_N^s */
    void add_pton(expr * ex, expr * const * args, unsigned num);  /* T_N^s */
    void add_ptol(expr * ex, expr * const * args, unsigned num);  /* T_N^s */
    void add_ptor(expr * ex, expr * const * args, unsigned num);  /* T_N^s */
    void add_ptod(expr * ex, expr * const * args, unsigned num);  /* T_N^s */
    void add_ptolr(expr * ex, expr * const * args, unsigned num);  /* T_N^s */
    void add_sep(expr * ex, expr * const * args, unsigned num);    /* T_N^s */

    void add_not(expr * ex, expr * const * args, unsigned num);     /* T_N^b */
    void add_and(expr * ex, expr * const * args, unsigned num);     /* T_N^b */
    void add_or(expr * ex, expr * const * args, unsigned num);     /* T_N^b */

private:
    bool is_any_spatial(expr * const * args, unsigned num);
    bool is_any_rewritten(expr * const * args, unsigned num);
};

class sl_enc{
public:
    expr * A;
    expr * B;
    expr * Yn;
    expr * Yl;
    expr * Yr;
    expr * Yd;
    bool is_spatial;
    bool is_rewritten;

    sl_enc(ast_manager & m, slstar_encoder & enc);
    ~sl_enc();
private:

    ast_manager            & m;
    slstar_encoder         & enc;
    void mk_fresh_Y();
    void copy_Y(sl_enc * other);
    void inc_ref();
    void dec_ref();
    friend class slstar_encoder;
};

#endif //SLSTAR_CONVERTER_H_ 