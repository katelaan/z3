#ifndef SLSTAR_ENCODER_H_
#define SLSTAR_ENCODER_H_

#include <unordered_map>
#include <unordered_set>
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

enum sl_enc_level {
    SL_LEVEL_FULL = 100,
    SL_LEVEL_FOOTPRINTS = 90,
    SL_LEVEL_UF = 80,
    SL_LEVEL_INVALID = 0
};

#include "ast/slstar/pred_encoder.h"
#include "ast/slstar/list_encoder.h"
#include "ast/slstar/tree_encoder.h"

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

class slstar_set_encoder {
private:
    ast_manager & m;
    array_util m_arrayutil;
    sort_ref m_array_sort;
    sort_ref m_loc_sort;
public:
    slstar_set_encoder(ast_manager & m, sort * loc_sort);
    ~slstar_set_encoder();

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
};

class sl_enc {
public:
    expr_ref A;
    expr_ref B;
    expr_ref Yn;
    expr_ref Yl;
    expr_ref Yr;
    expr_ref Yd;
    bool is_spatial;
    bool is_rewritten;
    bool needs_tree_footprint;
    bool needs_list_footprint;
    sl_enc_level level;

    sl_enc(ast_manager & m, slstar_set_encoder & set_enc, bool trees, bool lists );
    ~sl_enc();
    void mk_fresh_Y();
    void copy_Y(sl_enc* other);
    void pp(std::ostream & out);
private:
    ast_manager & m;
    slstar_set_encoder & set_enc;
};

class enc_cache {
public:
    enc_cache(ast_manager & m, sort_ref const& loc_sort);
    ~enc_cache();

    func_decl * get_f_dat(sort * s);
    bool has_cached_encoding(expr * e) const;
    sl_enc* get_cached_encoding(expr * e) const;
    void add_encoding(expr * e, sl_enc * enc);
    bool has_encoded_loc(expr * e) const;
    app* get_encoded_loc(expr * e) const;
    void add_encoded_loc(expr * e, app * encoded);
    void uncache(expr *const e);
    void clear_enc_dict();
    std::unordered_set<app*> all_encoded_consts() const;
    std::unordered_map<sort*, func_decl*> get_f_dat_map() const;
private:
    ast_manager & m; 
    sort_ref const& m_loc_sort;

    #if defined(Z3DEBUG)
    std::unordered_set<expr*>          encodedlocs;
    #endif  
    std::unordered_map<sort*, func_decl*> f_dat_map;
    std::unordered_map<expr*, sl_enc*> encoding;
    std::unordered_map<expr*, app*> locencoding;
    std::unordered_set<app*> encoded_const;

    void clear_loc_vars();
};

class slstar_encoder {
    friend class pred_encoder;
    friend class list_encoder;
    friend class tree_encoder;
    friend class slstar_model_converter;
    friend class slstar_tactic; // TODO: Remove this from friends as soon as we have a proper way to clean the cache from outside; see the reduce tactic file
protected:
    ast_manager            & m;
    bool_rewriter            m_boolrw;
    sl_bounds                bounds;
    slstar_set_encoder       set_enc;
    
    sort_ref m_loc_sort;
    func_decl_ref f_next;
    func_decl_ref f_left;
    func_decl_ref f_right;

    enc_cache                cache;

    expr_ref_vector list_locs;
    expr_ref_vector tree_locs;

    app_ref Xn;
    app_ref Xl;
    app_ref Xr;
    app_ref Xd;
    app_ref enc_null;

    bool needs_tree_footprint;
    bool needs_list_footprint;

public:
    static const std::string Z_prefix;
    static const std::string Y_prefix;
    static const std::string reach_prefix;
    static const std::string X_prefix;
    static const std::string xl_prefix;
    static const std::string xt_prefix;

    slstar_util              util;
    sl_enc_level             current_level;

    slstar_encoder(ast_manager & m, sort * loc_sort);
    ~slstar_encoder();

    app * mk_encoded_loc(expr * ex);
    app * mk_global_constraints();

    void clear_X_vector();

    void prepare(sl_bounds bd, sl_enc_level level);
    void encode_top(expr * current, expr_ref & new_ex);
    void encode(expr * ex);

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
    sl_enc_level get_lowest_level(expr * const * args, unsigned num);
};

#endif //SLSTAR_ENCODER_H_ 