#ifndef slstar_decl_plugin_H_
#define slstar_decl_plugin_H_

#include <list>
#include "ast/ast.h"
#include "util/id_gen.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "util/mpf.h"

enum slstar_sort_kind {
    SLSTAR_TREE_LOC,
    SLSTAR_LIST_LOC,
    SLSTAR_DPRED
};

enum slstar_op_kind {
    OP_SLSTAR_SEP,
    OP_SLSTAR_POINTSTOL,
    OP_SLSTAR_POINTSTOR,
    OP_SLSTAR_POINTSTOLR,
    OP_SLSTAR_POINTSTON,
    OP_SLSTAR_POINTSTOD,
    OP_SLSTAR_TREE,
    OP_SLSTAR_LIST,
    OP_SLSTAR_NULL,

    OP_SLSTAR_UNARY,
    OP_SLSTAR_LEFT,
    OP_SLSTAR_RIGHT,
    OP_SLSTAR_NEXT,

    OP_SLSTAR_ALPHA,
    OP_SLSTAR_BETA,
};

class slstar_decl_plugin : public decl_plugin {
    
private:
    sort *              m_int_sort;
    sort *              m_dpred_sort;

    std::vector<parameter> check_call_sort_params(unsigned num_parameters, parameter const * parameters);
    void set_loc_sort( sort * &lhs , sort * rhs );
    void check_loc_sort( sort * sort);

    func_decl * mk_null_func_decl(decl_kind k, sort * range);
    func_decl * mk_support_decl(symbol name, decl_kind k, unsigned num_parameters, 
                                    parameter const * parameters, unsigned arity,
                                    sort * const * domain, sort * range);
    func_decl * mk_data_predicate_decl(symbol name, decl_kind k, unsigned num_parameters, 
                                    parameter const * parameters, unsigned arity,
                                    sort * const * domain, sort * range);
    func_decl * mk_pred_func_decl(symbol name, std::string loc, decl_kind loc_k,
                                    decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                    unsigned arity, sort * const * domain, sort * range);
    func_decl * mk_pto_func_decl(symbol name, std::string loc, decl_kind loc_k,unsigned exp_arity,
                                    decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                    unsigned arity, sort * const * domain, sort * range);
    func_decl * mk_ptod_func_decl(symbol name, unsigned exp_arity,
                                    decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                    unsigned arity, sort * const * domain, sort * range);
public:

    decl_plugin * mk_fresh();

    static sort * get_loc_sort(ast_manager * m);

    sort * mk_slstar_tree(unsigned num_parameters, parameter const * parameters);
    sort * mk_slstar_list(unsigned num_parameters, parameter const * parameters);
    sort * mk_slstar_nullsort(unsigned num_parameters, parameter const * parameters);
    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;

    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range) override;

    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;
    void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) override;

    void set_manager(ast_manager * m, family_id id) override;

    ~slstar_decl_plugin() override;
    void finalize() override;
};

class slstar_util {
    ast_manager        & m_manager;
    slstar_decl_plugin * m_plugin;
    family_id          m_fid;
public:
    slstar_util(ast_manager & m);
    ~slstar_util();

    ast_manager & m() const { return m_manager; }
    family_id get_fid() const { return m_fid; }
    family_id get_family_id() const { return m_fid; }

    void get_spatial_atoms(std::list<expr*> * atoms, expr * ex);
    void get_spatial_atoms_with_polarity(std::list<std::pair<expr*,bool> > * atoms, expr * ex, bool parent_neg = false);
    void get_constants(std::list<expr*> * consts, expr * ex);

    bool is_pto(expr const * ex);
    bool is_ptolr(expr const * ex);
    bool is_ptor(expr const * ex);
    bool is_ptol(expr const * ex);
    bool is_pton(expr const * ex);
    bool is_ptod(expr const * ex);
     
    bool is_sep(expr const * ex);

    bool is_call(expr const * ex);
    bool is_tree(expr const * ex);
    bool is_list(expr const * ex);
    bool is_alpha(expr const * ex);
    bool is_beta(expr const * ex);

    bool is_listconst(expr const * ex);
    bool is_treeconst(expr const * ex);
    bool is_null(expr const * ex);
    bool is_loc(expr const * ex);

    bool is_dpred_unary(expr const * ex);
    bool is_dpred_binary(expr const * ex);
    bool is_dpred_left(expr const * ex);
    bool is_dpred_right(expr const * ex);
    bool is_dpred_next(expr const * ex);
    bool is_dpred(expr const * ex);

    bool is_listloc(sort const * s);
    bool is_treeloc(sort const * s);
    bool is_dpred(sort const * s);

    app * mk_null(sort * nullsort) ;

    unsigned int num_stop_nodes(expr const * t);
};

#endif //slstar_decl_plugin_H_