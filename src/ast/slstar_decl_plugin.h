#ifndef slstar_decl_plugin_H_
#define slstar_decl_plugin_H_

#include "ast/ast.h"
#include "util/id_gen.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "util/mpf.h"

enum slstar_sort_kind {
    SLSTAR_TREE_LOC,
    SLSTAR_LIST_LOC,
    SLSTAR_KEYWORD,
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
public:

    decl_plugin * mk_fresh();

    sort * mk_slstar_tree();
    sort * mk_slstar_list();
    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;

    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range) override;

    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;
    void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) override;

    void set_manager(ast_manager * m, family_id id) override;

    ~slstar_decl_plugin() override;
    void finalize() override;
};

#endif //slstar_decl_plugin_H_