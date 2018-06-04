#ifndef slstar_decl_plugin_H_
#define slstar_decl_plugin_H_

#include "ast/ast.h"
#include "util/id_gen.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "util/mpf.h"

enum slstar_sort_kind {
    SLSTAR_TREE,
    SLSTAR_LIST,
};

enum slstar_op_kind {
    SLSTAR_SEP,
    SLSTAR_OP
};

class slstar_decl_plugin : public decl_plugin {
    
    decl_plugin * mk_fresh();

    sort * mk_slstar_tree();
    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;

    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range) override;

    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;
    void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) override;
};

#endif //slstar_decl_plugin_H_