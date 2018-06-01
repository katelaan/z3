#ifndef sloth_decl_plugin_H_
#define sloth_decl_plugin_H_

#include "ast/ast.h"
#include "util/id_gen.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "util/mpf.h"

enum sloth_sort_kind {
    SLOTH_SORT,
};

enum sloth_op_kind {
    SLOTH_OP
};

class sloth_decl_plugin : public decl_plugin {
    
    decl_plugin * mk_fresh();

    sort * mk_sloth_sort();
    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters);

    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range);

    void get_op_names(svector<builtin_name> & op_names, symbol const & logic);
};

#endif //sloth_decl_plugin_H_