#ifndef SLSTAR_REWRITER_H_
#define SLSTAR_REWRITER_H_

#include "ast/rewriter/rewriter.h"
#include "ast/slstar_decl_plugin.h"
#include "ast/slstar/slstar_converter.h"


struct slstar_rewriter_cfg : public default_rewriter_cfg {
    ast_manager              & m_manager;
    expr_ref_vector            m_out;
    slstar_converter         & m_conv;
    sort_ref_vector            m_bindings;

    unsigned long long         m_max_memory;
    unsigned                   m_max_steps;

    slstar_rewriter_cfg(ast_manager & m, slstar_converter & c, params_ref const & p);

    void updt_local_params(params_ref const & _p);

    void updt_params(params_ref const & p);

};

struct slstar_rewriter : public rewriter_tpl<slstar_rewriter_cfg> {
    slstar_rewriter_cfg m_cfg;
    slstar_rewriter(ast_manager & m, slstar_converter & c, params_ref const & p):
        rewriter_tpl<slstar_rewriter_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m, c, p) {
    }
};

#endif //SLSTAR_REWRITER_H_