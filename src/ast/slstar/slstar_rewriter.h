#ifndef SLSTAR_REWRITER_H_
#define SLSTAR_REWRITER_H_

#include "ast/rewriter/rewriter.h"
#include "ast/slstar_decl_plugin.h"
#include "ast/slstar/slstar_encoder.h"


struct slstar_rewriter_cfg : public default_rewriter_cfg {
    ast_manager              & m_manager;
    expr_ref_vector            m_out;
    slstar_encoder           & m_enc;
    sort_ref_vector            m_bindings;
    expr                     * current;

    unsigned long long         m_max_memory;
    unsigned                   m_max_steps;

    slstar_rewriter_cfg(ast_manager & m, slstar_encoder & c, params_ref const & p);

    void updt_local_params(params_ref const & _p);

    void updt_params(params_ref const & p);

    //bool cache_all_results() const;
    //bool cache_results() const;
    //bool flat_assoc(func_decl * f) const { return true; } // '(sep (sep a b) c)' should be treated as '(sep a b c)' TODOsl: how to set sep as associative?
    //bool rewrite_patterns() const;
    //bool max_scopes_exceeded(unsigned num_scopes) const;
    //bool max_frames_exceeded(unsigned num_frames) const;
    //bool max_steps_exceeded(unsigned num_steps) const;
    bool pre_visit(expr * t);
    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr);
    //bool reduce_quantifier(quantifier * old_q, 
    //                       expr * new_body, 
    //                       expr * const * new_patterns, 
    //                       expr * const * new_no_patterns,
    //                       expr_ref & result,
    //                       proof_ref & result_pr);
    //bool get_macro(func_decl * d, expr * & def, quantifier * & q, proof * & def_pr);
    //bool get_subst(expr * s, expr * & t, proof * & t_pr);

    void reset(){
    }
    void cleanup(){
    }
};

struct slstar_rewriter : public rewriter_tpl<slstar_rewriter_cfg> {
    slstar_rewriter_cfg m_cfg;
    slstar_rewriter(ast_manager & m, slstar_encoder & e, params_ref const & p):
        rewriter_tpl<slstar_rewriter_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m, e, p) {
    }
};

#endif //SLSTAR_REWRITER_H_