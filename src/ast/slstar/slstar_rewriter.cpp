#include "ast/rewriter/rewriter_def.h"
#include "ast/slstar/slstar_rewriter.h"
#include "util/cooperate.h"

slstar_rewriter_cfg::slstar_rewriter_cfg(ast_manager & m, slstar_converter & c, params_ref const & p) :
    m_manager(m),
    m_out(m),
    m_conv(c),
    m_bindings(m)
{

}

void slstar_rewriter_cfg::updt_params(params_ref const & p) {
    m_max_memory        = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
    m_max_steps         = p.get_uint("max_steps", UINT_MAX);
    updt_local_params(p);
}


void slstar_rewriter_cfg::updt_local_params(params_ref const & _p) {
    /* nothing yet */
}

br_status slstar_rewriter_cfg::reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
    TRACE("slstar_rw", tout << "func: " << f->get_name() << std::endl;
                       tout << "args: " << std::endl;);
    
    switch(f->get_decl_kind()) {
        case OP_SLSTAR_LIST:
            result = m_manager.mk_eq(m_conv.mk_fresh_array("X"), m_conv.mk_fresh_array("Y"));
            return BR_DONE;
        case OP_SLSTAR_ALPHA:
        case OP_SLSTAR_BETA:
        default:
            return default_rewriter_cfg::reduce_app(f, num, args, result, result_pr);
    }
}

template class rewriter_tpl<slstar_rewriter_cfg>;
