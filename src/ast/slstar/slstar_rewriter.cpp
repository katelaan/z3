#include "ast/slstar/slstar_rewriter.h"


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