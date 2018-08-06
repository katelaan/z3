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

bool slstar_rewriter_cfg::pre_visit(expr * t) {
    current = t;
    return true;
}

br_status slstar_rewriter_cfg::reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
    TRACE("slstar_rw", 
        tout << "func: " << f->get_name() << std::endl;
        tout << "args: " << std::endl;
        for(unsigned int i=0; i<num; i++) {
            tout <<  mk_ismt2_pp(args[i], m_manager, 2) << std::endl;
        }
    );
    if(f->get_family_id() == m_conv.util.get_family_id()) {
        switch(f->get_decl_kind()) {
            case OP_SLSTAR_TREE:
            case OP_SLSTAR_LIST:
                m_conv.add_pred(current, args, num);
                break;
                //result = m_manager.mk_eq(m_conv.mk_fresh_array("X"), m_conv.mk_fresh_array("Y"));
                //return BR_DONE;
            case OP_SLSTAR_POINTSTOD:
            case OP_SLSTAR_POINTSTOL:
            case OP_SLSTAR_POINTSTOR:
            case OP_SLSTAR_POINTSTOLR:
            case OP_SLSTAR_POINTSTON:
                m_conv.add_ptox(current, args, num);
                break;
            case OP_SLSTAR_ALPHA:
            case OP_SLSTAR_BETA:
                return default_rewriter_cfg::reduce_app(f, num, args, result, result_pr);
            default:
                SASSERT(false);
        }
    } else if(f->get_family_id() == -1 /* null_family_id*/) {
        switch(f->get_decl_kind()) {
            case OP_AND:
                m_conv.add_and(current, args, num);
                break;
            case OP_OR:
                m_conv.add_or(current, args, num);
                break;
            case OP_BNEG:
                m_conv.add_neg_app(current, args, num);
                break;
            default:
                m_conv.add_app(current, args, num);
        }
    }
    // if is top level:
    // return A & B & m_conv.mk_glob_constr()
    // else 
    return default_rewriter_cfg::reduce_app(f, num, args, result, result_pr);
}

template class rewriter_tpl<slstar_rewriter_cfg>;
