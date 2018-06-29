#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/bv/bit_blaster_tactic.h"
#include "sat/tactic/sat_tactic.h"
#include "smt/tactic/smt_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "ackermannization/ackermannize_bv_tactic.h"
#include "tactic/arith/probe_arith.h"
#include "tactic/smtlogics/qfnra_tactic.h"

#include "tactic/slstar/slstar_reduce_tactic.h"

class slstar_tactic : public tactic {
    struct imp {
        ast_manager &     m;
        //fpa2bv_converter  m_conv;
        //fpa2bv_rewriter   m_rw;
        unsigned          m_num_steps;

        bool              m_proofs_enabled;
        bool              m_produce_models;
        bool              m_produce_unsat_cores;

        imp(ast_manager & _m, params_ref const & p):
            m(_m),
            //m_conv(m),
            //m_rw(m, m_conv, p),
            m_proofs_enabled(false),
            m_produce_models(false),
            m_produce_unsat_cores(false) {
            }

        void updt_params(params_ref const & p) {
           // m_rw.cfg().updt_params(p);
        }

        void operator()(goal_ref const & g,
                        goal_ref_buffer & result,
                        model_converter_ref & mc,
                        proof_converter_ref & pc,
                        expr_dependency_ref & core) {
            SASSERT(g->is_well_sorted());
            m_proofs_enabled      = g->proofs_enabled();
            m_produce_models      = g->models_enabled();
            m_produce_unsat_cores = g->unsat_core_enabled();

            mc = nullptr; pc = nullptr; core = nullptr; result.reset();
            tactic_report report("fpa2bv", *g);
            //m_rw.reset();

            TRACE("fpa2bv", tout << "BEFORE: " << std::endl; g->display(tout););

            if (g->inconsistent()) {
                result.push_back(g.get());
                return;
            }

            m_num_steps = 0;
            expr_ref   new_curr(m);
            proof_ref  new_pr(m);
            unsigned size = g->size();
            for (unsigned idx = 0; idx < size; idx++) {
                if (g->inconsistent())
                    break;
                expr * curr = g->form(idx);
                //m_rw(curr, new_curr, new_pr);
                //m_num_steps += m_rw.get_num_steps();
                if (m_proofs_enabled) {
                    proof * pr = g->pr(idx);
                    new_pr     = m.mk_modus_ponens(pr, new_pr);
                }
                g->update(idx, new_curr, new_pr, g->dep(idx));

                if (is_app(new_curr)) {
                    const app * a = to_app(new_curr.get());
                    /*if (a->get_family_id() == m_conv.fu().get_family_id() &&
                        a->get_decl_kind() == OP_FPA_IS_NAN) {
                        // Inject auxiliary lemmas that fix e to the one and only NaN value,
                        // that is (= e (fp #b0 #b1...1 #b0...01)), so that the value propagation
                        // has a value to propagate.
                        expr * sgn, *sig, *exp;
                        m_conv.split_fp(new_curr, sgn, exp, sig);
                        result.back()->assert_expr(m.mk_eq(sgn, m_conv.bu().mk_numeral(0, 1)));
                        result.back()->assert_expr(m.mk_eq(exp, m_conv.bu().mk_bv_neg(m_conv.bu().mk_numeral(1, m_conv.bu().get_bv_size(exp)))));
                        result.back()->assert_expr(m.mk_eq(sig, m_conv.bu().mk_numeral(1, m_conv.bu().get_bv_size(sig))));
                    }*/
                }
            }

            //if (g->models_enabled())
            //    mc = mk_fpa2bv_model_converter(m, m_conv);

            g->inc_depth();
            result.push_back(g.get());

            //for (unsigned i = 0; i < m_conv.m_extra_assertions.size(); i++)
            //    result.back()->assert_expr(m_conv.m_extra_assertions[i].get());

            SASSERT(g->is_well_sorted());
            TRACE("fpa2bv", tout << "AFTER: " << std::endl; g->display(tout);
                            if (mc) mc->display(tout); tout << std::endl; );
        }
    };

    imp *      m_imp;
    params_ref m_params;

public:
    slstar_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(slstar_tactic, m, m_params);
    }

    ~slstar_tactic() override {
        dealloc(m_imp);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
        m_imp->updt_params(p);
    }

    void collect_param_descrs(param_descrs & r) override {
    }

    void operator()(goal_ref const & in,
                    goal_ref_buffer & result,
                    model_converter_ref & mc,
                    proof_converter_ref & pc,
                    expr_dependency_ref & core) override {
        /*try {
            (*m_imp)(in, result, mc, pc, core);
        }
        catch (rewriter_exception & ex) {
            throw tactic_exception(ex.msg());
        }*/
    }

    void cleanup() override {
        imp * d = alloc(imp, m_imp->m, m_params);
        std::swap(d, m_imp);
        dealloc(d);
    }

};

struct is_non_slstar_predicate {
    struct found {};
    ast_manager & m;
    bv_util       bu;
    fpa_util      fu;
    arith_util    au;

    is_non_slstar_predicate(ast_manager & _m) : m(_m), bu(m), fu(m), au(m) {}

    void operator()(var *) { throw found(); }

    void operator()(quantifier *) { throw found(); }

    void operator()(app * n) {
        sort * s = get_sort(n);
        if (!m.is_bool(s) && !fu.is_float(s) && !fu.is_rm(s) && !bu.is_bv_sort(s) && !au.is_real(s))
            throw found();
        family_id fid = n->get_family_id();
        if (fid == m.get_basic_family_id())
            return;
        if (fid == fu.get_family_id() || fid == bu.get_family_id())
            return;
        if (is_uninterp_const(n))
            return;
        if (au.is_real(s) && au.is_numeral(n))
            return;

        throw found();
    }
};

class is_slstar_probe : public probe {
public:
    result operator()(goal const & g) override {
        //return !test<is_non_slstar_predicate>(g);
        result r(false);
        return r;
    }

    ~is_slstar_probe() override {}
};

probe * mk_is_slstar_probe() {
    return alloc(is_slstar_probe);
}

tactic * mk_slstar_reduce_tactic(ast_manager & m, params_ref const & p) {
    //params_ref simp_p = p;
    //simp_p.set_bool("arith_lhs", true);
    //simp_p.set_bool("elim_and", true);
//
    //tactic * preamble = and_then(mk_simplify_tactic(m, simp_p),
    //                             mk_propagate_values_tactic(m, p),
    //                             mk_fpa2bv_tactic(m, p),
    //                             mk_propagate_values_tactic(m, p),
    //                             using_params(mk_simplify_tactic(m, p), simp_p),
    //                             if_no_proofs(if_no_unsat_cores(mk_ackermannize_bv_tactic(m, p))));
//
    //tactic * st = and_then(preamble,
    //                       mk_bit_blaster_tactic(m, p),
    //                       using_params(mk_simplify_tactic(m, p), simp_p),
    //                       cond(mk_is_propositional_probe(),
    //                            cond(mk_produce_proofs_probe(),
    //                                 mk_smt_tactic(p), // `sat' does not support proofs.
    //                                 mk_sat_tactic(m, p)),
    //                            cond(mk_is_fp_qfnra_probe(),
    //                                 mk_qfnra_tactic(m, p),
    //                                 mk_smt_tactic(p))));
//
    //st->updt_params(p);
    return clean(alloc(slstar_tactic, m, p));
}