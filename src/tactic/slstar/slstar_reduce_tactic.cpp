#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/bv/bit_blaster_tactic.h"
#include "sat/tactic/sat_tactic.h"
#include "smt/tactic/smt_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "ackermannization/ackermannize_bv_tactic.h"
#include "tactic/arith/probe_arith.h"
#include "tactic/smtlogics/qfnra_tactic.h"

#include "ast/slstar_decl_plugin.h"
#include "ast/slstar/slstar_rewriter.h"
#include "ast/slstar/slstar_converter.h"
#include "tactic/slstar/slstar_reduce_tactic.h"

#include <set>

class slstar_tactic : public tactic {
    struct bounds {
        int m_list = -1;
        int m_tree = -1;
        int n_list = -1;
        int n_tree = -1;

        bool is_def() {
            return (m_list != -1) && (n_list != -1) && (m_list != -1) && (n_list != -1);
        }

        void define() {
            m_list = 0;
            m_tree = 0;
            n_list = 0;
            n_tree = 0;
        }
    };

    struct imp {
        ast_manager &     m;
        slstar_util       util;
        slstar_converter  m_conv;
        slstar_rewriter   m_rw;
        unsigned          m_num_steps;

        bool              m_proofs_enabled;
        bool              m_produce_models;
        bool              m_produce_unsat_cores;

        imp(ast_manager & _m, params_ref const & p):
            m(_m),
            util(m),
            m_conv(m, util),
            m_rw(m, m_conv, p),
            m_proofs_enabled(false),
            m_produce_models(false),
            m_produce_unsat_cores(false) {
            }

        void updt_params(params_ref const & p) {
            m_rw.cfg().updt_params(p);
        }

        bounds calc_bounds(goal_ref const & g) {
            bounds ret = noncall_conjunct_bounds(g);
            if( !ret.is_def() ) {
                // compute normal bounds
            }
            return ret;
        }
 
        bounds noncall_conjunct_bounds(goal_ref const & g) {
            bounds ret;
            expr * conj;
            // Each top level assertion is a conjunct
            // if one of them is free of predicate calls (tree/list) it implicitly gives us the bound
            for (unsigned int i = 0; i < g->size(); i++) {
                conj = g->form(i);
                if(noncall_conjunct_bounds(conj,conj)){
                    if(conj != nullptr) {
                        //calculate ret
                        count_src_symbols(conj, &ret);
                        return ret; //TODOsl possible opt. minimum, all bounds must be equal or it's unsat
                    }
                }
            }
            
            return ret;
        }

        void count_src_symbols(expr * ex, bounds * ret){
            std::set<std::string> alloced_const;

            ret->define();

            std::list<expr*> atoms;
            util.get_spatial_atoms(&atoms,ex);

            for(auto it = atoms.begin(); it != atoms.end(); it++){
                SASSERT(!util.is_call(*it));
                if(util.is_pto(*it)) {
                    app * t = to_app(*it);
                    SASSERT( t->get_num_args() >= 1 );
                    expr * src = t->get_arg(0);
                    SASSERT( is_app(src) );
                    func_decl * d = to_app(src)->get_decl();
                    // for each unique allocated constant increment bound by location sort
                    if(alloced_const.find(d->get_name().str()) == alloced_const.end() ){
                        alloced_const.insert( d->get_name().str() );
                        if(util.is_listloc(get_sort(src))){
                            ret->n_list++;
                        } else if(util.is_treeloc(get_sort(src))) {
                            ret->n_tree++;
                        } else {
                            SASSERT(false);
                        }
                    }
                }
            }
        }

        bool noncall_conjunct_bounds(expr * in, expr *& out ) {
            if(in->get_kind() != AST_APP )
                return false;
            app * t = to_app(in);

            // ignore negations and disjucts
            if(m.is_not(t) || m.is_or(t)){
                return false;
            }
            // further explore ands
            if(m.is_and(t)){
                expr * conj;
                for(unsigned int i=0; i<t->get_num_args(); i++){
                    conj = t->get_arg(i);
                    if(noncall_conjunct_bounds(conj,out) && out != nullptr){
                        return true;
                    }
                }
                out = nullptr;
                return false;
            }
            // in is either spatial atom or spatial form
            // if one of the spatial atom of the spatial form is a call, ignore (i.e. reuturn true and nullptr) ...
            std::list<expr*> atoms;
            util.get_spatial_atoms( &atoms, in );
            for(auto it = atoms.begin(); it != atoms.end(); it++){
                if(util.is_call(*it)){
                    out = nullptr;
                    return true;
                }
            }
            // ... if not use the expr for calculating bound
            out = in;
            return true;
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
            tactic_report report("slstar_reduce", *g);
            m_rw.reset();

            TRACE("slstar", tout << "BEFORE: " << std::endl; g->display(tout););

            bounds bd = calc_bounds(g);

            TRACE("slstar-bound", tout << "Bounds:" << 
                " mList " << bd.m_list << 
                " nList " << bd.n_list << 
                " mTree " << bd.m_tree << 
                " nTree " << bd.n_tree << std::endl; );

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
                m_rw(curr, new_curr, new_pr);
                m_num_steps += m_rw.get_num_steps();
                if (m_proofs_enabled) {
                    proof * pr = g->pr(idx);
                    new_pr     = m.mk_modus_ponens(pr, new_pr);
                }
                g->update(idx, new_curr, new_pr, g->dep(idx));

                if (is_app(new_curr)) {
                    //const app * a = to_app(new_curr.get());
                    //if (a->get_family_id() == m_conv.fu().get_family_id() &&
                    //    a->get_decl_kind() == OP_FPA_IS_NAN) {
                    //     Inject auxiliary lemmas that fix e to the one and only NaN value,
                    //     that is (= e (fp #b0 #b1...1 #b0...01)), so that the value propagation
                    //     has a value to propagate.
                    //    expr * sgn, *sig, *exp;
                    //    m_conv.split_fp(new_curr, sgn, exp, sig);
                    //    result.back()->assert_expr(m.mk_eq(sgn, m_conv.bu().mk_numeral(0, 1)));
                    //    result.back()->assert_expr(m.mk_eq(exp, m_conv.bu().mk_bv_neg(m_conv.bu().mk_numeral(1, m_conv.bu().get_bv_size(exp)))));
                    //    result.back()->assert_expr(m.mk_eq(sig, m_conv.bu().mk_numeral(1, m_conv.bu().get_bv_size(sig))));
                    //}
                }
            }

            //if (g->models_enabled())
            //    mc = mk_slstar_model_converter(m, m_conv);

            g->inc_depth();
            result.push_back(g.get());

            //for (unsigned i = 0; i < m_conv.m_extra_assertions.size(); i++)
            //    result.back()->assert_expr(m_conv.m_extra_assertions[i].get());

            SASSERT(g->is_well_sorted());
            TRACE("slstar", tout << "AFTER: " << std::endl; g->display(tout);
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
        try {
            (*m_imp)(in, result, mc, pc, core);
        }
        catch (rewriter_exception & ex) {
            throw tactic_exception(ex.msg());
        }
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

tactic * mk_slstar_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(slstar_tactic, m, p));
}

tactic * mk_slstar_reduce_tactic(ast_manager & m, params_ref const & p) {
    params_ref simp_p = p;
    simp_p.set_bool("arith_lhs", true);
    simp_p.set_bool("elim_and", true);

    tactic * preamble = and_then(mk_simplify_tactic(m, simp_p),
                                 mk_propagate_values_tactic(m, p),
                                 mk_slstar_tactic(m, p),
                                 mk_propagate_values_tactic(m, p),
                                 using_params(mk_simplify_tactic(m, p), simp_p),
                                 if_no_proofs(if_no_unsat_cores(mk_ackermannize_bv_tactic(m, p))));

    tactic * st = and_then(preamble,
                           mk_bit_blaster_tactic(m, p),
                           using_params(mk_simplify_tactic(m, p), simp_p),
                           cond(mk_is_propositional_probe(),
                                cond(mk_produce_proofs_probe(),
                                     mk_smt_tactic(p), // `sat' does not support proofs.
                                     mk_sat_tactic(m, p)),
                                mk_smt_tactic(p))
                    );

    st->updt_params(p);
    return st;
}




//Debug code
class print_tactic : public tactic {
    public:
    print_tactic(){
        name = "unnamed";
    }
    std::string name;
    void setName(std::string _name){
        name = _name;
    }
    void operator()(goal_ref const & g,
                goal_ref_buffer & result,
                model_converter_ref & mc,
                proof_converter_ref & pc,
                expr_dependency_ref & core) {
        std::cout << "-" << name << "-" << std::endl;
        g->display(std::cout);
        std::cout << "-------" << std::endl;
        
        result.push_back(g.get());
    }
    void cleanup() override {}
    tactic * translate(ast_manager & m) override {
        return alloc(print_tactic);
        //return this;
    }
};

tactic * mk_print_tactic(std::string name) {
    print_tactic* pt = alloc(print_tactic);
    pt->setName(name);
    return pt;
}
