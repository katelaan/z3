#include "tactic/tactical.h"
#include "sat/tactic/sat_tactic.h"
#include "smt/tactic/smt_tactic.h"
#include "tactic/portfolio/default_tactic.h"

#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"

#include "ast/slstar_decl_plugin.h"
#include "ast/slstar/slstar_encoder.h"
#include "tactic/slstar/slstar_reduce_tactic.h"
#include "tactic/slstar/slstar_model_converter.h"
#include "tactic/slstar/slstar_spatial_eq_propagation_tactic.h"
#include "tactic/slstar/slstar_bounds.h"

#include <unordered_set>

class slstar_tactic : public tactic {
    struct imp {
        ast_manager &     m;
        slstar_util       util;

        bool              m_proofs_enabled;
        bool              m_produce_models;
        bool              m_produce_unsat_cores;
        params_ref        m_param;
        equality_bin_map_ref equality_bins;

        imp(ast_manager & _m, equality_bin_map_ref eq_bins, params_ref const & p):
            m(_m),
            util(m),
            m_proofs_enabled(false),
            m_produce_models(false),
            m_produce_unsat_cores(false),
            m_param(p),
            equality_bins(eq_bins) { 
            }

        void updt_params(params_ref const & p) {
        }

        void perform_encoding(slstar_encoder & encoder, goal_ref const & g, goal_ref_buffer & result, bool contains_calls) {
            
            goal* goal_tmp = alloc(goal, *g, false);

            expr_ref new_curr(m);
            unsigned size = g->size();
            for (unsigned idx = 0; idx < size; idx++) {
                if (g->inconsistent())
                    break;
                expr * curr = g->form(idx);
                encoder.encode_top(curr, new_curr);

                goal_tmp->assert_expr(new_curr);
            }
            
            // assert the equalness of all substituted locations
            std::unordered_set<equality_bin> seen;
            for(auto it=equality_bins->begin(); it!=equality_bins->end(); ++it) {
                if( seen.find(it->second)!=seen.end()){
                    continue;
                }
                seen.emplace(it->second);
                std::vector<expr*> eq_args;
                //eq_args.reserve(it->second->size());
                for(auto jt = it->second->begin(); jt != it->second->end(); ++jt){
                    eq_args.push_back(encoder.mk_encoded_loc(*jt));
                }
                // e.g. (= x x) -> (= x) invalid
                if(eq_args.size()>=2) {
                    goal_tmp->assert_expr(m.mk_app(m.get_basic_family_id(), OP_EQ, eq_args.size(), &eq_args[0]));
                }

            }

            if(contains_calls) {
                goal_tmp->assert_expr(encoder.mk_global_constraints());
            }

            goal_tmp->inc_depth();

            result.push_back(goal_tmp);
        }

        void release_eq_symbols() {
            // release reference to equality symbols
            std::unordered_set<equality_bin> seen;
            for(auto it=equality_bins->begin(); it!=equality_bins->end(); ++it) {
                if( seen.find(it->second)!=seen.end()){
                    continue;
                }
                seen.emplace(it->second);
                for(auto jt = it->second->begin(); jt != it->second->end(); ++jt){
                    m.dec_ref(*jt);
                }
            }
        }

        void operator()(goal_ref const & g,
                        goal_ref_buffer & result,
                        sort* loc_sort) {
            SASSERT(g->is_well_sorted());
            m_proofs_enabled      = g->proofs_enabled();
            m_produce_models      = g->models_enabled();
            m_produce_unsat_cores = g->unsat_core_enabled();

            result.reset();
            tactic_report report("slstar_reduce", *g);

            TRACE("slstar", tout << "BEFORE: " << std::endl; g->display(tout););

            slstar_bound_computation bc(m, util);
            sl_bounds bd = bc.calc_bounds(g);

            TRACE("slstar-bound", tout << "Bounds:" << 
                " nList " << bd.n_list << 
                " nTree " << bd.n_tree << std::endl; );

            if (g->inconsistent()) {
                result.push_back(g.get());
                return;
            }

            slstar_encoder    encoder(m, loc_sort );           

            static const sl_enc_level levels[] = {SL_LEVEL_UF, SL_LEVEL_FULL};

            for (unsigned i = 0; i<sizeof(levels)/sizeof(sl_enc_level); i++) {                
                encoder.prepare(bd, levels[i]);
                perform_encoding(encoder, g, result, bd.contains_calls);

                
                if (levels[i] != SL_LEVEL_FULL) {
                    goal_ref_buffer tmp_result;
                    goal_ref tmp_goal_in(result[0]);
                    //tactic* t = mk_default_tactic(m,m_param);
                    tactic* t = mk_smt_tactic(m, m_param);
                    (*t)(tmp_goal_in, tmp_result);
                    t->cleanup();
                    SASSERT(tmp_result.size() == 1);

                    if(tmp_result[0]->is_decided_unsat()) {
                        result.reset();
                        result.append(tmp_result);

                        tmp_result.reset();
                        encoder.clear_enc_dict();
                        release_eq_symbols();
                        return;
                    }
                    tmp_result.reset();
                    result.reset();
                }
            }

            encoder.clear_enc_dict();
            release_eq_symbols();

            SASSERT(g->is_well_sorted());

            if (g->models_enabled() && !g->inconsistent()) {
                slstar_model_converter* mc = alloc(slstar_model_converter, m, encoder);
                TRACE("slstar", tout << "AFTER: " << std::endl; result[0]->display(tout);
                            if (mc) mc->display(tout); tout << std::endl; );
            }
        }
    };

    imp *      m_imp;
    params_ref m_params;

    ast_manager           & m;
    equality_bin_map_ref    equality_bins;

public:
    slstar_tactic(ast_manager & m, equality_bin_map_ref eq_bins, params_ref const & p):
        m_params(p),
        m(m),
        equality_bins(eq_bins)
    {
        m_imp = alloc(imp, m, eq_bins, p );
    }

    tactic * translate(ast_manager & m) override {
        return alloc(slstar_tactic, m, equality_bin_map_ref( new equality_bin_map() ), m_params);
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
                    goal_ref_buffer & result) override {
        try {
            (*m_imp)(in, result, slstar_decl_plugin::get_loc_sort(&m));
        }
        catch (rewriter_exception & ex) {
            throw tactic_exception(ex.msg());
        }
    }

    void cleanup() override {
        imp * d = alloc(imp, m_imp->m, equality_bins, m_params);
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

tactic * mk_slstar_tactic(ast_manager & m, equality_bin_map_ref eq_bins, params_ref const & p) {
    return clean(alloc(slstar_tactic, m, eq_bins, p));
}

tactic * mk_slstar_reduce_tactic(ast_manager & m, params_ref const & p) {
    TRACE("slstar", p.display(tout););
    bool propeqs = p.get_bool("slstar.propagateeqs", false);
    TRACE("slstar",  tout << "Will propagate equalities: " << propeqs;);

    std::shared_ptr<equality_bin_map> equalities( new equality_bin_map() );

    tactic * st = and_then( /*mk_simplify_tactic(m, p),
                            mk_propagate_values_tactic(m, p),*/
                            mk_slstar_spatial_eq_propagation_tactic(m, equalities),
                            mk_slstar_tactic(m, equalities, p),
                            mk_propagate_values_tactic(m, p),
                            mk_default_tactic(m, p));

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
                goal_ref_buffer & result) override {
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
