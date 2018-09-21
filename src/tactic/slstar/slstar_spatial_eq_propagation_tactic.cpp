#include "slstar_spatial_eq_propagation_tactic.h"
#include "tactic/tactical.h"
#include "sat/tactic/sat_tactic.h"
#include "smt/tactic/smt_tactic.h"
#include "ast/slstar_decl_plugin.h"

#include "ast/rewriter/th_rewriter.h"
#include "ast/ast_smt2_pp.h"
#include "ast/expr_substitution.h"


class slstar_spatial_eq_propagation_tactic : public tactic {

    ast_manager                 & m;
    slstar_util                   util;
    equality_bin_map_ref          equality_bins;

    th_rewriter                   rewriter;
    scoped_ptr<expr_substitution> subst;

    public:

    slstar_spatial_eq_propagation_tactic(ast_manager & m) : slstar_spatial_eq_propagation_tactic(m, equality_bin_map_ref(new equality_bin_map())) {}

    slstar_spatial_eq_propagation_tactic(ast_manager & m, equality_bin_map_ref eq_bins) :
        m(m),
        util(m),
        equality_bins(eq_bins),
        rewriter(m)
    {

    }

    equality_bin get_equality_bin(expr * const * atoms, unsigned num) {
        // try to find a bin
        for(unsigned i=0; i<num; i++){
            app * loc = to_app(atoms[i]);
            func_decl * decl = loc->get_decl();
            auto find = equality_bins->find(decl->get_name().bare_str());
            if(find != equality_bins->end()) {
                return find->second;
            }

        }
        // if there is no bin create new bin
        app * loc = to_app(atoms[num-1]);
        func_decl * decl = loc->get_decl();
        auto new_item = equality_bins->emplace(decl->get_name().bare_str(), equality_bin(new std::set<expr*>()));
        return new_item.first->second;
    }

    void merge_bins(equality_bin& deleted, equality_bin& merge_into) {
        // for all items in deleted bin, set the merged bin as current-bin and append it there
        for(auto it = deleted->begin(); it!=deleted->end(); ++it) {
            app * loc = to_app(*it);
            func_decl * decl = loc->get_decl();
            (*equality_bins)[decl->get_name().bare_str()] = merge_into;
            merge_into->emplace(loc);
        }
        deleted = merge_into;
    }

    void find_equalities(goal_ref const & g) {
        for (unsigned int i = 0; i < g->size(); i++) {
            expr * ex = g->form(i);
            SASSERT(is_app(ex));
            app * t = to_app(ex);

            std::list<std::pair<expr*,bool> > atoms; // pair of atom, and bool if the parent is negated
            util.get_spatial_atoms_with_polarity(&atoms, t);

            for(auto it = atoms.begin(); it != atoms.end(); ++it) {
                // propagating equalities under negation is not sound
                if(it->second){
                    continue;
                }
                if(m.is_eq(it->first)){
                    app * atom = to_app(it->first);
                    unsigned sz = atom->get_num_args();
                    SASSERT(sz > 0);
                    //only propagate location equalities
                    if(!util.is_loc(atom->get_arg(0))) {
                        continue;
                    }
                    equality_bin eq_bin = get_equality_bin(atom->get_args(), sz);
                    for(unsigned i=0; i<sz; i++){
                        app * loc = to_app(atom->get_arg(i));
                        func_decl * decl = loc->get_decl();
                        
                        auto is_new = equality_bins->emplace(decl->get_name().bare_str(), nullptr);
                        if(is_new.second){
                            // if no eq bin pointer is associated yet set it to the current bin
                            is_new.first->second = eq_bin;
                        }
                        // merge bins if we encounter two different
                        if(is_new.first->second.get() != eq_bin.get()){
                            merge_bins(is_new.first->second, eq_bin);
                        }
                        SASSERT( is_new.first->second.get() == eq_bin.get() );
                        eq_bin->emplace(loc);
                        //m.inc_ref(loc);
                    }
                }
                
            }
        }
    }

    void operator()(goal_ref const & g,
                goal_ref_buffer & result,
                model_converter_ref & mc,
                proof_converter_ref & pc,
                expr_dependency_ref & core) 
    {
        find_equalities(g);

        subst = alloc(expr_substitution, m, g->unsat_core_enabled(), g->proofs_enabled());
        rewriter.set_substitution(subst.get());

        std::unordered_set<equality_bin> seen;
        for(auto it=equality_bins->begin(); it!=equality_bins->end(); ++it) {
            if( seen.find(it->second)!=seen.end()){
                continue;
            }
            seen.emplace(it->second);
            app * representative = nullptr;
            for(auto jt = it->second->begin(); jt != it->second->end(); ++jt){
                
                app * loc = to_app(*jt);
                if( representative == nullptr ){
                    representative = loc;
                } else {
                    subst->insert(representative, loc);
                }
                m.inc_ref(loc);
            //    func_decl * decl = loc->get_decl();
            //    std::cout << decl->get_name().bare_str() << ", ";
            }
            //std::cout << std::endl;
        }
        if( !subst->empty() ){
            for (unsigned int i = 0; i < g->size(); i++) {
                expr * ex = g->form(i);
                expr_ref   new_ex(m);
                rewriter(ex, new_ex);
                g->update(i, new_ex);
            }
        }

        g->inc_depth();
        result.push_back(g.get());
        
    }

    void cleanup() override {}

    tactic * translate(ast_manager & m) override {
        return alloc(slstar_spatial_eq_propagation_tactic, m);
    }
};

tactic * mk_slstar_spatial_eq_propagation_tactic(ast_manager & m, equality_bin_map_ref eq_bins, params_ref const & p) {
    return alloc(slstar_spatial_eq_propagation_tactic, m, eq_bins);
}
 
