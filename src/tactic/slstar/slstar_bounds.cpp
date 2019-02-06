#include "tactic/goal.h"
#include "tactic/slstar/slstar_bounds.h"

#define MIN(a,b) ((a) < (b) ? (a) : (b))
#define MAX(a,b) ((a) > (b) ? (a) : (b))

slstar_bound_computation::slstar_bound_computation(ast_manager & m, slstar_util& util) : m(m), util(util) {

}

sl_bounds slstar_bound_computation::calc_bounds(goal_ref const & g) {
    sl_bounds ret = noncall_conjunct_bounds(g);
    if( !ret.is_def() ) {
        // compute normal bounds
        ret.define();
        calc_spatial_bounds(g, ret);
    }
    return ret;
}

sl_bounds slstar_bound_computation::noncall_conjunct_bounds(goal_ref const & g) {
    sl_bounds ret;
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

void slstar_bound_computation::count_src_symbols(expr * ex, sl_bounds * ret) {
    std::set<std::string> alloced_const;

    ret->define();

    std::list<expr*> atoms;
    util.get_spatial_atoms(&atoms,ex);

    for(auto it = atoms.begin(); it != atoms.end(); ++it){
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
                } else if(util.is_null(src)){
                    // ignore // TODOsl
                } else {
                    SASSERT(false);
                }
            }
        }
    }
}

void slstar_bound_computation::count_non_null_const(sl_bounds & ret, std::list<expr*> & consts) {
    std::unordered_set<std::string> tconst;
    std::unordered_set<std::string> lconst;

    for(auto it = consts.begin(); it != consts.end(); ++it){
        SASSERT( is_app(*it));
        app * t = to_app(*it);
        func_decl * d = to_app(t)->get_decl();

        if(util.is_listconst(*it)){
            if(lconst.find(d->get_name().str()) == lconst.end() ){
                lconst.insert( d->get_name().str() );
                ret.n_list++;
            }
        } else if (util.is_treeconst(*it)) {
            if(tconst.find(d->get_name().str()) == tconst.end() ){
                tconst.insert( d->get_name().str() );
                ret.n_tree++;
            }
        }
    }
}

bool slstar_bound_computation::noncall_conjunct_bounds(expr * in, expr *& out) {
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
    for(auto it = atoms.begin(); it != atoms.end(); ++it){
        if(util.is_call(*it)){
            out = nullptr;
            return true;
        }
    }
    // ... if not use the expr for calculating bound
    out = in;
    return true;
}

void slstar_bound_computation::calc_spatial_bounds(goal_ref const & g, sl_bounds & ret) {
    for (unsigned int i = 0; i < g->size(); i++) {
        expr * ex = g->form(i);
        SASSERT(is_app(ex));
        app * t = to_app(ex);
        sl_bounds tmp;
        tmp.define();

        calc_bounds_spatial(tmp,t);     

        calc_bounds_max(ret, tmp);
    }
}

void slstar_bound_computation::calc_bounds_max(sl_bounds & a_ret, sl_bounds & b) {
    a_ret.n_list = MAX(a_ret.n_list, b.n_list);
    a_ret.n_tree = MAX(a_ret.n_tree, b.n_tree);
}

void slstar_bound_computation::calc_nondata_bounds_non_spatial(sl_bounds & ret, app * t) {
    expr * arg;
    for(unsigned int i=0; i<t->get_num_args(); i++){
        arg = t->get_arg(i);
        SASSERT(is_app(arg));
        app * argt = to_app(arg);
        sl_bounds tmp;
        tmp.define();
        calc_nondata_bounds_non_spatial(tmp, argt);
        calc_bounds_max(ret, tmp);
    }
}

void slstar_bound_computation::calc_bounds_spatial(sl_bounds & ret, app * t) {
    std::list<expr*> consts;
    util.get_constants(&consts, t);
    count_non_null_const(ret, consts);

    std::list<std::pair<expr*,bool> > atoms; // pair of atom, and bool if the parent is negated
    util.get_spatial_atoms_with_polarity(&atoms, t);
    for(auto it = atoms.begin(); it != atoms.end(); ++it){
        if(util.is_call( (*it).first) ) {
            ret.contains_calls = true;
            if(util.is_list( (*it).first )) { 
                ret.n_list += 1;

                const app * t = to_app( (*it).first );
                int max_dpred_bound = 0;
                for(unsigned int i = 0; i < t->get_num_args(); i++){
                    expr * arg = t->get_arg(i);
                    if( !is_sort_of(get_sort(arg), util.get_family_id(), SLSTAR_DPRED) ){
                        //ret.n_list += t->get_num_args()-i-1;
                        break;
                    } else if( (*it).second ){
                        func_decl * d = to_app(arg)->get_decl();
                        if(d->get_name().str() == "unary"){
                            max_dpred_bound = 1;
                        } else if(d->get_name().str() == "next"){
                            max_dpred_bound = 2;
                            break; //No bigger data predicate bound known
                        } else {
                            //TODOsl throw error;
                        }
                    }
                }
                ret.n_list += max_dpred_bound;
            }
            else if(util.is_tree( (*it).first) ) {
                ret.n_tree += 1;

                const app * t = to_app( (*it).first );
                int max_dpred_bound = 0;
                for(unsigned int i = 0; i < t->get_num_args(); i++){
                    expr * arg = t->get_arg(i);
                    if( !is_sort_of(get_sort(arg), util.get_family_id(), SLSTAR_DPRED) ){
                        ret.n_tree += t->get_num_args()-i-1;
                        break;
                    } else if( (*it).second ){
                        func_decl * d = to_app(arg)->get_decl();
                        if(d->get_name().str() == "unary"){
                            max_dpred_bound = 1;
                        } else if(d->get_name().str() == "left"){
                            max_dpred_bound = 2;
                            break; //No bigger data predicate bound known
                        } else if(d->get_name().str() == "right"){
                            max_dpred_bound = 2;
                            break; //No bigger data predicate bound known
                        } else {
                            //TODOsl throw error;
                        }
                    }
                }
                ret.n_tree += max_dpred_bound;
            } else {
                SASSERT(false); // not supported
            }
        }
    }
}
