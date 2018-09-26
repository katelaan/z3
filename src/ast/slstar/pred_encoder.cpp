#include "ast/slstar/pred_encoder.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_smt2_pp.h"
#include "ast/slstar/slstar_encoder.h"

pred_encoder::pred_encoder(slstar_encoder & enc) : enc(enc), m(enc.m){
}

pred_encoder::~pred_encoder(){}

app * pred_encoder::mk_isstop(expr * xenc, std::vector<expr*> & stops) {
    std::vector<app*> orargs;
    orargs.push_back( m.mk_eq(xenc, enc.enc_null ) );
    for(unsigned i=0; i<stops.size(); i++) {
        orargs.push_back( m.mk_eq(xenc, stops[i]));
    }
    if(orargs.size()==1) {
        return orargs[0];
    } else if(orargs.size() == 0) {
        return m.mk_false();
    } else {
        return m.mk_or(orargs.size(), (expr * const *) &orargs[0]);
    }
}

app * pred_encoder::mk_reach1(expr * Z, 
        std::vector<func_decl*> & prev_reach, 
        std::vector<expr*> & xlocs, 
        std::vector<expr*> & stops) 
{
    sort * const domain[] = {enc.m_loc_sort, enc.m_loc_sort};
    func_decl * reach = m.mk_fresh_func_decl(slstar_encoder::reach_prefix.c_str(), 2, domain, m.mk_bool_sort());
    
    std::vector<expr*> andargs;
    for(unsigned i=0; i<xlocs.size(); i++) {
        for(unsigned j=0; j<xlocs.size(); j++) {
            //if (i==j) continue; TODOsl?
            expr * tmp = m.mk_and(enc.mk_is_element(xlocs[i], Z), m.mk_not(mk_isstop(xlocs[j], stops)), mk_is_successor(xlocs[i], xlocs[j]) );
            expr * reachargs[] = {xlocs[i], xlocs[j]};
            andargs.push_back( m.mk_iff(m.mk_app(reach, reachargs), tmp));
        }
    }
    prev_reach.push_back(reach);
    return m.mk_and(andargs.size(), &andargs[0]);
}
app * pred_encoder::mk_reachN(std::vector<func_decl*> & prev_reach, std::vector<expr*> & xlocs) {
    sort * const domain[] = {enc.m_loc_sort, enc.m_loc_sort};
    func_decl * reach = m.mk_fresh_func_decl(slstar_encoder::reach_prefix.c_str(), 2, domain, m.mk_bool_sort());
    func_decl * preach = prev_reach[prev_reach.size()-1];
    func_decl * reach1 = prev_reach[0];

    std::vector<expr*> andargs;
    for(unsigned i=0; i<xlocs.size(); i++) {
        for(unsigned j=0; j<xlocs.size(); j++) {
            //if (i==j) continue; TODOsl?
            std::vector<expr*> orargs;
            for(unsigned k=0; k<xlocs.size(); k++) {
                expr * preachargs[] = {xlocs[i], xlocs[k]};
                expr * reach1args[] = {xlocs[k], xlocs[j]};
                orargs.push_back( m.mk_and(m.mk_app(preach, preachargs), m.mk_app(reach1, reach1args) ) );
            }
            
            expr * reachargs[] = {xlocs[i], xlocs[j]};
            orargs.push_back( m.mk_app(preach, reachargs));
            expr * tmp = m.mk_or(orargs.size(), &orargs[0]);
            andargs.push_back( m.mk_iff(m.mk_app(reach, reachargs), tmp));
        }
    }
    prev_reach.push_back(reach);
    return m.mk_and(andargs.size(), &andargs[0]);
}

app * pred_encoder::mk_reachability( expr * Z, std::vector<func_decl*> & prev_reach, std::vector<expr*> & stops, std::vector<expr*> xlocs, int bound) {
    std::vector<expr*> andargs;
    if(bound > 0)
        andargs.push_back( mk_reach1(Z, prev_reach, xlocs, stops));
    for(int i=1; i<bound; i++){
        andargs.push_back( mk_reachN(prev_reach, xlocs));
    }
    SASSERT( prev_reach.size() ==  andargs.size() );
    SASSERT( bound == (int) andargs.size() );
    return m.mk_and( bound, &andargs[0]);
}

app * pred_encoder::mk_emptyZ(expr * xenc, std::vector<expr*> & xlocs, std::vector<expr*> & stops) {
    std::vector<expr*> andargs;
    for(unsigned i=0; i<xlocs.size(); i++) {
        andargs.push_back( m.mk_not(m.mk_eq(xenc,xlocs[i])) );
    }
    return m.mk_or( mk_isstop(xenc, stops), m.mk_and(andargs.size(), &andargs[0]) );
}
app * pred_encoder::mk_footprint(expr * xenc, 
    expr * Z, 
    std::vector<expr*> & xlocs, 
    std::vector<func_decl*> & prev_reach, 
    std::vector<expr*> & stops) 
{
    std::vector<expr*> andargs;
    for(unsigned i=0; i<xlocs.size(); i++) {
        func_decl * rN = prev_reach[prev_reach.size()-1];
        expr * reachargs[] = {xenc, xlocs[i]};
        andargs.push_back( m.mk_iff(enc.mk_is_element(xlocs[i], Z), 
            m.mk_or(
                m.mk_eq(xenc, xlocs[i]), 
                m.mk_app(rN, reachargs))) );
    }

    return m.mk_and( 
        enc.mk_subset_eq(Z, enc.mk_set_from_elements(&xlocs[0], xlocs.size())),
        m.mk_implies(mk_emptyZ(xenc,xlocs, stops), enc.mk_is_empty(Z)),
        m.mk_implies(m.mk_not(mk_emptyZ(xenc,xlocs, stops)),  // TODOsl cache emptyZ?
            m.mk_and(andargs.size(), &andargs[0]) ) );
}

app * pred_encoder::mk_structure(expr * xenc, 
    expr * Z, 
    std::vector<expr*> & xlocs, 
    std::vector<func_decl*> & prev_reach, 
    std::vector<expr*> & stops) 
{
    expr * reachable;
    //if(enc.bounds.n_tree == 0){
    //    reachable = m.mk_false();
    //} else {
        func_decl * rN = prev_reach[prev_reach.size()-1];
        expr * reachargs[] = {xenc, xenc};
        reachable = m.mk_app(rN, reachargs);
    //}
    
    return m.mk_and(
        m.mk_implies(m.mk_not(mk_isstop(xenc, stops)), enc.mk_is_element(xenc,Z)),
        mk_oneparent(Z,xlocs),
        m.mk_not(reachable));
}

app * pred_encoder::mk_stopseq(expr * xenc, std::vector<expr*> & stops) {
    std::vector<expr*> andargs;
    for(unsigned i=0; i<stops.size(); i++) {
        andargs.push_back( m.mk_eq(xenc, stops[i]));
    }
    expr * tmp = m.mk_and(andargs.size(), &andargs[0]);
    andargs.clear();

    for(unsigned i=0; i<stops.size(); i++) {
        for(unsigned j=0; j<i; j++) {
            andargs.push_back( m.mk_not(m.mk_eq(stops[i], stops[j])));
        }
    }
    andargs.push_back(m.mk_implies(mk_isstop(xenc,stops), tmp));
    return m.mk_and(andargs.size(), &andargs[0]);
}


app * pred_encoder::mk_stopsoccur(expr * xenc, expr * Z, std::vector<expr*> & xlocs, std::vector<expr*> & stops ) {
    std::vector<expr*> andargs, orargs;
    for(unsigned i=0; i<stops.size(); i++) {
        for(unsigned p=0; p<xlocs.size(); p++) {
            orargs.push_back( m.mk_and(enc.mk_is_element(xlocs[p],Z), mk_is_successor(xlocs[p], stops[i]) ) );
        }
        andargs.push_back(m.mk_or(orargs.size(), &orargs[0]));
        orargs.clear();
    }
    return m.mk_implies( m.mk_not(mk_isstop(xenc, stops)), m.mk_and(andargs.size(), &andargs[0]));
}

app * pred_encoder::mk_Rn_f(func_decl * f, func_decl * rn, expr * x, expr * y, expr * Z) {
    expr * reachargs[] = {m.mk_app(f,x),y};
    return m.mk_or(
        m.mk_eq(m.mk_app(f,x), y),
        m.mk_and(
            enc.mk_is_element(m.mk_app(f,x), Z), 
            m.mk_app(rn,reachargs)));
}

app * pred_encoder::mk_fstop(expr * xp, expr * s, func_decl * f, expr * Z, std::vector<expr*> & xlocs, 
        std::vector<func_decl*> & prev_reach) 
{
    func_decl * rN = prev_reach[prev_reach.size()-1];
    std::vector<expr*> orargs;
    orargs.push_back(m.mk_eq( m.mk_app(f, xp), s ));
    for(unsigned c=0; c<xlocs.size(); c++) {
        orargs.push_back( m.mk_and( 
            mk_Rn_f(f,rN,xp,xlocs[c],Z),
            enc.mk_is_element(xlocs[c],Z), 
            mk_is_successor(xlocs[c], s) ) );
    }
    return m.mk_or(orargs.size(), &orargs[0]);;
}

app * pred_encoder::mk_is_location(expr* xenc, std::vector<expr*> & xlocs){
    return enc.mk_is_element(xenc, enc.mk_set_from_elements(&xlocs[0], xlocs.size()));
}

app * pred_encoder::mk_bdata(expr * Pcont, expr * Z, func_decl * f, 
    std::vector<expr*> & xlocs, std::vector<func_decl*> & prev_reach) 
{
    app * P = to_app(to_app(Pcont)->get_arg(0));
    func_decl * Pdecl = P->get_decl();
    func_decl * rn = prev_reach[prev_reach.size()-1];
    std::vector<expr*> andargs;
    for(unsigned i=0; i<xlocs.size(); i++) {
        for(unsigned j=0; j<xlocs.size(); j++) {
            std::vector<expr*> pargs;
            for(unsigned k=0; k < P->get_num_args(); k++){
                expr* arg = P->get_arg(k);
                if(enc.util.is_alpha(arg)){
                    app * t = to_app(arg);
                    pargs.push_back(m.mk_app(enc.get_f_dat(t->get_decl()->get_range()), xlocs[i]));
                } else if(enc.util.is_beta(arg)) {
                    app * t = to_app(arg);
                    pargs.push_back(m.mk_app(enc.get_f_dat(t->get_decl()->get_range()), xlocs[j]));
                } else {
                    pargs.push_back(arg);
                }
            }
            andargs.push_back( m.mk_implies( 
                m.mk_and(
                    enc.mk_is_element(xlocs[i], Z),
                    enc.mk_is_element(xlocs[j], Z),
                    mk_Rn_f(f,rn,xlocs[i], xlocs[j], Z)),
                m.mk_app(Pdecl, pargs.size(), &pargs[0]) ));
        }
    }
    return m.mk_and(andargs.size(), &andargs[0]);
}

app * pred_encoder::mk_udata(expr * Pcont, expr * Z, std::vector<expr*> & xlocs) {
    app * P = to_app(to_app(Pcont)->get_arg(0));
    func_decl * Pdecl = P->get_decl();
    std::vector<expr*> andargs;
    for(unsigned i=0; i < xlocs.size(); i++) {
        std::vector<expr*> pargs;
        for(unsigned k=0; k < P->get_num_args(); k++){
            expr* arg = P->get_arg(k);
            if(enc.util.is_alpha(arg)){
                app * t = to_app(arg);
                pargs.push_back(m.mk_app(enc.get_f_dat(t->get_decl()->get_range()), xlocs[i]));
            } else {
                pargs.push_back(arg);
            }
        }
        andargs.push_back( m.mk_implies( 
            enc.mk_is_element(xlocs[i], Z),
            m.mk_app(Pdecl, pargs.size(), &pargs[0]) ));
    }
    return m.mk_and(andargs.size(), &andargs[0]);
}