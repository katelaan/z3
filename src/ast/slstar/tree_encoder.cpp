#include "ast/slstar/tree_encoder.h"

tree_encoder::tree_encoder(slstar_encoder & enc) : pred_encoder(enc) {}

app * tree_encoder::mk_is_successor(expr * x, expr * y) {
    expr* f_left_x = m.mk_app(enc.f_left,x);
    expr* f_right_x = m.mk_app(enc.f_right,x);
    return m.mk_or(m.mk_eq(f_left_x,y), m.mk_eq(f_right_x,y));
}

app * tree_encoder::mk_ordered(expr * Z, 
    std::vector<expr*> & xlocs, 
    std::vector<expr*> & stops,
    std::vector<func_decl*> & prev_reach) 
{
    std::vector<expr*> andargs;
    for(int i=0; i< ((int)stops.size())-1; i++) {
        std::vector<expr*> orargs;
        for(unsigned p=0; p<xlocs.size(); p++) {
            orargs.push_back(m.mk_and(
                enc.mk_is_element(xlocs[p], Z),
                mk_fstop(xlocs[p], stops[i], enc.f_left, Z, xlocs, prev_reach),
                mk_fstop(xlocs[p], stops[i+1], enc.f_right, Z, xlocs, prev_reach) ));
        }
        andargs.push_back(m.mk_or(orargs.size(), &orargs[0]));
    }
    return m.mk_and(andargs.size(), &andargs[0]);
}

app * tree_encoder::mk_defineY(sl_enc * e, expr * Z) {
    std::vector<expr*> andargs;
    if(Z!=nullptr){
        andargs.push_back(m.mk_eq(e->Yd, Z));
        if(enc.needs_tree_footprint){
            andargs.push_back(m.mk_eq(e->Yl, Z));
            andargs.push_back(m.mk_eq(e->Yr, Z));
        }
    } else {
        andargs.push_back(enc.mk_is_empty(e->Yd));
        if(enc.needs_tree_footprint){
            andargs.push_back(enc.mk_is_empty(e->Yl));
            andargs.push_back(enc.mk_is_empty(e->Yr));
        }
    }
    if(enc.needs_list_footprint){
        andargs.push_back(enc.mk_is_empty(e->Yn));
    }
    return m.mk_and(andargs.size(), &andargs[0]);
}

app * tree_encoder::mk_all_succs_different(expr * xi, expr * xj) {
    expr * andargs[4];
    andargs[0] = m.mk_implies(
        m.mk_eq(m.mk_app(enc.f_left,xi), m.mk_app(enc.f_left,xj) ),
        m.mk_eq(m.mk_app(enc.f_left,xi), enc.enc_null));

    andargs[1] = m.mk_implies(
        m.mk_eq(m.mk_app(enc.f_right,xi), m.mk_app(enc.f_right,xj) ),
        m.mk_eq(m.mk_app(enc.f_right,xi), enc.enc_null));

    andargs[2] = m.mk_implies(
        m.mk_eq(m.mk_app(enc.f_left,xi), m.mk_app(enc.f_right,xj) ),
        m.mk_eq(m.mk_app(enc.f_left,xi), enc.enc_null));

    andargs[3] = m.mk_implies(
        m.mk_eq(m.mk_app(enc.f_right,xi), m.mk_app(enc.f_left,xj) ),
        m.mk_eq(m.mk_app(enc.f_right,xi), enc.enc_null));
    return m.mk_and(4,andargs);
}


app * tree_encoder::mk_oneparent(expr * Z, std::vector<expr*> & xlocs) {
    std::vector<expr*> andargs;
    for(unsigned i = 0; i<xlocs.size(); i++) {
        std::vector<expr*> andargs2;
        andargs2.push_back(m.mk_implies(
            enc.mk_is_element(xlocs[i], Z),
            m.mk_implies(
                m.mk_eq(m.mk_app(enc.f_left,xlocs[i]), m.mk_app(enc.f_right,xlocs[i])),
                m.mk_eq(m.mk_app(enc.f_left,xlocs[i]), enc.enc_null ) )));
        andargs.push_back( m.mk_and(andargs2.size(), &andargs2[0]));
        
        for(unsigned j = 0; j<xlocs.size(); j++) {
            if(i==j) continue;
            andargs.push_back( m.mk_implies(
                m.mk_and( enc.mk_is_element(xlocs[j], Z), m.mk_not(m.mk_eq(xlocs[i], xlocs[j])) ),
                mk_all_succs_different(xlocs[i], xlocs[j])    
            ));
        }
    }
    return  m.mk_and(andargs.size(), &andargs[0]);
}

app * tree_encoder::mk_stopleaves(expr * Z, std::vector<expr*> & xlocs, std::vector<expr*> & stops ){
    std::vector<expr*> andargs;
    for(unsigned i=0; i<xlocs.size(); i++ ) {
        andargs.push_back(m.mk_implies(
            m.mk_and(enc.mk_is_element(xlocs[i], Z), m.mk_not(enc.mk_is_element(m.mk_app(enc.f_left, xlocs[i]),Z)) ), 
            mk_isstop(m.mk_app(enc.f_left, xlocs[i]), stops)));
        andargs.push_back(m.mk_implies(
            m.mk_and(enc.mk_is_element(xlocs[i], Z), m.mk_not(enc.mk_is_element(m.mk_app(enc.f_right, xlocs[i]),Z)) ), 
            mk_isstop(m.mk_app(enc.f_right, xlocs[i]), stops)));
    }
    return m.mk_and(andargs.size(), &andargs[0]);
}