#include "ast/slstar/list_encoder.h"

list_encoder::list_encoder(slstar_encoder & enc) : pred_encoder(enc) {}

app * list_encoder::mk_is_successor(expr * x, expr * y) {
    expr* f_next_x = m.mk_app(enc.f_next,x);
    return m.mk_eq(f_next_x,y);
}

app * list_encoder::mk_defineY(sl_enc * e, expr * Z) {
    std::vector<expr*> andargs;
    andargs.push_back(m.mk_eq(e->Yd, Z));
    andargs.push_back(enc.mk_is_empty(e->Yl));
    andargs.push_back(enc.mk_is_empty(e->Yr));
    andargs.push_back(m.mk_eq(e->Yn, Z));
    return m.mk_and(andargs.size(), &andargs[0]);
}

app * list_encoder::mk_all_succs_different(expr * xi, expr * xj) {
    return m.mk_implies(
        m.mk_eq(m.mk_app(enc.f_next,xi), m.mk_app(enc.f_next,xj) ),
        m.mk_eq(m.mk_app(enc.f_next,xi), enc.enc_null));
}

app * list_encoder::mk_oneparent(expr * Z, std::vector<expr*> & xlocs) {
    std::vector<expr*> andargs;
    for(unsigned i = 0; i<xlocs.size(); i++) {
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

app * list_encoder::mk_stopleaves(expr * Z, std::vector<expr*> & xlocs, std::vector<expr*> & stops ){
    std::vector<expr*> andargs;
    for(unsigned i=0; i<xlocs.size(); i++ ) {
        andargs.push_back(m.mk_implies(
            m.mk_and(enc.mk_is_element(xlocs[i], Z), m.mk_not(enc.mk_is_element(m.mk_app(enc.f_next, xlocs[i]),Z)) ), 
            mk_isstop(m.mk_app(enc.f_next, xlocs[i]), stops)));
    }
    return m.mk_and(andargs.size(), &andargs[0]);
}