#include "ast/slstar/list_encoder.h"

list_encoder::list_encoder(slstar_encoder & enc) : pred_encoder(enc) {}

void list_encoder::add_list(expr * ex, expr * const * args, unsigned num, sl_enc_level level) {
    switch(level) {
        case SL_LEVEL_UF:
            add_list_uf(ex,args,num);
            break;
        case SL_LEVEL_FOOTPRINTS:
            
        case SL_LEVEL_FULL:
        default:
            add_list_full(ex,args,num);
    }
}

void list_encoder::add_list_uf(expr * ex, expr * const * args, unsigned num) {
    SASSERT(is_app(ex));
    sl_enc * enc = new sl_enc(m,this->enc, this->enc.needs_tree_footprint, this->enc.needs_list_footprint);
    enc->mk_fresh_Y();
    enc->is_spatial = true;

    enc->A = ex;
    enc->B = m.mk_true();

    enc->inc_ref();
    enc->level = SL_LEVEL_UF;
    this->enc.encoding[ex] = enc;
}

void list_encoder::add_list_full(expr * ex, expr * const * args, unsigned num) {
    SASSERT(is_app(ex));
    sl_enc * enc = new sl_enc(m,this->enc, this->enc.needs_tree_footprint, this->enc.needs_list_footprint);
    enc->mk_fresh_Y();
    enc->is_spatial = true;
    enc->level = SL_LEVEL_FULL;

    expr * xenc;

    std::vector<func_decl*> prev_reach;
    std::vector<expr*> dpred;
    std::vector<expr*> stops;
    {
        unsigned i;
        for(i=0; i<num; i++) {
            if(!this->enc.util.is_dpred(args[i])){
                break;
            }
            dpred.push_back(args[i]);
        }
        xenc = this->enc.mk_encoded_loc(args[i]);
        i++;
        for(;i<num; i++) {
            stops.push_back( this->enc.mk_encoded_loc(args[i]));
        }
    }

    if(this->enc.bounds.n_list == 0) {
        enc->B = mk_defineY(enc,nullptr);
        /* data predicates are trivally true, since we got an empty list */
        if(stops.size() == 0){
            enc->A = m.mk_eq(xenc, this->enc.enc_null);
        } else if(stops.size() == 1){
            enc->A = m.mk_and(m.mk_eq(xenc, this->enc.enc_null), m.mk_eq(stops[0], this->enc.enc_null));
        } else {
            enc->A = m.mk_false();
        }
        enc->inc_ref();
        this->enc.encoding[ex] = enc;
        return;
    }

    expr * Z = this->enc.mk_fresh_array(slstar_encoder::Z_prefix.c_str());
    std::vector<expr*> andargs;
    // reachability creates all r_i^Z (prev_reach)
    // -> B must be defined before A otherwise prev_reach is empty
    andargs.push_back( mk_reachability(Z,prev_reach, stops, this->enc.list_locs, this->enc.bounds.n_list) );
    andargs.push_back( mk_footprint(xenc,Z, this->enc.list_locs,prev_reach, stops) );
    andargs.push_back( mk_defineY(enc,Z) );
    andargs.push_back( mk_is_location(xenc, this->enc.list_locs) );
    enc->B = m.mk_and(andargs.size(), &andargs[0]);
    andargs.clear();

    andargs.push_back( mk_structure(xenc,Z, this->enc.list_locs,prev_reach,stops));
    andargs.push_back( mk_stopsoccur(xenc,Z, this->enc.list_locs,stops));
    andargs.push_back( mk_stopseq(xenc,stops));
    andargs.push_back( mk_stopleaves(Z, this->enc.list_locs,stops));
    
    for( auto it = dpred.begin(); it!=dpred.end(); it++) {
        if( this->enc.util.is_dpred_left(*it) ) {
            andargs.push_back( mk_bdata(*it, Z, this->enc.f_left, this->enc.list_locs, prev_reach) );
        }
        if( this->enc.util.is_dpred_right(*it) ) {
            andargs.push_back( mk_bdata(*it, Z, this->enc.f_right, this->enc.list_locs, prev_reach) );
        }
        if( this->enc.util.is_dpred_next(*it) ) {
            andargs.push_back( mk_bdata(*it, Z, this->enc.f_next, this->enc.list_locs, prev_reach) );
        }
        if( this->enc.util.is_dpred_unary(*it)) {
            andargs.push_back( mk_udata(*it,Z,this->enc.list_locs));
        }
    }

    enc->A = m.mk_and( andargs.size(), &andargs[0]);
    enc->inc_ref();
    this->enc.encoding[ex] = enc;
}

app * list_encoder::mk_is_successor(expr * x, expr * y) {
    expr* f_next_x = m.mk_app(enc.f_next,x);
    return m.mk_eq(f_next_x,y);
}

app * list_encoder::mk_defineY(sl_enc * e, expr * Z) {
    std::vector<expr*> andargs;
    if(Z!=nullptr){
        andargs.push_back(m.mk_eq(e->Yd, Z));
        if(enc.needs_list_footprint){
            andargs.push_back(m.mk_eq(e->Yn, Z));
        }
    } else {
        andargs.push_back(enc.mk_is_empty(e->Yd));
        if(enc.needs_list_footprint){
            andargs.push_back(enc.mk_is_empty(e->Yn));
        }
    }
    if(enc.needs_tree_footprint){
        andargs.push_back(enc.mk_is_empty(e->Yl));
        andargs.push_back(enc.mk_is_empty(e->Yr));
    }
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