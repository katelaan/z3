#include "ast/slstar/tree_encoder.h"

tree_encoder::tree_encoder(slstar_encoder & enc) : pred_encoder(enc) {}

void tree_encoder::add_tree(expr * ex, expr * const * args, unsigned num, sl_enc_level level) {
    switch(level) {
        case SL_LEVEL_UF:            
            add_tree_uf(ex,args,num);
            break;
        case SL_LEVEL_FOOTPRINTS:

        case SL_LEVEL_FULL:
        default:
            add_tree_full(ex,args,num);
    }
}

void tree_encoder::add_tree_uf(expr * ex, expr * const * args, unsigned num) {
    SASSERT(is_app(ex));
    sl_enc * enc = new sl_enc(m,this->enc.set_enc, this->enc.needs_tree_footprint, this->enc.needs_list_footprint);
    enc->mk_fresh_Y();
    enc->is_spatial = true;

    enc->A = ex;
    enc->B = m.mk_true();

    enc->level = SL_LEVEL_UF;
    this->enc.cache.add_encoding(ex, enc);
}

void tree_encoder::add_tree_full(expr * ex, expr * const * args, unsigned num) {
    SASSERT(is_app(ex));
    sl_enc * enc = new sl_enc(m,this->enc.set_enc, this->enc.needs_tree_footprint, this->enc.needs_list_footprint);
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

    if(this->enc.bounds.n_tree == 0) {
        enc->B = mk_defineY(enc,nullptr);
        /* data predicates are trivally true, since we got an empty list */
        if(stops.size() == 0){
            enc->A = m.mk_eq(xenc, this->enc.enc_null);
        } else if(stops.size() == 1){
            enc->A = m.mk_and(m.mk_eq(xenc, this->enc.enc_null), m.mk_eq(stops[0], this->enc.enc_null));
        } else {
            enc->A = m.mk_false();
        }
        this->enc.cache.add_encoding(ex, enc);
        return;
    }

    expr * Z = this->enc.set_enc.mk_fresh_array(slstar_encoder::Z_prefix.c_str());
    std::vector<expr*> andargs;
    // reachability creates all r_i^Z (prev_reach)
    // -> B must be defined before A otherwise prev_reach is empty

    andargs.push_back( mk_reachability(Z,prev_reach, stops, this->enc.tree_locs, this->enc.bounds.n_tree) );
    andargs.push_back( mk_footprint(xenc,Z, this->enc.tree_locs, prev_reach, stops) );
    andargs.push_back( mk_defineY(enc,Z) );
    andargs.push_back( mk_is_location(xenc, this->enc.tree_locs) );
    enc->B = m.mk_and(andargs.size(), &andargs[0]);
    andargs.clear();

    andargs.push_back( mk_structure(xenc,Z, this->enc.tree_locs,prev_reach,stops));
    andargs.push_back( mk_stopsoccur(xenc,Z, this->enc.tree_locs,stops));
    andargs.push_back( mk_stopseq(xenc,stops));
    andargs.push_back( mk_stopleaves(Z, this->enc.tree_locs,stops));
    andargs.push_back( mk_ordered(Z,this->enc.tree_locs,stops,prev_reach));
    
    for( auto it = dpred.begin(); it!=dpred.end(); it++) {
        if( this->enc.util.is_dpred_left(*it) ) {
            andargs.push_back( mk_bdata(*it, Z, this->enc.f_left, this->enc.tree_locs, prev_reach) );
        }
        if( this->enc.util.is_dpred_right(*it) ) {
            andargs.push_back( mk_bdata(*it, Z, this->enc.f_right, this->enc.tree_locs, prev_reach) );
        }
        if( this->enc.util.is_dpred_next(*it) ) {
            andargs.push_back( mk_bdata(*it, Z, this->enc.f_next, this->enc.tree_locs, prev_reach) );
        }
        if( this->enc.util.is_dpred_unary(*it)) {
            andargs.push_back( mk_udata(*it,Z,this->enc.tree_locs));
        }
    }

    enc->A = m.mk_and( andargs.size(), &andargs[0]);
    this->enc.cache.add_encoding(ex, enc);
}

app * tree_encoder::mk_is_successor(expr * x, expr * y) {
    expr* f_left_x = m.mk_app(enc.f_left,x);
    expr* f_right_x = m.mk_app(enc.f_right,x);
    return m.mk_or(m.mk_eq(f_left_x,y), m.mk_eq(f_right_x,y));
}

app * tree_encoder::mk_ordered(expr * Z, 
    expr_ref_vector const& xlocs, 
    std::vector<expr*> & stops,
    std::vector<func_decl*> & prev_reach) 
{
    std::vector<expr*> andargs;
    for(int i=0; i< ((int)stops.size())-1; i++) {
        std::vector<expr*> orargs;
        for(unsigned p=0; p<xlocs.size(); p++) {
            orargs.push_back(m.mk_and(
                enc.set_enc.mk_is_element(xlocs[p], Z),
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
        andargs.push_back(enc.set_enc.mk_is_empty(e->Yd));
        if(enc.needs_tree_footprint){
            andargs.push_back(enc.set_enc.mk_is_empty(e->Yl));
            andargs.push_back(enc.set_enc.mk_is_empty(e->Yr));
        }
    }
    if(enc.needs_list_footprint){
        andargs.push_back(enc.set_enc.mk_is_empty(e->Yn));
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


app * tree_encoder::mk_oneparent(expr * Z, expr_ref_vector const& xlocs) {
    std::vector<expr*> andargs;
    for(unsigned i = 0; i<xlocs.size(); i++) {
        std::vector<expr*> andargs2;
        andargs2.push_back(m.mk_implies(
            enc.set_enc.mk_is_element(xlocs[i], Z),
            m.mk_implies(
                m.mk_eq(m.mk_app(enc.f_left,xlocs[i]), m.mk_app(enc.f_right,xlocs[i])),
                m.mk_eq(m.mk_app(enc.f_left,xlocs[i]), enc.enc_null ) )));
        andargs.push_back( m.mk_and(andargs2.size(), &andargs2[0]));
        
        for(unsigned j = 0; j<xlocs.size(); j++) {
            if(i==j) continue;
            andargs.push_back( m.mk_implies(
                m.mk_and( enc.set_enc.mk_is_element(xlocs[j], Z), m.mk_not(m.mk_eq(xlocs[i], xlocs[j])) ),
                mk_all_succs_different(xlocs[i], xlocs[j])    
            ));
        }
    }
    return  m.mk_and(andargs.size(), &andargs[0]);
}

app * tree_encoder::mk_stopleaves(expr * Z, expr_ref_vector const& xlocs, std::vector<expr*> & stops ){
    std::vector<expr*> andargs;
    for(unsigned i=0; i<xlocs.size(); i++ ) {
        andargs.push_back(m.mk_implies(
            m.mk_and(enc.set_enc.mk_is_element(xlocs[i], Z), m.mk_not(enc.set_enc.mk_is_element(m.mk_app(enc.f_left, xlocs[i]),Z)) ), 
            mk_isstop(m.mk_app(enc.f_left, xlocs[i]), stops)));
        andargs.push_back(m.mk_implies(
            m.mk_and(enc.set_enc.mk_is_element(xlocs[i], Z), m.mk_not(enc.set_enc.mk_is_element(m.mk_app(enc.f_right, xlocs[i]),Z)) ), 
            mk_isstop(m.mk_app(enc.f_right, xlocs[i]), stops)));
    }
    return m.mk_and(andargs.size(), &andargs[0]);
}