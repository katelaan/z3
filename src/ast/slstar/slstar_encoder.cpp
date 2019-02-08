#include "ast/slstar/slstar_encoder.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_smt2_pp.h"

const std::string slstar_encoder::Z_prefix = "__Z";
const std::string slstar_encoder::Y_prefix = "__Y";
const std::string slstar_encoder::reach_prefix = "__reach";
const std::string slstar_encoder::X_prefix = "X";
const std::string slstar_encoder::xl_prefix = "__xl";
const std::string slstar_encoder::xt_prefix = "__xt";

slstar_encoder::slstar_encoder(ast_manager & m, sort * loc_sort) : m(m), m_boolrw(m),
    set_enc(m, loc_sort), m_loc_sort(loc_sort, m), f_next(m), f_left(m), f_right(m), cache(m, m_loc_sort),
    list_locs(m), tree_locs(m), Xn(m), Xl(m), Xr(m), Xd(m), enc_null(m),
    util(m)
 {
    sort * const domain[] = {loc_sort};
    
    f_next = m.mk_fresh_func_decl("f_next", 1, domain, loc_sort);
    f_left = m.mk_fresh_func_decl("f_left", 1, domain, loc_sort);
    f_right = m.mk_fresh_func_decl("f_right", 1, domain, loc_sort);
    enc_null = m.mk_fresh_const("null", m_loc_sort);
}

slstar_encoder::~slstar_encoder() {

}

app * slstar_encoder::mk_global_constraints() {
    if(!bounds.contains_calls) {
        return m.mk_true();
    }
    vector<expr*> unionargs;
    unionargs.push_back(Xd);
    if(needs_list_footprint){
        unionargs.push_back(Xn);
    }
    if(needs_tree_footprint){
        unionargs.push_back(Xr);
        unionargs.push_back(Xl);
    }
    expr * X = set_enc.mk_fresh_array("X");

    std::vector<expr*> andargs;

    std::vector<expr*> locs;
    locs.insert(locs.end(), list_locs.begin(), list_locs.end());
    locs.insert(locs.end(), tree_locs.begin(), tree_locs.end());
    
    andargs.push_back( m.mk_eq(X, set_enc.mk_union(&unionargs[0],unionargs.size())) );
    andargs.push_back( set_enc.mk_subset_eq(X, set_enc.mk_set_from_elements(&locs[0], locs.size())) );
    if(bounds.contains_calls) {
        andargs.push_back( m.mk_not(set_enc.mk_is_element(enc_null, X)) );
        if(needs_list_footprint && needs_tree_footprint){
            expr * unionargsLR[] = {Xl,Xr}; 
            expr * Xlr = set_enc.mk_union(unionargsLR,2);
            andargs.push_back( set_enc.mk_is_empty( set_enc.mk_intersect(Xn,Xlr)) );
        }
    }
    return m.mk_and(andargs.size(), &andargs[0]);
}

void slstar_encoder::prepare(sl_bounds bd, sl_enc_level level) {
    bounds = bd;
    current_level = level;

    needs_tree_footprint = bounds.n_tree > 0;
    needs_list_footprint = bounds.n_list > 0;
    if( list_locs.size()==0 ) {
        for(int i=0; i<bd.n_list; i++) {
            app * fresh = m.mk_fresh_const(xt_prefix.c_str(), m_loc_sort);
            m.inc_ref(fresh);
            list_locs.push_back(fresh);
        }
    }
    if( tree_locs.size()==0 ) {
        for(int i=0; i<bd.n_tree; i++) {
            app * fresh = m.mk_fresh_const(xt_prefix.c_str(), m_loc_sort);
            m.inc_ref(fresh);
            tree_locs.push_back(fresh);
        }
    }
    SASSERT( (unsigned) bd.n_list == list_locs.size());
    SASSERT( (unsigned) bd.n_tree == tree_locs.size());

    if(needs_list_footprint){
        Xn = set_enc.mk_fresh_array( (X_prefix + "n").c_str());
    }
    if(needs_tree_footprint){
        Xl = set_enc. mk_fresh_array( (X_prefix + "l").c_str());
        Xr = set_enc.mk_fresh_array( (X_prefix + "r").c_str());
    }
    Xd = set_enc.mk_fresh_array( (X_prefix + "d").c_str());
}

void slstar_encoder::encode_top(expr * current, expr_ref & new_ex) {
    encode(current);
    
    if (cache.has_cached_encoding(current)){
        sl_enc* enc = cache.get_cached_encoding(current);
        //expr * const andargs[3] = {enc->A, enc->B, mk_gobal_constraints(current)};
        //expr * const andargs[3] = {m.mk_true(), m.mk_true(), mk_gobal_constraints(current)};
        std::vector<expr*> andargs;
        andargs.push_back(enc->A);
        andargs.push_back(enc->B);
        if(needs_list_footprint){
            andargs.push_back(m.mk_eq(enc->Yn, Xn));
        }
        if(needs_tree_footprint){
            andargs.push_back(m.mk_eq(enc->Yl, Xl));
            andargs.push_back(m.mk_eq(enc->Yr, Xr));
        }
        andargs.push_back(m.mk_eq(enc->Yd, Xd));
        new_ex = m.mk_and(andargs.size(), &andargs[0]);

        std::cout << "Finished top level encoding: " << new_ex << std::endl;
    } else {
        m.raise_exception("Unexpected encoder error: no top level encoding found!");
    }
}

void slstar_encoder::encode(expr * ex) {
    SASSERT(is_app(ex));
    std::cout << "Encoding " << mk_ismt2_pp(ex, m) << std::endl;

    /* ignore already encoded expressions, but only if encoding level is 
    lower than current encoding level */
    if(cache.has_cached_encoding(ex)) {
        sl_enc* cached = cache.get_cached_encoding(ex);
        SASSERT(cached->level != SL_LEVEL_INVALID);
        if(cached->level >= current_level) {
            std::cout << "Encoding of " << mk_ismt2_pp(ex, m) << " already performed for the current level => return" << std::endl;
            return;
        }

        std::cout << "Encoding of " << mk_ismt2_pp(ex, m) << " already performed for previous level => erase outdated encoding" << std::endl;
        // TODOsl remove old encoding
        cache.uncache(ex);
        // TODO[REF] Why does the following delete operation segfault now (but not before using references in the sl_enc class)?
        //delete ex;
    }

    app * t = to_app(ex);
    unsigned num = t->get_num_args();
    for(unsigned i=0; i<num; i++){
        expr * arg = t->get_arg(i);
        encode(arg);
    }

    // assert all children encodings are on current level
    
    TRACE("slstar_enc", 
        tout <<  "func:" << mk_ismt2_pp(ex, m, 2) << std::endl;
        tout << "args: " << std::endl;
        expr * const * args = t->get_args();
        for(unsigned int i=0; i<num; i++) {
            tout <<  mk_ismt2_pp(args[i], m, 2) << std::endl;
        }
    );
    if(num == 0) {
        add_floc_fdat(ex,t->get_args(), num);
    } else if(util.is_ptod(t)) {
        add_ptod(ex, t->get_args(), num);
    } else if(util.is_pton(t)) {
        add_pton(ex, t->get_args(), num);
    } else if(util.is_ptol(t)) {
        add_ptol(ex, t->get_args(), num);
    } else if(util.is_ptor(t)) {
        add_ptor(ex, t->get_args(), num);
    } else if(util.is_ptolr(t)) {
        add_ptolr(ex, t->get_args(), num);
    } else if(util.is_sep(t)) {
        add_sep(ex, t->get_args(), num);
    } else if(util.is_list(t)) {
        list_encoder pe(*this);
        pe.add_list(ex, t->get_args(), num, current_level);
    } else if(util.is_tree(t)) {
        tree_encoder pe(*this);
        pe.add_tree(ex, t->get_args(), num, current_level);
    } else if(m.is_and(t)){
        add_and(ex, t->get_args(), num);
    } else if(m.is_or(t)){
        add_or(ex, t->get_args(), num);
    } else if(m.is_not(t)){
        add_not(ex, t->get_args(), num);
    } else if(m.is_eq(t)){
        add_eq(ex, t->get_args(), num);
    } else if(m.is_distinct(t)){
        add_distinct(ex, t->get_args(), num);
    } else {
        add_floc_fdat( ex, t->get_args(), num);
        //TRACE("slstar_enc", 
        //    tout << "Unknown operation!" << std::endl;
        //);
        //m.raise_exception("Unknown operation");
    }
}

app * slstar_encoder::mk_encoded_loc(expr * x) {
#if defined(Z3DEBUG)
    SASSERT(!cache.has_encoded_loc(x));
#endif
    if (cache.has_encoded_loc(x)) {
        return cache.get_encoded_loc(x);
    }
    // ensure all nulls are the same location
    if(util.is_null(x) ) {
        SASSERT(enc_null != nullptr);
        return enc_null;
    }

    app* xt = to_app(x);
    func_decl * fdec =xt->get_decl();
    app * fresh = m.mk_fresh_const(fdec->get_name().bare_str(), m_loc_sort);

    cache.add_encoded_loc(x, fresh);
    return fresh;
}

void slstar_encoder::add_floc_fdat(expr * ex, expr * const * args, unsigned num) {
    sl_enc * enc = new sl_enc(m, set_enc, needs_tree_footprint, needs_list_footprint);
    enc->is_spatial = false;
    
    enc->mk_fresh_Y();

    std::vector<expr*> andargs;
    if(needs_list_footprint) {
        andargs.push_back(set_enc.mk_is_empty(enc->Yn));
    }
    if(needs_tree_footprint){
        andargs.push_back(set_enc.mk_is_empty(enc->Yl));
        andargs.push_back(set_enc.mk_is_empty(enc->Yr));
    }
    andargs.push_back(set_enc.mk_is_empty(enc->Yd));

    enc->B = m.mk_and(andargs.size(), &andargs[0]);
    bool needs_rewrite = is_any_rewritten(args,num);
    if(needs_rewrite) {
        app * t = to_app(ex);
        func_decl * decl = t->get_decl();
        std::vector<expr*> newargs;
        for(unsigned i=0; i<num; i++){
            newargs.push_back(cache.get_cached_encoding(args[i])->A);
        }
        enc->A = m.mk_app(decl, num, &newargs[0]);
    } else {
        enc->A = ex;
    }
    enc->is_rewritten = needs_rewrite;

    enc->level = SL_LEVEL_FULL;
    cache.add_encoding(ex, enc);
}


void slstar_encoder::add_const(expr * ex) {
    sl_enc * enc = new sl_enc(m, set_enc, needs_tree_footprint, needs_list_footprint);
    enc->is_spatial = false;
    enc->level = SL_LEVEL_FULL;
    cache.add_encoding(ex, enc);
}


void slstar_encoder::add_pton(expr * ex, expr * const * args, unsigned num) {
    SASSERT(num==2);
    sl_enc * enc = new sl_enc(m, set_enc, needs_tree_footprint, needs_list_footprint);
    enc->mk_fresh_Y();
    enc->is_spatial = true;

    expr * x = mk_encoded_loc(args[0]);
    expr * y = mk_encoded_loc(args[1]);
    
    expr* f_next_x = m.mk_app(f_next,x);
    enc->A = m.mk_and(m.mk_eq(f_next_x,y), m.mk_not(m.mk_eq(x, enc_null )));
    
    std::vector<expr*> andargs;
    andargs.push_back(m.mk_eq(enc->Yn, set_enc.mk_set_from_elements(&x,1)));
    if(needs_tree_footprint){
        andargs.push_back(set_enc.mk_is_empty(enc->Yl));
        andargs.push_back(set_enc.mk_is_empty(enc->Yr));
    }
    andargs.push_back(set_enc.mk_is_empty(enc->Yd));
    enc->B = m.mk_and(andargs.size(), &andargs[0]);

    enc->level = SL_LEVEL_FULL;
    cache.add_encoding(ex, enc);
}

void slstar_encoder::add_ptol(expr * ex, expr * const * args, unsigned num) {
    SASSERT(num==2);
    sl_enc * enc = new sl_enc(m, set_enc, needs_tree_footprint, needs_list_footprint);
    enc->mk_fresh_Y();
    enc->is_spatial = true;

    expr * x = mk_encoded_loc(args[0]);
    expr * y = mk_encoded_loc(args[1]);

    expr* f_left_x = m.mk_app(f_left,x);
    enc->A = m.mk_and(m.mk_eq(f_left_x,y), m.mk_not(m.mk_eq(x, enc_null )));
    
    std::vector<expr*> andargs;
    andargs.push_back(m.mk_eq(enc->Yl, set_enc.mk_set_from_elements(&x,1)));
    andargs.push_back(set_enc.mk_is_empty(enc->Yr));
    if(needs_list_footprint) {
        andargs.push_back(set_enc.mk_is_empty(enc->Yn));
    }
    andargs.push_back(set_enc.mk_is_empty(enc->Yd));

    enc->B = m.mk_and(andargs.size(), &andargs[0]);

    enc->level = SL_LEVEL_FULL;
    cache.add_encoding(ex, enc);
}

void slstar_encoder::add_ptor(expr * ex, expr * const * args, unsigned num) {
    SASSERT(num==2);
    sl_enc * enc = new sl_enc(m, set_enc, needs_tree_footprint, needs_list_footprint);
    enc->mk_fresh_Y();
    enc->is_spatial = true;

    expr * x = mk_encoded_loc(args[0]);
    expr * y = mk_encoded_loc(args[1]);

    expr* f_right_x = m.mk_app(f_right,x);
    enc->A = m.mk_and(m.mk_eq(f_right_x,y), m.mk_not(m.mk_eq(x, enc_null )));
    
    std::vector<expr*> andargs;
    andargs.push_back(m.mk_eq(enc->Yr, set_enc.mk_set_from_elements(&x,1)));
    andargs.push_back(set_enc.mk_is_empty(enc->Yl));
    if(needs_list_footprint) {
        andargs.push_back(set_enc.mk_is_empty(enc->Yn));
    }
    andargs.push_back(set_enc.mk_is_empty(enc->Yd));

    enc->B = m.mk_and(andargs.size(), &andargs[0]);

    enc->level = SL_LEVEL_FULL;
    cache.add_encoding(ex, enc);
}

void slstar_encoder::add_ptod(expr * ex, expr * const * args, unsigned num) {
    SASSERT(num==2);

    expr * x = mk_encoded_loc(args[0]);
    app * y = to_app(args[1]);

    app * tx = to_app(args[0]);
    func_decl * x_decl = tx->get_decl();
    SASSERT(x_decl->get_range()->get_num_parameters() == 2 );
    const parameter& dat_sort_param = x_decl->get_range()->get_parameter(1);
    SASSERT(dat_sort_param.is_ast());
    SASSERT(is_sort(dat_sort_param.get_ast()));
    sort * data_sort = to_sort(dat_sort_param.get_ast());

    
    if(!y->get_decl()->get_range()->is_sort_of(data_sort->get_family_id(), data_sort->get_decl_kind())) {
        m.raise_exception("ptod location points to wrong datasort!");
    }

    sl_enc * enc = new sl_enc(m, set_enc, needs_tree_footprint, needs_list_footprint);
    enc->mk_fresh_Y();
    enc->is_spatial = true;

    func_decl * f_dat = cache.get_f_dat(data_sort);

    expr* f_dat_x = m.mk_app(f_dat,x);
    enc->A = m.mk_and(m.mk_eq(f_dat_x,y), m.mk_not(m.mk_eq(x, enc_null )));

    std::vector<expr*> andargs;
    andargs.push_back(m.mk_eq(enc->Yd, set_enc.mk_set_from_elements(&x,1)));
    if(needs_list_footprint) {
        andargs.push_back(set_enc.mk_is_empty(enc->Yn));
    }
    if(needs_tree_footprint) {
        andargs.push_back(set_enc.mk_is_empty(enc->Yl));
        andargs.push_back(set_enc.mk_is_empty(enc->Yr));
    }

    enc->B = m.mk_and(andargs.size(), &andargs[0]);

    enc->level = SL_LEVEL_FULL;
    cache.add_encoding(ex, enc);
}

void slstar_encoder::add_ptolr(expr * ex, expr * const * args, unsigned num) {
    SASSERT(num==3);
    sl_enc * enc = new sl_enc(m, set_enc, needs_tree_footprint, needs_list_footprint);
    enc->mk_fresh_Y();
    enc->is_spatial = true;

    expr * x = mk_encoded_loc(args[0]);
    expr * y1 = mk_encoded_loc(args[1]);
    expr * y2 = mk_encoded_loc(args[2]);

    expr* f_right_x = m.mk_app(f_right,x);
    expr* f_left_x = m.mk_app(f_left,x);
    enc->A = m.mk_and(m.mk_eq(f_left_x,y1), m.mk_eq(f_right_x,y2), m.mk_not(m.mk_eq(x, enc_null ) ));
    
    std::vector<expr*> andargs;
    andargs.push_back(m.mk_eq(enc->Yl, set_enc.mk_set_from_elements(&x,1)));
    andargs.push_back(m.mk_eq(enc->Yr, set_enc.mk_set_from_elements(&x,1)));
    if(needs_list_footprint) {
        andargs.push_back(set_enc.mk_is_empty(enc->Yn));
    }
    andargs.push_back(set_enc.mk_is_empty(enc->Yd));

    enc->B = m.mk_and(andargs.size(), &andargs[0]);

    enc->level = SL_LEVEL_FULL;
    cache.add_encoding(ex, enc);
}

void slstar_encoder::add_sep(expr * ex, expr * const * args, unsigned num) {
    sl_enc * enc = new sl_enc(m, set_enc, needs_tree_footprint, needs_list_footprint);
    enc->mk_fresh_Y();
    enc->is_spatial = true;

    vector<expr*> andargsA;
    vector<expr*> andargsB;
    vector<expr*> Yn;
    vector<expr*> Yl;
    vector<expr*> Yr;
    vector<expr*> Yd;
    // A resp. B is conj. over all As and Bs
    for(unsigned i=0; i<num; i++) {
        SASSERT(cache.has_cached_encoding(args[i]));
        if (cache.get_cached_encoding(args[i])->is_spatial && m.is_not(args[i])) {
            m.raise_exception("Spatial atoms must not be negated!");
        }
        if (!util.is_call(args[i]) && !util.is_pto(args[i]) && !util.is_sep(args[i]) && cache.get_cached_encoding(args[i])->is_spatial ){
            m.raise_exception("Invalid spatial atom!");
        }
        auto cached = cache.get_cached_encoding(args[i]);
        andargsA.push_back(cached->A);
        andargsB.push_back(cached->B);
        if(needs_list_footprint){
            Yn.push_back(cached->Yn);
        }
        if(needs_tree_footprint){
            Yl.push_back(cached->Yl);
            Yr.push_back(cached->Yr);
        }
        Yd.push_back(cached->Yd);
    }
    // add A: pairwise check of separation of Ys
    for(unsigned i=0; i<num; i++) {
        auto cached_i = cache.get_cached_encoding(args[i]);
        for(unsigned j=i+1; j<num; j++){
            auto cached_j = cache.get_cached_encoding(args[j]);
            if (needs_list_footprint){
                andargsA.push_back(set_enc.mk_is_empty(set_enc.mk_intersect(cached_i->Yn, cached_j->Yn)));
            }
            if (needs_tree_footprint){
                andargsA.push_back(set_enc.mk_is_empty(set_enc.mk_intersect(cached_i->Yl, cached_j->Yl)));
                andargsA.push_back(set_enc.mk_is_empty(set_enc.mk_intersect(cached_i->Yr, cached_j->Yr)));
            }
            andargsA.push_back(set_enc.mk_is_empty(set_enc.mk_intersect(cached_i->Yd, cached_j->Yd)));
        }
    }
    // add B: current Y is equal to union of all Ys
    if(needs_list_footprint) {
        andargsB.push_back( m.mk_eq(set_enc.mk_union(&Yn[0], num), enc->Yn ));
    }
    if(needs_tree_footprint) {
        andargsB.push_back( m.mk_eq(set_enc.mk_union(&Yl[0], num), enc->Yl ));
        andargsB.push_back( m.mk_eq(set_enc.mk_union(&Yr[0], num), enc->Yr ));
    }
    andargsB.push_back( m.mk_eq(set_enc.mk_union(&Yd[0], num), enc->Yd ));

    enc->A = m.mk_and(andargsA.size(), &andargsA[0]);
    enc->B = m.mk_and(andargsB.size(), &andargsB[0]);

    enc->level = get_lowest_level(args,num);
    cache.add_encoding(ex, enc);
}
void slstar_encoder::add_not(expr * ex, expr * const * args, unsigned num) {
    SASSERT(num==1);
    SASSERT(cache.has_cached_encoding(args[0]));

    sl_enc * enc = new sl_enc(m, set_enc, needs_tree_footprint, needs_list_footprint);
    auto cached = cache.get_cached_encoding(args[0]);
    enc->is_spatial = cached->is_spatial;
    enc->A = m.mk_not( cached->A );
    enc->B = cached->B;
    enc->copy_Y(cached);
    enc->level = cached->level;
    cache.add_encoding(ex, enc);
}

void slstar_encoder::add_eq(expr * ex, expr * const * args, unsigned num) {
    SASSERT(num!=0);
    add_floc_fdat(ex,args,num);
    if(util.is_loc(args[0])) {
        std::vector<expr*> eqargs;
        for(unsigned i=0; i<num; i++) {
            eqargs.push_back(mk_encoded_loc(args[i]));
        }
        auto cached = cache.get_cached_encoding(ex);
        cached->A = m.mk_app(m.get_basic_family_id(), OP_EQ, num, &eqargs[0]);
        cached->level = SL_LEVEL_FULL;
        cached->is_rewritten = true;
    }
}

void slstar_encoder::add_distinct(expr * ex, expr * const * args, unsigned num) {
    SASSERT(num!=0);
    add_floc_fdat(ex,args,num);
    if(util.is_loc(args[0])) {
        std::vector<expr*> distargs;
        for(unsigned i=0; i<num; i++) {
            distargs.push_back(mk_encoded_loc(args[i]));
        }
        auto cached = cache.get_cached_encoding(ex);
        cached->A = m.mk_distinct(num, &distargs[0]);
        cached->level = SL_LEVEL_FULL;
        cached->is_rewritten = true;
    }
}

void slstar_encoder::add_and(expr * ex, expr * const * args, unsigned num) {
    bool is_spatial = is_any_spatial(args,num);
    if(is_spatial) {
        sl_enc * enc = new sl_enc(m, set_enc, needs_tree_footprint, needs_list_footprint);
        enc->is_spatial = is_spatial;
        enc->copy_Y(cache.get_cached_encoding(args[0]));

        vector<expr*> andargsA;
        vector<expr*> andargsB;
        for(unsigned i=0; i<num; i++) {
            auto cached_i = cache.get_cached_encoding(args[i]);
            andargsA.push_back(cached_i->A);
            andargsB.push_back(cached_i->B);
        }
        enc->A = m.mk_and(andargsA.size(), &andargsA[0]);
        enc->B = m.mk_and(andargsB.size(), &andargsB[0]);

        enc->level = get_lowest_level(args, num);
        cache.add_encoding(ex, enc);
    } else {
        add_floc_fdat(ex,args,num);
    }
}
void slstar_encoder::add_or(expr * ex, expr * const * args, unsigned num) {
    bool is_spatial = is_any_spatial(args,num);
    if(is_spatial) {
        sl_enc * enc = new sl_enc(m, set_enc, needs_tree_footprint, needs_list_footprint);
        enc->is_spatial = is_spatial;
        enc->copy_Y(cache.get_cached_encoding(args[0]));

        vector<expr*> orargsA;
        vector<expr*> andargsB;
        for(unsigned i=0; i<num; i++) {
            orargsA.push_back(cache.get_cached_encoding(args[i])->A);
            andargsB.push_back(cache.get_cached_encoding(args[i])->B);
        }
        enc->A = m.mk_or(orargsA.size(), &orargsA[0]);
        enc->B = m.mk_and(andargsB.size(), &andargsB[0]);

        enc->level = get_lowest_level(args, num);
        cache.add_encoding(ex, enc);
    } else {
        add_floc_fdat(ex,args,num);
    }
}

bool slstar_encoder::is_any_spatial(expr * const * args, unsigned num) {
    for(unsigned i=0; i<num; i++) {
        SASSERT(cache.has_cached_encoding(args[i]));
        if (cache.get_cached_encoding(args[i])->is_spatial) {
            return true;
        }
    }
    return false;
}


bool slstar_encoder::is_any_rewritten(expr * const * args, unsigned num) {
    for(unsigned i=0; i<num; i++) {
        SASSERT(cache.has_cached_encoding(args[i]));
        if (cache.get_cached_encoding(args[i])->is_rewritten) {
            return true;
        }
    }
    return false;
}

sl_enc_level slstar_encoder::get_lowest_level(expr * const * args, unsigned num) {
    sl_enc_level ret = SL_LEVEL_FULL;
    for(unsigned i=0; i<num; i++) {
        SASSERT(cache.has_cached_encoding(args[i]));
        if(cache.get_cached_encoding(args[i])->level < ret) {
            ret = cache.get_cached_encoding(args[i])->level;
        }
    }
    return ret;
}

/**
 * slstar_set_encoder
 */

slstar_set_encoder::slstar_set_encoder(ast_manager & m, sort * loc_sort) : m(m), m_arrayutil(m), m_array_sort(m), m_loc_sort(loc_sort, m){
    auto fid = m.mk_family_id("arith");
    fid = m.mk_family_id("array");
    vector<parameter> params;
    params.push_back(parameter(loc_sort)); //TODOsl configurable LocSort
    params.push_back(parameter(m.mk_bool_sort()));
    m_array_sort = m.mk_sort(fid, ARRAY_SORT, params.size(), params.c_ptr());
}

slstar_set_encoder::~slstar_set_encoder() {    
}

app * slstar_set_encoder::mk_fresh_array(char const * prefix) {
    return m.mk_fresh_const(prefix,m_array_sort);
}

app * slstar_set_encoder::mk_empty_array() {
    return m_arrayutil.mk_empty_set(m_array_sort);
}

app * slstar_set_encoder::mk_full_array() {
    return m_arrayutil.mk_full_set(m_array_sort);
}

app * slstar_set_encoder::mk_set_from_elements(expr * const * elem, unsigned num ) {
    app * tmp = mk_empty_array();
    for(unsigned i=0; i<num; i++ ){
        expr * args[3] = {tmp, elem[i], m.mk_true()};
        tmp = m_arrayutil.mk_store(3, args);
    }
    return tmp;
}

app * slstar_set_encoder::mk_set_remove_element(expr * x, expr * set) {
    expr * args[3] = {set, x, m.mk_false()};
    return m_arrayutil.mk_store(3, args);
}

app * slstar_set_encoder::mk_is_empty(expr * set){
    return m.mk_eq(set, mk_empty_array());
}

app * slstar_set_encoder::mk_is_element(expr * x, expr * set) {
    expr * args[2] = {set, x};
    return m_arrayutil.mk_select(2, args);
}

app * slstar_set_encoder::mk_subset_eq(expr * lhs, expr * rhs) {
    //TODOsl
    //app * tmp = m.mk_implies(m.mk_true(), m.mk_true());
    //tmp->get_decl(); 
    sort *domain[2] = {m.mk_bool_sort(), m.mk_bool_sort()};
    func_decl * f = m.get_basic_decl_plugin()->mk_func_decl(OP_IMPLIES, 0, nullptr, 2, domain, nullptr); 
    expr * args[2] = {lhs, rhs};
    return m.mk_eq(m_arrayutil.mk_map(f, 2, args), mk_full_array());
}

app * slstar_set_encoder::mk_union(expr * const *args, unsigned num) {
    SASSERT(num >= 2);
    
    sort *domain[2] = {m.mk_bool_sort(), m.mk_bool_sort()};
    func_decl * f = m.get_basic_decl_plugin()->mk_func_decl(OP_OR, 0, nullptr, 2, domain, nullptr);
    app * curr = to_app(args[0]);
    for(unsigned i=1; i<num; i++) {
        expr* mapargs[2] = {curr, args[i]};
        curr = m_arrayutil.mk_map(f, 2, mapargs);
    }
    return curr;
}

app * slstar_set_encoder::mk_intersect(expr * lhs, expr * rhs) {
    sort *domain[2] = {m.mk_bool_sort(), m.mk_bool_sort()};
    func_decl * f = m.get_basic_decl_plugin()->mk_func_decl(OP_AND, 0, nullptr, 2, domain, nullptr); 
    expr * args[2] = {lhs, rhs};
    return m_arrayutil.mk_map(f, 2, args);
}

/**
 * sl_enc
 */

void sl_enc::mk_fresh_Y() {
    if(needs_list_footprint) {
        Yn = set_enc.mk_fresh_array( (slstar_encoder::Y_prefix + "n").c_str() );
    }
    if(needs_tree_footprint) {
        Yl = set_enc.mk_fresh_array( (slstar_encoder::Y_prefix + "l").c_str() );
        Yr = set_enc.mk_fresh_array( (slstar_encoder::Y_prefix + "r").c_str() );
    }
    Yd = set_enc.mk_fresh_array( (slstar_encoder::Y_prefix + "d").c_str() );
}

void sl_enc::copy_Y(sl_enc * other) {
    Yn = other->Yn;
    Yl = other->Yl;
    Yr = other->Yr;
    Yd = other->Yd;
}

sl_enc::sl_enc(ast_manager & _m, slstar_set_encoder & set_enc, bool trees, bool lists) :
    A(m), B(m), Yn(m), Yl(m), Yr(m), Yd(m), m(_m), set_enc(set_enc)
 {
    is_spatial = false;
    is_rewritten = false;
    needs_tree_footprint = trees;
    needs_list_footprint = lists;
}

sl_enc::~sl_enc() {
    std::cout << "Will delete sl_enc with: " << std::endl;
    std::cout << A << std::endl;
    std::cout << B << std::endl;
    std::cout << "FPs: " << Yn << ", " << Yl << ", " << Yr << ", " << Yd << std::endl;
}

/**
 * 
 */

enc_cache::enc_cache(ast_manager & m, sort_ref const& loc_sort): m(m), m_loc_sort(loc_sort) {

}

void enc_cache::clear_enc_dict() {
    for(auto it=encoding.begin(); it!=encoding.end(); it++) {
        sl_enc* enc = it->second;
        delete enc;
    }
    encoding.clear();
}

void enc_cache::clear_loc_vars(){
    for(auto it=locencoding.begin(); it!=locencoding.end(); ++it){
        m.dec_ref(it->second);
    }
}

enc_cache::~enc_cache() {
    for(auto i = f_dat_map.begin(); i!=f_dat_map.end(); ++i) {
        m.dec_ref(i->second);
    }

    clear_enc_dict();
    clear_loc_vars();
}

func_decl * enc_cache::get_f_dat(sort * s) {
    auto i = f_dat_map.emplace(s, nullptr);

    if (i.second) {
        std::string name = s->get_name().bare_str();

        TRACE("slstar_f_dat", 
            tout <<  "new f_dat from Sort: " << name; 
        );

        std::transform(name.begin(), name.end(), name.begin(), ::tolower);
        name = "f_dat_" + name;

        sort * const domain[] = {m_loc_sort};
        i.first->second = m.mk_fresh_func_decl(name.c_str(), 1, domain, s);
        m.inc_ref(i.first->second);
    }
    return i.first->second;
}

bool enc_cache::has_cached_encoding(expr * e) const {
    return encoding.find(e) != encoding.end();
}

sl_enc* enc_cache::get_cached_encoding(expr * e) const {
    SASSERT(has_cached_encoding(e));
    return encoding.at(e);
}

bool enc_cache::has_encoded_loc(expr * e) const {
    return locencoding.find(e) != locencoding.end();
}

app* enc_cache::get_encoded_loc(expr * e) const {
    SASSERT(has_encoded_loc(e));
    return locencoding.at(e);
}

void enc_cache::add_encoded_loc(expr * e, app * encoded) {
    encoded_const.emplace(encoded);
    locencoding.emplace(e, encoded);
#if defined(Z3DEBUG)
    encodedlocs.emplace(encoded); //TODOsl delete
#endif
    m.inc_ref(encoded);
}

void enc_cache::add_encoding(expr * e, sl_enc* enc) {
    // TODO: Perhaps assert that there isn't already something in the cache?
    encoding[e] = enc;
}

void enc_cache::uncache(expr *const e) {
    encoding.erase(e);
}

std::unordered_set<app*> enc_cache::all_encoded_consts() const {
    return encoded_const;
}

std::unordered_map<sort*, func_decl*> enc_cache::get_f_dat_map() const {
    return f_dat_map;
}