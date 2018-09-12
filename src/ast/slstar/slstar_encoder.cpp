#include "ast/slstar/slstar_encoder.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_smt2_pp.h"

slstar_encoder::slstar_encoder(ast_manager & m, sort * loc_sort, sort * data_sort) : m(m),  m_boolrw(m), util(m), m_arrayutil(m) {
    auto fid = m.mk_family_id("arith");

    m_loc_sort = loc_sort;
    m.inc_ref(m_loc_sort);
    m_data_sort = data_sort;
    m.inc_ref(m_data_sort);

    //m_int_sort = m.mk_sort(fid, INT_SORT);
    //m.inc_ref(m_int_sort);

    vector<parameter> params;
    params.push_back(parameter(loc_sort)); //TODOsl configurable LocSort
    params.push_back(parameter(m.mk_bool_sort()));
    fid = m.mk_family_id("array");
    m_array_sort = m.mk_sort(fid, ARRAY_SORT, params.size(), params.c_ptr());
    m.inc_ref(m_array_sort);

    //TODOsl configurable LocSort, DatSort
    sort * const domain[] = {loc_sort};
    
    f_next = m.mk_fresh_func_decl("f_next", 1, domain, loc_sort);
    m.inc_ref(f_next);

    f_dat = m.mk_fresh_func_decl("f_dat", 1, domain, m_data_sort);
    m.inc_ref(f_dat);

    f_left = m.mk_fresh_func_decl("f_left", 1, domain, loc_sort);
    m.inc_ref(f_left);

    f_right = m.mk_fresh_func_decl("f_right", 1, domain, loc_sort);
    m.inc_ref(f_right);

    enc_null = m.mk_fresh_const("null", m_loc_sort);
    m.inc_ref(enc_null);
}

app * slstar_encoder::mk_global_constraints() {
    if(!bounds.contains_calls) {
        return m.mk_true();
    }
    expr * unionargs[] = {Xn,Xl,Xr,Xd};
    expr * X = m.mk_fresh_const("X", m_array_sort);

    expr * unionargsLR[] = {Xl,Xr}; 
    std::vector<expr*> andargs;

    std::vector<expr*> locs;
    locs.insert(locs.end(), list_locs.begin(), list_locs.end());
    locs.insert(locs.end(), tree_locs.begin(), tree_locs.end());
    
    andargs.push_back( m.mk_eq(X,mk_union(unionargs,4)) );
    andargs.push_back( mk_subset_eq(X, mk_set_from_elements(&locs[0], locs.size())) );
    if(bounds.contains_calls) {
        andargs.push_back( m.mk_not(mk_is_element(enc_null, X)) );
        expr * Xlr = mk_union(unionargsLR,2); //unionargs+1; TODOsl test
        andargs.push_back( mk_is_empty( mk_intersect(Xn,Xlr)) );
    }
    return m.mk_and(andargs.size(), &andargs[0]);
}

void slstar_encoder::prepare(sl_bounds bd) {
    SASSERT(list_locs.size()==0 && tree_locs.size()==0);
    bounds = bd;
    for(int i=0; i<bd.n_list; i++) {
        app * fresh = m.mk_fresh_const("xl", m_loc_sort);
        m.inc_ref(fresh);
        list_locs.push_back(fresh);
    }
    for(int i=0; i<bd.n_tree; i++) {
        app * fresh = m.mk_fresh_const("xt", m_loc_sort);
        m.inc_ref(fresh);
        tree_locs.push_back(fresh);
    }

    Xn = mk_fresh_array("Xn");
    Xl = mk_fresh_array("Xl");
    Xr = mk_fresh_array("Xr");
    Xd = mk_fresh_array("Xd");
}

void slstar_encoder::encode_top(expr * current, expr_ref & new_ex) {
    encode(current);
    if(encoding.find(current) != encoding.end() ){
        sl_enc* enc = encoding[current];
        //expr * const andargs[3] = {enc->A, enc->B, mk_gobal_constraints(current)};
        //expr * const andargs[3] = {m.mk_true(), m.mk_true(), mk_gobal_constraints(current)};
        std::vector<expr*> andargs;
        andargs.push_back(enc->A);
        andargs.push_back(enc->B);
        andargs.push_back(m.mk_eq(enc->Yn, Xn));
        andargs.push_back(m.mk_eq(enc->Yl, Xl));
        andargs.push_back(m.mk_eq(enc->Yr, Xr));
        andargs.push_back(m.mk_eq(enc->Yd, Xd));
        new_ex = m.mk_and(andargs.size(), &andargs[0]);
    } else {
        m.raise_exception("Unexpected encoder error: no top level encoding found!");
    }
}

void slstar_encoder::encode(expr * ex) {
    SASSERT(is_app(ex));
    /* ignore constants */
    if(encoding.find(ex) != encoding.end() ) {
        return;
    }
    app * t = to_app(ex);
    unsigned num = t->get_num_args();
    for(unsigned i=0; i<num; i++){
        expr * arg = t->get_arg(i);
        encode(arg);
    }
    
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
        add_list(ex, t->get_args(), num);
    } else if(util.is_tree(t)) {
        add_tree(ex, t->get_args(), num);
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

void slstar_encoder::clear_enc_dict() {
    for(auto it=encoding.begin(); it!=encoding.end(); it++) {
        sl_enc* enc = it->second;
        delete enc;
    }
    encoding.clear();
}

void slstar_encoder::clear_loc_vars(){
    for(auto it=list_locs.begin(); it!=list_locs.end(); it++){
        m.dec_ref(*it);
    }
    list_locs.clear();

    for(auto it=tree_locs.begin(); it!=tree_locs.end(); it++){
        m.dec_ref(*it);
    }
    tree_locs.clear();
}

slstar_encoder::~slstar_encoder() {
    if(m_array_sort) m.dec_ref(m_array_sort);
    if(m_loc_sort) m.dec_ref(m_loc_sort);
    if(m_data_sort) m.dec_ref(m_data_sort);

    if(f_next) m.dec_ref(f_next);
    if(f_dat) m.dec_ref(f_dat);
    if(f_left) m.dec_ref(f_left);
    if(f_right) m.dec_ref(f_right);

    if(enc_null) m.dec_ref(enc_null);

    clear_enc_dict();
    clear_loc_vars();
}

app * slstar_encoder::mk_fresh_array(char const * prefix) {
    return m.mk_fresh_const(prefix,m_array_sort);
}

app * slstar_encoder::mk_empty_array() {
    return m_arrayutil.mk_empty_set(m_array_sort);
}

app * slstar_encoder::mk_full_array() {
    return m_arrayutil.mk_full_set(m_array_sort);
}

app * slstar_encoder::mk_set_from_elements(expr * const * elem, unsigned num ) {
    app * tmp = mk_empty_array();
    for(unsigned i=0; i<num; i++ ){
        expr * args[3] = {tmp, elem[i], m.mk_true()};
        tmp = m_arrayutil.mk_store(3, args);
    }
    return tmp;
}

app * slstar_encoder::mk_set_remove_element(expr * x, expr * set) {
    expr * args[3] = {set, x, m.mk_false()};
    return m_arrayutil.mk_store(3, args);
}

app * slstar_encoder::mk_is_empty(expr * set){
    return m.mk_eq(set, mk_empty_array());
}

app * slstar_encoder::mk_is_element(expr * x, expr * set){
    expr * args[2] = {set, x};
    return m_arrayutil.mk_select(2, args);
}

app * slstar_encoder::mk_subset_eq(expr * lhs, expr * rhs) {
    //TODOsl
    //app * tmp = m.mk_implies(m.mk_true(), m.mk_true());
    //tmp->get_decl(); 
    sort *domain[2] = {m.mk_bool_sort(), m.mk_bool_sort()};
    func_decl * f = m.get_basic_decl_plugin()->mk_func_decl(OP_IMPLIES, 0, nullptr, 2, domain, nullptr); 
    expr * args[2] = {lhs, rhs};
    return m.mk_eq(m_arrayutil.mk_map(f, 2, args), mk_full_array());
}

app * slstar_encoder::mk_union(expr * const *args, unsigned num){
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

app * slstar_encoder::mk_intersect(expr * lhs, expr * rhs) {
    sort *domain[2] = {m.mk_bool_sort(), m.mk_bool_sort()};
    func_decl * f = m.get_basic_decl_plugin()->mk_func_decl(OP_AND, 0, nullptr, 2, domain, nullptr); 
    expr * args[2] = {lhs, rhs};
    return m_arrayutil.mk_map(f, 2, args);
}

app * slstar_encoder::mk_encoded_loc(expr * x) {
#if defined(Z3DEBUG)
    SASSERT( encodedlocs.find(x)==encodedlocs.end() );
#endif

    if(locencoding.find(x) != locencoding.end()){
        app * ret = locencoding[x];
        return ret;
    }
    // ensure all nulls are the same location
    if(util.is_null(x) ) {
        SASSERT(enc_null != nullptr);
        return enc_null;
    }

    app* xt = to_app(x);
    func_decl * fdec =xt->get_decl();
    app * fresh = m.mk_fresh_const(fdec->get_name().bare_str(), m_loc_sort);
    encoded_const.emplace(fresh);
    locencoding[x] = fresh;
#if defined(Z3DEBUG)
    encodedlocs.emplace(fresh); //TODOsl delete
#endif
    return fresh;
}

void slstar_encoder::add_list(expr * ex, expr * const * args, unsigned num) {
    SASSERT(is_app(ex));
    sl_enc * enc = new sl_enc(m,*this);
    enc->mk_fresh_Y();
    enc->is_spatial = true;

    expr * xenc;

    std::vector<func_decl*> prev_reach;
    std::vector<expr*> dpred;
    std::vector<expr*> stops;
    {
        unsigned i;
        for(i=0; i<num; i++) {
            if(!util.is_dpred(args[i])){
                break;
            }
            dpred.push_back(args[i]);
        }
        xenc = mk_encoded_loc(args[i]);
        i++;
        for(;i<num; i++) {
            stops.push_back( mk_encoded_loc(args[i]));
        }
    }

    list_encoder pe(*this);
    if(bounds.n_list == 0) {
        enc->B = pe.mk_defineY(enc,nullptr);
        /* data predicates are trivally true, since we got an empty list */
        if(stops.size() == 0){
            enc->A = m.mk_eq(xenc, enc_null);
        } else if(stops.size() == 1){
            enc->A = m.mk_and(m.mk_eq(xenc, enc_null), m.mk_eq(stops[0],enc_null));
        } else {
            enc->A = m.mk_false();
        }
        enc->inc_ref();
        encoding[ex] = enc;
        return;
    }

    expr * Z = mk_fresh_array("Z");
    std::vector<expr*> andargs;
    // reachability creates all r_i^Z (prev_reach)
    // -> B must be defined before A otherwise prev_reach is empty
    andargs.push_back( pe.mk_reachability(Z,prev_reach, stops, list_locs, bounds.n_list) );
    andargs.push_back( pe.mk_footprint(xenc,Z,list_locs,prev_reach, stops) );
    andargs.push_back( pe.mk_defineY(enc,Z) );
    andargs.push_back( pe.mk_is_location(xenc, list_locs) );
    enc->B = m.mk_and(andargs.size(), &andargs[0]);
    andargs.clear();

    andargs.push_back( pe.mk_structure(xenc,Z,list_locs,prev_reach,stops));
    andargs.push_back( pe.mk_stopsoccur(xenc,Z,list_locs,stops));
    andargs.push_back( pe.mk_stopseq(xenc,stops));
    andargs.push_back( pe.mk_stopleaves(Z,list_locs,stops));
    
    for( auto it = dpred.begin(); it!=dpred.end(); it++) {
        if( util.is_dpred_left(*it) ) {
            andargs.push_back( pe.mk_bdata(*it, Z, f_left, list_locs, prev_reach) );
        }
        if( util.is_dpred_right(*it) ) {
            andargs.push_back( pe.mk_bdata(*it, Z, f_right, list_locs, prev_reach) );
        }
        if( util.is_dpred_next(*it) ) {
            andargs.push_back( pe.mk_bdata(*it, Z, f_next, list_locs, prev_reach) );
        }
        if( util.is_dpred_unary(*it)) {
            andargs.push_back( pe.mk_udata(*it,Z,list_locs));
        }
    }

    enc->A = m.mk_and( andargs.size(), &andargs[0]);
    enc->inc_ref();
    encoding[ex] = enc;
}

void slstar_encoder::add_tree(expr * ex, expr * const * args, unsigned num) {
    SASSERT(is_app(ex));
    sl_enc * enc = new sl_enc(m,*this);
    enc->mk_fresh_Y();
    enc->is_spatial = true;

    expr * xenc;
    std::vector<func_decl*> prev_reach;
    std::vector<expr*> dpred;
    std::vector<expr*> stops;
    {
        unsigned i;
        for(i=0; i<num; i++) {
            if(!util.is_dpred(args[i])){
                break;
            }
            dpred.push_back(args[i]);
        }
        xenc = mk_encoded_loc(args[i]);
        i++;
        for(;i<num; i++) {
            stops.push_back( mk_encoded_loc(args[i]));
        }
    }

    tree_encoder pe(*this);
    if(bounds.n_tree == 0) {
        enc->B = pe.mk_defineY(enc,nullptr);
        /* data predicates are trivally true, since we got an empty list */
        if(stops.size() == 0){
            enc->A = m.mk_eq(xenc, enc_null);
        } else if(stops.size() == 1){
            enc->A = m.mk_and(m.mk_eq(xenc, enc_null), m.mk_eq(stops[0],enc_null));
        } else {
            enc->A = m.mk_false();
        }
        enc->inc_ref();
        encoding[ex] = enc;
        return;
    }

    expr * Z = mk_fresh_array("Z");
    std::vector<expr*> andargs;
    // reachability creates all r_i^Z (prev_reach)
    // -> B must be defined before A otherwise prev_reach is empty

    andargs.push_back( pe.mk_reachability(Z,prev_reach, stops, tree_locs, bounds.n_tree) );
    andargs.push_back( pe.mk_footprint(xenc,Z,tree_locs,prev_reach, stops) );
    andargs.push_back( pe.mk_defineY(enc,Z) );
    andargs.push_back( pe.mk_is_location(xenc, tree_locs) );
    enc->B = m.mk_and(andargs.size(), &andargs[0]);
    andargs.clear();

    andargs.push_back( pe.mk_structure(xenc,Z,tree_locs,prev_reach,stops));
    andargs.push_back( pe.mk_stopsoccur(xenc,Z,tree_locs,stops));
    andargs.push_back( pe.mk_stopseq(xenc,stops));
    andargs.push_back( pe.mk_stopleaves(Z,tree_locs,stops));
    andargs.push_back( pe.mk_ordered(Z,tree_locs,stops,prev_reach));
    
    for( auto it = dpred.begin(); it!=dpred.end(); it++) {
        if( util.is_dpred_left(*it) ) {
            andargs.push_back( pe.mk_bdata(*it, Z, f_left, tree_locs, prev_reach) );
        }
        if( util.is_dpred_right(*it) ) {
            andargs.push_back( pe.mk_bdata(*it, Z, f_right, tree_locs, prev_reach) );
        }
        if( util.is_dpred_next(*it) ) {
            andargs.push_back( pe.mk_bdata(*it, Z, f_next, tree_locs, prev_reach) );
        }
        if( util.is_dpred_unary(*it)) {
            andargs.push_back( pe.mk_udata(*it,Z,tree_locs));
        }
    }

    enc->A = m.mk_and( andargs.size(), &andargs[0]);
    enc->inc_ref();
    encoding[ex] = enc;
}

void slstar_encoder::add_floc_fdat(expr * ex, expr * const * args, unsigned num) {
    sl_enc * enc = new sl_enc(m,*this);
    enc->is_spatial = false;
    
    enc->mk_fresh_Y();
    expr * const andargs[] = {mk_is_empty(enc->Yn), mk_is_empty(enc->Yl), mk_is_empty(enc->Yn), mk_is_empty(enc->Yd) };
    enc->B = m.mk_and(4, andargs);
    bool needs_rewrite = is_any_rewritten(args,num);
    if(needs_rewrite) {
        app * t = to_app(ex);
        func_decl * decl = t->get_decl();
        std::vector<expr*> newargs;
        for(unsigned i=0; i<num; i++){
            newargs.push_back(encoding[args[i]]->A);
        }
        enc->A = m.mk_app(decl, num, &newargs[0]);
    } else {
        enc->A = ex;
    }
    enc->is_rewritten = needs_rewrite;

    enc->inc_ref();
    encoding[ex] = enc;
}


void slstar_encoder::add_const(expr * ex) {
    sl_enc * enc = new sl_enc(m,*this);
    enc->is_spatial = false;

    enc->inc_ref();
    encoding[ex] = enc;
}


void slstar_encoder::add_pton(expr * ex, expr * const * args, unsigned num) {
    SASSERT(num==2);
    sl_enc * enc = new sl_enc(m,*this);
    enc->mk_fresh_Y();
    enc->is_spatial = true;

    expr * x = mk_encoded_loc(args[0]);
    expr * y = mk_encoded_loc(args[1]);
    
    expr* f_next_x = m.mk_app(f_next,x);
    enc->A = m.mk_and(m.mk_eq(f_next_x,y), m.mk_not(m.mk_eq(x, enc_null )));
    
    expr * tmp = m.mk_eq(enc->Yn, mk_set_from_elements(&x,1));
    expr * const andargs[] = {tmp, mk_is_empty(enc->Yl), mk_is_empty(enc->Yr), mk_is_empty(enc->Yd) };
    enc->B = m.mk_and(4, andargs);

    enc->inc_ref();
    encoding[ex] = enc;
}

void slstar_encoder::add_ptol(expr * ex, expr * const * args, unsigned num) {
    SASSERT(num==2);
    sl_enc * enc = new sl_enc(m,*this);
    enc->mk_fresh_Y();
    enc->is_spatial = true;

    expr * x = mk_encoded_loc(args[0]);
    expr * y = mk_encoded_loc(args[1]);

    expr* f_left_x = m.mk_app(f_left,x);
    enc->A = m.mk_and(m.mk_eq(f_left_x,y), m.mk_not(m.mk_eq(x, enc_null )));
    
    
    expr * tmp = m.mk_eq(enc->Yl, mk_set_from_elements(&x,1));
    expr * const andargs[] = {tmp, mk_is_empty(enc->Yn), mk_is_empty(enc->Yr), mk_is_empty(enc->Yd) };
    enc->B = m.mk_and(4, andargs);

    enc->inc_ref();
    encoding[ex] = enc;
}

void slstar_encoder::add_ptor(expr * ex, expr * const * args, unsigned num) {
    SASSERT(num==2);
    sl_enc * enc = new sl_enc(m,*this);
    enc->mk_fresh_Y();
    enc->is_spatial = true;

    expr * x = mk_encoded_loc(args[0]);
    expr * y = mk_encoded_loc(args[1]);

    expr* f_right_x = m.mk_app(f_right,x);
    enc->A = m.mk_and(m.mk_eq(f_right_x,y), m.mk_not(m.mk_eq(x, enc_null )));
    
    
    expr * tmp = m.mk_eq(enc->Yr, mk_set_from_elements(&x,1));
    expr * const andargs[] = {tmp, mk_is_empty(enc->Yl), mk_is_empty(enc->Yn), mk_is_empty(enc->Yd) };
    enc->B = m.mk_and(4, andargs);

    enc->inc_ref();
    encoding[ex] = enc;
}

void slstar_encoder::add_ptod(expr * ex, expr * const * args, unsigned num) {
    SASSERT(num==2);
    sl_enc * enc = new sl_enc(m,*this);
    enc->mk_fresh_Y();
    enc->is_spatial = true;

    expr * x = mk_encoded_loc(args[0]);
    expr * y = args[1];

    expr* f_dat_x = m.mk_app(f_dat,x);
    enc->A = m.mk_and(m.mk_eq(f_dat_x,y), m.mk_not(m.mk_eq(x, enc_null )));
    
    
    expr * tmp = m.mk_eq(enc->Yd, mk_set_from_elements(&x,1));
    expr * const andargs[] = {tmp, mk_is_empty(enc->Yl), mk_is_empty(enc->Yr), mk_is_empty(enc->Yn) };
    enc->B = m.mk_and(4, andargs);

    enc->inc_ref();
    encoding[ex] = enc;
}

void slstar_encoder::add_ptolr(expr * ex, expr * const * args, unsigned num) {
    SASSERT(num==3);
    sl_enc * enc = new sl_enc(m,*this);
    enc->mk_fresh_Y();
    enc->is_spatial = true;

    expr * x = mk_encoded_loc(args[0]);
    expr * y1 = mk_encoded_loc(args[1]);
    expr * y2 = mk_encoded_loc(args[2]);

    expr* f_right_x = m.mk_app(f_right,x);
    expr* f_left_x = m.mk_app(f_left,x);
    enc->A = m.mk_and(m.mk_eq(f_left_x,y1), m.mk_eq(f_right_x,y2), m.mk_not(m.mk_eq(x, enc_null ) ));
    
    expr * tmp1 = m.mk_eq(enc->Yl, mk_set_from_elements(&x,1));
    expr * tmp2 = m.mk_eq(enc->Yr, mk_set_from_elements(&x,1));
    expr * const andargs[] = {tmp1, tmp2, mk_is_empty(enc->Yn), mk_is_empty(enc->Yd) };
    enc->B = m.mk_and(4, andargs);

    enc->inc_ref();
    encoding[ex] = enc;
}

void slstar_encoder::add_sep(expr * ex, expr * const * args, unsigned num) {
    sl_enc * enc = new sl_enc(m,*this);
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
        SASSERT(encoding.find(args[i]) != encoding.end());
        if(encoding[args[i]]->is_spatial && m.is_not(args[i])) {
            m.raise_exception("Spatial atoms must not be negated!");
        }
        if(!util.is_call(args[i]) && !util.is_pto(args[i]) && !util.is_sep(args[i]) && encoding[args[i]]->is_spatial ){
            //TODOsl allow floc, fdat
            m.raise_exception("Invalid spatial atom!");
        }
        andargsA.push_back(encoding[args[i]]->A);
        andargsB.push_back(encoding[args[i]]->B);
        Yn.push_back(encoding[args[i]]->Yn);
        Yl.push_back(encoding[args[i]]->Yl);
        Yr.push_back(encoding[args[i]]->Yr);
        Yd.push_back(encoding[args[i]]->Yd);
    }
    // add A: pairwise check of separation of Ys
    for(unsigned i=0; i<num; i++) {
        for(unsigned j=i+1; j<num; j++){
            andargsA.push_back(mk_is_empty(mk_intersect(encoding[args[i]]->Yn, encoding[args[j]]->Yn)));
            andargsA.push_back(mk_is_empty(mk_intersect(encoding[args[i]]->Yl, encoding[args[j]]->Yl)));
            andargsA.push_back(mk_is_empty(mk_intersect(encoding[args[i]]->Yr, encoding[args[j]]->Yr)));
            andargsA.push_back(mk_is_empty(mk_intersect(encoding[args[i]]->Yd, encoding[args[j]]->Yd)));
        }
    }
    // add B: current Y is equal to union of all Ys
    andargsB.push_back( m.mk_eq(mk_union(&Yn[0], num), enc->Yn ));
    andargsB.push_back( m.mk_eq(mk_union(&Yl[0], num), enc->Yl ));
    andargsB.push_back( m.mk_eq(mk_union(&Yr[0], num), enc->Yr ));
    andargsB.push_back( m.mk_eq(mk_union(&Yd[0], num), enc->Yd ));

    enc->A = m.mk_and(andargsA.size(), &andargsA[0]);
    enc->B = m.mk_and(andargsB.size(), &andargsB[0]);

    enc->inc_ref();
    encoding[ex] = enc;
}
void slstar_encoder::add_not(expr * ex, expr * const * args, unsigned num) {
    SASSERT(num==1);
    SASSERT(encoding.find(args[0]) != encoding.end());

    sl_enc * enc = new sl_enc(m,*this);
    enc->is_spatial = encoding[args[0]]->is_spatial;
    enc->A = m.mk_not( encoding[args[0]]->A );
    enc->B = encoding[args[0]]->B;
    enc->copy_Y(encoding[args[0]]);
    enc->inc_ref();
    encoding[ex] = enc;
}

void slstar_encoder::add_eq(expr * ex, expr * const * args, unsigned num) {
    SASSERT(num!=0);
    add_floc_fdat(ex,args,num);
    if(util.is_loc(args[0])) {
        std::vector<expr*> eqargs;
        for(unsigned i=0; i<num; i++) {
            eqargs.push_back(mk_encoded_loc(args[i]));
        }
        m.dec_ref(encoding[ex]->A);
        encoding[ex]->A = m.mk_app(m.get_basic_family_id(), OP_EQ, num, &eqargs[0]);
        m.inc_ref(encoding[ex]->A);
        encoding[ex]->is_rewritten = true;
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
        m.dec_ref(encoding[ex]->A);
        encoding[ex]->A = m.mk_distinct(num, &distargs[0]);
        m.inc_ref(encoding[ex]->A);
        encoding[ex]->is_rewritten = true;
    }
}

void slstar_encoder::add_and(expr * ex, expr * const * args, unsigned num) {
    bool is_spatial = is_any_spatial(args,num);
    if(is_spatial) {
        sl_enc * enc = new sl_enc(m,*this);
        enc->is_spatial = is_spatial;
        enc->copy_Y(encoding[args[0]]);

        vector<expr*> andargsA;
        vector<expr*> andargsB;
        for(unsigned i=0; i<num; i++) {
            andargsA.push_back(encoding[args[i]]->A);
            andargsB.push_back(encoding[args[i]]->B);
        }
        enc->A = m.mk_and(andargsA.size(), &andargsA[0]);
        enc->B = m.mk_and(andargsB.size(), &andargsB[0]);

        enc->inc_ref();
        encoding[ex] = enc;
    } else {
        add_floc_fdat(ex,args,num);
    }
}
void slstar_encoder::add_or(expr * ex, expr * const * args, unsigned num) {
    bool is_spatial = is_any_spatial(args,num);
    if(is_spatial) {
        sl_enc * enc = new sl_enc(m,*this);
        enc->is_spatial = is_spatial;
        enc->copy_Y(encoding[args[0]]);

        vector<expr*> orargsA;
        vector<expr*> andargsB;
        for(unsigned i=0; i<num; i++) {
            orargsA.push_back(encoding[args[i]]->A);
            andargsB.push_back(encoding[args[i]]->B);
        }
        enc->A = m.mk_or(orargsA.size(), &orargsA[0]);
        enc->B = m.mk_and(andargsB.size(), &andargsB[0]);

        enc->inc_ref();
        encoding[ex] = enc;
    } else {
        add_floc_fdat(ex,args,num);
    }
}

bool slstar_encoder::is_any_spatial(expr * const * args, unsigned num) {
    for(unsigned i=0; i<num; i++) {
        SASSERT(encoding.find(args[i]) != encoding.end());
        if(encoding[args[i]]->is_spatial) {
            return true;
        }
    }
    return false;
}


bool slstar_encoder::is_any_rewritten(expr * const * args, unsigned num) {
    for(unsigned i=0; i<num; i++) {
        SASSERT(encoding.find(args[i]) != encoding.end());
        if(encoding[args[i]]->is_rewritten) {
            return true;
        }
    }
    return false;
}

void sl_enc::mk_fresh_Y() {
    if(Yn) m.dec_ref(Yn);
    if(Yl) m.dec_ref(Yl);
    if(Yr) m.dec_ref(Yr);
    if(Yd) m.dec_ref(Yd);
    Yn = enc.mk_fresh_array("Yn");
    Yl = enc.mk_fresh_array("Yl");
    Yr = enc.mk_fresh_array("Yr");
    Yd = enc.mk_fresh_array("Yd");
}

void sl_enc::copy_Y(sl_enc * other) {
    Yn = other->Yn;
    Yl = other->Yl;
    Yr = other->Yr;
    Yd = other->Yd;
}

sl_enc::sl_enc(ast_manager & _m, slstar_encoder & _enc) : m(_m), enc(_enc){
    Yn = nullptr;
    Yl = nullptr;
    Yr = nullptr;
    Yd = nullptr;
    A = nullptr;
    B = nullptr;
    is_spatial = false;
    is_rewritten = false;
}

sl_enc::~sl_enc() {
    if(Yn) m.dec_ref(Yn);
    if(Yl) m.dec_ref(Yl);
    if(Yr) m.dec_ref(Yr);
    if(Yd) m.dec_ref(Yd);
    if(A) m.dec_ref(A);
    if(B) m.dec_ref(B);

}

void sl_enc::inc_ref() {
    if(Yn) m.inc_ref(Yn);
    if(Yl) m.inc_ref(Yl);
    if(Yr) m.inc_ref(Yr);
    if(Yd) m.inc_ref(Yd);
    if(A) m.inc_ref(A);
    if(B) m.inc_ref(B);
}