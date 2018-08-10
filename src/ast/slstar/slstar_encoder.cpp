#include "ast/slstar/slstar_encoder.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_smt2_pp.h"

slstar_encoder::slstar_encoder(ast_manager & m) : m(m),  m_boolrw(m), util(m), m_arrayutil(m) {
    auto fid = m.mk_family_id("arith");
    m_int_sort = m.mk_sort(fid, INT_SORT);
    m.inc_ref(m_int_sort);

    vector<parameter> params;
    params.push_back(parameter(m_int_sort)); //TODOsl configurable LocSort
    params.push_back(parameter(m.mk_bool_sort()));
    fid = m.mk_family_id("array");
    m_array_sort = m.mk_sort(fid, ARRAY_SORT, params.size(), params.c_ptr());
    m.inc_ref(m_array_sort);

    //TODOsl configurable LocSort, DatSort
    sort * const domain[] = {m_int_sort};
    
    f_next = m.mk_fresh_func_decl("f_next", 1, domain, m_int_sort);
    m.inc_ref(f_next);

    f_dat = m.mk_fresh_func_decl("f_dat", 1, domain, m_int_sort);
    m.inc_ref(f_dat);

    f_left = m.mk_fresh_func_decl("f_left", 1, domain, m_int_sort);
    m.inc_ref(f_left);

    f_right = m.mk_fresh_func_decl("f_right", 1, domain, m_int_sort);
    m.inc_ref(f_right);
}

void slstar_encoder::operator()(sl_bounds bd, expr * current, expr_ref & new_ex) {
    encode(current);
    if(encoding.find(current) != encoding.end() ){
        sl_enc* enc = encoding[current];
        //expr * const andargs[3] = {enc->A, enc->B, mk_gobal_constraints(current)};
        expr * const andargs[3] = {m.mk_true(), m.mk_true(), mk_gobal_constraints(current)};
        new_ex = m.mk_and(3,andargs);
    } else {
        m.raise_exception("Unexpected encoder error: no top level encoding found!");
    }
}

app * slstar_encoder::mk_gobal_constraints(expr * ex) {
    return m.mk_true();
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
        add_pred(ex, t->get_args(), num);
    } else if(util.is_tree(t)) {
        add_pred(ex, t->get_args(), num);
    } else if(m.is_and(t)){
        add_and(ex, t->get_args(), num);
    } else if(m.is_or(t)){
        add_or(ex, t->get_args(), num);
    } else if(m.is_not(t)){
        add_not(ex, t->get_args(), num);
    } else {
        TRACE("slstar_enc", 
            tout << "Unknown operation!" << std::endl;
        );
        m.raise_exception("Unknown operation");
    }
}

void slstar_encoder::reset() {
    for(auto it=encoding.begin(); it!=encoding.end(); it++) {
        sl_enc* enc = it->second;
        delete enc;
    }
    encoding.clear();
}

slstar_encoder::~slstar_encoder() {
    if(m_array_sort) m.dec_ref(m_array_sort);
    if(m_int_sort) m.dec_ref(m_int_sort);

    if(f_next) m.dec_ref(f_next);
    if(f_dat) m.dec_ref(f_dat);
    if(f_left) m.dec_ref(f_left);
    if(f_right) m.dec_ref(f_right);

    reset();
}

app * slstar_encoder::mk_fresh_array(char const * prefix) {
    return m.mk_fresh_const(prefix,m_array_sort);
}

app * slstar_encoder::mk_empty_array() {
    return m_arrayutil.mk_empty_set(m_array_sort);
}

app * slstar_encoder::mk_single_element_array(expr * x) {
    app * tmp = mk_empty_array();
    expr * args[3] = {tmp, x, m.mk_true()};
    return m_arrayutil.mk_store(3, args);
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
    return m_arrayutil.mk_map(f, 2, args);
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
    app* xt = to_app(x);
    func_decl * fdec =xt->get_decl();
    return m.mk_fresh_const(fdec->get_name().bare_str(), m_int_sort); //TODOsl get sort 
}

void slstar_encoder::add_pred(expr * ex, expr * const * args, unsigned num) {
    SASSERT(is_app(ex));
    app * t = to_app(ex);

    sl_enc * enc = new sl_enc(m,*this);
    enc->mk_fresh_Y();
    enc->is_spatial = true;

    enc->A = m.mk_true();
    enc->B = m.mk_true();
    // TODOsl actual predicate encoding

    enc->inc_ref();
    encoding[ex] = enc;
}
void slstar_encoder::add_floc_fdat(expr * ex, expr * const * args, unsigned num) {
    sl_enc * enc = new sl_enc(m,*this);
    enc->is_spatial = false;
    
    enc->mk_fresh_Y();
    expr * const andargs[] = {mk_is_empty(enc->Yn), mk_is_empty(enc->Yl), mk_is_empty(enc->Yn), mk_is_empty(enc->Yd) };
    enc->B = m.mk_and(4, andargs);
    enc->A = ex;

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
    enc->A = m.mk_eq(f_next_x,y);
    
    expr * sigleton = mk_is_empty(mk_set_remove_element(x, enc->Yn));
    expr * iscontained = mk_is_element(x, enc->Yn);
    expr * tmp = m.mk_and(sigleton,iscontained);
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
    enc->A = m.mk_eq(f_left_x,y);
    
    expr * sigleton = mk_is_empty(mk_set_remove_element(x, enc->Yl));
    expr * iscontained = mk_is_element(x, enc->Yl);
    expr * tmp = m.mk_and(sigleton,iscontained);
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
    enc->A = m.mk_eq(f_right_x,y);
    
    expr * sigleton = mk_is_empty(mk_set_remove_element(x, enc->Yr));
    expr * iscontained = mk_is_element(x, enc->Yr);
    expr * tmp = m.mk_and(sigleton,iscontained);
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
    expr * y = mk_encoded_loc(args[1]);

    expr* f_dat_x = m.mk_app(f_dat,x);
    enc->A = m.mk_eq(f_dat_x,y);
    
    expr * sigleton = mk_is_empty(mk_set_remove_element(x, enc->Yd));
    expr * iscontained = mk_is_element(x, enc->Yd);
    expr * tmp = m.mk_and(sigleton,iscontained);
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
    enc->A = m.mk_and(m.mk_eq(f_left_x,y1), m.mk_eq(f_right_x,y2));
    
    expr * sigleton = mk_is_empty(mk_set_remove_element(x, enc->Yr));
    expr * iscontained = mk_is_element(x, enc->Yr);
    expr * tmp = m.mk_and(sigleton,iscontained);
    expr * const andargs[] = {tmp, mk_is_empty(enc->Yl), mk_is_empty(enc->Yn), mk_is_empty(enc->Yd) };
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

    enc->inc_ref();
    encoding[ex] = enc;
}
void slstar_encoder::add_app(expr * ex, expr * const * args, unsigned num) {
    //TODOsl this was intended for adding the X=Y constraints -> fix
    add_floc_fdat(ex,args,num);
}
void slstar_encoder::add_and(expr * ex, expr * const * args, unsigned num) {
    bool is_spatial = is_any_spatial(args,num);
    if(is_spatial) {
        sl_enc * enc = new sl_enc(m,*this);
        enc->is_spatial = is_spatial;

        vector<expr*> andargsA( num );
        vector<expr*> andargsB( num );
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

        vector<expr*> orargsA( num );
        vector<expr*> andargsB( num );
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

sl_enc::sl_enc(ast_manager & _m, slstar_encoder & _enc) : m(_m), enc(_enc){
    Yn = nullptr;
    Yl = nullptr;
    Yr = nullptr;
    Yd = nullptr;
    A = nullptr;
    B = nullptr;
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