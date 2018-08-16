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

app * slstar_encoder::mk_isstop(expr * xenc, std::vector<expr*> & stops) {
    std::vector<expr*> orargs;
    orargs.push_back( m.mk_eq(xenc, mk_encoded_loc(util.mk_null()) ) );
    for(unsigned i=0; i<stops.size(); i++) {
        orargs.push_back( m.mk_eq(xenc, mk_encoded_loc( stops[i])));
    }
    return m.mk_or(orargs.size(), &orargs[0]);
}

app * slstar_encoder::mk_is_successor_list(expr * x, expr * y) {
    expr* f_next_x = m.mk_app(f_next,x);
    return m.mk_eq(f_next_x,y);
}

app * slstar_encoder::mk_is_successor_tree(expr * x, expr * y) {
    expr* f_left_x = m.mk_app(f_left,x);
    expr* f_right_x = m.mk_app(f_right,x);
    return m.mk_or(m.mk_eq(f_left_x,y), m.mk_eq(f_right_x,y));
}

app * slstar_encoder::mk_defineY_tree(sl_enc * enc, expr * Z) {
    std::vector<expr*> andargs;
    andargs.push_back(m.mk_eq(enc->Yd, Z));
    andargs.push_back(m.mk_eq(enc->Yl, Z));
    andargs.push_back(m.mk_eq(enc->Yr, Z));
    andargs.push_back(mk_is_empty(enc->Yn));
    return m.mk_and(andargs.size(), &andargs[0]);
}
app * slstar_encoder::mk_defineY_list(sl_enc * enc, expr * Z) {
    std::vector<expr*> andargs;
    andargs.push_back(m.mk_eq(enc->Yd, Z));
    andargs.push_back(mk_is_empty(enc->Yl));
    andargs.push_back(mk_is_empty(enc->Yr));
    andargs.push_back(m.mk_eq(enc->Yn, Z));
    return m.mk_and(andargs.size(), &andargs[0]);
}

app * slstar_encoder::mk_reach1(expr * Z, 
        std::vector<func_decl*> & prev_reach, 
        std::vector<expr*> & xlocs, 
        std::vector<expr*> & stops,
        decl_kind k) {
    sort * const domain[] = {m_int_sort, m_int_sort}; //TODOsl configurable Loc-Sort
    func_decl * reach = m.mk_fresh_func_decl("reach", 2, domain, m.mk_bool_sort());
    
    std::vector<expr*> andargs;
    for(unsigned i=0; i<xlocs.size(); i++) {
        for(unsigned j=0; j<xlocs.size(); j++) {
            //if (i==j) continue; TODOsl?
            expr * tmp;
            if(k == OP_SLSTAR_LIST)  {
                tmp = m.mk_and(mk_is_element(xlocs[i], Z), m.mk_not(mk_isstop(xlocs[j], stops)), mk_is_successor_list(xlocs[i], xlocs[j]) );
            } else if(k == OP_SLSTAR_TREE) {
                tmp = m.mk_and(mk_is_element(xlocs[i], Z), m.mk_not(mk_isstop(xlocs[j], stops)), mk_is_successor_tree(xlocs[i], xlocs[j]) );
            }
            expr * reachargs[] = {xlocs[i], xlocs[j]};
            andargs.push_back( m.mk_iff(m.mk_app(reach, reachargs), tmp));
        }
    }
    prev_reach.push_back(reach);
    return m.mk_and(andargs.size(), &andargs[0]);
}
app * slstar_encoder::mk_reachN(std::vector<func_decl*> & prev_reach, std::vector<expr*> & xlocs) {
    sort * const domain[] = {m_int_sort, m_int_sort}; //TODOsl configurable Loc-Sort
    func_decl * reach = m.mk_fresh_func_decl("reach", 2, domain, m.mk_bool_sort());
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

app * slstar_encoder::mk_reachability_list( expr * Z, std::vector<func_decl*> & prev_reach, std::vector<expr*> & stops) {
    std::vector<expr*> andargs;
    andargs.push_back( mk_reach1( Z, prev_reach, list_locs, stops, OP_SLSTAR_LIST));
    for(int i=1; i<bounds.n_list; i++){
        andargs.push_back( mk_reachN(prev_reach, list_locs) );
    }
    SASSERT( prev_reach.size() == andargs.size() );
    SASSERT( bounds.n_list == (int) andargs.size() );
    return m.mk_and( bounds.n_list, &andargs[0]);
}

app * slstar_encoder::mk_reachability_tree( expr * Z, std::vector<func_decl*> & prev_reach, std::vector<expr*> & stops) {
    std::vector<expr*> andargs;
    andargs.push_back( mk_reach1(Z, prev_reach, tree_locs, stops, OP_SLSTAR_TREE));
    for(int i=1; i<bounds.n_tree; i++){
        andargs.push_back( mk_reachN(prev_reach, tree_locs));
    }
    SASSERT( prev_reach.size() ==  andargs.size() );
    SASSERT( bounds.n_tree == (int) andargs.size() );
    return m.mk_and( bounds.n_tree, &andargs[0]);
}

app * slstar_encoder::mk_emptyZ(expr * xenc, std::vector<expr*> & xlocs, std::vector<expr*> & stops) {
    std::vector<expr*> andargs;
    for(unsigned i=0; i<xlocs.size(); i++) {
        andargs.push_back( m.mk_eq(xenc,xlocs[i]) );
    }
    return m.mk_or( mk_isstop(xenc, stops), m.mk_and(andargs.size(), &andargs[0]) );
}
app * slstar_encoder::mk_footprint(expr * xenc, 
    expr * Z, 
    std::vector<expr*> & xlocs, 
    std::vector<func_decl*> & prev_reach, 
    std::vector<expr*> & stops) 
{
    std::vector<expr*> andargs;
    for(unsigned i=0; i<xlocs.size(); i++) {
        func_decl * rN = prev_reach[prev_reach.size()-1];
        expr * reachargs[] = {xenc, xlocs[i]};
        andargs.push_back( m.mk_iff(mk_is_element(xlocs[i], Z), 
            m.mk_or(m.mk_eq(xenc, xlocs[i]), m.mk_app(rN, reachargs))) );
    }
    return m.mk_and(
        mk_subset_eq(Z, mk_set_from_elements(&xlocs[0], xlocs.size())),
        m.mk_implies(mk_emptyZ(xenc,xlocs, stops), mk_is_empty(Z)),
        m.mk_implies(m.mk_not(mk_emptyZ(xenc,xlocs, stops)), 
            m.mk_and(andargs.size(), &andargs[0]) )); // TODOsl cache emptyZ?
}

app * slstar_encoder::mk_all_succs_different_list(expr * xi, expr * xj) {
    return m.mk_implies(
        m.mk_eq(m.mk_app(f_next,xi), m.mk_app(f_next,xj) ),
        m.mk_eq(m.mk_app(f_next,xi), util.mk_null()));
}

app * slstar_encoder::mk_all_succs_different_tree(expr * xi, expr * xj) {
    expr * andargs[4];
    andargs[0] = m.mk_implies(
        m.mk_eq(m.mk_app(f_left,xi), m.mk_app(f_left,xj) ),
        m.mk_eq(m.mk_app(f_left,xi), util.mk_null()));

    andargs[1] = m.mk_implies(
        m.mk_eq(m.mk_app(f_right,xi), m.mk_app(f_right,xj) ),
        m.mk_eq(m.mk_app(f_right,xi), util.mk_null()));

    andargs[2] = m.mk_implies(
        m.mk_eq(m.mk_app(f_left,xi), m.mk_app(f_right,xj) ),
        m.mk_eq(m.mk_app(f_left,xi), util.mk_null()));

    andargs[3] = m.mk_implies(
        m.mk_eq(m.mk_app(f_right,xi), m.mk_app(f_left,xj) ),
        m.mk_eq(m.mk_app(f_right,xi), util.mk_null()));
    return m.mk_and(4,andargs);
}

app * slstar_encoder::mk_oneparent_list(expr * Z, std::vector<expr*> & xlocs) {
    std::vector<expr*> andargs;
    for(unsigned i = 0; i<xlocs.size(); i++) {
        for(unsigned j = 0; j<xlocs.size(); j++) {
            andargs.push_back( m.mk_implies(
                m.mk_and( mk_is_element(xlocs[j], Z), m.mk_not(m.mk_eq(xlocs[i], xlocs[j])) ),
                mk_all_succs_different_list(xlocs[i], xlocs[j])    
            ));
        }
    }
    return  m.mk_and(andargs.size(), &andargs[0]);
}

app * slstar_encoder::mk_oneparent_tree(expr * Z, std::vector<expr*> & xlocs) {
    std::vector<expr*> andargs;
    for(unsigned i = 0; i<xlocs.size(); i++) {
        std::vector<expr*> andargs2;
        andargs2.push_back(m.mk_implies(
            mk_is_element(xlocs[i], Z),
            m.mk_implies(
                m.mk_eq(m.mk_app(f_left,xlocs[i]), m.mk_app(f_left,xlocs[i])),
                m.mk_eq(m.mk_app(f_left,xlocs[i]), mk_encoded_loc(util.mk_null())) )));
        andargs.push_back( m.mk_and(andargs2.size(), &andargs[0]));
        
        for(unsigned j = 0; j<xlocs.size(); j++) {
            andargs.push_back( m.mk_implies(
                m.mk_and( mk_is_element(xlocs[j], Z), m.mk_not(m.mk_eq(xlocs[i], xlocs[j])) ),
                mk_all_succs_different_list(xlocs[i], xlocs[j])    
            ));
        }
    }
    return  m.mk_and(andargs.size(), &andargs[0]);
}

app * slstar_encoder::mk_structure_list(expr * xenc, 
    expr * Z, 
    std::vector<expr*> & xlocs, 
    std::vector<func_decl*> & prev_reach, 
    std::vector<expr*> & stops) 
{
    func_decl * rN = prev_reach[prev_reach.size()-1];
    expr * reachargs[] = {xenc, xenc};
    return m.mk_and(
        m.mk_implies(m.mk_not(mk_isstop(xenc, stops)), mk_is_element(xenc,Z)),
        mk_oneparent_list(Z,xlocs),
        m.mk_app(rN, reachargs));
}

app * slstar_encoder::mk_structure_tree(expr * xenc, 
    expr * Z, 
    std::vector<expr*> & xlocs, 
    std::vector<func_decl*> & prev_reach, 
    std::vector<expr*> & stops) 
{
    func_decl * rN = prev_reach[prev_reach.size()-1];
    expr * reachargs[] = {xenc, xenc};
    return m.mk_and(
        m.mk_implies(m.mk_not(mk_isstop(xenc, stops)), mk_is_element(xenc,Z)),
        mk_oneparent_tree(Z,xlocs),
        m.mk_app(rN, reachargs));
}

app * slstar_encoder::mk_stopseq(expr * xenc, std::vector<expr*> & stops) {
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


app * slstar_encoder::mk_stopsoccur_list(expr * xenc, expr * Z, std::vector<expr*> & xlocs, std::vector<expr*> & stops ) {
    std::vector<expr*> andargs, orargs;
    for(unsigned i=0; i<stops.size(); i++) {
        for(unsigned p=0; p<xlocs.size(); p++) {
            orargs.push_back( m.mk_and(mk_is_element(xlocs[p],Z), mk_is_successor_list(xlocs[p], stops[i]) ) );
        }
        andargs.push_back(m.mk_or(orargs.size(), &orargs[0]));
        orargs.clear();
    }
    return m.mk_implies( mk_isstop(xenc, stops), m.mk_and(andargs.size(), &andargs[0]));
}

app * slstar_encoder::mk_stopsoccur_tree(expr * xenc, expr * Z, std::vector<expr*> & xlocs, std::vector<expr*> & stops ) {
    std::vector<expr*> andargs, orargs;
    for(unsigned i=0; i<stops.size(); i++) {
        for(unsigned p=0; p<xlocs.size(); p++) {
            orargs.push_back( m.mk_and(mk_is_element(xlocs[p],Z), mk_is_successor_tree(xlocs[p], stops[i]) ) );
        }
        andargs.push_back(m.mk_or(orargs.size(), &orargs[0]));
        orargs.clear();
    }
    return m.mk_implies( mk_isstop(xenc, stops), m.mk_and(andargs.size(), &andargs[0]));
}

app * slstar_encoder::mk_stopleaves_list(expr * Z, std::vector<expr*> & xlocs, std::vector<expr*> & stops ){
    std::vector<expr*> andargs;
    for(unsigned i=0; i<xlocs.size(); i++ ) {
        andargs.push_back(m.mk_implies(
            m.mk_and(mk_is_element(xlocs[i], Z), m.mk_not(mk_is_element(m.mk_app(f_next, xlocs[i]),Z)) ), 
            mk_isstop(m.mk_app(f_next, xlocs[i]), stops)));
    }
    return m.mk_and(andargs.size(), &andargs[0]);
}

app * slstar_encoder::mk_stopleaves_tree(expr * Z, std::vector<expr*> & xlocs, std::vector<expr*> & stops ){
    std::vector<expr*> andargs;
    for(unsigned i=0; i<xlocs.size(); i++ ) {
        andargs.push_back(m.mk_implies(
            m.mk_and(mk_is_element(xlocs[i], Z), m.mk_not(mk_is_element(m.mk_app(f_left, xlocs[i]),Z)) ), 
            mk_isstop(m.mk_app(f_left, xlocs[i]), stops)));
        andargs.push_back(m.mk_implies(
            m.mk_and(mk_is_element(xlocs[i], Z), m.mk_not(mk_is_element(m.mk_app(f_right, xlocs[i]),Z)) ), 
            mk_isstop(m.mk_app(f_right, xlocs[i]), stops)));
    }
    return m.mk_and(andargs.size(), &andargs[0]);
}

app * slstar_encoder::mk_Rn_f(func_decl * f, func_decl * rn, expr * x, expr * y, expr * Z) {
    expr * reachargs[] = {m.mk_app(f,x),y};
    return m.mk_or(
        m.mk_eq(m.mk_app(f,x), y),
        m.mk_and(
            mk_is_element(m.mk_app(f,x), Z), 
            m.mk_app(rn,reachargs)));
}

app * slstar_encoder::mk_fstop_tree(expr * xp, expr * s, func_decl * f, expr * Z, std::vector<expr*> & xlocs, 
        std::vector<func_decl*> & prev_reach) 
{
    func_decl * rN = prev_reach[prev_reach.size()-1];
    std::vector<expr*> orargs;
    orargs.push_back(m.mk_app(f, xp));
    for(unsigned c=0; c<xlocs.size(); c++) {
        orargs.push_back( m.mk_and( 
            mk_Rn_f(f,rN,xp,xlocs[c],Z),
            mk_is_element(xlocs[c],Z), 
            mk_is_successor_tree(xlocs[c], s) ) );
    }
    return m.mk_or(orargs.size(), &orargs[0]);
}

app * slstar_encoder::mk_ordered_tree(expr * Z, 
    std::vector<expr*> & xlocs, 
    std::vector<expr*> & stops,
    std::vector<func_decl*> & prev_reach) 
{
    std::vector<expr*> andargs;
    for(unsigned i=0; i<stops.size()-1; i++) {
        std::vector<expr*> orargs;
        for(unsigned p=0; p<xlocs.size(); p++) {
            orargs.push_back(m.mk_and(
                mk_is_element(xlocs[p], Z),
                mk_fstop_tree(xlocs[p], stops[i], f_left, Z, xlocs, prev_reach),
                mk_fstop_tree(xlocs[p], stops[i+1], f_right, Z, xlocs, prev_reach) ));
        }
        andargs.push_back(m.mk_or(orargs.size(), &orargs[0]));
    }
    return m.mk_and(andargs.size(), &andargs[0]);
}

app * slstar_encoder::mk_global_constraints() {
    expr * unionargs[] = {Xn,Xl,Xr,Xd};
    expr * X = m.mk_fresh_const("X", m_array_sort);
    expr * enc_null = mk_encoded_loc(util.mk_null());

    expr * unionargsLR[] = {Xl,Xr}; 
    expr * Xlr = mk_union(unionargsLR,2); //unionargs+1; TODOsl test
    return m.mk_and(
        m.mk_eq(X,mk_union(unionargs,4)),
        m.mk_not(mk_is_element(enc_null, X)),
        mk_is_empty( mk_intersect(Xn,Xlr)));
}

void slstar_encoder::prepare(sl_bounds bd) {
    SASSERT(list_locs.size()==0 && tree_locs.size()==0);
    bounds = bd;
    for(int i=0; i<bd.n_list; i++) {
        app * fresh = m.mk_fresh_const("xl", m_int_sort); //TODOsl get sort
        m.inc_ref(fresh);
        list_locs.push_back(fresh);
    }
    for(int i=0; i<bd.n_tree; i++) {
        app * fresh = m.mk_fresh_const("xt", m_int_sort); //TODOsl get sort
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
    if(m_int_sort) m.dec_ref(m_int_sort);

    if(f_next) m.dec_ref(f_next);
    if(f_dat) m.dec_ref(f_dat);
    if(f_left) m.dec_ref(f_left);
    if(f_right) m.dec_ref(f_right);

    clear_enc_dict();
    clear_loc_vars();
}

app * slstar_encoder::mk_fresh_array(char const * prefix) {
    return m.mk_fresh_const(prefix,m_array_sort);
}

app * slstar_encoder::mk_empty_array() {
    return m_arrayutil.mk_empty_set(m_array_sort);
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
    if(locencoding.find(x) != locencoding.end()){
        app * ret = locencoding[x];
        return ret;
    }

    app* xt = to_app(x);
    func_decl * fdec =xt->get_decl();
    app * fresh = m.mk_fresh_const(fdec->get_name().bare_str(), m_int_sort); //TODOsl get sort 
    locencoding[x] = fresh;
    return fresh;
}

void slstar_encoder::add_list(expr * ex, expr * const * args, unsigned num) {
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

void slstar_encoder::add_tree(expr * ex, expr * const * args, unsigned num) {
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

void slstar_encoder::add_eq(expr * ex, expr * const * args, unsigned num) {
    SASSERT(num==2);
    add_floc_fdat(ex,args,num);
    if(util.is_loc(args[0])) {
        expr* lhs = mk_encoded_loc(args[0]);
        expr* rhs = mk_encoded_loc(args[1]);
        m.dec_ref(encoding[ex]->A);
        encoding[ex]->A = m.mk_eq(lhs,rhs);
        m.inc_ref(encoding[ex]->A);
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
    }
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