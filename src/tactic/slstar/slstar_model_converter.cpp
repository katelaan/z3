#include "ast/ast_smt2_pp.h"
#include "tactic/slstar/slstar_model_converter.h"

slstar_model_converter::slstar_model_converter(ast_manager & m, slstar_encoder & enc):
    m(m),
    loc_constants(enc.encoded_const),
    list_locs(enc.list_locs),
    tree_locs(enc.tree_locs)
{
    Xd_name = enc.Xd->get_decl()->get_name().bare_str();
    Xn_name = enc.Xn->get_decl()->get_name().bare_str();;
    Xl_name = enc.Xl->get_decl()->get_name().bare_str();;
    Xr_name = enc.Xr->get_decl()->get_name().bare_str();;

    f_next_name = enc.f_next->get_name().bare_str();
    f_left_name = enc.f_left->get_name().bare_str();
    f_right_name = enc.f_right->get_name().bare_str();
    for(auto it=enc.f_dat_map.begin(); it!=enc.f_dat_map.end(); ++it ) {
        std::string f_dat_name = it->second->get_name().bare_str();
        f_dat_names.emplace(f_dat_name);
    }

    for(auto it=list_locs.begin(); it!=list_locs.end(); ++it) {
        m.inc_ref(*it);
    }
    for(auto it=tree_locs.begin(); it!=tree_locs.end(); ++it) {
        m.inc_ref(*it);
    }
    for(auto it=loc_constants.begin(); it!=loc_constants.end(); ++it) {
        m.inc_ref(*it);
        func_decl * decl = (*it)->get_decl();
        std::string name = decl->get_name().bare_str();
        loc_constants_names.emplace(name);
    }
}

slstar_model_converter::~slstar_model_converter(){
    for(auto it=list_locs.begin(); it!=list_locs.end(); it++) {
        m.dec_ref(*it);
    }
    for(auto it=tree_locs.begin(); it!=tree_locs.end(); it++) {
        m.dec_ref(*it);
    }    
    for(auto it=loc_constants.begin(); it!=loc_constants.end(); it++) {
        m.dec_ref(*it);
    }
}

void slstar_model_converter::display(std::ostream & out) {
    out << "(slstar_model_converter";

    out << ")";
}

model_converter * slstar_model_converter::translate(ast_translation & translator) {
    return nullptr;
}

void slstar_model_converter::convert(model * mc, model * mdl) {
    unsigned sz = mc->get_num_constants();

    for(unsigned i=0; i<sz; i++){
        func_decl * c = mc->get_constant(i);
        std::string name = c->get_name().bare_str();
        std::string rname = name;

        int char_pos = name.find_last_of('!');
        if(char_pos != -1){
            rname = name.substr(0,char_pos);
        }
        if(loc_constants_names.find(name) != loc_constants_names.end() || rname == "null"){
            register_const(rname, c, mc, mdl);
            continue;
        }
        if(is_footprint_decl_list(c)){
            register_const(rname, c, mc, mdl, gather_elements(list_locs,c,mc));
            continue;
        }
        if(is_footprint_decl_tree(c)){
            register_const(rname, c, mc, mdl, gather_elements(list_locs,c,mc));
            continue;
        }

    }
    sz = mc->get_num_functions();
    for(unsigned i=0; i<sz; i++) {
        func_decl * f = mc->get_function(i);
        if( is_footprint_fld(f)){
            std::string name = f->get_name().bare_str();
            int char_pos = name.find_last_of('!');
            if(char_pos != -1){
                name = name.substr(0,char_pos);
            }
            register_func(name, f, mc, mdl); continue;
        }
    }
}

void slstar_model_converter::check_single_loc(std::vector<expr*> & elements, expr * loc, func_decl * Xdecl, model * mc) {
    expr_ref   result(m);

    parameter p = to_app(mc->get_const_interp(Xdecl))->get_decl()->get_parameter(0);
    func_decl * array_decl = (func_decl*) to_decl(p.get_ast());
    
    model_evaluator ev(*mc);
    ev.set_model_completion(true);
    expr * e = m.mk_app(array_decl, loc);
    ev(e, result);
    m.inc_ref(e);
    m.dec_ref(e);
    if(m.is_true(result.get())) {
        try {
            ev(loc, result);
            elements.push_back(result.get());
        } catch (model_evaluator_exception & ex) {
            (void)ex;
            SASSERT(false);
        }
    }
}

expr * slstar_model_converter::gather_elements(std::vector<expr*> & locs, func_decl * Xdecl, model * mc) {
    std::vector<expr*> elements;

    // check tree/list locations X={x1,x2,...,xN}
    for(auto it=locs.begin(); it != locs.end(); it++){
        check_single_loc(elements, *it, Xdecl, mc);
    }
    // check locations defined as constants in formula
    for(auto it=loc_constants.begin(); it != loc_constants.end(); it++){
        check_single_loc(elements, *it, Xdecl, mc);
    }

    std::sort(elements.begin(), elements.end(), isless(m,mc));

    std::vector<sort*> domain;
    for(auto it=elements.begin(); it!=elements.end(); it++){
        domain.push_back(m.get_sort(*it));
    }
    func_decl * fd = m.mk_func_decl(symbol(""), elements.size(), &domain[0], Xdecl->get_range());
    return m.mk_app(fd, elements.size(), &elements[0]);
}

void slstar_model_converter::register_const(std::string newname, func_decl * orig, model_core * mc, model * mdl, expr * e){
    if(e == nullptr) {
        e = mc->get_const_interp(orig);
    }
    mdl->register_decl(
        m.mk_func_decl(symbol(newname.c_str()), 
        orig->get_arity(), orig->get_domain(), orig->get_range()), e);
}

void slstar_model_converter::register_func(std::string newname, func_decl * orig, model_core * mc, model * mdl){
    func_interp * val = mc->get_func_interp(orig)->copy();
    mdl->register_decl(
        m.mk_func_decl(symbol(newname.c_str()), 
        orig->get_arity(), orig->get_domain(), orig->get_range()), val);
}

bool slstar_model_converter::is_footprint_decl_list(func_decl * decl) {
    std::string name = decl->get_name().bare_str();
    return 
        name == Xd_name ||
        name == Xn_name;
}

bool slstar_model_converter::is_footprint_decl_tree(func_decl * decl) {
    std::string name = decl->get_name().bare_str();
    return 
        name == Xd_name ||
        name == Xl_name ||
        name == Xr_name;
}

bool slstar_model_converter::is_footprint_fld(func_decl * decl){
    symbol sym = decl->get_name();
    if(sym.is_numerical()){
        return false;
    }
    std::string name = sym.bare_str();
    bool is_f_dat_name = (f_dat_names.find(name) != f_dat_names.end());
    return
        name == f_next_name ||
        name == f_left_name ||
        name == f_right_name ||
        is_f_dat_name;
}


isless::isless(ast_manager & m, model * mc) : m(m), mc(mc), au(m) { 
}

bool isless::operator()(expr * a, expr * b) {
    expr_ref   result(m);
    expr * e = au.mk_lt(a,b);
    mc->eval(e, result);
    m.inc_ref(e);
    m.dec_ref(e);
    return m.is_true(result.get());
}

