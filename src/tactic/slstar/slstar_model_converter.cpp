#include "ast/ast_smt2_pp.h"
#include "tactic/slstar/slstar_model_converter.h"

slstar_model_converter::slstar_model_converter(ast_manager & m, slstar_encoder & enc):
    m(m),
    locs(enc.encoded_const_names) 
{
    Xdname = enc.Xd->get_decl()->get_name().bare_str();
    Xnname = enc.Xn->get_decl()->get_name().bare_str();
    Xlname = enc.Xl->get_decl()->get_name().bare_str();
    Xrname = enc.Xr->get_decl()->get_name().bare_str();

    f_next_name = enc.f_next->get_name().bare_str();
    f_left_name = enc.f_left->get_name().bare_str();
    f_right_name = enc.f_right->get_name().bare_str();
    f_dat_name = enc.f_dat->get_name().bare_str();
}

void slstar_model_converter::display(std::ostream & out) {
    out << "(slstar_model_converter";

    out << ")";
}

model_converter * slstar_model_converter::translate(ast_translation & translator) {
    return nullptr;
}

void slstar_model_converter::convert(model_core * mc, model * mdl) {
    unsigned sz = mc->get_num_constants();
    for(unsigned i=0; i<sz; i++){
        func_decl * c = mc->get_constant(i);
        std::string name = c->get_name().bare_str();
        if(name.substr(0,9) == "list.null" /*|| name.substr(0,9) == "tree.null"*/){
            register_const("null", c, mc, mdl);
            continue;
        }
        if(is_footprint_decl(c)){
           mdl->register_decl(c, m.mk_true());
           continue;
	}
        if(locs.find(name) != locs.end() || is_footprint_decl(c)){
            int char_pos = name.find_last_of('!');
            if(char_pos != -1){
                name = name.substr(0,char_pos);
            }
            register_const(name, c, mc, mdl);
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
            register_func(name, f, mc, mdl);
        }
    }
}

void slstar_model_converter::register_const(std::string newname, func_decl * orig, model_core * mc, model * mdl){
    mdl->register_decl(
        m.mk_func_decl(symbol(newname.c_str()), 
        orig->get_arity(), orig->get_domain(), orig->get_range()), mc->get_const_interp(orig));
}

void slstar_model_converter::register_func(std::string newname, func_decl * orig, model_core * mc, model * mdl){
    func_interp * val = mc->get_func_interp(orig)->copy();
    mdl->register_decl(
        m.mk_func_decl(symbol(newname.c_str()), 
        orig->get_arity(), orig->get_domain(), orig->get_range()), val);
}

bool slstar_model_converter::is_footprint_decl(func_decl * decl) {
    std::string name = decl->get_name().bare_str();
    return 
        name == Xdname ||
        name == Xnname ||
        name == Xlname ||
        name == Xrname;
}

bool slstar_model_converter::is_footprint_fld(func_decl * decl){
    symbol sym = decl->get_name();
    if(sym.is_numerical()){
        return false;
    }
    std::string name = sym.bare_str();
    return
        name == f_next_name ||
        name == f_left_name ||
        name == f_right_name ||
        name == f_dat_name;
}

