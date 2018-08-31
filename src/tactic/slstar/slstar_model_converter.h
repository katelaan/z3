
#ifndef SLSTAR_MODEL_CONVERTER_H_
#define SLSTAR_MODEL_CONVERTER_H_

#include "tactic/model_converter.h"
#include "ast/slstar/slstar_encoder.h"
class slstar_model_converter : public model_converter {
    ast_manager & m;
    std::set<std::string> locs;
    std::string Xnname;
    std::string Xlname;
    std::string Xrname;
    std::string Xdname;
    std::string f_next_name;
    std::string f_left_name;
    std::string f_right_name;
    std::string f_dat_name;

public:
    slstar_model_converter(ast_manager & m, slstar_encoder & enc);

    ~slstar_model_converter() override {
    }

    void operator()(model_ref & md, unsigned goal_idx) override {
        SASSERT(goal_idx == 0);
        model * new_model = alloc(model, m);
        convert(md.get(), new_model);
        md = new_model;
    }

    void operator()(model_ref & md) override {
        operator()(md, 0);
    }

    void display(std::ostream & out) override;

    model_converter * translate(ast_translation & translator) override;

protected:

    void convert(model_core * mc, model * mdl);
    void register_const(std::string newname, func_decl * orig, model_core * mc, model * mdl);
    void register_func(std::string newname, func_decl * orig, model_core * mc, model * mdl);
    bool is_footprint_decl(func_decl * decl);
    bool is_footprint_fld(func_decl * decl);
};


#endif
