
#ifndef SLSTAR_MODEL_CONVERTER_H_
#define SLSTAR_MODEL_CONVERTER_H_

#include "tactic/model_converter.h"
#include "ast/slstar/slstar_encoder.h"
#include "model/model_evaluator.h"

class slstar_model_converter : public model_converter {
    ast_manager & m;
    std::set<app*>              loc_constants;
    std::set<std::string>       loc_constants_names;
    std::vector<expr*>          list_locs;
    std::vector<expr*>          tree_locs;

    std::string                  Xn_name;
    std::string                  Xl_name;
    std::string                  Xr_name;
    std::string                  Xd_name;

    std::string                 f_next_name;
    std::string                 f_left_name;
    std::string                 f_right_name;
    std::string                 f_dat_name;

public:
    slstar_model_converter(ast_manager & m, slstar_encoder & enc);

    ~slstar_model_converter() override;

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

    void convert(model * mc, model * mdl);
    void register_const(std::string newname, func_decl * orig, model_core * mc, model * mdl, expr * e = nullptr);
    void register_func(std::string newname, func_decl * orig, model_core * mc, model * mdl);
    bool is_footprint_decl_list(func_decl * decl);
    bool is_footprint_decl_tree(func_decl * decl);
    bool is_footprint_fld(func_decl * decl);
    expr * gather_elements(std::vector<expr*> & locs, func_decl * decl, model * mc);
    void check_single_loc(std::vector<expr*> & elements, expr * loc, func_decl * Xdecl, model * mc);
};

class isless {
    ast_manager   & m;
    model         * mc;
    arith_util      au;
public:
    isless(ast_manager & m, model * mc);
    bool operator()(expr * a, expr * b);
};


#endif
