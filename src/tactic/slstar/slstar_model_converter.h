
#ifndef SLSTAR_MODEL_CONVERTER_H_
#define SLSTAR_MODEL_CONVERTER_H_

#include "tactic/model_converter.h"
#include "ast/slstar/slstar_encoder.h"
#include "model/model_evaluator.h"

class slstar_model_converter : public model_converter {
    ast_manager & m;
    array_util m_arrayutil;
    std::unordered_set<app*>              loc_constants;
    std::unordered_set<std::string>       loc_constants_names;
    expr_ref_vector const&                list_locs;
    expr_ref_vector const&                tree_locs;

    std::string                  Xn_name;
    std::string                  Xl_name;
    std::string                  Xr_name;
    std::string                  Xd_name;

    std::string                           f_next_name;
    std::string                           f_left_name;
    std::string                           f_right_name;
    std::unordered_set<std::string>       f_dat_names;

    bool needs_tree_footprint;
    bool needs_list_footprint;
public:
    slstar_model_converter(ast_manager & m, slstar_encoder & enc);

    ~slstar_model_converter() override;

    void operator()(model_ref & md) override {
        model * new_model = alloc(model, m);
        convert(md.get(), new_model);
        md = new_model;
    }

    void display(std::ostream & out) override;

    model_converter * translate(ast_translation & translator) override;

protected:

    void convert(model * mc, model * mdl);
    void register_const(symbol newname, func_decl * orig, model_core * mc, model * mdl, expr * e = nullptr);
    void register_func(symbol newname, func_decl * orig, model_core * mc, model * mdl);
    bool is_footprint_decl_list(func_decl * decl);
    bool is_footprint_decl_tree(func_decl * decl);
    bool is_footprint_fld(func_decl * decl);
    bool is_footprint_helper_set(const std::string s);
    bool is_footprint_helper_varlist(const std::string s);
    bool is_reach_constraint(const std::string s);
    expr * gather_elements(expr_ref_vector const& locs, func_decl * decl, model * mc);
    void check_single_loc(std::vector<expr*> & elements, expr * loc, func_decl * Xdecl, model * mc);
    void emplace_array_helper(std::unordered_set<symbol> &array_helpers, model * mc, func_decl * decl);
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
