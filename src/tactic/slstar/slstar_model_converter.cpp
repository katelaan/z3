#include "ast/ast_smt2_pp.h"
#include "tactic/slstar/slstar_model_converter.h"

void slstar_model_converter::display(std::ostream & out) {
    out << "(slstar_model_converter";

    out << ")";
}

model_converter * slstar_model_converter::translate(ast_translation & translator) {
    return nullptr;
}

void slstar_model_converter::convert(model_core * mc, model * float_mdl) {

}

