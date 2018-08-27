
#ifndef SLSTAR_MODEL_CONVERTER_H_
#define SLSTAR_MODEL_CONVERTER_H_

#include "tactic/model_converter.h"
#include "ast/slstar/slstar_encoder.h"
class slstar_model_converter : public model_converter {
    ast_manager & m;
    slstar_encoder & enc;

public:
    slstar_model_converter(ast_manager & m, slstar_encoder & enc):
        m(m),
        enc(enc) {
    }

    ~slstar_model_converter() override {
    }

    void operator()(model_ref & md, unsigned goal_idx) override {
        
    }

    void operator()(model_ref & md) override {
        operator()(md, 0);
    }

    void display(std::ostream & out) override;

    model_converter * translate(ast_translation & translator) override;

protected:

    void convert(model_core * mc, model * float_mdl);
};


#endif
