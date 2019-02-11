#include "tactic/slstar/utils.h"
#include "ast/ast_smt2_pp.h"

void pcount(std::ostream & out, ast* e) {
    out << (e ? e->get_ref_count() : 0) << " ";
}

void print_usages(expr* e, ast_manager& m, std::string msg) {
    std::cout << "######## BEGIN: " << msg << " ########" << std::endl;
    std::vector<expr*> stack;
    stack.push_back(e);
    while (!stack.empty()) {
        expr* e = stack.back();
        stack.pop_back();
        std::cout << mk_ismt2_pp(e, m) << " ";
        pcount(std::cout, e);
        std::cout << std::endl;
        app* a = to_app(e);
        unsigned num = a->get_num_args();

        for (unsigned i = 0; i < num; ++i) {
            stack.push_back(a->get_arg(i));
        }
    }
    std::cout << "######## END: " << msg << " ########" << std::endl;
}