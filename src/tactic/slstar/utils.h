#ifndef SLSTAR_REDUCE_UTILS_H_
#define SLSTAR_REDUCE_UTILS_H_

#include "ast/ast.h"

void pcount(std::ostream & out, ast* e);

void print_usages(expr* e, ast_manager& m, std::string msg);

#endif