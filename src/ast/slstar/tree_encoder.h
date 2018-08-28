#ifndef TREE_ENCODER_H_
#define TREE_ENCODER_H_

#include <map>
#include <set>
#include "ast/ast.h"
#include "util/obj_hashtable.h"
#include "util/ref_util.h"
#include "ast/slstar_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/dl_decl_plugin.h"
#include "ast/pb_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/slstar/pred_encoder.h"
#include "ast/slstar/slstar_encoder.h"

class tree_encoder : public pred_encoder {

public:
    tree_encoder(slstar_encoder & enc);
    app * mk_is_successor(expr * x, expr * y);
    app * mk_ordered(expr * Z, 
        std::vector<expr*> & xlocs, 
        std::vector<expr*> & stops,
        std::vector<func_decl*> & prev_reach);
    app * mk_defineY(sl_enc * e, expr * Z);
    app * mk_all_succs_different(expr * xi, expr * xj);
    app * mk_oneparent(expr * Z, std::vector<expr*> & xlocs);
    app * mk_stopleaves(expr * Z, std::vector<expr*> & xlocs, std::vector<expr*> & stops );
};

#endif //TREE_ENCODER_H_