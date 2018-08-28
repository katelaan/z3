#ifndef PRED_ENCODER_H_
#define PRED_ENCODER_H_

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

class slstar_encoder;
class sl_enc;

class pred_encoder {
protected:
    slstar_encoder           & enc;
    ast_manager              & m;
public:
    pred_encoder(slstar_encoder & enc);
    ~pred_encoder();

    app * mk_isstop(expr * xenc, std::vector<expr*> & stops);
    virtual app * mk_is_successor(expr * x, expr * y) = 0;
    virtual app * mk_defineY(sl_enc * enc, expr * Z) = 0;
    app * mk_reach1(expr * Z, 
        std::vector<func_decl*> & prev_reach, 
        std::vector<expr*> & xlocs, 
        std::vector<expr*> & stops);
    app * mk_reachN(std::vector<func_decl*> & prev_reach, std::vector<expr*> & xlocs);
    app * mk_reachability(expr * Z, std::vector<func_decl*> & prev_reach, std::vector<expr*> & stops, std::vector<expr*> xlocs, int bound);
    app * mk_emptyZ(expr * xenc, std::vector<expr*> & xlocs, std::vector<expr*> & stops);
    app * mk_footprint(expr * xenc,
        expr * Z, 
        std::vector<expr*> & xlocs, 
        std::vector<func_decl*> & prev_reach, 
        std::vector<expr*> & stops);
    virtual app * mk_all_succs_different(expr * xi, expr * xj) = 0;
    virtual app * mk_oneparent(expr * Z, std::vector<expr*> & xlocs) = 0;
    app * mk_structure(expr * xenc, 
        expr * Z, 
        std::vector<expr*> & xlocs, 
        std::vector<func_decl*> & prev_reach, 
        std::vector<expr*> & stops);
    app * mk_stopseq(expr * xenc, std::vector<expr*> & stops);
    app * mk_stopsoccur(expr * xenc, expr * Z, std::vector<expr*> & xlocs, std::vector<expr*> & stops );
    virtual app * mk_stopleaves(expr * Z, std::vector<expr*> & xlocs, std::vector<expr*> & stops ) = 0;
    app * mk_Rn_f(func_decl * f, func_decl * rn, expr * x, expr * y, expr * Z);
    app * mk_fstop(expr * xp, expr * s, func_decl * f, expr * Z, std::vector<expr*> & xlocs, 
        std::vector<func_decl*> & prev_reach);
    app * mk_is_location(expr* xenc, std::vector<expr*> & xlocs);
    app * mk_bdata(expr * P, expr * Z, func_decl * f, std::vector<expr*> & xlocs, 
        std::vector<func_decl*> & prev_reach);
    app * mk_udata(expr * P, expr * Z, std::vector<expr*> & xlocs);
};

#endif //PRED_ENCODER_H_