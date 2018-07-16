#include "ast/slstar_decl_plugin.h"

void slstar_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    //Const.
    op_names.push_back(builtin_name("null", OP_SLSTAR_NULL));
    op_names.push_back(builtin_name("nil", OP_SLSTAR_NULL));

    //"Keywords"
    op_names.push_back(builtin_name("unary", OP_SLSTAR_UNARY));
    op_names.push_back(builtin_name("left", OP_SLSTAR_LEFT));
    op_names.push_back(builtin_name("right", OP_SLSTAR_RIGHT));
    op_names.push_back(builtin_name("next", OP_SLSTAR_NEXT));
    op_names.push_back(builtin_name("alpha", OP_SLSTAR_ALPHA));
    op_names.push_back(builtin_name("beta", OP_SLSTAR_BETA));


    //Ops
    op_names.push_back(builtin_name("sep", OP_SLSTAR_SEP));
    op_names.push_back(builtin_name("ptol", OP_SLSTAR_POINTSTOL));
    op_names.push_back(builtin_name("ptor", OP_SLSTAR_POINTSTOR));
    op_names.push_back(builtin_name("ptolr", OP_SLSTAR_POINTSTOLR));
    op_names.push_back(builtin_name("pton", OP_SLSTAR_POINTSTON));
    op_names.push_back(builtin_name("ptod", OP_SLSTAR_POINTSTOD));
    op_names.push_back(builtin_name("tree", OP_SLSTAR_TREE));
    op_names.push_back(builtin_name("list", OP_SLSTAR_LIST));
}

void slstar_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    //Sorts
    sort_names.push_back(builtin_name("TreeLoc", SLSTAR_TREE_LOC));
    sort_names.push_back(builtin_name("ListLoc", SLSTAR_LIST_LOC));
}

decl_plugin * slstar_decl_plugin::mk_fresh() {
    return alloc(slstar_decl_plugin);
}

sort * slstar_decl_plugin::mk_slstar_tree(unsigned num_parameters, parameter const * parameters) {
    parameter const * params;

    if(num_parameters == 1) {
        if( !parameters[0].is_ast() || !is_sort(parameters[0].get_ast()) ){
            m_manager->raise_exception("TreeLoc parameter must be sort");
            return nullptr;
        }
        params = parameters;
    } else if(num_parameters == 0) {
        params = nullptr;
    } else {
        m_manager->raise_exception("TreeLoc must not have more than one parameter");
        return nullptr;
    }

    sort_size sz;
    sz = sort_size::mk_very_big(); // TODO: refine
    return m_manager->mk_sort(symbol("TreeLoc"), sort_info(m_family_id, SLSTAR_TREE_LOC, sz, num_parameters, params));
}

sort * slstar_decl_plugin::mk_slstar_list(unsigned num_parameters, parameter const * parameters) {
    parameter const * params;

    if(num_parameters == 1) {
        if( !parameters[0].is_ast() || !is_sort(parameters[0].get_ast()) ){
            m_manager->raise_exception("ListLoc parameter must be sort");
            return nullptr;
        }
        params = parameters;
    } else if(num_parameters == 0) {
        params = nullptr;
    } else {
        m_manager->raise_exception("ListLoc must not have more than one parameter");
        return nullptr;
    }

    sort_size sz;
    sz = sort_size::mk_very_big(); // TODO: refine
    return m_manager->mk_sort(symbol("ListLoc"), sort_info(m_family_id, SLSTAR_LIST_LOC, sz, num_parameters, params));
}

sort * slstar_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    switch (k) {
    case SLSTAR_TREE_LOC:
        return mk_slstar_tree(num_parameters, parameters);
    case SLSTAR_LIST_LOC:
        return mk_slstar_list(num_parameters, parameters);
    default:
        m_manager->raise_exception("unknown separation logic theory sort"); 
        return nullptr;
    }
}

func_decl * slstar_decl_plugin::mk_support_decl(symbol name, decl_kind k, unsigned num_parameters, 
                                    parameter const * parameters, unsigned arity,
                                    sort * const * domain, sort * range) {
    if(arity != 0){
        m_manager->raise_exception("Support variables must have arity 0");
        return nullptr;
    }
    sort * data_sort = m_int_sort; // slTODO get sort from parent

    return m_manager->mk_func_decl(name, arity, domain, data_sort, func_decl_info(m_family_id, k));                                   
}

func_decl * slstar_decl_plugin::mk_data_predicate_decl(symbol name, decl_kind k, unsigned num_parameters, 
                                    parameter const * parameters, unsigned arity,
                                    sort * const * domain, sort * range) {                                    
    return m_manager->mk_func_decl(name, arity, domain, m_dpred_sort, func_decl_info(m_family_id, k));
}

func_decl * slstar_decl_plugin::mk_pred_func_decl(symbol name, std::string loc, decl_kind loc_k,
                                    decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                    unsigned arity, sort * const * domain, sort * range) {
                                        
    sort * data_sort = nullptr; //TODOsl

    /*if(num_parameters == 1 && parameters[0].is_ast() && is_sort(parameters[0].get_ast())) {
        data_sort = to_sort(parameters[0].get_ast());
    } else {
        data_sort = m_int_sort;
    }*/

    unsigned arg_ptr = 0;
    while( arg_ptr < arity && domain[arg_ptr]->is_sort_of(m_dpred_sort->get_family_id(), m_dpred_sort->get_decl_kind())){
        arg_ptr++;
    }
    std::string msg;
    if(arg_ptr == arity) {
        msg = "predicate needs at least one " + loc + " argument";
        m_manager->raise_exception(msg.c_str());
        return nullptr;
    }
    while( arg_ptr < arity && 
        (domain[arg_ptr]->is_sort_of(m_family_id, loc_k) 
        || domain[arg_ptr]->is_sort_of(m_null_sort->get_family_id(), m_null_sort->get_decl_kind()) ) )
    {
        if(domain[arg_ptr]->get_num_parameters() == 1){
            parameter p = domain[arg_ptr]->get_parameter(0);
            if(!p.is_ast()) {
                m_manager->raise_exception("Locations must be a sort"); //TODOsl better message
            }
            if(data_sort == nullptr){
                data_sort = to_sort( p.get_ast());
            } else if(!to_sort( p.get_ast())->is_sort_of(data_sort->get_family_id(), data_sort->get_decl_kind())){
                m_manager->raise_exception("Locations must use same data sort"); //TODOsl better message
            }
        }
        arg_ptr++;
    }
    
    if(arg_ptr != arity) {
        msg= "invalid argument sort(s). Expected: (" + std::string(name.bare_str()) + " Dpred*, " + loc + "+) ";
        m_manager->raise_exception(msg.c_str());
        return nullptr;
    }
    return m_manager->mk_func_decl(name, arity, domain, m_manager->mk_bool_sort(), func_decl_info(m_family_id, k));
}

func_decl * slstar_decl_plugin::mk_pto_func_decl(symbol name, std::string loc, decl_kind loc_k,unsigned exp_arity,
                                    decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                    unsigned arity, sort * const * domain, sort * range) {
    std::string msg;
    if(exp_arity != arity) {
        msg = "Arity missmatch for '" + std::string(name.bare_str()) + "'";
        m_manager->raise_exception(msg.c_str());
        return nullptr;
    }
    unsigned arg_ptr;
    while( arg_ptr < arity && 
        (domain[arg_ptr]->is_sort_of(m_family_id, loc_k) 
        || domain[arg_ptr]->is_sort_of(m_null_sort->get_family_id(), m_null_sort->get_decl_kind()) ) )
    {
        arg_ptr++;
    }
    if(arg_ptr != arity) {
        msg = "invalid argument sort(s). Expected: (" + std::string(name.bare_str()) + " " + loc + " DataSort) ";
        m_manager->raise_exception(msg.c_str());
        return nullptr;
    }
    
    return m_manager->mk_func_decl(name, arity, domain, m_manager->mk_bool_sort(), func_decl_info(m_family_id, k));
}

func_decl * slstar_decl_plugin::mk_ptod_func_decl(symbol name, unsigned exp_arity,
                                    decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                    unsigned arity, sort * const * domain, sort * range) {
    std::string msg;
    if(exp_arity != arity) {
        msg = "Arity missmatch for '" + std::string(name.bare_str()) + "'";
        m_manager->raise_exception(msg.c_str());
        return nullptr;
    }
    unsigned arg_ptr;
    while( arg_ptr < arity - 1 && 
        (domain[arg_ptr]->is_sort_of(m_family_id, SLSTAR_TREE_LOC) 
        || domain[arg_ptr]->is_sort_of(m_family_id, SLSTAR_LIST_LOC)  
        || domain[arg_ptr]->is_sort_of(m_null_sort->get_family_id(), m_null_sort->get_decl_kind()) ) )
    {
        arg_ptr++;
    }
    if(arg_ptr != arity - 1) {
        msg = "invalid argument sort(s). Expected: (" + std::string(name.bare_str()) + " (TreeLoc|DataLoc) DataSort) ";
        m_manager->raise_exception(msg.c_str());
        return nullptr;
    }
    
    return m_manager->mk_func_decl(name, arity, domain, m_manager->mk_bool_sort(), func_decl_info(m_family_id, k));
}

func_decl * slstar_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range) {
    switch(k) {
    case OP_SLSTAR_NULL:
        return m_manager->mk_func_decl(symbol("null"), arity, domain, m_null_sort, func_decl_info(m_family_id, k));

    case OP_SLSTAR_UNARY:
        return mk_data_predicate_decl(symbol("unary"), k, num_parameters, parameters, arity, domain, range);    
    case OP_SLSTAR_LEFT:
        return mk_data_predicate_decl(symbol("left"), k, num_parameters, parameters, arity, domain, range);
    case OP_SLSTAR_RIGHT:
        return mk_data_predicate_decl(symbol("right"), k, num_parameters, parameters, arity, domain, range);
    case OP_SLSTAR_NEXT:
        return mk_data_predicate_decl(symbol("next"), k, num_parameters, parameters, arity, domain, range);
    case OP_SLSTAR_ALPHA:
        return mk_support_decl(symbol("alpha"), k, num_parameters, parameters, arity, domain, range);
    case OP_SLSTAR_BETA:
        return mk_support_decl(symbol("beta"), k, num_parameters, parameters, arity, domain, range);

    case OP_SLSTAR_SEP:
        return m_manager->mk_func_decl(symbol("sep"), arity, domain, m_manager->mk_bool_sort(), func_decl_info(m_family_id, k));
    case OP_SLSTAR_POINTSTOL:
        return mk_pto_func_decl(symbol("ptol"), "TreeLoc", SLSTAR_TREE_LOC, 2, k, num_parameters, parameters, arity, domain, range);
    case OP_SLSTAR_POINTSTOR:
        return mk_pto_func_decl(symbol("ptor"), "TreeLoc", SLSTAR_TREE_LOC, 2, k, num_parameters, parameters, arity, domain, range);
    case OP_SLSTAR_POINTSTOLR:
        return mk_pto_func_decl(symbol("ptolr"), "TreeLoc", SLSTAR_TREE_LOC, 3, k, num_parameters, parameters, arity, domain, range);
    case OP_SLSTAR_POINTSTON:
        return mk_pto_func_decl(symbol("pton"), "ListLoc", SLSTAR_LIST_LOC, 2, k, num_parameters, parameters, arity, domain, range);
    case OP_SLSTAR_POINTSTOD:
        return mk_ptod_func_decl(symbol("ptod"), 2, k, num_parameters, parameters, arity, domain, range);
    
    case OP_SLSTAR_TREE:
        return mk_pred_func_decl(symbol("tree"), "TreeLoc", SLSTAR_TREE_LOC, k, num_parameters, parameters, arity, domain, range);
    case OP_SLSTAR_LIST:
        return mk_pred_func_decl(symbol("list"), "ListLoc", SLSTAR_LIST_LOC, k, num_parameters, parameters, arity, domain, range);
    default:
        m_manager->raise_exception("unsupported separation logic operator");
        return nullptr;
    }
}

void slstar_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);

    auto m_arith_fid = m_manager->mk_family_id("arith");

    m_int_sort = m_manager->mk_sort(m_arith_fid, INT_SORT);
    SASSERT(m_int_sort != 0); // arith_decl_plugin must be installed before slstar_decl_plugin.
    m_manager->inc_ref(m_int_sort);

    sort_size sz;
    sz = sort_size::mk_very_big(); // TODO: refine
    m_dpred_sort = m_manager->mk_sort(symbol("Dpred"), sort_info(m_family_id, SLSTAR_DPRED, sz, 0, nullptr));
    m_manager->inc_ref(m_dpred_sort);

    m_null_sort = m_manager->mk_sort(symbol("NullLoc"), sort_info(m_family_id, SLSTAR_NULL_LOC, sz, 0, nullptr));
    m_manager->inc_ref(m_null_sort);
}

void slstar_decl_plugin::finalize() {
    if (m_int_sort)  { m_manager->dec_ref(m_int_sort); }
    if (m_dpred_sort)  { m_manager->dec_ref(m_dpred_sort); }
    if (m_null_sort)  { m_manager->dec_ref(m_null_sort); }
}

slstar_decl_plugin::~slstar_decl_plugin() {
}

slstar_util::slstar_util(ast_manager & m) :
    m_manager(m),
    m_fid(m.mk_family_id("slstar"))
{
    m_plugin = static_cast<slstar_decl_plugin*>(m.get_plugin(m_fid));
}

slstar_util::~slstar_util() {
}

void slstar_util::get_spatial_atoms(std::list<expr*> * atoms, expr * ex) {
    SASSERT(is_app(ex));
    app * t = to_app(ex);

    // further explore formulas and spatial formulas
    if(m_manager.is_and(t) 
      || m_manager.is_not(t) 
      || m_manager.is_or(t)
      || is_sep(t)
    ){
        expr * arg;
        for(unsigned int i=0; i<t->get_num_args(); i++){
            arg = t->get_arg(i);
            get_spatial_atoms(atoms, arg);
        }
        return;
    }
    atoms->push_back(ex);
}

void slstar_util::get_spatial_atoms_with_polarity(std::list<std::pair<expr*,bool> > * atoms, 
    expr * ex, bool parent_neg)
{
    SASSERT(is_app(ex));
    app * t = to_app(ex);

    // further explore formulas and spatial formulas
    if(m_manager.is_and(t) 
      || m_manager.is_not(t) 
      || m_manager.is_or(t)
      || is_sep(t)
    ){
        expr * arg;
        for(unsigned int i=0; i<t->get_num_args(); i++){
            arg = t->get_arg(i);
            get_spatial_atoms_with_polarity(atoms, arg, parent_neg != m_manager.is_not(t));
        }
        return;
    }
    atoms->push_back(std::pair<expr*,bool> (ex, parent_neg));
}


void slstar_util::get_constants(std::list<expr*> * consts, expr * ex) {
    SASSERT(is_app(ex));
    app * t = to_app(ex);
    expr * arg;
    for(unsigned int i=0; i<t->get_num_args(); i++){
        arg = t->get_arg(i);
        get_constants(consts, arg);
    }
    if( t->get_num_args() == 0) {
        consts->push_back(ex);
    }
}

bool slstar_util::is_pto(expr const * ex)  {
    return is_ptolr(ex) || is_ptor(ex) || is_ptol(ex) || is_pton(ex) || is_ptod(ex);
}
bool slstar_util::is_ptor(expr const * ex) {
    return is_app_of(ex, m_fid, OP_SLSTAR_POINTSTOR);
}
bool slstar_util::is_ptol(expr const * ex) {
    return is_app_of(ex, m_fid, OP_SLSTAR_POINTSTOL);
}
bool slstar_util::is_ptolr(expr const * ex) {
    return is_app_of(ex, m_fid, OP_SLSTAR_POINTSTOLR);
}
bool slstar_util::is_pton(expr const * ex) {
    return is_app_of(ex, m_fid, OP_SLSTAR_POINTSTON);
}
bool slstar_util::is_ptod(expr const * ex) {
    return is_app_of(ex, m_fid, OP_SLSTAR_POINTSTOD);
}

bool slstar_util::is_sep(expr const * ex)  {
    return is_app_of(ex, m_fid, OP_SLSTAR_SEP);
}

bool slstar_util::is_call(expr const * ex)  {
    return is_tree(ex) || is_list(ex);
}
bool slstar_util::is_tree(expr const * ex) {
    return is_app_of(ex, m_fid, OP_SLSTAR_TREE);
}
bool slstar_util::is_list(expr const * ex) {
    return is_app_of(ex, m_fid, OP_SLSTAR_LIST);
}

bool slstar_util::is_treeloc(sort const * s){
    return s->is_sort_of(m_fid, SLSTAR_TREE_LOC);
}
bool slstar_util::is_listloc(sort const * s){
    return s->is_sort_of(m_fid, SLSTAR_LIST_LOC);
}

bool slstar_util::is_nullloc(sort const * s){
    return s->is_sort_of(m_fid, SLSTAR_NULL_LOC);
}

bool slstar_util::is_dpred(sort const * s){
    return s->is_sort_of(m_fid, SLSTAR_DPRED);
}

bool slstar_util::is_null(expr const * ex) {
    return is_app_of(ex, m_fid, OP_SLSTAR_NULL);
}
bool slstar_util::is_listconst(expr const * ex) {
    return is_sort_of( get_sort(ex), m_fid, SLSTAR_LIST_LOC);
}
bool slstar_util::is_treeconst(expr const * ex) {
    return is_sort_of( get_sort(ex), m_fid, SLSTAR_TREE_LOC);
}

unsigned int slstar_util::num_stop_nodes(expr const * ex) {
    SASSERT(is_tree(ex) || is_list(ex));
    const app * t = to_app(ex);
    for(unsigned int i = 0; i < t->get_num_args(); i++){
        expr * arg = t->get_arg(i);
        if( !is_sort_of(get_sort(arg), m_fid, SLSTAR_DPRED) ){
            return t->get_num_args()-i-1;
        }
    }
    SASSERT(false);
    return 0;
}
