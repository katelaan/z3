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

sort * slstar_decl_plugin::mk_slstar_tree() {
    //TODOsl
    //parameter ps[0] = { };
    sort_size sz;
    sz = sort_size::mk_very_big(); // TODO: refine
    return m_manager->mk_sort(symbol("TreeLoc"), sort_info(m_family_id, SLSTAR_TREE_LOC, sz, 0, NULL));
    //return m_manager->mk_sort(symbol("TreeLoc"), sort_info(m_family_id, SLSTAR_TREE_LOC, sz, 0, ps));
}

sort * slstar_decl_plugin::mk_slstar_list() {
    sort_size sz;
    sz = sort_size::mk_very_big(); // TODO: refine
    return m_manager->mk_sort(symbol("ListLoc"), sort_info(m_family_id, SLSTAR_LIST_LOC, sz, 0, NULL));
}

sort * slstar_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    switch (k) {
    case SLSTAR_TREE_LOC:
        return mk_slstar_tree();
    case SLSTAR_LIST_LOC:
        return mk_slstar_list();
    default:
        m_manager->raise_exception("unknown separation logic theory sort");
        return nullptr;
    }
}

/*func_decl * slstar_decl_plugin::mk_const_decl() {
    func_decl * r;
    r = m_manager->mk_const_decl(symbol("+oo"), s, func_decl_info(m_family_id, OP_FPA_PLUS_INF));
    return r;
}*/

func_decl * slstar_decl_plugin::mk_support_decl(symbol name, decl_kind k, unsigned num_parameters, 
                                    parameter const * parameters, unsigned arity,
                                    sort * const * domain, sort * range) {
    if(arity != 0){
        m_manager->raise_exception("Support variables must have arity 0");
        return nullptr;
    }
    sort * sort = m_int_sort;
    if(num_parameters == 1 && parameters[0].is_ast() && is_sort(parameters[0].get_ast())) {
        sort = to_sort(parameters[0].get_ast());
    } else if(num_parameters != 0) {
        m_manager->raise_exception("First parameter must be sort");
        return nullptr;
    }

    return m_manager->mk_func_decl(name, arity, domain, sort, func_decl_info(m_family_id, k));                                   
}

func_decl * slstar_decl_plugin::mk_data_predicate_decl(symbol name, decl_kind k, unsigned num_parameters, 
                                    parameter const * parameters, unsigned arity,
                                    sort * const * domain, sort * range) {                                    
    return m_manager->mk_func_decl(name, arity, domain, m_manager->mk_uninterpreted_sort(symbol("Dpred")), func_decl_info(m_family_id, k));
}
                                    


func_decl * slstar_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range) {
    switch(k) {
    case OP_SLSTAR_NULL:
        return m_manager->mk_func_decl(symbol("null"), arity, domain, m_manager->mk_bool_sort(), func_decl_info(m_family_id, k));

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
        return m_manager->mk_func_decl(symbol("ptol"), arity, domain, m_manager->mk_bool_sort(), func_decl_info(m_family_id, k));
    case OP_SLSTAR_POINTSTOR:
        return m_manager->mk_func_decl(symbol("ptor"), arity, domain, m_manager->mk_bool_sort(), func_decl_info(m_family_id, k));
    case OP_SLSTAR_POINTSTOLR:
        return m_manager->mk_func_decl(symbol("ptolr"), arity, domain, m_manager->mk_bool_sort(), func_decl_info(m_family_id, k));
    case OP_SLSTAR_POINTSTON:
        return m_manager->mk_func_decl(symbol("pton"), arity, domain, m_manager->mk_bool_sort(), func_decl_info(m_family_id, k));
    case OP_SLSTAR_POINTSTOD:
        return m_manager->mk_func_decl(symbol("ptod"), arity, domain, m_manager->mk_bool_sort(), func_decl_info(m_family_id, k));
    case OP_SLSTAR_TREE:
        return m_manager->mk_func_decl(symbol("tree"), arity, domain, m_manager->mk_bool_sort(), func_decl_info(m_family_id, k));
    case OP_SLSTAR_LIST:
        return m_manager->mk_func_decl(symbol("list"), arity, domain, m_manager->mk_bool_sort(), func_decl_info(m_family_id, k));
    default:
        m_manager->raise_exception("unsupported separation logic operator");
        return nullptr;
    }
}

void slstar_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);

    auto m_arith_fid = m_manager->mk_family_id("arith");

    m_int_sort = m_manager->mk_sort(m_arith_fid, INT_SORT);
    SASSERT(m_int_sort != 0); // arith_decl_plugin must be installed before fpa_decl_plugin.
    m_manager->inc_ref(m_int_sort);
}

void slstar_decl_plugin::finalize() {
    if (m_int_sort)  { m_manager->dec_ref(m_int_sort); }
}

slstar_decl_plugin::~slstar_decl_plugin() {
}