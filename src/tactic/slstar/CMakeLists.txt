z3_add_component(slstar_tactics
  SOURCES
    slstar_reduce_tactic.cpp
    slstar_spatial_eq_propagation_tactic.cpp
    slstar_model_converter.cpp
    slstar_bounds.cpp
    utils.cpp
  COMPONENT_DEPENDENCIES
    slstar
    arith_tactics
    bv_tactics
    core_tactics
    sat_tactic
    smtlogic_tactics
    smt_tactic
  TACTIC_HEADERS
    slstar_reduce_tactic.h
    slstar_spatial_eq_propagation_tactic.h
)
