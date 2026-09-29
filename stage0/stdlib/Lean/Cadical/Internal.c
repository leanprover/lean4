// Lean compiler output
// Module: Lean.Cadical.Internal
// Imports: public import Init.Data.String.Bootstrap public import Init.Data.SInt.Basic public import Init.System.IO
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
uint32_t lean_int32_of_nat(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Cadical_Internal_0__Lean_Cadical_Internal_SolverImpl;
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_satisfiable_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_satisfiable_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_satisfiable_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_satisfiable_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unsatisfiable_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unsatisfiable_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unsatisfiable_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unsatisfiable_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unknown_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unknown_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unknown_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unknown_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Cadical_Internal_instInhabitedStatus_default;
LEAN_EXPORT uint8_t l_Lean_Cadical_Internal_instInhabitedStatus;
LEAN_EXPORT uint8_t l_Lean_Cadical_Internal_Status_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Cadical_Internal_instDecidableEqStatus(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_instDecidableEqStatus___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Cadical_Internal_instHashableStatus_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_instHashableStatus_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Cadical_Internal_instHashableStatus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Cadical_Internal_instHashableStatus_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Cadical_Internal_instHashableStatus___closed__0 = (const lean_object*)&l_Lean_Cadical_Internal_instHashableStatus___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Cadical_Internal_instHashableStatus = (const lean_object*)&l_Lean_Cadical_Internal_instHashableStatus___closed__0_value;
static const lean_string_object l_Lean_Cadical_Internal_instReprStatus_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Cadical.Internal.Status.satisfiable"};
static const lean_object* l_Lean_Cadical_Internal_instReprStatus_repr___closed__0 = (const lean_object*)&l_Lean_Cadical_Internal_instReprStatus_repr___closed__0_value;
static const lean_ctor_object l_Lean_Cadical_Internal_instReprStatus_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Cadical_Internal_instReprStatus_repr___closed__0_value)}};
static const lean_object* l_Lean_Cadical_Internal_instReprStatus_repr___closed__1 = (const lean_object*)&l_Lean_Cadical_Internal_instReprStatus_repr___closed__1_value;
static const lean_string_object l_Lean_Cadical_Internal_instReprStatus_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean.Cadical.Internal.Status.unsatisfiable"};
static const lean_object* l_Lean_Cadical_Internal_instReprStatus_repr___closed__2 = (const lean_object*)&l_Lean_Cadical_Internal_instReprStatus_repr___closed__2_value;
static const lean_ctor_object l_Lean_Cadical_Internal_instReprStatus_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Cadical_Internal_instReprStatus_repr___closed__2_value)}};
static const lean_object* l_Lean_Cadical_Internal_instReprStatus_repr___closed__3 = (const lean_object*)&l_Lean_Cadical_Internal_instReprStatus_repr___closed__3_value;
static const lean_string_object l_Lean_Cadical_Internal_instReprStatus_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Cadical.Internal.Status.unknown"};
static const lean_object* l_Lean_Cadical_Internal_instReprStatus_repr___closed__4 = (const lean_object*)&l_Lean_Cadical_Internal_instReprStatus_repr___closed__4_value;
static const lean_ctor_object l_Lean_Cadical_Internal_instReprStatus_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Cadical_Internal_instReprStatus_repr___closed__4_value)}};
static const lean_object* l_Lean_Cadical_Internal_instReprStatus_repr___closed__5 = (const lean_object*)&l_Lean_Cadical_Internal_instReprStatus_repr___closed__5_value;
static lean_once_cell_t l_Lean_Cadical_Internal_instReprStatus_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Cadical_Internal_instReprStatus_repr___closed__6;
static lean_once_cell_t l_Lean_Cadical_Internal_instReprStatus_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Cadical_Internal_instReprStatus_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_instReprStatus_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_instReprStatus_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Cadical_Internal_instReprStatus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Cadical_Internal_instReprStatus_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Cadical_Internal_instReprStatus___closed__0 = (const lean_object*)&l_Lean_Cadical_Internal_instReprStatus___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Cadical_Internal_instReprStatus = (const lean_object*)&l_Lean_Cadical_Internal_instReprStatus___closed__0_value;
static lean_once_cell_t l_Lean_Cadical_Internal_Status_toInt32___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Lean_Cadical_Internal_Status_toInt32___closed__0;
static lean_once_cell_t l_Lean_Cadical_Internal_Status_toInt32___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Lean_Cadical_Internal_Status_toInt32___closed__1;
static lean_once_cell_t l_Lean_Cadical_Internal_Status_toInt32___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Lean_Cadical_Internal_Status_toInt32___closed__2;
LEAN_EXPORT uint32_t l_Lean_Cadical_Internal_Status_toInt32(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_toInt32___boxed(lean_object*);
lean_object* lean_cadical_signature(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Cadical_Internal_0__Lean_Cadical_Internal_getSignature___boxed(lean_object*);
static lean_once_cell_t l_Lean_Cadical_Internal_signature___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Cadical_Internal_signature___closed__0;
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_signature;
lean_object* lean_cadical_solver_new();
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_new___boxed(lean_object*);
lean_object* lean_cadical_solver_add(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_add___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_cadical_solver_clause(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_clause___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_cadical_solver_inconsistent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_inconsistent___boxed(lean_object*, lean_object*);
lean_object* lean_cadical_solver_assume(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_assume___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_cadical_solver_solve(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_solve___boxed(lean_object*, lean_object*);
uint32_t lean_cadical_solver_val(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_val___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_cadical_solver_flip(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_flip___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_cadical_solver_flippable(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_flippable___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_cadical_solver_failed(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_failed___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_cadical_solver_constrain(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_constrain___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_cadical_solver_constraint_failed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_constraintFailed___boxed(lean_object*, lean_object*);
uint32_t lean_cadical_solver_lookahead(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_lookahead___boxed(lean_object*, lean_object*);
lean_object* lean_cadical_solver_reset_assumptions(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_resetAssumptions___boxed(lean_object*, lean_object*);
lean_object* lean_cadical_solver_reset_constraint(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_resetConstraint___boxed(lean_object*, lean_object*);
uint8_t lean_cadical_solver_status(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_status___boxed(lean_object*, lean_object*);
uint32_t lean_cadical_solver_vars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_vars___boxed(lean_object*, lean_object*);
lean_object* lean_cadical_solver_resize(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_resize___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_cadical_solver_is_valid_option(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isValidOption___boxed(lean_object*);
uint8_t lean_cadical_solver_is_preprocessing_option(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isPreprocessingOption___boxed(lean_object*);
uint8_t lean_cadical_solver_is_valid_long_option(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isValidLongOption___boxed(lean_object*);
uint32_t lean_cadical_solver_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_get___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_cadical_solver_set(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_cadical_solver_set_long_option(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_setLongOption___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_cadical_solver_is_valid_configuration(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isValidConfiguration___boxed(lean_object*);
uint8_t lean_cadical_solver_configure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_configure___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_cadical_solver_optimize(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_optimize___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_cadical_solver_limit(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_limit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_cadical_solver_is_valid_limit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isValidLimit___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_cadical_solver_active(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_active___boxed(lean_object*, lean_object*);
uint64_t lean_cadical_solver_redundant(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_redundant___boxed(lean_object*, lean_object*);
uint64_t lean_cadical_solver_irredundant(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_irredundant___boxed(lean_object*, lean_object*);
uint8_t lean_cadical_solver_simplify(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_simplify___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_cadical_solver_terminate(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_terminate___boxed(lean_object*, lean_object*);
uint8_t lean_cadical_solver_frozen(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_frozen___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_cadical_solver_freeze(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_freeze___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_cadical_solver_melt(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_melt___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_cadical_solver_fixed(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_fixed___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_cadical_solver_phase(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_phase___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_cadical_solver_unphase(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_unphase___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_cadical_solver_conclude(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_conclude___boxed(lean_object*, lean_object*);
lean_object* lean_cadical_solver_usage();
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_usage___boxed(lean_object*);
lean_object* lean_cadical_solver_configurations();
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_configurations___boxed(lean_object*);
lean_object* lean_cadical_solver_statistics(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_statistics___boxed(lean_object*, lean_object*);
lean_object* lean_cadical_solver_resources(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_resources___boxed(lean_object*, lean_object*);
uint16_t lean_cadical_solver_state(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_state___boxed(lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Cadical_Internal_0__Lean_Cadical_Internal_SolverImpl(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorIdx(uint8_t v_x_2_){
_start:
{
switch(v_x_2_)
{
case 0:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(0u);
return v___x_3_;
}
case 1:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(1u);
return v___x_4_;
}
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(2u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
uint8_t v_x_boxed_7_; lean_object* v_res_8_; 
v_x_boxed_7_ = lean_unbox(v_x_6_);
v_res_8_ = l_Lean_Cadical_Internal_Status_ctorIdx(v_x_boxed_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorElim___redArg(lean_object* v_k_9_){
_start:
{
lean_inc(v_k_9_);
return v_k_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorElim___redArg___boxed(lean_object* v_k_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Cadical_Internal_Status_ctorElim___redArg(v_k_10_);
lean_dec(v_k_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, uint8_t v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_inc(v_k_16_);
return v_k_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_Cadical_Internal_Status_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_satisfiable_elim___redArg(lean_object* v_satisfiable_24_){
_start:
{
lean_inc(v_satisfiable_24_);
return v_satisfiable_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_satisfiable_elim___redArg___boxed(lean_object* v_satisfiable_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Cadical_Internal_Status_satisfiable_elim___redArg(v_satisfiable_25_);
lean_dec(v_satisfiable_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_satisfiable_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_satisfiable_30_){
_start:
{
lean_inc(v_satisfiable_30_);
return v_satisfiable_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_satisfiable_elim___boxed(lean_object* v_motive_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_satisfiable_34_){
_start:
{
uint8_t v_t_boxed_35_; lean_object* v_res_36_; 
v_t_boxed_35_ = lean_unbox(v_t_32_);
v_res_36_ = l_Lean_Cadical_Internal_Status_satisfiable_elim(v_motive_31_, v_t_boxed_35_, v_h_33_, v_satisfiable_34_);
lean_dec(v_satisfiable_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unsatisfiable_elim___redArg(lean_object* v_unsatisfiable_37_){
_start:
{
lean_inc(v_unsatisfiable_37_);
return v_unsatisfiable_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unsatisfiable_elim___redArg___boxed(lean_object* v_unsatisfiable_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Cadical_Internal_Status_unsatisfiable_elim___redArg(v_unsatisfiable_38_);
lean_dec(v_unsatisfiable_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unsatisfiable_elim(lean_object* v_motive_40_, uint8_t v_t_41_, lean_object* v_h_42_, lean_object* v_unsatisfiable_43_){
_start:
{
lean_inc(v_unsatisfiable_43_);
return v_unsatisfiable_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unsatisfiable_elim___boxed(lean_object* v_motive_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_unsatisfiable_47_){
_start:
{
uint8_t v_t_boxed_48_; lean_object* v_res_49_; 
v_t_boxed_48_ = lean_unbox(v_t_45_);
v_res_49_ = l_Lean_Cadical_Internal_Status_unsatisfiable_elim(v_motive_44_, v_t_boxed_48_, v_h_46_, v_unsatisfiable_47_);
lean_dec(v_unsatisfiable_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unknown_elim___redArg(lean_object* v_unknown_50_){
_start:
{
lean_inc(v_unknown_50_);
return v_unknown_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unknown_elim___redArg___boxed(lean_object* v_unknown_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Cadical_Internal_Status_unknown_elim___redArg(v_unknown_51_);
lean_dec(v_unknown_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unknown_elim(lean_object* v_motive_53_, uint8_t v_t_54_, lean_object* v_h_55_, lean_object* v_unknown_56_){
_start:
{
lean_inc(v_unknown_56_);
return v_unknown_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unknown_elim___boxed(lean_object* v_motive_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_unknown_60_){
_start:
{
uint8_t v_t_boxed_61_; lean_object* v_res_62_; 
v_t_boxed_61_ = lean_unbox(v_t_58_);
v_res_62_ = l_Lean_Cadical_Internal_Status_unknown_elim(v_motive_57_, v_t_boxed_61_, v_h_59_, v_unknown_60_);
lean_dec(v_unknown_60_);
return v_res_62_;
}
}
static uint8_t _init_l_Lean_Cadical_Internal_instInhabitedStatus_default(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
static uint8_t _init_l_Lean_Cadical_Internal_instInhabitedStatus(void){
_start:
{
uint8_t v___x_64_; 
v___x_64_ = 0;
return v___x_64_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Internal_Status_ofNat(lean_object* v_n_65_){
_start:
{
lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = lean_nat_dec_le(v_n_65_, v___x_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = lean_nat_dec_le(v_n_65_, v___x_68_);
if (v___x_69_ == 0)
{
uint8_t v___x_70_; 
v___x_70_ = 2;
return v___x_70_;
}
else
{
uint8_t v___x_71_; 
v___x_71_ = 1;
return v___x_71_;
}
}
else
{
uint8_t v___x_72_; 
v___x_72_ = 0;
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ofNat___boxed(lean_object* v_n_73_){
_start:
{
uint8_t v_res_74_; lean_object* v_r_75_; 
v_res_74_ = l_Lean_Cadical_Internal_Status_ofNat(v_n_73_);
lean_dec(v_n_73_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Internal_instDecidableEqStatus(uint8_t v_x_76_, uint8_t v_y_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_78_ = l_Lean_Cadical_Internal_Status_ctorIdx(v_x_76_);
v___x_79_ = l_Lean_Cadical_Internal_Status_ctorIdx(v_y_77_);
v___x_80_ = lean_nat_dec_eq(v___x_78_, v___x_79_);
lean_dec(v___x_79_);
lean_dec(v___x_78_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_instDecidableEqStatus___boxed(lean_object* v_x_81_, lean_object* v_y_82_){
_start:
{
uint8_t v_x_20__boxed_83_; uint8_t v_y_21__boxed_84_; uint8_t v_res_85_; lean_object* v_r_86_; 
v_x_20__boxed_83_ = lean_unbox(v_x_81_);
v_y_21__boxed_84_ = lean_unbox(v_y_82_);
v_res_85_ = l_Lean_Cadical_Internal_instDecidableEqStatus(v_x_20__boxed_83_, v_y_21__boxed_84_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT uint64_t l_Lean_Cadical_Internal_instHashableStatus_hash(uint8_t v_x_87_){
_start:
{
switch(v_x_87_)
{
case 0:
{
uint64_t v___x_88_; 
v___x_88_ = 0ULL;
return v___x_88_;
}
case 1:
{
uint64_t v___x_89_; 
v___x_89_ = 1ULL;
return v___x_89_;
}
default: 
{
uint64_t v___x_90_; 
v___x_90_ = 2ULL;
return v___x_90_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_instHashableStatus_hash___boxed(lean_object* v_x_91_){
_start:
{
uint8_t v_x_40__boxed_92_; uint64_t v_res_93_; lean_object* v_r_94_; 
v_x_40__boxed_92_ = lean_unbox(v_x_91_);
v_res_93_ = l_Lean_Cadical_Internal_instHashableStatus_hash(v_x_40__boxed_92_);
v_r_94_ = lean_box_uint64(v_res_93_);
return v_r_94_;
}
}
static lean_object* _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__6(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(2u);
v___x_107_ = lean_nat_to_int(v___x_106_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__7(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lean_nat_to_int(v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_instReprStatus_repr(uint8_t v_x_110_, lean_object* v_prec_111_){
_start:
{
lean_object* v___y_113_; lean_object* v___y_120_; lean_object* v___y_127_; 
switch(v_x_110_)
{
case 0:
{
lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_133_ = lean_unsigned_to_nat(1024u);
v___x_134_ = lean_nat_dec_le(v___x_133_, v_prec_111_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; 
v___x_135_ = lean_obj_once(&l_Lean_Cadical_Internal_instReprStatus_repr___closed__6, &l_Lean_Cadical_Internal_instReprStatus_repr___closed__6_once, _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__6);
v___y_113_ = v___x_135_;
goto v___jp_112_;
}
else
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_Lean_Cadical_Internal_instReprStatus_repr___closed__7, &l_Lean_Cadical_Internal_instReprStatus_repr___closed__7_once, _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__7);
v___y_113_ = v___x_136_;
goto v___jp_112_;
}
}
case 1:
{
lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_137_ = lean_unsigned_to_nat(1024u);
v___x_138_ = lean_nat_dec_le(v___x_137_, v_prec_111_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; 
v___x_139_ = lean_obj_once(&l_Lean_Cadical_Internal_instReprStatus_repr___closed__6, &l_Lean_Cadical_Internal_instReprStatus_repr___closed__6_once, _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__6);
v___y_120_ = v___x_139_;
goto v___jp_119_;
}
else
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_Lean_Cadical_Internal_instReprStatus_repr___closed__7, &l_Lean_Cadical_Internal_instReprStatus_repr___closed__7_once, _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__7);
v___y_120_ = v___x_140_;
goto v___jp_119_;
}
}
default: 
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = lean_unsigned_to_nat(1024u);
v___x_142_ = lean_nat_dec_le(v___x_141_, v_prec_111_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
v___x_143_ = lean_obj_once(&l_Lean_Cadical_Internal_instReprStatus_repr___closed__6, &l_Lean_Cadical_Internal_instReprStatus_repr___closed__6_once, _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__6);
v___y_127_ = v___x_143_;
goto v___jp_126_;
}
else
{
lean_object* v___x_144_; 
v___x_144_ = lean_obj_once(&l_Lean_Cadical_Internal_instReprStatus_repr___closed__7, &l_Lean_Cadical_Internal_instReprStatus_repr___closed__7_once, _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__7);
v___y_127_ = v___x_144_;
goto v___jp_126_;
}
}
}
v___jp_112_:
{
lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_114_ = ((lean_object*)(l_Lean_Cadical_Internal_instReprStatus_repr___closed__1));
lean_inc(v___y_113_);
v___x_115_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_115_, 0, v___y_113_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
v___x_116_ = 0;
v___x_117_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_117_, 0, v___x_115_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*1, v___x_116_);
v___x_118_ = l_Repr_addAppParen(v___x_117_, v_prec_111_);
return v___x_118_;
}
v___jp_119_:
{
lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_121_ = ((lean_object*)(l_Lean_Cadical_Internal_instReprStatus_repr___closed__3));
lean_inc(v___y_120_);
v___x_122_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_122_, 0, v___y_120_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = 0;
v___x_124_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_124_, 0, v___x_122_);
lean_ctor_set_uint8(v___x_124_, sizeof(void*)*1, v___x_123_);
v___x_125_ = l_Repr_addAppParen(v___x_124_, v_prec_111_);
return v___x_125_;
}
v___jp_126_:
{
lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_128_ = ((lean_object*)(l_Lean_Cadical_Internal_instReprStatus_repr___closed__5));
lean_inc(v___y_127_);
v___x_129_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_129_, 0, v___y_127_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = 0;
v___x_131_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*1, v___x_130_);
v___x_132_ = l_Repr_addAppParen(v___x_131_, v_prec_111_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_instReprStatus_repr___boxed(lean_object* v_x_145_, lean_object* v_prec_146_){
_start:
{
uint8_t v_x_171__boxed_147_; lean_object* v_res_148_; 
v_x_171__boxed_147_ = lean_unbox(v_x_145_);
v_res_148_ = l_Lean_Cadical_Internal_instReprStatus_repr(v_x_171__boxed_147_, v_prec_146_);
lean_dec(v_prec_146_);
return v_res_148_;
}
}
static uint32_t _init_l_Lean_Cadical_Internal_Status_toInt32___closed__0(void){
_start:
{
lean_object* v___x_151_; uint32_t v___x_152_; 
v___x_151_ = lean_unsigned_to_nat(10u);
v___x_152_ = lean_int32_of_nat(v___x_151_);
return v___x_152_;
}
}
static uint32_t _init_l_Lean_Cadical_Internal_Status_toInt32___closed__1(void){
_start:
{
lean_object* v___x_153_; uint32_t v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(20u);
v___x_154_ = lean_int32_of_nat(v___x_153_);
return v___x_154_;
}
}
static uint32_t _init_l_Lean_Cadical_Internal_Status_toInt32___closed__2(void){
_start:
{
lean_object* v___x_155_; uint32_t v___x_156_; 
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = lean_int32_of_nat(v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT uint32_t l_Lean_Cadical_Internal_Status_toInt32(uint8_t v_x_157_){
_start:
{
switch(v_x_157_)
{
case 0:
{
uint32_t v___x_158_; 
v___x_158_ = lean_uint32_once(&l_Lean_Cadical_Internal_Status_toInt32___closed__0, &l_Lean_Cadical_Internal_Status_toInt32___closed__0_once, _init_l_Lean_Cadical_Internal_Status_toInt32___closed__0);
return v___x_158_;
}
case 1:
{
uint32_t v___x_159_; 
v___x_159_ = lean_uint32_once(&l_Lean_Cadical_Internal_Status_toInt32___closed__1, &l_Lean_Cadical_Internal_Status_toInt32___closed__1_once, _init_l_Lean_Cadical_Internal_Status_toInt32___closed__1);
return v___x_159_;
}
default: 
{
uint32_t v___x_160_; 
v___x_160_ = lean_uint32_once(&l_Lean_Cadical_Internal_Status_toInt32___closed__2, &l_Lean_Cadical_Internal_Status_toInt32___closed__2_once, _init_l_Lean_Cadical_Internal_Status_toInt32___closed__2);
return v___x_160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_toInt32___boxed(lean_object* v_x_161_){
_start:
{
uint8_t v_x_52__boxed_162_; uint32_t v_res_163_; lean_object* v_r_164_; 
v_x_52__boxed_162_ = lean_unbox(v_x_161_);
v_res_163_ = l_Lean_Cadical_Internal_Status_toInt32(v_x_52__boxed_162_);
v_r_164_ = lean_box_uint32(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Cadical_Internal_0__Lean_Cadical_Internal_getSignature___boxed(lean_object* v_u_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = lean_cadical_signature(v_u_166_);
return v_res_167_;
}
}
static lean_object* _init_l_Lean_Cadical_Internal_signature___closed__0(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = lean_box(0);
v___x_169_ = lean_cadical_signature(v___x_168_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_Cadical_Internal_signature(void){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_obj_once(&l_Lean_Cadical_Internal_signature___closed__0, &l_Lean_Cadical_Internal_signature___closed__0_once, _init_l_Lean_Cadical_Internal_signature___closed__0);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_new___boxed(lean_object* v_a_00___x40___internal___hyg_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = lean_cadical_solver_new();
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_add___boxed(lean_object* v_s_177_, lean_object* v_lit_178_, lean_object* v_a_00___x40___internal___hyg_179_){
_start:
{
uint32_t v_lit_boxed_180_; lean_object* v_res_181_; 
v_lit_boxed_180_ = lean_unbox_uint32(v_lit_178_);
lean_dec(v_lit_178_);
v_res_181_ = lean_cadical_solver_add(v_s_177_, v_lit_boxed_180_);
lean_dec(v_s_177_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_clause___boxed(lean_object* v_s_185_, lean_object* v_lits_186_, lean_object* v_a_00___x40___internal___hyg_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = lean_cadical_solver_clause(v_s_185_, v_lits_186_);
lean_dec_ref(v_lits_186_);
lean_dec(v_s_185_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_inconsistent___boxed(lean_object* v_s_191_, lean_object* v_a_00___x40___internal___hyg_192_){
_start:
{
uint8_t v_res_193_; lean_object* v_r_194_; 
v_res_193_ = lean_cadical_solver_inconsistent(v_s_191_);
lean_dec(v_s_191_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_assume___boxed(lean_object* v_s_198_, lean_object* v_lit_199_, lean_object* v_a_00___x40___internal___hyg_200_){
_start:
{
uint32_t v_lit_boxed_201_; lean_object* v_res_202_; 
v_lit_boxed_201_ = lean_unbox_uint32(v_lit_199_);
lean_dec(v_lit_199_);
v_res_202_ = lean_cadical_solver_assume(v_s_198_, v_lit_boxed_201_);
lean_dec(v_s_198_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_solve___boxed(lean_object* v_s_205_, lean_object* v_a_00___x40___internal___hyg_206_){
_start:
{
uint8_t v_res_207_; lean_object* v_r_208_; 
v_res_207_ = lean_cadical_solver_solve(v_s_205_);
lean_dec(v_s_205_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_val___boxed(lean_object* v_s_212_, lean_object* v_lit_213_, lean_object* v_a_00___x40___internal___hyg_214_){
_start:
{
uint32_t v_lit_boxed_215_; uint32_t v_res_216_; lean_object* v_r_217_; 
v_lit_boxed_215_ = lean_unbox_uint32(v_lit_213_);
lean_dec(v_lit_213_);
v_res_216_ = lean_cadical_solver_val(v_s_212_, v_lit_boxed_215_);
lean_dec(v_s_212_);
v_r_217_ = lean_box_uint32(v_res_216_);
return v_r_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_flip___boxed(lean_object* v_s_221_, lean_object* v_lit_222_, lean_object* v_a_00___x40___internal___hyg_223_){
_start:
{
uint32_t v_lit_boxed_224_; uint8_t v_res_225_; lean_object* v_r_226_; 
v_lit_boxed_224_ = lean_unbox_uint32(v_lit_222_);
lean_dec(v_lit_222_);
v_res_225_ = lean_cadical_solver_flip(v_s_221_, v_lit_boxed_224_);
lean_dec(v_s_221_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_flippable___boxed(lean_object* v_s_230_, lean_object* v_lit_231_, lean_object* v_a_00___x40___internal___hyg_232_){
_start:
{
uint32_t v_lit_boxed_233_; uint8_t v_res_234_; lean_object* v_r_235_; 
v_lit_boxed_233_ = lean_unbox_uint32(v_lit_231_);
lean_dec(v_lit_231_);
v_res_234_ = lean_cadical_solver_flippable(v_s_230_, v_lit_boxed_233_);
lean_dec(v_s_230_);
v_r_235_ = lean_box(v_res_234_);
return v_r_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_failed___boxed(lean_object* v_s_239_, lean_object* v_lit_240_, lean_object* v_a_00___x40___internal___hyg_241_){
_start:
{
uint32_t v_lit_boxed_242_; uint8_t v_res_243_; lean_object* v_r_244_; 
v_lit_boxed_242_ = lean_unbox_uint32(v_lit_240_);
lean_dec(v_lit_240_);
v_res_243_ = lean_cadical_solver_failed(v_s_239_, v_lit_boxed_242_);
lean_dec(v_s_239_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_constrain___boxed(lean_object* v_s_248_, lean_object* v_lit_249_, lean_object* v_a_00___x40___internal___hyg_250_){
_start:
{
uint32_t v_lit_boxed_251_; lean_object* v_res_252_; 
v_lit_boxed_251_ = lean_unbox_uint32(v_lit_249_);
lean_dec(v_lit_249_);
v_res_252_ = lean_cadical_solver_constrain(v_s_248_, v_lit_boxed_251_);
lean_dec(v_s_248_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_constraintFailed___boxed(lean_object* v_s_255_, lean_object* v_a_00___x40___internal___hyg_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = lean_cadical_solver_constraint_failed(v_s_255_);
lean_dec(v_s_255_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_lookahead___boxed(lean_object* v_s_261_, lean_object* v_a_00___x40___internal___hyg_262_){
_start:
{
uint32_t v_res_263_; lean_object* v_r_264_; 
v_res_263_ = lean_cadical_solver_lookahead(v_s_261_);
lean_dec(v_s_261_);
v_r_264_ = lean_box_uint32(v_res_263_);
return v_r_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_resetAssumptions___boxed(lean_object* v_s_267_, lean_object* v_a_00___x40___internal___hyg_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = lean_cadical_solver_reset_assumptions(v_s_267_);
lean_dec(v_s_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_resetConstraint___boxed(lean_object* v_s_272_, lean_object* v_a_00___x40___internal___hyg_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = lean_cadical_solver_reset_constraint(v_s_272_);
lean_dec(v_s_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_status___boxed(lean_object* v_s_277_, lean_object* v_a_00___x40___internal___hyg_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = lean_cadical_solver_status(v_s_277_);
lean_dec(v_s_277_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_vars___boxed(lean_object* v_s_283_, lean_object* v_a_00___x40___internal___hyg_284_){
_start:
{
uint32_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = lean_cadical_solver_vars(v_s_283_);
lean_dec(v_s_283_);
v_r_286_ = lean_box_uint32(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_resize___boxed(lean_object* v_s_290_, lean_object* v_minMaxVar_291_, lean_object* v_a_00___x40___internal___hyg_292_){
_start:
{
uint32_t v_minMaxVar_boxed_293_; lean_object* v_res_294_; 
v_minMaxVar_boxed_293_ = lean_unbox_uint32(v_minMaxVar_291_);
lean_dec(v_minMaxVar_291_);
v_res_294_ = lean_cadical_solver_resize(v_s_290_, v_minMaxVar_boxed_293_);
lean_dec(v_s_290_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isValidOption___boxed(lean_object* v_opt_296_){
_start:
{
uint8_t v_res_297_; lean_object* v_r_298_; 
v_res_297_ = lean_cadical_solver_is_valid_option(v_opt_296_);
lean_dec_ref(v_opt_296_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isPreprocessingOption___boxed(lean_object* v_opt_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = lean_cadical_solver_is_preprocessing_option(v_opt_300_);
lean_dec_ref(v_opt_300_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isValidLongOption___boxed(lean_object* v_opt_304_){
_start:
{
uint8_t v_res_305_; lean_object* v_r_306_; 
v_res_305_ = lean_cadical_solver_is_valid_long_option(v_opt_304_);
lean_dec_ref(v_opt_304_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_get___boxed(lean_object* v_s_310_, lean_object* v_opt_311_, lean_object* v_a_00___x40___internal___hyg_312_){
_start:
{
uint32_t v_res_313_; lean_object* v_r_314_; 
v_res_313_ = lean_cadical_solver_get(v_s_310_, v_opt_311_);
lean_dec_ref(v_opt_311_);
lean_dec(v_s_310_);
v_r_314_ = lean_box_uint32(v_res_313_);
return v_r_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_set___boxed(lean_object* v_s_319_, lean_object* v_opt_320_, lean_object* v_val_321_, lean_object* v_a_00___x40___internal___hyg_322_){
_start:
{
uint32_t v_val_boxed_323_; uint8_t v_res_324_; lean_object* v_r_325_; 
v_val_boxed_323_ = lean_unbox_uint32(v_val_321_);
lean_dec(v_val_321_);
v_res_324_ = lean_cadical_solver_set(v_s_319_, v_opt_320_, v_val_boxed_323_);
lean_dec_ref(v_opt_320_);
lean_dec(v_s_319_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_setLongOption___boxed(lean_object* v_s_329_, lean_object* v_opt_330_, lean_object* v_a_00___x40___internal___hyg_331_){
_start:
{
uint8_t v_res_332_; lean_object* v_r_333_; 
v_res_332_ = lean_cadical_solver_set_long_option(v_s_329_, v_opt_330_);
lean_dec_ref(v_opt_330_);
lean_dec(v_s_329_);
v_r_333_ = lean_box(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isValidConfiguration___boxed(lean_object* v_opt_335_){
_start:
{
uint8_t v_res_336_; lean_object* v_r_337_; 
v_res_336_ = lean_cadical_solver_is_valid_configuration(v_opt_335_);
lean_dec_ref(v_opt_335_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_configure___boxed(lean_object* v_s_341_, lean_object* v_opt_342_, lean_object* v_a_00___x40___internal___hyg_343_){
_start:
{
uint8_t v_res_344_; lean_object* v_r_345_; 
v_res_344_ = lean_cadical_solver_configure(v_s_341_, v_opt_342_);
lean_dec_ref(v_opt_342_);
lean_dec(v_s_341_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_optimize___boxed(lean_object* v_s_349_, lean_object* v_val_350_, lean_object* v_a_00___x40___internal___hyg_351_){
_start:
{
uint32_t v_val_boxed_352_; lean_object* v_res_353_; 
v_val_boxed_352_ = lean_unbox_uint32(v_val_350_);
lean_dec(v_val_350_);
v_res_353_ = lean_cadical_solver_optimize(v_s_349_, v_val_boxed_352_);
lean_dec(v_s_349_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_limit___boxed(lean_object* v_s_358_, lean_object* v_limit_359_, lean_object* v_val_360_, lean_object* v_a_00___x40___internal___hyg_361_){
_start:
{
uint32_t v_val_boxed_362_; uint8_t v_res_363_; lean_object* v_r_364_; 
v_val_boxed_362_ = lean_unbox_uint32(v_val_360_);
lean_dec(v_val_360_);
v_res_363_ = lean_cadical_solver_limit(v_s_358_, v_limit_359_, v_val_boxed_362_);
lean_dec_ref(v_limit_359_);
lean_dec(v_s_358_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isValidLimit___boxed(lean_object* v_s_368_, lean_object* v_limit_369_, lean_object* v_a_00___x40___internal___hyg_370_){
_start:
{
uint8_t v_res_371_; lean_object* v_r_372_; 
v_res_371_ = lean_cadical_solver_is_valid_limit(v_s_368_, v_limit_369_);
lean_dec_ref(v_limit_369_);
lean_dec(v_s_368_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_active___boxed(lean_object* v_s_375_, lean_object* v_a_00___x40___internal___hyg_376_){
_start:
{
uint32_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = lean_cadical_solver_active(v_s_375_);
lean_dec(v_s_375_);
v_r_378_ = lean_box_uint32(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_redundant___boxed(lean_object* v_s_381_, lean_object* v_a_00___x40___internal___hyg_382_){
_start:
{
uint64_t v_res_383_; lean_object* v_r_384_; 
v_res_383_ = lean_cadical_solver_redundant(v_s_381_);
lean_dec(v_s_381_);
v_r_384_ = lean_box_uint64(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_irredundant___boxed(lean_object* v_s_387_, lean_object* v_a_00___x40___internal___hyg_388_){
_start:
{
uint64_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = lean_cadical_solver_irredundant(v_s_387_);
lean_dec(v_s_387_);
v_r_390_ = lean_box_uint64(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_simplify___boxed(lean_object* v_s_394_, lean_object* v_rounds_395_, lean_object* v_a_00___x40___internal___hyg_396_){
_start:
{
uint32_t v_rounds_boxed_397_; uint8_t v_res_398_; lean_object* v_r_399_; 
v_rounds_boxed_397_ = lean_unbox_uint32(v_rounds_395_);
lean_dec(v_rounds_395_);
v_res_398_ = lean_cadical_solver_simplify(v_s_394_, v_rounds_boxed_397_);
lean_dec(v_s_394_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_terminate___boxed(lean_object* v_s_402_, lean_object* v_a_00___x40___internal___hyg_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = lean_cadical_solver_terminate(v_s_402_);
lean_dec(v_s_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_frozen___boxed(lean_object* v_s_408_, lean_object* v_lit_409_, lean_object* v_a_00___x40___internal___hyg_410_){
_start:
{
uint32_t v_lit_boxed_411_; uint8_t v_res_412_; lean_object* v_r_413_; 
v_lit_boxed_411_ = lean_unbox_uint32(v_lit_409_);
lean_dec(v_lit_409_);
v_res_412_ = lean_cadical_solver_frozen(v_s_408_, v_lit_boxed_411_);
lean_dec(v_s_408_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_freeze___boxed(lean_object* v_s_417_, lean_object* v_lit_418_, lean_object* v_a_00___x40___internal___hyg_419_){
_start:
{
uint32_t v_lit_boxed_420_; lean_object* v_res_421_; 
v_lit_boxed_420_ = lean_unbox_uint32(v_lit_418_);
lean_dec(v_lit_418_);
v_res_421_ = lean_cadical_solver_freeze(v_s_417_, v_lit_boxed_420_);
lean_dec(v_s_417_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_melt___boxed(lean_object* v_s_425_, lean_object* v_lit_426_, lean_object* v_a_00___x40___internal___hyg_427_){
_start:
{
uint32_t v_lit_boxed_428_; lean_object* v_res_429_; 
v_lit_boxed_428_ = lean_unbox_uint32(v_lit_426_);
lean_dec(v_lit_426_);
v_res_429_ = lean_cadical_solver_melt(v_s_425_, v_lit_boxed_428_);
lean_dec(v_s_425_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_fixed___boxed(lean_object* v_s_433_, lean_object* v_lit_434_, lean_object* v_a_00___x40___internal___hyg_435_){
_start:
{
uint32_t v_lit_boxed_436_; uint32_t v_res_437_; lean_object* v_r_438_; 
v_lit_boxed_436_ = lean_unbox_uint32(v_lit_434_);
lean_dec(v_lit_434_);
v_res_437_ = lean_cadical_solver_fixed(v_s_433_, v_lit_boxed_436_);
lean_dec(v_s_433_);
v_r_438_ = lean_box_uint32(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_phase___boxed(lean_object* v_s_442_, lean_object* v_lit_443_, lean_object* v_a_00___x40___internal___hyg_444_){
_start:
{
uint32_t v_lit_boxed_445_; lean_object* v_res_446_; 
v_lit_boxed_445_ = lean_unbox_uint32(v_lit_443_);
lean_dec(v_lit_443_);
v_res_446_ = lean_cadical_solver_phase(v_s_442_, v_lit_boxed_445_);
lean_dec(v_s_442_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_unphase___boxed(lean_object* v_s_450_, lean_object* v_lit_451_, lean_object* v_a_00___x40___internal___hyg_452_){
_start:
{
uint32_t v_lit_boxed_453_; lean_object* v_res_454_; 
v_lit_boxed_453_ = lean_unbox_uint32(v_lit_451_);
lean_dec(v_lit_451_);
v_res_454_ = lean_cadical_solver_unphase(v_s_450_, v_lit_boxed_453_);
lean_dec(v_s_450_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_conclude___boxed(lean_object* v_s_457_, lean_object* v_a_00___x40___internal___hyg_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = lean_cadical_solver_conclude(v_s_457_);
lean_dec(v_s_457_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_usage___boxed(lean_object* v_a_00___x40___internal___hyg_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = lean_cadical_solver_usage();
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_configurations___boxed(lean_object* v_a_00___x40___internal___hyg_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = lean_cadical_solver_configurations();
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_statistics___boxed(lean_object* v_s_468_, lean_object* v_a_00___x40___internal___hyg_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = lean_cadical_solver_statistics(v_s_468_);
lean_dec(v_s_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_resources___boxed(lean_object* v_s_473_, lean_object* v_a_00___x40___internal___hyg_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = lean_cadical_solver_resources(v_s_473_);
lean_dec(v_s_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_state___boxed(lean_object* v_s_478_, lean_object* v_a_00___x40___internal___hyg_479_){
_start:
{
uint16_t v_res_480_; lean_object* v_r_481_; 
v_res_480_ = lean_cadical_solver_state(v_s_478_);
lean_dec(v_s_478_);
v_r_481_ = lean_box(v_res_480_);
return v_r_481_;
}
}
lean_object* runtime_initialize_Init_Data_String_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Cadical_Internal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Cadical_Internal_0__Lean_Cadical_Internal_SolverImpl = _init_l___private_Lean_Cadical_Internal_0__Lean_Cadical_Internal_SolverImpl();
l_Lean_Cadical_Internal_instInhabitedStatus_default = _init_l_Lean_Cadical_Internal_instInhabitedStatus_default();
l_Lean_Cadical_Internal_instInhabitedStatus = _init_l_Lean_Cadical_Internal_instInhabitedStatus();
l_Lean_Cadical_Internal_signature = _init_l_Lean_Cadical_Internal_signature();
lean_mark_persistent(l_Lean_Cadical_Internal_signature);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Cadical_Internal(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Init_System_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Cadical_Internal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Cadical_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Cadical_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Cadical_Internal(builtin);
}
#ifdef __cplusplus
}
#endif
