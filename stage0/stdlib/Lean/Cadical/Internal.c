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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Cadical_Internal_0__Lean_Cadical_Internal_SolverImpl;
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorIdx___impl(uint8_t v_x_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_box(v_x_2_);
v___x_4_ = lean_obj_tag_nat(v___x_3_);
lean_dec(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Cadical_Internal_Status_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Cadical_Internal_Status_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_Cadical_Internal_Status_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_satisfiable_elim___redArg(lean_object* v_satisfiable_23_){
_start:
{
lean_inc(v_satisfiable_23_);
return v_satisfiable_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_satisfiable_elim___redArg___boxed(lean_object* v_satisfiable_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Cadical_Internal_Status_satisfiable_elim___redArg(v_satisfiable_24_);
lean_dec(v_satisfiable_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_satisfiable_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_satisfiable_29_){
_start:
{
lean_inc(v_satisfiable_29_);
return v_satisfiable_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_satisfiable_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_satisfiable_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_Cadical_Internal_Status_satisfiable_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_satisfiable_33_);
lean_dec(v_satisfiable_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unsatisfiable_elim___redArg(lean_object* v_unsatisfiable_36_){
_start:
{
lean_inc(v_unsatisfiable_36_);
return v_unsatisfiable_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unsatisfiable_elim___redArg___boxed(lean_object* v_unsatisfiable_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Cadical_Internal_Status_unsatisfiable_elim___redArg(v_unsatisfiable_37_);
lean_dec(v_unsatisfiable_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unsatisfiable_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_unsatisfiable_42_){
_start:
{
lean_inc(v_unsatisfiable_42_);
return v_unsatisfiable_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unsatisfiable_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_unsatisfiable_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_Cadical_Internal_Status_unsatisfiable_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_unsatisfiable_46_);
lean_dec(v_unsatisfiable_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unknown_elim___redArg(lean_object* v_unknown_49_){
_start:
{
lean_inc(v_unknown_49_);
return v_unknown_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unknown_elim___redArg___boxed(lean_object* v_unknown_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Cadical_Internal_Status_unknown_elim___redArg(v_unknown_50_);
lean_dec(v_unknown_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unknown_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_unknown_55_){
_start:
{
lean_inc(v_unknown_55_);
return v_unknown_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unknown_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_unknown_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_Cadical_Internal_Status_unknown_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_unknown_59_);
lean_dec(v_unknown_59_);
return v_res_61_;
}
}
static uint8_t _init_l_Lean_Cadical_Internal_instInhabitedStatus_default(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static uint8_t _init_l_Lean_Cadical_Internal_instInhabitedStatus(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Internal_Status_ofNat(lean_object* v_n_64_){
_start:
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = lean_nat_dec_le(v_n_64_, v___x_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(1u);
v___x_68_ = lean_nat_dec_le(v_n_64_, v___x_67_);
if (v___x_68_ == 0)
{
uint8_t v___x_69_; 
v___x_69_ = 2;
return v___x_69_;
}
else
{
uint8_t v___x_70_; 
v___x_70_ = 1;
return v___x_70_;
}
}
else
{
uint8_t v___x_71_; 
v___x_71_ = 0;
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ofNat___boxed(lean_object* v_n_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Lean_Cadical_Internal_Status_ofNat(v_n_72_);
lean_dec(v_n_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Internal_instDecidableEqStatus(uint8_t v_x_75_, uint8_t v_y_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_77_ = lean_box(v_x_75_);
v___x_78_ = lean_obj_tag_nat(v___x_77_);
lean_dec(v___x_77_);
v___x_79_ = lean_box(v_y_76_);
v___x_80_ = lean_obj_tag_nat(v___x_79_);
lean_dec(v___x_79_);
v___x_81_ = lean_nat_dec_eq(v___x_78_, v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_instDecidableEqStatus___boxed(lean_object* v_x_82_, lean_object* v_y_83_){
_start:
{
uint8_t v_x_23__boxed_84_; uint8_t v_y_24__boxed_85_; uint8_t v_res_86_; lean_object* v_r_87_; 
v_x_23__boxed_84_ = lean_unbox(v_x_82_);
v_y_24__boxed_85_ = lean_unbox(v_y_83_);
v_res_86_ = l_Lean_Cadical_Internal_instDecidableEqStatus(v_x_23__boxed_84_, v_y_24__boxed_85_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT uint64_t l_Lean_Cadical_Internal_instHashableStatus_hash(uint8_t v_x_88_){
_start:
{
switch(v_x_88_)
{
case 0:
{
uint64_t v___x_89_; 
v___x_89_ = 0ULL;
return v___x_89_;
}
case 1:
{
uint64_t v___x_90_; 
v___x_90_ = 1ULL;
return v___x_90_;
}
default: 
{
uint64_t v___x_91_; 
v___x_91_ = 2ULL;
return v___x_91_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_instHashableStatus_hash___boxed(lean_object* v_x_92_){
_start:
{
uint8_t v_x_40__boxed_93_; uint64_t v_res_94_; lean_object* v_r_95_; 
v_x_40__boxed_93_ = lean_unbox(v_x_92_);
v_res_94_ = l_Lean_Cadical_Internal_instHashableStatus_hash(v_x_40__boxed_93_);
v_r_95_ = lean_box_uint64(v_res_94_);
return v_r_95_;
}
}
static lean_object* _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__6(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_unsigned_to_nat(2u);
v___x_108_ = lean_nat_to_int(v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__7(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(1u);
v___x_110_ = lean_nat_to_int(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_instReprStatus_repr(uint8_t v_x_111_, lean_object* v_prec_112_){
_start:
{
lean_object* v___y_114_; lean_object* v___y_121_; lean_object* v___y_128_; 
switch(v_x_111_)
{
case 0:
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(1024u);
v___x_135_ = lean_nat_dec_le(v___x_134_, v_prec_112_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_Lean_Cadical_Internal_instReprStatus_repr___closed__6, &l_Lean_Cadical_Internal_instReprStatus_repr___closed__6_once, _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__6);
v___y_114_ = v___x_136_;
goto v___jp_113_;
}
else
{
lean_object* v___x_137_; 
v___x_137_ = lean_obj_once(&l_Lean_Cadical_Internal_instReprStatus_repr___closed__7, &l_Lean_Cadical_Internal_instReprStatus_repr___closed__7_once, _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__7);
v___y_114_ = v___x_137_;
goto v___jp_113_;
}
}
case 1:
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(1024u);
v___x_139_ = lean_nat_dec_le(v___x_138_, v_prec_112_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_Lean_Cadical_Internal_instReprStatus_repr___closed__6, &l_Lean_Cadical_Internal_instReprStatus_repr___closed__6_once, _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__6);
v___y_121_ = v___x_140_;
goto v___jp_120_;
}
else
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&l_Lean_Cadical_Internal_instReprStatus_repr___closed__7, &l_Lean_Cadical_Internal_instReprStatus_repr___closed__7_once, _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__7);
v___y_121_ = v___x_141_;
goto v___jp_120_;
}
}
default: 
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(1024u);
v___x_143_ = lean_nat_dec_le(v___x_142_, v_prec_112_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; 
v___x_144_ = lean_obj_once(&l_Lean_Cadical_Internal_instReprStatus_repr___closed__6, &l_Lean_Cadical_Internal_instReprStatus_repr___closed__6_once, _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__6);
v___y_128_ = v___x_144_;
goto v___jp_127_;
}
else
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_once(&l_Lean_Cadical_Internal_instReprStatus_repr___closed__7, &l_Lean_Cadical_Internal_instReprStatus_repr___closed__7_once, _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__7);
v___y_128_ = v___x_145_;
goto v___jp_127_;
}
}
}
v___jp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_115_ = ((lean_object*)(l_Lean_Cadical_Internal_instReprStatus_repr___closed__1));
lean_inc(v___y_114_);
v___x_116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_116_, 0, v___y_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = 0;
v___x_118_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_118_, 0, v___x_116_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*1, v___x_117_);
v___x_119_ = l_Repr_addAppParen(v___x_118_, v_prec_112_);
return v___x_119_;
}
v___jp_120_:
{
lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_122_ = ((lean_object*)(l_Lean_Cadical_Internal_instReprStatus_repr___closed__3));
lean_inc(v___y_121_);
v___x_123_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_123_, 0, v___y_121_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v___x_124_ = 0;
v___x_125_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*1, v___x_124_);
v___x_126_ = l_Repr_addAppParen(v___x_125_, v_prec_112_);
return v___x_126_;
}
v___jp_127_:
{
lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_129_ = ((lean_object*)(l_Lean_Cadical_Internal_instReprStatus_repr___closed__5));
lean_inc(v___y_128_);
v___x_130_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_130_, 0, v___y_128_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = 0;
v___x_132_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_132_, 0, v___x_130_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*1, v___x_131_);
v___x_133_ = l_Repr_addAppParen(v___x_132_, v_prec_112_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_instReprStatus_repr___boxed(lean_object* v_x_146_, lean_object* v_prec_147_){
_start:
{
uint8_t v_x_171__boxed_148_; lean_object* v_res_149_; 
v_x_171__boxed_148_ = lean_unbox(v_x_146_);
v_res_149_ = l_Lean_Cadical_Internal_instReprStatus_repr(v_x_171__boxed_148_, v_prec_147_);
lean_dec(v_prec_147_);
return v_res_149_;
}
}
static uint32_t _init_l_Lean_Cadical_Internal_Status_toInt32___closed__0(void){
_start:
{
lean_object* v___x_152_; uint32_t v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(10u);
v___x_153_ = lean_int32_of_nat(v___x_152_);
return v___x_153_;
}
}
static uint32_t _init_l_Lean_Cadical_Internal_Status_toInt32___closed__1(void){
_start:
{
lean_object* v___x_154_; uint32_t v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(20u);
v___x_155_ = lean_int32_of_nat(v___x_154_);
return v___x_155_;
}
}
static uint32_t _init_l_Lean_Cadical_Internal_Status_toInt32___closed__2(void){
_start:
{
lean_object* v___x_156_; uint32_t v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_int32_of_nat(v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT uint32_t l_Lean_Cadical_Internal_Status_toInt32(uint8_t v_x_158_){
_start:
{
switch(v_x_158_)
{
case 0:
{
uint32_t v___x_159_; 
v___x_159_ = lean_uint32_once(&l_Lean_Cadical_Internal_Status_toInt32___closed__0, &l_Lean_Cadical_Internal_Status_toInt32___closed__0_once, _init_l_Lean_Cadical_Internal_Status_toInt32___closed__0);
return v___x_159_;
}
case 1:
{
uint32_t v___x_160_; 
v___x_160_ = lean_uint32_once(&l_Lean_Cadical_Internal_Status_toInt32___closed__1, &l_Lean_Cadical_Internal_Status_toInt32___closed__1_once, _init_l_Lean_Cadical_Internal_Status_toInt32___closed__1);
return v___x_160_;
}
default: 
{
uint32_t v___x_161_; 
v___x_161_ = lean_uint32_once(&l_Lean_Cadical_Internal_Status_toInt32___closed__2, &l_Lean_Cadical_Internal_Status_toInt32___closed__2_once, _init_l_Lean_Cadical_Internal_Status_toInt32___closed__2);
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_toInt32___boxed(lean_object* v_x_162_){
_start:
{
uint8_t v_x_52__boxed_163_; uint32_t v_res_164_; lean_object* v_r_165_; 
v_x_52__boxed_163_ = lean_unbox(v_x_162_);
v_res_164_ = l_Lean_Cadical_Internal_Status_toInt32(v_x_52__boxed_163_);
v_r_165_ = lean_box_uint32(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Cadical_Internal_0__Lean_Cadical_Internal_getSignature___boxed(lean_object* v_u_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = lean_cadical_signature(v_u_167_);
return v_res_168_;
}
}
static lean_object* _init_l_Lean_Cadical_Internal_signature___closed__0(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_box(0);
v___x_170_ = lean_cadical_signature(v___x_169_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_Cadical_Internal_signature(void){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l_Lean_Cadical_Internal_signature___closed__0, &l_Lean_Cadical_Internal_signature___closed__0_once, _init_l_Lean_Cadical_Internal_signature___closed__0);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_new___boxed(lean_object* v_a_00___x40___internal___hyg_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = lean_cadical_solver_new();
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_add___boxed(lean_object* v_s_178_, lean_object* v_lit_179_, lean_object* v_a_00___x40___internal___hyg_180_){
_start:
{
uint32_t v_lit_boxed_181_; lean_object* v_res_182_; 
v_lit_boxed_181_ = lean_unbox_uint32(v_lit_179_);
lean_dec(v_lit_179_);
v_res_182_ = lean_cadical_solver_add(v_s_178_, v_lit_boxed_181_);
lean_dec(v_s_178_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_clause___boxed(lean_object* v_s_186_, lean_object* v_lits_187_, lean_object* v_a_00___x40___internal___hyg_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = lean_cadical_solver_clause(v_s_186_, v_lits_187_);
lean_dec_ref(v_lits_187_);
lean_dec(v_s_186_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_inconsistent___boxed(lean_object* v_s_192_, lean_object* v_a_00___x40___internal___hyg_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = lean_cadical_solver_inconsistent(v_s_192_);
lean_dec(v_s_192_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_assume___boxed(lean_object* v_s_199_, lean_object* v_lit_200_, lean_object* v_a_00___x40___internal___hyg_201_){
_start:
{
uint32_t v_lit_boxed_202_; lean_object* v_res_203_; 
v_lit_boxed_202_ = lean_unbox_uint32(v_lit_200_);
lean_dec(v_lit_200_);
v_res_203_ = lean_cadical_solver_assume(v_s_199_, v_lit_boxed_202_);
lean_dec(v_s_199_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_solve___boxed(lean_object* v_s_206_, lean_object* v_a_00___x40___internal___hyg_207_){
_start:
{
uint8_t v_res_208_; lean_object* v_r_209_; 
v_res_208_ = lean_cadical_solver_solve(v_s_206_);
lean_dec(v_s_206_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_val___boxed(lean_object* v_s_213_, lean_object* v_lit_214_, lean_object* v_a_00___x40___internal___hyg_215_){
_start:
{
uint32_t v_lit_boxed_216_; uint32_t v_res_217_; lean_object* v_r_218_; 
v_lit_boxed_216_ = lean_unbox_uint32(v_lit_214_);
lean_dec(v_lit_214_);
v_res_217_ = lean_cadical_solver_val(v_s_213_, v_lit_boxed_216_);
lean_dec(v_s_213_);
v_r_218_ = lean_box_uint32(v_res_217_);
return v_r_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_flip___boxed(lean_object* v_s_222_, lean_object* v_lit_223_, lean_object* v_a_00___x40___internal___hyg_224_){
_start:
{
uint32_t v_lit_boxed_225_; uint8_t v_res_226_; lean_object* v_r_227_; 
v_lit_boxed_225_ = lean_unbox_uint32(v_lit_223_);
lean_dec(v_lit_223_);
v_res_226_ = lean_cadical_solver_flip(v_s_222_, v_lit_boxed_225_);
lean_dec(v_s_222_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_flippable___boxed(lean_object* v_s_231_, lean_object* v_lit_232_, lean_object* v_a_00___x40___internal___hyg_233_){
_start:
{
uint32_t v_lit_boxed_234_; uint8_t v_res_235_; lean_object* v_r_236_; 
v_lit_boxed_234_ = lean_unbox_uint32(v_lit_232_);
lean_dec(v_lit_232_);
v_res_235_ = lean_cadical_solver_flippable(v_s_231_, v_lit_boxed_234_);
lean_dec(v_s_231_);
v_r_236_ = lean_box(v_res_235_);
return v_r_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_failed___boxed(lean_object* v_s_240_, lean_object* v_lit_241_, lean_object* v_a_00___x40___internal___hyg_242_){
_start:
{
uint32_t v_lit_boxed_243_; uint8_t v_res_244_; lean_object* v_r_245_; 
v_lit_boxed_243_ = lean_unbox_uint32(v_lit_241_);
lean_dec(v_lit_241_);
v_res_244_ = lean_cadical_solver_failed(v_s_240_, v_lit_boxed_243_);
lean_dec(v_s_240_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_constrain___boxed(lean_object* v_s_249_, lean_object* v_lit_250_, lean_object* v_a_00___x40___internal___hyg_251_){
_start:
{
uint32_t v_lit_boxed_252_; lean_object* v_res_253_; 
v_lit_boxed_252_ = lean_unbox_uint32(v_lit_250_);
lean_dec(v_lit_250_);
v_res_253_ = lean_cadical_solver_constrain(v_s_249_, v_lit_boxed_252_);
lean_dec(v_s_249_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_constraintFailed___boxed(lean_object* v_s_256_, lean_object* v_a_00___x40___internal___hyg_257_){
_start:
{
uint8_t v_res_258_; lean_object* v_r_259_; 
v_res_258_ = lean_cadical_solver_constraint_failed(v_s_256_);
lean_dec(v_s_256_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_lookahead___boxed(lean_object* v_s_262_, lean_object* v_a_00___x40___internal___hyg_263_){
_start:
{
uint32_t v_res_264_; lean_object* v_r_265_; 
v_res_264_ = lean_cadical_solver_lookahead(v_s_262_);
lean_dec(v_s_262_);
v_r_265_ = lean_box_uint32(v_res_264_);
return v_r_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_resetAssumptions___boxed(lean_object* v_s_268_, lean_object* v_a_00___x40___internal___hyg_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = lean_cadical_solver_reset_assumptions(v_s_268_);
lean_dec(v_s_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_resetConstraint___boxed(lean_object* v_s_273_, lean_object* v_a_00___x40___internal___hyg_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = lean_cadical_solver_reset_constraint(v_s_273_);
lean_dec(v_s_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_status___boxed(lean_object* v_s_278_, lean_object* v_a_00___x40___internal___hyg_279_){
_start:
{
uint8_t v_res_280_; lean_object* v_r_281_; 
v_res_280_ = lean_cadical_solver_status(v_s_278_);
lean_dec(v_s_278_);
v_r_281_ = lean_box(v_res_280_);
return v_r_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_vars___boxed(lean_object* v_s_284_, lean_object* v_a_00___x40___internal___hyg_285_){
_start:
{
uint32_t v_res_286_; lean_object* v_r_287_; 
v_res_286_ = lean_cadical_solver_vars(v_s_284_);
lean_dec(v_s_284_);
v_r_287_ = lean_box_uint32(v_res_286_);
return v_r_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_resize___boxed(lean_object* v_s_291_, lean_object* v_minMaxVar_292_, lean_object* v_a_00___x40___internal___hyg_293_){
_start:
{
uint32_t v_minMaxVar_boxed_294_; lean_object* v_res_295_; 
v_minMaxVar_boxed_294_ = lean_unbox_uint32(v_minMaxVar_292_);
lean_dec(v_minMaxVar_292_);
v_res_295_ = lean_cadical_solver_resize(v_s_291_, v_minMaxVar_boxed_294_);
lean_dec(v_s_291_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isValidOption___boxed(lean_object* v_opt_297_){
_start:
{
uint8_t v_res_298_; lean_object* v_r_299_; 
v_res_298_ = lean_cadical_solver_is_valid_option(v_opt_297_);
lean_dec_ref(v_opt_297_);
v_r_299_ = lean_box(v_res_298_);
return v_r_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isPreprocessingOption___boxed(lean_object* v_opt_301_){
_start:
{
uint8_t v_res_302_; lean_object* v_r_303_; 
v_res_302_ = lean_cadical_solver_is_preprocessing_option(v_opt_301_);
lean_dec_ref(v_opt_301_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isValidLongOption___boxed(lean_object* v_opt_305_){
_start:
{
uint8_t v_res_306_; lean_object* v_r_307_; 
v_res_306_ = lean_cadical_solver_is_valid_long_option(v_opt_305_);
lean_dec_ref(v_opt_305_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_get___boxed(lean_object* v_s_311_, lean_object* v_opt_312_, lean_object* v_a_00___x40___internal___hyg_313_){
_start:
{
uint32_t v_res_314_; lean_object* v_r_315_; 
v_res_314_ = lean_cadical_solver_get(v_s_311_, v_opt_312_);
lean_dec_ref(v_opt_312_);
lean_dec(v_s_311_);
v_r_315_ = lean_box_uint32(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_set___boxed(lean_object* v_s_320_, lean_object* v_opt_321_, lean_object* v_val_322_, lean_object* v_a_00___x40___internal___hyg_323_){
_start:
{
uint32_t v_val_boxed_324_; uint8_t v_res_325_; lean_object* v_r_326_; 
v_val_boxed_324_ = lean_unbox_uint32(v_val_322_);
lean_dec(v_val_322_);
v_res_325_ = lean_cadical_solver_set(v_s_320_, v_opt_321_, v_val_boxed_324_);
lean_dec_ref(v_opt_321_);
lean_dec(v_s_320_);
v_r_326_ = lean_box(v_res_325_);
return v_r_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_setLongOption___boxed(lean_object* v_s_330_, lean_object* v_opt_331_, lean_object* v_a_00___x40___internal___hyg_332_){
_start:
{
uint8_t v_res_333_; lean_object* v_r_334_; 
v_res_333_ = lean_cadical_solver_set_long_option(v_s_330_, v_opt_331_);
lean_dec_ref(v_opt_331_);
lean_dec(v_s_330_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isValidConfiguration___boxed(lean_object* v_opt_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = lean_cadical_solver_is_valid_configuration(v_opt_336_);
lean_dec_ref(v_opt_336_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_configure___boxed(lean_object* v_s_342_, lean_object* v_opt_343_, lean_object* v_a_00___x40___internal___hyg_344_){
_start:
{
uint8_t v_res_345_; lean_object* v_r_346_; 
v_res_345_ = lean_cadical_solver_configure(v_s_342_, v_opt_343_);
lean_dec_ref(v_opt_343_);
lean_dec(v_s_342_);
v_r_346_ = lean_box(v_res_345_);
return v_r_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_optimize___boxed(lean_object* v_s_350_, lean_object* v_val_351_, lean_object* v_a_00___x40___internal___hyg_352_){
_start:
{
uint32_t v_val_boxed_353_; lean_object* v_res_354_; 
v_val_boxed_353_ = lean_unbox_uint32(v_val_351_);
lean_dec(v_val_351_);
v_res_354_ = lean_cadical_solver_optimize(v_s_350_, v_val_boxed_353_);
lean_dec(v_s_350_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_limit___boxed(lean_object* v_s_359_, lean_object* v_limit_360_, lean_object* v_val_361_, lean_object* v_a_00___x40___internal___hyg_362_){
_start:
{
uint32_t v_val_boxed_363_; uint8_t v_res_364_; lean_object* v_r_365_; 
v_val_boxed_363_ = lean_unbox_uint32(v_val_361_);
lean_dec(v_val_361_);
v_res_364_ = lean_cadical_solver_limit(v_s_359_, v_limit_360_, v_val_boxed_363_);
lean_dec_ref(v_limit_360_);
lean_dec(v_s_359_);
v_r_365_ = lean_box(v_res_364_);
return v_r_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isValidLimit___boxed(lean_object* v_s_369_, lean_object* v_limit_370_, lean_object* v_a_00___x40___internal___hyg_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = lean_cadical_solver_is_valid_limit(v_s_369_, v_limit_370_);
lean_dec_ref(v_limit_370_);
lean_dec(v_s_369_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_active___boxed(lean_object* v_s_376_, lean_object* v_a_00___x40___internal___hyg_377_){
_start:
{
uint32_t v_res_378_; lean_object* v_r_379_; 
v_res_378_ = lean_cadical_solver_active(v_s_376_);
lean_dec(v_s_376_);
v_r_379_ = lean_box_uint32(v_res_378_);
return v_r_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_redundant___boxed(lean_object* v_s_382_, lean_object* v_a_00___x40___internal___hyg_383_){
_start:
{
uint64_t v_res_384_; lean_object* v_r_385_; 
v_res_384_ = lean_cadical_solver_redundant(v_s_382_);
lean_dec(v_s_382_);
v_r_385_ = lean_box_uint64(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_irredundant___boxed(lean_object* v_s_388_, lean_object* v_a_00___x40___internal___hyg_389_){
_start:
{
uint64_t v_res_390_; lean_object* v_r_391_; 
v_res_390_ = lean_cadical_solver_irredundant(v_s_388_);
lean_dec(v_s_388_);
v_r_391_ = lean_box_uint64(v_res_390_);
return v_r_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_simplify___boxed(lean_object* v_s_395_, lean_object* v_rounds_396_, lean_object* v_a_00___x40___internal___hyg_397_){
_start:
{
uint32_t v_rounds_boxed_398_; uint8_t v_res_399_; lean_object* v_r_400_; 
v_rounds_boxed_398_ = lean_unbox_uint32(v_rounds_396_);
lean_dec(v_rounds_396_);
v_res_399_ = lean_cadical_solver_simplify(v_s_395_, v_rounds_boxed_398_);
lean_dec(v_s_395_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_terminate___boxed(lean_object* v_s_403_, lean_object* v_a_00___x40___internal___hyg_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = lean_cadical_solver_terminate(v_s_403_);
lean_dec(v_s_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_frozen___boxed(lean_object* v_s_409_, lean_object* v_lit_410_, lean_object* v_a_00___x40___internal___hyg_411_){
_start:
{
uint32_t v_lit_boxed_412_; uint8_t v_res_413_; lean_object* v_r_414_; 
v_lit_boxed_412_ = lean_unbox_uint32(v_lit_410_);
lean_dec(v_lit_410_);
v_res_413_ = lean_cadical_solver_frozen(v_s_409_, v_lit_boxed_412_);
lean_dec(v_s_409_);
v_r_414_ = lean_box(v_res_413_);
return v_r_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_freeze___boxed(lean_object* v_s_418_, lean_object* v_lit_419_, lean_object* v_a_00___x40___internal___hyg_420_){
_start:
{
uint32_t v_lit_boxed_421_; lean_object* v_res_422_; 
v_lit_boxed_421_ = lean_unbox_uint32(v_lit_419_);
lean_dec(v_lit_419_);
v_res_422_ = lean_cadical_solver_freeze(v_s_418_, v_lit_boxed_421_);
lean_dec(v_s_418_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_melt___boxed(lean_object* v_s_426_, lean_object* v_lit_427_, lean_object* v_a_00___x40___internal___hyg_428_){
_start:
{
uint32_t v_lit_boxed_429_; lean_object* v_res_430_; 
v_lit_boxed_429_ = lean_unbox_uint32(v_lit_427_);
lean_dec(v_lit_427_);
v_res_430_ = lean_cadical_solver_melt(v_s_426_, v_lit_boxed_429_);
lean_dec(v_s_426_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_fixed___boxed(lean_object* v_s_434_, lean_object* v_lit_435_, lean_object* v_a_00___x40___internal___hyg_436_){
_start:
{
uint32_t v_lit_boxed_437_; uint32_t v_res_438_; lean_object* v_r_439_; 
v_lit_boxed_437_ = lean_unbox_uint32(v_lit_435_);
lean_dec(v_lit_435_);
v_res_438_ = lean_cadical_solver_fixed(v_s_434_, v_lit_boxed_437_);
lean_dec(v_s_434_);
v_r_439_ = lean_box_uint32(v_res_438_);
return v_r_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_phase___boxed(lean_object* v_s_443_, lean_object* v_lit_444_, lean_object* v_a_00___x40___internal___hyg_445_){
_start:
{
uint32_t v_lit_boxed_446_; lean_object* v_res_447_; 
v_lit_boxed_446_ = lean_unbox_uint32(v_lit_444_);
lean_dec(v_lit_444_);
v_res_447_ = lean_cadical_solver_phase(v_s_443_, v_lit_boxed_446_);
lean_dec(v_s_443_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_unphase___boxed(lean_object* v_s_451_, lean_object* v_lit_452_, lean_object* v_a_00___x40___internal___hyg_453_){
_start:
{
uint32_t v_lit_boxed_454_; lean_object* v_res_455_; 
v_lit_boxed_454_ = lean_unbox_uint32(v_lit_452_);
lean_dec(v_lit_452_);
v_res_455_ = lean_cadical_solver_unphase(v_s_451_, v_lit_boxed_454_);
lean_dec(v_s_451_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_conclude___boxed(lean_object* v_s_458_, lean_object* v_a_00___x40___internal___hyg_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = lean_cadical_solver_conclude(v_s_458_);
lean_dec(v_s_458_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_usage___boxed(lean_object* v_a_00___x40___internal___hyg_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = lean_cadical_solver_usage();
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_configurations___boxed(lean_object* v_a_00___x40___internal___hyg_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = lean_cadical_solver_configurations();
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_statistics___boxed(lean_object* v_s_469_, lean_object* v_a_00___x40___internal___hyg_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = lean_cadical_solver_statistics(v_s_469_);
lean_dec(v_s_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_resources___boxed(lean_object* v_s_474_, lean_object* v_a_00___x40___internal___hyg_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = lean_cadical_solver_resources(v_s_474_);
lean_dec(v_s_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_state___boxed(lean_object* v_s_479_, lean_object* v_a_00___x40___internal___hyg_480_){
_start:
{
uint16_t v_res_481_; lean_object* v_r_482_; 
v_res_481_ = lean_cadical_solver_state(v_s_479_);
lean_dec(v_s_479_);
v_r_482_ = lean_box(v_res_481_);
return v_r_482_;
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
