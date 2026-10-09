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
lean_object* l_Lean_Cadical_Internal_Status_ctorIdx___impl(uint8_t v_x_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_box(v_x_2_);
v___x_4_ = lean_obj_tag_nat(v___x_3_);
lean_dec(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Status_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2_ = stack[0].m_num;
lean_object* v_res_5_;
v_res_5_ = l_Lean_Cadical_Internal_Status_ctorIdx___impl(v_x_2_);
stack->m_obj
 = v_res_5_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorIdx___impl___boxed(lean_object* v_x_6_){
_start:
{
uint8_t v_x_4__boxed_7_; lean_object* v_res_8_; 
v_x_4__boxed_7_ = lean_unbox(v_x_6_);
v_res_8_ = l_Lean_Cadical_Internal_Status_ctorIdx___impl(v_x_4__boxed_7_);
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
lean_object* l_Lean_Cadical_Internal_Status_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, uint8_t v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_inc(v_k_16_);
return v_k_16_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Status_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_13_ = stack[1].m_obj;
uint8_t v_t_14_ = stack[2].m_num;
lean_object* v_k_16_ = stack[4].m_obj;
lean_object* v_res_17_;
v_res_17_ = l_Lean_Cadical_Internal_Status_ctorElim(lean_box(0), v_ctorIdx_13_, v_t_14_, lean_box(0), v_k_16_);
stack->m_obj
 = v_res_17_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
uint8_t v_t_boxed_23_; lean_object* v_res_24_; 
v_t_boxed_23_ = lean_unbox(v_t_20_);
v_res_24_ = l_Lean_Cadical_Internal_Status_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_boxed_23_, v_h_21_, v_k_22_);
lean_dec(v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_satisfiable_elim___redArg(lean_object* v_satisfiable_25_){
_start:
{
lean_inc(v_satisfiable_25_);
return v_satisfiable_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_satisfiable_elim___redArg___boxed(lean_object* v_satisfiable_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_Cadical_Internal_Status_satisfiable_elim___redArg(v_satisfiable_26_);
lean_dec(v_satisfiable_26_);
return v_res_27_;
}
}
lean_object* l_Lean_Cadical_Internal_Status_satisfiable_elim(lean_object* v_motive_28_, uint8_t v_t_29_, lean_object* v_h_30_, lean_object* v_satisfiable_31_){
_start:
{
lean_inc(v_satisfiable_31_);
return v_satisfiable_31_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Status_satisfiable_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_29_ = stack[1].m_num;
lean_object* v_satisfiable_31_ = stack[3].m_obj;
lean_object* v_res_32_;
v_res_32_ = l_Lean_Cadical_Internal_Status_satisfiable_elim(lean_box(0), v_t_29_, lean_box(0), v_satisfiable_31_);
stack->m_obj
 = v_res_32_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_satisfiable_elim___boxed(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_satisfiable_36_){
_start:
{
uint8_t v_t_boxed_37_; lean_object* v_res_38_; 
v_t_boxed_37_ = lean_unbox(v_t_34_);
v_res_38_ = l_Lean_Cadical_Internal_Status_satisfiable_elim(v_motive_33_, v_t_boxed_37_, v_h_35_, v_satisfiable_36_);
lean_dec(v_satisfiable_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unsatisfiable_elim___redArg(lean_object* v_unsatisfiable_39_){
_start:
{
lean_inc(v_unsatisfiable_39_);
return v_unsatisfiable_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unsatisfiable_elim___redArg___boxed(lean_object* v_unsatisfiable_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_Cadical_Internal_Status_unsatisfiable_elim___redArg(v_unsatisfiable_40_);
lean_dec(v_unsatisfiable_40_);
return v_res_41_;
}
}
lean_object* l_Lean_Cadical_Internal_Status_unsatisfiable_elim(lean_object* v_motive_42_, uint8_t v_t_43_, lean_object* v_h_44_, lean_object* v_unsatisfiable_45_){
_start:
{
lean_inc(v_unsatisfiable_45_);
return v_unsatisfiable_45_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Status_unsatisfiable_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_43_ = stack[1].m_num;
lean_object* v_unsatisfiable_45_ = stack[3].m_obj;
lean_object* v_res_46_;
v_res_46_ = l_Lean_Cadical_Internal_Status_unsatisfiable_elim(lean_box(0), v_t_43_, lean_box(0), v_unsatisfiable_45_);
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unsatisfiable_elim___boxed(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_unsatisfiable_50_){
_start:
{
uint8_t v_t_boxed_51_; lean_object* v_res_52_; 
v_t_boxed_51_ = lean_unbox(v_t_48_);
v_res_52_ = l_Lean_Cadical_Internal_Status_unsatisfiable_elim(v_motive_47_, v_t_boxed_51_, v_h_49_, v_unsatisfiable_50_);
lean_dec(v_unsatisfiable_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unknown_elim___redArg(lean_object* v_unknown_53_){
_start:
{
lean_inc(v_unknown_53_);
return v_unknown_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unknown_elim___redArg___boxed(lean_object* v_unknown_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_Cadical_Internal_Status_unknown_elim___redArg(v_unknown_54_);
lean_dec(v_unknown_54_);
return v_res_55_;
}
}
lean_object* l_Lean_Cadical_Internal_Status_unknown_elim(lean_object* v_motive_56_, uint8_t v_t_57_, lean_object* v_h_58_, lean_object* v_unknown_59_){
_start:
{
lean_inc(v_unknown_59_);
return v_unknown_59_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Status_unknown_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_57_ = stack[1].m_num;
lean_object* v_unknown_59_ = stack[3].m_obj;
lean_object* v_res_60_;
v_res_60_ = l_Lean_Cadical_Internal_Status_unknown_elim(lean_box(0), v_t_57_, lean_box(0), v_unknown_59_);
stack->m_obj
 = v_res_60_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_unknown_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_unknown_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_Cadical_Internal_Status_unknown_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_unknown_64_);
lean_dec(v_unknown_64_);
return v_res_66_;
}
}
static uint8_t _init_l_Lean_Cadical_Internal_instInhabitedStatus_default(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
static uint8_t _init_l_Lean_Cadical_Internal_instInhabitedStatus(void){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
uint8_t l_Lean_Cadical_Internal_Status_ofNat(lean_object* v_n_69_){
_start:
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_nat_dec_le(v_n_69_, v___x_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_dec_le(v_n_69_, v___x_72_);
if (v___x_73_ == 0)
{
uint8_t v___x_74_; 
v___x_74_ = 2;
return v___x_74_;
}
else
{
uint8_t v___x_75_; 
v___x_75_ = 1;
return v___x_75_;
}
}
else
{
uint8_t v___x_76_; 
v___x_76_ = 0;
return v___x_76_;
}
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Status_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_69_ = stack[0].m_obj;
uint8_t v_res_77_;
v_res_77_ = l_Lean_Cadical_Internal_Status_ofNat(v_n_69_);
stack->m_num = v_res_77_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_ofNat___boxed(lean_object* v_n_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Lean_Cadical_Internal_Status_ofNat(v_n_78_);
lean_dec(v_n_78_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
uint8_t l_Lean_Cadical_Internal_instDecidableEqStatus(uint8_t v_x_81_, uint8_t v_y_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_83_ = lean_box(v_x_81_);
v___x_84_ = lean_obj_tag_nat(v___x_83_);
lean_dec(v___x_83_);
v___x_85_ = lean_box(v_y_82_);
v___x_86_ = lean_obj_tag_nat(v___x_85_);
lean_dec(v___x_85_);
v___x_87_ = lean_nat_dec_eq(v___x_84_, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_instDecidableEqStatus_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_81_ = stack[0].m_num;
uint8_t v_y_82_ = stack[1].m_num;
uint8_t v_res_88_;
v_res_88_ = l_Lean_Cadical_Internal_instDecidableEqStatus(v_x_81_, v_y_82_);
stack->m_num = v_res_88_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_instDecidableEqStatus___boxed(lean_object* v_x_89_, lean_object* v_y_90_){
_start:
{
uint8_t v_x_23__boxed_91_; uint8_t v_y_24__boxed_92_; uint8_t v_res_93_; lean_object* v_r_94_; 
v_x_23__boxed_91_ = lean_unbox(v_x_89_);
v_y_24__boxed_92_ = lean_unbox(v_y_90_);
v_res_93_ = l_Lean_Cadical_Internal_instDecidableEqStatus(v_x_23__boxed_91_, v_y_24__boxed_92_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
uint64_t l_Lean_Cadical_Internal_instHashableStatus_hash(uint8_t v_x_95_){
_start:
{
switch(v_x_95_)
{
case 0:
{
uint64_t v___x_96_; 
v___x_96_ = 0ULL;
return v___x_96_;
}
case 1:
{
uint64_t v___x_97_; 
v___x_97_ = 1ULL;
return v___x_97_;
}
default: 
{
uint64_t v___x_98_; 
v___x_98_ = 2ULL;
return v___x_98_;
}
}
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_instHashableStatus_hash_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_95_ = stack[0].m_num;
uint64_t v_res_99_;
v_res_99_ = l_Lean_Cadical_Internal_instHashableStatus_hash(v_x_95_);
stack->m_num = v_res_99_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_instHashableStatus_hash___boxed(lean_object* v_x_100_){
_start:
{
uint8_t v_x_40__boxed_101_; uint64_t v_res_102_; lean_object* v_r_103_; 
v_x_40__boxed_101_ = lean_unbox(v_x_100_);
v_res_102_ = l_Lean_Cadical_Internal_instHashableStatus_hash(v_x_40__boxed_101_);
v_r_103_ = lean_box_uint64(v_res_102_);
return v_r_103_;
}
}
static lean_object* _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__6(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_unsigned_to_nat(2u);
v___x_116_ = lean_nat_to_int(v___x_115_);
return v___x_116_;
}
}
static lean_object* _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__7(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_unsigned_to_nat(1u);
v___x_118_ = lean_nat_to_int(v___x_117_);
return v___x_118_;
}
}
lean_object* l_Lean_Cadical_Internal_instReprStatus_repr(uint8_t v_x_119_, lean_object* v_prec_120_){
_start:
{
lean_object* v___y_122_; lean_object* v___y_129_; lean_object* v___y_136_; 
switch(v_x_119_)
{
case 0:
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(1024u);
v___x_143_ = lean_nat_dec_le(v___x_142_, v_prec_120_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; 
v___x_144_ = lean_obj_once(&l_Lean_Cadical_Internal_instReprStatus_repr___closed__6, &l_Lean_Cadical_Internal_instReprStatus_repr___closed__6_once, _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__6);
v___y_122_ = v___x_144_;
goto v___jp_121_;
}
else
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_once(&l_Lean_Cadical_Internal_instReprStatus_repr___closed__7, &l_Lean_Cadical_Internal_instReprStatus_repr___closed__7_once, _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__7);
v___y_122_ = v___x_145_;
goto v___jp_121_;
}
}
case 1:
{
lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_146_ = lean_unsigned_to_nat(1024u);
v___x_147_ = lean_nat_dec_le(v___x_146_, v_prec_120_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; 
v___x_148_ = lean_obj_once(&l_Lean_Cadical_Internal_instReprStatus_repr___closed__6, &l_Lean_Cadical_Internal_instReprStatus_repr___closed__6_once, _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__6);
v___y_129_ = v___x_148_;
goto v___jp_128_;
}
else
{
lean_object* v___x_149_; 
v___x_149_ = lean_obj_once(&l_Lean_Cadical_Internal_instReprStatus_repr___closed__7, &l_Lean_Cadical_Internal_instReprStatus_repr___closed__7_once, _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__7);
v___y_129_ = v___x_149_;
goto v___jp_128_;
}
}
default: 
{
lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_150_ = lean_unsigned_to_nat(1024u);
v___x_151_ = lean_nat_dec_le(v___x_150_, v_prec_120_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; 
v___x_152_ = lean_obj_once(&l_Lean_Cadical_Internal_instReprStatus_repr___closed__6, &l_Lean_Cadical_Internal_instReprStatus_repr___closed__6_once, _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__6);
v___y_136_ = v___x_152_;
goto v___jp_135_;
}
else
{
lean_object* v___x_153_; 
v___x_153_ = lean_obj_once(&l_Lean_Cadical_Internal_instReprStatus_repr___closed__7, &l_Lean_Cadical_Internal_instReprStatus_repr___closed__7_once, _init_l_Lean_Cadical_Internal_instReprStatus_repr___closed__7);
v___y_136_ = v___x_153_;
goto v___jp_135_;
}
}
}
v___jp_121_:
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_123_ = ((lean_object*)(l_Lean_Cadical_Internal_instReprStatus_repr___closed__1));
lean_inc(v___y_122_);
v___x_124_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_124_, 0, v___y_122_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
v___x_125_ = 0;
v___x_126_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_126_, 0, v___x_124_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*1, v___x_125_);
v___x_127_ = l_Repr_addAppParen(v___x_126_, v_prec_120_);
return v___x_127_;
}
v___jp_128_:
{
lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_130_ = ((lean_object*)(l_Lean_Cadical_Internal_instReprStatus_repr___closed__3));
lean_inc(v___y_129_);
v___x_131_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_131_, 0, v___y_129_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = 0;
v___x_133_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set_uint8(v___x_133_, sizeof(void*)*1, v___x_132_);
v___x_134_ = l_Repr_addAppParen(v___x_133_, v_prec_120_);
return v___x_134_;
}
v___jp_135_:
{
lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_137_ = ((lean_object*)(l_Lean_Cadical_Internal_instReprStatus_repr___closed__5));
lean_inc(v___y_136_);
v___x_138_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_138_, 0, v___y_136_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = 0;
v___x_140_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_140_, 0, v___x_138_);
lean_ctor_set_uint8(v___x_140_, sizeof(void*)*1, v___x_139_);
v___x_141_ = l_Repr_addAppParen(v___x_140_, v_prec_120_);
return v___x_141_;
}
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_instReprStatus_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_119_ = stack[0].m_num;
lean_object* v_prec_120_ = stack[1].m_obj;
lean_object* v_res_154_;
v_res_154_ = l_Lean_Cadical_Internal_instReprStatus_repr(v_x_119_, v_prec_120_);
stack->m_obj
 = v_res_154_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_instReprStatus_repr___boxed(lean_object* v_x_155_, lean_object* v_prec_156_){
_start:
{
uint8_t v_x_171__boxed_157_; lean_object* v_res_158_; 
v_x_171__boxed_157_ = lean_unbox(v_x_155_);
v_res_158_ = l_Lean_Cadical_Internal_instReprStatus_repr(v_x_171__boxed_157_, v_prec_156_);
lean_dec(v_prec_156_);
return v_res_158_;
}
}
static uint32_t _init_l_Lean_Cadical_Internal_Status_toInt32___closed__0(void){
_start:
{
lean_object* v___x_161_; uint32_t v___x_162_; 
v___x_161_ = lean_unsigned_to_nat(10u);
v___x_162_ = lean_int32_of_nat(v___x_161_);
return v___x_162_;
}
}
static uint32_t _init_l_Lean_Cadical_Internal_Status_toInt32___closed__1(void){
_start:
{
lean_object* v___x_163_; uint32_t v___x_164_; 
v___x_163_ = lean_unsigned_to_nat(20u);
v___x_164_ = lean_int32_of_nat(v___x_163_);
return v___x_164_;
}
}
static uint32_t _init_l_Lean_Cadical_Internal_Status_toInt32___closed__2(void){
_start:
{
lean_object* v___x_165_; uint32_t v___x_166_; 
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = lean_int32_of_nat(v___x_165_);
return v___x_166_;
}
}
uint32_t l_Lean_Cadical_Internal_Status_toInt32(uint8_t v_x_167_){
_start:
{
switch(v_x_167_)
{
case 0:
{
uint32_t v___x_168_; 
v___x_168_ = lean_uint32_once(&l_Lean_Cadical_Internal_Status_toInt32___closed__0, &l_Lean_Cadical_Internal_Status_toInt32___closed__0_once, _init_l_Lean_Cadical_Internal_Status_toInt32___closed__0);
return v___x_168_;
}
case 1:
{
uint32_t v___x_169_; 
v___x_169_ = lean_uint32_once(&l_Lean_Cadical_Internal_Status_toInt32___closed__1, &l_Lean_Cadical_Internal_Status_toInt32___closed__1_once, _init_l_Lean_Cadical_Internal_Status_toInt32___closed__1);
return v___x_169_;
}
default: 
{
uint32_t v___x_170_; 
v___x_170_ = lean_uint32_once(&l_Lean_Cadical_Internal_Status_toInt32___closed__2, &l_Lean_Cadical_Internal_Status_toInt32___closed__2_once, _init_l_Lean_Cadical_Internal_Status_toInt32___closed__2);
return v___x_170_;
}
}
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Status_toInt32_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_167_ = stack[0].m_num;
uint32_t v_res_171_;
v_res_171_ = l_Lean_Cadical_Internal_Status_toInt32(v_x_167_);
stack->m_num = v_res_171_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Status_toInt32___boxed(lean_object* v_x_172_){
_start:
{
uint8_t v_x_52__boxed_173_; uint32_t v_res_174_; lean_object* v_r_175_; 
v_x_52__boxed_173_ = lean_unbox(v_x_172_);
v_res_174_ = l_Lean_Cadical_Internal_Status_toInt32(v_x_52__boxed_173_);
v_r_175_ = lean_box_uint32(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT void l___private_Lean_Cadical_Internal_0__Lean_Cadical_Internal_getSignature_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_176_ = stack[0].m_obj;
lean_object* v_res_177_;
v_res_177_ = lean_cadical_signature(v_u_176_);
stack->m_obj
 = v_res_177_;
}
LEAN_EXPORT lean_object* l___private_Lean_Cadical_Internal_0__Lean_Cadical_Internal_getSignature___boxed(lean_object* v_u_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = lean_cadical_signature(v_u_178_);
return v_res_179_;
}
}
static lean_object* _init_l_Lean_Cadical_Internal_signature___closed__0(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_box(0);
v___x_181_ = lean_cadical_signature(v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_Cadical_Internal_signature(void){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&l_Lean_Cadical_Internal_signature___closed__0, &l_Lean_Cadical_Internal_signature___closed__0_once, _init_l_Lean_Cadical_Internal_signature___closed__0);
return v___x_182_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_184_;
v_res_184_ = lean_cadical_solver_new();
stack->m_obj
 = v_res_184_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_new___boxed(lean_object* v_a_00___x40___internal___hyg_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = lean_cadical_solver_new();
return v_res_186_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_add_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_187_ = stack[0].m_obj;
uint32_t v_lit_188_ = stack[1].m_num;
lean_object* v_res_190_;
v_res_190_ = lean_cadical_solver_add(v_s_187_, v_lit_188_);
stack->m_obj
 = v_res_190_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_add___boxed(lean_object* v_s_191_, lean_object* v_lit_192_, lean_object* v_a_00___x40___internal___hyg_193_){
_start:
{
uint32_t v_lit_boxed_194_; lean_object* v_res_195_; 
v_lit_boxed_194_ = lean_unbox_uint32(v_lit_192_);
lean_dec(v_lit_192_);
v_res_195_ = lean_cadical_solver_add(v_s_191_, v_lit_boxed_194_);
lean_dec(v_s_191_);
return v_res_195_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_clause_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_196_ = stack[0].m_obj;
lean_object* v_lits_197_ = stack[1].m_obj;
lean_object* v_res_199_;
v_res_199_ = lean_cadical_solver_clause(v_s_196_, v_lits_197_);
stack->m_obj
 = v_res_199_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_clause___boxed(lean_object* v_s_200_, lean_object* v_lits_201_, lean_object* v_a_00___x40___internal___hyg_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = lean_cadical_solver_clause(v_s_200_, v_lits_201_);
lean_dec_ref(v_lits_201_);
lean_dec(v_s_200_);
return v_res_203_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_inconsistent_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_204_ = stack[0].m_obj;
uint8_t v_res_206_;
v_res_206_ = lean_cadical_solver_inconsistent(v_s_204_);
stack->m_num = v_res_206_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_inconsistent___boxed(lean_object* v_s_207_, lean_object* v_a_00___x40___internal___hyg_208_){
_start:
{
uint8_t v_res_209_; lean_object* v_r_210_; 
v_res_209_ = lean_cadical_solver_inconsistent(v_s_207_);
lean_dec(v_s_207_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_assume_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_211_ = stack[0].m_obj;
uint32_t v_lit_212_ = stack[1].m_num;
lean_object* v_res_214_;
v_res_214_ = lean_cadical_solver_assume(v_s_211_, v_lit_212_);
stack->m_obj
 = v_res_214_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_assume___boxed(lean_object* v_s_215_, lean_object* v_lit_216_, lean_object* v_a_00___x40___internal___hyg_217_){
_start:
{
uint32_t v_lit_boxed_218_; lean_object* v_res_219_; 
v_lit_boxed_218_ = lean_unbox_uint32(v_lit_216_);
lean_dec(v_lit_216_);
v_res_219_ = lean_cadical_solver_assume(v_s_215_, v_lit_boxed_218_);
lean_dec(v_s_215_);
return v_res_219_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_solve_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_220_ = stack[0].m_obj;
uint8_t v_res_222_;
v_res_222_ = lean_cadical_solver_solve(v_s_220_);
stack->m_num = v_res_222_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_solve___boxed(lean_object* v_s_223_, lean_object* v_a_00___x40___internal___hyg_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = lean_cadical_solver_solve(v_s_223_);
lean_dec(v_s_223_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_val_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_227_ = stack[0].m_obj;
uint32_t v_lit_228_ = stack[1].m_num;
uint32_t v_res_230_;
v_res_230_ = lean_cadical_solver_val(v_s_227_, v_lit_228_);
stack->m_num = v_res_230_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_val___boxed(lean_object* v_s_231_, lean_object* v_lit_232_, lean_object* v_a_00___x40___internal___hyg_233_){
_start:
{
uint32_t v_lit_boxed_234_; uint32_t v_res_235_; lean_object* v_r_236_; 
v_lit_boxed_234_ = lean_unbox_uint32(v_lit_232_);
lean_dec(v_lit_232_);
v_res_235_ = lean_cadical_solver_val(v_s_231_, v_lit_boxed_234_);
lean_dec(v_s_231_);
v_r_236_ = lean_box_uint32(v_res_235_);
return v_r_236_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_flip_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_237_ = stack[0].m_obj;
uint32_t v_lit_238_ = stack[1].m_num;
uint8_t v_res_240_;
v_res_240_ = lean_cadical_solver_flip(v_s_237_, v_lit_238_);
stack->m_num = v_res_240_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_flip___boxed(lean_object* v_s_241_, lean_object* v_lit_242_, lean_object* v_a_00___x40___internal___hyg_243_){
_start:
{
uint32_t v_lit_boxed_244_; uint8_t v_res_245_; lean_object* v_r_246_; 
v_lit_boxed_244_ = lean_unbox_uint32(v_lit_242_);
lean_dec(v_lit_242_);
v_res_245_ = lean_cadical_solver_flip(v_s_241_, v_lit_boxed_244_);
lean_dec(v_s_241_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_flippable_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_247_ = stack[0].m_obj;
uint32_t v_lit_248_ = stack[1].m_num;
uint8_t v_res_250_;
v_res_250_ = lean_cadical_solver_flippable(v_s_247_, v_lit_248_);
stack->m_num = v_res_250_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_flippable___boxed(lean_object* v_s_251_, lean_object* v_lit_252_, lean_object* v_a_00___x40___internal___hyg_253_){
_start:
{
uint32_t v_lit_boxed_254_; uint8_t v_res_255_; lean_object* v_r_256_; 
v_lit_boxed_254_ = lean_unbox_uint32(v_lit_252_);
lean_dec(v_lit_252_);
v_res_255_ = lean_cadical_solver_flippable(v_s_251_, v_lit_boxed_254_);
lean_dec(v_s_251_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_failed_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_257_ = stack[0].m_obj;
uint32_t v_lit_258_ = stack[1].m_num;
uint8_t v_res_260_;
v_res_260_ = lean_cadical_solver_failed(v_s_257_, v_lit_258_);
stack->m_num = v_res_260_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_failed___boxed(lean_object* v_s_261_, lean_object* v_lit_262_, lean_object* v_a_00___x40___internal___hyg_263_){
_start:
{
uint32_t v_lit_boxed_264_; uint8_t v_res_265_; lean_object* v_r_266_; 
v_lit_boxed_264_ = lean_unbox_uint32(v_lit_262_);
lean_dec(v_lit_262_);
v_res_265_ = lean_cadical_solver_failed(v_s_261_, v_lit_boxed_264_);
lean_dec(v_s_261_);
v_r_266_ = lean_box(v_res_265_);
return v_r_266_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_constrain_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_267_ = stack[0].m_obj;
uint32_t v_lit_268_ = stack[1].m_num;
lean_object* v_res_270_;
v_res_270_ = lean_cadical_solver_constrain(v_s_267_, v_lit_268_);
stack->m_obj
 = v_res_270_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_constrain___boxed(lean_object* v_s_271_, lean_object* v_lit_272_, lean_object* v_a_00___x40___internal___hyg_273_){
_start:
{
uint32_t v_lit_boxed_274_; lean_object* v_res_275_; 
v_lit_boxed_274_ = lean_unbox_uint32(v_lit_272_);
lean_dec(v_lit_272_);
v_res_275_ = lean_cadical_solver_constrain(v_s_271_, v_lit_boxed_274_);
lean_dec(v_s_271_);
return v_res_275_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_constraintFailed_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_276_ = stack[0].m_obj;
uint8_t v_res_278_;
v_res_278_ = lean_cadical_solver_constraint_failed(v_s_276_);
stack->m_num = v_res_278_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_constraintFailed___boxed(lean_object* v_s_279_, lean_object* v_a_00___x40___internal___hyg_280_){
_start:
{
uint8_t v_res_281_; lean_object* v_r_282_; 
v_res_281_ = lean_cadical_solver_constraint_failed(v_s_279_);
lean_dec(v_s_279_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_lookahead_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_283_ = stack[0].m_obj;
uint32_t v_res_285_;
v_res_285_ = lean_cadical_solver_lookahead(v_s_283_);
stack->m_num = v_res_285_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_lookahead___boxed(lean_object* v_s_286_, lean_object* v_a_00___x40___internal___hyg_287_){
_start:
{
uint32_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = lean_cadical_solver_lookahead(v_s_286_);
lean_dec(v_s_286_);
v_r_289_ = lean_box_uint32(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_resetAssumptions_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_290_ = stack[0].m_obj;
lean_object* v_res_292_;
v_res_292_ = lean_cadical_solver_reset_assumptions(v_s_290_);
stack->m_obj
 = v_res_292_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_resetAssumptions___boxed(lean_object* v_s_293_, lean_object* v_a_00___x40___internal___hyg_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = lean_cadical_solver_reset_assumptions(v_s_293_);
lean_dec(v_s_293_);
return v_res_295_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_resetConstraint_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_296_ = stack[0].m_obj;
lean_object* v_res_298_;
v_res_298_ = lean_cadical_solver_reset_constraint(v_s_296_);
stack->m_obj
 = v_res_298_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_resetConstraint___boxed(lean_object* v_s_299_, lean_object* v_a_00___x40___internal___hyg_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = lean_cadical_solver_reset_constraint(v_s_299_);
lean_dec(v_s_299_);
return v_res_301_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_status_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_302_ = stack[0].m_obj;
uint8_t v_res_304_;
v_res_304_ = lean_cadical_solver_status(v_s_302_);
stack->m_num = v_res_304_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_status___boxed(lean_object* v_s_305_, lean_object* v_a_00___x40___internal___hyg_306_){
_start:
{
uint8_t v_res_307_; lean_object* v_r_308_; 
v_res_307_ = lean_cadical_solver_status(v_s_305_);
lean_dec(v_s_305_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_vars_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_309_ = stack[0].m_obj;
uint32_t v_res_311_;
v_res_311_ = lean_cadical_solver_vars(v_s_309_);
stack->m_num = v_res_311_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_vars___boxed(lean_object* v_s_312_, lean_object* v_a_00___x40___internal___hyg_313_){
_start:
{
uint32_t v_res_314_; lean_object* v_r_315_; 
v_res_314_ = lean_cadical_solver_vars(v_s_312_);
lean_dec(v_s_312_);
v_r_315_ = lean_box_uint32(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_resize_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_316_ = stack[0].m_obj;
uint32_t v_minMaxVar_317_ = stack[1].m_num;
lean_object* v_res_319_;
v_res_319_ = lean_cadical_solver_resize(v_s_316_, v_minMaxVar_317_);
stack->m_obj
 = v_res_319_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_resize___boxed(lean_object* v_s_320_, lean_object* v_minMaxVar_321_, lean_object* v_a_00___x40___internal___hyg_322_){
_start:
{
uint32_t v_minMaxVar_boxed_323_; lean_object* v_res_324_; 
v_minMaxVar_boxed_323_ = lean_unbox_uint32(v_minMaxVar_321_);
lean_dec(v_minMaxVar_321_);
v_res_324_ = lean_cadical_solver_resize(v_s_320_, v_minMaxVar_boxed_323_);
lean_dec(v_s_320_);
return v_res_324_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_isValidOption_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_325_ = stack[0].m_obj;
uint8_t v_res_326_;
v_res_326_ = lean_cadical_solver_is_valid_option(v_opt_325_);
stack->m_num = v_res_326_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isValidOption___boxed(lean_object* v_opt_327_){
_start:
{
uint8_t v_res_328_; lean_object* v_r_329_; 
v_res_328_ = lean_cadical_solver_is_valid_option(v_opt_327_);
lean_dec_ref(v_opt_327_);
v_r_329_ = lean_box(v_res_328_);
return v_r_329_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_isPreprocessingOption_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_330_ = stack[0].m_obj;
uint8_t v_res_331_;
v_res_331_ = lean_cadical_solver_is_preprocessing_option(v_opt_330_);
stack->m_num = v_res_331_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isPreprocessingOption___boxed(lean_object* v_opt_332_){
_start:
{
uint8_t v_res_333_; lean_object* v_r_334_; 
v_res_333_ = lean_cadical_solver_is_preprocessing_option(v_opt_332_);
lean_dec_ref(v_opt_332_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_isValidLongOption_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_335_ = stack[0].m_obj;
uint8_t v_res_336_;
v_res_336_ = lean_cadical_solver_is_valid_long_option(v_opt_335_);
stack->m_num = v_res_336_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isValidLongOption___boxed(lean_object* v_opt_337_){
_start:
{
uint8_t v_res_338_; lean_object* v_r_339_; 
v_res_338_ = lean_cadical_solver_is_valid_long_option(v_opt_337_);
lean_dec_ref(v_opt_337_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_get_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_340_ = stack[0].m_obj;
lean_object* v_opt_341_ = stack[1].m_obj;
uint32_t v_res_343_;
v_res_343_ = lean_cadical_solver_get(v_s_340_, v_opt_341_);
stack->m_num = v_res_343_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_get___boxed(lean_object* v_s_344_, lean_object* v_opt_345_, lean_object* v_a_00___x40___internal___hyg_346_){
_start:
{
uint32_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = lean_cadical_solver_get(v_s_344_, v_opt_345_);
lean_dec_ref(v_opt_345_);
lean_dec(v_s_344_);
v_r_348_ = lean_box_uint32(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_set_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_349_ = stack[0].m_obj;
lean_object* v_opt_350_ = stack[1].m_obj;
uint32_t v_val_351_ = stack[2].m_num;
uint8_t v_res_353_;
v_res_353_ = lean_cadical_solver_set(v_s_349_, v_opt_350_, v_val_351_);
stack->m_num = v_res_353_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_set___boxed(lean_object* v_s_354_, lean_object* v_opt_355_, lean_object* v_val_356_, lean_object* v_a_00___x40___internal___hyg_357_){
_start:
{
uint32_t v_val_boxed_358_; uint8_t v_res_359_; lean_object* v_r_360_; 
v_val_boxed_358_ = lean_unbox_uint32(v_val_356_);
lean_dec(v_val_356_);
v_res_359_ = lean_cadical_solver_set(v_s_354_, v_opt_355_, v_val_boxed_358_);
lean_dec_ref(v_opt_355_);
lean_dec(v_s_354_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_setLongOption_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_361_ = stack[0].m_obj;
lean_object* v_opt_362_ = stack[1].m_obj;
uint8_t v_res_364_;
v_res_364_ = lean_cadical_solver_set_long_option(v_s_361_, v_opt_362_);
stack->m_num = v_res_364_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_setLongOption___boxed(lean_object* v_s_365_, lean_object* v_opt_366_, lean_object* v_a_00___x40___internal___hyg_367_){
_start:
{
uint8_t v_res_368_; lean_object* v_r_369_; 
v_res_368_ = lean_cadical_solver_set_long_option(v_s_365_, v_opt_366_);
lean_dec_ref(v_opt_366_);
lean_dec(v_s_365_);
v_r_369_ = lean_box(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_isValidConfiguration_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_370_ = stack[0].m_obj;
uint8_t v_res_371_;
v_res_371_ = lean_cadical_solver_is_valid_configuration(v_opt_370_);
stack->m_num = v_res_371_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isValidConfiguration___boxed(lean_object* v_opt_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = lean_cadical_solver_is_valid_configuration(v_opt_372_);
lean_dec_ref(v_opt_372_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_configure_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_375_ = stack[0].m_obj;
lean_object* v_opt_376_ = stack[1].m_obj;
uint8_t v_res_378_;
v_res_378_ = lean_cadical_solver_configure(v_s_375_, v_opt_376_);
stack->m_num = v_res_378_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_configure___boxed(lean_object* v_s_379_, lean_object* v_opt_380_, lean_object* v_a_00___x40___internal___hyg_381_){
_start:
{
uint8_t v_res_382_; lean_object* v_r_383_; 
v_res_382_ = lean_cadical_solver_configure(v_s_379_, v_opt_380_);
lean_dec_ref(v_opt_380_);
lean_dec(v_s_379_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_optimize_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_384_ = stack[0].m_obj;
uint32_t v_val_385_ = stack[1].m_num;
lean_object* v_res_387_;
v_res_387_ = lean_cadical_solver_optimize(v_s_384_, v_val_385_);
stack->m_obj
 = v_res_387_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_optimize___boxed(lean_object* v_s_388_, lean_object* v_val_389_, lean_object* v_a_00___x40___internal___hyg_390_){
_start:
{
uint32_t v_val_boxed_391_; lean_object* v_res_392_; 
v_val_boxed_391_ = lean_unbox_uint32(v_val_389_);
lean_dec(v_val_389_);
v_res_392_ = lean_cadical_solver_optimize(v_s_388_, v_val_boxed_391_);
lean_dec(v_s_388_);
return v_res_392_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_limit_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_393_ = stack[0].m_obj;
lean_object* v_limit_394_ = stack[1].m_obj;
uint32_t v_val_395_ = stack[2].m_num;
uint8_t v_res_397_;
v_res_397_ = lean_cadical_solver_limit(v_s_393_, v_limit_394_, v_val_395_);
stack->m_num = v_res_397_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_limit___boxed(lean_object* v_s_398_, lean_object* v_limit_399_, lean_object* v_val_400_, lean_object* v_a_00___x40___internal___hyg_401_){
_start:
{
uint32_t v_val_boxed_402_; uint8_t v_res_403_; lean_object* v_r_404_; 
v_val_boxed_402_ = lean_unbox_uint32(v_val_400_);
lean_dec(v_val_400_);
v_res_403_ = lean_cadical_solver_limit(v_s_398_, v_limit_399_, v_val_boxed_402_);
lean_dec_ref(v_limit_399_);
lean_dec(v_s_398_);
v_r_404_ = lean_box(v_res_403_);
return v_r_404_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_isValidLimit_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_405_ = stack[0].m_obj;
lean_object* v_limit_406_ = stack[1].m_obj;
uint8_t v_res_408_;
v_res_408_ = lean_cadical_solver_is_valid_limit(v_s_405_, v_limit_406_);
stack->m_num = v_res_408_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_isValidLimit___boxed(lean_object* v_s_409_, lean_object* v_limit_410_, lean_object* v_a_00___x40___internal___hyg_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = lean_cadical_solver_is_valid_limit(v_s_409_, v_limit_410_);
lean_dec_ref(v_limit_410_);
lean_dec(v_s_409_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_active_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_414_ = stack[0].m_obj;
uint32_t v_res_416_;
v_res_416_ = lean_cadical_solver_active(v_s_414_);
stack->m_num = v_res_416_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_active___boxed(lean_object* v_s_417_, lean_object* v_a_00___x40___internal___hyg_418_){
_start:
{
uint32_t v_res_419_; lean_object* v_r_420_; 
v_res_419_ = lean_cadical_solver_active(v_s_417_);
lean_dec(v_s_417_);
v_r_420_ = lean_box_uint32(v_res_419_);
return v_r_420_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_redundant_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_421_ = stack[0].m_obj;
uint64_t v_res_423_;
v_res_423_ = lean_cadical_solver_redundant(v_s_421_);
stack->m_num = v_res_423_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_redundant___boxed(lean_object* v_s_424_, lean_object* v_a_00___x40___internal___hyg_425_){
_start:
{
uint64_t v_res_426_; lean_object* v_r_427_; 
v_res_426_ = lean_cadical_solver_redundant(v_s_424_);
lean_dec(v_s_424_);
v_r_427_ = lean_box_uint64(v_res_426_);
return v_r_427_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_irredundant_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_428_ = stack[0].m_obj;
uint64_t v_res_430_;
v_res_430_ = lean_cadical_solver_irredundant(v_s_428_);
stack->m_num = v_res_430_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_irredundant___boxed(lean_object* v_s_431_, lean_object* v_a_00___x40___internal___hyg_432_){
_start:
{
uint64_t v_res_433_; lean_object* v_r_434_; 
v_res_433_ = lean_cadical_solver_irredundant(v_s_431_);
lean_dec(v_s_431_);
v_r_434_ = lean_box_uint64(v_res_433_);
return v_r_434_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_simplify_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_435_ = stack[0].m_obj;
uint32_t v_rounds_436_ = stack[1].m_num;
uint8_t v_res_438_;
v_res_438_ = lean_cadical_solver_simplify(v_s_435_, v_rounds_436_);
stack->m_num = v_res_438_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_simplify___boxed(lean_object* v_s_439_, lean_object* v_rounds_440_, lean_object* v_a_00___x40___internal___hyg_441_){
_start:
{
uint32_t v_rounds_boxed_442_; uint8_t v_res_443_; lean_object* v_r_444_; 
v_rounds_boxed_442_ = lean_unbox_uint32(v_rounds_440_);
lean_dec(v_rounds_440_);
v_res_443_ = lean_cadical_solver_simplify(v_s_439_, v_rounds_boxed_442_);
lean_dec(v_s_439_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_terminate_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_445_ = stack[0].m_obj;
lean_object* v_res_447_;
v_res_447_ = lean_cadical_solver_terminate(v_s_445_);
stack->m_obj
 = v_res_447_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_terminate___boxed(lean_object* v_s_448_, lean_object* v_a_00___x40___internal___hyg_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = lean_cadical_solver_terminate(v_s_448_);
lean_dec(v_s_448_);
return v_res_450_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_frozen_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_451_ = stack[0].m_obj;
uint32_t v_lit_452_ = stack[1].m_num;
uint8_t v_res_454_;
v_res_454_ = lean_cadical_solver_frozen(v_s_451_, v_lit_452_);
stack->m_num = v_res_454_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_frozen___boxed(lean_object* v_s_455_, lean_object* v_lit_456_, lean_object* v_a_00___x40___internal___hyg_457_){
_start:
{
uint32_t v_lit_boxed_458_; uint8_t v_res_459_; lean_object* v_r_460_; 
v_lit_boxed_458_ = lean_unbox_uint32(v_lit_456_);
lean_dec(v_lit_456_);
v_res_459_ = lean_cadical_solver_frozen(v_s_455_, v_lit_boxed_458_);
lean_dec(v_s_455_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_freeze_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_461_ = stack[0].m_obj;
uint32_t v_lit_462_ = stack[1].m_num;
lean_object* v_res_464_;
v_res_464_ = lean_cadical_solver_freeze(v_s_461_, v_lit_462_);
stack->m_obj
 = v_res_464_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_freeze___boxed(lean_object* v_s_465_, lean_object* v_lit_466_, lean_object* v_a_00___x40___internal___hyg_467_){
_start:
{
uint32_t v_lit_boxed_468_; lean_object* v_res_469_; 
v_lit_boxed_468_ = lean_unbox_uint32(v_lit_466_);
lean_dec(v_lit_466_);
v_res_469_ = lean_cadical_solver_freeze(v_s_465_, v_lit_boxed_468_);
lean_dec(v_s_465_);
return v_res_469_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_melt_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_470_ = stack[0].m_obj;
uint32_t v_lit_471_ = stack[1].m_num;
lean_object* v_res_473_;
v_res_473_ = lean_cadical_solver_melt(v_s_470_, v_lit_471_);
stack->m_obj
 = v_res_473_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_melt___boxed(lean_object* v_s_474_, lean_object* v_lit_475_, lean_object* v_a_00___x40___internal___hyg_476_){
_start:
{
uint32_t v_lit_boxed_477_; lean_object* v_res_478_; 
v_lit_boxed_477_ = lean_unbox_uint32(v_lit_475_);
lean_dec(v_lit_475_);
v_res_478_ = lean_cadical_solver_melt(v_s_474_, v_lit_boxed_477_);
lean_dec(v_s_474_);
return v_res_478_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_fixed_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_479_ = stack[0].m_obj;
uint32_t v_lit_480_ = stack[1].m_num;
uint32_t v_res_482_;
v_res_482_ = lean_cadical_solver_fixed(v_s_479_, v_lit_480_);
stack->m_num = v_res_482_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_fixed___boxed(lean_object* v_s_483_, lean_object* v_lit_484_, lean_object* v_a_00___x40___internal___hyg_485_){
_start:
{
uint32_t v_lit_boxed_486_; uint32_t v_res_487_; lean_object* v_r_488_; 
v_lit_boxed_486_ = lean_unbox_uint32(v_lit_484_);
lean_dec(v_lit_484_);
v_res_487_ = lean_cadical_solver_fixed(v_s_483_, v_lit_boxed_486_);
lean_dec(v_s_483_);
v_r_488_ = lean_box_uint32(v_res_487_);
return v_r_488_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_phase_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_489_ = stack[0].m_obj;
uint32_t v_lit_490_ = stack[1].m_num;
lean_object* v_res_492_;
v_res_492_ = lean_cadical_solver_phase(v_s_489_, v_lit_490_);
stack->m_obj
 = v_res_492_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_phase___boxed(lean_object* v_s_493_, lean_object* v_lit_494_, lean_object* v_a_00___x40___internal___hyg_495_){
_start:
{
uint32_t v_lit_boxed_496_; lean_object* v_res_497_; 
v_lit_boxed_496_ = lean_unbox_uint32(v_lit_494_);
lean_dec(v_lit_494_);
v_res_497_ = lean_cadical_solver_phase(v_s_493_, v_lit_boxed_496_);
lean_dec(v_s_493_);
return v_res_497_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_unphase_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_498_ = stack[0].m_obj;
uint32_t v_lit_499_ = stack[1].m_num;
lean_object* v_res_501_;
v_res_501_ = lean_cadical_solver_unphase(v_s_498_, v_lit_499_);
stack->m_obj
 = v_res_501_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_unphase___boxed(lean_object* v_s_502_, lean_object* v_lit_503_, lean_object* v_a_00___x40___internal___hyg_504_){
_start:
{
uint32_t v_lit_boxed_505_; lean_object* v_res_506_; 
v_lit_boxed_505_ = lean_unbox_uint32(v_lit_503_);
lean_dec(v_lit_503_);
v_res_506_ = lean_cadical_solver_unphase(v_s_502_, v_lit_boxed_505_);
lean_dec(v_s_502_);
return v_res_506_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_conclude_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_507_ = stack[0].m_obj;
lean_object* v_res_509_;
v_res_509_ = lean_cadical_solver_conclude(v_s_507_);
stack->m_obj
 = v_res_509_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_conclude___boxed(lean_object* v_s_510_, lean_object* v_a_00___x40___internal___hyg_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = lean_cadical_solver_conclude(v_s_510_);
lean_dec(v_s_510_);
return v_res_512_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_usage_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_514_;
v_res_514_ = lean_cadical_solver_usage();
stack->m_obj
 = v_res_514_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_usage___boxed(lean_object* v_a_00___x40___internal___hyg_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = lean_cadical_solver_usage();
return v_res_516_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_configurations_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_518_;
v_res_518_ = lean_cadical_solver_configurations();
stack->m_obj
 = v_res_518_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_configurations___boxed(lean_object* v_a_00___x40___internal___hyg_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = lean_cadical_solver_configurations();
return v_res_520_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_statistics_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_521_ = stack[0].m_obj;
lean_object* v_res_523_;
v_res_523_ = lean_cadical_solver_statistics(v_s_521_);
stack->m_obj
 = v_res_523_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_statistics___boxed(lean_object* v_s_524_, lean_object* v_a_00___x40___internal___hyg_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = lean_cadical_solver_statistics(v_s_524_);
lean_dec(v_s_524_);
return v_res_526_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_resources_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_527_ = stack[0].m_obj;
lean_object* v_res_529_;
v_res_529_ = lean_cadical_solver_resources(v_s_527_);
stack->m_obj
 = v_res_529_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_resources___boxed(lean_object* v_s_530_, lean_object* v_a_00___x40___internal___hyg_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = lean_cadical_solver_resources(v_s_530_);
lean_dec(v_s_530_);
return v_res_532_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Internal_Solver_state_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_533_ = stack[0].m_obj;
uint16_t v_res_535_;
v_res_535_ = lean_cadical_solver_state(v_s_533_);
stack->m_num = v_res_535_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Internal_Solver_state___boxed(lean_object* v_s_536_, lean_object* v_a_00___x40___internal___hyg_537_){
_start:
{
uint16_t v_res_538_; lean_object* v_r_539_; 
v_res_538_ = lean_cadical_solver_state(v_s_536_);
lean_dec(v_s_536_);
v_r_539_ = lean_box(v_res_538_);
return v_r_539_;
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
