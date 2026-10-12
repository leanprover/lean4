// Lean compiler output
// Module: Lean.Cadical.Basic
// Imports: import Lean.Cadical.Internal public import Std.Sat.CNF.Basic public import Init.Data.SInt.Basic public import Init.System.IO
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
lean_object* lean_int32_to_int(uint32_t);
lean_object* l_Int_toNat(lean_object*);
uint8_t lean_cadical_solver_is_valid_option(lean_object*);
uint16_t lean_cadical_solver_state(lean_object*);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint32_t lean_cadical_solver_val(lean_object*, uint32_t);
uint8_t lean_int32_dec_eq(uint32_t, uint32_t);
extern lean_object* l_instMonadBaseIO;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
uint16_t lean_uint16_of_nat_mk(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_cadical_solver_new();
uint8_t lean_cadical_solver_is_preprocessing_option(lean_object*);
lean_object* lean_cadical_solver_configurations();
lean_object* lean_cadical_solver_assume(lean_object*, uint32_t);
uint32_t lean_int32_neg(uint32_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_cadical_solver_resources(lean_object*);
uint8_t lean_cadical_solver_is_valid_configuration(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_cadical_solver_inconsistent(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_cadical_solver_add(lean_object*, uint32_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_byte_array_uget(lean_object*, size_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint64_t lean_uint16_to_uint64(uint16_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t lean_cadical_solver_status(lean_object*);
uint8_t lean_cadical_solver_set_long_option(lean_object*, lean_object*);
uint8_t lean_cadical_solver_set(lean_object*, lean_object*, uint32_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_cadical_solver_get(lean_object*, lean_object*);
lean_object* lean_cadical_solver_terminate(lean_object*);
uint8_t lean_cadical_solver_configure(lean_object*, lean_object*);
lean_object* lean_cadical_solver_statistics(lean_object*);
uint8_t lean_cadical_solver_is_valid_long_option(lean_object*);
uint8_t lean_cadical_solver_solve(lean_object*);
lean_object* lean_cadical_solver_reset_assumptions(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Cadical_instInhabitedState_default;
LEAN_EXPORT uint16_t l_Lean_Cadical_instInhabitedState;
LEAN_EXPORT uint8_t l_Lean_Cadical_instDecidableEqState_decEq(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_instDecidableEqState_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Cadical_instDecidableEqState(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_instDecidableEqState___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Cadical_instHashableState_hash(uint16_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_instHashableState_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Cadical_instHashableState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Cadical_instHashableState_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Cadical_instHashableState___closed__0 = (const lean_object*)&l_Lean_Cadical_instHashableState___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Cadical_instHashableState = (const lean_object*)&l_Lean_Cadical_instHashableState___closed__0_value;
LEAN_EXPORT uint16_t l_Lean_Cadical_State_initializing;
LEAN_EXPORT uint16_t l_Lean_Cadical_State_configuring;
LEAN_EXPORT uint16_t l_Lean_Cadical_State_steady;
LEAN_EXPORT uint16_t l_Lean_Cadical_State_adding;
LEAN_EXPORT uint16_t l_Lean_Cadical_State_solving;
LEAN_EXPORT uint16_t l_Lean_Cadical_State_satisfied;
LEAN_EXPORT uint16_t l_Lean_Cadical_State_unsatisfied;
LEAN_EXPORT uint16_t l_Lean_Cadical_State_deleting;
LEAN_EXPORT uint16_t l_Lean_Cadical_State_inconclusive;
LEAN_EXPORT uint16_t l___private_Lean_Cadical_Basic_0__Lean_Cadical_State_ready;
LEAN_EXPORT uint16_t l___private_Lean_Cadical_Basic_0__Lean_Cadical_State_valid;
LEAN_EXPORT uint16_t l___private_Lean_Cadical_Basic_0__Lean_Cadical_State_invalid;
static lean_once_cell_t l_Lean_Cadical_State_isReady___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Cadical_State_isReady___closed__0;
static lean_once_cell_t l_Lean_Cadical_State_isReady___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Lean_Cadical_State_isReady___closed__1;
LEAN_EXPORT uint8_t l_Lean_Cadical_State_isReady(uint16_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_State_isReady___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Cadical_State_isValid(uint16_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_State_isValid___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Cadical_State_isInvalid(uint16_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_State_isInvalid___boxed(lean_object*);
static const lean_string_object l_Lean_Cadical_State_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "INVALID_STATE"};
static const lean_object* l_Lean_Cadical_State_toString___closed__0 = (const lean_object*)&l_Lean_Cadical_State_toString___closed__0_value;
static const lean_string_object l_Lean_Cadical_State_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "INCONCLUSIVE"};
static const lean_object* l_Lean_Cadical_State_toString___closed__1 = (const lean_object*)&l_Lean_Cadical_State_toString___closed__1_value;
static const lean_string_object l_Lean_Cadical_State_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "UNSATISFIED"};
static const lean_object* l_Lean_Cadical_State_toString___closed__2 = (const lean_object*)&l_Lean_Cadical_State_toString___closed__2_value;
static const lean_string_object l_Lean_Cadical_State_toString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "SATISFIED"};
static const lean_object* l_Lean_Cadical_State_toString___closed__3 = (const lean_object*)&l_Lean_Cadical_State_toString___closed__3_value;
static const lean_string_object l_Lean_Cadical_State_toString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "SOLVING"};
static const lean_object* l_Lean_Cadical_State_toString___closed__4 = (const lean_object*)&l_Lean_Cadical_State_toString___closed__4_value;
static const lean_string_object l_Lean_Cadical_State_toString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ADDING"};
static const lean_object* l_Lean_Cadical_State_toString___closed__5 = (const lean_object*)&l_Lean_Cadical_State_toString___closed__5_value;
static const lean_string_object l_Lean_Cadical_State_toString___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "STEADY"};
static const lean_object* l_Lean_Cadical_State_toString___closed__6 = (const lean_object*)&l_Lean_Cadical_State_toString___closed__6_value;
static const lean_string_object l_Lean_Cadical_State_toString___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "CONFIGURING"};
static const lean_object* l_Lean_Cadical_State_toString___closed__7 = (const lean_object*)&l_Lean_Cadical_State_toString___closed__7_value;
static const lean_string_object l_Lean_Cadical_State_toString___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "INITIALIZING"};
static const lean_object* l_Lean_Cadical_State_toString___closed__8 = (const lean_object*)&l_Lean_Cadical_State_toString___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Cadical_State_toString(uint16_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_State_toString___boxed(lean_object*);
static const lean_closure_object l_Lean_Cadical_State_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Cadical_State_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Cadical_State_instToString___closed__0 = (const lean_object*)&l_Lean_Cadical_State_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Cadical_State_instToString = (const lean_object*)&l_Lean_Cadical_State_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_satisfiable_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_satisfiable_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_satisfiable_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_satisfiable_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unsatisfiable_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unsatisfiable_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unsatisfiable_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unsatisfiable_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unknown_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unknown_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unknown_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unknown_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Cadical_instInhabitedStatus_default;
LEAN_EXPORT uint8_t l_Lean_Cadical_instInhabitedStatus;
LEAN_EXPORT uint8_t l_Lean_Cadical_Status_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Cadical_instDecidableEqStatus(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_instDecidableEqStatus___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Cadical_instHashableStatus_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_instHashableStatus_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Cadical_instHashableStatus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Cadical_instHashableStatus_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Cadical_instHashableStatus___closed__0 = (const lean_object*)&l_Lean_Cadical_instHashableStatus___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Cadical_instHashableStatus = (const lean_object*)&l_Lean_Cadical_instHashableStatus___closed__0_value;
static const lean_string_object l_Lean_Cadical_instReprStatus_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Cadical.Status.satisfiable"};
static const lean_object* l_Lean_Cadical_instReprStatus_repr___closed__0 = (const lean_object*)&l_Lean_Cadical_instReprStatus_repr___closed__0_value;
static const lean_ctor_object l_Lean_Cadical_instReprStatus_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Cadical_instReprStatus_repr___closed__0_value)}};
static const lean_object* l_Lean_Cadical_instReprStatus_repr___closed__1 = (const lean_object*)&l_Lean_Cadical_instReprStatus_repr___closed__1_value;
static const lean_string_object l_Lean_Cadical_instReprStatus_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Cadical.Status.unsatisfiable"};
static const lean_object* l_Lean_Cadical_instReprStatus_repr___closed__2 = (const lean_object*)&l_Lean_Cadical_instReprStatus_repr___closed__2_value;
static const lean_ctor_object l_Lean_Cadical_instReprStatus_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Cadical_instReprStatus_repr___closed__2_value)}};
static const lean_object* l_Lean_Cadical_instReprStatus_repr___closed__3 = (const lean_object*)&l_Lean_Cadical_instReprStatus_repr___closed__3_value;
static const lean_string_object l_Lean_Cadical_instReprStatus_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Cadical.Status.unknown"};
static const lean_object* l_Lean_Cadical_instReprStatus_repr___closed__4 = (const lean_object*)&l_Lean_Cadical_instReprStatus_repr___closed__4_value;
static const lean_ctor_object l_Lean_Cadical_instReprStatus_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Cadical_instReprStatus_repr___closed__4_value)}};
static const lean_object* l_Lean_Cadical_instReprStatus_repr___closed__5 = (const lean_object*)&l_Lean_Cadical_instReprStatus_repr___closed__5_value;
static lean_once_cell_t l_Lean_Cadical_instReprStatus_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Cadical_instReprStatus_repr___closed__6;
static lean_once_cell_t l_Lean_Cadical_instReprStatus_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Cadical_instReprStatus_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Cadical_instReprStatus_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_instReprStatus_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Cadical_instReprStatus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Cadical_instReprStatus_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Cadical_instReprStatus___closed__0 = (const lean_object*)&l_Lean_Cadical_instReprStatus___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Cadical_instReprStatus = (const lean_object*)&l_Lean_Cadical_instReprStatus___closed__0_value;
static lean_once_cell_t l_Lean_Cadical_Status_toInt32___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Lean_Cadical_Status_toInt32___closed__0;
static lean_once_cell_t l_Lean_Cadical_Status_toInt32___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Lean_Cadical_Status_toInt32___closed__1;
static lean_once_cell_t l_Lean_Cadical_Status_toInt32___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Lean_Cadical_Status_toInt32___closed__2;
LEAN_EXPORT uint32_t l_Lean_Cadical_Status_toInt32(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_toInt32___boxed(lean_object*);
static const lean_string_object l_Lean_Cadical_Status_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "SAT"};
static const lean_object* l_Lean_Cadical_Status_toString___closed__0 = (const lean_object*)&l_Lean_Cadical_Status_toString___closed__0_value;
static const lean_string_object l_Lean_Cadical_Status_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UNSAT"};
static const lean_object* l_Lean_Cadical_Status_toString___closed__1 = (const lean_object*)&l_Lean_Cadical_Status_toString___closed__1_value;
static const lean_string_object l_Lean_Cadical_Status_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "UNKNOWN"};
static const lean_object* l_Lean_Cadical_Status_toString___closed__2 = (const lean_object*)&l_Lean_Cadical_Status_toString___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_toString(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_toString___boxed(lean_object*);
static const lean_closure_object l_Lean_Cadical_Status_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Cadical_Status_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Cadical_Status_instToString___closed__0 = (const lean_object*)&l_Lean_Cadical_Status_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Cadical_Status_instToString = (const lean_object*)&l_Lean_Cadical_Status_instToString___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lean_Cadical_Basic_0__Lean_Cadical_Status_ofInternal(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Cadical_Basic_0__Lean_Cadical_Status_ofInternal___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__0;
static lean_once_cell_t l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__1;
static lean_once_cell_t l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2;
static const lean_string_object l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Literal {lit} too large for SAT API"};
static const lean_object* l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__3 = (const lean_object*)&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__3_value;
static const lean_ctor_object l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__3_value)}};
static const lean_object* l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__4 = (const lean_object*)&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_new();
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_new___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Lean_Cadical_Solver_state(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_state___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Cadical_Solver_clause_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Cadical_Solver_clause_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_clause_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_clause_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Lean_Cadical_Solver_clause_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Lean_Cadical_Solver_clause_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Cadical_Solver_clause___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Cadical.Basic"};
static const lean_object* l_Lean_Cadical_Solver_clause___closed__0 = (const lean_object*)&l_Lean_Cadical_Solver_clause___closed__0_value;
static const lean_string_object l_Lean_Cadical_Solver_clause___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Cadical.Solver.clause"};
static const lean_object* l_Lean_Cadical_Solver_clause___closed__1 = (const lean_object*)&l_Lean_Cadical_Solver_clause___closed__1_value;
static const lean_string_object l_Lean_Cadical_Solver_clause___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "assertion violation: ( __do_lift._@.Lean.Cadical.Basic.3562234251._hygCtx._hyg.11.0 ).isValid\n  "};
static const lean_object* l_Lean_Cadical_Solver_clause___closed__2 = (const lean_object*)&l_Lean_Cadical_Solver_clause___closed__2_value;
static lean_once_cell_t l_Lean_Cadical_Solver_clause___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Cadical_Solver_clause___closed__3;
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_clause(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_clause___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_inconsistent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_inconsistent___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Cadical_Solver_assume___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Cadical.Solver.assume"};
static const lean_object* l_Lean_Cadical_Solver_assume___closed__0 = (const lean_object*)&l_Lean_Cadical_Solver_assume___closed__0_value;
static const lean_string_object l_Lean_Cadical_Solver_assume___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "assertion violation: ( __do_lift._@.Lean.Cadical.Basic.3174909903._hygCtx._hyg.11.0 ).isReady\n  "};
static const lean_object* l_Lean_Cadical_Solver_assume___closed__1 = (const lean_object*)&l_Lean_Cadical_Solver_assume___closed__1_value;
static lean_once_cell_t l_Lean_Cadical_Solver_assume___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Cadical_Solver_assume___closed__2;
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_assume(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_assume___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Cadical_Solver_solve_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Cadical_Solver_solve_spec__0___closed__0;
LEAN_EXPORT uint8_t l_panic___at___00Lean_Cadical_Solver_solve_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_solve_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Cadical_Solver_solve___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Cadical.Solver.solve"};
static const lean_object* l_Lean_Cadical_Solver_solve___closed__0 = (const lean_object*)&l_Lean_Cadical_Solver_solve___closed__0_value;
static const lean_string_object l_Lean_Cadical_Solver_solve___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 96, .m_capacity = 96, .m_length = 95, .m_data = "assertion violation: ( __do_lift._@.Lean.Cadical.Basic.3198481143._hygCtx._hyg.9.0 ).isReady\n  "};
static const lean_object* l_Lean_Cadical_Solver_solve___closed__1 = (const lean_object*)&l_Lean_Cadical_Solver_solve___closed__1_value;
static lean_once_cell_t l_Lean_Cadical_Solver_solve___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Cadical_Solver_solve___closed__2;
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_solve(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_solve___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Cadical_Solver_val___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "State should be "};
static const lean_object* l_Lean_Cadical_Solver_val___closed__0 = (const lean_object*)&l_Lean_Cadical_Solver_val___closed__0_value;
static lean_once_cell_t l_Lean_Cadical_Solver_val___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Cadical_Solver_val___closed__1;
static lean_once_cell_t l_Lean_Cadical_Solver_val___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Cadical_Solver_val___closed__2;
static const lean_string_object l_Lean_Cadical_Solver_val___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " but is "};
static const lean_object* l_Lean_Cadical_Solver_val___closed__3 = (const lean_object*)&l_Lean_Cadical_Solver_val___closed__3_value;
static lean_once_cell_t l_Lean_Cadical_Solver_val___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Cadical_Solver_val___closed__4;
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_val(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_val___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_resetAssumptions(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_resetAssumptions___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_status(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_status___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_isValidOption(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_isValidOption___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_isPreprocessingOption(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_isPreprocessingOption___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_isValidLongOption(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_isValidLongOption___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Cadical_Solver_getOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_getOption___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Cadical_Solver_setOption_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Cadical_Solver_setOption_spec__0___closed__0;
LEAN_EXPORT uint8_t l_panic___at___00Lean_Cadical_Solver_setOption_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_setOption_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Cadical_Solver_setOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Cadical.Solver.setOption"};
static const lean_object* l_Lean_Cadical_Solver_setOption___closed__0 = (const lean_object*)&l_Lean_Cadical_Solver_setOption___closed__0_value;
static const lean_string_object l_Lean_Cadical_Solver_setOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 105, .m_capacity = 105, .m_length = 104, .m_data = "assertion violation: ( __do_lift._@.Lean.Cadical.Basic.2432095391._hygCtx._hyg.11.0 ) == .configuring\n  "};
static const lean_object* l_Lean_Cadical_Solver_setOption___closed__1 = (const lean_object*)&l_Lean_Cadical_Solver_setOption___closed__1_value;
static lean_once_cell_t l_Lean_Cadical_Solver_setOption___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Cadical_Solver_setOption___closed__2;
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_setOption(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_setOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Cadical_Solver_setLongOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Cadical.Solver.setLongOption"};
static const lean_object* l_Lean_Cadical_Solver_setLongOption___closed__0 = (const lean_object*)&l_Lean_Cadical_Solver_setLongOption___closed__0_value;
static const lean_string_object l_Lean_Cadical_Solver_setLongOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 105, .m_capacity = 105, .m_length = 104, .m_data = "assertion violation: ( __do_lift._@.Lean.Cadical.Basic.2675852425._hygCtx._hyg.10.0 ) == .configuring\n  "};
static const lean_object* l_Lean_Cadical_Solver_setLongOption___closed__1 = (const lean_object*)&l_Lean_Cadical_Solver_setLongOption___closed__1_value;
static lean_once_cell_t l_Lean_Cadical_Solver_setLongOption___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Cadical_Solver_setLongOption___closed__2;
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_setLongOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_setLongOption___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_isValidConfiguration(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_isValidConfiguration___boxed(lean_object*);
static const lean_string_object l_Lean_Cadical_Solver_configure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Cadical.Solver.configure"};
static const lean_object* l_Lean_Cadical_Solver_configure___closed__0 = (const lean_object*)&l_Lean_Cadical_Solver_configure___closed__0_value;
static const lean_string_object l_Lean_Cadical_Solver_configure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 105, .m_capacity = 105, .m_length = 104, .m_data = "assertion violation: ( __do_lift._@.Lean.Cadical.Basic.3118119930._hygCtx._hyg.10.0 ) == .configuring\n  "};
static const lean_object* l_Lean_Cadical_Solver_configure___closed__1 = (const lean_object*)&l_Lean_Cadical_Solver_configure___closed__1_value;
static lean_once_cell_t l_Lean_Cadical_Solver_configure___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Cadical_Solver_configure___closed__2;
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_configure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_configure___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Cadical_Solver_terminate_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Cadical_Solver_terminate_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_terminate_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_terminate_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Cadical_Solver_terminate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Cadical.Solver.terminate"};
static const lean_object* l_Lean_Cadical_Solver_terminate___closed__0 = (const lean_object*)&l_Lean_Cadical_Solver_terminate___closed__0_value;
static const lean_string_object l_Lean_Cadical_Solver_terminate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "assertion violation: state == .solving || state.isReady\n  "};
static const lean_object* l_Lean_Cadical_Solver_terminate___closed__1 = (const lean_object*)&l_Lean_Cadical_Solver_terminate___closed__1_value;
static lean_once_cell_t l_Lean_Cadical_Solver_terminate___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Cadical_Solver_terminate___closed__2;
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_terminate(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_terminate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printConfigurations();
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printConfigurations___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printStatistics(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printStatistics___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printResources(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printResources___boxed(lean_object*, lean_object*);
static uint16_t _init_l_Lean_Cadical_instInhabitedState_default(void){
_start:
{
uint16_t v___x_1_; 
v___x_1_ = 0;
return v___x_1_;
}
}
static uint16_t _init_l_Lean_Cadical_instInhabitedState(void){
_start:
{
uint16_t v___x_2_; 
v___x_2_ = 0;
return v___x_2_;
}
}
uint8_t l_Lean_Cadical_instDecidableEqState_decEq(uint16_t v_x_3_, uint16_t v_x_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_uint16_dec_eq(v_x_3_, v_x_4_);
return v___x_5_;
}
}
LEAN_EXPORT void l_Lean_Cadical_instDecidableEqState_decEq_0interp(lean_interpreter_value* stack)
{
uint16_t v_x_3_ = stack[0].m_num;
uint16_t v_x_4_ = stack[1].m_num;
uint8_t v_res_6_;
v_res_6_ = l_Lean_Cadical_instDecidableEqState_decEq(v_x_3_, v_x_4_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_instDecidableEqState_decEq___boxed(lean_object* v_x_7_, lean_object* v_x_8_){
_start:
{
uint16_t v_x_31__boxed_9_; uint16_t v_x_32__boxed_10_; uint8_t v_res_11_; lean_object* v_r_12_; 
v_x_31__boxed_9_ = lean_unbox(v_x_7_);
v_x_32__boxed_10_ = lean_unbox(v_x_8_);
v_res_11_ = l_Lean_Cadical_instDecidableEqState_decEq(v_x_31__boxed_9_, v_x_32__boxed_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
uint8_t l_Lean_Cadical_instDecidableEqState(uint16_t v_x_13_, uint16_t v_x_14_){
_start:
{
uint8_t v___x_15_; 
v___x_15_ = lean_uint16_dec_eq(v_x_13_, v_x_14_);
return v___x_15_;
}
}
LEAN_EXPORT void l_Lean_Cadical_instDecidableEqState_0interp(lean_interpreter_value* stack)
{
uint16_t v_x_13_ = stack[0].m_num;
uint16_t v_x_14_ = stack[1].m_num;
uint8_t v_res_16_;
v_res_16_ = l_Lean_Cadical_instDecidableEqState(v_x_13_, v_x_14_);
stack->m_num = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_instDecidableEqState___boxed(lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
uint16_t v_x_6__boxed_19_; uint16_t v_x_7__boxed_20_; uint8_t v_res_21_; lean_object* v_r_22_; 
v_x_6__boxed_19_ = lean_unbox(v_x_17_);
v_x_7__boxed_20_ = lean_unbox(v_x_18_);
v_res_21_ = l_Lean_Cadical_instDecidableEqState(v_x_6__boxed_19_, v_x_7__boxed_20_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
uint64_t l_Lean_Cadical_instHashableState_hash(uint16_t v_x_23_){
_start:
{
uint64_t v___x_24_; uint64_t v___x_25_; uint64_t v___x_26_; 
v___x_24_ = 0ULL;
v___x_25_ = lean_uint16_to_uint64(v_x_23_);
v___x_26_ = lean_uint64_mix_hash(v___x_24_, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT void l_Lean_Cadical_instHashableState_hash_0interp(lean_interpreter_value* stack)
{
uint16_t v_x_23_ = stack[0].m_num;
uint64_t v_res_27_;
v_res_27_ = l_Lean_Cadical_instHashableState_hash(v_x_23_);
stack->m_num = v_res_27_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_instHashableState_hash___boxed(lean_object* v_x_28_){
_start:
{
uint16_t v_x_26__boxed_29_; uint64_t v_res_30_; lean_object* v_r_31_; 
v_x_26__boxed_29_ = lean_unbox(v_x_28_);
v_res_30_ = l_Lean_Cadical_instHashableState_hash(v_x_26__boxed_29_);
v_r_31_ = lean_box_uint64(v_res_30_);
return v_r_31_;
}
}
static uint16_t _init_l_Lean_Cadical_State_initializing(void){
_start:
{
uint16_t v___x_34_; 
v___x_34_ = 1;
return v___x_34_;
}
}
static uint16_t _init_l_Lean_Cadical_State_configuring(void){
_start:
{
uint16_t v___x_35_; 
v___x_35_ = 2;
return v___x_35_;
}
}
static uint16_t _init_l_Lean_Cadical_State_steady(void){
_start:
{
uint16_t v___x_36_; 
v___x_36_ = 4;
return v___x_36_;
}
}
static uint16_t _init_l_Lean_Cadical_State_adding(void){
_start:
{
uint16_t v___x_37_; 
v___x_37_ = 8;
return v___x_37_;
}
}
static uint16_t _init_l_Lean_Cadical_State_solving(void){
_start:
{
uint16_t v___x_38_; 
v___x_38_ = 16;
return v___x_38_;
}
}
static uint16_t _init_l_Lean_Cadical_State_satisfied(void){
_start:
{
uint16_t v___x_39_; 
v___x_39_ = 32;
return v___x_39_;
}
}
static uint16_t _init_l_Lean_Cadical_State_unsatisfied(void){
_start:
{
uint16_t v___x_40_; 
v___x_40_ = 64;
return v___x_40_;
}
}
static uint16_t _init_l_Lean_Cadical_State_deleting(void){
_start:
{
uint16_t v___x_41_; 
v___x_41_ = 128;
return v___x_41_;
}
}
static uint16_t _init_l_Lean_Cadical_State_inconclusive(void){
_start:
{
uint16_t v___x_42_; 
v___x_42_ = 256;
return v___x_42_;
}
}
static uint16_t _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_State_ready(void){
_start:
{
uint16_t v___x_43_; 
v___x_43_ = 358;
return v___x_43_;
}
}
static uint16_t _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_State_valid(void){
_start:
{
uint16_t v___x_44_; 
v___x_44_ = 366;
return v___x_44_;
}
}
static uint16_t _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_State_invalid(void){
_start:
{
uint16_t v___x_45_; 
v___x_45_ = 129;
return v___x_45_;
}
}
static lean_object* _init_l_Lean_Cadical_State_isReady___closed__0(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_unsigned_to_nat(0u);
v___x_47_ = lean_unsigned_to_nat(16u);
v___x_48_ = l_BitVec_ofNat(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static uint16_t _init_l_Lean_Cadical_State_isReady___closed__1(void){
_start:
{
lean_object* v___x_49_; uint16_t v___x_50_; 
v___x_49_ = lean_obj_once(&l_Lean_Cadical_State_isReady___closed__0, &l_Lean_Cadical_State_isReady___closed__0_once, _init_l_Lean_Cadical_State_isReady___closed__0);
v___x_50_ = lean_uint16_of_nat_mk(v___x_49_);
return v___x_50_;
}
}
uint8_t l_Lean_Cadical_State_isReady(uint16_t v_s_51_){
_start:
{
uint16_t v___x_52_; uint16_t v___x_53_; uint16_t v___x_54_; uint8_t v___x_55_; 
v___x_52_ = 358;
v___x_53_ = lean_uint16_land(v_s_51_, v___x_52_);
v___x_54_ = lean_uint16_once(&l_Lean_Cadical_State_isReady___closed__1, &l_Lean_Cadical_State_isReady___closed__1_once, _init_l_Lean_Cadical_State_isReady___closed__1);
v___x_55_ = lean_uint16_dec_eq(v___x_53_, v___x_54_);
if (v___x_55_ == 0)
{
uint8_t v___x_56_; 
v___x_56_ = 1;
return v___x_56_;
}
else
{
uint8_t v___x_57_; 
v___x_57_ = 0;
return v___x_57_;
}
}
}
LEAN_EXPORT void l_Lean_Cadical_State_isReady_0interp(lean_interpreter_value* stack)
{
uint16_t v_s_51_ = stack[0].m_num;
uint8_t v_res_58_;
v_res_58_ = l_Lean_Cadical_State_isReady(v_s_51_);
stack->m_num = v_res_58_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_State_isReady___boxed(lean_object* v_s_59_){
_start:
{
uint16_t v_s_boxed_60_; uint8_t v_res_61_; lean_object* v_r_62_; 
v_s_boxed_60_ = lean_unbox(v_s_59_);
v_res_61_ = l_Lean_Cadical_State_isReady(v_s_boxed_60_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
uint8_t l_Lean_Cadical_State_isValid(uint16_t v_s_63_){
_start:
{
uint16_t v___x_64_; uint16_t v___x_65_; uint16_t v___x_66_; uint8_t v___x_67_; 
v___x_64_ = 366;
v___x_65_ = lean_uint16_land(v_s_63_, v___x_64_);
v___x_66_ = lean_uint16_once(&l_Lean_Cadical_State_isReady___closed__1, &l_Lean_Cadical_State_isReady___closed__1_once, _init_l_Lean_Cadical_State_isReady___closed__1);
v___x_67_ = lean_uint16_dec_eq(v___x_65_, v___x_66_);
if (v___x_67_ == 0)
{
uint8_t v___x_68_; 
v___x_68_ = 1;
return v___x_68_;
}
else
{
uint8_t v___x_69_; 
v___x_69_ = 0;
return v___x_69_;
}
}
}
LEAN_EXPORT void l_Lean_Cadical_State_isValid_0interp(lean_interpreter_value* stack)
{
uint16_t v_s_63_ = stack[0].m_num;
uint8_t v_res_70_;
v_res_70_ = l_Lean_Cadical_State_isValid(v_s_63_);
stack->m_num = v_res_70_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_State_isValid___boxed(lean_object* v_s_71_){
_start:
{
uint16_t v_s_boxed_72_; uint8_t v_res_73_; lean_object* v_r_74_; 
v_s_boxed_72_ = lean_unbox(v_s_71_);
v_res_73_ = l_Lean_Cadical_State_isValid(v_s_boxed_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
uint8_t l_Lean_Cadical_State_isInvalid(uint16_t v_s_75_){
_start:
{
uint16_t v___x_76_; uint16_t v___x_77_; uint16_t v___x_78_; uint8_t v___x_79_; 
v___x_76_ = 129;
v___x_77_ = lean_uint16_land(v_s_75_, v___x_76_);
v___x_78_ = lean_uint16_once(&l_Lean_Cadical_State_isReady___closed__1, &l_Lean_Cadical_State_isReady___closed__1_once, _init_l_Lean_Cadical_State_isReady___closed__1);
v___x_79_ = lean_uint16_dec_eq(v___x_77_, v___x_78_);
if (v___x_79_ == 0)
{
uint8_t v___x_80_; 
v___x_80_ = 1;
return v___x_80_;
}
else
{
uint8_t v___x_81_; 
v___x_81_ = 0;
return v___x_81_;
}
}
}
LEAN_EXPORT void l_Lean_Cadical_State_isInvalid_0interp(lean_interpreter_value* stack)
{
uint16_t v_s_75_ = stack[0].m_num;
uint8_t v_res_82_;
v_res_82_ = l_Lean_Cadical_State_isInvalid(v_s_75_);
stack->m_num = v_res_82_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_State_isInvalid___boxed(lean_object* v_s_83_){
_start:
{
uint16_t v_s_boxed_84_; uint8_t v_res_85_; lean_object* v_r_86_; 
v_s_boxed_84_ = lean_unbox(v_s_83_);
v_res_85_ = l_Lean_Cadical_State_isInvalid(v_s_boxed_84_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
lean_object* l_Lean_Cadical_State_toString(uint16_t v_s_96_){
_start:
{
uint16_t v___x_97_; uint8_t v___x_98_; 
v___x_97_ = 1;
v___x_98_ = lean_uint16_dec_eq(v_s_96_, v___x_97_);
if (v___x_98_ == 0)
{
uint16_t v___x_99_; uint8_t v___x_100_; 
v___x_99_ = 2;
v___x_100_ = lean_uint16_dec_eq(v_s_96_, v___x_99_);
if (v___x_100_ == 0)
{
uint16_t v___x_101_; uint8_t v___x_102_; 
v___x_101_ = 4;
v___x_102_ = lean_uint16_dec_eq(v_s_96_, v___x_101_);
if (v___x_102_ == 0)
{
uint16_t v___x_103_; uint8_t v___x_104_; 
v___x_103_ = 8;
v___x_104_ = lean_uint16_dec_eq(v_s_96_, v___x_103_);
if (v___x_104_ == 0)
{
uint16_t v___x_105_; uint8_t v___x_106_; 
v___x_105_ = 16;
v___x_106_ = lean_uint16_dec_eq(v_s_96_, v___x_105_);
if (v___x_106_ == 0)
{
uint16_t v___x_107_; uint8_t v___x_108_; 
v___x_107_ = 32;
v___x_108_ = lean_uint16_dec_eq(v_s_96_, v___x_107_);
if (v___x_108_ == 0)
{
uint16_t v___x_109_; uint8_t v___x_110_; 
v___x_109_ = 64;
v___x_110_ = lean_uint16_dec_eq(v_s_96_, v___x_109_);
if (v___x_110_ == 0)
{
uint16_t v___x_111_; uint8_t v___x_112_; 
v___x_111_ = 256;
v___x_112_ = lean_uint16_dec_eq(v_s_96_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; 
v___x_113_ = ((lean_object*)(l_Lean_Cadical_State_toString___closed__0));
return v___x_113_;
}
else
{
lean_object* v___x_114_; 
v___x_114_ = ((lean_object*)(l_Lean_Cadical_State_toString___closed__1));
return v___x_114_;
}
}
else
{
lean_object* v___x_115_; 
v___x_115_ = ((lean_object*)(l_Lean_Cadical_State_toString___closed__2));
return v___x_115_;
}
}
else
{
lean_object* v___x_116_; 
v___x_116_ = ((lean_object*)(l_Lean_Cadical_State_toString___closed__3));
return v___x_116_;
}
}
else
{
lean_object* v___x_117_; 
v___x_117_ = ((lean_object*)(l_Lean_Cadical_State_toString___closed__4));
return v___x_117_;
}
}
else
{
lean_object* v___x_118_; 
v___x_118_ = ((lean_object*)(l_Lean_Cadical_State_toString___closed__5));
return v___x_118_;
}
}
else
{
lean_object* v___x_119_; 
v___x_119_ = ((lean_object*)(l_Lean_Cadical_State_toString___closed__6));
return v___x_119_;
}
}
else
{
lean_object* v___x_120_; 
v___x_120_ = ((lean_object*)(l_Lean_Cadical_State_toString___closed__7));
return v___x_120_;
}
}
else
{
lean_object* v___x_121_; 
v___x_121_ = ((lean_object*)(l_Lean_Cadical_State_toString___closed__8));
return v___x_121_;
}
}
}
LEAN_EXPORT void l_Lean_Cadical_State_toString_0interp(lean_interpreter_value* stack)
{
uint16_t v_s_96_ = stack[0].m_num;
lean_object* v_res_122_;
v_res_122_ = l_Lean_Cadical_State_toString(v_s_96_);
stack->m_obj
 = v_res_122_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_State_toString___boxed(lean_object* v_s_123_){
_start:
{
uint16_t v_s_boxed_124_; lean_object* v_res_125_; 
v_s_boxed_124_ = lean_unbox(v_s_123_);
v_res_125_ = l_Lean_Cadical_State_toString(v_s_boxed_124_);
return v_res_125_;
}
}
lean_object* l_Lean_Cadical_Status_ctorIdx___impl(uint8_t v_x_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_box(v_x_128_);
v___x_130_ = lean_obj_tag_nat(v___x_129_);
lean_dec(v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Status_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_128_ = stack[0].m_num;
lean_object* v_res_131_;
v_res_131_ = l_Lean_Cadical_Status_ctorIdx___impl(v_x_128_);
stack->m_obj
 = v_res_131_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorIdx___impl___boxed(lean_object* v_x_132_){
_start:
{
uint8_t v_x_4__boxed_133_; lean_object* v_res_134_; 
v_x_4__boxed_133_ = lean_unbox(v_x_132_);
v_res_134_ = l_Lean_Cadical_Status_ctorIdx___impl(v_x_4__boxed_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorElim___redArg(lean_object* v_k_135_){
_start:
{
lean_inc(v_k_135_);
return v_k_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorElim___redArg___boxed(lean_object* v_k_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_Cadical_Status_ctorElim___redArg(v_k_136_);
lean_dec(v_k_136_);
return v_res_137_;
}
}
lean_object* l_Lean_Cadical_Status_ctorElim(lean_object* v_motive_138_, lean_object* v_ctorIdx_139_, uint8_t v_t_140_, lean_object* v_h_141_, lean_object* v_k_142_){
_start:
{
lean_inc(v_k_142_);
return v_k_142_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Status_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_139_ = stack[1].m_obj;
uint8_t v_t_140_ = stack[2].m_num;
lean_object* v_k_142_ = stack[4].m_obj;
lean_object* v_res_143_;
v_res_143_ = l_Lean_Cadical_Status_ctorElim(lean_box(0), v_ctorIdx_139_, v_t_140_, lean_box(0), v_k_142_);
stack->m_obj
 = v_res_143_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorElim___boxed(lean_object* v_motive_144_, lean_object* v_ctorIdx_145_, lean_object* v_t_146_, lean_object* v_h_147_, lean_object* v_k_148_){
_start:
{
uint8_t v_t_boxed_149_; lean_object* v_res_150_; 
v_t_boxed_149_ = lean_unbox(v_t_146_);
v_res_150_ = l_Lean_Cadical_Status_ctorElim(v_motive_144_, v_ctorIdx_145_, v_t_boxed_149_, v_h_147_, v_k_148_);
lean_dec(v_k_148_);
lean_dec(v_ctorIdx_145_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_satisfiable_elim___redArg(lean_object* v_satisfiable_151_){
_start:
{
lean_inc(v_satisfiable_151_);
return v_satisfiable_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_satisfiable_elim___redArg___boxed(lean_object* v_satisfiable_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_Cadical_Status_satisfiable_elim___redArg(v_satisfiable_152_);
lean_dec(v_satisfiable_152_);
return v_res_153_;
}
}
lean_object* l_Lean_Cadical_Status_satisfiable_elim(lean_object* v_motive_154_, uint8_t v_t_155_, lean_object* v_h_156_, lean_object* v_satisfiable_157_){
_start:
{
lean_inc(v_satisfiable_157_);
return v_satisfiable_157_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Status_satisfiable_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_155_ = stack[1].m_num;
lean_object* v_satisfiable_157_ = stack[3].m_obj;
lean_object* v_res_158_;
v_res_158_ = l_Lean_Cadical_Status_satisfiable_elim(lean_box(0), v_t_155_, lean_box(0), v_satisfiable_157_);
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_satisfiable_elim___boxed(lean_object* v_motive_159_, lean_object* v_t_160_, lean_object* v_h_161_, lean_object* v_satisfiable_162_){
_start:
{
uint8_t v_t_boxed_163_; lean_object* v_res_164_; 
v_t_boxed_163_ = lean_unbox(v_t_160_);
v_res_164_ = l_Lean_Cadical_Status_satisfiable_elim(v_motive_159_, v_t_boxed_163_, v_h_161_, v_satisfiable_162_);
lean_dec(v_satisfiable_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unsatisfiable_elim___redArg(lean_object* v_unsatisfiable_165_){
_start:
{
lean_inc(v_unsatisfiable_165_);
return v_unsatisfiable_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unsatisfiable_elim___redArg___boxed(lean_object* v_unsatisfiable_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_Cadical_Status_unsatisfiable_elim___redArg(v_unsatisfiable_166_);
lean_dec(v_unsatisfiable_166_);
return v_res_167_;
}
}
lean_object* l_Lean_Cadical_Status_unsatisfiable_elim(lean_object* v_motive_168_, uint8_t v_t_169_, lean_object* v_h_170_, lean_object* v_unsatisfiable_171_){
_start:
{
lean_inc(v_unsatisfiable_171_);
return v_unsatisfiable_171_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Status_unsatisfiable_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_169_ = stack[1].m_num;
lean_object* v_unsatisfiable_171_ = stack[3].m_obj;
lean_object* v_res_172_;
v_res_172_ = l_Lean_Cadical_Status_unsatisfiable_elim(lean_box(0), v_t_169_, lean_box(0), v_unsatisfiable_171_);
stack->m_obj
 = v_res_172_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unsatisfiable_elim___boxed(lean_object* v_motive_173_, lean_object* v_t_174_, lean_object* v_h_175_, lean_object* v_unsatisfiable_176_){
_start:
{
uint8_t v_t_boxed_177_; lean_object* v_res_178_; 
v_t_boxed_177_ = lean_unbox(v_t_174_);
v_res_178_ = l_Lean_Cadical_Status_unsatisfiable_elim(v_motive_173_, v_t_boxed_177_, v_h_175_, v_unsatisfiable_176_);
lean_dec(v_unsatisfiable_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unknown_elim___redArg(lean_object* v_unknown_179_){
_start:
{
lean_inc(v_unknown_179_);
return v_unknown_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unknown_elim___redArg___boxed(lean_object* v_unknown_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_Cadical_Status_unknown_elim___redArg(v_unknown_180_);
lean_dec(v_unknown_180_);
return v_res_181_;
}
}
lean_object* l_Lean_Cadical_Status_unknown_elim(lean_object* v_motive_182_, uint8_t v_t_183_, lean_object* v_h_184_, lean_object* v_unknown_185_){
_start:
{
lean_inc(v_unknown_185_);
return v_unknown_185_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Status_unknown_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_183_ = stack[1].m_num;
lean_object* v_unknown_185_ = stack[3].m_obj;
lean_object* v_res_186_;
v_res_186_ = l_Lean_Cadical_Status_unknown_elim(lean_box(0), v_t_183_, lean_box(0), v_unknown_185_);
stack->m_obj
 = v_res_186_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unknown_elim___boxed(lean_object* v_motive_187_, lean_object* v_t_188_, lean_object* v_h_189_, lean_object* v_unknown_190_){
_start:
{
uint8_t v_t_boxed_191_; lean_object* v_res_192_; 
v_t_boxed_191_ = lean_unbox(v_t_188_);
v_res_192_ = l_Lean_Cadical_Status_unknown_elim(v_motive_187_, v_t_boxed_191_, v_h_189_, v_unknown_190_);
lean_dec(v_unknown_190_);
return v_res_192_;
}
}
static uint8_t _init_l_Lean_Cadical_instInhabitedStatus_default(void){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = 0;
return v___x_193_;
}
}
static uint8_t _init_l_Lean_Cadical_instInhabitedStatus(void){
_start:
{
uint8_t v___x_194_; 
v___x_194_ = 0;
return v___x_194_;
}
}
uint8_t l_Lean_Cadical_Status_ofNat(lean_object* v_n_195_){
_start:
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = lean_nat_dec_le(v_n_195_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_198_ = lean_unsigned_to_nat(1u);
v___x_199_ = lean_nat_dec_le(v_n_195_, v___x_198_);
if (v___x_199_ == 0)
{
uint8_t v___x_200_; 
v___x_200_ = 2;
return v___x_200_;
}
else
{
uint8_t v___x_201_; 
v___x_201_ = 1;
return v___x_201_;
}
}
else
{
uint8_t v___x_202_; 
v___x_202_ = 0;
return v___x_202_;
}
}
}
LEAN_EXPORT void l_Lean_Cadical_Status_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_195_ = stack[0].m_obj;
uint8_t v_res_203_;
v_res_203_ = l_Lean_Cadical_Status_ofNat(v_n_195_);
stack->m_num = v_res_203_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ofNat___boxed(lean_object* v_n_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Lean_Cadical_Status_ofNat(v_n_204_);
lean_dec(v_n_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
uint8_t l_Lean_Cadical_instDecidableEqStatus(uint8_t v_x_207_, uint8_t v_y_208_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_209_ = lean_box(v_x_207_);
v___x_210_ = lean_obj_tag_nat(v___x_209_);
lean_dec(v___x_209_);
v___x_211_ = lean_box(v_y_208_);
v___x_212_ = lean_obj_tag_nat(v___x_211_);
lean_dec(v___x_211_);
v___x_213_ = lean_nat_dec_eq(v___x_210_, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT void l_Lean_Cadical_instDecidableEqStatus_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_207_ = stack[0].m_num;
uint8_t v_y_208_ = stack[1].m_num;
uint8_t v_res_214_;
v_res_214_ = l_Lean_Cadical_instDecidableEqStatus(v_x_207_, v_y_208_);
stack->m_num = v_res_214_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_instDecidableEqStatus___boxed(lean_object* v_x_215_, lean_object* v_y_216_){
_start:
{
uint8_t v_x_23__boxed_217_; uint8_t v_y_24__boxed_218_; uint8_t v_res_219_; lean_object* v_r_220_; 
v_x_23__boxed_217_ = lean_unbox(v_x_215_);
v_y_24__boxed_218_ = lean_unbox(v_y_216_);
v_res_219_ = l_Lean_Cadical_instDecidableEqStatus(v_x_23__boxed_217_, v_y_24__boxed_218_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
uint64_t l_Lean_Cadical_instHashableStatus_hash(uint8_t v_x_221_){
_start:
{
switch(v_x_221_)
{
case 0:
{
uint64_t v___x_222_; 
v___x_222_ = 0ULL;
return v___x_222_;
}
case 1:
{
uint64_t v___x_223_; 
v___x_223_ = 1ULL;
return v___x_223_;
}
default: 
{
uint64_t v___x_224_; 
v___x_224_ = 2ULL;
return v___x_224_;
}
}
}
}
LEAN_EXPORT void l_Lean_Cadical_instHashableStatus_hash_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_221_ = stack[0].m_num;
uint64_t v_res_225_;
v_res_225_ = l_Lean_Cadical_instHashableStatus_hash(v_x_221_);
stack->m_num = v_res_225_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_instHashableStatus_hash___boxed(lean_object* v_x_226_){
_start:
{
uint8_t v_x_40__boxed_227_; uint64_t v_res_228_; lean_object* v_r_229_; 
v_x_40__boxed_227_ = lean_unbox(v_x_226_);
v_res_228_ = l_Lean_Cadical_instHashableStatus_hash(v_x_40__boxed_227_);
v_r_229_ = lean_box_uint64(v_res_228_);
return v_r_229_;
}
}
static lean_object* _init_l_Lean_Cadical_instReprStatus_repr___closed__6(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_unsigned_to_nat(2u);
v___x_242_ = lean_nat_to_int(v___x_241_);
return v___x_242_;
}
}
static lean_object* _init_l_Lean_Cadical_instReprStatus_repr___closed__7(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_unsigned_to_nat(1u);
v___x_244_ = lean_nat_to_int(v___x_243_);
return v___x_244_;
}
}
lean_object* l_Lean_Cadical_instReprStatus_repr(uint8_t v_x_245_, lean_object* v_prec_246_){
_start:
{
lean_object* v___y_248_; lean_object* v___y_255_; lean_object* v___y_262_; 
switch(v_x_245_)
{
case 0:
{
lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(1024u);
v___x_269_ = lean_nat_dec_le(v___x_268_, v_prec_246_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; 
v___x_270_ = lean_obj_once(&l_Lean_Cadical_instReprStatus_repr___closed__6, &l_Lean_Cadical_instReprStatus_repr___closed__6_once, _init_l_Lean_Cadical_instReprStatus_repr___closed__6);
v___y_248_ = v___x_270_;
goto v___jp_247_;
}
else
{
lean_object* v___x_271_; 
v___x_271_ = lean_obj_once(&l_Lean_Cadical_instReprStatus_repr___closed__7, &l_Lean_Cadical_instReprStatus_repr___closed__7_once, _init_l_Lean_Cadical_instReprStatus_repr___closed__7);
v___y_248_ = v___x_271_;
goto v___jp_247_;
}
}
case 1:
{
lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_272_ = lean_unsigned_to_nat(1024u);
v___x_273_ = lean_nat_dec_le(v___x_272_, v_prec_246_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
v___x_274_ = lean_obj_once(&l_Lean_Cadical_instReprStatus_repr___closed__6, &l_Lean_Cadical_instReprStatus_repr___closed__6_once, _init_l_Lean_Cadical_instReprStatus_repr___closed__6);
v___y_255_ = v___x_274_;
goto v___jp_254_;
}
else
{
lean_object* v___x_275_; 
v___x_275_ = lean_obj_once(&l_Lean_Cadical_instReprStatus_repr___closed__7, &l_Lean_Cadical_instReprStatus_repr___closed__7_once, _init_l_Lean_Cadical_instReprStatus_repr___closed__7);
v___y_255_ = v___x_275_;
goto v___jp_254_;
}
}
default: 
{
lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_276_ = lean_unsigned_to_nat(1024u);
v___x_277_ = lean_nat_dec_le(v___x_276_, v_prec_246_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; 
v___x_278_ = lean_obj_once(&l_Lean_Cadical_instReprStatus_repr___closed__6, &l_Lean_Cadical_instReprStatus_repr___closed__6_once, _init_l_Lean_Cadical_instReprStatus_repr___closed__6);
v___y_262_ = v___x_278_;
goto v___jp_261_;
}
else
{
lean_object* v___x_279_; 
v___x_279_ = lean_obj_once(&l_Lean_Cadical_instReprStatus_repr___closed__7, &l_Lean_Cadical_instReprStatus_repr___closed__7_once, _init_l_Lean_Cadical_instReprStatus_repr___closed__7);
v___y_262_ = v___x_279_;
goto v___jp_261_;
}
}
}
v___jp_247_:
{
lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_249_ = ((lean_object*)(l_Lean_Cadical_instReprStatus_repr___closed__1));
lean_inc(v___y_248_);
v___x_250_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_250_, 0, v___y_248_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = 0;
v___x_252_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set_uint8(v___x_252_, sizeof(void*)*1, v___x_251_);
v___x_253_ = l_Repr_addAppParen(v___x_252_, v_prec_246_);
return v___x_253_;
}
v___jp_254_:
{
lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_256_ = ((lean_object*)(l_Lean_Cadical_instReprStatus_repr___closed__3));
lean_inc(v___y_255_);
v___x_257_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_257_, 0, v___y_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = 0;
v___x_259_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_259_, 0, v___x_257_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*1, v___x_258_);
v___x_260_ = l_Repr_addAppParen(v___x_259_, v_prec_246_);
return v___x_260_;
}
v___jp_261_:
{
lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_263_ = ((lean_object*)(l_Lean_Cadical_instReprStatus_repr___closed__5));
lean_inc(v___y_262_);
v___x_264_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_264_, 0, v___y_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = 0;
v___x_266_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set_uint8(v___x_266_, sizeof(void*)*1, v___x_265_);
v___x_267_ = l_Repr_addAppParen(v___x_266_, v_prec_246_);
return v___x_267_;
}
}
}
LEAN_EXPORT void l_Lean_Cadical_instReprStatus_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_245_ = stack[0].m_num;
lean_object* v_prec_246_ = stack[1].m_obj;
lean_object* v_res_280_;
v_res_280_ = l_Lean_Cadical_instReprStatus_repr(v_x_245_, v_prec_246_);
stack->m_obj
 = v_res_280_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_instReprStatus_repr___boxed(lean_object* v_x_281_, lean_object* v_prec_282_){
_start:
{
uint8_t v_x_171__boxed_283_; lean_object* v_res_284_; 
v_x_171__boxed_283_ = lean_unbox(v_x_281_);
v_res_284_ = l_Lean_Cadical_instReprStatus_repr(v_x_171__boxed_283_, v_prec_282_);
lean_dec(v_prec_282_);
return v_res_284_;
}
}
static uint32_t _init_l_Lean_Cadical_Status_toInt32___closed__0(void){
_start:
{
lean_object* v___x_287_; uint32_t v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(10u);
v___x_288_ = lean_int32_of_nat(v___x_287_);
return v___x_288_;
}
}
static uint32_t _init_l_Lean_Cadical_Status_toInt32___closed__1(void){
_start:
{
lean_object* v___x_289_; uint32_t v___x_290_; 
v___x_289_ = lean_unsigned_to_nat(20u);
v___x_290_ = lean_int32_of_nat(v___x_289_);
return v___x_290_;
}
}
static uint32_t _init_l_Lean_Cadical_Status_toInt32___closed__2(void){
_start:
{
lean_object* v___x_291_; uint32_t v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = lean_int32_of_nat(v___x_291_);
return v___x_292_;
}
}
uint32_t l_Lean_Cadical_Status_toInt32(uint8_t v_x_293_){
_start:
{
switch(v_x_293_)
{
case 0:
{
uint32_t v___x_294_; 
v___x_294_ = lean_uint32_once(&l_Lean_Cadical_Status_toInt32___closed__0, &l_Lean_Cadical_Status_toInt32___closed__0_once, _init_l_Lean_Cadical_Status_toInt32___closed__0);
return v___x_294_;
}
case 1:
{
uint32_t v___x_295_; 
v___x_295_ = lean_uint32_once(&l_Lean_Cadical_Status_toInt32___closed__1, &l_Lean_Cadical_Status_toInt32___closed__1_once, _init_l_Lean_Cadical_Status_toInt32___closed__1);
return v___x_295_;
}
default: 
{
uint32_t v___x_296_; 
v___x_296_ = lean_uint32_once(&l_Lean_Cadical_Status_toInt32___closed__2, &l_Lean_Cadical_Status_toInt32___closed__2_once, _init_l_Lean_Cadical_Status_toInt32___closed__2);
return v___x_296_;
}
}
}
}
LEAN_EXPORT void l_Lean_Cadical_Status_toInt32_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_293_ = stack[0].m_num;
uint32_t v_res_297_;
v_res_297_ = l_Lean_Cadical_Status_toInt32(v_x_293_);
stack->m_num = v_res_297_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_toInt32___boxed(lean_object* v_x_298_){
_start:
{
uint8_t v_x_52__boxed_299_; uint32_t v_res_300_; lean_object* v_r_301_; 
v_x_52__boxed_299_ = lean_unbox(v_x_298_);
v_res_300_ = l_Lean_Cadical_Status_toInt32(v_x_52__boxed_299_);
v_r_301_ = lean_box_uint32(v_res_300_);
return v_r_301_;
}
}
lean_object* l_Lean_Cadical_Status_toString(uint8_t v_x_305_){
_start:
{
switch(v_x_305_)
{
case 0:
{
lean_object* v___x_306_; 
v___x_306_ = ((lean_object*)(l_Lean_Cadical_Status_toString___closed__0));
return v___x_306_;
}
case 1:
{
lean_object* v___x_307_; 
v___x_307_ = ((lean_object*)(l_Lean_Cadical_Status_toString___closed__1));
return v___x_307_;
}
default: 
{
lean_object* v___x_308_; 
v___x_308_ = ((lean_object*)(l_Lean_Cadical_Status_toString___closed__2));
return v___x_308_;
}
}
}
}
LEAN_EXPORT void l_Lean_Cadical_Status_toString_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_305_ = stack[0].m_num;
lean_object* v_res_309_;
v_res_309_ = l_Lean_Cadical_Status_toString(v_x_305_);
stack->m_obj
 = v_res_309_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_toString___boxed(lean_object* v_x_310_){
_start:
{
uint8_t v_x_31__boxed_311_; lean_object* v_res_312_; 
v_x_31__boxed_311_ = lean_unbox(v_x_310_);
v_res_312_ = l_Lean_Cadical_Status_toString(v_x_31__boxed_311_);
return v_res_312_;
}
}
uint8_t l___private_Lean_Cadical_Basic_0__Lean_Cadical_Status_ofInternal(uint8_t v_s_315_){
_start:
{
switch(v_s_315_)
{
case 0:
{
uint8_t v___x_316_; 
v___x_316_ = 0;
return v___x_316_;
}
case 1:
{
uint8_t v___x_317_; 
v___x_317_ = 1;
return v___x_317_;
}
default: 
{
uint8_t v___x_318_; 
v___x_318_ = 2;
return v___x_318_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Cadical_Basic_0__Lean_Cadical_Status_ofInternal_0interp(lean_interpreter_value* stack)
{
uint8_t v_s_315_ = stack[0].m_num;
uint8_t v_res_319_;
v_res_319_ = l___private_Lean_Cadical_Basic_0__Lean_Cadical_Status_ofInternal(v_s_315_);
stack->m_num = v_res_319_;
}
LEAN_EXPORT lean_object* l___private_Lean_Cadical_Basic_0__Lean_Cadical_Status_ofInternal___boxed(lean_object* v_s_320_){
_start:
{
uint8_t v_s_boxed_321_; uint8_t v_res_322_; lean_object* v_r_323_; 
v_s_boxed_321_ = lean_unbox(v_s_320_);
v_res_322_ = l___private_Lean_Cadical_Basic_0__Lean_Cadical_Status_ofInternal(v_s_boxed_321_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
static uint32_t _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__0(void){
_start:
{
lean_object* v___x_324_; uint32_t v___x_325_; 
v___x_324_ = lean_unsigned_to_nat(2147483647u);
v___x_325_ = lean_int32_of_nat(v___x_324_);
return v___x_325_;
}
}
static lean_object* _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__1(void){
_start:
{
uint32_t v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_uint32_once(&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__0, &l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__0_once, _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__0);
v___x_327_ = lean_int32_to_int(v___x_326_);
return v___x_327_;
}
}
static lean_object* _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_obj_once(&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__1, &l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__1_once, _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__1);
v___x_329_ = l_Int_toNat(v___x_328_);
return v___x_329_;
}
}
lean_object* l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit(lean_object* v_lit_333_, uint8_t v_pol_334_){
_start:
{
lean_object* v___x_336_; lean_object* v_lit_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_336_ = lean_unsigned_to_nat(1u);
v_lit_337_ = lean_nat_add(v_lit_333_, v___x_336_);
v___x_338_ = lean_obj_once(&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2, &l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2_once, _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2);
v___x_339_ = lean_nat_dec_lt(v___x_338_, v_lit_337_);
if (v___x_339_ == 0)
{
uint32_t v_lit_340_; 
v_lit_340_ = lean_int32_of_nat(v_lit_337_);
lean_dec(v_lit_337_);
if (v_pol_334_ == 0)
{
uint32_t v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_int32_neg(v_lit_340_);
v___x_342_ = lean_box_uint32(v___x_341_);
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_box_uint32(v_lit_340_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; 
lean_dec(v_lit_337_);
v___x_346_ = ((lean_object*)(l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__4));
v___x_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
return v___x_347_;
}
}
}
LEAN_EXPORT void l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit_0interp(lean_interpreter_value* stack)
{
lean_object* v_lit_333_ = stack[0].m_obj;
uint8_t v_pol_334_ = stack[1].m_num;
lean_object* v_res_348_;
v_res_348_ = l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit(v_lit_333_, v_pol_334_);
stack->m_obj
 = v_res_348_;
}
LEAN_EXPORT lean_object* l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___boxed(lean_object* v_lit_349_, lean_object* v_pol_350_, lean_object* v_a_351_){
_start:
{
uint8_t v_pol_boxed_352_; lean_object* v_res_353_; 
v_pol_boxed_352_ = lean_unbox(v_pol_350_);
v_res_353_ = l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit(v_lit_349_, v_pol_boxed_352_);
lean_dec(v_lit_349_);
return v_res_353_;
}
}
lean_object* l_Lean_Cadical_Solver_new(){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_cadical_solver_new();
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_357_;
v_res_357_ = l_Lean_Cadical_Solver_new();
stack->m_obj
 = v_res_357_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_new___boxed(lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Cadical_Solver_new();
return v_res_359_;
}
}
uint16_t l_Lean_Cadical_Solver_state(lean_object* v_s_360_){
_start:
{
lean_object* v_solver_362_; uint16_t v___x_363_; 
v_solver_362_ = lean_ctor_get(v_s_360_, 0);
v___x_363_ = lean_cadical_solver_state(v_solver_362_);
return v___x_363_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_state_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_360_ = stack[0].m_obj;
uint16_t v_res_364_;
v_res_364_ = l_Lean_Cadical_Solver_state(v_s_360_);
stack->m_num = v_res_364_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_state___boxed(lean_object* v_s_365_, lean_object* v_a_366_){
_start:
{
uint16_t v_res_367_; lean_object* v_r_368_; 
v_res_367_ = l_Lean_Cadical_Solver_state(v_s_365_);
lean_dec_ref(v_s_365_);
v_r_368_ = lean_box(v_res_367_);
return v_r_368_;
}
}
static lean_object* _init_l_panic___at___00Lean_Cadical_Solver_clause_spec__1___closed__0(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = l_instInhabitedError;
v___x_370_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_370_, 0, lean_box(0));
lean_closure_set(v___x_370_, 1, lean_box(0));
lean_closure_set(v___x_370_, 2, v___x_369_);
return v___x_370_;
}
}
lean_object* l_panic___at___00Lean_Cadical_Solver_clause_spec__1(lean_object* v_msg_371_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_806__overap_374_; lean_object* v___x_375_; 
v___x_373_ = lean_obj_once(&l_panic___at___00Lean_Cadical_Solver_clause_spec__1___closed__0, &l_panic___at___00Lean_Cadical_Solver_clause_spec__1___closed__0_once, _init_l_panic___at___00Lean_Cadical_Solver_clause_spec__1___closed__0);
v___x_806__overap_374_ = lean_panic_fn_borrowed(v___x_373_, v_msg_371_);
v___x_375_ = lean_apply_1(v___x_806__overap_374_, lean_box(0));
return v___x_375_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Cadical_Solver_clause_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_371_ = stack[0].m_obj;
lean_object* v_res_376_;
v_res_376_ = l_panic___at___00Lean_Cadical_Solver_clause_spec__1(v_msg_371_);
stack->m_obj
 = v_res_376_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_clause_spec__1___boxed(lean_object* v_msg_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_panic___at___00Lean_Cadical_Solver_clause_spec__1(v_msg_377_);
return v_res_379_;
}
}
lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Lean_Cadical_Solver_clause_spec__0(lean_object* v_s_380_, lean_object* v_c_381_, size_t v_sz_382_, size_t v_i_383_, lean_object* v_b_384_){
_start:
{
uint8_t v___x_386_; 
v___x_386_ = lean_usize_dec_lt(v_i_383_, v_sz_382_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; 
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v_b_384_);
return v___x_387_;
}
else
{
lean_object* v_atoms_388_; lean_object* v_polarities_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v_lit_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v_atoms_388_ = lean_ctor_get(v_c_381_, 0);
v_polarities_389_ = lean_ctor_get(v_c_381_, 1);
v___x_390_ = lean_array_uget_borrowed(v_atoms_388_, v_i_383_);
v___x_391_ = lean_unsigned_to_nat(1u);
v_lit_392_ = lean_nat_add(v___x_390_, v___x_391_);
v___x_393_ = lean_obj_once(&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2, &l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2_once, _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2);
v___x_394_ = lean_nat_dec_lt(v___x_393_, v_lit_392_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; uint32_t v_a_397_; uint8_t v___x_403_; uint8_t v___x_404_; uint8_t v___x_405_; uint32_t v_lit_406_; 
v___x_395_ = lean_box(0);
v___x_403_ = lean_byte_array_uget(v_polarities_389_, v_i_383_);
v___x_404_ = 1;
v___x_405_ = lean_uint8_dec_eq(v___x_403_, v___x_404_);
v_lit_406_ = lean_int32_of_nat(v_lit_392_);
lean_dec(v_lit_392_);
if (v___x_405_ == 0)
{
uint32_t v___x_407_; 
v___x_407_ = lean_int32_neg(v_lit_406_);
v_a_397_ = v___x_407_;
goto v___jp_396_;
}
else
{
v_a_397_ = v_lit_406_;
goto v___jp_396_;
}
v___jp_396_:
{
lean_object* v_solver_398_; lean_object* v___x_399_; size_t v___x_400_; size_t v___x_401_; 
v_solver_398_ = lean_ctor_get(v_s_380_, 0);
v___x_399_ = lean_cadical_solver_add(v_solver_398_, v_a_397_);
v___x_400_ = ((size_t)1ULL);
v___x_401_ = lean_usize_add(v_i_383_, v___x_400_);
v_i_383_ = v___x_401_;
v_b_384_ = v___x_395_;
goto _start;
}
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec(v_lit_392_);
v___x_408_ = ((lean_object*)(l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__4));
v___x_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Lean_Cadical_Solver_clause_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_380_ = stack[0].m_obj;
lean_object* v_c_381_ = stack[1].m_obj;
size_t v_sz_382_ = stack[2].m_num;
size_t v_i_383_ = stack[3].m_num;
lean_object* v_b_384_ = stack[4].m_obj;
lean_object* v_res_410_;
v_res_410_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Lean_Cadical_Solver_clause_spec__0(v_s_380_, v_c_381_, v_sz_382_, v_i_383_, v_b_384_);
stack->m_obj
 = v_res_410_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Lean_Cadical_Solver_clause_spec__0___boxed(lean_object* v_s_411_, lean_object* v_c_412_, lean_object* v_sz_413_, lean_object* v_i_414_, lean_object* v_b_415_, lean_object* v___y_416_){
_start:
{
size_t v_sz_boxed_417_; size_t v_i_boxed_418_; lean_object* v_res_419_; 
v_sz_boxed_417_ = lean_unbox_usize(v_sz_413_);
lean_dec(v_sz_413_);
v_i_boxed_418_ = lean_unbox_usize(v_i_414_);
lean_dec(v_i_414_);
v_res_419_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Lean_Cadical_Solver_clause_spec__0(v_s_411_, v_c_412_, v_sz_boxed_417_, v_i_boxed_418_, v_b_415_);
lean_dec_ref(v_c_412_);
lean_dec_ref(v_s_411_);
return v_res_419_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_clause___closed__3(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_423_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__2));
v___x_424_ = lean_unsigned_to_nat(2u);
v___x_425_ = lean_unsigned_to_nat(176u);
v___x_426_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__1));
v___x_427_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_428_ = l_mkPanicMessageWithDecl(v___x_427_, v___x_426_, v___x_425_, v___x_424_, v___x_423_);
return v___x_428_;
}
}
lean_object* l_Lean_Cadical_Solver_clause(lean_object* v_s_429_, lean_object* v_clause_430_){
_start:
{
uint16_t v___x_432_; uint16_t v___x_433_; uint16_t v___x_434_; uint16_t v___x_435_; uint8_t v___x_436_; 
v___x_432_ = l_Lean_Cadical_Solver_state(v_s_429_);
v___x_433_ = 366;
v___x_434_ = lean_uint16_land(v___x_432_, v___x_433_);
v___x_435_ = lean_uint16_once(&l_Lean_Cadical_State_isReady___closed__1, &l_Lean_Cadical_State_isReady___closed__1_once, _init_l_Lean_Cadical_State_isReady___closed__1);
v___x_436_ = lean_uint16_dec_eq(v___x_434_, v___x_435_);
if (v___x_436_ == 0)
{
lean_object* v_atoms_437_; lean_object* v___x_438_; size_t v_sz_439_; size_t v___x_440_; lean_object* v___x_441_; 
v_atoms_437_ = lean_ctor_get(v_clause_430_, 0);
v___x_438_ = lean_box(0);
v_sz_439_ = lean_array_size(v_atoms_437_);
v___x_440_ = ((size_t)0ULL);
v___x_441_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Lean_Cadical_Solver_clause_spec__0(v_s_429_, v_clause_430_, v_sz_439_, v___x_440_, v___x_438_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_451_; 
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_451_ == 0)
{
lean_object* v_unused_452_; 
v_unused_452_ = lean_ctor_get(v___x_441_, 0);
lean_dec(v_unused_452_);
v___x_443_ = v___x_441_;
v_isShared_444_ = v_isSharedCheck_451_;
goto v_resetjp_442_;
}
else
{
lean_dec(v___x_441_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_451_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v_solver_445_; uint32_t v___x_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
v_solver_445_ = lean_ctor_get(v_s_429_, 0);
v___x_446_ = lean_uint32_once(&l_Lean_Cadical_Status_toInt32___closed__2, &l_Lean_Cadical_Status_toInt32___closed__2_once, _init_l_Lean_Cadical_Status_toInt32___closed__2);
v___x_447_ = lean_cadical_solver_add(v_solver_445_, v___x_446_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_447_);
v___x_449_ = v___x_443_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
else
{
return v___x_441_;
}
}
else
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_obj_once(&l_Lean_Cadical_Solver_clause___closed__3, &l_Lean_Cadical_Solver_clause___closed__3_once, _init_l_Lean_Cadical_Solver_clause___closed__3);
v___x_454_ = l_panic___at___00Lean_Cadical_Solver_clause_spec__1(v___x_453_);
return v___x_454_;
}
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_clause_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_429_ = stack[0].m_obj;
lean_object* v_clause_430_ = stack[1].m_obj;
lean_object* v_res_455_;
v_res_455_ = l_Lean_Cadical_Solver_clause(v_s_429_, v_clause_430_);
stack->m_obj
 = v_res_455_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_clause___boxed(lean_object* v_s_456_, lean_object* v_clause_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_Cadical_Solver_clause(v_s_456_, v_clause_457_);
lean_dec_ref(v_clause_457_);
lean_dec_ref(v_s_456_);
return v_res_459_;
}
}
uint8_t l_Lean_Cadical_Solver_inconsistent(lean_object* v_s_460_){
_start:
{
lean_object* v_solver_462_; uint8_t v___x_463_; 
v_solver_462_ = lean_ctor_get(v_s_460_, 0);
v___x_463_ = lean_cadical_solver_inconsistent(v_solver_462_);
return v___x_463_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_inconsistent_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_460_ = stack[0].m_obj;
uint8_t v_res_464_;
v_res_464_ = l_Lean_Cadical_Solver_inconsistent(v_s_460_);
stack->m_num = v_res_464_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_inconsistent___boxed(lean_object* v_s_465_, lean_object* v_a_466_){
_start:
{
uint8_t v_res_467_; lean_object* v_r_468_; 
v_res_467_ = l_Lean_Cadical_Solver_inconsistent(v_s_465_);
lean_dec_ref(v_s_465_);
v_r_468_ = lean_box(v_res_467_);
return v_r_468_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_assume___closed__2(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_471_ = ((lean_object*)(l_Lean_Cadical_Solver_assume___closed__1));
v___x_472_ = lean_unsigned_to_nat(2u);
v___x_473_ = lean_unsigned_to_nat(191u);
v___x_474_ = ((lean_object*)(l_Lean_Cadical_Solver_assume___closed__0));
v___x_475_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_476_ = l_mkPanicMessageWithDecl(v___x_475_, v___x_474_, v___x_473_, v___x_472_, v___x_471_);
return v___x_476_;
}
}
lean_object* l_Lean_Cadical_Solver_assume(lean_object* v_s_477_, lean_object* v_lit_478_, uint8_t v_pol_479_){
_start:
{
uint32_t v_a_482_; uint16_t v___x_492_; uint16_t v___x_493_; uint16_t v___x_494_; uint16_t v___x_495_; uint8_t v___x_496_; 
v___x_492_ = l_Lean_Cadical_Solver_state(v_s_477_);
v___x_493_ = 358;
v___x_494_ = lean_uint16_land(v___x_492_, v___x_493_);
v___x_495_ = lean_uint16_once(&l_Lean_Cadical_State_isReady___closed__1, &l_Lean_Cadical_State_isReady___closed__1_once, _init_l_Lean_Cadical_State_isReady___closed__1);
v___x_496_ = lean_uint16_dec_eq(v___x_494_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v_lit_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_497_ = lean_unsigned_to_nat(1u);
v_lit_498_ = lean_nat_add(v_lit_478_, v___x_497_);
v___x_499_ = lean_obj_once(&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2, &l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2_once, _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2);
v___x_500_ = lean_nat_dec_lt(v___x_499_, v_lit_498_);
if (v___x_500_ == 0)
{
uint32_t v_lit_501_; 
v_lit_501_ = lean_int32_of_nat(v_lit_498_);
lean_dec(v_lit_498_);
if (v_pol_479_ == 0)
{
uint32_t v___x_502_; 
v___x_502_ = lean_int32_neg(v_lit_501_);
v_a_482_ = v___x_502_;
goto v___jp_481_;
}
else
{
v_a_482_ = v_lit_501_;
goto v___jp_481_;
}
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec(v_lit_498_);
lean_dec_ref(v_s_477_);
v___x_503_ = ((lean_object*)(l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__4));
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; 
lean_dec_ref(v_s_477_);
v___x_505_ = lean_obj_once(&l_Lean_Cadical_Solver_assume___closed__2, &l_Lean_Cadical_Solver_assume___closed__2_once, _init_l_Lean_Cadical_Solver_assume___closed__2);
v___x_506_ = l_panic___at___00Lean_Cadical_Solver_clause_spec__1(v___x_505_);
return v___x_506_;
}
v___jp_481_:
{
lean_object* v_solver_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_491_; 
v_solver_483_ = lean_ctor_get(v_s_477_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v_s_477_);
if (v_isSharedCheck_491_ == 0)
{
v___x_485_ = v_s_477_;
v_isShared_486_ = v_isSharedCheck_491_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_solver_483_);
lean_dec(v_s_477_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_491_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_487_ = lean_cadical_solver_assume(v_solver_483_, v_a_482_);
lean_dec(v_solver_483_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_487_);
v___x_489_ = v___x_485_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_assume_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_477_ = stack[0].m_obj;
lean_object* v_lit_478_ = stack[1].m_obj;
uint8_t v_pol_479_ = stack[2].m_num;
lean_object* v_res_507_;
v_res_507_ = l_Lean_Cadical_Solver_assume(v_s_477_, v_lit_478_, v_pol_479_);
stack->m_obj
 = v_res_507_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_assume___boxed(lean_object* v_s_508_, lean_object* v_lit_509_, lean_object* v_pol_510_, lean_object* v_a_511_){
_start:
{
uint8_t v_pol_boxed_512_; lean_object* v_res_513_; 
v_pol_boxed_512_ = lean_unbox(v_pol_510_);
v_res_513_ = l_Lean_Cadical_Solver_assume(v_s_508_, v_lit_509_, v_pol_boxed_512_);
lean_dec(v_lit_509_);
return v_res_513_;
}
}
static lean_object* _init_l_panic___at___00Lean_Cadical_Solver_solve_spec__0___closed__0(void){
_start:
{
uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_514_ = 0;
v___x_515_ = l_instMonadBaseIO;
v___x_516_ = lean_box(v___x_514_);
v___x_517_ = l_instInhabitedOfMonad___redArg(v___x_515_, v___x_516_);
return v___x_517_;
}
}
uint8_t l_panic___at___00Lean_Cadical_Solver_solve_spec__0(lean_object* v_msg_518_){
_start:
{
lean_object* v___x_520_; lean_object* v___x_211__overap_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_520_ = lean_obj_once(&l_panic___at___00Lean_Cadical_Solver_solve_spec__0___closed__0, &l_panic___at___00Lean_Cadical_Solver_solve_spec__0___closed__0_once, _init_l_panic___at___00Lean_Cadical_Solver_solve_spec__0___closed__0);
v___x_211__overap_521_ = lean_panic_fn_borrowed(v___x_520_, v_msg_518_);
v___x_522_ = lean_apply_1(v___x_211__overap_521_, lean_box(0));
v___x_523_ = lean_unbox(v___x_522_);
return v___x_523_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Cadical_Solver_solve_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_518_ = stack[0].m_obj;
uint8_t v_res_524_;
v_res_524_ = l_panic___at___00Lean_Cadical_Solver_solve_spec__0(v_msg_518_);
stack->m_num = v_res_524_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_solve_spec__0___boxed(lean_object* v_msg_525_, lean_object* v___y_526_){
_start:
{
uint8_t v_res_527_; lean_object* v_r_528_; 
v_res_527_ = l_panic___at___00Lean_Cadical_Solver_solve_spec__0(v_msg_525_);
v_r_528_ = lean_box(v_res_527_);
return v_r_528_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_solve___closed__2(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_531_ = ((lean_object*)(l_Lean_Cadical_Solver_solve___closed__1));
v___x_532_ = lean_unsigned_to_nat(2u);
v___x_533_ = lean_unsigned_to_nat(198u);
v___x_534_ = ((lean_object*)(l_Lean_Cadical_Solver_solve___closed__0));
v___x_535_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_536_ = l_mkPanicMessageWithDecl(v___x_535_, v___x_534_, v___x_533_, v___x_532_, v___x_531_);
return v___x_536_;
}
}
uint8_t l_Lean_Cadical_Solver_solve(lean_object* v_s_537_){
_start:
{
uint16_t v___x_539_; uint16_t v___x_540_; uint16_t v___x_541_; uint16_t v___x_542_; uint8_t v___x_543_; 
v___x_539_ = l_Lean_Cadical_Solver_state(v_s_537_);
v___x_540_ = 358;
v___x_541_ = lean_uint16_land(v___x_539_, v___x_540_);
v___x_542_ = lean_uint16_once(&l_Lean_Cadical_State_isReady___closed__1, &l_Lean_Cadical_State_isReady___closed__1_once, _init_l_Lean_Cadical_State_isReady___closed__1);
v___x_543_ = lean_uint16_dec_eq(v___x_541_, v___x_542_);
if (v___x_543_ == 0)
{
lean_object* v_solver_544_; uint8_t v___x_545_; 
v_solver_544_ = lean_ctor_get(v_s_537_, 0);
v___x_545_ = lean_cadical_solver_solve(v_solver_544_);
switch(v___x_545_)
{
case 0:
{
uint8_t v___x_546_; 
v___x_546_ = 0;
return v___x_546_;
}
case 1:
{
uint8_t v___x_547_; 
v___x_547_ = 1;
return v___x_547_;
}
default: 
{
uint8_t v___x_548_; 
v___x_548_ = 2;
return v___x_548_;
}
}
}
else
{
lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_549_ = lean_obj_once(&l_Lean_Cadical_Solver_solve___closed__2, &l_Lean_Cadical_Solver_solve___closed__2_once, _init_l_Lean_Cadical_Solver_solve___closed__2);
v___x_550_ = l_panic___at___00Lean_Cadical_Solver_solve_spec__0(v___x_549_);
return v___x_550_;
}
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_solve_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_537_ = stack[0].m_obj;
uint8_t v_res_551_;
v_res_551_ = l_Lean_Cadical_Solver_solve(v_s_537_);
stack->m_num = v_res_551_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_solve___boxed(lean_object* v_s_552_, lean_object* v_a_553_){
_start:
{
uint8_t v_res_554_; lean_object* v_r_555_; 
v_res_554_ = l_Lean_Cadical_Solver_solve(v_s_552_);
lean_dec_ref(v_s_552_);
v_r_555_ = lean_box(v_res_554_);
return v_r_555_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_val___closed__1(void){
_start:
{
uint16_t v___x_557_; lean_object* v___x_558_; 
v___x_557_ = 32;
v___x_558_ = l_Lean_Cadical_State_toString(v___x_557_);
return v___x_558_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_val___closed__2(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = lean_obj_once(&l_Lean_Cadical_Solver_val___closed__1, &l_Lean_Cadical_Solver_val___closed__1_once, _init_l_Lean_Cadical_Solver_val___closed__1);
v___x_560_ = ((lean_object*)(l_Lean_Cadical_Solver_val___closed__0));
v___x_561_ = lean_string_append(v___x_560_, v___x_559_);
return v___x_561_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_val___closed__4(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_563_ = ((lean_object*)(l_Lean_Cadical_Solver_val___closed__3));
v___x_564_ = lean_obj_once(&l_Lean_Cadical_Solver_val___closed__2, &l_Lean_Cadical_Solver_val___closed__2_once, _init_l_Lean_Cadical_Solver_val___closed__2);
v___x_565_ = lean_string_append(v___x_564_, v___x_563_);
return v___x_565_;
}
}
lean_object* l_Lean_Cadical_Solver_val(lean_object* v_s_566_, lean_object* v_lit_567_){
_start:
{
uint16_t v___x_569_; uint16_t v___x_570_; uint8_t v___x_571_; 
v___x_569_ = l_Lean_Cadical_Solver_state(v_s_566_);
v___x_570_ = 32;
v___x_571_ = lean_uint16_dec_eq(v___x_569_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec_ref(v_s_566_);
v___x_572_ = lean_obj_once(&l_Lean_Cadical_Solver_val___closed__4, &l_Lean_Cadical_Solver_val___closed__4_once, _init_l_Lean_Cadical_Solver_val___closed__4);
v___x_573_ = l_Lean_Cadical_State_toString(v___x_569_);
v___x_574_ = lean_string_append(v___x_572_, v___x_573_);
lean_dec_ref(v___x_573_);
v___x_575_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
v___x_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
else
{
lean_object* v___x_577_; lean_object* v_lit_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_577_ = lean_unsigned_to_nat(1u);
v_lit_578_ = lean_nat_add(v_lit_567_, v___x_577_);
v___x_579_ = lean_obj_once(&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2, &l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2_once, _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2);
v___x_580_ = lean_nat_dec_lt(v___x_579_, v_lit_578_);
if (v___x_580_ == 0)
{
lean_object* v_solver_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_592_; 
v_solver_581_ = lean_ctor_get(v_s_566_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v_s_566_);
if (v_isSharedCheck_592_ == 0)
{
v___x_583_ = v_s_566_;
v_isShared_584_ = v_isSharedCheck_592_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_solver_581_);
lean_dec(v_s_566_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_592_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
uint32_t v_lit_585_; uint32_t v___x_586_; uint8_t v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v_lit_585_ = lean_int32_of_nat(v_lit_578_);
lean_dec(v_lit_578_);
v___x_586_ = lean_cadical_solver_val(v_solver_581_, v_lit_585_);
lean_dec(v_solver_581_);
v___x_587_ = lean_int32_dec_eq(v_lit_585_, v___x_586_);
v___x_588_ = lean_box(v___x_587_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_588_);
v___x_590_ = v___x_583_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec(v_lit_578_);
lean_dec_ref(v_s_566_);
v___x_593_ = ((lean_object*)(l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__4));
v___x_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
return v___x_594_;
}
}
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_val_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_566_ = stack[0].m_obj;
lean_object* v_lit_567_ = stack[1].m_obj;
lean_object* v_res_595_;
v_res_595_ = l_Lean_Cadical_Solver_val(v_s_566_, v_lit_567_);
stack->m_obj
 = v_res_595_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_val___boxed(lean_object* v_s_596_, lean_object* v_lit_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_Cadical_Solver_val(v_s_596_, v_lit_597_);
lean_dec(v_lit_597_);
return v_res_599_;
}
}
lean_object* l_Lean_Cadical_Solver_resetAssumptions(lean_object* v_s_600_){
_start:
{
lean_object* v_solver_602_; lean_object* v___x_603_; 
v_solver_602_ = lean_ctor_get(v_s_600_, 0);
v___x_603_ = lean_cadical_solver_reset_assumptions(v_solver_602_);
return v___x_603_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_resetAssumptions_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_600_ = stack[0].m_obj;
lean_object* v_res_604_;
v_res_604_ = l_Lean_Cadical_Solver_resetAssumptions(v_s_600_);
stack->m_obj
 = v_res_604_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_resetAssumptions___boxed(lean_object* v_s_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_Cadical_Solver_resetAssumptions(v_s_605_);
lean_dec_ref(v_s_605_);
return v_res_607_;
}
}
uint8_t l_Lean_Cadical_Solver_status(lean_object* v_s_608_){
_start:
{
lean_object* v_solver_610_; uint8_t v___x_611_; 
v_solver_610_ = lean_ctor_get(v_s_608_, 0);
v___x_611_ = lean_cadical_solver_status(v_solver_610_);
switch(v___x_611_)
{
case 0:
{
uint8_t v___x_612_; 
v___x_612_ = 0;
return v___x_612_;
}
case 1:
{
uint8_t v___x_613_; 
v___x_613_ = 1;
return v___x_613_;
}
default: 
{
uint8_t v___x_614_; 
v___x_614_ = 2;
return v___x_614_;
}
}
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_status_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_608_ = stack[0].m_obj;
uint8_t v_res_615_;
v_res_615_ = l_Lean_Cadical_Solver_status(v_s_608_);
stack->m_num = v_res_615_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_status___boxed(lean_object* v_s_616_, lean_object* v_a_617_){
_start:
{
uint8_t v_res_618_; lean_object* v_r_619_; 
v_res_618_ = l_Lean_Cadical_Solver_status(v_s_616_);
lean_dec_ref(v_s_616_);
v_r_619_ = lean_box(v_res_618_);
return v_r_619_;
}
}
uint8_t l_Lean_Cadical_Solver_isValidOption(lean_object* v_opt_620_){
_start:
{
uint8_t v___x_621_; 
v___x_621_ = lean_cadical_solver_is_valid_option(v_opt_620_);
return v___x_621_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_isValidOption_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_620_ = stack[0].m_obj;
uint8_t v_res_622_;
v_res_622_ = l_Lean_Cadical_Solver_isValidOption(v_opt_620_);
stack->m_num = v_res_622_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_isValidOption___boxed(lean_object* v_opt_623_){
_start:
{
uint8_t v_res_624_; lean_object* v_r_625_; 
v_res_624_ = l_Lean_Cadical_Solver_isValidOption(v_opt_623_);
lean_dec_ref(v_opt_623_);
v_r_625_ = lean_box(v_res_624_);
return v_r_625_;
}
}
uint8_t l_Lean_Cadical_Solver_isPreprocessingOption(lean_object* v_opt_626_){
_start:
{
uint8_t v___x_627_; 
v___x_627_ = lean_cadical_solver_is_preprocessing_option(v_opt_626_);
return v___x_627_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_isPreprocessingOption_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_626_ = stack[0].m_obj;
uint8_t v_res_628_;
v_res_628_ = l_Lean_Cadical_Solver_isPreprocessingOption(v_opt_626_);
stack->m_num = v_res_628_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_isPreprocessingOption___boxed(lean_object* v_opt_629_){
_start:
{
uint8_t v_res_630_; lean_object* v_r_631_; 
v_res_630_ = l_Lean_Cadical_Solver_isPreprocessingOption(v_opt_629_);
lean_dec_ref(v_opt_629_);
v_r_631_ = lean_box(v_res_630_);
return v_r_631_;
}
}
uint8_t l_Lean_Cadical_Solver_isValidLongOption(lean_object* v_opt_632_){
_start:
{
uint8_t v___x_633_; 
v___x_633_ = lean_cadical_solver_is_valid_long_option(v_opt_632_);
return v___x_633_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_isValidLongOption_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_632_ = stack[0].m_obj;
uint8_t v_res_634_;
v_res_634_ = l_Lean_Cadical_Solver_isValidLongOption(v_opt_632_);
stack->m_num = v_res_634_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_isValidLongOption___boxed(lean_object* v_opt_635_){
_start:
{
uint8_t v_res_636_; lean_object* v_r_637_; 
v_res_636_ = l_Lean_Cadical_Solver_isValidLongOption(v_opt_635_);
lean_dec_ref(v_opt_635_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
uint32_t l_Lean_Cadical_Solver_getOption(lean_object* v_s_638_, lean_object* v_opt_639_){
_start:
{
lean_object* v_solver_641_; uint32_t v___x_642_; 
v_solver_641_ = lean_ctor_get(v_s_638_, 0);
v___x_642_ = lean_cadical_solver_get(v_solver_641_, v_opt_639_);
return v___x_642_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_getOption_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_638_ = stack[0].m_obj;
lean_object* v_opt_639_ = stack[1].m_obj;
uint32_t v_res_643_;
v_res_643_ = l_Lean_Cadical_Solver_getOption(v_s_638_, v_opt_639_);
stack->m_num = v_res_643_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_getOption___boxed(lean_object* v_s_644_, lean_object* v_opt_645_, lean_object* v_a_646_){
_start:
{
uint32_t v_res_647_; lean_object* v_r_648_; 
v_res_647_ = l_Lean_Cadical_Solver_getOption(v_s_644_, v_opt_645_);
lean_dec_ref(v_opt_645_);
lean_dec_ref(v_s_644_);
v_r_648_ = lean_box_uint32(v_res_647_);
return v_r_648_;
}
}
static lean_object* _init_l_panic___at___00Lean_Cadical_Solver_setOption_spec__0___closed__0(void){
_start:
{
uint8_t v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_649_ = 0;
v___x_650_ = l_instMonadBaseIO;
v___x_651_ = lean_box(v___x_649_);
v___x_652_ = l_instInhabitedOfMonad___redArg(v___x_650_, v___x_651_);
return v___x_652_;
}
}
uint8_t l_panic___at___00Lean_Cadical_Solver_setOption_spec__0(lean_object* v_msg_653_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_132__overap_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_655_ = lean_obj_once(&l_panic___at___00Lean_Cadical_Solver_setOption_spec__0___closed__0, &l_panic___at___00Lean_Cadical_Solver_setOption_spec__0___closed__0_once, _init_l_panic___at___00Lean_Cadical_Solver_setOption_spec__0___closed__0);
v___x_132__overap_656_ = lean_panic_fn_borrowed(v___x_655_, v_msg_653_);
v___x_657_ = lean_apply_1(v___x_132__overap_656_, lean_box(0));
v___x_658_ = lean_unbox(v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Cadical_Solver_setOption_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_653_ = stack[0].m_obj;
uint8_t v_res_659_;
v_res_659_ = l_panic___at___00Lean_Cadical_Solver_setOption_spec__0(v_msg_653_);
stack->m_num = v_res_659_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_setOption_spec__0___boxed(lean_object* v_msg_660_, lean_object* v___y_661_){
_start:
{
uint8_t v_res_662_; lean_object* v_r_663_; 
v_res_662_ = l_panic___at___00Lean_Cadical_Solver_setOption_spec__0(v_msg_660_);
v_r_663_ = lean_box(v_res_662_);
return v_r_663_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_setOption___closed__2(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_666_ = ((lean_object*)(l_Lean_Cadical_Solver_setOption___closed__1));
v___x_667_ = lean_unsigned_to_nat(2u);
v___x_668_ = lean_unsigned_to_nat(235u);
v___x_669_ = ((lean_object*)(l_Lean_Cadical_Solver_setOption___closed__0));
v___x_670_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_671_ = l_mkPanicMessageWithDecl(v___x_670_, v___x_669_, v___x_668_, v___x_667_, v___x_666_);
return v___x_671_;
}
}
uint8_t l_Lean_Cadical_Solver_setOption(lean_object* v_s_672_, lean_object* v_opt_673_, uint32_t v_val_674_){
_start:
{
uint16_t v___x_676_; uint16_t v___x_677_; uint8_t v___x_678_; 
v___x_676_ = l_Lean_Cadical_Solver_state(v_s_672_);
v___x_677_ = 2;
v___x_678_ = lean_uint16_dec_eq(v___x_676_, v___x_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = lean_obj_once(&l_Lean_Cadical_Solver_setOption___closed__2, &l_Lean_Cadical_Solver_setOption___closed__2_once, _init_l_Lean_Cadical_Solver_setOption___closed__2);
v___x_680_ = l_panic___at___00Lean_Cadical_Solver_setOption_spec__0(v___x_679_);
return v___x_680_;
}
else
{
lean_object* v_solver_681_; uint8_t v___x_682_; 
v_solver_681_ = lean_ctor_get(v_s_672_, 0);
v___x_682_ = lean_cadical_solver_set(v_solver_681_, v_opt_673_, v_val_674_);
return v___x_682_;
}
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_setOption_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_672_ = stack[0].m_obj;
lean_object* v_opt_673_ = stack[1].m_obj;
uint32_t v_val_674_ = stack[2].m_num;
uint8_t v_res_683_;
v_res_683_ = l_Lean_Cadical_Solver_setOption(v_s_672_, v_opt_673_, v_val_674_);
stack->m_num = v_res_683_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_setOption___boxed(lean_object* v_s_684_, lean_object* v_opt_685_, lean_object* v_val_686_, lean_object* v_a_687_){
_start:
{
uint32_t v_val_boxed_688_; uint8_t v_res_689_; lean_object* v_r_690_; 
v_val_boxed_688_ = lean_unbox_uint32(v_val_686_);
lean_dec(v_val_686_);
v_res_689_ = l_Lean_Cadical_Solver_setOption(v_s_684_, v_opt_685_, v_val_boxed_688_);
lean_dec_ref(v_opt_685_);
lean_dec_ref(v_s_684_);
v_r_690_ = lean_box(v_res_689_);
return v_r_690_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_setLongOption___closed__2(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_693_ = ((lean_object*)(l_Lean_Cadical_Solver_setLongOption___closed__1));
v___x_694_ = lean_unsigned_to_nat(2u);
v___x_695_ = lean_unsigned_to_nat(239u);
v___x_696_ = ((lean_object*)(l_Lean_Cadical_Solver_setLongOption___closed__0));
v___x_697_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_698_ = l_mkPanicMessageWithDecl(v___x_697_, v___x_696_, v___x_695_, v___x_694_, v___x_693_);
return v___x_698_;
}
}
uint8_t l_Lean_Cadical_Solver_setLongOption(lean_object* v_s_699_, lean_object* v_opt_700_){
_start:
{
uint16_t v___x_702_; uint16_t v___x_703_; uint8_t v___x_704_; 
v___x_702_ = l_Lean_Cadical_Solver_state(v_s_699_);
v___x_703_ = 2;
v___x_704_ = lean_uint16_dec_eq(v___x_702_, v___x_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_705_ = lean_obj_once(&l_Lean_Cadical_Solver_setLongOption___closed__2, &l_Lean_Cadical_Solver_setLongOption___closed__2_once, _init_l_Lean_Cadical_Solver_setLongOption___closed__2);
v___x_706_ = l_panic___at___00Lean_Cadical_Solver_setOption_spec__0(v___x_705_);
return v___x_706_;
}
else
{
lean_object* v_solver_707_; uint8_t v___x_708_; 
v_solver_707_ = lean_ctor_get(v_s_699_, 0);
v___x_708_ = lean_cadical_solver_set_long_option(v_solver_707_, v_opt_700_);
return v___x_708_;
}
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_setLongOption_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_699_ = stack[0].m_obj;
lean_object* v_opt_700_ = stack[1].m_obj;
uint8_t v_res_709_;
v_res_709_ = l_Lean_Cadical_Solver_setLongOption(v_s_699_, v_opt_700_);
stack->m_num = v_res_709_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_setLongOption___boxed(lean_object* v_s_710_, lean_object* v_opt_711_, lean_object* v_a_712_){
_start:
{
uint8_t v_res_713_; lean_object* v_r_714_; 
v_res_713_ = l_Lean_Cadical_Solver_setLongOption(v_s_710_, v_opt_711_);
lean_dec_ref(v_opt_711_);
lean_dec_ref(v_s_710_);
v_r_714_ = lean_box(v_res_713_);
return v_r_714_;
}
}
uint8_t l_Lean_Cadical_Solver_isValidConfiguration(lean_object* v_opt_715_){
_start:
{
uint8_t v___x_716_; 
v___x_716_ = lean_cadical_solver_is_valid_configuration(v_opt_715_);
return v___x_716_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_isValidConfiguration_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_715_ = stack[0].m_obj;
uint8_t v_res_717_;
v_res_717_ = l_Lean_Cadical_Solver_isValidConfiguration(v_opt_715_);
stack->m_num = v_res_717_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_isValidConfiguration___boxed(lean_object* v_opt_718_){
_start:
{
uint8_t v_res_719_; lean_object* v_r_720_; 
v_res_719_ = l_Lean_Cadical_Solver_isValidConfiguration(v_opt_718_);
lean_dec_ref(v_opt_718_);
v_r_720_ = lean_box(v_res_719_);
return v_r_720_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_configure___closed__2(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_723_ = ((lean_object*)(l_Lean_Cadical_Solver_configure___closed__1));
v___x_724_ = lean_unsigned_to_nat(2u);
v___x_725_ = lean_unsigned_to_nat(245u);
v___x_726_ = ((lean_object*)(l_Lean_Cadical_Solver_configure___closed__0));
v___x_727_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_728_ = l_mkPanicMessageWithDecl(v___x_727_, v___x_726_, v___x_725_, v___x_724_, v___x_723_);
return v___x_728_;
}
}
uint8_t l_Lean_Cadical_Solver_configure(lean_object* v_s_729_, lean_object* v_opt_730_){
_start:
{
uint16_t v___x_732_; uint16_t v___x_733_; uint8_t v___x_734_; 
v___x_732_ = l_Lean_Cadical_Solver_state(v_s_729_);
v___x_733_ = 2;
v___x_734_ = lean_uint16_dec_eq(v___x_732_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = lean_obj_once(&l_Lean_Cadical_Solver_configure___closed__2, &l_Lean_Cadical_Solver_configure___closed__2_once, _init_l_Lean_Cadical_Solver_configure___closed__2);
v___x_736_ = l_panic___at___00Lean_Cadical_Solver_setOption_spec__0(v___x_735_);
return v___x_736_;
}
else
{
lean_object* v_solver_737_; uint8_t v___x_738_; 
v_solver_737_ = lean_ctor_get(v_s_729_, 0);
v___x_738_ = lean_cadical_solver_configure(v_solver_737_, v_opt_730_);
return v___x_738_;
}
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_configure_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_729_ = stack[0].m_obj;
lean_object* v_opt_730_ = stack[1].m_obj;
uint8_t v_res_739_;
v_res_739_ = l_Lean_Cadical_Solver_configure(v_s_729_, v_opt_730_);
stack->m_num = v_res_739_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_configure___boxed(lean_object* v_s_740_, lean_object* v_opt_741_, lean_object* v_a_742_){
_start:
{
uint8_t v_res_743_; lean_object* v_r_744_; 
v_res_743_ = l_Lean_Cadical_Solver_configure(v_s_740_, v_opt_741_);
lean_dec_ref(v_opt_741_);
lean_dec_ref(v_s_740_);
v_r_744_ = lean_box(v_res_743_);
return v_r_744_;
}
}
static lean_object* _init_l_panic___at___00Lean_Cadical_Solver_terminate_spec__0___closed__0(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_745_ = lean_box(0);
v___x_746_ = l_instMonadBaseIO;
v___x_747_ = l_instInhabitedOfMonad___redArg(v___x_746_, v___x_745_);
return v___x_747_;
}
}
lean_object* l_panic___at___00Lean_Cadical_Solver_terminate_spec__0(lean_object* v_msg_748_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_246__overap_751_; lean_object* v___x_752_; 
v___x_750_ = lean_obj_once(&l_panic___at___00Lean_Cadical_Solver_terminate_spec__0___closed__0, &l_panic___at___00Lean_Cadical_Solver_terminate_spec__0___closed__0_once, _init_l_panic___at___00Lean_Cadical_Solver_terminate_spec__0___closed__0);
v___x_246__overap_751_ = lean_panic_fn_borrowed(v___x_750_, v_msg_748_);
v___x_752_ = lean_apply_1(v___x_246__overap_751_, lean_box(0));
return v___x_752_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Cadical_Solver_terminate_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_748_ = stack[0].m_obj;
lean_object* v_res_753_;
v_res_753_ = l_panic___at___00Lean_Cadical_Solver_terminate_spec__0(v_msg_748_);
stack->m_obj
 = v_res_753_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_terminate_spec__0___boxed(lean_object* v_msg_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_panic___at___00Lean_Cadical_Solver_terminate_spec__0(v_msg_754_);
return v_res_756_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_terminate___closed__2(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_759_ = ((lean_object*)(l_Lean_Cadical_Solver_terminate___closed__1));
v___x_760_ = lean_unsigned_to_nat(2u);
v___x_761_ = lean_unsigned_to_nat(250u);
v___x_762_ = ((lean_object*)(l_Lean_Cadical_Solver_terminate___closed__0));
v___x_763_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_764_ = l_mkPanicMessageWithDecl(v___x_763_, v___x_762_, v___x_761_, v___x_760_, v___x_759_);
return v___x_764_;
}
}
lean_object* l_Lean_Cadical_Solver_terminate(lean_object* v_s_765_){
_start:
{
uint16_t v___x_767_; uint16_t v___x_771_; uint8_t v___x_772_; 
v___x_767_ = l_Lean_Cadical_Solver_state(v_s_765_);
v___x_771_ = 16;
v___x_772_ = lean_uint16_dec_eq(v___x_767_, v___x_771_);
if (v___x_772_ == 0)
{
uint16_t v___x_773_; uint16_t v___x_774_; uint16_t v___x_775_; uint8_t v___x_776_; 
v___x_773_ = 358;
v___x_774_ = lean_uint16_land(v___x_767_, v___x_773_);
v___x_775_ = lean_uint16_once(&l_Lean_Cadical_State_isReady___closed__1, &l_Lean_Cadical_State_isReady___closed__1_once, _init_l_Lean_Cadical_State_isReady___closed__1);
v___x_776_ = lean_uint16_dec_eq(v___x_774_, v___x_775_);
if (v___x_776_ == 0)
{
goto v___jp_768_;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_obj_once(&l_Lean_Cadical_Solver_terminate___closed__2, &l_Lean_Cadical_Solver_terminate___closed__2_once, _init_l_Lean_Cadical_Solver_terminate___closed__2);
v___x_778_ = l_panic___at___00Lean_Cadical_Solver_terminate_spec__0(v___x_777_);
return v___x_778_;
}
}
else
{
goto v___jp_768_;
}
v___jp_768_:
{
lean_object* v_solver_769_; lean_object* v___x_770_; 
v_solver_769_ = lean_ctor_get(v_s_765_, 0);
v___x_770_ = lean_cadical_solver_terminate(v_solver_769_);
return v___x_770_;
}
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_terminate_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_765_ = stack[0].m_obj;
lean_object* v_res_779_;
v_res_779_ = l_Lean_Cadical_Solver_terminate(v_s_765_);
stack->m_obj
 = v_res_779_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_terminate___boxed(lean_object* v_s_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Cadical_Solver_terminate(v_s_780_);
lean_dec_ref(v_s_780_);
return v_res_782_;
}
}
lean_object* l_Lean_Cadical_Solver_printConfigurations(){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = lean_cadical_solver_configurations();
return v___x_784_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_printConfigurations_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_785_;
v_res_785_ = l_Lean_Cadical_Solver_printConfigurations();
stack->m_obj
 = v_res_785_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printConfigurations___boxed(lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Cadical_Solver_printConfigurations();
return v_res_787_;
}
}
lean_object* l_Lean_Cadical_Solver_printStatistics(lean_object* v_s_788_){
_start:
{
lean_object* v_solver_790_; lean_object* v___x_791_; 
v_solver_790_ = lean_ctor_get(v_s_788_, 0);
v___x_791_ = lean_cadical_solver_statistics(v_solver_790_);
return v___x_791_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_printStatistics_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_788_ = stack[0].m_obj;
lean_object* v_res_792_;
v_res_792_ = l_Lean_Cadical_Solver_printStatistics(v_s_788_);
stack->m_obj
 = v_res_792_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printStatistics___boxed(lean_object* v_s_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_Cadical_Solver_printStatistics(v_s_793_);
lean_dec_ref(v_s_793_);
return v_res_795_;
}
}
lean_object* l_Lean_Cadical_Solver_printResources(lean_object* v_s_796_){
_start:
{
lean_object* v_solver_798_; lean_object* v___x_799_; 
v_solver_798_ = lean_ctor_get(v_s_796_, 0);
v___x_799_ = lean_cadical_solver_resources(v_solver_798_);
return v___x_799_;
}
}
LEAN_EXPORT void l_Lean_Cadical_Solver_printResources_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_796_ = stack[0].m_obj;
lean_object* v_res_800_;
v_res_800_ = l_Lean_Cadical_Solver_printResources(v_s_796_);
stack->m_obj
 = v_res_800_;
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printResources___boxed(lean_object* v_s_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_Cadical_Solver_printResources(v_s_801_);
lean_dec_ref(v_s_801_);
return v_res_803_;
}
}
lean_object* runtime_initialize_Lean_Cadical_Internal(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_CNF_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Cadical_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Cadical_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Cadical_instInhabitedState_default = _init_l_Lean_Cadical_instInhabitedState_default();
l_Lean_Cadical_instInhabitedState = _init_l_Lean_Cadical_instInhabitedState();
l_Lean_Cadical_State_initializing = _init_l_Lean_Cadical_State_initializing();
l_Lean_Cadical_State_configuring = _init_l_Lean_Cadical_State_configuring();
l_Lean_Cadical_State_steady = _init_l_Lean_Cadical_State_steady();
l_Lean_Cadical_State_adding = _init_l_Lean_Cadical_State_adding();
l_Lean_Cadical_State_solving = _init_l_Lean_Cadical_State_solving();
l_Lean_Cadical_State_satisfied = _init_l_Lean_Cadical_State_satisfied();
l_Lean_Cadical_State_unsatisfied = _init_l_Lean_Cadical_State_unsatisfied();
l_Lean_Cadical_State_deleting = _init_l_Lean_Cadical_State_deleting();
l_Lean_Cadical_State_inconclusive = _init_l_Lean_Cadical_State_inconclusive();
l___private_Lean_Cadical_Basic_0__Lean_Cadical_State_ready = _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_State_ready();
l___private_Lean_Cadical_Basic_0__Lean_Cadical_State_valid = _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_State_valid();
l___private_Lean_Cadical_Basic_0__Lean_Cadical_State_invalid = _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_State_invalid();
l_Lean_Cadical_instInhabitedStatus_default = _init_l_Lean_Cadical_instInhabitedStatus_default();
l_Lean_Cadical_instInhabitedStatus = _init_l_Lean_Cadical_instInhabitedStatus();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Cadical_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Cadical_Internal(uint8_t builtin);
lean_object* initialize_Std_Sat_CNF_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Init_System_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Cadical_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Cadical_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Cadical_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Cadical_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Cadical_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
