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
LEAN_EXPORT uint8_t l_Lean_Cadical_instDecidableEqState_decEq(uint16_t v_x_3_, uint16_t v_x_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_uint16_dec_eq(v_x_3_, v_x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_instDecidableEqState_decEq___boxed(lean_object* v_x_6_, lean_object* v_x_7_){
_start:
{
uint16_t v_x_31__boxed_8_; uint16_t v_x_32__boxed_9_; uint8_t v_res_10_; lean_object* v_r_11_; 
v_x_31__boxed_8_ = lean_unbox(v_x_6_);
v_x_32__boxed_9_ = lean_unbox(v_x_7_);
v_res_10_ = l_Lean_Cadical_instDecidableEqState_decEq(v_x_31__boxed_8_, v_x_32__boxed_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_instDecidableEqState(uint16_t v_x_12_, uint16_t v_x_13_){
_start:
{
uint8_t v___x_14_; 
v___x_14_ = lean_uint16_dec_eq(v_x_12_, v_x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_instDecidableEqState___boxed(lean_object* v_x_15_, lean_object* v_x_16_){
_start:
{
uint16_t v_x_6__boxed_17_; uint16_t v_x_7__boxed_18_; uint8_t v_res_19_; lean_object* v_r_20_; 
v_x_6__boxed_17_ = lean_unbox(v_x_15_);
v_x_7__boxed_18_ = lean_unbox(v_x_16_);
v_res_19_ = l_Lean_Cadical_instDecidableEqState(v_x_6__boxed_17_, v_x_7__boxed_18_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT uint64_t l_Lean_Cadical_instHashableState_hash(uint16_t v_x_21_){
_start:
{
uint64_t v___x_22_; uint64_t v___x_23_; uint64_t v___x_24_; 
v___x_22_ = 0ULL;
v___x_23_ = lean_uint16_to_uint64(v_x_21_);
v___x_24_ = lean_uint64_mix_hash(v___x_22_, v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_instHashableState_hash___boxed(lean_object* v_x_25_){
_start:
{
uint16_t v_x_26__boxed_26_; uint64_t v_res_27_; lean_object* v_r_28_; 
v_x_26__boxed_26_ = lean_unbox(v_x_25_);
v_res_27_ = l_Lean_Cadical_instHashableState_hash(v_x_26__boxed_26_);
v_r_28_ = lean_box_uint64(v_res_27_);
return v_r_28_;
}
}
static uint16_t _init_l_Lean_Cadical_State_initializing(void){
_start:
{
uint16_t v___x_31_; 
v___x_31_ = 1;
return v___x_31_;
}
}
static uint16_t _init_l_Lean_Cadical_State_configuring(void){
_start:
{
uint16_t v___x_32_; 
v___x_32_ = 2;
return v___x_32_;
}
}
static uint16_t _init_l_Lean_Cadical_State_steady(void){
_start:
{
uint16_t v___x_33_; 
v___x_33_ = 4;
return v___x_33_;
}
}
static uint16_t _init_l_Lean_Cadical_State_adding(void){
_start:
{
uint16_t v___x_34_; 
v___x_34_ = 8;
return v___x_34_;
}
}
static uint16_t _init_l_Lean_Cadical_State_solving(void){
_start:
{
uint16_t v___x_35_; 
v___x_35_ = 16;
return v___x_35_;
}
}
static uint16_t _init_l_Lean_Cadical_State_satisfied(void){
_start:
{
uint16_t v___x_36_; 
v___x_36_ = 32;
return v___x_36_;
}
}
static uint16_t _init_l_Lean_Cadical_State_unsatisfied(void){
_start:
{
uint16_t v___x_37_; 
v___x_37_ = 64;
return v___x_37_;
}
}
static uint16_t _init_l_Lean_Cadical_State_deleting(void){
_start:
{
uint16_t v___x_38_; 
v___x_38_ = 128;
return v___x_38_;
}
}
static uint16_t _init_l_Lean_Cadical_State_inconclusive(void){
_start:
{
uint16_t v___x_39_; 
v___x_39_ = 256;
return v___x_39_;
}
}
static uint16_t _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_State_ready(void){
_start:
{
uint16_t v___x_40_; 
v___x_40_ = 358;
return v___x_40_;
}
}
static uint16_t _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_State_valid(void){
_start:
{
uint16_t v___x_41_; 
v___x_41_ = 366;
return v___x_41_;
}
}
static uint16_t _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_State_invalid(void){
_start:
{
uint16_t v___x_42_; 
v___x_42_ = 129;
return v___x_42_;
}
}
static lean_object* _init_l_Lean_Cadical_State_isReady___closed__0(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = lean_unsigned_to_nat(0u);
v___x_44_ = lean_unsigned_to_nat(16u);
v___x_45_ = l_BitVec_ofNat(v___x_44_, v___x_43_);
return v___x_45_;
}
}
static uint16_t _init_l_Lean_Cadical_State_isReady___closed__1(void){
_start:
{
lean_object* v___x_46_; uint16_t v___x_47_; 
v___x_46_ = lean_obj_once(&l_Lean_Cadical_State_isReady___closed__0, &l_Lean_Cadical_State_isReady___closed__0_once, _init_l_Lean_Cadical_State_isReady___closed__0);
v___x_47_ = lean_uint16_of_nat_mk(v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_State_isReady(uint16_t v_s_48_){
_start:
{
uint16_t v___x_49_; uint16_t v___x_50_; uint16_t v___x_51_; uint8_t v___x_52_; 
v___x_49_ = 358;
v___x_50_ = lean_uint16_land(v_s_48_, v___x_49_);
v___x_51_ = lean_uint16_once(&l_Lean_Cadical_State_isReady___closed__1, &l_Lean_Cadical_State_isReady___closed__1_once, _init_l_Lean_Cadical_State_isReady___closed__1);
v___x_52_ = lean_uint16_dec_eq(v___x_50_, v___x_51_);
if (v___x_52_ == 0)
{
uint8_t v___x_53_; 
v___x_53_ = 1;
return v___x_53_;
}
else
{
uint8_t v___x_54_; 
v___x_54_ = 0;
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_State_isReady___boxed(lean_object* v_s_55_){
_start:
{
uint16_t v_s_boxed_56_; uint8_t v_res_57_; lean_object* v_r_58_; 
v_s_boxed_56_ = lean_unbox(v_s_55_);
v_res_57_ = l_Lean_Cadical_State_isReady(v_s_boxed_56_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_State_isValid(uint16_t v_s_59_){
_start:
{
uint16_t v___x_60_; uint16_t v___x_61_; uint16_t v___x_62_; uint8_t v___x_63_; 
v___x_60_ = 366;
v___x_61_ = lean_uint16_land(v_s_59_, v___x_60_);
v___x_62_ = lean_uint16_once(&l_Lean_Cadical_State_isReady___closed__1, &l_Lean_Cadical_State_isReady___closed__1_once, _init_l_Lean_Cadical_State_isReady___closed__1);
v___x_63_ = lean_uint16_dec_eq(v___x_61_, v___x_62_);
if (v___x_63_ == 0)
{
uint8_t v___x_64_; 
v___x_64_ = 1;
return v___x_64_;
}
else
{
uint8_t v___x_65_; 
v___x_65_ = 0;
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_State_isValid___boxed(lean_object* v_s_66_){
_start:
{
uint16_t v_s_boxed_67_; uint8_t v_res_68_; lean_object* v_r_69_; 
v_s_boxed_67_ = lean_unbox(v_s_66_);
v_res_68_ = l_Lean_Cadical_State_isValid(v_s_boxed_67_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_State_isInvalid(uint16_t v_s_70_){
_start:
{
uint16_t v___x_71_; uint16_t v___x_72_; uint16_t v___x_73_; uint8_t v___x_74_; 
v___x_71_ = 129;
v___x_72_ = lean_uint16_land(v_s_70_, v___x_71_);
v___x_73_ = lean_uint16_once(&l_Lean_Cadical_State_isReady___closed__1, &l_Lean_Cadical_State_isReady___closed__1_once, _init_l_Lean_Cadical_State_isReady___closed__1);
v___x_74_ = lean_uint16_dec_eq(v___x_72_, v___x_73_);
if (v___x_74_ == 0)
{
uint8_t v___x_75_; 
v___x_75_ = 1;
return v___x_75_;
}
else
{
uint8_t v___x_76_; 
v___x_76_ = 0;
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_State_isInvalid___boxed(lean_object* v_s_77_){
_start:
{
uint16_t v_s_boxed_78_; uint8_t v_res_79_; lean_object* v_r_80_; 
v_s_boxed_78_ = lean_unbox(v_s_77_);
v_res_79_ = l_Lean_Cadical_State_isInvalid(v_s_boxed_78_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_State_toString(uint16_t v_s_90_){
_start:
{
uint16_t v___x_91_; uint8_t v___x_92_; 
v___x_91_ = 1;
v___x_92_ = lean_uint16_dec_eq(v_s_90_, v___x_91_);
if (v___x_92_ == 0)
{
uint16_t v___x_93_; uint8_t v___x_94_; 
v___x_93_ = 2;
v___x_94_ = lean_uint16_dec_eq(v_s_90_, v___x_93_);
if (v___x_94_ == 0)
{
uint16_t v___x_95_; uint8_t v___x_96_; 
v___x_95_ = 4;
v___x_96_ = lean_uint16_dec_eq(v_s_90_, v___x_95_);
if (v___x_96_ == 0)
{
uint16_t v___x_97_; uint8_t v___x_98_; 
v___x_97_ = 8;
v___x_98_ = lean_uint16_dec_eq(v_s_90_, v___x_97_);
if (v___x_98_ == 0)
{
uint16_t v___x_99_; uint8_t v___x_100_; 
v___x_99_ = 16;
v___x_100_ = lean_uint16_dec_eq(v_s_90_, v___x_99_);
if (v___x_100_ == 0)
{
uint16_t v___x_101_; uint8_t v___x_102_; 
v___x_101_ = 32;
v___x_102_ = lean_uint16_dec_eq(v_s_90_, v___x_101_);
if (v___x_102_ == 0)
{
uint16_t v___x_103_; uint8_t v___x_104_; 
v___x_103_ = 64;
v___x_104_ = lean_uint16_dec_eq(v_s_90_, v___x_103_);
if (v___x_104_ == 0)
{
uint16_t v___x_105_; uint8_t v___x_106_; 
v___x_105_ = 256;
v___x_106_ = lean_uint16_dec_eq(v_s_90_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
v___x_107_ = ((lean_object*)(l_Lean_Cadical_State_toString___closed__0));
return v___x_107_;
}
else
{
lean_object* v___x_108_; 
v___x_108_ = ((lean_object*)(l_Lean_Cadical_State_toString___closed__1));
return v___x_108_;
}
}
else
{
lean_object* v___x_109_; 
v___x_109_ = ((lean_object*)(l_Lean_Cadical_State_toString___closed__2));
return v___x_109_;
}
}
else
{
lean_object* v___x_110_; 
v___x_110_ = ((lean_object*)(l_Lean_Cadical_State_toString___closed__3));
return v___x_110_;
}
}
else
{
lean_object* v___x_111_; 
v___x_111_ = ((lean_object*)(l_Lean_Cadical_State_toString___closed__4));
return v___x_111_;
}
}
else
{
lean_object* v___x_112_; 
v___x_112_ = ((lean_object*)(l_Lean_Cadical_State_toString___closed__5));
return v___x_112_;
}
}
else
{
lean_object* v___x_113_; 
v___x_113_ = ((lean_object*)(l_Lean_Cadical_State_toString___closed__6));
return v___x_113_;
}
}
else
{
lean_object* v___x_114_; 
v___x_114_ = ((lean_object*)(l_Lean_Cadical_State_toString___closed__7));
return v___x_114_;
}
}
else
{
lean_object* v___x_115_; 
v___x_115_ = ((lean_object*)(l_Lean_Cadical_State_toString___closed__8));
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_State_toString___boxed(lean_object* v_s_116_){
_start:
{
uint16_t v_s_boxed_117_; lean_object* v_res_118_; 
v_s_boxed_117_ = lean_unbox(v_s_116_);
v_res_118_ = l_Lean_Cadical_State_toString(v_s_boxed_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorIdx___impl(uint8_t v_x_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_box(v_x_121_);
v___x_123_ = lean_obj_tag_nat(v___x_122_);
lean_dec(v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorIdx___impl___boxed(lean_object* v_x_124_){
_start:
{
uint8_t v_x_4__boxed_125_; lean_object* v_res_126_; 
v_x_4__boxed_125_ = lean_unbox(v_x_124_);
v_res_126_ = l_Lean_Cadical_Status_ctorIdx___impl(v_x_4__boxed_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorElim___redArg(lean_object* v_k_127_){
_start:
{
lean_inc(v_k_127_);
return v_k_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorElim___redArg___boxed(lean_object* v_k_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_Cadical_Status_ctorElim___redArg(v_k_128_);
lean_dec(v_k_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorElim(lean_object* v_motive_130_, lean_object* v_ctorIdx_131_, uint8_t v_t_132_, lean_object* v_h_133_, lean_object* v_k_134_){
_start:
{
lean_inc(v_k_134_);
return v_k_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorElim___boxed(lean_object* v_motive_135_, lean_object* v_ctorIdx_136_, lean_object* v_t_137_, lean_object* v_h_138_, lean_object* v_k_139_){
_start:
{
uint8_t v_t_boxed_140_; lean_object* v_res_141_; 
v_t_boxed_140_ = lean_unbox(v_t_137_);
v_res_141_ = l_Lean_Cadical_Status_ctorElim(v_motive_135_, v_ctorIdx_136_, v_t_boxed_140_, v_h_138_, v_k_139_);
lean_dec(v_k_139_);
lean_dec(v_ctorIdx_136_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_satisfiable_elim___redArg(lean_object* v_satisfiable_142_){
_start:
{
lean_inc(v_satisfiable_142_);
return v_satisfiable_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_satisfiable_elim___redArg___boxed(lean_object* v_satisfiable_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Cadical_Status_satisfiable_elim___redArg(v_satisfiable_143_);
lean_dec(v_satisfiable_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_satisfiable_elim(lean_object* v_motive_145_, uint8_t v_t_146_, lean_object* v_h_147_, lean_object* v_satisfiable_148_){
_start:
{
lean_inc(v_satisfiable_148_);
return v_satisfiable_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_satisfiable_elim___boxed(lean_object* v_motive_149_, lean_object* v_t_150_, lean_object* v_h_151_, lean_object* v_satisfiable_152_){
_start:
{
uint8_t v_t_boxed_153_; lean_object* v_res_154_; 
v_t_boxed_153_ = lean_unbox(v_t_150_);
v_res_154_ = l_Lean_Cadical_Status_satisfiable_elim(v_motive_149_, v_t_boxed_153_, v_h_151_, v_satisfiable_152_);
lean_dec(v_satisfiable_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unsatisfiable_elim___redArg(lean_object* v_unsatisfiable_155_){
_start:
{
lean_inc(v_unsatisfiable_155_);
return v_unsatisfiable_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unsatisfiable_elim___redArg___boxed(lean_object* v_unsatisfiable_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_Cadical_Status_unsatisfiable_elim___redArg(v_unsatisfiable_156_);
lean_dec(v_unsatisfiable_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unsatisfiable_elim(lean_object* v_motive_158_, uint8_t v_t_159_, lean_object* v_h_160_, lean_object* v_unsatisfiable_161_){
_start:
{
lean_inc(v_unsatisfiable_161_);
return v_unsatisfiable_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unsatisfiable_elim___boxed(lean_object* v_motive_162_, lean_object* v_t_163_, lean_object* v_h_164_, lean_object* v_unsatisfiable_165_){
_start:
{
uint8_t v_t_boxed_166_; lean_object* v_res_167_; 
v_t_boxed_166_ = lean_unbox(v_t_163_);
v_res_167_ = l_Lean_Cadical_Status_unsatisfiable_elim(v_motive_162_, v_t_boxed_166_, v_h_164_, v_unsatisfiable_165_);
lean_dec(v_unsatisfiable_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unknown_elim___redArg(lean_object* v_unknown_168_){
_start:
{
lean_inc(v_unknown_168_);
return v_unknown_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unknown_elim___redArg___boxed(lean_object* v_unknown_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_Cadical_Status_unknown_elim___redArg(v_unknown_169_);
lean_dec(v_unknown_169_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unknown_elim(lean_object* v_motive_171_, uint8_t v_t_172_, lean_object* v_h_173_, lean_object* v_unknown_174_){
_start:
{
lean_inc(v_unknown_174_);
return v_unknown_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unknown_elim___boxed(lean_object* v_motive_175_, lean_object* v_t_176_, lean_object* v_h_177_, lean_object* v_unknown_178_){
_start:
{
uint8_t v_t_boxed_179_; lean_object* v_res_180_; 
v_t_boxed_179_ = lean_unbox(v_t_176_);
v_res_180_ = l_Lean_Cadical_Status_unknown_elim(v_motive_175_, v_t_boxed_179_, v_h_177_, v_unknown_178_);
lean_dec(v_unknown_178_);
return v_res_180_;
}
}
static uint8_t _init_l_Lean_Cadical_instInhabitedStatus_default(void){
_start:
{
uint8_t v___x_181_; 
v___x_181_ = 0;
return v___x_181_;
}
}
static uint8_t _init_l_Lean_Cadical_instInhabitedStatus(void){
_start:
{
uint8_t v___x_182_; 
v___x_182_ = 0;
return v___x_182_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Status_ofNat(lean_object* v_n_183_){
_start:
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_nat_dec_le(v_n_183_, v___x_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_dec_le(v_n_183_, v___x_186_);
if (v___x_187_ == 0)
{
uint8_t v___x_188_; 
v___x_188_ = 2;
return v___x_188_;
}
else
{
uint8_t v___x_189_; 
v___x_189_ = 1;
return v___x_189_;
}
}
else
{
uint8_t v___x_190_; 
v___x_190_ = 0;
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ofNat___boxed(lean_object* v_n_191_){
_start:
{
uint8_t v_res_192_; lean_object* v_r_193_; 
v_res_192_ = l_Lean_Cadical_Status_ofNat(v_n_191_);
lean_dec(v_n_191_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_instDecidableEqStatus(uint8_t v_x_194_, uint8_t v_y_195_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_196_ = lean_box(v_x_194_);
v___x_197_ = lean_obj_tag_nat(v___x_196_);
lean_dec(v___x_196_);
v___x_198_ = lean_box(v_y_195_);
v___x_199_ = lean_obj_tag_nat(v___x_198_);
lean_dec(v___x_198_);
v___x_200_ = lean_nat_dec_eq(v___x_197_, v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_instDecidableEqStatus___boxed(lean_object* v_x_201_, lean_object* v_y_202_){
_start:
{
uint8_t v_x_23__boxed_203_; uint8_t v_y_24__boxed_204_; uint8_t v_res_205_; lean_object* v_r_206_; 
v_x_23__boxed_203_ = lean_unbox(v_x_201_);
v_y_24__boxed_204_ = lean_unbox(v_y_202_);
v_res_205_ = l_Lean_Cadical_instDecidableEqStatus(v_x_23__boxed_203_, v_y_24__boxed_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT uint64_t l_Lean_Cadical_instHashableStatus_hash(uint8_t v_x_207_){
_start:
{
switch(v_x_207_)
{
case 0:
{
uint64_t v___x_208_; 
v___x_208_ = 0ULL;
return v___x_208_;
}
case 1:
{
uint64_t v___x_209_; 
v___x_209_ = 1ULL;
return v___x_209_;
}
default: 
{
uint64_t v___x_210_; 
v___x_210_ = 2ULL;
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_instHashableStatus_hash___boxed(lean_object* v_x_211_){
_start:
{
uint8_t v_x_40__boxed_212_; uint64_t v_res_213_; lean_object* v_r_214_; 
v_x_40__boxed_212_ = lean_unbox(v_x_211_);
v_res_213_ = l_Lean_Cadical_instHashableStatus_hash(v_x_40__boxed_212_);
v_r_214_ = lean_box_uint64(v_res_213_);
return v_r_214_;
}
}
static lean_object* _init_l_Lean_Cadical_instReprStatus_repr___closed__6(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_unsigned_to_nat(2u);
v___x_227_ = lean_nat_to_int(v___x_226_);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_Cadical_instReprStatus_repr___closed__7(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = lean_nat_to_int(v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_instReprStatus_repr(uint8_t v_x_230_, lean_object* v_prec_231_){
_start:
{
lean_object* v___y_233_; lean_object* v___y_240_; lean_object* v___y_247_; 
switch(v_x_230_)
{
case 0:
{
lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_253_ = lean_unsigned_to_nat(1024u);
v___x_254_ = lean_nat_dec_le(v___x_253_, v_prec_231_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
v___x_255_ = lean_obj_once(&l_Lean_Cadical_instReprStatus_repr___closed__6, &l_Lean_Cadical_instReprStatus_repr___closed__6_once, _init_l_Lean_Cadical_instReprStatus_repr___closed__6);
v___y_233_ = v___x_255_;
goto v___jp_232_;
}
else
{
lean_object* v___x_256_; 
v___x_256_ = lean_obj_once(&l_Lean_Cadical_instReprStatus_repr___closed__7, &l_Lean_Cadical_instReprStatus_repr___closed__7_once, _init_l_Lean_Cadical_instReprStatus_repr___closed__7);
v___y_233_ = v___x_256_;
goto v___jp_232_;
}
}
case 1:
{
lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_unsigned_to_nat(1024u);
v___x_258_ = lean_nat_dec_le(v___x_257_, v_prec_231_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
v___x_259_ = lean_obj_once(&l_Lean_Cadical_instReprStatus_repr___closed__6, &l_Lean_Cadical_instReprStatus_repr___closed__6_once, _init_l_Lean_Cadical_instReprStatus_repr___closed__6);
v___y_240_ = v___x_259_;
goto v___jp_239_;
}
else
{
lean_object* v___x_260_; 
v___x_260_ = lean_obj_once(&l_Lean_Cadical_instReprStatus_repr___closed__7, &l_Lean_Cadical_instReprStatus_repr___closed__7_once, _init_l_Lean_Cadical_instReprStatus_repr___closed__7);
v___y_240_ = v___x_260_;
goto v___jp_239_;
}
}
default: 
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = lean_unsigned_to_nat(1024u);
v___x_262_ = lean_nat_dec_le(v___x_261_, v_prec_231_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; 
v___x_263_ = lean_obj_once(&l_Lean_Cadical_instReprStatus_repr___closed__6, &l_Lean_Cadical_instReprStatus_repr___closed__6_once, _init_l_Lean_Cadical_instReprStatus_repr___closed__6);
v___y_247_ = v___x_263_;
goto v___jp_246_;
}
else
{
lean_object* v___x_264_; 
v___x_264_ = lean_obj_once(&l_Lean_Cadical_instReprStatus_repr___closed__7, &l_Lean_Cadical_instReprStatus_repr___closed__7_once, _init_l_Lean_Cadical_instReprStatus_repr___closed__7);
v___y_247_ = v___x_264_;
goto v___jp_246_;
}
}
}
v___jp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_234_ = ((lean_object*)(l_Lean_Cadical_instReprStatus_repr___closed__1));
lean_inc(v___y_233_);
v___x_235_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_235_, 0, v___y_233_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = 0;
v___x_237_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*1, v___x_236_);
v___x_238_ = l_Repr_addAppParen(v___x_237_, v_prec_231_);
return v___x_238_;
}
v___jp_239_:
{
lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_241_ = ((lean_object*)(l_Lean_Cadical_instReprStatus_repr___closed__3));
lean_inc(v___y_240_);
v___x_242_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_242_, 0, v___y_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = 0;
v___x_244_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*1, v___x_243_);
v___x_245_ = l_Repr_addAppParen(v___x_244_, v_prec_231_);
return v___x_245_;
}
v___jp_246_:
{
lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_248_ = ((lean_object*)(l_Lean_Cadical_instReprStatus_repr___closed__5));
lean_inc(v___y_247_);
v___x_249_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_249_, 0, v___y_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = 0;
v___x_251_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*1, v___x_250_);
v___x_252_ = l_Repr_addAppParen(v___x_251_, v_prec_231_);
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_instReprStatus_repr___boxed(lean_object* v_x_265_, lean_object* v_prec_266_){
_start:
{
uint8_t v_x_171__boxed_267_; lean_object* v_res_268_; 
v_x_171__boxed_267_ = lean_unbox(v_x_265_);
v_res_268_ = l_Lean_Cadical_instReprStatus_repr(v_x_171__boxed_267_, v_prec_266_);
lean_dec(v_prec_266_);
return v_res_268_;
}
}
static uint32_t _init_l_Lean_Cadical_Status_toInt32___closed__0(void){
_start:
{
lean_object* v___x_271_; uint32_t v___x_272_; 
v___x_271_ = lean_unsigned_to_nat(10u);
v___x_272_ = lean_int32_of_nat(v___x_271_);
return v___x_272_;
}
}
static uint32_t _init_l_Lean_Cadical_Status_toInt32___closed__1(void){
_start:
{
lean_object* v___x_273_; uint32_t v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(20u);
v___x_274_ = lean_int32_of_nat(v___x_273_);
return v___x_274_;
}
}
static uint32_t _init_l_Lean_Cadical_Status_toInt32___closed__2(void){
_start:
{
lean_object* v___x_275_; uint32_t v___x_276_; 
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_int32_of_nat(v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT uint32_t l_Lean_Cadical_Status_toInt32(uint8_t v_x_277_){
_start:
{
switch(v_x_277_)
{
case 0:
{
uint32_t v___x_278_; 
v___x_278_ = lean_uint32_once(&l_Lean_Cadical_Status_toInt32___closed__0, &l_Lean_Cadical_Status_toInt32___closed__0_once, _init_l_Lean_Cadical_Status_toInt32___closed__0);
return v___x_278_;
}
case 1:
{
uint32_t v___x_279_; 
v___x_279_ = lean_uint32_once(&l_Lean_Cadical_Status_toInt32___closed__1, &l_Lean_Cadical_Status_toInt32___closed__1_once, _init_l_Lean_Cadical_Status_toInt32___closed__1);
return v___x_279_;
}
default: 
{
uint32_t v___x_280_; 
v___x_280_ = lean_uint32_once(&l_Lean_Cadical_Status_toInt32___closed__2, &l_Lean_Cadical_Status_toInt32___closed__2_once, _init_l_Lean_Cadical_Status_toInt32___closed__2);
return v___x_280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_toInt32___boxed(lean_object* v_x_281_){
_start:
{
uint8_t v_x_52__boxed_282_; uint32_t v_res_283_; lean_object* v_r_284_; 
v_x_52__boxed_282_ = lean_unbox(v_x_281_);
v_res_283_ = l_Lean_Cadical_Status_toInt32(v_x_52__boxed_282_);
v_r_284_ = lean_box_uint32(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_toString(uint8_t v_x_288_){
_start:
{
switch(v_x_288_)
{
case 0:
{
lean_object* v___x_289_; 
v___x_289_ = ((lean_object*)(l_Lean_Cadical_Status_toString___closed__0));
return v___x_289_;
}
case 1:
{
lean_object* v___x_290_; 
v___x_290_ = ((lean_object*)(l_Lean_Cadical_Status_toString___closed__1));
return v___x_290_;
}
default: 
{
lean_object* v___x_291_; 
v___x_291_ = ((lean_object*)(l_Lean_Cadical_Status_toString___closed__2));
return v___x_291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_toString___boxed(lean_object* v_x_292_){
_start:
{
uint8_t v_x_31__boxed_293_; lean_object* v_res_294_; 
v_x_31__boxed_293_ = lean_unbox(v_x_292_);
v_res_294_ = l_Lean_Cadical_Status_toString(v_x_31__boxed_293_);
return v_res_294_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Cadical_Basic_0__Lean_Cadical_Status_ofInternal(uint8_t v_s_297_){
_start:
{
switch(v_s_297_)
{
case 0:
{
uint8_t v___x_298_; 
v___x_298_ = 0;
return v___x_298_;
}
case 1:
{
uint8_t v___x_299_; 
v___x_299_ = 1;
return v___x_299_;
}
default: 
{
uint8_t v___x_300_; 
v___x_300_ = 2;
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Cadical_Basic_0__Lean_Cadical_Status_ofInternal___boxed(lean_object* v_s_301_){
_start:
{
uint8_t v_s_boxed_302_; uint8_t v_res_303_; lean_object* v_r_304_; 
v_s_boxed_302_ = lean_unbox(v_s_301_);
v_res_303_ = l___private_Lean_Cadical_Basic_0__Lean_Cadical_Status_ofInternal(v_s_boxed_302_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
static uint32_t _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__0(void){
_start:
{
lean_object* v___x_305_; uint32_t v___x_306_; 
v___x_305_ = lean_unsigned_to_nat(2147483647u);
v___x_306_ = lean_int32_of_nat(v___x_305_);
return v___x_306_;
}
}
static lean_object* _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__1(void){
_start:
{
uint32_t v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_uint32_once(&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__0, &l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__0_once, _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__0);
v___x_308_ = lean_int32_to_int(v___x_307_);
return v___x_308_;
}
}
static lean_object* _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_obj_once(&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__1, &l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__1_once, _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__1);
v___x_310_ = l_Int_toNat(v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit(lean_object* v_lit_314_, uint8_t v_pol_315_){
_start:
{
lean_object* v___x_317_; lean_object* v_lit_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_317_ = lean_unsigned_to_nat(1u);
v_lit_318_ = lean_nat_add(v_lit_314_, v___x_317_);
v___x_319_ = lean_obj_once(&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2, &l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2_once, _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2);
v___x_320_ = lean_nat_dec_lt(v___x_319_, v_lit_318_);
if (v___x_320_ == 0)
{
uint32_t v_lit_321_; 
v_lit_321_ = lean_int32_of_nat(v_lit_318_);
lean_dec(v_lit_318_);
if (v_pol_315_ == 0)
{
uint32_t v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_int32_neg(v_lit_321_);
v___x_323_ = lean_box_uint32(v___x_322_);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
else
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_box_uint32(v_lit_321_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec(v_lit_318_);
v___x_327_ = ((lean_object*)(l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__4));
v___x_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___boxed(lean_object* v_lit_329_, lean_object* v_pol_330_, lean_object* v_a_331_){
_start:
{
uint8_t v_pol_boxed_332_; lean_object* v_res_333_; 
v_pol_boxed_332_ = lean_unbox(v_pol_330_);
v_res_333_ = l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit(v_lit_329_, v_pol_boxed_332_);
lean_dec(v_lit_329_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_new(){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_cadical_solver_new();
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_new___boxed(lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Cadical_Solver_new();
return v_res_338_;
}
}
LEAN_EXPORT uint16_t l_Lean_Cadical_Solver_state(lean_object* v_s_339_){
_start:
{
lean_object* v_solver_341_; uint16_t v___x_342_; 
v_solver_341_ = lean_ctor_get(v_s_339_, 0);
v___x_342_ = lean_cadical_solver_state(v_solver_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_state___boxed(lean_object* v_s_343_, lean_object* v_a_344_){
_start:
{
uint16_t v_res_345_; lean_object* v_r_346_; 
v_res_345_ = l_Lean_Cadical_Solver_state(v_s_343_);
lean_dec_ref(v_s_343_);
v_r_346_ = lean_box(v_res_345_);
return v_r_346_;
}
}
static lean_object* _init_l_panic___at___00Lean_Cadical_Solver_clause_spec__1___closed__0(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = l_instInhabitedError;
v___x_348_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_348_, 0, lean_box(0));
lean_closure_set(v___x_348_, 1, lean_box(0));
lean_closure_set(v___x_348_, 2, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_clause_spec__1(lean_object* v_msg_349_){
_start:
{
lean_object* v___x_351_; lean_object* v___x_806__overap_352_; lean_object* v___x_353_; 
v___x_351_ = lean_obj_once(&l_panic___at___00Lean_Cadical_Solver_clause_spec__1___closed__0, &l_panic___at___00Lean_Cadical_Solver_clause_spec__1___closed__0_once, _init_l_panic___at___00Lean_Cadical_Solver_clause_spec__1___closed__0);
v___x_806__overap_352_ = lean_panic_fn_borrowed(v___x_351_, v_msg_349_);
v___x_353_ = lean_apply_1(v___x_806__overap_352_, lean_box(0));
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_clause_spec__1___boxed(lean_object* v_msg_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_panic___at___00Lean_Cadical_Solver_clause_spec__1(v_msg_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Lean_Cadical_Solver_clause_spec__0(lean_object* v_s_357_, lean_object* v_c_358_, size_t v_sz_359_, size_t v_i_360_, lean_object* v_b_361_){
_start:
{
uint8_t v___x_363_; 
v___x_363_ = lean_usize_dec_lt(v_i_360_, v_sz_359_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v_b_361_);
return v___x_364_;
}
else
{
lean_object* v_atoms_365_; lean_object* v_polarities_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v_lit_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v_atoms_365_ = lean_ctor_get(v_c_358_, 0);
v_polarities_366_ = lean_ctor_get(v_c_358_, 1);
v___x_367_ = lean_array_uget_borrowed(v_atoms_365_, v_i_360_);
v___x_368_ = lean_unsigned_to_nat(1u);
v_lit_369_ = lean_nat_add(v___x_367_, v___x_368_);
v___x_370_ = lean_obj_once(&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2, &l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2_once, _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2);
v___x_371_ = lean_nat_dec_lt(v___x_370_, v_lit_369_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; uint32_t v_a_374_; uint8_t v___x_380_; uint8_t v___x_381_; uint8_t v___x_382_; uint32_t v_lit_383_; 
v___x_372_ = lean_box(0);
v___x_380_ = lean_byte_array_uget(v_polarities_366_, v_i_360_);
v___x_381_ = 1;
v___x_382_ = lean_uint8_dec_eq(v___x_380_, v___x_381_);
v_lit_383_ = lean_int32_of_nat(v_lit_369_);
lean_dec(v_lit_369_);
if (v___x_382_ == 0)
{
uint32_t v___x_384_; 
v___x_384_ = lean_int32_neg(v_lit_383_);
v_a_374_ = v___x_384_;
goto v___jp_373_;
}
else
{
v_a_374_ = v_lit_383_;
goto v___jp_373_;
}
v___jp_373_:
{
lean_object* v_solver_375_; lean_object* v___x_376_; size_t v___x_377_; size_t v___x_378_; 
v_solver_375_ = lean_ctor_get(v_s_357_, 0);
v___x_376_ = lean_cadical_solver_add(v_solver_375_, v_a_374_);
v___x_377_ = ((size_t)1ULL);
v___x_378_ = lean_usize_add(v_i_360_, v___x_377_);
v_i_360_ = v___x_378_;
v_b_361_ = v___x_372_;
goto _start;
}
}
else
{
lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec(v_lit_369_);
v___x_385_ = ((lean_object*)(l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__4));
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Lean_Cadical_Solver_clause_spec__0___boxed(lean_object* v_s_387_, lean_object* v_c_388_, lean_object* v_sz_389_, lean_object* v_i_390_, lean_object* v_b_391_, lean_object* v___y_392_){
_start:
{
size_t v_sz_boxed_393_; size_t v_i_boxed_394_; lean_object* v_res_395_; 
v_sz_boxed_393_ = lean_unbox_usize(v_sz_389_);
lean_dec(v_sz_389_);
v_i_boxed_394_ = lean_unbox_usize(v_i_390_);
lean_dec(v_i_390_);
v_res_395_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Lean_Cadical_Solver_clause_spec__0(v_s_387_, v_c_388_, v_sz_boxed_393_, v_i_boxed_394_, v_b_391_);
lean_dec_ref(v_c_388_);
lean_dec_ref(v_s_387_);
return v_res_395_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_clause___closed__3(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_399_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__2));
v___x_400_ = lean_unsigned_to_nat(2u);
v___x_401_ = lean_unsigned_to_nat(176u);
v___x_402_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__1));
v___x_403_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_404_ = l_mkPanicMessageWithDecl(v___x_403_, v___x_402_, v___x_401_, v___x_400_, v___x_399_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_clause(lean_object* v_s_405_, lean_object* v_clause_406_){
_start:
{
uint16_t v___x_408_; uint16_t v___x_409_; uint16_t v___x_410_; uint16_t v___x_411_; uint8_t v___x_412_; 
v___x_408_ = l_Lean_Cadical_Solver_state(v_s_405_);
v___x_409_ = 366;
v___x_410_ = lean_uint16_land(v___x_408_, v___x_409_);
v___x_411_ = lean_uint16_once(&l_Lean_Cadical_State_isReady___closed__1, &l_Lean_Cadical_State_isReady___closed__1_once, _init_l_Lean_Cadical_State_isReady___closed__1);
v___x_412_ = lean_uint16_dec_eq(v___x_410_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v_atoms_413_; lean_object* v___x_414_; size_t v_sz_415_; size_t v___x_416_; lean_object* v___x_417_; 
v_atoms_413_ = lean_ctor_get(v_clause_406_, 0);
v___x_414_ = lean_box(0);
v_sz_415_ = lean_array_size(v_atoms_413_);
v___x_416_ = ((size_t)0ULL);
v___x_417_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Lean_Cadical_Solver_clause_spec__0(v_s_405_, v_clause_406_, v_sz_415_, v___x_416_, v___x_414_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_427_; 
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_427_ == 0)
{
lean_object* v_unused_428_; 
v_unused_428_ = lean_ctor_get(v___x_417_, 0);
lean_dec(v_unused_428_);
v___x_419_ = v___x_417_;
v_isShared_420_ = v_isSharedCheck_427_;
goto v_resetjp_418_;
}
else
{
lean_dec(v___x_417_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_427_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v_solver_421_; uint32_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
v_solver_421_ = lean_ctor_get(v_s_405_, 0);
v___x_422_ = lean_uint32_once(&l_Lean_Cadical_Status_toInt32___closed__2, &l_Lean_Cadical_Status_toInt32___closed__2_once, _init_l_Lean_Cadical_Status_toInt32___closed__2);
v___x_423_ = lean_cadical_solver_add(v_solver_421_, v___x_422_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_423_);
v___x_425_ = v___x_419_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
else
{
return v___x_417_;
}
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_obj_once(&l_Lean_Cadical_Solver_clause___closed__3, &l_Lean_Cadical_Solver_clause___closed__3_once, _init_l_Lean_Cadical_Solver_clause___closed__3);
v___x_430_ = l_panic___at___00Lean_Cadical_Solver_clause_spec__1(v___x_429_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_clause___boxed(lean_object* v_s_431_, lean_object* v_clause_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_Cadical_Solver_clause(v_s_431_, v_clause_432_);
lean_dec_ref(v_clause_432_);
lean_dec_ref(v_s_431_);
return v_res_434_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_inconsistent(lean_object* v_s_435_){
_start:
{
lean_object* v_solver_437_; uint8_t v___x_438_; 
v_solver_437_ = lean_ctor_get(v_s_435_, 0);
v___x_438_ = lean_cadical_solver_inconsistent(v_solver_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_inconsistent___boxed(lean_object* v_s_439_, lean_object* v_a_440_){
_start:
{
uint8_t v_res_441_; lean_object* v_r_442_; 
v_res_441_ = l_Lean_Cadical_Solver_inconsistent(v_s_439_);
lean_dec_ref(v_s_439_);
v_r_442_ = lean_box(v_res_441_);
return v_r_442_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_assume___closed__2(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_445_ = ((lean_object*)(l_Lean_Cadical_Solver_assume___closed__1));
v___x_446_ = lean_unsigned_to_nat(2u);
v___x_447_ = lean_unsigned_to_nat(191u);
v___x_448_ = ((lean_object*)(l_Lean_Cadical_Solver_assume___closed__0));
v___x_449_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_450_ = l_mkPanicMessageWithDecl(v___x_449_, v___x_448_, v___x_447_, v___x_446_, v___x_445_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_assume(lean_object* v_s_451_, lean_object* v_lit_452_, uint8_t v_pol_453_){
_start:
{
uint32_t v_a_456_; uint16_t v___x_466_; uint16_t v___x_467_; uint16_t v___x_468_; uint16_t v___x_469_; uint8_t v___x_470_; 
v___x_466_ = l_Lean_Cadical_Solver_state(v_s_451_);
v___x_467_ = 358;
v___x_468_ = lean_uint16_land(v___x_466_, v___x_467_);
v___x_469_ = lean_uint16_once(&l_Lean_Cadical_State_isReady___closed__1, &l_Lean_Cadical_State_isReady___closed__1_once, _init_l_Lean_Cadical_State_isReady___closed__1);
v___x_470_ = lean_uint16_dec_eq(v___x_468_, v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v_lit_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_471_ = lean_unsigned_to_nat(1u);
v_lit_472_ = lean_nat_add(v_lit_452_, v___x_471_);
v___x_473_ = lean_obj_once(&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2, &l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2_once, _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2);
v___x_474_ = lean_nat_dec_lt(v___x_473_, v_lit_472_);
if (v___x_474_ == 0)
{
uint32_t v_lit_475_; 
v_lit_475_ = lean_int32_of_nat(v_lit_472_);
lean_dec(v_lit_472_);
if (v_pol_453_ == 0)
{
uint32_t v___x_476_; 
v___x_476_ = lean_int32_neg(v_lit_475_);
v_a_456_ = v___x_476_;
goto v___jp_455_;
}
else
{
v_a_456_ = v_lit_475_;
goto v___jp_455_;
}
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_lit_472_);
lean_dec_ref(v_s_451_);
v___x_477_ = ((lean_object*)(l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__4));
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; 
lean_dec_ref(v_s_451_);
v___x_479_ = lean_obj_once(&l_Lean_Cadical_Solver_assume___closed__2, &l_Lean_Cadical_Solver_assume___closed__2_once, _init_l_Lean_Cadical_Solver_assume___closed__2);
v___x_480_ = l_panic___at___00Lean_Cadical_Solver_clause_spec__1(v___x_479_);
return v___x_480_;
}
v___jp_455_:
{
lean_object* v_solver_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_465_; 
v_solver_457_ = lean_ctor_get(v_s_451_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v_s_451_);
if (v_isSharedCheck_465_ == 0)
{
v___x_459_ = v_s_451_;
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_solver_457_);
lean_dec(v_s_451_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = lean_cadical_solver_assume(v_solver_457_, v_a_456_);
lean_dec(v_solver_457_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_461_);
v___x_463_ = v___x_459_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_assume___boxed(lean_object* v_s_481_, lean_object* v_lit_482_, lean_object* v_pol_483_, lean_object* v_a_484_){
_start:
{
uint8_t v_pol_boxed_485_; lean_object* v_res_486_; 
v_pol_boxed_485_ = lean_unbox(v_pol_483_);
v_res_486_ = l_Lean_Cadical_Solver_assume(v_s_481_, v_lit_482_, v_pol_boxed_485_);
lean_dec(v_lit_482_);
return v_res_486_;
}
}
static lean_object* _init_l_panic___at___00Lean_Cadical_Solver_solve_spec__0___closed__0(void){
_start:
{
uint8_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_487_ = 0;
v___x_488_ = l_instMonadBaseIO;
v___x_489_ = lean_box(v___x_487_);
v___x_490_ = l_instInhabitedOfMonad___redArg(v___x_488_, v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Cadical_Solver_solve_spec__0(lean_object* v_msg_491_){
_start:
{
lean_object* v___x_493_; lean_object* v___x_211__overap_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_493_ = lean_obj_once(&l_panic___at___00Lean_Cadical_Solver_solve_spec__0___closed__0, &l_panic___at___00Lean_Cadical_Solver_solve_spec__0___closed__0_once, _init_l_panic___at___00Lean_Cadical_Solver_solve_spec__0___closed__0);
v___x_211__overap_494_ = lean_panic_fn_borrowed(v___x_493_, v_msg_491_);
v___x_495_ = lean_apply_1(v___x_211__overap_494_, lean_box(0));
v___x_496_ = lean_unbox(v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_solve_spec__0___boxed(lean_object* v_msg_497_, lean_object* v___y_498_){
_start:
{
uint8_t v_res_499_; lean_object* v_r_500_; 
v_res_499_ = l_panic___at___00Lean_Cadical_Solver_solve_spec__0(v_msg_497_);
v_r_500_ = lean_box(v_res_499_);
return v_r_500_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_solve___closed__2(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_503_ = ((lean_object*)(l_Lean_Cadical_Solver_solve___closed__1));
v___x_504_ = lean_unsigned_to_nat(2u);
v___x_505_ = lean_unsigned_to_nat(198u);
v___x_506_ = ((lean_object*)(l_Lean_Cadical_Solver_solve___closed__0));
v___x_507_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_508_ = l_mkPanicMessageWithDecl(v___x_507_, v___x_506_, v___x_505_, v___x_504_, v___x_503_);
return v___x_508_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_solve(lean_object* v_s_509_){
_start:
{
uint16_t v___x_511_; uint16_t v___x_512_; uint16_t v___x_513_; uint16_t v___x_514_; uint8_t v___x_515_; 
v___x_511_ = l_Lean_Cadical_Solver_state(v_s_509_);
v___x_512_ = 358;
v___x_513_ = lean_uint16_land(v___x_511_, v___x_512_);
v___x_514_ = lean_uint16_once(&l_Lean_Cadical_State_isReady___closed__1, &l_Lean_Cadical_State_isReady___closed__1_once, _init_l_Lean_Cadical_State_isReady___closed__1);
v___x_515_ = lean_uint16_dec_eq(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v_solver_516_; uint8_t v___x_517_; 
v_solver_516_ = lean_ctor_get(v_s_509_, 0);
v___x_517_ = lean_cadical_solver_solve(v_solver_516_);
switch(v___x_517_)
{
case 0:
{
uint8_t v___x_518_; 
v___x_518_ = 0;
return v___x_518_;
}
case 1:
{
uint8_t v___x_519_; 
v___x_519_ = 1;
return v___x_519_;
}
default: 
{
uint8_t v___x_520_; 
v___x_520_ = 2;
return v___x_520_;
}
}
}
else
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = lean_obj_once(&l_Lean_Cadical_Solver_solve___closed__2, &l_Lean_Cadical_Solver_solve___closed__2_once, _init_l_Lean_Cadical_Solver_solve___closed__2);
v___x_522_ = l_panic___at___00Lean_Cadical_Solver_solve_spec__0(v___x_521_);
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_solve___boxed(lean_object* v_s_523_, lean_object* v_a_524_){
_start:
{
uint8_t v_res_525_; lean_object* v_r_526_; 
v_res_525_ = l_Lean_Cadical_Solver_solve(v_s_523_);
lean_dec_ref(v_s_523_);
v_r_526_ = lean_box(v_res_525_);
return v_r_526_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_val___closed__1(void){
_start:
{
uint16_t v___x_528_; lean_object* v___x_529_; 
v___x_528_ = 32;
v___x_529_ = l_Lean_Cadical_State_toString(v___x_528_);
return v___x_529_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_val___closed__2(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = lean_obj_once(&l_Lean_Cadical_Solver_val___closed__1, &l_Lean_Cadical_Solver_val___closed__1_once, _init_l_Lean_Cadical_Solver_val___closed__1);
v___x_531_ = ((lean_object*)(l_Lean_Cadical_Solver_val___closed__0));
v___x_532_ = lean_string_append(v___x_531_, v___x_530_);
return v___x_532_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_val___closed__4(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_534_ = ((lean_object*)(l_Lean_Cadical_Solver_val___closed__3));
v___x_535_ = lean_obj_once(&l_Lean_Cadical_Solver_val___closed__2, &l_Lean_Cadical_Solver_val___closed__2_once, _init_l_Lean_Cadical_Solver_val___closed__2);
v___x_536_ = lean_string_append(v___x_535_, v___x_534_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_val(lean_object* v_s_537_, lean_object* v_lit_538_){
_start:
{
uint16_t v___x_540_; uint16_t v___x_541_; uint8_t v___x_542_; 
v___x_540_ = l_Lean_Cadical_Solver_state(v_s_537_);
v___x_541_ = 32;
v___x_542_ = lean_uint16_dec_eq(v___x_540_, v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
lean_dec_ref(v_s_537_);
v___x_543_ = lean_obj_once(&l_Lean_Cadical_Solver_val___closed__4, &l_Lean_Cadical_Solver_val___closed__4_once, _init_l_Lean_Cadical_Solver_val___closed__4);
v___x_544_ = l_Lean_Cadical_State_toString(v___x_540_);
v___x_545_ = lean_string_append(v___x_543_, v___x_544_);
lean_dec_ref(v___x_544_);
v___x_546_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
v___x_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
else
{
lean_object* v___x_548_; lean_object* v_lit_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_548_ = lean_unsigned_to_nat(1u);
v_lit_549_ = lean_nat_add(v_lit_538_, v___x_548_);
v___x_550_ = lean_obj_once(&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2, &l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2_once, _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2);
v___x_551_ = lean_nat_dec_lt(v___x_550_, v_lit_549_);
if (v___x_551_ == 0)
{
lean_object* v_solver_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_563_; 
v_solver_552_ = lean_ctor_get(v_s_537_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v_s_537_);
if (v_isSharedCheck_563_ == 0)
{
v___x_554_ = v_s_537_;
v_isShared_555_ = v_isSharedCheck_563_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_solver_552_);
lean_dec(v_s_537_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_563_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
uint32_t v_lit_556_; uint32_t v___x_557_; uint8_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
v_lit_556_ = lean_int32_of_nat(v_lit_549_);
lean_dec(v_lit_549_);
v___x_557_ = lean_cadical_solver_val(v_solver_552_, v_lit_556_);
lean_dec(v_solver_552_);
v___x_558_ = lean_int32_dec_eq(v_lit_556_, v___x_557_);
v___x_559_ = lean_box(v___x_558_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_559_);
v___x_561_ = v___x_554_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec(v_lit_549_);
lean_dec_ref(v_s_537_);
v___x_564_ = ((lean_object*)(l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__4));
v___x_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_val___boxed(lean_object* v_s_566_, lean_object* v_lit_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Cadical_Solver_val(v_s_566_, v_lit_567_);
lean_dec(v_lit_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_resetAssumptions(lean_object* v_s_570_){
_start:
{
lean_object* v_solver_572_; lean_object* v___x_573_; 
v_solver_572_ = lean_ctor_get(v_s_570_, 0);
v___x_573_ = lean_cadical_solver_reset_assumptions(v_solver_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_resetAssumptions___boxed(lean_object* v_s_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Cadical_Solver_resetAssumptions(v_s_574_);
lean_dec_ref(v_s_574_);
return v_res_576_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_status(lean_object* v_s_577_){
_start:
{
lean_object* v_solver_579_; uint8_t v___x_580_; 
v_solver_579_ = lean_ctor_get(v_s_577_, 0);
v___x_580_ = lean_cadical_solver_status(v_solver_579_);
switch(v___x_580_)
{
case 0:
{
uint8_t v___x_581_; 
v___x_581_ = 0;
return v___x_581_;
}
case 1:
{
uint8_t v___x_582_; 
v___x_582_ = 1;
return v___x_582_;
}
default: 
{
uint8_t v___x_583_; 
v___x_583_ = 2;
return v___x_583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_status___boxed(lean_object* v_s_584_, lean_object* v_a_585_){
_start:
{
uint8_t v_res_586_; lean_object* v_r_587_; 
v_res_586_ = l_Lean_Cadical_Solver_status(v_s_584_);
lean_dec_ref(v_s_584_);
v_r_587_ = lean_box(v_res_586_);
return v_r_587_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_isValidOption(lean_object* v_opt_588_){
_start:
{
uint8_t v___x_589_; 
v___x_589_ = lean_cadical_solver_is_valid_option(v_opt_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_isValidOption___boxed(lean_object* v_opt_590_){
_start:
{
uint8_t v_res_591_; lean_object* v_r_592_; 
v_res_591_ = l_Lean_Cadical_Solver_isValidOption(v_opt_590_);
lean_dec_ref(v_opt_590_);
v_r_592_ = lean_box(v_res_591_);
return v_r_592_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_isPreprocessingOption(lean_object* v_opt_593_){
_start:
{
uint8_t v___x_594_; 
v___x_594_ = lean_cadical_solver_is_preprocessing_option(v_opt_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_isPreprocessingOption___boxed(lean_object* v_opt_595_){
_start:
{
uint8_t v_res_596_; lean_object* v_r_597_; 
v_res_596_ = l_Lean_Cadical_Solver_isPreprocessingOption(v_opt_595_);
lean_dec_ref(v_opt_595_);
v_r_597_ = lean_box(v_res_596_);
return v_r_597_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_isValidLongOption(lean_object* v_opt_598_){
_start:
{
uint8_t v___x_599_; 
v___x_599_ = lean_cadical_solver_is_valid_long_option(v_opt_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_isValidLongOption___boxed(lean_object* v_opt_600_){
_start:
{
uint8_t v_res_601_; lean_object* v_r_602_; 
v_res_601_ = l_Lean_Cadical_Solver_isValidLongOption(v_opt_600_);
lean_dec_ref(v_opt_600_);
v_r_602_ = lean_box(v_res_601_);
return v_r_602_;
}
}
LEAN_EXPORT uint32_t l_Lean_Cadical_Solver_getOption(lean_object* v_s_603_, lean_object* v_opt_604_){
_start:
{
lean_object* v_solver_606_; uint32_t v___x_607_; 
v_solver_606_ = lean_ctor_get(v_s_603_, 0);
v___x_607_ = lean_cadical_solver_get(v_solver_606_, v_opt_604_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_getOption___boxed(lean_object* v_s_608_, lean_object* v_opt_609_, lean_object* v_a_610_){
_start:
{
uint32_t v_res_611_; lean_object* v_r_612_; 
v_res_611_ = l_Lean_Cadical_Solver_getOption(v_s_608_, v_opt_609_);
lean_dec_ref(v_opt_609_);
lean_dec_ref(v_s_608_);
v_r_612_ = lean_box_uint32(v_res_611_);
return v_r_612_;
}
}
static lean_object* _init_l_panic___at___00Lean_Cadical_Solver_setOption_spec__0___closed__0(void){
_start:
{
uint8_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_613_ = 0;
v___x_614_ = l_instMonadBaseIO;
v___x_615_ = lean_box(v___x_613_);
v___x_616_ = l_instInhabitedOfMonad___redArg(v___x_614_, v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Cadical_Solver_setOption_spec__0(lean_object* v_msg_617_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_132__overap_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_619_ = lean_obj_once(&l_panic___at___00Lean_Cadical_Solver_setOption_spec__0___closed__0, &l_panic___at___00Lean_Cadical_Solver_setOption_spec__0___closed__0_once, _init_l_panic___at___00Lean_Cadical_Solver_setOption_spec__0___closed__0);
v___x_132__overap_620_ = lean_panic_fn_borrowed(v___x_619_, v_msg_617_);
v___x_621_ = lean_apply_1(v___x_132__overap_620_, lean_box(0));
v___x_622_ = lean_unbox(v___x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_setOption_spec__0___boxed(lean_object* v_msg_623_, lean_object* v___y_624_){
_start:
{
uint8_t v_res_625_; lean_object* v_r_626_; 
v_res_625_ = l_panic___at___00Lean_Cadical_Solver_setOption_spec__0(v_msg_623_);
v_r_626_ = lean_box(v_res_625_);
return v_r_626_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_setOption___closed__2(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_629_ = ((lean_object*)(l_Lean_Cadical_Solver_setOption___closed__1));
v___x_630_ = lean_unsigned_to_nat(2u);
v___x_631_ = lean_unsigned_to_nat(235u);
v___x_632_ = ((lean_object*)(l_Lean_Cadical_Solver_setOption___closed__0));
v___x_633_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_634_ = l_mkPanicMessageWithDecl(v___x_633_, v___x_632_, v___x_631_, v___x_630_, v___x_629_);
return v___x_634_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_setOption(lean_object* v_s_635_, lean_object* v_opt_636_, uint32_t v_val_637_){
_start:
{
uint16_t v___x_639_; uint16_t v___x_640_; uint8_t v___x_641_; 
v___x_639_ = l_Lean_Cadical_Solver_state(v_s_635_);
v___x_640_ = 2;
v___x_641_ = lean_uint16_dec_eq(v___x_639_, v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = lean_obj_once(&l_Lean_Cadical_Solver_setOption___closed__2, &l_Lean_Cadical_Solver_setOption___closed__2_once, _init_l_Lean_Cadical_Solver_setOption___closed__2);
v___x_643_ = l_panic___at___00Lean_Cadical_Solver_setOption_spec__0(v___x_642_);
return v___x_643_;
}
else
{
lean_object* v_solver_644_; uint8_t v___x_645_; 
v_solver_644_ = lean_ctor_get(v_s_635_, 0);
v___x_645_ = lean_cadical_solver_set(v_solver_644_, v_opt_636_, v_val_637_);
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_setOption___boxed(lean_object* v_s_646_, lean_object* v_opt_647_, lean_object* v_val_648_, lean_object* v_a_649_){
_start:
{
uint32_t v_val_boxed_650_; uint8_t v_res_651_; lean_object* v_r_652_; 
v_val_boxed_650_ = lean_unbox_uint32(v_val_648_);
lean_dec(v_val_648_);
v_res_651_ = l_Lean_Cadical_Solver_setOption(v_s_646_, v_opt_647_, v_val_boxed_650_);
lean_dec_ref(v_opt_647_);
lean_dec_ref(v_s_646_);
v_r_652_ = lean_box(v_res_651_);
return v_r_652_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_setLongOption___closed__2(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_655_ = ((lean_object*)(l_Lean_Cadical_Solver_setLongOption___closed__1));
v___x_656_ = lean_unsigned_to_nat(2u);
v___x_657_ = lean_unsigned_to_nat(239u);
v___x_658_ = ((lean_object*)(l_Lean_Cadical_Solver_setLongOption___closed__0));
v___x_659_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_660_ = l_mkPanicMessageWithDecl(v___x_659_, v___x_658_, v___x_657_, v___x_656_, v___x_655_);
return v___x_660_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_setLongOption(lean_object* v_s_661_, lean_object* v_opt_662_){
_start:
{
uint16_t v___x_664_; uint16_t v___x_665_; uint8_t v___x_666_; 
v___x_664_ = l_Lean_Cadical_Solver_state(v_s_661_);
v___x_665_ = 2;
v___x_666_ = lean_uint16_dec_eq(v___x_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_667_ = lean_obj_once(&l_Lean_Cadical_Solver_setLongOption___closed__2, &l_Lean_Cadical_Solver_setLongOption___closed__2_once, _init_l_Lean_Cadical_Solver_setLongOption___closed__2);
v___x_668_ = l_panic___at___00Lean_Cadical_Solver_setOption_spec__0(v___x_667_);
return v___x_668_;
}
else
{
lean_object* v_solver_669_; uint8_t v___x_670_; 
v_solver_669_ = lean_ctor_get(v_s_661_, 0);
v___x_670_ = lean_cadical_solver_set_long_option(v_solver_669_, v_opt_662_);
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_setLongOption___boxed(lean_object* v_s_671_, lean_object* v_opt_672_, lean_object* v_a_673_){
_start:
{
uint8_t v_res_674_; lean_object* v_r_675_; 
v_res_674_ = l_Lean_Cadical_Solver_setLongOption(v_s_671_, v_opt_672_);
lean_dec_ref(v_opt_672_);
lean_dec_ref(v_s_671_);
v_r_675_ = lean_box(v_res_674_);
return v_r_675_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_isValidConfiguration(lean_object* v_opt_676_){
_start:
{
uint8_t v___x_677_; 
v___x_677_ = lean_cadical_solver_is_valid_configuration(v_opt_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_isValidConfiguration___boxed(lean_object* v_opt_678_){
_start:
{
uint8_t v_res_679_; lean_object* v_r_680_; 
v_res_679_ = l_Lean_Cadical_Solver_isValidConfiguration(v_opt_678_);
lean_dec_ref(v_opt_678_);
v_r_680_ = lean_box(v_res_679_);
return v_r_680_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_configure___closed__2(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_683_ = ((lean_object*)(l_Lean_Cadical_Solver_configure___closed__1));
v___x_684_ = lean_unsigned_to_nat(2u);
v___x_685_ = lean_unsigned_to_nat(245u);
v___x_686_ = ((lean_object*)(l_Lean_Cadical_Solver_configure___closed__0));
v___x_687_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_688_ = l_mkPanicMessageWithDecl(v___x_687_, v___x_686_, v___x_685_, v___x_684_, v___x_683_);
return v___x_688_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_configure(lean_object* v_s_689_, lean_object* v_opt_690_){
_start:
{
uint16_t v___x_692_; uint16_t v___x_693_; uint8_t v___x_694_; 
v___x_692_ = l_Lean_Cadical_Solver_state(v_s_689_);
v___x_693_ = 2;
v___x_694_ = lean_uint16_dec_eq(v___x_692_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_695_ = lean_obj_once(&l_Lean_Cadical_Solver_configure___closed__2, &l_Lean_Cadical_Solver_configure___closed__2_once, _init_l_Lean_Cadical_Solver_configure___closed__2);
v___x_696_ = l_panic___at___00Lean_Cadical_Solver_setOption_spec__0(v___x_695_);
return v___x_696_;
}
else
{
lean_object* v_solver_697_; uint8_t v___x_698_; 
v_solver_697_ = lean_ctor_get(v_s_689_, 0);
v___x_698_ = lean_cadical_solver_configure(v_solver_697_, v_opt_690_);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_configure___boxed(lean_object* v_s_699_, lean_object* v_opt_700_, lean_object* v_a_701_){
_start:
{
uint8_t v_res_702_; lean_object* v_r_703_; 
v_res_702_ = l_Lean_Cadical_Solver_configure(v_s_699_, v_opt_700_);
lean_dec_ref(v_opt_700_);
lean_dec_ref(v_s_699_);
v_r_703_ = lean_box(v_res_702_);
return v_r_703_;
}
}
static lean_object* _init_l_panic___at___00Lean_Cadical_Solver_terminate_spec__0___closed__0(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = lean_box(0);
v___x_705_ = l_instMonadBaseIO;
v___x_706_ = l_instInhabitedOfMonad___redArg(v___x_705_, v___x_704_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_terminate_spec__0(lean_object* v_msg_707_){
_start:
{
lean_object* v___x_709_; lean_object* v___x_246__overap_710_; lean_object* v___x_711_; 
v___x_709_ = lean_obj_once(&l_panic___at___00Lean_Cadical_Solver_terminate_spec__0___closed__0, &l_panic___at___00Lean_Cadical_Solver_terminate_spec__0___closed__0_once, _init_l_panic___at___00Lean_Cadical_Solver_terminate_spec__0___closed__0);
v___x_246__overap_710_ = lean_panic_fn_borrowed(v___x_709_, v_msg_707_);
v___x_711_ = lean_apply_1(v___x_246__overap_710_, lean_box(0));
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_terminate_spec__0___boxed(lean_object* v_msg_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_panic___at___00Lean_Cadical_Solver_terminate_spec__0(v_msg_712_);
return v_res_714_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_terminate___closed__2(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_717_ = ((lean_object*)(l_Lean_Cadical_Solver_terminate___closed__1));
v___x_718_ = lean_unsigned_to_nat(2u);
v___x_719_ = lean_unsigned_to_nat(250u);
v___x_720_ = ((lean_object*)(l_Lean_Cadical_Solver_terminate___closed__0));
v___x_721_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_722_ = l_mkPanicMessageWithDecl(v___x_721_, v___x_720_, v___x_719_, v___x_718_, v___x_717_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_terminate(lean_object* v_s_723_){
_start:
{
uint16_t v___x_725_; uint16_t v___x_729_; uint8_t v___x_730_; 
v___x_725_ = l_Lean_Cadical_Solver_state(v_s_723_);
v___x_729_ = 16;
v___x_730_ = lean_uint16_dec_eq(v___x_725_, v___x_729_);
if (v___x_730_ == 0)
{
uint16_t v___x_731_; uint16_t v___x_732_; uint16_t v___x_733_; uint8_t v___x_734_; 
v___x_731_ = 358;
v___x_732_ = lean_uint16_land(v___x_725_, v___x_731_);
v___x_733_ = lean_uint16_once(&l_Lean_Cadical_State_isReady___closed__1, &l_Lean_Cadical_State_isReady___closed__1_once, _init_l_Lean_Cadical_State_isReady___closed__1);
v___x_734_ = lean_uint16_dec_eq(v___x_732_, v___x_733_);
if (v___x_734_ == 0)
{
goto v___jp_726_;
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_obj_once(&l_Lean_Cadical_Solver_terminate___closed__2, &l_Lean_Cadical_Solver_terminate___closed__2_once, _init_l_Lean_Cadical_Solver_terminate___closed__2);
v___x_736_ = l_panic___at___00Lean_Cadical_Solver_terminate_spec__0(v___x_735_);
return v___x_736_;
}
}
else
{
goto v___jp_726_;
}
v___jp_726_:
{
lean_object* v_solver_727_; lean_object* v___x_728_; 
v_solver_727_ = lean_ctor_get(v_s_723_, 0);
v___x_728_ = lean_cadical_solver_terminate(v_solver_727_);
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_terminate___boxed(lean_object* v_s_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_Cadical_Solver_terminate(v_s_737_);
lean_dec_ref(v_s_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printConfigurations(){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = lean_cadical_solver_configurations();
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printConfigurations___boxed(lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_Cadical_Solver_printConfigurations();
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printStatistics(lean_object* v_s_744_){
_start:
{
lean_object* v_solver_746_; lean_object* v___x_747_; 
v_solver_746_ = lean_ctor_get(v_s_744_, 0);
v___x_747_ = lean_cadical_solver_statistics(v_solver_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printStatistics___boxed(lean_object* v_s_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_Cadical_Solver_printStatistics(v_s_748_);
lean_dec_ref(v_s_748_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printResources(lean_object* v_s_751_){
_start:
{
lean_object* v_solver_753_; lean_object* v___x_754_; 
v_solver_753_ = lean_ctor_get(v_s_751_, 0);
v___x_754_ = lean_cadical_solver_resources(v_solver_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printResources___boxed(lean_object* v_s_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_Cadical_Solver_printResources(v_s_755_);
lean_dec_ref(v_s_755_);
return v_res_757_;
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
