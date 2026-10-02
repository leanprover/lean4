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
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorIdx(uint8_t v_x_121_){
_start:
{
switch(v_x_121_)
{
case 0:
{
lean_object* v___x_122_; 
v___x_122_ = lean_unsigned_to_nat(0u);
return v___x_122_;
}
case 1:
{
lean_object* v___x_123_; 
v___x_123_ = lean_unsigned_to_nat(1u);
return v___x_123_;
}
default: 
{
lean_object* v___x_124_; 
v___x_124_ = lean_unsigned_to_nat(2u);
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorIdx___boxed(lean_object* v_x_125_){
_start:
{
uint8_t v_x_boxed_126_; lean_object* v_res_127_; 
v_x_boxed_126_ = lean_unbox(v_x_125_);
v_res_127_ = l_Lean_Cadical_Status_ctorIdx(v_x_boxed_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorElim___redArg(lean_object* v_k_128_){
_start:
{
lean_inc(v_k_128_);
return v_k_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorElim___redArg___boxed(lean_object* v_k_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Cadical_Status_ctorElim___redArg(v_k_129_);
lean_dec(v_k_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorElim(lean_object* v_motive_131_, lean_object* v_ctorIdx_132_, uint8_t v_t_133_, lean_object* v_h_134_, lean_object* v_k_135_){
_start:
{
lean_inc(v_k_135_);
return v_k_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ctorElim___boxed(lean_object* v_motive_136_, lean_object* v_ctorIdx_137_, lean_object* v_t_138_, lean_object* v_h_139_, lean_object* v_k_140_){
_start:
{
uint8_t v_t_boxed_141_; lean_object* v_res_142_; 
v_t_boxed_141_ = lean_unbox(v_t_138_);
v_res_142_ = l_Lean_Cadical_Status_ctorElim(v_motive_136_, v_ctorIdx_137_, v_t_boxed_141_, v_h_139_, v_k_140_);
lean_dec(v_k_140_);
lean_dec(v_ctorIdx_137_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_satisfiable_elim___redArg(lean_object* v_satisfiable_143_){
_start:
{
lean_inc(v_satisfiable_143_);
return v_satisfiable_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_satisfiable_elim___redArg___boxed(lean_object* v_satisfiable_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Cadical_Status_satisfiable_elim___redArg(v_satisfiable_144_);
lean_dec(v_satisfiable_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_satisfiable_elim(lean_object* v_motive_146_, uint8_t v_t_147_, lean_object* v_h_148_, lean_object* v_satisfiable_149_){
_start:
{
lean_inc(v_satisfiable_149_);
return v_satisfiable_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_satisfiable_elim___boxed(lean_object* v_motive_150_, lean_object* v_t_151_, lean_object* v_h_152_, lean_object* v_satisfiable_153_){
_start:
{
uint8_t v_t_boxed_154_; lean_object* v_res_155_; 
v_t_boxed_154_ = lean_unbox(v_t_151_);
v_res_155_ = l_Lean_Cadical_Status_satisfiable_elim(v_motive_150_, v_t_boxed_154_, v_h_152_, v_satisfiable_153_);
lean_dec(v_satisfiable_153_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unsatisfiable_elim___redArg(lean_object* v_unsatisfiable_156_){
_start:
{
lean_inc(v_unsatisfiable_156_);
return v_unsatisfiable_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unsatisfiable_elim___redArg___boxed(lean_object* v_unsatisfiable_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_Cadical_Status_unsatisfiable_elim___redArg(v_unsatisfiable_157_);
lean_dec(v_unsatisfiable_157_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unsatisfiable_elim(lean_object* v_motive_159_, uint8_t v_t_160_, lean_object* v_h_161_, lean_object* v_unsatisfiable_162_){
_start:
{
lean_inc(v_unsatisfiable_162_);
return v_unsatisfiable_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unsatisfiable_elim___boxed(lean_object* v_motive_163_, lean_object* v_t_164_, lean_object* v_h_165_, lean_object* v_unsatisfiable_166_){
_start:
{
uint8_t v_t_boxed_167_; lean_object* v_res_168_; 
v_t_boxed_167_ = lean_unbox(v_t_164_);
v_res_168_ = l_Lean_Cadical_Status_unsatisfiable_elim(v_motive_163_, v_t_boxed_167_, v_h_165_, v_unsatisfiable_166_);
lean_dec(v_unsatisfiable_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unknown_elim___redArg(lean_object* v_unknown_169_){
_start:
{
lean_inc(v_unknown_169_);
return v_unknown_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unknown_elim___redArg___boxed(lean_object* v_unknown_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Cadical_Status_unknown_elim___redArg(v_unknown_170_);
lean_dec(v_unknown_170_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unknown_elim(lean_object* v_motive_172_, uint8_t v_t_173_, lean_object* v_h_174_, lean_object* v_unknown_175_){
_start:
{
lean_inc(v_unknown_175_);
return v_unknown_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_unknown_elim___boxed(lean_object* v_motive_176_, lean_object* v_t_177_, lean_object* v_h_178_, lean_object* v_unknown_179_){
_start:
{
uint8_t v_t_boxed_180_; lean_object* v_res_181_; 
v_t_boxed_180_ = lean_unbox(v_t_177_);
v_res_181_ = l_Lean_Cadical_Status_unknown_elim(v_motive_176_, v_t_boxed_180_, v_h_178_, v_unknown_179_);
lean_dec(v_unknown_179_);
return v_res_181_;
}
}
static uint8_t _init_l_Lean_Cadical_instInhabitedStatus_default(void){
_start:
{
uint8_t v___x_182_; 
v___x_182_ = 0;
return v___x_182_;
}
}
static uint8_t _init_l_Lean_Cadical_instInhabitedStatus(void){
_start:
{
uint8_t v___x_183_; 
v___x_183_ = 0;
return v___x_183_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Status_ofNat(lean_object* v_n_184_){
_start:
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = lean_nat_dec_le(v_n_184_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_nat_dec_le(v_n_184_, v___x_187_);
if (v___x_188_ == 0)
{
uint8_t v___x_189_; 
v___x_189_ = 2;
return v___x_189_;
}
else
{
uint8_t v___x_190_; 
v___x_190_ = 1;
return v___x_190_;
}
}
else
{
uint8_t v___x_191_; 
v___x_191_ = 0;
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_ofNat___boxed(lean_object* v_n_192_){
_start:
{
uint8_t v_res_193_; lean_object* v_r_194_; 
v_res_193_ = l_Lean_Cadical_Status_ofNat(v_n_192_);
lean_dec(v_n_192_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_instDecidableEqStatus(uint8_t v_x_195_, uint8_t v_y_196_){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_197_ = l_Lean_Cadical_Status_ctorIdx(v_x_195_);
v___x_198_ = l_Lean_Cadical_Status_ctorIdx(v_y_196_);
v___x_199_ = lean_nat_dec_eq(v___x_197_, v___x_198_);
lean_dec(v___x_198_);
lean_dec(v___x_197_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_instDecidableEqStatus___boxed(lean_object* v_x_200_, lean_object* v_y_201_){
_start:
{
uint8_t v_x_20__boxed_202_; uint8_t v_y_21__boxed_203_; uint8_t v_res_204_; lean_object* v_r_205_; 
v_x_20__boxed_202_ = lean_unbox(v_x_200_);
v_y_21__boxed_203_ = lean_unbox(v_y_201_);
v_res_204_ = l_Lean_Cadical_instDecidableEqStatus(v_x_20__boxed_202_, v_y_21__boxed_203_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT uint64_t l_Lean_Cadical_instHashableStatus_hash(uint8_t v_x_206_){
_start:
{
switch(v_x_206_)
{
case 0:
{
uint64_t v___x_207_; 
v___x_207_ = 0ULL;
return v___x_207_;
}
case 1:
{
uint64_t v___x_208_; 
v___x_208_ = 1ULL;
return v___x_208_;
}
default: 
{
uint64_t v___x_209_; 
v___x_209_ = 2ULL;
return v___x_209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_instHashableStatus_hash___boxed(lean_object* v_x_210_){
_start:
{
uint8_t v_x_40__boxed_211_; uint64_t v_res_212_; lean_object* v_r_213_; 
v_x_40__boxed_211_ = lean_unbox(v_x_210_);
v_res_212_ = l_Lean_Cadical_instHashableStatus_hash(v_x_40__boxed_211_);
v_r_213_ = lean_box_uint64(v_res_212_);
return v_r_213_;
}
}
static lean_object* _init_l_Lean_Cadical_instReprStatus_repr___closed__6(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_unsigned_to_nat(2u);
v___x_226_ = lean_nat_to_int(v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Cadical_instReprStatus_repr___closed__7(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = lean_nat_to_int(v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_instReprStatus_repr(uint8_t v_x_229_, lean_object* v_prec_230_){
_start:
{
lean_object* v___y_232_; lean_object* v___y_239_; lean_object* v___y_246_; 
switch(v_x_229_)
{
case 0:
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = lean_unsigned_to_nat(1024u);
v___x_253_ = lean_nat_dec_le(v___x_252_, v_prec_230_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
v___x_254_ = lean_obj_once(&l_Lean_Cadical_instReprStatus_repr___closed__6, &l_Lean_Cadical_instReprStatus_repr___closed__6_once, _init_l_Lean_Cadical_instReprStatus_repr___closed__6);
v___y_232_ = v___x_254_;
goto v___jp_231_;
}
else
{
lean_object* v___x_255_; 
v___x_255_ = lean_obj_once(&l_Lean_Cadical_instReprStatus_repr___closed__7, &l_Lean_Cadical_instReprStatus_repr___closed__7_once, _init_l_Lean_Cadical_instReprStatus_repr___closed__7);
v___y_232_ = v___x_255_;
goto v___jp_231_;
}
}
case 1:
{
lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_256_ = lean_unsigned_to_nat(1024u);
v___x_257_ = lean_nat_dec_le(v___x_256_, v_prec_230_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
v___x_258_ = lean_obj_once(&l_Lean_Cadical_instReprStatus_repr___closed__6, &l_Lean_Cadical_instReprStatus_repr___closed__6_once, _init_l_Lean_Cadical_instReprStatus_repr___closed__6);
v___y_239_ = v___x_258_;
goto v___jp_238_;
}
else
{
lean_object* v___x_259_; 
v___x_259_ = lean_obj_once(&l_Lean_Cadical_instReprStatus_repr___closed__7, &l_Lean_Cadical_instReprStatus_repr___closed__7_once, _init_l_Lean_Cadical_instReprStatus_repr___closed__7);
v___y_239_ = v___x_259_;
goto v___jp_238_;
}
}
default: 
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = lean_unsigned_to_nat(1024u);
v___x_261_ = lean_nat_dec_le(v___x_260_, v_prec_230_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
v___x_262_ = lean_obj_once(&l_Lean_Cadical_instReprStatus_repr___closed__6, &l_Lean_Cadical_instReprStatus_repr___closed__6_once, _init_l_Lean_Cadical_instReprStatus_repr___closed__6);
v___y_246_ = v___x_262_;
goto v___jp_245_;
}
else
{
lean_object* v___x_263_; 
v___x_263_ = lean_obj_once(&l_Lean_Cadical_instReprStatus_repr___closed__7, &l_Lean_Cadical_instReprStatus_repr___closed__7_once, _init_l_Lean_Cadical_instReprStatus_repr___closed__7);
v___y_246_ = v___x_263_;
goto v___jp_245_;
}
}
}
v___jp_231_:
{
lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_233_ = ((lean_object*)(l_Lean_Cadical_instReprStatus_repr___closed__1));
lean_inc(v___y_232_);
v___x_234_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_234_, 0, v___y_232_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = 0;
v___x_236_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_236_, 0, v___x_234_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*1, v___x_235_);
v___x_237_ = l_Repr_addAppParen(v___x_236_, v_prec_230_);
return v___x_237_;
}
v___jp_238_:
{
lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_240_ = ((lean_object*)(l_Lean_Cadical_instReprStatus_repr___closed__3));
lean_inc(v___y_239_);
v___x_241_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_241_, 0, v___y_239_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = 0;
v___x_243_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set_uint8(v___x_243_, sizeof(void*)*1, v___x_242_);
v___x_244_ = l_Repr_addAppParen(v___x_243_, v_prec_230_);
return v___x_244_;
}
v___jp_245_:
{
lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_247_ = ((lean_object*)(l_Lean_Cadical_instReprStatus_repr___closed__5));
lean_inc(v___y_246_);
v___x_248_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_248_, 0, v___y_246_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = 0;
v___x_250_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_250_, 0, v___x_248_);
lean_ctor_set_uint8(v___x_250_, sizeof(void*)*1, v___x_249_);
v___x_251_ = l_Repr_addAppParen(v___x_250_, v_prec_230_);
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_instReprStatus_repr___boxed(lean_object* v_x_264_, lean_object* v_prec_265_){
_start:
{
uint8_t v_x_171__boxed_266_; lean_object* v_res_267_; 
v_x_171__boxed_266_ = lean_unbox(v_x_264_);
v_res_267_ = l_Lean_Cadical_instReprStatus_repr(v_x_171__boxed_266_, v_prec_265_);
lean_dec(v_prec_265_);
return v_res_267_;
}
}
static uint32_t _init_l_Lean_Cadical_Status_toInt32___closed__0(void){
_start:
{
lean_object* v___x_270_; uint32_t v___x_271_; 
v___x_270_ = lean_unsigned_to_nat(10u);
v___x_271_ = lean_int32_of_nat(v___x_270_);
return v___x_271_;
}
}
static uint32_t _init_l_Lean_Cadical_Status_toInt32___closed__1(void){
_start:
{
lean_object* v___x_272_; uint32_t v___x_273_; 
v___x_272_ = lean_unsigned_to_nat(20u);
v___x_273_ = lean_int32_of_nat(v___x_272_);
return v___x_273_;
}
}
static uint32_t _init_l_Lean_Cadical_Status_toInt32___closed__2(void){
_start:
{
lean_object* v___x_274_; uint32_t v___x_275_; 
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = lean_int32_of_nat(v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT uint32_t l_Lean_Cadical_Status_toInt32(uint8_t v_x_276_){
_start:
{
switch(v_x_276_)
{
case 0:
{
uint32_t v___x_277_; 
v___x_277_ = lean_uint32_once(&l_Lean_Cadical_Status_toInt32___closed__0, &l_Lean_Cadical_Status_toInt32___closed__0_once, _init_l_Lean_Cadical_Status_toInt32___closed__0);
return v___x_277_;
}
case 1:
{
uint32_t v___x_278_; 
v___x_278_ = lean_uint32_once(&l_Lean_Cadical_Status_toInt32___closed__1, &l_Lean_Cadical_Status_toInt32___closed__1_once, _init_l_Lean_Cadical_Status_toInt32___closed__1);
return v___x_278_;
}
default: 
{
uint32_t v___x_279_; 
v___x_279_ = lean_uint32_once(&l_Lean_Cadical_Status_toInt32___closed__2, &l_Lean_Cadical_Status_toInt32___closed__2_once, _init_l_Lean_Cadical_Status_toInt32___closed__2);
return v___x_279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_toInt32___boxed(lean_object* v_x_280_){
_start:
{
uint8_t v_x_52__boxed_281_; uint32_t v_res_282_; lean_object* v_r_283_; 
v_x_52__boxed_281_ = lean_unbox(v_x_280_);
v_res_282_ = l_Lean_Cadical_Status_toInt32(v_x_52__boxed_281_);
v_r_283_ = lean_box_uint32(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_toString(uint8_t v_x_287_){
_start:
{
switch(v_x_287_)
{
case 0:
{
lean_object* v___x_288_; 
v___x_288_ = ((lean_object*)(l_Lean_Cadical_Status_toString___closed__0));
return v___x_288_;
}
case 1:
{
lean_object* v___x_289_; 
v___x_289_ = ((lean_object*)(l_Lean_Cadical_Status_toString___closed__1));
return v___x_289_;
}
default: 
{
lean_object* v___x_290_; 
v___x_290_ = ((lean_object*)(l_Lean_Cadical_Status_toString___closed__2));
return v___x_290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Status_toString___boxed(lean_object* v_x_291_){
_start:
{
uint8_t v_x_31__boxed_292_; lean_object* v_res_293_; 
v_x_31__boxed_292_ = lean_unbox(v_x_291_);
v_res_293_ = l_Lean_Cadical_Status_toString(v_x_31__boxed_292_);
return v_res_293_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Cadical_Basic_0__Lean_Cadical_Status_ofInternal(uint8_t v_s_296_){
_start:
{
switch(v_s_296_)
{
case 0:
{
uint8_t v___x_297_; 
v___x_297_ = 0;
return v___x_297_;
}
case 1:
{
uint8_t v___x_298_; 
v___x_298_ = 1;
return v___x_298_;
}
default: 
{
uint8_t v___x_299_; 
v___x_299_ = 2;
return v___x_299_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Cadical_Basic_0__Lean_Cadical_Status_ofInternal___boxed(lean_object* v_s_300_){
_start:
{
uint8_t v_s_boxed_301_; uint8_t v_res_302_; lean_object* v_r_303_; 
v_s_boxed_301_ = lean_unbox(v_s_300_);
v_res_302_ = l___private_Lean_Cadical_Basic_0__Lean_Cadical_Status_ofInternal(v_s_boxed_301_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
static uint32_t _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__0(void){
_start:
{
lean_object* v___x_304_; uint32_t v___x_305_; 
v___x_304_ = lean_unsigned_to_nat(2147483647u);
v___x_305_ = lean_int32_of_nat(v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__1(void){
_start:
{
uint32_t v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_uint32_once(&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__0, &l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__0_once, _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__0);
v___x_307_ = lean_int32_to_int(v___x_306_);
return v___x_307_;
}
}
static lean_object* _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_obj_once(&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__1, &l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__1_once, _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__1);
v___x_309_ = l_Int_toNat(v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit(lean_object* v_lit_313_, uint8_t v_pol_314_){
_start:
{
lean_object* v___x_316_; lean_object* v_lit_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_316_ = lean_unsigned_to_nat(1u);
v_lit_317_ = lean_nat_add(v_lit_313_, v___x_316_);
v___x_318_ = lean_obj_once(&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2, &l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2_once, _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2);
v___x_319_ = lean_nat_dec_lt(v___x_318_, v_lit_317_);
if (v___x_319_ == 0)
{
uint32_t v_lit_320_; 
v_lit_320_ = lean_int32_of_nat(v_lit_317_);
lean_dec(v_lit_317_);
if (v_pol_314_ == 0)
{
uint32_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_int32_neg(v_lit_320_);
v___x_322_ = lean_box_uint32(v___x_321_);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_box_uint32(v_lit_320_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; 
lean_dec(v_lit_317_);
v___x_326_ = ((lean_object*)(l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__4));
v___x_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___boxed(lean_object* v_lit_328_, lean_object* v_pol_329_, lean_object* v_a_330_){
_start:
{
uint8_t v_pol_boxed_331_; lean_object* v_res_332_; 
v_pol_boxed_331_ = lean_unbox(v_pol_329_);
v_res_332_ = l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit(v_lit_328_, v_pol_boxed_331_);
lean_dec(v_lit_328_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_new(){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_cadical_solver_new();
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_new___boxed(lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Cadical_Solver_new();
return v_res_337_;
}
}
LEAN_EXPORT uint16_t l_Lean_Cadical_Solver_state(lean_object* v_s_338_){
_start:
{
lean_object* v_solver_340_; uint16_t v___x_341_; 
v_solver_340_ = lean_ctor_get(v_s_338_, 0);
v___x_341_ = lean_cadical_solver_state(v_solver_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_state___boxed(lean_object* v_s_342_, lean_object* v_a_343_){
_start:
{
uint16_t v_res_344_; lean_object* v_r_345_; 
v_res_344_ = l_Lean_Cadical_Solver_state(v_s_342_);
lean_dec_ref(v_s_342_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
static lean_object* _init_l_panic___at___00Lean_Cadical_Solver_clause_spec__1___closed__0(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = l_instInhabitedError;
v___x_347_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_347_, 0, lean_box(0));
lean_closure_set(v___x_347_, 1, lean_box(0));
lean_closure_set(v___x_347_, 2, v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_clause_spec__1(lean_object* v_msg_348_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_806__overap_351_; lean_object* v___x_352_; 
v___x_350_ = lean_obj_once(&l_panic___at___00Lean_Cadical_Solver_clause_spec__1___closed__0, &l_panic___at___00Lean_Cadical_Solver_clause_spec__1___closed__0_once, _init_l_panic___at___00Lean_Cadical_Solver_clause_spec__1___closed__0);
v___x_806__overap_351_ = lean_panic_fn_borrowed(v___x_350_, v_msg_348_);
v___x_352_ = lean_apply_1(v___x_806__overap_351_, lean_box(0));
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_clause_spec__1___boxed(lean_object* v_msg_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_panic___at___00Lean_Cadical_Solver_clause_spec__1(v_msg_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Lean_Cadical_Solver_clause_spec__0(lean_object* v_s_356_, lean_object* v_c_357_, size_t v_sz_358_, size_t v_i_359_, lean_object* v_b_360_){
_start:
{
uint8_t v___x_362_; 
v___x_362_ = lean_usize_dec_lt(v_i_359_, v_sz_358_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v_b_360_);
return v___x_363_;
}
else
{
lean_object* v_atoms_364_; lean_object* v_polarities_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_lit_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v_atoms_364_ = lean_ctor_get(v_c_357_, 0);
v_polarities_365_ = lean_ctor_get(v_c_357_, 1);
v___x_366_ = lean_array_uget_borrowed(v_atoms_364_, v_i_359_);
v___x_367_ = lean_unsigned_to_nat(1u);
v_lit_368_ = lean_nat_add(v___x_366_, v___x_367_);
v___x_369_ = lean_obj_once(&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2, &l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2_once, _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2);
v___x_370_ = lean_nat_dec_lt(v___x_369_, v_lit_368_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; uint32_t v_a_373_; uint8_t v___x_379_; uint8_t v___x_380_; uint8_t v___x_381_; uint32_t v_lit_382_; 
v___x_371_ = lean_box(0);
v___x_379_ = lean_byte_array_uget(v_polarities_365_, v_i_359_);
v___x_380_ = 1;
v___x_381_ = lean_uint8_dec_eq(v___x_379_, v___x_380_);
v_lit_382_ = lean_int32_of_nat(v_lit_368_);
lean_dec(v_lit_368_);
if (v___x_381_ == 0)
{
uint32_t v___x_383_; 
v___x_383_ = lean_int32_neg(v_lit_382_);
v_a_373_ = v___x_383_;
goto v___jp_372_;
}
else
{
v_a_373_ = v_lit_382_;
goto v___jp_372_;
}
v___jp_372_:
{
lean_object* v_solver_374_; lean_object* v___x_375_; size_t v___x_376_; size_t v___x_377_; 
v_solver_374_ = lean_ctor_get(v_s_356_, 0);
v___x_375_ = lean_cadical_solver_add(v_solver_374_, v_a_373_);
v___x_376_ = ((size_t)1ULL);
v___x_377_ = lean_usize_add(v_i_359_, v___x_376_);
v_i_359_ = v___x_377_;
v_b_360_ = v___x_371_;
goto _start;
}
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec(v_lit_368_);
v___x_384_ = ((lean_object*)(l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__4));
v___x_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Lean_Cadical_Solver_clause_spec__0___boxed(lean_object* v_s_386_, lean_object* v_c_387_, lean_object* v_sz_388_, lean_object* v_i_389_, lean_object* v_b_390_, lean_object* v___y_391_){
_start:
{
size_t v_sz_boxed_392_; size_t v_i_boxed_393_; lean_object* v_res_394_; 
v_sz_boxed_392_ = lean_unbox_usize(v_sz_388_);
lean_dec(v_sz_388_);
v_i_boxed_393_ = lean_unbox_usize(v_i_389_);
lean_dec(v_i_389_);
v_res_394_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Lean_Cadical_Solver_clause_spec__0(v_s_386_, v_c_387_, v_sz_boxed_392_, v_i_boxed_393_, v_b_390_);
lean_dec_ref(v_c_387_);
lean_dec_ref(v_s_386_);
return v_res_394_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_clause___closed__3(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_398_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__2));
v___x_399_ = lean_unsigned_to_nat(2u);
v___x_400_ = lean_unsigned_to_nat(176u);
v___x_401_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__1));
v___x_402_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_403_ = l_mkPanicMessageWithDecl(v___x_402_, v___x_401_, v___x_400_, v___x_399_, v___x_398_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_clause(lean_object* v_s_404_, lean_object* v_clause_405_){
_start:
{
uint16_t v___x_407_; uint16_t v___x_408_; uint16_t v___x_409_; uint16_t v___x_410_; uint8_t v___x_411_; 
v___x_407_ = l_Lean_Cadical_Solver_state(v_s_404_);
v___x_408_ = 366;
v___x_409_ = lean_uint16_land(v___x_407_, v___x_408_);
v___x_410_ = lean_uint16_once(&l_Lean_Cadical_State_isReady___closed__1, &l_Lean_Cadical_State_isReady___closed__1_once, _init_l_Lean_Cadical_State_isReady___closed__1);
v___x_411_ = lean_uint16_dec_eq(v___x_409_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v_atoms_412_; lean_object* v___x_413_; size_t v_sz_414_; size_t v___x_415_; lean_object* v___x_416_; 
v_atoms_412_ = lean_ctor_get(v_clause_405_, 0);
v___x_413_ = lean_box(0);
v_sz_414_ = lean_array_size(v_atoms_412_);
v___x_415_ = ((size_t)0ULL);
v___x_416_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00Lean_Cadical_Solver_clause_spec__0(v_s_404_, v_clause_405_, v_sz_414_, v___x_415_, v___x_413_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_426_; 
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_426_ == 0)
{
lean_object* v_unused_427_; 
v_unused_427_ = lean_ctor_get(v___x_416_, 0);
lean_dec(v_unused_427_);
v___x_418_ = v___x_416_;
v_isShared_419_ = v_isSharedCheck_426_;
goto v_resetjp_417_;
}
else
{
lean_dec(v___x_416_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_426_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v_solver_420_; uint32_t v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
v_solver_420_ = lean_ctor_get(v_s_404_, 0);
v___x_421_ = lean_uint32_once(&l_Lean_Cadical_Status_toInt32___closed__2, &l_Lean_Cadical_Status_toInt32___closed__2_once, _init_l_Lean_Cadical_Status_toInt32___closed__2);
v___x_422_ = lean_cadical_solver_add(v_solver_420_, v___x_421_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_422_);
v___x_424_ = v___x_418_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
else
{
return v___x_416_;
}
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_obj_once(&l_Lean_Cadical_Solver_clause___closed__3, &l_Lean_Cadical_Solver_clause___closed__3_once, _init_l_Lean_Cadical_Solver_clause___closed__3);
v___x_429_ = l_panic___at___00Lean_Cadical_Solver_clause_spec__1(v___x_428_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_clause___boxed(lean_object* v_s_430_, lean_object* v_clause_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_Cadical_Solver_clause(v_s_430_, v_clause_431_);
lean_dec_ref(v_clause_431_);
lean_dec_ref(v_s_430_);
return v_res_433_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_inconsistent(lean_object* v_s_434_){
_start:
{
lean_object* v_solver_436_; uint8_t v___x_437_; 
v_solver_436_ = lean_ctor_get(v_s_434_, 0);
v___x_437_ = lean_cadical_solver_inconsistent(v_solver_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_inconsistent___boxed(lean_object* v_s_438_, lean_object* v_a_439_){
_start:
{
uint8_t v_res_440_; lean_object* v_r_441_; 
v_res_440_ = l_Lean_Cadical_Solver_inconsistent(v_s_438_);
lean_dec_ref(v_s_438_);
v_r_441_ = lean_box(v_res_440_);
return v_r_441_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_assume___closed__2(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_444_ = ((lean_object*)(l_Lean_Cadical_Solver_assume___closed__1));
v___x_445_ = lean_unsigned_to_nat(2u);
v___x_446_ = lean_unsigned_to_nat(191u);
v___x_447_ = ((lean_object*)(l_Lean_Cadical_Solver_assume___closed__0));
v___x_448_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_449_ = l_mkPanicMessageWithDecl(v___x_448_, v___x_447_, v___x_446_, v___x_445_, v___x_444_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_assume(lean_object* v_s_450_, lean_object* v_lit_451_, uint8_t v_pol_452_){
_start:
{
uint32_t v_a_455_; uint16_t v___x_465_; uint16_t v___x_466_; uint16_t v___x_467_; uint16_t v___x_468_; uint8_t v___x_469_; 
v___x_465_ = l_Lean_Cadical_Solver_state(v_s_450_);
v___x_466_ = 358;
v___x_467_ = lean_uint16_land(v___x_465_, v___x_466_);
v___x_468_ = lean_uint16_once(&l_Lean_Cadical_State_isReady___closed__1, &l_Lean_Cadical_State_isReady___closed__1_once, _init_l_Lean_Cadical_State_isReady___closed__1);
v___x_469_ = lean_uint16_dec_eq(v___x_467_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v_lit_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_470_ = lean_unsigned_to_nat(1u);
v_lit_471_ = lean_nat_add(v_lit_451_, v___x_470_);
v___x_472_ = lean_obj_once(&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2, &l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2_once, _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2);
v___x_473_ = lean_nat_dec_lt(v___x_472_, v_lit_471_);
if (v___x_473_ == 0)
{
uint32_t v_lit_474_; 
v_lit_474_ = lean_int32_of_nat(v_lit_471_);
lean_dec(v_lit_471_);
if (v_pol_452_ == 0)
{
uint32_t v___x_475_; 
v___x_475_ = lean_int32_neg(v_lit_474_);
v_a_455_ = v___x_475_;
goto v___jp_454_;
}
else
{
v_a_455_ = v_lit_474_;
goto v___jp_454_;
}
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; 
lean_dec(v_lit_471_);
lean_dec_ref(v_s_450_);
v___x_476_ = ((lean_object*)(l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__4));
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
return v___x_477_;
}
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec_ref(v_s_450_);
v___x_478_ = lean_obj_once(&l_Lean_Cadical_Solver_assume___closed__2, &l_Lean_Cadical_Solver_assume___closed__2_once, _init_l_Lean_Cadical_Solver_assume___closed__2);
v___x_479_ = l_panic___at___00Lean_Cadical_Solver_clause_spec__1(v___x_478_);
return v___x_479_;
}
v___jp_454_:
{
lean_object* v_solver_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_464_; 
v_solver_456_ = lean_ctor_get(v_s_450_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v_s_450_);
if (v_isSharedCheck_464_ == 0)
{
v___x_458_ = v_s_450_;
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_solver_456_);
lean_dec(v_s_450_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = lean_cadical_solver_assume(v_solver_456_, v_a_455_);
lean_dec(v_solver_456_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_460_);
v___x_462_ = v___x_458_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_assume___boxed(lean_object* v_s_480_, lean_object* v_lit_481_, lean_object* v_pol_482_, lean_object* v_a_483_){
_start:
{
uint8_t v_pol_boxed_484_; lean_object* v_res_485_; 
v_pol_boxed_484_ = lean_unbox(v_pol_482_);
v_res_485_ = l_Lean_Cadical_Solver_assume(v_s_480_, v_lit_481_, v_pol_boxed_484_);
lean_dec(v_lit_481_);
return v_res_485_;
}
}
static lean_object* _init_l_panic___at___00Lean_Cadical_Solver_solve_spec__0___closed__0(void){
_start:
{
uint8_t v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_486_ = 0;
v___x_487_ = l_instMonadBaseIO;
v___x_488_ = lean_box(v___x_486_);
v___x_489_ = l_instInhabitedOfMonad___redArg(v___x_487_, v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Cadical_Solver_solve_spec__0(lean_object* v_msg_490_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_211__overap_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_492_ = lean_obj_once(&l_panic___at___00Lean_Cadical_Solver_solve_spec__0___closed__0, &l_panic___at___00Lean_Cadical_Solver_solve_spec__0___closed__0_once, _init_l_panic___at___00Lean_Cadical_Solver_solve_spec__0___closed__0);
v___x_211__overap_493_ = lean_panic_fn_borrowed(v___x_492_, v_msg_490_);
v___x_494_ = lean_apply_1(v___x_211__overap_493_, lean_box(0));
v___x_495_ = lean_unbox(v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_solve_spec__0___boxed(lean_object* v_msg_496_, lean_object* v___y_497_){
_start:
{
uint8_t v_res_498_; lean_object* v_r_499_; 
v_res_498_ = l_panic___at___00Lean_Cadical_Solver_solve_spec__0(v_msg_496_);
v_r_499_ = lean_box(v_res_498_);
return v_r_499_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_solve___closed__2(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_502_ = ((lean_object*)(l_Lean_Cadical_Solver_solve___closed__1));
v___x_503_ = lean_unsigned_to_nat(2u);
v___x_504_ = lean_unsigned_to_nat(198u);
v___x_505_ = ((lean_object*)(l_Lean_Cadical_Solver_solve___closed__0));
v___x_506_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_507_ = l_mkPanicMessageWithDecl(v___x_506_, v___x_505_, v___x_504_, v___x_503_, v___x_502_);
return v___x_507_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_solve(lean_object* v_s_508_){
_start:
{
uint16_t v___x_510_; uint16_t v___x_511_; uint16_t v___x_512_; uint16_t v___x_513_; uint8_t v___x_514_; 
v___x_510_ = l_Lean_Cadical_Solver_state(v_s_508_);
v___x_511_ = 358;
v___x_512_ = lean_uint16_land(v___x_510_, v___x_511_);
v___x_513_ = lean_uint16_once(&l_Lean_Cadical_State_isReady___closed__1, &l_Lean_Cadical_State_isReady___closed__1_once, _init_l_Lean_Cadical_State_isReady___closed__1);
v___x_514_ = lean_uint16_dec_eq(v___x_512_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v_solver_515_; uint8_t v___x_516_; 
v_solver_515_ = lean_ctor_get(v_s_508_, 0);
v___x_516_ = lean_cadical_solver_solve(v_solver_515_);
switch(v___x_516_)
{
case 0:
{
uint8_t v___x_517_; 
v___x_517_ = 0;
return v___x_517_;
}
case 1:
{
uint8_t v___x_518_; 
v___x_518_ = 1;
return v___x_518_;
}
default: 
{
uint8_t v___x_519_; 
v___x_519_ = 2;
return v___x_519_;
}
}
}
else
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = lean_obj_once(&l_Lean_Cadical_Solver_solve___closed__2, &l_Lean_Cadical_Solver_solve___closed__2_once, _init_l_Lean_Cadical_Solver_solve___closed__2);
v___x_521_ = l_panic___at___00Lean_Cadical_Solver_solve_spec__0(v___x_520_);
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_solve___boxed(lean_object* v_s_522_, lean_object* v_a_523_){
_start:
{
uint8_t v_res_524_; lean_object* v_r_525_; 
v_res_524_ = l_Lean_Cadical_Solver_solve(v_s_522_);
lean_dec_ref(v_s_522_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_val___closed__1(void){
_start:
{
uint16_t v___x_527_; lean_object* v___x_528_; 
v___x_527_ = 32;
v___x_528_ = l_Lean_Cadical_State_toString(v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_val___closed__2(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_obj_once(&l_Lean_Cadical_Solver_val___closed__1, &l_Lean_Cadical_Solver_val___closed__1_once, _init_l_Lean_Cadical_Solver_val___closed__1);
v___x_530_ = ((lean_object*)(l_Lean_Cadical_Solver_val___closed__0));
v___x_531_ = lean_string_append(v___x_530_, v___x_529_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_val___closed__4(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = ((lean_object*)(l_Lean_Cadical_Solver_val___closed__3));
v___x_534_ = lean_obj_once(&l_Lean_Cadical_Solver_val___closed__2, &l_Lean_Cadical_Solver_val___closed__2_once, _init_l_Lean_Cadical_Solver_val___closed__2);
v___x_535_ = lean_string_append(v___x_534_, v___x_533_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_val(lean_object* v_s_536_, lean_object* v_lit_537_){
_start:
{
uint16_t v___x_539_; uint16_t v___x_540_; uint8_t v___x_541_; 
v___x_539_ = l_Lean_Cadical_Solver_state(v_s_536_);
v___x_540_ = 32;
v___x_541_ = lean_uint16_dec_eq(v___x_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec_ref(v_s_536_);
v___x_542_ = lean_obj_once(&l_Lean_Cadical_Solver_val___closed__4, &l_Lean_Cadical_Solver_val___closed__4_once, _init_l_Lean_Cadical_Solver_val___closed__4);
v___x_543_ = l_Lean_Cadical_State_toString(v___x_539_);
v___x_544_ = lean_string_append(v___x_542_, v___x_543_);
lean_dec_ref(v___x_543_);
v___x_545_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
else
{
lean_object* v___x_547_; lean_object* v_lit_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_547_ = lean_unsigned_to_nat(1u);
v_lit_548_ = lean_nat_add(v_lit_537_, v___x_547_);
v___x_549_ = lean_obj_once(&l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2, &l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2_once, _init_l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__2);
v___x_550_ = lean_nat_dec_lt(v___x_549_, v_lit_548_);
if (v___x_550_ == 0)
{
lean_object* v_solver_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_562_; 
v_solver_551_ = lean_ctor_get(v_s_536_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v_s_536_);
if (v_isSharedCheck_562_ == 0)
{
v___x_553_ = v_s_536_;
v_isShared_554_ = v_isSharedCheck_562_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_solver_551_);
lean_dec(v_s_536_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_562_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
uint32_t v_lit_555_; uint32_t v___x_556_; uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
v_lit_555_ = lean_int32_of_nat(v_lit_548_);
lean_dec(v_lit_548_);
v___x_556_ = lean_cadical_solver_val(v_solver_551_, v_lit_555_);
lean_dec(v_solver_551_);
v___x_557_ = lean_int32_dec_eq(v_lit_555_, v___x_556_);
v___x_558_ = lean_box(v___x_557_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_558_);
v___x_560_ = v___x_553_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec(v_lit_548_);
lean_dec_ref(v_s_536_);
v___x_563_ = ((lean_object*)(l___private_Lean_Cadical_Basic_0__Lean_Cadical_Solver_toApiLit___closed__4));
v___x_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_val___boxed(lean_object* v_s_565_, lean_object* v_lit_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_Cadical_Solver_val(v_s_565_, v_lit_566_);
lean_dec(v_lit_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_resetAssumptions(lean_object* v_s_569_){
_start:
{
lean_object* v_solver_571_; lean_object* v___x_572_; 
v_solver_571_ = lean_ctor_get(v_s_569_, 0);
v___x_572_ = lean_cadical_solver_reset_assumptions(v_solver_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_resetAssumptions___boxed(lean_object* v_s_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Cadical_Solver_resetAssumptions(v_s_573_);
lean_dec_ref(v_s_573_);
return v_res_575_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_status(lean_object* v_s_576_){
_start:
{
lean_object* v_solver_578_; uint8_t v___x_579_; 
v_solver_578_ = lean_ctor_get(v_s_576_, 0);
v___x_579_ = lean_cadical_solver_status(v_solver_578_);
switch(v___x_579_)
{
case 0:
{
uint8_t v___x_580_; 
v___x_580_ = 0;
return v___x_580_;
}
case 1:
{
uint8_t v___x_581_; 
v___x_581_ = 1;
return v___x_581_;
}
default: 
{
uint8_t v___x_582_; 
v___x_582_ = 2;
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_status___boxed(lean_object* v_s_583_, lean_object* v_a_584_){
_start:
{
uint8_t v_res_585_; lean_object* v_r_586_; 
v_res_585_ = l_Lean_Cadical_Solver_status(v_s_583_);
lean_dec_ref(v_s_583_);
v_r_586_ = lean_box(v_res_585_);
return v_r_586_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_isValidOption(lean_object* v_opt_587_){
_start:
{
uint8_t v___x_588_; 
v___x_588_ = lean_cadical_solver_is_valid_option(v_opt_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_isValidOption___boxed(lean_object* v_opt_589_){
_start:
{
uint8_t v_res_590_; lean_object* v_r_591_; 
v_res_590_ = l_Lean_Cadical_Solver_isValidOption(v_opt_589_);
lean_dec_ref(v_opt_589_);
v_r_591_ = lean_box(v_res_590_);
return v_r_591_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_isPreprocessingOption(lean_object* v_opt_592_){
_start:
{
uint8_t v___x_593_; 
v___x_593_ = lean_cadical_solver_is_preprocessing_option(v_opt_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_isPreprocessingOption___boxed(lean_object* v_opt_594_){
_start:
{
uint8_t v_res_595_; lean_object* v_r_596_; 
v_res_595_ = l_Lean_Cadical_Solver_isPreprocessingOption(v_opt_594_);
lean_dec_ref(v_opt_594_);
v_r_596_ = lean_box(v_res_595_);
return v_r_596_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_isValidLongOption(lean_object* v_opt_597_){
_start:
{
uint8_t v___x_598_; 
v___x_598_ = lean_cadical_solver_is_valid_long_option(v_opt_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_isValidLongOption___boxed(lean_object* v_opt_599_){
_start:
{
uint8_t v_res_600_; lean_object* v_r_601_; 
v_res_600_ = l_Lean_Cadical_Solver_isValidLongOption(v_opt_599_);
lean_dec_ref(v_opt_599_);
v_r_601_ = lean_box(v_res_600_);
return v_r_601_;
}
}
LEAN_EXPORT uint32_t l_Lean_Cadical_Solver_getOption(lean_object* v_s_602_, lean_object* v_opt_603_){
_start:
{
lean_object* v_solver_605_; uint32_t v___x_606_; 
v_solver_605_ = lean_ctor_get(v_s_602_, 0);
v___x_606_ = lean_cadical_solver_get(v_solver_605_, v_opt_603_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_getOption___boxed(lean_object* v_s_607_, lean_object* v_opt_608_, lean_object* v_a_609_){
_start:
{
uint32_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l_Lean_Cadical_Solver_getOption(v_s_607_, v_opt_608_);
lean_dec_ref(v_opt_608_);
lean_dec_ref(v_s_607_);
v_r_611_ = lean_box_uint32(v_res_610_);
return v_r_611_;
}
}
static lean_object* _init_l_panic___at___00Lean_Cadical_Solver_setOption_spec__0___closed__0(void){
_start:
{
uint8_t v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_612_ = 0;
v___x_613_ = l_instMonadBaseIO;
v___x_614_ = lean_box(v___x_612_);
v___x_615_ = l_instInhabitedOfMonad___redArg(v___x_613_, v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Cadical_Solver_setOption_spec__0(lean_object* v_msg_616_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_132__overap_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_618_ = lean_obj_once(&l_panic___at___00Lean_Cadical_Solver_setOption_spec__0___closed__0, &l_panic___at___00Lean_Cadical_Solver_setOption_spec__0___closed__0_once, _init_l_panic___at___00Lean_Cadical_Solver_setOption_spec__0___closed__0);
v___x_132__overap_619_ = lean_panic_fn_borrowed(v___x_618_, v_msg_616_);
v___x_620_ = lean_apply_1(v___x_132__overap_619_, lean_box(0));
v___x_621_ = lean_unbox(v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_setOption_spec__0___boxed(lean_object* v_msg_622_, lean_object* v___y_623_){
_start:
{
uint8_t v_res_624_; lean_object* v_r_625_; 
v_res_624_ = l_panic___at___00Lean_Cadical_Solver_setOption_spec__0(v_msg_622_);
v_r_625_ = lean_box(v_res_624_);
return v_r_625_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_setOption___closed__2(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_628_ = ((lean_object*)(l_Lean_Cadical_Solver_setOption___closed__1));
v___x_629_ = lean_unsigned_to_nat(2u);
v___x_630_ = lean_unsigned_to_nat(235u);
v___x_631_ = ((lean_object*)(l_Lean_Cadical_Solver_setOption___closed__0));
v___x_632_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_633_ = l_mkPanicMessageWithDecl(v___x_632_, v___x_631_, v___x_630_, v___x_629_, v___x_628_);
return v___x_633_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_setOption(lean_object* v_s_634_, lean_object* v_opt_635_, uint32_t v_val_636_){
_start:
{
uint16_t v___x_638_; uint16_t v___x_639_; uint8_t v___x_640_; 
v___x_638_ = l_Lean_Cadical_Solver_state(v_s_634_);
v___x_639_ = 2;
v___x_640_ = lean_uint16_dec_eq(v___x_638_, v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_obj_once(&l_Lean_Cadical_Solver_setOption___closed__2, &l_Lean_Cadical_Solver_setOption___closed__2_once, _init_l_Lean_Cadical_Solver_setOption___closed__2);
v___x_642_ = l_panic___at___00Lean_Cadical_Solver_setOption_spec__0(v___x_641_);
return v___x_642_;
}
else
{
lean_object* v_solver_643_; uint8_t v___x_644_; 
v_solver_643_ = lean_ctor_get(v_s_634_, 0);
v___x_644_ = lean_cadical_solver_set(v_solver_643_, v_opt_635_, v_val_636_);
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_setOption___boxed(lean_object* v_s_645_, lean_object* v_opt_646_, lean_object* v_val_647_, lean_object* v_a_648_){
_start:
{
uint32_t v_val_boxed_649_; uint8_t v_res_650_; lean_object* v_r_651_; 
v_val_boxed_649_ = lean_unbox_uint32(v_val_647_);
lean_dec(v_val_647_);
v_res_650_ = l_Lean_Cadical_Solver_setOption(v_s_645_, v_opt_646_, v_val_boxed_649_);
lean_dec_ref(v_opt_646_);
lean_dec_ref(v_s_645_);
v_r_651_ = lean_box(v_res_650_);
return v_r_651_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_setLongOption___closed__2(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_654_ = ((lean_object*)(l_Lean_Cadical_Solver_setLongOption___closed__1));
v___x_655_ = lean_unsigned_to_nat(2u);
v___x_656_ = lean_unsigned_to_nat(239u);
v___x_657_ = ((lean_object*)(l_Lean_Cadical_Solver_setLongOption___closed__0));
v___x_658_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_659_ = l_mkPanicMessageWithDecl(v___x_658_, v___x_657_, v___x_656_, v___x_655_, v___x_654_);
return v___x_659_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_setLongOption(lean_object* v_s_660_, lean_object* v_opt_661_){
_start:
{
uint16_t v___x_663_; uint16_t v___x_664_; uint8_t v___x_665_; 
v___x_663_ = l_Lean_Cadical_Solver_state(v_s_660_);
v___x_664_ = 2;
v___x_665_ = lean_uint16_dec_eq(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = lean_obj_once(&l_Lean_Cadical_Solver_setLongOption___closed__2, &l_Lean_Cadical_Solver_setLongOption___closed__2_once, _init_l_Lean_Cadical_Solver_setLongOption___closed__2);
v___x_667_ = l_panic___at___00Lean_Cadical_Solver_setOption_spec__0(v___x_666_);
return v___x_667_;
}
else
{
lean_object* v_solver_668_; uint8_t v___x_669_; 
v_solver_668_ = lean_ctor_get(v_s_660_, 0);
v___x_669_ = lean_cadical_solver_set_long_option(v_solver_668_, v_opt_661_);
return v___x_669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_setLongOption___boxed(lean_object* v_s_670_, lean_object* v_opt_671_, lean_object* v_a_672_){
_start:
{
uint8_t v_res_673_; lean_object* v_r_674_; 
v_res_673_ = l_Lean_Cadical_Solver_setLongOption(v_s_670_, v_opt_671_);
lean_dec_ref(v_opt_671_);
lean_dec_ref(v_s_670_);
v_r_674_ = lean_box(v_res_673_);
return v_r_674_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_isValidConfiguration(lean_object* v_opt_675_){
_start:
{
uint8_t v___x_676_; 
v___x_676_ = lean_cadical_solver_is_valid_configuration(v_opt_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_isValidConfiguration___boxed(lean_object* v_opt_677_){
_start:
{
uint8_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = l_Lean_Cadical_Solver_isValidConfiguration(v_opt_677_);
lean_dec_ref(v_opt_677_);
v_r_679_ = lean_box(v_res_678_);
return v_r_679_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_configure___closed__2(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_682_ = ((lean_object*)(l_Lean_Cadical_Solver_configure___closed__1));
v___x_683_ = lean_unsigned_to_nat(2u);
v___x_684_ = lean_unsigned_to_nat(245u);
v___x_685_ = ((lean_object*)(l_Lean_Cadical_Solver_configure___closed__0));
v___x_686_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_687_ = l_mkPanicMessageWithDecl(v___x_686_, v___x_685_, v___x_684_, v___x_683_, v___x_682_);
return v___x_687_;
}
}
LEAN_EXPORT uint8_t l_Lean_Cadical_Solver_configure(lean_object* v_s_688_, lean_object* v_opt_689_){
_start:
{
uint16_t v___x_691_; uint16_t v___x_692_; uint8_t v___x_693_; 
v___x_691_ = l_Lean_Cadical_Solver_state(v_s_688_);
v___x_692_ = 2;
v___x_693_ = lean_uint16_dec_eq(v___x_691_, v___x_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = lean_obj_once(&l_Lean_Cadical_Solver_configure___closed__2, &l_Lean_Cadical_Solver_configure___closed__2_once, _init_l_Lean_Cadical_Solver_configure___closed__2);
v___x_695_ = l_panic___at___00Lean_Cadical_Solver_setOption_spec__0(v___x_694_);
return v___x_695_;
}
else
{
lean_object* v_solver_696_; uint8_t v___x_697_; 
v_solver_696_ = lean_ctor_get(v_s_688_, 0);
v___x_697_ = lean_cadical_solver_configure(v_solver_696_, v_opt_689_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_configure___boxed(lean_object* v_s_698_, lean_object* v_opt_699_, lean_object* v_a_700_){
_start:
{
uint8_t v_res_701_; lean_object* v_r_702_; 
v_res_701_ = l_Lean_Cadical_Solver_configure(v_s_698_, v_opt_699_);
lean_dec_ref(v_opt_699_);
lean_dec_ref(v_s_698_);
v_r_702_ = lean_box(v_res_701_);
return v_r_702_;
}
}
static lean_object* _init_l_panic___at___00Lean_Cadical_Solver_terminate_spec__0___closed__0(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = lean_box(0);
v___x_704_ = l_instMonadBaseIO;
v___x_705_ = l_instInhabitedOfMonad___redArg(v___x_704_, v___x_703_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_terminate_spec__0(lean_object* v_msg_706_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_246__overap_709_; lean_object* v___x_710_; 
v___x_708_ = lean_obj_once(&l_panic___at___00Lean_Cadical_Solver_terminate_spec__0___closed__0, &l_panic___at___00Lean_Cadical_Solver_terminate_spec__0___closed__0_once, _init_l_panic___at___00Lean_Cadical_Solver_terminate_spec__0___closed__0);
v___x_246__overap_709_ = lean_panic_fn_borrowed(v___x_708_, v_msg_706_);
v___x_710_ = lean_apply_1(v___x_246__overap_709_, lean_box(0));
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Cadical_Solver_terminate_spec__0___boxed(lean_object* v_msg_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_panic___at___00Lean_Cadical_Solver_terminate_spec__0(v_msg_711_);
return v_res_713_;
}
}
static lean_object* _init_l_Lean_Cadical_Solver_terminate___closed__2(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_716_ = ((lean_object*)(l_Lean_Cadical_Solver_terminate___closed__1));
v___x_717_ = lean_unsigned_to_nat(2u);
v___x_718_ = lean_unsigned_to_nat(250u);
v___x_719_ = ((lean_object*)(l_Lean_Cadical_Solver_terminate___closed__0));
v___x_720_ = ((lean_object*)(l_Lean_Cadical_Solver_clause___closed__0));
v___x_721_ = l_mkPanicMessageWithDecl(v___x_720_, v___x_719_, v___x_718_, v___x_717_, v___x_716_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_terminate(lean_object* v_s_722_){
_start:
{
uint16_t v___x_724_; uint16_t v___x_728_; uint8_t v___x_729_; 
v___x_724_ = l_Lean_Cadical_Solver_state(v_s_722_);
v___x_728_ = 16;
v___x_729_ = lean_uint16_dec_eq(v___x_724_, v___x_728_);
if (v___x_729_ == 0)
{
uint16_t v___x_730_; uint16_t v___x_731_; uint16_t v___x_732_; uint8_t v___x_733_; 
v___x_730_ = 358;
v___x_731_ = lean_uint16_land(v___x_724_, v___x_730_);
v___x_732_ = lean_uint16_once(&l_Lean_Cadical_State_isReady___closed__1, &l_Lean_Cadical_State_isReady___closed__1_once, _init_l_Lean_Cadical_State_isReady___closed__1);
v___x_733_ = lean_uint16_dec_eq(v___x_731_, v___x_732_);
if (v___x_733_ == 0)
{
goto v___jp_725_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_obj_once(&l_Lean_Cadical_Solver_terminate___closed__2, &l_Lean_Cadical_Solver_terminate___closed__2_once, _init_l_Lean_Cadical_Solver_terminate___closed__2);
v___x_735_ = l_panic___at___00Lean_Cadical_Solver_terminate_spec__0(v___x_734_);
return v___x_735_;
}
}
else
{
goto v___jp_725_;
}
v___jp_725_:
{
lean_object* v_solver_726_; lean_object* v___x_727_; 
v_solver_726_ = lean_ctor_get(v_s_722_, 0);
v___x_727_ = lean_cadical_solver_terminate(v_solver_726_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_terminate___boxed(lean_object* v_s_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_Cadical_Solver_terminate(v_s_736_);
lean_dec_ref(v_s_736_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printConfigurations(){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = lean_cadical_solver_configurations();
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printConfigurations___boxed(lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Cadical_Solver_printConfigurations();
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printStatistics(lean_object* v_s_743_){
_start:
{
lean_object* v_solver_745_; lean_object* v___x_746_; 
v_solver_745_ = lean_ctor_get(v_s_743_, 0);
v___x_746_ = lean_cadical_solver_statistics(v_solver_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printStatistics___boxed(lean_object* v_s_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_Cadical_Solver_printStatistics(v_s_747_);
lean_dec_ref(v_s_747_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printResources(lean_object* v_s_750_){
_start:
{
lean_object* v_solver_752_; lean_object* v___x_753_; 
v_solver_752_ = lean_ctor_get(v_s_750_, 0);
v___x_753_ = lean_cadical_solver_resources(v_solver_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Cadical_Solver_printResources___boxed(lean_object* v_s_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_Cadical_Solver_printResources(v_s_754_);
lean_dec_ref(v_s_754_);
return v_res_756_;
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
