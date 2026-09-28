// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.External
// Imports: import Std.Tactic.BVDecide.LRAT.Parser public import Lean.CoreM public import Std.Tactic.BVDecide.Syntax
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_io_process_child_try_wait(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_IO_sleep(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_io_process_child_kill(lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint32_t lean_uint8_to_uint32(uint8_t);
uint8_t lean_uint32_to_uint8(uint32_t);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* lean_int_neg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_sat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_sat_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_unsat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_unsat_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '32'"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "digit expected"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "id was 0"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__4_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__0(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__1(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "expected: '118'"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__1_value;
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " 0"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '10'"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__7_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines_go(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "s SATISFIABLE"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_success_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_success_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_timeout_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_timeout_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--unsat"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "--sat"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__2_value;
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "--default"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__4_value;
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__4_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___boxed(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "The external prover produced unexpected output, stdout:\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nstderr:\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Error "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " while parsing:\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--lrat"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__4_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "--binary="};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__5_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--quiet"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__6_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "--shrink=0"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 2, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__8_value;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__9_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "s UNSATISFIABLE"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__10_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Failed to execute external prover:\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__11_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 245, .m_capacity = 245, .m_length = 244, .m_data = "The SAT solver timed out while solving the problem.\nConsider increasing the timeout with the `timeout` config option.\nIf solving your problem relies inherently on using associativity or commutativity, consider enabling the `acNf` config option."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__12_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__14;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__15 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__15_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__16 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorIdx(v_x_4_);
lean_dec(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_assignment_8_; lean_object* v___x_9_; 
v_assignment_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_assignment_8_);
lean_dec_ref_known(v_t_6_, 1);
v___x_9_ = lean_apply_1(v_k_7_, v_assignment_8_);
return v___x_9_;
}
else
{
return v_k_7_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_sat_elim___redArg(lean_object* v_t_22_, lean_object* v_sat_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(v_t_22_, v_sat_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_sat_elim(lean_object* v_motive_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_sat_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(v_t_26_, v_sat_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_unsat_elim___redArg(lean_object* v_t_30_, lean_object* v_unsat_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(v_t_30_, v_unsat_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_unsat_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_unsat_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(v_t_34_, v_unsat_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit(lean_object* v_a_47_){
_start:
{
lean_object* v_array_48_; lean_object* v_idx_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v_array_48_ = lean_ctor_get(v_a_47_, 0);
v_idx_49_ = lean_ctor_get(v_a_47_, 1);
v___x_50_ = lean_byte_array_size(v_array_48_);
v___x_51_ = lean_nat_dec_lt(v_idx_49_, v___x_50_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_box(0);
v___x_53_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_53_, 0, v_a_47_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
return v___x_53_;
}
else
{
uint8_t v___x_54_; uint8_t v_got_55_; uint8_t v___x_56_; 
v___x_54_ = 32;
v_got_55_ = lean_byte_array_fget(v_array_48_, v_idx_49_);
v___x_56_ = lean_uint8_dec_eq(v_got_55_, v___x_54_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1));
v___x_58_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_58_, 0, v_a_47_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
return v___x_58_;
}
else
{
lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_142_; 
lean_inc(v_idx_49_);
lean_inc_ref(v_array_48_);
v_isSharedCheck_142_ = !lean_is_exclusive(v_a_47_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; lean_object* v_unused_144_; 
v_unused_143_ = lean_ctor_get(v_a_47_, 1);
lean_dec(v_unused_143_);
v_unused_144_ = lean_ctor_get(v_a_47_, 0);
lean_dec(v_unused_144_);
v___x_60_ = v_a_47_;
v_isShared_61_ = v_isSharedCheck_142_;
goto v_resetjp_59_;
}
else
{
lean_dec(v_a_47_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_142_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_62_ = lean_unsigned_to_nat(1u);
v___x_63_ = lean_nat_add(v_idx_49_, v___x_62_);
lean_dec(v_idx_49_);
lean_inc(v___x_63_);
lean_inc_ref(v_array_48_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 1, v___x_63_);
v___x_65_ = v___x_60_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_array_48_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v___x_63_);
v___x_65_ = v_reuseFailAlloc_141_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
uint8_t v___x_66_; 
v___x_66_ = lean_nat_dec_lt(v___x_63_, v___x_50_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec(v___x_63_);
lean_dec_ref(v_array_48_);
v___x_67_ = lean_box(0);
v___x_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_65_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
return v___x_68_;
}
else
{
uint8_t v___x_69_; uint8_t v___x_70_; uint8_t v___x_71_; 
v___x_69_ = lean_byte_array_fget(v_array_48_, v___x_63_);
v___x_70_ = 45;
v___x_71_ = lean_uint8_dec_eq(v___x_69_, v___x_70_);
if (v___x_71_ == 0)
{
uint8_t v___x_72_; uint8_t v___y_74_; uint8_t v___x_100_; 
v___x_72_ = 48;
v___x_100_ = lean_uint8_dec_le(v___x_72_, v___x_69_);
if (v___x_100_ == 0)
{
v___y_74_ = v___x_100_;
goto v___jp_73_;
}
else
{
uint8_t v___x_101_; uint8_t v___x_102_; 
v___x_101_ = 57;
v___x_102_ = lean_uint8_dec_le(v___x_69_, v___x_101_);
v___y_74_ = v___x_102_;
goto v___jp_73_;
}
v___jp_73_:
{
if (v___y_74_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec(v___x_63_);
lean_dec_ref(v_array_48_);
v___x_75_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3));
v___x_76_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_65_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
return v___x_76_;
}
else
{
lean_object* v___x_77_; lean_object* v_it_x27_78_; uint32_t v___x_79_; uint8_t v___x_80_; uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v_fst_84_; lean_object* v_snd_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_99_; 
lean_dec_ref(v___x_65_);
v___x_77_ = lean_nat_add(v___x_63_, v___x_62_);
lean_dec(v___x_63_);
v_it_x27_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_78_, 0, v_array_48_);
lean_ctor_set(v_it_x27_78_, 1, v___x_77_);
v___x_79_ = lean_uint8_to_uint32(v___x_69_);
v___x_80_ = lean_uint32_to_uint8(v___x_79_);
v___x_81_ = lean_uint8_sub(v___x_80_, v___x_72_);
v___x_82_ = lean_uint8_to_nat(v___x_81_);
v___x_83_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_78_, v___x_82_);
v_fst_84_ = lean_ctor_get(v___x_83_, 0);
v_snd_85_ = lean_ctor_get(v___x_83_, 1);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_99_ == 0)
{
v___x_87_ = v___x_83_;
v_isShared_88_ = v_isSharedCheck_99_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_snd_85_);
lean_inc(v_fst_84_);
lean_dec(v___x_83_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_99_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_nat_dec_eq(v_fst_84_, v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_91_ = lean_nat_to_int(v_fst_84_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 1, v___x_91_);
lean_ctor_set(v___x_87_, 0, v_snd_85_);
v___x_93_ = v___x_87_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_snd_85_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
else
{
lean_object* v___x_95_; lean_object* v___x_97_; 
lean_dec(v_fst_84_);
v___x_95_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5));
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 1);
lean_ctor_set(v___x_87_, 1, v___x_95_);
lean_ctor_set(v___x_87_, 0, v_snd_85_);
v___x_97_ = v___x_87_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_snd_85_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v___x_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
}
else
{
lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
lean_dec_ref(v___x_65_);
v___x_103_ = lean_nat_add(v___x_63_, v___x_62_);
lean_dec(v___x_63_);
lean_inc(v___x_103_);
lean_inc_ref(v_array_48_);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v_array_48_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = lean_nat_dec_lt(v___x_103_, v___x_50_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; 
lean_dec(v___x_103_);
lean_dec_ref(v_array_48_);
v___x_106_ = lean_box(0);
v___x_107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_104_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
return v___x_107_;
}
else
{
uint8_t v_c_108_; uint8_t v___x_109_; uint8_t v___y_111_; uint8_t v___x_138_; 
v_c_108_ = lean_byte_array_fget(v_array_48_, v___x_103_);
v___x_109_ = 48;
v___x_138_ = lean_uint8_dec_le(v___x_109_, v_c_108_);
if (v___x_138_ == 0)
{
v___y_111_ = v___x_138_;
goto v___jp_110_;
}
else
{
uint8_t v___x_139_; uint8_t v___x_140_; 
v___x_139_ = 57;
v___x_140_ = lean_uint8_dec_le(v_c_108_, v___x_139_);
v___y_111_ = v___x_140_;
goto v___jp_110_;
}
v___jp_110_:
{
if (v___y_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_dec(v___x_103_);
lean_dec_ref(v_array_48_);
v___x_112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3));
v___x_113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_104_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
return v___x_113_;
}
else
{
lean_object* v___x_114_; lean_object* v_it_x27_115_; uint32_t v___x_116_; uint8_t v___x_117_; uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_fst_121_; lean_object* v_snd_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_137_; 
lean_dec_ref_known(v___x_104_, 2);
v___x_114_ = lean_nat_add(v___x_103_, v___x_62_);
lean_dec(v___x_103_);
v_it_x27_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_115_, 0, v_array_48_);
lean_ctor_set(v_it_x27_115_, 1, v___x_114_);
v___x_116_ = lean_uint8_to_uint32(v_c_108_);
v___x_117_ = lean_uint32_to_uint8(v___x_116_);
v___x_118_ = lean_uint8_sub(v___x_117_, v___x_109_);
v___x_119_ = lean_uint8_to_nat(v___x_118_);
v___x_120_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_115_, v___x_119_);
v_fst_121_ = lean_ctor_get(v___x_120_, 0);
v_snd_122_ = lean_ctor_get(v___x_120_, 1);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_137_ == 0)
{
v___x_124_ = v___x_120_;
v_isShared_125_ = v_isSharedCheck_137_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_snd_122_);
lean_inc(v_fst_121_);
lean_dec(v___x_120_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_137_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_nat_dec_eq(v_fst_121_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_128_ = lean_nat_to_int(v_fst_121_);
v___x_129_ = lean_int_neg(v___x_128_);
lean_dec(v___x_128_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v___x_129_);
lean_ctor_set(v___x_124_, 0, v_snd_122_);
v___x_131_ = v___x_124_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_snd_122_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
else
{
lean_object* v___x_133_; lean_object* v___x_135_; 
lean_dec(v_fst_121_);
v___x_133_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5));
if (v_isShared_125_ == 0)
{
lean_ctor_set_tag(v___x_124_, 1);
lean_ctor_set(v___x_124_, 1, v___x_133_);
lean_ctor_set(v___x_124_, 0, v_snd_122_);
v___x_135_ = v___x_124_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_snd_122_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__0(lean_object* v_a_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = lean_nat_to_int(v_a_145_);
return v___x_146_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = lean_nat_to_int(v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(size_t v_sz_149_, size_t v_i_150_, lean_object* v_bs_151_){
_start:
{
uint8_t v___x_152_; 
v___x_152_ = lean_usize_dec_lt(v_i_150_, v_sz_149_);
if (v___x_152_ == 0)
{
return v_bs_151_;
}
else
{
lean_object* v_v_153_; lean_object* v___x_154_; lean_object* v_bs_x27_155_; lean_object* v___x_156_; uint8_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; size_t v___x_161_; size_t v___x_162_; lean_object* v___x_163_; 
v_v_153_ = lean_array_uget(v_bs_151_, v_i_150_);
v___x_154_ = lean_unsigned_to_nat(0u);
v_bs_x27_155_ = lean_array_uset(v_bs_151_, v_i_150_, v___x_154_);
v___x_156_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0);
v___x_157_ = lean_int_dec_lt(v___x_156_, v_v_153_);
v___x_158_ = lean_nat_abs(v_v_153_);
lean_dec(v_v_153_);
v___x_159_ = lean_box(v___x_157_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_158_);
v___x_161_ = ((size_t)1ULL);
v___x_162_ = lean_usize_add(v_i_150_, v___x_161_);
v___x_163_ = lean_array_uset(v_bs_x27_155_, v_i_150_, v___x_160_);
v_i_150_ = v___x_162_;
v_bs_151_ = v___x_163_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___boxed(lean_object* v_sz_165_, lean_object* v_i_166_, lean_object* v_bs_167_){
_start:
{
size_t v_sz_boxed_168_; size_t v_i_boxed_169_; lean_object* v_res_170_; 
v_sz_boxed_168_ = lean_unbox_usize(v_sz_165_);
lean_dec(v_sz_165_);
v_i_boxed_169_ = lean_unbox_usize(v_i_166_);
lean_dec(v_i_166_);
v_res_170_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(v_sz_boxed_168_, v_i_boxed_169_, v_bs_167_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__1(lean_object* v_acc_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_pos_174_; lean_object* v_res_175_; lean_object* v_array_178_; lean_object* v_idx_179_; lean_object* v_pos_181_; lean_object* v_idx_182_; lean_object* v_err_183_; lean_object* v___x_187_; uint8_t v___x_188_; 
v_array_178_ = lean_ctor_get(v_a_172_, 0);
v_idx_179_ = lean_ctor_get(v_a_172_, 1);
lean_inc(v_idx_179_);
v___x_187_ = lean_byte_array_size(v_array_178_);
v___x_188_ = lean_nat_dec_lt(v_idx_179_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_box(0);
lean_inc(v_idx_179_);
v_pos_181_ = v_a_172_;
v_idx_182_ = v_idx_179_;
v_err_183_ = v___x_189_;
goto v___jp_180_;
}
else
{
uint8_t v___x_190_; uint8_t v_got_191_; uint8_t v___x_192_; 
v___x_190_ = 32;
v_got_191_ = lean_byte_array_fget(v_array_178_, v_idx_179_);
v___x_192_ = lean_uint8_dec_eq(v_got_191_, v___x_190_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; 
v___x_193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1));
lean_inc(v_idx_179_);
v_pos_181_ = v_a_172_;
v_idx_182_ = v_idx_179_;
v_err_183_ = v___x_193_;
goto v___jp_180_;
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_194_ = lean_unsigned_to_nat(1u);
v___x_195_ = lean_nat_add(v_idx_179_, v___x_194_);
v___x_196_ = lean_nat_dec_lt(v___x_195_, v___x_187_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; 
lean_dec(v___x_195_);
v___x_197_ = lean_box(0);
lean_inc(v_idx_179_);
v_pos_181_ = v_a_172_;
v_idx_182_ = v_idx_179_;
v_err_183_ = v___x_197_;
goto v___jp_180_;
}
else
{
uint8_t v___x_198_; uint8_t v___x_199_; uint8_t v___x_200_; 
v___x_198_ = lean_byte_array_fget(v_array_178_, v___x_195_);
v___x_199_ = 45;
v___x_200_ = lean_uint8_dec_eq(v___x_198_, v___x_199_);
if (v___x_200_ == 0)
{
uint8_t v___x_201_; uint8_t v___y_203_; uint8_t v___x_218_; 
v___x_201_ = 48;
v___x_218_ = lean_uint8_dec_le(v___x_201_, v___x_198_);
if (v___x_218_ == 0)
{
v___y_203_ = v___x_218_;
goto v___jp_202_;
}
else
{
uint8_t v___x_219_; uint8_t v___x_220_; 
v___x_219_ = 57;
v___x_220_ = lean_uint8_dec_le(v___x_198_, v___x_219_);
v___y_203_ = v___x_220_;
goto v___jp_202_;
}
v___jp_202_:
{
if (v___y_203_ == 0)
{
lean_object* v___x_204_; 
lean_dec(v___x_195_);
v___x_204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3));
lean_inc(v_idx_179_);
v_pos_181_ = v_a_172_;
v_idx_182_ = v_idx_179_;
v_err_183_ = v___x_204_;
goto v___jp_180_;
}
else
{
lean_object* v___x_205_; lean_object* v_it_x27_206_; uint32_t v___x_207_; uint8_t v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v_fst_212_; lean_object* v_snd_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_205_ = lean_nat_add(v___x_195_, v___x_194_);
lean_dec(v___x_195_);
lean_inc_ref(v_array_178_);
v_it_x27_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_206_, 0, v_array_178_);
lean_ctor_set(v_it_x27_206_, 1, v___x_205_);
v___x_207_ = lean_uint8_to_uint32(v___x_198_);
v___x_208_ = lean_uint32_to_uint8(v___x_207_);
v___x_209_ = lean_uint8_sub(v___x_208_, v___x_201_);
v___x_210_ = lean_uint8_to_nat(v___x_209_);
v___x_211_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_206_, v___x_210_);
v_fst_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_fst_212_);
v_snd_213_ = lean_ctor_get(v___x_211_, 1);
lean_inc(v_snd_213_);
lean_dec_ref(v___x_211_);
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_nat_dec_eq(v_fst_212_, v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
lean_dec(v_idx_179_);
lean_dec_ref(v_a_172_);
v___x_216_ = lean_nat_to_int(v_fst_212_);
v_pos_174_ = v_snd_213_;
v_res_175_ = v___x_216_;
goto v___jp_173_;
}
else
{
lean_object* v___x_217_; 
lean_dec(v_snd_213_);
lean_dec(v_fst_212_);
v___x_217_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5));
lean_inc(v_idx_179_);
v_pos_181_ = v_a_172_;
v_idx_182_ = v_idx_179_;
v_err_183_ = v___x_217_;
goto v___jp_180_;
}
}
}
}
else
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = lean_nat_add(v___x_195_, v___x_194_);
lean_dec(v___x_195_);
v___x_222_ = lean_nat_dec_lt(v___x_221_, v___x_187_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; 
lean_dec(v___x_221_);
v___x_223_ = lean_box(0);
lean_inc(v_idx_179_);
v_pos_181_ = v_a_172_;
v_idx_182_ = v_idx_179_;
v_err_183_ = v___x_223_;
goto v___jp_180_;
}
else
{
uint8_t v_c_224_; uint8_t v___x_225_; uint8_t v___y_227_; uint8_t v___x_243_; 
v_c_224_ = lean_byte_array_fget(v_array_178_, v___x_221_);
v___x_225_ = 48;
v___x_243_ = lean_uint8_dec_le(v___x_225_, v_c_224_);
if (v___x_243_ == 0)
{
v___y_227_ = v___x_243_;
goto v___jp_226_;
}
else
{
uint8_t v___x_244_; uint8_t v___x_245_; 
v___x_244_ = 57;
v___x_245_ = lean_uint8_dec_le(v_c_224_, v___x_244_);
v___y_227_ = v___x_245_;
goto v___jp_226_;
}
v___jp_226_:
{
if (v___y_227_ == 0)
{
lean_object* v___x_228_; 
lean_dec(v___x_221_);
v___x_228_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3));
lean_inc(v_idx_179_);
v_pos_181_ = v_a_172_;
v_idx_182_ = v_idx_179_;
v_err_183_ = v___x_228_;
goto v___jp_180_;
}
else
{
lean_object* v___x_229_; lean_object* v_it_x27_230_; uint32_t v___x_231_; uint8_t v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v_fst_236_; lean_object* v_snd_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_229_ = lean_nat_add(v___x_221_, v___x_194_);
lean_dec(v___x_221_);
lean_inc_ref(v_array_178_);
v_it_x27_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_230_, 0, v_array_178_);
lean_ctor_set(v_it_x27_230_, 1, v___x_229_);
v___x_231_ = lean_uint8_to_uint32(v_c_224_);
v___x_232_ = lean_uint32_to_uint8(v___x_231_);
v___x_233_ = lean_uint8_sub(v___x_232_, v___x_225_);
v___x_234_ = lean_uint8_to_nat(v___x_233_);
v___x_235_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_230_, v___x_234_);
v_fst_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_fst_236_);
v_snd_237_ = lean_ctor_get(v___x_235_, 1);
lean_inc(v_snd_237_);
lean_dec_ref(v___x_235_);
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = lean_nat_dec_eq(v_fst_236_, v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec(v_idx_179_);
lean_dec_ref(v_a_172_);
v___x_240_ = lean_nat_to_int(v_fst_236_);
v___x_241_ = lean_int_neg(v___x_240_);
lean_dec(v___x_240_);
v_pos_174_ = v_snd_237_;
v_res_175_ = v___x_241_;
goto v___jp_173_;
}
else
{
lean_object* v___x_242_; 
lean_dec(v_snd_237_);
lean_dec(v_fst_236_);
v___x_242_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5));
lean_inc(v_idx_179_);
v_pos_181_ = v_a_172_;
v_idx_182_ = v_idx_179_;
v_err_183_ = v___x_242_;
goto v___jp_180_;
}
}
}
}
}
}
}
}
v___jp_173_:
{
lean_object* v___x_176_; 
v___x_176_ = lean_array_push(v_acc_171_, v_res_175_);
v_acc_171_ = v___x_176_;
v_a_172_ = v_pos_174_;
goto _start;
}
v___jp_180_:
{
uint8_t v___x_184_; 
v___x_184_ = lean_nat_dec_eq(v_idx_179_, v_idx_182_);
lean_dec(v_idx_182_);
lean_dec(v_idx_179_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; 
lean_dec_ref(v_acc_171_);
lean_inc(v_err_183_);
v___x_185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_185_, 0, v_pos_181_);
lean_ctor_set(v___x_185_, 1, v_err_183_);
return v___x_185_;
}
else
{
lean_object* v___x_186_; 
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v_pos_181_);
lean_ctor_set(v___x_186_, 1, v_acc_171_);
return v___x_186_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4(void){
_start:
{
lean_object* v___x_252_; lean_object* v_utf8_253_; 
v___x_252_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__3));
v_utf8_253_ = lean_string_to_utf8(v___x_252_);
return v_utf8_253_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6(void){
_start:
{
lean_object* v___x_255_; lean_object* v_utf8_256_; 
v___x_255_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__5));
v_utf8_256_ = lean_string_to_utf8(v___x_255_);
return v_utf8_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment(lean_object* v_a_260_){
_start:
{
lean_object* v_array_261_; lean_object* v_idx_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_array_261_ = lean_ctor_get(v_a_260_, 0);
v_idx_262_ = lean_ctor_get(v_a_260_, 1);
v___x_263_ = lean_byte_array_size(v_array_261_);
v___x_264_ = lean_nat_dec_lt(v_idx_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_box(0);
v___x_266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_266_, 0, v_a_260_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
return v___x_266_;
}
else
{
uint8_t v___x_267_; uint8_t v_got_268_; uint8_t v___x_269_; 
v___x_267_ = 118;
v_got_268_ = lean_byte_array_fget(v_array_261_, v_idx_262_);
v___x_269_ = lean_uint8_dec_eq(v_got_268_, v___x_267_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__1));
v___x_271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_271_, 0, v_a_260_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
return v___x_271_;
}
else
{
lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_373_; 
lean_inc(v_idx_262_);
lean_inc_ref(v_array_261_);
v_isSharedCheck_373_ = !lean_is_exclusive(v_a_260_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; lean_object* v_unused_375_; 
v_unused_374_ = lean_ctor_get(v_a_260_, 1);
lean_dec(v_unused_374_);
v_unused_375_ = lean_ctor_get(v_a_260_, 0);
lean_dec(v_unused_375_);
v___x_273_ = v_a_260_;
v_isShared_274_ = v_isSharedCheck_373_;
goto v_resetjp_272_;
}
else
{
lean_dec(v_a_260_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_373_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_nat_add(v_idx_262_, v___x_275_);
lean_dec(v_idx_262_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 1, v___x_276_);
v___x_278_ = v___x_273_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_array_261_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v___x_276_);
v___x_278_ = v_reuseFailAlloc_372_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__2));
v___x_280_ = l_Std_Internal_Parsec_manyCore___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__1(v___x_279_, v___x_278_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_pos_281_; lean_object* v_res_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_362_; 
v_pos_281_ = lean_ctor_get(v___x_280_, 0);
v_res_282_ = lean_ctor_get(v___x_280_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_362_ == 0)
{
v___x_284_ = v___x_280_;
v_isShared_285_ = v_isSharedCheck_362_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_res_282_);
lean_inc(v_pos_281_);
lean_dec(v___x_280_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_362_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
size_t v_sz_286_; size_t v___x_287_; lean_object* v___x_288_; lean_object* v_pos_290_; lean_object* v_pos_297_; lean_object* v___y_303_; lean_object* v_utf8_314_; lean_object* v___x_315_; 
v_sz_286_ = lean_array_size(v_res_282_);
v___x_287_ = ((size_t)0ULL);
v___x_288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(v_sz_286_, v___x_287_, v_res_282_);
v_utf8_314_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4);
lean_inc(v_pos_281_);
v___x_315_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_314_, v_pos_281_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_pos_316_; 
lean_dec(v_pos_281_);
v_pos_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_pos_316_);
lean_dec_ref_known(v___x_315_, 2);
v_pos_290_ = v_pos_316_;
goto v___jp_289_;
}
else
{
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_pos_317_; 
lean_dec(v_pos_281_);
v_pos_317_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_pos_317_);
lean_dec_ref_known(v___x_315_, 2);
v_pos_290_ = v_pos_317_;
goto v___jp_289_;
}
else
{
lean_object* v_pos_318_; lean_object* v_err_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_361_; 
lean_del_object(v___x_284_);
v_pos_318_ = lean_ctor_get(v___x_315_, 0);
v_err_319_ = lean_ctor_get(v___x_315_, 1);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_361_ == 0)
{
v___x_321_ = v___x_315_;
v_isShared_322_ = v_isSharedCheck_361_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_err_319_);
lean_inc(v_pos_318_);
lean_dec(v___x_315_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_361_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v_idx_323_; lean_object* v_array_324_; lean_object* v_idx_325_; lean_object* v___y_327_; lean_object* v_pos_328_; lean_object* v_idx_329_; uint8_t v___x_334_; 
v_idx_323_ = lean_ctor_get(v_pos_281_, 1);
lean_inc(v_idx_323_);
lean_dec(v_pos_281_);
v_array_324_ = lean_ctor_get(v_pos_318_, 0);
v_idx_325_ = lean_ctor_get(v_pos_318_, 1);
v___x_334_ = lean_nat_dec_eq(v_idx_323_, v_idx_325_);
lean_dec(v_idx_323_);
if (v___x_334_ == 0)
{
lean_object* v___x_336_; 
lean_dec_ref(v___x_288_);
if (v_isShared_322_ == 0)
{
v___x_336_ = v___x_321_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_pos_318_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_err_319_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
else
{
lean_object* v___x_338_; uint8_t v___x_339_; 
lean_inc(v_idx_325_);
lean_dec(v_err_319_);
v___x_338_ = lean_byte_array_size(v_array_324_);
v___x_339_ = lean_nat_dec_lt(v_idx_325_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_340_ = lean_box(0);
lean_inc(v_pos_318_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 1, v___x_340_);
v___x_342_ = v___x_321_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_pos_318_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_inc(v_idx_325_);
v___y_327_ = v___x_342_;
v_pos_328_ = v_pos_318_;
v_idx_329_ = v_idx_325_;
goto v___jp_326_;
}
}
else
{
uint8_t v___x_344_; uint8_t v_got_345_; uint8_t v___x_346_; 
v___x_344_ = 10;
v_got_345_ = lean_byte_array_fget(v_array_324_, v_idx_325_);
v___x_346_ = lean_uint8_dec_eq(v_got_345_, v___x_344_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8));
lean_inc(v_pos_318_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 1, v___x_347_);
v___x_349_ = v___x_321_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_pos_318_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_inc(v_idx_325_);
v___y_327_ = v___x_349_;
v_pos_328_ = v_pos_318_;
v_idx_329_ = v_idx_325_;
goto v___jp_326_;
}
}
else
{
lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_358_; 
lean_inc_ref(v_array_324_);
lean_del_object(v___x_321_);
v_isSharedCheck_358_ = !lean_is_exclusive(v_pos_318_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; lean_object* v_unused_360_; 
v_unused_359_ = lean_ctor_get(v_pos_318_, 1);
lean_dec(v_unused_359_);
v_unused_360_ = lean_ctor_get(v_pos_318_, 0);
lean_dec(v_unused_360_);
v___x_352_ = v_pos_318_;
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
else
{
lean_dec(v_pos_318_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_354_ = lean_nat_add(v_idx_325_, v___x_275_);
lean_dec(v_idx_325_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 1, v___x_354_);
v___x_356_ = v___x_352_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_array_324_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
v_pos_297_ = v___x_356_;
goto v___jp_296_;
}
}
}
}
}
v___jp_326_:
{
uint8_t v___x_330_; 
v___x_330_ = lean_nat_dec_eq(v_idx_325_, v_idx_329_);
lean_dec(v_idx_329_);
lean_dec(v_idx_325_);
if (v___x_330_ == 0)
{
lean_dec_ref(v_pos_328_);
v___y_303_ = v___y_327_;
goto v___jp_302_;
}
else
{
lean_object* v_utf8_331_; lean_object* v___x_332_; 
lean_dec_ref(v___y_327_);
v_utf8_331_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6);
v___x_332_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_331_, v_pos_328_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_pos_333_; 
v_pos_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_pos_333_);
lean_dec_ref_known(v___x_332_, 2);
v_pos_297_ = v_pos_333_;
goto v___jp_296_;
}
else
{
v___y_303_ = v___x_332_;
goto v___jp_302_;
}
}
}
}
}
}
v___jp_289_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_291_ = lean_box(v___x_269_);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___x_288_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 1, v___x_292_);
lean_ctor_set(v___x_284_, 0, v_pos_290_);
v___x_294_ = v___x_284_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_pos_290_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
v___jp_296_:
{
uint8_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_298_ = 0;
v___x_299_ = lean_box(v___x_298_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___x_288_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v_pos_297_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
return v___x_301_;
}
v___jp_302_:
{
if (lean_obj_tag(v___y_303_) == 0)
{
lean_object* v_pos_304_; 
v_pos_304_ = lean_ctor_get(v___y_303_, 0);
lean_inc(v_pos_304_);
lean_dec_ref_known(v___y_303_, 2);
v_pos_297_ = v_pos_304_;
goto v___jp_296_;
}
else
{
lean_object* v_pos_305_; lean_object* v_err_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_dec_ref(v___x_288_);
v_pos_305_ = lean_ctor_get(v___y_303_, 0);
v_err_306_ = lean_ctor_get(v___y_303_, 1);
v_isSharedCheck_313_ = !lean_is_exclusive(v___y_303_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___y_303_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_err_306_);
lean_inc(v_pos_305_);
lean_dec(v___y_303_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_pos_305_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_err_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
}
else
{
lean_object* v_pos_363_; lean_object* v_err_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
v_pos_363_ = lean_ctor_get(v___x_280_, 0);
v_err_364_ = lean_ctor_get(v___x_280_, 1);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_280_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_err_364_);
lean_inc(v_pos_363_);
lean_dec(v___x_280_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_pos_363_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_err_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines_go(lean_object* v_acc_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment(v_a_377_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_res_379_; lean_object* v_pos_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_392_; 
v_res_379_ = lean_ctor_get(v___x_378_, 1);
v_pos_380_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_392_ == 0)
{
v___x_382_ = v___x_378_;
v_isShared_383_ = v_isSharedCheck_392_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_res_379_);
lean_inc(v_pos_380_);
lean_dec(v___x_378_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_392_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v_fst_384_; lean_object* v_snd_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v_fst_384_ = lean_ctor_get(v_res_379_, 0);
lean_inc(v_fst_384_);
v_snd_385_ = lean_ctor_get(v_res_379_, 1);
lean_inc(v_snd_385_);
lean_dec(v_res_379_);
v___x_386_ = l_Array_append___redArg(v_acc_376_, v_snd_385_);
lean_dec(v_snd_385_);
v___x_387_ = lean_unbox(v_fst_384_);
lean_dec(v_fst_384_);
if (v___x_387_ == 0)
{
lean_del_object(v___x_382_);
v_acc_376_ = v___x_386_;
v_a_377_ = v_pos_380_;
goto _start;
}
else
{
lean_object* v___x_390_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 1, v___x_386_);
v___x_390_ = v___x_382_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_pos_380_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v___x_386_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
else
{
lean_object* v_pos_393_; lean_object* v_err_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec_ref(v_acc_376_);
v_pos_393_ = lean_ctor_get(v___x_378_, 0);
v_err_394_ = lean_ctor_get(v___x_378_, 1);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_378_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_err_394_);
lean_inc(v_pos_393_);
lean_dec(v___x_378_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_pos_393_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_err_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines(lean_object* v_a_404_){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines___closed__0));
v___x_406_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines_go(v___x_405_, v_a_404_);
return v___x_406_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1(void){
_start:
{
lean_object* v___x_408_; lean_object* v_utf8_409_; 
v___x_408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0));
v_utf8_409_ = lean_string_to_utf8(v___x_408_);
return v_utf8_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader(lean_object* v_a_410_){
_start:
{
lean_object* v_idx_412_; lean_object* v___y_413_; lean_object* v_pos_414_; lean_object* v_idx_415_; lean_object* v_pos_430_; lean_object* v_utf8_455_; lean_object* v___x_456_; 
v_utf8_455_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1);
v___x_456_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_455_, v_a_410_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_pos_457_; 
v_pos_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_pos_457_);
lean_dec_ref_known(v___x_456_, 2);
v_pos_430_ = v_pos_457_;
goto v___jp_429_;
}
else
{
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_pos_458_; 
v_pos_458_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_pos_458_);
lean_dec_ref_known(v___x_456_, 2);
v_pos_430_ = v_pos_458_;
goto v___jp_429_;
}
else
{
return v___x_456_;
}
}
v___jp_411_:
{
uint8_t v___x_416_; 
v___x_416_ = lean_nat_dec_eq(v_idx_412_, v_idx_415_);
lean_dec(v_idx_415_);
lean_dec(v_idx_412_);
if (v___x_416_ == 0)
{
lean_dec_ref(v_pos_414_);
return v___y_413_;
}
else
{
lean_object* v_utf8_417_; lean_object* v___x_418_; 
lean_dec_ref(v___y_413_);
v_utf8_417_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6);
v___x_418_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_417_, v_pos_414_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_pos_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_427_; 
v_pos_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_427_ == 0)
{
lean_object* v_unused_428_; 
v_unused_428_ = lean_ctor_get(v___x_418_, 1);
lean_dec(v_unused_428_);
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_427_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_pos_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_427_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_423_ = lean_box(0);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 1, v___x_423_);
v___x_425_ = v___x_421_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_pos_419_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v___x_423_);
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
return v___x_418_;
}
}
}
v___jp_429_:
{
lean_object* v_array_431_; lean_object* v_idx_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_array_431_ = lean_ctor_get(v_pos_430_, 0);
v_idx_432_ = lean_ctor_get(v_pos_430_, 1);
lean_inc(v_idx_432_);
v___x_433_ = lean_byte_array_size(v_array_431_);
v___x_434_ = lean_nat_dec_lt(v_idx_432_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_box(0);
lean_inc_ref(v_pos_430_);
v___x_436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_436_, 0, v_pos_430_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
lean_inc(v_idx_432_);
v_idx_412_ = v_idx_432_;
v___y_413_ = v___x_436_;
v_pos_414_ = v_pos_430_;
v_idx_415_ = v_idx_432_;
goto v___jp_411_;
}
else
{
uint8_t v___x_437_; uint8_t v_got_438_; uint8_t v___x_439_; 
v___x_437_ = 10;
v_got_438_ = lean_byte_array_fget(v_array_431_, v_idx_432_);
v___x_439_ = lean_uint8_dec_eq(v_got_438_, v___x_437_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8));
lean_inc_ref(v_pos_430_);
v___x_441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_441_, 0, v_pos_430_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
lean_inc(v_idx_432_);
v_idx_412_ = v_idx_432_;
v___y_413_ = v___x_441_;
v_pos_414_ = v_pos_430_;
v_idx_415_ = v_idx_432_;
goto v___jp_411_;
}
else
{
lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_452_; 
lean_inc_ref(v_array_431_);
v_isSharedCheck_452_ = !lean_is_exclusive(v_pos_430_);
if (v_isSharedCheck_452_ == 0)
{
lean_object* v_unused_453_; lean_object* v_unused_454_; 
v_unused_453_ = lean_ctor_get(v_pos_430_, 1);
lean_dec(v_unused_453_);
v_unused_454_ = lean_ctor_get(v_pos_430_, 0);
lean_dec(v_unused_454_);
v___x_443_ = v_pos_430_;
v_isShared_444_ = v_isSharedCheck_452_;
goto v_resetjp_442_;
}
else
{
lean_dec(v_pos_430_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_452_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = lean_nat_add(v_idx_432_, v___x_445_);
lean_dec(v_idx_432_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 1, v___x_446_);
v___x_448_ = v___x_443_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_array_431_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v___x_446_);
v___x_448_ = v_reuseFailAlloc_451_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_box(0);
v___x_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
return v___x_450_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parse(lean_object* v_a_459_){
_start:
{
lean_object* v___y_461_; lean_object* v_idx_474_; lean_object* v___y_475_; lean_object* v_pos_476_; lean_object* v_idx_477_; lean_object* v_pos_484_; lean_object* v_utf8_508_; lean_object* v___x_509_; 
v_utf8_508_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1);
v___x_509_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_508_, v_a_459_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_pos_510_; 
v_pos_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_pos_510_);
lean_dec_ref_known(v___x_509_, 2);
v_pos_484_ = v_pos_510_;
goto v___jp_483_;
}
else
{
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_pos_511_; 
v_pos_511_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_pos_511_);
lean_dec_ref_known(v___x_509_, 2);
v_pos_484_ = v_pos_511_;
goto v___jp_483_;
}
else
{
v___y_461_ = v___x_509_;
goto v___jp_460_;
}
}
v___jp_460_:
{
if (lean_obj_tag(v___y_461_) == 0)
{
lean_object* v_pos_462_; lean_object* v___x_463_; 
v_pos_462_ = lean_ctor_get(v___y_461_, 0);
lean_inc(v_pos_462_);
lean_dec_ref_known(v___y_461_, 2);
v___x_463_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines(v_pos_462_);
return v___x_463_;
}
else
{
lean_object* v_pos_464_; lean_object* v_err_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
v_pos_464_ = lean_ctor_get(v___y_461_, 0);
v_err_465_ = lean_ctor_get(v___y_461_, 1);
v_isSharedCheck_472_ = !lean_is_exclusive(v___y_461_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___y_461_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_err_465_);
lean_inc(v_pos_464_);
lean_dec(v___y_461_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_pos_464_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_err_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
v___jp_473_:
{
uint8_t v___x_478_; 
v___x_478_ = lean_nat_dec_eq(v_idx_474_, v_idx_477_);
lean_dec(v_idx_477_);
lean_dec(v_idx_474_);
if (v___x_478_ == 0)
{
lean_dec_ref(v_pos_476_);
v___y_461_ = v___y_475_;
goto v___jp_460_;
}
else
{
lean_object* v_utf8_479_; lean_object* v___x_480_; 
lean_dec_ref(v___y_475_);
v_utf8_479_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6);
v___x_480_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_479_, v_pos_476_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_pos_481_; lean_object* v___x_482_; 
v_pos_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_pos_481_);
lean_dec_ref_known(v___x_480_, 2);
v___x_482_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines(v_pos_481_);
return v___x_482_;
}
else
{
v___y_461_ = v___x_480_;
goto v___jp_460_;
}
}
}
v___jp_483_:
{
lean_object* v_array_485_; lean_object* v_idx_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_array_485_ = lean_ctor_get(v_pos_484_, 0);
v_idx_486_ = lean_ctor_get(v_pos_484_, 1);
lean_inc(v_idx_486_);
v___x_487_ = lean_byte_array_size(v_array_485_);
v___x_488_ = lean_nat_dec_lt(v_idx_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_box(0);
lean_inc_ref(v_pos_484_);
v___x_490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_490_, 0, v_pos_484_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
lean_inc(v_idx_486_);
v_idx_474_ = v_idx_486_;
v___y_475_ = v___x_490_;
v_pos_476_ = v_pos_484_;
v_idx_477_ = v_idx_486_;
goto v___jp_473_;
}
else
{
uint8_t v___x_491_; uint8_t v_got_492_; uint8_t v___x_493_; 
v___x_491_ = 10;
v_got_492_ = lean_byte_array_fget(v_array_485_, v_idx_486_);
v___x_493_ = lean_uint8_dec_eq(v_got_492_, v___x_491_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8));
lean_inc_ref(v_pos_484_);
v___x_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_495_, 0, v_pos_484_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
lean_inc(v_idx_486_);
v_idx_474_ = v_idx_486_;
v___y_475_ = v___x_495_;
v_pos_476_ = v_pos_484_;
v_idx_477_ = v_idx_486_;
goto v___jp_473_;
}
else
{
lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_505_; 
lean_inc_ref(v_array_485_);
v_isSharedCheck_505_ = !lean_is_exclusive(v_pos_484_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; lean_object* v_unused_507_; 
v_unused_506_ = lean_ctor_get(v_pos_484_, 1);
lean_dec(v_unused_506_);
v_unused_507_ = lean_ctor_get(v_pos_484_, 0);
lean_dec(v_unused_507_);
v___x_497_ = v_pos_484_;
v_isShared_498_ = v_isSharedCheck_505_;
goto v_resetjp_496_;
}
else
{
lean_dec(v_pos_484_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_505_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_nat_add(v_idx_486_, v___x_499_);
lean_dec(v_idx_486_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 1, v___x_500_);
v___x_502_ = v___x_497_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_array_485_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_500_);
v___x_502_ = v_reuseFailAlloc_504_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_503_; 
v___x_503_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines(v___x_502_);
return v___x_503_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___redArg(lean_object* v_x_512_){
_start:
{
if (lean_obj_tag(v_x_512_) == 0)
{
lean_object* v___x_513_; 
v___x_513_ = lean_unsigned_to_nat(0u);
return v___x_513_;
}
else
{
lean_object* v___x_514_; 
v___x_514_ = lean_unsigned_to_nat(1u);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___redArg___boxed(lean_object* v_x_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___redArg(v_x_515_);
lean_dec(v_x_515_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx(lean_object* v_00_u03b1_517_, lean_object* v_x_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___redArg(v_x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___boxed(lean_object* v_00_u03b1_520_, lean_object* v_x_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx(v_00_u03b1_520_, v_x_521_);
lean_dec(v_x_521_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(lean_object* v_t_523_, lean_object* v_k_524_){
_start:
{
if (lean_obj_tag(v_t_523_) == 0)
{
lean_object* v_x_525_; lean_object* v___x_526_; 
v_x_525_ = lean_ctor_get(v_t_523_, 0);
lean_inc(v_x_525_);
lean_dec_ref_known(v_t_523_, 1);
v___x_526_ = lean_apply_1(v_k_524_, v_x_525_);
return v___x_526_;
}
else
{
return v_k_524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim(lean_object* v_00_u03b1_527_, lean_object* v_motive_528_, lean_object* v_ctorIdx_529_, lean_object* v_t_530_, lean_object* v_h_531_, lean_object* v_k_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_530_, v_k_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___boxed(lean_object* v_00_u03b1_534_, lean_object* v_motive_535_, lean_object* v_ctorIdx_536_, lean_object* v_t_537_, lean_object* v_h_538_, lean_object* v_k_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim(v_00_u03b1_534_, v_motive_535_, v_ctorIdx_536_, v_t_537_, v_h_538_, v_k_539_);
lean_dec(v_ctorIdx_536_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_success_elim___redArg(lean_object* v_t_541_, lean_object* v_success_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_541_, v_success_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_success_elim(lean_object* v_00_u03b1_544_, lean_object* v_motive_545_, lean_object* v_t_546_, lean_object* v_h_547_, lean_object* v_success_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_546_, v_success_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_timeout_elim___redArg(lean_object* v_t_550_, lean_object* v_timeout_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_550_, v_timeout_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_timeout_elim(lean_object* v_00_u03b1_553_, lean_object* v_motive_554_, lean_object* v_t_555_, lean_object* v_h_556_, lean_object* v_timeout_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_555_, v_timeout_557_);
return v___x_558_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = lean_box(0);
v___x_560_ = l_Lean_interruptExceptionId;
v___x_561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
lean_ctor_set(v___x_561_, 1, v___x_559_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg(){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0);
v___x_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___boxed(lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg();
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0(lean_object* v_00_u03b1_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg();
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___boxed(lean_object* v_00_u03b1_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0(v_00_u03b1_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(lean_object* v_cleanup_577_, lean_object* v_x_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_toCold_582_; lean_object* v_cancelTk_x3f_583_; 
v_toCold_582_ = lean_ctor_get(v_a_579_, 0);
v_cancelTk_x3f_583_ = lean_ctor_get(v_toCold_582_, 10);
if (lean_obj_tag(v_cancelTk_x3f_583_) == 1)
{
lean_object* v_val_584_; uint8_t v___x_585_; 
v_val_584_ = lean_ctor_get(v_cancelTk_x3f_583_, 0);
v___x_585_ = l_IO_CancelToken_isSet(v_val_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
lean_dec_ref(v_cleanup_577_);
lean_inc(v_a_580_);
lean_inc_ref(v_a_579_);
v___x_586_ = lean_apply_3(v_x_578_, v_a_579_, v_a_580_, lean_box(0));
return v___x_586_;
}
else
{
lean_object* v___x_587_; 
lean_dec_ref(v_x_578_);
lean_inc(v_a_580_);
lean_inc_ref(v_a_579_);
v___x_587_ = lean_apply_3(v_cleanup_577_, v_a_579_, v_a_580_, lean_box(0));
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v___x_588_; lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec_ref_known(v___x_587_, 1);
v___x_588_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg();
v_a_589_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_588_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
v_a_597_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_587_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_587_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
else
{
lean_object* v___x_605_; 
lean_dec_ref(v_cleanup_577_);
lean_inc(v_a_580_);
lean_inc_ref(v_a_579_);
v___x_605_ = lean_apply_3(v_x_578_, v_a_579_, v_a_580_, lean_box(0));
return v___x_605_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg___boxed(lean_object* v_cleanup_606_, lean_object* v_x_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(v_cleanup_606_, v_x_607_, v_a_608_, v_a_609_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck(lean_object* v_00_u03b1_612_, lean_object* v_cleanup_613_, lean_object* v_x_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(v_cleanup_613_, v_x_614_, v_a_615_, v_a_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___boxed(lean_object* v_00_u03b1_619_, lean_object* v_cleanup_620_, lean_object* v_x_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck(v_00_u03b1_619_, v_cleanup_620_, v_x_621_, v_a_622_, v_a_623_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(lean_object* v_budgetMs_626_, lean_object* v_cleanup_627_, lean_object* v_x_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_632_ = lean_unsigned_to_nat(0u);
v___x_633_ = lean_nat_dec_eq(v_budgetMs_626_, v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; 
lean_dec_ref(v_cleanup_627_);
lean_inc(v_a_630_);
lean_inc_ref(v_a_629_);
v___x_634_ = lean_apply_3(v_x_628_, v_a_629_, v_a_630_, lean_box(0));
return v___x_634_;
}
else
{
lean_object* v___x_635_; 
lean_dec_ref(v_x_628_);
lean_inc(v_a_630_);
lean_inc_ref(v_a_629_);
v___x_635_ = lean_apply_3(v_cleanup_627_, v_a_629_, v_a_630_, lean_box(0));
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_643_; 
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; 
v_unused_644_ = lean_ctor_get(v___x_635_, 0);
lean_dec(v_unused_644_);
v___x_637_ = v___x_635_;
v_isShared_638_ = v_isSharedCheck_643_;
goto v_resetjp_636_;
}
else
{
lean_dec(v___x_635_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_643_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_639_ = lean_box(1);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_639_);
v___x_641_ = v___x_637_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
v_a_645_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_635_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_635_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg___boxed(lean_object* v_budgetMs_653_, lean_object* v_cleanup_654_, lean_object* v_x_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(v_budgetMs_653_, v_cleanup_654_, v_x_655_, v_a_656_, v_a_657_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_budgetMs_653_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck(lean_object* v_00_u03b1_660_, lean_object* v_budgetMs_661_, lean_object* v_cleanup_662_, lean_object* v_x_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(v_budgetMs_661_, v_cleanup_662_, v_x_663_, v_a_664_, v_a_665_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___boxed(lean_object* v_00_u03b1_668_, lean_object* v_budgetMs_669_, lean_object* v_cleanup_670_, lean_object* v_x_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck(v_00_u03b1_668_, v_budgetMs_669_, v_cleanup_670_, v_x_671_, v_a_672_, v_a_673_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_budgetMs_669_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait(lean_object* v_cfg_676_, lean_object* v_child_677_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = lean_io_process_child_kill(v_cfg_676_, v_child_677_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; 
lean_dec_ref_known(v___x_679_, 1);
v___x_680_ = lean_box(0);
v___x_681_ = lean_io_process_child_wait(v_cfg_676_, v_child_677_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; 
v_unused_689_ = lean_ctor_get(v___x_681_, 0);
lean_dec(v_unused_689_);
v___x_683_ = v___x_681_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_dec(v___x_681_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_680_);
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_680_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_a_690_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_681_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_681_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
else
{
return v___x_679_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait___boxed(lean_object* v_cfg_698_, lean_object* v_child_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait(v_cfg_698_, v_child_699_);
lean_dec_ref(v_child_699_);
lean_dec_ref(v_cfg_698_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(lean_object* v_e_702_){
_start:
{
if (lean_obj_tag(v_e_702_) == 0)
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_713_; 
v_a_704_ = lean_ctor_get(v_e_702_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v_e_702_);
if (v_isSharedCheck_713_ == 0)
{
v___x_706_ = v_e_702_;
v_isShared_707_ = v_isSharedCheck_713_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v_e_702_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_713_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_708_ = lean_io_error_to_string(v_a_704_);
v___x_709_ = lean_mk_io_user_error(v___x_708_);
if (v_isShared_707_ == 0)
{
lean_ctor_set_tag(v___x_706_, 1);
lean_ctor_set(v___x_706_, 0, v___x_709_);
v___x_711_ = v___x_706_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
v_a_714_ = lean_ctor_get(v_e_702_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v_e_702_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v_e_702_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v_e_702_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
lean_ctor_set_tag(v___x_716_, 0);
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg___boxed(lean_object* v_e_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v_e_722_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0(lean_object* v_00_u03b1_725_, lean_object* v_e_726_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v_e_726_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___boxed(lean_object* v_00_u03b1_729_, lean_object* v_e_730_, lean_object* v_a_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0(v_00_u03b1_729_, v_e_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1(lean_object* v_cfg_733_, lean_object* v_child_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_ref_738_; lean_object* v___x_739_; 
v_ref_738_ = lean_ctor_get(v___y_735_, 2);
v___x_739_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait(v_cfg_733_, v_child_734_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_759_; 
v_a_748_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_759_ == 0)
{
v___x_750_ = v___x_739_;
v_isShared_751_ = v_isSharedCheck_759_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_739_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_759_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_752_ = lean_io_error_to_string(v_a_748_);
v___x_753_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
v___x_754_ = l_Lean_MessageData_ofFormat(v___x_753_);
lean_inc(v_ref_738_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v_ref_738_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_755_);
v___x_757_ = v___x_750_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1___boxed(lean_object* v_cfg_760_, lean_object* v_child_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1(v_cfg_760_, v_child_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec_ref(v_child_761_);
lean_dec_ref(v_cfg_760_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0(lean_object* v_cfg_766_, lean_object* v_child_767_, lean_object* v_sleepMs_768_, lean_object* v_budgetMs_769_, lean_object* v_maxSleepMs_770_, lean_object* v_stdout_771_, lean_object* v_stderr_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_ref_776_; lean_object* v___x_777_; 
v_ref_776_ = lean_ctor_get(v___y_773_, 2);
v___x_777_ = lean_io_process_child_try_wait(v_cfg_766_, v_child_767_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
lean_dec_ref_known(v___x_777_, 1);
if (lean_obj_tag(v_a_778_) == 0)
{
uint32_t v___x_779_; lean_object* v___x_780_; lean_object* v___y_782_; uint8_t v___x_785_; 
v___x_779_ = lean_uint32_of_nat(v_sleepMs_768_);
v___x_780_ = l_IO_sleep(v___x_779_);
v___x_785_ = lean_nat_dec_le(v_maxSleepMs_770_, v_sleepMs_768_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_unsigned_to_nat(2u);
v___x_787_ = lean_nat_mul(v_sleepMs_768_, v___x_786_);
v___y_782_ = v___x_787_;
goto v___jp_781_;
}
else
{
lean_inc(v_sleepMs_768_);
v___y_782_ = v_sleepMs_768_;
goto v___jp_781_;
}
v___jp_781_:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_nat_sub(v_budgetMs_769_, v_sleepMs_768_);
lean_dec(v_sleepMs_768_);
v___x_784_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(v_cfg_766_, v___x_783_, v___y_782_, v_maxSleepMs_770_, v_child_767_, v_stdout_771_, v_stderr_772_, v___y_773_, v___y_774_);
return v___x_784_;
}
}
else
{
lean_object* v_val_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_838_; 
lean_dec(v_maxSleepMs_770_);
lean_dec(v_sleepMs_768_);
lean_dec_ref(v_child_767_);
lean_dec_ref(v_cfg_766_);
v_val_788_ = lean_ctor_get(v_a_778_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v_a_778_);
if (v_isSharedCheck_838_ == 0)
{
v___x_790_ = v_a_778_;
v_isShared_791_ = v_isSharedCheck_838_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_val_788_);
lean_dec(v_a_778_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_838_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_task_get_own(v_stdout_771_);
v___x_793_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v___x_792_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v___x_793_, 1);
v___x_795_ = lean_task_get_own(v_stderr_772_);
v___x_796_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v___x_795_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_809_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_809_ == 0)
{
v___x_799_ = v___x_796_;
v_isShared_800_ = v_isSharedCheck_809_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_809_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; uint32_t v___x_802_; lean_object* v___x_804_; 
v___x_801_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_801_, 0, v_a_794_);
lean_ctor_set(v___x_801_, 1, v_a_797_);
v___x_802_ = lean_unbox_uint32(v_val_788_);
lean_dec(v_val_788_);
lean_ctor_set_uint32(v___x_801_, sizeof(void*)*2, v___x_802_);
if (v_isShared_791_ == 0)
{
lean_ctor_set_tag(v___x_790_, 0);
lean_ctor_set(v___x_790_, 0, v___x_801_);
v___x_804_ = v___x_790_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_801_);
v___x_804_ = v_reuseFailAlloc_808_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_806_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_804_);
v___x_806_ = v___x_799_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_823_; 
lean_dec(v_a_794_);
lean_dec(v_val_788_);
v_a_810_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_823_ == 0)
{
v___x_812_ = v___x_796_;
v_isShared_813_ = v_isSharedCheck_823_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_796_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_823_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_814_ = lean_io_error_to_string(v_a_810_);
if (v_isShared_791_ == 0)
{
lean_ctor_set_tag(v___x_790_, 3);
lean_ctor_set(v___x_790_, 0, v___x_814_);
v___x_816_ = v___x_790_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_822_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_817_ = l_Lean_MessageData_ofFormat(v___x_816_);
lean_inc(v_ref_776_);
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v_ref_776_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_818_);
v___x_820_ = v___x_812_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_837_; 
lean_dec(v_val_788_);
lean_dec_ref(v_stderr_772_);
v_a_824_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_837_ == 0)
{
v___x_826_ = v___x_793_;
v_isShared_827_ = v_isSharedCheck_837_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_793_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_837_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_828_ = lean_io_error_to_string(v_a_824_);
if (v_isShared_791_ == 0)
{
lean_ctor_set_tag(v___x_790_, 3);
lean_ctor_set(v___x_790_, 0, v___x_828_);
v___x_830_ = v___x_790_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_836_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_831_ = l_Lean_MessageData_ofFormat(v___x_830_);
lean_inc(v_ref_776_);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v_ref_776_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_832_);
v___x_834_ = v___x_826_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_850_; 
lean_dec_ref(v_stderr_772_);
lean_dec_ref(v_stdout_771_);
lean_dec(v_maxSleepMs_770_);
lean_dec(v_sleepMs_768_);
lean_dec_ref(v_child_767_);
lean_dec_ref(v_cfg_766_);
v_a_839_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_850_ == 0)
{
v___x_841_ = v___x_777_;
v_isShared_842_ = v_isSharedCheck_850_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_777_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_850_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_843_ = lean_io_error_to_string(v_a_839_);
v___x_844_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
v___x_845_ = l_Lean_MessageData_ofFormat(v___x_844_);
lean_inc(v_ref_776_);
v___x_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_846_, 0, v_ref_776_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_846_);
v___x_848_ = v___x_841_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0___boxed(lean_object* v_cfg_851_, lean_object* v_child_852_, lean_object* v_sleepMs_853_, lean_object* v_budgetMs_854_, lean_object* v_maxSleepMs_855_, lean_object* v_stdout_856_, lean_object* v_stderr_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0(v_cfg_851_, v_child_852_, v_sleepMs_853_, v_budgetMs_854_, v_maxSleepMs_855_, v_stdout_856_, v_stderr_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v_budgetMs_854_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(lean_object* v_cfg_862_, lean_object* v_budgetMs_863_, lean_object* v_sleepMs_864_, lean_object* v_maxSleepMs_865_, lean_object* v_child_866_, lean_object* v_stdout_867_, lean_object* v_stderr_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v___f_872_; lean_object* v___f_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
lean_inc(v_budgetMs_863_);
lean_inc_ref(v_child_866_);
lean_inc_ref(v_cfg_862_);
v___f_872_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0___boxed), 10, 7);
lean_closure_set(v___f_872_, 0, v_cfg_862_);
lean_closure_set(v___f_872_, 1, v_child_866_);
lean_closure_set(v___f_872_, 2, v_sleepMs_864_);
lean_closure_set(v___f_872_, 3, v_budgetMs_863_);
lean_closure_set(v___f_872_, 4, v_maxSleepMs_865_);
lean_closure_set(v___f_872_, 5, v_stdout_867_);
lean_closure_set(v___f_872_, 6, v_stderr_868_);
v___f_873_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1___boxed), 5, 2);
lean_closure_set(v___f_873_, 0, v_cfg_862_);
lean_closure_set(v___f_873_, 1, v_child_866_);
lean_inc_ref(v___f_873_);
v___x_874_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___boxed), 6, 3);
lean_closure_set(v___x_874_, 0, lean_box(0));
lean_closure_set(v___x_874_, 1, v___f_873_);
lean_closure_set(v___x_874_, 2, v___f_872_);
v___x_875_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(v_budgetMs_863_, v___f_873_, v___x_874_, v_a_869_, v_a_870_);
lean_dec(v_budgetMs_863_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___boxed(lean_object* v_cfg_876_, lean_object* v_budgetMs_877_, lean_object* v_sleepMs_878_, lean_object* v_maxSleepMs_879_, lean_object* v_child_880_, lean_object* v_stdout_881_, lean_object* v_stderr_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(v_cfg_876_, v_budgetMs_877_, v_sleepMs_878_, v_maxSleepMs_879_, v_child_880_, v_stdout_881_, v_stderr_882_, v_a_883_, v_a_884_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0(lean_object* v_stderr_887_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_IO_FS_Handle_readToEnd(v_stderr_887_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set_tag(v___x_892_, 1);
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
v_a_898_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_889_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_889_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set_tag(v___x_900_, 0);
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0___boxed(lean_object* v_stderr_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0(v_stderr_906_);
lean_dec(v_stderr_906_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1(lean_object* v_stdout_909_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_IO_FS_Handle_readToEnd(v_stdout_909_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
lean_ctor_set_tag(v___x_914_, 1);
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
v_a_920_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_911_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_911_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
lean_ctor_set_tag(v___x_922_, 0);
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1___boxed(lean_object* v_stdout_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1(v_stdout_928_);
lean_dec(v_stdout_928_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible(lean_object* v_timeout_934_, lean_object* v_args_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v___x_939_; lean_object* v_cmd_940_; lean_object* v_args_941_; lean_object* v_cwd_942_; lean_object* v_env_943_; uint8_t v_inheritEnv_944_; uint8_t v_setsid_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_979_; 
v___x_939_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0));
v_cmd_940_ = lean_ctor_get(v_args_935_, 1);
v_args_941_ = lean_ctor_get(v_args_935_, 2);
v_cwd_942_ = lean_ctor_get(v_args_935_, 3);
v_env_943_ = lean_ctor_get(v_args_935_, 4);
v_inheritEnv_944_ = lean_ctor_get_uint8(v_args_935_, sizeof(void*)*5);
v_setsid_945_ = lean_ctor_get_uint8(v_args_935_, sizeof(void*)*5 + 1);
v_isSharedCheck_979_ = !lean_is_exclusive(v_args_935_);
if (v_isSharedCheck_979_ == 0)
{
lean_object* v_unused_980_; 
v_unused_980_ = lean_ctor_get(v_args_935_, 0);
lean_dec(v_unused_980_);
v___x_947_ = v_args_935_;
v_isShared_948_ = v_isSharedCheck_979_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_env_943_);
lean_inc(v_cwd_942_);
lean_inc(v_args_941_);
lean_inc(v_cmd_940_);
lean_dec(v_args_935_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_979_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v_ref_949_; lean_object* v___x_951_; 
v_ref_949_ = lean_ctor_get(v_a_936_, 2);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_939_);
v___x_951_ = v___x_947_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_cmd_940_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v_args_941_);
lean_ctor_set(v_reuseFailAlloc_978_, 3, v_cwd_942_);
lean_ctor_set(v_reuseFailAlloc_978_, 4, v_env_943_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, sizeof(void*)*5, v_inheritEnv_944_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, sizeof(void*)*5 + 1, v_setsid_945_);
v___x_951_ = v_reuseFailAlloc_978_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; 
v___x_952_ = lean_io_process_spawn(v___x_951_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v_stdout_954_; lean_object* v_stderr_955_; lean_object* v___f_956_; lean_object* v___f_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_952_, 1);
v_stdout_954_ = lean_ctor_get(v_a_953_, 1);
v_stderr_955_ = lean_ctor_get(v_a_953_, 2);
lean_inc(v_stderr_955_);
v___f_956_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0___boxed), 2, 1);
lean_closure_set(v___f_956_, 0, v_stderr_955_);
lean_inc(v_stdout_954_);
v___f_957_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1___boxed), 2, 1);
lean_closure_set(v___f_957_, 0, v_stdout_954_);
v___x_958_ = lean_unsigned_to_nat(9u);
v___x_959_ = lean_io_as_task(v___f_957_, v___x_958_);
v___x_960_ = lean_io_as_task(v___f_956_, v___x_958_);
v___x_961_ = lean_unsigned_to_nat(1000u);
v___x_962_ = lean_nat_mul(v_timeout_934_, v___x_961_);
v___x_963_ = lean_unsigned_to_nat(1u);
v___x_964_ = lean_unsigned_to_nat(64u);
v___x_965_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(v___x_939_, v___x_962_, v___x_963_, v___x_964_, v_a_953_, v___x_959_, v___x_960_, v_a_936_, v_a_937_);
return v___x_965_;
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_977_; 
v_a_966_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_977_ == 0)
{
v___x_968_ = v___x_952_;
v_isShared_969_ = v_isSharedCheck_977_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_952_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_977_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_970_ = lean_io_error_to_string(v_a_966_);
v___x_971_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
v___x_972_ = l_Lean_MessageData_ofFormat(v___x_971_);
lean_inc(v_ref_949_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v_ref_949_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v___x_973_);
v___x_975_ = v___x_968_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___boxed(lean_object* v_timeout_981_, lean_object* v_args_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible(v_timeout_981_, v_args_982_, v_a_983_, v_a_984_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_timeout_981_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags(uint8_t v_mode_1002_){
_start:
{
switch(v_mode_1002_)
{
case 0:
{
lean_object* v___x_1003_; 
v___x_1003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__1));
return v___x_1003_;
}
case 1:
{
lean_object* v___x_1004_; 
v___x_1004_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__3));
return v___x_1004_;
}
default: 
{
lean_object* v___x_1005_; 
v___x_1005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___closed__5));
return v___x_1005_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags___boxed(lean_object* v_mode_1006_){
_start:
{
uint8_t v_mode_boxed_1007_; lean_object* v_res_1008_; 
v_mode_boxed_1007_ = lean_unbox(v_mode_1006_);
v_res_1008_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags(v_mode_boxed_1007_);
return v_res_1008_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__0);
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1);
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
lean_ctor_set(v___x_1014_, 2, v___x_1013_);
lean_ctor_set(v___x_1014_, 3, v___x_1013_);
lean_ctor_set(v___x_1014_, 4, v___x_1012_);
lean_ctor_set(v___x_1014_, 5, v___x_1012_);
lean_ctor_set(v___x_1014_, 6, v___x_1012_);
lean_ctor_set(v___x_1014_, 7, v___x_1012_);
lean_ctor_set(v___x_1014_, 8, v___x_1012_);
lean_ctor_set(v___x_1014_, 9, v___x_1012_);
lean_ctor_set(v___x_1014_, 10, v___x_1012_);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = lean_unsigned_to_nat(32u);
v___x_1016_ = lean_mk_empty_array_with_capacity(v___x_1015_);
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1018_ = ((size_t)5ULL);
v___x_1019_ = lean_unsigned_to_nat(0u);
v___x_1020_ = lean_unsigned_to_nat(32u);
v___x_1021_ = lean_mk_empty_array_with_capacity(v___x_1020_);
v___x_1022_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__3);
v___x_1023_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v___x_1021_);
lean_ctor_set(v___x_1023_, 2, v___x_1019_);
lean_ctor_set(v___x_1023_, 3, v___x_1019_);
lean_ctor_set_usize(v___x_1023_, 4, v___x_1018_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1024_ = lean_box(1);
v___x_1025_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__4);
v___x_1026_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__1);
v___x_1027_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v___x_1025_);
lean_ctor_set(v___x_1027_, 2, v___x_1024_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0(lean_object* v_msgData_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; lean_object* v_toCold_1033_; lean_object* v_env_1034_; lean_object* v_options_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1032_ = lean_st_ref_get(v___y_1030_);
v_toCold_1033_ = lean_ctor_get(v___y_1029_, 0);
v_env_1034_ = lean_ctor_get(v___x_1032_, 0);
lean_inc_ref(v_env_1034_);
lean_dec(v___x_1032_);
v_options_1035_ = lean_ctor_get(v_toCold_1033_, 2);
v___x_1036_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__2);
v___x_1037_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_1035_);
v___x_1038_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1038_, 0, v_env_1034_);
lean_ctor_set(v___x_1038_, 1, v___x_1036_);
lean_ctor_set(v___x_1038_, 2, v___x_1037_);
lean_ctor_set(v___x_1038_, 3, v_options_1035_);
v___x_1039_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v_msgData_1028_);
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0___boxed(lean_object* v_msgData_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0(v_msgData_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg(lean_object* v_msg_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_ref_1050_; lean_object* v___x_1051_; lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1060_; 
v_ref_1050_ = lean_ctor_get(v___y_1047_, 2);
v___x_1051_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0_spec__0(v_msg_1046_, v___y_1047_, v___y_1048_);
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1060_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1060_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1058_; 
lean_inc(v_ref_1050_);
v___x_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1056_, 0, v_ref_1050_);
lean_ctor_set(v___x_1056_, 1, v_a_1052_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set_tag(v___x_1054_, 1);
lean_ctor_set(v___x_1054_, 0, v___x_1056_);
v___x_1058_ = v___x_1054_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg___boxed(lean_object* v_msg_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg(v_msg_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
return v_res_1065_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__14(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__13));
v___x_1085_ = l_Lean_MessageData_ofFormat(v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery(lean_object* v_solverPath_1088_, lean_object* v_problemPath_1089_, lean_object* v_proofOutput_1090_, lean_object* v_timeout_1091_, uint8_t v_binaryProofs_1092_, uint8_t v_mode_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___y_1147_; 
v___x_1144_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__4));
v___x_1145_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__5));
if (v_binaryProofs_1092_ == 0)
{
lean_object* v___x_1210_; 
v___x_1210_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__15));
v___y_1147_ = v___x_1210_;
goto v___jp_1146_;
}
else
{
lean_object* v___x_1211_; 
v___x_1211_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__16));
v___y_1147_ = v___x_1211_;
goto v___jp_1146_;
}
v___jp_1097_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1100_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__0));
v___x_1101_ = lean_string_append(v___x_1100_, v___y_1099_);
lean_dec_ref(v___y_1099_);
v___x_1102_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__1));
v___x_1103_ = lean_string_append(v___x_1101_, v___x_1102_);
v___x_1104_ = lean_string_append(v___x_1103_, v___y_1098_);
lean_dec_ref(v___y_1098_);
v___x_1105_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
v___x_1106_ = l_Lean_MessageData_ofFormat(v___x_1105_);
v___x_1107_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg(v___x_1106_, v_a_1094_, v_a_1095_);
return v___x_1107_;
}
v___jp_1108_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1112_ = lean_string_utf8_byte_size(v___y_1111_);
v___x_1113_ = lean_unsigned_to_nat(13u);
v___x_1114_ = lean_nat_dec_le(v___x_1113_, v___x_1112_);
if (v___x_1114_ == 0)
{
v___y_1098_ = v___y_1110_;
v___y_1099_ = v___y_1111_;
goto v___jp_1097_;
}
else
{
lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0));
v___x_1116_ = lean_string_memcmp(v___y_1111_, v___x_1115_, v___y_1109_, v___y_1109_, v___x_1113_);
if (v___x_1116_ == 0)
{
v___y_1098_ = v___y_1110_;
v___y_1099_ = v___y_1111_;
goto v___jp_1097_;
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_dec_ref(v___y_1110_);
v___x_1117_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parse), 1, 0);
v___x_1118_ = lean_string_to_utf8(v___y_1111_);
v___x_1119_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_1117_, v___x_1118_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1134_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1134_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1134_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1124_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__2));
v___x_1125_ = lean_string_append(v___x_1124_, v_a_1120_);
lean_dec(v_a_1120_);
v___x_1126_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__3));
v___x_1127_ = lean_string_append(v___x_1125_, v___x_1126_);
v___x_1128_ = lean_string_append(v___x_1127_, v___y_1111_);
lean_dec_ref(v___y_1111_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set_tag(v___x_1122_, 3);
lean_ctor_set(v___x_1122_, 0, v___x_1128_);
v___x_1130_ = v___x_1122_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = l_Lean_MessageData_ofFormat(v___x_1130_);
v___x_1132_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg(v___x_1131_, v_a_1094_, v_a_1095_);
return v___x_1132_;
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1143_; 
lean_dec_ref(v___y_1111_);
v_a_1135_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1137_ = v___x_1119_;
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1119_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set_tag(v___x_1137_, 0);
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
}
}
}
}
}
v___jp_1146_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v_args_1158_; lean_object* v___x_1159_; lean_object* v_args_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1148_ = lean_string_append(v___x_1145_, v___y_1147_);
v___x_1149_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__6));
v___x_1150_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__7));
v___x_1151_ = lean_unsigned_to_nat(6u);
v___x_1152_ = lean_mk_empty_array_with_capacity(v___x_1151_);
v___x_1153_ = lean_array_push(v___x_1152_, v_problemPath_1089_);
v___x_1154_ = lean_array_push(v___x_1153_, v_proofOutput_1090_);
v___x_1155_ = lean_array_push(v___x_1154_, v___x_1144_);
v___x_1156_ = lean_array_push(v___x_1155_, v___x_1148_);
v___x_1157_ = lean_array_push(v___x_1156_, v___x_1149_);
v_args_1158_ = lean_array_push(v___x_1157_, v___x_1150_);
v___x_1159_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_satQuery_solverModeFlags(v_mode_1093_);
v_args_1160_ = l_Array_append___redArg(v_args_1158_, v___x_1159_);
lean_dec_ref(v___x_1159_);
v___x_1161_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__8));
v___x_1162_ = lean_box(0);
v___x_1163_ = lean_unsigned_to_nat(0u);
v___x_1164_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__9));
v___x_1165_ = 1;
v___x_1166_ = 0;
v___x_1167_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1167_, 0, v___x_1161_);
lean_ctor_set(v___x_1167_, 1, v_solverPath_1088_);
lean_ctor_set(v___x_1167_, 2, v_args_1160_);
lean_ctor_set(v___x_1167_, 3, v___x_1162_);
lean_ctor_set(v___x_1167_, 4, v___x_1164_);
lean_ctor_set_uint8(v___x_1167_, sizeof(void*)*5, v___x_1165_);
lean_ctor_set_uint8(v___x_1167_, sizeof(void*)*5 + 1, v___x_1166_);
v___x_1168_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible(v_timeout_1091_, v___x_1167_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1201_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1201_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1201_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
if (lean_obj_tag(v_a_1169_) == 0)
{
lean_object* v_x_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1198_; 
v_x_1173_ = lean_ctor_get(v_a_1169_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_a_1169_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1175_ = v_a_1169_;
v_isShared_1176_ = v_isSharedCheck_1198_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_x_1173_);
lean_dec(v_a_1169_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1198_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
uint32_t v_exitCode_1177_; lean_object* v_stdout_1178_; lean_object* v_stderr_1179_; uint32_t v___x_1180_; uint8_t v___x_1181_; 
v_exitCode_1177_ = lean_ctor_get_uint32(v_x_1173_, sizeof(void*)*2);
v_stdout_1178_ = lean_ctor_get(v_x_1173_, 0);
lean_inc_ref(v_stdout_1178_);
v_stderr_1179_ = lean_ctor_get(v_x_1173_, 1);
lean_inc_ref(v_stderr_1179_);
lean_dec(v_x_1173_);
v___x_1180_ = 255;
v___x_1181_ = lean_uint32_dec_eq(v_exitCode_1177_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
lean_del_object(v___x_1175_);
v___x_1182_ = lean_string_utf8_byte_size(v_stdout_1178_);
v___x_1183_ = lean_unsigned_to_nat(15u);
v___x_1184_ = lean_nat_dec_le(v___x_1183_, v___x_1182_);
if (v___x_1184_ == 0)
{
lean_del_object(v___x_1171_);
v___y_1109_ = v___x_1163_;
v___y_1110_ = v_stderr_1179_;
v___y_1111_ = v_stdout_1178_;
goto v___jp_1108_;
}
else
{
lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__10));
v___x_1186_ = lean_string_memcmp(v_stdout_1178_, v___x_1185_, v___x_1163_, v___x_1163_, v___x_1183_);
if (v___x_1186_ == 0)
{
lean_del_object(v___x_1171_);
v___y_1109_ = v___x_1163_;
v___y_1110_ = v_stderr_1179_;
v___y_1111_ = v_stdout_1178_;
goto v___jp_1108_;
}
else
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
lean_dec_ref(v_stderr_1179_);
lean_dec_ref(v_stdout_1178_);
v___x_1187_ = lean_box(1);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1187_);
v___x_1189_ = v___x_1171_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
else
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
lean_dec_ref(v_stdout_1178_);
lean_del_object(v___x_1171_);
v___x_1191_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__11));
v___x_1192_ = lean_string_append(v___x_1191_, v_stderr_1179_);
lean_dec_ref(v_stderr_1179_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set_tag(v___x_1175_, 3);
lean_ctor_set(v___x_1175_, 0, v___x_1192_);
v___x_1194_ = v___x_1175_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = l_Lean_MessageData_ofFormat(v___x_1194_);
v___x_1196_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg(v___x_1195_, v_a_1094_, v_a_1095_);
return v___x_1196_;
}
}
}
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_del_object(v___x_1171_);
v___x_1199_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__14, &l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__14);
v___x_1200_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg(v___x_1199_, v_a_1094_, v_a_1095_);
return v___x_1200_;
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
v_a_1202_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1168_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1168_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___boxed(lean_object* v_solverPath_1212_, lean_object* v_problemPath_1213_, lean_object* v_proofOutput_1214_, lean_object* v_timeout_1215_, lean_object* v_binaryProofs_1216_, lean_object* v_mode_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
uint8_t v_binaryProofs_boxed_1221_; uint8_t v_mode_boxed_1222_; lean_object* v_res_1223_; 
v_binaryProofs_boxed_1221_ = lean_unbox(v_binaryProofs_1216_);
v_mode_boxed_1222_ = lean_unbox(v_mode_1217_);
v_res_1223_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solverPath_1212_, v_problemPath_1213_, v_proofOutput_1214_, v_timeout_1215_, v_binaryProofs_boxed_1221_, v_mode_boxed_1222_, v_a_1218_, v_a_1219_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_timeout_1215_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0(lean_object* v_00_u03b1_1224_, lean_object* v_msg_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___redArg(v_msg_1225_, v___y_1226_, v___y_1227_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0___boxed(lean_object* v_00_u03b1_1230_, lean_object* v_msg_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_satQuery_spec__0(v_00_u03b1_1230_, v_msg_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
return v_res_1235_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_External(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_External(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Parser(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_External(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
}
#ifdef __cplusplus
}
#endif
