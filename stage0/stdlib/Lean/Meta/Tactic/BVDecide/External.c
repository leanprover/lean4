// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.External
// Imports: import Std.Tactic.BVDecide.LRAT.Parser public import Lean.CoreM public import Std.Tactic.BVDecide.Syntax public import Lean.Cadical.Basic
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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* lean_io_process_child_kill(lean_object*, lean_object*, uint8_t);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* lean_io_process_spawn(lean_object*);
uint8_t l_Lean_Cadical_Solver_configure(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Cadical_Solver_setLongOption(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Cadical_Solver_setOption(lean_object*, lean_object*, uint32_t);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint32_t lean_uint8_to_uint32(uint8_t);
uint8_t lean_uint32_to_uint8(uint32_t);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
uint32_t lean_int32_of_nat(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint32_t lean_bool_to_uint32(uint8_t);
lean_object* lean_int32_to_int(uint32_t);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___impl___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Failed to execute external prover `"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__2;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`:\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__4;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "\n\nThe prover can be configured with the option `sat.solver`."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 245, .m_capacity = 245, .m_length = 244, .m_data = "The SAT solver timed out while solving the problem.\nConsider increasing the timeout with the `timeout` config option.\nIf solving your problem relies inherently on using associativity or commutativity, consider enabling the `acNf` config option."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "shrink"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__3___boxed__const__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__4;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "unsat"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__5_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sat"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__6_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lrat"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "quiet"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___closed__1_value;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___closed__0_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___closed__1_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binary"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ilb"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__2___boxed__const__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__2;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lucky"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "--"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flag___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flag___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flag(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flag___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flagValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flagValue___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flagValue___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flagValue(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flagValue___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 2, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__0_value;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "The external prover produced unexpected output, stdout:\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nstderr:\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Error "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__4_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " while parsing:\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__5_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "s UNSATISFIABLE"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_assignment_7_; lean_object* v___x_8_; 
v_assignment_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_assignment_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_assignment_7_);
return v___x_8_;
}
else
{
return v_k_6_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_sat_elim___redArg(lean_object* v_t_21_, lean_object* v_sat_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(v_t_21_, v_sat_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_sat_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_sat_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(v_t_25_, v_sat_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_unsat_elim___redArg(lean_object* v_t_29_, lean_object* v_unsat_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(v_t_29_, v_unsat_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SolverResult_unsat_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_unsat_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Meta_Tactic_BVDecide_External_SolverResult_ctorElim___redArg(v_t_33_, v_unsat_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit(lean_object* v_a_46_){
_start:
{
lean_object* v_array_47_; lean_object* v_idx_48_; lean_object* v___x_49_; uint8_t v___x_50_; 
v_array_47_ = lean_ctor_get(v_a_46_, 0);
v_idx_48_ = lean_ctor_get(v_a_46_, 1);
v___x_49_ = lean_byte_array_size(v_array_47_);
v___x_50_ = lean_nat_dec_lt(v_idx_48_, v___x_49_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_box(0);
v___x_52_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_52_, 0, v_a_46_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
return v___x_52_;
}
else
{
uint8_t v___x_53_; uint8_t v_got_54_; uint8_t v___x_55_; 
v___x_53_ = 32;
v_got_54_ = lean_byte_array_fget(v_array_47_, v_idx_48_);
v___x_55_ = lean_uint8_dec_eq(v_got_54_, v___x_53_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1));
v___x_57_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_57_, 0, v_a_46_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
return v___x_57_;
}
else
{
lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_139_; 
lean_inc(v_idx_48_);
lean_inc_ref(v_array_47_);
v_isSharedCheck_139_ = !lean_is_exclusive(v_a_46_);
if (v_isSharedCheck_139_ == 0)
{
lean_object* v_unused_140_; lean_object* v_unused_141_; 
v_unused_140_ = lean_ctor_get(v_a_46_, 1);
lean_dec(v_unused_140_);
v_unused_141_ = lean_ctor_get(v_a_46_, 0);
lean_dec(v_unused_141_);
v___x_59_ = v_a_46_;
v_isShared_60_ = v_isSharedCheck_139_;
goto v_resetjp_58_;
}
else
{
lean_dec(v_a_46_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_139_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_add(v_idx_48_, v___x_61_);
lean_dec(v_idx_48_);
lean_inc(v___x_62_);
lean_inc_ref(v_array_47_);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 1, v___x_62_);
v___x_64_ = v___x_59_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_array_47_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_62_);
v___x_64_ = v_reuseFailAlloc_138_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
uint8_t v___x_68_; 
v___x_68_ = lean_nat_dec_lt(v___x_62_, v___x_49_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v___x_62_);
lean_dec_ref(v_array_47_);
v___x_69_ = lean_box(0);
v___x_70_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_64_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
return v___x_70_;
}
else
{
uint8_t v___x_71_; uint8_t v___x_72_; uint8_t v___x_73_; 
v___x_71_ = lean_byte_array_fget(v_array_47_, v___x_62_);
v___x_72_ = 45;
v___x_73_ = lean_uint8_dec_eq(v___x_71_, v___x_72_);
if (v___x_73_ == 0)
{
uint8_t v___x_74_; uint8_t v___x_75_; 
v___x_74_ = 48;
v___x_75_ = lean_uint8_dec_le(v___x_74_, v___x_71_);
if (v___x_75_ == 0)
{
lean_dec(v___x_62_);
lean_dec_ref(v_array_47_);
goto v___jp_65_;
}
else
{
uint8_t v___x_76_; uint8_t v___x_77_; 
v___x_76_ = 57;
v___x_77_ = lean_uint8_dec_le(v___x_71_, v___x_76_);
if (v___x_77_ == 0)
{
lean_dec(v___x_62_);
lean_dec_ref(v_array_47_);
goto v___jp_65_;
}
else
{
lean_object* v___x_78_; lean_object* v_it_x27_79_; uint32_t v___x_80_; uint8_t v___x_81_; uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v_fst_85_; lean_object* v_snd_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_100_; 
lean_dec_ref(v___x_64_);
v___x_78_ = lean_nat_add(v___x_62_, v___x_61_);
lean_dec(v___x_62_);
v_it_x27_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_79_, 0, v_array_47_);
lean_ctor_set(v_it_x27_79_, 1, v___x_78_);
v___x_80_ = lean_uint8_to_uint32(v___x_71_);
v___x_81_ = lean_uint32_to_uint8(v___x_80_);
v___x_82_ = lean_uint8_sub(v___x_81_, v___x_74_);
v___x_83_ = lean_uint8_to_nat(v___x_82_);
v___x_84_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_79_, v___x_83_);
v_fst_85_ = lean_ctor_get(v___x_84_, 0);
v_snd_86_ = lean_ctor_get(v___x_84_, 1);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_100_ == 0)
{
v___x_88_ = v___x_84_;
v_isShared_89_ = v_isSharedCheck_100_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_snd_86_);
lean_inc(v_fst_85_);
lean_dec(v___x_84_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_100_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_nat_dec_eq(v_fst_85_, v___x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_92_ = lean_nat_to_int(v_fst_85_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 1, v___x_92_);
lean_ctor_set(v___x_88_, 0, v_snd_86_);
v___x_94_ = v___x_88_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_snd_86_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
else
{
lean_object* v___x_96_; lean_object* v___x_98_; 
lean_dec(v_fst_85_);
v___x_96_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5));
if (v_isShared_89_ == 0)
{
lean_ctor_set_tag(v___x_88_, 1);
lean_ctor_set(v___x_88_, 1, v___x_96_);
lean_ctor_set(v___x_88_, 0, v_snd_86_);
v___x_98_ = v___x_88_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_snd_86_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
}
else
{
lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_106_; 
lean_dec_ref(v___x_64_);
v___x_101_ = lean_nat_add(v___x_62_, v___x_61_);
lean_dec(v___x_62_);
lean_inc(v___x_101_);
lean_inc_ref(v_array_47_);
v___x_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_102_, 0, v_array_47_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_106_ = lean_nat_dec_lt(v___x_101_, v___x_49_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; 
lean_dec(v___x_101_);
lean_dec_ref(v_array_47_);
v___x_107_ = lean_box(0);
v___x_108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_102_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
return v___x_108_;
}
else
{
uint8_t v_c_109_; uint8_t v___x_110_; uint8_t v___x_111_; 
v_c_109_ = lean_byte_array_fget(v_array_47_, v___x_101_);
v___x_110_ = 48;
v___x_111_ = lean_uint8_dec_le(v___x_110_, v_c_109_);
if (v___x_111_ == 0)
{
lean_dec(v___x_101_);
lean_dec_ref(v_array_47_);
goto v___jp_103_;
}
else
{
uint8_t v___x_112_; uint8_t v___x_113_; 
v___x_112_ = 57;
v___x_113_ = lean_uint8_dec_le(v_c_109_, v___x_112_);
if (v___x_113_ == 0)
{
lean_dec(v___x_101_);
lean_dec_ref(v_array_47_);
goto v___jp_103_;
}
else
{
lean_object* v___x_114_; lean_object* v_it_x27_115_; uint32_t v___x_116_; uint8_t v___x_117_; uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_fst_121_; lean_object* v_snd_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_137_; 
lean_dec_ref_known(v___x_102_, 2);
v___x_114_ = lean_nat_add(v___x_101_, v___x_61_);
lean_dec(v___x_101_);
v_it_x27_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_115_, 0, v_array_47_);
lean_ctor_set(v_it_x27_115_, 1, v___x_114_);
v___x_116_ = lean_uint8_to_uint32(v_c_109_);
v___x_117_ = lean_uint32_to_uint8(v___x_116_);
v___x_118_ = lean_uint8_sub(v___x_117_, v___x_110_);
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
v___jp_103_:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3));
v___x_105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_102_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
return v___x_105_;
}
}
}
v___jp_65_:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3));
v___x_67_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_64_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
return v___x_67_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__0(lean_object* v_a_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_nat_to_int(v_a_142_);
return v___x_143_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_nat_to_int(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(size_t v_sz_146_, size_t v_i_147_, lean_object* v_bs_148_){
_start:
{
uint8_t v___x_149_; 
v___x_149_ = lean_usize_dec_lt(v_i_147_, v_sz_146_);
if (v___x_149_ == 0)
{
return v_bs_148_;
}
else
{
lean_object* v_v_150_; lean_object* v___x_151_; lean_object* v_bs_x27_152_; lean_object* v___x_153_; uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; size_t v___x_158_; size_t v___x_159_; lean_object* v___x_160_; 
v_v_150_ = lean_array_uget(v_bs_148_, v_i_147_);
v___x_151_ = lean_unsigned_to_nat(0u);
v_bs_x27_152_ = lean_array_uset(v_bs_148_, v_i_147_, v___x_151_);
v___x_153_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___closed__0);
v___x_154_ = lean_int_dec_lt(v___x_153_, v_v_150_);
v___x_155_ = lean_nat_abs(v_v_150_);
lean_dec(v_v_150_);
v___x_156_ = lean_box(v___x_154_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_155_);
v___x_158_ = ((size_t)1ULL);
v___x_159_ = lean_usize_add(v_i_147_, v___x_158_);
v___x_160_ = lean_array_uset(v_bs_x27_152_, v_i_147_, v___x_157_);
v_i_147_ = v___x_159_;
v_bs_148_ = v___x_160_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___boxed(lean_object* v_sz_162_, lean_object* v_i_163_, lean_object* v_bs_164_){
_start:
{
size_t v_sz_boxed_165_; size_t v_i_boxed_166_; lean_object* v_res_167_; 
v_sz_boxed_165_ = lean_unbox_usize(v_sz_162_);
lean_dec(v_sz_162_);
v_i_boxed_166_ = lean_unbox_usize(v_i_163_);
lean_dec(v_i_163_);
v_res_167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(v_sz_boxed_165_, v_i_boxed_166_, v_bs_164_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__1(lean_object* v_acc_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_pos_171_; lean_object* v_res_172_; lean_object* v_array_175_; lean_object* v_idx_176_; lean_object* v_pos_178_; lean_object* v_idx_179_; lean_object* v_err_180_; lean_object* v___x_188_; uint8_t v___x_189_; 
v_array_175_ = lean_ctor_get(v_a_169_, 0);
v_idx_176_ = lean_ctor_get(v_a_169_, 1);
lean_inc(v_idx_176_);
v___x_188_ = lean_byte_array_size(v_array_175_);
v___x_189_ = lean_nat_dec_lt(v_idx_176_, v___x_188_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; 
v___x_190_ = lean_box(0);
lean_inc(v_idx_176_);
v_pos_178_ = v_a_169_;
v_idx_179_ = v_idx_176_;
v_err_180_ = v___x_190_;
goto v___jp_177_;
}
else
{
uint8_t v___x_191_; uint8_t v_got_192_; uint8_t v___x_193_; 
v___x_191_ = 32;
v_got_192_ = lean_byte_array_fget(v_array_175_, v_idx_176_);
v___x_193_ = lean_uint8_dec_eq(v_got_192_, v___x_191_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
v___x_194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1));
lean_inc(v_idx_176_);
v_pos_178_ = v_a_169_;
v_idx_179_ = v_idx_176_;
v_err_180_ = v___x_194_;
goto v___jp_177_;
}
else
{
lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_195_ = lean_unsigned_to_nat(1u);
v___x_196_ = lean_nat_add(v_idx_176_, v___x_195_);
v___x_197_ = lean_nat_dec_lt(v___x_196_, v___x_188_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
lean_dec(v___x_196_);
v___x_198_ = lean_box(0);
lean_inc(v_idx_176_);
v_pos_178_ = v_a_169_;
v_idx_179_ = v_idx_176_;
v_err_180_ = v___x_198_;
goto v___jp_177_;
}
else
{
uint8_t v___x_199_; uint8_t v___x_200_; uint8_t v___x_201_; 
v___x_199_ = lean_byte_array_fget(v_array_175_, v___x_196_);
v___x_200_ = 45;
v___x_201_ = lean_uint8_dec_eq(v___x_199_, v___x_200_);
if (v___x_201_ == 0)
{
uint8_t v___x_202_; uint8_t v___x_203_; 
v___x_202_ = 48;
v___x_203_ = lean_uint8_dec_le(v___x_202_, v___x_199_);
if (v___x_203_ == 0)
{
lean_dec(v___x_196_);
goto v___jp_186_;
}
else
{
uint8_t v___x_204_; uint8_t v___x_205_; 
v___x_204_ = 57;
v___x_205_ = lean_uint8_dec_le(v___x_199_, v___x_204_);
if (v___x_205_ == 0)
{
lean_dec(v___x_196_);
goto v___jp_186_;
}
else
{
lean_object* v___x_206_; lean_object* v_it_x27_207_; uint32_t v___x_208_; uint8_t v___x_209_; uint8_t v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v_fst_213_; lean_object* v_snd_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_206_ = lean_nat_add(v___x_196_, v___x_195_);
lean_dec(v___x_196_);
lean_inc_ref(v_array_175_);
v_it_x27_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_207_, 0, v_array_175_);
lean_ctor_set(v_it_x27_207_, 1, v___x_206_);
v___x_208_ = lean_uint8_to_uint32(v___x_199_);
v___x_209_ = lean_uint32_to_uint8(v___x_208_);
v___x_210_ = lean_uint8_sub(v___x_209_, v___x_202_);
v___x_211_ = lean_uint8_to_nat(v___x_210_);
v___x_212_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_207_, v___x_211_);
v_fst_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_fst_213_);
v_snd_214_ = lean_ctor_get(v___x_212_, 1);
lean_inc(v_snd_214_);
lean_dec_ref(v___x_212_);
v___x_215_ = lean_unsigned_to_nat(0u);
v___x_216_ = lean_nat_dec_eq(v_fst_213_, v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; 
lean_dec(v_idx_176_);
lean_dec_ref(v_a_169_);
v___x_217_ = lean_nat_to_int(v_fst_213_);
v_pos_171_ = v_snd_214_;
v_res_172_ = v___x_217_;
goto v___jp_170_;
}
else
{
lean_object* v___x_218_; 
lean_dec(v_snd_214_);
lean_dec(v_fst_213_);
v___x_218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5));
lean_inc(v_idx_176_);
v_pos_178_ = v_a_169_;
v_idx_179_ = v_idx_176_;
v_err_180_ = v___x_218_;
goto v___jp_177_;
}
}
}
}
else
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = lean_nat_add(v___x_196_, v___x_195_);
lean_dec(v___x_196_);
v___x_220_ = lean_nat_dec_lt(v___x_219_, v___x_188_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; 
lean_dec(v___x_219_);
v___x_221_ = lean_box(0);
lean_inc(v_idx_176_);
v_pos_178_ = v_a_169_;
v_idx_179_ = v_idx_176_;
v_err_180_ = v___x_221_;
goto v___jp_177_;
}
else
{
uint8_t v_c_222_; uint8_t v___x_223_; uint8_t v___x_224_; 
v_c_222_ = lean_byte_array_fget(v_array_175_, v___x_219_);
v___x_223_ = 48;
v___x_224_ = lean_uint8_dec_le(v___x_223_, v_c_222_);
if (v___x_224_ == 0)
{
lean_dec(v___x_219_);
goto v___jp_184_;
}
else
{
uint8_t v___x_225_; uint8_t v___x_226_; 
v___x_225_ = 57;
v___x_226_ = lean_uint8_dec_le(v_c_222_, v___x_225_);
if (v___x_226_ == 0)
{
lean_dec(v___x_219_);
goto v___jp_184_;
}
else
{
lean_object* v___x_227_; lean_object* v_it_x27_228_; uint32_t v___x_229_; uint8_t v___x_230_; uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v_fst_234_; lean_object* v_snd_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_227_ = lean_nat_add(v___x_219_, v___x_195_);
lean_dec(v___x_219_);
lean_inc_ref(v_array_175_);
v_it_x27_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_228_, 0, v_array_175_);
lean_ctor_set(v_it_x27_228_, 1, v___x_227_);
v___x_229_ = lean_uint8_to_uint32(v_c_222_);
v___x_230_ = lean_uint32_to_uint8(v___x_229_);
v___x_231_ = lean_uint8_sub(v___x_230_, v___x_223_);
v___x_232_ = lean_uint8_to_nat(v___x_231_);
v___x_233_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_228_, v___x_232_);
v_fst_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_fst_234_);
v_snd_235_ = lean_ctor_get(v___x_233_, 1);
lean_inc(v_snd_235_);
lean_dec_ref(v___x_233_);
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = lean_nat_dec_eq(v_fst_234_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec(v_idx_176_);
lean_dec_ref(v_a_169_);
v___x_238_ = lean_nat_to_int(v_fst_234_);
v___x_239_ = lean_int_neg(v___x_238_);
lean_dec(v___x_238_);
v_pos_171_ = v_snd_235_;
v_res_172_ = v___x_239_;
goto v___jp_170_;
}
else
{
lean_object* v___x_240_; 
lean_dec(v_snd_235_);
lean_dec(v_fst_234_);
v___x_240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5));
lean_inc(v_idx_176_);
v_pos_178_ = v_a_169_;
v_idx_179_ = v_idx_176_;
v_err_180_ = v___x_240_;
goto v___jp_177_;
}
}
}
}
}
}
}
}
v___jp_170_:
{
lean_object* v___x_173_; 
v___x_173_ = lean_array_push(v_acc_168_, v_res_172_);
v_acc_168_ = v___x_173_;
v_a_169_ = v_pos_171_;
goto _start;
}
v___jp_177_:
{
uint8_t v___x_181_; 
v___x_181_ = lean_nat_dec_eq(v_idx_176_, v_idx_179_);
lean_dec(v_idx_179_);
lean_dec(v_idx_176_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
lean_dec_ref(v_acc_168_);
lean_inc(v_err_180_);
v___x_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_182_, 0, v_pos_178_);
lean_ctor_set(v___x_182_, 1, v_err_180_);
return v___x_182_;
}
else
{
lean_object* v___x_183_; 
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v_pos_178_);
lean_ctor_set(v___x_183_, 1, v_acc_168_);
return v___x_183_;
}
}
v___jp_184_:
{
lean_object* v___x_185_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3));
lean_inc(v_idx_176_);
v_pos_178_ = v_a_169_;
v_idx_179_ = v_idx_176_;
v_err_180_ = v___x_185_;
goto v___jp_177_;
}
v___jp_186_:
{
lean_object* v___x_187_; 
v___x_187_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3));
lean_inc(v_idx_176_);
v_pos_178_ = v_a_169_;
v_idx_179_ = v_idx_176_;
v_err_180_ = v___x_187_;
goto v___jp_177_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4(void){
_start:
{
lean_object* v___x_247_; lean_object* v_utf8_248_; 
v___x_247_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__3));
v_utf8_248_ = lean_string_to_utf8(v___x_247_);
return v_utf8_248_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6(void){
_start:
{
lean_object* v___x_250_; lean_object* v_utf8_251_; 
v___x_250_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__5));
v_utf8_251_ = lean_string_to_utf8(v___x_250_);
return v_utf8_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment(lean_object* v_a_255_){
_start:
{
lean_object* v_array_256_; lean_object* v_idx_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v_array_256_ = lean_ctor_get(v_a_255_, 0);
v_idx_257_ = lean_ctor_get(v_a_255_, 1);
v___x_258_ = lean_byte_array_size(v_array_256_);
v___x_259_ = lean_nat_dec_lt(v_idx_257_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_box(0);
v___x_261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_261_, 0, v_a_255_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
return v___x_261_;
}
else
{
uint8_t v___x_262_; uint8_t v_got_263_; uint8_t v___x_264_; 
v___x_262_ = 118;
v_got_263_ = lean_byte_array_fget(v_array_256_, v_idx_257_);
v___x_264_ = lean_uint8_dec_eq(v_got_263_, v___x_262_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__1));
v___x_266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_266_, 0, v_a_255_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
return v___x_266_;
}
else
{
lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_378_; 
lean_inc(v_idx_257_);
lean_inc_ref(v_array_256_);
v_isSharedCheck_378_ = !lean_is_exclusive(v_a_255_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; lean_object* v_unused_380_; 
v_unused_379_ = lean_ctor_get(v_a_255_, 1);
lean_dec(v_unused_379_);
v_unused_380_ = lean_ctor_get(v_a_255_, 0);
lean_dec(v_unused_380_);
v___x_268_ = v_a_255_;
v_isShared_269_ = v_isSharedCheck_378_;
goto v_resetjp_267_;
}
else
{
lean_dec(v_a_255_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_378_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = lean_nat_add(v_idx_257_, v___x_270_);
lean_dec(v_idx_257_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 1, v___x_271_);
v___x_273_ = v___x_268_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_array_256_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v___x_271_);
v___x_273_ = v_reuseFailAlloc_377_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__2));
v___x_275_ = l_Std_Internal_Parsec_manyCore___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__1(v___x_274_, v___x_273_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_pos_276_; lean_object* v_res_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_367_; 
v_pos_276_ = lean_ctor_get(v___x_275_, 0);
v_res_277_ = lean_ctor_get(v___x_275_, 1);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_367_ == 0)
{
v___x_279_ = v___x_275_;
v_isShared_280_ = v_isSharedCheck_367_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_res_277_);
lean_inc(v_pos_276_);
lean_dec(v___x_275_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_367_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
size_t v_sz_281_; size_t v___x_282_; lean_object* v___x_283_; lean_object* v_pos_285_; lean_object* v_utf8_292_; lean_object* v___x_293_; 
v_sz_281_ = lean_array_size(v_res_277_);
v___x_282_ = ((size_t)0ULL);
v___x_283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(v_sz_281_, v___x_282_, v_res_277_);
v_utf8_292_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4);
lean_inc(v_pos_276_);
v___x_293_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_292_, v_pos_276_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_pos_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_303_; 
lean_del_object(v___x_279_);
lean_dec(v_pos_276_);
v_pos_294_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_303_ == 0)
{
lean_object* v_unused_304_; 
v_unused_304_ = lean_ctor_get(v___x_293_, 1);
lean_dec(v_unused_304_);
v___x_296_ = v___x_293_;
v_isShared_297_ = v_isSharedCheck_303_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_pos_294_);
lean_dec(v___x_293_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_303_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_298_ = lean_box(v___x_264_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_283_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 1, v___x_299_);
v___x_301_ = v___x_296_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_pos_294_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
else
{
lean_object* v_pos_305_; lean_object* v_err_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_366_; 
v_pos_305_ = lean_ctor_get(v___x_293_, 0);
v_err_306_ = lean_ctor_get(v___x_293_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_366_ == 0)
{
v___x_308_ = v___x_293_;
v_isShared_309_ = v_isSharedCheck_366_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_err_306_);
lean_inc(v_pos_305_);
lean_dec(v___x_293_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_366_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_idx_310_; lean_object* v_array_311_; lean_object* v_idx_312_; lean_object* v___y_314_; lean_object* v_pos_315_; lean_object* v_idx_316_; uint8_t v___x_339_; 
v_idx_310_ = lean_ctor_get(v_pos_276_, 1);
lean_inc(v_idx_310_);
lean_dec(v_pos_276_);
v_array_311_ = lean_ctor_get(v_pos_305_, 0);
v_idx_312_ = lean_ctor_get(v_pos_305_, 1);
v___x_339_ = lean_nat_dec_eq(v_idx_310_, v_idx_312_);
lean_dec(v_idx_310_);
if (v___x_339_ == 0)
{
lean_object* v___x_341_; 
lean_dec_ref(v___x_283_);
lean_del_object(v___x_279_);
if (v_isShared_309_ == 0)
{
v___x_341_ = v___x_308_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_pos_305_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_err_306_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
else
{
lean_object* v___x_343_; uint8_t v___x_344_; 
lean_inc(v_idx_312_);
lean_dec(v_err_306_);
v___x_343_ = lean_byte_array_size(v_array_311_);
v___x_344_ = lean_nat_dec_lt(v_idx_312_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_345_ = lean_box(0);
lean_inc(v_pos_305_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_345_);
v___x_347_ = v___x_308_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_pos_305_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_inc(v_idx_312_);
v___y_314_ = v___x_347_;
v_pos_315_ = v_pos_305_;
v_idx_316_ = v_idx_312_;
goto v___jp_313_;
}
}
else
{
uint8_t v___x_349_; uint8_t v_got_350_; uint8_t v___x_351_; 
v___x_349_ = 10;
v_got_350_ = lean_byte_array_fget(v_array_311_, v_idx_312_);
v___x_351_ = lean_uint8_dec_eq(v_got_350_, v___x_349_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8));
lean_inc(v_pos_305_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_352_);
v___x_354_ = v___x_308_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_pos_305_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_inc(v_idx_312_);
v___y_314_ = v___x_354_;
v_pos_315_ = v_pos_305_;
v_idx_316_ = v_idx_312_;
goto v___jp_313_;
}
}
else
{
lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_363_; 
lean_inc_ref(v_array_311_);
lean_del_object(v___x_308_);
v_isSharedCheck_363_ = !lean_is_exclusive(v_pos_305_);
if (v_isSharedCheck_363_ == 0)
{
lean_object* v_unused_364_; lean_object* v_unused_365_; 
v_unused_364_ = lean_ctor_get(v_pos_305_, 1);
lean_dec(v_unused_364_);
v_unused_365_ = lean_ctor_get(v_pos_305_, 0);
lean_dec(v_unused_365_);
v___x_357_ = v_pos_305_;
v_isShared_358_ = v_isSharedCheck_363_;
goto v_resetjp_356_;
}
else
{
lean_dec(v_pos_305_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_363_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = lean_nat_add(v_idx_312_, v___x_270_);
lean_dec(v_idx_312_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 1, v___x_359_);
v___x_361_ = v___x_357_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_array_311_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
v_pos_285_ = v___x_361_;
goto v___jp_284_;
}
}
}
}
}
v___jp_313_:
{
uint8_t v___x_317_; 
v___x_317_ = lean_nat_dec_eq(v_idx_312_, v_idx_316_);
lean_dec(v_idx_316_);
lean_dec(v_idx_312_);
if (v___x_317_ == 0)
{
lean_object* v_pos_318_; lean_object* v_err_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec_ref(v_pos_315_);
lean_dec_ref(v___x_283_);
lean_del_object(v___x_279_);
v_pos_318_ = lean_ctor_get(v___y_314_, 0);
v_err_319_ = lean_ctor_get(v___y_314_, 1);
v_isSharedCheck_326_ = !lean_is_exclusive(v___y_314_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___y_314_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_err_319_);
lean_inc(v_pos_318_);
lean_dec(v___y_314_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_pos_318_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_err_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
else
{
lean_object* v_utf8_327_; lean_object* v___x_328_; 
lean_dec_ref(v___y_314_);
v_utf8_327_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6);
v___x_328_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_327_, v_pos_315_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_pos_329_; 
v_pos_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_pos_329_);
lean_dec_ref_known(v___x_328_, 2);
v_pos_285_ = v_pos_329_;
goto v___jp_284_;
}
else
{
lean_object* v_pos_330_; lean_object* v_err_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec_ref(v___x_283_);
lean_del_object(v___x_279_);
v_pos_330_ = lean_ctor_get(v___x_328_, 0);
v_err_331_ = lean_ctor_get(v___x_328_, 1);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_328_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_err_331_);
lean_inc(v_pos_330_);
lean_dec(v___x_328_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_pos_330_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_err_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
}
}
v___jp_284_:
{
uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_286_ = 0;
v___x_287_ = lean_box(v___x_286_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_283_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 1, v___x_288_);
lean_ctor_set(v___x_279_, 0, v_pos_285_);
v___x_290_ = v___x_279_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_pos_285_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v___x_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
else
{
lean_object* v_pos_368_; lean_object* v_err_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
v_pos_368_ = lean_ctor_get(v___x_275_, 0);
v_err_369_ = lean_ctor_get(v___x_275_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_275_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_err_369_);
lean_inc(v_pos_368_);
lean_dec(v___x_275_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_pos_368_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_err_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines_go(lean_object* v_acc_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment(v_a_382_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_res_384_; lean_object* v_pos_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_397_; 
v_res_384_ = lean_ctor_get(v___x_383_, 1);
v_pos_385_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_397_ == 0)
{
v___x_387_ = v___x_383_;
v_isShared_388_ = v_isSharedCheck_397_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_res_384_);
lean_inc(v_pos_385_);
lean_dec(v___x_383_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_397_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v_fst_389_; lean_object* v_snd_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v_fst_389_ = lean_ctor_get(v_res_384_, 0);
lean_inc(v_fst_389_);
v_snd_390_ = lean_ctor_get(v_res_384_, 1);
lean_inc(v_snd_390_);
lean_dec(v_res_384_);
v___x_391_ = l_Array_append___redArg(v_acc_381_, v_snd_390_);
lean_dec(v_snd_390_);
v___x_392_ = lean_unbox(v_fst_389_);
lean_dec(v_fst_389_);
if (v___x_392_ == 0)
{
lean_del_object(v___x_387_);
v_acc_381_ = v___x_391_;
v_a_382_ = v_pos_385_;
goto _start;
}
else
{
lean_object* v___x_395_; 
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 1, v___x_391_);
v___x_395_ = v___x_387_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_pos_385_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_391_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
else
{
lean_object* v_pos_398_; lean_object* v_err_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec_ref(v_acc_381_);
v_pos_398_ = lean_ctor_get(v___x_383_, 0);
v_err_399_ = lean_ctor_get(v___x_383_, 1);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_383_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_err_399_);
lean_inc(v_pos_398_);
lean_dec(v___x_383_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_pos_398_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_err_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines(lean_object* v_a_409_){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines___closed__0));
v___x_411_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines_go(v___x_410_, v_a_409_);
return v___x_411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1(void){
_start:
{
lean_object* v___x_413_; lean_object* v_utf8_414_; 
v___x_413_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0));
v_utf8_414_ = lean_string_to_utf8(v___x_413_);
return v_utf8_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader(lean_object* v_a_415_){
_start:
{
lean_object* v_utf8_416_; lean_object* v___x_417_; 
v_utf8_416_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1);
v___x_417_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_416_, v_a_415_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_pos_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_469_; 
v_pos_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; 
v_unused_470_ = lean_ctor_get(v___x_417_, 1);
lean_dec(v_unused_470_);
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_469_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_pos_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_469_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v_array_422_; lean_object* v_idx_423_; lean_object* v___y_425_; lean_object* v_pos_426_; lean_object* v_idx_427_; lean_object* v___x_441_; uint8_t v___x_442_; 
v_array_422_ = lean_ctor_get(v_pos_418_, 0);
v_idx_423_ = lean_ctor_get(v_pos_418_, 1);
lean_inc(v_idx_423_);
v___x_441_ = lean_byte_array_size(v_array_422_);
v___x_442_ = lean_nat_dec_lt(v_idx_423_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_443_ = lean_box(0);
lean_inc(v_pos_418_);
if (v_isShared_421_ == 0)
{
lean_ctor_set_tag(v___x_420_, 1);
lean_ctor_set(v___x_420_, 1, v___x_443_);
v___x_445_ = v___x_420_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_pos_418_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_inc(v_idx_423_);
v___y_425_ = v___x_445_;
v_pos_426_ = v_pos_418_;
v_idx_427_ = v_idx_423_;
goto v___jp_424_;
}
}
else
{
uint8_t v___x_447_; uint8_t v_got_448_; uint8_t v___x_449_; 
v___x_447_ = 10;
v_got_448_ = lean_byte_array_fget(v_array_422_, v_idx_423_);
v___x_449_ = lean_uint8_dec_eq(v_got_448_, v___x_447_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8));
lean_inc(v_pos_418_);
if (v_isShared_421_ == 0)
{
lean_ctor_set_tag(v___x_420_, 1);
lean_ctor_set(v___x_420_, 1, v___x_450_);
v___x_452_ = v___x_420_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_pos_418_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_inc(v_idx_423_);
v___y_425_ = v___x_452_;
v_pos_426_ = v_pos_418_;
v_idx_427_ = v_idx_423_;
goto v___jp_424_;
}
}
else
{
lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_466_; 
lean_inc_ref(v_array_422_);
v_isSharedCheck_466_ = !lean_is_exclusive(v_pos_418_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; lean_object* v_unused_468_; 
v_unused_467_ = lean_ctor_get(v_pos_418_, 1);
lean_dec(v_unused_467_);
v_unused_468_ = lean_ctor_get(v_pos_418_, 0);
lean_dec(v_unused_468_);
v___x_455_ = v_pos_418_;
v_isShared_456_ = v_isSharedCheck_466_;
goto v_resetjp_454_;
}
else
{
lean_dec(v_pos_418_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_466_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_add(v_idx_423_, v___x_457_);
lean_dec(v_idx_423_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_458_);
v___x_460_ = v___x_455_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_array_422_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v___x_458_);
v___x_460_ = v_reuseFailAlloc_465_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = lean_box(0);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 1, v___x_461_);
lean_ctor_set(v___x_420_, 0, v___x_460_);
v___x_463_ = v___x_420_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v___x_461_);
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
v___jp_424_:
{
uint8_t v___x_428_; 
v___x_428_ = lean_nat_dec_eq(v_idx_423_, v_idx_427_);
lean_dec(v_idx_427_);
lean_dec(v_idx_423_);
if (v___x_428_ == 0)
{
lean_dec_ref(v_pos_426_);
return v___y_425_;
}
else
{
lean_object* v_utf8_429_; lean_object* v___x_430_; 
lean_dec_ref(v___y_425_);
v_utf8_429_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6);
v___x_430_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_429_, v_pos_426_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_pos_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_439_; 
v_pos_431_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_439_ == 0)
{
lean_object* v_unused_440_; 
v_unused_440_ = lean_ctor_get(v___x_430_, 1);
lean_dec(v_unused_440_);
v___x_433_ = v___x_430_;
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_pos_431_);
lean_dec(v___x_430_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = lean_box(0);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v___x_435_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_pos_431_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
else
{
return v___x_430_;
}
}
}
}
}
else
{
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parse(lean_object* v_a_471_){
_start:
{
lean_object* v_utf8_472_; lean_object* v___x_473_; 
v_utf8_472_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1);
v___x_473_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_472_, v_a_471_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_pos_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_532_; 
v_pos_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; 
v_unused_533_ = lean_ctor_get(v___x_473_, 1);
lean_dec(v_unused_533_);
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_532_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_pos_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_532_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v_array_478_; lean_object* v_idx_479_; lean_object* v___y_481_; lean_object* v_pos_482_; lean_object* v_idx_483_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_array_478_ = lean_ctor_get(v_pos_474_, 0);
v_idx_479_ = lean_ctor_get(v_pos_474_, 1);
lean_inc(v_idx_479_);
v___x_507_ = lean_byte_array_size(v_array_478_);
v___x_508_ = lean_nat_dec_lt(v_idx_479_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_509_ = lean_box(0);
lean_inc(v_pos_474_);
if (v_isShared_477_ == 0)
{
lean_ctor_set_tag(v___x_476_, 1);
lean_ctor_set(v___x_476_, 1, v___x_509_);
v___x_511_ = v___x_476_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_pos_474_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_inc(v_idx_479_);
v___y_481_ = v___x_511_;
v_pos_482_ = v_pos_474_;
v_idx_483_ = v_idx_479_;
goto v___jp_480_;
}
}
else
{
uint8_t v___x_513_; uint8_t v_got_514_; uint8_t v___x_515_; 
v___x_513_ = 10;
v_got_514_ = lean_byte_array_fget(v_array_478_, v_idx_479_);
v___x_515_ = lean_uint8_dec_eq(v_got_514_, v___x_513_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_516_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8));
lean_inc(v_pos_474_);
if (v_isShared_477_ == 0)
{
lean_ctor_set_tag(v___x_476_, 1);
lean_ctor_set(v___x_476_, 1, v___x_516_);
v___x_518_ = v___x_476_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_pos_474_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_inc(v_idx_479_);
v___y_481_ = v___x_518_;
v_pos_482_ = v_pos_474_;
v_idx_483_ = v_idx_479_;
goto v___jp_480_;
}
}
else
{
lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_529_; 
lean_inc_ref(v_array_478_);
lean_del_object(v___x_476_);
v_isSharedCheck_529_ = !lean_is_exclusive(v_pos_474_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; lean_object* v_unused_531_; 
v_unused_530_ = lean_ctor_get(v_pos_474_, 1);
lean_dec(v_unused_530_);
v_unused_531_ = lean_ctor_get(v_pos_474_, 0);
lean_dec(v_unused_531_);
v___x_521_ = v_pos_474_;
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
else
{
lean_dec(v_pos_474_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_add(v_idx_479_, v___x_523_);
lean_dec(v_idx_479_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v___x_524_);
v___x_526_ = v___x_521_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_array_478_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v___x_524_);
v___x_526_ = v_reuseFailAlloc_528_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; 
v___x_527_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines(v___x_526_);
return v___x_527_;
}
}
}
}
v___jp_480_:
{
uint8_t v___x_484_; 
v___x_484_ = lean_nat_dec_eq(v_idx_479_, v_idx_483_);
lean_dec(v_idx_483_);
lean_dec(v_idx_479_);
if (v___x_484_ == 0)
{
lean_object* v_pos_485_; lean_object* v_err_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec_ref(v_pos_482_);
v_pos_485_ = lean_ctor_get(v___y_481_, 0);
v_err_486_ = lean_ctor_get(v___y_481_, 1);
v_isSharedCheck_493_ = !lean_is_exclusive(v___y_481_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___y_481_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_err_486_);
lean_inc(v_pos_485_);
lean_dec(v___y_481_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_pos_485_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_err_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
else
{
lean_object* v_utf8_494_; lean_object* v___x_495_; 
lean_dec_ref(v___y_481_);
v_utf8_494_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6);
v___x_495_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_494_, v_pos_482_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_pos_496_; lean_object* v___x_497_; 
v_pos_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_pos_496_);
lean_dec_ref_known(v___x_495_, 2);
v___x_497_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines(v_pos_496_);
return v___x_497_;
}
else
{
lean_object* v_pos_498_; lean_object* v_err_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
v_pos_498_ = lean_ctor_get(v___x_495_, 0);
v_err_499_ = lean_ctor_get(v___x_495_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_495_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_err_499_);
lean_inc(v_pos_498_);
lean_dec(v___x_495_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_pos_498_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_err_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_534_; lean_object* v_err_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
v_pos_534_ = lean_ctor_get(v___x_473_, 0);
v_err_535_ = lean_ctor_get(v___x_473_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_473_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_err_535_);
lean_inc(v_pos_534_);
lean_dec(v___x_473_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_pos_534_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_err_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___impl___redArg(lean_object* v_x_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = lean_obj_tag_nat(v_x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___impl___redArg___boxed(lean_object* v_x_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___impl___redArg(v_x_545_);
lean_dec(v_x_545_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___impl(lean_object* v_00_u03b1_547_, lean_object* v_x_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = lean_obj_tag_nat(v_x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___impl___boxed(lean_object* v_00_u03b1_550_, lean_object* v_x_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___impl(v_00_u03b1_550_, v_x_551_);
lean_dec(v_x_551_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(lean_object* v_t_553_, lean_object* v_k_554_){
_start:
{
if (lean_obj_tag(v_t_553_) == 0)
{
lean_object* v_x_555_; lean_object* v___x_556_; 
v_x_555_ = lean_ctor_get(v_t_553_, 0);
lean_inc(v_x_555_);
lean_dec_ref_known(v_t_553_, 1);
v___x_556_ = lean_apply_1(v_k_554_, v_x_555_);
return v___x_556_;
}
else
{
return v_k_554_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim(lean_object* v_00_u03b1_557_, lean_object* v_motive_558_, lean_object* v_ctorIdx_559_, lean_object* v_t_560_, lean_object* v_h_561_, lean_object* v_k_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_560_, v_k_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___boxed(lean_object* v_00_u03b1_564_, lean_object* v_motive_565_, lean_object* v_ctorIdx_566_, lean_object* v_t_567_, lean_object* v_h_568_, lean_object* v_k_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim(v_00_u03b1_564_, v_motive_565_, v_ctorIdx_566_, v_t_567_, v_h_568_, v_k_569_);
lean_dec(v_ctorIdx_566_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_success_elim___redArg(lean_object* v_t_571_, lean_object* v_success_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_571_, v_success_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_success_elim(lean_object* v_00_u03b1_574_, lean_object* v_motive_575_, lean_object* v_t_576_, lean_object* v_h_577_, lean_object* v_success_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_576_, v_success_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_timeout_elim___redArg(lean_object* v_t_580_, lean_object* v_timeout_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_580_, v_timeout_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_timeout_elim(lean_object* v_00_u03b1_583_, lean_object* v_motive_584_, lean_object* v_t_585_, lean_object* v_h_586_, lean_object* v_timeout_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_585_, v_timeout_587_);
return v___x_588_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = lean_box(0);
v___x_590_ = l_Lean_interruptExceptionId;
v___x_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
lean_ctor_set(v___x_591_, 1, v___x_589_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg(){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0);
v___x_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___boxed(lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg();
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0(lean_object* v_00_u03b1_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg();
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___boxed(lean_object* v_00_u03b1_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0(v_00_u03b1_602_, v___y_603_, v___y_604_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(lean_object* v_cleanup_607_, lean_object* v_x_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_toCold_612_; lean_object* v_cancelTk_x3f_613_; 
v_toCold_612_ = lean_ctor_get(v_a_609_, 0);
v_cancelTk_x3f_613_ = lean_ctor_get(v_toCold_612_, 10);
if (lean_obj_tag(v_cancelTk_x3f_613_) == 1)
{
lean_object* v_val_614_; uint8_t v___x_615_; 
v_val_614_ = lean_ctor_get(v_cancelTk_x3f_613_, 0);
v___x_615_ = l_IO_CancelToken_isSet(v_val_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; 
lean_dec_ref(v_cleanup_607_);
lean_inc(v_a_610_);
lean_inc_ref(v_a_609_);
v___x_616_ = lean_apply_3(v_x_608_, v_a_609_, v_a_610_, lean_box(0));
return v___x_616_;
}
else
{
lean_object* v___x_617_; 
lean_dec_ref(v_x_608_);
lean_inc(v_a_610_);
lean_inc_ref(v_a_609_);
v___x_617_ = lean_apply_3(v_cleanup_607_, v_a_609_, v_a_610_, lean_box(0));
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_618_; lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec_ref_known(v___x_617_, 1);
v___x_618_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg();
v_a_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
v_a_627_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_617_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_617_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
else
{
lean_object* v___x_635_; 
lean_dec_ref(v_cleanup_607_);
lean_inc(v_a_610_);
lean_inc_ref(v_a_609_);
v___x_635_ = lean_apply_3(v_x_608_, v_a_609_, v_a_610_, lean_box(0));
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg___boxed(lean_object* v_cleanup_636_, lean_object* v_x_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(v_cleanup_636_, v_x_637_, v_a_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck(lean_object* v_00_u03b1_642_, lean_object* v_cleanup_643_, lean_object* v_x_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(v_cleanup_643_, v_x_644_, v_a_645_, v_a_646_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___boxed(lean_object* v_00_u03b1_649_, lean_object* v_cleanup_650_, lean_object* v_x_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck(v_00_u03b1_649_, v_cleanup_650_, v_x_651_, v_a_652_, v_a_653_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(lean_object* v_budgetMs_656_, lean_object* v_cleanup_657_, lean_object* v_x_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_nat_dec_eq(v_budgetMs_656_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
lean_dec_ref(v_cleanup_657_);
lean_inc(v_a_660_);
lean_inc_ref(v_a_659_);
v___x_664_ = lean_apply_3(v_x_658_, v_a_659_, v_a_660_, lean_box(0));
return v___x_664_;
}
else
{
lean_object* v___x_665_; 
lean_dec_ref(v_x_658_);
lean_inc(v_a_660_);
lean_inc_ref(v_a_659_);
v___x_665_ = lean_apply_3(v_cleanup_657_, v_a_659_, v_a_660_, lean_box(0));
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_673_; 
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; 
v_unused_674_ = lean_ctor_get(v___x_665_, 0);
lean_dec(v_unused_674_);
v___x_667_ = v___x_665_;
v_isShared_668_ = v_isSharedCheck_673_;
goto v_resetjp_666_;
}
else
{
lean_dec(v___x_665_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_673_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_669_ = lean_box(1);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_669_);
v___x_671_ = v___x_667_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
v_a_675_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_665_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_665_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg___boxed(lean_object* v_budgetMs_683_, lean_object* v_cleanup_684_, lean_object* v_x_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(v_budgetMs_683_, v_cleanup_684_, v_x_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_budgetMs_683_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck(lean_object* v_00_u03b1_690_, lean_object* v_budgetMs_691_, lean_object* v_cleanup_692_, lean_object* v_x_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(v_budgetMs_691_, v_cleanup_692_, v_x_693_, v_a_694_, v_a_695_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___boxed(lean_object* v_00_u03b1_698_, lean_object* v_budgetMs_699_, lean_object* v_cleanup_700_, lean_object* v_x_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck(v_00_u03b1_698_, v_budgetMs_699_, v_cleanup_700_, v_x_701_, v_a_702_, v_a_703_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
lean_dec(v_budgetMs_699_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait(lean_object* v_cfg_706_, lean_object* v_child_707_){
_start:
{
uint8_t v___x_709_; lean_object* v___x_710_; 
v___x_709_ = 1;
v___x_710_ = lean_io_process_child_kill(v_cfg_706_, v_child_707_, v___x_709_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; 
lean_dec_ref_known(v___x_710_, 1);
v___x_711_ = lean_box(0);
v___x_712_ = lean_io_process_child_wait(v_cfg_706_, v_child_707_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; 
v_unused_720_ = lean_ctor_get(v___x_712_, 0);
lean_dec(v_unused_720_);
v___x_714_ = v___x_712_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_dec(v___x_712_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_711_);
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_711_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
v_a_721_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_712_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_712_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
else
{
return v___x_710_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait___boxed(lean_object* v_cfg_729_, lean_object* v_child_730_, lean_object* v_a_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait(v_cfg_729_, v_child_730_);
lean_dec_ref(v_child_730_);
lean_dec_ref(v_cfg_729_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(lean_object* v_e_733_){
_start:
{
if (lean_obj_tag(v_e_733_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_744_; 
v_a_735_ = lean_ctor_get(v_e_733_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v_e_733_);
if (v_isSharedCheck_744_ == 0)
{
v___x_737_ = v_e_733_;
v_isShared_738_ = v_isSharedCheck_744_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v_e_733_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_744_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_739_ = lean_io_error_to_string(v_a_735_);
v___x_740_ = lean_mk_io_user_error(v___x_739_);
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 1);
lean_ctor_set(v___x_737_, 0, v___x_740_);
v___x_742_ = v___x_737_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
v_a_745_ = lean_ctor_get(v_e_733_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v_e_733_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v_e_733_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v_e_733_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set_tag(v___x_747_, 0);
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg___boxed(lean_object* v_e_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v_e_753_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0(lean_object* v_00_u03b1_756_, lean_object* v_e_757_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v_e_757_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___boxed(lean_object* v_00_u03b1_760_, lean_object* v_e_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0(v_00_u03b1_760_, v_e_761_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1(lean_object* v_cfg_764_, lean_object* v_child_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_ref_769_; lean_object* v___x_770_; 
v_ref_769_ = lean_ctor_get(v___y_766_, 2);
v___x_770_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait(v_cfg_764_, v_child_765_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_790_; 
v_a_779_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_790_ == 0)
{
v___x_781_ = v___x_770_;
v_isShared_782_ = v_isSharedCheck_790_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_770_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_790_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_783_ = lean_io_error_to_string(v_a_779_);
v___x_784_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
v___x_785_ = l_Lean_MessageData_ofFormat(v___x_784_);
lean_inc(v_ref_769_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v_ref_769_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_786_);
v___x_788_ = v___x_781_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1___boxed(lean_object* v_cfg_791_, lean_object* v_child_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1(v_cfg_791_, v_child_792_, v___y_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec_ref(v_child_792_);
lean_dec_ref(v_cfg_791_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0(lean_object* v_cfg_797_, lean_object* v_child_798_, lean_object* v_sleepMs_799_, lean_object* v_budgetMs_800_, lean_object* v_maxSleepMs_801_, lean_object* v_stdout_802_, lean_object* v_stderr_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_ref_807_; lean_object* v___x_808_; 
v_ref_807_ = lean_ctor_get(v___y_804_, 2);
v___x_808_ = lean_io_process_child_try_wait(v_cfg_797_, v_child_798_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
if (lean_obj_tag(v_a_809_) == 0)
{
uint32_t v___x_810_; lean_object* v___x_811_; lean_object* v___y_813_; uint8_t v___x_816_; 
v___x_810_ = lean_uint32_of_nat(v_sleepMs_799_);
v___x_811_ = l_IO_sleep(v___x_810_);
v___x_816_ = lean_nat_dec_le(v_maxSleepMs_801_, v_sleepMs_799_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_unsigned_to_nat(2u);
v___x_818_ = lean_nat_mul(v_sleepMs_799_, v___x_817_);
v___y_813_ = v___x_818_;
goto v___jp_812_;
}
else
{
lean_inc(v_sleepMs_799_);
v___y_813_ = v_sleepMs_799_;
goto v___jp_812_;
}
v___jp_812_:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_nat_sub(v_budgetMs_800_, v_sleepMs_799_);
lean_dec(v_sleepMs_799_);
v___x_815_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(v_cfg_797_, v___x_814_, v___y_813_, v_maxSleepMs_801_, v_child_798_, v_stdout_802_, v_stderr_803_, v___y_804_, v___y_805_);
return v___x_815_;
}
}
else
{
lean_object* v_val_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_869_; 
lean_dec(v_maxSleepMs_801_);
lean_dec(v_sleepMs_799_);
lean_dec_ref(v_child_798_);
lean_dec_ref(v_cfg_797_);
v_val_819_ = lean_ctor_get(v_a_809_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v_a_809_);
if (v_isSharedCheck_869_ == 0)
{
v___x_821_ = v_a_809_;
v_isShared_822_ = v_isSharedCheck_869_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_val_819_);
lean_dec(v_a_809_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_869_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_task_get_own(v_stdout_802_);
v___x_824_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v___x_823_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_a_825_);
lean_dec_ref_known(v___x_824_, 1);
v___x_826_ = lean_task_get_own(v_stderr_803_);
v___x_827_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v___x_826_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_840_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_840_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_840_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_840_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; uint32_t v___x_833_; lean_object* v___x_835_; 
v___x_832_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_832_, 0, v_a_825_);
lean_ctor_set(v___x_832_, 1, v_a_828_);
v___x_833_ = lean_unbox_uint32(v_val_819_);
lean_dec(v_val_819_);
lean_ctor_set_uint32(v___x_832_, sizeof(void*)*2, v___x_833_);
if (v_isShared_822_ == 0)
{
lean_ctor_set_tag(v___x_821_, 0);
lean_ctor_set(v___x_821_, 0, v___x_832_);
v___x_835_ = v___x_821_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_832_);
v___x_835_ = v_reuseFailAlloc_839_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_837_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_835_);
v___x_837_ = v___x_830_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_854_; 
lean_dec(v_a_825_);
lean_dec(v_val_819_);
v_a_841_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_854_ == 0)
{
v___x_843_ = v___x_827_;
v_isShared_844_ = v_isSharedCheck_854_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_827_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_854_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_845_ = lean_io_error_to_string(v_a_841_);
if (v_isShared_822_ == 0)
{
lean_ctor_set_tag(v___x_821_, 3);
lean_ctor_set(v___x_821_, 0, v___x_845_);
v___x_847_ = v___x_821_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_853_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_848_ = l_Lean_MessageData_ofFormat(v___x_847_);
lean_inc(v_ref_807_);
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v_ref_807_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_849_);
v___x_851_ = v___x_843_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_868_; 
lean_dec(v_val_819_);
lean_dec_ref(v_stderr_803_);
v_a_855_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_868_ == 0)
{
v___x_857_ = v___x_824_;
v_isShared_858_ = v_isSharedCheck_868_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_824_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_868_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_859_ = lean_io_error_to_string(v_a_855_);
if (v_isShared_822_ == 0)
{
lean_ctor_set_tag(v___x_821_, 3);
lean_ctor_set(v___x_821_, 0, v___x_859_);
v___x_861_ = v___x_821_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_867_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_862_ = l_Lean_MessageData_ofFormat(v___x_861_);
lean_inc(v_ref_807_);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v_ref_807_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_863_);
v___x_865_ = v___x_857_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_881_; 
lean_dec_ref(v_stderr_803_);
lean_dec_ref(v_stdout_802_);
lean_dec(v_maxSleepMs_801_);
lean_dec(v_sleepMs_799_);
lean_dec_ref(v_child_798_);
lean_dec_ref(v_cfg_797_);
v_a_870_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_881_ == 0)
{
v___x_872_ = v___x_808_;
v_isShared_873_ = v_isSharedCheck_881_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_808_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_881_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_874_ = lean_io_error_to_string(v_a_870_);
v___x_875_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
v___x_876_ = l_Lean_MessageData_ofFormat(v___x_875_);
lean_inc(v_ref_807_);
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v_ref_807_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_877_);
v___x_879_ = v___x_872_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0___boxed(lean_object* v_cfg_882_, lean_object* v_child_883_, lean_object* v_sleepMs_884_, lean_object* v_budgetMs_885_, lean_object* v_maxSleepMs_886_, lean_object* v_stdout_887_, lean_object* v_stderr_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0(v_cfg_882_, v_child_883_, v_sleepMs_884_, v_budgetMs_885_, v_maxSleepMs_886_, v_stdout_887_, v_stderr_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v_budgetMs_885_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(lean_object* v_cfg_893_, lean_object* v_budgetMs_894_, lean_object* v_sleepMs_895_, lean_object* v_maxSleepMs_896_, lean_object* v_child_897_, lean_object* v_stdout_898_, lean_object* v_stderr_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v___f_903_; lean_object* v___f_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
lean_inc(v_budgetMs_894_);
lean_inc_ref(v_child_897_);
lean_inc_ref(v_cfg_893_);
v___f_903_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0___boxed), 10, 7);
lean_closure_set(v___f_903_, 0, v_cfg_893_);
lean_closure_set(v___f_903_, 1, v_child_897_);
lean_closure_set(v___f_903_, 2, v_sleepMs_895_);
lean_closure_set(v___f_903_, 3, v_budgetMs_894_);
lean_closure_set(v___f_903_, 4, v_maxSleepMs_896_);
lean_closure_set(v___f_903_, 5, v_stdout_898_);
lean_closure_set(v___f_903_, 6, v_stderr_899_);
v___f_904_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1___boxed), 5, 2);
lean_closure_set(v___f_904_, 0, v_cfg_893_);
lean_closure_set(v___f_904_, 1, v_child_897_);
lean_inc_ref(v___f_904_);
v___x_905_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___boxed), 6, 3);
lean_closure_set(v___x_905_, 0, lean_box(0));
lean_closure_set(v___x_905_, 1, v___f_904_);
lean_closure_set(v___x_905_, 2, v___f_903_);
v___x_906_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(v_budgetMs_894_, v___f_904_, v___x_905_, v_a_900_, v_a_901_);
lean_dec(v_budgetMs_894_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___boxed(lean_object* v_cfg_907_, lean_object* v_budgetMs_908_, lean_object* v_sleepMs_909_, lean_object* v_maxSleepMs_910_, lean_object* v_child_911_, lean_object* v_stdout_912_, lean_object* v_stderr_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(v_cfg_907_, v_budgetMs_908_, v_sleepMs_909_, v_maxSleepMs_910_, v_child_911_, v_stdout_912_, v_stderr_913_, v_a_914_, v_a_915_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0(lean_object* v_stderr_918_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_IO_FS_Handle_readToEnd(v_stderr_918_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set_tag(v___x_923_, 1);
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
v_a_929_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_920_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_920_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set_tag(v___x_931_, 0);
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0___boxed(lean_object* v_stderr_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0(v_stderr_937_);
lean_dec(v_stderr_937_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1(lean_object* v_stdout_940_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_IO_FS_Handle_readToEnd(v_stdout_940_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set_tag(v___x_945_, 1);
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
v_a_951_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_942_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_942_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set_tag(v___x_953_, 0);
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1___boxed(lean_object* v_stdout_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1(v_stdout_959_);
lean_dec(v_stdout_959_);
return v_res_961_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_962_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__0);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_965_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__1);
v___x_966_ = lean_unsigned_to_nat(0u);
v___x_967_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
lean_ctor_set(v___x_967_, 2, v___x_966_);
lean_ctor_set(v___x_967_, 3, v___x_966_);
lean_ctor_set(v___x_967_, 4, v___x_965_);
lean_ctor_set(v___x_967_, 5, v___x_965_);
lean_ctor_set(v___x_967_, 6, v___x_965_);
lean_ctor_set(v___x_967_, 7, v___x_965_);
lean_ctor_set(v___x_967_, 8, v___x_965_);
lean_ctor_set(v___x_967_, 9, v___x_965_);
lean_ctor_set(v___x_967_, 10, v___x_965_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_968_ = lean_unsigned_to_nat(32u);
v___x_969_ = lean_mk_empty_array_with_capacity(v___x_968_);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_971_ = ((size_t)5ULL);
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = lean_unsigned_to_nat(32u);
v___x_974_ = lean_mk_empty_array_with_capacity(v___x_973_);
v___x_975_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__3);
v___x_976_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v___x_974_);
lean_ctor_set(v___x_976_, 2, v___x_972_);
lean_ctor_set(v___x_976_, 3, v___x_972_);
lean_ctor_set_usize(v___x_976_, 4, v___x_971_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_977_ = lean_box(1);
v___x_978_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__4);
v___x_979_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__1);
v___x_980_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set(v___x_980_, 1, v___x_978_);
lean_ctor_set(v___x_980_, 2, v___x_977_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0(lean_object* v_msgData_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v___x_985_; lean_object* v_toCold_986_; lean_object* v_env_987_; lean_object* v_options_988_; uint8_t v___x_989_; lean_object* v_env_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_985_ = lean_st_ref_get(v___y_983_);
v_toCold_986_ = lean_ctor_get(v___y_982_, 0);
v_env_987_ = lean_ctor_get(v___x_985_, 0);
lean_inc_ref(v_env_987_);
lean_dec(v___x_985_);
v_options_988_ = lean_ctor_get(v_toCold_986_, 2);
v___x_989_ = 0;
v_env_990_ = l_Lean_Environment_setRecordingDeps(v_env_987_, v___x_989_);
v___x_991_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__2);
v___x_992_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_988_);
v___x_993_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_993_, 0, v_env_990_);
lean_ctor_set(v___x_993_, 1, v___x_991_);
lean_ctor_set(v___x_993_, 2, v___x_992_);
lean_ctor_set(v___x_993_, 3, v_options_988_);
v___x_994_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v_msgData_981_);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0___boxed(lean_object* v_msgData_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0(v_msgData_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0___redArg(lean_object* v_msg_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_ref_1005_; lean_object* v___x_1006_; lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1015_; 
v_ref_1005_ = lean_ctor_get(v___y_1002_, 2);
v___x_1006_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0_spec__0(v_msg_1001_, v___y_1002_, v___y_1003_);
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1015_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1015_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
lean_inc(v_ref_1005_);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v_ref_1005_);
lean_ctor_set(v___x_1011_, 1, v_a_1007_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set_tag(v___x_1009_, 1);
lean_ctor_set(v___x_1009_, 0, v___x_1011_);
v___x_1013_ = v___x_1009_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0___redArg___boxed(lean_object* v_msg_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0___redArg(v_msg_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
return v_res_1020_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__2(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__1));
v___x_1026_ = l_Lean_stringToMessageData(v___x_1025_);
return v___x_1026_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__4(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__3));
v___x_1029_ = l_Lean_stringToMessageData(v___x_1028_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__6(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__5));
v___x_1032_ = l_Lean_stringToMessageData(v___x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible(lean_object* v_timeout_1033_, lean_object* v_args_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v___x_1038_; lean_object* v_child_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v_cmd_1055_; lean_object* v_args_1056_; lean_object* v_cwd_1057_; lean_object* v_env_1058_; uint8_t v_inheritEnv_1059_; uint8_t v_setsid_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1096_; 
v___x_1038_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0));
v_cmd_1055_ = lean_ctor_get(v_args_1034_, 1);
v_args_1056_ = lean_ctor_get(v_args_1034_, 2);
v_cwd_1057_ = lean_ctor_get(v_args_1034_, 3);
v_env_1058_ = lean_ctor_get(v_args_1034_, 4);
v_inheritEnv_1059_ = lean_ctor_get_uint8(v_args_1034_, sizeof(void*)*5);
v_setsid_1060_ = lean_ctor_get_uint8(v_args_1034_, sizeof(void*)*5 + 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_args_1034_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v_args_1034_, 0);
lean_dec(v_unused_1097_);
v___x_1062_ = v_args_1034_;
v_isShared_1063_ = v_isSharedCheck_1096_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_env_1058_);
lean_inc(v_cwd_1057_);
lean_inc(v_args_1056_);
lean_inc(v_cmd_1055_);
lean_dec(v_args_1034_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1096_;
goto v_resetjp_1061_;
}
v___jp_1039_:
{
lean_object* v_stdout_1043_; lean_object* v_stderr_1044_; lean_object* v___f_1045_; lean_object* v___f_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v_stdout_1043_ = lean_ctor_get(v_child_1040_, 1);
v_stderr_1044_ = lean_ctor_get(v_child_1040_, 2);
lean_inc(v_stderr_1044_);
v___f_1045_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1045_, 0, v_stderr_1044_);
lean_inc(v_stdout_1043_);
v___f_1046_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1046_, 0, v_stdout_1043_);
v___x_1047_ = lean_unsigned_to_nat(9u);
v___x_1048_ = lean_io_as_task(v___f_1046_, v___x_1047_);
v___x_1049_ = lean_io_as_task(v___f_1045_, v___x_1047_);
v___x_1050_ = lean_unsigned_to_nat(1000u);
v___x_1051_ = lean_nat_mul(v_timeout_1033_, v___x_1050_);
v___x_1052_ = lean_unsigned_to_nat(1u);
v___x_1053_ = lean_unsigned_to_nat(64u);
v___x_1054_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(v___x_1038_, v___x_1051_, v___x_1052_, v___x_1053_, v_child_1040_, v___x_1048_, v___x_1049_, v___y_1041_, v___y_1042_);
return v___x_1054_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
lean_inc_ref(v_cmd_1055_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v___x_1038_);
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_cmd_1055_);
lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_args_1056_);
lean_ctor_set(v_reuseFailAlloc_1095_, 3, v_cwd_1057_);
lean_ctor_set(v_reuseFailAlloc_1095_, 4, v_env_1058_);
lean_ctor_set_uint8(v_reuseFailAlloc_1095_, sizeof(void*)*5, v_inheritEnv_1059_);
lean_ctor_set_uint8(v_reuseFailAlloc_1095_, sizeof(void*)*5 + 1, v_setsid_1060_);
v___x_1065_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_io_process_spawn(v___x_1065_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; 
lean_dec_ref(v_cmd_1055_);
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
v_child_1040_ = v_a_1067_;
v___y_1041_ = v_a_1035_;
v___y_1042_ = v_a_1036_;
goto v___jp_1039_;
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1094_; 
v_a_1068_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1070_ = v___x_1066_;
v_isShared_1071_ = v_isSharedCheck_1094_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1066_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1094_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1072_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__2, &l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__2);
v___x_1073_ = l_Lean_stringToMessageData(v_cmd_1055_);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__4, &l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__4);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_io_error_to_string(v_a_1068_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 3);
lean_ctor_set(v___x_1070_, 0, v___x_1077_);
v___x_1079_ = v___x_1070_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
v___x_1080_ = l_Lean_MessageData_ofFormat(v___x_1079_);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1076_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__6, &l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__6);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0___redArg(v___x_1083_, v_a_1035_, v_a_1036_);
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___boxed(lean_object* v_timeout_1098_, lean_object* v_args_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible(v_timeout_1098_, v_args_1099_, v_a_1100_, v_a_1101_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_timeout_1098_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0(lean_object* v_00_u03b1_1104_, lean_object* v_msg_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0___redArg(v_msg_1105_, v___y_1106_, v___y_1107_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0___boxed(lean_object* v_00_u03b1_1110_, lean_object* v_msg_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0(v_00_u03b1_1110_, v_msg_1111_, v___y_1112_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
return v_res_1115_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___closed__2(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___closed__1));
v___x_1120_ = l_Lean_MessageData_ofFormat(v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___closed__2);
v___x_1125_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0___redArg(v___x_1124_, v_a_1121_, v_a_1122_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___boxed(lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(v_a_1126_, v_a_1127_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout(lean_object* v_00_u03b1_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(v_a_1131_, v_a_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___boxed(lean_object* v_00_u03b1_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout(v_00_u03b1_1135_, v_a_1136_, v_a_1137_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
return v_res_1139_;
}
}
static uint32_t _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__2(void){
_start:
{
lean_object* v___x_1143_; uint32_t v___x_1144_; 
v___x_1143_ = lean_unsigned_to_nat(0u);
v___x_1144_ = lean_int32_of_nat(v___x_1143_);
return v___x_1144_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_uint32_once(&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__2, &l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__2);
v___x_1146_ = lean_box_uint32(v___x_1145_);
return v___x_1146_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__3(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1147_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__1));
v___x_1148_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__3___boxed__const__1;
v___x_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
return v___x_1149_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__4(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1150_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__3, &l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__3);
v___x_1151_ = lean_unsigned_to_nat(1u);
v___x_1152_ = lean_mk_empty_array_with_capacity(v___x_1151_);
v___x_1153_ = lean_array_push(v___x_1152_, v___x_1150_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode(uint8_t v_mode_1157_){
_start:
{
lean_object* v___y_1159_; 
switch(v_mode_1157_)
{
case 0:
{
lean_object* v___x_1163_; 
v___x_1163_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__5));
v___y_1159_ = v___x_1163_;
goto v___jp_1158_;
}
case 1:
{
lean_object* v___x_1164_; 
v___x_1164_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__6));
v___y_1159_ = v___x_1164_;
goto v___jp_1158_;
}
default: 
{
lean_object* v___x_1165_; 
v___x_1165_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__7));
v___y_1159_ = v___x_1165_;
goto v___jp_1158_;
}
}
v___jp_1158_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1160_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__0));
v___x_1161_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__4, &l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__4);
lean_inc_ref(v___y_1159_);
v___x_1162_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1162_, 0, v___y_1159_);
lean_ctor_set(v___x_1162_, 1, v___x_1160_);
lean_ctor_set(v___x_1162_, 2, v___x_1161_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___boxed(lean_object* v_mode_1166_){
_start:
{
uint8_t v_mode_boxed_1167_; lean_object* v_res_1168_; 
v_mode_boxed_1167_ = lean_unbox(v_mode_1166_);
v_res_1168_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode(v_mode_boxed_1167_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat(lean_object* v_opts_1178_, uint8_t v_binary_1179_){
_start:
{
lean_object* v_configuration_1180_; lean_object* v_longOptions_1181_; lean_object* v_options_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1196_; 
v_configuration_1180_ = lean_ctor_get(v_opts_1178_, 0);
v_longOptions_1181_ = lean_ctor_get(v_opts_1178_, 1);
v_options_1182_ = lean_ctor_get(v_opts_1178_, 2);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_opts_1178_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1184_ = v_opts_1178_;
v_isShared_1185_ = v_isSharedCheck_1196_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_options_1182_);
lean_inc(v_longOptions_1181_);
lean_inc(v_configuration_1180_);
lean_dec(v_opts_1178_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1196_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint32_t v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1186_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___closed__2));
v___x_1187_ = l_Array_append___redArg(v_longOptions_1181_, v___x_1186_);
v___x_1188_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___closed__3));
v___x_1189_ = lean_bool_to_uint32(v_binary_1179_);
v___x_1190_ = lean_box_uint32(v___x_1189_);
v___x_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1188_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = lean_array_push(v_options_1182_, v___x_1191_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 2, v___x_1192_);
lean_ctor_set(v___x_1184_, 1, v___x_1187_);
v___x_1194_ = v___x_1184_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_configuration_1180_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1195_, 2, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___boxed(lean_object* v_opts_1197_, lean_object* v_binary_1198_){
_start:
{
uint8_t v_binary_boxed_1199_; lean_object* v_res_1200_; 
v_binary_boxed_1199_ = lean_unbox(v_binary_1198_);
v_res_1200_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat(v_opts_1197_, v_binary_boxed_1199_);
return v_res_1200_;
}
}
static uint32_t _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__1(void){
_start:
{
lean_object* v___x_1202_; uint32_t v___x_1203_; 
v___x_1202_ = lean_unsigned_to_nat(2u);
v___x_1203_ = lean_int32_of_nat(v___x_1202_);
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_uint32_once(&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__1, &l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__1);
v___x_1205_ = lean_box_uint32(v___x_1204_);
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__2(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__0));
v___x_1207_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__2___boxed__const__1;
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1206_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
return v___x_1208_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__4(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1210_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__3));
v___x_1211_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__3___boxed__const__1;
v___x_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental(lean_object* v_opts_1213_){
_start:
{
lean_object* v_configuration_1214_; lean_object* v_longOptions_1215_; lean_object* v_options_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1227_; 
v_configuration_1214_ = lean_ctor_get(v_opts_1213_, 0);
v_longOptions_1215_ = lean_ctor_get(v_opts_1213_, 1);
v_options_1216_ = lean_ctor_get(v_opts_1213_, 2);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_opts_1213_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1218_ = v_opts_1213_;
v_isShared_1219_ = v_isSharedCheck_1227_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_options_1216_);
lean_inc(v_longOptions_1215_);
lean_inc(v_configuration_1214_);
lean_dec(v_opts_1213_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1227_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1220_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__2, &l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__2);
v___x_1221_ = lean_array_push(v_options_1216_, v___x_1220_);
v___x_1222_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__4, &l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__4);
v___x_1223_ = lean_array_push(v___x_1221_, v___x_1222_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 2, v___x_1223_);
v___x_1225_ = v___x_1218_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_configuration_1214_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_longOptions_1215_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flag(lean_object* v_opt_1229_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flag___closed__0));
v___x_1231_ = lean_string_append(v___x_1230_, v_opt_1229_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flag___boxed(lean_object* v_opt_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flag(v_opt_1232_);
lean_dec_ref(v_opt_1232_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flagValue(lean_object* v_opt_1235_, uint32_t v_val_1236_){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1237_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flag___closed__0));
v___x_1238_ = lean_string_append(v___x_1237_, v_opt_1235_);
v___x_1239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flagValue___closed__0));
v___x_1240_ = lean_string_append(v___x_1238_, v___x_1239_);
v___x_1241_ = lean_int32_to_int(v_val_1236_);
v___x_1242_ = l_Int_repr(v___x_1241_);
lean_dec(v___x_1241_);
v___x_1243_ = lean_string_append(v___x_1240_, v___x_1242_);
lean_dec_ref(v___x_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flagValue___boxed(lean_object* v_opt_1244_, lean_object* v_val_1245_){
_start:
{
uint32_t v_val_boxed_1246_; lean_object* v_res_1247_; 
v_val_boxed_1246_ = lean_unbox_uint32(v_val_1245_);
lean_dec(v_val_1245_);
v_res_1247_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flagValue(v_opt_1244_, v_val_boxed_1246_);
lean_dec_ref(v_opt_1244_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__1(lean_object* v_as_1248_, size_t v_sz_1249_, size_t v_i_1250_, lean_object* v_b_1251_){
_start:
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_usize_dec_lt(v_i_1250_, v_sz_1249_);
if (v___x_1252_ == 0)
{
return v_b_1251_;
}
else
{
lean_object* v_a_1253_; lean_object* v_fst_1254_; lean_object* v_snd_1255_; uint32_t v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; size_t v___x_1259_; size_t v___x_1260_; 
v_a_1253_ = lean_array_uget_borrowed(v_as_1248_, v_i_1250_);
v_fst_1254_ = lean_ctor_get(v_a_1253_, 0);
v_snd_1255_ = lean_ctor_get(v_a_1253_, 1);
v___x_1256_ = lean_unbox_uint32(v_snd_1255_);
v___x_1257_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flagValue(v_fst_1254_, v___x_1256_);
v___x_1258_ = lean_array_push(v_b_1251_, v___x_1257_);
v___x_1259_ = ((size_t)1ULL);
v___x_1260_ = lean_usize_add(v_i_1250_, v___x_1259_);
v_i_1250_ = v___x_1260_;
v_b_1251_ = v___x_1258_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__1___boxed(lean_object* v_as_1262_, lean_object* v_sz_1263_, lean_object* v_i_1264_, lean_object* v_b_1265_){
_start:
{
size_t v_sz_boxed_1266_; size_t v_i_boxed_1267_; lean_object* v_res_1268_; 
v_sz_boxed_1266_ = lean_unbox_usize(v_sz_1263_);
lean_dec(v_sz_1263_);
v_i_boxed_1267_ = lean_unbox_usize(v_i_1264_);
lean_dec(v_i_1264_);
v_res_1268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__1(v_as_1262_, v_sz_boxed_1266_, v_i_boxed_1267_, v_b_1265_);
lean_dec_ref(v_as_1262_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__0(lean_object* v_as_1269_, size_t v_sz_1270_, size_t v_i_1271_, lean_object* v_b_1272_){
_start:
{
uint8_t v___x_1273_; 
v___x_1273_ = lean_usize_dec_lt(v_i_1271_, v_sz_1270_);
if (v___x_1273_ == 0)
{
return v_b_1272_;
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; size_t v___x_1277_; size_t v___x_1278_; 
v_a_1274_ = lean_array_uget_borrowed(v_as_1269_, v_i_1271_);
v___x_1275_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flag(v_a_1274_);
v___x_1276_ = lean_array_push(v_b_1272_, v___x_1275_);
v___x_1277_ = ((size_t)1ULL);
v___x_1278_ = lean_usize_add(v_i_1271_, v___x_1277_);
v_i_1271_ = v___x_1278_;
v_b_1272_ = v___x_1276_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__0___boxed(lean_object* v_as_1280_, lean_object* v_sz_1281_, lean_object* v_i_1282_, lean_object* v_b_1283_){
_start:
{
size_t v_sz_boxed_1284_; size_t v_i_boxed_1285_; lean_object* v_res_1286_; 
v_sz_boxed_1284_ = lean_unbox_usize(v_sz_1281_);
lean_dec(v_sz_1281_);
v_i_boxed_1285_ = lean_unbox_usize(v_i_1282_);
lean_dec(v_i_1282_);
v_res_1286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__0(v_as_1280_, v_sz_boxed_1284_, v_i_boxed_1285_, v_b_1283_);
lean_dec_ref(v_as_1280_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs(lean_object* v_opts_1287_){
_start:
{
lean_object* v_configuration_1288_; lean_object* v_longOptions_1289_; lean_object* v_options_1290_; lean_object* v_args_1291_; lean_object* v___x_1292_; lean_object* v_args_1293_; size_t v_sz_1294_; size_t v___x_1295_; lean_object* v___x_1296_; size_t v_sz_1297_; lean_object* v___x_1298_; 
v_configuration_1288_ = lean_ctor_get(v_opts_1287_, 0);
v_longOptions_1289_ = lean_ctor_get(v_opts_1287_, 1);
v_options_1290_ = lean_ctor_get(v_opts_1287_, 2);
v_args_1291_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__0));
v___x_1292_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flag(v_configuration_1288_);
v_args_1293_ = lean_array_push(v_args_1291_, v___x_1292_);
v_sz_1294_ = lean_array_size(v_longOptions_1289_);
v___x_1295_ = ((size_t)0ULL);
v___x_1296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__0(v_longOptions_1289_, v_sz_1294_, v___x_1295_, v_args_1293_);
v_sz_1297_ = lean_array_size(v_options_1290_);
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__1(v_options_1290_, v_sz_1297_, v___x_1295_, v___x_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs___boxed(lean_object* v_opts_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs(v_opts_1299_);
lean_dec_ref(v_opts_1299_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__1(lean_object* v_solver_1301_, lean_object* v_as_1302_, size_t v_sz_1303_, size_t v_i_1304_, lean_object* v_b_1305_){
_start:
{
uint8_t v___x_1307_; 
v___x_1307_ = lean_usize_dec_lt(v_i_1304_, v_sz_1303_);
if (v___x_1307_ == 0)
{
return v_b_1305_;
}
else
{
lean_object* v_a_1308_; lean_object* v_fst_1309_; lean_object* v_snd_1310_; lean_object* v___x_1311_; uint32_t v___x_1312_; uint8_t v___x_1313_; size_t v___x_1314_; size_t v___x_1315_; 
v_a_1308_ = lean_array_uget_borrowed(v_as_1302_, v_i_1304_);
v_fst_1309_ = lean_ctor_get(v_a_1308_, 0);
v_snd_1310_ = lean_ctor_get(v_a_1308_, 1);
v___x_1311_ = lean_box(0);
v___x_1312_ = lean_unbox_uint32(v_snd_1310_);
v___x_1313_ = l_Lean_Cadical_Solver_setOption(v_solver_1301_, v_fst_1309_, v___x_1312_);
v___x_1314_ = ((size_t)1ULL);
v___x_1315_ = lean_usize_add(v_i_1304_, v___x_1314_);
v_i_1304_ = v___x_1315_;
v_b_1305_ = v___x_1311_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__1___boxed(lean_object* v_solver_1317_, lean_object* v_as_1318_, lean_object* v_sz_1319_, lean_object* v_i_1320_, lean_object* v_b_1321_, lean_object* v___y_1322_){
_start:
{
size_t v_sz_boxed_1323_; size_t v_i_boxed_1324_; lean_object* v_res_1325_; 
v_sz_boxed_1323_ = lean_unbox_usize(v_sz_1319_);
lean_dec(v_sz_1319_);
v_i_boxed_1324_ = lean_unbox_usize(v_i_1320_);
lean_dec(v_i_1320_);
v_res_1325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__1(v_solver_1317_, v_as_1318_, v_sz_boxed_1323_, v_i_boxed_1324_, v_b_1321_);
lean_dec_ref(v_as_1318_);
lean_dec_ref(v_solver_1317_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__0(lean_object* v_solver_1326_, lean_object* v_as_1327_, size_t v_sz_1328_, size_t v_i_1329_, lean_object* v_b_1330_){
_start:
{
uint8_t v___x_1332_; 
v___x_1332_ = lean_usize_dec_lt(v_i_1329_, v_sz_1328_);
if (v___x_1332_ == 0)
{
return v_b_1330_;
}
else
{
lean_object* v___x_1333_; lean_object* v_a_1334_; uint8_t v___x_1335_; size_t v___x_1336_; size_t v___x_1337_; 
v___x_1333_ = lean_box(0);
v_a_1334_ = lean_array_uget_borrowed(v_as_1327_, v_i_1329_);
v___x_1335_ = l_Lean_Cadical_Solver_setLongOption(v_solver_1326_, v_a_1334_);
v___x_1336_ = ((size_t)1ULL);
v___x_1337_ = lean_usize_add(v_i_1329_, v___x_1336_);
v_i_1329_ = v___x_1337_;
v_b_1330_ = v___x_1333_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__0___boxed(lean_object* v_solver_1339_, lean_object* v_as_1340_, lean_object* v_sz_1341_, lean_object* v_i_1342_, lean_object* v_b_1343_, lean_object* v___y_1344_){
_start:
{
size_t v_sz_boxed_1345_; size_t v_i_boxed_1346_; lean_object* v_res_1347_; 
v_sz_boxed_1345_ = lean_unbox_usize(v_sz_1341_);
lean_dec(v_sz_1341_);
v_i_boxed_1346_ = lean_unbox_usize(v_i_1342_);
lean_dec(v_i_1342_);
v_res_1347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__0(v_solver_1339_, v_as_1340_, v_sz_boxed_1345_, v_i_boxed_1346_, v_b_1343_);
lean_dec_ref(v_as_1340_);
lean_dec_ref(v_solver_1339_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver(lean_object* v_opts_1348_, lean_object* v_solver_1349_){
_start:
{
lean_object* v_configuration_1351_; lean_object* v_longOptions_1352_; lean_object* v_options_1353_; uint8_t v___x_1354_; lean_object* v___x_1355_; size_t v_sz_1356_; size_t v___x_1357_; lean_object* v___x_1358_; size_t v_sz_1359_; lean_object* v___x_1360_; 
v_configuration_1351_ = lean_ctor_get(v_opts_1348_, 0);
v_longOptions_1352_ = lean_ctor_get(v_opts_1348_, 1);
v_options_1353_ = lean_ctor_get(v_opts_1348_, 2);
v___x_1354_ = l_Lean_Cadical_Solver_configure(v_solver_1349_, v_configuration_1351_);
v___x_1355_ = lean_box(0);
v_sz_1356_ = lean_array_size(v_longOptions_1352_);
v___x_1357_ = ((size_t)0ULL);
v___x_1358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__0(v_solver_1349_, v_longOptions_1352_, v_sz_1356_, v___x_1357_, v___x_1355_);
v_sz_1359_ = lean_array_size(v_options_1353_);
v___x_1360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__1(v_solver_1349_, v_options_1353_, v_sz_1359_, v___x_1357_, v___x_1355_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver___boxed(lean_object* v_opts_1361_, lean_object* v_solver_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver(v_opts_1361_, v_solver_1362_);
lean_dec_ref(v_solver_1362_);
lean_dec_ref(v_opts_1361_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery(lean_object* v_solverPath_1375_, lean_object* v_problemPath_1376_, lean_object* v_proofOutput_1377_, lean_object* v_timeout_1378_, uint8_t v_binaryProofs_1379_, uint8_t v_mode_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v___x_1384_; lean_object* v_options_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v_args_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; uint8_t v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1384_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode(v_mode_1380_);
v_options_1385_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat(v___x_1384_, v_binaryProofs_1379_);
v___x_1386_ = lean_unsigned_to_nat(2u);
v___x_1387_ = lean_mk_empty_array_with_capacity(v___x_1386_);
v___x_1388_ = lean_array_push(v___x_1387_, v_problemPath_1376_);
v___x_1389_ = lean_array_push(v___x_1388_, v_proofOutput_1377_);
v___x_1390_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs(v_options_1385_);
lean_dec_ref(v_options_1385_);
v_args_1391_ = l_Array_append___redArg(v___x_1389_, v___x_1390_);
lean_dec_ref(v___x_1390_);
v___x_1392_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__0));
v___x_1393_ = lean_box(0);
v___x_1394_ = lean_unsigned_to_nat(0u);
v___x_1395_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__1));
v___x_1396_ = 1;
v___x_1397_ = 0;
v___x_1398_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1398_, 0, v___x_1392_);
lean_ctor_set(v___x_1398_, 1, v_solverPath_1375_);
lean_ctor_set(v___x_1398_, 2, v_args_1391_);
lean_ctor_set(v___x_1398_, 3, v___x_1393_);
lean_ctor_set(v___x_1398_, 4, v___x_1395_);
lean_ctor_set_uint8(v___x_1398_, sizeof(void*)*5, v___x_1396_);
lean_ctor_set_uint8(v___x_1398_, sizeof(void*)*5 + 1, v___x_1397_);
v___x_1399_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible(v_timeout_1378_, v___x_1398_, v_a_1381_, v_a_1382_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1465_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1465_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1465_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
if (lean_obj_tag(v_a_1400_) == 0)
{
lean_object* v_x_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1463_; 
v_x_1404_ = lean_ctor_get(v_a_1400_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_a_1400_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1406_ = v_a_1400_;
v_isShared_1407_ = v_isSharedCheck_1463_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_x_1404_);
lean_dec(v_a_1400_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1463_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v_stdout_1408_; lean_object* v_stderr_1409_; lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v_stdout_1408_ = lean_ctor_get(v_x_1404_, 0);
lean_inc_ref(v_stdout_1408_);
v_stderr_1409_ = lean_ctor_get(v_x_1404_, 1);
lean_inc_ref(v_stderr_1409_);
lean_dec(v_x_1404_);
v___x_1456_ = lean_string_utf8_byte_size(v_stdout_1408_);
v___x_1457_ = lean_unsigned_to_nat(15u);
v___x_1458_ = lean_nat_dec_le(v___x_1457_, v___x_1456_);
if (v___x_1458_ == 0)
{
goto v___jp_1421_;
}
else
{
lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1459_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__6));
v___x_1460_ = lean_string_memcmp(v_stdout_1408_, v___x_1459_, v___x_1394_, v___x_1394_, v___x_1457_);
if (v___x_1460_ == 0)
{
goto v___jp_1421_;
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec_ref(v_stderr_1409_);
lean_dec_ref(v_stdout_1408_);
lean_del_object(v___x_1406_);
lean_del_object(v___x_1402_);
v___x_1461_ = lean_box(1);
v___x_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
return v___x_1462_;
}
}
v___jp_1410_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1411_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__2));
v___x_1412_ = lean_string_append(v___x_1411_, v_stdout_1408_);
lean_dec_ref(v_stdout_1408_);
v___x_1413_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__3));
v___x_1414_ = lean_string_append(v___x_1412_, v___x_1413_);
v___x_1415_ = lean_string_append(v___x_1414_, v_stderr_1409_);
lean_dec_ref(v_stderr_1409_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set_tag(v___x_1406_, 3);
lean_ctor_set(v___x_1406_, 0, v___x_1415_);
v___x_1417_ = v___x_1406_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = l_Lean_MessageData_ofFormat(v___x_1417_);
v___x_1419_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0___redArg(v___x_1418_, v_a_1381_, v_a_1382_);
return v___x_1419_;
}
}
v___jp_1421_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1422_ = lean_string_utf8_byte_size(v_stdout_1408_);
v___x_1423_ = lean_unsigned_to_nat(13u);
v___x_1424_ = lean_nat_dec_le(v___x_1423_, v___x_1422_);
if (v___x_1424_ == 0)
{
lean_del_object(v___x_1402_);
goto v___jp_1410_;
}
else
{
lean_object* v___x_1425_; uint8_t v___x_1426_; 
v___x_1425_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0));
v___x_1426_ = lean_string_memcmp(v_stdout_1408_, v___x_1425_, v___x_1394_, v___x_1394_, v___x_1423_);
if (v___x_1426_ == 0)
{
lean_del_object(v___x_1402_);
goto v___jp_1410_;
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_dec_ref(v_stderr_1409_);
lean_del_object(v___x_1406_);
v___x_1427_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parse), 1, 0);
lean_inc_ref(v_stdout_1408_);
v___x_1428_ = lean_string_to_utf8(v_stdout_1408_);
v___x_1429_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_1427_, v___x_1428_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1444_; 
lean_del_object(v___x_1402_);
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1444_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1444_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1434_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__4));
v___x_1435_ = lean_string_append(v___x_1434_, v_a_1430_);
lean_dec(v_a_1430_);
v___x_1436_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__5));
v___x_1437_ = lean_string_append(v___x_1435_, v___x_1436_);
v___x_1438_ = lean_string_append(v___x_1437_, v_stdout_1408_);
lean_dec_ref(v_stdout_1408_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set_tag(v___x_1432_, 3);
lean_ctor_set(v___x_1432_, 0, v___x_1438_);
v___x_1440_ = v___x_1432_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = l_Lean_MessageData_ofFormat(v___x_1440_);
v___x_1442_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_runInterruptible_spec__0___redArg(v___x_1441_, v_a_1381_, v_a_1382_);
return v___x_1442_;
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1455_; 
lean_dec_ref(v_stdout_1408_);
v_a_1445_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1447_ = v___x_1429_;
v_isShared_1448_ = v_isSharedCheck_1455_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1429_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1455_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
lean_ctor_set_tag(v___x_1447_, 0);
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1452_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v___x_1450_);
v___x_1452_ = v___x_1402_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1464_; 
lean_del_object(v___x_1402_);
v___x_1464_ = l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(v_a_1381_, v_a_1382_);
return v___x_1464_;
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
v_a_1466_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1399_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1399_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___boxed(lean_object* v_solverPath_1474_, lean_object* v_problemPath_1475_, lean_object* v_proofOutput_1476_, lean_object* v_timeout_1477_, lean_object* v_binaryProofs_1478_, lean_object* v_mode_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
uint8_t v_binaryProofs_boxed_1483_; uint8_t v_mode_boxed_1484_; lean_object* v_res_1485_; 
v_binaryProofs_boxed_1483_ = lean_unbox(v_binaryProofs_1478_);
v_mode_boxed_1484_ = lean_unbox(v_mode_1479_);
v_res_1485_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solverPath_1474_, v_problemPath_1475_, v_proofOutput_1476_, v_timeout_1477_, v_binaryProofs_boxed_1483_, v_mode_boxed_1484_, v_a_1480_, v_a_1481_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
lean_dec(v_timeout_1477_);
return v_res_1485_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Cadical_Basic(uint8_t builtin);
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
res = runtime_initialize_Lean_Cadical_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__3___boxed__const__1 = _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__3___boxed__const__1();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__3___boxed__const__1);
l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__2___boxed__const__1 = _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__2___boxed__const__1();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__2___boxed__const__1);
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
lean_object* initialize_Lean_Cadical_Basic(uint8_t builtin);
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
res = initialize_Lean_Cadical_Basic(builtin);
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
