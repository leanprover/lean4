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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint32_t lean_bool_to_uint32(uint8_t);
uint32_t lean_int32_of_nat(lean_object*);
lean_object* lean_int32_to_int(uint32_t);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
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
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Failed to execute external prover:\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__7_value;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(size_t v_sz_146_, size_t v_i_147_, lean_object* v_bs_148_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_146_ = stack[0].m_num;
size_t v_i_147_ = stack[1].m_num;
lean_object* v_bs_148_ = stack[2].m_obj;
lean_object* v_res_162_;
v_res_162_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(v_sz_146_, v_i_147_, v_bs_148_);
stack->m_obj
 = v_res_162_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___boxed(lean_object* v_sz_163_, lean_object* v_i_164_, lean_object* v_bs_165_){
_start:
{
size_t v_sz_boxed_166_; size_t v_i_boxed_167_; lean_object* v_res_168_; 
v_sz_boxed_166_ = lean_unbox_usize(v_sz_163_);
lean_dec(v_sz_163_);
v_i_boxed_167_ = lean_unbox_usize(v_i_164_);
lean_dec(v_i_164_);
v_res_168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(v_sz_boxed_166_, v_i_boxed_167_, v_bs_165_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__1(lean_object* v_acc_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_pos_172_; lean_object* v_res_173_; lean_object* v_array_176_; lean_object* v_idx_177_; lean_object* v_pos_179_; lean_object* v_idx_180_; lean_object* v_err_181_; lean_object* v___x_189_; uint8_t v___x_190_; 
v_array_176_ = lean_ctor_get(v_a_170_, 0);
v_idx_177_ = lean_ctor_get(v_a_170_, 1);
lean_inc(v_idx_177_);
v___x_189_ = lean_byte_array_size(v_array_176_);
v___x_190_ = lean_nat_dec_lt(v_idx_177_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
v___x_191_ = lean_box(0);
lean_inc(v_idx_177_);
v_pos_179_ = v_a_170_;
v_idx_180_ = v_idx_177_;
v_err_181_ = v___x_191_;
goto v___jp_178_;
}
else
{
uint8_t v___x_192_; uint8_t v_got_193_; uint8_t v___x_194_; 
v___x_192_ = 32;
v_got_193_ = lean_byte_array_fget(v_array_176_, v_idx_177_);
v___x_194_ = lean_uint8_dec_eq(v_got_193_, v___x_192_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
v___x_195_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__1));
lean_inc(v_idx_177_);
v_pos_179_ = v_a_170_;
v_idx_180_ = v_idx_177_;
v_err_181_ = v___x_195_;
goto v___jp_178_;
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_nat_add(v_idx_177_, v___x_196_);
v___x_198_ = lean_nat_dec_lt(v___x_197_, v___x_189_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
lean_dec(v___x_197_);
v___x_199_ = lean_box(0);
lean_inc(v_idx_177_);
v_pos_179_ = v_a_170_;
v_idx_180_ = v_idx_177_;
v_err_181_ = v___x_199_;
goto v___jp_178_;
}
else
{
uint8_t v___x_200_; uint8_t v___x_201_; uint8_t v___x_202_; 
v___x_200_ = lean_byte_array_fget(v_array_176_, v___x_197_);
v___x_201_ = 45;
v___x_202_ = lean_uint8_dec_eq(v___x_200_, v___x_201_);
if (v___x_202_ == 0)
{
uint8_t v___x_203_; uint8_t v___x_204_; 
v___x_203_ = 48;
v___x_204_ = lean_uint8_dec_le(v___x_203_, v___x_200_);
if (v___x_204_ == 0)
{
lean_dec(v___x_197_);
goto v___jp_187_;
}
else
{
uint8_t v___x_205_; uint8_t v___x_206_; 
v___x_205_ = 57;
v___x_206_ = lean_uint8_dec_le(v___x_200_, v___x_205_);
if (v___x_206_ == 0)
{
lean_dec(v___x_197_);
goto v___jp_187_;
}
else
{
lean_object* v___x_207_; lean_object* v_it_x27_208_; uint32_t v___x_209_; uint8_t v___x_210_; uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v_fst_214_; lean_object* v_snd_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_207_ = lean_nat_add(v___x_197_, v___x_196_);
lean_dec(v___x_197_);
lean_inc_ref(v_array_176_);
v_it_x27_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_208_, 0, v_array_176_);
lean_ctor_set(v_it_x27_208_, 1, v___x_207_);
v___x_209_ = lean_uint8_to_uint32(v___x_200_);
v___x_210_ = lean_uint32_to_uint8(v___x_209_);
v___x_211_ = lean_uint8_sub(v___x_210_, v___x_203_);
v___x_212_ = lean_uint8_to_nat(v___x_211_);
v___x_213_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_208_, v___x_212_);
v_fst_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_fst_214_);
v_snd_215_ = lean_ctor_get(v___x_213_, 1);
lean_inc(v_snd_215_);
lean_dec_ref(v___x_213_);
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_nat_dec_eq(v_fst_214_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; 
lean_dec(v_idx_177_);
lean_dec_ref(v_a_170_);
v___x_218_ = lean_nat_to_int(v_fst_214_);
v_pos_172_ = v_snd_215_;
v_res_173_ = v___x_218_;
goto v___jp_171_;
}
else
{
lean_object* v___x_219_; 
lean_dec(v_snd_215_);
lean_dec(v_fst_214_);
v___x_219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5));
lean_inc(v_idx_177_);
v_pos_179_ = v_a_170_;
v_idx_180_ = v_idx_177_;
v_err_181_ = v___x_219_;
goto v___jp_178_;
}
}
}
}
else
{
lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_220_ = lean_nat_add(v___x_197_, v___x_196_);
lean_dec(v___x_197_);
v___x_221_ = lean_nat_dec_lt(v___x_220_, v___x_189_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; 
lean_dec(v___x_220_);
v___x_222_ = lean_box(0);
lean_inc(v_idx_177_);
v_pos_179_ = v_a_170_;
v_idx_180_ = v_idx_177_;
v_err_181_ = v___x_222_;
goto v___jp_178_;
}
else
{
uint8_t v_c_223_; uint8_t v___x_224_; uint8_t v___x_225_; 
v_c_223_ = lean_byte_array_fget(v_array_176_, v___x_220_);
v___x_224_ = 48;
v___x_225_ = lean_uint8_dec_le(v___x_224_, v_c_223_);
if (v___x_225_ == 0)
{
lean_dec(v___x_220_);
goto v___jp_185_;
}
else
{
uint8_t v___x_226_; uint8_t v___x_227_; 
v___x_226_ = 57;
v___x_227_ = lean_uint8_dec_le(v_c_223_, v___x_226_);
if (v___x_227_ == 0)
{
lean_dec(v___x_220_);
goto v___jp_185_;
}
else
{
lean_object* v___x_228_; lean_object* v_it_x27_229_; uint32_t v___x_230_; uint8_t v___x_231_; uint8_t v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v_fst_235_; lean_object* v_snd_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_228_ = lean_nat_add(v___x_220_, v___x_196_);
lean_dec(v___x_220_);
lean_inc_ref(v_array_176_);
v_it_x27_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_229_, 0, v_array_176_);
lean_ctor_set(v_it_x27_229_, 1, v___x_228_);
v___x_230_ = lean_uint8_to_uint32(v_c_223_);
v___x_231_ = lean_uint32_to_uint8(v___x_230_);
v___x_232_ = lean_uint8_sub(v___x_231_, v___x_224_);
v___x_233_ = lean_uint8_to_nat(v___x_232_);
v___x_234_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_229_, v___x_233_);
v_fst_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_fst_235_);
v_snd_236_ = lean_ctor_get(v___x_234_, 1);
lean_inc(v_snd_236_);
lean_dec_ref(v___x_234_);
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = lean_nat_dec_eq(v_fst_235_, v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec(v_idx_177_);
lean_dec_ref(v_a_170_);
v___x_239_ = lean_nat_to_int(v_fst_235_);
v___x_240_ = lean_int_neg(v___x_239_);
lean_dec(v___x_239_);
v_pos_172_ = v_snd_236_;
v_res_173_ = v___x_240_;
goto v___jp_171_;
}
else
{
lean_object* v___x_241_; 
lean_dec(v_snd_236_);
lean_dec(v_fst_235_);
v___x_241_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__5));
lean_inc(v_idx_177_);
v_pos_179_ = v_a_170_;
v_idx_180_ = v_idx_177_;
v_err_181_ = v___x_241_;
goto v___jp_178_;
}
}
}
}
}
}
}
}
v___jp_171_:
{
lean_object* v___x_174_; 
v___x_174_ = lean_array_push(v_acc_169_, v_res_173_);
v_acc_169_ = v___x_174_;
v_a_170_ = v_pos_172_;
goto _start;
}
v___jp_178_:
{
uint8_t v___x_182_; 
v___x_182_ = lean_nat_dec_eq(v_idx_177_, v_idx_180_);
lean_dec(v_idx_180_);
lean_dec(v_idx_177_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; 
lean_dec_ref(v_acc_169_);
lean_inc(v_err_181_);
v___x_183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_183_, 0, v_pos_179_);
lean_ctor_set(v___x_183_, 1, v_err_181_);
return v___x_183_;
}
else
{
lean_object* v___x_184_; 
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v_pos_179_);
lean_ctor_set(v___x_184_, 1, v_acc_169_);
return v___x_184_;
}
}
v___jp_185_:
{
lean_object* v___x_186_; 
v___x_186_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3));
lean_inc(v_idx_177_);
v_pos_179_ = v_a_170_;
v_idx_180_ = v_idx_177_;
v_err_181_ = v___x_186_;
goto v___jp_178_;
}
v___jp_187_:
{
lean_object* v___x_188_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit___closed__3));
lean_inc(v_idx_177_);
v_pos_179_ = v_a_170_;
v_idx_180_ = v_idx_177_;
v_err_181_ = v___x_188_;
goto v___jp_178_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4(void){
_start:
{
lean_object* v___x_248_; lean_object* v_utf8_249_; 
v___x_248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__3));
v_utf8_249_ = lean_string_to_utf8(v___x_248_);
return v_utf8_249_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6(void){
_start:
{
lean_object* v___x_251_; lean_object* v_utf8_252_; 
v___x_251_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__5));
v_utf8_252_ = lean_string_to_utf8(v___x_251_);
return v_utf8_252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment(lean_object* v_a_256_){
_start:
{
lean_object* v_array_257_; lean_object* v_idx_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v_array_257_ = lean_ctor_get(v_a_256_, 0);
v_idx_258_ = lean_ctor_get(v_a_256_, 1);
v___x_259_ = lean_byte_array_size(v_array_257_);
v___x_260_ = lean_nat_dec_lt(v_idx_258_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_262_, 0, v_a_256_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
return v___x_262_;
}
else
{
uint8_t v___x_263_; uint8_t v_got_264_; uint8_t v___x_265_; 
v___x_263_ = 118;
v_got_264_ = lean_byte_array_fget(v_array_257_, v_idx_258_);
v___x_265_ = lean_uint8_dec_eq(v_got_264_, v___x_263_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__1));
v___x_267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_267_, 0, v_a_256_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
return v___x_267_;
}
else
{
lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_369_; 
lean_inc(v_idx_258_);
lean_inc_ref(v_array_257_);
v_isSharedCheck_369_ = !lean_is_exclusive(v_a_256_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; lean_object* v_unused_371_; 
v_unused_370_ = lean_ctor_get(v_a_256_, 1);
lean_dec(v_unused_370_);
v_unused_371_ = lean_ctor_get(v_a_256_, 0);
lean_dec(v_unused_371_);
v___x_269_ = v_a_256_;
v_isShared_270_ = v_isSharedCheck_369_;
goto v_resetjp_268_;
}
else
{
lean_dec(v_a_256_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_369_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_271_ = lean_unsigned_to_nat(1u);
v___x_272_ = lean_nat_add(v_idx_258_, v___x_271_);
lean_dec(v_idx_258_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v___x_272_);
v___x_274_ = v___x_269_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_array_257_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v___x_272_);
v___x_274_ = v_reuseFailAlloc_368_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__2));
v___x_276_ = l_Std_Internal_Parsec_manyCore___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__1(v___x_275_, v___x_274_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_pos_277_; lean_object* v_res_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_358_; 
v_pos_277_ = lean_ctor_get(v___x_276_, 0);
v_res_278_ = lean_ctor_get(v___x_276_, 1);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_358_ == 0)
{
v___x_280_ = v___x_276_;
v_isShared_281_ = v_isSharedCheck_358_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_res_278_);
lean_inc(v_pos_277_);
lean_dec(v___x_276_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_358_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
size_t v_sz_282_; size_t v___x_283_; lean_object* v___x_284_; lean_object* v_pos_286_; lean_object* v_pos_293_; lean_object* v___y_299_; lean_object* v_utf8_310_; lean_object* v___x_311_; 
v_sz_282_ = lean_array_size(v_res_278_);
v___x_283_ = ((size_t)0ULL);
v___x_284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(v_sz_282_, v___x_283_, v_res_278_);
v_utf8_310_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__4);
lean_inc(v_pos_277_);
v___x_311_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_310_, v_pos_277_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_pos_312_; 
lean_dec(v_pos_277_);
v_pos_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_pos_312_);
lean_dec_ref_known(v___x_311_, 2);
v_pos_286_ = v_pos_312_;
goto v___jp_285_;
}
else
{
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_pos_313_; 
lean_dec(v_pos_277_);
v_pos_313_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_pos_313_);
lean_dec_ref_known(v___x_311_, 2);
v_pos_286_ = v_pos_313_;
goto v___jp_285_;
}
else
{
lean_object* v_pos_314_; lean_object* v_err_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_357_; 
lean_del_object(v___x_280_);
v_pos_314_ = lean_ctor_get(v___x_311_, 0);
v_err_315_ = lean_ctor_get(v___x_311_, 1);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_357_ == 0)
{
v___x_317_ = v___x_311_;
v_isShared_318_ = v_isSharedCheck_357_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_err_315_);
lean_inc(v_pos_314_);
lean_dec(v___x_311_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_357_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v_idx_319_; lean_object* v_array_320_; lean_object* v_idx_321_; lean_object* v___y_323_; lean_object* v_pos_324_; lean_object* v_idx_325_; uint8_t v___x_330_; 
v_idx_319_ = lean_ctor_get(v_pos_277_, 1);
lean_inc(v_idx_319_);
lean_dec(v_pos_277_);
v_array_320_ = lean_ctor_get(v_pos_314_, 0);
v_idx_321_ = lean_ctor_get(v_pos_314_, 1);
v___x_330_ = lean_nat_dec_eq(v_idx_319_, v_idx_321_);
lean_dec(v_idx_319_);
if (v___x_330_ == 0)
{
lean_object* v___x_332_; 
lean_dec_ref(v___x_284_);
if (v_isShared_318_ == 0)
{
v___x_332_ = v___x_317_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_pos_314_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_err_315_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
else
{
lean_object* v___x_334_; uint8_t v___x_335_; 
lean_inc(v_idx_321_);
lean_dec(v_err_315_);
v___x_334_ = lean_byte_array_size(v_array_320_);
v___x_335_ = lean_nat_dec_lt(v_idx_321_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = lean_box(0);
lean_inc(v_pos_314_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 1, v___x_336_);
v___x_338_ = v___x_317_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_pos_314_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_inc(v_idx_321_);
v___y_323_ = v___x_338_;
v_pos_324_ = v_pos_314_;
v_idx_325_ = v_idx_321_;
goto v___jp_322_;
}
}
else
{
uint8_t v___x_340_; uint8_t v_got_341_; uint8_t v___x_342_; 
v___x_340_ = 10;
v_got_341_ = lean_byte_array_fget(v_array_320_, v_idx_321_);
v___x_342_ = lean_uint8_dec_eq(v_got_341_, v___x_340_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_343_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8));
lean_inc(v_pos_314_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 1, v___x_343_);
v___x_345_ = v___x_317_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_pos_314_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_inc(v_idx_321_);
v___y_323_ = v___x_345_;
v_pos_324_ = v_pos_314_;
v_idx_325_ = v_idx_321_;
goto v___jp_322_;
}
}
else
{
lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_354_; 
lean_inc_ref(v_array_320_);
lean_del_object(v___x_317_);
v_isSharedCheck_354_ = !lean_is_exclusive(v_pos_314_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; lean_object* v_unused_356_; 
v_unused_355_ = lean_ctor_get(v_pos_314_, 1);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_pos_314_, 0);
lean_dec(v_unused_356_);
v___x_348_ = v_pos_314_;
v_isShared_349_ = v_isSharedCheck_354_;
goto v_resetjp_347_;
}
else
{
lean_dec(v_pos_314_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_354_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = lean_nat_add(v_idx_321_, v___x_271_);
lean_dec(v_idx_321_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 1, v___x_350_);
v___x_352_ = v___x_348_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_array_320_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
v_pos_293_ = v___x_352_;
goto v___jp_292_;
}
}
}
}
}
v___jp_322_:
{
uint8_t v___x_326_; 
v___x_326_ = lean_nat_dec_eq(v_idx_321_, v_idx_325_);
lean_dec(v_idx_325_);
lean_dec(v_idx_321_);
if (v___x_326_ == 0)
{
lean_dec_ref(v_pos_324_);
v___y_299_ = v___y_323_;
goto v___jp_298_;
}
else
{
lean_object* v_utf8_327_; lean_object* v___x_328_; 
lean_dec_ref(v___y_323_);
v_utf8_327_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6);
v___x_328_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_327_, v_pos_324_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_pos_329_; 
v_pos_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_pos_329_);
lean_dec_ref_known(v___x_328_, 2);
v_pos_293_ = v_pos_329_;
goto v___jp_292_;
}
else
{
v___y_299_ = v___x_328_;
goto v___jp_298_;
}
}
}
}
}
}
v___jp_285_:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_287_ = lean_box(v___x_265_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_284_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 1, v___x_288_);
lean_ctor_set(v___x_280_, 0, v_pos_286_);
v___x_290_ = v___x_280_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_pos_286_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v___x_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
v___jp_292_:
{
uint8_t v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_294_ = 0;
v___x_295_ = lean_box(v___x_294_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v___x_284_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v_pos_293_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
return v___x_297_;
}
v___jp_298_:
{
if (lean_obj_tag(v___y_299_) == 0)
{
lean_object* v_pos_300_; 
v_pos_300_ = lean_ctor_get(v___y_299_, 0);
lean_inc(v_pos_300_);
lean_dec_ref_known(v___y_299_, 2);
v_pos_293_ = v_pos_300_;
goto v___jp_292_;
}
else
{
lean_object* v_pos_301_; lean_object* v_err_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec_ref(v___x_284_);
v_pos_301_ = lean_ctor_get(v___y_299_, 0);
v_err_302_ = lean_ctor_get(v___y_299_, 1);
v_isSharedCheck_309_ = !lean_is_exclusive(v___y_299_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___y_299_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_err_302_);
lean_inc(v_pos_301_);
lean_dec(v___y_299_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_pos_301_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_err_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
}
else
{
lean_object* v_pos_359_; lean_object* v_err_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
v_pos_359_ = lean_ctor_get(v___x_276_, 0);
v_err_360_ = lean_ctor_get(v___x_276_, 1);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_276_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_err_360_);
lean_inc(v_pos_359_);
lean_dec(v___x_276_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_pos_359_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_err_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines_go(lean_object* v_acc_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment(v_a_373_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_res_375_; lean_object* v_pos_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_388_; 
v_res_375_ = lean_ctor_get(v___x_374_, 1);
v_pos_376_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_388_ == 0)
{
v___x_378_ = v___x_374_;
v_isShared_379_ = v_isSharedCheck_388_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_res_375_);
lean_inc(v_pos_376_);
lean_dec(v___x_374_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_388_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v_fst_380_; lean_object* v_snd_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v_fst_380_ = lean_ctor_get(v_res_375_, 0);
lean_inc(v_fst_380_);
v_snd_381_ = lean_ctor_get(v_res_375_, 1);
lean_inc(v_snd_381_);
lean_dec(v_res_375_);
v___x_382_ = l_Array_append___redArg(v_acc_372_, v_snd_381_);
lean_dec(v_snd_381_);
v___x_383_ = lean_unbox(v_fst_380_);
lean_dec(v_fst_380_);
if (v___x_383_ == 0)
{
lean_del_object(v___x_378_);
v_acc_372_ = v___x_382_;
v_a_373_ = v_pos_376_;
goto _start;
}
else
{
lean_object* v___x_386_; 
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 1, v___x_382_);
v___x_386_ = v___x_378_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_pos_376_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v___x_382_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
lean_object* v_pos_389_; lean_object* v_err_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec_ref(v_acc_372_);
v_pos_389_ = lean_ctor_get(v___x_374_, 0);
v_err_390_ = lean_ctor_get(v___x_374_, 1);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_374_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_err_390_);
lean_inc(v_pos_389_);
lean_dec(v___x_374_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_pos_389_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_err_390_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines(lean_object* v_a_400_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines___closed__0));
v___x_402_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines_go(v___x_401_, v_a_400_);
return v___x_402_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1(void){
_start:
{
lean_object* v___x_404_; lean_object* v_utf8_405_; 
v___x_404_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0));
v_utf8_405_ = lean_string_to_utf8(v___x_404_);
return v_utf8_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader(lean_object* v_a_406_){
_start:
{
lean_object* v_idx_408_; lean_object* v___y_409_; lean_object* v_pos_410_; lean_object* v_idx_411_; lean_object* v_pos_426_; lean_object* v_utf8_451_; lean_object* v___x_452_; 
v_utf8_451_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1);
v___x_452_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_451_, v_a_406_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_pos_453_; 
v_pos_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_pos_453_);
lean_dec_ref_known(v___x_452_, 2);
v_pos_426_ = v_pos_453_;
goto v___jp_425_;
}
else
{
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_pos_454_; 
v_pos_454_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_pos_454_);
lean_dec_ref_known(v___x_452_, 2);
v_pos_426_ = v_pos_454_;
goto v___jp_425_;
}
else
{
return v___x_452_;
}
}
v___jp_407_:
{
uint8_t v___x_412_; 
v___x_412_ = lean_nat_dec_eq(v_idx_408_, v_idx_411_);
lean_dec(v_idx_411_);
lean_dec(v_idx_408_);
if (v___x_412_ == 0)
{
lean_dec_ref(v_pos_410_);
return v___y_409_;
}
else
{
lean_object* v_utf8_413_; lean_object* v___x_414_; 
lean_dec_ref(v___y_409_);
v_utf8_413_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6);
v___x_414_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_413_, v_pos_410_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_pos_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_423_; 
v_pos_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v___x_414_, 1);
lean_dec(v_unused_424_);
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_pos_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_419_ = lean_box(0);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v___x_419_);
v___x_421_ = v___x_417_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_pos_415_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
else
{
return v___x_414_;
}
}
}
v___jp_425_:
{
lean_object* v_array_427_; lean_object* v_idx_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v_array_427_ = lean_ctor_get(v_pos_426_, 0);
v_idx_428_ = lean_ctor_get(v_pos_426_, 1);
lean_inc(v_idx_428_);
v___x_429_ = lean_byte_array_size(v_array_427_);
v___x_430_ = lean_nat_dec_lt(v_idx_428_, v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_box(0);
lean_inc_ref(v_pos_426_);
v___x_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_432_, 0, v_pos_426_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
lean_inc(v_idx_428_);
v_idx_408_ = v_idx_428_;
v___y_409_ = v___x_432_;
v_pos_410_ = v_pos_426_;
v_idx_411_ = v_idx_428_;
goto v___jp_407_;
}
else
{
uint8_t v___x_433_; uint8_t v_got_434_; uint8_t v___x_435_; 
v___x_433_ = 10;
v_got_434_ = lean_byte_array_fget(v_array_427_, v_idx_428_);
v___x_435_ = lean_uint8_dec_eq(v_got_434_, v___x_433_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8));
lean_inc_ref(v_pos_426_);
v___x_437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_437_, 0, v_pos_426_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
lean_inc(v_idx_428_);
v_idx_408_ = v_idx_428_;
v___y_409_ = v___x_437_;
v_pos_410_ = v_pos_426_;
v_idx_411_ = v_idx_428_;
goto v___jp_407_;
}
else
{
lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_448_; 
lean_inc_ref(v_array_427_);
v_isSharedCheck_448_ = !lean_is_exclusive(v_pos_426_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; lean_object* v_unused_450_; 
v_unused_449_ = lean_ctor_get(v_pos_426_, 1);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_pos_426_, 0);
lean_dec(v_unused_450_);
v___x_439_ = v_pos_426_;
v_isShared_440_ = v_isSharedCheck_448_;
goto v_resetjp_438_;
}
else
{
lean_dec(v_pos_426_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_448_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_441_ = lean_unsigned_to_nat(1u);
v___x_442_ = lean_nat_add(v_idx_428_, v___x_441_);
lean_dec(v_idx_428_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___x_442_);
v___x_444_ = v___x_439_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_array_427_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v___x_442_);
v___x_444_ = v_reuseFailAlloc_447_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_box(0);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_444_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
return v___x_446_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parse(lean_object* v_a_455_){
_start:
{
lean_object* v___y_457_; lean_object* v_idx_470_; lean_object* v___y_471_; lean_object* v_pos_472_; lean_object* v_idx_473_; lean_object* v_pos_480_; lean_object* v_utf8_504_; lean_object* v___x_505_; 
v_utf8_504_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__1);
v___x_505_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_504_, v_a_455_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_pos_506_; 
v_pos_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_pos_506_);
lean_dec_ref_known(v___x_505_, 2);
v_pos_480_ = v_pos_506_;
goto v___jp_479_;
}
else
{
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_pos_507_; 
v_pos_507_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_pos_507_);
lean_dec_ref_known(v___x_505_, 2);
v_pos_480_ = v_pos_507_;
goto v___jp_479_;
}
else
{
v___y_457_ = v___x_505_;
goto v___jp_456_;
}
}
v___jp_456_:
{
if (lean_obj_tag(v___y_457_) == 0)
{
lean_object* v_pos_458_; lean_object* v___x_459_; 
v_pos_458_ = lean_ctor_get(v___y_457_, 0);
lean_inc(v_pos_458_);
lean_dec_ref_known(v___y_457_, 2);
v___x_459_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines(v_pos_458_);
return v___x_459_;
}
else
{
lean_object* v_pos_460_; lean_object* v_err_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
v_pos_460_ = lean_ctor_get(v___y_457_, 0);
v_err_461_ = lean_ctor_get(v___y_457_, 1);
v_isSharedCheck_468_ = !lean_is_exclusive(v___y_457_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___y_457_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_err_461_);
lean_inc(v_pos_460_);
lean_dec(v___y_457_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_pos_460_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_err_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
v___jp_469_:
{
uint8_t v___x_474_; 
v___x_474_ = lean_nat_dec_eq(v_idx_470_, v_idx_473_);
lean_dec(v_idx_473_);
lean_dec(v_idx_470_);
if (v___x_474_ == 0)
{
lean_dec_ref(v_pos_472_);
v___y_457_ = v___y_471_;
goto v___jp_456_;
}
else
{
lean_object* v_utf8_475_; lean_object* v___x_476_; 
lean_dec_ref(v___y_471_);
v_utf8_475_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__6);
v___x_476_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_475_, v_pos_472_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_pos_477_; lean_object* v___x_478_; 
v_pos_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_pos_477_);
lean_dec_ref_known(v___x_476_, 2);
v___x_478_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines(v_pos_477_);
return v___x_478_;
}
else
{
v___y_457_ = v___x_476_;
goto v___jp_456_;
}
}
}
v___jp_479_:
{
lean_object* v_array_481_; lean_object* v_idx_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_array_481_ = lean_ctor_get(v_pos_480_, 0);
v_idx_482_ = lean_ctor_get(v_pos_480_, 1);
lean_inc(v_idx_482_);
v___x_483_ = lean_byte_array_size(v_array_481_);
v___x_484_ = lean_nat_dec_lt(v_idx_482_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_box(0);
lean_inc_ref(v_pos_480_);
v___x_486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_486_, 0, v_pos_480_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
lean_inc(v_idx_482_);
v_idx_470_ = v_idx_482_;
v___y_471_ = v___x_486_;
v_pos_472_ = v_pos_480_;
v_idx_473_ = v_idx_482_;
goto v___jp_469_;
}
else
{
uint8_t v___x_487_; uint8_t v_got_488_; uint8_t v___x_489_; 
v___x_487_ = 10;
v_got_488_ = lean_byte_array_fget(v_array_481_, v_idx_482_);
v___x_489_ = lean_uint8_dec_eq(v_got_488_, v___x_487_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parsePartialAssignment___closed__8));
lean_inc_ref(v_pos_480_);
v___x_491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_491_, 0, v_pos_480_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
lean_inc(v_idx_482_);
v_idx_470_ = v_idx_482_;
v___y_471_ = v___x_491_;
v_pos_472_ = v_pos_480_;
v_idx_473_ = v_idx_482_;
goto v___jp_469_;
}
else
{
lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_501_; 
lean_inc_ref(v_array_481_);
v_isSharedCheck_501_ = !lean_is_exclusive(v_pos_480_);
if (v_isSharedCheck_501_ == 0)
{
lean_object* v_unused_502_; lean_object* v_unused_503_; 
v_unused_502_ = lean_ctor_get(v_pos_480_, 1);
lean_dec(v_unused_502_);
v_unused_503_ = lean_ctor_get(v_pos_480_, 0);
lean_dec(v_unused_503_);
v___x_493_ = v_pos_480_;
v_isShared_494_ = v_isSharedCheck_501_;
goto v_resetjp_492_;
}
else
{
lean_dec(v_pos_480_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_501_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_495_ = lean_unsigned_to_nat(1u);
v___x_496_ = lean_nat_add(v_idx_482_, v___x_495_);
lean_dec(v_idx_482_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_496_);
v___x_498_ = v___x_493_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_array_481_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v___x_496_);
v___x_498_ = v_reuseFailAlloc_500_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_499_; 
v___x_499_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseLines(v___x_498_);
return v___x_499_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___impl___redArg(lean_object* v_x_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = lean_obj_tag_nat(v_x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___impl___redArg___boxed(lean_object* v_x_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___impl___redArg(v_x_510_);
lean_dec(v_x_510_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___impl(lean_object* v_00_u03b1_512_, lean_object* v_x_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = lean_obj_tag_nat(v_x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___impl___boxed(lean_object* v_00_u03b1_515_, lean_object* v_x_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorIdx___impl(v_00_u03b1_515_, v_x_516_);
lean_dec(v_x_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(lean_object* v_t_518_, lean_object* v_k_519_){
_start:
{
if (lean_obj_tag(v_t_518_) == 0)
{
lean_object* v_x_520_; lean_object* v___x_521_; 
v_x_520_ = lean_ctor_get(v_t_518_, 0);
lean_inc(v_x_520_);
lean_dec_ref_known(v_t_518_, 1);
v___x_521_ = lean_apply_1(v_k_519_, v_x_520_);
return v___x_521_;
}
else
{
return v_k_519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim(lean_object* v_00_u03b1_522_, lean_object* v_motive_523_, lean_object* v_ctorIdx_524_, lean_object* v_t_525_, lean_object* v_h_526_, lean_object* v_k_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_525_, v_k_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___boxed(lean_object* v_00_u03b1_529_, lean_object* v_motive_530_, lean_object* v_ctorIdx_531_, lean_object* v_t_532_, lean_object* v_h_533_, lean_object* v_k_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim(v_00_u03b1_529_, v_motive_530_, v_ctorIdx_531_, v_t_532_, v_h_533_, v_k_534_);
lean_dec(v_ctorIdx_531_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_success_elim___redArg(lean_object* v_t_536_, lean_object* v_success_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_536_, v_success_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_success_elim(lean_object* v_00_u03b1_539_, lean_object* v_motive_540_, lean_object* v_t_541_, lean_object* v_h_542_, lean_object* v_success_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_541_, v_success_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_timeout_elim___redArg(lean_object* v_t_545_, lean_object* v_timeout_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_545_, v_timeout_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_TimedOut_timeout_elim(lean_object* v_00_u03b1_548_, lean_object* v_motive_549_, lean_object* v_t_550_, lean_object* v_h_551_, lean_object* v_timeout_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Meta_Tactic_BVDecide_External_TimedOut_ctorElim___redArg(v_t_550_, v_timeout_552_);
return v___x_553_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_box(0);
v___x_555_ = l_Lean_interruptExceptionId;
v___x_556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set(v___x_556_, 1, v___x_554_);
return v___x_556_;
}
}
lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg(){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___closed__0);
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_560_;
v_res_560_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg();
stack->m_obj
 = v_res_560_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg___boxed(lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg();
return v_res_562_;
}
}
lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0(lean_object* v_00_u03b1_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg();
return v___x_567_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_564_ = stack[1].m_obj;
lean_object* v___y_565_ = stack[2].m_obj;
lean_object* v_res_568_;
v_res_568_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0(lean_box(0), v___y_564_, v___y_565_);
stack->m_obj
 = v_res_568_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___boxed(lean_object* v_00_u03b1_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0(v_00_u03b1_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
return v_res_573_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(lean_object* v_cleanup_574_, lean_object* v_x_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_toCold_579_; lean_object* v_cancelTk_x3f_580_; 
v_toCold_579_ = lean_ctor_get(v_a_576_, 0);
v_cancelTk_x3f_580_ = lean_ctor_get(v_toCold_579_, 10);
if (lean_obj_tag(v_cancelTk_x3f_580_) == 1)
{
lean_object* v_val_581_; uint8_t v___x_582_; 
v_val_581_ = lean_ctor_get(v_cancelTk_x3f_580_, 0);
v___x_582_ = l_IO_CancelToken_isSet(v_val_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
lean_dec_ref(v_cleanup_574_);
lean_inc(v_a_577_);
lean_inc_ref(v_a_576_);
v___x_583_ = lean_apply_3(v_x_575_, v_a_576_, v_a_577_, lean_box(0));
return v___x_583_;
}
else
{
lean_object* v___x_584_; 
lean_dec_ref(v_x_575_);
lean_inc(v_a_577_);
lean_inc_ref(v_a_576_);
v___x_584_ = lean_apply_3(v_cleanup_574_, v_a_576_, v_a_577_, lean_box(0));
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v___x_585_; lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec_ref_known(v___x_584_, 1);
v___x_585_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg();
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
v_a_594_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_584_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_584_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
else
{
lean_object* v___x_602_; 
lean_dec_ref(v_cleanup_574_);
lean_inc(v_a_577_);
lean_inc_ref(v_a_576_);
v___x_602_ = lean_apply_3(v_x_575_, v_a_576_, v_a_577_, lean_box(0));
return v___x_602_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cleanup_574_ = stack[0].m_obj;
lean_object* v_x_575_ = stack[1].m_obj;
lean_object* v_a_576_ = stack[2].m_obj;
lean_object* v_a_577_ = stack[3].m_obj;
lean_object* v_res_603_;
v_res_603_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(v_cleanup_574_, v_x_575_, v_a_576_, v_a_577_);
stack->m_obj
 = v_res_603_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg___boxed(lean_object* v_cleanup_604_, lean_object* v_x_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(v_cleanup_604_, v_x_605_, v_a_606_, v_a_607_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
return v_res_609_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck(lean_object* v_00_u03b1_610_, lean_object* v_cleanup_611_, lean_object* v_x_612_, lean_object* v_a_613_, lean_object* v_a_614_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(v_cleanup_611_, v_x_612_, v_a_613_, v_a_614_);
return v___x_616_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_0interp(lean_interpreter_value* stack)
{
lean_object* v_cleanup_611_ = stack[1].m_obj;
lean_object* v_x_612_ = stack[2].m_obj;
lean_object* v_a_613_ = stack[3].m_obj;
lean_object* v_a_614_ = stack[4].m_obj;
lean_object* v_res_617_;
v_res_617_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck(lean_box(0), v_cleanup_611_, v_x_612_, v_a_613_, v_a_614_);
stack->m_obj
 = v_res_617_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___boxed(lean_object* v_00_u03b1_618_, lean_object* v_cleanup_619_, lean_object* v_x_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck(v_00_u03b1_618_, v_cleanup_619_, v_x_620_, v_a_621_, v_a_622_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
return v_res_624_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(lean_object* v_budgetMs_625_, lean_object* v_cleanup_626_, lean_object* v_x_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = lean_unsigned_to_nat(0u);
v___x_632_ = lean_nat_dec_eq(v_budgetMs_625_, v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
lean_dec_ref(v_cleanup_626_);
lean_inc(v_a_629_);
lean_inc_ref(v_a_628_);
v___x_633_ = lean_apply_3(v_x_627_, v_a_628_, v_a_629_, lean_box(0));
return v___x_633_;
}
else
{
lean_object* v___x_634_; 
lean_dec_ref(v_x_627_);
lean_inc(v_a_629_);
lean_inc_ref(v_a_628_);
v___x_634_ = lean_apply_3(v_cleanup_626_, v_a_628_, v_a_629_, lean_box(0));
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_642_; 
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; 
v_unused_643_ = lean_ctor_get(v___x_634_, 0);
lean_dec(v_unused_643_);
v___x_636_ = v___x_634_;
v_isShared_637_ = v_isSharedCheck_642_;
goto v_resetjp_635_;
}
else
{
lean_dec(v___x_634_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_642_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_638_ = lean_box(1);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_638_);
v___x_640_ = v___x_636_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
v_a_644_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_634_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_634_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_budgetMs_625_ = stack[0].m_obj;
lean_object* v_cleanup_626_ = stack[1].m_obj;
lean_object* v_x_627_ = stack[2].m_obj;
lean_object* v_a_628_ = stack[3].m_obj;
lean_object* v_a_629_ = stack[4].m_obj;
lean_object* v_res_652_;
v_res_652_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(v_budgetMs_625_, v_cleanup_626_, v_x_627_, v_a_628_, v_a_629_);
stack->m_obj
 = v_res_652_;
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
lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck(lean_object* v_00_u03b1_660_, lean_object* v_budgetMs_661_, lean_object* v_cleanup_662_, lean_object* v_x_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(v_budgetMs_661_, v_cleanup_662_, v_x_663_, v_a_664_, v_a_665_);
return v___x_667_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck_0interp(lean_interpreter_value* stack)
{
lean_object* v_budgetMs_661_ = stack[1].m_obj;
lean_object* v_cleanup_662_ = stack[2].m_obj;
lean_object* v_x_663_ = stack[3].m_obj;
lean_object* v_a_664_ = stack[4].m_obj;
lean_object* v_a_665_ = stack[5].m_obj;
lean_object* v_res_668_;
v_res_668_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck(lean_box(0), v_budgetMs_661_, v_cleanup_662_, v_x_663_, v_a_664_, v_a_665_);
stack->m_obj
 = v_res_668_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___boxed(lean_object* v_00_u03b1_669_, lean_object* v_budgetMs_670_, lean_object* v_cleanup_671_, lean_object* v_x_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck(v_00_u03b1_669_, v_budgetMs_670_, v_cleanup_671_, v_x_672_, v_a_673_, v_a_674_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_budgetMs_670_);
return v_res_676_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait(lean_object* v_cfg_677_, lean_object* v_child_678_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = lean_io_process_child_kill(v_cfg_677_, v_child_678_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; 
lean_dec_ref_known(v___x_680_, 1);
v___x_681_ = lean_box(0);
v___x_682_ = lean_io_process_child_wait(v_cfg_677_, v_child_678_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; 
v_unused_690_ = lean_ctor_get(v___x_682_, 0);
lean_dec(v_unused_690_);
v___x_684_ = v___x_682_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_dec(v___x_682_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_681_);
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_681_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
v_a_691_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_682_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_682_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
else
{
return v___x_680_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_677_ = stack[0].m_obj;
lean_object* v_child_678_ = stack[1].m_obj;
lean_object* v_res_699_;
v_res_699_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait(v_cfg_677_, v_child_678_);
stack->m_obj
 = v_res_699_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait___boxed(lean_object* v_cfg_700_, lean_object* v_child_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait(v_cfg_700_, v_child_701_);
lean_dec_ref(v_child_701_);
lean_dec_ref(v_cfg_700_);
return v_res_703_;
}
}
lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(lean_object* v_e_704_){
_start:
{
if (lean_obj_tag(v_e_704_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_715_; 
v_a_706_ = lean_ctor_get(v_e_704_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v_e_704_);
if (v_isSharedCheck_715_ == 0)
{
v___x_708_ = v_e_704_;
v_isShared_709_ = v_isSharedCheck_715_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v_e_704_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_715_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_710_ = lean_io_error_to_string(v_a_706_);
v___x_711_ = lean_mk_io_user_error(v___x_710_);
if (v_isShared_709_ == 0)
{
lean_ctor_set_tag(v___x_708_, 1);
lean_ctor_set(v___x_708_, 0, v___x_711_);
v___x_713_ = v___x_708_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
v_a_716_ = lean_ctor_get(v_e_704_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v_e_704_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v_e_704_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v_e_704_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set_tag(v___x_718_, 0);
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_704_ = stack[0].m_obj;
lean_object* v_res_724_;
v_res_724_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v_e_704_);
stack->m_obj
 = v_res_724_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg___boxed(lean_object* v_e_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v_e_725_);
return v_res_727_;
}
}
lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0(lean_object* v_00_u03b1_728_, lean_object* v_e_729_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v_e_729_);
return v___x_731_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_729_ = stack[1].m_obj;
lean_object* v_res_732_;
v_res_732_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0(lean_box(0), v_e_729_);
stack->m_obj
 = v_res_732_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___boxed(lean_object* v_00_u03b1_733_, lean_object* v_e_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0(v_00_u03b1_733_, v_e_734_);
return v_res_736_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1(lean_object* v_cfg_737_, lean_object* v_child_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_ref_742_; lean_object* v___x_743_; 
v_ref_742_ = lean_ctor_get(v___y_739_, 2);
v___x_743_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_killAndWait(v_cfg_737_, v_child_738_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_763_; 
v_a_752_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_763_ == 0)
{
v___x_754_ = v___x_743_;
v_isShared_755_ = v_isSharedCheck_763_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_743_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_763_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_756_ = lean_io_error_to_string(v_a_752_);
v___x_757_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
v___x_758_ = l_Lean_MessageData_ofFormat(v___x_757_);
lean_inc(v_ref_742_);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v_ref_742_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_759_);
v___x_761_ = v___x_754_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_737_ = stack[0].m_obj;
lean_object* v_child_738_ = stack[1].m_obj;
lean_object* v___y_739_ = stack[2].m_obj;
lean_object* v___y_740_ = stack[3].m_obj;
lean_object* v_res_764_;
v_res_764_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1(v_cfg_737_, v_child_738_, v___y_739_, v___y_740_);
stack->m_obj
 = v_res_764_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1___boxed(lean_object* v_cfg_765_, lean_object* v_child_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1(v_cfg_765_, v_child_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec_ref(v_child_766_);
lean_dec_ref(v_cfg_765_);
return v_res_770_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0(lean_object* v_cfg_771_, lean_object* v_child_772_, lean_object* v_sleepMs_773_, lean_object* v_budgetMs_774_, lean_object* v_maxSleepMs_775_, lean_object* v_stdout_776_, lean_object* v_stderr_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_ref_781_; lean_object* v___x_782_; 
v_ref_781_ = lean_ctor_get(v___y_778_, 2);
v___x_782_ = lean_io_process_child_try_wait(v_cfg_771_, v_child_772_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_782_, 1);
if (lean_obj_tag(v_a_783_) == 0)
{
uint32_t v___x_784_; lean_object* v___x_785_; lean_object* v___y_787_; uint8_t v___x_790_; 
v___x_784_ = lean_uint32_of_nat(v_sleepMs_773_);
v___x_785_ = l_IO_sleep(v___x_784_);
v___x_790_ = lean_nat_dec_le(v_maxSleepMs_775_, v_sleepMs_773_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_unsigned_to_nat(2u);
v___x_792_ = lean_nat_mul(v_sleepMs_773_, v___x_791_);
v___y_787_ = v___x_792_;
goto v___jp_786_;
}
else
{
lean_inc(v_sleepMs_773_);
v___y_787_ = v_sleepMs_773_;
goto v___jp_786_;
}
v___jp_786_:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_nat_sub(v_budgetMs_774_, v_sleepMs_773_);
lean_dec(v_sleepMs_773_);
v___x_789_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(v_cfg_771_, v___x_788_, v___y_787_, v_maxSleepMs_775_, v_child_772_, v_stdout_776_, v_stderr_777_, v___y_778_, v___y_779_);
return v___x_789_;
}
}
else
{
lean_object* v_val_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_843_; 
lean_dec(v_maxSleepMs_775_);
lean_dec(v_sleepMs_773_);
lean_dec_ref(v_child_772_);
lean_dec_ref(v_cfg_771_);
v_val_793_ = lean_ctor_get(v_a_783_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v_a_783_);
if (v_isSharedCheck_843_ == 0)
{
v___x_795_ = v_a_783_;
v_isShared_796_ = v_isSharedCheck_843_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_val_793_);
lean_dec(v_a_783_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_843_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_task_get_own(v_stdout_776_);
v___x_798_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v___x_797_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
v___x_800_ = lean_task_get_own(v_stderr_777_);
v___x_801_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_spec__0___redArg(v___x_800_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_814_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_814_ == 0)
{
v___x_804_ = v___x_801_;
v_isShared_805_ = v_isSharedCheck_814_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_814_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; uint32_t v___x_807_; lean_object* v___x_809_; 
v___x_806_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_806_, 0, v_a_799_);
lean_ctor_set(v___x_806_, 1, v_a_802_);
v___x_807_ = lean_unbox_uint32(v_val_793_);
lean_dec(v_val_793_);
lean_ctor_set_uint32(v___x_806_, sizeof(void*)*2, v___x_807_);
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 0);
lean_ctor_set(v___x_795_, 0, v___x_806_);
v___x_809_ = v___x_795_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_806_);
v___x_809_ = v_reuseFailAlloc_813_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_811_; 
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_809_);
v___x_811_ = v___x_804_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_828_; 
lean_dec(v_a_799_);
lean_dec(v_val_793_);
v_a_815_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_828_ == 0)
{
v___x_817_ = v___x_801_;
v_isShared_818_ = v_isSharedCheck_828_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_801_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_828_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_819_ = lean_io_error_to_string(v_a_815_);
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 3);
lean_ctor_set(v___x_795_, 0, v___x_819_);
v___x_821_ = v___x_795_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_827_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_822_ = l_Lean_MessageData_ofFormat(v___x_821_);
lean_inc(v_ref_781_);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v_ref_781_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_823_);
v___x_825_ = v___x_817_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_842_; 
lean_dec(v_val_793_);
lean_dec_ref(v_stderr_777_);
v_a_829_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_842_ == 0)
{
v___x_831_ = v___x_798_;
v_isShared_832_ = v_isSharedCheck_842_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_798_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_842_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_833_ = lean_io_error_to_string(v_a_829_);
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 3);
lean_ctor_set(v___x_795_, 0, v___x_833_);
v___x_835_ = v___x_795_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_841_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_836_ = l_Lean_MessageData_ofFormat(v___x_835_);
lean_inc(v_ref_781_);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v_ref_781_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_837_);
v___x_839_ = v___x_831_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_855_; 
lean_dec_ref(v_stderr_777_);
lean_dec_ref(v_stdout_776_);
lean_dec(v_maxSleepMs_775_);
lean_dec(v_sleepMs_773_);
lean_dec_ref(v_child_772_);
lean_dec_ref(v_cfg_771_);
v_a_844_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_855_ == 0)
{
v___x_846_ = v___x_782_;
v_isShared_847_ = v_isSharedCheck_855_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_782_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_855_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_848_ = lean_io_error_to_string(v_a_844_);
v___x_849_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
v___x_850_ = l_Lean_MessageData_ofFormat(v___x_849_);
lean_inc(v_ref_781_);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v_ref_781_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_851_);
v___x_853_ = v___x_846_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_771_ = stack[0].m_obj;
lean_object* v_child_772_ = stack[1].m_obj;
lean_object* v_sleepMs_773_ = stack[2].m_obj;
lean_object* v_budgetMs_774_ = stack[3].m_obj;
lean_object* v_maxSleepMs_775_ = stack[4].m_obj;
lean_object* v_stdout_776_ = stack[5].m_obj;
lean_object* v_stderr_777_ = stack[6].m_obj;
lean_object* v___y_778_ = stack[7].m_obj;
lean_object* v___y_779_ = stack[8].m_obj;
lean_object* v_res_856_;
v_res_856_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0(v_cfg_771_, v_child_772_, v_sleepMs_773_, v_budgetMs_774_, v_maxSleepMs_775_, v_stdout_776_, v_stderr_777_, v___y_778_, v___y_779_);
stack->m_obj
 = v_res_856_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0___boxed(lean_object* v_cfg_857_, lean_object* v_child_858_, lean_object* v_sleepMs_859_, lean_object* v_budgetMs_860_, lean_object* v_maxSleepMs_861_, lean_object* v_stdout_862_, lean_object* v_stderr_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0(v_cfg_857_, v_child_858_, v_sleepMs_859_, v_budgetMs_860_, v_maxSleepMs_861_, v_stdout_862_, v_stderr_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v_budgetMs_860_);
return v_res_867_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(lean_object* v_cfg_868_, lean_object* v_budgetMs_869_, lean_object* v_sleepMs_870_, lean_object* v_maxSleepMs_871_, lean_object* v_child_872_, lean_object* v_stdout_873_, lean_object* v_stderr_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v___f_878_; lean_object* v___f_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
lean_inc(v_budgetMs_869_);
lean_inc_ref(v_child_872_);
lean_inc_ref(v_cfg_868_);
v___f_878_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__0___boxed), 10, 7);
lean_closure_set(v___f_878_, 0, v_cfg_868_);
lean_closure_set(v___f_878_, 1, v_child_872_);
lean_closure_set(v___f_878_, 2, v_sleepMs_870_);
lean_closure_set(v___f_878_, 3, v_budgetMs_869_);
lean_closure_set(v___f_878_, 4, v_maxSleepMs_871_);
lean_closure_set(v___f_878_, 5, v_stdout_873_);
lean_closure_set(v___f_878_, 6, v_stderr_874_);
v___f_879_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___lam__1___boxed), 5, 2);
lean_closure_set(v___f_879_, 0, v_cfg_868_);
lean_closure_set(v___f_879_, 1, v_child_872_);
lean_inc_ref(v___f_879_);
v___x_880_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___boxed), 6, 3);
lean_closure_set(v___x_880_, 0, lean_box(0));
lean_closure_set(v___x_880_, 1, v___f_879_);
lean_closure_set(v___x_880_, 2, v___f_878_);
v___x_881_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(v_budgetMs_869_, v___f_879_, v___x_880_, v_a_875_, v_a_876_);
lean_dec(v_budgetMs_869_);
return v___x_881_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_868_ = stack[0].m_obj;
lean_object* v_budgetMs_869_ = stack[1].m_obj;
lean_object* v_sleepMs_870_ = stack[2].m_obj;
lean_object* v_maxSleepMs_871_ = stack[3].m_obj;
lean_object* v_child_872_ = stack[4].m_obj;
lean_object* v_stdout_873_ = stack[5].m_obj;
lean_object* v_stderr_874_ = stack[6].m_obj;
lean_object* v_a_875_ = stack[7].m_obj;
lean_object* v_a_876_ = stack[8].m_obj;
lean_object* v_res_882_;
v_res_882_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(v_cfg_868_, v_budgetMs_869_, v_sleepMs_870_, v_maxSleepMs_871_, v_child_872_, v_stdout_873_, v_stderr_874_, v_a_875_, v_a_876_);
stack->m_obj
 = v_res_882_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go___boxed(lean_object* v_cfg_883_, lean_object* v_budgetMs_884_, lean_object* v_sleepMs_885_, lean_object* v_maxSleepMs_886_, lean_object* v_child_887_, lean_object* v_stdout_888_, lean_object* v_stderr_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(v_cfg_883_, v_budgetMs_884_, v_sleepMs_885_, v_maxSleepMs_886_, v_child_887_, v_stdout_888_, v_stderr_889_, v_a_890_, v_a_891_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
return v_res_893_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0(lean_object* v_stderr_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_IO_FS_Handle_readToEnd(v_stderr_894_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
lean_ctor_set_tag(v___x_899_, 1);
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
v_a_905_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_896_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_896_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set_tag(v___x_907_, 0);
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stderr_894_ = stack[0].m_obj;
lean_object* v_res_913_;
v_res_913_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0(v_stderr_894_);
stack->m_obj
 = v_res_913_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0___boxed(lean_object* v_stderr_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0(v_stderr_914_);
lean_dec(v_stderr_914_);
return v_res_916_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1(lean_object* v_stdout_917_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_IO_FS_Handle_readToEnd(v_stdout_917_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
lean_ctor_set_tag(v___x_922_, 1);
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
v_a_928_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_919_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_919_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set_tag(v___x_930_, 0);
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_stdout_917_ = stack[0].m_obj;
lean_object* v_res_936_;
v_res_936_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1(v_stdout_917_);
stack->m_obj
 = v_res_936_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1___boxed(lean_object* v_stdout_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1(v_stdout_937_);
lean_dec(v_stdout_937_);
return v_res_939_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible(lean_object* v_timeout_943_, lean_object* v_args_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_948_; lean_object* v_cmd_949_; lean_object* v_args_950_; lean_object* v_cwd_951_; lean_object* v_env_952_; uint8_t v_inheritEnv_953_; uint8_t v_setsid_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_988_; 
v___x_948_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___closed__0));
v_cmd_949_ = lean_ctor_get(v_args_944_, 1);
v_args_950_ = lean_ctor_get(v_args_944_, 2);
v_cwd_951_ = lean_ctor_get(v_args_944_, 3);
v_env_952_ = lean_ctor_get(v_args_944_, 4);
v_inheritEnv_953_ = lean_ctor_get_uint8(v_args_944_, sizeof(void*)*5);
v_setsid_954_ = lean_ctor_get_uint8(v_args_944_, sizeof(void*)*5 + 1);
v_isSharedCheck_988_ = !lean_is_exclusive(v_args_944_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; 
v_unused_989_ = lean_ctor_get(v_args_944_, 0);
lean_dec(v_unused_989_);
v___x_956_ = v_args_944_;
v_isShared_957_ = v_isSharedCheck_988_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_env_952_);
lean_inc(v_cwd_951_);
lean_inc(v_args_950_);
lean_inc(v_cmd_949_);
lean_dec(v_args_944_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_988_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v_ref_958_; lean_object* v___x_960_; 
v_ref_958_ = lean_ctor_get(v_a_945_, 2);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_948_);
v___x_960_ = v___x_956_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_cmd_949_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_args_950_);
lean_ctor_set(v_reuseFailAlloc_987_, 3, v_cwd_951_);
lean_ctor_set(v_reuseFailAlloc_987_, 4, v_env_952_);
lean_ctor_set_uint8(v_reuseFailAlloc_987_, sizeof(void*)*5, v_inheritEnv_953_);
lean_ctor_set_uint8(v_reuseFailAlloc_987_, sizeof(void*)*5 + 1, v_setsid_954_);
v___x_960_ = v_reuseFailAlloc_987_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_961_; 
v___x_961_ = lean_io_process_spawn(v___x_960_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v_stdout_963_; lean_object* v_stderr_964_; lean_object* v___f_965_; lean_object* v___f_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v___x_961_, 1);
v_stdout_963_ = lean_ctor_get(v_a_962_, 1);
v_stderr_964_ = lean_ctor_get(v_a_962_, 2);
lean_inc(v_stderr_964_);
v___f_965_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__0___boxed), 2, 1);
lean_closure_set(v___f_965_, 0, v_stderr_964_);
lean_inc(v_stdout_963_);
v___f_966_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___lam__1___boxed), 2, 1);
lean_closure_set(v___f_966_, 0, v_stdout_963_);
v___x_967_ = lean_unsigned_to_nat(9u);
v___x_968_ = lean_io_as_task(v___f_966_, v___x_967_);
v___x_969_ = lean_io_as_task(v___f_965_, v___x_967_);
v___x_970_ = lean_unsigned_to_nat(1000u);
v___x_971_ = lean_nat_mul(v_timeout_943_, v___x_970_);
v___x_972_ = lean_unsigned_to_nat(1u);
v___x_973_ = lean_unsigned_to_nat(64u);
v___x_974_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_runInterruptible_go(v___x_948_, v___x_971_, v___x_972_, v___x_973_, v_a_962_, v___x_968_, v___x_969_, v_a_945_, v_a_946_);
return v___x_974_;
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_986_; 
v_a_975_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_986_ == 0)
{
v___x_977_ = v___x_961_;
v_isShared_978_ = v_isSharedCheck_986_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_961_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_986_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_979_ = lean_io_error_to_string(v_a_975_);
v___x_980_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
v___x_981_ = l_Lean_MessageData_ofFormat(v___x_980_);
lean_inc(v_ref_958_);
v___x_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_982_, 0, v_ref_958_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_982_);
v___x_984_ = v___x_977_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_External_runInterruptible_0interp(lean_interpreter_value* stack)
{
lean_object* v_timeout_943_ = stack[0].m_obj;
lean_object* v_args_944_ = stack[1].m_obj;
lean_object* v_a_945_ = stack[2].m_obj;
lean_object* v_a_946_ = stack[3].m_obj;
lean_object* v_res_990_;
v_res_990_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible(v_timeout_943_, v_args_944_, v_a_945_, v_a_946_);
stack->m_obj
 = v_res_990_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_runInterruptible___boxed(lean_object* v_timeout_991_, lean_object* v_args_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible(v_timeout_991_, v_args_992_, v_a_993_, v_a_994_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec(v_timeout_991_);
return v_res_996_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_997_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__0);
v___x_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1000_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1001_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__1);
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
lean_ctor_set(v___x_1003_, 2, v___x_1002_);
lean_ctor_set(v___x_1003_, 3, v___x_1002_);
lean_ctor_set(v___x_1003_, 4, v___x_1001_);
lean_ctor_set(v___x_1003_, 5, v___x_1001_);
lean_ctor_set(v___x_1003_, 6, v___x_1001_);
lean_ctor_set(v___x_1003_, 7, v___x_1001_);
lean_ctor_set(v___x_1003_, 8, v___x_1001_);
lean_ctor_set(v___x_1003_, 9, v___x_1001_);
lean_ctor_set(v___x_1003_, 10, v___x_1001_);
lean_ctor_set(v___x_1003_, 11, v___x_1000_);
return v___x_1003_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = lean_unsigned_to_nat(32u);
v___x_1005_ = lean_mk_empty_array_with_capacity(v___x_1004_);
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1007_ = ((size_t)5ULL);
v___x_1008_ = lean_unsigned_to_nat(0u);
v___x_1009_ = lean_unsigned_to_nat(32u);
v___x_1010_ = lean_mk_empty_array_with_capacity(v___x_1009_);
v___x_1011_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__3);
v___x_1012_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v___x_1010_);
lean_ctor_set(v___x_1012_, 2, v___x_1008_);
lean_ctor_set(v___x_1012_, 3, v___x_1008_);
lean_ctor_set_usize(v___x_1012_, 4, v___x_1007_);
return v___x_1012_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1013_ = lean_box(1);
v___x_1014_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__4);
v___x_1015_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__1);
v___x_1016_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v___x_1014_);
lean_ctor_set(v___x_1016_, 2, v___x_1013_);
return v___x_1016_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0(lean_object* v_msgData_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v_toCold_1022_; lean_object* v_env_1023_; lean_object* v_options_1024_; uint8_t v___x_1025_; lean_object* v_env_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1021_ = lean_st_ref_get(v___y_1019_);
v_toCold_1022_ = lean_ctor_get(v___y_1018_, 0);
v_env_1023_ = lean_ctor_get(v___x_1021_, 0);
lean_inc_ref(v_env_1023_);
lean_dec(v___x_1021_);
v_options_1024_ = lean_ctor_get(v_toCold_1022_, 2);
v___x_1025_ = 0;
v_env_1026_ = l_Lean_Environment_setRecordingDeps(v_env_1023_, v___x_1025_);
v___x_1027_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__2);
v___x_1028_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_1024_);
v___x_1029_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1029_, 0, v_env_1026_);
lean_ctor_set(v___x_1029_, 1, v___x_1027_);
lean_ctor_set(v___x_1029_, 2, v___x_1028_);
lean_ctor_set(v___x_1029_, 3, v_options_1024_);
v___x_1030_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v_msgData_1017_);
v___x_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1017_ = stack[0].m_obj;
lean_object* v___y_1018_ = stack[1].m_obj;
lean_object* v___y_1019_ = stack[2].m_obj;
lean_object* v_res_1032_;
v_res_1032_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0(v_msgData_1017_, v___y_1018_, v___y_1019_);
stack->m_obj
 = v_res_1032_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0___boxed(lean_object* v_msgData_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0(v_msgData_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
return v_res_1037_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0___redArg(lean_object* v_msg_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_ref_1042_; lean_object* v___x_1043_; lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1052_; 
v_ref_1042_ = lean_ctor_get(v___y_1039_, 2);
v___x_1043_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_spec__0(v_msg_1038_, v___y_1039_, v___y_1040_);
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1046_ = v___x_1043_;
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1043_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1050_; 
lean_inc(v_ref_1042_);
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v_ref_1042_);
lean_ctor_set(v___x_1048_, 1, v_a_1044_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 1);
lean_ctor_set(v___x_1046_, 0, v___x_1048_);
v___x_1050_ = v___x_1046_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1038_ = stack[0].m_obj;
lean_object* v___y_1039_ = stack[1].m_obj;
lean_object* v___y_1040_ = stack[2].m_obj;
lean_object* v_res_1053_;
v_res_1053_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0___redArg(v_msg_1038_, v___y_1039_, v___y_1040_);
stack->m_obj
 = v_res_1053_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0___redArg___boxed(lean_object* v_msg_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0___redArg(v_msg_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
return v_res_1058_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___closed__2(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___closed__1));
v___x_1063_ = l_Lean_MessageData_ofFormat(v___x_1062_);
return v___x_1063_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___closed__2);
v___x_1068_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0___redArg(v___x_1067_, v_a_1064_, v_a_1065_);
return v___x_1068_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1064_ = stack[0].m_obj;
lean_object* v_a_1065_ = stack[1].m_obj;
lean_object* v_res_1069_;
v_res_1069_ = l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(v_a_1064_, v_a_1065_);
stack->m_obj
 = v_res_1069_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg___boxed(lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(v_a_1070_, v_a_1071_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
return v_res_1073_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout(lean_object* v_00_u03b1_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(v_a_1075_, v_a_1076_);
return v___x_1078_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1075_ = stack[1].m_obj;
lean_object* v_a_1076_ = stack[2].m_obj;
lean_object* v_res_1079_;
v_res_1079_ = l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout(lean_box(0), v_a_1075_, v_a_1076_);
stack->m_obj
 = v_res_1079_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___boxed(lean_object* v_00_u03b1_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout(v_00_u03b1_1080_, v_a_1081_, v_a_1082_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
return v_res_1084_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0(lean_object* v_00_u03b1_1085_, lean_object* v_msg_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0___redArg(v_msg_1086_, v___y_1087_, v___y_1088_);
return v___x_1090_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1086_ = stack[1].m_obj;
lean_object* v___y_1087_ = stack[2].m_obj;
lean_object* v___y_1088_ = stack[3].m_obj;
lean_object* v_res_1091_;
v_res_1091_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0(lean_box(0), v_msg_1086_, v___y_1087_, v___y_1088_);
stack->m_obj
 = v_res_1091_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0___boxed(lean_object* v_00_u03b1_1092_, lean_object* v_msg_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0(v_00_u03b1_1092_, v_msg_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1097_;
}
}
static uint32_t _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__2(void){
_start:
{
lean_object* v___x_1101_; uint32_t v___x_1102_; 
v___x_1101_ = lean_unsigned_to_nat(0u);
v___x_1102_ = lean_int32_of_nat(v___x_1101_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = lean_uint32_once(&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__2, &l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__2);
v___x_1104_ = lean_box_uint32(v___x_1103_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__3(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1105_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__1));
v___x_1106_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__3___boxed__const__1;
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__4(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1108_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__3, &l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__3);
v___x_1109_ = lean_unsigned_to_nat(1u);
v___x_1110_ = lean_mk_empty_array_with_capacity(v___x_1109_);
v___x_1111_ = lean_array_push(v___x_1110_, v___x_1108_);
return v___x_1111_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode(uint8_t v_mode_1115_){
_start:
{
lean_object* v___y_1117_; 
switch(v_mode_1115_)
{
case 0:
{
lean_object* v___x_1121_; 
v___x_1121_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__5));
v___y_1117_ = v___x_1121_;
goto v___jp_1116_;
}
case 1:
{
lean_object* v___x_1122_; 
v___x_1122_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__6));
v___y_1117_ = v___x_1122_;
goto v___jp_1116_;
}
default: 
{
lean_object* v___x_1123_; 
v___x_1123_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__7));
v___y_1117_ = v___x_1123_;
goto v___jp_1116_;
}
}
v___jp_1116_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__0));
v___x_1119_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__4, &l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__4);
lean_inc_ref(v___y_1117_);
v___x_1120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1120_, 0, v___y_1117_);
lean_ctor_set(v___x_1120_, 1, v___x_1118_);
lean_ctor_set(v___x_1120_, 2, v___x_1119_);
return v___x_1120_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode_0interp(lean_interpreter_value* stack)
{
uint8_t v_mode_1115_ = stack[0].m_num;
lean_object* v_res_1124_;
v_res_1124_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode(v_mode_1115_);
stack->m_obj
 = v_res_1124_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___boxed(lean_object* v_mode_1125_){
_start:
{
uint8_t v_mode_boxed_1126_; lean_object* v_res_1127_; 
v_mode_boxed_1126_ = lean_unbox(v_mode_1125_);
v_res_1127_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode(v_mode_boxed_1126_);
return v_res_1127_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat(lean_object* v_opts_1137_, uint8_t v_binary_1138_){
_start:
{
lean_object* v_configuration_1139_; lean_object* v_longOptions_1140_; lean_object* v_options_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1155_; 
v_configuration_1139_ = lean_ctor_get(v_opts_1137_, 0);
v_longOptions_1140_ = lean_ctor_get(v_opts_1137_, 1);
v_options_1141_ = lean_ctor_get(v_opts_1137_, 2);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_opts_1137_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1143_ = v_opts_1137_;
v_isShared_1144_ = v_isSharedCheck_1155_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_options_1141_);
lean_inc(v_longOptions_1140_);
lean_inc(v_configuration_1139_);
lean_dec(v_opts_1137_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1155_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; uint32_t v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1145_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___closed__2));
v___x_1146_ = l_Array_append___redArg(v_longOptions_1140_, v___x_1145_);
v___x_1147_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___closed__3));
v___x_1148_ = lean_bool_to_uint32(v_binary_1138_);
v___x_1149_ = lean_box_uint32(v___x_1148_);
v___x_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1147_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = lean_array_push(v_options_1141_, v___x_1150_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 2, v___x_1151_);
lean_ctor_set(v___x_1143_, 1, v___x_1146_);
v___x_1153_ = v___x_1143_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_configuration_1139_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1137_ = stack[0].m_obj;
uint8_t v_binary_1138_ = stack[1].m_num;
lean_object* v_res_1156_;
v_res_1156_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat(v_opts_1137_, v_binary_1138_);
stack->m_obj
 = v_res_1156_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat___boxed(lean_object* v_opts_1157_, lean_object* v_binary_1158_){
_start:
{
uint8_t v_binary_boxed_1159_; lean_object* v_res_1160_; 
v_binary_boxed_1159_ = lean_unbox(v_binary_1158_);
v_res_1160_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat(v_opts_1157_, v_binary_boxed_1159_);
return v_res_1160_;
}
}
static uint32_t _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__1(void){
_start:
{
lean_object* v___x_1162_; uint32_t v___x_1163_; 
v___x_1162_ = lean_unsigned_to_nat(2u);
v___x_1163_ = lean_int32_of_nat(v___x_1162_);
return v___x_1163_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_uint32_once(&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__1, &l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__1);
v___x_1165_ = lean_box_uint32(v___x_1164_);
return v___x_1165_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__2(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__0));
v___x_1167_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__2___boxed__const__1;
v___x_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1166_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental(lean_object* v_opts_1169_){
_start:
{
lean_object* v_configuration_1170_; lean_object* v_longOptions_1171_; lean_object* v_options_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1181_; 
v_configuration_1170_ = lean_ctor_get(v_opts_1169_, 0);
v_longOptions_1171_ = lean_ctor_get(v_opts_1169_, 1);
v_options_1172_ = lean_ctor_get(v_opts_1169_, 2);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_opts_1169_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1174_ = v_opts_1169_;
v_isShared_1175_ = v_isSharedCheck_1181_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_options_1172_);
lean_inc(v_longOptions_1171_);
lean_inc(v_configuration_1170_);
lean_dec(v_opts_1169_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1181_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1176_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__2, &l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental___closed__2);
v___x_1177_ = lean_array_push(v_options_1172_, v___x_1176_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 2, v___x_1177_);
v___x_1179_ = v___x_1174_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_configuration_1170_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_longOptions_1171_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flag(lean_object* v_opt_1183_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flag___closed__0));
v___x_1185_ = lean_string_append(v___x_1184_, v_opt_1183_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flag___boxed(lean_object* v_opt_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flag(v_opt_1186_);
lean_dec_ref(v_opt_1186_);
return v_res_1187_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flagValue(lean_object* v_opt_1189_, uint32_t v_val_1190_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flag___closed__0));
v___x_1192_ = lean_string_append(v___x_1191_, v_opt_1189_);
v___x_1193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flagValue___closed__0));
v___x_1194_ = lean_string_append(v___x_1192_, v___x_1193_);
v___x_1195_ = lean_int32_to_int(v_val_1190_);
v___x_1196_ = l_Int_repr(v___x_1195_);
lean_dec(v___x_1195_);
v___x_1197_ = lean_string_append(v___x_1194_, v___x_1196_);
lean_dec_ref(v___x_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flagValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_1189_ = stack[0].m_obj;
uint32_t v_val_1190_ = stack[1].m_num;
lean_object* v_res_1198_;
v_res_1198_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flagValue(v_opt_1189_, v_val_1190_);
stack->m_obj
 = v_res_1198_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flagValue___boxed(lean_object* v_opt_1199_, lean_object* v_val_1200_){
_start:
{
uint32_t v_val_boxed_1201_; lean_object* v_res_1202_; 
v_val_boxed_1201_ = lean_unbox_uint32(v_val_1200_);
lean_dec(v_val_1200_);
v_res_1202_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flagValue(v_opt_1199_, v_val_boxed_1201_);
lean_dec_ref(v_opt_1199_);
return v_res_1202_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__1(lean_object* v_as_1203_, size_t v_sz_1204_, size_t v_i_1205_, lean_object* v_b_1206_){
_start:
{
uint8_t v___x_1207_; 
v___x_1207_ = lean_usize_dec_lt(v_i_1205_, v_sz_1204_);
if (v___x_1207_ == 0)
{
return v_b_1206_;
}
else
{
lean_object* v_a_1208_; lean_object* v_fst_1209_; lean_object* v_snd_1210_; uint32_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; size_t v___x_1214_; size_t v___x_1215_; 
v_a_1208_ = lean_array_uget_borrowed(v_as_1203_, v_i_1205_);
v_fst_1209_ = lean_ctor_get(v_a_1208_, 0);
v_snd_1210_ = lean_ctor_get(v_a_1208_, 1);
v___x_1211_ = lean_unbox_uint32(v_snd_1210_);
v___x_1212_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flagValue(v_fst_1209_, v___x_1211_);
v___x_1213_ = lean_array_push(v_b_1206_, v___x_1212_);
v___x_1214_ = ((size_t)1ULL);
v___x_1215_ = lean_usize_add(v_i_1205_, v___x_1214_);
v_i_1205_ = v___x_1215_;
v_b_1206_ = v___x_1213_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1203_ = stack[0].m_obj;
size_t v_sz_1204_ = stack[1].m_num;
size_t v_i_1205_ = stack[2].m_num;
lean_object* v_b_1206_ = stack[3].m_obj;
lean_object* v_res_1217_;
v_res_1217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__1(v_as_1203_, v_sz_1204_, v_i_1205_, v_b_1206_);
stack->m_obj
 = v_res_1217_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__1___boxed(lean_object* v_as_1218_, lean_object* v_sz_1219_, lean_object* v_i_1220_, lean_object* v_b_1221_){
_start:
{
size_t v_sz_boxed_1222_; size_t v_i_boxed_1223_; lean_object* v_res_1224_; 
v_sz_boxed_1222_ = lean_unbox_usize(v_sz_1219_);
lean_dec(v_sz_1219_);
v_i_boxed_1223_ = lean_unbox_usize(v_i_1220_);
lean_dec(v_i_1220_);
v_res_1224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__1(v_as_1218_, v_sz_boxed_1222_, v_i_boxed_1223_, v_b_1221_);
lean_dec_ref(v_as_1218_);
return v_res_1224_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__0(lean_object* v_as_1225_, size_t v_sz_1226_, size_t v_i_1227_, lean_object* v_b_1228_){
_start:
{
uint8_t v___x_1229_; 
v___x_1229_ = lean_usize_dec_lt(v_i_1227_, v_sz_1226_);
if (v___x_1229_ == 0)
{
return v_b_1228_;
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; size_t v___x_1233_; size_t v___x_1234_; 
v_a_1230_ = lean_array_uget_borrowed(v_as_1225_, v_i_1227_);
v___x_1231_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flag(v_a_1230_);
v___x_1232_ = lean_array_push(v_b_1228_, v___x_1231_);
v___x_1233_ = ((size_t)1ULL);
v___x_1234_ = lean_usize_add(v_i_1227_, v___x_1233_);
v_i_1227_ = v___x_1234_;
v_b_1228_ = v___x_1232_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1225_ = stack[0].m_obj;
size_t v_sz_1226_ = stack[1].m_num;
size_t v_i_1227_ = stack[2].m_num;
lean_object* v_b_1228_ = stack[3].m_obj;
lean_object* v_res_1236_;
v_res_1236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__0(v_as_1225_, v_sz_1226_, v_i_1227_, v_b_1228_);
stack->m_obj
 = v_res_1236_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__0___boxed(lean_object* v_as_1237_, lean_object* v_sz_1238_, lean_object* v_i_1239_, lean_object* v_b_1240_){
_start:
{
size_t v_sz_boxed_1241_; size_t v_i_boxed_1242_; lean_object* v_res_1243_; 
v_sz_boxed_1241_ = lean_unbox_usize(v_sz_1238_);
lean_dec(v_sz_1238_);
v_i_boxed_1242_ = lean_unbox_usize(v_i_1239_);
lean_dec(v_i_1239_);
v_res_1243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__0(v_as_1237_, v_sz_boxed_1241_, v_i_boxed_1242_, v_b_1240_);
lean_dec_ref(v_as_1237_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs(lean_object* v_opts_1244_){
_start:
{
lean_object* v_configuration_1245_; lean_object* v_longOptions_1246_; lean_object* v_options_1247_; lean_object* v_args_1248_; lean_object* v___x_1249_; lean_object* v_args_1250_; size_t v_sz_1251_; size_t v___x_1252_; lean_object* v___x_1253_; size_t v_sz_1254_; lean_object* v___x_1255_; 
v_configuration_1245_ = lean_ctor_get(v_opts_1244_, 0);
v_longOptions_1246_ = lean_ctor_get(v_opts_1244_, 1);
v_options_1247_ = lean_ctor_get(v_opts_1244_, 2);
v_args_1248_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode___closed__0));
v___x_1249_ = l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_flag(v_configuration_1245_);
v_args_1250_ = lean_array_push(v_args_1248_, v___x_1249_);
v_sz_1251_ = lean_array_size(v_longOptions_1246_);
v___x_1252_ = ((size_t)0ULL);
v___x_1253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__0(v_longOptions_1246_, v_sz_1251_, v___x_1252_, v_args_1250_);
v_sz_1254_ = lean_array_size(v_options_1247_);
v___x_1255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs_spec__1(v_options_1247_, v_sz_1254_, v___x_1252_, v___x_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs___boxed(lean_object* v_opts_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs(v_opts_1256_);
lean_dec_ref(v_opts_1256_);
return v_res_1257_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__1(lean_object* v_solver_1258_, lean_object* v_as_1259_, size_t v_sz_1260_, size_t v_i_1261_, lean_object* v_b_1262_){
_start:
{
uint8_t v___x_1264_; 
v___x_1264_ = lean_usize_dec_lt(v_i_1261_, v_sz_1260_);
if (v___x_1264_ == 0)
{
return v_b_1262_;
}
else
{
lean_object* v_a_1265_; lean_object* v_fst_1266_; lean_object* v_snd_1267_; lean_object* v___x_1268_; uint32_t v___x_1269_; uint8_t v___x_1270_; size_t v___x_1271_; size_t v___x_1272_; 
v_a_1265_ = lean_array_uget_borrowed(v_as_1259_, v_i_1261_);
v_fst_1266_ = lean_ctor_get(v_a_1265_, 0);
v_snd_1267_ = lean_ctor_get(v_a_1265_, 1);
v___x_1268_ = lean_box(0);
v___x_1269_ = lean_unbox_uint32(v_snd_1267_);
v___x_1270_ = l_Lean_Cadical_Solver_setOption(v_solver_1258_, v_fst_1266_, v___x_1269_);
v___x_1271_ = ((size_t)1ULL);
v___x_1272_ = lean_usize_add(v_i_1261_, v___x_1271_);
v_i_1261_ = v___x_1272_;
v_b_1262_ = v___x_1268_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_solver_1258_ = stack[0].m_obj;
lean_object* v_as_1259_ = stack[1].m_obj;
size_t v_sz_1260_ = stack[2].m_num;
size_t v_i_1261_ = stack[3].m_num;
lean_object* v_b_1262_ = stack[4].m_obj;
lean_object* v_res_1274_;
v_res_1274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__1(v_solver_1258_, v_as_1259_, v_sz_1260_, v_i_1261_, v_b_1262_);
stack->m_obj
 = v_res_1274_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__1___boxed(lean_object* v_solver_1275_, lean_object* v_as_1276_, lean_object* v_sz_1277_, lean_object* v_i_1278_, lean_object* v_b_1279_, lean_object* v___y_1280_){
_start:
{
size_t v_sz_boxed_1281_; size_t v_i_boxed_1282_; lean_object* v_res_1283_; 
v_sz_boxed_1281_ = lean_unbox_usize(v_sz_1277_);
lean_dec(v_sz_1277_);
v_i_boxed_1282_ = lean_unbox_usize(v_i_1278_);
lean_dec(v_i_1278_);
v_res_1283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__1(v_solver_1275_, v_as_1276_, v_sz_boxed_1281_, v_i_boxed_1282_, v_b_1279_);
lean_dec_ref(v_as_1276_);
lean_dec_ref(v_solver_1275_);
return v_res_1283_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__0(lean_object* v_solver_1284_, lean_object* v_as_1285_, size_t v_sz_1286_, size_t v_i_1287_, lean_object* v_b_1288_){
_start:
{
uint8_t v___x_1290_; 
v___x_1290_ = lean_usize_dec_lt(v_i_1287_, v_sz_1286_);
if (v___x_1290_ == 0)
{
return v_b_1288_;
}
else
{
lean_object* v___x_1291_; lean_object* v_a_1292_; uint8_t v___x_1293_; size_t v___x_1294_; size_t v___x_1295_; 
v___x_1291_ = lean_box(0);
v_a_1292_ = lean_array_uget_borrowed(v_as_1285_, v_i_1287_);
v___x_1293_ = l_Lean_Cadical_Solver_setLongOption(v_solver_1284_, v_a_1292_);
v___x_1294_ = ((size_t)1ULL);
v___x_1295_ = lean_usize_add(v_i_1287_, v___x_1294_);
v_i_1287_ = v___x_1295_;
v_b_1288_ = v___x_1291_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_solver_1284_ = stack[0].m_obj;
lean_object* v_as_1285_ = stack[1].m_obj;
size_t v_sz_1286_ = stack[2].m_num;
size_t v_i_1287_ = stack[3].m_num;
lean_object* v_b_1288_ = stack[4].m_obj;
lean_object* v_res_1297_;
v_res_1297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__0(v_solver_1284_, v_as_1285_, v_sz_1286_, v_i_1287_, v_b_1288_);
stack->m_obj
 = v_res_1297_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__0___boxed(lean_object* v_solver_1298_, lean_object* v_as_1299_, lean_object* v_sz_1300_, lean_object* v_i_1301_, lean_object* v_b_1302_, lean_object* v___y_1303_){
_start:
{
size_t v_sz_boxed_1304_; size_t v_i_boxed_1305_; lean_object* v_res_1306_; 
v_sz_boxed_1304_ = lean_unbox_usize(v_sz_1300_);
lean_dec(v_sz_1300_);
v_i_boxed_1305_ = lean_unbox_usize(v_i_1301_);
lean_dec(v_i_1301_);
v_res_1306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__0(v_solver_1298_, v_as_1299_, v_sz_boxed_1304_, v_i_boxed_1305_, v_b_1302_);
lean_dec_ref(v_as_1299_);
lean_dec_ref(v_solver_1298_);
return v_res_1306_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver(lean_object* v_opts_1307_, lean_object* v_solver_1308_){
_start:
{
lean_object* v_configuration_1310_; lean_object* v_longOptions_1311_; lean_object* v_options_1312_; uint8_t v___x_1313_; lean_object* v___x_1314_; size_t v_sz_1315_; size_t v___x_1316_; lean_object* v___x_1317_; size_t v_sz_1318_; lean_object* v___x_1319_; 
v_configuration_1310_ = lean_ctor_get(v_opts_1307_, 0);
v_longOptions_1311_ = lean_ctor_get(v_opts_1307_, 1);
v_options_1312_ = lean_ctor_get(v_opts_1307_, 2);
v___x_1313_ = l_Lean_Cadical_Solver_configure(v_solver_1308_, v_configuration_1310_);
v___x_1314_ = lean_box(0);
v_sz_1315_ = lean_array_size(v_longOptions_1311_);
v___x_1316_ = ((size_t)0ULL);
v___x_1317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__0(v_solver_1308_, v_longOptions_1311_, v_sz_1315_, v___x_1316_, v___x_1314_);
v_sz_1318_ = lean_array_size(v_options_1312_);
v___x_1319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_spec__1(v_solver_1308_, v_options_1312_, v_sz_1318_, v___x_1316_, v___x_1314_);
return v___x_1314_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1307_ = stack[0].m_obj;
lean_object* v_solver_1308_ = stack[1].m_obj;
lean_object* v_res_1320_;
v_res_1320_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver(v_opts_1307_, v_solver_1308_);
stack->m_obj
 = v_res_1320_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver___boxed(lean_object* v_opts_1321_, lean_object* v_solver_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver(v_opts_1321_, v_solver_1322_);
lean_dec_ref(v_solver_1322_);
lean_dec_ref(v_opts_1321_);
return v_res_1324_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery(lean_object* v_solverPath_1336_, lean_object* v_problemPath_1337_, lean_object* v_proofOutput_1338_, lean_object* v_timeout_1339_, uint8_t v_binaryProofs_1340_, uint8_t v_mode_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v___x_1345_; lean_object* v_options_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v_args_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1345_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode(v_mode_1341_);
v_options_1346_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addLrat(v___x_1345_, v_binaryProofs_1340_);
v___x_1347_ = lean_unsigned_to_nat(2u);
v___x_1348_ = lean_mk_empty_array_with_capacity(v___x_1347_);
v___x_1349_ = lean_array_push(v___x_1348_, v_problemPath_1337_);
v___x_1350_ = lean_array_push(v___x_1349_, v_proofOutput_1338_);
v___x_1351_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_toArgs(v_options_1346_);
lean_dec_ref(v_options_1346_);
v_args_1352_ = l_Array_append___redArg(v___x_1350_, v___x_1351_);
lean_dec_ref(v___x_1351_);
v___x_1353_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__0));
v___x_1354_ = lean_box(0);
v___x_1355_ = lean_unsigned_to_nat(0u);
v___x_1356_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__1));
v___x_1357_ = 1;
v___x_1358_ = 0;
v___x_1359_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1359_, 0, v___x_1353_);
lean_ctor_set(v___x_1359_, 1, v_solverPath_1336_);
lean_ctor_set(v___x_1359_, 2, v_args_1352_);
lean_ctor_set(v___x_1359_, 3, v___x_1354_);
lean_ctor_set(v___x_1359_, 4, v___x_1356_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*5, v___x_1357_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*5 + 1, v___x_1358_);
v___x_1360_ = l_Lean_Meta_Tactic_BVDecide_External_runInterruptible(v_timeout_1339_, v___x_1359_, v_a_1342_, v_a_1343_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1434_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1434_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1434_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
if (lean_obj_tag(v_a_1361_) == 0)
{
lean_object* v_x_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1432_; 
v_x_1365_ = lean_ctor_get(v_a_1361_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_a_1361_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1367_ = v_a_1361_;
v_isShared_1368_ = v_isSharedCheck_1432_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_x_1365_);
lean_dec(v_a_1361_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1432_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
uint32_t v_exitCode_1369_; lean_object* v_stdout_1370_; lean_object* v_stderr_1371_; uint32_t v___x_1418_; uint8_t v___x_1419_; 
v_exitCode_1369_ = lean_ctor_get_uint32(v_x_1365_, sizeof(void*)*2);
v_stdout_1370_ = lean_ctor_get(v_x_1365_, 0);
lean_inc_ref(v_stdout_1370_);
v_stderr_1371_ = lean_ctor_get(v_x_1365_, 1);
lean_inc_ref(v_stderr_1371_);
lean_dec(v_x_1365_);
v___x_1418_ = 255;
v___x_1419_ = lean_uint32_dec_eq(v_exitCode_1369_, v___x_1418_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1420_ = lean_string_utf8_byte_size(v_stdout_1370_);
v___x_1421_ = lean_unsigned_to_nat(15u);
v___x_1422_ = lean_nat_dec_le(v___x_1421_, v___x_1420_);
if (v___x_1422_ == 0)
{
goto v___jp_1383_;
}
else
{
lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1423_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__6));
v___x_1424_ = lean_string_memcmp(v_stdout_1370_, v___x_1423_, v___x_1355_, v___x_1355_, v___x_1421_);
if (v___x_1424_ == 0)
{
goto v___jp_1383_;
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_dec_ref(v_stderr_1371_);
lean_dec_ref(v_stdout_1370_);
lean_del_object(v___x_1367_);
lean_del_object(v___x_1363_);
v___x_1425_ = lean_box(1);
v___x_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
return v___x_1426_;
}
}
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec_ref(v_stdout_1370_);
lean_del_object(v___x_1367_);
lean_del_object(v___x_1363_);
v___x_1427_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__7));
v___x_1428_ = lean_string_append(v___x_1427_, v_stderr_1371_);
lean_dec_ref(v_stderr_1371_);
v___x_1429_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
v___x_1430_ = l_Lean_MessageData_ofFormat(v___x_1429_);
v___x_1431_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0___redArg(v___x_1430_, v_a_1342_, v_a_1343_);
return v___x_1431_;
}
v___jp_1372_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1373_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__2));
v___x_1374_ = lean_string_append(v___x_1373_, v_stdout_1370_);
lean_dec_ref(v_stdout_1370_);
v___x_1375_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__3));
v___x_1376_ = lean_string_append(v___x_1374_, v___x_1375_);
v___x_1377_ = lean_string_append(v___x_1376_, v_stderr_1371_);
lean_dec_ref(v_stderr_1371_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set_tag(v___x_1367_, 3);
lean_ctor_set(v___x_1367_, 0, v___x_1377_);
v___x_1379_ = v___x_1367_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = l_Lean_MessageData_ofFormat(v___x_1379_);
v___x_1381_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0___redArg(v___x_1380_, v_a_1342_, v_a_1343_);
return v___x_1381_;
}
}
v___jp_1383_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1384_ = lean_string_utf8_byte_size(v_stdout_1370_);
v___x_1385_ = lean_unsigned_to_nat(13u);
v___x_1386_ = lean_nat_dec_le(v___x_1385_, v___x_1384_);
if (v___x_1386_ == 0)
{
lean_del_object(v___x_1363_);
goto v___jp_1372_;
}
else
{
lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1387_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parseHeader___closed__0));
v___x_1388_ = lean_string_memcmp(v_stdout_1370_, v___x_1387_, v___x_1355_, v___x_1355_, v___x_1385_);
if (v___x_1388_ == 0)
{
lean_del_object(v___x_1363_);
goto v___jp_1372_;
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
lean_dec_ref(v_stderr_1371_);
lean_del_object(v___x_1367_);
v___x_1389_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_External_0__Lean_Meta_Tactic_BVDecide_External_ModelParser_parse), 1, 0);
v___x_1390_ = lean_string_to_utf8(v_stdout_1370_);
v___x_1391_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_1389_, v___x_1390_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1406_; 
lean_del_object(v___x_1363_);
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1394_ = v___x_1391_;
v_isShared_1395_ = v_isSharedCheck_1406_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1391_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1406_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1396_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__4));
v___x_1397_ = lean_string_append(v___x_1396_, v_a_1392_);
lean_dec(v_a_1392_);
v___x_1398_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_External_satQuery___closed__5));
v___x_1399_ = lean_string_append(v___x_1397_, v___x_1398_);
v___x_1400_ = lean_string_append(v___x_1399_, v_stdout_1370_);
lean_dec_ref(v_stdout_1370_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set_tag(v___x_1394_, 3);
lean_ctor_set(v___x_1394_, 0, v___x_1400_);
v___x_1402_ = v___x_1394_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = l_Lean_MessageData_ofFormat(v___x_1402_);
v___x_1404_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_External_throwSatTimeout_spec__0___redArg(v___x_1403_, v_a_1342_, v_a_1343_);
return v___x_1404_;
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1417_; 
lean_dec_ref(v_stdout_1370_);
v_a_1407_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1409_ = v___x_1391_;
v_isShared_1410_ = v_isSharedCheck_1417_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1391_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1417_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set_tag(v___x_1409_, 0);
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1414_; 
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1412_);
v___x_1414_ = v___x_1363_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
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
lean_object* v___x_1433_; 
lean_del_object(v___x_1363_);
v___x_1433_ = l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(v_a_1342_, v_a_1343_);
return v___x_1433_;
}
}
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
v_a_1435_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1360_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1360_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_External_satQuery_0interp(lean_interpreter_value* stack)
{
lean_object* v_solverPath_1336_ = stack[0].m_obj;
lean_object* v_problemPath_1337_ = stack[1].m_obj;
lean_object* v_proofOutput_1338_ = stack[2].m_obj;
lean_object* v_timeout_1339_ = stack[3].m_obj;
uint8_t v_binaryProofs_1340_ = stack[4].m_num;
uint8_t v_mode_1341_ = stack[5].m_num;
lean_object* v_a_1342_ = stack[6].m_obj;
lean_object* v_a_1343_ = stack[7].m_obj;
lean_object* v_res_1443_;
v_res_1443_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solverPath_1336_, v_problemPath_1337_, v_proofOutput_1338_, v_timeout_1339_, v_binaryProofs_1340_, v_mode_1341_, v_a_1342_, v_a_1343_);
stack->m_obj
 = v_res_1443_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_External_satQuery___boxed(lean_object* v_solverPath_1444_, lean_object* v_problemPath_1445_, lean_object* v_proofOutput_1446_, lean_object* v_timeout_1447_, lean_object* v_binaryProofs_1448_, lean_object* v_mode_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_){
_start:
{
uint8_t v_binaryProofs_boxed_1453_; uint8_t v_mode_boxed_1454_; lean_object* v_res_1455_; 
v_binaryProofs_boxed_1453_ = lean_unbox(v_binaryProofs_1448_);
v_mode_boxed_1454_ = lean_unbox(v_mode_1449_);
v_res_1455_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(v_solverPath_1444_, v_problemPath_1445_, v_proofOutput_1446_, v_timeout_1447_, v_binaryProofs_boxed_1453_, v_mode_boxed_1454_, v_a_1450_, v_a_1451_);
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
lean_dec(v_timeout_1447_);
return v_res_1455_;
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
