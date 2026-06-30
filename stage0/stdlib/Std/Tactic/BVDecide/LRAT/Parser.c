// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Parser
// Imports: public import Init.System.IO public import Std.Tactic.BVDecide.LRAT.Actions public import Std.Internal.Parsec
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
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_uint64_to_uint8(uint64_t);
uint8_t lean_uint8_land(uint8_t, uint8_t);
uint8_t lean_uint8_lor(uint8_t, uint8_t);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint32_t lean_uint8_to_uint32(uint8_t);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
uint64_t lean_uint8_to_uint64(uint8_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint64_t lean_uint64_add(uint64_t, uint64_t);
uint64_t lean_uint64_land(uint64_t, uint64_t);
uint8_t lean_uint8_complement(uint8_t);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*);
lean_object* lean_mk_empty_byte_array(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
extern lean_object* l_Int_instInhabited;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___boxed(lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__0_value;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expected: '"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3_value;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7_value;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline(lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "digit expected"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1_value;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "id was 0"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos(lean_object*);
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseId(lean_object*);
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero(lean_object*);
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0;
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1;
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2;
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3;
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4;
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_spec__0(lean_object*, lean_object*);
static const lean_array_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(lean_object*);
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseLit(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_litWs(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__1(lean_object*, lean_object*);
static const lean_array_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(lean_object*, lean_object*);
static const lean_array_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "There cannot be any ratHints for adding the empty clause"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "condition not satisfied"};
static const lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__1_value;
static lean_once_cell_t l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2;
static lean_once_cell_t l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(lean_object*, lean_object*);
static const lean_array_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: '0'"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__0_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__0_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero(lean_object*);
static const lean_string_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Invalid zero byte in literal"};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__0 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__0_value;
static const lean_ctor_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__0_value)}};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1_value;
static const lean_string_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Excessive literal"};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2_value;
static const lean_ctor_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2_value)}};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3_value;
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(uint64_t, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "parsed non negative lit where negative was expected"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__0_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__0_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg(lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "parsed non positive lit where positive was expected"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__0_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__0_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(lean_object*);
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Expected a or d got: "};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expected end of input"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__0_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__0_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_parseActions(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_parseLRATProof(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___boxed(lean_object*);
static const lean_string_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___boxed(lean_object*);
static const lean_string_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " 0 "};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__0 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__0_value;
static const lean_string_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "0"};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1_value;
static const lean_string_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "0 "};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2_value;
static const lean_string_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "1 d "};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startDelete(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(lean_object*);
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0;
static const lean_string_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.Tactic.BVDecide.LRAT.Parser"};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1_value;
static const lean_string_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "_private.Std.Tactic.BVDecide.LRAT.Parser.0.Std.Tactic.BVDecide.LRAT.lratProofToBinary.addInt"};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2_value;
static const lean_string_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 91, .m_data = "assertion violation: mapped ≤ (2^64 - 1) -- our parser \"only\" supports 64 bit literals\n    "};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3_value;
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_zeroByte(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startAdd(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(lean_object* v_clause_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v_pivotInt_6_; lean_object* v___x_7_; uint8_t v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_4_ = l_Int_instInhabited;
v___x_5_ = lean_unsigned_to_nat(0u);
v_pivotInt_6_ = lean_array_get_borrowed(v___x_4_, v_clause_3_, v___x_5_);
v___x_7_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_8_ = lean_int_dec_lt(v___x_7_, v_pivotInt_6_);
v___x_9_ = lean_nat_abs(v_pivotInt_6_);
v___x_10_ = lean_box(v___x_8_);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_9_);
lean_ctor_set(v___x_11_, 1, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___boxed(lean_object* v_clause_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_clause_12_);
lean_dec_ref(v_clause_12_);
return v_res_13_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1(void){
_start:
{
lean_object* v___x_15_; lean_object* v_utf8_16_; 
v___x_15_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__0));
v_utf8_16_ = lean_string_to_utf8(v___x_15_);
return v_utf8_16_;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2(void){
_start:
{
uint32_t v___x_17_; uint8_t v___x_18_; 
v___x_17_ = 10;
v___x_18_ = lean_uint32_to_uint8(v___x_17_);
return v___x_18_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4(void){
_start:
{
uint8_t v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2);
v___x_21_ = lean_uint8_to_nat(v___x_20_);
return v___x_21_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4);
v___x_23_ = l_Nat_reprFast(v___x_22_);
return v___x_23_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5);
v___x_25_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
v___x_26_ = lean_string_append(v___x_25_, v___x_24_);
return v___x_26_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7));
v___x_29_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6);
v___x_30_ = lean_string_append(v___x_29_, v___x_28_);
return v___x_30_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8);
v___x_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline(lean_object* v_a_33_){
_start:
{
lean_object* v_array_34_; lean_object* v_idx_35_; lean_object* v___y_37_; lean_object* v_pos_38_; lean_object* v_idx_39_; lean_object* v___x_53_; uint8_t v___x_54_; 
v_array_34_ = lean_ctor_get(v_a_33_, 0);
v_idx_35_ = lean_ctor_get(v_a_33_, 1);
lean_inc(v_idx_35_);
v___x_53_ = lean_byte_array_size(v_array_34_);
v___x_54_ = lean_nat_dec_lt(v_idx_35_, v___x_53_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_box(0);
lean_inc_ref(v_a_33_);
v___x_56_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_56_, 0, v_a_33_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
lean_inc(v_idx_35_);
v___y_37_ = v___x_56_;
v_pos_38_ = v_a_33_;
v_idx_39_ = v_idx_35_;
goto v___jp_36_;
}
else
{
uint8_t v___x_57_; uint8_t v_got_58_; uint8_t v___x_59_; 
v___x_57_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2);
v_got_58_ = lean_byte_array_fget(v_array_34_, v_idx_35_);
v___x_59_ = lean_uint8_dec_eq(v_got_58_, v___x_57_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9);
lean_inc_ref(v_a_33_);
v___x_61_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_61_, 0, v_a_33_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
lean_inc(v_idx_35_);
v___y_37_ = v___x_61_;
v_pos_38_ = v_a_33_;
v_idx_39_ = v_idx_35_;
goto v___jp_36_;
}
else
{
lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_72_; 
lean_inc_ref(v_array_34_);
v_isSharedCheck_72_ = !lean_is_exclusive(v_a_33_);
if (v_isSharedCheck_72_ == 0)
{
lean_object* v_unused_73_; lean_object* v_unused_74_; 
v_unused_73_ = lean_ctor_get(v_a_33_, 1);
lean_dec(v_unused_73_);
v_unused_74_ = lean_ctor_get(v_a_33_, 0);
lean_dec(v_unused_74_);
v___x_63_ = v_a_33_;
v_isShared_64_ = v_isSharedCheck_72_;
goto v_resetjp_62_;
}
else
{
lean_dec(v_a_33_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_72_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_68_; 
v___x_65_ = lean_unsigned_to_nat(1u);
v___x_66_ = lean_nat_add(v_idx_35_, v___x_65_);
lean_dec(v_idx_35_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 1, v___x_66_);
v___x_68_ = v___x_63_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_array_34_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v___x_66_);
v___x_68_ = v_reuseFailAlloc_71_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_box(0);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_68_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
return v___x_70_;
}
}
}
}
v___jp_36_:
{
uint8_t v___x_40_; 
v___x_40_ = lean_nat_dec_eq(v_idx_35_, v_idx_39_);
lean_dec(v_idx_39_);
lean_dec(v_idx_35_);
if (v___x_40_ == 0)
{
lean_dec_ref(v_pos_38_);
return v___y_37_;
}
else
{
lean_object* v_utf8_41_; lean_object* v___x_42_; 
lean_dec_ref(v___y_37_);
v_utf8_41_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1);
v___x_42_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_41_, v_pos_38_);
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v_pos_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_51_; 
v_pos_43_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_51_ == 0)
{
lean_object* v_unused_52_; 
v_unused_52_ = lean_ctor_get(v___x_42_, 1);
lean_dec(v_unused_52_);
v___x_45_ = v___x_42_;
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_pos_43_);
lean_dec(v___x_42_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_49_; 
v___x_47_ = lean_box(0);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 1, v___x_47_);
v___x_49_ = v___x_45_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_pos_43_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v___x_47_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
else
{
return v___x_42_;
}
}
}
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2(void){
_start:
{
uint32_t v___x_78_; uint8_t v___x_79_; 
v___x_78_ = 48;
v___x_79_ = lean_uint32_to_uint8(v___x_78_);
return v___x_79_;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3(void){
_start:
{
uint32_t v___x_80_; uint8_t v___x_81_; 
v___x_80_ = 57;
v___x_81_ = lean_uint32_to_uint8(v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos(lean_object* v_a_85_){
_start:
{
lean_object* v_array_89_; lean_object* v_idx_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v_array_89_ = lean_ctor_get(v_a_85_, 0);
v_idx_90_ = lean_ctor_get(v_a_85_, 1);
v___x_91_ = lean_byte_array_size(v_array_89_);
v___x_92_ = lean_nat_dec_lt(v_idx_90_, v___x_91_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_box(0);
v___x_94_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_94_, 0, v_a_85_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
return v___x_94_;
}
else
{
uint8_t v_c_95_; uint8_t v___x_96_; uint8_t v___x_97_; 
v_c_95_ = lean_byte_array_fget(v_array_89_, v_idx_90_);
v___x_96_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
v___x_97_ = lean_uint8_dec_le(v___x_96_, v_c_95_);
if (v___x_97_ == 0)
{
goto v___jp_86_;
}
else
{
uint8_t v___x_98_; uint8_t v___x_99_; 
v___x_98_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
v___x_99_ = lean_uint8_dec_le(v_c_95_, v___x_98_);
if (v___x_99_ == 0)
{
goto v___jp_86_;
}
else
{
lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_128_; 
lean_inc(v_idx_90_);
lean_inc_ref(v_array_89_);
v_isSharedCheck_128_ = !lean_is_exclusive(v_a_85_);
if (v_isSharedCheck_128_ == 0)
{
lean_object* v_unused_129_; lean_object* v_unused_130_; 
v_unused_129_ = lean_ctor_get(v_a_85_, 1);
lean_dec(v_unused_129_);
v_unused_130_ = lean_ctor_get(v_a_85_, 0);
lean_dec(v_unused_130_);
v___x_101_ = v_a_85_;
v_isShared_102_ = v_isSharedCheck_128_;
goto v_resetjp_100_;
}
else
{
lean_dec(v_a_85_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_128_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v_it_x27_106_; 
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = lean_nat_add(v_idx_90_, v___x_103_);
lean_dec(v_idx_90_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v___x_104_);
v_it_x27_106_ = v___x_101_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_array_89_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v___x_104_);
v_it_x27_106_ = v_reuseFailAlloc_127_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
uint32_t v___x_107_; uint8_t v___x_108_; uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v_fst_112_; lean_object* v_snd_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_126_; 
v___x_107_ = lean_uint8_to_uint32(v_c_95_);
v___x_108_ = lean_uint32_to_uint8(v___x_107_);
v___x_109_ = lean_uint8_sub(v___x_108_, v___x_96_);
v___x_110_ = lean_uint8_to_nat(v___x_109_);
v___x_111_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_106_, v___x_110_);
v_fst_112_ = lean_ctor_get(v___x_111_, 0);
v_snd_113_ = lean_ctor_get(v___x_111_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_126_ == 0)
{
v___x_115_ = v___x_111_;
v_isShared_116_ = v_isSharedCheck_126_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_snd_113_);
lean_inc(v_fst_112_);
lean_dec(v___x_111_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_126_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_nat_dec_eq(v_fst_112_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_120_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v_fst_112_);
lean_ctor_set(v___x_115_, 0, v_snd_113_);
v___x_120_ = v___x_115_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_snd_113_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_fst_112_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
else
{
lean_object* v___x_122_; lean_object* v___x_124_; 
lean_dec(v_fst_112_);
v___x_122_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
if (v_isShared_116_ == 0)
{
lean_ctor_set_tag(v___x_115_, 1);
lean_ctor_set(v___x_115_, 1, v___x_122_);
lean_ctor_set(v___x_115_, 0, v_snd_113_);
v___x_124_ = v___x_115_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_snd_113_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
}
}
}
}
v___jp_86_:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_88_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_88_, 0, v_a_85_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
return v___x_88_;
}
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0(void){
_start:
{
uint32_t v___x_131_; uint8_t v___x_132_; 
v___x_131_ = 45;
v___x_132_ = lean_uint32_to_uint8(v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1(void){
_start:
{
uint8_t v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0);
v___x_134_ = lean_uint8_to_nat(v___x_133_);
return v___x_134_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1);
v___x_136_ = l_Nat_reprFast(v___x_135_);
return v___x_136_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2);
v___x_138_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
v___x_139_ = lean_string_append(v___x_138_, v___x_137_);
return v___x_139_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7));
v___x_141_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3);
v___x_142_ = lean_string_append(v___x_141_, v___x_140_);
return v___x_142_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4);
v___x_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg(lean_object* v_a_145_){
_start:
{
lean_object* v_array_146_; lean_object* v_idx_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v_array_146_ = lean_ctor_get(v_a_145_, 0);
v_idx_147_ = lean_ctor_get(v_a_145_, 1);
v___x_148_ = lean_byte_array_size(v_array_146_);
v___x_149_ = lean_nat_dec_lt(v_idx_147_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_box(0);
v___x_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_151_, 0, v_a_145_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
return v___x_151_;
}
else
{
uint8_t v___x_152_; uint8_t v_got_153_; uint8_t v___x_154_; 
v___x_152_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0);
v_got_153_ = lean_byte_array_fget(v_array_146_, v_idx_147_);
v___x_154_ = lean_uint8_dec_eq(v_got_153_, v___x_152_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
v___x_156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_156_, 0, v_a_145_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
return v___x_156_;
}
else
{
lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_200_; 
lean_inc(v_idx_147_);
lean_inc_ref(v_array_146_);
v_isSharedCheck_200_ = !lean_is_exclusive(v_a_145_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; lean_object* v_unused_202_; 
v_unused_201_ = lean_ctor_get(v_a_145_, 1);
lean_dec(v_unused_201_);
v_unused_202_ = lean_ctor_get(v_a_145_, 0);
lean_dec(v_unused_202_);
v___x_158_ = v_a_145_;
v_isShared_159_ = v_isSharedCheck_200_;
goto v_resetjp_157_;
}
else
{
lean_dec(v_a_145_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_200_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_160_ = lean_unsigned_to_nat(1u);
v___x_161_ = lean_nat_add(v_idx_147_, v___x_160_);
lean_dec(v_idx_147_);
lean_inc(v___x_161_);
lean_inc_ref(v_array_146_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v___x_161_);
v___x_163_ = v___x_158_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_array_146_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v___x_161_);
v___x_163_ = v_reuseFailAlloc_199_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
uint8_t v___x_167_; 
v___x_167_ = lean_nat_dec_lt(v___x_161_, v___x_148_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec(v___x_161_);
lean_dec_ref(v_array_146_);
v___x_168_ = lean_box(0);
v___x_169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_163_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
return v___x_169_;
}
else
{
uint8_t v_c_170_; uint8_t v___x_171_; uint8_t v___x_172_; 
v_c_170_ = lean_byte_array_fget(v_array_146_, v___x_161_);
v___x_171_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
v___x_172_ = lean_uint8_dec_le(v___x_171_, v_c_170_);
if (v___x_172_ == 0)
{
lean_dec(v___x_161_);
lean_dec_ref(v_array_146_);
goto v___jp_164_;
}
else
{
uint8_t v___x_173_; uint8_t v___x_174_; 
v___x_173_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
v___x_174_ = lean_uint8_dec_le(v_c_170_, v___x_173_);
if (v___x_174_ == 0)
{
lean_dec(v___x_161_);
lean_dec_ref(v_array_146_);
goto v___jp_164_;
}
else
{
lean_object* v___x_175_; lean_object* v_it_x27_176_; uint32_t v___x_177_; uint8_t v___x_178_; uint8_t v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v_fst_182_; lean_object* v_snd_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_198_; 
lean_dec_ref(v___x_163_);
v___x_175_ = lean_nat_add(v___x_161_, v___x_160_);
lean_dec(v___x_161_);
v_it_x27_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_176_, 0, v_array_146_);
lean_ctor_set(v_it_x27_176_, 1, v___x_175_);
v___x_177_ = lean_uint8_to_uint32(v_c_170_);
v___x_178_ = lean_uint32_to_uint8(v___x_177_);
v___x_179_ = lean_uint8_sub(v___x_178_, v___x_171_);
v___x_180_ = lean_uint8_to_nat(v___x_179_);
v___x_181_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_176_, v___x_180_);
v_fst_182_ = lean_ctor_get(v___x_181_, 0);
v_snd_183_ = lean_ctor_get(v___x_181_, 1);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_198_ == 0)
{
v___x_185_ = v___x_181_;
v_isShared_186_ = v_isSharedCheck_198_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_snd_183_);
lean_inc(v_fst_182_);
lean_dec(v___x_181_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_198_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = lean_nat_dec_eq(v_fst_182_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_189_ = lean_nat_to_int(v_fst_182_);
v___x_190_ = lean_int_neg(v___x_189_);
lean_dec(v___x_189_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 1, v___x_190_);
lean_ctor_set(v___x_185_, 0, v_snd_183_);
v___x_192_ = v___x_185_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_snd_183_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
else
{
lean_object* v___x_194_; lean_object* v___x_196_; 
lean_dec(v_fst_182_);
v___x_194_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
if (v_isShared_186_ == 0)
{
lean_ctor_set_tag(v___x_185_, 1);
lean_ctor_set(v___x_185_, 1, v___x_194_);
lean_ctor_set(v___x_185_, 0, v_snd_183_);
v___x_196_ = v___x_185_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_snd_183_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
}
v___jp_164_:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_163_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
return v___x_166_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseId(lean_object* v_a_203_){
_start:
{
lean_object* v_array_207_; lean_object* v_idx_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v_array_207_ = lean_ctor_get(v_a_203_, 0);
v_idx_208_ = lean_ctor_get(v_a_203_, 1);
v___x_209_ = lean_byte_array_size(v_array_207_);
v___x_210_ = lean_nat_dec_lt(v_idx_208_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_box(0);
v___x_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_212_, 0, v_a_203_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
return v___x_212_;
}
else
{
uint8_t v_c_213_; uint8_t v___x_214_; uint8_t v___x_215_; 
v_c_213_ = lean_byte_array_fget(v_array_207_, v_idx_208_);
v___x_214_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
v___x_215_ = lean_uint8_dec_le(v___x_214_, v_c_213_);
if (v___x_215_ == 0)
{
goto v___jp_204_;
}
else
{
uint8_t v___x_216_; uint8_t v___x_217_; 
v___x_216_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
v___x_217_ = lean_uint8_dec_le(v_c_213_, v___x_216_);
if (v___x_217_ == 0)
{
goto v___jp_204_;
}
else
{
lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_246_; 
lean_inc(v_idx_208_);
lean_inc_ref(v_array_207_);
v_isSharedCheck_246_ = !lean_is_exclusive(v_a_203_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; lean_object* v_unused_248_; 
v_unused_247_ = lean_ctor_get(v_a_203_, 1);
lean_dec(v_unused_247_);
v_unused_248_ = lean_ctor_get(v_a_203_, 0);
lean_dec(v_unused_248_);
v___x_219_ = v_a_203_;
v_isShared_220_ = v_isSharedCheck_246_;
goto v_resetjp_218_;
}
else
{
lean_dec(v_a_203_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_246_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v_it_x27_224_; 
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_add(v_idx_208_, v___x_221_);
lean_dec(v_idx_208_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v___x_222_);
v_it_x27_224_ = v___x_219_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_array_207_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v___x_222_);
v_it_x27_224_ = v_reuseFailAlloc_245_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
uint32_t v___x_225_; uint8_t v___x_226_; uint8_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_fst_230_; lean_object* v_snd_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_244_; 
v___x_225_ = lean_uint8_to_uint32(v_c_213_);
v___x_226_ = lean_uint32_to_uint8(v___x_225_);
v___x_227_ = lean_uint8_sub(v___x_226_, v___x_214_);
v___x_228_ = lean_uint8_to_nat(v___x_227_);
v___x_229_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_224_, v___x_228_);
v_fst_230_ = lean_ctor_get(v___x_229_, 0);
v_snd_231_ = lean_ctor_get(v___x_229_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_244_ == 0)
{
v___x_233_ = v___x_229_;
v_isShared_234_ = v_isSharedCheck_244_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_snd_231_);
lean_inc(v_fst_230_);
lean_dec(v___x_229_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_244_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = lean_nat_dec_eq(v_fst_230_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_238_; 
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v_fst_230_);
lean_ctor_set(v___x_233_, 0, v_snd_231_);
v___x_238_ = v___x_233_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_snd_231_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_fst_230_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
else
{
lean_object* v___x_240_; lean_object* v___x_242_; 
lean_dec(v_fst_230_);
v___x_240_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
if (v_isShared_234_ == 0)
{
lean_ctor_set_tag(v___x_233_, 1);
lean_ctor_set(v___x_233_, 1, v___x_240_);
lean_ctor_set(v___x_233_, 0, v_snd_231_);
v___x_242_ = v___x_233_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_snd_231_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
}
}
}
v___jp_204_:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_206_, 0, v_a_203_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
return v___x_206_;
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0(void){
_start:
{
uint8_t v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
v___x_250_ = lean_uint8_to_nat(v___x_249_);
return v___x_250_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0);
v___x_252_ = l_Nat_reprFast(v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1);
v___x_254_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
v___x_255_ = lean_string_append(v___x_254_, v___x_253_);
return v___x_255_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7));
v___x_257_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2);
v___x_258_ = lean_string_append(v___x_257_, v___x_256_);
return v___x_258_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3);
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero(lean_object* v_a_261_){
_start:
{
lean_object* v_array_262_; lean_object* v_idx_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_array_262_ = lean_ctor_get(v_a_261_, 0);
v_idx_263_ = lean_ctor_get(v_a_261_, 1);
v___x_264_ = lean_byte_array_size(v_array_262_);
v___x_265_ = lean_nat_dec_lt(v_idx_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_box(0);
v___x_267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_267_, 0, v_a_261_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
return v___x_267_;
}
else
{
uint8_t v___x_268_; uint8_t v_got_269_; uint8_t v___x_270_; 
v___x_268_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
v_got_269_ = lean_byte_array_fget(v_array_262_, v_idx_263_);
v___x_270_ = lean_uint8_dec_eq(v_got_269_, v___x_268_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4);
v___x_272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_272_, 0, v_a_261_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
return v___x_272_;
}
else
{
lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_283_; 
lean_inc(v_idx_263_);
lean_inc_ref(v_array_262_);
v_isSharedCheck_283_ = !lean_is_exclusive(v_a_261_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; lean_object* v_unused_285_; 
v_unused_284_ = lean_ctor_get(v_a_261_, 1);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v_a_261_, 0);
lean_dec(v_unused_285_);
v___x_274_ = v_a_261_;
v_isShared_275_ = v_isSharedCheck_283_;
goto v_resetjp_273_;
}
else
{
lean_dec(v_a_261_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_283_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_276_ = lean_unsigned_to_nat(1u);
v___x_277_ = lean_nat_add(v_idx_263_, v___x_276_);
lean_dec(v_idx_263_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 1, v___x_277_);
v___x_279_ = v___x_274_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_array_262_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v___x_277_);
v___x_279_ = v_reuseFailAlloc_282_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_box(0);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_279_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
return v___x_281_;
}
}
}
}
}
}
static uint8_t _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0(void){
_start:
{
uint32_t v___x_286_; uint8_t v___x_287_; 
v___x_286_ = 32;
v___x_287_ = lean_uint32_to_uint8(v___x_286_);
return v___x_287_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1(void){
_start:
{
uint8_t v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
v___x_289_ = lean_uint8_to_nat(v___x_288_);
return v___x_289_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1);
v___x_291_ = l_Nat_reprFast(v___x_290_);
return v___x_291_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2);
v___x_293_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
v___x_294_ = lean_string_append(v___x_293_, v___x_292_);
return v___x_294_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7));
v___x_296_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3);
v___x_297_ = lean_string_append(v___x_296_, v___x_295_);
return v___x_297_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4);
v___x_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs(lean_object* v_a_300_){
_start:
{
lean_object* v_array_304_; lean_object* v_idx_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v_array_304_ = lean_ctor_get(v_a_300_, 0);
v_idx_305_ = lean_ctor_get(v_a_300_, 1);
v___x_306_ = lean_byte_array_size(v_array_304_);
v___x_307_ = lean_nat_dec_lt(v_idx_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_box(0);
v___x_309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_309_, 0, v_a_300_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
return v___x_309_;
}
else
{
uint8_t v_c_310_; uint8_t v___x_311_; uint8_t v___x_312_; 
v_c_310_ = lean_byte_array_fget(v_array_304_, v_idx_305_);
v___x_311_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
v___x_312_ = lean_uint8_dec_le(v___x_311_, v_c_310_);
if (v___x_312_ == 0)
{
goto v___jp_301_;
}
else
{
uint8_t v___x_313_; uint8_t v___x_314_; 
v___x_313_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
v___x_314_ = lean_uint8_dec_le(v_c_310_, v___x_313_);
if (v___x_314_ == 0)
{
goto v___jp_301_;
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v_it_x27_317_; uint32_t v___x_318_; uint8_t v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v_fst_323_; lean_object* v_snd_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_362_; 
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_add(v_idx_305_, v___x_315_);
lean_inc_ref(v_array_304_);
v_it_x27_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_317_, 0, v_array_304_);
lean_ctor_set(v_it_x27_317_, 1, v___x_316_);
v___x_318_ = lean_uint8_to_uint32(v_c_310_);
v___x_319_ = lean_uint32_to_uint8(v___x_318_);
v___x_320_ = lean_uint8_sub(v___x_319_, v___x_311_);
v___x_321_ = lean_uint8_to_nat(v___x_320_);
v___x_322_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_317_, v___x_321_);
v_fst_323_ = lean_ctor_get(v___x_322_, 0);
v_snd_324_ = lean_ctor_get(v___x_322_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_362_ == 0)
{
v___x_326_ = v___x_322_;
v_isShared_327_ = v_isSharedCheck_362_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_snd_324_);
lean_inc(v_fst_323_);
lean_dec(v___x_322_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_362_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = lean_nat_dec_eq(v_fst_323_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v_array_330_; lean_object* v_idx_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
lean_dec_ref(v_a_300_);
v_array_330_ = lean_ctor_get(v_snd_324_, 0);
v_idx_331_ = lean_ctor_get(v_snd_324_, 1);
v___x_332_ = lean_byte_array_size(v_array_330_);
v___x_333_ = lean_nat_dec_lt(v_idx_331_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_336_; 
lean_dec(v_fst_323_);
v___x_334_ = lean_box(0);
if (v_isShared_327_ == 0)
{
lean_ctor_set_tag(v___x_326_, 1);
lean_ctor_set(v___x_326_, 1, v___x_334_);
lean_ctor_set(v___x_326_, 0, v_snd_324_);
v___x_336_ = v___x_326_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_snd_324_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v___x_334_);
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
uint8_t v___x_338_; uint8_t v_got_339_; uint8_t v___x_340_; 
v___x_338_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
v_got_339_ = lean_byte_array_fget(v_array_330_, v_idx_331_);
v___x_340_ = lean_uint8_dec_eq(v_got_339_, v___x_338_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; lean_object* v___x_343_; 
lean_dec(v_fst_323_);
v___x_341_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
if (v_isShared_327_ == 0)
{
lean_ctor_set_tag(v___x_326_, 1);
lean_ctor_set(v___x_326_, 1, v___x_341_);
lean_ctor_set(v___x_326_, 0, v_snd_324_);
v___x_343_ = v___x_326_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_snd_324_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
else
{
lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_355_; 
lean_inc(v_idx_331_);
lean_inc_ref(v_array_330_);
v_isSharedCheck_355_ = !lean_is_exclusive(v_snd_324_);
if (v_isSharedCheck_355_ == 0)
{
lean_object* v_unused_356_; lean_object* v_unused_357_; 
v_unused_356_ = lean_ctor_get(v_snd_324_, 1);
lean_dec(v_unused_356_);
v_unused_357_ = lean_ctor_get(v_snd_324_, 0);
lean_dec(v_unused_357_);
v___x_346_ = v_snd_324_;
v_isShared_347_ = v_isSharedCheck_355_;
goto v_resetjp_345_;
}
else
{
lean_dec(v_snd_324_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_355_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_348_ = lean_nat_add(v_idx_331_, v___x_315_);
lean_dec(v_idx_331_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v___x_348_);
v___x_350_ = v___x_346_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_array_330_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v___x_348_);
v___x_350_ = v_reuseFailAlloc_354_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_352_; 
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 1, v_fst_323_);
lean_ctor_set(v___x_326_, 0, v___x_350_);
v___x_352_ = v___x_326_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_fst_323_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
}
else
{
lean_object* v___x_358_; lean_object* v___x_360_; 
lean_dec(v_snd_324_);
lean_dec(v_fst_323_);
v___x_358_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
if (v_isShared_327_ == 0)
{
lean_ctor_set_tag(v___x_326_, 1);
lean_ctor_set(v___x_326_, 1, v___x_358_);
lean_ctor_set(v___x_326_, 0, v_a_300_);
v___x_360_ = v___x_326_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_300_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
}
v___jp_301_:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_303_, 0, v_a_300_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_spec__0(lean_object* v_acc_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_array_365_; lean_object* v_idx_366_; lean_object* v_pos_368_; lean_object* v_idx_369_; lean_object* v_err_370_; lean_object* v___x_376_; uint8_t v___x_377_; 
v_array_365_ = lean_ctor_get(v_a_364_, 0);
v_idx_366_ = lean_ctor_get(v_a_364_, 1);
lean_inc(v_idx_366_);
v___x_376_ = lean_byte_array_size(v_array_365_);
v___x_377_ = lean_nat_dec_lt(v_idx_366_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
v___x_378_ = lean_box(0);
lean_inc(v_idx_366_);
v_pos_368_ = v_a_364_;
v_idx_369_ = v_idx_366_;
v_err_370_ = v___x_378_;
goto v___jp_367_;
}
else
{
uint8_t v_c_379_; uint8_t v___x_380_; uint8_t v___x_381_; 
v_c_379_ = lean_byte_array_fget(v_array_365_, v_idx_366_);
v___x_380_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
v___x_381_ = lean_uint8_dec_le(v___x_380_, v_c_379_);
if (v___x_381_ == 0)
{
goto v___jp_374_;
}
else
{
uint8_t v___x_382_; uint8_t v___x_383_; 
v___x_382_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
v___x_383_ = lean_uint8_dec_le(v_c_379_, v___x_382_);
if (v___x_383_ == 0)
{
goto v___jp_374_;
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v_it_x27_386_; uint32_t v___x_387_; uint8_t v___x_388_; uint8_t v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v_fst_392_; lean_object* v_snd_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_384_ = lean_unsigned_to_nat(1u);
v___x_385_ = lean_nat_add(v_idx_366_, v___x_384_);
lean_inc_ref(v_array_365_);
v_it_x27_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_386_, 0, v_array_365_);
lean_ctor_set(v_it_x27_386_, 1, v___x_385_);
v___x_387_ = lean_uint8_to_uint32(v_c_379_);
v___x_388_ = lean_uint32_to_uint8(v___x_387_);
v___x_389_ = lean_uint8_sub(v___x_388_, v___x_380_);
v___x_390_ = lean_uint8_to_nat(v___x_389_);
v___x_391_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_386_, v___x_390_);
v_fst_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_fst_392_);
v_snd_393_ = lean_ctor_get(v___x_391_, 1);
lean_inc(v_snd_393_);
lean_dec_ref(v___x_391_);
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = lean_nat_dec_eq(v_fst_392_, v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v_array_396_; lean_object* v_idx_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
lean_dec_ref(v_a_364_);
v_array_396_ = lean_ctor_get(v_snd_393_, 0);
v_idx_397_ = lean_ctor_get(v_snd_393_, 1);
lean_inc(v_idx_397_);
v___x_398_ = lean_byte_array_size(v_array_396_);
v___x_399_ = lean_nat_dec_lt(v_idx_397_, v___x_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; 
lean_dec(v_fst_392_);
v___x_400_ = lean_box(0);
v_pos_368_ = v_snd_393_;
v_idx_369_ = v_idx_397_;
v_err_370_ = v___x_400_;
goto v___jp_367_;
}
else
{
uint8_t v___x_401_; uint8_t v_got_402_; uint8_t v___x_403_; 
v___x_401_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
v_got_402_ = lean_byte_array_fget(v_array_396_, v_idx_397_);
v___x_403_ = lean_uint8_dec_eq(v_got_402_, v___x_401_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; 
lean_dec(v_fst_392_);
v___x_404_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
v_pos_368_ = v_snd_393_;
v_idx_369_ = v_idx_397_;
v_err_370_ = v___x_404_;
goto v___jp_367_;
}
else
{
lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_414_; 
lean_inc_ref(v_array_396_);
lean_dec(v_idx_366_);
v_isSharedCheck_414_ = !lean_is_exclusive(v_snd_393_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; lean_object* v_unused_416_; 
v_unused_415_ = lean_ctor_get(v_snd_393_, 1);
lean_dec(v_unused_415_);
v_unused_416_ = lean_ctor_get(v_snd_393_, 0);
lean_dec(v_unused_416_);
v___x_406_ = v_snd_393_;
v_isShared_407_ = v_isSharedCheck_414_;
goto v_resetjp_405_;
}
else
{
lean_dec(v_snd_393_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_414_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_nat_add(v_idx_397_, v___x_384_);
lean_dec(v_idx_397_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v___x_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_array_396_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v___x_408_);
v___x_410_ = v_reuseFailAlloc_413_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; 
v___x_411_ = lean_array_push(v_acc_363_, v_fst_392_);
v_acc_363_ = v___x_411_;
v_a_364_ = v___x_410_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_417_; 
lean_dec(v_snd_393_);
lean_dec(v_fst_392_);
v___x_417_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
lean_inc(v_idx_366_);
v_pos_368_ = v_a_364_;
v_idx_369_ = v_idx_366_;
v_err_370_ = v___x_417_;
goto v___jp_367_;
}
}
}
}
v___jp_367_:
{
uint8_t v___x_371_; 
v___x_371_ = lean_nat_dec_eq(v_idx_366_, v_idx_369_);
lean_dec(v_idx_369_);
lean_dec(v_idx_366_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; 
lean_dec_ref(v_acc_363_);
lean_inc(v_err_370_);
v___x_372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_372_, 0, v_pos_368_);
lean_ctor_set(v___x_372_, 1, v_err_370_);
return v___x_372_;
}
else
{
lean_object* v___x_373_; 
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v_pos_368_);
lean_ctor_set(v___x_373_, 1, v_acc_363_);
return v___x_373_;
}
}
v___jp_374_:
{
lean_object* v___x_375_; 
v___x_375_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
lean_inc(v_idx_366_);
v_pos_368_ = v_a_364_;
v_idx_369_ = v_idx_366_;
v_err_370_ = v___x_375_;
goto v___jp_367_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(lean_object* v_a_420_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0));
v___x_422_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_spec__0(v___x_421_, v_a_420_);
return v___x_422_;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0(void){
_start:
{
uint32_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = 100;
v___x_424_ = lean_uint32_to_uint8(v___x_423_);
return v___x_424_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1(void){
_start:
{
uint8_t v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
v___x_426_ = lean_uint8_to_nat(v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1);
v___x_428_ = l_Nat_reprFast(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2);
v___x_430_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
v___x_431_ = lean_string_append(v___x_430_, v___x_429_);
return v___x_431_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7));
v___x_433_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3);
v___x_434_ = lean_string_append(v___x_433_, v___x_432_);
return v___x_434_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4);
v___x_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(lean_object* v_a_437_){
_start:
{
lean_object* v_array_438_; lean_object* v_idx_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v_array_438_ = lean_ctor_get(v_a_437_, 0);
v_idx_439_ = lean_ctor_get(v_a_437_, 1);
v___x_440_ = lean_byte_array_size(v_array_438_);
v___x_441_ = lean_nat_dec_lt(v_idx_439_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_box(0);
v___x_443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_443_, 0, v_a_437_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
return v___x_443_;
}
else
{
uint8_t v___x_444_; uint8_t v_got_445_; uint8_t v___x_446_; 
v___x_444_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
v_got_445_ = lean_byte_array_fget(v_array_438_, v_idx_439_);
v___x_446_ = lean_uint8_dec_eq(v_got_445_, v___x_444_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5);
v___x_448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_448_, 0, v_a_437_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
return v___x_448_;
}
else
{
lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_512_; 
lean_inc(v_idx_439_);
lean_inc_ref(v_array_438_);
v_isSharedCheck_512_ = !lean_is_exclusive(v_a_437_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; lean_object* v_unused_514_; 
v_unused_513_ = lean_ctor_get(v_a_437_, 1);
lean_dec(v_unused_513_);
v_unused_514_ = lean_ctor_get(v_a_437_, 0);
lean_dec(v_unused_514_);
v___x_450_ = v_a_437_;
v_isShared_451_ = v_isSharedCheck_512_;
goto v_resetjp_449_;
}
else
{
lean_dec(v_a_437_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_512_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_452_ = lean_unsigned_to_nat(1u);
v___x_453_ = lean_nat_add(v_idx_439_, v___x_452_);
lean_dec(v_idx_439_);
lean_inc(v___x_453_);
lean_inc_ref(v_array_438_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v___x_453_);
v___x_455_ = v___x_450_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_array_438_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v___x_453_);
v___x_455_ = v_reuseFailAlloc_511_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
uint8_t v___x_456_; 
v___x_456_ = lean_nat_dec_lt(v___x_453_, v___x_440_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec(v___x_453_);
lean_dec_ref(v_array_438_);
v___x_457_ = lean_box(0);
v___x_458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_455_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
return v___x_458_;
}
else
{
uint8_t v___x_459_; uint8_t v_got_460_; uint8_t v___x_461_; 
v___x_459_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
v_got_460_ = lean_byte_array_fget(v_array_438_, v___x_453_);
v___x_461_ = lean_uint8_dec_eq(v_got_460_, v___x_459_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec(v___x_453_);
lean_dec_ref(v_array_438_);
v___x_462_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
v___x_463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_455_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
return v___x_463_;
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec_ref(v___x_455_);
v___x_464_ = lean_nat_add(v___x_453_, v___x_452_);
lean_dec(v___x_453_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v_array_438_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(v___x_465_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_pos_467_; lean_object* v_res_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_501_; 
v_pos_467_ = lean_ctor_get(v___x_466_, 0);
v_res_468_ = lean_ctor_get(v___x_466_, 1);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_501_ == 0)
{
v___x_470_ = v___x_466_;
v_isShared_471_ = v_isSharedCheck_501_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_res_468_);
lean_inc(v_pos_467_);
lean_dec(v___x_466_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_501_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v_array_472_; lean_object* v_idx_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v_array_472_ = lean_ctor_get(v_pos_467_, 0);
v_idx_473_ = lean_ctor_get(v_pos_467_, 1);
v___x_474_ = lean_byte_array_size(v_array_472_);
v___x_475_ = lean_nat_dec_lt(v_idx_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_478_; 
lean_dec(v_res_468_);
v___x_476_ = lean_box(0);
if (v_isShared_471_ == 0)
{
lean_ctor_set_tag(v___x_470_, 1);
lean_ctor_set(v___x_470_, 1, v___x_476_);
v___x_478_ = v___x_470_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_pos_467_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
else
{
uint8_t v___x_480_; uint8_t v_got_481_; uint8_t v___x_482_; 
v___x_480_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
v_got_481_ = lean_byte_array_fget(v_array_472_, v_idx_473_);
v___x_482_ = lean_uint8_dec_eq(v_got_481_, v___x_480_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_dec(v_res_468_);
v___x_483_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4);
if (v_isShared_471_ == 0)
{
lean_ctor_set_tag(v___x_470_, 1);
lean_ctor_set(v___x_470_, 1, v___x_483_);
v___x_485_ = v___x_470_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_pos_467_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
else
{
lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_498_; 
lean_inc(v_idx_473_);
lean_inc_ref(v_array_472_);
v_isSharedCheck_498_ = !lean_is_exclusive(v_pos_467_);
if (v_isSharedCheck_498_ == 0)
{
lean_object* v_unused_499_; lean_object* v_unused_500_; 
v_unused_499_ = lean_ctor_get(v_pos_467_, 1);
lean_dec(v_unused_499_);
v_unused_500_ = lean_ctor_get(v_pos_467_, 0);
lean_dec(v_unused_500_);
v___x_488_ = v_pos_467_;
v_isShared_489_ = v_isSharedCheck_498_;
goto v_resetjp_487_;
}
else
{
lean_dec(v_pos_467_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_498_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_490_ = lean_nat_add(v_idx_473_, v___x_452_);
lean_dec(v_idx_473_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v___x_490_);
v___x_492_ = v___x_488_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_array_472_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v___x_490_);
v___x_492_ = v_reuseFailAlloc_497_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_493_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_493_, 0, v_res_468_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 1, v___x_493_);
lean_ctor_set(v___x_470_, 0, v___x_492_);
v___x_495_ = v___x_470_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_502_; lean_object* v_err_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
v_pos_502_ = lean_ctor_get(v___x_466_, 0);
v_err_503_ = lean_ctor_get(v___x_466_, 1);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_466_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_err_503_);
lean_inc(v_pos_502_);
lean_dec(v___x_466_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_pos_502_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_err_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseLit(lean_object* v_a_515_){
_start:
{
lean_object* v_array_519_; lean_object* v_idx_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v_array_519_ = lean_ctor_get(v_a_515_, 0);
v_idx_520_ = lean_ctor_get(v_a_515_, 1);
v___x_521_ = lean_byte_array_size(v_array_519_);
v___x_522_ = lean_nat_dec_lt(v_idx_520_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_box(0);
v___x_524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_524_, 0, v_a_515_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
return v___x_524_;
}
else
{
uint8_t v___x_525_; uint8_t v___x_526_; uint8_t v___x_527_; 
v___x_525_ = lean_byte_array_fget(v_array_519_, v_idx_520_);
v___x_526_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0);
v___x_527_ = lean_uint8_dec_eq(v___x_525_, v___x_526_);
if (v___x_527_ == 0)
{
if (v___x_522_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_box(0);
v___x_529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_529_, 0, v_a_515_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
return v___x_529_;
}
else
{
uint8_t v___x_530_; uint8_t v___x_531_; 
v___x_530_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
v___x_531_ = lean_uint8_dec_le(v___x_530_, v___x_525_);
if (v___x_531_ == 0)
{
goto v___jp_516_;
}
else
{
uint8_t v___x_532_; uint8_t v___x_533_; 
v___x_532_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
v___x_533_ = lean_uint8_dec_le(v___x_525_, v___x_532_);
if (v___x_533_ == 0)
{
goto v___jp_516_;
}
else
{
lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_563_; 
lean_inc(v_idx_520_);
lean_inc_ref(v_array_519_);
v_isSharedCheck_563_ = !lean_is_exclusive(v_a_515_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; lean_object* v_unused_565_; 
v_unused_564_ = lean_ctor_get(v_a_515_, 1);
lean_dec(v_unused_564_);
v_unused_565_ = lean_ctor_get(v_a_515_, 0);
lean_dec(v_unused_565_);
v___x_535_ = v_a_515_;
v_isShared_536_ = v_isSharedCheck_563_;
goto v_resetjp_534_;
}
else
{
lean_dec(v_a_515_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_563_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v_it_x27_540_; 
v___x_537_ = lean_unsigned_to_nat(1u);
v___x_538_ = lean_nat_add(v_idx_520_, v___x_537_);
lean_dec(v_idx_520_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 1, v___x_538_);
v_it_x27_540_ = v___x_535_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_array_519_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_538_);
v_it_x27_540_ = v_reuseFailAlloc_562_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
uint32_t v___x_541_; uint8_t v___x_542_; uint8_t v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v_fst_546_; lean_object* v_snd_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_561_; 
v___x_541_ = lean_uint8_to_uint32(v___x_525_);
v___x_542_ = lean_uint32_to_uint8(v___x_541_);
v___x_543_ = lean_uint8_sub(v___x_542_, v___x_530_);
v___x_544_ = lean_uint8_to_nat(v___x_543_);
v___x_545_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_540_, v___x_544_);
v_fst_546_ = lean_ctor_get(v___x_545_, 0);
v_snd_547_ = lean_ctor_get(v___x_545_, 1);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_561_ == 0)
{
v___x_549_ = v___x_545_;
v_isShared_550_ = v_isSharedCheck_561_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_snd_547_);
lean_inc(v_fst_546_);
lean_dec(v___x_545_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_561_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_551_ = lean_unsigned_to_nat(0u);
v___x_552_ = lean_nat_dec_eq(v_fst_546_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = lean_nat_to_int(v_fst_546_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 1, v___x_553_);
lean_ctor_set(v___x_549_, 0, v_snd_547_);
v___x_555_ = v___x_549_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_snd_547_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
else
{
lean_object* v___x_557_; lean_object* v___x_559_; 
lean_dec(v_fst_546_);
v___x_557_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 1);
lean_ctor_set(v___x_549_, 1, v___x_557_);
lean_ctor_set(v___x_549_, 0, v_snd_547_);
v___x_559_ = v___x_549_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_snd_547_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
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
if (v___x_522_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_box(0);
v___x_567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_567_, 0, v_a_515_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
return v___x_567_;
}
else
{
if (v___x_527_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
v___x_569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_569_, 0, v_a_515_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
return v___x_569_;
}
else
{
lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_613_; 
lean_inc(v_idx_520_);
lean_inc_ref(v_array_519_);
v_isSharedCheck_613_ = !lean_is_exclusive(v_a_515_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; lean_object* v_unused_615_; 
v_unused_614_ = lean_ctor_get(v_a_515_, 1);
lean_dec(v_unused_614_);
v_unused_615_ = lean_ctor_get(v_a_515_, 0);
lean_dec(v_unused_615_);
v___x_571_ = v_a_515_;
v_isShared_572_ = v_isSharedCheck_613_;
goto v_resetjp_570_;
}
else
{
lean_dec(v_a_515_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_613_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_573_ = lean_unsigned_to_nat(1u);
v___x_574_ = lean_nat_add(v_idx_520_, v___x_573_);
lean_dec(v_idx_520_);
lean_inc(v___x_574_);
lean_inc_ref(v_array_519_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 1, v___x_574_);
v___x_576_ = v___x_571_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_array_519_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v___x_574_);
v___x_576_ = v_reuseFailAlloc_612_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
uint8_t v___x_580_; 
v___x_580_ = lean_nat_dec_lt(v___x_574_, v___x_521_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; 
lean_dec(v___x_574_);
lean_dec_ref(v_array_519_);
v___x_581_ = lean_box(0);
v___x_582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_576_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
return v___x_582_;
}
else
{
uint8_t v_c_583_; uint8_t v___x_584_; uint8_t v___x_585_; 
v_c_583_ = lean_byte_array_fget(v_array_519_, v___x_574_);
v___x_584_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
v___x_585_ = lean_uint8_dec_le(v___x_584_, v_c_583_);
if (v___x_585_ == 0)
{
lean_dec(v___x_574_);
lean_dec_ref(v_array_519_);
goto v___jp_577_;
}
else
{
uint8_t v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
v___x_587_ = lean_uint8_dec_le(v_c_583_, v___x_586_);
if (v___x_587_ == 0)
{
lean_dec(v___x_574_);
lean_dec_ref(v_array_519_);
goto v___jp_577_;
}
else
{
lean_object* v___x_588_; lean_object* v_it_x27_589_; uint32_t v___x_590_; uint8_t v___x_591_; uint8_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v_fst_595_; lean_object* v_snd_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_611_; 
lean_dec_ref(v___x_576_);
v___x_588_ = lean_nat_add(v___x_574_, v___x_573_);
lean_dec(v___x_574_);
v_it_x27_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_589_, 0, v_array_519_);
lean_ctor_set(v_it_x27_589_, 1, v___x_588_);
v___x_590_ = lean_uint8_to_uint32(v_c_583_);
v___x_591_ = lean_uint32_to_uint8(v___x_590_);
v___x_592_ = lean_uint8_sub(v___x_591_, v___x_584_);
v___x_593_ = lean_uint8_to_nat(v___x_592_);
v___x_594_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_589_, v___x_593_);
v_fst_595_ = lean_ctor_get(v___x_594_, 0);
v_snd_596_ = lean_ctor_get(v___x_594_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_611_ == 0)
{
v___x_598_ = v___x_594_;
v_isShared_599_ = v_isSharedCheck_611_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_snd_596_);
lean_inc(v_fst_595_);
lean_dec(v___x_594_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_611_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = lean_nat_dec_eq(v_fst_595_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_602_ = lean_nat_to_int(v_fst_595_);
v___x_603_ = lean_int_neg(v___x_602_);
lean_dec(v___x_602_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 1, v___x_603_);
lean_ctor_set(v___x_598_, 0, v_snd_596_);
v___x_605_ = v___x_598_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_snd_596_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v___x_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
else
{
lean_object* v___x_607_; lean_object* v___x_609_; 
lean_dec(v_fst_595_);
v___x_607_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
if (v_isShared_599_ == 0)
{
lean_ctor_set_tag(v___x_598_, 1);
lean_ctor_set(v___x_598_, 1, v___x_607_);
lean_ctor_set(v___x_598_, 0, v_snd_596_);
v___x_609_ = v___x_598_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_snd_596_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
v___jp_577_:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_576_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
return v___x_579_;
}
}
}
}
}
}
}
v___jp_516_:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_518_, 0, v_a_515_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_litWs(lean_object* v_a_616_){
_start:
{
lean_object* v_pos_618_; lean_object* v_res_619_; lean_object* v_array_649_; lean_object* v_idx_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v_array_649_ = lean_ctor_get(v_a_616_, 0);
v_idx_650_ = lean_ctor_get(v_a_616_, 1);
v___x_651_ = lean_byte_array_size(v_array_649_);
v___x_652_ = lean_nat_dec_lt(v_idx_650_, v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_box(0);
v___x_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_654_, 0, v_a_616_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
return v___x_654_;
}
else
{
uint8_t v___x_655_; uint8_t v___x_656_; uint8_t v___x_657_; 
v___x_655_ = lean_byte_array_fget(v_array_649_, v_idx_650_);
v___x_656_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0);
v___x_657_ = lean_uint8_dec_eq(v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
if (v___x_652_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_box(0);
v___x_659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_659_, 0, v_a_616_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
return v___x_659_;
}
else
{
uint8_t v___x_660_; uint8_t v___x_661_; 
v___x_660_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
v___x_661_ = lean_uint8_dec_le(v___x_660_, v___x_655_);
if (v___x_661_ == 0)
{
goto v___jp_643_;
}
else
{
uint8_t v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
v___x_663_ = lean_uint8_dec_le(v___x_655_, v___x_662_);
if (v___x_663_ == 0)
{
goto v___jp_643_;
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v_it_x27_666_; uint32_t v___x_667_; uint8_t v___x_668_; uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v_fst_672_; lean_object* v_snd_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_684_; 
v___x_664_ = lean_unsigned_to_nat(1u);
v___x_665_ = lean_nat_add(v_idx_650_, v___x_664_);
lean_inc_ref(v_array_649_);
v_it_x27_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_666_, 0, v_array_649_);
lean_ctor_set(v_it_x27_666_, 1, v___x_665_);
v___x_667_ = lean_uint8_to_uint32(v___x_655_);
v___x_668_ = lean_uint32_to_uint8(v___x_667_);
v___x_669_ = lean_uint8_sub(v___x_668_, v___x_660_);
v___x_670_ = lean_uint8_to_nat(v___x_669_);
v___x_671_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_666_, v___x_670_);
v_fst_672_ = lean_ctor_get(v___x_671_, 0);
v_snd_673_ = lean_ctor_get(v___x_671_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_684_ == 0)
{
v___x_675_ = v___x_671_;
v_isShared_676_ = v_isSharedCheck_684_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_snd_673_);
lean_inc(v_fst_672_);
lean_dec(v___x_671_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_684_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_677_ = lean_unsigned_to_nat(0u);
v___x_678_ = lean_nat_dec_eq(v_fst_672_, v___x_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
lean_del_object(v___x_675_);
lean_dec_ref(v_a_616_);
v___x_679_ = lean_nat_to_int(v_fst_672_);
v_pos_618_ = v_snd_673_;
v_res_619_ = v___x_679_;
goto v___jp_617_;
}
else
{
lean_object* v___x_680_; lean_object* v___x_682_; 
lean_dec(v_snd_673_);
lean_dec(v_fst_672_);
v___x_680_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
if (v_isShared_676_ == 0)
{
lean_ctor_set_tag(v___x_675_, 1);
lean_ctor_set(v___x_675_, 1, v___x_680_);
lean_ctor_set(v___x_675_, 0, v_a_616_);
v___x_682_ = v___x_675_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_616_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
}
}
else
{
if (v___x_652_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_box(0);
v___x_686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_686_, 0, v_a_616_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
return v___x_686_;
}
else
{
if (v___x_657_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
v___x_688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_688_, 0, v_a_616_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
return v___x_688_;
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_689_ = lean_unsigned_to_nat(1u);
v___x_690_ = lean_nat_add(v_idx_650_, v___x_689_);
v___x_691_ = lean_nat_dec_lt(v___x_690_, v___x_651_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; 
lean_dec(v___x_690_);
v___x_692_ = lean_box(0);
v___x_693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_693_, 0, v_a_616_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
return v___x_693_;
}
else
{
uint8_t v_c_694_; uint8_t v___x_695_; uint8_t v___x_696_; 
v_c_694_ = lean_byte_array_fget(v_array_649_, v___x_690_);
v___x_695_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
v___x_696_ = lean_uint8_dec_le(v___x_695_, v_c_694_);
if (v___x_696_ == 0)
{
lean_dec(v___x_690_);
goto v___jp_646_;
}
else
{
uint8_t v___x_697_; uint8_t v___x_698_; 
v___x_697_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
v___x_698_ = lean_uint8_dec_le(v_c_694_, v___x_697_);
if (v___x_698_ == 0)
{
lean_dec(v___x_690_);
goto v___jp_646_;
}
else
{
lean_object* v___x_699_; lean_object* v_it_x27_700_; uint32_t v___x_701_; uint8_t v___x_702_; uint8_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v_fst_706_; lean_object* v_snd_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_719_; 
v___x_699_ = lean_nat_add(v___x_690_, v___x_689_);
lean_dec(v___x_690_);
lean_inc_ref(v_array_649_);
v_it_x27_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_700_, 0, v_array_649_);
lean_ctor_set(v_it_x27_700_, 1, v___x_699_);
v___x_701_ = lean_uint8_to_uint32(v_c_694_);
v___x_702_ = lean_uint32_to_uint8(v___x_701_);
v___x_703_ = lean_uint8_sub(v___x_702_, v___x_695_);
v___x_704_ = lean_uint8_to_nat(v___x_703_);
v___x_705_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_700_, v___x_704_);
v_fst_706_ = lean_ctor_get(v___x_705_, 0);
v_snd_707_ = lean_ctor_get(v___x_705_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_719_ == 0)
{
v___x_709_ = v___x_705_;
v_isShared_710_ = v_isSharedCheck_719_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_snd_707_);
lean_inc(v_fst_706_);
lean_dec(v___x_705_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_719_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_711_ = lean_unsigned_to_nat(0u);
v___x_712_ = lean_nat_dec_eq(v_fst_706_, v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; 
lean_del_object(v___x_709_);
lean_dec_ref(v_a_616_);
v___x_713_ = lean_nat_to_int(v_fst_706_);
v___x_714_ = lean_int_neg(v___x_713_);
lean_dec(v___x_713_);
v_pos_618_ = v_snd_707_;
v_res_619_ = v___x_714_;
goto v___jp_617_;
}
else
{
lean_object* v___x_715_; lean_object* v___x_717_; 
lean_dec(v_snd_707_);
lean_dec(v_fst_706_);
v___x_715_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
if (v_isShared_710_ == 0)
{
lean_ctor_set_tag(v___x_709_, 1);
lean_ctor_set(v___x_709_, 1, v___x_715_);
lean_ctor_set(v___x_709_, 0, v_a_616_);
v___x_717_ = v___x_709_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_616_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
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
v___jp_617_:
{
lean_object* v_array_620_; lean_object* v_idx_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v_array_620_ = lean_ctor_get(v_pos_618_, 0);
v_idx_621_ = lean_ctor_get(v_pos_618_, 1);
v___x_622_ = lean_byte_array_size(v_array_620_);
v___x_623_ = lean_nat_dec_lt(v_idx_621_, v___x_622_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec(v_res_619_);
v___x_624_ = lean_box(0);
v___x_625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_625_, 0, v_pos_618_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
return v___x_625_;
}
else
{
uint8_t v___x_626_; uint8_t v_got_627_; uint8_t v___x_628_; 
v___x_626_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
v_got_627_ = lean_byte_array_fget(v_array_620_, v_idx_621_);
v___x_628_ = lean_uint8_dec_eq(v_got_627_, v___x_626_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec(v_res_619_);
v___x_629_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
v___x_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_630_, 0, v_pos_618_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
return v___x_630_;
}
else
{
lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_640_; 
lean_inc(v_idx_621_);
lean_inc_ref(v_array_620_);
v_isSharedCheck_640_ = !lean_is_exclusive(v_pos_618_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; lean_object* v_unused_642_; 
v_unused_641_ = lean_ctor_get(v_pos_618_, 1);
lean_dec(v_unused_641_);
v_unused_642_ = lean_ctor_get(v_pos_618_, 0);
lean_dec(v_unused_642_);
v___x_632_ = v_pos_618_;
v_isShared_633_ = v_isSharedCheck_640_;
goto v_resetjp_631_;
}
else
{
lean_dec(v_pos_618_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_640_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_634_ = lean_unsigned_to_nat(1u);
v___x_635_ = lean_nat_add(v_idx_621_, v___x_634_);
lean_dec(v_idx_621_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 1, v___x_635_);
v___x_637_ = v___x_632_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_array_620_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___x_635_);
v___x_637_ = v_reuseFailAlloc_639_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; 
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v_res_619_);
return v___x_638_;
}
}
}
}
}
v___jp_643_:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_645_, 0, v_a_616_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
return v___x_645_;
}
v___jp_646_:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_648_, 0, v_a_616_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__0(lean_object* v_a_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = lean_nat_to_int(v_a_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__1(lean_object* v_acc_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_array_724_; lean_object* v_idx_725_; lean_object* v_pos_727_; lean_object* v_idx_728_; lean_object* v_err_729_; lean_object* v_pos_738_; lean_object* v_res_739_; lean_object* v___x_762_; uint8_t v___x_763_; 
v_array_724_ = lean_ctor_get(v_a_723_, 0);
v_idx_725_ = lean_ctor_get(v_a_723_, 1);
lean_inc(v_idx_725_);
v___x_762_ = lean_byte_array_size(v_array_724_);
v___x_763_ = lean_nat_dec_lt(v_idx_725_, v___x_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; 
v___x_764_ = lean_box(0);
lean_inc(v_idx_725_);
v_pos_727_ = v_a_723_;
v_idx_728_ = v_idx_725_;
v_err_729_ = v___x_764_;
goto v___jp_726_;
}
else
{
uint8_t v___x_765_; uint8_t v___x_766_; uint8_t v___x_767_; 
v___x_765_ = lean_byte_array_fget(v_array_724_, v_idx_725_);
v___x_766_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0);
v___x_767_ = lean_uint8_dec_eq(v___x_765_, v___x_766_);
if (v___x_767_ == 0)
{
if (v___x_763_ == 0)
{
lean_object* v___x_768_; 
v___x_768_ = lean_box(0);
lean_inc(v_idx_725_);
v_pos_727_ = v_a_723_;
v_idx_728_ = v_idx_725_;
v_err_729_ = v___x_768_;
goto v___jp_726_;
}
else
{
uint8_t v___x_769_; uint8_t v___x_770_; 
v___x_769_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
v___x_770_ = lean_uint8_dec_le(v___x_769_, v___x_765_);
if (v___x_770_ == 0)
{
goto v___jp_735_;
}
else
{
uint8_t v___x_771_; uint8_t v___x_772_; 
v___x_771_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
v___x_772_ = lean_uint8_dec_le(v___x_765_, v___x_771_);
if (v___x_772_ == 0)
{
goto v___jp_735_;
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v_it_x27_775_; uint32_t v___x_776_; uint8_t v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v_fst_781_; lean_object* v_snd_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_773_ = lean_unsigned_to_nat(1u);
v___x_774_ = lean_nat_add(v_idx_725_, v___x_773_);
lean_inc_ref(v_array_724_);
v_it_x27_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_775_, 0, v_array_724_);
lean_ctor_set(v_it_x27_775_, 1, v___x_774_);
v___x_776_ = lean_uint8_to_uint32(v___x_765_);
v___x_777_ = lean_uint32_to_uint8(v___x_776_);
v___x_778_ = lean_uint8_sub(v___x_777_, v___x_769_);
v___x_779_ = lean_uint8_to_nat(v___x_778_);
v___x_780_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_775_, v___x_779_);
v_fst_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_fst_781_);
v_snd_782_ = lean_ctor_get(v___x_780_, 1);
lean_inc(v_snd_782_);
lean_dec_ref(v___x_780_);
v___x_783_ = lean_unsigned_to_nat(0u);
v___x_784_ = lean_nat_dec_eq(v_fst_781_, v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_dec_ref(v_a_723_);
v___x_785_ = lean_nat_to_int(v_fst_781_);
v_pos_738_ = v_snd_782_;
v_res_739_ = v___x_785_;
goto v___jp_737_;
}
else
{
lean_object* v___x_786_; 
lean_dec(v_snd_782_);
lean_dec(v_fst_781_);
v___x_786_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
lean_inc(v_idx_725_);
v_pos_727_ = v_a_723_;
v_idx_728_ = v_idx_725_;
v_err_729_ = v___x_786_;
goto v___jp_726_;
}
}
}
}
}
else
{
if (v___x_763_ == 0)
{
lean_object* v___x_787_; 
v___x_787_ = lean_box(0);
lean_inc(v_idx_725_);
v_pos_727_ = v_a_723_;
v_idx_728_ = v_idx_725_;
v_err_729_ = v___x_787_;
goto v___jp_726_;
}
else
{
if (v___x_767_ == 0)
{
lean_object* v___x_788_; 
v___x_788_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
lean_inc(v_idx_725_);
v_pos_727_ = v_a_723_;
v_idx_728_ = v_idx_725_;
v_err_729_ = v___x_788_;
goto v___jp_726_;
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_add(v_idx_725_, v___x_789_);
v___x_791_ = lean_nat_dec_lt(v___x_790_, v___x_762_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; 
lean_dec(v___x_790_);
v___x_792_ = lean_box(0);
lean_inc(v_idx_725_);
v_pos_727_ = v_a_723_;
v_idx_728_ = v_idx_725_;
v_err_729_ = v___x_792_;
goto v___jp_726_;
}
else
{
uint8_t v_c_793_; uint8_t v___x_794_; uint8_t v___x_795_; 
v_c_793_ = lean_byte_array_fget(v_array_724_, v___x_790_);
v___x_794_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
v___x_795_ = lean_uint8_dec_le(v___x_794_, v_c_793_);
if (v___x_795_ == 0)
{
lean_dec(v___x_790_);
goto v___jp_733_;
}
else
{
uint8_t v___x_796_; uint8_t v___x_797_; 
v___x_796_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
v___x_797_ = lean_uint8_dec_le(v_c_793_, v___x_796_);
if (v___x_797_ == 0)
{
lean_dec(v___x_790_);
goto v___jp_733_;
}
else
{
lean_object* v___x_798_; lean_object* v_it_x27_799_; uint32_t v___x_800_; uint8_t v___x_801_; uint8_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v_fst_805_; lean_object* v_snd_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_798_ = lean_nat_add(v___x_790_, v___x_789_);
lean_dec(v___x_790_);
lean_inc_ref(v_array_724_);
v_it_x27_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_799_, 0, v_array_724_);
lean_ctor_set(v_it_x27_799_, 1, v___x_798_);
v___x_800_ = lean_uint8_to_uint32(v_c_793_);
v___x_801_ = lean_uint32_to_uint8(v___x_800_);
v___x_802_ = lean_uint8_sub(v___x_801_, v___x_794_);
v___x_803_ = lean_uint8_to_nat(v___x_802_);
v___x_804_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_799_, v___x_803_);
v_fst_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_fst_805_);
v_snd_806_ = lean_ctor_get(v___x_804_, 1);
lean_inc(v_snd_806_);
lean_dec_ref(v___x_804_);
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = lean_nat_dec_eq(v_fst_805_, v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec_ref(v_a_723_);
v___x_809_ = lean_nat_to_int(v_fst_805_);
v___x_810_ = lean_int_neg(v___x_809_);
lean_dec(v___x_809_);
v_pos_738_ = v_snd_806_;
v_res_739_ = v___x_810_;
goto v___jp_737_;
}
else
{
lean_object* v___x_811_; 
lean_dec(v_snd_806_);
lean_dec(v_fst_805_);
v___x_811_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
lean_inc(v_idx_725_);
v_pos_727_ = v_a_723_;
v_idx_728_ = v_idx_725_;
v_err_729_ = v___x_811_;
goto v___jp_726_;
}
}
}
}
}
}
}
}
v___jp_726_:
{
uint8_t v___x_730_; 
v___x_730_ = lean_nat_dec_eq(v_idx_725_, v_idx_728_);
lean_dec(v_idx_728_);
lean_dec(v_idx_725_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; 
lean_dec_ref(v_acc_722_);
lean_inc(v_err_729_);
v___x_731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_731_, 0, v_pos_727_);
lean_ctor_set(v___x_731_, 1, v_err_729_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; 
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v_pos_727_);
lean_ctor_set(v___x_732_, 1, v_acc_722_);
return v___x_732_;
}
}
v___jp_733_:
{
lean_object* v___x_734_; 
v___x_734_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
lean_inc(v_idx_725_);
v_pos_727_ = v_a_723_;
v_idx_728_ = v_idx_725_;
v_err_729_ = v___x_734_;
goto v___jp_726_;
}
v___jp_735_:
{
lean_object* v___x_736_; 
v___x_736_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
lean_inc(v_idx_725_);
v_pos_727_ = v_a_723_;
v_idx_728_ = v_idx_725_;
v_err_729_ = v___x_736_;
goto v___jp_726_;
}
v___jp_737_:
{
lean_object* v_array_740_; lean_object* v_idx_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v_array_740_ = lean_ctor_get(v_pos_738_, 0);
v_idx_741_ = lean_ctor_get(v_pos_738_, 1);
lean_inc(v_idx_741_);
v___x_742_ = lean_byte_array_size(v_array_740_);
v___x_743_ = lean_nat_dec_lt(v_idx_741_, v___x_742_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; 
lean_dec(v_res_739_);
v___x_744_ = lean_box(0);
v_pos_727_ = v_pos_738_;
v_idx_728_ = v_idx_741_;
v_err_729_ = v___x_744_;
goto v___jp_726_;
}
else
{
uint8_t v___x_745_; uint8_t v_got_746_; uint8_t v___x_747_; 
v___x_745_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
v_got_746_ = lean_byte_array_fget(v_array_740_, v_idx_741_);
v___x_747_ = lean_uint8_dec_eq(v_got_746_, v___x_745_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; 
lean_dec(v_res_739_);
v___x_748_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
v_pos_727_ = v_pos_738_;
v_idx_728_ = v_idx_741_;
v_err_729_ = v___x_748_;
goto v___jp_726_;
}
else
{
lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_759_; 
lean_inc_ref(v_array_740_);
lean_dec(v_idx_725_);
v_isSharedCheck_759_ = !lean_is_exclusive(v_pos_738_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; lean_object* v_unused_761_; 
v_unused_760_ = lean_ctor_get(v_pos_738_, 1);
lean_dec(v_unused_760_);
v_unused_761_ = lean_ctor_get(v_pos_738_, 0);
lean_dec(v_unused_761_);
v___x_750_ = v_pos_738_;
v_isShared_751_ = v_isSharedCheck_759_;
goto v_resetjp_749_;
}
else
{
lean_dec(v_pos_738_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_759_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_752_ = lean_unsigned_to_nat(1u);
v___x_753_ = lean_nat_add(v_idx_741_, v___x_752_);
lean_dec(v_idx_741_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 1, v___x_753_);
v___x_755_ = v___x_750_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_array_740_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v___x_753_);
v___x_755_ = v_reuseFailAlloc_758_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; 
v___x_756_ = lean_array_push(v_acc_722_, v_res_739_);
v_acc_722_ = v___x_756_;
v_a_723_ = v___x_755_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(lean_object* v_a_814_){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0));
v___x_816_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__1(v___x_815_, v_a_814_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_pos_817_; lean_object* v_res_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_851_; 
v_pos_817_ = lean_ctor_get(v___x_816_, 0);
v_res_818_ = lean_ctor_get(v___x_816_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_851_ == 0)
{
v___x_820_ = v___x_816_;
v_isShared_821_ = v_isSharedCheck_851_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_res_818_);
lean_inc(v_pos_817_);
lean_dec(v___x_816_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_851_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v_array_822_; lean_object* v_idx_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v_array_822_ = lean_ctor_get(v_pos_817_, 0);
v_idx_823_ = lean_ctor_get(v_pos_817_, 1);
v___x_824_ = lean_byte_array_size(v_array_822_);
v___x_825_ = lean_nat_dec_lt(v_idx_823_, v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_828_; 
lean_dec(v_res_818_);
v___x_826_ = lean_box(0);
if (v_isShared_821_ == 0)
{
lean_ctor_set_tag(v___x_820_, 1);
lean_ctor_set(v___x_820_, 1, v___x_826_);
v___x_828_ = v___x_820_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_pos_817_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
else
{
uint8_t v___x_830_; uint8_t v_got_831_; uint8_t v___x_832_; 
v___x_830_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
v_got_831_ = lean_byte_array_fget(v_array_822_, v_idx_823_);
v___x_832_ = lean_uint8_dec_eq(v_got_831_, v___x_830_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_835_; 
lean_dec(v_res_818_);
v___x_833_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4);
if (v_isShared_821_ == 0)
{
lean_ctor_set_tag(v___x_820_, 1);
lean_ctor_set(v___x_820_, 1, v___x_833_);
v___x_835_ = v___x_820_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_pos_817_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
else
{
lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_848_; 
lean_inc(v_idx_823_);
lean_inc_ref(v_array_822_);
v_isSharedCheck_848_ = !lean_is_exclusive(v_pos_817_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; lean_object* v_unused_850_; 
v_unused_849_ = lean_ctor_get(v_pos_817_, 1);
lean_dec(v_unused_849_);
v_unused_850_ = lean_ctor_get(v_pos_817_, 0);
lean_dec(v_unused_850_);
v___x_838_ = v_pos_817_;
v_isShared_839_ = v_isSharedCheck_848_;
goto v_resetjp_837_;
}
else
{
lean_dec(v_pos_817_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_848_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_840_ = lean_unsigned_to_nat(1u);
v___x_841_ = lean_nat_add(v_idx_823_, v___x_840_);
lean_dec(v_idx_823_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v___x_841_);
v___x_843_ = v___x_838_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_array_822_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_841_);
v___x_843_ = v_reuseFailAlloc_847_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_845_; 
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_843_);
v___x_845_ = v___x_820_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_res_818_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
}
}
else
{
return v___x_816_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(lean_object* v_a_852_){
_start:
{
lean_object* v_array_853_; lean_object* v_idx_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v_array_853_ = lean_ctor_get(v_a_852_, 0);
v_idx_854_ = lean_ctor_get(v_a_852_, 1);
v___x_855_ = lean_byte_array_size(v_array_853_);
v___x_856_ = lean_nat_dec_lt(v_idx_854_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_box(0);
v___x_858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_858_, 0, v_a_852_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
return v___x_858_;
}
else
{
uint8_t v___x_859_; uint8_t v_got_860_; uint8_t v___x_861_; 
v___x_859_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0);
v_got_860_ = lean_byte_array_fget(v_array_853_, v_idx_854_);
v___x_861_ = lean_uint8_dec_eq(v_got_860_, v___x_859_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
v___x_863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_863_, 0, v_a_852_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
return v___x_863_;
}
else
{
lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_946_; 
lean_inc(v_idx_854_);
lean_inc_ref(v_array_853_);
v_isSharedCheck_946_ = !lean_is_exclusive(v_a_852_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; lean_object* v_unused_948_; 
v_unused_947_ = lean_ctor_get(v_a_852_, 1);
lean_dec(v_unused_947_);
v_unused_948_ = lean_ctor_get(v_a_852_, 0);
lean_dec(v_unused_948_);
v___x_865_ = v_a_852_;
v_isShared_866_ = v_isSharedCheck_946_;
goto v_resetjp_864_;
}
else
{
lean_dec(v_a_852_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_946_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_867_ = lean_unsigned_to_nat(1u);
v___x_868_ = lean_nat_add(v_idx_854_, v___x_867_);
lean_dec(v_idx_854_);
lean_inc(v___x_868_);
lean_inc_ref(v_array_853_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 1, v___x_868_);
v___x_870_ = v___x_865_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_array_853_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v___x_868_);
v___x_870_ = v_reuseFailAlloc_945_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
uint8_t v___x_874_; 
v___x_874_ = lean_nat_dec_lt(v___x_868_, v___x_855_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec(v___x_868_);
lean_dec_ref(v_array_853_);
v___x_875_ = lean_box(0);
v___x_876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_870_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
return v___x_876_;
}
else
{
uint8_t v_c_877_; uint8_t v___x_878_; uint8_t v___x_879_; 
v_c_877_ = lean_byte_array_fget(v_array_853_, v___x_868_);
v___x_878_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
v___x_879_ = lean_uint8_dec_le(v___x_878_, v_c_877_);
if (v___x_879_ == 0)
{
lean_dec(v___x_868_);
lean_dec_ref(v_array_853_);
goto v___jp_871_;
}
else
{
uint8_t v___x_880_; uint8_t v___x_881_; 
v___x_880_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
v___x_881_ = lean_uint8_dec_le(v_c_877_, v___x_880_);
if (v___x_881_ == 0)
{
lean_dec(v___x_868_);
lean_dec_ref(v_array_853_);
goto v___jp_871_;
}
else
{
lean_object* v___x_882_; lean_object* v_it_x27_883_; uint32_t v___x_884_; uint8_t v___x_885_; uint8_t v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v_fst_889_; lean_object* v_snd_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v___x_870_);
v___x_882_ = lean_nat_add(v___x_868_, v___x_867_);
lean_dec(v___x_868_);
v_it_x27_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_883_, 0, v_array_853_);
lean_ctor_set(v_it_x27_883_, 1, v___x_882_);
v___x_884_ = lean_uint8_to_uint32(v_c_877_);
v___x_885_ = lean_uint32_to_uint8(v___x_884_);
v___x_886_ = lean_uint8_sub(v___x_885_, v___x_878_);
v___x_887_ = lean_uint8_to_nat(v___x_886_);
v___x_888_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_883_, v___x_887_);
v_fst_889_ = lean_ctor_get(v___x_888_, 0);
v_snd_890_ = lean_ctor_get(v___x_888_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_944_ == 0)
{
v___x_892_ = v___x_888_;
v_isShared_893_ = v_isSharedCheck_944_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_snd_890_);
lean_inc(v_fst_889_);
lean_dec(v___x_888_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_944_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = lean_nat_dec_eq(v_fst_889_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v_array_896_; lean_object* v_idx_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v_array_896_ = lean_ctor_get(v_snd_890_, 0);
v_idx_897_ = lean_ctor_get(v_snd_890_, 1);
v___x_898_ = lean_byte_array_size(v_array_896_);
v___x_899_ = lean_nat_dec_lt(v_idx_897_, v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; 
lean_del_object(v___x_892_);
lean_dec(v_fst_889_);
v___x_900_ = lean_box(0);
v___x_901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_901_, 0, v_snd_890_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
return v___x_901_;
}
else
{
uint8_t v___x_902_; uint8_t v_got_903_; uint8_t v___x_904_; 
v___x_902_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
v_got_903_ = lean_byte_array_fget(v_array_896_, v_idx_897_);
v___x_904_ = lean_uint8_dec_eq(v_got_903_, v___x_902_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; 
lean_del_object(v___x_892_);
lean_dec(v_fst_889_);
v___x_905_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
v___x_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_906_, 0, v_snd_890_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
return v___x_906_;
}
else
{
lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_939_; 
lean_inc(v_idx_897_);
lean_inc_ref(v_array_896_);
v_isSharedCheck_939_ = !lean_is_exclusive(v_snd_890_);
if (v_isSharedCheck_939_ == 0)
{
lean_object* v_unused_940_; lean_object* v_unused_941_; 
v_unused_940_ = lean_ctor_get(v_snd_890_, 1);
lean_dec(v_unused_940_);
v_unused_941_ = lean_ctor_get(v_snd_890_, 0);
lean_dec(v_unused_941_);
v___x_908_ = v_snd_890_;
v_isShared_909_ = v_isSharedCheck_939_;
goto v_resetjp_907_;
}
else
{
lean_dec(v_snd_890_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_939_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_910_ = lean_nat_add(v_idx_897_, v___x_867_);
lean_dec(v_idx_897_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 1, v___x_910_);
v___x_912_ = v___x_908_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_array_896_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___x_910_);
v___x_912_ = v_reuseFailAlloc_938_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_913_; 
v___x_913_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(v___x_912_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_pos_914_; lean_object* v_res_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_928_; 
v_pos_914_ = lean_ctor_get(v___x_913_, 0);
v_res_915_ = lean_ctor_get(v___x_913_, 1);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_928_ == 0)
{
v___x_917_ = v___x_913_;
v_isShared_918_ = v_isSharedCheck_928_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_res_915_);
lean_inc(v_pos_914_);
lean_dec(v___x_913_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_928_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_919_ = lean_nat_to_int(v_fst_889_);
v___x_920_ = lean_int_neg(v___x_919_);
lean_dec(v___x_919_);
v___x_921_ = lean_nat_abs(v___x_920_);
lean_dec(v___x_920_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 1, v_res_915_);
lean_ctor_set(v___x_892_, 0, v___x_921_);
v___x_923_ = v___x_892_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_res_915_);
v___x_923_ = v_reuseFailAlloc_927_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_925_; 
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 1, v___x_923_);
v___x_925_ = v___x_917_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_pos_914_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v___x_923_);
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
else
{
lean_object* v_pos_929_; lean_object* v_err_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_del_object(v___x_892_);
lean_dec(v_fst_889_);
v_pos_929_ = lean_ctor_get(v___x_913_, 0);
v_err_930_ = lean_ctor_get(v___x_913_, 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_913_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_err_930_);
lean_inc(v_pos_929_);
lean_dec(v___x_913_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_pos_929_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_err_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
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
lean_object* v___x_942_; lean_object* v___x_943_; 
lean_del_object(v___x_892_);
lean_dec(v_fst_889_);
v___x_942_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
v___x_943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_943_, 0, v_snd_890_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
return v___x_943_;
}
}
}
}
}
v___jp_871_:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_870_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
return v___x_873_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(lean_object* v_acc_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_pos_952_; lean_object* v_err_953_; lean_object* v___x_968_; 
lean_inc_ref(v_a_950_);
v___x_968_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(v_a_950_);
if (lean_obj_tag(v___x_968_) == 0)
{
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_pos_969_; lean_object* v_res_970_; lean_object* v___x_971_; 
lean_dec_ref(v_a_950_);
v_pos_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_pos_969_);
v_res_970_ = lean_ctor_get(v___x_968_, 1);
lean_inc(v_res_970_);
lean_dec_ref_known(v___x_968_, 2);
v___x_971_ = lean_array_push(v_acc_949_, v_res_970_);
v_acc_949_ = v___x_971_;
v_a_950_ = v_pos_969_;
goto _start;
}
else
{
lean_object* v_pos_973_; lean_object* v_err_974_; 
v_pos_973_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_pos_973_);
v_err_974_ = lean_ctor_get(v___x_968_, 1);
lean_inc(v_err_974_);
lean_dec_ref_known(v___x_968_, 2);
v_pos_952_ = v_pos_973_;
v_err_953_ = v_err_974_;
goto v___jp_951_;
}
}
else
{
lean_object* v_err_975_; 
v_err_975_ = lean_ctor_get(v___x_968_, 1);
lean_inc(v_err_975_);
lean_dec_ref_known(v___x_968_, 2);
lean_inc_ref(v_a_950_);
v_pos_952_ = v_a_950_;
v_err_953_ = v_err_975_;
goto v___jp_951_;
}
v___jp_951_:
{
lean_object* v_idx_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_966_; 
v_idx_954_ = lean_ctor_get(v_a_950_, 1);
v_isSharedCheck_966_ = !lean_is_exclusive(v_a_950_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; 
v_unused_967_ = lean_ctor_get(v_a_950_, 0);
lean_dec(v_unused_967_);
v___x_956_ = v_a_950_;
v_isShared_957_ = v_isSharedCheck_966_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_idx_954_);
lean_dec(v_a_950_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_966_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v_idx_958_; uint8_t v___x_959_; 
v_idx_958_ = lean_ctor_get(v_pos_952_, 1);
v___x_959_ = lean_nat_dec_eq(v_idx_954_, v_idx_958_);
lean_dec(v_idx_954_);
if (v___x_959_ == 0)
{
lean_object* v___x_961_; 
lean_dec_ref(v_acc_949_);
if (v_isShared_957_ == 0)
{
lean_ctor_set_tag(v___x_956_, 1);
lean_ctor_set(v___x_956_, 1, v_err_953_);
lean_ctor_set(v___x_956_, 0, v_pos_952_);
v___x_961_ = v___x_956_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_pos_952_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_err_953_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
else
{
lean_object* v___x_964_; 
lean_dec(v_err_953_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v_acc_949_);
lean_ctor_set(v___x_956_, 0, v_pos_952_);
v___x_964_ = v___x_956_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_pos_952_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_acc_949_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(lean_object* v_ident_981_, lean_object* v_a_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(v_a_982_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_pos_984_; lean_object* v_res_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1093_; 
v_pos_984_ = lean_ctor_get(v___x_983_, 0);
v_res_985_ = lean_ctor_get(v___x_983_, 1);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_987_ = v___x_983_;
v_isShared_988_ = v_isSharedCheck_1093_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_res_985_);
lean_inc(v_pos_984_);
lean_dec(v___x_983_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1093_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v_array_989_; lean_object* v_idx_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v_array_989_ = lean_ctor_get(v_pos_984_, 0);
v_idx_990_ = lean_ctor_get(v_pos_984_, 1);
v___x_991_ = lean_byte_array_size(v_array_989_);
v___x_992_ = lean_nat_dec_lt(v_idx_990_, v___x_991_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_995_; 
lean_dec(v_res_985_);
lean_dec(v_ident_981_);
v___x_993_ = lean_box(0);
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 1);
lean_ctor_set(v___x_987_, 1, v___x_993_);
v___x_995_ = v___x_987_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_pos_984_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
else
{
uint8_t v___x_997_; uint8_t v_got_998_; uint8_t v___x_999_; 
v___x_997_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
v_got_998_ = lean_byte_array_fget(v_array_989_, v_idx_990_);
v___x_999_ = lean_uint8_dec_eq(v_got_998_, v___x_997_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
lean_dec(v_res_985_);
lean_dec(v_ident_981_);
v___x_1000_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 1);
lean_ctor_set(v___x_987_, 1, v___x_1000_);
v___x_1002_ = v___x_987_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_pos_984_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
else
{
lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1090_; 
lean_inc(v_idx_990_);
lean_inc_ref(v_array_989_);
lean_del_object(v___x_987_);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_pos_984_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; lean_object* v_unused_1092_; 
v_unused_1091_ = lean_ctor_get(v_pos_984_, 1);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v_pos_984_, 0);
lean_dec(v_unused_1092_);
v___x_1005_ = v_pos_984_;
v_isShared_1006_ = v_isSharedCheck_1090_;
goto v_resetjp_1004_;
}
else
{
lean_dec(v_pos_984_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1090_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1007_ = lean_unsigned_to_nat(1u);
v___x_1008_ = lean_nat_add(v_idx_990_, v___x_1007_);
lean_dec(v_idx_990_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 1, v___x_1008_);
v___x_1010_ = v___x_1005_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_array_989_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(v___x_1010_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_pos_1012_; lean_object* v_res_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_pos_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_pos_1012_);
v_res_1013_ = lean_ctor_get(v___x_1011_, 1);
lean_inc(v_res_1013_);
lean_dec_ref_known(v___x_1011_, 2);
v___x_1014_ = lean_unsigned_to_nat(0u);
v___x_1015_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0));
v___x_1016_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(v___x_1015_, v_pos_1012_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_pos_1017_; lean_object* v_res_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1070_; 
v_pos_1017_ = lean_ctor_get(v___x_1016_, 0);
v_res_1018_ = lean_ctor_get(v___x_1016_, 1);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1020_ = v___x_1016_;
v_isShared_1021_ = v_isSharedCheck_1070_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_res_1018_);
lean_inc(v_pos_1017_);
lean_dec(v___x_1016_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1070_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v_array_1022_; lean_object* v_idx_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v_array_1022_ = lean_ctor_get(v_pos_1017_, 0);
v_idx_1023_ = lean_ctor_get(v_pos_1017_, 1);
v___x_1024_ = lean_byte_array_size(v_array_1022_);
v___x_1025_ = lean_nat_dec_lt(v_idx_1023_, v___x_1024_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
lean_dec(v_res_1018_);
lean_dec(v_res_1013_);
lean_dec(v_res_985_);
lean_dec(v_ident_981_);
v___x_1026_ = lean_box(0);
if (v_isShared_1021_ == 0)
{
lean_ctor_set_tag(v___x_1020_, 1);
lean_ctor_set(v___x_1020_, 1, v___x_1026_);
v___x_1028_ = v___x_1020_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_pos_1017_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
else
{
uint8_t v___x_1030_; uint8_t v_got_1031_; uint8_t v___x_1032_; 
v___x_1030_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
v_got_1031_ = lean_byte_array_fget(v_array_1022_, v_idx_1023_);
v___x_1032_ = lean_uint8_dec_eq(v_got_1031_, v___x_1030_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
lean_dec(v_res_1018_);
lean_dec(v_res_1013_);
lean_dec(v_res_985_);
lean_dec(v_ident_981_);
v___x_1033_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4);
if (v_isShared_1021_ == 0)
{
lean_ctor_set_tag(v___x_1020_, 1);
lean_ctor_set(v___x_1020_, 1, v___x_1033_);
v___x_1035_ = v___x_1020_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_pos_1017_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
else
{
lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1067_; 
lean_inc(v_idx_1023_);
lean_inc_ref(v_array_1022_);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_pos_1017_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; lean_object* v_unused_1069_; 
v_unused_1068_ = lean_ctor_get(v_pos_1017_, 1);
lean_dec(v_unused_1068_);
v_unused_1069_ = lean_ctor_get(v_pos_1017_, 0);
lean_dec(v_unused_1069_);
v___x_1038_ = v_pos_1017_;
v_isShared_1039_ = v_isSharedCheck_1067_;
goto v_resetjp_1037_;
}
else
{
lean_dec(v_pos_1017_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1067_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1040_ = lean_nat_add(v_idx_1023_, v___x_1007_);
lean_dec(v_idx_1023_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 1, v___x_1040_);
v___x_1042_ = v___x_1038_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_array_1022_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1043_ = lean_array_get_size(v_res_985_);
v___x_1044_ = lean_nat_dec_eq(v___x_1043_, v___x_1014_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1045_ = lean_array_get_size(v_res_1018_);
v___x_1046_ = lean_nat_dec_eq(v___x_1045_, v___x_1014_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1047_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_985_);
v___x_1048_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_1048_, 0, v_ident_981_);
lean_ctor_set(v___x_1048_, 1, v_res_985_);
lean_ctor_set(v___x_1048_, 2, v___x_1047_);
lean_ctor_set(v___x_1048_, 3, v_res_1013_);
lean_ctor_set(v___x_1048_, 4, v_res_1018_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 1, v___x_1048_);
lean_ctor_set(v___x_1020_, 0, v___x_1042_);
v___x_1050_ = v___x_1020_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1054_; 
lean_dec(v_res_1018_);
v___x_1052_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1052_, 0, v_ident_981_);
lean_ctor_set(v___x_1052_, 1, v_res_985_);
lean_ctor_set(v___x_1052_, 2, v_res_1013_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 1, v___x_1052_);
lean_ctor_set(v___x_1020_, 0, v___x_1042_);
v___x_1054_ = v___x_1020_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
else
{
lean_object* v___x_1056_; uint8_t v___x_1057_; 
lean_dec(v_res_985_);
v___x_1056_ = lean_array_get_size(v_res_1018_);
lean_dec(v_res_1018_);
v___x_1057_ = lean_nat_dec_eq(v___x_1056_, v___x_1014_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; lean_object* v___x_1060_; 
lean_dec(v_res_1013_);
lean_dec(v_ident_981_);
v___x_1058_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2));
if (v_isShared_1021_ == 0)
{
lean_ctor_set_tag(v___x_1020_, 1);
lean_ctor_set(v___x_1020_, 1, v___x_1058_);
lean_ctor_set(v___x_1020_, 0, v___x_1042_);
v___x_1060_ = v___x_1020_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v_ident_981_);
lean_ctor_set(v___x_1062_, 1, v_res_1013_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 1, v___x_1062_);
lean_ctor_set(v___x_1020_, 0, v___x_1042_);
v___x_1064_ = v___x_1020_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
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
lean_object* v_pos_1071_; lean_object* v_err_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec(v_res_1013_);
lean_dec(v_res_985_);
lean_dec(v_ident_981_);
v_pos_1071_ = lean_ctor_get(v___x_1016_, 0);
v_err_1072_ = lean_ctor_get(v___x_1016_, 1);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1016_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_err_1072_);
lean_inc(v_pos_1071_);
lean_dec(v___x_1016_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_pos_1071_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_err_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
else
{
lean_object* v_pos_1080_; lean_object* v_err_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec(v_res_985_);
lean_dec(v_ident_981_);
v_pos_1080_ = lean_ctor_get(v___x_1011_, 0);
v_err_1081_ = lean_ctor_get(v___x_1011_, 1);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1011_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_err_1081_);
lean_inc(v_pos_1080_);
lean_dec(v___x_1011_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_pos_1080_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_err_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
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
lean_object* v_pos_1094_; lean_object* v_err_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec(v_ident_981_);
v_pos_1094_ = lean_ctor_get(v___x_983_, 0);
v_err_1095_ = lean_ctor_get(v___x_983_, 1);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_983_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_err_1095_);
lean_inc(v_pos_1094_);
lean_dec(v___x_983_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_pos_1094_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_err_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(lean_object* v_a_1103_){
_start:
{
lean_object* v_array_1107_; lean_object* v_idx_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v_array_1107_ = lean_ctor_get(v_a_1103_, 0);
v_idx_1108_ = lean_ctor_get(v_a_1103_, 1);
v___x_1109_ = lean_byte_array_size(v_array_1107_);
v___x_1110_ = lean_nat_dec_lt(v_idx_1108_, v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1112_, 0, v_a_1103_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
return v___x_1112_;
}
else
{
uint8_t v_c_1113_; uint8_t v___x_1114_; uint8_t v___x_1115_; 
v_c_1113_ = lean_byte_array_fget(v_array_1107_, v_idx_1108_);
v___x_1114_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
v___x_1115_ = lean_uint8_dec_le(v___x_1114_, v_c_1113_);
if (v___x_1115_ == 0)
{
goto v___jp_1104_;
}
else
{
uint8_t v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
v___x_1117_ = lean_uint8_dec_le(v_c_1113_, v___x_1116_);
if (v___x_1117_ == 0)
{
goto v___jp_1104_;
}
else
{
lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1178_; 
lean_inc(v_idx_1108_);
lean_inc_ref(v_array_1107_);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_a_1103_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; lean_object* v_unused_1180_; 
v_unused_1179_ = lean_ctor_get(v_a_1103_, 1);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v_a_1103_, 0);
lean_dec(v_unused_1180_);
v___x_1119_ = v_a_1103_;
v_isShared_1120_ = v_isSharedCheck_1178_;
goto v_resetjp_1118_;
}
else
{
lean_dec(v_a_1103_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1178_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v_it_x27_1124_; 
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = lean_nat_add(v_idx_1108_, v___x_1121_);
lean_dec(v_idx_1108_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 1, v___x_1122_);
v_it_x27_1124_ = v___x_1119_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_array_1107_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1122_);
v_it_x27_1124_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
uint32_t v___x_1125_; uint8_t v___x_1126_; uint8_t v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v_fst_1130_; lean_object* v_snd_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1176_; 
v___x_1125_ = lean_uint8_to_uint32(v_c_1113_);
v___x_1126_ = lean_uint32_to_uint8(v___x_1125_);
v___x_1127_ = lean_uint8_sub(v___x_1126_, v___x_1114_);
v___x_1128_ = lean_uint8_to_nat(v___x_1127_);
v___x_1129_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_1124_, v___x_1128_);
v_fst_1130_ = lean_ctor_get(v___x_1129_, 0);
v_snd_1131_ = lean_ctor_get(v___x_1129_, 1);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1133_ = v___x_1129_;
v_isShared_1134_ = v_isSharedCheck_1176_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_snd_1131_);
lean_inc(v_fst_1130_);
lean_dec(v___x_1129_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1176_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = lean_unsigned_to_nat(0u);
v___x_1136_ = lean_nat_dec_eq(v_fst_1130_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v_array_1137_; lean_object* v_idx_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v_array_1137_ = lean_ctor_get(v_snd_1131_, 0);
v_idx_1138_ = lean_ctor_get(v_snd_1131_, 1);
v___x_1139_ = lean_byte_array_size(v_array_1137_);
v___x_1140_ = lean_nat_dec_lt(v_idx_1138_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
lean_dec(v_fst_1130_);
v___x_1141_ = lean_box(0);
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 1);
lean_ctor_set(v___x_1133_, 1, v___x_1141_);
lean_ctor_set(v___x_1133_, 0, v_snd_1131_);
v___x_1143_ = v___x_1133_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_snd_1131_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
else
{
uint8_t v___x_1145_; uint8_t v_got_1146_; uint8_t v___x_1147_; 
v___x_1145_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
v_got_1146_ = lean_byte_array_fget(v_array_1137_, v_idx_1138_);
v___x_1147_ = lean_uint8_dec_eq(v_got_1146_, v___x_1145_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1150_; 
lean_dec(v_fst_1130_);
v___x_1148_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 1);
lean_ctor_set(v___x_1133_, 1, v___x_1148_);
lean_ctor_set(v___x_1133_, 0, v_snd_1131_);
v___x_1150_ = v___x_1133_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_snd_1131_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
else
{
lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1169_; 
lean_inc(v_idx_1138_);
lean_inc_ref(v_array_1137_);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_snd_1131_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; lean_object* v_unused_1171_; 
v_unused_1170_ = lean_ctor_get(v_snd_1131_, 1);
lean_dec(v_unused_1170_);
v_unused_1171_ = lean_ctor_get(v_snd_1131_, 0);
lean_dec(v_unused_1171_);
v___x_1153_ = v_snd_1131_;
v_isShared_1154_ = v_isSharedCheck_1169_;
goto v_resetjp_1152_;
}
else
{
lean_dec(v_snd_1131_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1169_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = lean_nat_add(v_idx_1138_, v___x_1121_);
lean_dec(v_idx_1138_);
lean_inc(v___x_1155_);
lean_inc_ref(v_array_1137_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 1, v___x_1155_);
v___x_1157_ = v___x_1153_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_array_1137_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
uint8_t v___x_1158_; 
v___x_1158_ = lean_nat_dec_lt(v___x_1155_, v___x_1139_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
lean_dec(v___x_1155_);
lean_dec_ref(v_array_1137_);
lean_dec(v_fst_1130_);
v___x_1159_ = lean_box(0);
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 1);
lean_ctor_set(v___x_1133_, 1, v___x_1159_);
lean_ctor_set(v___x_1133_, 0, v___x_1157_);
v___x_1161_ = v___x_1133_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
else
{
uint8_t v___x_1163_; uint8_t v___x_1164_; uint8_t v___x_1165_; 
lean_del_object(v___x_1133_);
v___x_1163_ = lean_byte_array_fget(v_array_1137_, v___x_1155_);
lean_dec(v___x_1155_);
lean_dec_ref(v_array_1137_);
v___x_1164_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
v___x_1165_ = lean_uint8_dec_eq(v___x_1163_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(v_fst_1130_, v___x_1157_);
return v___x_1166_;
}
else
{
lean_object* v___x_1167_; 
lean_dec(v_fst_1130_);
v___x_1167_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(v___x_1157_);
return v___x_1167_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1174_; 
lean_dec(v_fst_1130_);
v___x_1172_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 1);
lean_ctor_set(v___x_1133_, 1, v___x_1172_);
lean_ctor_set(v___x_1133_, 0, v_snd_1131_);
v___x_1174_ = v___x_1133_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_snd_1131_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
}
}
}
v___jp_1104_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_1106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1106_, 0, v_a_1103_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
return v___x_1106_;
}
}
}
static uint8_t _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2(void){
_start:
{
uint32_t v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = 13;
v___x_1185_ = lean_uint32_to_uint8(v___x_1184_);
return v___x_1185_;
}
}
static uint8_t _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3(void){
_start:
{
uint32_t v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = 99;
v___x_1187_ = lean_uint32_to_uint8(v___x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(uint8_t v___x_1188_, lean_object* v_acc_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v_array_1191_; lean_object* v_idx_1192_; lean_object* v_pos_1194_; lean_object* v_idx_1195_; lean_object* v_err_1196_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v_array_1191_ = lean_ctor_get(v_a_1190_, 0);
v_idx_1192_ = lean_ctor_get(v_a_1190_, 1);
lean_inc(v_idx_1192_);
v___x_1202_ = lean_byte_array_size(v_array_1191_);
v___x_1203_ = lean_nat_dec_lt(v_idx_1192_, v___x_1202_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_box(0);
lean_inc(v_idx_1192_);
v_pos_1194_ = v_a_1190_;
v_idx_1195_ = v_idx_1192_;
v_err_1196_ = v___x_1204_;
goto v___jp_1193_;
}
else
{
uint8_t v_c_1205_; uint8_t v___x_1206_; uint8_t v___x_1207_; 
v_c_1205_ = lean_byte_array_fget(v_array_1191_, v_idx_1192_);
v___x_1206_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2);
v___x_1207_ = lean_uint8_dec_eq(v_c_1205_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_it_x27_1210_; uint8_t v___y_1212_; uint8_t v___x_1216_; uint8_t v___x_1217_; 
v___x_1208_ = lean_unsigned_to_nat(1u);
v___x_1209_ = lean_nat_add(v_idx_1192_, v___x_1208_);
lean_inc_ref(v_array_1191_);
v_it_x27_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_1210_, 0, v_array_1191_);
lean_ctor_set(v_it_x27_1210_, 1, v___x_1209_);
v___x_1216_ = lean_uint8_once(&l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2, &l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2_once, _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2);
v___x_1217_ = lean_uint8_dec_eq(v_c_1205_, v___x_1216_);
if (v___x_1217_ == 0)
{
uint8_t v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = lean_uint8_once(&l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3, &l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3_once, _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3);
v___x_1219_ = lean_uint8_dec_eq(v___x_1188_, v___x_1218_);
v___y_1212_ = v___x_1219_;
goto v___jp_1211_;
}
else
{
v___y_1212_ = v___x_1207_;
goto v___jp_1211_;
}
v___jp_1211_:
{
if (v___y_1212_ == 0)
{
lean_dec_ref_known(v_it_x27_1210_, 2);
goto v___jp_1200_;
}
else
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
lean_dec(v_idx_1192_);
lean_dec_ref(v_a_1190_);
v___x_1213_ = lean_box(v_c_1205_);
v___x_1214_ = lean_array_push(v_acc_1189_, v___x_1213_);
v_acc_1189_ = v___x_1214_;
v_a_1190_ = v_it_x27_1210_;
goto _start;
}
}
}
else
{
goto v___jp_1200_;
}
}
v___jp_1193_:
{
uint8_t v___x_1197_; 
v___x_1197_ = lean_nat_dec_eq(v_idx_1192_, v_idx_1195_);
lean_dec(v_idx_1195_);
lean_dec(v_idx_1192_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; 
lean_dec_ref(v_acc_1189_);
lean_inc(v_err_1196_);
v___x_1198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1198_, 0, v_pos_1194_);
lean_ctor_set(v___x_1198_, 1, v_err_1196_);
return v___x_1198_;
}
else
{
lean_object* v___x_1199_; 
v___x_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1199_, 0, v_pos_1194_);
lean_ctor_set(v___x_1199_, 1, v_acc_1189_);
return v___x_1199_;
}
}
v___jp_1200_:
{
lean_object* v___x_1201_; 
v___x_1201_ = ((lean_object*)(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__1));
lean_inc(v_idx_1192_);
v_pos_1194_ = v_a_1190_;
v_idx_1195_ = v_idx_1192_;
v_err_1196_ = v___x_1201_;
goto v___jp_1193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___boxed(lean_object* v___x_1220_, lean_object* v_acc_1221_, lean_object* v_a_1222_){
_start:
{
uint8_t v___x_2518__boxed_1223_; lean_object* v_res_1224_; 
v___x_2518__boxed_1223_ = lean_unbox(v___x_1220_);
v_res_1224_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(v___x_2518__boxed_1223_, v_acc_1221_, v_a_1222_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(lean_object* v_actions_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_pos_1230_; lean_object* v_array_1231_; lean_object* v_idx_1232_; lean_object* v_pos_1238_; lean_object* v___y_1242_; lean_object* v_array_1253_; lean_object* v_idx_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v_array_1253_ = lean_ctor_get(v_a_1228_, 0);
v_idx_1254_ = lean_ctor_get(v_a_1228_, 1);
v___x_1255_ = lean_byte_array_size(v_array_1253_);
v___x_1256_ = lean_nat_dec_lt(v_idx_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_dec_ref(v_actions_1227_);
v___x_1257_ = lean_box(0);
v___x_1258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1258_, 0, v_a_1228_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
return v___x_1258_;
}
else
{
uint8_t v___x_1259_; uint8_t v___x_1260_; uint8_t v___x_1261_; 
v___x_1259_ = lean_byte_array_fget(v_array_1253_, v_idx_1254_);
v___x_1260_ = lean_uint8_once(&l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3, &l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3_once, _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3);
v___x_1261_ = lean_uint8_dec_eq(v___x_1259_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(v_a_1228_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_pos_1263_; lean_object* v_res_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1325_; 
v_pos_1263_ = lean_ctor_get(v___x_1262_, 0);
v_res_1264_ = lean_ctor_get(v___x_1262_, 1);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1266_ = v___x_1262_;
v_isShared_1267_ = v_isSharedCheck_1325_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_res_1264_);
lean_inc(v_pos_1263_);
lean_dec(v___x_1262_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1325_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v_pos_1269_; lean_object* v_array_1270_; lean_object* v_idx_1271_; lean_object* v_pos_1280_; lean_object* v___y_1284_; lean_object* v_array_1295_; lean_object* v_idx_1296_; lean_object* v___y_1298_; lean_object* v_pos_1299_; lean_object* v_idx_1300_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v_array_1295_ = lean_ctor_get(v_pos_1263_, 0);
v_idx_1296_ = lean_ctor_get(v_pos_1263_, 1);
lean_inc(v_idx_1296_);
v___x_1305_ = lean_byte_array_size(v_array_1295_);
v___x_1306_ = lean_nat_dec_lt(v_idx_1296_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = lean_box(0);
lean_inc(v_pos_1263_);
v___x_1308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1308_, 0, v_pos_1263_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
lean_inc(v_idx_1296_);
v___y_1298_ = v___x_1308_;
v_pos_1299_ = v_pos_1263_;
v_idx_1300_ = v_idx_1296_;
goto v___jp_1297_;
}
else
{
uint8_t v___x_1309_; uint8_t v_got_1310_; uint8_t v___x_1311_; 
v___x_1309_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2);
v_got_1310_ = lean_byte_array_fget(v_array_1295_, v_idx_1296_);
v___x_1311_ = lean_uint8_dec_eq(v_got_1310_, v___x_1309_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9);
lean_inc(v_pos_1263_);
v___x_1313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_pos_1263_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
lean_inc(v_idx_1296_);
v___y_1298_ = v___x_1313_;
v_pos_1299_ = v_pos_1263_;
v_idx_1300_ = v_idx_1296_;
goto v___jp_1297_;
}
else
{
lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1322_; 
lean_inc_ref(v_array_1295_);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_pos_1263_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; lean_object* v_unused_1324_; 
v_unused_1323_ = lean_ctor_get(v_pos_1263_, 1);
lean_dec(v_unused_1323_);
v_unused_1324_ = lean_ctor_get(v_pos_1263_, 0);
lean_dec(v_unused_1324_);
v___x_1315_ = v_pos_1263_;
v_isShared_1316_ = v_isSharedCheck_1322_;
goto v_resetjp_1314_;
}
else
{
lean_dec(v_pos_1263_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1322_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1317_ = lean_unsigned_to_nat(1u);
v___x_1318_ = lean_nat_add(v_idx_1296_, v___x_1317_);
lean_dec(v_idx_1296_);
lean_inc(v___x_1318_);
lean_inc_ref(v_array_1295_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 1, v___x_1318_);
v___x_1320_ = v___x_1315_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_array_1295_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
v_pos_1269_ = v___x_1320_;
v_array_1270_ = v_array_1295_;
v_idx_1271_ = v___x_1318_;
goto v___jp_1268_;
}
}
}
}
v___jp_1268_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1272_ = lean_array_push(v_actions_1227_, v_res_1264_);
v___x_1273_ = lean_byte_array_size(v_array_1270_);
lean_dec_ref(v_array_1270_);
v___x_1274_ = lean_nat_dec_lt(v_idx_1271_, v___x_1273_);
lean_dec(v_idx_1271_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1276_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v___x_1272_);
lean_ctor_set(v___x_1266_, 0, v_pos_1269_);
v___x_1276_ = v___x_1266_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_pos_1269_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v___x_1272_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
else
{
lean_del_object(v___x_1266_);
v_actions_1227_ = v___x_1272_;
v_a_1228_ = v_pos_1269_;
goto _start;
}
}
v___jp_1279_:
{
lean_object* v_array_1281_; lean_object* v_idx_1282_; 
v_array_1281_ = lean_ctor_get(v_pos_1280_, 0);
lean_inc_ref(v_array_1281_);
v_idx_1282_ = lean_ctor_get(v_pos_1280_, 1);
lean_inc(v_idx_1282_);
v_pos_1269_ = v_pos_1280_;
v_array_1270_ = v_array_1281_;
v_idx_1271_ = v_idx_1282_;
goto v___jp_1268_;
}
v___jp_1283_:
{
if (lean_obj_tag(v___y_1284_) == 0)
{
lean_object* v_pos_1285_; 
v_pos_1285_ = lean_ctor_get(v___y_1284_, 0);
lean_inc(v_pos_1285_);
lean_dec_ref_known(v___y_1284_, 2);
v_pos_1280_ = v_pos_1285_;
goto v___jp_1279_;
}
else
{
lean_object* v_pos_1286_; lean_object* v_err_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_del_object(v___x_1266_);
lean_dec(v_res_1264_);
lean_dec_ref(v_actions_1227_);
v_pos_1286_ = lean_ctor_get(v___y_1284_, 0);
v_err_1287_ = lean_ctor_get(v___y_1284_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___y_1284_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___y_1284_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_err_1287_);
lean_inc(v_pos_1286_);
lean_dec(v___y_1284_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_pos_1286_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_err_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
v___jp_1297_:
{
uint8_t v___x_1301_; 
v___x_1301_ = lean_nat_dec_eq(v_idx_1296_, v_idx_1300_);
lean_dec(v_idx_1300_);
lean_dec(v_idx_1296_);
if (v___x_1301_ == 0)
{
lean_dec_ref(v_pos_1299_);
v___y_1284_ = v___y_1298_;
goto v___jp_1283_;
}
else
{
lean_object* v_utf8_1302_; lean_object* v___x_1303_; 
lean_dec_ref(v___y_1298_);
v_utf8_1302_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1);
v___x_1303_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1302_, v_pos_1299_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_pos_1304_; 
v_pos_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_pos_1304_);
lean_dec_ref_known(v___x_1303_, 2);
v_pos_1280_ = v_pos_1304_;
goto v___jp_1279_;
}
else
{
v___y_1284_ = v___x_1303_;
goto v___jp_1283_;
}
}
}
}
}
else
{
lean_object* v_pos_1326_; lean_object* v_err_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec_ref(v_actions_1227_);
v_pos_1326_ = lean_ctor_get(v___x_1262_, 0);
v_err_1327_ = lean_ctor_get(v___x_1262_, 1);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1262_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_err_1327_);
lean_inc(v_pos_1326_);
lean_dec(v___x_1262_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_pos_1326_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_err_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0));
v___x_1336_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(v___x_1259_, v___x_1335_, v_a_1228_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_pos_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1375_; 
v_pos_1337_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; 
v_unused_1376_ = lean_ctor_get(v___x_1336_, 1);
lean_dec(v_unused_1376_);
v___x_1339_ = v___x_1336_;
v_isShared_1340_ = v_isSharedCheck_1375_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_pos_1337_);
lean_dec(v___x_1336_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1375_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v_array_1341_; lean_object* v_idx_1342_; lean_object* v___y_1344_; lean_object* v_pos_1345_; lean_object* v_idx_1346_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v_array_1341_ = lean_ctor_get(v_pos_1337_, 0);
v_idx_1342_ = lean_ctor_get(v_pos_1337_, 1);
lean_inc(v_idx_1342_);
v___x_1351_ = lean_byte_array_size(v_array_1341_);
v___x_1352_ = lean_nat_dec_lt(v_idx_1342_, v___x_1351_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1353_ = lean_box(0);
lean_inc(v_pos_1337_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set_tag(v___x_1339_, 1);
lean_ctor_set(v___x_1339_, 1, v___x_1353_);
v___x_1355_ = v___x_1339_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_pos_1337_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_inc(v_idx_1342_);
v___y_1344_ = v___x_1355_;
v_pos_1345_ = v_pos_1337_;
v_idx_1346_ = v_idx_1342_;
goto v___jp_1343_;
}
}
else
{
uint8_t v___x_1357_; uint8_t v_got_1358_; uint8_t v___x_1359_; 
v___x_1357_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2);
v_got_1358_ = lean_byte_array_fget(v_array_1341_, v_idx_1342_);
v___x_1359_ = lean_uint8_dec_eq(v_got_1358_, v___x_1357_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1360_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9);
lean_inc(v_pos_1337_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set_tag(v___x_1339_, 1);
lean_ctor_set(v___x_1339_, 1, v___x_1360_);
v___x_1362_ = v___x_1339_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_pos_1337_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_inc(v_idx_1342_);
v___y_1344_ = v___x_1362_;
v_pos_1345_ = v_pos_1337_;
v_idx_1346_ = v_idx_1342_;
goto v___jp_1343_;
}
}
else
{
lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1372_; 
lean_inc_ref(v_array_1341_);
lean_del_object(v___x_1339_);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_pos_1337_);
if (v_isSharedCheck_1372_ == 0)
{
lean_object* v_unused_1373_; lean_object* v_unused_1374_; 
v_unused_1373_ = lean_ctor_get(v_pos_1337_, 1);
lean_dec(v_unused_1373_);
v_unused_1374_ = lean_ctor_get(v_pos_1337_, 0);
lean_dec(v_unused_1374_);
v___x_1365_ = v_pos_1337_;
v_isShared_1366_ = v_isSharedCheck_1372_;
goto v_resetjp_1364_;
}
else
{
lean_dec(v_pos_1337_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1372_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1367_ = lean_unsigned_to_nat(1u);
v___x_1368_ = lean_nat_add(v_idx_1342_, v___x_1367_);
lean_dec(v_idx_1342_);
lean_inc(v___x_1368_);
lean_inc_ref(v_array_1341_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v___x_1368_);
v___x_1370_ = v___x_1365_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_array_1341_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
v_pos_1230_ = v___x_1370_;
v_array_1231_ = v_array_1341_;
v_idx_1232_ = v___x_1368_;
goto v___jp_1229_;
}
}
}
}
v___jp_1343_:
{
uint8_t v___x_1347_; 
v___x_1347_ = lean_nat_dec_eq(v_idx_1342_, v_idx_1346_);
lean_dec(v_idx_1346_);
lean_dec(v_idx_1342_);
if (v___x_1347_ == 0)
{
lean_dec_ref(v_pos_1345_);
v___y_1242_ = v___y_1344_;
goto v___jp_1241_;
}
else
{
lean_object* v_utf8_1348_; lean_object* v___x_1349_; 
lean_dec_ref(v___y_1344_);
v_utf8_1348_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1);
v___x_1349_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1348_, v_pos_1345_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_pos_1350_; 
v_pos_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_pos_1350_);
lean_dec_ref_known(v___x_1349_, 2);
v_pos_1238_ = v_pos_1350_;
goto v___jp_1237_;
}
else
{
v___y_1242_ = v___x_1349_;
goto v___jp_1241_;
}
}
}
}
}
else
{
lean_object* v_pos_1377_; lean_object* v_err_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec_ref(v_actions_1227_);
v_pos_1377_ = lean_ctor_get(v___x_1336_, 0);
v_err_1378_ = lean_ctor_get(v___x_1336_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1336_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_err_1378_);
lean_inc(v_pos_1377_);
lean_dec(v___x_1336_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_pos_1377_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_err_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
v___jp_1229_:
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_byte_array_size(v_array_1231_);
lean_dec_ref(v_array_1231_);
v___x_1234_ = lean_nat_dec_lt(v_idx_1232_, v___x_1233_);
lean_dec(v_idx_1232_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v_pos_1230_);
lean_ctor_set(v___x_1235_, 1, v_actions_1227_);
return v___x_1235_;
}
else
{
v_a_1228_ = v_pos_1230_;
goto _start;
}
}
v___jp_1237_:
{
lean_object* v_array_1239_; lean_object* v_idx_1240_; 
v_array_1239_ = lean_ctor_get(v_pos_1238_, 0);
lean_inc_ref(v_array_1239_);
v_idx_1240_ = lean_ctor_get(v_pos_1238_, 1);
lean_inc(v_idx_1240_);
v_pos_1230_ = v_pos_1238_;
v_array_1231_ = v_array_1239_;
v_idx_1232_ = v_idx_1240_;
goto v___jp_1229_;
}
v___jp_1241_:
{
if (lean_obj_tag(v___y_1242_) == 0)
{
lean_object* v_pos_1243_; 
v_pos_1243_ = lean_ctor_get(v___y_1242_, 0);
lean_inc(v_pos_1243_);
lean_dec_ref_known(v___y_1242_, 2);
v_pos_1238_ = v_pos_1243_;
goto v___jp_1237_;
}
else
{
lean_object* v_pos_1244_; lean_object* v_err_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec_ref(v_actions_1227_);
v_pos_1244_ = lean_ctor_get(v___y_1242_, 0);
v_err_1245_ = lean_ctor_get(v___y_1242_, 1);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___y_1242_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___y_1242_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_err_1245_);
lean_inc(v_pos_1244_);
lean_dec(v___y_1242_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_pos_1244_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_err_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(lean_object* v_a_1388_){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0));
v___x_1390_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(v___x_1389_, v_a_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero(lean_object* v_a_1394_){
_start:
{
lean_object* v_array_1395_; lean_object* v_idx_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v_array_1395_ = lean_ctor_get(v_a_1394_, 0);
v_idx_1396_ = lean_ctor_get(v_a_1394_, 1);
v___x_1397_ = lean_byte_array_size(v_array_1395_);
v___x_1398_ = lean_nat_dec_lt(v_idx_1396_, v___x_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_box(0);
v___x_1400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1400_, 0, v_a_1394_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
return v___x_1400_;
}
else
{
uint8_t v___x_1401_; uint8_t v_got_1402_; uint8_t v___x_1403_; 
v___x_1401_ = 0;
v_got_1402_ = lean_byte_array_fget(v_array_1395_, v_idx_1396_);
v___x_1403_ = lean_uint8_dec_eq(v_got_1402_, v___x_1401_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
v___x_1405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1405_, 0, v_a_1394_);
lean_ctor_set(v___x_1405_, 1, v___x_1404_);
return v___x_1405_;
}
else
{
lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1416_; 
lean_inc(v_idx_1396_);
lean_inc_ref(v_array_1395_);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_a_1394_);
if (v_isSharedCheck_1416_ == 0)
{
lean_object* v_unused_1417_; lean_object* v_unused_1418_; 
v_unused_1417_ = lean_ctor_get(v_a_1394_, 1);
lean_dec(v_unused_1417_);
v_unused_1418_ = lean_ctor_get(v_a_1394_, 0);
lean_dec(v_unused_1418_);
v___x_1407_ = v_a_1394_;
v_isShared_1408_ = v_isSharedCheck_1416_;
goto v_resetjp_1406_;
}
else
{
lean_dec(v_a_1394_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1416_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1409_ = lean_unsigned_to_nat(1u);
v___x_1410_ = lean_nat_add(v_idx_1396_, v___x_1409_);
lean_dec(v_idx_1396_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 1, v___x_1410_);
v___x_1412_ = v___x_1407_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_array_1395_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_box(0);
v___x_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1412_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
return v___x_1414_;
}
}
}
}
}
}
static uint8_t _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4(void){
_start:
{
uint8_t v___x_1425_; uint8_t v___x_1426_; 
v___x_1425_ = 15;
v___x_1426_ = lean_uint8_complement(v___x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(uint64_t v_uidx_1427_, uint64_t v_shift_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v_array_1430_; lean_object* v_idx_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v_array_1430_ = lean_ctor_get(v_a_1429_, 0);
v_idx_1431_ = lean_ctor_get(v_a_1429_, 1);
v___x_1432_ = lean_byte_array_size(v_array_1430_);
v___x_1433_ = lean_nat_dec_lt(v_idx_1431_, v___x_1432_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_box(0);
v___x_1435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_a_1429_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
return v___x_1435_;
}
else
{
lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1486_; 
lean_inc(v_idx_1431_);
lean_inc_ref(v_array_1430_);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_a_1429_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; lean_object* v_unused_1488_; 
v_unused_1487_ = lean_ctor_get(v_a_1429_, 1);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v_a_1429_, 0);
lean_dec(v_unused_1488_);
v___x_1437_ = v_a_1429_;
v_isShared_1438_ = v_isSharedCheck_1486_;
goto v_resetjp_1436_;
}
else
{
lean_dec(v_a_1429_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1486_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
uint8_t v_c_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v_it_x27_1443_; 
v_c_1439_ = lean_byte_array_fget(v_array_1430_, v_idx_1431_);
v___x_1440_ = lean_unsigned_to_nat(1u);
v___x_1441_ = lean_nat_add(v_idx_1431_, v___x_1440_);
lean_dec(v_idx_1431_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 1, v___x_1441_);
v_it_x27_1443_ = v___x_1437_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_array_1430_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v___x_1441_);
v_it_x27_1443_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
uint64_t v___y_1445_; uint8_t v___y_1446_; uint8_t v___y_1476_; uint64_t v___x_1479_; uint8_t v___x_1480_; 
v___x_1479_ = 28ULL;
v___x_1480_ = lean_uint64_dec_eq(v_shift_1428_, v___x_1479_);
if (v___x_1480_ == 0)
{
v___y_1476_ = v___x_1480_;
goto v___jp_1475_;
}
else
{
uint8_t v___x_1481_; uint8_t v___x_1482_; uint8_t v___x_1483_; uint8_t v___x_1484_; 
v___x_1481_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4);
v___x_1482_ = lean_uint8_land(v_c_1439_, v___x_1481_);
v___x_1483_ = 0;
v___x_1484_ = lean_uint8_dec_eq(v___x_1482_, v___x_1483_);
if (v___x_1484_ == 0)
{
v___y_1476_ = v___x_1480_;
goto v___jp_1475_;
}
else
{
goto v___jp_1454_;
}
}
v___jp_1444_:
{
if (v___y_1446_ == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1447_ = lean_uint64_to_nat(v___y_1445_);
v___x_1448_ = lean_nat_to_int(v___x_1447_);
v___x_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1449_, 0, v_it_x27_1443_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
return v___x_1449_;
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1450_ = lean_uint64_to_nat(v___y_1445_);
v___x_1451_ = lean_nat_to_int(v___x_1450_);
v___x_1452_ = lean_int_neg(v___x_1451_);
lean_dec(v___x_1451_);
v___x_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1453_, 0, v_it_x27_1443_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
return v___x_1453_;
}
}
v___jp_1454_:
{
uint8_t v___x_1455_; uint8_t v___x_1456_; 
v___x_1455_ = 0;
v___x_1456_ = lean_uint8_dec_eq(v_c_1439_, v___x_1455_);
if (v___x_1456_ == 0)
{
uint8_t v___x_1457_; uint8_t v___x_1458_; uint64_t v___x_1459_; uint64_t v___x_1460_; uint64_t v___x_1461_; uint8_t v___x_1462_; uint8_t v___x_1463_; uint8_t v___x_1464_; 
v___x_1457_ = 127;
v___x_1458_ = lean_uint8_land(v_c_1439_, v___x_1457_);
v___x_1459_ = lean_uint8_to_uint64(v___x_1458_);
v___x_1460_ = lean_uint64_shift_left(v___x_1459_, v_shift_1428_);
v___x_1461_ = lean_uint64_lor(v_uidx_1427_, v___x_1460_);
v___x_1462_ = 128;
v___x_1463_ = lean_uint8_land(v_c_1439_, v___x_1462_);
v___x_1464_ = lean_uint8_dec_eq(v___x_1463_, v___x_1455_);
if (v___x_1464_ == 0)
{
uint64_t v___x_1465_; uint64_t v___x_1466_; 
v___x_1465_ = 7ULL;
v___x_1466_ = lean_uint64_add(v_shift_1428_, v___x_1465_);
v_uidx_1427_ = v___x_1461_;
v_shift_1428_ = v___x_1466_;
v_a_1429_ = v_it_x27_1443_;
goto _start;
}
else
{
uint64_t v___x_1468_; uint64_t v___x_1469_; uint64_t v___x_1470_; uint64_t v___x_1471_; uint8_t v___x_1472_; 
v___x_1468_ = 1ULL;
v___x_1469_ = lean_uint64_shift_right(v___x_1461_, v___x_1468_);
v___x_1470_ = lean_uint64_land(v___x_1468_, v___x_1461_);
v___x_1471_ = 0ULL;
v___x_1472_ = lean_uint64_dec_eq(v___x_1470_, v___x_1471_);
if (v___x_1472_ == 0)
{
v___y_1445_ = v___x_1469_;
v___y_1446_ = v___x_1464_;
goto v___jp_1444_;
}
else
{
v___y_1445_ = v___x_1469_;
v___y_1446_ = v___x_1456_;
goto v___jp_1444_;
}
}
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1));
v___x_1474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1474_, 0, v_it_x27_1443_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
return v___x_1474_;
}
}
v___jp_1475_:
{
if (v___y_1476_ == 0)
{
goto v___jp_1454_;
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3));
v___x_1478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1478_, 0, v_it_x27_1443_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
return v___x_1478_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___boxed(lean_object* v_uidx_1489_, lean_object* v_shift_1490_, lean_object* v_a_1491_){
_start:
{
uint64_t v_uidx_boxed_1492_; uint64_t v_shift_boxed_1493_; lean_object* v_res_1494_; 
v_uidx_boxed_1492_ = lean_unbox_uint64(v_uidx_1489_);
lean_dec_ref(v_uidx_1489_);
v_shift_boxed_1493_ = lean_unbox_uint64(v_shift_1490_);
lean_dec_ref(v_shift_1490_);
v_res_1494_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(v_uidx_boxed_1492_, v_shift_boxed_1493_, v_a_1491_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(lean_object* v_a_1495_){
_start:
{
uint64_t v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = 0ULL;
v___x_1497_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(v___x_1496_, v___x_1496_, v_a_1495_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg(lean_object* v_a_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1501_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_pos_1503_; lean_object* v_res_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1518_; 
v_pos_1503_ = lean_ctor_get(v___x_1502_, 0);
v_res_1504_ = lean_ctor_get(v___x_1502_, 1);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1506_ = v___x_1502_;
v_isShared_1507_ = v_isSharedCheck_1518_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_res_1504_);
lean_inc(v_pos_1503_);
lean_dec(v___x_1502_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1518_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; uint8_t v___x_1509_; 
v___x_1508_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1509_ = lean_int_dec_lt(v_res_1504_, v___x_1508_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; lean_object* v___x_1512_; 
lean_dec(v_res_1504_);
v___x_1510_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1));
if (v_isShared_1507_ == 0)
{
lean_ctor_set_tag(v___x_1506_, 1);
lean_ctor_set(v___x_1506_, 1, v___x_1510_);
v___x_1512_ = v___x_1506_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_pos_1503_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
else
{
lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1514_ = lean_nat_abs(v_res_1504_);
lean_dec(v_res_1504_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 1, v___x_1514_);
v___x_1516_ = v___x_1506_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_pos_1503_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
else
{
lean_object* v_pos_1519_; lean_object* v_err_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
v_pos_1519_ = lean_ctor_get(v___x_1502_, 0);
v_err_1520_ = lean_ctor_get(v___x_1502_, 1);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1502_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_err_1520_);
lean_inc(v_pos_1519_);
lean_dec(v___x_1502_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_pos_1519_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_err_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos(lean_object* v_a_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1531_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_pos_1533_; lean_object* v_res_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1548_; 
v_pos_1533_ = lean_ctor_get(v___x_1532_, 0);
v_res_1534_ = lean_ctor_get(v___x_1532_, 1);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1536_ = v___x_1532_;
v_isShared_1537_ = v_isSharedCheck_1548_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_res_1534_);
lean_inc(v_pos_1533_);
lean_dec(v___x_1532_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1548_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1538_; uint8_t v___x_1539_; 
v___x_1538_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1539_ = lean_int_dec_lt(v___x_1538_, v_res_1534_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; lean_object* v___x_1542_; 
lean_dec(v_res_1534_);
v___x_1540_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1537_ == 0)
{
lean_ctor_set_tag(v___x_1536_, 1);
lean_ctor_set(v___x_1536_, 1, v___x_1540_);
v___x_1542_ = v___x_1536_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_pos_1533_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
else
{
lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1544_ = lean_nat_abs(v_res_1534_);
lean_dec(v_res_1534_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 1, v___x_1544_);
v___x_1546_ = v___x_1536_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_pos_1533_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
else
{
lean_object* v_pos_1549_; lean_object* v_err_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
v_pos_1549_ = lean_ctor_get(v___x_1532_, 0);
v_err_1550_ = lean_ctor_get(v___x_1532_, 1);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1532_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_err_1550_);
lean_inc(v_pos_1549_);
lean_dec(v___x_1532_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_pos_1549_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_err_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId(lean_object* v_a_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1558_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_pos_1560_; lean_object* v_res_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1575_; 
v_pos_1560_ = lean_ctor_get(v___x_1559_, 0);
v_res_1561_ = lean_ctor_get(v___x_1559_, 1);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1563_ = v___x_1559_;
v_isShared_1564_ = v_isSharedCheck_1575_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_res_1561_);
lean_inc(v_pos_1560_);
lean_dec(v___x_1559_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1575_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1565_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1566_ = lean_int_dec_lt(v___x_1565_, v_res_1561_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; lean_object* v___x_1569_; 
lean_dec(v_res_1561_);
v___x_1567_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1564_ == 0)
{
lean_ctor_set_tag(v___x_1563_, 1);
lean_ctor_set(v___x_1563_, 1, v___x_1567_);
v___x_1569_ = v___x_1563_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_pos_1560_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1571_ = lean_nat_abs(v_res_1561_);
lean_dec(v_res_1561_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 1, v___x_1571_);
v___x_1573_ = v___x_1563_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_pos_1560_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
else
{
lean_object* v_pos_1576_; lean_object* v_err_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
v_pos_1576_ = lean_ctor_get(v___x_1559_, 0);
v_err_1577_ = lean_ctor_get(v___x_1559_, 1);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1559_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_err_1577_);
lean_inc(v_pos_1576_);
lean_dec(v___x_1559_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_pos_1576_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_err_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(lean_object* v_parser_1585_, lean_object* v_acc_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v_array_1588_; lean_object* v_idx_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; 
v_array_1588_ = lean_ctor_get(v_a_1587_, 0);
v_idx_1589_ = lean_ctor_get(v_a_1587_, 1);
v___x_1590_ = lean_byte_array_size(v_array_1588_);
v___x_1591_ = lean_nat_dec_lt(v_idx_1589_, v___x_1590_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
lean_dec_ref(v_acc_1586_);
lean_dec_ref(v_parser_1585_);
v___x_1592_ = lean_box(0);
v___x_1593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1593_, 0, v_a_1587_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
return v___x_1593_;
}
else
{
uint8_t v___x_1594_; uint8_t v___x_1595_; uint8_t v___x_1596_; 
v___x_1594_ = lean_byte_array_fget(v_array_1588_, v_idx_1589_);
v___x_1595_ = 0;
v___x_1596_ = lean_uint8_dec_eq(v___x_1594_, v___x_1595_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; 
lean_inc_ref(v_parser_1585_);
v___x_1597_ = lean_apply_1(v_parser_1585_, v_a_1587_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_pos_1598_; lean_object* v_res_1599_; lean_object* v___x_1600_; 
v_pos_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_pos_1598_);
v_res_1599_ = lean_ctor_get(v___x_1597_, 1);
lean_inc(v_res_1599_);
lean_dec_ref_known(v___x_1597_, 2);
v___x_1600_ = lean_array_push(v_acc_1586_, v_res_1599_);
v_acc_1586_ = v___x_1600_;
v_a_1587_ = v_pos_1598_;
goto _start;
}
else
{
lean_object* v_pos_1602_; lean_object* v_err_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec_ref(v_acc_1586_);
lean_dec_ref(v_parser_1585_);
v_pos_1602_ = lean_ctor_get(v___x_1597_, 0);
v_err_1603_ = lean_ctor_get(v___x_1597_, 1);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1597_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_err_1603_);
lean_inc(v_pos_1602_);
lean_dec(v___x_1597_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_pos_1602_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_err_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
else
{
lean_object* v___x_1611_; 
lean_dec_ref(v_parser_1585_);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v_a_1587_);
lean_ctor_set(v___x_1611_, 1, v_acc_1586_);
return v___x_1611_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go(lean_object* v_00_u03b1_1612_, lean_object* v_parser_1613_, lean_object* v_acc_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(v_parser_1613_, v_acc_1614_, v_a_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(lean_object* v_parser_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0));
v___x_1622_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(v_parser_1619_, v___x_1621_, v_a_1620_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero(lean_object* v_00_u03b1_1623_, lean_object* v_parser_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v_parser_1624_, v_a_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(lean_object* v_parser_1627_, lean_object* v_acc_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v_array_1630_; lean_object* v_idx_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v_array_1630_ = lean_ctor_get(v_a_1629_, 0);
v_idx_1631_ = lean_ctor_get(v_a_1629_, 1);
v___x_1632_ = lean_byte_array_size(v_array_1630_);
v___x_1633_ = lean_nat_dec_lt(v_idx_1631_, v___x_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
lean_dec_ref(v_acc_1628_);
lean_dec_ref(v_parser_1627_);
v___x_1634_ = lean_box(0);
v___x_1635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1635_, 0, v_a_1629_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
return v___x_1635_;
}
else
{
uint8_t v___x_1636_; uint8_t v___x_1655_; uint8_t v___x_1656_; uint8_t v___x_1657_; uint8_t v___x_1658_; 
v___x_1636_ = lean_byte_array_fget(v_array_1630_, v_idx_1631_);
v___x_1655_ = 1;
v___x_1656_ = lean_uint8_land(v___x_1655_, v___x_1636_);
v___x_1657_ = 0;
v___x_1658_ = lean_uint8_dec_eq(v___x_1656_, v___x_1657_);
if (v___x_1658_ == 0)
{
if (v___x_1633_ == 0)
{
goto v___jp_1637_;
}
else
{
lean_object* v___x_1659_; 
lean_dec_ref(v_parser_1627_);
v___x_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1659_, 0, v_a_1629_);
lean_ctor_set(v___x_1659_, 1, v_acc_1628_);
return v___x_1659_;
}
}
else
{
goto v___jp_1637_;
}
v___jp_1637_:
{
uint8_t v___x_1638_; uint8_t v___x_1639_; 
v___x_1638_ = 0;
v___x_1639_ = lean_uint8_dec_eq(v___x_1636_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; 
lean_inc_ref(v_parser_1627_);
v___x_1640_ = lean_apply_1(v_parser_1627_, v_a_1629_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_pos_1641_; lean_object* v_res_1642_; lean_object* v___x_1643_; 
v_pos_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_pos_1641_);
v_res_1642_ = lean_ctor_get(v___x_1640_, 1);
lean_inc(v_res_1642_);
lean_dec_ref_known(v___x_1640_, 2);
v___x_1643_ = lean_array_push(v_acc_1628_, v_res_1642_);
v_acc_1628_ = v___x_1643_;
v_a_1629_ = v_pos_1641_;
goto _start;
}
else
{
lean_object* v_pos_1645_; lean_object* v_err_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec_ref(v_acc_1628_);
lean_dec_ref(v_parser_1627_);
v_pos_1645_ = lean_ctor_get(v___x_1640_, 0);
v_err_1646_ = lean_ctor_get(v___x_1640_, 1);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1640_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_err_1646_);
lean_inc(v_pos_1645_);
lean_dec(v___x_1640_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_pos_1645_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_err_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_object* v___x_1654_; 
lean_dec_ref(v_parser_1627_);
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_a_1629_);
lean_ctor_set(v___x_1654_, 1, v_acc_1628_);
return v___x_1654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go(lean_object* v_00_u03b1_1660_, lean_object* v_parser_1661_, lean_object* v_acc_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(v_parser_1661_, v_acc_1662_, v_a_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(lean_object* v_parser_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0));
v___x_1668_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(v_parser_1665_, v___x_1667_, v_a_1666_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero(lean_object* v_00_u03b1_1669_, lean_object* v_parser_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(v_parser_1670_, v_a_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList(lean_object* v_a_1673_){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId), 1, 0);
v___x_1675_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(v___x_1674_, v_a_1673_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause(lean_object* v_a_1676_){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit), 1, 0);
v___x_1678_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v___x_1677_, v_a_1676_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(lean_object* v_acc_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v_array_1681_; lean_object* v_idx_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; 
v_array_1681_ = lean_ctor_get(v_a_1680_, 0);
v_idx_1682_ = lean_ctor_get(v_a_1680_, 1);
v___x_1683_ = lean_byte_array_size(v_array_1681_);
v___x_1684_ = lean_nat_dec_lt(v_idx_1682_, v___x_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_dec_ref(v_acc_1679_);
v___x_1685_ = lean_box(0);
v___x_1686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1686_, 0, v_a_1680_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
return v___x_1686_;
}
else
{
uint8_t v___x_1687_; uint8_t v___x_1717_; uint8_t v___x_1718_; uint8_t v___x_1719_; uint8_t v___x_1720_; 
v___x_1687_ = lean_byte_array_fget(v_array_1681_, v_idx_1682_);
v___x_1717_ = 1;
v___x_1718_ = lean_uint8_land(v___x_1717_, v___x_1687_);
v___x_1719_ = 0;
v___x_1720_ = lean_uint8_dec_eq(v___x_1718_, v___x_1719_);
if (v___x_1720_ == 0)
{
if (v___x_1684_ == 0)
{
goto v___jp_1688_;
}
else
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1721_, 0, v_a_1680_);
lean_ctor_set(v___x_1721_, 1, v_acc_1679_);
return v___x_1721_;
}
}
else
{
goto v___jp_1688_;
}
v___jp_1688_:
{
uint8_t v___x_1689_; uint8_t v___x_1690_; 
v___x_1689_ = 0;
v___x_1690_ = lean_uint8_dec_eq(v___x_1687_, v___x_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1680_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_pos_1692_; lean_object* v_res_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1706_; 
v_pos_1692_ = lean_ctor_get(v___x_1691_, 0);
v_res_1693_ = lean_ctor_get(v___x_1691_, 1);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1695_ = v___x_1691_;
v_isShared_1696_ = v_isSharedCheck_1706_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_res_1693_);
lean_inc(v_pos_1692_);
lean_dec(v___x_1691_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1706_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; uint8_t v___x_1698_; 
v___x_1697_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1698_ = lean_int_dec_lt(v___x_1697_, v_res_1693_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
lean_dec(v_res_1693_);
lean_dec_ref(v_acc_1679_);
v___x_1699_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 1);
lean_ctor_set(v___x_1695_, 1, v___x_1699_);
v___x_1701_ = v___x_1695_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_pos_1692_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
else
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_del_object(v___x_1695_);
v___x_1703_ = lean_nat_abs(v_res_1693_);
lean_dec(v_res_1693_);
v___x_1704_ = lean_array_push(v_acc_1679_, v___x_1703_);
v_acc_1679_ = v___x_1704_;
v_a_1680_ = v_pos_1692_;
goto _start;
}
}
}
else
{
lean_object* v_pos_1707_; lean_object* v_err_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec_ref(v_acc_1679_);
v_pos_1707_ = lean_ctor_get(v___x_1691_, 0);
v_err_1708_ = lean_ctor_get(v___x_1691_, 1);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1691_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_err_1708_);
lean_inc(v_pos_1707_);
lean_dec(v___x_1691_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_pos_1707_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_err_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
else
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1716_, 0, v_a_1680_);
lean_ctor_set(v___x_1716_, 1, v_acc_1679_);
return v___x_1716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(lean_object* v_a_1722_){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0));
v___x_1724_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(v___x_1723_, v_a_1722_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(lean_object* v_a_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1725_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_pos_1727_; lean_object* v_res_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1759_; 
v_pos_1727_ = lean_ctor_get(v___x_1726_, 0);
v_res_1728_ = lean_ctor_get(v___x_1726_, 1);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1730_ = v___x_1726_;
v_isShared_1731_ = v_isSharedCheck_1759_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_res_1728_);
lean_inc(v_pos_1727_);
lean_dec(v___x_1726_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1759_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1733_ = lean_int_dec_lt(v_res_1728_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1736_; 
lean_dec(v_res_1728_);
v___x_1734_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1));
if (v_isShared_1731_ == 0)
{
lean_ctor_set_tag(v___x_1730_, 1);
lean_ctor_set(v___x_1730_, 1, v___x_1734_);
v___x_1736_ = v___x_1730_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_pos_1727_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v___x_1734_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
else
{
lean_object* v___x_1738_; 
lean_del_object(v___x_1730_);
v___x_1738_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v_pos_1727_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_pos_1739_; lean_object* v_res_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1749_; 
v_pos_1739_ = lean_ctor_get(v___x_1738_, 0);
v_res_1740_ = lean_ctor_get(v___x_1738_, 1);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1742_ = v___x_1738_;
v_isShared_1743_ = v_isSharedCheck_1749_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_res_1740_);
lean_inc(v_pos_1739_);
lean_dec(v___x_1738_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1749_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1747_; 
v___x_1744_ = lean_nat_abs(v_res_1728_);
lean_dec(v_res_1728_);
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
lean_ctor_set(v___x_1745_, 1, v_res_1740_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 1, v___x_1745_);
v___x_1747_ = v___x_1742_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_pos_1739_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
else
{
lean_object* v_pos_1750_; lean_object* v_err_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
lean_dec(v_res_1728_);
v_pos_1750_ = lean_ctor_get(v___x_1738_, 0);
v_err_1751_ = lean_ctor_get(v___x_1738_, 1);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1738_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_err_1751_);
lean_inc(v_pos_1750_);
lean_dec(v___x_1738_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_pos_1750_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_err_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1760_; lean_object* v_err_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
v_pos_1760_ = lean_ctor_get(v___x_1726_, 0);
v_err_1761_ = lean_ctor_get(v___x_1726_, 1);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1726_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_err_1761_);
lean_inc(v_pos_1760_);
lean_dec(v___x_1726_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_pos_1760_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_err_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints(lean_object* v_a_1769_){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes), 1, 0);
v___x_1771_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v___x_1770_, v_a_1769_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(lean_object* v_acc_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v_array_1774_; lean_object* v_idx_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v_array_1774_ = lean_ctor_get(v_a_1773_, 0);
v_idx_1775_ = lean_ctor_get(v_a_1773_, 1);
v___x_1776_ = lean_byte_array_size(v_array_1774_);
v___x_1777_ = lean_nat_dec_lt(v_idx_1775_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
lean_dec_ref(v_acc_1772_);
v___x_1778_ = lean_box(0);
v___x_1779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1779_, 0, v_a_1773_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
return v___x_1779_;
}
else
{
uint8_t v___x_1780_; uint8_t v___x_1781_; uint8_t v___x_1782_; 
v___x_1780_ = lean_byte_array_fget(v_array_1774_, v_idx_1775_);
v___x_1781_ = 0;
v___x_1782_ = lean_uint8_dec_eq(v___x_1780_, v___x_1781_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1773_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_pos_1784_; lean_object* v_res_1785_; lean_object* v___x_1786_; 
v_pos_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_pos_1784_);
v_res_1785_ = lean_ctor_get(v___x_1783_, 1);
lean_inc(v_res_1785_);
lean_dec_ref_known(v___x_1783_, 2);
v___x_1786_ = lean_array_push(v_acc_1772_, v_res_1785_);
v_acc_1772_ = v___x_1786_;
v_a_1773_ = v_pos_1784_;
goto _start;
}
else
{
lean_object* v_pos_1788_; lean_object* v_err_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec_ref(v_acc_1772_);
v_pos_1788_ = lean_ctor_get(v___x_1783_, 0);
v_err_1789_ = lean_ctor_get(v___x_1783_, 1);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1783_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_err_1789_);
lean_inc(v_pos_1788_);
lean_dec(v___x_1783_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_pos_1788_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_err_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
else
{
lean_object* v___x_1797_; 
v___x_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1797_, 0, v_a_1773_);
lean_ctor_set(v___x_1797_, 1, v_acc_1772_);
return v___x_1797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(lean_object* v_a_1798_){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0));
v___x_1800_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(v___x_1799_, v_a_1798_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1_spec__2(lean_object* v_acc_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_array_1803_; lean_object* v_idx_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v_array_1803_ = lean_ctor_get(v_a_1802_, 0);
v_idx_1804_ = lean_ctor_get(v_a_1802_, 1);
v___x_1805_ = lean_byte_array_size(v_array_1803_);
v___x_1806_ = lean_nat_dec_lt(v_idx_1804_, v___x_1805_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_dec_ref(v_acc_1801_);
v___x_1807_ = lean_box(0);
v___x_1808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1808_, 0, v_a_1802_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
return v___x_1808_;
}
else
{
uint8_t v___x_1809_; uint8_t v___x_1810_; uint8_t v___x_1811_; 
v___x_1809_ = lean_byte_array_fget(v_array_1803_, v_idx_1804_);
v___x_1810_ = 0;
v___x_1811_ = lean_uint8_dec_eq(v___x_1809_, v___x_1810_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(v_a_1802_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_pos_1813_; lean_object* v_res_1814_; lean_object* v___x_1815_; 
v_pos_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_pos_1813_);
v_res_1814_ = lean_ctor_get(v___x_1812_, 1);
lean_inc(v_res_1814_);
lean_dec_ref_known(v___x_1812_, 2);
v___x_1815_ = lean_array_push(v_acc_1801_, v_res_1814_);
v_acc_1801_ = v___x_1815_;
v_a_1802_ = v_pos_1813_;
goto _start;
}
else
{
lean_object* v_pos_1817_; lean_object* v_err_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec_ref(v_acc_1801_);
v_pos_1817_ = lean_ctor_get(v___x_1812_, 0);
v_err_1818_ = lean_ctor_get(v___x_1812_, 1);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1812_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_err_1818_);
lean_inc(v_pos_1817_);
lean_dec(v___x_1812_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_pos_1817_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_err_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
else
{
lean_object* v___x_1826_; 
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v_a_1802_);
lean_ctor_set(v___x_1826_, 1, v_acc_1801_);
return v___x_1826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1(lean_object* v_a_1827_){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0));
v___x_1829_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1_spec__2(v___x_1828_, v_a_1827_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(lean_object* v_a_1830_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1830_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_pos_1832_; lean_object* v_res_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1962_; 
v_pos_1832_ = lean_ctor_get(v___x_1831_, 0);
v_res_1833_ = lean_ctor_get(v___x_1831_, 1);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1835_ = v___x_1831_;
v_isShared_1836_ = v_isSharedCheck_1962_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_res_1833_);
lean_inc(v_pos_1832_);
lean_dec(v___x_1831_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1962_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1837_ = lean_unsigned_to_nat(0u);
v___x_1838_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1839_ = lean_int_dec_lt(v___x_1838_, v_res_1833_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1842_; 
lean_dec(v_res_1833_);
v___x_1840_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1836_ == 0)
{
lean_ctor_set_tag(v___x_1835_, 1);
lean_ctor_set(v___x_1835_, 1, v___x_1840_);
v___x_1842_ = v___x_1835_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_pos_1832_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
else
{
lean_object* v___x_1844_; 
lean_del_object(v___x_1835_);
v___x_1844_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(v_pos_1832_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_pos_1845_; lean_object* v_res_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1952_; 
v_pos_1845_ = lean_ctor_get(v___x_1844_, 0);
v_res_1846_ = lean_ctor_get(v___x_1844_, 1);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1848_ = v___x_1844_;
v_isShared_1849_ = v_isSharedCheck_1952_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_res_1846_);
lean_inc(v_pos_1845_);
lean_dec(v___x_1844_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1952_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v_array_1850_; lean_object* v_idx_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
v_array_1850_ = lean_ctor_get(v_pos_1845_, 0);
v_idx_1851_ = lean_ctor_get(v_pos_1845_, 1);
v___x_1852_ = lean_byte_array_size(v_array_1850_);
v___x_1853_ = lean_nat_dec_lt(v_idx_1851_, v___x_1852_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
lean_dec(v_res_1846_);
lean_dec(v_res_1833_);
v___x_1854_ = lean_box(0);
if (v_isShared_1849_ == 0)
{
lean_ctor_set_tag(v___x_1848_, 1);
lean_ctor_set(v___x_1848_, 1, v___x_1854_);
v___x_1856_ = v___x_1848_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_pos_1845_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
else
{
uint8_t v___x_1858_; uint8_t v_got_1859_; uint8_t v___x_1860_; 
v___x_1858_ = 0;
v_got_1859_ = lean_byte_array_fget(v_array_1850_, v_idx_1851_);
v___x_1860_ = lean_uint8_dec_eq(v_got_1859_, v___x_1858_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
lean_dec(v_res_1846_);
lean_dec(v_res_1833_);
v___x_1861_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
if (v_isShared_1849_ == 0)
{
lean_ctor_set_tag(v___x_1848_, 1);
lean_ctor_set(v___x_1848_, 1, v___x_1861_);
v___x_1863_ = v___x_1848_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_pos_1845_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
else
{
lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1949_; 
lean_inc(v_idx_1851_);
lean_inc_ref(v_array_1850_);
lean_del_object(v___x_1848_);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_pos_1845_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; lean_object* v_unused_1951_; 
v_unused_1950_ = lean_ctor_get(v_pos_1845_, 1);
lean_dec(v_unused_1950_);
v_unused_1951_ = lean_ctor_get(v_pos_1845_, 0);
lean_dec(v_unused_1951_);
v___x_1866_ = v_pos_1845_;
v_isShared_1867_ = v_isSharedCheck_1949_;
goto v_resetjp_1865_;
}
else
{
lean_dec(v_pos_1845_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1949_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1871_; 
v___x_1868_ = lean_unsigned_to_nat(1u);
v___x_1869_ = lean_nat_add(v_idx_1851_, v___x_1868_);
lean_dec(v_idx_1851_);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 1, v___x_1869_);
v___x_1871_ = v___x_1866_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_array_1850_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v___x_1871_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_pos_1873_; lean_object* v_res_1874_; lean_object* v___x_1875_; 
v_pos_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_pos_1873_);
v_res_1874_ = lean_ctor_get(v___x_1872_, 1);
lean_inc(v_res_1874_);
lean_dec_ref_known(v___x_1872_, 2);
v___x_1875_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1(v_pos_1873_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_pos_1876_; lean_object* v_res_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1929_; 
v_pos_1876_ = lean_ctor_get(v___x_1875_, 0);
v_res_1877_ = lean_ctor_get(v___x_1875_, 1);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1879_ = v___x_1875_;
v_isShared_1880_ = v_isSharedCheck_1929_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_res_1877_);
lean_inc(v_pos_1876_);
lean_dec(v___x_1875_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1929_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v_array_1881_; lean_object* v_idx_1882_; lean_object* v___x_1883_; uint8_t v___x_1884_; 
v_array_1881_ = lean_ctor_get(v_pos_1876_, 0);
v_idx_1882_ = lean_ctor_get(v_pos_1876_, 1);
v___x_1883_ = lean_byte_array_size(v_array_1881_);
v___x_1884_ = lean_nat_dec_lt(v_idx_1882_, v___x_1883_);
if (v___x_1884_ == 0)
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
lean_dec(v_res_1877_);
lean_dec(v_res_1874_);
lean_dec(v_res_1846_);
lean_dec(v_res_1833_);
v___x_1885_ = lean_box(0);
if (v_isShared_1880_ == 0)
{
lean_ctor_set_tag(v___x_1879_, 1);
lean_ctor_set(v___x_1879_, 1, v___x_1885_);
v___x_1887_ = v___x_1879_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_pos_1876_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
else
{
uint8_t v_got_1889_; uint8_t v___x_1890_; 
v_got_1889_ = lean_byte_array_fget(v_array_1881_, v_idx_1882_);
v___x_1890_ = lean_uint8_dec_eq(v_got_1889_, v___x_1858_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
lean_dec(v_res_1877_);
lean_dec(v_res_1874_);
lean_dec(v_res_1846_);
lean_dec(v_res_1833_);
v___x_1891_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
if (v_isShared_1880_ == 0)
{
lean_ctor_set_tag(v___x_1879_, 1);
lean_ctor_set(v___x_1879_, 1, v___x_1891_);
v___x_1893_ = v___x_1879_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_pos_1876_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
else
{
lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1926_; 
lean_inc(v_idx_1882_);
lean_inc_ref(v_array_1881_);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_pos_1876_);
if (v_isSharedCheck_1926_ == 0)
{
lean_object* v_unused_1927_; lean_object* v_unused_1928_; 
v_unused_1927_ = lean_ctor_get(v_pos_1876_, 1);
lean_dec(v_unused_1927_);
v_unused_1928_ = lean_ctor_get(v_pos_1876_, 0);
lean_dec(v_unused_1928_);
v___x_1896_ = v_pos_1876_;
v_isShared_1897_ = v_isSharedCheck_1926_;
goto v_resetjp_1895_;
}
else
{
lean_dec(v_pos_1876_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1926_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1898_ = lean_nat_abs(v_res_1833_);
lean_dec(v_res_1833_);
v___x_1899_ = lean_nat_add(v_idx_1882_, v___x_1868_);
lean_dec(v_idx_1882_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 1, v___x_1899_);
v___x_1901_ = v___x_1896_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_array_1881_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1902_; uint8_t v___x_1903_; 
v___x_1902_ = lean_array_get_size(v_res_1846_);
v___x_1903_ = lean_nat_dec_eq(v___x_1902_, v___x_1837_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1904_ = lean_array_get_size(v_res_1877_);
v___x_1905_ = lean_nat_dec_eq(v___x_1904_, v___x_1837_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1906_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_1846_);
v___x_1907_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1898_);
lean_ctor_set(v___x_1907_, 1, v_res_1846_);
lean_ctor_set(v___x_1907_, 2, v___x_1906_);
lean_ctor_set(v___x_1907_, 3, v_res_1874_);
lean_ctor_set(v___x_1907_, 4, v_res_1877_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v___x_1907_);
lean_ctor_set(v___x_1879_, 0, v___x_1901_);
v___x_1909_ = v___x_1879_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
else
{
lean_object* v___x_1911_; lean_object* v___x_1913_; 
lean_dec(v_res_1877_);
v___x_1911_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1898_);
lean_ctor_set(v___x_1911_, 1, v_res_1846_);
lean_ctor_set(v___x_1911_, 2, v_res_1874_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v___x_1911_);
lean_ctor_set(v___x_1879_, 0, v___x_1901_);
v___x_1913_ = v___x_1879_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
else
{
lean_object* v___x_1915_; uint8_t v___x_1916_; 
lean_dec(v_res_1846_);
v___x_1915_ = lean_array_get_size(v_res_1877_);
lean_dec(v_res_1877_);
v___x_1916_ = lean_nat_dec_eq(v___x_1915_, v___x_1837_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; lean_object* v___x_1919_; 
lean_dec(v___x_1898_);
lean_dec(v_res_1874_);
v___x_1917_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2));
if (v_isShared_1880_ == 0)
{
lean_ctor_set_tag(v___x_1879_, 1);
lean_ctor_set(v___x_1879_, 1, v___x_1917_);
lean_ctor_set(v___x_1879_, 0, v___x_1901_);
v___x_1919_ = v___x_1879_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v___x_1917_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
else
{
lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1898_);
lean_ctor_set(v___x_1921_, 1, v_res_1874_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v___x_1921_);
lean_ctor_set(v___x_1879_, 0, v___x_1901_);
v___x_1923_ = v___x_1879_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
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
lean_object* v_pos_1930_; lean_object* v_err_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec(v_res_1874_);
lean_dec(v_res_1846_);
lean_dec(v_res_1833_);
v_pos_1930_ = lean_ctor_get(v___x_1875_, 0);
v_err_1931_ = lean_ctor_get(v___x_1875_, 1);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1875_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_err_1931_);
lean_inc(v_pos_1930_);
lean_dec(v___x_1875_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_pos_1930_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_err_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
else
{
lean_object* v_pos_1939_; lean_object* v_err_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec(v_res_1846_);
lean_dec(v_res_1833_);
v_pos_1939_ = lean_ctor_get(v___x_1872_, 0);
v_err_1940_ = lean_ctor_get(v___x_1872_, 1);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1872_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_err_1940_);
lean_inc(v_pos_1939_);
lean_dec(v___x_1872_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_pos_1939_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_err_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
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
lean_object* v_pos_1953_; lean_object* v_err_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v_res_1833_);
v_pos_1953_ = lean_ctor_get(v___x_1844_, 0);
v_err_1954_ = lean_ctor_get(v___x_1844_, 1);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1844_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_err_1954_);
lean_inc(v_pos_1953_);
lean_dec(v___x_1844_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_pos_1953_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_err_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1963_; lean_object* v_err_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
v_pos_1963_ = lean_ctor_get(v___x_1831_, 0);
v_err_1964_ = lean_ctor_get(v___x_1831_, 1);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1831_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_err_1964_);
lean_inc(v_pos_1963_);
lean_dec(v___x_1831_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_pos_1963_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_err_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(lean_object* v_a_1972_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v_a_1972_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_pos_1974_; lean_object* v_res_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2009_; 
v_pos_1974_ = lean_ctor_get(v___x_1973_, 0);
v_res_1975_ = lean_ctor_get(v___x_1973_, 1);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_1977_ = v___x_1973_;
v_isShared_1978_ = v_isSharedCheck_2009_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_res_1975_);
lean_inc(v_pos_1974_);
lean_dec(v___x_1973_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2009_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v_array_1979_; lean_object* v_idx_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
v_array_1979_ = lean_ctor_get(v_pos_1974_, 0);
v_idx_1980_ = lean_ctor_get(v_pos_1974_, 1);
v___x_1981_ = lean_byte_array_size(v_array_1979_);
v___x_1982_ = lean_nat_dec_lt(v_idx_1980_, v___x_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1985_; 
lean_dec(v_res_1975_);
v___x_1983_ = lean_box(0);
if (v_isShared_1978_ == 0)
{
lean_ctor_set_tag(v___x_1977_, 1);
lean_ctor_set(v___x_1977_, 1, v___x_1983_);
v___x_1985_ = v___x_1977_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_pos_1974_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
else
{
uint8_t v___x_1987_; uint8_t v_got_1988_; uint8_t v___x_1989_; 
v___x_1987_ = 0;
v_got_1988_ = lean_byte_array_fget(v_array_1979_, v_idx_1980_);
v___x_1989_ = lean_uint8_dec_eq(v_got_1988_, v___x_1987_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1992_; 
lean_dec(v_res_1975_);
v___x_1990_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
if (v_isShared_1978_ == 0)
{
lean_ctor_set_tag(v___x_1977_, 1);
lean_ctor_set(v___x_1977_, 1, v___x_1990_);
v___x_1992_ = v___x_1977_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_pos_1974_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
else
{
lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2006_; 
lean_inc(v_idx_1980_);
lean_inc_ref(v_array_1979_);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_pos_1974_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; lean_object* v_unused_2008_; 
v_unused_2007_ = lean_ctor_get(v_pos_1974_, 1);
lean_dec(v_unused_2007_);
v_unused_2008_ = lean_ctor_get(v_pos_1974_, 0);
lean_dec(v_unused_2008_);
v___x_1995_ = v_pos_1974_;
v_isShared_1996_ = v_isSharedCheck_2006_;
goto v_resetjp_1994_;
}
else
{
lean_dec(v_pos_1974_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2006_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1997_ = lean_unsigned_to_nat(1u);
v___x_1998_ = lean_nat_add(v_idx_1980_, v___x_1997_);
lean_dec(v_idx_1980_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 1, v___x_1998_);
v___x_2000_ = v___x_1995_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_array_1979_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2005_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2001_; lean_object* v___x_2003_; 
v___x_2001_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2001_, 0, v_res_1975_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 1, v___x_2001_);
lean_ctor_set(v___x_1977_, 0, v___x_2000_);
v___x_2003_ = v___x_1977_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2000_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_2010_; lean_object* v_err_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
v_pos_2010_ = lean_ctor_get(v___x_1973_, 0);
v_err_2011_ = lean_ctor_get(v___x_1973_, 1);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_1973_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_err_2011_);
lean_inc(v_pos_2010_);
lean_dec(v___x_1973_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_pos_2010_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_err_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0(void){
_start:
{
uint32_t v___x_2019_; uint8_t v___x_2020_; 
v___x_2019_ = 97;
v___x_2020_ = lean_uint32_to_uint8(v___x_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(lean_object* v_a_2022_){
_start:
{
lean_object* v_array_2023_; lean_object* v_idx_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; 
v_array_2023_ = lean_ctor_get(v_a_2022_, 0);
v_idx_2024_ = lean_ctor_get(v_a_2022_, 1);
v___x_2025_ = lean_byte_array_size(v_array_2023_);
v___x_2026_ = lean_nat_dec_lt(v_idx_2024_, v___x_2025_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = lean_box(0);
v___x_2028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2028_, 0, v_a_2022_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
return v___x_2028_;
}
else
{
lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2050_; 
lean_inc(v_idx_2024_);
lean_inc_ref(v_array_2023_);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_a_2022_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; lean_object* v_unused_2052_; 
v_unused_2051_ = lean_ctor_get(v_a_2022_, 1);
lean_dec(v_unused_2051_);
v_unused_2052_ = lean_ctor_get(v_a_2022_, 0);
lean_dec(v_unused_2052_);
v___x_2030_ = v_a_2022_;
v_isShared_2031_ = v_isSharedCheck_2050_;
goto v_resetjp_2029_;
}
else
{
lean_dec(v_a_2022_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2050_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
uint8_t v_c_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v_it_x27_2036_; 
v_c_2032_ = lean_byte_array_fget(v_array_2023_, v_idx_2024_);
v___x_2033_ = lean_unsigned_to_nat(1u);
v___x_2034_ = lean_nat_add(v_idx_2024_, v___x_2033_);
lean_dec(v_idx_2024_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 1, v___x_2034_);
v_it_x27_2036_ = v___x_2030_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_array_2023_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v___x_2034_);
v_it_x27_2036_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
uint8_t v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
v___x_2038_ = lean_uint8_dec_eq(v_c_2032_, v___x_2037_);
if (v___x_2038_ == 0)
{
uint8_t v___x_2039_; uint8_t v___x_2040_; 
v___x_2039_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
v___x_2040_ = lean_uint8_dec_eq(v_c_2032_, v___x_2039_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2041_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1));
v___x_2042_ = lean_uint8_to_nat(v_c_2032_);
v___x_2043_ = l_Nat_reprFast(v___x_2042_);
v___x_2044_ = lean_string_append(v___x_2041_, v___x_2043_);
lean_dec_ref(v___x_2043_);
v___x_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
v___x_2046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2046_, 0, v_it_x27_2036_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
return v___x_2046_;
}
else
{
lean_object* v___x_2047_; 
v___x_2047_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(v_it_x27_2036_);
return v___x_2047_;
}
}
else
{
lean_object* v___x_2048_; 
v___x_2048_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(v_it_x27_2036_);
return v___x_2048_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(lean_object* v_acc_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v___x_2055_; 
lean_inc_ref(v_a_2054_);
v___x_2055_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(v_a_2054_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_pos_2056_; lean_object* v_res_2057_; lean_object* v___x_2058_; 
lean_dec_ref(v_a_2054_);
v_pos_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_pos_2056_);
v_res_2057_ = lean_ctor_get(v___x_2055_, 1);
lean_inc(v_res_2057_);
lean_dec_ref_known(v___x_2055_, 2);
v___x_2058_ = lean_array_push(v_acc_2053_, v_res_2057_);
v_acc_2053_ = v___x_2058_;
v_a_2054_ = v_pos_2056_;
goto _start;
}
else
{
lean_object* v_pos_2060_; lean_object* v_err_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2074_; 
v_pos_2060_ = lean_ctor_get(v___x_2055_, 0);
v_err_2061_ = lean_ctor_get(v___x_2055_, 1);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2063_ = v___x_2055_;
v_isShared_2064_ = v_isSharedCheck_2074_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_err_2061_);
lean_inc(v_pos_2060_);
lean_dec(v___x_2055_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2074_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v_idx_2065_; lean_object* v_idx_2066_; uint8_t v___x_2067_; 
v_idx_2065_ = lean_ctor_get(v_a_2054_, 1);
lean_inc(v_idx_2065_);
lean_dec_ref(v_a_2054_);
v_idx_2066_ = lean_ctor_get(v_pos_2060_, 1);
v___x_2067_ = lean_nat_dec_eq(v_idx_2065_, v_idx_2066_);
lean_dec(v_idx_2065_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2069_; 
lean_dec_ref(v_acc_2053_);
if (v_isShared_2064_ == 0)
{
v___x_2069_ = v___x_2063_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_pos_2060_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v_err_2061_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
else
{
lean_object* v___x_2072_; 
lean_dec(v_err_2061_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set_tag(v___x_2063_, 0);
lean_ctor_set(v___x_2063_, 1, v_acc_2053_);
v___x_2072_ = v___x_2063_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_pos_2060_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v_acc_2053_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(lean_object* v_a_2078_){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0));
v___x_2080_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(v___x_2079_, v_a_2078_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_pos_2081_; lean_object* v_array_2082_; lean_object* v_idx_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v_pos_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_pos_2081_);
v_array_2082_ = lean_ctor_get(v_pos_2081_, 0);
v_idx_2083_ = lean_ctor_get(v_pos_2081_, 1);
v___x_2084_ = lean_byte_array_size(v_array_2082_);
v___x_2085_ = lean_nat_dec_lt(v_idx_2083_, v___x_2084_);
if (v___x_2085_ == 0)
{
lean_dec(v_pos_2081_);
return v___x_2080_;
}
else
{
lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2093_; 
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; lean_object* v_unused_2095_; 
v_unused_2094_ = lean_ctor_get(v___x_2080_, 1);
lean_dec(v_unused_2094_);
v_unused_2095_ = lean_ctor_get(v___x_2080_, 0);
lean_dec(v_unused_2095_);
v___x_2087_ = v___x_2080_;
v_isShared_2088_ = v_isSharedCheck_2093_;
goto v_resetjp_2086_;
}
else
{
lean_dec(v___x_2080_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2093_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2089_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__1));
if (v_isShared_2088_ == 0)
{
lean_ctor_set_tag(v___x_2087_, 1);
lean_ctor_set(v___x_2087_, 1, v___x_2089_);
v___x_2091_ = v___x_2087_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_pos_2081_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
else
{
return v___x_2080_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_parseActions(lean_object* v_a_2096_){
_start:
{
uint8_t v___y_2098_; lean_object* v_array_2101_; lean_object* v_idx_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; 
v_array_2101_ = lean_ctor_get(v_a_2096_, 0);
v_idx_2102_ = lean_ctor_get(v_a_2096_, 1);
v___x_2103_ = lean_byte_array_size(v_array_2101_);
v___x_2104_ = lean_nat_dec_lt(v_idx_2102_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = lean_box(0);
v___x_2106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2106_, 0, v_a_2096_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
return v___x_2106_;
}
else
{
uint8_t v___x_2107_; uint8_t v___x_2108_; uint8_t v___x_2109_; 
v___x_2107_ = lean_byte_array_fget(v_array_2101_, v_idx_2102_);
v___x_2108_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
v___x_2109_ = lean_uint8_dec_eq(v___x_2107_, v___x_2108_);
if (v___x_2109_ == 0)
{
uint8_t v___x_2110_; uint8_t v___x_2111_; 
v___x_2110_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
v___x_2111_ = lean_uint8_dec_eq(v___x_2107_, v___x_2110_);
v___y_2098_ = v___x_2111_;
goto v___jp_2097_;
}
else
{
v___y_2098_ = v___x_2109_;
goto v___jp_2097_;
}
}
v___jp_2097_:
{
if (v___y_2098_ == 0)
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(v_a_2096_);
return v___x_2099_;
}
else
{
lean_object* v___x_2100_; 
v___x_2100_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(v_a_2096_);
return v___x_2100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object* v_path_2112_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_IO_FS_readBinFile(v_path_2112_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2136_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2117_ = v___x_2114_;
v_isShared_2118_ = v_isSharedCheck_2136_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2136_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_parseActions), 1, 0);
v___x_2120_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_2119_, v_a_2115_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2131_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2131_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2131_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
lean_ctor_set_tag(v___x_2123_, 18);
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2128_; 
if (v_isShared_2118_ == 0)
{
lean_ctor_set_tag(v___x_2117_, 1);
lean_ctor_set(v___x_2117_, 0, v___x_2126_);
v___x_2128_ = v___x_2117_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; 
v_a_2132_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2120_, 1);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 0, v_a_2132_);
v___x_2134_ = v___x_2117_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
v_a_2137_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2114_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2114_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof___boxed(lean_object* v_path_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(v_path_2145_);
lean_dec_ref(v_path_2145_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_parseLRATProof(lean_object* v_proof_2148_){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_parseActions), 1, 0);
v___x_2150_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_2149_, v_proof_2148_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(lean_object* v_as_2152_, size_t v_i_2153_, size_t v_stop_2154_, lean_object* v_b_2155_){
_start:
{
uint8_t v___x_2156_; 
v___x_2156_ = lean_usize_dec_eq(v_i_2153_, v_stop_2154_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; size_t v___x_2162_; size_t v___x_2163_; 
v___x_2157_ = lean_array_uget_borrowed(v_as_2152_, v_i_2153_);
lean_inc(v___x_2157_);
v___x_2158_ = l_Nat_reprFast(v___x_2157_);
v___x_2159_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2160_ = lean_string_append(v___x_2158_, v___x_2159_);
v___x_2161_ = lean_string_append(v_b_2155_, v___x_2160_);
lean_dec_ref(v___x_2160_);
v___x_2162_ = ((size_t)1ULL);
v___x_2163_ = lean_usize_add(v_i_2153_, v___x_2162_);
v_i_2153_ = v___x_2163_;
v_b_2155_ = v___x_2161_;
goto _start;
}
else
{
return v_b_2155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___boxed(lean_object* v_as_2165_, lean_object* v_i_2166_, lean_object* v_stop_2167_, lean_object* v_b_2168_){
_start:
{
size_t v_i_boxed_2169_; size_t v_stop_boxed_2170_; lean_object* v_res_2171_; 
v_i_boxed_2169_ = lean_unbox_usize(v_i_2166_);
lean_dec(v_i_2166_);
v_stop_boxed_2170_ = lean_unbox_usize(v_stop_2167_);
lean_dec(v_stop_2167_);
v_res_2171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_as_2165_, v_i_boxed_2169_, v_stop_boxed_2170_, v_b_2168_);
lean_dec_ref(v_as_2165_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(lean_object* v_ids_2173_){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2174_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2175_ = lean_unsigned_to_nat(0u);
v___x_2176_ = lean_array_get_size(v_ids_2173_);
v___x_2177_ = lean_nat_dec_lt(v___x_2175_, v___x_2176_);
if (v___x_2177_ == 0)
{
return v___x_2174_;
}
else
{
uint8_t v___x_2178_; 
v___x_2178_ = lean_nat_dec_le(v___x_2176_, v___x_2176_);
if (v___x_2178_ == 0)
{
if (v___x_2177_ == 0)
{
return v___x_2174_;
}
else
{
size_t v___x_2179_; size_t v___x_2180_; lean_object* v___x_2181_; 
v___x_2179_ = ((size_t)0ULL);
v___x_2180_ = lean_usize_of_nat(v___x_2176_);
v___x_2181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_ids_2173_, v___x_2179_, v___x_2180_, v___x_2174_);
return v___x_2181_;
}
}
else
{
size_t v___x_2182_; size_t v___x_2183_; lean_object* v___x_2184_; 
v___x_2182_ = ((size_t)0ULL);
v___x_2183_ = lean_usize_of_nat(v___x_2176_);
v___x_2184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_ids_2173_, v___x_2182_, v___x_2183_, v___x_2174_);
return v___x_2184_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___boxed(lean_object* v_ids_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_ids_2185_);
lean_dec_ref(v_ids_2185_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(lean_object* v_hint_2188_){
_start:
{
lean_object* v_fst_2189_; lean_object* v_snd_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v_fst_2189_ = lean_ctor_get(v_hint_2188_, 0);
lean_inc(v_fst_2189_);
v_snd_2190_ = lean_ctor_get(v_hint_2188_, 1);
lean_inc(v_snd_2190_);
lean_dec_ref(v_hint_2188_);
v___x_2191_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0));
v___x_2192_ = l_Nat_reprFast(v_fst_2189_);
v___x_2193_ = lean_string_append(v___x_2191_, v___x_2192_);
lean_dec_ref(v___x_2192_);
v___x_2194_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2195_ = lean_string_append(v___x_2193_, v___x_2194_);
v___x_2196_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_snd_2190_);
lean_dec(v_snd_2190_);
v___x_2197_ = lean_string_append(v___x_2195_, v___x_2196_);
lean_dec_ref(v___x_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(lean_object* v_as_2198_, size_t v_i_2199_, size_t v_stop_2200_, lean_object* v_b_2201_){
_start:
{
uint8_t v___x_2202_; 
v___x_2202_ = lean_usize_dec_eq(v_i_2199_, v_stop_2200_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; size_t v___x_2206_; size_t v___x_2207_; 
v___x_2203_ = lean_array_uget_borrowed(v_as_2198_, v_i_2199_);
lean_inc(v___x_2203_);
v___x_2204_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(v___x_2203_);
v___x_2205_ = lean_string_append(v_b_2201_, v___x_2204_);
lean_dec_ref(v___x_2204_);
v___x_2206_ = ((size_t)1ULL);
v___x_2207_ = lean_usize_add(v_i_2199_, v___x_2206_);
v_i_2199_ = v___x_2207_;
v_b_2201_ = v___x_2205_;
goto _start;
}
else
{
return v_b_2201_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0___boxed(lean_object* v_as_2209_, lean_object* v_i_2210_, lean_object* v_stop_2211_, lean_object* v_b_2212_){
_start:
{
size_t v_i_boxed_2213_; size_t v_stop_boxed_2214_; lean_object* v_res_2215_; 
v_i_boxed_2213_ = lean_unbox_usize(v_i_2210_);
lean_dec(v_i_2210_);
v_stop_boxed_2214_ = lean_unbox_usize(v_stop_2211_);
lean_dec(v_stop_2211_);
v_res_2215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_as_2209_, v_i_boxed_2213_, v_stop_boxed_2214_, v_b_2212_);
lean_dec_ref(v_as_2209_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(lean_object* v_hints_2216_){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; 
v___x_2217_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2218_ = lean_unsigned_to_nat(0u);
v___x_2219_ = lean_array_get_size(v_hints_2216_);
v___x_2220_ = lean_nat_dec_lt(v___x_2218_, v___x_2219_);
if (v___x_2220_ == 0)
{
return v___x_2217_;
}
else
{
uint8_t v___x_2221_; 
v___x_2221_ = lean_nat_dec_le(v___x_2219_, v___x_2219_);
if (v___x_2221_ == 0)
{
if (v___x_2220_ == 0)
{
return v___x_2217_;
}
else
{
size_t v___x_2222_; size_t v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = ((size_t)0ULL);
v___x_2223_ = lean_usize_of_nat(v___x_2219_);
v___x_2224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_hints_2216_, v___x_2222_, v___x_2223_, v___x_2217_);
return v___x_2224_;
}
}
else
{
size_t v___x_2225_; size_t v___x_2226_; lean_object* v___x_2227_; 
v___x_2225_ = ((size_t)0ULL);
v___x_2226_ = lean_usize_of_nat(v___x_2219_);
v___x_2227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_hints_2216_, v___x_2225_, v___x_2226_, v___x_2217_);
return v___x_2227_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___boxed(lean_object* v_hints_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(v_hints_2228_);
lean_dec_ref(v_hints_2228_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(lean_object* v_as_2230_, size_t v_i_2231_, size_t v_stop_2232_, lean_object* v_b_2233_){
_start:
{
uint8_t v___x_2234_; 
v___x_2234_ = lean_usize_dec_eq(v_i_2231_, v_stop_2232_);
if (v___x_2234_ == 0)
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; size_t v___x_2240_; size_t v___x_2241_; 
v___x_2235_ = lean_array_uget_borrowed(v_as_2230_, v_i_2231_);
v___x_2236_ = l_Int_repr(v___x_2235_);
v___x_2237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2238_ = lean_string_append(v___x_2236_, v___x_2237_);
v___x_2239_ = lean_string_append(v_b_2233_, v___x_2238_);
lean_dec_ref(v___x_2238_);
v___x_2240_ = ((size_t)1ULL);
v___x_2241_ = lean_usize_add(v_i_2231_, v___x_2240_);
v_i_2231_ = v___x_2241_;
v_b_2233_ = v___x_2239_;
goto _start;
}
else
{
return v_b_2233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0___boxed(lean_object* v_as_2243_, lean_object* v_i_2244_, lean_object* v_stop_2245_, lean_object* v_b_2246_){
_start:
{
size_t v_i_boxed_2247_; size_t v_stop_boxed_2248_; lean_object* v_res_2249_; 
v_i_boxed_2247_ = lean_unbox_usize(v_i_2244_);
lean_dec(v_i_2244_);
v_stop_boxed_2248_ = lean_unbox_usize(v_stop_2245_);
lean_dec(v_stop_2245_);
v_res_2249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_as_2243_, v_i_boxed_2247_, v_stop_boxed_2248_, v_b_2246_);
lean_dec_ref(v_as_2243_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(lean_object* v_clause_2250_){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; 
v___x_2251_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2252_ = lean_unsigned_to_nat(0u);
v___x_2253_ = lean_array_get_size(v_clause_2250_);
v___x_2254_ = lean_nat_dec_lt(v___x_2252_, v___x_2253_);
if (v___x_2254_ == 0)
{
return v___x_2251_;
}
else
{
uint8_t v___x_2255_; 
v___x_2255_ = lean_nat_dec_le(v___x_2253_, v___x_2253_);
if (v___x_2255_ == 0)
{
if (v___x_2254_ == 0)
{
return v___x_2251_;
}
else
{
size_t v___x_2256_; size_t v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = ((size_t)0ULL);
v___x_2257_ = lean_usize_of_nat(v___x_2253_);
v___x_2258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_clause_2250_, v___x_2256_, v___x_2257_, v___x_2251_);
return v___x_2258_;
}
}
else
{
size_t v___x_2259_; size_t v___x_2260_; lean_object* v___x_2261_; 
v___x_2259_ = ((size_t)0ULL);
v___x_2260_ = lean_usize_of_nat(v___x_2253_);
v___x_2261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_clause_2250_, v___x_2259_, v___x_2260_, v___x_2251_);
return v___x_2261_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___boxed(lean_object* v_clause_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_clause_2262_);
lean_dec_ref(v_clause_2262_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(lean_object* v_a_2268_){
_start:
{
switch(lean_obj_tag(v_a_2268_))
{
case 0:
{
lean_object* v_id_2269_; lean_object* v_rupHints_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v_id_2269_ = lean_ctor_get(v_a_2268_, 0);
lean_inc(v_id_2269_);
v_rupHints_2270_ = lean_ctor_get(v_a_2268_, 1);
lean_inc_ref(v_rupHints_2270_);
lean_dec_ref_known(v_a_2268_, 2);
v___x_2271_ = l_Nat_reprFast(v_id_2269_);
v___x_2272_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__0));
v___x_2273_ = lean_string_append(v___x_2271_, v___x_2272_);
v___x_2274_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2270_);
lean_dec_ref(v_rupHints_2270_);
v___x_2275_ = lean_string_append(v___x_2273_, v___x_2274_);
lean_dec_ref(v___x_2274_);
v___x_2276_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2277_ = lean_string_append(v___x_2275_, v___x_2276_);
return v___x_2277_;
}
case 1:
{
lean_object* v_id_2278_; lean_object* v_c_2279_; lean_object* v_rupHints_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v_id_2278_ = lean_ctor_get(v_a_2268_, 0);
lean_inc(v_id_2278_);
v_c_2279_ = lean_ctor_get(v_a_2268_, 1);
lean_inc(v_c_2279_);
v_rupHints_2280_ = lean_ctor_get(v_a_2268_, 2);
lean_inc_ref(v_rupHints_2280_);
lean_dec_ref_known(v_a_2268_, 3);
v___x_2281_ = l_Nat_reprFast(v_id_2278_);
v___x_2282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2283_ = lean_string_append(v___x_2281_, v___x_2282_);
v___x_2284_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_c_2279_);
lean_dec(v_c_2279_);
v___x_2285_ = lean_string_append(v___x_2283_, v___x_2284_);
lean_dec_ref(v___x_2284_);
v___x_2286_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2));
v___x_2287_ = lean_string_append(v___x_2285_, v___x_2286_);
v___x_2288_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2280_);
lean_dec_ref(v_rupHints_2280_);
v___x_2289_ = lean_string_append(v___x_2287_, v___x_2288_);
lean_dec_ref(v___x_2288_);
v___x_2290_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2291_ = lean_string_append(v___x_2289_, v___x_2290_);
return v___x_2291_;
}
case 2:
{
lean_object* v_id_2292_; lean_object* v_c_2293_; lean_object* v_rupHints_2294_; lean_object* v_ratHints_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v_id_2292_ = lean_ctor_get(v_a_2268_, 0);
lean_inc(v_id_2292_);
v_c_2293_ = lean_ctor_get(v_a_2268_, 1);
lean_inc(v_c_2293_);
v_rupHints_2294_ = lean_ctor_get(v_a_2268_, 3);
lean_inc_ref(v_rupHints_2294_);
v_ratHints_2295_ = lean_ctor_get(v_a_2268_, 4);
lean_inc_ref(v_ratHints_2295_);
lean_dec_ref_known(v_a_2268_, 5);
v___x_2296_ = l_Nat_reprFast(v_id_2292_);
v___x_2297_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2298_ = lean_string_append(v___x_2296_, v___x_2297_);
v___x_2299_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_c_2293_);
lean_dec(v_c_2293_);
v___x_2300_ = lean_string_append(v___x_2298_, v___x_2299_);
lean_dec_ref(v___x_2299_);
v___x_2301_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2));
v___x_2302_ = lean_string_append(v___x_2300_, v___x_2301_);
v___x_2303_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2294_);
lean_dec_ref(v_rupHints_2294_);
v___x_2304_ = lean_string_append(v___x_2302_, v___x_2303_);
lean_dec_ref(v___x_2303_);
v___x_2305_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(v_ratHints_2295_);
lean_dec_ref(v_ratHints_2295_);
v___x_2306_ = lean_string_append(v___x_2304_, v___x_2305_);
lean_dec_ref(v___x_2305_);
v___x_2307_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2308_ = lean_string_append(v___x_2306_, v___x_2307_);
return v___x_2308_;
}
default: 
{
lean_object* v_ids_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v_ids_2309_ = lean_ctor_get(v_a_2268_, 0);
lean_inc_ref(v_ids_2309_);
lean_dec_ref_known(v_a_2268_, 1);
v___x_2310_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3));
v___x_2311_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_ids_2309_);
lean_dec_ref(v_ids_2309_);
v___x_2312_ = lean_string_append(v___x_2310_, v___x_2311_);
lean_dec_ref(v___x_2311_);
v___x_2313_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2314_ = lean_string_append(v___x_2312_, v___x_2313_);
return v___x_2314_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(lean_object* v_as_2316_, size_t v_i_2317_, size_t v_stop_2318_, lean_object* v_b_2319_){
_start:
{
uint8_t v___x_2320_; 
v___x_2320_ = lean_usize_dec_eq(v_i_2317_, v_stop_2318_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; size_t v___x_2326_; size_t v___x_2327_; 
v___x_2321_ = lean_array_uget_borrowed(v_as_2316_, v_i_2317_);
lean_inc(v___x_2321_);
v___x_2322_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(v___x_2321_);
v___x_2323_ = lean_string_append(v_b_2319_, v___x_2322_);
lean_dec_ref(v___x_2322_);
v___x_2324_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___closed__0));
v___x_2325_ = lean_string_append(v___x_2323_, v___x_2324_);
v___x_2326_ = ((size_t)1ULL);
v___x_2327_ = lean_usize_add(v_i_2317_, v___x_2326_);
v_i_2317_ = v___x_2327_;
v_b_2319_ = v___x_2325_;
goto _start;
}
else
{
return v_b_2319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___boxed(lean_object* v_as_2329_, lean_object* v_i_2330_, lean_object* v_stop_2331_, lean_object* v_b_2332_){
_start:
{
size_t v_i_boxed_2333_; size_t v_stop_boxed_2334_; lean_object* v_res_2335_; 
v_i_boxed_2333_ = lean_unbox_usize(v_i_2330_);
lean_dec(v_i_2330_);
v_stop_boxed_2334_ = lean_unbox_usize(v_stop_2331_);
lean_dec(v_stop_2331_);
v_res_2335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_as_2329_, v_i_boxed_2333_, v_stop_boxed_2334_, v_b_2332_);
lean_dec_ref(v_as_2329_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString(lean_object* v_proof_2336_){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v___x_2337_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2338_ = lean_unsigned_to_nat(0u);
v___x_2339_ = lean_array_get_size(v_proof_2336_);
v___x_2340_ = lean_nat_dec_lt(v___x_2338_, v___x_2339_);
if (v___x_2340_ == 0)
{
return v___x_2337_;
}
else
{
uint8_t v___x_2341_; 
v___x_2341_ = lean_nat_dec_le(v___x_2339_, v___x_2339_);
if (v___x_2341_ == 0)
{
if (v___x_2340_ == 0)
{
return v___x_2337_;
}
else
{
size_t v___x_2342_; size_t v___x_2343_; lean_object* v___x_2344_; 
v___x_2342_ = ((size_t)0ULL);
v___x_2343_ = lean_usize_of_nat(v___x_2339_);
v___x_2344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_proof_2336_, v___x_2342_, v___x_2343_, v___x_2337_);
return v___x_2344_;
}
}
else
{
size_t v___x_2345_; size_t v___x_2346_; lean_object* v___x_2347_; 
v___x_2345_ = ((size_t)0ULL);
v___x_2346_ = lean_usize_of_nat(v___x_2339_);
v___x_2347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_proof_2336_, v___x_2345_, v___x_2346_, v___x_2337_);
return v___x_2347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString___boxed(lean_object* v_proof_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_proof_2348_);
lean_dec_ref(v_proof_2348_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startDelete(lean_object* v_acc_2350_){
_start:
{
uint8_t v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
v___x_2352_ = lean_byte_array_push(v_acc_2350_, v___x_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(lean_object* v_acc_2353_, uint64_t v_lit_2354_){
_start:
{
uint8_t v___y_2356_; uint64_t v___x_2361_; uint8_t v___x_2362_; 
v___x_2361_ = 0ULL;
v___x_2362_ = lean_uint64_dec_eq(v_lit_2354_, v___x_2361_);
if (v___x_2362_ == 0)
{
uint64_t v___x_2363_; uint8_t v___x_2364_; 
v___x_2363_ = 127ULL;
v___x_2364_ = lean_uint64_dec_lt(v___x_2363_, v_lit_2354_);
if (v___x_2364_ == 0)
{
uint8_t v___x_2365_; uint8_t v___x_2366_; uint8_t v___x_2367_; 
v___x_2365_ = lean_uint64_to_uint8(v_lit_2354_);
v___x_2366_ = 127;
v___x_2367_ = lean_uint8_land(v___x_2365_, v___x_2366_);
v___y_2356_ = v___x_2367_;
goto v___jp_2355_;
}
else
{
uint8_t v___x_2368_; uint8_t v___x_2369_; uint8_t v___x_2370_; uint8_t v___x_2371_; uint8_t v___x_2372_; 
v___x_2368_ = lean_uint64_to_uint8(v_lit_2354_);
v___x_2369_ = 127;
v___x_2370_ = lean_uint8_land(v___x_2368_, v___x_2369_);
v___x_2371_ = 128;
v___x_2372_ = lean_uint8_lor(v___x_2370_, v___x_2371_);
v___y_2356_ = v___x_2372_;
goto v___jp_2355_;
}
}
else
{
return v_acc_2353_;
}
v___jp_2355_:
{
lean_object* v_acc_2357_; uint64_t v___x_2358_; uint64_t v___x_2359_; 
v_acc_2357_ = lean_byte_array_push(v_acc_2353_, v___y_2356_);
v___x_2358_ = 7ULL;
v___x_2359_ = lean_uint64_shift_right(v_lit_2354_, v___x_2358_);
v_acc_2353_ = v_acc_2357_;
v_lit_2354_ = v___x_2359_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode___boxed(lean_object* v_acc_2373_, lean_object* v_lit_2374_){
_start:
{
uint64_t v_lit_boxed_2375_; lean_object* v_res_2376_; 
v_lit_boxed_2375_ = lean_unbox_uint64(v_lit_2374_);
lean_dec_ref(v_lit_2374_);
v_res_2376_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(v_acc_2373_, v_lit_boxed_2375_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(lean_object* v_msg_2377_){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = l_ByteArray_empty;
v___x_2379_ = lean_panic_fn_borrowed(v___x_2378_, v_msg_2377_);
return v___x_2379_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0(void){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = lean_cstr_to_nat("18446744073709551615");
return v___x_2380_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2384_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3));
v___x_2385_ = lean_unsigned_to_nat(4u);
v___x_2386_ = lean_unsigned_to_nat(388u);
v___x_2387_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2));
v___x_2388_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1));
v___x_2389_ = l_mkPanicMessageWithDecl(v___x_2388_, v___x_2387_, v___x_2386_, v___x_2385_, v___x_2384_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(lean_object* v_acc_2390_, lean_object* v_lit_2391_){
_start:
{
lean_object* v___y_2393_; lean_object* v___x_2400_; uint8_t v___x_2401_; 
v___x_2400_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_2401_ = lean_int_dec_lt(v___x_2400_, v_lit_2391_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2402_ = lean_unsigned_to_nat(2u);
v___x_2403_ = lean_nat_abs(v_lit_2391_);
v___x_2404_ = lean_nat_mul(v___x_2402_, v___x_2403_);
lean_dec(v___x_2403_);
v___x_2405_ = lean_unsigned_to_nat(1u);
v___x_2406_ = lean_nat_add(v___x_2404_, v___x_2405_);
lean_dec(v___x_2404_);
v___y_2393_ = v___x_2406_;
goto v___jp_2392_;
}
else
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2407_ = lean_unsigned_to_nat(2u);
v___x_2408_ = lean_nat_abs(v_lit_2391_);
v___x_2409_ = lean_nat_mul(v___x_2407_, v___x_2408_);
lean_dec(v___x_2408_);
v___y_2393_ = v___x_2409_;
goto v___jp_2392_;
}
v___jp_2392_:
{
lean_object* v___x_2394_; uint8_t v___x_2395_; 
v___x_2394_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0);
v___x_2395_ = lean_nat_dec_le(v___y_2393_, v___x_2394_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
lean_dec(v___y_2393_);
lean_dec_ref(v_acc_2390_);
v___x_2396_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4);
v___x_2397_ = l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(v___x_2396_);
return v___x_2397_;
}
else
{
uint64_t v_mapped_2398_; lean_object* v___x_2399_; 
v_mapped_2398_ = lean_uint64_of_nat(v___y_2393_);
lean_dec(v___y_2393_);
v___x_2399_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(v_acc_2390_, v_mapped_2398_);
return v___x_2399_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___boxed(lean_object* v_acc_2410_, lean_object* v_lit_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2410_, v_lit_2411_);
lean_dec(v_lit_2411_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_zeroByte(lean_object* v_acc_2413_){
_start:
{
uint8_t v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = 0;
v___x_2415_ = lean_byte_array_push(v_acc_2413_, v___x_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addNat(lean_object* v_acc_2416_, lean_object* v_n_2417_){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = lean_nat_to_int(v_n_2417_);
v___x_2419_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2416_, v___x_2418_);
lean_dec(v___x_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startAdd(lean_object* v_acc_2420_){
_start:
{
uint8_t v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
v___x_2422_ = lean_byte_array_push(v_acc_2420_, v___x_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(lean_object* v_as_2423_, size_t v_i_2424_, size_t v_stop_2425_, lean_object* v_b_2426_){
_start:
{
uint8_t v___x_2427_; 
v___x_2427_ = lean_usize_dec_eq(v_i_2424_, v_stop_2425_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; size_t v___x_2431_; size_t v___x_2432_; 
v___x_2428_ = lean_array_uget_borrowed(v_as_2423_, v_i_2424_);
lean_inc(v___x_2428_);
v___x_2429_ = lean_nat_to_int(v___x_2428_);
v___x_2430_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2426_, v___x_2429_);
lean_dec(v___x_2429_);
v___x_2431_ = ((size_t)1ULL);
v___x_2432_ = lean_usize_add(v_i_2424_, v___x_2431_);
v_i_2424_ = v___x_2432_;
v_b_2426_ = v___x_2430_;
goto _start;
}
else
{
return v_b_2426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0___boxed(lean_object* v_as_2434_, lean_object* v_i_2435_, lean_object* v_stop_2436_, lean_object* v_b_2437_){
_start:
{
size_t v_i_boxed_2438_; size_t v_stop_boxed_2439_; lean_object* v_res_2440_; 
v_i_boxed_2438_ = lean_unbox_usize(v_i_2435_);
lean_dec(v_i_2435_);
v_stop_boxed_2439_ = lean_unbox_usize(v_stop_2436_);
lean_dec(v_stop_2436_);
v_res_2440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(v_as_2434_, v_i_boxed_2438_, v_stop_boxed_2439_, v_b_2437_);
lean_dec_ref(v_as_2434_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(lean_object* v_as_2441_, size_t v_i_2442_, size_t v_stop_2443_, lean_object* v_b_2444_){
_start:
{
uint8_t v___x_2445_; 
v___x_2445_ = lean_usize_dec_eq(v_i_2442_, v_stop_2443_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; size_t v___x_2449_; size_t v___x_2450_; lean_object* v___x_2451_; 
v___x_2446_ = lean_array_uget_borrowed(v_as_2441_, v_i_2442_);
lean_inc(v___x_2446_);
v___x_2447_ = lean_nat_to_int(v___x_2446_);
v___x_2448_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2444_, v___x_2447_);
lean_dec(v___x_2447_);
v___x_2449_ = ((size_t)1ULL);
v___x_2450_ = lean_usize_add(v_i_2442_, v___x_2449_);
v___x_2451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(v_as_2441_, v___x_2450_, v_stop_2443_, v___x_2448_);
return v___x_2451_;
}
else
{
return v_b_2444_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0___boxed(lean_object* v_as_2452_, lean_object* v_i_2453_, lean_object* v_stop_2454_, lean_object* v_b_2455_){
_start:
{
size_t v_i_boxed_2456_; size_t v_stop_boxed_2457_; lean_object* v_res_2458_; 
v_i_boxed_2456_ = lean_unbox_usize(v_i_2453_);
lean_dec(v_i_2453_);
v_stop_boxed_2457_ = lean_unbox_usize(v_stop_2454_);
lean_dec(v_stop_2454_);
v_res_2458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_as_2452_, v_i_boxed_2456_, v_stop_boxed_2457_, v_b_2455_);
lean_dec_ref(v_as_2452_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(lean_object* v_as_2459_, size_t v_i_2460_, size_t v_stop_2461_, lean_object* v_b_2462_){
_start:
{
lean_object* v___y_2464_; uint8_t v___x_2468_; 
v___x_2468_ = lean_usize_dec_eq(v_i_2460_, v_stop_2461_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; lean_object* v_fst_2470_; lean_object* v_snd_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v_acc_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; 
v___x_2469_ = lean_array_uget_borrowed(v_as_2459_, v_i_2460_);
v_fst_2470_ = lean_ctor_get(v___x_2469_, 0);
v_snd_2471_ = lean_ctor_get(v___x_2469_, 1);
v___x_2472_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_2470_);
v___x_2473_ = lean_nat_to_int(v_fst_2470_);
v___x_2474_ = lean_int_neg(v___x_2473_);
lean_dec(v___x_2473_);
v_acc_2475_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2462_, v___x_2474_);
lean_dec(v___x_2474_);
v___x_2476_ = lean_array_get_size(v_snd_2471_);
v___x_2477_ = lean_nat_dec_lt(v___x_2472_, v___x_2476_);
if (v___x_2477_ == 0)
{
v___y_2464_ = v_acc_2475_;
goto v___jp_2463_;
}
else
{
uint8_t v___x_2478_; 
v___x_2478_ = lean_nat_dec_le(v___x_2476_, v___x_2476_);
if (v___x_2478_ == 0)
{
if (v___x_2477_ == 0)
{
v___y_2464_ = v_acc_2475_;
goto v___jp_2463_;
}
else
{
size_t v___x_2479_; size_t v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = ((size_t)0ULL);
v___x_2480_ = lean_usize_of_nat(v___x_2476_);
v___x_2481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2471_, v___x_2479_, v___x_2480_, v_acc_2475_);
v___y_2464_ = v___x_2481_;
goto v___jp_2463_;
}
}
else
{
size_t v___x_2482_; size_t v___x_2483_; lean_object* v___x_2484_; 
v___x_2482_ = ((size_t)0ULL);
v___x_2483_ = lean_usize_of_nat(v___x_2476_);
v___x_2484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2471_, v___x_2482_, v___x_2483_, v_acc_2475_);
v___y_2464_ = v___x_2484_;
goto v___jp_2463_;
}
}
}
else
{
return v_b_2462_;
}
v___jp_2463_:
{
size_t v___x_2465_; size_t v___x_2466_; 
v___x_2465_ = ((size_t)1ULL);
v___x_2466_ = lean_usize_add(v_i_2460_, v___x_2465_);
v_i_2460_ = v___x_2466_;
v_b_2462_ = v___y_2464_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3___boxed(lean_object* v_as_2485_, lean_object* v_i_2486_, lean_object* v_stop_2487_, lean_object* v_b_2488_){
_start:
{
size_t v_i_boxed_2489_; size_t v_stop_boxed_2490_; lean_object* v_res_2491_; 
v_i_boxed_2489_ = lean_unbox_usize(v_i_2486_);
lean_dec(v_i_2486_);
v_stop_boxed_2490_ = lean_unbox_usize(v_stop_2487_);
lean_dec(v_stop_2487_);
v_res_2491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(v_as_2485_, v_i_boxed_2489_, v_stop_boxed_2490_, v_b_2488_);
lean_dec_ref(v_as_2485_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(lean_object* v_as_2492_, size_t v_i_2493_, size_t v_stop_2494_, lean_object* v_b_2495_){
_start:
{
lean_object* v___y_2497_; uint8_t v___x_2501_; 
v___x_2501_ = lean_usize_dec_eq(v_i_2493_, v_stop_2494_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; lean_object* v_fst_2503_; lean_object* v_snd_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v_acc_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; 
v___x_2502_ = lean_array_uget_borrowed(v_as_2492_, v_i_2493_);
v_fst_2503_ = lean_ctor_get(v___x_2502_, 0);
v_snd_2504_ = lean_ctor_get(v___x_2502_, 1);
v___x_2505_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_2503_);
v___x_2506_ = lean_nat_to_int(v_fst_2503_);
v___x_2507_ = lean_int_neg(v___x_2506_);
lean_dec(v___x_2506_);
v_acc_2508_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2495_, v___x_2507_);
lean_dec(v___x_2507_);
v___x_2509_ = lean_array_get_size(v_snd_2504_);
v___x_2510_ = lean_nat_dec_lt(v___x_2505_, v___x_2509_);
if (v___x_2510_ == 0)
{
v___y_2497_ = v_acc_2508_;
goto v___jp_2496_;
}
else
{
uint8_t v___x_2511_; 
v___x_2511_ = lean_nat_dec_le(v___x_2509_, v___x_2509_);
if (v___x_2511_ == 0)
{
if (v___x_2510_ == 0)
{
v___y_2497_ = v_acc_2508_;
goto v___jp_2496_;
}
else
{
size_t v___x_2512_; size_t v___x_2513_; lean_object* v___x_2514_; 
v___x_2512_ = ((size_t)0ULL);
v___x_2513_ = lean_usize_of_nat(v___x_2509_);
v___x_2514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2504_, v___x_2512_, v___x_2513_, v_acc_2508_);
v___y_2497_ = v___x_2514_;
goto v___jp_2496_;
}
}
else
{
size_t v___x_2515_; size_t v___x_2516_; lean_object* v___x_2517_; 
v___x_2515_ = ((size_t)0ULL);
v___x_2516_ = lean_usize_of_nat(v___x_2509_);
v___x_2517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2504_, v___x_2515_, v___x_2516_, v_acc_2508_);
v___y_2497_ = v___x_2517_;
goto v___jp_2496_;
}
}
}
else
{
return v_b_2495_;
}
v___jp_2496_:
{
size_t v___x_2498_; size_t v___x_2499_; lean_object* v___x_2500_; 
v___x_2498_ = ((size_t)1ULL);
v___x_2499_ = lean_usize_add(v_i_2493_, v___x_2498_);
v___x_2500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(v_as_2492_, v___x_2499_, v_stop_2494_, v___y_2497_);
return v___x_2500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2___boxed(lean_object* v_as_2518_, lean_object* v_i_2519_, lean_object* v_stop_2520_, lean_object* v_b_2521_){
_start:
{
size_t v_i_boxed_2522_; size_t v_stop_boxed_2523_; lean_object* v_res_2524_; 
v_i_boxed_2522_ = lean_unbox_usize(v_i_2519_);
lean_dec(v_i_2519_);
v_stop_boxed_2523_ = lean_unbox_usize(v_stop_2520_);
lean_dec(v_stop_2520_);
v_res_2524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_as_2518_, v_i_boxed_2522_, v_stop_boxed_2523_, v_b_2521_);
lean_dec_ref(v_as_2518_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(lean_object* v_as_2525_, size_t v_i_2526_, size_t v_stop_2527_, lean_object* v_b_2528_){
_start:
{
uint8_t v___x_2529_; 
v___x_2529_ = lean_usize_dec_eq(v_i_2526_, v_stop_2527_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; lean_object* v___x_2531_; size_t v___x_2532_; size_t v___x_2533_; 
v___x_2530_ = lean_array_uget_borrowed(v_as_2525_, v_i_2526_);
v___x_2531_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2528_, v___x_2530_);
v___x_2532_ = ((size_t)1ULL);
v___x_2533_ = lean_usize_add(v_i_2526_, v___x_2532_);
v_i_2526_ = v___x_2533_;
v_b_2528_ = v___x_2531_;
goto _start;
}
else
{
return v_b_2528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1___boxed(lean_object* v_as_2535_, lean_object* v_i_2536_, lean_object* v_stop_2537_, lean_object* v_b_2538_){
_start:
{
size_t v_i_boxed_2539_; size_t v_stop_boxed_2540_; lean_object* v_res_2541_; 
v_i_boxed_2539_ = lean_unbox_usize(v_i_2536_);
lean_dec(v_i_2536_);
v_stop_boxed_2540_ = lean_unbox_usize(v_stop_2537_);
lean_dec(v_stop_2537_);
v_res_2541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_as_2535_, v_i_boxed_2539_, v_stop_boxed_2540_, v_b_2538_);
lean_dec_ref(v_as_2535_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(lean_object* v_proof_2542_, lean_object* v_idx_2543_, lean_object* v_acc_2544_){
_start:
{
lean_object* v___y_2546_; lean_object* v___y_2551_; lean_object* v___y_2555_; lean_object* v___y_2559_; lean_object* v___y_2563_; lean_object* v___x_2566_; uint8_t v___x_2567_; 
v___x_2566_ = lean_array_get_size(v_proof_2542_);
v___x_2567_ = lean_nat_dec_lt(v_idx_2543_, v___x_2566_);
if (v___x_2567_ == 0)
{
lean_dec(v_idx_2543_);
return v_acc_2544_;
}
else
{
lean_object* v___x_2568_; 
v___x_2568_ = lean_array_fget_borrowed(v_proof_2542_, v_idx_2543_);
switch(lean_obj_tag(v___x_2568_))
{
case 0:
{
lean_object* v_id_2569_; lean_object* v_rupHints_2570_; uint8_t v___x_2571_; lean_object* v_acc_2572_; lean_object* v___x_2573_; lean_object* v_acc_2574_; uint8_t v___x_2575_; lean_object* v_acc_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; uint8_t v___x_2579_; 
v_id_2569_ = lean_ctor_get(v___x_2568_, 0);
v_rupHints_2570_ = lean_ctor_get(v___x_2568_, 1);
v___x_2571_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
v_acc_2572_ = lean_byte_array_push(v_acc_2544_, v___x_2571_);
lean_inc(v_id_2569_);
v___x_2573_ = lean_nat_to_int(v_id_2569_);
v_acc_2574_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2572_, v___x_2573_);
lean_dec(v___x_2573_);
v___x_2575_ = 0;
v_acc_2576_ = lean_byte_array_push(v_acc_2574_, v___x_2575_);
v___x_2577_ = lean_unsigned_to_nat(0u);
v___x_2578_ = lean_array_get_size(v_rupHints_2570_);
v___x_2579_ = lean_nat_dec_lt(v___x_2577_, v___x_2578_);
if (v___x_2579_ == 0)
{
v___y_2555_ = v_acc_2576_;
goto v___jp_2554_;
}
else
{
uint8_t v___x_2580_; 
v___x_2580_ = lean_nat_dec_le(v___x_2578_, v___x_2578_);
if (v___x_2580_ == 0)
{
if (v___x_2579_ == 0)
{
v___y_2555_ = v_acc_2576_;
goto v___jp_2554_;
}
else
{
size_t v___x_2581_; size_t v___x_2582_; lean_object* v___x_2583_; 
v___x_2581_ = ((size_t)0ULL);
v___x_2582_ = lean_usize_of_nat(v___x_2578_);
v___x_2583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2570_, v___x_2581_, v___x_2582_, v_acc_2576_);
v___y_2555_ = v___x_2583_;
goto v___jp_2554_;
}
}
else
{
size_t v___x_2584_; size_t v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = ((size_t)0ULL);
v___x_2585_ = lean_usize_of_nat(v___x_2578_);
v___x_2586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2570_, v___x_2584_, v___x_2585_, v_acc_2576_);
v___y_2555_ = v___x_2586_;
goto v___jp_2554_;
}
}
}
case 1:
{
lean_object* v_id_2587_; lean_object* v_c_2588_; lean_object* v_rupHints_2589_; uint8_t v___x_2590_; lean_object* v_acc_2591_; lean_object* v___x_2592_; lean_object* v_acc_2593_; lean_object* v___x_2594_; lean_object* v___y_2596_; lean_object* v___x_2608_; uint8_t v___x_2609_; 
v_id_2587_ = lean_ctor_get(v___x_2568_, 0);
v_c_2588_ = lean_ctor_get(v___x_2568_, 1);
v_rupHints_2589_ = lean_ctor_get(v___x_2568_, 2);
v___x_2590_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
v_acc_2591_ = lean_byte_array_push(v_acc_2544_, v___x_2590_);
lean_inc(v_id_2587_);
v___x_2592_ = lean_nat_to_int(v_id_2587_);
v_acc_2593_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2591_, v___x_2592_);
lean_dec(v___x_2592_);
v___x_2594_ = lean_unsigned_to_nat(0u);
v___x_2608_ = lean_array_get_size(v_c_2588_);
v___x_2609_ = lean_nat_dec_lt(v___x_2594_, v___x_2608_);
if (v___x_2609_ == 0)
{
v___y_2596_ = v_acc_2593_;
goto v___jp_2595_;
}
else
{
uint8_t v___x_2610_; 
v___x_2610_ = lean_nat_dec_le(v___x_2608_, v___x_2608_);
if (v___x_2610_ == 0)
{
if (v___x_2609_ == 0)
{
v___y_2596_ = v_acc_2593_;
goto v___jp_2595_;
}
else
{
size_t v___x_2611_; size_t v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = ((size_t)0ULL);
v___x_2612_ = lean_usize_of_nat(v___x_2608_);
v___x_2613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2588_, v___x_2611_, v___x_2612_, v_acc_2593_);
v___y_2596_ = v___x_2613_;
goto v___jp_2595_;
}
}
else
{
size_t v___x_2614_; size_t v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = ((size_t)0ULL);
v___x_2615_ = lean_usize_of_nat(v___x_2608_);
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2588_, v___x_2614_, v___x_2615_, v_acc_2593_);
v___y_2596_ = v___x_2616_;
goto v___jp_2595_;
}
}
v___jp_2595_:
{
uint8_t v___x_2597_; lean_object* v_acc_2598_; lean_object* v___x_2599_; uint8_t v___x_2600_; 
v___x_2597_ = 0;
v_acc_2598_ = lean_byte_array_push(v___y_2596_, v___x_2597_);
v___x_2599_ = lean_array_get_size(v_rupHints_2589_);
v___x_2600_ = lean_nat_dec_lt(v___x_2594_, v___x_2599_);
if (v___x_2600_ == 0)
{
v___y_2559_ = v_acc_2598_;
goto v___jp_2558_;
}
else
{
uint8_t v___x_2601_; 
v___x_2601_ = lean_nat_dec_le(v___x_2599_, v___x_2599_);
if (v___x_2601_ == 0)
{
if (v___x_2600_ == 0)
{
v___y_2559_ = v_acc_2598_;
goto v___jp_2558_;
}
else
{
size_t v___x_2602_; size_t v___x_2603_; lean_object* v___x_2604_; 
v___x_2602_ = ((size_t)0ULL);
v___x_2603_ = lean_usize_of_nat(v___x_2599_);
v___x_2604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2589_, v___x_2602_, v___x_2603_, v_acc_2598_);
v___y_2559_ = v___x_2604_;
goto v___jp_2558_;
}
}
else
{
size_t v___x_2605_; size_t v___x_2606_; lean_object* v___x_2607_; 
v___x_2605_ = ((size_t)0ULL);
v___x_2606_ = lean_usize_of_nat(v___x_2599_);
v___x_2607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2589_, v___x_2605_, v___x_2606_, v_acc_2598_);
v___y_2559_ = v___x_2607_;
goto v___jp_2558_;
}
}
}
}
case 2:
{
lean_object* v_id_2617_; lean_object* v_c_2618_; lean_object* v_rupHints_2619_; lean_object* v_ratHints_2620_; uint8_t v___x_2621_; lean_object* v_acc_2622_; lean_object* v___x_2623_; lean_object* v_acc_2624_; lean_object* v___x_2625_; lean_object* v___y_2627_; lean_object* v___y_2638_; lean_object* v___x_2650_; uint8_t v___x_2651_; 
v_id_2617_ = lean_ctor_get(v___x_2568_, 0);
v_c_2618_ = lean_ctor_get(v___x_2568_, 1);
v_rupHints_2619_ = lean_ctor_get(v___x_2568_, 3);
v_ratHints_2620_ = lean_ctor_get(v___x_2568_, 4);
v___x_2621_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
v_acc_2622_ = lean_byte_array_push(v_acc_2544_, v___x_2621_);
lean_inc(v_id_2617_);
v___x_2623_ = lean_nat_to_int(v_id_2617_);
v_acc_2624_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2622_, v___x_2623_);
lean_dec(v___x_2623_);
v___x_2625_ = lean_unsigned_to_nat(0u);
v___x_2650_ = lean_array_get_size(v_c_2618_);
v___x_2651_ = lean_nat_dec_lt(v___x_2625_, v___x_2650_);
if (v___x_2651_ == 0)
{
v___y_2638_ = v_acc_2624_;
goto v___jp_2637_;
}
else
{
uint8_t v___x_2652_; 
v___x_2652_ = lean_nat_dec_le(v___x_2650_, v___x_2650_);
if (v___x_2652_ == 0)
{
if (v___x_2651_ == 0)
{
v___y_2638_ = v_acc_2624_;
goto v___jp_2637_;
}
else
{
size_t v___x_2653_; size_t v___x_2654_; lean_object* v___x_2655_; 
v___x_2653_ = ((size_t)0ULL);
v___x_2654_ = lean_usize_of_nat(v___x_2650_);
v___x_2655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2618_, v___x_2653_, v___x_2654_, v_acc_2624_);
v___y_2638_ = v___x_2655_;
goto v___jp_2637_;
}
}
else
{
size_t v___x_2656_; size_t v___x_2657_; lean_object* v___x_2658_; 
v___x_2656_ = ((size_t)0ULL);
v___x_2657_ = lean_usize_of_nat(v___x_2650_);
v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2618_, v___x_2656_, v___x_2657_, v_acc_2624_);
v___y_2638_ = v___x_2658_;
goto v___jp_2637_;
}
}
v___jp_2626_:
{
lean_object* v___x_2628_; uint8_t v___x_2629_; 
v___x_2628_ = lean_array_get_size(v_ratHints_2620_);
v___x_2629_ = lean_nat_dec_lt(v___x_2625_, v___x_2628_);
if (v___x_2629_ == 0)
{
v___y_2551_ = v___y_2627_;
goto v___jp_2550_;
}
else
{
uint8_t v___x_2630_; 
v___x_2630_ = lean_nat_dec_le(v___x_2628_, v___x_2628_);
if (v___x_2630_ == 0)
{
if (v___x_2629_ == 0)
{
v___y_2551_ = v___y_2627_;
goto v___jp_2550_;
}
else
{
size_t v___x_2631_; size_t v___x_2632_; lean_object* v___x_2633_; 
v___x_2631_ = ((size_t)0ULL);
v___x_2632_ = lean_usize_of_nat(v___x_2628_);
v___x_2633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_ratHints_2620_, v___x_2631_, v___x_2632_, v___y_2627_);
v___y_2551_ = v___x_2633_;
goto v___jp_2550_;
}
}
else
{
size_t v___x_2634_; size_t v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = ((size_t)0ULL);
v___x_2635_ = lean_usize_of_nat(v___x_2628_);
v___x_2636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_ratHints_2620_, v___x_2634_, v___x_2635_, v___y_2627_);
v___y_2551_ = v___x_2636_;
goto v___jp_2550_;
}
}
}
v___jp_2637_:
{
uint8_t v___x_2639_; lean_object* v_acc_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2639_ = 0;
v_acc_2640_ = lean_byte_array_push(v___y_2638_, v___x_2639_);
v___x_2641_ = lean_array_get_size(v_rupHints_2619_);
v___x_2642_ = lean_nat_dec_lt(v___x_2625_, v___x_2641_);
if (v___x_2642_ == 0)
{
v___y_2627_ = v_acc_2640_;
goto v___jp_2626_;
}
else
{
uint8_t v___x_2643_; 
v___x_2643_ = lean_nat_dec_le(v___x_2641_, v___x_2641_);
if (v___x_2643_ == 0)
{
if (v___x_2642_ == 0)
{
v___y_2627_ = v_acc_2640_;
goto v___jp_2626_;
}
else
{
size_t v___x_2644_; size_t v___x_2645_; lean_object* v___x_2646_; 
v___x_2644_ = ((size_t)0ULL);
v___x_2645_ = lean_usize_of_nat(v___x_2641_);
v___x_2646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2619_, v___x_2644_, v___x_2645_, v_acc_2640_);
v___y_2627_ = v___x_2646_;
goto v___jp_2626_;
}
}
else
{
size_t v___x_2647_; size_t v___x_2648_; lean_object* v___x_2649_; 
v___x_2647_ = ((size_t)0ULL);
v___x_2648_ = lean_usize_of_nat(v___x_2641_);
v___x_2649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2619_, v___x_2647_, v___x_2648_, v_acc_2640_);
v___y_2627_ = v___x_2649_;
goto v___jp_2626_;
}
}
}
}
default: 
{
lean_object* v_ids_2659_; uint8_t v___x_2660_; lean_object* v_acc_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; uint8_t v___x_2664_; 
v_ids_2659_ = lean_ctor_get(v___x_2568_, 0);
v___x_2660_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
v_acc_2661_ = lean_byte_array_push(v_acc_2544_, v___x_2660_);
v___x_2662_ = lean_unsigned_to_nat(0u);
v___x_2663_ = lean_array_get_size(v_ids_2659_);
v___x_2664_ = lean_nat_dec_lt(v___x_2662_, v___x_2663_);
if (v___x_2664_ == 0)
{
v___y_2563_ = v_acc_2661_;
goto v___jp_2562_;
}
else
{
uint8_t v___x_2665_; 
v___x_2665_ = lean_nat_dec_le(v___x_2663_, v___x_2663_);
if (v___x_2665_ == 0)
{
if (v___x_2664_ == 0)
{
v___y_2563_ = v_acc_2661_;
goto v___jp_2562_;
}
else
{
size_t v___x_2666_; size_t v___x_2667_; lean_object* v___x_2668_; 
v___x_2666_ = ((size_t)0ULL);
v___x_2667_ = lean_usize_of_nat(v___x_2663_);
v___x_2668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_ids_2659_, v___x_2666_, v___x_2667_, v_acc_2661_);
v___y_2563_ = v___x_2668_;
goto v___jp_2562_;
}
}
else
{
size_t v___x_2669_; size_t v___x_2670_; lean_object* v___x_2671_; 
v___x_2669_ = ((size_t)0ULL);
v___x_2670_ = lean_usize_of_nat(v___x_2663_);
v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_ids_2659_, v___x_2669_, v___x_2670_, v_acc_2661_);
v___y_2563_ = v___x_2671_;
goto v___jp_2562_;
}
}
}
}
}
v___jp_2545_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = lean_unsigned_to_nat(1u);
v___x_2548_ = lean_nat_add(v_idx_2543_, v___x_2547_);
lean_dec(v_idx_2543_);
v_idx_2543_ = v___x_2548_;
v_acc_2544_ = v___y_2546_;
goto _start;
}
v___jp_2550_:
{
uint8_t v___x_2552_; lean_object* v_acc_2553_; 
v___x_2552_ = 0;
v_acc_2553_ = lean_byte_array_push(v___y_2551_, v___x_2552_);
v___y_2546_ = v_acc_2553_;
goto v___jp_2545_;
}
v___jp_2554_:
{
uint8_t v___x_2556_; lean_object* v_acc_2557_; 
v___x_2556_ = 0;
v_acc_2557_ = lean_byte_array_push(v___y_2555_, v___x_2556_);
v___y_2546_ = v_acc_2557_;
goto v___jp_2545_;
}
v___jp_2558_:
{
uint8_t v___x_2560_; lean_object* v_acc_2561_; 
v___x_2560_ = 0;
v_acc_2561_ = lean_byte_array_push(v___y_2559_, v___x_2560_);
v___y_2546_ = v_acc_2561_;
goto v___jp_2545_;
}
v___jp_2562_:
{
uint8_t v___x_2564_; lean_object* v_acc_2565_; 
v___x_2564_ = 0;
v_acc_2565_ = lean_byte_array_push(v___y_2563_, v___x_2564_);
v___y_2546_ = v_acc_2565_;
goto v___jp_2545_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___boxed(lean_object* v_proof_2672_, lean_object* v_idx_2673_, lean_object* v_acc_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(v_proof_2672_, v_idx_2673_, v_acc_2674_);
lean_dec_ref(v_proof_2672_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(lean_object* v_proof_2676_){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2677_ = lean_unsigned_to_nat(0u);
v___x_2678_ = lean_unsigned_to_nat(4u);
v___x_2679_ = lean_array_get_size(v_proof_2676_);
v___x_2680_ = lean_nat_mul(v___x_2678_, v___x_2679_);
v___x_2681_ = lean_mk_empty_byte_array(v___x_2680_);
lean_dec(v___x_2680_);
v___x_2682_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(v_proof_2676_, v___x_2677_, v___x_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary___boxed(lean_object* v_proof_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(v_proof_2683_);
lean_dec_ref(v_proof_2683_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object* v_path_2685_, lean_object* v_proof_2686_, uint8_t v_binaryProofs_2687_){
_start:
{
if (v_binaryProofs_2687_ == 0)
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2689_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_proof_2686_);
v___x_2690_ = lean_string_to_utf8(v___x_2689_);
lean_dec_ref(v___x_2689_);
v___x_2691_ = l_IO_FS_writeBinFile(v_path_2685_, v___x_2690_);
lean_dec_ref(v___x_2690_);
return v___x_2691_;
}
else
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(v_proof_2686_);
v___x_2693_ = l_IO_FS_writeBinFile(v_path_2685_, v___x_2692_);
lean_dec_ref(v___x_2692_);
return v___x_2693_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof___boxed(lean_object* v_path_2694_, lean_object* v_proof_2695_, lean_object* v_binaryProofs_2696_, lean_object* v_a_2697_){
_start:
{
uint8_t v_binaryProofs_boxed_2698_; lean_object* v_res_2699_; 
v_binaryProofs_boxed_2698_ = lean_unbox(v_binaryProofs_2696_);
v_res_2699_ = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(v_path_2694_, v_proof_2695_, v_binaryProofs_boxed_2698_);
lean_dec_ref(v_proof_2695_);
lean_dec_ref(v_path_2694_);
return v_res_2699_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Parsec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Parser(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin);
lean_object* initialize_Std_Internal_Parsec(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Parser(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Parsec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
}
#ifdef __cplusplus
}
#endif
