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
uint32_t lean_uint8_to_uint32(uint8_t);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint64_t lean_uint8_to_uint64(uint8_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint64_t lean_uint64_add(uint64_t, uint64_t);
uint64_t lean_uint64_land(uint64_t, uint64_t);
lean_object* lean_uint64_to_nat(uint64_t);
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
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "digit expected"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "id was 0"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4_value;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5;
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0;
static const lean_array_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__1 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__1_value;
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
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2;
static const lean_string_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Excessive literal"};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3_value;
static const lean_ctor_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3_value)}};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4_value;
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
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0(void){
_start:
{
uint32_t v___x_75_; uint8_t v___x_76_; 
v___x_75_ = 48;
v___x_76_ = lean_uint32_to_uint8(v___x_75_);
return v___x_76_;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5(void){
_start:
{
uint32_t v___x_83_; uint8_t v___x_84_; 
v___x_83_ = 57;
v___x_84_ = lean_uint32_to_uint8(v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos(lean_object* v_a_85_){
_start:
{
lean_object* v_array_86_; lean_object* v_idx_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v_array_86_ = lean_ctor_get(v_a_85_, 0);
v_idx_87_ = lean_ctor_get(v_a_85_, 1);
v___x_88_ = lean_byte_array_size(v_array_86_);
v___x_89_ = lean_nat_dec_lt(v_idx_87_, v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_box(0);
v___x_91_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_91_, 0, v_a_85_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
return v___x_91_;
}
else
{
uint8_t v_c_92_; uint8_t v___x_93_; uint8_t v___y_95_; uint8_t v___x_129_; 
v_c_92_ = lean_byte_array_fget(v_array_86_, v_idx_87_);
v___x_93_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0);
v___x_129_ = lean_uint8_dec_le(v___x_93_, v_c_92_);
if (v___x_129_ == 0)
{
v___y_95_ = v___x_129_;
goto v___jp_94_;
}
else
{
uint8_t v___x_130_; uint8_t v___x_131_; 
v___x_130_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5);
v___x_131_ = lean_uint8_dec_le(v_c_92_, v___x_130_);
v___y_95_ = v___x_131_;
goto v___jp_94_;
}
v___jp_94_:
{
if (v___y_95_ == 0)
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2));
v___x_97_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_97_, 0, v_a_85_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
return v___x_97_;
}
else
{
lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_126_; 
lean_inc(v_idx_87_);
lean_inc_ref(v_array_86_);
v_isSharedCheck_126_ = !lean_is_exclusive(v_a_85_);
if (v_isSharedCheck_126_ == 0)
{
lean_object* v_unused_127_; lean_object* v_unused_128_; 
v_unused_127_ = lean_ctor_get(v_a_85_, 1);
lean_dec(v_unused_127_);
v_unused_128_ = lean_ctor_get(v_a_85_, 0);
lean_dec(v_unused_128_);
v___x_99_ = v_a_85_;
v_isShared_100_ = v_isSharedCheck_126_;
goto v_resetjp_98_;
}
else
{
lean_dec(v_a_85_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_126_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v_it_x27_104_; 
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_add(v_idx_87_, v___x_101_);
lean_dec(v_idx_87_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 1, v___x_102_);
v_it_x27_104_ = v___x_99_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_array_86_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v___x_102_);
v_it_x27_104_ = v_reuseFailAlloc_125_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
uint32_t v___x_105_; uint8_t v___x_106_; uint8_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v_fst_110_; lean_object* v_snd_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_124_; 
v___x_105_ = lean_uint8_to_uint32(v_c_92_);
v___x_106_ = lean_uint32_to_uint8(v___x_105_);
v___x_107_ = lean_uint8_sub(v___x_106_, v___x_93_);
v___x_108_ = lean_uint8_to_nat(v___x_107_);
v___x_109_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_104_, v___x_108_);
v_fst_110_ = lean_ctor_get(v___x_109_, 0);
v_snd_111_ = lean_ctor_get(v___x_109_, 1);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_124_ == 0)
{
v___x_113_ = v___x_109_;
v_isShared_114_ = v_isSharedCheck_124_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_snd_111_);
lean_inc(v_fst_110_);
lean_dec(v___x_109_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_124_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = lean_nat_dec_eq(v_fst_110_, v___x_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_118_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v_fst_110_);
lean_ctor_set(v___x_113_, 0, v_snd_111_);
v___x_118_ = v___x_113_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_snd_111_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_fst_110_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
else
{
lean_object* v___x_120_; lean_object* v___x_122_; 
lean_dec(v_fst_110_);
v___x_120_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4));
if (v_isShared_114_ == 0)
{
lean_ctor_set_tag(v___x_113_, 1);
lean_ctor_set(v___x_113_, 1, v___x_120_);
lean_ctor_set(v___x_113_, 0, v_snd_111_);
v___x_122_ = v___x_113_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_snd_111_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v___x_120_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
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
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0(void){
_start:
{
uint32_t v___x_132_; uint8_t v___x_133_; 
v___x_132_ = 45;
v___x_133_ = lean_uint32_to_uint8(v___x_132_);
return v___x_133_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1(void){
_start:
{
uint8_t v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0);
v___x_135_ = lean_uint8_to_nat(v___x_134_);
return v___x_135_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1);
v___x_137_ = l_Nat_reprFast(v___x_136_);
return v___x_137_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2);
v___x_139_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
v___x_140_ = lean_string_append(v___x_139_, v___x_138_);
return v___x_140_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_141_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7));
v___x_142_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3);
v___x_143_ = lean_string_append(v___x_142_, v___x_141_);
return v___x_143_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4);
v___x_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg(lean_object* v_a_146_){
_start:
{
lean_object* v_array_147_; lean_object* v_idx_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v_array_147_ = lean_ctor_get(v_a_146_, 0);
v_idx_148_ = lean_ctor_get(v_a_146_, 1);
v___x_149_ = lean_byte_array_size(v_array_147_);
v___x_150_ = lean_nat_dec_lt(v_idx_148_, v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_box(0);
v___x_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_152_, 0, v_a_146_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
return v___x_152_;
}
else
{
uint8_t v___x_153_; uint8_t v_got_154_; uint8_t v___x_155_; 
v___x_153_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0);
v_got_154_ = lean_byte_array_fget(v_array_147_, v_idx_148_);
v___x_155_ = lean_uint8_dec_eq(v_got_154_, v___x_153_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
v___x_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_157_, 0, v_a_146_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
return v___x_157_;
}
else
{
lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_202_; 
lean_inc(v_idx_148_);
lean_inc_ref(v_array_147_);
v_isSharedCheck_202_ = !lean_is_exclusive(v_a_146_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; lean_object* v_unused_204_; 
v_unused_203_ = lean_ctor_get(v_a_146_, 1);
lean_dec(v_unused_203_);
v_unused_204_ = lean_ctor_get(v_a_146_, 0);
lean_dec(v_unused_204_);
v___x_159_ = v_a_146_;
v_isShared_160_ = v_isSharedCheck_202_;
goto v_resetjp_158_;
}
else
{
lean_dec(v_a_146_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_202_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_161_ = lean_unsigned_to_nat(1u);
v___x_162_ = lean_nat_add(v_idx_148_, v___x_161_);
lean_dec(v_idx_148_);
lean_inc(v___x_162_);
lean_inc_ref(v_array_147_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v___x_162_);
v___x_164_ = v___x_159_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_array_147_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___x_162_);
v___x_164_ = v_reuseFailAlloc_201_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
uint8_t v___x_165_; 
v___x_165_ = lean_nat_dec_lt(v___x_162_, v___x_149_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v___x_162_);
lean_dec_ref(v_array_147_);
v___x_166_ = lean_box(0);
v___x_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_164_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
return v___x_167_;
}
else
{
uint8_t v_c_168_; uint8_t v___x_169_; uint8_t v___y_171_; uint8_t v___x_198_; 
v_c_168_ = lean_byte_array_fget(v_array_147_, v___x_162_);
v___x_169_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0);
v___x_198_ = lean_uint8_dec_le(v___x_169_, v_c_168_);
if (v___x_198_ == 0)
{
v___y_171_ = v___x_198_;
goto v___jp_170_;
}
else
{
uint8_t v___x_199_; uint8_t v___x_200_; 
v___x_199_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5);
v___x_200_ = lean_uint8_dec_le(v_c_168_, v___x_199_);
v___y_171_ = v___x_200_;
goto v___jp_170_;
}
v___jp_170_:
{
if (v___y_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; 
lean_dec(v___x_162_);
lean_dec_ref(v_array_147_);
v___x_172_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2));
v___x_173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_164_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
return v___x_173_;
}
else
{
lean_object* v___x_174_; lean_object* v_it_x27_175_; uint32_t v___x_176_; uint8_t v___x_177_; uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v_fst_181_; lean_object* v_snd_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_197_; 
lean_dec_ref(v___x_164_);
v___x_174_ = lean_nat_add(v___x_162_, v___x_161_);
lean_dec(v___x_162_);
v_it_x27_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_175_, 0, v_array_147_);
lean_ctor_set(v_it_x27_175_, 1, v___x_174_);
v___x_176_ = lean_uint8_to_uint32(v_c_168_);
v___x_177_ = lean_uint32_to_uint8(v___x_176_);
v___x_178_ = lean_uint8_sub(v___x_177_, v___x_169_);
v___x_179_ = lean_uint8_to_nat(v___x_178_);
v___x_180_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_175_, v___x_179_);
v_fst_181_ = lean_ctor_get(v___x_180_, 0);
v_snd_182_ = lean_ctor_get(v___x_180_, 1);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_197_ == 0)
{
v___x_184_ = v___x_180_;
v_isShared_185_ = v_isSharedCheck_197_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_snd_182_);
lean_inc(v_fst_181_);
lean_dec(v___x_180_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_197_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_unsigned_to_nat(0u);
v___x_187_ = lean_nat_dec_eq(v_fst_181_, v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_188_ = lean_nat_to_int(v_fst_181_);
v___x_189_ = lean_int_neg(v___x_188_);
lean_dec(v___x_188_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 1, v___x_189_);
lean_ctor_set(v___x_184_, 0, v_snd_182_);
v___x_191_ = v___x_184_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_snd_182_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
else
{
lean_object* v___x_193_; lean_object* v___x_195_; 
lean_dec(v_fst_181_);
v___x_193_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4));
if (v_isShared_185_ == 0)
{
lean_ctor_set_tag(v___x_184_, 1);
lean_ctor_set(v___x_184_, 1, v___x_193_);
lean_ctor_set(v___x_184_, 0, v_snd_182_);
v___x_195_ = v___x_184_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_snd_182_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseId(lean_object* v_a_205_){
_start:
{
lean_object* v_array_206_; lean_object* v_idx_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v_array_206_ = lean_ctor_get(v_a_205_, 0);
v_idx_207_ = lean_ctor_get(v_a_205_, 1);
v___x_208_ = lean_byte_array_size(v_array_206_);
v___x_209_ = lean_nat_dec_lt(v_idx_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_box(0);
v___x_211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_211_, 0, v_a_205_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
return v___x_211_;
}
else
{
uint8_t v_c_212_; uint8_t v___x_213_; uint8_t v___y_215_; uint8_t v___x_249_; 
v_c_212_ = lean_byte_array_fget(v_array_206_, v_idx_207_);
v___x_213_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0);
v___x_249_ = lean_uint8_dec_le(v___x_213_, v_c_212_);
if (v___x_249_ == 0)
{
v___y_215_ = v___x_249_;
goto v___jp_214_;
}
else
{
uint8_t v___x_250_; uint8_t v___x_251_; 
v___x_250_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5);
v___x_251_ = lean_uint8_dec_le(v_c_212_, v___x_250_);
v___y_215_ = v___x_251_;
goto v___jp_214_;
}
v___jp_214_:
{
if (v___y_215_ == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2));
v___x_217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_217_, 0, v_a_205_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
return v___x_217_;
}
else
{
lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_246_; 
lean_inc(v_idx_207_);
lean_inc_ref(v_array_206_);
v_isSharedCheck_246_ = !lean_is_exclusive(v_a_205_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; lean_object* v_unused_248_; 
v_unused_247_ = lean_ctor_get(v_a_205_, 1);
lean_dec(v_unused_247_);
v_unused_248_ = lean_ctor_get(v_a_205_, 0);
lean_dec(v_unused_248_);
v___x_219_ = v_a_205_;
v_isShared_220_ = v_isSharedCheck_246_;
goto v_resetjp_218_;
}
else
{
lean_dec(v_a_205_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_246_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v_it_x27_224_; 
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_add(v_idx_207_, v___x_221_);
lean_dec(v_idx_207_);
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
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_array_206_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v___x_222_);
v_it_x27_224_ = v_reuseFailAlloc_245_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
uint32_t v___x_225_; uint8_t v___x_226_; uint8_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_fst_230_; lean_object* v_snd_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_244_; 
v___x_225_ = lean_uint8_to_uint32(v_c_212_);
v___x_226_ = lean_uint32_to_uint8(v___x_225_);
v___x_227_ = lean_uint8_sub(v___x_226_, v___x_213_);
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
v___x_240_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4));
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
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0(void){
_start:
{
uint8_t v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0);
v___x_253_ = lean_uint8_to_nat(v___x_252_);
return v___x_253_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0);
v___x_255_ = l_Nat_reprFast(v___x_254_);
return v___x_255_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1);
v___x_257_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
v___x_258_ = lean_string_append(v___x_257_, v___x_256_);
return v___x_258_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_259_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7));
v___x_260_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2);
v___x_261_ = lean_string_append(v___x_260_, v___x_259_);
return v___x_261_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3);
v___x_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero(lean_object* v_a_264_){
_start:
{
lean_object* v_array_265_; lean_object* v_idx_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_array_265_ = lean_ctor_get(v_a_264_, 0);
v_idx_266_ = lean_ctor_get(v_a_264_, 1);
v___x_267_ = lean_byte_array_size(v_array_265_);
v___x_268_ = lean_nat_dec_lt(v_idx_266_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_box(0);
v___x_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_270_, 0, v_a_264_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
return v___x_270_;
}
else
{
uint8_t v___x_271_; uint8_t v_got_272_; uint8_t v___x_273_; 
v___x_271_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0);
v_got_272_ = lean_byte_array_fget(v_array_265_, v_idx_266_);
v___x_273_ = lean_uint8_dec_eq(v_got_272_, v___x_271_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4);
v___x_275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_275_, 0, v_a_264_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
return v___x_275_;
}
else
{
lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_286_; 
lean_inc(v_idx_266_);
lean_inc_ref(v_array_265_);
v_isSharedCheck_286_ = !lean_is_exclusive(v_a_264_);
if (v_isSharedCheck_286_ == 0)
{
lean_object* v_unused_287_; lean_object* v_unused_288_; 
v_unused_287_ = lean_ctor_get(v_a_264_, 1);
lean_dec(v_unused_287_);
v_unused_288_ = lean_ctor_get(v_a_264_, 0);
lean_dec(v_unused_288_);
v___x_277_ = v_a_264_;
v_isShared_278_ = v_isSharedCheck_286_;
goto v_resetjp_276_;
}
else
{
lean_dec(v_a_264_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_286_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = lean_nat_add(v_idx_266_, v___x_279_);
lean_dec(v_idx_266_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 1, v___x_280_);
v___x_282_ = v___x_277_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_array_265_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v___x_280_);
v___x_282_ = v_reuseFailAlloc_285_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_box(0);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
return v___x_284_;
}
}
}
}
}
}
static uint8_t _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0(void){
_start:
{
uint32_t v___x_289_; uint8_t v___x_290_; 
v___x_289_ = 32;
v___x_290_ = lean_uint32_to_uint8(v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1(void){
_start:
{
uint8_t v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
v___x_292_ = lean_uint8_to_nat(v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1);
v___x_294_ = l_Nat_reprFast(v___x_293_);
return v___x_294_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2);
v___x_296_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
v___x_297_ = lean_string_append(v___x_296_, v___x_295_);
return v___x_297_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7));
v___x_299_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3);
v___x_300_ = lean_string_append(v___x_299_, v___x_298_);
return v___x_300_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4);
v___x_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs(lean_object* v_a_303_){
_start:
{
lean_object* v_array_304_; lean_object* v_idx_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v_array_304_ = lean_ctor_get(v_a_303_, 0);
v_idx_305_ = lean_ctor_get(v_a_303_, 1);
v___x_306_ = lean_byte_array_size(v_array_304_);
v___x_307_ = lean_nat_dec_lt(v_idx_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_box(0);
v___x_309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_309_, 0, v_a_303_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
return v___x_309_;
}
else
{
uint8_t v_c_310_; uint8_t v___x_311_; uint8_t v___y_313_; uint8_t v___x_364_; 
v_c_310_ = lean_byte_array_fget(v_array_304_, v_idx_305_);
v___x_311_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0);
v___x_364_ = lean_uint8_dec_le(v___x_311_, v_c_310_);
if (v___x_364_ == 0)
{
v___y_313_ = v___x_364_;
goto v___jp_312_;
}
else
{
uint8_t v___x_365_; uint8_t v___x_366_; 
v___x_365_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5);
v___x_366_ = lean_uint8_dec_le(v_c_310_, v___x_365_);
v___y_313_ = v___x_366_;
goto v___jp_312_;
}
v___jp_312_:
{
if (v___y_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2));
v___x_315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_315_, 0, v_a_303_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
return v___x_315_;
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v_it_x27_318_; uint32_t v___x_319_; uint8_t v___x_320_; uint8_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v_fst_324_; lean_object* v_snd_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_363_; 
v___x_316_ = lean_unsigned_to_nat(1u);
v___x_317_ = lean_nat_add(v_idx_305_, v___x_316_);
lean_inc_ref(v_array_304_);
v_it_x27_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_318_, 0, v_array_304_);
lean_ctor_set(v_it_x27_318_, 1, v___x_317_);
v___x_319_ = lean_uint8_to_uint32(v_c_310_);
v___x_320_ = lean_uint32_to_uint8(v___x_319_);
v___x_321_ = lean_uint8_sub(v___x_320_, v___x_311_);
v___x_322_ = lean_uint8_to_nat(v___x_321_);
v___x_323_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_318_, v___x_322_);
v_fst_324_ = lean_ctor_get(v___x_323_, 0);
v_snd_325_ = lean_ctor_get(v___x_323_, 1);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_363_ == 0)
{
v___x_327_ = v___x_323_;
v_isShared_328_ = v_isSharedCheck_363_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_snd_325_);
lean_inc(v_fst_324_);
lean_dec(v___x_323_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_363_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = lean_unsigned_to_nat(0u);
v___x_330_ = lean_nat_dec_eq(v_fst_324_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v_array_331_; lean_object* v_idx_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
lean_dec_ref(v_a_303_);
v_array_331_ = lean_ctor_get(v_snd_325_, 0);
v_idx_332_ = lean_ctor_get(v_snd_325_, 1);
v___x_333_ = lean_byte_array_size(v_array_331_);
v___x_334_ = lean_nat_dec_lt(v_idx_332_, v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_337_; 
lean_dec(v_fst_324_);
v___x_335_ = lean_box(0);
if (v_isShared_328_ == 0)
{
lean_ctor_set_tag(v___x_327_, 1);
lean_ctor_set(v___x_327_, 1, v___x_335_);
lean_ctor_set(v___x_327_, 0, v_snd_325_);
v___x_337_ = v___x_327_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_snd_325_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v___x_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
else
{
uint8_t v___x_339_; uint8_t v_got_340_; uint8_t v___x_341_; 
v___x_339_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
v_got_340_ = lean_byte_array_fget(v_array_331_, v_idx_332_);
v___x_341_ = lean_uint8_dec_eq(v_got_340_, v___x_339_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_344_; 
lean_dec(v_fst_324_);
v___x_342_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
if (v_isShared_328_ == 0)
{
lean_ctor_set_tag(v___x_327_, 1);
lean_ctor_set(v___x_327_, 1, v___x_342_);
lean_ctor_set(v___x_327_, 0, v_snd_325_);
v___x_344_ = v___x_327_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_snd_325_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
else
{
lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_356_; 
lean_inc(v_idx_332_);
lean_inc_ref(v_array_331_);
v_isSharedCheck_356_ = !lean_is_exclusive(v_snd_325_);
if (v_isSharedCheck_356_ == 0)
{
lean_object* v_unused_357_; lean_object* v_unused_358_; 
v_unused_357_ = lean_ctor_get(v_snd_325_, 1);
lean_dec(v_unused_357_);
v_unused_358_ = lean_ctor_get(v_snd_325_, 0);
lean_dec(v_unused_358_);
v___x_347_ = v_snd_325_;
v_isShared_348_ = v_isSharedCheck_356_;
goto v_resetjp_346_;
}
else
{
lean_dec(v_snd_325_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_356_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_349_ = lean_nat_add(v_idx_332_, v___x_316_);
lean_dec(v_idx_332_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v___x_349_);
v___x_351_ = v___x_347_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_array_331_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v___x_349_);
v___x_351_ = v_reuseFailAlloc_355_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_353_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v_fst_324_);
lean_ctor_set(v___x_327_, 0, v___x_351_);
v___x_353_ = v___x_327_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_fst_324_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
}
else
{
lean_object* v___x_359_; lean_object* v___x_361_; 
lean_dec(v_snd_325_);
lean_dec(v_fst_324_);
v___x_359_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4));
if (v_isShared_328_ == 0)
{
lean_ctor_set_tag(v___x_327_, 1);
lean_ctor_set(v___x_327_, 1, v___x_359_);
lean_ctor_set(v___x_327_, 0, v_a_303_);
v___x_361_ = v___x_327_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_303_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_spec__0(lean_object* v_acc_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_array_369_; lean_object* v_idx_370_; lean_object* v_pos_372_; lean_object* v_idx_373_; lean_object* v_err_374_; lean_object* v___x_378_; uint8_t v___x_379_; 
v_array_369_ = lean_ctor_get(v_a_368_, 0);
v_idx_370_ = lean_ctor_get(v_a_368_, 1);
lean_inc(v_idx_370_);
v___x_378_ = lean_byte_array_size(v_array_369_);
v___x_379_ = lean_nat_dec_lt(v_idx_370_, v___x_378_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; 
v___x_380_ = lean_box(0);
lean_inc(v_idx_370_);
v_pos_372_ = v_a_368_;
v_idx_373_ = v_idx_370_;
v_err_374_ = v___x_380_;
goto v___jp_371_;
}
else
{
uint8_t v_c_381_; uint8_t v___x_382_; uint8_t v___y_384_; uint8_t v___x_420_; 
v_c_381_ = lean_byte_array_fget(v_array_369_, v_idx_370_);
v___x_382_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0);
v___x_420_ = lean_uint8_dec_le(v___x_382_, v_c_381_);
if (v___x_420_ == 0)
{
v___y_384_ = v___x_420_;
goto v___jp_383_;
}
else
{
uint8_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5);
v___x_422_ = lean_uint8_dec_le(v_c_381_, v___x_421_);
v___y_384_ = v___x_422_;
goto v___jp_383_;
}
v___jp_383_:
{
if (v___y_384_ == 0)
{
lean_object* v___x_385_; 
v___x_385_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2));
lean_inc(v_idx_370_);
v_pos_372_ = v_a_368_;
v_idx_373_ = v_idx_370_;
v_err_374_ = v___x_385_;
goto v___jp_371_;
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v_it_x27_388_; uint32_t v___x_389_; uint8_t v___x_390_; uint8_t v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v_fst_394_; lean_object* v_snd_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_add(v_idx_370_, v___x_386_);
lean_inc_ref(v_array_369_);
v_it_x27_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_388_, 0, v_array_369_);
lean_ctor_set(v_it_x27_388_, 1, v___x_387_);
v___x_389_ = lean_uint8_to_uint32(v_c_381_);
v___x_390_ = lean_uint32_to_uint8(v___x_389_);
v___x_391_ = lean_uint8_sub(v___x_390_, v___x_382_);
v___x_392_ = lean_uint8_to_nat(v___x_391_);
v___x_393_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_388_, v___x_392_);
v_fst_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_fst_394_);
v_snd_395_ = lean_ctor_get(v___x_393_, 1);
lean_inc(v_snd_395_);
lean_dec_ref(v___x_393_);
v___x_396_ = lean_unsigned_to_nat(0u);
v___x_397_ = lean_nat_dec_eq(v_fst_394_, v___x_396_);
if (v___x_397_ == 0)
{
lean_object* v_array_398_; lean_object* v_idx_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
lean_dec_ref(v_a_368_);
v_array_398_ = lean_ctor_get(v_snd_395_, 0);
v_idx_399_ = lean_ctor_get(v_snd_395_, 1);
lean_inc(v_idx_399_);
v___x_400_ = lean_byte_array_size(v_array_398_);
v___x_401_ = lean_nat_dec_lt(v_idx_399_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
lean_dec(v_fst_394_);
v___x_402_ = lean_box(0);
v_pos_372_ = v_snd_395_;
v_idx_373_ = v_idx_399_;
v_err_374_ = v___x_402_;
goto v___jp_371_;
}
else
{
uint8_t v___x_403_; uint8_t v_got_404_; uint8_t v___x_405_; 
v___x_403_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
v_got_404_ = lean_byte_array_fget(v_array_398_, v_idx_399_);
v___x_405_ = lean_uint8_dec_eq(v_got_404_, v___x_403_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; 
lean_dec(v_fst_394_);
v___x_406_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
v_pos_372_ = v_snd_395_;
v_idx_373_ = v_idx_399_;
v_err_374_ = v___x_406_;
goto v___jp_371_;
}
else
{
lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_416_; 
lean_inc_ref(v_array_398_);
lean_dec(v_idx_370_);
v_isSharedCheck_416_ = !lean_is_exclusive(v_snd_395_);
if (v_isSharedCheck_416_ == 0)
{
lean_object* v_unused_417_; lean_object* v_unused_418_; 
v_unused_417_ = lean_ctor_get(v_snd_395_, 1);
lean_dec(v_unused_417_);
v_unused_418_ = lean_ctor_get(v_snd_395_, 0);
lean_dec(v_unused_418_);
v___x_408_ = v_snd_395_;
v_isShared_409_ = v_isSharedCheck_416_;
goto v_resetjp_407_;
}
else
{
lean_dec(v_snd_395_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_416_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_410_ = lean_nat_add(v_idx_399_, v___x_386_);
lean_dec(v_idx_399_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 1, v___x_410_);
v___x_412_ = v___x_408_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_array_398_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v___x_410_);
v___x_412_ = v_reuseFailAlloc_415_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_413_; 
v___x_413_ = lean_array_push(v_acc_367_, v_fst_394_);
v_acc_367_ = v___x_413_;
v_a_368_ = v___x_412_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_419_; 
lean_dec(v_snd_395_);
lean_dec(v_fst_394_);
v___x_419_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4));
lean_inc(v_idx_370_);
v_pos_372_ = v_a_368_;
v_idx_373_ = v_idx_370_;
v_err_374_ = v___x_419_;
goto v___jp_371_;
}
}
}
}
v___jp_371_:
{
uint8_t v___x_375_; 
v___x_375_ = lean_nat_dec_eq(v_idx_370_, v_idx_373_);
lean_dec(v_idx_373_);
lean_dec(v_idx_370_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; 
lean_dec_ref(v_acc_367_);
lean_inc(v_err_374_);
v___x_376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_376_, 0, v_pos_372_);
lean_ctor_set(v___x_376_, 1, v_err_374_);
return v___x_376_;
}
else
{
lean_object* v___x_377_; 
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v_pos_372_);
lean_ctor_set(v___x_377_, 1, v_acc_367_);
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(lean_object* v_a_425_){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0));
v___x_427_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_spec__0(v___x_426_, v_a_425_);
return v___x_427_;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0(void){
_start:
{
uint32_t v___x_428_; uint8_t v___x_429_; 
v___x_428_ = 100;
v___x_429_ = lean_uint32_to_uint8(v___x_428_);
return v___x_429_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1(void){
_start:
{
uint8_t v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
v___x_431_ = lean_uint8_to_nat(v___x_430_);
return v___x_431_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1);
v___x_433_ = l_Nat_reprFast(v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2);
v___x_435_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
v___x_436_ = lean_string_append(v___x_435_, v___x_434_);
return v___x_436_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_437_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7));
v___x_438_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3);
v___x_439_ = lean_string_append(v___x_438_, v___x_437_);
return v___x_439_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4);
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(lean_object* v_a_442_){
_start:
{
lean_object* v_array_443_; lean_object* v_idx_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v_array_443_ = lean_ctor_get(v_a_442_, 0);
v_idx_444_ = lean_ctor_get(v_a_442_, 1);
v___x_445_ = lean_byte_array_size(v_array_443_);
v___x_446_ = lean_nat_dec_lt(v_idx_444_, v___x_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_box(0);
v___x_448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_448_, 0, v_a_442_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
return v___x_448_;
}
else
{
uint8_t v___x_449_; uint8_t v_got_450_; uint8_t v___x_451_; 
v___x_449_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
v_got_450_ = lean_byte_array_fget(v_array_443_, v_idx_444_);
v___x_451_ = lean_uint8_dec_eq(v_got_450_, v___x_449_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5);
v___x_453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_453_, 0, v_a_442_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
return v___x_453_;
}
else
{
lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_517_; 
lean_inc(v_idx_444_);
lean_inc_ref(v_array_443_);
v_isSharedCheck_517_ = !lean_is_exclusive(v_a_442_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; lean_object* v_unused_519_; 
v_unused_518_ = lean_ctor_get(v_a_442_, 1);
lean_dec(v_unused_518_);
v_unused_519_ = lean_ctor_get(v_a_442_, 0);
lean_dec(v_unused_519_);
v___x_455_ = v_a_442_;
v_isShared_456_ = v_isSharedCheck_517_;
goto v_resetjp_454_;
}
else
{
lean_dec(v_a_442_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_517_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_add(v_idx_444_, v___x_457_);
lean_dec(v_idx_444_);
lean_inc(v___x_458_);
lean_inc_ref(v_array_443_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_458_);
v___x_460_ = v___x_455_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_array_443_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v___x_458_);
v___x_460_ = v_reuseFailAlloc_516_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
uint8_t v___x_461_; 
v___x_461_ = lean_nat_dec_lt(v___x_458_, v___x_445_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec(v___x_458_);
lean_dec_ref(v_array_443_);
v___x_462_ = lean_box(0);
v___x_463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_460_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
return v___x_463_;
}
else
{
uint8_t v___x_464_; uint8_t v_got_465_; uint8_t v___x_466_; 
v___x_464_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
v_got_465_ = lean_byte_array_fget(v_array_443_, v___x_458_);
v___x_466_ = lean_uint8_dec_eq(v_got_465_, v___x_464_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec(v___x_458_);
lean_dec_ref(v_array_443_);
v___x_467_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
v___x_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_460_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
return v___x_468_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
lean_dec_ref(v___x_460_);
v___x_469_ = lean_nat_add(v___x_458_, v___x_457_);
lean_dec(v___x_458_);
v___x_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_470_, 0, v_array_443_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(v___x_470_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_pos_472_; lean_object* v_res_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_506_; 
v_pos_472_ = lean_ctor_get(v___x_471_, 0);
v_res_473_ = lean_ctor_get(v___x_471_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_506_ == 0)
{
v___x_475_ = v___x_471_;
v_isShared_476_ = v_isSharedCheck_506_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_res_473_);
lean_inc(v_pos_472_);
lean_dec(v___x_471_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_506_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v_array_477_; lean_object* v_idx_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v_array_477_ = lean_ctor_get(v_pos_472_, 0);
v_idx_478_ = lean_ctor_get(v_pos_472_, 1);
v___x_479_ = lean_byte_array_size(v_array_477_);
v___x_480_ = lean_nat_dec_lt(v_idx_478_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_483_; 
lean_dec(v_res_473_);
v___x_481_ = lean_box(0);
if (v_isShared_476_ == 0)
{
lean_ctor_set_tag(v___x_475_, 1);
lean_ctor_set(v___x_475_, 1, v___x_481_);
v___x_483_ = v___x_475_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_pos_472_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
else
{
uint8_t v___x_485_; uint8_t v_got_486_; uint8_t v___x_487_; 
v___x_485_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0);
v_got_486_ = lean_byte_array_fget(v_array_477_, v_idx_478_);
v___x_487_ = lean_uint8_dec_eq(v_got_486_, v___x_485_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; lean_object* v___x_490_; 
lean_dec(v_res_473_);
v___x_488_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4);
if (v_isShared_476_ == 0)
{
lean_ctor_set_tag(v___x_475_, 1);
lean_ctor_set(v___x_475_, 1, v___x_488_);
v___x_490_ = v___x_475_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_pos_472_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v___x_488_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
else
{
lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_503_; 
lean_inc(v_idx_478_);
lean_inc_ref(v_array_477_);
v_isSharedCheck_503_ = !lean_is_exclusive(v_pos_472_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; lean_object* v_unused_505_; 
v_unused_504_ = lean_ctor_get(v_pos_472_, 1);
lean_dec(v_unused_504_);
v_unused_505_ = lean_ctor_get(v_pos_472_, 0);
lean_dec(v_unused_505_);
v___x_493_ = v_pos_472_;
v_isShared_494_ = v_isSharedCheck_503_;
goto v_resetjp_492_;
}
else
{
lean_dec(v_pos_472_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_503_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_495_ = lean_nat_add(v_idx_478_, v___x_457_);
lean_dec(v_idx_478_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_495_);
v___x_497_ = v___x_493_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_array_477_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v___x_495_);
v___x_497_ = v_reuseFailAlloc_502_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_498_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_498_, 0, v_res_473_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 1, v___x_498_);
lean_ctor_set(v___x_475_, 0, v___x_497_);
v___x_500_ = v___x_475_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_507_; lean_object* v_err_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
v_pos_507_ = lean_ctor_get(v___x_471_, 0);
v_err_508_ = lean_ctor_get(v___x_471_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_471_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_err_508_);
lean_inc(v_pos_507_);
lean_dec(v___x_471_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_pos_507_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_err_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseLit(lean_object* v_a_520_){
_start:
{
lean_object* v_array_521_; lean_object* v_idx_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v_array_521_ = lean_ctor_get(v_a_520_, 0);
v_idx_522_ = lean_ctor_get(v_a_520_, 1);
v___x_523_ = lean_byte_array_size(v_array_521_);
v___x_524_ = lean_nat_dec_lt(v_idx_522_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_box(0);
v___x_526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_526_, 0, v_a_520_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
return v___x_526_;
}
else
{
uint8_t v___x_527_; uint8_t v___x_528_; uint8_t v___x_529_; 
v___x_527_ = lean_byte_array_fget(v_array_521_, v_idx_522_);
v___x_528_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0);
v___x_529_ = lean_uint8_dec_eq(v___x_527_, v___x_528_);
if (v___x_529_ == 0)
{
if (v___x_524_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_box(0);
v___x_531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_531_, 0, v_a_520_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
return v___x_531_;
}
else
{
uint8_t v___x_532_; uint8_t v___y_534_; uint8_t v___x_569_; 
v___x_532_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0);
v___x_569_ = lean_uint8_dec_le(v___x_532_, v___x_527_);
if (v___x_569_ == 0)
{
v___y_534_ = v___x_569_;
goto v___jp_533_;
}
else
{
uint8_t v___x_570_; uint8_t v___x_571_; 
v___x_570_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5);
v___x_571_ = lean_uint8_dec_le(v___x_527_, v___x_570_);
v___y_534_ = v___x_571_;
goto v___jp_533_;
}
v___jp_533_:
{
if (v___y_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2));
v___x_536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_536_, 0, v_a_520_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
return v___x_536_;
}
else
{
lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_566_; 
lean_inc(v_idx_522_);
lean_inc_ref(v_array_521_);
v_isSharedCheck_566_ = !lean_is_exclusive(v_a_520_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; lean_object* v_unused_568_; 
v_unused_567_ = lean_ctor_get(v_a_520_, 1);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v_a_520_, 0);
lean_dec(v_unused_568_);
v___x_538_ = v_a_520_;
v_isShared_539_ = v_isSharedCheck_566_;
goto v_resetjp_537_;
}
else
{
lean_dec(v_a_520_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_566_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v_it_x27_543_; 
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = lean_nat_add(v_idx_522_, v___x_540_);
lean_dec(v_idx_522_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v___x_541_);
v_it_x27_543_ = v___x_538_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_array_521_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v___x_541_);
v_it_x27_543_ = v_reuseFailAlloc_565_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
uint32_t v___x_544_; uint8_t v___x_545_; uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v_fst_549_; lean_object* v_snd_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_564_; 
v___x_544_ = lean_uint8_to_uint32(v___x_527_);
v___x_545_ = lean_uint32_to_uint8(v___x_544_);
v___x_546_ = lean_uint8_sub(v___x_545_, v___x_532_);
v___x_547_ = lean_uint8_to_nat(v___x_546_);
v___x_548_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_543_, v___x_547_);
v_fst_549_ = lean_ctor_get(v___x_548_, 0);
v_snd_550_ = lean_ctor_get(v___x_548_, 1);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_564_ == 0)
{
v___x_552_ = v___x_548_;
v_isShared_553_ = v_isSharedCheck_564_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_snd_550_);
lean_inc(v_fst_549_);
lean_dec(v___x_548_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_564_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = lean_nat_dec_eq(v_fst_549_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_556_ = lean_nat_to_int(v_fst_549_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v___x_556_);
lean_ctor_set(v___x_552_, 0, v_snd_550_);
v___x_558_ = v___x_552_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_snd_550_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
else
{
lean_object* v___x_560_; lean_object* v___x_562_; 
lean_dec(v_fst_549_);
v___x_560_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4));
if (v_isShared_553_ == 0)
{
lean_ctor_set_tag(v___x_552_, 1);
lean_ctor_set(v___x_552_, 1, v___x_560_);
lean_ctor_set(v___x_552_, 0, v_snd_550_);
v___x_562_ = v___x_552_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_snd_550_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
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
if (v___x_524_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_box(0);
v___x_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_573_, 0, v_a_520_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
return v___x_573_;
}
else
{
if (v___x_529_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
v___x_575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_575_, 0, v_a_520_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
return v___x_575_;
}
else
{
lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_620_; 
lean_inc(v_idx_522_);
lean_inc_ref(v_array_521_);
v_isSharedCheck_620_ = !lean_is_exclusive(v_a_520_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; lean_object* v_unused_622_; 
v_unused_621_ = lean_ctor_get(v_a_520_, 1);
lean_dec(v_unused_621_);
v_unused_622_ = lean_ctor_get(v_a_520_, 0);
lean_dec(v_unused_622_);
v___x_577_ = v_a_520_;
v_isShared_578_ = v_isSharedCheck_620_;
goto v_resetjp_576_;
}
else
{
lean_dec(v_a_520_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_620_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_579_ = lean_unsigned_to_nat(1u);
v___x_580_ = lean_nat_add(v_idx_522_, v___x_579_);
lean_dec(v_idx_522_);
lean_inc(v___x_580_);
lean_inc_ref(v_array_521_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 1, v___x_580_);
v___x_582_ = v___x_577_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_array_521_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v___x_580_);
v___x_582_ = v_reuseFailAlloc_619_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
uint8_t v___x_583_; 
v___x_583_ = lean_nat_dec_lt(v___x_580_, v___x_523_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v___x_580_);
lean_dec_ref(v_array_521_);
v___x_584_ = lean_box(0);
v___x_585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_582_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
return v___x_585_;
}
else
{
uint8_t v_c_586_; uint8_t v___x_587_; uint8_t v___y_589_; uint8_t v___x_616_; 
v_c_586_ = lean_byte_array_fget(v_array_521_, v___x_580_);
v___x_587_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0);
v___x_616_ = lean_uint8_dec_le(v___x_587_, v_c_586_);
if (v___x_616_ == 0)
{
v___y_589_ = v___x_616_;
goto v___jp_588_;
}
else
{
uint8_t v___x_617_; uint8_t v___x_618_; 
v___x_617_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5);
v___x_618_ = lean_uint8_dec_le(v_c_586_, v___x_617_);
v___y_589_ = v___x_618_;
goto v___jp_588_;
}
v___jp_588_:
{
if (v___y_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; 
lean_dec(v___x_580_);
lean_dec_ref(v_array_521_);
v___x_590_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2));
v___x_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_582_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
return v___x_591_;
}
else
{
lean_object* v___x_592_; lean_object* v_it_x27_593_; uint32_t v___x_594_; uint8_t v___x_595_; uint8_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v_fst_599_; lean_object* v_snd_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v___x_582_);
v___x_592_ = lean_nat_add(v___x_580_, v___x_579_);
lean_dec(v___x_580_);
v_it_x27_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_593_, 0, v_array_521_);
lean_ctor_set(v_it_x27_593_, 1, v___x_592_);
v___x_594_ = lean_uint8_to_uint32(v_c_586_);
v___x_595_ = lean_uint32_to_uint8(v___x_594_);
v___x_596_ = lean_uint8_sub(v___x_595_, v___x_587_);
v___x_597_ = lean_uint8_to_nat(v___x_596_);
v___x_598_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_593_, v___x_597_);
v_fst_599_ = lean_ctor_get(v___x_598_, 0);
v_snd_600_ = lean_ctor_get(v___x_598_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_615_ == 0)
{
v___x_602_ = v___x_598_;
v_isShared_603_ = v_isSharedCheck_615_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_snd_600_);
lean_inc(v_fst_599_);
lean_dec(v___x_598_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_615_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_unsigned_to_nat(0u);
v___x_605_ = lean_nat_dec_eq(v_fst_599_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_606_ = lean_nat_to_int(v_fst_599_);
v___x_607_ = lean_int_neg(v___x_606_);
lean_dec(v___x_606_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 1, v___x_607_);
lean_ctor_set(v___x_602_, 0, v_snd_600_);
v___x_609_ = v___x_602_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_snd_600_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_613_; 
lean_dec(v_fst_599_);
v___x_611_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4));
if (v_isShared_603_ == 0)
{
lean_ctor_set_tag(v___x_602_, 1);
lean_ctor_set(v___x_602_, 1, v___x_611_);
lean_ctor_set(v___x_602_, 0, v_snd_600_);
v___x_613_ = v___x_602_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_snd_600_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_litWs(lean_object* v_a_623_){
_start:
{
lean_object* v_pos_625_; lean_object* v_res_626_; lean_object* v_array_650_; lean_object* v_idx_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v_array_650_ = lean_ctor_get(v_a_623_, 0);
v_idx_651_ = lean_ctor_get(v_a_623_, 1);
v___x_652_ = lean_byte_array_size(v_array_650_);
v___x_653_ = lean_nat_dec_lt(v_idx_651_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_box(0);
v___x_655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_655_, 0, v_a_623_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
return v___x_655_;
}
else
{
uint8_t v___x_656_; uint8_t v___x_657_; uint8_t v___x_658_; 
v___x_656_ = lean_byte_array_fget(v_array_650_, v_idx_651_);
v___x_657_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0);
v___x_658_ = lean_uint8_dec_eq(v___x_656_, v___x_657_);
if (v___x_658_ == 0)
{
uint8_t v___x_659_; uint8_t v___y_661_; uint8_t v___x_685_; 
v___x_659_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0);
v___x_685_ = lean_uint8_dec_le(v___x_659_, v___x_656_);
if (v___x_685_ == 0)
{
v___y_661_ = v___x_685_;
goto v___jp_660_;
}
else
{
uint8_t v___x_686_; uint8_t v___x_687_; 
v___x_686_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5);
v___x_687_ = lean_uint8_dec_le(v___x_656_, v___x_686_);
v___y_661_ = v___x_687_;
goto v___jp_660_;
}
v___jp_660_:
{
if (v___y_661_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2));
v___x_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_663_, 0, v_a_623_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
return v___x_663_;
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v_it_x27_666_; uint32_t v___x_667_; uint8_t v___x_668_; uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v_fst_672_; lean_object* v_snd_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_684_; 
v___x_664_ = lean_unsigned_to_nat(1u);
v___x_665_ = lean_nat_add(v_idx_651_, v___x_664_);
lean_inc_ref(v_array_650_);
v_it_x27_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_666_, 0, v_array_650_);
lean_ctor_set(v_it_x27_666_, 1, v___x_665_);
v___x_667_ = lean_uint8_to_uint32(v___x_656_);
v___x_668_ = lean_uint32_to_uint8(v___x_667_);
v___x_669_ = lean_uint8_sub(v___x_668_, v___x_659_);
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
lean_dec_ref(v_a_623_);
v___x_679_ = lean_nat_to_int(v_fst_672_);
v_pos_625_ = v_snd_673_;
v_res_626_ = v___x_679_;
goto v___jp_624_;
}
else
{
lean_object* v___x_680_; lean_object* v___x_682_; 
lean_dec(v_snd_673_);
lean_dec(v_fst_672_);
v___x_680_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4));
if (v_isShared_676_ == 0)
{
lean_ctor_set_tag(v___x_675_, 1);
lean_ctor_set(v___x_675_, 1, v___x_680_);
lean_ctor_set(v___x_675_, 0, v_a_623_);
v___x_682_ = v___x_675_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_623_);
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
else
{
lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_688_ = lean_unsigned_to_nat(1u);
v___x_689_ = lean_nat_add(v_idx_651_, v___x_688_);
v___x_690_ = lean_nat_dec_lt(v___x_689_, v___x_652_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec(v___x_689_);
v___x_691_ = lean_box(0);
v___x_692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_692_, 0, v_a_623_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
return v___x_692_;
}
else
{
uint8_t v_c_693_; uint8_t v___x_694_; uint8_t v___y_696_; uint8_t v___x_720_; 
v_c_693_ = lean_byte_array_fget(v_array_650_, v___x_689_);
v___x_694_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0);
v___x_720_ = lean_uint8_dec_le(v___x_694_, v_c_693_);
if (v___x_720_ == 0)
{
v___y_696_ = v___x_720_;
goto v___jp_695_;
}
else
{
uint8_t v___x_721_; uint8_t v___x_722_; 
v___x_721_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5);
v___x_722_ = lean_uint8_dec_le(v_c_693_, v___x_721_);
v___y_696_ = v___x_722_;
goto v___jp_695_;
}
v___jp_695_:
{
if (v___y_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; 
lean_dec(v___x_689_);
v___x_697_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2));
v___x_698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_698_, 0, v_a_623_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
return v___x_698_;
}
else
{
lean_object* v___x_699_; lean_object* v_it_x27_700_; uint32_t v___x_701_; uint8_t v___x_702_; uint8_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v_fst_706_; lean_object* v_snd_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_719_; 
v___x_699_ = lean_nat_add(v___x_689_, v___x_688_);
lean_dec(v___x_689_);
lean_inc_ref(v_array_650_);
v_it_x27_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_700_, 0, v_array_650_);
lean_ctor_set(v_it_x27_700_, 1, v___x_699_);
v___x_701_ = lean_uint8_to_uint32(v_c_693_);
v___x_702_ = lean_uint32_to_uint8(v___x_701_);
v___x_703_ = lean_uint8_sub(v___x_702_, v___x_694_);
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
lean_dec_ref(v_a_623_);
v___x_713_ = lean_nat_to_int(v_fst_706_);
v___x_714_ = lean_int_neg(v___x_713_);
lean_dec(v___x_713_);
v_pos_625_ = v_snd_707_;
v_res_626_ = v___x_714_;
goto v___jp_624_;
}
else
{
lean_object* v___x_715_; lean_object* v___x_717_; 
lean_dec(v_snd_707_);
lean_dec(v_fst_706_);
v___x_715_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4));
if (v_isShared_710_ == 0)
{
lean_ctor_set_tag(v___x_709_, 1);
lean_ctor_set(v___x_709_, 1, v___x_715_);
lean_ctor_set(v___x_709_, 0, v_a_623_);
v___x_717_ = v___x_709_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_623_);
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
v___jp_624_:
{
lean_object* v_array_627_; lean_object* v_idx_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_array_627_ = lean_ctor_get(v_pos_625_, 0);
v_idx_628_ = lean_ctor_get(v_pos_625_, 1);
v___x_629_ = lean_byte_array_size(v_array_627_);
v___x_630_ = lean_nat_dec_lt(v_idx_628_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec(v_res_626_);
v___x_631_ = lean_box(0);
v___x_632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_632_, 0, v_pos_625_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
return v___x_632_;
}
else
{
uint8_t v___x_633_; uint8_t v_got_634_; uint8_t v___x_635_; 
v___x_633_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
v_got_634_ = lean_byte_array_fget(v_array_627_, v_idx_628_);
v___x_635_ = lean_uint8_dec_eq(v_got_634_, v___x_633_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; 
lean_dec(v_res_626_);
v___x_636_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
v___x_637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_637_, 0, v_pos_625_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
return v___x_637_;
}
else
{
lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_647_; 
lean_inc(v_idx_628_);
lean_inc_ref(v_array_627_);
v_isSharedCheck_647_ = !lean_is_exclusive(v_pos_625_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; lean_object* v_unused_649_; 
v_unused_648_ = lean_ctor_get(v_pos_625_, 1);
lean_dec(v_unused_648_);
v_unused_649_ = lean_ctor_get(v_pos_625_, 0);
lean_dec(v_unused_649_);
v___x_639_ = v_pos_625_;
v_isShared_640_ = v_isSharedCheck_647_;
goto v_resetjp_638_;
}
else
{
lean_dec(v_pos_625_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_647_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_641_ = lean_unsigned_to_nat(1u);
v___x_642_ = lean_nat_add(v_idx_628_, v___x_641_);
lean_dec(v_idx_628_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 1, v___x_642_);
v___x_644_ = v___x_639_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_array_627_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v___x_642_);
v___x_644_ = v_reuseFailAlloc_646_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; 
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v_res_626_);
return v___x_645_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__0(lean_object* v_a_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = lean_nat_to_int(v_a_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__1(lean_object* v_acc_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_array_727_; lean_object* v_idx_728_; lean_object* v_pos_730_; lean_object* v_idx_731_; lean_object* v_err_732_; lean_object* v_pos_737_; lean_object* v_res_738_; lean_object* v___x_761_; uint8_t v___x_762_; 
v_array_727_ = lean_ctor_get(v_a_726_, 0);
v_idx_728_ = lean_ctor_get(v_a_726_, 1);
lean_inc(v_idx_728_);
v___x_761_ = lean_byte_array_size(v_array_727_);
v___x_762_ = lean_nat_dec_lt(v_idx_728_, v___x_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; 
v___x_763_ = lean_box(0);
lean_inc(v_idx_728_);
v_pos_730_ = v_a_726_;
v_idx_731_ = v_idx_728_;
v_err_732_ = v___x_763_;
goto v___jp_729_;
}
else
{
uint8_t v___x_764_; uint8_t v___x_765_; uint8_t v___x_766_; 
v___x_764_ = lean_byte_array_fget(v_array_727_, v_idx_728_);
v___x_765_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0);
v___x_766_ = lean_uint8_dec_eq(v___x_764_, v___x_765_);
if (v___x_766_ == 0)
{
uint8_t v___x_767_; uint8_t v___y_769_; uint8_t v___x_785_; 
v___x_767_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0);
v___x_785_ = lean_uint8_dec_le(v___x_767_, v___x_764_);
if (v___x_785_ == 0)
{
v___y_769_ = v___x_785_;
goto v___jp_768_;
}
else
{
uint8_t v___x_786_; uint8_t v___x_787_; 
v___x_786_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5);
v___x_787_ = lean_uint8_dec_le(v___x_764_, v___x_786_);
v___y_769_ = v___x_787_;
goto v___jp_768_;
}
v___jp_768_:
{
if (v___y_769_ == 0)
{
lean_object* v___x_770_; 
v___x_770_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2));
lean_inc(v_idx_728_);
v_pos_730_ = v_a_726_;
v_idx_731_ = v_idx_728_;
v_err_732_ = v___x_770_;
goto v___jp_729_;
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v_it_x27_773_; uint32_t v___x_774_; uint8_t v___x_775_; uint8_t v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v_fst_779_; lean_object* v_snd_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = lean_nat_add(v_idx_728_, v___x_771_);
lean_inc_ref(v_array_727_);
v_it_x27_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_773_, 0, v_array_727_);
lean_ctor_set(v_it_x27_773_, 1, v___x_772_);
v___x_774_ = lean_uint8_to_uint32(v___x_764_);
v___x_775_ = lean_uint32_to_uint8(v___x_774_);
v___x_776_ = lean_uint8_sub(v___x_775_, v___x_767_);
v___x_777_ = lean_uint8_to_nat(v___x_776_);
v___x_778_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_773_, v___x_777_);
v_fst_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_fst_779_);
v_snd_780_ = lean_ctor_get(v___x_778_, 1);
lean_inc(v_snd_780_);
lean_dec_ref(v___x_778_);
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = lean_nat_dec_eq(v_fst_779_, v___x_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; 
lean_dec_ref(v_a_726_);
v___x_783_ = lean_nat_to_int(v_fst_779_);
v_pos_737_ = v_snd_780_;
v_res_738_ = v___x_783_;
goto v___jp_736_;
}
else
{
lean_object* v___x_784_; 
lean_dec(v_snd_780_);
lean_dec(v_fst_779_);
v___x_784_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4));
lean_inc(v_idx_728_);
v_pos_730_ = v_a_726_;
v_idx_731_ = v_idx_728_;
v_err_732_ = v___x_784_;
goto v___jp_729_;
}
}
}
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_788_ = lean_unsigned_to_nat(1u);
v___x_789_ = lean_nat_add(v_idx_728_, v___x_788_);
v___x_790_ = lean_nat_dec_lt(v___x_789_, v___x_761_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
lean_dec(v___x_789_);
v___x_791_ = lean_box(0);
lean_inc(v_idx_728_);
v_pos_730_ = v_a_726_;
v_idx_731_ = v_idx_728_;
v_err_732_ = v___x_791_;
goto v___jp_729_;
}
else
{
uint8_t v_c_792_; uint8_t v___x_793_; uint8_t v___y_795_; uint8_t v___x_811_; 
v_c_792_ = lean_byte_array_fget(v_array_727_, v___x_789_);
v___x_793_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0);
v___x_811_ = lean_uint8_dec_le(v___x_793_, v_c_792_);
if (v___x_811_ == 0)
{
v___y_795_ = v___x_811_;
goto v___jp_794_;
}
else
{
uint8_t v___x_812_; uint8_t v___x_813_; 
v___x_812_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5);
v___x_813_ = lean_uint8_dec_le(v_c_792_, v___x_812_);
v___y_795_ = v___x_813_;
goto v___jp_794_;
}
v___jp_794_:
{
if (v___y_795_ == 0)
{
lean_object* v___x_796_; 
lean_dec(v___x_789_);
v___x_796_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2));
lean_inc(v_idx_728_);
v_pos_730_ = v_a_726_;
v_idx_731_ = v_idx_728_;
v_err_732_ = v___x_796_;
goto v___jp_729_;
}
else
{
lean_object* v___x_797_; lean_object* v_it_x27_798_; uint32_t v___x_799_; uint8_t v___x_800_; uint8_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v_fst_804_; lean_object* v_snd_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_797_ = lean_nat_add(v___x_789_, v___x_788_);
lean_dec(v___x_789_);
lean_inc_ref(v_array_727_);
v_it_x27_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_798_, 0, v_array_727_);
lean_ctor_set(v_it_x27_798_, 1, v___x_797_);
v___x_799_ = lean_uint8_to_uint32(v_c_792_);
v___x_800_ = lean_uint32_to_uint8(v___x_799_);
v___x_801_ = lean_uint8_sub(v___x_800_, v___x_793_);
v___x_802_ = lean_uint8_to_nat(v___x_801_);
v___x_803_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_798_, v___x_802_);
v_fst_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_fst_804_);
v_snd_805_ = lean_ctor_get(v___x_803_, 1);
lean_inc(v_snd_805_);
lean_dec_ref(v___x_803_);
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = lean_nat_dec_eq(v_fst_804_, v___x_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec_ref(v_a_726_);
v___x_808_ = lean_nat_to_int(v_fst_804_);
v___x_809_ = lean_int_neg(v___x_808_);
lean_dec(v___x_808_);
v_pos_737_ = v_snd_805_;
v_res_738_ = v___x_809_;
goto v___jp_736_;
}
else
{
lean_object* v___x_810_; 
lean_dec(v_snd_805_);
lean_dec(v_fst_804_);
v___x_810_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4));
lean_inc(v_idx_728_);
v_pos_730_ = v_a_726_;
v_idx_731_ = v_idx_728_;
v_err_732_ = v___x_810_;
goto v___jp_729_;
}
}
}
}
}
}
v___jp_729_:
{
uint8_t v___x_733_; 
v___x_733_ = lean_nat_dec_eq(v_idx_728_, v_idx_731_);
lean_dec(v_idx_731_);
lean_dec(v_idx_728_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; 
lean_dec_ref(v_acc_725_);
lean_inc(v_err_732_);
v___x_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_734_, 0, v_pos_730_);
lean_ctor_set(v___x_734_, 1, v_err_732_);
return v___x_734_;
}
else
{
lean_object* v___x_735_; 
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v_pos_730_);
lean_ctor_set(v___x_735_, 1, v_acc_725_);
return v___x_735_;
}
}
v___jp_736_:
{
lean_object* v_array_739_; lean_object* v_idx_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v_array_739_ = lean_ctor_get(v_pos_737_, 0);
v_idx_740_ = lean_ctor_get(v_pos_737_, 1);
lean_inc(v_idx_740_);
v___x_741_ = lean_byte_array_size(v_array_739_);
v___x_742_ = lean_nat_dec_lt(v_idx_740_, v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
lean_dec(v_res_738_);
v___x_743_ = lean_box(0);
v_pos_730_ = v_pos_737_;
v_idx_731_ = v_idx_740_;
v_err_732_ = v___x_743_;
goto v___jp_729_;
}
else
{
uint8_t v___x_744_; uint8_t v_got_745_; uint8_t v___x_746_; 
v___x_744_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
v_got_745_ = lean_byte_array_fget(v_array_739_, v_idx_740_);
v___x_746_ = lean_uint8_dec_eq(v_got_745_, v___x_744_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; 
lean_dec(v_res_738_);
v___x_747_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
v_pos_730_ = v_pos_737_;
v_idx_731_ = v_idx_740_;
v_err_732_ = v___x_747_;
goto v___jp_729_;
}
else
{
lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_758_; 
lean_inc_ref(v_array_739_);
lean_dec(v_idx_728_);
v_isSharedCheck_758_ = !lean_is_exclusive(v_pos_737_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; lean_object* v_unused_760_; 
v_unused_759_ = lean_ctor_get(v_pos_737_, 1);
lean_dec(v_unused_759_);
v_unused_760_ = lean_ctor_get(v_pos_737_, 0);
lean_dec(v_unused_760_);
v___x_749_ = v_pos_737_;
v_isShared_750_ = v_isSharedCheck_758_;
goto v_resetjp_748_;
}
else
{
lean_dec(v_pos_737_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_758_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_751_ = lean_unsigned_to_nat(1u);
v___x_752_ = lean_nat_add(v_idx_740_, v___x_751_);
lean_dec(v_idx_740_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_752_);
v___x_754_ = v___x_749_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_array_739_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v___x_752_);
v___x_754_ = v_reuseFailAlloc_757_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; 
v___x_755_ = lean_array_push(v_acc_725_, v_res_738_);
v_acc_725_ = v___x_755_;
v_a_726_ = v___x_754_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(lean_object* v_a_816_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0));
v___x_818_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__1(v___x_817_, v_a_816_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_pos_819_; lean_object* v_res_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_853_; 
v_pos_819_ = lean_ctor_get(v___x_818_, 0);
v_res_820_ = lean_ctor_get(v___x_818_, 1);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_853_ == 0)
{
v___x_822_ = v___x_818_;
v_isShared_823_ = v_isSharedCheck_853_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_res_820_);
lean_inc(v_pos_819_);
lean_dec(v___x_818_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_853_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_array_824_; lean_object* v_idx_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v_array_824_ = lean_ctor_get(v_pos_819_, 0);
v_idx_825_ = lean_ctor_get(v_pos_819_, 1);
v___x_826_ = lean_byte_array_size(v_array_824_);
v___x_827_ = lean_nat_dec_lt(v_idx_825_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_830_; 
lean_dec(v_res_820_);
v___x_828_ = lean_box(0);
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 1);
lean_ctor_set(v___x_822_, 1, v___x_828_);
v___x_830_ = v___x_822_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_pos_819_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
else
{
uint8_t v___x_832_; uint8_t v_got_833_; uint8_t v___x_834_; 
v___x_832_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0);
v_got_833_ = lean_byte_array_fget(v_array_824_, v_idx_825_);
v___x_834_ = lean_uint8_dec_eq(v_got_833_, v___x_832_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_837_; 
lean_dec(v_res_820_);
v___x_835_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4);
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 1);
lean_ctor_set(v___x_822_, 1, v___x_835_);
v___x_837_ = v___x_822_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_pos_819_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
else
{
lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_850_; 
lean_inc(v_idx_825_);
lean_inc_ref(v_array_824_);
v_isSharedCheck_850_ = !lean_is_exclusive(v_pos_819_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; lean_object* v_unused_852_; 
v_unused_851_ = lean_ctor_get(v_pos_819_, 1);
lean_dec(v_unused_851_);
v_unused_852_ = lean_ctor_get(v_pos_819_, 0);
lean_dec(v_unused_852_);
v___x_840_ = v_pos_819_;
v_isShared_841_ = v_isSharedCheck_850_;
goto v_resetjp_839_;
}
else
{
lean_dec(v_pos_819_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_850_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_842_ = lean_unsigned_to_nat(1u);
v___x_843_ = lean_nat_add(v_idx_825_, v___x_842_);
lean_dec(v_idx_825_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v___x_843_);
v___x_845_ = v___x_840_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_array_824_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v___x_843_);
v___x_845_ = v_reuseFailAlloc_849_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_847_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_845_);
v___x_847_ = v___x_822_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_res_820_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
}
}
else
{
return v___x_818_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(lean_object* v_a_854_){
_start:
{
lean_object* v_array_855_; lean_object* v_idx_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v_array_855_ = lean_ctor_get(v_a_854_, 0);
v_idx_856_ = lean_ctor_get(v_a_854_, 1);
v___x_857_ = lean_byte_array_size(v_array_855_);
v___x_858_ = lean_nat_dec_lt(v_idx_856_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_box(0);
v___x_860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_860_, 0, v_a_854_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
return v___x_860_;
}
else
{
uint8_t v___x_861_; uint8_t v_got_862_; uint8_t v___x_863_; 
v___x_861_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0);
v_got_862_ = lean_byte_array_fget(v_array_855_, v_idx_856_);
v___x_863_ = lean_uint8_dec_eq(v_got_862_, v___x_861_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
v___x_865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_865_, 0, v_a_854_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
return v___x_865_;
}
else
{
lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_949_; 
lean_inc(v_idx_856_);
lean_inc_ref(v_array_855_);
v_isSharedCheck_949_ = !lean_is_exclusive(v_a_854_);
if (v_isSharedCheck_949_ == 0)
{
lean_object* v_unused_950_; lean_object* v_unused_951_; 
v_unused_950_ = lean_ctor_get(v_a_854_, 1);
lean_dec(v_unused_950_);
v_unused_951_ = lean_ctor_get(v_a_854_, 0);
lean_dec(v_unused_951_);
v___x_867_ = v_a_854_;
v_isShared_868_ = v_isSharedCheck_949_;
goto v_resetjp_866_;
}
else
{
lean_dec(v_a_854_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_949_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_869_ = lean_unsigned_to_nat(1u);
v___x_870_ = lean_nat_add(v_idx_856_, v___x_869_);
lean_dec(v_idx_856_);
lean_inc(v___x_870_);
lean_inc_ref(v_array_855_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v___x_870_);
v___x_872_ = v___x_867_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_array_855_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___x_870_);
v___x_872_ = v_reuseFailAlloc_948_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
uint8_t v___x_873_; 
v___x_873_ = lean_nat_dec_lt(v___x_870_, v___x_857_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; lean_object* v___x_875_; 
lean_dec(v___x_870_);
lean_dec_ref(v_array_855_);
v___x_874_ = lean_box(0);
v___x_875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_872_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
return v___x_875_;
}
else
{
uint8_t v_c_876_; uint8_t v___x_877_; uint8_t v___y_879_; uint8_t v___x_945_; 
v_c_876_ = lean_byte_array_fget(v_array_855_, v___x_870_);
v___x_877_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0);
v___x_945_ = lean_uint8_dec_le(v___x_877_, v_c_876_);
if (v___x_945_ == 0)
{
v___y_879_ = v___x_945_;
goto v___jp_878_;
}
else
{
uint8_t v___x_946_; uint8_t v___x_947_; 
v___x_946_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5);
v___x_947_ = lean_uint8_dec_le(v_c_876_, v___x_946_);
v___y_879_ = v___x_947_;
goto v___jp_878_;
}
v___jp_878_:
{
if (v___y_879_ == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec(v___x_870_);
lean_dec_ref(v_array_855_);
v___x_880_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2));
v___x_881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_872_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
return v___x_881_;
}
else
{
lean_object* v___x_882_; lean_object* v_it_x27_883_; uint32_t v___x_884_; uint8_t v___x_885_; uint8_t v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v_fst_889_; lean_object* v_snd_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v___x_872_);
v___x_882_ = lean_nat_add(v___x_870_, v___x_869_);
lean_dec(v___x_870_);
v_it_x27_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_883_, 0, v_array_855_);
lean_ctor_set(v_it_x27_883_, 1, v___x_882_);
v___x_884_ = lean_uint8_to_uint32(v_c_876_);
v___x_885_ = lean_uint32_to_uint8(v___x_884_);
v___x_886_ = lean_uint8_sub(v___x_885_, v___x_877_);
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
v___x_910_ = lean_nat_add(v_idx_897_, v___x_869_);
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
v___x_942_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4));
v___x_943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_943_, 0, v_snd_890_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
return v___x_943_;
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(lean_object* v_acc_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_pos_955_; lean_object* v_err_956_; lean_object* v___x_971_; 
lean_inc_ref(v_a_953_);
v___x_971_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(v_a_953_);
if (lean_obj_tag(v___x_971_) == 0)
{
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_pos_972_; lean_object* v_res_973_; lean_object* v___x_974_; 
lean_dec_ref(v_a_953_);
v_pos_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_pos_972_);
v_res_973_ = lean_ctor_get(v___x_971_, 1);
lean_inc(v_res_973_);
lean_dec_ref_known(v___x_971_, 2);
v___x_974_ = lean_array_push(v_acc_952_, v_res_973_);
v_acc_952_ = v___x_974_;
v_a_953_ = v_pos_972_;
goto _start;
}
else
{
lean_object* v_pos_976_; lean_object* v_err_977_; 
v_pos_976_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_pos_976_);
v_err_977_ = lean_ctor_get(v___x_971_, 1);
lean_inc(v_err_977_);
lean_dec_ref_known(v___x_971_, 2);
v_pos_955_ = v_pos_976_;
v_err_956_ = v_err_977_;
goto v___jp_954_;
}
}
else
{
lean_object* v_err_978_; 
v_err_978_ = lean_ctor_get(v___x_971_, 1);
lean_inc(v_err_978_);
lean_dec_ref_known(v___x_971_, 2);
lean_inc_ref(v_a_953_);
v_pos_955_ = v_a_953_;
v_err_956_ = v_err_978_;
goto v___jp_954_;
}
v___jp_954_:
{
lean_object* v_idx_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_969_; 
v_idx_957_ = lean_ctor_get(v_a_953_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v_a_953_);
if (v_isSharedCheck_969_ == 0)
{
lean_object* v_unused_970_; 
v_unused_970_ = lean_ctor_get(v_a_953_, 0);
lean_dec(v_unused_970_);
v___x_959_ = v_a_953_;
v_isShared_960_ = v_isSharedCheck_969_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_idx_957_);
lean_dec(v_a_953_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_969_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_idx_961_; uint8_t v___x_962_; 
v_idx_961_ = lean_ctor_get(v_pos_955_, 1);
v___x_962_ = lean_nat_dec_eq(v_idx_957_, v_idx_961_);
lean_dec(v_idx_957_);
if (v___x_962_ == 0)
{
lean_object* v___x_964_; 
lean_dec_ref(v_acc_952_);
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 1);
lean_ctor_set(v___x_959_, 1, v_err_956_);
lean_ctor_set(v___x_959_, 0, v_pos_955_);
v___x_964_ = v___x_959_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_pos_955_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_err_956_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
else
{
lean_object* v___x_967_; 
lean_dec(v_err_956_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 1, v_acc_952_);
lean_ctor_set(v___x_959_, 0, v_pos_955_);
v___x_967_ = v___x_959_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_pos_955_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_acc_952_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(lean_object* v_ident_984_, lean_object* v_a_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(v_a_985_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_pos_987_; lean_object* v_res_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1103_; 
v_pos_987_ = lean_ctor_get(v___x_986_, 0);
v_res_988_ = lean_ctor_get(v___x_986_, 1);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_990_ = v___x_986_;
v_isShared_991_ = v_isSharedCheck_1103_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_res_988_);
lean_inc(v_pos_987_);
lean_dec(v___x_986_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1103_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v_array_992_; lean_object* v_idx_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v_array_992_ = lean_ctor_get(v_pos_987_, 0);
v_idx_993_ = lean_ctor_get(v_pos_987_, 1);
v___x_994_ = lean_byte_array_size(v_array_992_);
v___x_995_ = lean_nat_dec_lt(v_idx_993_, v___x_994_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v___x_998_; 
lean_dec(v_res_988_);
lean_dec(v_ident_984_);
v___x_996_ = lean_box(0);
if (v_isShared_991_ == 0)
{
lean_ctor_set_tag(v___x_990_, 1);
lean_ctor_set(v___x_990_, 1, v___x_996_);
v___x_998_ = v___x_990_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_pos_987_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
else
{
uint8_t v___x_1000_; uint8_t v_got_1001_; uint8_t v___x_1002_; 
v___x_1000_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
v_got_1001_ = lean_byte_array_fget(v_array_992_, v_idx_993_);
v___x_1002_ = lean_uint8_dec_eq(v_got_1001_, v___x_1000_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
lean_dec(v_res_988_);
lean_dec(v_ident_984_);
v___x_1003_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
if (v_isShared_991_ == 0)
{
lean_ctor_set_tag(v___x_990_, 1);
lean_ctor_set(v___x_990_, 1, v___x_1003_);
v___x_1005_ = v___x_990_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_pos_987_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
else
{
lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1100_; 
lean_inc(v_idx_993_);
lean_inc_ref(v_array_992_);
lean_del_object(v___x_990_);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_pos_987_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; lean_object* v_unused_1102_; 
v_unused_1101_ = lean_ctor_get(v_pos_987_, 1);
lean_dec(v_unused_1101_);
v_unused_1102_ = lean_ctor_get(v_pos_987_, 0);
lean_dec(v_unused_1102_);
v___x_1008_ = v_pos_987_;
v_isShared_1009_ = v_isSharedCheck_1100_;
goto v_resetjp_1007_;
}
else
{
lean_dec(v_pos_987_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1100_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1010_ = lean_unsigned_to_nat(1u);
v___x_1011_ = lean_nat_add(v_idx_993_, v___x_1010_);
lean_dec(v_idx_993_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v___x_1011_);
v___x_1013_ = v___x_1008_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_array_992_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(v___x_1013_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_pos_1015_; lean_object* v_res_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v_pos_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_pos_1015_);
v_res_1016_ = lean_ctor_get(v___x_1014_, 1);
lean_inc(v_res_1016_);
lean_dec_ref_known(v___x_1014_, 2);
v___x_1017_ = lean_unsigned_to_nat(0u);
v___x_1018_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0));
v___x_1019_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(v___x_1018_, v_pos_1015_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_pos_1020_; lean_object* v_res_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1080_; 
v_pos_1020_ = lean_ctor_get(v___x_1019_, 0);
v_res_1021_ = lean_ctor_get(v___x_1019_, 1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1023_ = v___x_1019_;
v_isShared_1024_ = v_isSharedCheck_1080_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_res_1021_);
lean_inc(v_pos_1020_);
lean_dec(v___x_1019_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1080_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v_array_1025_; lean_object* v_idx_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v_array_1025_ = lean_ctor_get(v_pos_1020_, 0);
v_idx_1026_ = lean_ctor_get(v_pos_1020_, 1);
v___x_1027_ = lean_byte_array_size(v_array_1025_);
v___x_1028_ = lean_nat_dec_lt(v_idx_1026_, v___x_1027_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
lean_dec(v_res_1021_);
lean_dec(v_res_1016_);
lean_dec(v_res_988_);
lean_dec(v_ident_984_);
v___x_1029_ = lean_box(0);
if (v_isShared_1024_ == 0)
{
lean_ctor_set_tag(v___x_1023_, 1);
lean_ctor_set(v___x_1023_, 1, v___x_1029_);
v___x_1031_ = v___x_1023_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_pos_1020_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
else
{
uint8_t v___x_1033_; uint8_t v_got_1034_; uint8_t v___x_1035_; 
v___x_1033_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0);
v_got_1034_ = lean_byte_array_fget(v_array_1025_, v_idx_1026_);
v___x_1035_ = lean_uint8_dec_eq(v_got_1034_, v___x_1033_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
lean_dec(v_res_1021_);
lean_dec(v_res_1016_);
lean_dec(v_res_988_);
lean_dec(v_ident_984_);
v___x_1036_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4);
if (v_isShared_1024_ == 0)
{
lean_ctor_set_tag(v___x_1023_, 1);
lean_ctor_set(v___x_1023_, 1, v___x_1036_);
v___x_1038_ = v___x_1023_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_pos_1020_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
else
{
lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1077_; 
lean_inc(v_idx_1026_);
lean_inc_ref(v_array_1025_);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_pos_1020_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; lean_object* v_unused_1079_; 
v_unused_1078_ = lean_ctor_get(v_pos_1020_, 1);
lean_dec(v_unused_1078_);
v_unused_1079_ = lean_ctor_get(v_pos_1020_, 0);
lean_dec(v_unused_1079_);
v___x_1041_ = v_pos_1020_;
v_isShared_1042_ = v_isSharedCheck_1077_;
goto v_resetjp_1040_;
}
else
{
lean_dec(v_pos_1020_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1077_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1043_ = lean_nat_add(v_idx_1026_, v___x_1010_);
lean_dec(v_idx_1026_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 1, v___x_1043_);
v___x_1045_ = v___x_1041_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_array_1025_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; uint8_t v___x_1047_; 
v___x_1046_ = lean_array_get_size(v_res_988_);
v___x_1047_ = lean_nat_dec_eq(v___x_1046_, v___x_1017_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1048_ = lean_array_get_size(v_res_1021_);
v___x_1049_ = lean_nat_dec_eq(v___x_1048_, v___x_1017_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
v___x_1050_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_988_);
v___x_1051_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_1051_, 0, v_ident_984_);
lean_ctor_set(v___x_1051_, 1, v_res_988_);
lean_ctor_set(v___x_1051_, 2, v___x_1050_);
lean_ctor_set(v___x_1051_, 3, v_res_1016_);
lean_ctor_set(v___x_1051_, 4, v_res_1021_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v___x_1051_);
lean_ctor_set(v___x_1023_, 0, v___x_1045_);
v___x_1053_ = v___x_1023_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
else
{
lean_object* v___x_1055_; uint8_t v___x_1056_; 
lean_dec(v_res_1021_);
v___x_1055_ = lean_array_get_size(v_res_1016_);
v___x_1056_ = lean_nat_dec_eq(v___x_1055_, v___x_1017_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1057_, 0, v_ident_984_);
lean_ctor_set(v___x_1057_, 1, v_res_988_);
lean_ctor_set(v___x_1057_, 2, v_res_1016_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v___x_1057_);
lean_ctor_set(v___x_1023_, 0, v___x_1045_);
v___x_1059_ = v___x_1023_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
else
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
lean_dec(v_res_1016_);
v___x_1061_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_988_);
v___x_1062_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_1062_, 0, v_ident_984_);
lean_ctor_set(v___x_1062_, 1, v_res_988_);
lean_ctor_set(v___x_1062_, 2, v___x_1061_);
lean_ctor_set(v___x_1062_, 3, v___x_1018_);
lean_ctor_set(v___x_1062_, 4, v___x_1018_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v___x_1062_);
lean_ctor_set(v___x_1023_, 0, v___x_1045_);
v___x_1064_ = v___x_1023_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1045_);
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
else
{
lean_object* v___x_1066_; uint8_t v___x_1067_; 
lean_dec(v_res_988_);
v___x_1066_ = lean_array_get_size(v_res_1021_);
lean_dec(v_res_1021_);
v___x_1067_ = lean_nat_dec_eq(v___x_1066_, v___x_1017_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
lean_dec(v_res_1016_);
lean_dec(v_ident_984_);
v___x_1068_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2));
if (v_isShared_1024_ == 0)
{
lean_ctor_set_tag(v___x_1023_, 1);
lean_ctor_set(v___x_1023_, 1, v___x_1068_);
lean_ctor_set(v___x_1023_, 0, v___x_1045_);
v___x_1070_ = v___x_1023_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v_ident_984_);
lean_ctor_set(v___x_1072_, 1, v_res_1016_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v___x_1072_);
lean_ctor_set(v___x_1023_, 0, v___x_1045_);
v___x_1074_ = v___x_1023_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
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
lean_object* v_pos_1081_; lean_object* v_err_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec(v_res_1016_);
lean_dec(v_res_988_);
lean_dec(v_ident_984_);
v_pos_1081_ = lean_ctor_get(v___x_1019_, 0);
v_err_1082_ = lean_ctor_get(v___x_1019_, 1);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1019_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_err_1082_);
lean_inc(v_pos_1081_);
lean_dec(v___x_1019_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_pos_1081_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_err_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
else
{
lean_object* v_pos_1090_; lean_object* v_err_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec(v_res_988_);
lean_dec(v_ident_984_);
v_pos_1090_ = lean_ctor_get(v___x_1014_, 0);
v_err_1091_ = lean_ctor_get(v___x_1014_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1014_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_err_1091_);
lean_inc(v_pos_1090_);
lean_dec(v___x_1014_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_pos_1090_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_err_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
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
lean_object* v_pos_1104_; lean_object* v_err_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec(v_ident_984_);
v_pos_1104_ = lean_ctor_get(v___x_986_, 0);
v_err_1105_ = lean_ctor_get(v___x_986_, 1);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_986_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_err_1105_);
lean_inc(v_pos_1104_);
lean_dec(v___x_986_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_pos_1104_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_err_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(lean_object* v_a_1113_){
_start:
{
lean_object* v_array_1114_; lean_object* v_idx_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_array_1114_ = lean_ctor_get(v_a_1113_, 0);
v_idx_1115_ = lean_ctor_get(v_a_1113_, 1);
v___x_1116_ = lean_byte_array_size(v_array_1114_);
v___x_1117_ = lean_nat_dec_lt(v_idx_1115_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_box(0);
v___x_1119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1119_, 0, v_a_1113_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
return v___x_1119_;
}
else
{
uint8_t v_c_1120_; uint8_t v___x_1121_; uint8_t v___y_1123_; uint8_t v___x_1189_; 
v_c_1120_ = lean_byte_array_fget(v_array_1114_, v_idx_1115_);
v___x_1121_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0);
v___x_1189_ = lean_uint8_dec_le(v___x_1121_, v_c_1120_);
if (v___x_1189_ == 0)
{
v___y_1123_ = v___x_1189_;
goto v___jp_1122_;
}
else
{
uint8_t v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5);
v___x_1191_ = lean_uint8_dec_le(v_c_1120_, v___x_1190_);
v___y_1123_ = v___x_1191_;
goto v___jp_1122_;
}
v___jp_1122_:
{
if (v___y_1123_ == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2));
v___x_1125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1125_, 0, v_a_1113_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
return v___x_1125_;
}
else
{
lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1186_; 
lean_inc(v_idx_1115_);
lean_inc_ref(v_array_1114_);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_a_1113_);
if (v_isSharedCheck_1186_ == 0)
{
lean_object* v_unused_1187_; lean_object* v_unused_1188_; 
v_unused_1187_ = lean_ctor_get(v_a_1113_, 1);
lean_dec(v_unused_1187_);
v_unused_1188_ = lean_ctor_get(v_a_1113_, 0);
lean_dec(v_unused_1188_);
v___x_1127_ = v_a_1113_;
v_isShared_1128_ = v_isSharedCheck_1186_;
goto v_resetjp_1126_;
}
else
{
lean_dec(v_a_1113_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1186_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v_it_x27_1132_; 
v___x_1129_ = lean_unsigned_to_nat(1u);
v___x_1130_ = lean_nat_add(v_idx_1115_, v___x_1129_);
lean_dec(v_idx_1115_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 1, v___x_1130_);
v_it_x27_1132_ = v___x_1127_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_array_1114_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v___x_1130_);
v_it_x27_1132_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
uint32_t v___x_1133_; uint8_t v___x_1134_; uint8_t v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v_fst_1138_; lean_object* v_snd_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1184_; 
v___x_1133_ = lean_uint8_to_uint32(v_c_1120_);
v___x_1134_ = lean_uint32_to_uint8(v___x_1133_);
v___x_1135_ = lean_uint8_sub(v___x_1134_, v___x_1121_);
v___x_1136_ = lean_uint8_to_nat(v___x_1135_);
v___x_1137_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_1132_, v___x_1136_);
v_fst_1138_ = lean_ctor_get(v___x_1137_, 0);
v_snd_1139_ = lean_ctor_get(v___x_1137_, 1);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1141_ = v___x_1137_;
v_isShared_1142_ = v_isSharedCheck_1184_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_snd_1139_);
lean_inc(v_fst_1138_);
lean_dec(v___x_1137_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1184_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = lean_unsigned_to_nat(0u);
v___x_1144_ = lean_nat_dec_eq(v_fst_1138_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v_array_1145_; lean_object* v_idx_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v_array_1145_ = lean_ctor_get(v_snd_1139_, 0);
v_idx_1146_ = lean_ctor_get(v_snd_1139_, 1);
v___x_1147_ = lean_byte_array_size(v_array_1145_);
v___x_1148_ = lean_nat_dec_lt(v_idx_1146_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
lean_dec(v_fst_1138_);
v___x_1149_ = lean_box(0);
if (v_isShared_1142_ == 0)
{
lean_ctor_set_tag(v___x_1141_, 1);
lean_ctor_set(v___x_1141_, 1, v___x_1149_);
lean_ctor_set(v___x_1141_, 0, v_snd_1139_);
v___x_1151_ = v___x_1141_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_snd_1139_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
else
{
uint8_t v___x_1153_; uint8_t v_got_1154_; uint8_t v___x_1155_; 
v___x_1153_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
v_got_1154_ = lean_byte_array_fget(v_array_1145_, v_idx_1146_);
v___x_1155_ = lean_uint8_dec_eq(v_got_1154_, v___x_1153_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
lean_dec(v_fst_1138_);
v___x_1156_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
if (v_isShared_1142_ == 0)
{
lean_ctor_set_tag(v___x_1141_, 1);
lean_ctor_set(v___x_1141_, 1, v___x_1156_);
lean_ctor_set(v___x_1141_, 0, v_snd_1139_);
v___x_1158_ = v___x_1141_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_snd_1139_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
else
{
lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1177_; 
lean_inc(v_idx_1146_);
lean_inc_ref(v_array_1145_);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_snd_1139_);
if (v_isSharedCheck_1177_ == 0)
{
lean_object* v_unused_1178_; lean_object* v_unused_1179_; 
v_unused_1178_ = lean_ctor_get(v_snd_1139_, 1);
lean_dec(v_unused_1178_);
v_unused_1179_ = lean_ctor_get(v_snd_1139_, 0);
lean_dec(v_unused_1179_);
v___x_1161_ = v_snd_1139_;
v_isShared_1162_ = v_isSharedCheck_1177_;
goto v_resetjp_1160_;
}
else
{
lean_dec(v_snd_1139_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1177_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1163_ = lean_nat_add(v_idx_1146_, v___x_1129_);
lean_dec(v_idx_1146_);
lean_inc(v___x_1163_);
lean_inc_ref(v_array_1145_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v___x_1163_);
v___x_1165_ = v___x_1161_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_array_1145_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
uint8_t v___x_1166_; 
v___x_1166_ = lean_nat_dec_lt(v___x_1163_, v___x_1147_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; lean_object* v___x_1169_; 
lean_dec(v___x_1163_);
lean_dec_ref(v_array_1145_);
lean_dec(v_fst_1138_);
v___x_1167_ = lean_box(0);
if (v_isShared_1142_ == 0)
{
lean_ctor_set_tag(v___x_1141_, 1);
lean_ctor_set(v___x_1141_, 1, v___x_1167_);
lean_ctor_set(v___x_1141_, 0, v___x_1165_);
v___x_1169_ = v___x_1141_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
else
{
uint8_t v___x_1171_; uint8_t v___x_1172_; uint8_t v___x_1173_; 
lean_del_object(v___x_1141_);
v___x_1171_ = lean_byte_array_fget(v_array_1145_, v___x_1163_);
lean_dec(v___x_1163_);
lean_dec_ref(v_array_1145_);
v___x_1172_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
v___x_1173_ = lean_uint8_dec_eq(v___x_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(v_fst_1138_, v___x_1165_);
return v___x_1174_;
}
else
{
lean_object* v___x_1175_; 
lean_dec(v_fst_1138_);
v___x_1175_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(v___x_1165_);
return v___x_1175_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1182_; 
lean_dec(v_fst_1138_);
v___x_1180_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4));
if (v_isShared_1142_ == 0)
{
lean_ctor_set_tag(v___x_1141_, 1);
lean_ctor_set(v___x_1141_, 1, v___x_1180_);
lean_ctor_set(v___x_1141_, 0, v_snd_1139_);
v___x_1182_ = v___x_1141_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_snd_1139_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
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
static uint8_t _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2(void){
_start:
{
uint32_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = 13;
v___x_1196_ = lean_uint32_to_uint8(v___x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(lean_object* v_acc_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v_array_1199_; lean_object* v_idx_1200_; lean_object* v_pos_1202_; lean_object* v_idx_1203_; lean_object* v_err_1204_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v_array_1199_ = lean_ctor_get(v_a_1198_, 0);
v_idx_1200_ = lean_ctor_get(v_a_1198_, 1);
lean_inc(v_idx_1200_);
v___x_1210_ = lean_byte_array_size(v_array_1199_);
v___x_1211_ = lean_nat_dec_lt(v_idx_1200_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_box(0);
lean_inc(v_idx_1200_);
v_pos_1202_ = v_a_1198_;
v_idx_1203_ = v_idx_1200_;
v_err_1204_ = v___x_1212_;
goto v___jp_1201_;
}
else
{
uint8_t v_c_1213_; uint8_t v___x_1214_; uint8_t v___x_1215_; 
v_c_1213_ = lean_byte_array_fget(v_array_1199_, v_idx_1200_);
v___x_1214_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2);
v___x_1215_ = lean_uint8_dec_eq(v_c_1213_, v___x_1214_);
if (v___x_1215_ == 0)
{
uint8_t v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = lean_uint8_once(&l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2, &l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2_once, _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2);
v___x_1217_ = lean_uint8_dec_eq(v_c_1213_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1229_; 
lean_inc_ref(v_array_1199_);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_a_1198_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; lean_object* v_unused_1231_; 
v_unused_1230_ = lean_ctor_get(v_a_1198_, 1);
lean_dec(v_unused_1230_);
v_unused_1231_ = lean_ctor_get(v_a_1198_, 0);
lean_dec(v_unused_1231_);
v___x_1219_ = v_a_1198_;
v_isShared_1220_ = v_isSharedCheck_1229_;
goto v_resetjp_1218_;
}
else
{
lean_dec(v_a_1198_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1229_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_it_x27_1224_; 
v___x_1221_ = lean_unsigned_to_nat(1u);
v___x_1222_ = lean_nat_add(v_idx_1200_, v___x_1221_);
lean_dec(v_idx_1200_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 1, v___x_1222_);
v_it_x27_1224_ = v___x_1219_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_array_1199_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v___x_1222_);
v_it_x27_1224_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_box(v_c_1213_);
v___x_1226_ = lean_array_push(v_acc_1197_, v___x_1225_);
v_acc_1197_ = v___x_1226_;
v_a_1198_ = v_it_x27_1224_;
goto _start;
}
}
}
else
{
goto v___jp_1208_;
}
}
else
{
goto v___jp_1208_;
}
}
v___jp_1201_:
{
uint8_t v___x_1205_; 
v___x_1205_ = lean_nat_dec_eq(v_idx_1200_, v_idx_1203_);
lean_dec(v_idx_1203_);
lean_dec(v_idx_1200_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; 
lean_dec_ref(v_acc_1197_);
lean_inc(v_err_1204_);
v___x_1206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1206_, 0, v_pos_1202_);
lean_ctor_set(v___x_1206_, 1, v_err_1204_);
return v___x_1206_;
}
else
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v_pos_1202_);
lean_ctor_set(v___x_1207_, 1, v_acc_1197_);
return v___x_1207_;
}
}
v___jp_1208_:
{
lean_object* v___x_1209_; 
v___x_1209_ = ((lean_object*)(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__1));
lean_inc(v_idx_1200_);
v_pos_1202_ = v_a_1198_;
v_idx_1203_ = v_idx_1200_;
v_err_1204_ = v___x_1209_;
goto v___jp_1201_;
}
}
}
static uint8_t _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0(void){
_start:
{
uint32_t v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = 99;
v___x_1233_ = lean_uint32_to_uint8(v___x_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(lean_object* v_actions_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_pos_1239_; lean_object* v_array_1240_; lean_object* v_idx_1241_; lean_object* v_pos_1247_; lean_object* v___y_1251_; lean_object* v_array_1262_; lean_object* v_idx_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_array_1262_ = lean_ctor_get(v_a_1237_, 0);
v_idx_1263_ = lean_ctor_get(v_a_1237_, 1);
v___x_1264_ = lean_byte_array_size(v_array_1262_);
v___x_1265_ = lean_nat_dec_lt(v_idx_1263_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_dec_ref(v_actions_1236_);
v___x_1266_ = lean_box(0);
v___x_1267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1267_, 0, v_a_1237_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
return v___x_1267_;
}
else
{
uint8_t v___x_1268_; uint8_t v___x_1269_; uint8_t v___x_1270_; 
v___x_1268_ = lean_byte_array_fget(v_array_1262_, v_idx_1263_);
v___x_1269_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0);
v___x_1270_ = lean_uint8_dec_eq(v___x_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(v_a_1237_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_pos_1272_; lean_object* v_res_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1334_; 
v_pos_1272_ = lean_ctor_get(v___x_1271_, 0);
v_res_1273_ = lean_ctor_get(v___x_1271_, 1);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1275_ = v___x_1271_;
v_isShared_1276_ = v_isSharedCheck_1334_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_res_1273_);
lean_inc(v_pos_1272_);
lean_dec(v___x_1271_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1334_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v_pos_1278_; lean_object* v_array_1279_; lean_object* v_idx_1280_; lean_object* v_pos_1289_; lean_object* v___y_1293_; lean_object* v_array_1304_; lean_object* v_idx_1305_; lean_object* v___y_1307_; lean_object* v_pos_1308_; lean_object* v_idx_1309_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v_array_1304_ = lean_ctor_get(v_pos_1272_, 0);
v_idx_1305_ = lean_ctor_get(v_pos_1272_, 1);
lean_inc(v_idx_1305_);
v___x_1314_ = lean_byte_array_size(v_array_1304_);
v___x_1315_ = lean_nat_dec_lt(v_idx_1305_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_box(0);
lean_inc(v_pos_1272_);
v___x_1317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1317_, 0, v_pos_1272_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
lean_inc(v_idx_1305_);
v___y_1307_ = v___x_1317_;
v_pos_1308_ = v_pos_1272_;
v_idx_1309_ = v_idx_1305_;
goto v___jp_1306_;
}
else
{
uint8_t v___x_1318_; uint8_t v_got_1319_; uint8_t v___x_1320_; 
v___x_1318_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2);
v_got_1319_ = lean_byte_array_fget(v_array_1304_, v_idx_1305_);
v___x_1320_ = lean_uint8_dec_eq(v_got_1319_, v___x_1318_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9);
lean_inc(v_pos_1272_);
v___x_1322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1322_, 0, v_pos_1272_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
lean_inc(v_idx_1305_);
v___y_1307_ = v___x_1322_;
v_pos_1308_ = v_pos_1272_;
v_idx_1309_ = v_idx_1305_;
goto v___jp_1306_;
}
else
{
lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1331_; 
lean_inc_ref(v_array_1304_);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_pos_1272_);
if (v_isSharedCheck_1331_ == 0)
{
lean_object* v_unused_1332_; lean_object* v_unused_1333_; 
v_unused_1332_ = lean_ctor_get(v_pos_1272_, 1);
lean_dec(v_unused_1332_);
v_unused_1333_ = lean_ctor_get(v_pos_1272_, 0);
lean_dec(v_unused_1333_);
v___x_1324_ = v_pos_1272_;
v_isShared_1325_ = v_isSharedCheck_1331_;
goto v_resetjp_1323_;
}
else
{
lean_dec(v_pos_1272_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1331_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1326_ = lean_unsigned_to_nat(1u);
v___x_1327_ = lean_nat_add(v_idx_1305_, v___x_1326_);
lean_dec(v_idx_1305_);
lean_inc(v___x_1327_);
lean_inc_ref(v_array_1304_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 1, v___x_1327_);
v___x_1329_ = v___x_1324_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_array_1304_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
v_pos_1278_ = v___x_1329_;
v_array_1279_ = v_array_1304_;
v_idx_1280_ = v___x_1327_;
goto v___jp_1277_;
}
}
}
}
v___jp_1277_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1281_ = lean_array_push(v_actions_1236_, v_res_1273_);
v___x_1282_ = lean_byte_array_size(v_array_1279_);
lean_dec_ref(v_array_1279_);
v___x_1283_ = lean_nat_dec_lt(v_idx_1280_, v___x_1282_);
lean_dec(v_idx_1280_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1285_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 1, v___x_1281_);
lean_ctor_set(v___x_1275_, 0, v_pos_1278_);
v___x_1285_ = v___x_1275_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_pos_1278_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v___x_1281_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
else
{
lean_del_object(v___x_1275_);
v_actions_1236_ = v___x_1281_;
v_a_1237_ = v_pos_1278_;
goto _start;
}
}
v___jp_1288_:
{
lean_object* v_array_1290_; lean_object* v_idx_1291_; 
v_array_1290_ = lean_ctor_get(v_pos_1289_, 0);
lean_inc_ref(v_array_1290_);
v_idx_1291_ = lean_ctor_get(v_pos_1289_, 1);
lean_inc(v_idx_1291_);
v_pos_1278_ = v_pos_1289_;
v_array_1279_ = v_array_1290_;
v_idx_1280_ = v_idx_1291_;
goto v___jp_1277_;
}
v___jp_1292_:
{
if (lean_obj_tag(v___y_1293_) == 0)
{
lean_object* v_pos_1294_; 
v_pos_1294_ = lean_ctor_get(v___y_1293_, 0);
lean_inc(v_pos_1294_);
lean_dec_ref_known(v___y_1293_, 2);
v_pos_1289_ = v_pos_1294_;
goto v___jp_1288_;
}
else
{
lean_object* v_pos_1295_; lean_object* v_err_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_del_object(v___x_1275_);
lean_dec(v_res_1273_);
lean_dec_ref(v_actions_1236_);
v_pos_1295_ = lean_ctor_get(v___y_1293_, 0);
v_err_1296_ = lean_ctor_get(v___y_1293_, 1);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___y_1293_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___y_1293_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_err_1296_);
lean_inc(v_pos_1295_);
lean_dec(v___y_1293_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_pos_1295_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_err_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
v___jp_1306_:
{
uint8_t v___x_1310_; 
v___x_1310_ = lean_nat_dec_eq(v_idx_1305_, v_idx_1309_);
lean_dec(v_idx_1309_);
lean_dec(v_idx_1305_);
if (v___x_1310_ == 0)
{
lean_dec_ref(v_pos_1308_);
v___y_1293_ = v___y_1307_;
goto v___jp_1292_;
}
else
{
lean_object* v_utf8_1311_; lean_object* v___x_1312_; 
lean_dec_ref(v___y_1307_);
v_utf8_1311_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1);
v___x_1312_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1311_, v_pos_1308_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_pos_1313_; 
v_pos_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_pos_1313_);
lean_dec_ref_known(v___x_1312_, 2);
v_pos_1289_ = v_pos_1313_;
goto v___jp_1288_;
}
else
{
v___y_1293_ = v___x_1312_;
goto v___jp_1292_;
}
}
}
}
}
else
{
lean_object* v_pos_1335_; lean_object* v_err_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec_ref(v_actions_1236_);
v_pos_1335_ = lean_ctor_get(v___x_1271_, 0);
v_err_1336_ = lean_ctor_get(v___x_1271_, 1);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1271_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_err_1336_);
lean_inc(v_pos_1335_);
lean_dec(v___x_1271_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_pos_1335_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_err_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__1));
v___x_1345_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(v___x_1344_, v_a_1237_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_pos_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1384_; 
v_pos_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1384_ == 0)
{
lean_object* v_unused_1385_; 
v_unused_1385_ = lean_ctor_get(v___x_1345_, 1);
lean_dec(v_unused_1385_);
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1384_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_pos_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1384_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v_array_1350_; lean_object* v_idx_1351_; lean_object* v___y_1353_; lean_object* v_pos_1354_; lean_object* v_idx_1355_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v_array_1350_ = lean_ctor_get(v_pos_1346_, 0);
v_idx_1351_ = lean_ctor_get(v_pos_1346_, 1);
lean_inc(v_idx_1351_);
v___x_1360_ = lean_byte_array_size(v_array_1350_);
v___x_1361_ = lean_nat_dec_lt(v_idx_1351_, v___x_1360_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1362_ = lean_box(0);
lean_inc(v_pos_1346_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set_tag(v___x_1348_, 1);
lean_ctor_set(v___x_1348_, 1, v___x_1362_);
v___x_1364_ = v___x_1348_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_pos_1346_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_inc(v_idx_1351_);
v___y_1353_ = v___x_1364_;
v_pos_1354_ = v_pos_1346_;
v_idx_1355_ = v_idx_1351_;
goto v___jp_1352_;
}
}
else
{
uint8_t v___x_1366_; uint8_t v_got_1367_; uint8_t v___x_1368_; 
v___x_1366_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2);
v_got_1367_ = lean_byte_array_fget(v_array_1350_, v_idx_1351_);
v___x_1368_ = lean_uint8_dec_eq(v_got_1367_, v___x_1366_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1369_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9);
lean_inc(v_pos_1346_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set_tag(v___x_1348_, 1);
lean_ctor_set(v___x_1348_, 1, v___x_1369_);
v___x_1371_ = v___x_1348_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_pos_1346_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_inc(v_idx_1351_);
v___y_1353_ = v___x_1371_;
v_pos_1354_ = v_pos_1346_;
v_idx_1355_ = v_idx_1351_;
goto v___jp_1352_;
}
}
else
{
lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1381_; 
lean_inc_ref(v_array_1350_);
lean_del_object(v___x_1348_);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_pos_1346_);
if (v_isSharedCheck_1381_ == 0)
{
lean_object* v_unused_1382_; lean_object* v_unused_1383_; 
v_unused_1382_ = lean_ctor_get(v_pos_1346_, 1);
lean_dec(v_unused_1382_);
v_unused_1383_ = lean_ctor_get(v_pos_1346_, 0);
lean_dec(v_unused_1383_);
v___x_1374_ = v_pos_1346_;
v_isShared_1375_ = v_isSharedCheck_1381_;
goto v_resetjp_1373_;
}
else
{
lean_dec(v_pos_1346_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1381_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1376_ = lean_unsigned_to_nat(1u);
v___x_1377_ = lean_nat_add(v_idx_1351_, v___x_1376_);
lean_dec(v_idx_1351_);
lean_inc(v___x_1377_);
lean_inc_ref(v_array_1350_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 1, v___x_1377_);
v___x_1379_ = v___x_1374_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_array_1350_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
v_pos_1239_ = v___x_1379_;
v_array_1240_ = v_array_1350_;
v_idx_1241_ = v___x_1377_;
goto v___jp_1238_;
}
}
}
}
v___jp_1352_:
{
uint8_t v___x_1356_; 
v___x_1356_ = lean_nat_dec_eq(v_idx_1351_, v_idx_1355_);
lean_dec(v_idx_1355_);
lean_dec(v_idx_1351_);
if (v___x_1356_ == 0)
{
lean_dec_ref(v_pos_1354_);
v___y_1251_ = v___y_1353_;
goto v___jp_1250_;
}
else
{
lean_object* v_utf8_1357_; lean_object* v___x_1358_; 
lean_dec_ref(v___y_1353_);
v_utf8_1357_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1);
v___x_1358_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1357_, v_pos_1354_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_pos_1359_; 
v_pos_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_pos_1359_);
lean_dec_ref_known(v___x_1358_, 2);
v_pos_1247_ = v_pos_1359_;
goto v___jp_1246_;
}
else
{
v___y_1251_ = v___x_1358_;
goto v___jp_1250_;
}
}
}
}
}
else
{
lean_object* v_pos_1386_; lean_object* v_err_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec_ref(v_actions_1236_);
v_pos_1386_ = lean_ctor_get(v___x_1345_, 0);
v_err_1387_ = lean_ctor_get(v___x_1345_, 1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1345_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_err_1387_);
lean_inc(v_pos_1386_);
lean_dec(v___x_1345_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_pos_1386_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_err_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
v___jp_1238_:
{
lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1242_ = lean_byte_array_size(v_array_1240_);
lean_dec_ref(v_array_1240_);
v___x_1243_ = lean_nat_dec_lt(v_idx_1241_, v___x_1242_);
lean_dec(v_idx_1241_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1244_, 0, v_pos_1239_);
lean_ctor_set(v___x_1244_, 1, v_actions_1236_);
return v___x_1244_;
}
else
{
v_a_1237_ = v_pos_1239_;
goto _start;
}
}
v___jp_1246_:
{
lean_object* v_array_1248_; lean_object* v_idx_1249_; 
v_array_1248_ = lean_ctor_get(v_pos_1247_, 0);
lean_inc_ref(v_array_1248_);
v_idx_1249_ = lean_ctor_get(v_pos_1247_, 1);
lean_inc(v_idx_1249_);
v_pos_1239_ = v_pos_1247_;
v_array_1240_ = v_array_1248_;
v_idx_1241_ = v_idx_1249_;
goto v___jp_1238_;
}
v___jp_1250_:
{
if (lean_obj_tag(v___y_1251_) == 0)
{
lean_object* v_pos_1252_; 
v_pos_1252_ = lean_ctor_get(v___y_1251_, 0);
lean_inc(v_pos_1252_);
lean_dec_ref_known(v___y_1251_, 2);
v_pos_1247_ = v_pos_1252_;
goto v___jp_1246_;
}
else
{
lean_object* v_pos_1253_; lean_object* v_err_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec_ref(v_actions_1236_);
v_pos_1253_ = lean_ctor_get(v___y_1251_, 0);
v_err_1254_ = lean_ctor_get(v___y_1251_, 1);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___y_1251_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___y_1251_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_err_1254_);
lean_inc(v_pos_1253_);
lean_dec(v___y_1251_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_pos_1253_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_err_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(lean_object* v_a_1397_){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0));
v___x_1399_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(v___x_1398_, v_a_1397_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero(lean_object* v_a_1403_){
_start:
{
lean_object* v_array_1404_; lean_object* v_idx_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v_array_1404_ = lean_ctor_get(v_a_1403_, 0);
v_idx_1405_ = lean_ctor_get(v_a_1403_, 1);
v___x_1406_ = lean_byte_array_size(v_array_1404_);
v___x_1407_ = lean_nat_dec_lt(v_idx_1405_, v___x_1406_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_box(0);
v___x_1409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1409_, 0, v_a_1403_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
return v___x_1409_;
}
else
{
uint8_t v___x_1410_; uint8_t v_got_1411_; uint8_t v___x_1412_; 
v___x_1410_ = 0;
v_got_1411_ = lean_byte_array_fget(v_array_1404_, v_idx_1405_);
v___x_1412_ = lean_uint8_dec_eq(v_got_1411_, v___x_1410_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
v___x_1414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1414_, 0, v_a_1403_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
return v___x_1414_;
}
else
{
lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1425_; 
lean_inc(v_idx_1405_);
lean_inc_ref(v_array_1404_);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_a_1403_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; lean_object* v_unused_1427_; 
v_unused_1426_ = lean_ctor_get(v_a_1403_, 1);
lean_dec(v_unused_1426_);
v_unused_1427_ = lean_ctor_get(v_a_1403_, 0);
lean_dec(v_unused_1427_);
v___x_1416_ = v_a_1403_;
v_isShared_1417_ = v_isSharedCheck_1425_;
goto v_resetjp_1415_;
}
else
{
lean_dec(v_a_1403_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1425_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1418_ = lean_unsigned_to_nat(1u);
v___x_1419_ = lean_nat_add(v_idx_1405_, v___x_1418_);
lean_dec(v_idx_1405_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 1, v___x_1419_);
v___x_1421_ = v___x_1416_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_array_1404_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = lean_box(0);
v___x_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1421_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
return v___x_1423_;
}
}
}
}
}
}
static uint8_t _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2(void){
_start:
{
uint8_t v___x_1431_; uint8_t v___x_1432_; 
v___x_1431_ = 15;
v___x_1432_ = lean_uint8_complement(v___x_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(uint64_t v_uidx_1436_, uint64_t v_shift_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v_array_1439_; lean_object* v_idx_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v_array_1439_ = lean_ctor_get(v_a_1438_, 0);
v_idx_1440_ = lean_ctor_get(v_a_1438_, 1);
v___x_1441_ = lean_byte_array_size(v_array_1439_);
v___x_1442_ = lean_nat_dec_lt(v_idx_1440_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = lean_box(0);
v___x_1444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1444_, 0, v_a_1438_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
return v___x_1444_;
}
else
{
lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1490_; 
lean_inc(v_idx_1440_);
lean_inc_ref(v_array_1439_);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_a_1438_);
if (v_isSharedCheck_1490_ == 0)
{
lean_object* v_unused_1491_; lean_object* v_unused_1492_; 
v_unused_1491_ = lean_ctor_get(v_a_1438_, 1);
lean_dec(v_unused_1491_);
v_unused_1492_ = lean_ctor_get(v_a_1438_, 0);
lean_dec(v_unused_1492_);
v___x_1446_ = v_a_1438_;
v_isShared_1447_ = v_isSharedCheck_1490_;
goto v_resetjp_1445_;
}
else
{
lean_dec(v_a_1438_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1490_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
uint8_t v_c_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v_it_x27_1452_; 
v_c_1448_ = lean_byte_array_fget(v_array_1439_, v_idx_1440_);
v___x_1449_ = lean_unsigned_to_nat(1u);
v___x_1450_ = lean_nat_add(v_idx_1440_, v___x_1449_);
lean_dec(v_idx_1440_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 1, v___x_1450_);
v_it_x27_1452_ = v___x_1446_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_array_1439_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v___x_1450_);
v_it_x27_1452_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
uint64_t v___x_1481_; uint8_t v___x_1482_; 
v___x_1481_ = 28ULL;
v___x_1482_ = lean_uint64_dec_eq(v_shift_1437_, v___x_1481_);
if (v___x_1482_ == 0)
{
goto v___jp_1453_;
}
else
{
uint8_t v___x_1483_; uint8_t v___x_1484_; uint8_t v___x_1485_; uint8_t v___x_1486_; 
v___x_1483_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2);
v___x_1484_ = lean_uint8_land(v_c_1448_, v___x_1483_);
v___x_1485_ = 0;
v___x_1486_ = lean_uint8_dec_eq(v___x_1484_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4));
v___x_1488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1488_, 0, v_it_x27_1452_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
return v___x_1488_;
}
else
{
goto v___jp_1453_;
}
}
v___jp_1453_:
{
uint8_t v___x_1454_; uint8_t v___x_1455_; 
v___x_1454_ = 0;
v___x_1455_ = lean_uint8_dec_eq(v_c_1448_, v___x_1454_);
if (v___x_1455_ == 0)
{
uint8_t v___x_1456_; uint8_t v___x_1457_; uint64_t v___x_1458_; uint64_t v___x_1459_; uint64_t v___x_1460_; uint8_t v___x_1461_; uint8_t v___x_1462_; uint8_t v___x_1463_; 
v___x_1456_ = 127;
v___x_1457_ = lean_uint8_land(v_c_1448_, v___x_1456_);
v___x_1458_ = lean_uint8_to_uint64(v___x_1457_);
v___x_1459_ = lean_uint64_shift_left(v___x_1458_, v_shift_1437_);
v___x_1460_ = lean_uint64_lor(v_uidx_1436_, v___x_1459_);
v___x_1461_ = 128;
v___x_1462_ = lean_uint8_land(v_c_1448_, v___x_1461_);
v___x_1463_ = lean_uint8_dec_eq(v___x_1462_, v___x_1454_);
if (v___x_1463_ == 0)
{
uint64_t v___x_1464_; uint64_t v___x_1465_; 
v___x_1464_ = 7ULL;
v___x_1465_ = lean_uint64_add(v_shift_1437_, v___x_1464_);
v_uidx_1436_ = v___x_1460_;
v_shift_1437_ = v___x_1465_;
v_a_1438_ = v_it_x27_1452_;
goto _start;
}
else
{
uint64_t v___x_1467_; uint64_t v___x_1468_; uint64_t v___x_1469_; uint64_t v___x_1470_; uint8_t v___x_1471_; 
v___x_1467_ = 1ULL;
v___x_1468_ = lean_uint64_shift_right(v___x_1460_, v___x_1467_);
v___x_1469_ = lean_uint64_land(v___x_1467_, v___x_1460_);
v___x_1470_ = 0ULL;
v___x_1471_ = lean_uint64_dec_eq(v___x_1469_, v___x_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1472_ = lean_uint64_to_nat(v___x_1468_);
v___x_1473_ = lean_nat_to_int(v___x_1472_);
v___x_1474_ = lean_int_neg(v___x_1473_);
lean_dec(v___x_1473_);
v___x_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1475_, 0, v_it_x27_1452_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
return v___x_1475_;
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1476_ = lean_uint64_to_nat(v___x_1468_);
v___x_1477_ = lean_nat_to_int(v___x_1476_);
v___x_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1478_, 0, v_it_x27_1452_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
return v___x_1478_;
}
}
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1));
v___x_1480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1480_, 0, v_it_x27_1452_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
return v___x_1480_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___boxed(lean_object* v_uidx_1493_, lean_object* v_shift_1494_, lean_object* v_a_1495_){
_start:
{
uint64_t v_uidx_boxed_1496_; uint64_t v_shift_boxed_1497_; lean_object* v_res_1498_; 
v_uidx_boxed_1496_ = lean_unbox_uint64(v_uidx_1493_);
lean_dec_ref(v_uidx_1493_);
v_shift_boxed_1497_ = lean_unbox_uint64(v_shift_1494_);
lean_dec_ref(v_shift_1494_);
v_res_1498_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(v_uidx_boxed_1496_, v_shift_boxed_1497_, v_a_1495_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(lean_object* v_a_1499_){
_start:
{
uint64_t v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = 0ULL;
v___x_1501_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(v___x_1500_, v___x_1500_, v_a_1499_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg(lean_object* v_a_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1505_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_pos_1507_; lean_object* v_res_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1522_; 
v_pos_1507_ = lean_ctor_get(v___x_1506_, 0);
v_res_1508_ = lean_ctor_get(v___x_1506_, 1);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1510_ = v___x_1506_;
v_isShared_1511_ = v_isSharedCheck_1522_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_res_1508_);
lean_inc(v_pos_1507_);
lean_dec(v___x_1506_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1522_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1512_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1513_ = lean_int_dec_lt(v_res_1508_, v___x_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; lean_object* v___x_1516_; 
lean_dec(v_res_1508_);
v___x_1514_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1));
if (v_isShared_1511_ == 0)
{
lean_ctor_set_tag(v___x_1510_, 1);
lean_ctor_set(v___x_1510_, 1, v___x_1514_);
v___x_1516_ = v___x_1510_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_pos_1507_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1518_ = lean_nat_abs(v_res_1508_);
lean_dec(v_res_1508_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 1, v___x_1518_);
v___x_1520_ = v___x_1510_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_pos_1507_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
else
{
lean_object* v_pos_1523_; lean_object* v_err_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
v_pos_1523_ = lean_ctor_get(v___x_1506_, 0);
v_err_1524_ = lean_ctor_get(v___x_1506_, 1);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1506_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_err_1524_);
lean_inc(v_pos_1523_);
lean_dec(v___x_1506_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_pos_1523_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_err_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos(lean_object* v_a_1535_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1535_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_pos_1537_; lean_object* v_res_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1552_; 
v_pos_1537_ = lean_ctor_get(v___x_1536_, 0);
v_res_1538_ = lean_ctor_get(v___x_1536_, 1);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1540_ = v___x_1536_;
v_isShared_1541_ = v_isSharedCheck_1552_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_res_1538_);
lean_inc(v_pos_1537_);
lean_dec(v___x_1536_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1552_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1542_; uint8_t v___x_1543_; 
v___x_1542_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1543_ = lean_int_dec_lt(v___x_1542_, v_res_1538_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1546_; 
lean_dec(v_res_1538_);
v___x_1544_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1541_ == 0)
{
lean_ctor_set_tag(v___x_1540_, 1);
lean_ctor_set(v___x_1540_, 1, v___x_1544_);
v___x_1546_ = v___x_1540_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_pos_1537_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1548_ = lean_nat_abs(v_res_1538_);
lean_dec(v_res_1538_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 1, v___x_1548_);
v___x_1550_ = v___x_1540_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_pos_1537_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
lean_object* v_pos_1553_; lean_object* v_err_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
v_pos_1553_ = lean_ctor_get(v___x_1536_, 0);
v_err_1554_ = lean_ctor_get(v___x_1536_, 1);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1536_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_err_1554_);
lean_inc(v_pos_1553_);
lean_dec(v___x_1536_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_pos_1553_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_err_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId(lean_object* v_a_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1562_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_pos_1564_; lean_object* v_res_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1579_; 
v_pos_1564_ = lean_ctor_get(v___x_1563_, 0);
v_res_1565_ = lean_ctor_get(v___x_1563_, 1);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1567_ = v___x_1563_;
v_isShared_1568_ = v_isSharedCheck_1579_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_res_1565_);
lean_inc(v_pos_1564_);
lean_dec(v___x_1563_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1579_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1569_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1570_ = lean_int_dec_lt(v___x_1569_, v_res_1565_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
lean_dec(v_res_1565_);
v___x_1571_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1568_ == 0)
{
lean_ctor_set_tag(v___x_1567_, 1);
lean_ctor_set(v___x_1567_, 1, v___x_1571_);
v___x_1573_ = v___x_1567_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_pos_1564_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
else
{
lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1575_ = lean_nat_abs(v_res_1565_);
lean_dec(v_res_1565_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 1, v___x_1575_);
v___x_1577_ = v___x_1567_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_pos_1564_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
else
{
lean_object* v_pos_1580_; lean_object* v_err_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
v_pos_1580_ = lean_ctor_get(v___x_1563_, 0);
v_err_1581_ = lean_ctor_get(v___x_1563_, 1);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1563_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_err_1581_);
lean_inc(v_pos_1580_);
lean_dec(v___x_1563_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_pos_1580_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_err_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(lean_object* v_parser_1589_, lean_object* v_acc_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v_array_1592_; lean_object* v_idx_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v_array_1592_ = lean_ctor_get(v_a_1591_, 0);
v_idx_1593_ = lean_ctor_get(v_a_1591_, 1);
v___x_1594_ = lean_byte_array_size(v_array_1592_);
v___x_1595_ = lean_nat_dec_lt(v_idx_1593_, v___x_1594_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_dec_ref(v_acc_1590_);
lean_dec_ref(v_parser_1589_);
v___x_1596_ = lean_box(0);
v___x_1597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1597_, 0, v_a_1591_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
return v___x_1597_;
}
else
{
uint8_t v___x_1598_; uint8_t v___x_1599_; uint8_t v___x_1600_; 
v___x_1598_ = lean_byte_array_fget(v_array_1592_, v_idx_1593_);
v___x_1599_ = 0;
v___x_1600_ = lean_uint8_dec_eq(v___x_1598_, v___x_1599_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; 
lean_inc_ref(v_parser_1589_);
v___x_1601_ = lean_apply_1(v_parser_1589_, v_a_1591_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_pos_1602_; lean_object* v_res_1603_; lean_object* v___x_1604_; 
v_pos_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_pos_1602_);
v_res_1603_ = lean_ctor_get(v___x_1601_, 1);
lean_inc(v_res_1603_);
lean_dec_ref_known(v___x_1601_, 2);
v___x_1604_ = lean_array_push(v_acc_1590_, v_res_1603_);
v_acc_1590_ = v___x_1604_;
v_a_1591_ = v_pos_1602_;
goto _start;
}
else
{
lean_object* v_pos_1606_; lean_object* v_err_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec_ref(v_acc_1590_);
lean_dec_ref(v_parser_1589_);
v_pos_1606_ = lean_ctor_get(v___x_1601_, 0);
v_err_1607_ = lean_ctor_get(v___x_1601_, 1);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1601_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_err_1607_);
lean_inc(v_pos_1606_);
lean_dec(v___x_1601_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_pos_1606_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_err_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
else
{
lean_object* v___x_1615_; 
lean_dec_ref(v_parser_1589_);
v___x_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1615_, 0, v_a_1591_);
lean_ctor_set(v___x_1615_, 1, v_acc_1590_);
return v___x_1615_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go(lean_object* v_00_u03b1_1616_, lean_object* v_parser_1617_, lean_object* v_acc_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(v_parser_1617_, v_acc_1618_, v_a_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(lean_object* v_parser_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0));
v___x_1626_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(v_parser_1623_, v___x_1625_, v_a_1624_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero(lean_object* v_00_u03b1_1627_, lean_object* v_parser_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v_parser_1628_, v_a_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(lean_object* v_parser_1631_, lean_object* v_acc_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v_array_1634_; lean_object* v_idx_1635_; lean_object* v___x_1636_; uint8_t v___x_1637_; 
v_array_1634_ = lean_ctor_get(v_a_1633_, 0);
v_idx_1635_ = lean_ctor_get(v_a_1633_, 1);
v___x_1636_ = lean_byte_array_size(v_array_1634_);
v___x_1637_ = lean_nat_dec_lt(v_idx_1635_, v___x_1636_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_dec_ref(v_acc_1632_);
lean_dec_ref(v_parser_1631_);
v___x_1638_ = lean_box(0);
v___x_1639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1639_, 0, v_a_1633_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
return v___x_1639_;
}
else
{
uint8_t v___x_1640_; uint8_t v___x_1641_; uint8_t v___x_1642_; uint8_t v___x_1643_; uint8_t v___x_1644_; 
v___x_1640_ = lean_byte_array_fget(v_array_1634_, v_idx_1635_);
v___x_1641_ = 1;
v___x_1642_ = lean_uint8_land(v___x_1641_, v___x_1640_);
v___x_1643_ = 0;
v___x_1644_ = lean_uint8_dec_eq(v___x_1642_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; 
lean_dec_ref(v_parser_1631_);
v___x_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1645_, 0, v_a_1633_);
lean_ctor_set(v___x_1645_, 1, v_acc_1632_);
return v___x_1645_;
}
else
{
uint8_t v___x_1646_; 
v___x_1646_ = lean_uint8_dec_eq(v___x_1640_, v___x_1643_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; 
lean_inc_ref(v_parser_1631_);
v___x_1647_ = lean_apply_1(v_parser_1631_, v_a_1633_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_pos_1648_; lean_object* v_res_1649_; lean_object* v___x_1650_; 
v_pos_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_pos_1648_);
v_res_1649_ = lean_ctor_get(v___x_1647_, 1);
lean_inc(v_res_1649_);
lean_dec_ref_known(v___x_1647_, 2);
v___x_1650_ = lean_array_push(v_acc_1632_, v_res_1649_);
v_acc_1632_ = v___x_1650_;
v_a_1633_ = v_pos_1648_;
goto _start;
}
else
{
lean_object* v_pos_1652_; lean_object* v_err_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec_ref(v_acc_1632_);
lean_dec_ref(v_parser_1631_);
v_pos_1652_ = lean_ctor_get(v___x_1647_, 0);
v_err_1653_ = lean_ctor_get(v___x_1647_, 1);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1647_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_err_1653_);
lean_inc(v_pos_1652_);
lean_dec(v___x_1647_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_pos_1652_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_err_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
else
{
lean_object* v___x_1661_; 
lean_dec_ref(v_parser_1631_);
v___x_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1661_, 0, v_a_1633_);
lean_ctor_set(v___x_1661_, 1, v_acc_1632_);
return v___x_1661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go(lean_object* v_00_u03b1_1662_, lean_object* v_parser_1663_, lean_object* v_acc_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(v_parser_1663_, v_acc_1664_, v_a_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(lean_object* v_parser_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0));
v___x_1670_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(v_parser_1667_, v___x_1669_, v_a_1668_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero(lean_object* v_00_u03b1_1671_, lean_object* v_parser_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(v_parser_1672_, v_a_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList(lean_object* v_a_1675_){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId), 1, 0);
v___x_1677_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(v___x_1676_, v_a_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause(lean_object* v_a_1678_){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit), 1, 0);
v___x_1680_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v___x_1679_, v_a_1678_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(lean_object* v_acc_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v_array_1683_; lean_object* v_idx_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; 
v_array_1683_ = lean_ctor_get(v_a_1682_, 0);
v_idx_1684_ = lean_ctor_get(v_a_1682_, 1);
v___x_1685_ = lean_byte_array_size(v_array_1683_);
v___x_1686_ = lean_nat_dec_lt(v_idx_1684_, v___x_1685_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_dec_ref(v_acc_1681_);
v___x_1687_ = lean_box(0);
v___x_1688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1688_, 0, v_a_1682_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
return v___x_1688_;
}
else
{
uint8_t v___x_1689_; uint8_t v___x_1690_; uint8_t v___x_1691_; uint8_t v___x_1692_; uint8_t v___x_1693_; 
v___x_1689_ = lean_byte_array_fget(v_array_1683_, v_idx_1684_);
v___x_1690_ = 1;
v___x_1691_ = lean_uint8_land(v___x_1690_, v___x_1689_);
v___x_1692_ = 0;
v___x_1693_ = lean_uint8_dec_eq(v___x_1691_, v___x_1692_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v_a_1682_);
lean_ctor_set(v___x_1694_, 1, v_acc_1681_);
return v___x_1694_;
}
else
{
uint8_t v___x_1695_; 
v___x_1695_ = lean_uint8_dec_eq(v___x_1689_, v___x_1692_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1682_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_pos_1697_; lean_object* v_res_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1711_; 
v_pos_1697_ = lean_ctor_get(v___x_1696_, 0);
v_res_1698_ = lean_ctor_get(v___x_1696_, 1);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1700_ = v___x_1696_;
v_isShared_1701_ = v_isSharedCheck_1711_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_res_1698_);
lean_inc(v_pos_1697_);
lean_dec(v___x_1696_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1711_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1702_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1703_ = lean_int_dec_lt(v___x_1702_, v_res_1698_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1706_; 
lean_dec(v_res_1698_);
lean_dec_ref(v_acc_1681_);
v___x_1704_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1701_ == 0)
{
lean_ctor_set_tag(v___x_1700_, 1);
lean_ctor_set(v___x_1700_, 1, v___x_1704_);
v___x_1706_ = v___x_1700_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_pos_1697_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
else
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_del_object(v___x_1700_);
v___x_1708_ = lean_nat_abs(v_res_1698_);
lean_dec(v_res_1698_);
v___x_1709_ = lean_array_push(v_acc_1681_, v___x_1708_);
v_acc_1681_ = v___x_1709_;
v_a_1682_ = v_pos_1697_;
goto _start;
}
}
}
else
{
lean_object* v_pos_1712_; lean_object* v_err_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec_ref(v_acc_1681_);
v_pos_1712_ = lean_ctor_get(v___x_1696_, 0);
v_err_1713_ = lean_ctor_get(v___x_1696_, 1);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1696_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_err_1713_);
lean_inc(v_pos_1712_);
lean_dec(v___x_1696_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_pos_1712_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_err_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
else
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1721_, 0, v_a_1682_);
lean_ctor_set(v___x_1721_, 1, v_acc_1681_);
return v___x_1721_;
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
lean_object* v_pos_1832_; lean_object* v_res_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1970_; 
v_pos_1832_ = lean_ctor_get(v___x_1831_, 0);
v_res_1833_ = lean_ctor_get(v___x_1831_, 1);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1835_ = v___x_1831_;
v_isShared_1836_ = v_isSharedCheck_1970_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_res_1833_);
lean_inc(v_pos_1832_);
lean_dec(v___x_1831_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1970_;
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
lean_object* v_pos_1845_; lean_object* v_res_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1960_; 
v_pos_1845_ = lean_ctor_get(v___x_1844_, 0);
v_res_1846_ = lean_ctor_get(v___x_1844_, 1);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1848_ = v___x_1844_;
v_isShared_1849_ = v_isSharedCheck_1960_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_res_1846_);
lean_inc(v_pos_1845_);
lean_dec(v___x_1844_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1960_;
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
lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1957_; 
lean_inc(v_idx_1851_);
lean_inc_ref(v_array_1850_);
lean_del_object(v___x_1848_);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_pos_1845_);
if (v_isSharedCheck_1957_ == 0)
{
lean_object* v_unused_1958_; lean_object* v_unused_1959_; 
v_unused_1958_ = lean_ctor_get(v_pos_1845_, 1);
lean_dec(v_unused_1958_);
v_unused_1959_ = lean_ctor_get(v_pos_1845_, 0);
lean_dec(v_unused_1959_);
v___x_1866_ = v_pos_1845_;
v_isShared_1867_ = v_isSharedCheck_1957_;
goto v_resetjp_1865_;
}
else
{
lean_dec(v_pos_1845_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1957_;
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
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_array_1850_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1956_;
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
lean_object* v_pos_1876_; lean_object* v_res_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1937_; 
v_pos_1876_ = lean_ctor_get(v___x_1875_, 0);
v_res_1877_ = lean_ctor_get(v___x_1875_, 1);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1879_ = v___x_1875_;
v_isShared_1880_ = v_isSharedCheck_1937_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_res_1877_);
lean_inc(v_pos_1876_);
lean_dec(v___x_1875_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1937_;
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
lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1934_; 
lean_inc(v_idx_1882_);
lean_inc_ref(v_array_1881_);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_pos_1876_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; lean_object* v_unused_1936_; 
v_unused_1935_ = lean_ctor_get(v_pos_1876_, 1);
lean_dec(v_unused_1935_);
v_unused_1936_ = lean_ctor_get(v_pos_1876_, 0);
lean_dec(v_unused_1936_);
v___x_1896_ = v_pos_1876_;
v_isShared_1897_ = v_isSharedCheck_1934_;
goto v_resetjp_1895_;
}
else
{
lean_dec(v_pos_1876_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1934_;
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
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_array_1881_);
lean_ctor_set(v_reuseFailAlloc_1933_, 1, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1933_;
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
lean_object* v___x_1911_; uint8_t v___x_1912_; 
lean_dec(v_res_1877_);
v___x_1911_ = lean_array_get_size(v_res_1874_);
v___x_1912_ = lean_nat_dec_eq(v___x_1911_, v___x_1837_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
v___x_1913_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1898_);
lean_ctor_set(v___x_1913_, 1, v_res_1846_);
lean_ctor_set(v___x_1913_, 2, v_res_1874_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v___x_1913_);
lean_ctor_set(v___x_1879_, 0, v___x_1901_);
v___x_1915_ = v___x_1879_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1921_; 
lean_dec(v_res_1874_);
v___x_1917_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_1846_);
v___x_1918_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0));
v___x_1919_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1898_);
lean_ctor_set(v___x_1919_, 1, v_res_1846_);
lean_ctor_set(v___x_1919_, 2, v___x_1917_);
lean_ctor_set(v___x_1919_, 3, v___x_1918_);
lean_ctor_set(v___x_1919_, 4, v___x_1918_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v___x_1919_);
lean_ctor_set(v___x_1879_, 0, v___x_1901_);
v___x_1921_ = v___x_1879_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
else
{
lean_object* v___x_1923_; uint8_t v___x_1924_; 
lean_dec(v_res_1846_);
v___x_1923_ = lean_array_get_size(v_res_1877_);
lean_dec(v_res_1877_);
v___x_1924_ = lean_nat_dec_eq(v___x_1923_, v___x_1837_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
lean_dec(v___x_1898_);
lean_dec(v_res_1874_);
v___x_1925_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2));
if (v_isShared_1880_ == 0)
{
lean_ctor_set_tag(v___x_1879_, 1);
lean_ctor_set(v___x_1879_, 1, v___x_1925_);
lean_ctor_set(v___x_1879_, 0, v___x_1901_);
v___x_1927_ = v___x_1879_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1898_);
lean_ctor_set(v___x_1929_, 1, v_res_1874_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v___x_1929_);
lean_ctor_set(v___x_1879_, 0, v___x_1901_);
v___x_1931_ = v___x_1879_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
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
lean_object* v_pos_1938_; lean_object* v_err_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec(v_res_1874_);
lean_dec(v_res_1846_);
lean_dec(v_res_1833_);
v_pos_1938_ = lean_ctor_get(v___x_1875_, 0);
v_err_1939_ = lean_ctor_get(v___x_1875_, 1);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1875_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_err_1939_);
lean_inc(v_pos_1938_);
lean_dec(v___x_1875_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_pos_1938_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_err_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
else
{
lean_object* v_pos_1947_; lean_object* v_err_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec(v_res_1846_);
lean_dec(v_res_1833_);
v_pos_1947_ = lean_ctor_get(v___x_1872_, 0);
v_err_1948_ = lean_ctor_get(v___x_1872_, 1);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1872_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_err_1948_);
lean_inc(v_pos_1947_);
lean_dec(v___x_1872_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_pos_1947_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_err_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
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
lean_object* v_pos_1961_; lean_object* v_err_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v_res_1833_);
v_pos_1961_ = lean_ctor_get(v___x_1844_, 0);
v_err_1962_ = lean_ctor_get(v___x_1844_, 1);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1844_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_err_1962_);
lean_inc(v_pos_1961_);
lean_dec(v___x_1844_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_pos_1961_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_err_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1971_; lean_object* v_err_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
v_pos_1971_ = lean_ctor_get(v___x_1831_, 0);
v_err_1972_ = lean_ctor_get(v___x_1831_, 1);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1831_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_err_1972_);
lean_inc(v_pos_1971_);
lean_dec(v___x_1831_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_pos_1971_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_err_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(lean_object* v_a_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v_a_1980_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_pos_1982_; lean_object* v_res_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2017_; 
v_pos_1982_ = lean_ctor_get(v___x_1981_, 0);
v_res_1983_ = lean_ctor_get(v___x_1981_, 1);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_1985_ = v___x_1981_;
v_isShared_1986_ = v_isSharedCheck_2017_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_res_1983_);
lean_inc(v_pos_1982_);
lean_dec(v___x_1981_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2017_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v_array_1987_; lean_object* v_idx_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v_array_1987_ = lean_ctor_get(v_pos_1982_, 0);
v_idx_1988_ = lean_ctor_get(v_pos_1982_, 1);
v___x_1989_ = lean_byte_array_size(v_array_1987_);
v___x_1990_ = lean_nat_dec_lt(v_idx_1988_, v___x_1989_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; lean_object* v___x_1993_; 
lean_dec(v_res_1983_);
v___x_1991_ = lean_box(0);
if (v_isShared_1986_ == 0)
{
lean_ctor_set_tag(v___x_1985_, 1);
lean_ctor_set(v___x_1985_, 1, v___x_1991_);
v___x_1993_ = v___x_1985_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_pos_1982_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
else
{
uint8_t v___x_1995_; uint8_t v_got_1996_; uint8_t v___x_1997_; 
v___x_1995_ = 0;
v_got_1996_ = lean_byte_array_fget(v_array_1987_, v_idx_1988_);
v___x_1997_ = lean_uint8_dec_eq(v_got_1996_, v___x_1995_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; lean_object* v___x_2000_; 
lean_dec(v_res_1983_);
v___x_1998_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
if (v_isShared_1986_ == 0)
{
lean_ctor_set_tag(v___x_1985_, 1);
lean_ctor_set(v___x_1985_, 1, v___x_1998_);
v___x_2000_ = v___x_1985_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_pos_1982_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
else
{
lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2014_; 
lean_inc(v_idx_1988_);
lean_inc_ref(v_array_1987_);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_pos_1982_);
if (v_isSharedCheck_2014_ == 0)
{
lean_object* v_unused_2015_; lean_object* v_unused_2016_; 
v_unused_2015_ = lean_ctor_get(v_pos_1982_, 1);
lean_dec(v_unused_2015_);
v_unused_2016_ = lean_ctor_get(v_pos_1982_, 0);
lean_dec(v_unused_2016_);
v___x_2003_ = v_pos_1982_;
v_isShared_2004_ = v_isSharedCheck_2014_;
goto v_resetjp_2002_;
}
else
{
lean_dec(v_pos_1982_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2014_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2008_; 
v___x_2005_ = lean_unsigned_to_nat(1u);
v___x_2006_ = lean_nat_add(v_idx_1988_, v___x_2005_);
lean_dec(v_idx_1988_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 1, v___x_2006_);
v___x_2008_ = v___x_2003_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_array_1987_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2009_; lean_object* v___x_2011_; 
v___x_2009_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2009_, 0, v_res_1983_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 1, v___x_2009_);
lean_ctor_set(v___x_1985_, 0, v___x_2008_);
v___x_2011_ = v___x_1985_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_2018_; lean_object* v_err_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
v_pos_2018_ = lean_ctor_get(v___x_1981_, 0);
v_err_2019_ = lean_ctor_get(v___x_1981_, 1);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_1981_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_err_2019_);
lean_inc(v_pos_2018_);
lean_dec(v___x_1981_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_pos_2018_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_err_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0(void){
_start:
{
uint32_t v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = 97;
v___x_2028_ = lean_uint32_to_uint8(v___x_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(lean_object* v_a_2030_){
_start:
{
lean_object* v_array_2031_; lean_object* v_idx_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v_array_2031_ = lean_ctor_get(v_a_2030_, 0);
v_idx_2032_ = lean_ctor_get(v_a_2030_, 1);
v___x_2033_ = lean_byte_array_size(v_array_2031_);
v___x_2034_ = lean_nat_dec_lt(v_idx_2032_, v___x_2033_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = lean_box(0);
v___x_2036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2036_, 0, v_a_2030_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
return v___x_2036_;
}
else
{
lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2058_; 
lean_inc(v_idx_2032_);
lean_inc_ref(v_array_2031_);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_a_2030_);
if (v_isSharedCheck_2058_ == 0)
{
lean_object* v_unused_2059_; lean_object* v_unused_2060_; 
v_unused_2059_ = lean_ctor_get(v_a_2030_, 1);
lean_dec(v_unused_2059_);
v_unused_2060_ = lean_ctor_get(v_a_2030_, 0);
lean_dec(v_unused_2060_);
v___x_2038_ = v_a_2030_;
v_isShared_2039_ = v_isSharedCheck_2058_;
goto v_resetjp_2037_;
}
else
{
lean_dec(v_a_2030_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2058_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
uint8_t v_c_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v_it_x27_2044_; 
v_c_2040_ = lean_byte_array_fget(v_array_2031_, v_idx_2032_);
v___x_2041_ = lean_unsigned_to_nat(1u);
v___x_2042_ = lean_nat_add(v_idx_2032_, v___x_2041_);
lean_dec(v_idx_2032_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 1, v___x_2042_);
v_it_x27_2044_ = v___x_2038_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_array_2031_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v___x_2042_);
v_it_x27_2044_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
uint8_t v___x_2045_; uint8_t v___x_2046_; 
v___x_2045_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
v___x_2046_ = lean_uint8_dec_eq(v_c_2040_, v___x_2045_);
if (v___x_2046_ == 0)
{
uint8_t v___x_2047_; uint8_t v___x_2048_; 
v___x_2047_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
v___x_2048_ = lean_uint8_dec_eq(v_c_2040_, v___x_2047_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2049_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1));
v___x_2050_ = lean_uint8_to_nat(v_c_2040_);
v___x_2051_ = l_Nat_reprFast(v___x_2050_);
v___x_2052_ = lean_string_append(v___x_2049_, v___x_2051_);
lean_dec_ref(v___x_2051_);
v___x_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
v___x_2054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2054_, 0, v_it_x27_2044_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
return v___x_2054_;
}
else
{
lean_object* v___x_2055_; 
v___x_2055_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(v_it_x27_2044_);
return v___x_2055_;
}
}
else
{
lean_object* v___x_2056_; 
v___x_2056_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(v_it_x27_2044_);
return v___x_2056_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(lean_object* v_acc_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v___x_2063_; 
lean_inc_ref(v_a_2062_);
v___x_2063_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(v_a_2062_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_pos_2064_; lean_object* v_res_2065_; lean_object* v___x_2066_; 
lean_dec_ref(v_a_2062_);
v_pos_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_pos_2064_);
v_res_2065_ = lean_ctor_get(v___x_2063_, 1);
lean_inc(v_res_2065_);
lean_dec_ref_known(v___x_2063_, 2);
v___x_2066_ = lean_array_push(v_acc_2061_, v_res_2065_);
v_acc_2061_ = v___x_2066_;
v_a_2062_ = v_pos_2064_;
goto _start;
}
else
{
lean_object* v_pos_2068_; lean_object* v_err_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2082_; 
v_pos_2068_ = lean_ctor_get(v___x_2063_, 0);
v_err_2069_ = lean_ctor_get(v___x_2063_, 1);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2071_ = v___x_2063_;
v_isShared_2072_ = v_isSharedCheck_2082_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_err_2069_);
lean_inc(v_pos_2068_);
lean_dec(v___x_2063_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2082_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v_idx_2073_; lean_object* v_idx_2074_; uint8_t v___x_2075_; 
v_idx_2073_ = lean_ctor_get(v_a_2062_, 1);
lean_inc(v_idx_2073_);
lean_dec_ref(v_a_2062_);
v_idx_2074_ = lean_ctor_get(v_pos_2068_, 1);
v___x_2075_ = lean_nat_dec_eq(v_idx_2073_, v_idx_2074_);
lean_dec(v_idx_2073_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2077_; 
lean_dec_ref(v_acc_2061_);
if (v_isShared_2072_ == 0)
{
v___x_2077_ = v___x_2071_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_pos_2068_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_err_2069_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
else
{
lean_object* v___x_2080_; 
lean_dec(v_err_2069_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set_tag(v___x_2071_, 0);
lean_ctor_set(v___x_2071_, 1, v_acc_2061_);
v___x_2080_ = v___x_2071_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_pos_2068_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v_acc_2061_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(lean_object* v_a_2086_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0));
v___x_2088_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(v___x_2087_, v_a_2086_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_pos_2089_; lean_object* v_array_2090_; lean_object* v_idx_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v_pos_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_pos_2089_);
v_array_2090_ = lean_ctor_get(v_pos_2089_, 0);
v_idx_2091_ = lean_ctor_get(v_pos_2089_, 1);
v___x_2092_ = lean_byte_array_size(v_array_2090_);
v___x_2093_ = lean_nat_dec_lt(v_idx_2091_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_dec(v_pos_2089_);
return v___x_2088_;
}
else
{
lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2101_; 
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2101_ == 0)
{
lean_object* v_unused_2102_; lean_object* v_unused_2103_; 
v_unused_2102_ = lean_ctor_get(v___x_2088_, 1);
lean_dec(v_unused_2102_);
v_unused_2103_ = lean_ctor_get(v___x_2088_, 0);
lean_dec(v_unused_2103_);
v___x_2095_ = v___x_2088_;
v_isShared_2096_ = v_isSharedCheck_2101_;
goto v_resetjp_2094_;
}
else
{
lean_dec(v___x_2088_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2101_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2097_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__1));
if (v_isShared_2096_ == 0)
{
lean_ctor_set_tag(v___x_2095_, 1);
lean_ctor_set(v___x_2095_, 1, v___x_2097_);
v___x_2099_ = v___x_2095_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_pos_2089_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
else
{
return v___x_2088_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_parseActions(lean_object* v_a_2104_){
_start:
{
lean_object* v_array_2105_; lean_object* v_idx_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; 
v_array_2105_ = lean_ctor_get(v_a_2104_, 0);
v_idx_2106_ = lean_ctor_get(v_a_2104_, 1);
v___x_2107_ = lean_byte_array_size(v_array_2105_);
v___x_2108_ = lean_nat_dec_lt(v_idx_2106_, v___x_2107_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = lean_box(0);
v___x_2110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2110_, 0, v_a_2104_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
return v___x_2110_;
}
else
{
uint8_t v___x_2111_; uint8_t v___x_2112_; uint8_t v___x_2113_; 
v___x_2111_ = lean_byte_array_fget(v_array_2105_, v_idx_2106_);
v___x_2112_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
v___x_2113_ = lean_uint8_dec_eq(v___x_2111_, v___x_2112_);
if (v___x_2113_ == 0)
{
uint8_t v___x_2114_; uint8_t v___x_2115_; 
v___x_2114_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
v___x_2115_ = lean_uint8_dec_eq(v___x_2111_, v___x_2114_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; 
v___x_2116_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(v_a_2104_);
return v___x_2116_;
}
else
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(v_a_2104_);
return v___x_2117_;
}
}
else
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(v_a_2104_);
return v___x_2118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object* v_path_2119_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_IO_FS_readBinFile(v_path_2119_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2143_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2143_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2143_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_parseActions), 1, 0);
v___x_2127_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_2126_, v_a_2122_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2138_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2130_ = v___x_2127_;
v_isShared_2131_ = v_isSharedCheck_2138_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2127_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2138_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
lean_ctor_set_tag(v___x_2130_, 18);
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2135_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set_tag(v___x_2124_, 1);
lean_ctor_set(v___x_2124_, 0, v___x_2133_);
v___x_2135_ = v___x_2124_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; 
v_a_2139_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2127_, 1);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v_a_2139_);
v___x_2141_ = v___x_2124_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2139_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
v_a_2144_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2121_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2121_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof___boxed(lean_object* v_path_2152_, lean_object* v_a_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(v_path_2152_);
lean_dec_ref(v_path_2152_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_parseLRATProof(lean_object* v_proof_2155_){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_parseActions), 1, 0);
v___x_2157_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_2156_, v_proof_2155_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(lean_object* v_as_2159_, size_t v_i_2160_, size_t v_stop_2161_, lean_object* v_b_2162_){
_start:
{
uint8_t v___x_2163_; 
v___x_2163_ = lean_usize_dec_eq(v_i_2160_, v_stop_2161_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; size_t v___x_2169_; size_t v___x_2170_; 
v___x_2164_ = lean_array_uget_borrowed(v_as_2159_, v_i_2160_);
lean_inc(v___x_2164_);
v___x_2165_ = l_Nat_reprFast(v___x_2164_);
v___x_2166_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2167_ = lean_string_append(v___x_2165_, v___x_2166_);
v___x_2168_ = lean_string_append(v_b_2162_, v___x_2167_);
lean_dec_ref(v___x_2167_);
v___x_2169_ = ((size_t)1ULL);
v___x_2170_ = lean_usize_add(v_i_2160_, v___x_2169_);
v_i_2160_ = v___x_2170_;
v_b_2162_ = v___x_2168_;
goto _start;
}
else
{
return v_b_2162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___boxed(lean_object* v_as_2172_, lean_object* v_i_2173_, lean_object* v_stop_2174_, lean_object* v_b_2175_){
_start:
{
size_t v_i_boxed_2176_; size_t v_stop_boxed_2177_; lean_object* v_res_2178_; 
v_i_boxed_2176_ = lean_unbox_usize(v_i_2173_);
lean_dec(v_i_2173_);
v_stop_boxed_2177_ = lean_unbox_usize(v_stop_2174_);
lean_dec(v_stop_2174_);
v_res_2178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_as_2172_, v_i_boxed_2176_, v_stop_boxed_2177_, v_b_2175_);
lean_dec_ref(v_as_2172_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(lean_object* v_ids_2180_){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
v___x_2181_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2182_ = lean_unsigned_to_nat(0u);
v___x_2183_ = lean_array_get_size(v_ids_2180_);
v___x_2184_ = lean_nat_dec_lt(v___x_2182_, v___x_2183_);
if (v___x_2184_ == 0)
{
return v___x_2181_;
}
else
{
uint8_t v___x_2185_; 
v___x_2185_ = lean_nat_dec_le(v___x_2183_, v___x_2183_);
if (v___x_2185_ == 0)
{
if (v___x_2184_ == 0)
{
return v___x_2181_;
}
else
{
size_t v___x_2186_; size_t v___x_2187_; lean_object* v___x_2188_; 
v___x_2186_ = ((size_t)0ULL);
v___x_2187_ = lean_usize_of_nat(v___x_2183_);
v___x_2188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_ids_2180_, v___x_2186_, v___x_2187_, v___x_2181_);
return v___x_2188_;
}
}
else
{
size_t v___x_2189_; size_t v___x_2190_; lean_object* v___x_2191_; 
v___x_2189_ = ((size_t)0ULL);
v___x_2190_ = lean_usize_of_nat(v___x_2183_);
v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_ids_2180_, v___x_2189_, v___x_2190_, v___x_2181_);
return v___x_2191_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___boxed(lean_object* v_ids_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_ids_2192_);
lean_dec_ref(v_ids_2192_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(lean_object* v_hint_2195_){
_start:
{
lean_object* v_fst_2196_; lean_object* v_snd_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_fst_2196_ = lean_ctor_get(v_hint_2195_, 0);
lean_inc(v_fst_2196_);
v_snd_2197_ = lean_ctor_get(v_hint_2195_, 1);
lean_inc(v_snd_2197_);
lean_dec_ref(v_hint_2195_);
v___x_2198_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0));
v___x_2199_ = l_Nat_reprFast(v_fst_2196_);
v___x_2200_ = lean_string_append(v___x_2198_, v___x_2199_);
lean_dec_ref(v___x_2199_);
v___x_2201_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2202_ = lean_string_append(v___x_2200_, v___x_2201_);
v___x_2203_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_snd_2197_);
lean_dec(v_snd_2197_);
v___x_2204_ = lean_string_append(v___x_2202_, v___x_2203_);
lean_dec_ref(v___x_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(lean_object* v_as_2205_, size_t v_i_2206_, size_t v_stop_2207_, lean_object* v_b_2208_){
_start:
{
uint8_t v___x_2209_; 
v___x_2209_ = lean_usize_dec_eq(v_i_2206_, v_stop_2207_);
if (v___x_2209_ == 0)
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; size_t v___x_2213_; size_t v___x_2214_; 
v___x_2210_ = lean_array_uget_borrowed(v_as_2205_, v_i_2206_);
lean_inc(v___x_2210_);
v___x_2211_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(v___x_2210_);
v___x_2212_ = lean_string_append(v_b_2208_, v___x_2211_);
lean_dec_ref(v___x_2211_);
v___x_2213_ = ((size_t)1ULL);
v___x_2214_ = lean_usize_add(v_i_2206_, v___x_2213_);
v_i_2206_ = v___x_2214_;
v_b_2208_ = v___x_2212_;
goto _start;
}
else
{
return v_b_2208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0___boxed(lean_object* v_as_2216_, lean_object* v_i_2217_, lean_object* v_stop_2218_, lean_object* v_b_2219_){
_start:
{
size_t v_i_boxed_2220_; size_t v_stop_boxed_2221_; lean_object* v_res_2222_; 
v_i_boxed_2220_ = lean_unbox_usize(v_i_2217_);
lean_dec(v_i_2217_);
v_stop_boxed_2221_ = lean_unbox_usize(v_stop_2218_);
lean_dec(v_stop_2218_);
v_res_2222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_as_2216_, v_i_boxed_2220_, v_stop_boxed_2221_, v_b_2219_);
lean_dec_ref(v_as_2216_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(lean_object* v_hints_2223_){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___x_2224_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2225_ = lean_unsigned_to_nat(0u);
v___x_2226_ = lean_array_get_size(v_hints_2223_);
v___x_2227_ = lean_nat_dec_lt(v___x_2225_, v___x_2226_);
if (v___x_2227_ == 0)
{
return v___x_2224_;
}
else
{
uint8_t v___x_2228_; 
v___x_2228_ = lean_nat_dec_le(v___x_2226_, v___x_2226_);
if (v___x_2228_ == 0)
{
if (v___x_2227_ == 0)
{
return v___x_2224_;
}
else
{
size_t v___x_2229_; size_t v___x_2230_; lean_object* v___x_2231_; 
v___x_2229_ = ((size_t)0ULL);
v___x_2230_ = lean_usize_of_nat(v___x_2226_);
v___x_2231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_hints_2223_, v___x_2229_, v___x_2230_, v___x_2224_);
return v___x_2231_;
}
}
else
{
size_t v___x_2232_; size_t v___x_2233_; lean_object* v___x_2234_; 
v___x_2232_ = ((size_t)0ULL);
v___x_2233_ = lean_usize_of_nat(v___x_2226_);
v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_hints_2223_, v___x_2232_, v___x_2233_, v___x_2224_);
return v___x_2234_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___boxed(lean_object* v_hints_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(v_hints_2235_);
lean_dec_ref(v_hints_2235_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(lean_object* v_as_2237_, size_t v_i_2238_, size_t v_stop_2239_, lean_object* v_b_2240_){
_start:
{
uint8_t v___x_2241_; 
v___x_2241_ = lean_usize_dec_eq(v_i_2238_, v_stop_2239_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; size_t v___x_2247_; size_t v___x_2248_; 
v___x_2242_ = lean_array_uget_borrowed(v_as_2237_, v_i_2238_);
v___x_2243_ = l_Int_repr(v___x_2242_);
v___x_2244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2245_ = lean_string_append(v___x_2243_, v___x_2244_);
v___x_2246_ = lean_string_append(v_b_2240_, v___x_2245_);
lean_dec_ref(v___x_2245_);
v___x_2247_ = ((size_t)1ULL);
v___x_2248_ = lean_usize_add(v_i_2238_, v___x_2247_);
v_i_2238_ = v___x_2248_;
v_b_2240_ = v___x_2246_;
goto _start;
}
else
{
return v_b_2240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0___boxed(lean_object* v_as_2250_, lean_object* v_i_2251_, lean_object* v_stop_2252_, lean_object* v_b_2253_){
_start:
{
size_t v_i_boxed_2254_; size_t v_stop_boxed_2255_; lean_object* v_res_2256_; 
v_i_boxed_2254_ = lean_unbox_usize(v_i_2251_);
lean_dec(v_i_2251_);
v_stop_boxed_2255_ = lean_unbox_usize(v_stop_2252_);
lean_dec(v_stop_2252_);
v_res_2256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_as_2250_, v_i_boxed_2254_, v_stop_boxed_2255_, v_b_2253_);
lean_dec_ref(v_as_2250_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(lean_object* v_clause_2257_){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; 
v___x_2258_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2259_ = lean_unsigned_to_nat(0u);
v___x_2260_ = lean_array_get_size(v_clause_2257_);
v___x_2261_ = lean_nat_dec_lt(v___x_2259_, v___x_2260_);
if (v___x_2261_ == 0)
{
return v___x_2258_;
}
else
{
uint8_t v___x_2262_; 
v___x_2262_ = lean_nat_dec_le(v___x_2260_, v___x_2260_);
if (v___x_2262_ == 0)
{
if (v___x_2261_ == 0)
{
return v___x_2258_;
}
else
{
size_t v___x_2263_; size_t v___x_2264_; lean_object* v___x_2265_; 
v___x_2263_ = ((size_t)0ULL);
v___x_2264_ = lean_usize_of_nat(v___x_2260_);
v___x_2265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_clause_2257_, v___x_2263_, v___x_2264_, v___x_2258_);
return v___x_2265_;
}
}
else
{
size_t v___x_2266_; size_t v___x_2267_; lean_object* v___x_2268_; 
v___x_2266_ = ((size_t)0ULL);
v___x_2267_ = lean_usize_of_nat(v___x_2260_);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_clause_2257_, v___x_2266_, v___x_2267_, v___x_2258_);
return v___x_2268_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___boxed(lean_object* v_clause_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_clause_2269_);
lean_dec_ref(v_clause_2269_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(lean_object* v_a_2275_){
_start:
{
switch(lean_obj_tag(v_a_2275_))
{
case 0:
{
lean_object* v_id_2276_; lean_object* v_rupHints_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v_id_2276_ = lean_ctor_get(v_a_2275_, 0);
lean_inc(v_id_2276_);
v_rupHints_2277_ = lean_ctor_get(v_a_2275_, 1);
lean_inc_ref(v_rupHints_2277_);
lean_dec_ref_known(v_a_2275_, 2);
v___x_2278_ = l_Nat_reprFast(v_id_2276_);
v___x_2279_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__0));
v___x_2280_ = lean_string_append(v___x_2278_, v___x_2279_);
v___x_2281_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2277_);
lean_dec_ref(v_rupHints_2277_);
v___x_2282_ = lean_string_append(v___x_2280_, v___x_2281_);
lean_dec_ref(v___x_2281_);
v___x_2283_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2284_ = lean_string_append(v___x_2282_, v___x_2283_);
return v___x_2284_;
}
case 1:
{
lean_object* v_id_2285_; lean_object* v_c_2286_; lean_object* v_rupHints_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v_id_2285_ = lean_ctor_get(v_a_2275_, 0);
lean_inc(v_id_2285_);
v_c_2286_ = lean_ctor_get(v_a_2275_, 1);
lean_inc(v_c_2286_);
v_rupHints_2287_ = lean_ctor_get(v_a_2275_, 2);
lean_inc_ref(v_rupHints_2287_);
lean_dec_ref_known(v_a_2275_, 3);
v___x_2288_ = l_Nat_reprFast(v_id_2285_);
v___x_2289_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2290_ = lean_string_append(v___x_2288_, v___x_2289_);
v___x_2291_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_c_2286_);
lean_dec(v_c_2286_);
v___x_2292_ = lean_string_append(v___x_2290_, v___x_2291_);
lean_dec_ref(v___x_2291_);
v___x_2293_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2));
v___x_2294_ = lean_string_append(v___x_2292_, v___x_2293_);
v___x_2295_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2287_);
lean_dec_ref(v_rupHints_2287_);
v___x_2296_ = lean_string_append(v___x_2294_, v___x_2295_);
lean_dec_ref(v___x_2295_);
v___x_2297_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2298_ = lean_string_append(v___x_2296_, v___x_2297_);
return v___x_2298_;
}
case 2:
{
lean_object* v_id_2299_; lean_object* v_c_2300_; lean_object* v_rupHints_2301_; lean_object* v_ratHints_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v_id_2299_ = lean_ctor_get(v_a_2275_, 0);
lean_inc(v_id_2299_);
v_c_2300_ = lean_ctor_get(v_a_2275_, 1);
lean_inc(v_c_2300_);
v_rupHints_2301_ = lean_ctor_get(v_a_2275_, 3);
lean_inc_ref(v_rupHints_2301_);
v_ratHints_2302_ = lean_ctor_get(v_a_2275_, 4);
lean_inc_ref(v_ratHints_2302_);
lean_dec_ref_known(v_a_2275_, 5);
v___x_2303_ = l_Nat_reprFast(v_id_2299_);
v___x_2304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2305_ = lean_string_append(v___x_2303_, v___x_2304_);
v___x_2306_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_c_2300_);
lean_dec(v_c_2300_);
v___x_2307_ = lean_string_append(v___x_2305_, v___x_2306_);
lean_dec_ref(v___x_2306_);
v___x_2308_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2));
v___x_2309_ = lean_string_append(v___x_2307_, v___x_2308_);
v___x_2310_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2301_);
lean_dec_ref(v_rupHints_2301_);
v___x_2311_ = lean_string_append(v___x_2309_, v___x_2310_);
lean_dec_ref(v___x_2310_);
v___x_2312_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(v_ratHints_2302_);
lean_dec_ref(v_ratHints_2302_);
v___x_2313_ = lean_string_append(v___x_2311_, v___x_2312_);
lean_dec_ref(v___x_2312_);
v___x_2314_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2315_ = lean_string_append(v___x_2313_, v___x_2314_);
return v___x_2315_;
}
default: 
{
lean_object* v_ids_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v_ids_2316_ = lean_ctor_get(v_a_2275_, 0);
lean_inc_ref(v_ids_2316_);
lean_dec_ref_known(v_a_2275_, 1);
v___x_2317_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3));
v___x_2318_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_ids_2316_);
lean_dec_ref(v_ids_2316_);
v___x_2319_ = lean_string_append(v___x_2317_, v___x_2318_);
lean_dec_ref(v___x_2318_);
v___x_2320_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2321_ = lean_string_append(v___x_2319_, v___x_2320_);
return v___x_2321_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(lean_object* v_as_2323_, size_t v_i_2324_, size_t v_stop_2325_, lean_object* v_b_2326_){
_start:
{
uint8_t v___x_2327_; 
v___x_2327_ = lean_usize_dec_eq(v_i_2324_, v_stop_2325_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; size_t v___x_2333_; size_t v___x_2334_; 
v___x_2328_ = lean_array_uget_borrowed(v_as_2323_, v_i_2324_);
lean_inc(v___x_2328_);
v___x_2329_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(v___x_2328_);
v___x_2330_ = lean_string_append(v_b_2326_, v___x_2329_);
lean_dec_ref(v___x_2329_);
v___x_2331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___closed__0));
v___x_2332_ = lean_string_append(v___x_2330_, v___x_2331_);
v___x_2333_ = ((size_t)1ULL);
v___x_2334_ = lean_usize_add(v_i_2324_, v___x_2333_);
v_i_2324_ = v___x_2334_;
v_b_2326_ = v___x_2332_;
goto _start;
}
else
{
return v_b_2326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___boxed(lean_object* v_as_2336_, lean_object* v_i_2337_, lean_object* v_stop_2338_, lean_object* v_b_2339_){
_start:
{
size_t v_i_boxed_2340_; size_t v_stop_boxed_2341_; lean_object* v_res_2342_; 
v_i_boxed_2340_ = lean_unbox_usize(v_i_2337_);
lean_dec(v_i_2337_);
v_stop_boxed_2341_ = lean_unbox_usize(v_stop_2338_);
lean_dec(v_stop_2338_);
v_res_2342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_as_2336_, v_i_boxed_2340_, v_stop_boxed_2341_, v_b_2339_);
lean_dec_ref(v_as_2336_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString(lean_object* v_proof_2343_){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___x_2344_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2345_ = lean_unsigned_to_nat(0u);
v___x_2346_ = lean_array_get_size(v_proof_2343_);
v___x_2347_ = lean_nat_dec_lt(v___x_2345_, v___x_2346_);
if (v___x_2347_ == 0)
{
return v___x_2344_;
}
else
{
uint8_t v___x_2348_; 
v___x_2348_ = lean_nat_dec_le(v___x_2346_, v___x_2346_);
if (v___x_2348_ == 0)
{
if (v___x_2347_ == 0)
{
return v___x_2344_;
}
else
{
size_t v___x_2349_; size_t v___x_2350_; lean_object* v___x_2351_; 
v___x_2349_ = ((size_t)0ULL);
v___x_2350_ = lean_usize_of_nat(v___x_2346_);
v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_proof_2343_, v___x_2349_, v___x_2350_, v___x_2344_);
return v___x_2351_;
}
}
else
{
size_t v___x_2352_; size_t v___x_2353_; lean_object* v___x_2354_; 
v___x_2352_ = ((size_t)0ULL);
v___x_2353_ = lean_usize_of_nat(v___x_2346_);
v___x_2354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_proof_2343_, v___x_2352_, v___x_2353_, v___x_2344_);
return v___x_2354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString___boxed(lean_object* v_proof_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_proof_2355_);
lean_dec_ref(v_proof_2355_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startDelete(lean_object* v_acc_2357_){
_start:
{
uint8_t v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
v___x_2359_ = lean_byte_array_push(v_acc_2357_, v___x_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(lean_object* v_acc_2360_, uint64_t v_lit_2361_){
_start:
{
uint8_t v___y_2363_; uint64_t v___x_2368_; uint8_t v___x_2369_; 
v___x_2368_ = 0ULL;
v___x_2369_ = lean_uint64_dec_eq(v_lit_2361_, v___x_2368_);
if (v___x_2369_ == 0)
{
uint64_t v___x_2370_; uint8_t v___x_2371_; 
v___x_2370_ = 127ULL;
v___x_2371_ = lean_uint64_dec_lt(v___x_2370_, v_lit_2361_);
if (v___x_2371_ == 0)
{
uint8_t v___x_2372_; uint8_t v___x_2373_; uint8_t v___x_2374_; 
v___x_2372_ = lean_uint64_to_uint8(v_lit_2361_);
v___x_2373_ = 127;
v___x_2374_ = lean_uint8_land(v___x_2372_, v___x_2373_);
v___y_2363_ = v___x_2374_;
goto v___jp_2362_;
}
else
{
uint8_t v___x_2375_; uint8_t v___x_2376_; uint8_t v___x_2377_; uint8_t v___x_2378_; uint8_t v___x_2379_; 
v___x_2375_ = lean_uint64_to_uint8(v_lit_2361_);
v___x_2376_ = 127;
v___x_2377_ = lean_uint8_land(v___x_2375_, v___x_2376_);
v___x_2378_ = 128;
v___x_2379_ = lean_uint8_lor(v___x_2377_, v___x_2378_);
v___y_2363_ = v___x_2379_;
goto v___jp_2362_;
}
}
else
{
return v_acc_2360_;
}
v___jp_2362_:
{
lean_object* v_acc_2364_; uint64_t v___x_2365_; uint64_t v___x_2366_; 
v_acc_2364_ = lean_byte_array_push(v_acc_2360_, v___y_2363_);
v___x_2365_ = 7ULL;
v___x_2366_ = lean_uint64_shift_right(v_lit_2361_, v___x_2365_);
v_acc_2360_ = v_acc_2364_;
v_lit_2361_ = v___x_2366_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode___boxed(lean_object* v_acc_2380_, lean_object* v_lit_2381_){
_start:
{
uint64_t v_lit_boxed_2382_; lean_object* v_res_2383_; 
v_lit_boxed_2382_ = lean_unbox_uint64(v_lit_2381_);
lean_dec_ref(v_lit_2381_);
v_res_2383_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(v_acc_2380_, v_lit_boxed_2382_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(lean_object* v_msg_2384_){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = l_ByteArray_empty;
v___x_2386_ = lean_panic_fn_borrowed(v___x_2385_, v_msg_2384_);
return v___x_2386_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0(void){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = lean_cstr_to_nat("18446744073709551615");
return v___x_2387_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2391_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3));
v___x_2392_ = lean_unsigned_to_nat(4u);
v___x_2393_ = lean_unsigned_to_nat(400u);
v___x_2394_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2));
v___x_2395_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1));
v___x_2396_ = l_mkPanicMessageWithDecl(v___x_2395_, v___x_2394_, v___x_2393_, v___x_2392_, v___x_2391_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(lean_object* v_acc_2397_, lean_object* v_lit_2398_){
_start:
{
lean_object* v___y_2400_; lean_object* v___x_2407_; uint8_t v___x_2408_; 
v___x_2407_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_2408_ = lean_int_dec_lt(v___x_2407_, v_lit_2398_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2409_ = lean_unsigned_to_nat(2u);
v___x_2410_ = lean_nat_abs(v_lit_2398_);
v___x_2411_ = lean_nat_mul(v___x_2409_, v___x_2410_);
lean_dec(v___x_2410_);
v___x_2412_ = lean_unsigned_to_nat(1u);
v___x_2413_ = lean_nat_add(v___x_2411_, v___x_2412_);
lean_dec(v___x_2411_);
v___y_2400_ = v___x_2413_;
goto v___jp_2399_;
}
else
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2414_ = lean_unsigned_to_nat(2u);
v___x_2415_ = lean_nat_abs(v_lit_2398_);
v___x_2416_ = lean_nat_mul(v___x_2414_, v___x_2415_);
lean_dec(v___x_2415_);
v___y_2400_ = v___x_2416_;
goto v___jp_2399_;
}
v___jp_2399_:
{
lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2401_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0);
v___x_2402_ = lean_nat_dec_le(v___y_2400_, v___x_2401_);
if (v___x_2402_ == 0)
{
lean_object* v___x_2403_; lean_object* v___x_2404_; 
lean_dec(v___y_2400_);
lean_dec_ref(v_acc_2397_);
v___x_2403_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4);
v___x_2404_ = l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(v___x_2403_);
return v___x_2404_;
}
else
{
uint64_t v_mapped_2405_; lean_object* v___x_2406_; 
v_mapped_2405_ = lean_uint64_of_nat(v___y_2400_);
lean_dec(v___y_2400_);
v___x_2406_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(v_acc_2397_, v_mapped_2405_);
return v___x_2406_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___boxed(lean_object* v_acc_2417_, lean_object* v_lit_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2417_, v_lit_2418_);
lean_dec(v_lit_2418_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_zeroByte(lean_object* v_acc_2420_){
_start:
{
uint8_t v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = 0;
v___x_2422_ = lean_byte_array_push(v_acc_2420_, v___x_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addNat(lean_object* v_acc_2423_, lean_object* v_n_2424_){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = lean_nat_to_int(v_n_2424_);
v___x_2426_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2423_, v___x_2425_);
lean_dec(v___x_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startAdd(lean_object* v_acc_2427_){
_start:
{
uint8_t v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
v___x_2429_ = lean_byte_array_push(v_acc_2427_, v___x_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(lean_object* v_as_2430_, size_t v_i_2431_, size_t v_stop_2432_, lean_object* v_b_2433_){
_start:
{
uint8_t v___x_2434_; 
v___x_2434_ = lean_usize_dec_eq(v_i_2431_, v_stop_2432_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; size_t v___x_2438_; size_t v___x_2439_; 
v___x_2435_ = lean_array_uget_borrowed(v_as_2430_, v_i_2431_);
lean_inc(v___x_2435_);
v___x_2436_ = lean_nat_to_int(v___x_2435_);
v___x_2437_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2433_, v___x_2436_);
lean_dec(v___x_2436_);
v___x_2438_ = ((size_t)1ULL);
v___x_2439_ = lean_usize_add(v_i_2431_, v___x_2438_);
v_i_2431_ = v___x_2439_;
v_b_2433_ = v___x_2437_;
goto _start;
}
else
{
return v_b_2433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0___boxed(lean_object* v_as_2441_, lean_object* v_i_2442_, lean_object* v_stop_2443_, lean_object* v_b_2444_){
_start:
{
size_t v_i_boxed_2445_; size_t v_stop_boxed_2446_; lean_object* v_res_2447_; 
v_i_boxed_2445_ = lean_unbox_usize(v_i_2442_);
lean_dec(v_i_2442_);
v_stop_boxed_2446_ = lean_unbox_usize(v_stop_2443_);
lean_dec(v_stop_2443_);
v_res_2447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(v_as_2441_, v_i_boxed_2445_, v_stop_boxed_2446_, v_b_2444_);
lean_dec_ref(v_as_2441_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(lean_object* v_as_2448_, size_t v_i_2449_, size_t v_stop_2450_, lean_object* v_b_2451_){
_start:
{
uint8_t v___x_2452_; 
v___x_2452_ = lean_usize_dec_eq(v_i_2449_, v_stop_2450_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; size_t v___x_2456_; size_t v___x_2457_; lean_object* v___x_2458_; 
v___x_2453_ = lean_array_uget_borrowed(v_as_2448_, v_i_2449_);
lean_inc(v___x_2453_);
v___x_2454_ = lean_nat_to_int(v___x_2453_);
v___x_2455_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2451_, v___x_2454_);
lean_dec(v___x_2454_);
v___x_2456_ = ((size_t)1ULL);
v___x_2457_ = lean_usize_add(v_i_2449_, v___x_2456_);
v___x_2458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(v_as_2448_, v___x_2457_, v_stop_2450_, v___x_2455_);
return v___x_2458_;
}
else
{
return v_b_2451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0___boxed(lean_object* v_as_2459_, lean_object* v_i_2460_, lean_object* v_stop_2461_, lean_object* v_b_2462_){
_start:
{
size_t v_i_boxed_2463_; size_t v_stop_boxed_2464_; lean_object* v_res_2465_; 
v_i_boxed_2463_ = lean_unbox_usize(v_i_2460_);
lean_dec(v_i_2460_);
v_stop_boxed_2464_ = lean_unbox_usize(v_stop_2461_);
lean_dec(v_stop_2461_);
v_res_2465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_as_2459_, v_i_boxed_2463_, v_stop_boxed_2464_, v_b_2462_);
lean_dec_ref(v_as_2459_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(lean_object* v_as_2466_, size_t v_i_2467_, size_t v_stop_2468_, lean_object* v_b_2469_){
_start:
{
lean_object* v___y_2471_; uint8_t v___x_2475_; 
v___x_2475_ = lean_usize_dec_eq(v_i_2467_, v_stop_2468_);
if (v___x_2475_ == 0)
{
lean_object* v___x_2476_; lean_object* v_fst_2477_; lean_object* v_snd_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v_acc_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; 
v___x_2476_ = lean_array_uget_borrowed(v_as_2466_, v_i_2467_);
v_fst_2477_ = lean_ctor_get(v___x_2476_, 0);
v_snd_2478_ = lean_ctor_get(v___x_2476_, 1);
v___x_2479_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_2477_);
v___x_2480_ = lean_nat_to_int(v_fst_2477_);
v___x_2481_ = lean_int_neg(v___x_2480_);
lean_dec(v___x_2480_);
v_acc_2482_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2469_, v___x_2481_);
lean_dec(v___x_2481_);
v___x_2483_ = lean_array_get_size(v_snd_2478_);
v___x_2484_ = lean_nat_dec_lt(v___x_2479_, v___x_2483_);
if (v___x_2484_ == 0)
{
v___y_2471_ = v_acc_2482_;
goto v___jp_2470_;
}
else
{
uint8_t v___x_2485_; 
v___x_2485_ = lean_nat_dec_le(v___x_2483_, v___x_2483_);
if (v___x_2485_ == 0)
{
if (v___x_2484_ == 0)
{
v___y_2471_ = v_acc_2482_;
goto v___jp_2470_;
}
else
{
size_t v___x_2486_; size_t v___x_2487_; lean_object* v___x_2488_; 
v___x_2486_ = ((size_t)0ULL);
v___x_2487_ = lean_usize_of_nat(v___x_2483_);
v___x_2488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2478_, v___x_2486_, v___x_2487_, v_acc_2482_);
v___y_2471_ = v___x_2488_;
goto v___jp_2470_;
}
}
else
{
size_t v___x_2489_; size_t v___x_2490_; lean_object* v___x_2491_; 
v___x_2489_ = ((size_t)0ULL);
v___x_2490_ = lean_usize_of_nat(v___x_2483_);
v___x_2491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2478_, v___x_2489_, v___x_2490_, v_acc_2482_);
v___y_2471_ = v___x_2491_;
goto v___jp_2470_;
}
}
}
else
{
return v_b_2469_;
}
v___jp_2470_:
{
size_t v___x_2472_; size_t v___x_2473_; 
v___x_2472_ = ((size_t)1ULL);
v___x_2473_ = lean_usize_add(v_i_2467_, v___x_2472_);
v_i_2467_ = v___x_2473_;
v_b_2469_ = v___y_2471_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3___boxed(lean_object* v_as_2492_, lean_object* v_i_2493_, lean_object* v_stop_2494_, lean_object* v_b_2495_){
_start:
{
size_t v_i_boxed_2496_; size_t v_stop_boxed_2497_; lean_object* v_res_2498_; 
v_i_boxed_2496_ = lean_unbox_usize(v_i_2493_);
lean_dec(v_i_2493_);
v_stop_boxed_2497_ = lean_unbox_usize(v_stop_2494_);
lean_dec(v_stop_2494_);
v_res_2498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(v_as_2492_, v_i_boxed_2496_, v_stop_boxed_2497_, v_b_2495_);
lean_dec_ref(v_as_2492_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(lean_object* v_as_2499_, size_t v_i_2500_, size_t v_stop_2501_, lean_object* v_b_2502_){
_start:
{
lean_object* v___y_2504_; uint8_t v___x_2508_; 
v___x_2508_ = lean_usize_dec_eq(v_i_2500_, v_stop_2501_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; lean_object* v_fst_2510_; lean_object* v_snd_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v_acc_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; 
v___x_2509_ = lean_array_uget_borrowed(v_as_2499_, v_i_2500_);
v_fst_2510_ = lean_ctor_get(v___x_2509_, 0);
v_snd_2511_ = lean_ctor_get(v___x_2509_, 1);
v___x_2512_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_2510_);
v___x_2513_ = lean_nat_to_int(v_fst_2510_);
v___x_2514_ = lean_int_neg(v___x_2513_);
lean_dec(v___x_2513_);
v_acc_2515_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2502_, v___x_2514_);
lean_dec(v___x_2514_);
v___x_2516_ = lean_array_get_size(v_snd_2511_);
v___x_2517_ = lean_nat_dec_lt(v___x_2512_, v___x_2516_);
if (v___x_2517_ == 0)
{
v___y_2504_ = v_acc_2515_;
goto v___jp_2503_;
}
else
{
uint8_t v___x_2518_; 
v___x_2518_ = lean_nat_dec_le(v___x_2516_, v___x_2516_);
if (v___x_2518_ == 0)
{
if (v___x_2517_ == 0)
{
v___y_2504_ = v_acc_2515_;
goto v___jp_2503_;
}
else
{
size_t v___x_2519_; size_t v___x_2520_; lean_object* v___x_2521_; 
v___x_2519_ = ((size_t)0ULL);
v___x_2520_ = lean_usize_of_nat(v___x_2516_);
v___x_2521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2511_, v___x_2519_, v___x_2520_, v_acc_2515_);
v___y_2504_ = v___x_2521_;
goto v___jp_2503_;
}
}
else
{
size_t v___x_2522_; size_t v___x_2523_; lean_object* v___x_2524_; 
v___x_2522_ = ((size_t)0ULL);
v___x_2523_ = lean_usize_of_nat(v___x_2516_);
v___x_2524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2511_, v___x_2522_, v___x_2523_, v_acc_2515_);
v___y_2504_ = v___x_2524_;
goto v___jp_2503_;
}
}
}
else
{
return v_b_2502_;
}
v___jp_2503_:
{
size_t v___x_2505_; size_t v___x_2506_; lean_object* v___x_2507_; 
v___x_2505_ = ((size_t)1ULL);
v___x_2506_ = lean_usize_add(v_i_2500_, v___x_2505_);
v___x_2507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(v_as_2499_, v___x_2506_, v_stop_2501_, v___y_2504_);
return v___x_2507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2___boxed(lean_object* v_as_2525_, lean_object* v_i_2526_, lean_object* v_stop_2527_, lean_object* v_b_2528_){
_start:
{
size_t v_i_boxed_2529_; size_t v_stop_boxed_2530_; lean_object* v_res_2531_; 
v_i_boxed_2529_ = lean_unbox_usize(v_i_2526_);
lean_dec(v_i_2526_);
v_stop_boxed_2530_ = lean_unbox_usize(v_stop_2527_);
lean_dec(v_stop_2527_);
v_res_2531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_as_2525_, v_i_boxed_2529_, v_stop_boxed_2530_, v_b_2528_);
lean_dec_ref(v_as_2525_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(lean_object* v_as_2532_, size_t v_i_2533_, size_t v_stop_2534_, lean_object* v_b_2535_){
_start:
{
uint8_t v___x_2536_; 
v___x_2536_ = lean_usize_dec_eq(v_i_2533_, v_stop_2534_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; lean_object* v___x_2538_; size_t v___x_2539_; size_t v___x_2540_; 
v___x_2537_ = lean_array_uget_borrowed(v_as_2532_, v_i_2533_);
v___x_2538_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2535_, v___x_2537_);
v___x_2539_ = ((size_t)1ULL);
v___x_2540_ = lean_usize_add(v_i_2533_, v___x_2539_);
v_i_2533_ = v___x_2540_;
v_b_2535_ = v___x_2538_;
goto _start;
}
else
{
return v_b_2535_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1___boxed(lean_object* v_as_2542_, lean_object* v_i_2543_, lean_object* v_stop_2544_, lean_object* v_b_2545_){
_start:
{
size_t v_i_boxed_2546_; size_t v_stop_boxed_2547_; lean_object* v_res_2548_; 
v_i_boxed_2546_ = lean_unbox_usize(v_i_2543_);
lean_dec(v_i_2543_);
v_stop_boxed_2547_ = lean_unbox_usize(v_stop_2544_);
lean_dec(v_stop_2544_);
v_res_2548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_as_2542_, v_i_boxed_2546_, v_stop_boxed_2547_, v_b_2545_);
lean_dec_ref(v_as_2542_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(lean_object* v_proof_2549_, lean_object* v_idx_2550_, lean_object* v_acc_2551_){
_start:
{
lean_object* v___y_2553_; lean_object* v___y_2558_; lean_object* v___y_2562_; lean_object* v___y_2566_; lean_object* v___y_2570_; lean_object* v___x_2573_; uint8_t v___x_2574_; 
v___x_2573_ = lean_array_get_size(v_proof_2549_);
v___x_2574_ = lean_nat_dec_lt(v_idx_2550_, v___x_2573_);
if (v___x_2574_ == 0)
{
lean_dec(v_idx_2550_);
return v_acc_2551_;
}
else
{
lean_object* v___x_2575_; 
v___x_2575_ = lean_array_fget_borrowed(v_proof_2549_, v_idx_2550_);
switch(lean_obj_tag(v___x_2575_))
{
case 0:
{
lean_object* v_id_2576_; lean_object* v_rupHints_2577_; uint8_t v___x_2578_; lean_object* v_acc_2579_; lean_object* v___x_2580_; lean_object* v_acc_2581_; uint8_t v___x_2582_; lean_object* v_acc_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; 
v_id_2576_ = lean_ctor_get(v___x_2575_, 0);
v_rupHints_2577_ = lean_ctor_get(v___x_2575_, 1);
v___x_2578_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
v_acc_2579_ = lean_byte_array_push(v_acc_2551_, v___x_2578_);
lean_inc(v_id_2576_);
v___x_2580_ = lean_nat_to_int(v_id_2576_);
v_acc_2581_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2579_, v___x_2580_);
lean_dec(v___x_2580_);
v___x_2582_ = 0;
v_acc_2583_ = lean_byte_array_push(v_acc_2581_, v___x_2582_);
v___x_2584_ = lean_unsigned_to_nat(0u);
v___x_2585_ = lean_array_get_size(v_rupHints_2577_);
v___x_2586_ = lean_nat_dec_lt(v___x_2584_, v___x_2585_);
if (v___x_2586_ == 0)
{
v___y_2562_ = v_acc_2583_;
goto v___jp_2561_;
}
else
{
uint8_t v___x_2587_; 
v___x_2587_ = lean_nat_dec_le(v___x_2585_, v___x_2585_);
if (v___x_2587_ == 0)
{
if (v___x_2586_ == 0)
{
v___y_2562_ = v_acc_2583_;
goto v___jp_2561_;
}
else
{
size_t v___x_2588_; size_t v___x_2589_; lean_object* v___x_2590_; 
v___x_2588_ = ((size_t)0ULL);
v___x_2589_ = lean_usize_of_nat(v___x_2585_);
v___x_2590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2577_, v___x_2588_, v___x_2589_, v_acc_2583_);
v___y_2562_ = v___x_2590_;
goto v___jp_2561_;
}
}
else
{
size_t v___x_2591_; size_t v___x_2592_; lean_object* v___x_2593_; 
v___x_2591_ = ((size_t)0ULL);
v___x_2592_ = lean_usize_of_nat(v___x_2585_);
v___x_2593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2577_, v___x_2591_, v___x_2592_, v_acc_2583_);
v___y_2562_ = v___x_2593_;
goto v___jp_2561_;
}
}
}
case 1:
{
lean_object* v_id_2594_; lean_object* v_c_2595_; lean_object* v_rupHints_2596_; uint8_t v___x_2597_; lean_object* v_acc_2598_; lean_object* v___x_2599_; lean_object* v_acc_2600_; lean_object* v___x_2601_; lean_object* v___y_2603_; lean_object* v___x_2615_; uint8_t v___x_2616_; 
v_id_2594_ = lean_ctor_get(v___x_2575_, 0);
v_c_2595_ = lean_ctor_get(v___x_2575_, 1);
v_rupHints_2596_ = lean_ctor_get(v___x_2575_, 2);
v___x_2597_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
v_acc_2598_ = lean_byte_array_push(v_acc_2551_, v___x_2597_);
lean_inc(v_id_2594_);
v___x_2599_ = lean_nat_to_int(v_id_2594_);
v_acc_2600_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2598_, v___x_2599_);
lean_dec(v___x_2599_);
v___x_2601_ = lean_unsigned_to_nat(0u);
v___x_2615_ = lean_array_get_size(v_c_2595_);
v___x_2616_ = lean_nat_dec_lt(v___x_2601_, v___x_2615_);
if (v___x_2616_ == 0)
{
v___y_2603_ = v_acc_2600_;
goto v___jp_2602_;
}
else
{
uint8_t v___x_2617_; 
v___x_2617_ = lean_nat_dec_le(v___x_2615_, v___x_2615_);
if (v___x_2617_ == 0)
{
if (v___x_2616_ == 0)
{
v___y_2603_ = v_acc_2600_;
goto v___jp_2602_;
}
else
{
size_t v___x_2618_; size_t v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = ((size_t)0ULL);
v___x_2619_ = lean_usize_of_nat(v___x_2615_);
v___x_2620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2595_, v___x_2618_, v___x_2619_, v_acc_2600_);
v___y_2603_ = v___x_2620_;
goto v___jp_2602_;
}
}
else
{
size_t v___x_2621_; size_t v___x_2622_; lean_object* v___x_2623_; 
v___x_2621_ = ((size_t)0ULL);
v___x_2622_ = lean_usize_of_nat(v___x_2615_);
v___x_2623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2595_, v___x_2621_, v___x_2622_, v_acc_2600_);
v___y_2603_ = v___x_2623_;
goto v___jp_2602_;
}
}
v___jp_2602_:
{
uint8_t v___x_2604_; lean_object* v_acc_2605_; lean_object* v___x_2606_; uint8_t v___x_2607_; 
v___x_2604_ = 0;
v_acc_2605_ = lean_byte_array_push(v___y_2603_, v___x_2604_);
v___x_2606_ = lean_array_get_size(v_rupHints_2596_);
v___x_2607_ = lean_nat_dec_lt(v___x_2601_, v___x_2606_);
if (v___x_2607_ == 0)
{
v___y_2566_ = v_acc_2605_;
goto v___jp_2565_;
}
else
{
uint8_t v___x_2608_; 
v___x_2608_ = lean_nat_dec_le(v___x_2606_, v___x_2606_);
if (v___x_2608_ == 0)
{
if (v___x_2607_ == 0)
{
v___y_2566_ = v_acc_2605_;
goto v___jp_2565_;
}
else
{
size_t v___x_2609_; size_t v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = ((size_t)0ULL);
v___x_2610_ = lean_usize_of_nat(v___x_2606_);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2596_, v___x_2609_, v___x_2610_, v_acc_2605_);
v___y_2566_ = v___x_2611_;
goto v___jp_2565_;
}
}
else
{
size_t v___x_2612_; size_t v___x_2613_; lean_object* v___x_2614_; 
v___x_2612_ = ((size_t)0ULL);
v___x_2613_ = lean_usize_of_nat(v___x_2606_);
v___x_2614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2596_, v___x_2612_, v___x_2613_, v_acc_2605_);
v___y_2566_ = v___x_2614_;
goto v___jp_2565_;
}
}
}
}
case 2:
{
lean_object* v_id_2624_; lean_object* v_c_2625_; lean_object* v_rupHints_2626_; lean_object* v_ratHints_2627_; uint8_t v___x_2628_; lean_object* v_acc_2629_; lean_object* v___x_2630_; lean_object* v_acc_2631_; lean_object* v___x_2632_; lean_object* v___y_2634_; lean_object* v___y_2645_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v_id_2624_ = lean_ctor_get(v___x_2575_, 0);
v_c_2625_ = lean_ctor_get(v___x_2575_, 1);
v_rupHints_2626_ = lean_ctor_get(v___x_2575_, 3);
v_ratHints_2627_ = lean_ctor_get(v___x_2575_, 4);
v___x_2628_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
v_acc_2629_ = lean_byte_array_push(v_acc_2551_, v___x_2628_);
lean_inc(v_id_2624_);
v___x_2630_ = lean_nat_to_int(v_id_2624_);
v_acc_2631_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2629_, v___x_2630_);
lean_dec(v___x_2630_);
v___x_2632_ = lean_unsigned_to_nat(0u);
v___x_2657_ = lean_array_get_size(v_c_2625_);
v___x_2658_ = lean_nat_dec_lt(v___x_2632_, v___x_2657_);
if (v___x_2658_ == 0)
{
v___y_2645_ = v_acc_2631_;
goto v___jp_2644_;
}
else
{
uint8_t v___x_2659_; 
v___x_2659_ = lean_nat_dec_le(v___x_2657_, v___x_2657_);
if (v___x_2659_ == 0)
{
if (v___x_2658_ == 0)
{
v___y_2645_ = v_acc_2631_;
goto v___jp_2644_;
}
else
{
size_t v___x_2660_; size_t v___x_2661_; lean_object* v___x_2662_; 
v___x_2660_ = ((size_t)0ULL);
v___x_2661_ = lean_usize_of_nat(v___x_2657_);
v___x_2662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2625_, v___x_2660_, v___x_2661_, v_acc_2631_);
v___y_2645_ = v___x_2662_;
goto v___jp_2644_;
}
}
else
{
size_t v___x_2663_; size_t v___x_2664_; lean_object* v___x_2665_; 
v___x_2663_ = ((size_t)0ULL);
v___x_2664_ = lean_usize_of_nat(v___x_2657_);
v___x_2665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2625_, v___x_2663_, v___x_2664_, v_acc_2631_);
v___y_2645_ = v___x_2665_;
goto v___jp_2644_;
}
}
v___jp_2633_:
{
lean_object* v___x_2635_; uint8_t v___x_2636_; 
v___x_2635_ = lean_array_get_size(v_ratHints_2627_);
v___x_2636_ = lean_nat_dec_lt(v___x_2632_, v___x_2635_);
if (v___x_2636_ == 0)
{
v___y_2558_ = v___y_2634_;
goto v___jp_2557_;
}
else
{
uint8_t v___x_2637_; 
v___x_2637_ = lean_nat_dec_le(v___x_2635_, v___x_2635_);
if (v___x_2637_ == 0)
{
if (v___x_2636_ == 0)
{
v___y_2558_ = v___y_2634_;
goto v___jp_2557_;
}
else
{
size_t v___x_2638_; size_t v___x_2639_; lean_object* v___x_2640_; 
v___x_2638_ = ((size_t)0ULL);
v___x_2639_ = lean_usize_of_nat(v___x_2635_);
v___x_2640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_ratHints_2627_, v___x_2638_, v___x_2639_, v___y_2634_);
v___y_2558_ = v___x_2640_;
goto v___jp_2557_;
}
}
else
{
size_t v___x_2641_; size_t v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = ((size_t)0ULL);
v___x_2642_ = lean_usize_of_nat(v___x_2635_);
v___x_2643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_ratHints_2627_, v___x_2641_, v___x_2642_, v___y_2634_);
v___y_2558_ = v___x_2643_;
goto v___jp_2557_;
}
}
}
v___jp_2644_:
{
uint8_t v___x_2646_; lean_object* v_acc_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___x_2646_ = 0;
v_acc_2647_ = lean_byte_array_push(v___y_2645_, v___x_2646_);
v___x_2648_ = lean_array_get_size(v_rupHints_2626_);
v___x_2649_ = lean_nat_dec_lt(v___x_2632_, v___x_2648_);
if (v___x_2649_ == 0)
{
v___y_2634_ = v_acc_2647_;
goto v___jp_2633_;
}
else
{
uint8_t v___x_2650_; 
v___x_2650_ = lean_nat_dec_le(v___x_2648_, v___x_2648_);
if (v___x_2650_ == 0)
{
if (v___x_2649_ == 0)
{
v___y_2634_ = v_acc_2647_;
goto v___jp_2633_;
}
else
{
size_t v___x_2651_; size_t v___x_2652_; lean_object* v___x_2653_; 
v___x_2651_ = ((size_t)0ULL);
v___x_2652_ = lean_usize_of_nat(v___x_2648_);
v___x_2653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2626_, v___x_2651_, v___x_2652_, v_acc_2647_);
v___y_2634_ = v___x_2653_;
goto v___jp_2633_;
}
}
else
{
size_t v___x_2654_; size_t v___x_2655_; lean_object* v___x_2656_; 
v___x_2654_ = ((size_t)0ULL);
v___x_2655_ = lean_usize_of_nat(v___x_2648_);
v___x_2656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2626_, v___x_2654_, v___x_2655_, v_acc_2647_);
v___y_2634_ = v___x_2656_;
goto v___jp_2633_;
}
}
}
}
default: 
{
lean_object* v_ids_2666_; uint8_t v___x_2667_; lean_object* v_acc_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; 
v_ids_2666_ = lean_ctor_get(v___x_2575_, 0);
v___x_2667_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
v_acc_2668_ = lean_byte_array_push(v_acc_2551_, v___x_2667_);
v___x_2669_ = lean_unsigned_to_nat(0u);
v___x_2670_ = lean_array_get_size(v_ids_2666_);
v___x_2671_ = lean_nat_dec_lt(v___x_2669_, v___x_2670_);
if (v___x_2671_ == 0)
{
v___y_2570_ = v_acc_2668_;
goto v___jp_2569_;
}
else
{
uint8_t v___x_2672_; 
v___x_2672_ = lean_nat_dec_le(v___x_2670_, v___x_2670_);
if (v___x_2672_ == 0)
{
if (v___x_2671_ == 0)
{
v___y_2570_ = v_acc_2668_;
goto v___jp_2569_;
}
else
{
size_t v___x_2673_; size_t v___x_2674_; lean_object* v___x_2675_; 
v___x_2673_ = ((size_t)0ULL);
v___x_2674_ = lean_usize_of_nat(v___x_2670_);
v___x_2675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_ids_2666_, v___x_2673_, v___x_2674_, v_acc_2668_);
v___y_2570_ = v___x_2675_;
goto v___jp_2569_;
}
}
else
{
size_t v___x_2676_; size_t v___x_2677_; lean_object* v___x_2678_; 
v___x_2676_ = ((size_t)0ULL);
v___x_2677_ = lean_usize_of_nat(v___x_2670_);
v___x_2678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_ids_2666_, v___x_2676_, v___x_2677_, v_acc_2668_);
v___y_2570_ = v___x_2678_;
goto v___jp_2569_;
}
}
}
}
}
v___jp_2552_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = lean_unsigned_to_nat(1u);
v___x_2555_ = lean_nat_add(v_idx_2550_, v___x_2554_);
lean_dec(v_idx_2550_);
v_idx_2550_ = v___x_2555_;
v_acc_2551_ = v___y_2553_;
goto _start;
}
v___jp_2557_:
{
uint8_t v___x_2559_; lean_object* v_acc_2560_; 
v___x_2559_ = 0;
v_acc_2560_ = lean_byte_array_push(v___y_2558_, v___x_2559_);
v___y_2553_ = v_acc_2560_;
goto v___jp_2552_;
}
v___jp_2561_:
{
uint8_t v___x_2563_; lean_object* v_acc_2564_; 
v___x_2563_ = 0;
v_acc_2564_ = lean_byte_array_push(v___y_2562_, v___x_2563_);
v___y_2553_ = v_acc_2564_;
goto v___jp_2552_;
}
v___jp_2565_:
{
uint8_t v___x_2567_; lean_object* v_acc_2568_; 
v___x_2567_ = 0;
v_acc_2568_ = lean_byte_array_push(v___y_2566_, v___x_2567_);
v___y_2553_ = v_acc_2568_;
goto v___jp_2552_;
}
v___jp_2569_:
{
uint8_t v___x_2571_; lean_object* v_acc_2572_; 
v___x_2571_ = 0;
v_acc_2572_ = lean_byte_array_push(v___y_2570_, v___x_2571_);
v___y_2553_ = v_acc_2572_;
goto v___jp_2552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___boxed(lean_object* v_proof_2679_, lean_object* v_idx_2680_, lean_object* v_acc_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(v_proof_2679_, v_idx_2680_, v_acc_2681_);
lean_dec_ref(v_proof_2679_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(lean_object* v_proof_2683_){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2684_ = lean_unsigned_to_nat(0u);
v___x_2685_ = lean_unsigned_to_nat(4u);
v___x_2686_ = lean_array_get_size(v_proof_2683_);
v___x_2687_ = lean_nat_mul(v___x_2685_, v___x_2686_);
v___x_2688_ = lean_mk_empty_byte_array(v___x_2687_);
lean_dec(v___x_2687_);
v___x_2689_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(v_proof_2683_, v___x_2684_, v___x_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary___boxed(lean_object* v_proof_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(v_proof_2690_);
lean_dec_ref(v_proof_2690_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object* v_path_2692_, lean_object* v_proof_2693_, uint8_t v_binaryProofs_2694_){
_start:
{
if (v_binaryProofs_2694_ == 0)
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2696_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_proof_2693_);
v___x_2697_ = lean_string_to_utf8(v___x_2696_);
lean_dec_ref(v___x_2696_);
v___x_2698_ = l_IO_FS_writeBinFile(v_path_2692_, v___x_2697_);
lean_dec_ref(v___x_2697_);
return v___x_2698_;
}
else
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(v_proof_2693_);
v___x_2700_ = l_IO_FS_writeBinFile(v_path_2692_, v___x_2699_);
lean_dec_ref(v___x_2699_);
return v___x_2700_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof___boxed(lean_object* v_path_2701_, lean_object* v_proof_2702_, lean_object* v_binaryProofs_2703_, lean_object* v_a_2704_){
_start:
{
uint8_t v_binaryProofs_boxed_2705_; lean_object* v_res_2706_; 
v_binaryProofs_boxed_2705_ = lean_unbox(v_binaryProofs_2703_);
v_res_2706_ = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(v_path_2701_, v_proof_2702_, v_binaryProofs_boxed_2705_);
lean_dec_ref(v_proof_2702_);
lean_dec_ref(v_path_2701_);
return v_res_2706_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
