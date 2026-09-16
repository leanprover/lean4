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
lean_object* v_pos_987_; lean_object* v_res_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1096_; 
v_pos_987_ = lean_ctor_get(v___x_986_, 0);
v_res_988_ = lean_ctor_get(v___x_986_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_990_ = v___x_986_;
v_isShared_991_ = v_isSharedCheck_1096_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_res_988_);
lean_inc(v_pos_987_);
lean_dec(v___x_986_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1096_;
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
lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1093_; 
lean_inc(v_idx_993_);
lean_inc_ref(v_array_992_);
lean_del_object(v___x_990_);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_pos_987_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; lean_object* v_unused_1095_; 
v_unused_1094_ = lean_ctor_get(v_pos_987_, 1);
lean_dec(v_unused_1094_);
v_unused_1095_ = lean_ctor_get(v_pos_987_, 0);
lean_dec(v_unused_1095_);
v___x_1008_ = v_pos_987_;
v_isShared_1009_ = v_isSharedCheck_1093_;
goto v_resetjp_1007_;
}
else
{
lean_dec(v_pos_987_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1093_;
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
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_array_992_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1092_;
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
lean_object* v_pos_1020_; lean_object* v_res_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1073_; 
v_pos_1020_ = lean_ctor_get(v___x_1019_, 0);
v_res_1021_ = lean_ctor_get(v___x_1019_, 1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1023_ = v___x_1019_;
v_isShared_1024_ = v_isSharedCheck_1073_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_res_1021_);
lean_inc(v_pos_1020_);
lean_dec(v___x_1019_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1073_;
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
lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1070_; 
lean_inc(v_idx_1026_);
lean_inc_ref(v_array_1025_);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_pos_1020_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; lean_object* v_unused_1072_; 
v_unused_1071_ = lean_ctor_get(v_pos_1020_, 1);
lean_dec(v_unused_1071_);
v_unused_1072_ = lean_ctor_get(v_pos_1020_, 0);
lean_dec(v_unused_1072_);
v___x_1041_ = v_pos_1020_;
v_isShared_1042_ = v_isSharedCheck_1070_;
goto v_resetjp_1040_;
}
else
{
lean_dec(v_pos_1020_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1070_;
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
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_array_1025_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1069_;
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
lean_object* v___x_1055_; lean_object* v___x_1057_; 
lean_dec(v_res_1021_);
v___x_1055_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1055_, 0, v_ident_984_);
lean_ctor_set(v___x_1055_, 1, v_res_988_);
lean_ctor_set(v___x_1055_, 2, v_res_1016_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v___x_1055_);
lean_ctor_set(v___x_1023_, 0, v___x_1045_);
v___x_1057_ = v___x_1023_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
else
{
lean_object* v___x_1059_; uint8_t v___x_1060_; 
lean_dec(v_res_988_);
v___x_1059_ = lean_array_get_size(v_res_1021_);
lean_dec(v_res_1021_);
v___x_1060_ = lean_nat_dec_eq(v___x_1059_, v___x_1017_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
lean_dec(v_res_1016_);
lean_dec(v_ident_984_);
v___x_1061_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2));
if (v_isShared_1024_ == 0)
{
lean_ctor_set_tag(v___x_1023_, 1);
lean_ctor_set(v___x_1023_, 1, v___x_1061_);
lean_ctor_set(v___x_1023_, 0, v___x_1045_);
v___x_1063_ = v___x_1023_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v_ident_984_);
lean_ctor_set(v___x_1065_, 1, v_res_1016_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v___x_1065_);
lean_ctor_set(v___x_1023_, 0, v___x_1045_);
v___x_1067_ = v___x_1023_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
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
lean_object* v_pos_1074_; lean_object* v_err_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec(v_res_1016_);
lean_dec(v_res_988_);
lean_dec(v_ident_984_);
v_pos_1074_ = lean_ctor_get(v___x_1019_, 0);
v_err_1075_ = lean_ctor_get(v___x_1019_, 1);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1019_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_err_1075_);
lean_inc(v_pos_1074_);
lean_dec(v___x_1019_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_pos_1074_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_err_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
else
{
lean_object* v_pos_1083_; lean_object* v_err_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec(v_res_988_);
lean_dec(v_ident_984_);
v_pos_1083_ = lean_ctor_get(v___x_1014_, 0);
v_err_1084_ = lean_ctor_get(v___x_1014_, 1);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1014_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_err_1084_);
lean_inc(v_pos_1083_);
lean_dec(v___x_1014_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_pos_1083_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_err_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
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
lean_object* v_pos_1097_; lean_object* v_err_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec(v_ident_984_);
v_pos_1097_ = lean_ctor_get(v___x_986_, 0);
v_err_1098_ = lean_ctor_get(v___x_986_, 1);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_986_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_err_1098_);
lean_inc(v_pos_1097_);
lean_dec(v___x_986_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_pos_1097_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_err_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(lean_object* v_a_1106_){
_start:
{
lean_object* v_array_1107_; lean_object* v_idx_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v_array_1107_ = lean_ctor_get(v_a_1106_, 0);
v_idx_1108_ = lean_ctor_get(v_a_1106_, 1);
v___x_1109_ = lean_byte_array_size(v_array_1107_);
v___x_1110_ = lean_nat_dec_lt(v_idx_1108_, v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1112_, 0, v_a_1106_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
return v___x_1112_;
}
else
{
uint8_t v_c_1113_; uint8_t v___x_1114_; uint8_t v___y_1116_; uint8_t v___x_1182_; 
v_c_1113_ = lean_byte_array_fget(v_array_1107_, v_idx_1108_);
v___x_1114_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0);
v___x_1182_ = lean_uint8_dec_le(v___x_1114_, v_c_1113_);
if (v___x_1182_ == 0)
{
v___y_1116_ = v___x_1182_;
goto v___jp_1115_;
}
else
{
uint8_t v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5);
v___x_1184_ = lean_uint8_dec_le(v_c_1113_, v___x_1183_);
v___y_1116_ = v___x_1184_;
goto v___jp_1115_;
}
v___jp_1115_:
{
if (v___y_1116_ == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2));
v___x_1118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1118_, 0, v_a_1106_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
return v___x_1118_;
}
else
{
lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1179_; 
lean_inc(v_idx_1108_);
lean_inc_ref(v_array_1107_);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_a_1106_);
if (v_isSharedCheck_1179_ == 0)
{
lean_object* v_unused_1180_; lean_object* v_unused_1181_; 
v_unused_1180_ = lean_ctor_get(v_a_1106_, 1);
lean_dec(v_unused_1180_);
v_unused_1181_ = lean_ctor_get(v_a_1106_, 0);
lean_dec(v_unused_1181_);
v___x_1120_ = v_a_1106_;
v_isShared_1121_ = v_isSharedCheck_1179_;
goto v_resetjp_1119_;
}
else
{
lean_dec(v_a_1106_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1179_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v_it_x27_1125_; 
v___x_1122_ = lean_unsigned_to_nat(1u);
v___x_1123_ = lean_nat_add(v_idx_1108_, v___x_1122_);
lean_dec(v_idx_1108_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 1, v___x_1123_);
v_it_x27_1125_ = v___x_1120_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_array_1107_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v___x_1123_);
v_it_x27_1125_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
uint32_t v___x_1126_; uint8_t v___x_1127_; uint8_t v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v_fst_1131_; lean_object* v_snd_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1177_; 
v___x_1126_ = lean_uint8_to_uint32(v_c_1113_);
v___x_1127_ = lean_uint32_to_uint8(v___x_1126_);
v___x_1128_ = lean_uint8_sub(v___x_1127_, v___x_1114_);
v___x_1129_ = lean_uint8_to_nat(v___x_1128_);
v___x_1130_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_1125_, v___x_1129_);
v_fst_1131_ = lean_ctor_get(v___x_1130_, 0);
v_snd_1132_ = lean_ctor_get(v___x_1130_, 1);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1134_ = v___x_1130_;
v_isShared_1135_ = v_isSharedCheck_1177_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_snd_1132_);
lean_inc(v_fst_1131_);
lean_dec(v___x_1130_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1177_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = lean_unsigned_to_nat(0u);
v___x_1137_ = lean_nat_dec_eq(v_fst_1131_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v_array_1138_; lean_object* v_idx_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v_array_1138_ = lean_ctor_get(v_snd_1132_, 0);
v_idx_1139_ = lean_ctor_get(v_snd_1132_, 1);
v___x_1140_ = lean_byte_array_size(v_array_1138_);
v___x_1141_ = lean_nat_dec_lt(v_idx_1139_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
lean_dec(v_fst_1131_);
v___x_1142_ = lean_box(0);
if (v_isShared_1135_ == 0)
{
lean_ctor_set_tag(v___x_1134_, 1);
lean_ctor_set(v___x_1134_, 1, v___x_1142_);
lean_ctor_set(v___x_1134_, 0, v_snd_1132_);
v___x_1144_ = v___x_1134_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_snd_1132_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
else
{
uint8_t v___x_1146_; uint8_t v_got_1147_; uint8_t v___x_1148_; 
v___x_1146_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
v_got_1147_ = lean_byte_array_fget(v_array_1138_, v_idx_1139_);
v___x_1148_ = lean_uint8_dec_eq(v_got_1147_, v___x_1146_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
lean_dec(v_fst_1131_);
v___x_1149_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
if (v_isShared_1135_ == 0)
{
lean_ctor_set_tag(v___x_1134_, 1);
lean_ctor_set(v___x_1134_, 1, v___x_1149_);
lean_ctor_set(v___x_1134_, 0, v_snd_1132_);
v___x_1151_ = v___x_1134_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_snd_1132_);
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
lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1170_; 
lean_inc(v_idx_1139_);
lean_inc_ref(v_array_1138_);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_snd_1132_);
if (v_isSharedCheck_1170_ == 0)
{
lean_object* v_unused_1171_; lean_object* v_unused_1172_; 
v_unused_1171_ = lean_ctor_get(v_snd_1132_, 1);
lean_dec(v_unused_1171_);
v_unused_1172_ = lean_ctor_get(v_snd_1132_, 0);
lean_dec(v_unused_1172_);
v___x_1154_ = v_snd_1132_;
v_isShared_1155_ = v_isSharedCheck_1170_;
goto v_resetjp_1153_;
}
else
{
lean_dec(v_snd_1132_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1170_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1156_ = lean_nat_add(v_idx_1139_, v___x_1122_);
lean_dec(v_idx_1139_);
lean_inc(v___x_1156_);
lean_inc_ref(v_array_1138_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v___x_1156_);
v___x_1158_ = v___x_1154_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_array_1138_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
uint8_t v___x_1159_; 
v___x_1159_ = lean_nat_dec_lt(v___x_1156_, v___x_1140_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1162_; 
lean_dec(v___x_1156_);
lean_dec_ref(v_array_1138_);
lean_dec(v_fst_1131_);
v___x_1160_ = lean_box(0);
if (v_isShared_1135_ == 0)
{
lean_ctor_set_tag(v___x_1134_, 1);
lean_ctor_set(v___x_1134_, 1, v___x_1160_);
lean_ctor_set(v___x_1134_, 0, v___x_1158_);
v___x_1162_ = v___x_1134_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
else
{
uint8_t v___x_1164_; uint8_t v___x_1165_; uint8_t v___x_1166_; 
lean_del_object(v___x_1134_);
v___x_1164_ = lean_byte_array_fget(v_array_1138_, v___x_1156_);
lean_dec(v___x_1156_);
lean_dec_ref(v_array_1138_);
v___x_1165_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
v___x_1166_ = lean_uint8_dec_eq(v___x_1164_, v___x_1165_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(v_fst_1131_, v___x_1158_);
return v___x_1167_;
}
else
{
lean_object* v___x_1168_; 
lean_dec(v_fst_1131_);
v___x_1168_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(v___x_1158_);
return v___x_1168_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1175_; 
lean_dec(v_fst_1131_);
v___x_1173_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__4));
if (v_isShared_1135_ == 0)
{
lean_ctor_set_tag(v___x_1134_, 1);
lean_ctor_set(v___x_1134_, 1, v___x_1173_);
lean_ctor_set(v___x_1134_, 0, v_snd_1132_);
v___x_1175_ = v___x_1134_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_snd_1132_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
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
uint32_t v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = 13;
v___x_1189_ = lean_uint32_to_uint8(v___x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(lean_object* v_acc_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v_array_1192_; lean_object* v_idx_1193_; lean_object* v_pos_1195_; lean_object* v_idx_1196_; lean_object* v_err_1197_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v_array_1192_ = lean_ctor_get(v_a_1191_, 0);
v_idx_1193_ = lean_ctor_get(v_a_1191_, 1);
lean_inc(v_idx_1193_);
v___x_1203_ = lean_byte_array_size(v_array_1192_);
v___x_1204_ = lean_nat_dec_lt(v_idx_1193_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_box(0);
lean_inc(v_idx_1193_);
v_pos_1195_ = v_a_1191_;
v_idx_1196_ = v_idx_1193_;
v_err_1197_ = v___x_1205_;
goto v___jp_1194_;
}
else
{
uint8_t v_c_1206_; uint8_t v___x_1207_; uint8_t v___x_1208_; 
v_c_1206_ = lean_byte_array_fget(v_array_1192_, v_idx_1193_);
v___x_1207_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2);
v___x_1208_ = lean_uint8_dec_eq(v_c_1206_, v___x_1207_);
if (v___x_1208_ == 0)
{
uint8_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = lean_uint8_once(&l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2, &l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2_once, _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2);
v___x_1210_ = lean_uint8_dec_eq(v_c_1206_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1222_; 
lean_inc_ref(v_array_1192_);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_a_1191_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; lean_object* v_unused_1224_; 
v_unused_1223_ = lean_ctor_get(v_a_1191_, 1);
lean_dec(v_unused_1223_);
v_unused_1224_ = lean_ctor_get(v_a_1191_, 0);
lean_dec(v_unused_1224_);
v___x_1212_ = v_a_1191_;
v_isShared_1213_ = v_isSharedCheck_1222_;
goto v_resetjp_1211_;
}
else
{
lean_dec(v_a_1191_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1222_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v_it_x27_1217_; 
v___x_1214_ = lean_unsigned_to_nat(1u);
v___x_1215_ = lean_nat_add(v_idx_1193_, v___x_1214_);
lean_dec(v_idx_1193_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 1, v___x_1215_);
v_it_x27_1217_ = v___x_1212_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_array_1192_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v___x_1215_);
v_it_x27_1217_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_box(v_c_1206_);
v___x_1219_ = lean_array_push(v_acc_1190_, v___x_1218_);
v_acc_1190_ = v___x_1219_;
v_a_1191_ = v_it_x27_1217_;
goto _start;
}
}
}
else
{
goto v___jp_1201_;
}
}
else
{
goto v___jp_1201_;
}
}
v___jp_1194_:
{
uint8_t v___x_1198_; 
v___x_1198_ = lean_nat_dec_eq(v_idx_1193_, v_idx_1196_);
lean_dec(v_idx_1196_);
lean_dec(v_idx_1193_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; 
lean_dec_ref(v_acc_1190_);
lean_inc(v_err_1197_);
v___x_1199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1199_, 0, v_pos_1195_);
lean_ctor_set(v___x_1199_, 1, v_err_1197_);
return v___x_1199_;
}
else
{
lean_object* v___x_1200_; 
v___x_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1200_, 0, v_pos_1195_);
lean_ctor_set(v___x_1200_, 1, v_acc_1190_);
return v___x_1200_;
}
}
v___jp_1201_:
{
lean_object* v___x_1202_; 
v___x_1202_ = ((lean_object*)(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__1));
lean_inc(v_idx_1193_);
v_pos_1195_ = v_a_1191_;
v_idx_1196_ = v_idx_1193_;
v_err_1197_ = v___x_1202_;
goto v___jp_1194_;
}
}
}
static uint8_t _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0(void){
_start:
{
uint32_t v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = 99;
v___x_1226_ = lean_uint32_to_uint8(v___x_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(lean_object* v_actions_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_pos_1232_; lean_object* v_array_1233_; lean_object* v_idx_1234_; lean_object* v_pos_1240_; lean_object* v___y_1244_; lean_object* v_array_1255_; lean_object* v_idx_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v_array_1255_ = lean_ctor_get(v_a_1230_, 0);
v_idx_1256_ = lean_ctor_get(v_a_1230_, 1);
v___x_1257_ = lean_byte_array_size(v_array_1255_);
v___x_1258_ = lean_nat_dec_lt(v_idx_1256_, v___x_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec_ref(v_actions_1229_);
v___x_1259_ = lean_box(0);
v___x_1260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1260_, 0, v_a_1230_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
return v___x_1260_;
}
else
{
uint8_t v___x_1261_; uint8_t v___x_1262_; uint8_t v___x_1263_; 
v___x_1261_ = lean_byte_array_fget(v_array_1255_, v_idx_1256_);
v___x_1262_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0);
v___x_1263_ = lean_uint8_dec_eq(v___x_1261_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(v_a_1230_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_pos_1265_; lean_object* v_res_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1327_; 
v_pos_1265_ = lean_ctor_get(v___x_1264_, 0);
v_res_1266_ = lean_ctor_get(v___x_1264_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1268_ = v___x_1264_;
v_isShared_1269_ = v_isSharedCheck_1327_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_res_1266_);
lean_inc(v_pos_1265_);
lean_dec(v___x_1264_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1327_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v_pos_1271_; lean_object* v_array_1272_; lean_object* v_idx_1273_; lean_object* v_pos_1282_; lean_object* v___y_1286_; lean_object* v_array_1297_; lean_object* v_idx_1298_; lean_object* v___y_1300_; lean_object* v_pos_1301_; lean_object* v_idx_1302_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v_array_1297_ = lean_ctor_get(v_pos_1265_, 0);
v_idx_1298_ = lean_ctor_get(v_pos_1265_, 1);
lean_inc(v_idx_1298_);
v___x_1307_ = lean_byte_array_size(v_array_1297_);
v___x_1308_ = lean_nat_dec_lt(v_idx_1298_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_box(0);
lean_inc(v_pos_1265_);
v___x_1310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1310_, 0, v_pos_1265_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
lean_inc(v_idx_1298_);
v___y_1300_ = v___x_1310_;
v_pos_1301_ = v_pos_1265_;
v_idx_1302_ = v_idx_1298_;
goto v___jp_1299_;
}
else
{
uint8_t v___x_1311_; uint8_t v_got_1312_; uint8_t v___x_1313_; 
v___x_1311_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2);
v_got_1312_ = lean_byte_array_fget(v_array_1297_, v_idx_1298_);
v___x_1313_ = lean_uint8_dec_eq(v_got_1312_, v___x_1311_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9);
lean_inc(v_pos_1265_);
v___x_1315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1315_, 0, v_pos_1265_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
lean_inc(v_idx_1298_);
v___y_1300_ = v___x_1315_;
v_pos_1301_ = v_pos_1265_;
v_idx_1302_ = v_idx_1298_;
goto v___jp_1299_;
}
else
{
lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1324_; 
lean_inc_ref(v_array_1297_);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_pos_1265_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; lean_object* v_unused_1326_; 
v_unused_1325_ = lean_ctor_get(v_pos_1265_, 1);
lean_dec(v_unused_1325_);
v_unused_1326_ = lean_ctor_get(v_pos_1265_, 0);
lean_dec(v_unused_1326_);
v___x_1317_ = v_pos_1265_;
v_isShared_1318_ = v_isSharedCheck_1324_;
goto v_resetjp_1316_;
}
else
{
lean_dec(v_pos_1265_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1324_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1319_ = lean_unsigned_to_nat(1u);
v___x_1320_ = lean_nat_add(v_idx_1298_, v___x_1319_);
lean_dec(v_idx_1298_);
lean_inc(v___x_1320_);
lean_inc_ref(v_array_1297_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 1, v___x_1320_);
v___x_1322_ = v___x_1317_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_array_1297_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
v_pos_1271_ = v___x_1322_;
v_array_1272_ = v_array_1297_;
v_idx_1273_ = v___x_1320_;
goto v___jp_1270_;
}
}
}
}
v___jp_1270_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1274_ = lean_array_push(v_actions_1229_, v_res_1266_);
v___x_1275_ = lean_byte_array_size(v_array_1272_);
lean_dec_ref(v_array_1272_);
v___x_1276_ = lean_nat_dec_lt(v_idx_1273_, v___x_1275_);
lean_dec(v_idx_1273_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1278_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 1, v___x_1274_);
lean_ctor_set(v___x_1268_, 0, v_pos_1271_);
v___x_1278_ = v___x_1268_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_pos_1271_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v___x_1274_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
else
{
lean_del_object(v___x_1268_);
v_actions_1229_ = v___x_1274_;
v_a_1230_ = v_pos_1271_;
goto _start;
}
}
v___jp_1281_:
{
lean_object* v_array_1283_; lean_object* v_idx_1284_; 
v_array_1283_ = lean_ctor_get(v_pos_1282_, 0);
lean_inc_ref(v_array_1283_);
v_idx_1284_ = lean_ctor_get(v_pos_1282_, 1);
lean_inc(v_idx_1284_);
v_pos_1271_ = v_pos_1282_;
v_array_1272_ = v_array_1283_;
v_idx_1273_ = v_idx_1284_;
goto v___jp_1270_;
}
v___jp_1285_:
{
if (lean_obj_tag(v___y_1286_) == 0)
{
lean_object* v_pos_1287_; 
v_pos_1287_ = lean_ctor_get(v___y_1286_, 0);
lean_inc(v_pos_1287_);
lean_dec_ref_known(v___y_1286_, 2);
v_pos_1282_ = v_pos_1287_;
goto v___jp_1281_;
}
else
{
lean_object* v_pos_1288_; lean_object* v_err_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_del_object(v___x_1268_);
lean_dec(v_res_1266_);
lean_dec_ref(v_actions_1229_);
v_pos_1288_ = lean_ctor_get(v___y_1286_, 0);
v_err_1289_ = lean_ctor_get(v___y_1286_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___y_1286_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___y_1286_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_err_1289_);
lean_inc(v_pos_1288_);
lean_dec(v___y_1286_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_pos_1288_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_err_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
v___jp_1299_:
{
uint8_t v___x_1303_; 
v___x_1303_ = lean_nat_dec_eq(v_idx_1298_, v_idx_1302_);
lean_dec(v_idx_1302_);
lean_dec(v_idx_1298_);
if (v___x_1303_ == 0)
{
lean_dec_ref(v_pos_1301_);
v___y_1286_ = v___y_1300_;
goto v___jp_1285_;
}
else
{
lean_object* v_utf8_1304_; lean_object* v___x_1305_; 
lean_dec_ref(v___y_1300_);
v_utf8_1304_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1);
v___x_1305_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1304_, v_pos_1301_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_pos_1306_; 
v_pos_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_pos_1306_);
lean_dec_ref_known(v___x_1305_, 2);
v_pos_1282_ = v_pos_1306_;
goto v___jp_1281_;
}
else
{
v___y_1286_ = v___x_1305_;
goto v___jp_1285_;
}
}
}
}
}
else
{
lean_object* v_pos_1328_; lean_object* v_err_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec_ref(v_actions_1229_);
v_pos_1328_ = lean_ctor_get(v___x_1264_, 0);
v_err_1329_ = lean_ctor_get(v___x_1264_, 1);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1264_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_err_1329_);
lean_inc(v_pos_1328_);
lean_dec(v___x_1264_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_pos_1328_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_err_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__1));
v___x_1338_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(v___x_1337_, v_a_1230_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_pos_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1377_; 
v_pos_1339_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1377_ == 0)
{
lean_object* v_unused_1378_; 
v_unused_1378_ = lean_ctor_get(v___x_1338_, 1);
lean_dec(v_unused_1378_);
v___x_1341_ = v___x_1338_;
v_isShared_1342_ = v_isSharedCheck_1377_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_pos_1339_);
lean_dec(v___x_1338_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1377_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v_array_1343_; lean_object* v_idx_1344_; lean_object* v___y_1346_; lean_object* v_pos_1347_; lean_object* v_idx_1348_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v_array_1343_ = lean_ctor_get(v_pos_1339_, 0);
v_idx_1344_ = lean_ctor_get(v_pos_1339_, 1);
lean_inc(v_idx_1344_);
v___x_1353_ = lean_byte_array_size(v_array_1343_);
v___x_1354_ = lean_nat_dec_lt(v_idx_1344_, v___x_1353_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1355_ = lean_box(0);
lean_inc(v_pos_1339_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set_tag(v___x_1341_, 1);
lean_ctor_set(v___x_1341_, 1, v___x_1355_);
v___x_1357_ = v___x_1341_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_pos_1339_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_inc(v_idx_1344_);
v___y_1346_ = v___x_1357_;
v_pos_1347_ = v_pos_1339_;
v_idx_1348_ = v_idx_1344_;
goto v___jp_1345_;
}
}
else
{
uint8_t v___x_1359_; uint8_t v_got_1360_; uint8_t v___x_1361_; 
v___x_1359_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2);
v_got_1360_ = lean_byte_array_fget(v_array_1343_, v_idx_1344_);
v___x_1361_ = lean_uint8_dec_eq(v_got_1360_, v___x_1359_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1362_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9);
lean_inc(v_pos_1339_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set_tag(v___x_1341_, 1);
lean_ctor_set(v___x_1341_, 1, v___x_1362_);
v___x_1364_ = v___x_1341_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_pos_1339_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_inc(v_idx_1344_);
v___y_1346_ = v___x_1364_;
v_pos_1347_ = v_pos_1339_;
v_idx_1348_ = v_idx_1344_;
goto v___jp_1345_;
}
}
else
{
lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1374_; 
lean_inc_ref(v_array_1343_);
lean_del_object(v___x_1341_);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_pos_1339_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; lean_object* v_unused_1376_; 
v_unused_1375_ = lean_ctor_get(v_pos_1339_, 1);
lean_dec(v_unused_1375_);
v_unused_1376_ = lean_ctor_get(v_pos_1339_, 0);
lean_dec(v_unused_1376_);
v___x_1367_ = v_pos_1339_;
v_isShared_1368_ = v_isSharedCheck_1374_;
goto v_resetjp_1366_;
}
else
{
lean_dec(v_pos_1339_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1374_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1369_ = lean_unsigned_to_nat(1u);
v___x_1370_ = lean_nat_add(v_idx_1344_, v___x_1369_);
lean_dec(v_idx_1344_);
lean_inc(v___x_1370_);
lean_inc_ref(v_array_1343_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 1, v___x_1370_);
v___x_1372_ = v___x_1367_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_array_1343_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
v_pos_1232_ = v___x_1372_;
v_array_1233_ = v_array_1343_;
v_idx_1234_ = v___x_1370_;
goto v___jp_1231_;
}
}
}
}
v___jp_1345_:
{
uint8_t v___x_1349_; 
v___x_1349_ = lean_nat_dec_eq(v_idx_1344_, v_idx_1348_);
lean_dec(v_idx_1348_);
lean_dec(v_idx_1344_);
if (v___x_1349_ == 0)
{
lean_dec_ref(v_pos_1347_);
v___y_1244_ = v___y_1346_;
goto v___jp_1243_;
}
else
{
lean_object* v_utf8_1350_; lean_object* v___x_1351_; 
lean_dec_ref(v___y_1346_);
v_utf8_1350_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1);
v___x_1351_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1350_, v_pos_1347_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_pos_1352_; 
v_pos_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_pos_1352_);
lean_dec_ref_known(v___x_1351_, 2);
v_pos_1240_ = v_pos_1352_;
goto v___jp_1239_;
}
else
{
v___y_1244_ = v___x_1351_;
goto v___jp_1243_;
}
}
}
}
}
else
{
lean_object* v_pos_1379_; lean_object* v_err_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec_ref(v_actions_1229_);
v_pos_1379_ = lean_ctor_get(v___x_1338_, 0);
v_err_1380_ = lean_ctor_get(v___x_1338_, 1);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1338_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_err_1380_);
lean_inc(v_pos_1379_);
lean_dec(v___x_1338_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_pos_1379_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_err_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
v___jp_1231_:
{
lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = lean_byte_array_size(v_array_1233_);
lean_dec_ref(v_array_1233_);
v___x_1236_ = lean_nat_dec_lt(v_idx_1234_, v___x_1235_);
lean_dec(v_idx_1234_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; 
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_pos_1232_);
lean_ctor_set(v___x_1237_, 1, v_actions_1229_);
return v___x_1237_;
}
else
{
v_a_1230_ = v_pos_1232_;
goto _start;
}
}
v___jp_1239_:
{
lean_object* v_array_1241_; lean_object* v_idx_1242_; 
v_array_1241_ = lean_ctor_get(v_pos_1240_, 0);
lean_inc_ref(v_array_1241_);
v_idx_1242_ = lean_ctor_get(v_pos_1240_, 1);
lean_inc(v_idx_1242_);
v_pos_1232_ = v_pos_1240_;
v_array_1233_ = v_array_1241_;
v_idx_1234_ = v_idx_1242_;
goto v___jp_1231_;
}
v___jp_1243_:
{
if (lean_obj_tag(v___y_1244_) == 0)
{
lean_object* v_pos_1245_; 
v_pos_1245_ = lean_ctor_get(v___y_1244_, 0);
lean_inc(v_pos_1245_);
lean_dec_ref_known(v___y_1244_, 2);
v_pos_1240_ = v_pos_1245_;
goto v___jp_1239_;
}
else
{
lean_object* v_pos_1246_; lean_object* v_err_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
lean_dec_ref(v_actions_1229_);
v_pos_1246_ = lean_ctor_get(v___y_1244_, 0);
v_err_1247_ = lean_ctor_get(v___y_1244_, 1);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___y_1244_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___y_1244_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_err_1247_);
lean_inc(v_pos_1246_);
lean_dec(v___y_1244_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_pos_1246_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_err_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(lean_object* v_a_1390_){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0));
v___x_1392_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(v___x_1391_, v_a_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero(lean_object* v_a_1396_){
_start:
{
lean_object* v_array_1397_; lean_object* v_idx_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v_array_1397_ = lean_ctor_get(v_a_1396_, 0);
v_idx_1398_ = lean_ctor_get(v_a_1396_, 1);
v___x_1399_ = lean_byte_array_size(v_array_1397_);
v___x_1400_ = lean_nat_dec_lt(v_idx_1398_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = lean_box(0);
v___x_1402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_a_1396_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
return v___x_1402_;
}
else
{
uint8_t v___x_1403_; uint8_t v_got_1404_; uint8_t v___x_1405_; 
v___x_1403_ = 0;
v_got_1404_ = lean_byte_array_fget(v_array_1397_, v_idx_1398_);
v___x_1405_ = lean_uint8_dec_eq(v_got_1404_, v___x_1403_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
v___x_1407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1407_, 0, v_a_1396_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
return v___x_1407_;
}
else
{
lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1418_; 
lean_inc(v_idx_1398_);
lean_inc_ref(v_array_1397_);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_a_1396_);
if (v_isSharedCheck_1418_ == 0)
{
lean_object* v_unused_1419_; lean_object* v_unused_1420_; 
v_unused_1419_ = lean_ctor_get(v_a_1396_, 1);
lean_dec(v_unused_1419_);
v_unused_1420_ = lean_ctor_get(v_a_1396_, 0);
lean_dec(v_unused_1420_);
v___x_1409_ = v_a_1396_;
v_isShared_1410_ = v_isSharedCheck_1418_;
goto v_resetjp_1408_;
}
else
{
lean_dec(v_a_1396_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1418_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1411_ = lean_unsigned_to_nat(1u);
v___x_1412_ = lean_nat_add(v_idx_1398_, v___x_1411_);
lean_dec(v_idx_1398_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 1, v___x_1412_);
v___x_1414_ = v___x_1409_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_array_1397_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = lean_box(0);
v___x_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
return v___x_1416_;
}
}
}
}
}
}
static uint8_t _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2(void){
_start:
{
uint8_t v___x_1424_; uint8_t v___x_1425_; 
v___x_1424_ = 15;
v___x_1425_ = lean_uint8_complement(v___x_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(uint64_t v_uidx_1429_, uint64_t v_shift_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v_array_1432_; lean_object* v_idx_1433_; lean_object* v___x_1434_; uint8_t v___x_1435_; 
v_array_1432_ = lean_ctor_get(v_a_1431_, 0);
v_idx_1433_ = lean_ctor_get(v_a_1431_, 1);
v___x_1434_ = lean_byte_array_size(v_array_1432_);
v___x_1435_ = lean_nat_dec_lt(v_idx_1433_, v___x_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = lean_box(0);
v___x_1437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1437_, 0, v_a_1431_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
return v___x_1437_;
}
else
{
lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1483_; 
lean_inc(v_idx_1433_);
lean_inc_ref(v_array_1432_);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_a_1431_);
if (v_isSharedCheck_1483_ == 0)
{
lean_object* v_unused_1484_; lean_object* v_unused_1485_; 
v_unused_1484_ = lean_ctor_get(v_a_1431_, 1);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v_a_1431_, 0);
lean_dec(v_unused_1485_);
v___x_1439_ = v_a_1431_;
v_isShared_1440_ = v_isSharedCheck_1483_;
goto v_resetjp_1438_;
}
else
{
lean_dec(v_a_1431_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1483_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
uint8_t v_c_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v_it_x27_1445_; 
v_c_1441_ = lean_byte_array_fget(v_array_1432_, v_idx_1433_);
v___x_1442_ = lean_unsigned_to_nat(1u);
v___x_1443_ = lean_nat_add(v_idx_1433_, v___x_1442_);
lean_dec(v_idx_1433_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v___x_1443_);
v_it_x27_1445_ = v___x_1439_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_array_1432_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___x_1443_);
v_it_x27_1445_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
uint64_t v___x_1474_; uint8_t v___x_1475_; 
v___x_1474_ = 28ULL;
v___x_1475_ = lean_uint64_dec_eq(v_shift_1430_, v___x_1474_);
if (v___x_1475_ == 0)
{
goto v___jp_1446_;
}
else
{
uint8_t v___x_1476_; uint8_t v___x_1477_; uint8_t v___x_1478_; uint8_t v___x_1479_; 
v___x_1476_ = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2);
v___x_1477_ = lean_uint8_land(v_c_1441_, v___x_1476_);
v___x_1478_ = 0;
v___x_1479_ = lean_uint8_dec_eq(v___x_1477_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4));
v___x_1481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1481_, 0, v_it_x27_1445_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
return v___x_1481_;
}
else
{
goto v___jp_1446_;
}
}
v___jp_1446_:
{
uint8_t v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = 0;
v___x_1448_ = lean_uint8_dec_eq(v_c_1441_, v___x_1447_);
if (v___x_1448_ == 0)
{
uint8_t v___x_1449_; uint8_t v___x_1450_; uint64_t v___x_1451_; uint64_t v___x_1452_; uint64_t v___x_1453_; uint8_t v___x_1454_; uint8_t v___x_1455_; uint8_t v___x_1456_; 
v___x_1449_ = 127;
v___x_1450_ = lean_uint8_land(v_c_1441_, v___x_1449_);
v___x_1451_ = lean_uint8_to_uint64(v___x_1450_);
v___x_1452_ = lean_uint64_shift_left(v___x_1451_, v_shift_1430_);
v___x_1453_ = lean_uint64_lor(v_uidx_1429_, v___x_1452_);
v___x_1454_ = 128;
v___x_1455_ = lean_uint8_land(v_c_1441_, v___x_1454_);
v___x_1456_ = lean_uint8_dec_eq(v___x_1455_, v___x_1447_);
if (v___x_1456_ == 0)
{
uint64_t v___x_1457_; uint64_t v___x_1458_; 
v___x_1457_ = 7ULL;
v___x_1458_ = lean_uint64_add(v_shift_1430_, v___x_1457_);
v_uidx_1429_ = v___x_1453_;
v_shift_1430_ = v___x_1458_;
v_a_1431_ = v_it_x27_1445_;
goto _start;
}
else
{
uint64_t v___x_1460_; uint64_t v___x_1461_; uint64_t v___x_1462_; uint64_t v___x_1463_; uint8_t v___x_1464_; 
v___x_1460_ = 1ULL;
v___x_1461_ = lean_uint64_shift_right(v___x_1453_, v___x_1460_);
v___x_1462_ = lean_uint64_land(v___x_1460_, v___x_1453_);
v___x_1463_ = 0ULL;
v___x_1464_ = lean_uint64_dec_eq(v___x_1462_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1465_ = lean_uint64_to_nat(v___x_1461_);
v___x_1466_ = lean_nat_to_int(v___x_1465_);
v___x_1467_ = lean_int_neg(v___x_1466_);
lean_dec(v___x_1466_);
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v_it_x27_1445_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
return v___x_1468_;
}
else
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1469_ = lean_uint64_to_nat(v___x_1461_);
v___x_1470_ = lean_nat_to_int(v___x_1469_);
v___x_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1471_, 0, v_it_x27_1445_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
return v___x_1471_;
}
}
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1));
v___x_1473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1473_, 0, v_it_x27_1445_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
return v___x_1473_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___boxed(lean_object* v_uidx_1486_, lean_object* v_shift_1487_, lean_object* v_a_1488_){
_start:
{
uint64_t v_uidx_boxed_1489_; uint64_t v_shift_boxed_1490_; lean_object* v_res_1491_; 
v_uidx_boxed_1489_ = lean_unbox_uint64(v_uidx_1486_);
lean_dec_ref(v_uidx_1486_);
v_shift_boxed_1490_ = lean_unbox_uint64(v_shift_1487_);
lean_dec_ref(v_shift_1487_);
v_res_1491_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(v_uidx_boxed_1489_, v_shift_boxed_1490_, v_a_1488_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(lean_object* v_a_1492_){
_start:
{
uint64_t v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = 0ULL;
v___x_1494_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(v___x_1493_, v___x_1493_, v_a_1492_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg(lean_object* v_a_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1498_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_pos_1500_; lean_object* v_res_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1515_; 
v_pos_1500_ = lean_ctor_get(v___x_1499_, 0);
v_res_1501_ = lean_ctor_get(v___x_1499_, 1);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1503_ = v___x_1499_;
v_isShared_1504_ = v_isSharedCheck_1515_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_res_1501_);
lean_inc(v_pos_1500_);
lean_dec(v___x_1499_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1515_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1505_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1506_ = lean_int_dec_lt(v_res_1501_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; lean_object* v___x_1509_; 
lean_dec(v_res_1501_);
v___x_1507_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1));
if (v_isShared_1504_ == 0)
{
lean_ctor_set_tag(v___x_1503_, 1);
lean_ctor_set(v___x_1503_, 1, v___x_1507_);
v___x_1509_ = v___x_1503_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_pos_1500_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
else
{
lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1511_ = lean_nat_abs(v_res_1501_);
lean_dec(v_res_1501_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 1, v___x_1511_);
v___x_1513_ = v___x_1503_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_pos_1500_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
else
{
lean_object* v_pos_1516_; lean_object* v_err_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
v_pos_1516_ = lean_ctor_get(v___x_1499_, 0);
v_err_1517_ = lean_ctor_get(v___x_1499_, 1);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1499_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_err_1517_);
lean_inc(v_pos_1516_);
lean_dec(v___x_1499_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_pos_1516_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_err_1517_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos(lean_object* v_a_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1528_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_pos_1530_; lean_object* v_res_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1545_; 
v_pos_1530_ = lean_ctor_get(v___x_1529_, 0);
v_res_1531_ = lean_ctor_get(v___x_1529_, 1);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1533_ = v___x_1529_;
v_isShared_1534_ = v_isSharedCheck_1545_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_res_1531_);
lean_inc(v_pos_1530_);
lean_dec(v___x_1529_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1545_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1535_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1536_ = lean_int_dec_lt(v___x_1535_, v_res_1531_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1539_; 
lean_dec(v_res_1531_);
v___x_1537_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1534_ == 0)
{
lean_ctor_set_tag(v___x_1533_, 1);
lean_ctor_set(v___x_1533_, 1, v___x_1537_);
v___x_1539_ = v___x_1533_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_pos_1530_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1541_ = lean_nat_abs(v_res_1531_);
lean_dec(v_res_1531_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 1, v___x_1541_);
v___x_1543_ = v___x_1533_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_pos_1530_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
else
{
lean_object* v_pos_1546_; lean_object* v_err_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
v_pos_1546_ = lean_ctor_get(v___x_1529_, 0);
v_err_1547_ = lean_ctor_get(v___x_1529_, 1);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1529_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_err_1547_);
lean_inc(v_pos_1546_);
lean_dec(v___x_1529_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_pos_1546_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_err_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId(lean_object* v_a_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1555_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_pos_1557_; lean_object* v_res_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1572_; 
v_pos_1557_ = lean_ctor_get(v___x_1556_, 0);
v_res_1558_ = lean_ctor_get(v___x_1556_, 1);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1560_ = v___x_1556_;
v_isShared_1561_ = v_isSharedCheck_1572_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_res_1558_);
lean_inc(v_pos_1557_);
lean_dec(v___x_1556_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1572_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; uint8_t v___x_1563_; 
v___x_1562_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1563_ = lean_int_dec_lt(v___x_1562_, v_res_1558_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; lean_object* v___x_1566_; 
lean_dec(v_res_1558_);
v___x_1564_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1561_ == 0)
{
lean_ctor_set_tag(v___x_1560_, 1);
lean_ctor_set(v___x_1560_, 1, v___x_1564_);
v___x_1566_ = v___x_1560_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_pos_1557_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1568_ = lean_nat_abs(v_res_1558_);
lean_dec(v_res_1558_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 1, v___x_1568_);
v___x_1570_ = v___x_1560_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_pos_1557_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
else
{
lean_object* v_pos_1573_; lean_object* v_err_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
v_pos_1573_ = lean_ctor_get(v___x_1556_, 0);
v_err_1574_ = lean_ctor_get(v___x_1556_, 1);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1556_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_err_1574_);
lean_inc(v_pos_1573_);
lean_dec(v___x_1556_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_pos_1573_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_err_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(lean_object* v_parser_1582_, lean_object* v_acc_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_array_1585_; lean_object* v_idx_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v_array_1585_ = lean_ctor_get(v_a_1584_, 0);
v_idx_1586_ = lean_ctor_get(v_a_1584_, 1);
v___x_1587_ = lean_byte_array_size(v_array_1585_);
v___x_1588_ = lean_nat_dec_lt(v_idx_1586_, v___x_1587_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec_ref(v_acc_1583_);
lean_dec_ref(v_parser_1582_);
v___x_1589_ = lean_box(0);
v___x_1590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1590_, 0, v_a_1584_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
return v___x_1590_;
}
else
{
uint8_t v___x_1591_; uint8_t v___x_1592_; uint8_t v___x_1593_; 
v___x_1591_ = lean_byte_array_fget(v_array_1585_, v_idx_1586_);
v___x_1592_ = 0;
v___x_1593_ = lean_uint8_dec_eq(v___x_1591_, v___x_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; 
lean_inc_ref(v_parser_1582_);
v___x_1594_ = lean_apply_1(v_parser_1582_, v_a_1584_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_pos_1595_; lean_object* v_res_1596_; lean_object* v___x_1597_; 
v_pos_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_pos_1595_);
v_res_1596_ = lean_ctor_get(v___x_1594_, 1);
lean_inc(v_res_1596_);
lean_dec_ref_known(v___x_1594_, 2);
v___x_1597_ = lean_array_push(v_acc_1583_, v_res_1596_);
v_acc_1583_ = v___x_1597_;
v_a_1584_ = v_pos_1595_;
goto _start;
}
else
{
lean_object* v_pos_1599_; lean_object* v_err_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec_ref(v_acc_1583_);
lean_dec_ref(v_parser_1582_);
v_pos_1599_ = lean_ctor_get(v___x_1594_, 0);
v_err_1600_ = lean_ctor_get(v___x_1594_, 1);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1594_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_err_1600_);
lean_inc(v_pos_1599_);
lean_dec(v___x_1594_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_pos_1599_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_err_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
else
{
lean_object* v___x_1608_; 
lean_dec_ref(v_parser_1582_);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v_a_1584_);
lean_ctor_set(v___x_1608_, 1, v_acc_1583_);
return v___x_1608_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go(lean_object* v_00_u03b1_1609_, lean_object* v_parser_1610_, lean_object* v_acc_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(v_parser_1610_, v_acc_1611_, v_a_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(lean_object* v_parser_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0));
v___x_1619_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(v_parser_1616_, v___x_1618_, v_a_1617_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero(lean_object* v_00_u03b1_1620_, lean_object* v_parser_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v_parser_1621_, v_a_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(lean_object* v_parser_1624_, lean_object* v_acc_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v_array_1627_; lean_object* v_idx_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
v_array_1627_ = lean_ctor_get(v_a_1626_, 0);
v_idx_1628_ = lean_ctor_get(v_a_1626_, 1);
v___x_1629_ = lean_byte_array_size(v_array_1627_);
v___x_1630_ = lean_nat_dec_lt(v_idx_1628_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
lean_dec_ref(v_acc_1625_);
lean_dec_ref(v_parser_1624_);
v___x_1631_ = lean_box(0);
v___x_1632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1632_, 0, v_a_1626_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
return v___x_1632_;
}
else
{
uint8_t v___x_1633_; uint8_t v___x_1634_; uint8_t v___x_1635_; uint8_t v___x_1636_; uint8_t v___x_1637_; 
v___x_1633_ = lean_byte_array_fget(v_array_1627_, v_idx_1628_);
v___x_1634_ = 1;
v___x_1635_ = lean_uint8_land(v___x_1634_, v___x_1633_);
v___x_1636_ = 0;
v___x_1637_ = lean_uint8_dec_eq(v___x_1635_, v___x_1636_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; 
lean_dec_ref(v_parser_1624_);
v___x_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1638_, 0, v_a_1626_);
lean_ctor_set(v___x_1638_, 1, v_acc_1625_);
return v___x_1638_;
}
else
{
uint8_t v___x_1639_; 
v___x_1639_ = lean_uint8_dec_eq(v___x_1633_, v___x_1636_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; 
lean_inc_ref(v_parser_1624_);
v___x_1640_ = lean_apply_1(v_parser_1624_, v_a_1626_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_pos_1641_; lean_object* v_res_1642_; lean_object* v___x_1643_; 
v_pos_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_pos_1641_);
v_res_1642_ = lean_ctor_get(v___x_1640_, 1);
lean_inc(v_res_1642_);
lean_dec_ref_known(v___x_1640_, 2);
v___x_1643_ = lean_array_push(v_acc_1625_, v_res_1642_);
v_acc_1625_ = v___x_1643_;
v_a_1626_ = v_pos_1641_;
goto _start;
}
else
{
lean_object* v_pos_1645_; lean_object* v_err_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec_ref(v_acc_1625_);
lean_dec_ref(v_parser_1624_);
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
lean_dec_ref(v_parser_1624_);
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_a_1626_);
lean_ctor_set(v___x_1654_, 1, v_acc_1625_);
return v___x_1654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go(lean_object* v_00_u03b1_1655_, lean_object* v_parser_1656_, lean_object* v_acc_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(v_parser_1656_, v_acc_1657_, v_a_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(lean_object* v_parser_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0));
v___x_1663_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(v_parser_1660_, v___x_1662_, v_a_1661_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero(lean_object* v_00_u03b1_1664_, lean_object* v_parser_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(v_parser_1665_, v_a_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList(lean_object* v_a_1668_){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId), 1, 0);
v___x_1670_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(v___x_1669_, v_a_1668_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause(lean_object* v_a_1671_){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit), 1, 0);
v___x_1673_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v___x_1672_, v_a_1671_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(lean_object* v_acc_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v_array_1676_; lean_object* v_idx_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v_array_1676_ = lean_ctor_get(v_a_1675_, 0);
v_idx_1677_ = lean_ctor_get(v_a_1675_, 1);
v___x_1678_ = lean_byte_array_size(v_array_1676_);
v___x_1679_ = lean_nat_dec_lt(v_idx_1677_, v___x_1678_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_dec_ref(v_acc_1674_);
v___x_1680_ = lean_box(0);
v___x_1681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1681_, 0, v_a_1675_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
return v___x_1681_;
}
else
{
uint8_t v___x_1682_; uint8_t v___x_1683_; uint8_t v___x_1684_; uint8_t v___x_1685_; uint8_t v___x_1686_; 
v___x_1682_ = lean_byte_array_fget(v_array_1676_, v_idx_1677_);
v___x_1683_ = 1;
v___x_1684_ = lean_uint8_land(v___x_1683_, v___x_1682_);
v___x_1685_ = 0;
v___x_1686_ = lean_uint8_dec_eq(v___x_1684_, v___x_1685_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1687_, 0, v_a_1675_);
lean_ctor_set(v___x_1687_, 1, v_acc_1674_);
return v___x_1687_;
}
else
{
uint8_t v___x_1688_; 
v___x_1688_ = lean_uint8_dec_eq(v___x_1682_, v___x_1685_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1675_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_pos_1690_; lean_object* v_res_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1704_; 
v_pos_1690_ = lean_ctor_get(v___x_1689_, 0);
v_res_1691_ = lean_ctor_get(v___x_1689_, 1);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1693_ = v___x_1689_;
v_isShared_1694_ = v_isSharedCheck_1704_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_res_1691_);
lean_inc(v_pos_1690_);
lean_dec(v___x_1689_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1704_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1695_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1696_ = lean_int_dec_lt(v___x_1695_, v_res_1691_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1699_; 
lean_dec(v_res_1691_);
lean_dec_ref(v_acc_1674_);
v___x_1697_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1694_ == 0)
{
lean_ctor_set_tag(v___x_1693_, 1);
lean_ctor_set(v___x_1693_, 1, v___x_1697_);
v___x_1699_ = v___x_1693_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_pos_1690_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_del_object(v___x_1693_);
v___x_1701_ = lean_nat_abs(v_res_1691_);
lean_dec(v_res_1691_);
v___x_1702_ = lean_array_push(v_acc_1674_, v___x_1701_);
v_acc_1674_ = v___x_1702_;
v_a_1675_ = v_pos_1690_;
goto _start;
}
}
}
else
{
lean_object* v_pos_1705_; lean_object* v_err_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec_ref(v_acc_1674_);
v_pos_1705_ = lean_ctor_get(v___x_1689_, 0);
v_err_1706_ = lean_ctor_get(v___x_1689_, 1);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1689_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_err_1706_);
lean_inc(v_pos_1705_);
lean_dec(v___x_1689_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_pos_1705_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_err_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
else
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1714_, 0, v_a_1675_);
lean_ctor_set(v___x_1714_, 1, v_acc_1674_);
return v___x_1714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(lean_object* v_a_1715_){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0));
v___x_1717_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(v___x_1716_, v_a_1715_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(lean_object* v_a_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1718_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_pos_1720_; lean_object* v_res_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1752_; 
v_pos_1720_ = lean_ctor_get(v___x_1719_, 0);
v_res_1721_ = lean_ctor_get(v___x_1719_, 1);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1723_ = v___x_1719_;
v_isShared_1724_ = v_isSharedCheck_1752_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_res_1721_);
lean_inc(v_pos_1720_);
lean_dec(v___x_1719_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1752_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1725_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1726_ = lean_int_dec_lt(v_res_1721_, v___x_1725_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
lean_dec(v_res_1721_);
v___x_1727_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1));
if (v_isShared_1724_ == 0)
{
lean_ctor_set_tag(v___x_1723_, 1);
lean_ctor_set(v___x_1723_, 1, v___x_1727_);
v___x_1729_ = v___x_1723_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_pos_1720_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
else
{
lean_object* v___x_1731_; 
lean_del_object(v___x_1723_);
v___x_1731_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v_pos_1720_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_pos_1732_; lean_object* v_res_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1742_; 
v_pos_1732_ = lean_ctor_get(v___x_1731_, 0);
v_res_1733_ = lean_ctor_get(v___x_1731_, 1);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1735_ = v___x_1731_;
v_isShared_1736_ = v_isSharedCheck_1742_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_res_1733_);
lean_inc(v_pos_1732_);
lean_dec(v___x_1731_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1742_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1737_ = lean_nat_abs(v_res_1721_);
lean_dec(v_res_1721_);
v___x_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
lean_ctor_set(v___x_1738_, 1, v_res_1733_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 1, v___x_1738_);
v___x_1740_ = v___x_1735_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_pos_1732_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
else
{
lean_object* v_pos_1743_; lean_object* v_err_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_dec(v_res_1721_);
v_pos_1743_ = lean_ctor_get(v___x_1731_, 0);
v_err_1744_ = lean_ctor_get(v___x_1731_, 1);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1731_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_err_1744_);
lean_inc(v_pos_1743_);
lean_dec(v___x_1731_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_pos_1743_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_err_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1753_; lean_object* v_err_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
v_pos_1753_ = lean_ctor_get(v___x_1719_, 0);
v_err_1754_ = lean_ctor_get(v___x_1719_, 1);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1719_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_err_1754_);
lean_inc(v_pos_1753_);
lean_dec(v___x_1719_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_pos_1753_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_err_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints(lean_object* v_a_1762_){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes), 1, 0);
v___x_1764_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v___x_1763_, v_a_1762_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(lean_object* v_acc_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v_array_1767_; lean_object* v_idx_1768_; lean_object* v___x_1769_; uint8_t v___x_1770_; 
v_array_1767_ = lean_ctor_get(v_a_1766_, 0);
v_idx_1768_ = lean_ctor_get(v_a_1766_, 1);
v___x_1769_ = lean_byte_array_size(v_array_1767_);
v___x_1770_ = lean_nat_dec_lt(v_idx_1768_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_dec_ref(v_acc_1765_);
v___x_1771_ = lean_box(0);
v___x_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1772_, 0, v_a_1766_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
return v___x_1772_;
}
else
{
uint8_t v___x_1773_; uint8_t v___x_1774_; uint8_t v___x_1775_; 
v___x_1773_ = lean_byte_array_fget(v_array_1767_, v_idx_1768_);
v___x_1774_ = 0;
v___x_1775_ = lean_uint8_dec_eq(v___x_1773_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1766_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_pos_1777_; lean_object* v_res_1778_; lean_object* v___x_1779_; 
v_pos_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_pos_1777_);
v_res_1778_ = lean_ctor_get(v___x_1776_, 1);
lean_inc(v_res_1778_);
lean_dec_ref_known(v___x_1776_, 2);
v___x_1779_ = lean_array_push(v_acc_1765_, v_res_1778_);
v_acc_1765_ = v___x_1779_;
v_a_1766_ = v_pos_1777_;
goto _start;
}
else
{
lean_object* v_pos_1781_; lean_object* v_err_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec_ref(v_acc_1765_);
v_pos_1781_ = lean_ctor_get(v___x_1776_, 0);
v_err_1782_ = lean_ctor_get(v___x_1776_, 1);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1776_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_err_1782_);
lean_inc(v_pos_1781_);
lean_dec(v___x_1776_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_pos_1781_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_err_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
else
{
lean_object* v___x_1790_; 
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v_a_1766_);
lean_ctor_set(v___x_1790_, 1, v_acc_1765_);
return v___x_1790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(lean_object* v_a_1791_){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0));
v___x_1793_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(v___x_1792_, v_a_1791_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1_spec__2(lean_object* v_acc_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v_array_1796_; lean_object* v_idx_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v_array_1796_ = lean_ctor_get(v_a_1795_, 0);
v_idx_1797_ = lean_ctor_get(v_a_1795_, 1);
v___x_1798_ = lean_byte_array_size(v_array_1796_);
v___x_1799_ = lean_nat_dec_lt(v_idx_1797_, v___x_1798_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_dec_ref(v_acc_1794_);
v___x_1800_ = lean_box(0);
v___x_1801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1801_, 0, v_a_1795_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
return v___x_1801_;
}
else
{
uint8_t v___x_1802_; uint8_t v___x_1803_; uint8_t v___x_1804_; 
v___x_1802_ = lean_byte_array_fget(v_array_1796_, v_idx_1797_);
v___x_1803_ = 0;
v___x_1804_ = lean_uint8_dec_eq(v___x_1802_, v___x_1803_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(v_a_1795_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_pos_1806_; lean_object* v_res_1807_; lean_object* v___x_1808_; 
v_pos_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_pos_1806_);
v_res_1807_ = lean_ctor_get(v___x_1805_, 1);
lean_inc(v_res_1807_);
lean_dec_ref_known(v___x_1805_, 2);
v___x_1808_ = lean_array_push(v_acc_1794_, v_res_1807_);
v_acc_1794_ = v___x_1808_;
v_a_1795_ = v_pos_1806_;
goto _start;
}
else
{
lean_object* v_pos_1810_; lean_object* v_err_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec_ref(v_acc_1794_);
v_pos_1810_ = lean_ctor_get(v___x_1805_, 0);
v_err_1811_ = lean_ctor_get(v___x_1805_, 1);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1805_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_err_1811_);
lean_inc(v_pos_1810_);
lean_dec(v___x_1805_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_pos_1810_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_err_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
else
{
lean_object* v___x_1819_; 
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v_a_1795_);
lean_ctor_set(v___x_1819_, 1, v_acc_1794_);
return v___x_1819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1(lean_object* v_a_1820_){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0));
v___x_1822_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1_spec__2(v___x_1821_, v_a_1820_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(lean_object* v_a_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1823_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_pos_1825_; lean_object* v_res_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1955_; 
v_pos_1825_ = lean_ctor_get(v___x_1824_, 0);
v_res_1826_ = lean_ctor_get(v___x_1824_, 1);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1828_ = v___x_1824_;
v_isShared_1829_ = v_isSharedCheck_1955_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_res_1826_);
lean_inc(v_pos_1825_);
lean_dec(v___x_1824_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1955_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1830_ = lean_unsigned_to_nat(0u);
v___x_1831_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1832_ = lean_int_dec_lt(v___x_1831_, v_res_1826_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
lean_dec(v_res_1826_);
v___x_1833_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1829_ == 0)
{
lean_ctor_set_tag(v___x_1828_, 1);
lean_ctor_set(v___x_1828_, 1, v___x_1833_);
v___x_1835_ = v___x_1828_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_pos_1825_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
else
{
lean_object* v___x_1837_; 
lean_del_object(v___x_1828_);
v___x_1837_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(v_pos_1825_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_pos_1838_; lean_object* v_res_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1945_; 
v_pos_1838_ = lean_ctor_get(v___x_1837_, 0);
v_res_1839_ = lean_ctor_get(v___x_1837_, 1);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1841_ = v___x_1837_;
v_isShared_1842_ = v_isSharedCheck_1945_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_res_1839_);
lean_inc(v_pos_1838_);
lean_dec(v___x_1837_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1945_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v_array_1843_; lean_object* v_idx_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; 
v_array_1843_ = lean_ctor_get(v_pos_1838_, 0);
v_idx_1844_ = lean_ctor_get(v_pos_1838_, 1);
v___x_1845_ = lean_byte_array_size(v_array_1843_);
v___x_1846_ = lean_nat_dec_lt(v_idx_1844_, v___x_1845_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
lean_dec(v_res_1839_);
lean_dec(v_res_1826_);
v___x_1847_ = lean_box(0);
if (v_isShared_1842_ == 0)
{
lean_ctor_set_tag(v___x_1841_, 1);
lean_ctor_set(v___x_1841_, 1, v___x_1847_);
v___x_1849_ = v___x_1841_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_pos_1838_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
else
{
uint8_t v___x_1851_; uint8_t v_got_1852_; uint8_t v___x_1853_; 
v___x_1851_ = 0;
v_got_1852_ = lean_byte_array_fget(v_array_1843_, v_idx_1844_);
v___x_1853_ = lean_uint8_dec_eq(v_got_1852_, v___x_1851_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
lean_dec(v_res_1839_);
lean_dec(v_res_1826_);
v___x_1854_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
if (v_isShared_1842_ == 0)
{
lean_ctor_set_tag(v___x_1841_, 1);
lean_ctor_set(v___x_1841_, 1, v___x_1854_);
v___x_1856_ = v___x_1841_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_pos_1838_);
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
lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1942_; 
lean_inc(v_idx_1844_);
lean_inc_ref(v_array_1843_);
lean_del_object(v___x_1841_);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_pos_1838_);
if (v_isSharedCheck_1942_ == 0)
{
lean_object* v_unused_1943_; lean_object* v_unused_1944_; 
v_unused_1943_ = lean_ctor_get(v_pos_1838_, 1);
lean_dec(v_unused_1943_);
v_unused_1944_ = lean_ctor_get(v_pos_1838_, 0);
lean_dec(v_unused_1944_);
v___x_1859_ = v_pos_1838_;
v_isShared_1860_ = v_isSharedCheck_1942_;
goto v_resetjp_1858_;
}
else
{
lean_dec(v_pos_1838_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1942_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1861_ = lean_unsigned_to_nat(1u);
v___x_1862_ = lean_nat_add(v_idx_1844_, v___x_1861_);
lean_dec(v_idx_1844_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 1, v___x_1862_);
v___x_1864_ = v___x_1859_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_array_1843_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v___x_1864_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_pos_1866_; lean_object* v_res_1867_; lean_object* v___x_1868_; 
v_pos_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_pos_1866_);
v_res_1867_ = lean_ctor_get(v___x_1865_, 1);
lean_inc(v_res_1867_);
lean_dec_ref_known(v___x_1865_, 2);
v___x_1868_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1(v_pos_1866_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_pos_1869_; lean_object* v_res_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1922_; 
v_pos_1869_ = lean_ctor_get(v___x_1868_, 0);
v_res_1870_ = lean_ctor_get(v___x_1868_, 1);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1872_ = v___x_1868_;
v_isShared_1873_ = v_isSharedCheck_1922_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_res_1870_);
lean_inc(v_pos_1869_);
lean_dec(v___x_1868_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1922_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v_array_1874_; lean_object* v_idx_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; 
v_array_1874_ = lean_ctor_get(v_pos_1869_, 0);
v_idx_1875_ = lean_ctor_get(v_pos_1869_, 1);
v___x_1876_ = lean_byte_array_size(v_array_1874_);
v___x_1877_ = lean_nat_dec_lt(v_idx_1875_, v___x_1876_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
lean_dec(v_res_1870_);
lean_dec(v_res_1867_);
lean_dec(v_res_1839_);
lean_dec(v_res_1826_);
v___x_1878_ = lean_box(0);
if (v_isShared_1873_ == 0)
{
lean_ctor_set_tag(v___x_1872_, 1);
lean_ctor_set(v___x_1872_, 1, v___x_1878_);
v___x_1880_ = v___x_1872_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_pos_1869_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
else
{
uint8_t v_got_1882_; uint8_t v___x_1883_; 
v_got_1882_ = lean_byte_array_fget(v_array_1874_, v_idx_1875_);
v___x_1883_ = lean_uint8_dec_eq(v_got_1882_, v___x_1851_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; lean_object* v___x_1886_; 
lean_dec(v_res_1870_);
lean_dec(v_res_1867_);
lean_dec(v_res_1839_);
lean_dec(v_res_1826_);
v___x_1884_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
if (v_isShared_1873_ == 0)
{
lean_ctor_set_tag(v___x_1872_, 1);
lean_ctor_set(v___x_1872_, 1, v___x_1884_);
v___x_1886_ = v___x_1872_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_pos_1869_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
else
{
lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1919_; 
lean_inc(v_idx_1875_);
lean_inc_ref(v_array_1874_);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_pos_1869_);
if (v_isSharedCheck_1919_ == 0)
{
lean_object* v_unused_1920_; lean_object* v_unused_1921_; 
v_unused_1920_ = lean_ctor_get(v_pos_1869_, 1);
lean_dec(v_unused_1920_);
v_unused_1921_ = lean_ctor_get(v_pos_1869_, 0);
lean_dec(v_unused_1921_);
v___x_1889_ = v_pos_1869_;
v_isShared_1890_ = v_isSharedCheck_1919_;
goto v_resetjp_1888_;
}
else
{
lean_dec(v_pos_1869_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1919_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1894_; 
v___x_1891_ = lean_nat_abs(v_res_1826_);
lean_dec(v_res_1826_);
v___x_1892_ = lean_nat_add(v_idx_1875_, v___x_1861_);
lean_dec(v_idx_1875_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 1, v___x_1892_);
v___x_1894_ = v___x_1889_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_array_1874_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1895_ = lean_array_get_size(v_res_1839_);
v___x_1896_ = lean_nat_dec_eq(v___x_1895_, v___x_1830_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1897_ = lean_array_get_size(v_res_1870_);
v___x_1898_ = lean_nat_dec_eq(v___x_1897_, v___x_1830_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1902_; 
v___x_1899_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_1839_);
v___x_1900_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1891_);
lean_ctor_set(v___x_1900_, 1, v_res_1839_);
lean_ctor_set(v___x_1900_, 2, v___x_1899_);
lean_ctor_set(v___x_1900_, 3, v_res_1867_);
lean_ctor_set(v___x_1900_, 4, v_res_1870_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 1, v___x_1900_);
lean_ctor_set(v___x_1872_, 0, v___x_1894_);
v___x_1902_ = v___x_1872_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
lean_dec(v_res_1870_);
v___x_1904_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1891_);
lean_ctor_set(v___x_1904_, 1, v_res_1839_);
lean_ctor_set(v___x_1904_, 2, v_res_1867_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 1, v___x_1904_);
lean_ctor_set(v___x_1872_, 0, v___x_1894_);
v___x_1906_ = v___x_1872_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
else
{
lean_object* v___x_1908_; uint8_t v___x_1909_; 
lean_dec(v_res_1839_);
v___x_1908_ = lean_array_get_size(v_res_1870_);
lean_dec(v_res_1870_);
v___x_1909_ = lean_nat_dec_eq(v___x_1908_, v___x_1830_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1910_; lean_object* v___x_1912_; 
lean_dec(v___x_1891_);
lean_dec(v_res_1867_);
v___x_1910_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2));
if (v_isShared_1873_ == 0)
{
lean_ctor_set_tag(v___x_1872_, 1);
lean_ctor_set(v___x_1872_, 1, v___x_1910_);
lean_ctor_set(v___x_1872_, 0, v___x_1894_);
v___x_1912_ = v___x_1872_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1891_);
lean_ctor_set(v___x_1914_, 1, v_res_1867_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 1, v___x_1914_);
lean_ctor_set(v___x_1872_, 0, v___x_1894_);
v___x_1916_ = v___x_1872_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
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
lean_object* v_pos_1923_; lean_object* v_err_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
lean_dec(v_res_1867_);
lean_dec(v_res_1839_);
lean_dec(v_res_1826_);
v_pos_1923_ = lean_ctor_get(v___x_1868_, 0);
v_err_1924_ = lean_ctor_get(v___x_1868_, 1);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1926_ = v___x_1868_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_err_1924_);
lean_inc(v_pos_1923_);
lean_dec(v___x_1868_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_pos_1923_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_err_1924_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
else
{
lean_object* v_pos_1932_; lean_object* v_err_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v_res_1839_);
lean_dec(v_res_1826_);
v_pos_1932_ = lean_ctor_get(v___x_1865_, 0);
v_err_1933_ = lean_ctor_get(v___x_1865_, 1);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1865_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_err_1933_);
lean_inc(v_pos_1932_);
lean_dec(v___x_1865_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_pos_1932_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_err_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
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
lean_object* v_pos_1946_; lean_object* v_err_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec(v_res_1826_);
v_pos_1946_ = lean_ctor_get(v___x_1837_, 0);
v_err_1947_ = lean_ctor_get(v___x_1837_, 1);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1837_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_err_1947_);
lean_inc(v_pos_1946_);
lean_dec(v___x_1837_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_pos_1946_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_err_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1956_; lean_object* v_err_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
v_pos_1956_ = lean_ctor_get(v___x_1824_, 0);
v_err_1957_ = lean_ctor_get(v___x_1824_, 1);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1824_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_err_1957_);
lean_inc(v_pos_1956_);
lean_dec(v___x_1824_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_pos_1956_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_err_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(lean_object* v_a_1965_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v_a_1965_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_pos_1967_; lean_object* v_res_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_2002_; 
v_pos_1967_ = lean_ctor_get(v___x_1966_, 0);
v_res_1968_ = lean_ctor_get(v___x_1966_, 1);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1970_ = v___x_1966_;
v_isShared_1971_ = v_isSharedCheck_2002_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_res_1968_);
lean_inc(v_pos_1967_);
lean_dec(v___x_1966_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_2002_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v_array_1972_; lean_object* v_idx_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
v_array_1972_ = lean_ctor_get(v_pos_1967_, 0);
v_idx_1973_ = lean_ctor_get(v_pos_1967_, 1);
v___x_1974_ = lean_byte_array_size(v_array_1972_);
v___x_1975_ = lean_nat_dec_lt(v_idx_1973_, v___x_1974_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1978_; 
lean_dec(v_res_1968_);
v___x_1976_ = lean_box(0);
if (v_isShared_1971_ == 0)
{
lean_ctor_set_tag(v___x_1970_, 1);
lean_ctor_set(v___x_1970_, 1, v___x_1976_);
v___x_1978_ = v___x_1970_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_pos_1967_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
else
{
uint8_t v___x_1980_; uint8_t v_got_1981_; uint8_t v___x_1982_; 
v___x_1980_ = 0;
v_got_1981_ = lean_byte_array_fget(v_array_1972_, v_idx_1973_);
v___x_1982_ = lean_uint8_dec_eq(v_got_1981_, v___x_1980_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1985_; 
lean_dec(v_res_1968_);
v___x_1983_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
if (v_isShared_1971_ == 0)
{
lean_ctor_set_tag(v___x_1970_, 1);
lean_ctor_set(v___x_1970_, 1, v___x_1983_);
v___x_1985_ = v___x_1970_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_pos_1967_);
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
lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1999_; 
lean_inc(v_idx_1973_);
lean_inc_ref(v_array_1972_);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_pos_1967_);
if (v_isSharedCheck_1999_ == 0)
{
lean_object* v_unused_2000_; lean_object* v_unused_2001_; 
v_unused_2000_ = lean_ctor_get(v_pos_1967_, 1);
lean_dec(v_unused_2000_);
v_unused_2001_ = lean_ctor_get(v_pos_1967_, 0);
lean_dec(v_unused_2001_);
v___x_1988_ = v_pos_1967_;
v_isShared_1989_ = v_isSharedCheck_1999_;
goto v_resetjp_1987_;
}
else
{
lean_dec(v_pos_1967_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1999_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1990_ = lean_unsigned_to_nat(1u);
v___x_1991_ = lean_nat_add(v_idx_1973_, v___x_1990_);
lean_dec(v_idx_1973_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 1, v___x_1991_);
v___x_1993_ = v___x_1988_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_array_1972_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1994_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1994_, 0, v_res_1968_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 1, v___x_1994_);
lean_ctor_set(v___x_1970_, 0, v___x_1993_);
v___x_1996_ = v___x_1970_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_2003_; lean_object* v_err_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
v_pos_2003_ = lean_ctor_get(v___x_1966_, 0);
v_err_2004_ = lean_ctor_get(v___x_1966_, 1);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_1966_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_err_2004_);
lean_inc(v_pos_2003_);
lean_dec(v___x_1966_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_pos_2003_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_err_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0(void){
_start:
{
uint32_t v___x_2012_; uint8_t v___x_2013_; 
v___x_2012_ = 97;
v___x_2013_ = lean_uint32_to_uint8(v___x_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(lean_object* v_a_2015_){
_start:
{
lean_object* v_array_2016_; lean_object* v_idx_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; 
v_array_2016_ = lean_ctor_get(v_a_2015_, 0);
v_idx_2017_ = lean_ctor_get(v_a_2015_, 1);
v___x_2018_ = lean_byte_array_size(v_array_2016_);
v___x_2019_ = lean_nat_dec_lt(v_idx_2017_, v___x_2018_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_box(0);
v___x_2021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2021_, 0, v_a_2015_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
return v___x_2021_;
}
else
{
lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2043_; 
lean_inc(v_idx_2017_);
lean_inc_ref(v_array_2016_);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_a_2015_);
if (v_isSharedCheck_2043_ == 0)
{
lean_object* v_unused_2044_; lean_object* v_unused_2045_; 
v_unused_2044_ = lean_ctor_get(v_a_2015_, 1);
lean_dec(v_unused_2044_);
v_unused_2045_ = lean_ctor_get(v_a_2015_, 0);
lean_dec(v_unused_2045_);
v___x_2023_ = v_a_2015_;
v_isShared_2024_ = v_isSharedCheck_2043_;
goto v_resetjp_2022_;
}
else
{
lean_dec(v_a_2015_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2043_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
uint8_t v_c_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v_it_x27_2029_; 
v_c_2025_ = lean_byte_array_fget(v_array_2016_, v_idx_2017_);
v___x_2026_ = lean_unsigned_to_nat(1u);
v___x_2027_ = lean_nat_add(v_idx_2017_, v___x_2026_);
lean_dec(v_idx_2017_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 1, v___x_2027_);
v_it_x27_2029_ = v___x_2023_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_array_2016_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v___x_2027_);
v_it_x27_2029_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
uint8_t v___x_2030_; uint8_t v___x_2031_; 
v___x_2030_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
v___x_2031_ = lean_uint8_dec_eq(v_c_2025_, v___x_2030_);
if (v___x_2031_ == 0)
{
uint8_t v___x_2032_; uint8_t v___x_2033_; 
v___x_2032_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
v___x_2033_ = lean_uint8_dec_eq(v_c_2025_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2034_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1));
v___x_2035_ = lean_uint8_to_nat(v_c_2025_);
v___x_2036_ = l_Nat_reprFast(v___x_2035_);
v___x_2037_ = lean_string_append(v___x_2034_, v___x_2036_);
lean_dec_ref(v___x_2036_);
v___x_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
v___x_2039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2039_, 0, v_it_x27_2029_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
return v___x_2039_;
}
else
{
lean_object* v___x_2040_; 
v___x_2040_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(v_it_x27_2029_);
return v___x_2040_;
}
}
else
{
lean_object* v___x_2041_; 
v___x_2041_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(v_it_x27_2029_);
return v___x_2041_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(lean_object* v_acc_2046_, lean_object* v_a_2047_){
_start:
{
lean_object* v___x_2048_; 
lean_inc_ref(v_a_2047_);
v___x_2048_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(v_a_2047_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_pos_2049_; lean_object* v_res_2050_; lean_object* v___x_2051_; 
lean_dec_ref(v_a_2047_);
v_pos_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_pos_2049_);
v_res_2050_ = lean_ctor_get(v___x_2048_, 1);
lean_inc(v_res_2050_);
lean_dec_ref_known(v___x_2048_, 2);
v___x_2051_ = lean_array_push(v_acc_2046_, v_res_2050_);
v_acc_2046_ = v___x_2051_;
v_a_2047_ = v_pos_2049_;
goto _start;
}
else
{
lean_object* v_pos_2053_; lean_object* v_err_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2067_; 
v_pos_2053_ = lean_ctor_get(v___x_2048_, 0);
v_err_2054_ = lean_ctor_get(v___x_2048_, 1);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2056_ = v___x_2048_;
v_isShared_2057_ = v_isSharedCheck_2067_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_err_2054_);
lean_inc(v_pos_2053_);
lean_dec(v___x_2048_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2067_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v_idx_2058_; lean_object* v_idx_2059_; uint8_t v___x_2060_; 
v_idx_2058_ = lean_ctor_get(v_a_2047_, 1);
lean_inc(v_idx_2058_);
lean_dec_ref(v_a_2047_);
v_idx_2059_ = lean_ctor_get(v_pos_2053_, 1);
v___x_2060_ = lean_nat_dec_eq(v_idx_2058_, v_idx_2059_);
lean_dec(v_idx_2058_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2062_; 
lean_dec_ref(v_acc_2046_);
if (v_isShared_2057_ == 0)
{
v___x_2062_ = v___x_2056_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_pos_2053_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_err_2054_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
else
{
lean_object* v___x_2065_; 
lean_dec(v_err_2054_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set_tag(v___x_2056_, 0);
lean_ctor_set(v___x_2056_, 1, v_acc_2046_);
v___x_2065_ = v___x_2056_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_pos_2053_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_acc_2046_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(lean_object* v_a_2071_){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0));
v___x_2073_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(v___x_2072_, v_a_2071_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_pos_2074_; lean_object* v_array_2075_; lean_object* v_idx_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v_pos_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_pos_2074_);
v_array_2075_ = lean_ctor_get(v_pos_2074_, 0);
v_idx_2076_ = lean_ctor_get(v_pos_2074_, 1);
v___x_2077_ = lean_byte_array_size(v_array_2075_);
v___x_2078_ = lean_nat_dec_lt(v_idx_2076_, v___x_2077_);
if (v___x_2078_ == 0)
{
lean_dec(v_pos_2074_);
return v___x_2073_;
}
else
{
lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2086_; 
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; lean_object* v_unused_2088_; 
v_unused_2087_ = lean_ctor_get(v___x_2073_, 1);
lean_dec(v_unused_2087_);
v_unused_2088_ = lean_ctor_get(v___x_2073_, 0);
lean_dec(v_unused_2088_);
v___x_2080_ = v___x_2073_;
v_isShared_2081_ = v_isSharedCheck_2086_;
goto v_resetjp_2079_;
}
else
{
lean_dec(v___x_2073_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2086_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2082_; lean_object* v___x_2084_; 
v___x_2082_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__1));
if (v_isShared_2081_ == 0)
{
lean_ctor_set_tag(v___x_2080_, 1);
lean_ctor_set(v___x_2080_, 1, v___x_2082_);
v___x_2084_ = v___x_2080_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_pos_2074_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v___x_2082_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
else
{
return v___x_2073_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_parseActions(lean_object* v_a_2089_){
_start:
{
lean_object* v_array_2090_; lean_object* v_idx_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v_array_2090_ = lean_ctor_get(v_a_2089_, 0);
v_idx_2091_ = lean_ctor_get(v_a_2089_, 1);
v___x_2092_ = lean_byte_array_size(v_array_2090_);
v___x_2093_ = lean_nat_dec_lt(v_idx_2091_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2094_ = lean_box(0);
v___x_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2095_, 0, v_a_2089_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
return v___x_2095_;
}
else
{
uint8_t v___x_2096_; uint8_t v___x_2097_; uint8_t v___x_2098_; 
v___x_2096_ = lean_byte_array_fget(v_array_2090_, v_idx_2091_);
v___x_2097_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
v___x_2098_ = lean_uint8_dec_eq(v___x_2096_, v___x_2097_);
if (v___x_2098_ == 0)
{
uint8_t v___x_2099_; uint8_t v___x_2100_; 
v___x_2099_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
v___x_2100_ = lean_uint8_dec_eq(v___x_2096_, v___x_2099_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; 
v___x_2101_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(v_a_2089_);
return v___x_2101_;
}
else
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(v_a_2089_);
return v___x_2102_;
}
}
else
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(v_a_2089_);
return v___x_2103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object* v_path_2104_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_IO_FS_readBinFile(v_path_2104_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2128_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2109_ = v___x_2106_;
v_isShared_2110_ = v_isSharedCheck_2128_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2128_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_parseActions), 1, 0);
v___x_2112_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_2111_, v_a_2107_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2123_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2123_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2123_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
lean_ctor_set_tag(v___x_2115_, 18);
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2120_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set_tag(v___x_2109_, 1);
lean_ctor_set(v___x_2109_, 0, v___x_2118_);
v___x_2120_ = v___x_2109_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2118_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; 
v_a_2124_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2112_, 1);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v_a_2124_);
v___x_2126_ = v___x_2109_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
v_a_2129_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2106_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2106_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
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
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof___boxed(lean_object* v_path_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(v_path_2137_);
lean_dec_ref(v_path_2137_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_parseLRATProof(lean_object* v_proof_2140_){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_parseActions), 1, 0);
v___x_2142_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_2141_, v_proof_2140_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(lean_object* v_as_2144_, size_t v_i_2145_, size_t v_stop_2146_, lean_object* v_b_2147_){
_start:
{
uint8_t v___x_2148_; 
v___x_2148_ = lean_usize_dec_eq(v_i_2145_, v_stop_2146_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; size_t v___x_2154_; size_t v___x_2155_; 
v___x_2149_ = lean_array_uget_borrowed(v_as_2144_, v_i_2145_);
lean_inc(v___x_2149_);
v___x_2150_ = l_Nat_reprFast(v___x_2149_);
v___x_2151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2152_ = lean_string_append(v___x_2150_, v___x_2151_);
v___x_2153_ = lean_string_append(v_b_2147_, v___x_2152_);
lean_dec_ref(v___x_2152_);
v___x_2154_ = ((size_t)1ULL);
v___x_2155_ = lean_usize_add(v_i_2145_, v___x_2154_);
v_i_2145_ = v___x_2155_;
v_b_2147_ = v___x_2153_;
goto _start;
}
else
{
return v_b_2147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___boxed(lean_object* v_as_2157_, lean_object* v_i_2158_, lean_object* v_stop_2159_, lean_object* v_b_2160_){
_start:
{
size_t v_i_boxed_2161_; size_t v_stop_boxed_2162_; lean_object* v_res_2163_; 
v_i_boxed_2161_ = lean_unbox_usize(v_i_2158_);
lean_dec(v_i_2158_);
v_stop_boxed_2162_ = lean_unbox_usize(v_stop_2159_);
lean_dec(v_stop_2159_);
v_res_2163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_as_2157_, v_i_boxed_2161_, v_stop_boxed_2162_, v_b_2160_);
lean_dec_ref(v_as_2157_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(lean_object* v_ids_2165_){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2166_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2167_ = lean_unsigned_to_nat(0u);
v___x_2168_ = lean_array_get_size(v_ids_2165_);
v___x_2169_ = lean_nat_dec_lt(v___x_2167_, v___x_2168_);
if (v___x_2169_ == 0)
{
return v___x_2166_;
}
else
{
uint8_t v___x_2170_; 
v___x_2170_ = lean_nat_dec_le(v___x_2168_, v___x_2168_);
if (v___x_2170_ == 0)
{
if (v___x_2169_ == 0)
{
return v___x_2166_;
}
else
{
size_t v___x_2171_; size_t v___x_2172_; lean_object* v___x_2173_; 
v___x_2171_ = ((size_t)0ULL);
v___x_2172_ = lean_usize_of_nat(v___x_2168_);
v___x_2173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_ids_2165_, v___x_2171_, v___x_2172_, v___x_2166_);
return v___x_2173_;
}
}
else
{
size_t v___x_2174_; size_t v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = ((size_t)0ULL);
v___x_2175_ = lean_usize_of_nat(v___x_2168_);
v___x_2176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_ids_2165_, v___x_2174_, v___x_2175_, v___x_2166_);
return v___x_2176_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___boxed(lean_object* v_ids_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_ids_2177_);
lean_dec_ref(v_ids_2177_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(lean_object* v_hint_2180_){
_start:
{
lean_object* v_fst_2181_; lean_object* v_snd_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v_fst_2181_ = lean_ctor_get(v_hint_2180_, 0);
lean_inc(v_fst_2181_);
v_snd_2182_ = lean_ctor_get(v_hint_2180_, 1);
lean_inc(v_snd_2182_);
lean_dec_ref(v_hint_2180_);
v___x_2183_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0));
v___x_2184_ = l_Nat_reprFast(v_fst_2181_);
v___x_2185_ = lean_string_append(v___x_2183_, v___x_2184_);
lean_dec_ref(v___x_2184_);
v___x_2186_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2187_ = lean_string_append(v___x_2185_, v___x_2186_);
v___x_2188_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_snd_2182_);
lean_dec(v_snd_2182_);
v___x_2189_ = lean_string_append(v___x_2187_, v___x_2188_);
lean_dec_ref(v___x_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(lean_object* v_as_2190_, size_t v_i_2191_, size_t v_stop_2192_, lean_object* v_b_2193_){
_start:
{
uint8_t v___x_2194_; 
v___x_2194_ = lean_usize_dec_eq(v_i_2191_, v_stop_2192_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; size_t v___x_2198_; size_t v___x_2199_; 
v___x_2195_ = lean_array_uget_borrowed(v_as_2190_, v_i_2191_);
lean_inc(v___x_2195_);
v___x_2196_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(v___x_2195_);
v___x_2197_ = lean_string_append(v_b_2193_, v___x_2196_);
lean_dec_ref(v___x_2196_);
v___x_2198_ = ((size_t)1ULL);
v___x_2199_ = lean_usize_add(v_i_2191_, v___x_2198_);
v_i_2191_ = v___x_2199_;
v_b_2193_ = v___x_2197_;
goto _start;
}
else
{
return v_b_2193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0___boxed(lean_object* v_as_2201_, lean_object* v_i_2202_, lean_object* v_stop_2203_, lean_object* v_b_2204_){
_start:
{
size_t v_i_boxed_2205_; size_t v_stop_boxed_2206_; lean_object* v_res_2207_; 
v_i_boxed_2205_ = lean_unbox_usize(v_i_2202_);
lean_dec(v_i_2202_);
v_stop_boxed_2206_ = lean_unbox_usize(v_stop_2203_);
lean_dec(v_stop_2203_);
v_res_2207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_as_2201_, v_i_boxed_2205_, v_stop_boxed_2206_, v_b_2204_);
lean_dec_ref(v_as_2201_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(lean_object* v_hints_2208_){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; uint8_t v___x_2212_; 
v___x_2209_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2210_ = lean_unsigned_to_nat(0u);
v___x_2211_ = lean_array_get_size(v_hints_2208_);
v___x_2212_ = lean_nat_dec_lt(v___x_2210_, v___x_2211_);
if (v___x_2212_ == 0)
{
return v___x_2209_;
}
else
{
uint8_t v___x_2213_; 
v___x_2213_ = lean_nat_dec_le(v___x_2211_, v___x_2211_);
if (v___x_2213_ == 0)
{
if (v___x_2212_ == 0)
{
return v___x_2209_;
}
else
{
size_t v___x_2214_; size_t v___x_2215_; lean_object* v___x_2216_; 
v___x_2214_ = ((size_t)0ULL);
v___x_2215_ = lean_usize_of_nat(v___x_2211_);
v___x_2216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_hints_2208_, v___x_2214_, v___x_2215_, v___x_2209_);
return v___x_2216_;
}
}
else
{
size_t v___x_2217_; size_t v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = ((size_t)0ULL);
v___x_2218_ = lean_usize_of_nat(v___x_2211_);
v___x_2219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_hints_2208_, v___x_2217_, v___x_2218_, v___x_2209_);
return v___x_2219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___boxed(lean_object* v_hints_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(v_hints_2220_);
lean_dec_ref(v_hints_2220_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(lean_object* v_as_2222_, size_t v_i_2223_, size_t v_stop_2224_, lean_object* v_b_2225_){
_start:
{
uint8_t v___x_2226_; 
v___x_2226_ = lean_usize_dec_eq(v_i_2223_, v_stop_2224_);
if (v___x_2226_ == 0)
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; size_t v___x_2232_; size_t v___x_2233_; 
v___x_2227_ = lean_array_uget_borrowed(v_as_2222_, v_i_2223_);
v___x_2228_ = l_Int_repr(v___x_2227_);
v___x_2229_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2230_ = lean_string_append(v___x_2228_, v___x_2229_);
v___x_2231_ = lean_string_append(v_b_2225_, v___x_2230_);
lean_dec_ref(v___x_2230_);
v___x_2232_ = ((size_t)1ULL);
v___x_2233_ = lean_usize_add(v_i_2223_, v___x_2232_);
v_i_2223_ = v___x_2233_;
v_b_2225_ = v___x_2231_;
goto _start;
}
else
{
return v_b_2225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0___boxed(lean_object* v_as_2235_, lean_object* v_i_2236_, lean_object* v_stop_2237_, lean_object* v_b_2238_){
_start:
{
size_t v_i_boxed_2239_; size_t v_stop_boxed_2240_; lean_object* v_res_2241_; 
v_i_boxed_2239_ = lean_unbox_usize(v_i_2236_);
lean_dec(v_i_2236_);
v_stop_boxed_2240_ = lean_unbox_usize(v_stop_2237_);
lean_dec(v_stop_2237_);
v_res_2241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_as_2235_, v_i_boxed_2239_, v_stop_boxed_2240_, v_b_2238_);
lean_dec_ref(v_as_2235_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(lean_object* v_clause_2242_){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; 
v___x_2243_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2244_ = lean_unsigned_to_nat(0u);
v___x_2245_ = lean_array_get_size(v_clause_2242_);
v___x_2246_ = lean_nat_dec_lt(v___x_2244_, v___x_2245_);
if (v___x_2246_ == 0)
{
return v___x_2243_;
}
else
{
uint8_t v___x_2247_; 
v___x_2247_ = lean_nat_dec_le(v___x_2245_, v___x_2245_);
if (v___x_2247_ == 0)
{
if (v___x_2246_ == 0)
{
return v___x_2243_;
}
else
{
size_t v___x_2248_; size_t v___x_2249_; lean_object* v___x_2250_; 
v___x_2248_ = ((size_t)0ULL);
v___x_2249_ = lean_usize_of_nat(v___x_2245_);
v___x_2250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_clause_2242_, v___x_2248_, v___x_2249_, v___x_2243_);
return v___x_2250_;
}
}
else
{
size_t v___x_2251_; size_t v___x_2252_; lean_object* v___x_2253_; 
v___x_2251_ = ((size_t)0ULL);
v___x_2252_ = lean_usize_of_nat(v___x_2245_);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_clause_2242_, v___x_2251_, v___x_2252_, v___x_2243_);
return v___x_2253_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___boxed(lean_object* v_clause_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_clause_2254_);
lean_dec_ref(v_clause_2254_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(lean_object* v_a_2260_){
_start:
{
switch(lean_obj_tag(v_a_2260_))
{
case 0:
{
lean_object* v_id_2261_; lean_object* v_rupHints_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v_id_2261_ = lean_ctor_get(v_a_2260_, 0);
lean_inc(v_id_2261_);
v_rupHints_2262_ = lean_ctor_get(v_a_2260_, 1);
lean_inc_ref(v_rupHints_2262_);
lean_dec_ref_known(v_a_2260_, 2);
v___x_2263_ = l_Nat_reprFast(v_id_2261_);
v___x_2264_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__0));
v___x_2265_ = lean_string_append(v___x_2263_, v___x_2264_);
v___x_2266_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2262_);
lean_dec_ref(v_rupHints_2262_);
v___x_2267_ = lean_string_append(v___x_2265_, v___x_2266_);
lean_dec_ref(v___x_2266_);
v___x_2268_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2269_ = lean_string_append(v___x_2267_, v___x_2268_);
return v___x_2269_;
}
case 1:
{
lean_object* v_id_2270_; lean_object* v_c_2271_; lean_object* v_rupHints_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v_id_2270_ = lean_ctor_get(v_a_2260_, 0);
lean_inc(v_id_2270_);
v_c_2271_ = lean_ctor_get(v_a_2260_, 1);
lean_inc(v_c_2271_);
v_rupHints_2272_ = lean_ctor_get(v_a_2260_, 2);
lean_inc_ref(v_rupHints_2272_);
lean_dec_ref_known(v_a_2260_, 3);
v___x_2273_ = l_Nat_reprFast(v_id_2270_);
v___x_2274_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2275_ = lean_string_append(v___x_2273_, v___x_2274_);
v___x_2276_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_c_2271_);
lean_dec(v_c_2271_);
v___x_2277_ = lean_string_append(v___x_2275_, v___x_2276_);
lean_dec_ref(v___x_2276_);
v___x_2278_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2));
v___x_2279_ = lean_string_append(v___x_2277_, v___x_2278_);
v___x_2280_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2272_);
lean_dec_ref(v_rupHints_2272_);
v___x_2281_ = lean_string_append(v___x_2279_, v___x_2280_);
lean_dec_ref(v___x_2280_);
v___x_2282_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2283_ = lean_string_append(v___x_2281_, v___x_2282_);
return v___x_2283_;
}
case 2:
{
lean_object* v_id_2284_; lean_object* v_c_2285_; lean_object* v_rupHints_2286_; lean_object* v_ratHints_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v_id_2284_ = lean_ctor_get(v_a_2260_, 0);
lean_inc(v_id_2284_);
v_c_2285_ = lean_ctor_get(v_a_2260_, 1);
lean_inc(v_c_2285_);
v_rupHints_2286_ = lean_ctor_get(v_a_2260_, 3);
lean_inc_ref(v_rupHints_2286_);
v_ratHints_2287_ = lean_ctor_get(v_a_2260_, 4);
lean_inc_ref(v_ratHints_2287_);
lean_dec_ref_known(v_a_2260_, 5);
v___x_2288_ = l_Nat_reprFast(v_id_2284_);
v___x_2289_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2290_ = lean_string_append(v___x_2288_, v___x_2289_);
v___x_2291_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_c_2285_);
lean_dec(v_c_2285_);
v___x_2292_ = lean_string_append(v___x_2290_, v___x_2291_);
lean_dec_ref(v___x_2291_);
v___x_2293_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2));
v___x_2294_ = lean_string_append(v___x_2292_, v___x_2293_);
v___x_2295_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2286_);
lean_dec_ref(v_rupHints_2286_);
v___x_2296_ = lean_string_append(v___x_2294_, v___x_2295_);
lean_dec_ref(v___x_2295_);
v___x_2297_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(v_ratHints_2287_);
lean_dec_ref(v_ratHints_2287_);
v___x_2298_ = lean_string_append(v___x_2296_, v___x_2297_);
lean_dec_ref(v___x_2297_);
v___x_2299_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2300_ = lean_string_append(v___x_2298_, v___x_2299_);
return v___x_2300_;
}
default: 
{
lean_object* v_ids_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v_ids_2301_ = lean_ctor_get(v_a_2260_, 0);
lean_inc_ref(v_ids_2301_);
lean_dec_ref_known(v_a_2260_, 1);
v___x_2302_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3));
v___x_2303_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_ids_2301_);
lean_dec_ref(v_ids_2301_);
v___x_2304_ = lean_string_append(v___x_2302_, v___x_2303_);
lean_dec_ref(v___x_2303_);
v___x_2305_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2306_ = lean_string_append(v___x_2304_, v___x_2305_);
return v___x_2306_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(lean_object* v_as_2308_, size_t v_i_2309_, size_t v_stop_2310_, lean_object* v_b_2311_){
_start:
{
uint8_t v___x_2312_; 
v___x_2312_ = lean_usize_dec_eq(v_i_2309_, v_stop_2310_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; size_t v___x_2318_; size_t v___x_2319_; 
v___x_2313_ = lean_array_uget_borrowed(v_as_2308_, v_i_2309_);
lean_inc(v___x_2313_);
v___x_2314_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(v___x_2313_);
v___x_2315_ = lean_string_append(v_b_2311_, v___x_2314_);
lean_dec_ref(v___x_2314_);
v___x_2316_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___closed__0));
v___x_2317_ = lean_string_append(v___x_2315_, v___x_2316_);
v___x_2318_ = ((size_t)1ULL);
v___x_2319_ = lean_usize_add(v_i_2309_, v___x_2318_);
v_i_2309_ = v___x_2319_;
v_b_2311_ = v___x_2317_;
goto _start;
}
else
{
return v_b_2311_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___boxed(lean_object* v_as_2321_, lean_object* v_i_2322_, lean_object* v_stop_2323_, lean_object* v_b_2324_){
_start:
{
size_t v_i_boxed_2325_; size_t v_stop_boxed_2326_; lean_object* v_res_2327_; 
v_i_boxed_2325_ = lean_unbox_usize(v_i_2322_);
lean_dec(v_i_2322_);
v_stop_boxed_2326_ = lean_unbox_usize(v_stop_2323_);
lean_dec(v_stop_2323_);
v_res_2327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_as_2321_, v_i_boxed_2325_, v_stop_boxed_2326_, v_b_2324_);
lean_dec_ref(v_as_2321_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString(lean_object* v_proof_2328_){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v___x_2329_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2330_ = lean_unsigned_to_nat(0u);
v___x_2331_ = lean_array_get_size(v_proof_2328_);
v___x_2332_ = lean_nat_dec_lt(v___x_2330_, v___x_2331_);
if (v___x_2332_ == 0)
{
return v___x_2329_;
}
else
{
uint8_t v___x_2333_; 
v___x_2333_ = lean_nat_dec_le(v___x_2331_, v___x_2331_);
if (v___x_2333_ == 0)
{
if (v___x_2332_ == 0)
{
return v___x_2329_;
}
else
{
size_t v___x_2334_; size_t v___x_2335_; lean_object* v___x_2336_; 
v___x_2334_ = ((size_t)0ULL);
v___x_2335_ = lean_usize_of_nat(v___x_2331_);
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_proof_2328_, v___x_2334_, v___x_2335_, v___x_2329_);
return v___x_2336_;
}
}
else
{
size_t v___x_2337_; size_t v___x_2338_; lean_object* v___x_2339_; 
v___x_2337_ = ((size_t)0ULL);
v___x_2338_ = lean_usize_of_nat(v___x_2331_);
v___x_2339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_proof_2328_, v___x_2337_, v___x_2338_, v___x_2329_);
return v___x_2339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString___boxed(lean_object* v_proof_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_proof_2340_);
lean_dec_ref(v_proof_2340_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startDelete(lean_object* v_acc_2342_){
_start:
{
uint8_t v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
v___x_2344_ = lean_byte_array_push(v_acc_2342_, v___x_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(lean_object* v_acc_2345_, uint64_t v_lit_2346_){
_start:
{
uint8_t v___y_2348_; uint64_t v___x_2353_; uint8_t v___x_2354_; 
v___x_2353_ = 0ULL;
v___x_2354_ = lean_uint64_dec_eq(v_lit_2346_, v___x_2353_);
if (v___x_2354_ == 0)
{
uint64_t v___x_2355_; uint8_t v___x_2356_; 
v___x_2355_ = 127ULL;
v___x_2356_ = lean_uint64_dec_lt(v___x_2355_, v_lit_2346_);
if (v___x_2356_ == 0)
{
uint8_t v___x_2357_; uint8_t v___x_2358_; uint8_t v___x_2359_; 
v___x_2357_ = lean_uint64_to_uint8(v_lit_2346_);
v___x_2358_ = 127;
v___x_2359_ = lean_uint8_land(v___x_2357_, v___x_2358_);
v___y_2348_ = v___x_2359_;
goto v___jp_2347_;
}
else
{
uint8_t v___x_2360_; uint8_t v___x_2361_; uint8_t v___x_2362_; uint8_t v___x_2363_; uint8_t v___x_2364_; 
v___x_2360_ = lean_uint64_to_uint8(v_lit_2346_);
v___x_2361_ = 127;
v___x_2362_ = lean_uint8_land(v___x_2360_, v___x_2361_);
v___x_2363_ = 128;
v___x_2364_ = lean_uint8_lor(v___x_2362_, v___x_2363_);
v___y_2348_ = v___x_2364_;
goto v___jp_2347_;
}
}
else
{
return v_acc_2345_;
}
v___jp_2347_:
{
lean_object* v_acc_2349_; uint64_t v___x_2350_; uint64_t v___x_2351_; 
v_acc_2349_ = lean_byte_array_push(v_acc_2345_, v___y_2348_);
v___x_2350_ = 7ULL;
v___x_2351_ = lean_uint64_shift_right(v_lit_2346_, v___x_2350_);
v_acc_2345_ = v_acc_2349_;
v_lit_2346_ = v___x_2351_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode___boxed(lean_object* v_acc_2365_, lean_object* v_lit_2366_){
_start:
{
uint64_t v_lit_boxed_2367_; lean_object* v_res_2368_; 
v_lit_boxed_2367_ = lean_unbox_uint64(v_lit_2366_);
lean_dec_ref(v_lit_2366_);
v_res_2368_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(v_acc_2365_, v_lit_boxed_2367_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(lean_object* v_msg_2369_){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = l_ByteArray_empty;
v___x_2371_ = lean_panic_fn_borrowed(v___x_2370_, v_msg_2369_);
return v___x_2371_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0(void){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = lean_cstr_to_nat("18446744073709551615");
return v___x_2372_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4(void){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2376_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3));
v___x_2377_ = lean_unsigned_to_nat(4u);
v___x_2378_ = lean_unsigned_to_nat(388u);
v___x_2379_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2));
v___x_2380_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1));
v___x_2381_ = l_mkPanicMessageWithDecl(v___x_2380_, v___x_2379_, v___x_2378_, v___x_2377_, v___x_2376_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(lean_object* v_acc_2382_, lean_object* v_lit_2383_){
_start:
{
lean_object* v___y_2385_; lean_object* v___x_2392_; uint8_t v___x_2393_; 
v___x_2392_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_2393_ = lean_int_dec_lt(v___x_2392_, v_lit_2383_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2394_ = lean_unsigned_to_nat(2u);
v___x_2395_ = lean_nat_abs(v_lit_2383_);
v___x_2396_ = lean_nat_mul(v___x_2394_, v___x_2395_);
lean_dec(v___x_2395_);
v___x_2397_ = lean_unsigned_to_nat(1u);
v___x_2398_ = lean_nat_add(v___x_2396_, v___x_2397_);
lean_dec(v___x_2396_);
v___y_2385_ = v___x_2398_;
goto v___jp_2384_;
}
else
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2399_ = lean_unsigned_to_nat(2u);
v___x_2400_ = lean_nat_abs(v_lit_2383_);
v___x_2401_ = lean_nat_mul(v___x_2399_, v___x_2400_);
lean_dec(v___x_2400_);
v___y_2385_ = v___x_2401_;
goto v___jp_2384_;
}
v___jp_2384_:
{
lean_object* v___x_2386_; uint8_t v___x_2387_; 
v___x_2386_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0);
v___x_2387_ = lean_nat_dec_le(v___y_2385_, v___x_2386_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
lean_dec(v___y_2385_);
lean_dec_ref(v_acc_2382_);
v___x_2388_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4);
v___x_2389_ = l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(v___x_2388_);
return v___x_2389_;
}
else
{
uint64_t v_mapped_2390_; lean_object* v___x_2391_; 
v_mapped_2390_ = lean_uint64_of_nat(v___y_2385_);
lean_dec(v___y_2385_);
v___x_2391_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(v_acc_2382_, v_mapped_2390_);
return v___x_2391_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___boxed(lean_object* v_acc_2402_, lean_object* v_lit_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2402_, v_lit_2403_);
lean_dec(v_lit_2403_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_zeroByte(lean_object* v_acc_2405_){
_start:
{
uint8_t v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = 0;
v___x_2407_ = lean_byte_array_push(v_acc_2405_, v___x_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addNat(lean_object* v_acc_2408_, lean_object* v_n_2409_){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = lean_nat_to_int(v_n_2409_);
v___x_2411_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2408_, v___x_2410_);
lean_dec(v___x_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startAdd(lean_object* v_acc_2412_){
_start:
{
uint8_t v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
v___x_2414_ = lean_byte_array_push(v_acc_2412_, v___x_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(lean_object* v_as_2415_, size_t v_i_2416_, size_t v_stop_2417_, lean_object* v_b_2418_){
_start:
{
uint8_t v___x_2419_; 
v___x_2419_ = lean_usize_dec_eq(v_i_2416_, v_stop_2417_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; size_t v___x_2423_; size_t v___x_2424_; 
v___x_2420_ = lean_array_uget_borrowed(v_as_2415_, v_i_2416_);
lean_inc(v___x_2420_);
v___x_2421_ = lean_nat_to_int(v___x_2420_);
v___x_2422_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2418_, v___x_2421_);
lean_dec(v___x_2421_);
v___x_2423_ = ((size_t)1ULL);
v___x_2424_ = lean_usize_add(v_i_2416_, v___x_2423_);
v_i_2416_ = v___x_2424_;
v_b_2418_ = v___x_2422_;
goto _start;
}
else
{
return v_b_2418_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0___boxed(lean_object* v_as_2426_, lean_object* v_i_2427_, lean_object* v_stop_2428_, lean_object* v_b_2429_){
_start:
{
size_t v_i_boxed_2430_; size_t v_stop_boxed_2431_; lean_object* v_res_2432_; 
v_i_boxed_2430_ = lean_unbox_usize(v_i_2427_);
lean_dec(v_i_2427_);
v_stop_boxed_2431_ = lean_unbox_usize(v_stop_2428_);
lean_dec(v_stop_2428_);
v_res_2432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(v_as_2426_, v_i_boxed_2430_, v_stop_boxed_2431_, v_b_2429_);
lean_dec_ref(v_as_2426_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(lean_object* v_as_2433_, size_t v_i_2434_, size_t v_stop_2435_, lean_object* v_b_2436_){
_start:
{
uint8_t v___x_2437_; 
v___x_2437_ = lean_usize_dec_eq(v_i_2434_, v_stop_2435_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; size_t v___x_2441_; size_t v___x_2442_; lean_object* v___x_2443_; 
v___x_2438_ = lean_array_uget_borrowed(v_as_2433_, v_i_2434_);
lean_inc(v___x_2438_);
v___x_2439_ = lean_nat_to_int(v___x_2438_);
v___x_2440_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2436_, v___x_2439_);
lean_dec(v___x_2439_);
v___x_2441_ = ((size_t)1ULL);
v___x_2442_ = lean_usize_add(v_i_2434_, v___x_2441_);
v___x_2443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(v_as_2433_, v___x_2442_, v_stop_2435_, v___x_2440_);
return v___x_2443_;
}
else
{
return v_b_2436_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0___boxed(lean_object* v_as_2444_, lean_object* v_i_2445_, lean_object* v_stop_2446_, lean_object* v_b_2447_){
_start:
{
size_t v_i_boxed_2448_; size_t v_stop_boxed_2449_; lean_object* v_res_2450_; 
v_i_boxed_2448_ = lean_unbox_usize(v_i_2445_);
lean_dec(v_i_2445_);
v_stop_boxed_2449_ = lean_unbox_usize(v_stop_2446_);
lean_dec(v_stop_2446_);
v_res_2450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_as_2444_, v_i_boxed_2448_, v_stop_boxed_2449_, v_b_2447_);
lean_dec_ref(v_as_2444_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(lean_object* v_as_2451_, size_t v_i_2452_, size_t v_stop_2453_, lean_object* v_b_2454_){
_start:
{
lean_object* v___y_2456_; uint8_t v___x_2460_; 
v___x_2460_ = lean_usize_dec_eq(v_i_2452_, v_stop_2453_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; lean_object* v_fst_2462_; lean_object* v_snd_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v_acc_2467_; lean_object* v___x_2468_; uint8_t v___x_2469_; 
v___x_2461_ = lean_array_uget_borrowed(v_as_2451_, v_i_2452_);
v_fst_2462_ = lean_ctor_get(v___x_2461_, 0);
v_snd_2463_ = lean_ctor_get(v___x_2461_, 1);
v___x_2464_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_2462_);
v___x_2465_ = lean_nat_to_int(v_fst_2462_);
v___x_2466_ = lean_int_neg(v___x_2465_);
lean_dec(v___x_2465_);
v_acc_2467_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2454_, v___x_2466_);
lean_dec(v___x_2466_);
v___x_2468_ = lean_array_get_size(v_snd_2463_);
v___x_2469_ = lean_nat_dec_lt(v___x_2464_, v___x_2468_);
if (v___x_2469_ == 0)
{
v___y_2456_ = v_acc_2467_;
goto v___jp_2455_;
}
else
{
uint8_t v___x_2470_; 
v___x_2470_ = lean_nat_dec_le(v___x_2468_, v___x_2468_);
if (v___x_2470_ == 0)
{
if (v___x_2469_ == 0)
{
v___y_2456_ = v_acc_2467_;
goto v___jp_2455_;
}
else
{
size_t v___x_2471_; size_t v___x_2472_; lean_object* v___x_2473_; 
v___x_2471_ = ((size_t)0ULL);
v___x_2472_ = lean_usize_of_nat(v___x_2468_);
v___x_2473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2463_, v___x_2471_, v___x_2472_, v_acc_2467_);
v___y_2456_ = v___x_2473_;
goto v___jp_2455_;
}
}
else
{
size_t v___x_2474_; size_t v___x_2475_; lean_object* v___x_2476_; 
v___x_2474_ = ((size_t)0ULL);
v___x_2475_ = lean_usize_of_nat(v___x_2468_);
v___x_2476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2463_, v___x_2474_, v___x_2475_, v_acc_2467_);
v___y_2456_ = v___x_2476_;
goto v___jp_2455_;
}
}
}
else
{
return v_b_2454_;
}
v___jp_2455_:
{
size_t v___x_2457_; size_t v___x_2458_; 
v___x_2457_ = ((size_t)1ULL);
v___x_2458_ = lean_usize_add(v_i_2452_, v___x_2457_);
v_i_2452_ = v___x_2458_;
v_b_2454_ = v___y_2456_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3___boxed(lean_object* v_as_2477_, lean_object* v_i_2478_, lean_object* v_stop_2479_, lean_object* v_b_2480_){
_start:
{
size_t v_i_boxed_2481_; size_t v_stop_boxed_2482_; lean_object* v_res_2483_; 
v_i_boxed_2481_ = lean_unbox_usize(v_i_2478_);
lean_dec(v_i_2478_);
v_stop_boxed_2482_ = lean_unbox_usize(v_stop_2479_);
lean_dec(v_stop_2479_);
v_res_2483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(v_as_2477_, v_i_boxed_2481_, v_stop_boxed_2482_, v_b_2480_);
lean_dec_ref(v_as_2477_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(lean_object* v_as_2484_, size_t v_i_2485_, size_t v_stop_2486_, lean_object* v_b_2487_){
_start:
{
lean_object* v___y_2489_; uint8_t v___x_2493_; 
v___x_2493_ = lean_usize_dec_eq(v_i_2485_, v_stop_2486_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; lean_object* v_fst_2495_; lean_object* v_snd_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v_acc_2500_; lean_object* v___x_2501_; uint8_t v___x_2502_; 
v___x_2494_ = lean_array_uget_borrowed(v_as_2484_, v_i_2485_);
v_fst_2495_ = lean_ctor_get(v___x_2494_, 0);
v_snd_2496_ = lean_ctor_get(v___x_2494_, 1);
v___x_2497_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_2495_);
v___x_2498_ = lean_nat_to_int(v_fst_2495_);
v___x_2499_ = lean_int_neg(v___x_2498_);
lean_dec(v___x_2498_);
v_acc_2500_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2487_, v___x_2499_);
lean_dec(v___x_2499_);
v___x_2501_ = lean_array_get_size(v_snd_2496_);
v___x_2502_ = lean_nat_dec_lt(v___x_2497_, v___x_2501_);
if (v___x_2502_ == 0)
{
v___y_2489_ = v_acc_2500_;
goto v___jp_2488_;
}
else
{
uint8_t v___x_2503_; 
v___x_2503_ = lean_nat_dec_le(v___x_2501_, v___x_2501_);
if (v___x_2503_ == 0)
{
if (v___x_2502_ == 0)
{
v___y_2489_ = v_acc_2500_;
goto v___jp_2488_;
}
else
{
size_t v___x_2504_; size_t v___x_2505_; lean_object* v___x_2506_; 
v___x_2504_ = ((size_t)0ULL);
v___x_2505_ = lean_usize_of_nat(v___x_2501_);
v___x_2506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2496_, v___x_2504_, v___x_2505_, v_acc_2500_);
v___y_2489_ = v___x_2506_;
goto v___jp_2488_;
}
}
else
{
size_t v___x_2507_; size_t v___x_2508_; lean_object* v___x_2509_; 
v___x_2507_ = ((size_t)0ULL);
v___x_2508_ = lean_usize_of_nat(v___x_2501_);
v___x_2509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2496_, v___x_2507_, v___x_2508_, v_acc_2500_);
v___y_2489_ = v___x_2509_;
goto v___jp_2488_;
}
}
}
else
{
return v_b_2487_;
}
v___jp_2488_:
{
size_t v___x_2490_; size_t v___x_2491_; lean_object* v___x_2492_; 
v___x_2490_ = ((size_t)1ULL);
v___x_2491_ = lean_usize_add(v_i_2485_, v___x_2490_);
v___x_2492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(v_as_2484_, v___x_2491_, v_stop_2486_, v___y_2489_);
return v___x_2492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2___boxed(lean_object* v_as_2510_, lean_object* v_i_2511_, lean_object* v_stop_2512_, lean_object* v_b_2513_){
_start:
{
size_t v_i_boxed_2514_; size_t v_stop_boxed_2515_; lean_object* v_res_2516_; 
v_i_boxed_2514_ = lean_unbox_usize(v_i_2511_);
lean_dec(v_i_2511_);
v_stop_boxed_2515_ = lean_unbox_usize(v_stop_2512_);
lean_dec(v_stop_2512_);
v_res_2516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_as_2510_, v_i_boxed_2514_, v_stop_boxed_2515_, v_b_2513_);
lean_dec_ref(v_as_2510_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(lean_object* v_as_2517_, size_t v_i_2518_, size_t v_stop_2519_, lean_object* v_b_2520_){
_start:
{
uint8_t v___x_2521_; 
v___x_2521_ = lean_usize_dec_eq(v_i_2518_, v_stop_2519_);
if (v___x_2521_ == 0)
{
lean_object* v___x_2522_; lean_object* v___x_2523_; size_t v___x_2524_; size_t v___x_2525_; 
v___x_2522_ = lean_array_uget_borrowed(v_as_2517_, v_i_2518_);
v___x_2523_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2520_, v___x_2522_);
v___x_2524_ = ((size_t)1ULL);
v___x_2525_ = lean_usize_add(v_i_2518_, v___x_2524_);
v_i_2518_ = v___x_2525_;
v_b_2520_ = v___x_2523_;
goto _start;
}
else
{
return v_b_2520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1___boxed(lean_object* v_as_2527_, lean_object* v_i_2528_, lean_object* v_stop_2529_, lean_object* v_b_2530_){
_start:
{
size_t v_i_boxed_2531_; size_t v_stop_boxed_2532_; lean_object* v_res_2533_; 
v_i_boxed_2531_ = lean_unbox_usize(v_i_2528_);
lean_dec(v_i_2528_);
v_stop_boxed_2532_ = lean_unbox_usize(v_stop_2529_);
lean_dec(v_stop_2529_);
v_res_2533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_as_2527_, v_i_boxed_2531_, v_stop_boxed_2532_, v_b_2530_);
lean_dec_ref(v_as_2527_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(lean_object* v_proof_2534_, lean_object* v_idx_2535_, lean_object* v_acc_2536_){
_start:
{
lean_object* v___y_2538_; lean_object* v___y_2543_; lean_object* v___y_2547_; lean_object* v___y_2551_; lean_object* v___y_2555_; lean_object* v___x_2558_; uint8_t v___x_2559_; 
v___x_2558_ = lean_array_get_size(v_proof_2534_);
v___x_2559_ = lean_nat_dec_lt(v_idx_2535_, v___x_2558_);
if (v___x_2559_ == 0)
{
lean_dec(v_idx_2535_);
return v_acc_2536_;
}
else
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_array_fget_borrowed(v_proof_2534_, v_idx_2535_);
switch(lean_obj_tag(v___x_2560_))
{
case 0:
{
lean_object* v_id_2561_; lean_object* v_rupHints_2562_; uint8_t v___x_2563_; lean_object* v_acc_2564_; lean_object* v___x_2565_; lean_object* v_acc_2566_; uint8_t v___x_2567_; lean_object* v_acc_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v_id_2561_ = lean_ctor_get(v___x_2560_, 0);
v_rupHints_2562_ = lean_ctor_get(v___x_2560_, 1);
v___x_2563_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
v_acc_2564_ = lean_byte_array_push(v_acc_2536_, v___x_2563_);
lean_inc(v_id_2561_);
v___x_2565_ = lean_nat_to_int(v_id_2561_);
v_acc_2566_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2564_, v___x_2565_);
lean_dec(v___x_2565_);
v___x_2567_ = 0;
v_acc_2568_ = lean_byte_array_push(v_acc_2566_, v___x_2567_);
v___x_2569_ = lean_unsigned_to_nat(0u);
v___x_2570_ = lean_array_get_size(v_rupHints_2562_);
v___x_2571_ = lean_nat_dec_lt(v___x_2569_, v___x_2570_);
if (v___x_2571_ == 0)
{
v___y_2547_ = v_acc_2568_;
goto v___jp_2546_;
}
else
{
uint8_t v___x_2572_; 
v___x_2572_ = lean_nat_dec_le(v___x_2570_, v___x_2570_);
if (v___x_2572_ == 0)
{
if (v___x_2571_ == 0)
{
v___y_2547_ = v_acc_2568_;
goto v___jp_2546_;
}
else
{
size_t v___x_2573_; size_t v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = ((size_t)0ULL);
v___x_2574_ = lean_usize_of_nat(v___x_2570_);
v___x_2575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2562_, v___x_2573_, v___x_2574_, v_acc_2568_);
v___y_2547_ = v___x_2575_;
goto v___jp_2546_;
}
}
else
{
size_t v___x_2576_; size_t v___x_2577_; lean_object* v___x_2578_; 
v___x_2576_ = ((size_t)0ULL);
v___x_2577_ = lean_usize_of_nat(v___x_2570_);
v___x_2578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2562_, v___x_2576_, v___x_2577_, v_acc_2568_);
v___y_2547_ = v___x_2578_;
goto v___jp_2546_;
}
}
}
case 1:
{
lean_object* v_id_2579_; lean_object* v_c_2580_; lean_object* v_rupHints_2581_; uint8_t v___x_2582_; lean_object* v_acc_2583_; lean_object* v___x_2584_; lean_object* v_acc_2585_; lean_object* v___x_2586_; lean_object* v___y_2588_; lean_object* v___x_2600_; uint8_t v___x_2601_; 
v_id_2579_ = lean_ctor_get(v___x_2560_, 0);
v_c_2580_ = lean_ctor_get(v___x_2560_, 1);
v_rupHints_2581_ = lean_ctor_get(v___x_2560_, 2);
v___x_2582_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
v_acc_2583_ = lean_byte_array_push(v_acc_2536_, v___x_2582_);
lean_inc(v_id_2579_);
v___x_2584_ = lean_nat_to_int(v_id_2579_);
v_acc_2585_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2583_, v___x_2584_);
lean_dec(v___x_2584_);
v___x_2586_ = lean_unsigned_to_nat(0u);
v___x_2600_ = lean_array_get_size(v_c_2580_);
v___x_2601_ = lean_nat_dec_lt(v___x_2586_, v___x_2600_);
if (v___x_2601_ == 0)
{
v___y_2588_ = v_acc_2585_;
goto v___jp_2587_;
}
else
{
uint8_t v___x_2602_; 
v___x_2602_ = lean_nat_dec_le(v___x_2600_, v___x_2600_);
if (v___x_2602_ == 0)
{
if (v___x_2601_ == 0)
{
v___y_2588_ = v_acc_2585_;
goto v___jp_2587_;
}
else
{
size_t v___x_2603_; size_t v___x_2604_; lean_object* v___x_2605_; 
v___x_2603_ = ((size_t)0ULL);
v___x_2604_ = lean_usize_of_nat(v___x_2600_);
v___x_2605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2580_, v___x_2603_, v___x_2604_, v_acc_2585_);
v___y_2588_ = v___x_2605_;
goto v___jp_2587_;
}
}
else
{
size_t v___x_2606_; size_t v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = ((size_t)0ULL);
v___x_2607_ = lean_usize_of_nat(v___x_2600_);
v___x_2608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2580_, v___x_2606_, v___x_2607_, v_acc_2585_);
v___y_2588_ = v___x_2608_;
goto v___jp_2587_;
}
}
v___jp_2587_:
{
uint8_t v___x_2589_; lean_object* v_acc_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; 
v___x_2589_ = 0;
v_acc_2590_ = lean_byte_array_push(v___y_2588_, v___x_2589_);
v___x_2591_ = lean_array_get_size(v_rupHints_2581_);
v___x_2592_ = lean_nat_dec_lt(v___x_2586_, v___x_2591_);
if (v___x_2592_ == 0)
{
v___y_2551_ = v_acc_2590_;
goto v___jp_2550_;
}
else
{
uint8_t v___x_2593_; 
v___x_2593_ = lean_nat_dec_le(v___x_2591_, v___x_2591_);
if (v___x_2593_ == 0)
{
if (v___x_2592_ == 0)
{
v___y_2551_ = v_acc_2590_;
goto v___jp_2550_;
}
else
{
size_t v___x_2594_; size_t v___x_2595_; lean_object* v___x_2596_; 
v___x_2594_ = ((size_t)0ULL);
v___x_2595_ = lean_usize_of_nat(v___x_2591_);
v___x_2596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2581_, v___x_2594_, v___x_2595_, v_acc_2590_);
v___y_2551_ = v___x_2596_;
goto v___jp_2550_;
}
}
else
{
size_t v___x_2597_; size_t v___x_2598_; lean_object* v___x_2599_; 
v___x_2597_ = ((size_t)0ULL);
v___x_2598_ = lean_usize_of_nat(v___x_2591_);
v___x_2599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2581_, v___x_2597_, v___x_2598_, v_acc_2590_);
v___y_2551_ = v___x_2599_;
goto v___jp_2550_;
}
}
}
}
case 2:
{
lean_object* v_id_2609_; lean_object* v_c_2610_; lean_object* v_rupHints_2611_; lean_object* v_ratHints_2612_; uint8_t v___x_2613_; lean_object* v_acc_2614_; lean_object* v___x_2615_; lean_object* v_acc_2616_; lean_object* v___x_2617_; lean_object* v___y_2619_; lean_object* v___y_2630_; lean_object* v___x_2642_; uint8_t v___x_2643_; 
v_id_2609_ = lean_ctor_get(v___x_2560_, 0);
v_c_2610_ = lean_ctor_get(v___x_2560_, 1);
v_rupHints_2611_ = lean_ctor_get(v___x_2560_, 3);
v_ratHints_2612_ = lean_ctor_get(v___x_2560_, 4);
v___x_2613_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
v_acc_2614_ = lean_byte_array_push(v_acc_2536_, v___x_2613_);
lean_inc(v_id_2609_);
v___x_2615_ = lean_nat_to_int(v_id_2609_);
v_acc_2616_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2614_, v___x_2615_);
lean_dec(v___x_2615_);
v___x_2617_ = lean_unsigned_to_nat(0u);
v___x_2642_ = lean_array_get_size(v_c_2610_);
v___x_2643_ = lean_nat_dec_lt(v___x_2617_, v___x_2642_);
if (v___x_2643_ == 0)
{
v___y_2630_ = v_acc_2616_;
goto v___jp_2629_;
}
else
{
uint8_t v___x_2644_; 
v___x_2644_ = lean_nat_dec_le(v___x_2642_, v___x_2642_);
if (v___x_2644_ == 0)
{
if (v___x_2643_ == 0)
{
v___y_2630_ = v_acc_2616_;
goto v___jp_2629_;
}
else
{
size_t v___x_2645_; size_t v___x_2646_; lean_object* v___x_2647_; 
v___x_2645_ = ((size_t)0ULL);
v___x_2646_ = lean_usize_of_nat(v___x_2642_);
v___x_2647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2610_, v___x_2645_, v___x_2646_, v_acc_2616_);
v___y_2630_ = v___x_2647_;
goto v___jp_2629_;
}
}
else
{
size_t v___x_2648_; size_t v___x_2649_; lean_object* v___x_2650_; 
v___x_2648_ = ((size_t)0ULL);
v___x_2649_ = lean_usize_of_nat(v___x_2642_);
v___x_2650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2610_, v___x_2648_, v___x_2649_, v_acc_2616_);
v___y_2630_ = v___x_2650_;
goto v___jp_2629_;
}
}
v___jp_2618_:
{
lean_object* v___x_2620_; uint8_t v___x_2621_; 
v___x_2620_ = lean_array_get_size(v_ratHints_2612_);
v___x_2621_ = lean_nat_dec_lt(v___x_2617_, v___x_2620_);
if (v___x_2621_ == 0)
{
v___y_2543_ = v___y_2619_;
goto v___jp_2542_;
}
else
{
uint8_t v___x_2622_; 
v___x_2622_ = lean_nat_dec_le(v___x_2620_, v___x_2620_);
if (v___x_2622_ == 0)
{
if (v___x_2621_ == 0)
{
v___y_2543_ = v___y_2619_;
goto v___jp_2542_;
}
else
{
size_t v___x_2623_; size_t v___x_2624_; lean_object* v___x_2625_; 
v___x_2623_ = ((size_t)0ULL);
v___x_2624_ = lean_usize_of_nat(v___x_2620_);
v___x_2625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_ratHints_2612_, v___x_2623_, v___x_2624_, v___y_2619_);
v___y_2543_ = v___x_2625_;
goto v___jp_2542_;
}
}
else
{
size_t v___x_2626_; size_t v___x_2627_; lean_object* v___x_2628_; 
v___x_2626_ = ((size_t)0ULL);
v___x_2627_ = lean_usize_of_nat(v___x_2620_);
v___x_2628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_ratHints_2612_, v___x_2626_, v___x_2627_, v___y_2619_);
v___y_2543_ = v___x_2628_;
goto v___jp_2542_;
}
}
}
v___jp_2629_:
{
uint8_t v___x_2631_; lean_object* v_acc_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___x_2631_ = 0;
v_acc_2632_ = lean_byte_array_push(v___y_2630_, v___x_2631_);
v___x_2633_ = lean_array_get_size(v_rupHints_2611_);
v___x_2634_ = lean_nat_dec_lt(v___x_2617_, v___x_2633_);
if (v___x_2634_ == 0)
{
v___y_2619_ = v_acc_2632_;
goto v___jp_2618_;
}
else
{
uint8_t v___x_2635_; 
v___x_2635_ = lean_nat_dec_le(v___x_2633_, v___x_2633_);
if (v___x_2635_ == 0)
{
if (v___x_2634_ == 0)
{
v___y_2619_ = v_acc_2632_;
goto v___jp_2618_;
}
else
{
size_t v___x_2636_; size_t v___x_2637_; lean_object* v___x_2638_; 
v___x_2636_ = ((size_t)0ULL);
v___x_2637_ = lean_usize_of_nat(v___x_2633_);
v___x_2638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2611_, v___x_2636_, v___x_2637_, v_acc_2632_);
v___y_2619_ = v___x_2638_;
goto v___jp_2618_;
}
}
else
{
size_t v___x_2639_; size_t v___x_2640_; lean_object* v___x_2641_; 
v___x_2639_ = ((size_t)0ULL);
v___x_2640_ = lean_usize_of_nat(v___x_2633_);
v___x_2641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2611_, v___x_2639_, v___x_2640_, v_acc_2632_);
v___y_2619_ = v___x_2641_;
goto v___jp_2618_;
}
}
}
}
default: 
{
lean_object* v_ids_2651_; uint8_t v___x_2652_; lean_object* v_acc_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; 
v_ids_2651_ = lean_ctor_get(v___x_2560_, 0);
v___x_2652_ = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
v_acc_2653_ = lean_byte_array_push(v_acc_2536_, v___x_2652_);
v___x_2654_ = lean_unsigned_to_nat(0u);
v___x_2655_ = lean_array_get_size(v_ids_2651_);
v___x_2656_ = lean_nat_dec_lt(v___x_2654_, v___x_2655_);
if (v___x_2656_ == 0)
{
v___y_2555_ = v_acc_2653_;
goto v___jp_2554_;
}
else
{
uint8_t v___x_2657_; 
v___x_2657_ = lean_nat_dec_le(v___x_2655_, v___x_2655_);
if (v___x_2657_ == 0)
{
if (v___x_2656_ == 0)
{
v___y_2555_ = v_acc_2653_;
goto v___jp_2554_;
}
else
{
size_t v___x_2658_; size_t v___x_2659_; lean_object* v___x_2660_; 
v___x_2658_ = ((size_t)0ULL);
v___x_2659_ = lean_usize_of_nat(v___x_2655_);
v___x_2660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_ids_2651_, v___x_2658_, v___x_2659_, v_acc_2653_);
v___y_2555_ = v___x_2660_;
goto v___jp_2554_;
}
}
else
{
size_t v___x_2661_; size_t v___x_2662_; lean_object* v___x_2663_; 
v___x_2661_ = ((size_t)0ULL);
v___x_2662_ = lean_usize_of_nat(v___x_2655_);
v___x_2663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_ids_2651_, v___x_2661_, v___x_2662_, v_acc_2653_);
v___y_2555_ = v___x_2663_;
goto v___jp_2554_;
}
}
}
}
}
v___jp_2537_:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = lean_unsigned_to_nat(1u);
v___x_2540_ = lean_nat_add(v_idx_2535_, v___x_2539_);
lean_dec(v_idx_2535_);
v_idx_2535_ = v___x_2540_;
v_acc_2536_ = v___y_2538_;
goto _start;
}
v___jp_2542_:
{
uint8_t v___x_2544_; lean_object* v_acc_2545_; 
v___x_2544_ = 0;
v_acc_2545_ = lean_byte_array_push(v___y_2543_, v___x_2544_);
v___y_2538_ = v_acc_2545_;
goto v___jp_2537_;
}
v___jp_2546_:
{
uint8_t v___x_2548_; lean_object* v_acc_2549_; 
v___x_2548_ = 0;
v_acc_2549_ = lean_byte_array_push(v___y_2547_, v___x_2548_);
v___y_2538_ = v_acc_2549_;
goto v___jp_2537_;
}
v___jp_2550_:
{
uint8_t v___x_2552_; lean_object* v_acc_2553_; 
v___x_2552_ = 0;
v_acc_2553_ = lean_byte_array_push(v___y_2551_, v___x_2552_);
v___y_2538_ = v_acc_2553_;
goto v___jp_2537_;
}
v___jp_2554_:
{
uint8_t v___x_2556_; lean_object* v_acc_2557_; 
v___x_2556_ = 0;
v_acc_2557_ = lean_byte_array_push(v___y_2555_, v___x_2556_);
v___y_2538_ = v_acc_2557_;
goto v___jp_2537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___boxed(lean_object* v_proof_2664_, lean_object* v_idx_2665_, lean_object* v_acc_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(v_proof_2664_, v_idx_2665_, v_acc_2666_);
lean_dec_ref(v_proof_2664_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(lean_object* v_proof_2668_){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2669_ = lean_unsigned_to_nat(0u);
v___x_2670_ = lean_unsigned_to_nat(4u);
v___x_2671_ = lean_array_get_size(v_proof_2668_);
v___x_2672_ = lean_nat_mul(v___x_2670_, v___x_2671_);
v___x_2673_ = lean_mk_empty_byte_array(v___x_2672_);
lean_dec(v___x_2672_);
v___x_2674_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(v_proof_2668_, v___x_2669_, v___x_2673_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary___boxed(lean_object* v_proof_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(v_proof_2675_);
lean_dec_ref(v_proof_2675_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object* v_path_2677_, lean_object* v_proof_2678_, uint8_t v_binaryProofs_2679_){
_start:
{
if (v_binaryProofs_2679_ == 0)
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2681_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_proof_2678_);
v___x_2682_ = lean_string_to_utf8(v___x_2681_);
lean_dec_ref(v___x_2681_);
v___x_2683_ = l_IO_FS_writeBinFile(v_path_2677_, v___x_2682_);
lean_dec_ref(v___x_2682_);
return v___x_2683_;
}
else
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2684_ = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(v_proof_2678_);
v___x_2685_ = l_IO_FS_writeBinFile(v_path_2677_, v___x_2684_);
lean_dec_ref(v___x_2684_);
return v___x_2685_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof___boxed(lean_object* v_path_2686_, lean_object* v_proof_2687_, lean_object* v_binaryProofs_2688_, lean_object* v_a_2689_){
_start:
{
uint8_t v_binaryProofs_boxed_2690_; lean_object* v_res_2691_; 
v_binaryProofs_boxed_2690_ = lean_unbox(v_binaryProofs_2688_);
v_res_2691_ = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(v_path_2686_, v_proof_2687_, v_binaryProofs_boxed_2690_);
lean_dec_ref(v_proof_2687_);
lean_dec_ref(v_path_2686_);
return v_res_2691_;
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
