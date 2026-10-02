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
uint8_t lean_uint32_to_uint8(uint32_t);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
lean_object* lean_uint8_to_nat(uint8_t);
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
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '10'"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline(lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "digit expected"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__0_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "id was 0"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos(lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '45'"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseId(lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '48'"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero(lean_object*);
static const lean_string_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "expected: '32'"};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_value;
static const lean_ctor_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_value)}};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_spec__0(lean_object*, lean_object*);
static const lean_array_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "expected: '100'"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1_value;
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(lean_object*, lean_object*);
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
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Expected a or d got: "};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_value;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline(lean_object* v_a_20_){
_start:
{
lean_object* v_array_21_; lean_object* v_idx_22_; lean_object* v___y_24_; lean_object* v_pos_25_; lean_object* v_idx_26_; lean_object* v___x_40_; uint8_t v___x_41_; 
v_array_21_ = lean_ctor_get(v_a_20_, 0);
v_idx_22_ = lean_ctor_get(v_a_20_, 1);
lean_inc(v_idx_22_);
v___x_40_ = lean_byte_array_size(v_array_21_);
v___x_41_ = lean_nat_dec_lt(v_idx_22_, v___x_40_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_box(0);
lean_inc_ref(v_a_20_);
v___x_43_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_43_, 0, v_a_20_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
lean_inc(v_idx_22_);
v___y_24_ = v___x_43_;
v_pos_25_ = v_a_20_;
v_idx_26_ = v_idx_22_;
goto v___jp_23_;
}
else
{
uint8_t v___x_44_; uint8_t v_got_45_; uint8_t v___x_46_; 
v___x_44_ = 10;
v_got_45_ = lean_byte_array_fget(v_array_21_, v_idx_22_);
v___x_46_ = lean_uint8_dec_eq(v_got_45_, v___x_44_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
lean_inc_ref(v_a_20_);
v___x_48_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_48_, 0, v_a_20_);
lean_ctor_set(v___x_48_, 1, v___x_47_);
lean_inc(v_idx_22_);
v___y_24_ = v___x_48_;
v_pos_25_ = v_a_20_;
v_idx_26_ = v_idx_22_;
goto v___jp_23_;
}
else
{
lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_59_; 
lean_inc_ref(v_array_21_);
v_isSharedCheck_59_ = !lean_is_exclusive(v_a_20_);
if (v_isSharedCheck_59_ == 0)
{
lean_object* v_unused_60_; lean_object* v_unused_61_; 
v_unused_60_ = lean_ctor_get(v_a_20_, 1);
lean_dec(v_unused_60_);
v_unused_61_ = lean_ctor_get(v_a_20_, 0);
lean_dec(v_unused_61_);
v___x_50_ = v_a_20_;
v_isShared_51_ = v_isSharedCheck_59_;
goto v_resetjp_49_;
}
else
{
lean_dec(v_a_20_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_59_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_55_; 
v___x_52_ = lean_unsigned_to_nat(1u);
v___x_53_ = lean_nat_add(v_idx_22_, v___x_52_);
lean_dec(v_idx_22_);
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 1, v___x_53_);
v___x_55_ = v___x_50_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_array_21_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v___x_53_);
v___x_55_ = v_reuseFailAlloc_58_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_box(0);
v___x_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
return v___x_57_;
}
}
}
}
v___jp_23_:
{
uint8_t v___x_27_; 
v___x_27_ = lean_nat_dec_eq(v_idx_22_, v_idx_26_);
lean_dec(v_idx_26_);
lean_dec(v_idx_22_);
if (v___x_27_ == 0)
{
lean_dec_ref(v_pos_25_);
return v___y_24_;
}
else
{
lean_object* v_utf8_28_; lean_object* v___x_29_; 
lean_dec_ref(v___y_24_);
v_utf8_28_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1);
v___x_29_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_28_, v_pos_25_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_pos_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_38_; 
v_pos_30_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_38_ == 0)
{
lean_object* v_unused_39_; 
v_unused_39_ = lean_ctor_get(v___x_29_, 1);
lean_dec(v_unused_39_);
v___x_32_ = v___x_29_;
v_isShared_33_ = v_isSharedCheck_38_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_pos_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_38_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_34_; lean_object* v___x_36_; 
v___x_34_ = lean_box(0);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 1, v___x_34_);
v___x_36_ = v___x_32_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_pos_30_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v___x_34_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
else
{
return v___x_29_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos(lean_object* v_a_68_){
_start:
{
lean_object* v_array_69_; lean_object* v_idx_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v_array_69_ = lean_ctor_get(v_a_68_, 0);
v_idx_70_ = lean_ctor_get(v_a_68_, 1);
v___x_71_ = lean_byte_array_size(v_array_69_);
v___x_72_ = lean_nat_dec_lt(v_idx_70_, v___x_71_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_box(0);
v___x_74_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_74_, 0, v_a_68_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
return v___x_74_;
}
else
{
uint8_t v_c_75_; uint8_t v___x_76_; uint8_t v___y_78_; uint8_t v___x_112_; 
v_c_75_ = lean_byte_array_fget(v_array_69_, v_idx_70_);
v___x_76_ = 48;
v___x_112_ = lean_uint8_dec_le(v___x_76_, v_c_75_);
if (v___x_112_ == 0)
{
v___y_78_ = v___x_112_;
goto v___jp_77_;
}
else
{
uint8_t v___x_113_; uint8_t v___x_114_; 
v___x_113_ = 57;
v___x_114_ = lean_uint8_dec_le(v_c_75_, v___x_113_);
v___y_78_ = v___x_114_;
goto v___jp_77_;
}
v___jp_77_:
{
if (v___y_78_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_80_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_80_, 0, v_a_68_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
return v___x_80_;
}
else
{
lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_109_; 
lean_inc(v_idx_70_);
lean_inc_ref(v_array_69_);
v_isSharedCheck_109_ = !lean_is_exclusive(v_a_68_);
if (v_isSharedCheck_109_ == 0)
{
lean_object* v_unused_110_; lean_object* v_unused_111_; 
v_unused_110_ = lean_ctor_get(v_a_68_, 1);
lean_dec(v_unused_110_);
v_unused_111_ = lean_ctor_get(v_a_68_, 0);
lean_dec(v_unused_111_);
v___x_82_ = v_a_68_;
v_isShared_83_ = v_isSharedCheck_109_;
goto v_resetjp_81_;
}
else
{
lean_dec(v_a_68_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_109_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v_it_x27_87_; 
v___x_84_ = lean_unsigned_to_nat(1u);
v___x_85_ = lean_nat_add(v_idx_70_, v___x_84_);
lean_dec(v_idx_70_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 1, v___x_85_);
v_it_x27_87_ = v___x_82_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_array_69_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v___x_85_);
v_it_x27_87_ = v_reuseFailAlloc_108_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
uint32_t v___x_88_; uint8_t v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v_fst_93_; lean_object* v_snd_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_107_; 
v___x_88_ = lean_uint8_to_uint32(v_c_75_);
v___x_89_ = lean_uint32_to_uint8(v___x_88_);
v___x_90_ = lean_uint8_sub(v___x_89_, v___x_76_);
v___x_91_ = lean_uint8_to_nat(v___x_90_);
v___x_92_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_87_, v___x_91_);
v_fst_93_ = lean_ctor_get(v___x_92_, 0);
v_snd_94_ = lean_ctor_get(v___x_92_, 1);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_107_ == 0)
{
v___x_96_ = v___x_92_;
v_isShared_97_ = v_isSharedCheck_107_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_snd_94_);
lean_inc(v_fst_93_);
lean_dec(v___x_92_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_107_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_nat_dec_eq(v_fst_93_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_101_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 1, v_fst_93_);
lean_ctor_set(v___x_96_, 0, v_snd_94_);
v___x_101_ = v___x_96_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_snd_94_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_fst_93_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
else
{
lean_object* v___x_103_; lean_object* v___x_105_; 
lean_dec(v_fst_93_);
v___x_103_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_97_ == 0)
{
lean_ctor_set_tag(v___x_96_, 1);
lean_ctor_set(v___x_96_, 1, v___x_103_);
lean_ctor_set(v___x_96_, 0, v_snd_94_);
v___x_105_ = v___x_96_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_snd_94_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg(lean_object* v_a_118_){
_start:
{
lean_object* v_array_119_; lean_object* v_idx_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v_array_119_ = lean_ctor_get(v_a_118_, 0);
v_idx_120_ = lean_ctor_get(v_a_118_, 1);
v___x_121_ = lean_byte_array_size(v_array_119_);
v___x_122_ = lean_nat_dec_lt(v_idx_120_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_box(0);
v___x_124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_124_, 0, v_a_118_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
return v___x_124_;
}
else
{
uint8_t v___x_125_; uint8_t v_got_126_; uint8_t v___x_127_; 
v___x_125_ = 45;
v_got_126_ = lean_byte_array_fget(v_array_119_, v_idx_120_);
v___x_127_ = lean_uint8_dec_eq(v_got_126_, v___x_125_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1));
v___x_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_129_, 0, v_a_118_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
return v___x_129_;
}
else
{
lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_174_; 
lean_inc(v_idx_120_);
lean_inc_ref(v_array_119_);
v_isSharedCheck_174_ = !lean_is_exclusive(v_a_118_);
if (v_isSharedCheck_174_ == 0)
{
lean_object* v_unused_175_; lean_object* v_unused_176_; 
v_unused_175_ = lean_ctor_get(v_a_118_, 1);
lean_dec(v_unused_175_);
v_unused_176_ = lean_ctor_get(v_a_118_, 0);
lean_dec(v_unused_176_);
v___x_131_ = v_a_118_;
v_isShared_132_ = v_isSharedCheck_174_;
goto v_resetjp_130_;
}
else
{
lean_dec(v_a_118_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_174_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_133_ = lean_unsigned_to_nat(1u);
v___x_134_ = lean_nat_add(v_idx_120_, v___x_133_);
lean_dec(v_idx_120_);
lean_inc(v___x_134_);
lean_inc_ref(v_array_119_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v___x_134_);
v___x_136_ = v___x_131_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_array_119_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v___x_134_);
v___x_136_ = v_reuseFailAlloc_173_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
uint8_t v___x_137_; 
v___x_137_ = lean_nat_dec_lt(v___x_134_, v___x_121_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec(v___x_134_);
lean_dec_ref(v_array_119_);
v___x_138_ = lean_box(0);
v___x_139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_136_);
lean_ctor_set(v___x_139_, 1, v___x_138_);
return v___x_139_;
}
else
{
uint8_t v_c_140_; uint8_t v___x_141_; uint8_t v___y_143_; uint8_t v___x_170_; 
v_c_140_ = lean_byte_array_fget(v_array_119_, v___x_134_);
v___x_141_ = 48;
v___x_170_ = lean_uint8_dec_le(v___x_141_, v_c_140_);
if (v___x_170_ == 0)
{
v___y_143_ = v___x_170_;
goto v___jp_142_;
}
else
{
uint8_t v___x_171_; uint8_t v___x_172_; 
v___x_171_ = 57;
v___x_172_ = lean_uint8_dec_le(v_c_140_, v___x_171_);
v___y_143_ = v___x_172_;
goto v___jp_142_;
}
v___jp_142_:
{
if (v___y_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v___x_134_);
lean_dec_ref(v_array_119_);
v___x_144_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_136_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
return v___x_145_;
}
else
{
lean_object* v___x_146_; lean_object* v_it_x27_147_; uint32_t v___x_148_; uint8_t v___x_149_; uint8_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v_fst_153_; lean_object* v_snd_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_169_; 
lean_dec_ref(v___x_136_);
v___x_146_ = lean_nat_add(v___x_134_, v___x_133_);
lean_dec(v___x_134_);
v_it_x27_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_147_, 0, v_array_119_);
lean_ctor_set(v_it_x27_147_, 1, v___x_146_);
v___x_148_ = lean_uint8_to_uint32(v_c_140_);
v___x_149_ = lean_uint32_to_uint8(v___x_148_);
v___x_150_ = lean_uint8_sub(v___x_149_, v___x_141_);
v___x_151_ = lean_uint8_to_nat(v___x_150_);
v___x_152_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_147_, v___x_151_);
v_fst_153_ = lean_ctor_get(v___x_152_, 0);
v_snd_154_ = lean_ctor_get(v___x_152_, 1);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_169_ == 0)
{
v___x_156_ = v___x_152_;
v_isShared_157_ = v_isSharedCheck_169_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_snd_154_);
lean_inc(v_fst_153_);
lean_dec(v___x_152_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_169_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_nat_dec_eq(v_fst_153_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_160_ = lean_nat_to_int(v_fst_153_);
v___x_161_ = lean_int_neg(v___x_160_);
lean_dec(v___x_160_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v___x_161_);
lean_ctor_set(v___x_156_, 0, v_snd_154_);
v___x_163_ = v___x_156_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_snd_154_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v___x_161_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
else
{
lean_object* v___x_165_; lean_object* v___x_167_; 
lean_dec(v_fst_153_);
v___x_165_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_157_ == 0)
{
lean_ctor_set_tag(v___x_156_, 1);
lean_ctor_set(v___x_156_, 1, v___x_165_);
lean_ctor_set(v___x_156_, 0, v_snd_154_);
v___x_167_ = v___x_156_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_snd_154_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseId(lean_object* v_a_177_){
_start:
{
lean_object* v_array_178_; lean_object* v_idx_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v_array_178_ = lean_ctor_get(v_a_177_, 0);
v_idx_179_ = lean_ctor_get(v_a_177_, 1);
v___x_180_ = lean_byte_array_size(v_array_178_);
v___x_181_ = lean_nat_dec_lt(v_idx_179_, v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_box(0);
v___x_183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_183_, 0, v_a_177_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
return v___x_183_;
}
else
{
uint8_t v_c_184_; uint8_t v___x_185_; uint8_t v___y_187_; uint8_t v___x_221_; 
v_c_184_ = lean_byte_array_fget(v_array_178_, v_idx_179_);
v___x_185_ = 48;
v___x_221_ = lean_uint8_dec_le(v___x_185_, v_c_184_);
if (v___x_221_ == 0)
{
v___y_187_ = v___x_221_;
goto v___jp_186_;
}
else
{
uint8_t v___x_222_; uint8_t v___x_223_; 
v___x_222_ = 57;
v___x_223_ = lean_uint8_dec_le(v_c_184_, v___x_222_);
v___y_187_ = v___x_223_;
goto v___jp_186_;
}
v___jp_186_:
{
if (v___y_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_189_, 0, v_a_177_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
return v___x_189_;
}
else
{
lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_218_; 
lean_inc(v_idx_179_);
lean_inc_ref(v_array_178_);
v_isSharedCheck_218_ = !lean_is_exclusive(v_a_177_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; lean_object* v_unused_220_; 
v_unused_219_ = lean_ctor_get(v_a_177_, 1);
lean_dec(v_unused_219_);
v_unused_220_ = lean_ctor_get(v_a_177_, 0);
lean_dec(v_unused_220_);
v___x_191_ = v_a_177_;
v_isShared_192_ = v_isSharedCheck_218_;
goto v_resetjp_190_;
}
else
{
lean_dec(v_a_177_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_218_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v_it_x27_196_; 
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = lean_nat_add(v_idx_179_, v___x_193_);
lean_dec(v_idx_179_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v___x_194_);
v_it_x27_196_ = v___x_191_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_array_178_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v___x_194_);
v_it_x27_196_ = v_reuseFailAlloc_217_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
uint32_t v___x_197_; uint8_t v___x_198_; uint8_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_fst_202_; lean_object* v_snd_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_216_; 
v___x_197_ = lean_uint8_to_uint32(v_c_184_);
v___x_198_ = lean_uint32_to_uint8(v___x_197_);
v___x_199_ = lean_uint8_sub(v___x_198_, v___x_185_);
v___x_200_ = lean_uint8_to_nat(v___x_199_);
v___x_201_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_196_, v___x_200_);
v_fst_202_ = lean_ctor_get(v___x_201_, 0);
v_snd_203_ = lean_ctor_get(v___x_201_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_216_ == 0)
{
v___x_205_ = v___x_201_;
v_isShared_206_ = v_isSharedCheck_216_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_snd_203_);
lean_inc(v_fst_202_);
lean_dec(v___x_201_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_216_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = lean_unsigned_to_nat(0u);
v___x_208_ = lean_nat_dec_eq(v_fst_202_, v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_210_; 
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v_fst_202_);
lean_ctor_set(v___x_205_, 0, v_snd_203_);
v___x_210_ = v___x_205_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_snd_203_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_fst_202_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
else
{
lean_object* v___x_212_; lean_object* v___x_214_; 
lean_dec(v_fst_202_);
v___x_212_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_206_ == 0)
{
lean_ctor_set_tag(v___x_205_, 1);
lean_ctor_set(v___x_205_, 1, v___x_212_);
lean_ctor_set(v___x_205_, 0, v_snd_203_);
v___x_214_ = v___x_205_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_snd_203_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero(lean_object* v_a_227_){
_start:
{
lean_object* v_array_228_; lean_object* v_idx_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v_array_228_ = lean_ctor_get(v_a_227_, 0);
v_idx_229_ = lean_ctor_get(v_a_227_, 1);
v___x_230_ = lean_byte_array_size(v_array_228_);
v___x_231_ = lean_nat_dec_lt(v_idx_229_, v___x_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_box(0);
v___x_233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_233_, 0, v_a_227_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
return v___x_233_;
}
else
{
uint8_t v___x_234_; uint8_t v_got_235_; uint8_t v___x_236_; 
v___x_234_ = 48;
v_got_235_ = lean_byte_array_fget(v_array_228_, v_idx_229_);
v___x_236_ = lean_uint8_dec_eq(v_got_235_, v___x_234_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1));
v___x_238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_238_, 0, v_a_227_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
return v___x_238_;
}
else
{
lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_249_; 
lean_inc(v_idx_229_);
lean_inc_ref(v_array_228_);
v_isSharedCheck_249_ = !lean_is_exclusive(v_a_227_);
if (v_isSharedCheck_249_ == 0)
{
lean_object* v_unused_250_; lean_object* v_unused_251_; 
v_unused_250_ = lean_ctor_get(v_a_227_, 1);
lean_dec(v_unused_250_);
v_unused_251_ = lean_ctor_get(v_a_227_, 0);
lean_dec(v_unused_251_);
v___x_240_ = v_a_227_;
v_isShared_241_ = v_isSharedCheck_249_;
goto v_resetjp_239_;
}
else
{
lean_dec(v_a_227_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_249_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_nat_add(v_idx_229_, v___x_242_);
lean_dec(v_idx_229_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v___x_243_);
v___x_245_ = v___x_240_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_array_228_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___x_243_);
v___x_245_ = v_reuseFailAlloc_248_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_box(0);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
return v___x_247_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs(lean_object* v_a_255_){
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
uint8_t v_c_262_; uint8_t v___x_263_; uint8_t v___y_265_; uint8_t v___x_316_; 
v_c_262_ = lean_byte_array_fget(v_array_256_, v_idx_257_);
v___x_263_ = 48;
v___x_316_ = lean_uint8_dec_le(v___x_263_, v_c_262_);
if (v___x_316_ == 0)
{
v___y_265_ = v___x_316_;
goto v___jp_264_;
}
else
{
uint8_t v___x_317_; uint8_t v___x_318_; 
v___x_317_ = 57;
v___x_318_ = lean_uint8_dec_le(v_c_262_, v___x_317_);
v___y_265_ = v___x_318_;
goto v___jp_264_;
}
v___jp_264_:
{
if (v___y_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_267_, 0, v_a_255_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v_it_x27_270_; uint32_t v___x_271_; uint8_t v___x_272_; uint8_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v_fst_276_; lean_object* v_snd_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_315_; 
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_nat_add(v_idx_257_, v___x_268_);
lean_inc_ref(v_array_256_);
v_it_x27_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_270_, 0, v_array_256_);
lean_ctor_set(v_it_x27_270_, 1, v___x_269_);
v___x_271_ = lean_uint8_to_uint32(v_c_262_);
v___x_272_ = lean_uint32_to_uint8(v___x_271_);
v___x_273_ = lean_uint8_sub(v___x_272_, v___x_263_);
v___x_274_ = lean_uint8_to_nat(v___x_273_);
v___x_275_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_270_, v___x_274_);
v_fst_276_ = lean_ctor_get(v___x_275_, 0);
v_snd_277_ = lean_ctor_get(v___x_275_, 1);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_315_ == 0)
{
v___x_279_ = v___x_275_;
v_isShared_280_ = v_isSharedCheck_315_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_snd_277_);
lean_inc(v_fst_276_);
lean_dec(v___x_275_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_315_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = lean_nat_dec_eq(v_fst_276_, v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v_array_283_; lean_object* v_idx_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
lean_dec_ref(v_a_255_);
v_array_283_ = lean_ctor_get(v_snd_277_, 0);
v_idx_284_ = lean_ctor_get(v_snd_277_, 1);
v___x_285_ = lean_byte_array_size(v_array_283_);
v___x_286_ = lean_nat_dec_lt(v_idx_284_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_289_; 
lean_dec(v_fst_276_);
v___x_287_ = lean_box(0);
if (v_isShared_280_ == 0)
{
lean_ctor_set_tag(v___x_279_, 1);
lean_ctor_set(v___x_279_, 1, v___x_287_);
lean_ctor_set(v___x_279_, 0, v_snd_277_);
v___x_289_ = v___x_279_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_snd_277_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v___x_287_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
else
{
uint8_t v___x_291_; uint8_t v_got_292_; uint8_t v___x_293_; 
v___x_291_ = 32;
v_got_292_ = lean_byte_array_fget(v_array_283_, v_idx_284_);
v___x_293_ = lean_uint8_dec_eq(v_got_292_, v___x_291_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_296_; 
lean_dec(v_fst_276_);
v___x_294_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
if (v_isShared_280_ == 0)
{
lean_ctor_set_tag(v___x_279_, 1);
lean_ctor_set(v___x_279_, 1, v___x_294_);
lean_ctor_set(v___x_279_, 0, v_snd_277_);
v___x_296_ = v___x_279_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_snd_277_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
else
{
lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_308_; 
lean_inc(v_idx_284_);
lean_inc_ref(v_array_283_);
v_isSharedCheck_308_ = !lean_is_exclusive(v_snd_277_);
if (v_isSharedCheck_308_ == 0)
{
lean_object* v_unused_309_; lean_object* v_unused_310_; 
v_unused_309_ = lean_ctor_get(v_snd_277_, 1);
lean_dec(v_unused_309_);
v_unused_310_ = lean_ctor_get(v_snd_277_, 0);
lean_dec(v_unused_310_);
v___x_299_ = v_snd_277_;
v_isShared_300_ = v_isSharedCheck_308_;
goto v_resetjp_298_;
}
else
{
lean_dec(v_snd_277_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_308_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_301_ = lean_nat_add(v_idx_284_, v___x_268_);
lean_dec(v_idx_284_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v___x_301_);
v___x_303_ = v___x_299_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_array_283_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v___x_301_);
v___x_303_ = v_reuseFailAlloc_307_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_305_; 
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 1, v_fst_276_);
lean_ctor_set(v___x_279_, 0, v___x_303_);
v___x_305_ = v___x_279_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_fst_276_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
}
else
{
lean_object* v___x_311_; lean_object* v___x_313_; 
lean_dec(v_snd_277_);
lean_dec(v_fst_276_);
v___x_311_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_280_ == 0)
{
lean_ctor_set_tag(v___x_279_, 1);
lean_ctor_set(v___x_279_, 1, v___x_311_);
lean_ctor_set(v___x_279_, 0, v_a_255_);
v___x_313_ = v___x_279_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_255_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_spec__0(lean_object* v_acc_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_array_321_; lean_object* v_idx_322_; lean_object* v_pos_324_; lean_object* v_idx_325_; lean_object* v_err_326_; lean_object* v___x_330_; uint8_t v___x_331_; 
v_array_321_ = lean_ctor_get(v_a_320_, 0);
v_idx_322_ = lean_ctor_get(v_a_320_, 1);
lean_inc(v_idx_322_);
v___x_330_ = lean_byte_array_size(v_array_321_);
v___x_331_ = lean_nat_dec_lt(v_idx_322_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; 
v___x_332_ = lean_box(0);
lean_inc(v_idx_322_);
v_pos_324_ = v_a_320_;
v_idx_325_ = v_idx_322_;
v_err_326_ = v___x_332_;
goto v___jp_323_;
}
else
{
uint8_t v_c_333_; uint8_t v___x_334_; uint8_t v___y_336_; uint8_t v___x_372_; 
v_c_333_ = lean_byte_array_fget(v_array_321_, v_idx_322_);
v___x_334_ = 48;
v___x_372_ = lean_uint8_dec_le(v___x_334_, v_c_333_);
if (v___x_372_ == 0)
{
v___y_336_ = v___x_372_;
goto v___jp_335_;
}
else
{
uint8_t v___x_373_; uint8_t v___x_374_; 
v___x_373_ = 57;
v___x_374_ = lean_uint8_dec_le(v_c_333_, v___x_373_);
v___y_336_ = v___x_374_;
goto v___jp_335_;
}
v___jp_335_:
{
if (v___y_336_ == 0)
{
lean_object* v___x_337_; 
v___x_337_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
lean_inc(v_idx_322_);
v_pos_324_ = v_a_320_;
v_idx_325_ = v_idx_322_;
v_err_326_ = v___x_337_;
goto v___jp_323_;
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v_it_x27_340_; uint32_t v___x_341_; uint8_t v___x_342_; uint8_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_fst_346_; lean_object* v_snd_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_338_ = lean_unsigned_to_nat(1u);
v___x_339_ = lean_nat_add(v_idx_322_, v___x_338_);
lean_inc_ref(v_array_321_);
v_it_x27_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_340_, 0, v_array_321_);
lean_ctor_set(v_it_x27_340_, 1, v___x_339_);
v___x_341_ = lean_uint8_to_uint32(v_c_333_);
v___x_342_ = lean_uint32_to_uint8(v___x_341_);
v___x_343_ = lean_uint8_sub(v___x_342_, v___x_334_);
v___x_344_ = lean_uint8_to_nat(v___x_343_);
v___x_345_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_340_, v___x_344_);
v_fst_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_fst_346_);
v_snd_347_ = lean_ctor_get(v___x_345_, 1);
lean_inc(v_snd_347_);
lean_dec_ref(v___x_345_);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_nat_dec_eq(v_fst_346_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v_array_350_; lean_object* v_idx_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
lean_dec_ref(v_a_320_);
v_array_350_ = lean_ctor_get(v_snd_347_, 0);
v_idx_351_ = lean_ctor_get(v_snd_347_, 1);
lean_inc(v_idx_351_);
v___x_352_ = lean_byte_array_size(v_array_350_);
v___x_353_ = lean_nat_dec_lt(v_idx_351_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; 
lean_dec(v_fst_346_);
v___x_354_ = lean_box(0);
v_pos_324_ = v_snd_347_;
v_idx_325_ = v_idx_351_;
v_err_326_ = v___x_354_;
goto v___jp_323_;
}
else
{
uint8_t v___x_355_; uint8_t v_got_356_; uint8_t v___x_357_; 
v___x_355_ = 32;
v_got_356_ = lean_byte_array_fget(v_array_350_, v_idx_351_);
v___x_357_ = lean_uint8_dec_eq(v_got_356_, v___x_355_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
lean_dec(v_fst_346_);
v___x_358_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
v_pos_324_ = v_snd_347_;
v_idx_325_ = v_idx_351_;
v_err_326_ = v___x_358_;
goto v___jp_323_;
}
else
{
lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_368_; 
lean_inc_ref(v_array_350_);
lean_dec(v_idx_322_);
v_isSharedCheck_368_ = !lean_is_exclusive(v_snd_347_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; lean_object* v_unused_370_; 
v_unused_369_ = lean_ctor_get(v_snd_347_, 1);
lean_dec(v_unused_369_);
v_unused_370_ = lean_ctor_get(v_snd_347_, 0);
lean_dec(v_unused_370_);
v___x_360_ = v_snd_347_;
v_isShared_361_ = v_isSharedCheck_368_;
goto v_resetjp_359_;
}
else
{
lean_dec(v_snd_347_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_368_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_362_ = lean_nat_add(v_idx_351_, v___x_338_);
lean_dec(v_idx_351_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v___x_362_);
v___x_364_ = v___x_360_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_array_350_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___x_362_);
v___x_364_ = v_reuseFailAlloc_367_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; 
v___x_365_ = lean_array_push(v_acc_319_, v_fst_346_);
v_acc_319_ = v___x_365_;
v_a_320_ = v___x_364_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_371_; 
lean_dec(v_snd_347_);
lean_dec(v_fst_346_);
v___x_371_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
lean_inc(v_idx_322_);
v_pos_324_ = v_a_320_;
v_idx_325_ = v_idx_322_;
v_err_326_ = v___x_371_;
goto v___jp_323_;
}
}
}
}
v___jp_323_:
{
uint8_t v___x_327_; 
v___x_327_ = lean_nat_dec_eq(v_idx_322_, v_idx_325_);
lean_dec(v_idx_325_);
lean_dec(v_idx_322_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; 
lean_dec_ref(v_acc_319_);
lean_inc(v_err_326_);
v___x_328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_328_, 0, v_pos_324_);
lean_ctor_set(v___x_328_, 1, v_err_326_);
return v___x_328_;
}
else
{
lean_object* v___x_329_; 
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v_pos_324_);
lean_ctor_set(v___x_329_, 1, v_acc_319_);
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(lean_object* v_a_377_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0));
v___x_379_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_spec__0(v___x_378_, v_a_377_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(lean_object* v_a_383_){
_start:
{
lean_object* v_array_384_; lean_object* v_idx_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v_array_384_ = lean_ctor_get(v_a_383_, 0);
v_idx_385_ = lean_ctor_get(v_a_383_, 1);
v___x_386_ = lean_byte_array_size(v_array_384_);
v___x_387_ = lean_nat_dec_lt(v_idx_385_, v___x_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_box(0);
v___x_389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_389_, 0, v_a_383_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
return v___x_389_;
}
else
{
uint8_t v___x_390_; uint8_t v_got_391_; uint8_t v___x_392_; 
v___x_390_ = 100;
v_got_391_ = lean_byte_array_fget(v_array_384_, v_idx_385_);
v___x_392_ = lean_uint8_dec_eq(v_got_391_, v___x_390_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1));
v___x_394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_394_, 0, v_a_383_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
return v___x_394_;
}
else
{
lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_458_; 
lean_inc(v_idx_385_);
lean_inc_ref(v_array_384_);
v_isSharedCheck_458_ = !lean_is_exclusive(v_a_383_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; lean_object* v_unused_460_; 
v_unused_459_ = lean_ctor_get(v_a_383_, 1);
lean_dec(v_unused_459_);
v_unused_460_ = lean_ctor_get(v_a_383_, 0);
lean_dec(v_unused_460_);
v___x_396_ = v_a_383_;
v_isShared_397_ = v_isSharedCheck_458_;
goto v_resetjp_395_;
}
else
{
lean_dec(v_a_383_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_458_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = lean_nat_add(v_idx_385_, v___x_398_);
lean_dec(v_idx_385_);
lean_inc(v___x_399_);
lean_inc_ref(v_array_384_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v___x_399_);
v___x_401_ = v___x_396_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_array_384_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_399_);
v___x_401_ = v_reuseFailAlloc_457_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
uint8_t v___x_402_; 
v___x_402_ = lean_nat_dec_lt(v___x_399_, v___x_386_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec(v___x_399_);
lean_dec_ref(v_array_384_);
v___x_403_ = lean_box(0);
v___x_404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_401_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
return v___x_404_;
}
else
{
uint8_t v___x_405_; uint8_t v_got_406_; uint8_t v___x_407_; 
v___x_405_ = 32;
v_got_406_ = lean_byte_array_fget(v_array_384_, v___x_399_);
v___x_407_ = lean_uint8_dec_eq(v_got_406_, v___x_405_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec(v___x_399_);
lean_dec_ref(v_array_384_);
v___x_408_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
v___x_409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_401_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
return v___x_409_;
}
else
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec_ref(v___x_401_);
v___x_410_ = lean_nat_add(v___x_399_, v___x_398_);
lean_dec(v___x_399_);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v_array_384_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(v___x_411_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_pos_413_; lean_object* v_res_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_447_; 
v_pos_413_ = lean_ctor_get(v___x_412_, 0);
v_res_414_ = lean_ctor_get(v___x_412_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_447_ == 0)
{
v___x_416_ = v___x_412_;
v_isShared_417_ = v_isSharedCheck_447_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_res_414_);
lean_inc(v_pos_413_);
lean_dec(v___x_412_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_447_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v_array_418_; lean_object* v_idx_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v_array_418_ = lean_ctor_get(v_pos_413_, 0);
v_idx_419_ = lean_ctor_get(v_pos_413_, 1);
v___x_420_ = lean_byte_array_size(v_array_418_);
v___x_421_ = lean_nat_dec_lt(v_idx_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_424_; 
lean_dec(v_res_414_);
v___x_422_ = lean_box(0);
if (v_isShared_417_ == 0)
{
lean_ctor_set_tag(v___x_416_, 1);
lean_ctor_set(v___x_416_, 1, v___x_422_);
v___x_424_ = v___x_416_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_pos_413_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
else
{
uint8_t v___x_426_; uint8_t v_got_427_; uint8_t v___x_428_; 
v___x_426_ = 48;
v_got_427_ = lean_byte_array_fget(v_array_418_, v_idx_419_);
v___x_428_ = lean_uint8_dec_eq(v_got_427_, v___x_426_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_431_; 
lean_dec(v_res_414_);
v___x_429_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1));
if (v_isShared_417_ == 0)
{
lean_ctor_set_tag(v___x_416_, 1);
lean_ctor_set(v___x_416_, 1, v___x_429_);
v___x_431_ = v___x_416_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_pos_413_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
else
{
lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_444_; 
lean_inc(v_idx_419_);
lean_inc_ref(v_array_418_);
v_isSharedCheck_444_ = !lean_is_exclusive(v_pos_413_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; lean_object* v_unused_446_; 
v_unused_445_ = lean_ctor_get(v_pos_413_, 1);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_pos_413_, 0);
lean_dec(v_unused_446_);
v___x_434_ = v_pos_413_;
v_isShared_435_ = v_isSharedCheck_444_;
goto v_resetjp_433_;
}
else
{
lean_dec(v_pos_413_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_444_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = lean_nat_add(v_idx_419_, v___x_398_);
lean_dec(v_idx_419_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v___x_436_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_array_418_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v___x_436_);
v___x_438_ = v_reuseFailAlloc_443_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_439_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_439_, 0, v_res_414_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v___x_439_);
lean_ctor_set(v___x_416_, 0, v___x_438_);
v___x_441_ = v___x_416_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v___x_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_448_; lean_object* v_err_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
v_pos_448_ = lean_ctor_get(v___x_412_, 0);
v_err_449_ = lean_ctor_get(v___x_412_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_412_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_err_449_);
lean_inc(v_pos_448_);
lean_dec(v___x_412_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_pos_448_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_err_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseLit(lean_object* v_a_461_){
_start:
{
lean_object* v_array_462_; lean_object* v_idx_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v_array_462_ = lean_ctor_get(v_a_461_, 0);
v_idx_463_ = lean_ctor_get(v_a_461_, 1);
v___x_464_ = lean_byte_array_size(v_array_462_);
v___x_465_ = lean_nat_dec_lt(v_idx_463_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_box(0);
v___x_467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_467_, 0, v_a_461_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
return v___x_467_;
}
else
{
uint8_t v___x_468_; uint8_t v___x_469_; uint8_t v___x_470_; 
v___x_468_ = lean_byte_array_fget(v_array_462_, v_idx_463_);
v___x_469_ = 45;
v___x_470_ = lean_uint8_dec_eq(v___x_468_, v___x_469_);
if (v___x_470_ == 0)
{
if (v___x_465_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_box(0);
v___x_472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_472_, 0, v_a_461_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
return v___x_472_;
}
else
{
uint8_t v___x_473_; uint8_t v___y_475_; uint8_t v___x_510_; 
v___x_473_ = 48;
v___x_510_ = lean_uint8_dec_le(v___x_473_, v___x_468_);
if (v___x_510_ == 0)
{
v___y_475_ = v___x_510_;
goto v___jp_474_;
}
else
{
uint8_t v___x_511_; uint8_t v___x_512_; 
v___x_511_ = 57;
v___x_512_ = lean_uint8_dec_le(v___x_468_, v___x_511_);
v___y_475_ = v___x_512_;
goto v___jp_474_;
}
v___jp_474_:
{
if (v___y_475_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_477_, 0, v_a_461_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
return v___x_477_;
}
else
{
lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_507_; 
lean_inc(v_idx_463_);
lean_inc_ref(v_array_462_);
v_isSharedCheck_507_ = !lean_is_exclusive(v_a_461_);
if (v_isSharedCheck_507_ == 0)
{
lean_object* v_unused_508_; lean_object* v_unused_509_; 
v_unused_508_ = lean_ctor_get(v_a_461_, 1);
lean_dec(v_unused_508_);
v_unused_509_ = lean_ctor_get(v_a_461_, 0);
lean_dec(v_unused_509_);
v___x_479_ = v_a_461_;
v_isShared_480_ = v_isSharedCheck_507_;
goto v_resetjp_478_;
}
else
{
lean_dec(v_a_461_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_507_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v_it_x27_484_; 
v___x_481_ = lean_unsigned_to_nat(1u);
v___x_482_ = lean_nat_add(v_idx_463_, v___x_481_);
lean_dec(v_idx_463_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v___x_482_);
v_it_x27_484_ = v___x_479_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_array_462_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v___x_482_);
v_it_x27_484_ = v_reuseFailAlloc_506_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
uint32_t v___x_485_; uint8_t v___x_486_; uint8_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v_fst_490_; lean_object* v_snd_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_505_; 
v___x_485_ = lean_uint8_to_uint32(v___x_468_);
v___x_486_ = lean_uint32_to_uint8(v___x_485_);
v___x_487_ = lean_uint8_sub(v___x_486_, v___x_473_);
v___x_488_ = lean_uint8_to_nat(v___x_487_);
v___x_489_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_484_, v___x_488_);
v_fst_490_ = lean_ctor_get(v___x_489_, 0);
v_snd_491_ = lean_ctor_get(v___x_489_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_505_ == 0)
{
v___x_493_ = v___x_489_;
v_isShared_494_ = v_isSharedCheck_505_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_snd_491_);
lean_inc(v_fst_490_);
lean_dec(v___x_489_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_505_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = lean_unsigned_to_nat(0u);
v___x_496_ = lean_nat_dec_eq(v_fst_490_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_497_ = lean_nat_to_int(v_fst_490_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_497_);
lean_ctor_set(v___x_493_, 0, v_snd_491_);
v___x_499_ = v___x_493_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_snd_491_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
else
{
lean_object* v___x_501_; lean_object* v___x_503_; 
lean_dec(v_fst_490_);
v___x_501_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_494_ == 0)
{
lean_ctor_set_tag(v___x_493_, 1);
lean_ctor_set(v___x_493_, 1, v___x_501_);
lean_ctor_set(v___x_493_, 0, v_snd_491_);
v___x_503_ = v___x_493_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_snd_491_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
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
if (v___x_465_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_box(0);
v___x_514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_514_, 0, v_a_461_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
return v___x_514_;
}
else
{
if (v___x_470_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1));
v___x_516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_516_, 0, v_a_461_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
return v___x_516_;
}
else
{
lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_561_; 
lean_inc(v_idx_463_);
lean_inc_ref(v_array_462_);
v_isSharedCheck_561_ = !lean_is_exclusive(v_a_461_);
if (v_isSharedCheck_561_ == 0)
{
lean_object* v_unused_562_; lean_object* v_unused_563_; 
v_unused_562_ = lean_ctor_get(v_a_461_, 1);
lean_dec(v_unused_562_);
v_unused_563_ = lean_ctor_get(v_a_461_, 0);
lean_dec(v_unused_563_);
v___x_518_ = v_a_461_;
v_isShared_519_ = v_isSharedCheck_561_;
goto v_resetjp_517_;
}
else
{
lean_dec(v_a_461_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_561_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = lean_nat_add(v_idx_463_, v___x_520_);
lean_dec(v_idx_463_);
lean_inc(v___x_521_);
lean_inc_ref(v_array_462_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 1, v___x_521_);
v___x_523_ = v___x_518_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_array_462_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_521_);
v___x_523_ = v_reuseFailAlloc_560_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
uint8_t v___x_524_; 
v___x_524_ = lean_nat_dec_lt(v___x_521_, v___x_464_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; 
lean_dec(v___x_521_);
lean_dec_ref(v_array_462_);
v___x_525_ = lean_box(0);
v___x_526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_523_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
return v___x_526_;
}
else
{
uint8_t v_c_527_; uint8_t v___x_528_; uint8_t v___y_530_; uint8_t v___x_557_; 
v_c_527_ = lean_byte_array_fget(v_array_462_, v___x_521_);
v___x_528_ = 48;
v___x_557_ = lean_uint8_dec_le(v___x_528_, v_c_527_);
if (v___x_557_ == 0)
{
v___y_530_ = v___x_557_;
goto v___jp_529_;
}
else
{
uint8_t v___x_558_; uint8_t v___x_559_; 
v___x_558_ = 57;
v___x_559_ = lean_uint8_dec_le(v_c_527_, v___x_558_);
v___y_530_ = v___x_559_;
goto v___jp_529_;
}
v___jp_529_:
{
if (v___y_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec(v___x_521_);
lean_dec_ref(v_array_462_);
v___x_531_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_523_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
return v___x_532_;
}
else
{
lean_object* v___x_533_; lean_object* v_it_x27_534_; uint32_t v___x_535_; uint8_t v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v_fst_540_; lean_object* v_snd_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_556_; 
lean_dec_ref(v___x_523_);
v___x_533_ = lean_nat_add(v___x_521_, v___x_520_);
lean_dec(v___x_521_);
v_it_x27_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_534_, 0, v_array_462_);
lean_ctor_set(v_it_x27_534_, 1, v___x_533_);
v___x_535_ = lean_uint8_to_uint32(v_c_527_);
v___x_536_ = lean_uint32_to_uint8(v___x_535_);
v___x_537_ = lean_uint8_sub(v___x_536_, v___x_528_);
v___x_538_ = lean_uint8_to_nat(v___x_537_);
v___x_539_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_534_, v___x_538_);
v_fst_540_ = lean_ctor_get(v___x_539_, 0);
v_snd_541_ = lean_ctor_get(v___x_539_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_556_ == 0)
{
v___x_543_ = v___x_539_;
v_isShared_544_ = v_isSharedCheck_556_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_snd_541_);
lean_inc(v_fst_540_);
lean_dec(v___x_539_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_556_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = lean_nat_dec_eq(v_fst_540_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_547_ = lean_nat_to_int(v_fst_540_);
v___x_548_ = lean_int_neg(v___x_547_);
lean_dec(v___x_547_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 1, v___x_548_);
lean_ctor_set(v___x_543_, 0, v_snd_541_);
v___x_550_ = v___x_543_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_snd_541_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_554_; 
lean_dec(v_fst_540_);
v___x_552_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 1);
lean_ctor_set(v___x_543_, 1, v___x_552_);
lean_ctor_set(v___x_543_, 0, v_snd_541_);
v___x_554_ = v___x_543_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_snd_541_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_litWs(lean_object* v_a_564_){
_start:
{
lean_object* v_pos_566_; lean_object* v_res_567_; lean_object* v_array_591_; lean_object* v_idx_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v_array_591_ = lean_ctor_get(v_a_564_, 0);
v_idx_592_ = lean_ctor_get(v_a_564_, 1);
v___x_593_ = lean_byte_array_size(v_array_591_);
v___x_594_ = lean_nat_dec_lt(v_idx_592_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_box(0);
v___x_596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_596_, 0, v_a_564_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
return v___x_596_;
}
else
{
uint8_t v___x_597_; uint8_t v___x_598_; uint8_t v___x_599_; 
v___x_597_ = lean_byte_array_fget(v_array_591_, v_idx_592_);
v___x_598_ = 45;
v___x_599_ = lean_uint8_dec_eq(v___x_597_, v___x_598_);
if (v___x_599_ == 0)
{
uint8_t v___x_600_; uint8_t v___y_602_; uint8_t v___x_626_; 
v___x_600_ = 48;
v___x_626_ = lean_uint8_dec_le(v___x_600_, v___x_597_);
if (v___x_626_ == 0)
{
v___y_602_ = v___x_626_;
goto v___jp_601_;
}
else
{
uint8_t v___x_627_; uint8_t v___x_628_; 
v___x_627_ = 57;
v___x_628_ = lean_uint8_dec_le(v___x_597_, v___x_627_);
v___y_602_ = v___x_628_;
goto v___jp_601_;
}
v___jp_601_:
{
if (v___y_602_ == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_604_, 0, v_a_564_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
return v___x_604_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v_it_x27_607_; uint32_t v___x_608_; uint8_t v___x_609_; uint8_t v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v_fst_613_; lean_object* v_snd_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_625_; 
v___x_605_ = lean_unsigned_to_nat(1u);
v___x_606_ = lean_nat_add(v_idx_592_, v___x_605_);
lean_inc_ref(v_array_591_);
v_it_x27_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_607_, 0, v_array_591_);
lean_ctor_set(v_it_x27_607_, 1, v___x_606_);
v___x_608_ = lean_uint8_to_uint32(v___x_597_);
v___x_609_ = lean_uint32_to_uint8(v___x_608_);
v___x_610_ = lean_uint8_sub(v___x_609_, v___x_600_);
v___x_611_ = lean_uint8_to_nat(v___x_610_);
v___x_612_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_607_, v___x_611_);
v_fst_613_ = lean_ctor_get(v___x_612_, 0);
v_snd_614_ = lean_ctor_get(v___x_612_, 1);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_625_ == 0)
{
v___x_616_ = v___x_612_;
v_isShared_617_ = v_isSharedCheck_625_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_snd_614_);
lean_inc(v_fst_613_);
lean_dec(v___x_612_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_625_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = lean_nat_dec_eq(v_fst_613_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
lean_del_object(v___x_616_);
lean_dec_ref(v_a_564_);
v___x_620_ = lean_nat_to_int(v_fst_613_);
v_pos_566_ = v_snd_614_;
v_res_567_ = v___x_620_;
goto v___jp_565_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_623_; 
lean_dec(v_snd_614_);
lean_dec(v_fst_613_);
v___x_621_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_617_ == 0)
{
lean_ctor_set_tag(v___x_616_, 1);
lean_ctor_set(v___x_616_, 1, v___x_621_);
lean_ctor_set(v___x_616_, 0, v_a_564_);
v___x_623_ = v___x_616_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_564_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_630_ = lean_nat_add(v_idx_592_, v___x_629_);
v___x_631_ = lean_nat_dec_lt(v___x_630_, v___x_593_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec(v___x_630_);
v___x_632_ = lean_box(0);
v___x_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_633_, 0, v_a_564_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
return v___x_633_;
}
else
{
uint8_t v_c_634_; uint8_t v___x_635_; uint8_t v___y_637_; uint8_t v___x_661_; 
v_c_634_ = lean_byte_array_fget(v_array_591_, v___x_630_);
v___x_635_ = 48;
v___x_661_ = lean_uint8_dec_le(v___x_635_, v_c_634_);
if (v___x_661_ == 0)
{
v___y_637_ = v___x_661_;
goto v___jp_636_;
}
else
{
uint8_t v___x_662_; uint8_t v___x_663_; 
v___x_662_ = 57;
v___x_663_ = lean_uint8_dec_le(v_c_634_, v___x_662_);
v___y_637_ = v___x_663_;
goto v___jp_636_;
}
v___jp_636_:
{
if (v___y_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec(v___x_630_);
v___x_638_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_639_, 0, v_a_564_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
return v___x_639_;
}
else
{
lean_object* v___x_640_; lean_object* v_it_x27_641_; uint32_t v___x_642_; uint8_t v___x_643_; uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v_fst_647_; lean_object* v_snd_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_660_; 
v___x_640_ = lean_nat_add(v___x_630_, v___x_629_);
lean_dec(v___x_630_);
lean_inc_ref(v_array_591_);
v_it_x27_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_641_, 0, v_array_591_);
lean_ctor_set(v_it_x27_641_, 1, v___x_640_);
v___x_642_ = lean_uint8_to_uint32(v_c_634_);
v___x_643_ = lean_uint32_to_uint8(v___x_642_);
v___x_644_ = lean_uint8_sub(v___x_643_, v___x_635_);
v___x_645_ = lean_uint8_to_nat(v___x_644_);
v___x_646_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_641_, v___x_645_);
v_fst_647_ = lean_ctor_get(v___x_646_, 0);
v_snd_648_ = lean_ctor_get(v___x_646_, 1);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_660_ == 0)
{
v___x_650_ = v___x_646_;
v_isShared_651_ = v_isSharedCheck_660_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_snd_648_);
lean_inc(v_fst_647_);
lean_dec(v___x_646_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_660_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_653_ = lean_nat_dec_eq(v_fst_647_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; 
lean_del_object(v___x_650_);
lean_dec_ref(v_a_564_);
v___x_654_ = lean_nat_to_int(v_fst_647_);
v___x_655_ = lean_int_neg(v___x_654_);
lean_dec(v___x_654_);
v_pos_566_ = v_snd_648_;
v_res_567_ = v___x_655_;
goto v___jp_565_;
}
else
{
lean_object* v___x_656_; lean_object* v___x_658_; 
lean_dec(v_snd_648_);
lean_dec(v_fst_647_);
v___x_656_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_651_ == 0)
{
lean_ctor_set_tag(v___x_650_, 1);
lean_ctor_set(v___x_650_, 1, v___x_656_);
lean_ctor_set(v___x_650_, 0, v_a_564_);
v___x_658_ = v___x_650_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_564_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
}
}
}
v___jp_565_:
{
lean_object* v_array_568_; lean_object* v_idx_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v_array_568_ = lean_ctor_get(v_pos_566_, 0);
v_idx_569_ = lean_ctor_get(v_pos_566_, 1);
v___x_570_ = lean_byte_array_size(v_array_568_);
v___x_571_ = lean_nat_dec_lt(v_idx_569_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec(v_res_567_);
v___x_572_ = lean_box(0);
v___x_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_573_, 0, v_pos_566_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
return v___x_573_;
}
else
{
uint8_t v___x_574_; uint8_t v_got_575_; uint8_t v___x_576_; 
v___x_574_ = 32;
v_got_575_ = lean_byte_array_fget(v_array_568_, v_idx_569_);
v___x_576_ = lean_uint8_dec_eq(v_got_575_, v___x_574_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec(v_res_567_);
v___x_577_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
v___x_578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_578_, 0, v_pos_566_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
return v___x_578_;
}
else
{
lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_588_; 
lean_inc(v_idx_569_);
lean_inc_ref(v_array_568_);
v_isSharedCheck_588_ = !lean_is_exclusive(v_pos_566_);
if (v_isSharedCheck_588_ == 0)
{
lean_object* v_unused_589_; lean_object* v_unused_590_; 
v_unused_589_ = lean_ctor_get(v_pos_566_, 1);
lean_dec(v_unused_589_);
v_unused_590_ = lean_ctor_get(v_pos_566_, 0);
lean_dec(v_unused_590_);
v___x_580_ = v_pos_566_;
v_isShared_581_ = v_isSharedCheck_588_;
goto v_resetjp_579_;
}
else
{
lean_dec(v_pos_566_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_588_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_582_ = lean_unsigned_to_nat(1u);
v___x_583_ = lean_nat_add(v_idx_569_, v___x_582_);
lean_dec(v_idx_569_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_583_);
v___x_585_ = v___x_580_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_array_568_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v___x_583_);
v___x_585_ = v_reuseFailAlloc_587_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; 
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v_res_567_);
return v___x_586_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__0(lean_object* v_a_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = lean_nat_to_int(v_a_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__1(lean_object* v_acc_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_array_668_; lean_object* v_idx_669_; lean_object* v_pos_671_; lean_object* v_idx_672_; lean_object* v_err_673_; lean_object* v_pos_678_; lean_object* v_res_679_; lean_object* v___x_702_; uint8_t v___x_703_; 
v_array_668_ = lean_ctor_get(v_a_667_, 0);
v_idx_669_ = lean_ctor_get(v_a_667_, 1);
lean_inc(v_idx_669_);
v___x_702_ = lean_byte_array_size(v_array_668_);
v___x_703_ = lean_nat_dec_lt(v_idx_669_, v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; 
v___x_704_ = lean_box(0);
lean_inc(v_idx_669_);
v_pos_671_ = v_a_667_;
v_idx_672_ = v_idx_669_;
v_err_673_ = v___x_704_;
goto v___jp_670_;
}
else
{
uint8_t v___x_705_; uint8_t v___x_706_; uint8_t v___x_707_; 
v___x_705_ = lean_byte_array_fget(v_array_668_, v_idx_669_);
v___x_706_ = 45;
v___x_707_ = lean_uint8_dec_eq(v___x_705_, v___x_706_);
if (v___x_707_ == 0)
{
uint8_t v___x_708_; uint8_t v___y_710_; uint8_t v___x_726_; 
v___x_708_ = 48;
v___x_726_ = lean_uint8_dec_le(v___x_708_, v___x_705_);
if (v___x_726_ == 0)
{
v___y_710_ = v___x_726_;
goto v___jp_709_;
}
else
{
uint8_t v___x_727_; uint8_t v___x_728_; 
v___x_727_ = 57;
v___x_728_ = lean_uint8_dec_le(v___x_705_, v___x_727_);
v___y_710_ = v___x_728_;
goto v___jp_709_;
}
v___jp_709_:
{
if (v___y_710_ == 0)
{
lean_object* v___x_711_; 
v___x_711_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
lean_inc(v_idx_669_);
v_pos_671_ = v_a_667_;
v_idx_672_ = v_idx_669_;
v_err_673_ = v___x_711_;
goto v___jp_670_;
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v_it_x27_714_; uint32_t v___x_715_; uint8_t v___x_716_; uint8_t v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v_fst_720_; lean_object* v_snd_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = lean_nat_add(v_idx_669_, v___x_712_);
lean_inc_ref(v_array_668_);
v_it_x27_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_714_, 0, v_array_668_);
lean_ctor_set(v_it_x27_714_, 1, v___x_713_);
v___x_715_ = lean_uint8_to_uint32(v___x_705_);
v___x_716_ = lean_uint32_to_uint8(v___x_715_);
v___x_717_ = lean_uint8_sub(v___x_716_, v___x_708_);
v___x_718_ = lean_uint8_to_nat(v___x_717_);
v___x_719_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_714_, v___x_718_);
v_fst_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_fst_720_);
v_snd_721_ = lean_ctor_get(v___x_719_, 1);
lean_inc(v_snd_721_);
lean_dec_ref(v___x_719_);
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = lean_nat_dec_eq(v_fst_720_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; 
lean_dec_ref(v_a_667_);
v___x_724_ = lean_nat_to_int(v_fst_720_);
v_pos_678_ = v_snd_721_;
v_res_679_ = v___x_724_;
goto v___jp_677_;
}
else
{
lean_object* v___x_725_; 
lean_dec(v_snd_721_);
lean_dec(v_fst_720_);
v___x_725_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
lean_inc(v_idx_669_);
v_pos_671_ = v_a_667_;
v_idx_672_ = v_idx_669_;
v_err_673_ = v___x_725_;
goto v___jp_670_;
}
}
}
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_729_ = lean_unsigned_to_nat(1u);
v___x_730_ = lean_nat_add(v_idx_669_, v___x_729_);
v___x_731_ = lean_nat_dec_lt(v___x_730_, v___x_702_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
lean_dec(v___x_730_);
v___x_732_ = lean_box(0);
lean_inc(v_idx_669_);
v_pos_671_ = v_a_667_;
v_idx_672_ = v_idx_669_;
v_err_673_ = v___x_732_;
goto v___jp_670_;
}
else
{
uint8_t v_c_733_; uint8_t v___x_734_; uint8_t v___y_736_; uint8_t v___x_752_; 
v_c_733_ = lean_byte_array_fget(v_array_668_, v___x_730_);
v___x_734_ = 48;
v___x_752_ = lean_uint8_dec_le(v___x_734_, v_c_733_);
if (v___x_752_ == 0)
{
v___y_736_ = v___x_752_;
goto v___jp_735_;
}
else
{
uint8_t v___x_753_; uint8_t v___x_754_; 
v___x_753_ = 57;
v___x_754_ = lean_uint8_dec_le(v_c_733_, v___x_753_);
v___y_736_ = v___x_754_;
goto v___jp_735_;
}
v___jp_735_:
{
if (v___y_736_ == 0)
{
lean_object* v___x_737_; 
lean_dec(v___x_730_);
v___x_737_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
lean_inc(v_idx_669_);
v_pos_671_ = v_a_667_;
v_idx_672_ = v_idx_669_;
v_err_673_ = v___x_737_;
goto v___jp_670_;
}
else
{
lean_object* v___x_738_; lean_object* v_it_x27_739_; uint32_t v___x_740_; uint8_t v___x_741_; uint8_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_fst_745_; lean_object* v_snd_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_738_ = lean_nat_add(v___x_730_, v___x_729_);
lean_dec(v___x_730_);
lean_inc_ref(v_array_668_);
v_it_x27_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_739_, 0, v_array_668_);
lean_ctor_set(v_it_x27_739_, 1, v___x_738_);
v___x_740_ = lean_uint8_to_uint32(v_c_733_);
v___x_741_ = lean_uint32_to_uint8(v___x_740_);
v___x_742_ = lean_uint8_sub(v___x_741_, v___x_734_);
v___x_743_ = lean_uint8_to_nat(v___x_742_);
v___x_744_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_739_, v___x_743_);
v_fst_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_fst_745_);
v_snd_746_ = lean_ctor_get(v___x_744_, 1);
lean_inc(v_snd_746_);
lean_dec_ref(v___x_744_);
v___x_747_ = lean_unsigned_to_nat(0u);
v___x_748_ = lean_nat_dec_eq(v_fst_745_, v___x_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; lean_object* v___x_750_; 
lean_dec_ref(v_a_667_);
v___x_749_ = lean_nat_to_int(v_fst_745_);
v___x_750_ = lean_int_neg(v___x_749_);
lean_dec(v___x_749_);
v_pos_678_ = v_snd_746_;
v_res_679_ = v___x_750_;
goto v___jp_677_;
}
else
{
lean_object* v___x_751_; 
lean_dec(v_snd_746_);
lean_dec(v_fst_745_);
v___x_751_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
lean_inc(v_idx_669_);
v_pos_671_ = v_a_667_;
v_idx_672_ = v_idx_669_;
v_err_673_ = v___x_751_;
goto v___jp_670_;
}
}
}
}
}
}
v___jp_670_:
{
uint8_t v___x_674_; 
v___x_674_ = lean_nat_dec_eq(v_idx_669_, v_idx_672_);
lean_dec(v_idx_672_);
lean_dec(v_idx_669_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
lean_dec_ref(v_acc_666_);
lean_inc(v_err_673_);
v___x_675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_675_, 0, v_pos_671_);
lean_ctor_set(v___x_675_, 1, v_err_673_);
return v___x_675_;
}
else
{
lean_object* v___x_676_; 
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_pos_671_);
lean_ctor_set(v___x_676_, 1, v_acc_666_);
return v___x_676_;
}
}
v___jp_677_:
{
lean_object* v_array_680_; lean_object* v_idx_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v_array_680_ = lean_ctor_get(v_pos_678_, 0);
v_idx_681_ = lean_ctor_get(v_pos_678_, 1);
lean_inc(v_idx_681_);
v___x_682_ = lean_byte_array_size(v_array_680_);
v___x_683_ = lean_nat_dec_lt(v_idx_681_, v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; 
lean_dec(v_res_679_);
v___x_684_ = lean_box(0);
v_pos_671_ = v_pos_678_;
v_idx_672_ = v_idx_681_;
v_err_673_ = v___x_684_;
goto v___jp_670_;
}
else
{
uint8_t v___x_685_; uint8_t v_got_686_; uint8_t v___x_687_; 
v___x_685_ = 32;
v_got_686_ = lean_byte_array_fget(v_array_680_, v_idx_681_);
v___x_687_ = lean_uint8_dec_eq(v_got_686_, v___x_685_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; 
lean_dec(v_res_679_);
v___x_688_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
v_pos_671_ = v_pos_678_;
v_idx_672_ = v_idx_681_;
v_err_673_ = v___x_688_;
goto v___jp_670_;
}
else
{
lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_699_; 
lean_inc_ref(v_array_680_);
lean_dec(v_idx_669_);
v_isSharedCheck_699_ = !lean_is_exclusive(v_pos_678_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; lean_object* v_unused_701_; 
v_unused_700_ = lean_ctor_get(v_pos_678_, 1);
lean_dec(v_unused_700_);
v_unused_701_ = lean_ctor_get(v_pos_678_, 0);
lean_dec(v_unused_701_);
v___x_690_ = v_pos_678_;
v_isShared_691_ = v_isSharedCheck_699_;
goto v_resetjp_689_;
}
else
{
lean_dec(v_pos_678_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_699_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_692_ = lean_unsigned_to_nat(1u);
v___x_693_ = lean_nat_add(v_idx_681_, v___x_692_);
lean_dec(v_idx_681_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___x_693_);
v___x_695_ = v___x_690_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_array_680_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v___x_693_);
v___x_695_ = v_reuseFailAlloc_698_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_696_; 
v___x_696_ = lean_array_push(v_acc_666_, v_res_679_);
v_acc_666_ = v___x_696_;
v_a_667_ = v___x_695_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(lean_object* v_a_757_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0));
v___x_759_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__1(v___x_758_, v_a_757_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_pos_760_; lean_object* v_res_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_794_; 
v_pos_760_ = lean_ctor_get(v___x_759_, 0);
v_res_761_ = lean_ctor_get(v___x_759_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_794_ == 0)
{
v___x_763_ = v___x_759_;
v_isShared_764_ = v_isSharedCheck_794_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_res_761_);
lean_inc(v_pos_760_);
lean_dec(v___x_759_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_794_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v_array_765_; lean_object* v_idx_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v_array_765_ = lean_ctor_get(v_pos_760_, 0);
v_idx_766_ = lean_ctor_get(v_pos_760_, 1);
v___x_767_ = lean_byte_array_size(v_array_765_);
v___x_768_ = lean_nat_dec_lt(v_idx_766_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_771_; 
lean_dec(v_res_761_);
v___x_769_ = lean_box(0);
if (v_isShared_764_ == 0)
{
lean_ctor_set_tag(v___x_763_, 1);
lean_ctor_set(v___x_763_, 1, v___x_769_);
v___x_771_ = v___x_763_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_pos_760_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
else
{
uint8_t v___x_773_; uint8_t v_got_774_; uint8_t v___x_775_; 
v___x_773_ = 48;
v_got_774_ = lean_byte_array_fget(v_array_765_, v_idx_766_);
v___x_775_ = lean_uint8_dec_eq(v_got_774_, v___x_773_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_778_; 
lean_dec(v_res_761_);
v___x_776_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1));
if (v_isShared_764_ == 0)
{
lean_ctor_set_tag(v___x_763_, 1);
lean_ctor_set(v___x_763_, 1, v___x_776_);
v___x_778_ = v___x_763_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_pos_760_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
else
{
lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_791_; 
lean_inc(v_idx_766_);
lean_inc_ref(v_array_765_);
v_isSharedCheck_791_ = !lean_is_exclusive(v_pos_760_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; lean_object* v_unused_793_; 
v_unused_792_ = lean_ctor_get(v_pos_760_, 1);
lean_dec(v_unused_792_);
v_unused_793_ = lean_ctor_get(v_pos_760_, 0);
lean_dec(v_unused_793_);
v___x_781_ = v_pos_760_;
v_isShared_782_ = v_isSharedCheck_791_;
goto v_resetjp_780_;
}
else
{
lean_dec(v_pos_760_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_791_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_783_ = lean_unsigned_to_nat(1u);
v___x_784_ = lean_nat_add(v_idx_766_, v___x_783_);
lean_dec(v_idx_766_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v___x_784_);
v___x_786_ = v___x_781_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_array_765_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_784_);
v___x_786_ = v_reuseFailAlloc_790_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_788_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_786_);
v___x_788_ = v___x_763_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_res_761_);
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
}
}
else
{
return v___x_759_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(lean_object* v_a_795_){
_start:
{
lean_object* v_array_796_; lean_object* v_idx_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v_array_796_ = lean_ctor_get(v_a_795_, 0);
v_idx_797_ = lean_ctor_get(v_a_795_, 1);
v___x_798_ = lean_byte_array_size(v_array_796_);
v___x_799_ = lean_nat_dec_lt(v_idx_797_, v___x_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_box(0);
v___x_801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_801_, 0, v_a_795_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
return v___x_801_;
}
else
{
uint8_t v___x_802_; uint8_t v_got_803_; uint8_t v___x_804_; 
v___x_802_ = 45;
v_got_803_ = lean_byte_array_fget(v_array_796_, v_idx_797_);
v___x_804_ = lean_uint8_dec_eq(v_got_803_, v___x_802_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1));
v___x_806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_806_, 0, v_a_795_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
return v___x_806_;
}
else
{
lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_890_; 
lean_inc(v_idx_797_);
lean_inc_ref(v_array_796_);
v_isSharedCheck_890_ = !lean_is_exclusive(v_a_795_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; lean_object* v_unused_892_; 
v_unused_891_ = lean_ctor_get(v_a_795_, 1);
lean_dec(v_unused_891_);
v_unused_892_ = lean_ctor_get(v_a_795_, 0);
lean_dec(v_unused_892_);
v___x_808_ = v_a_795_;
v_isShared_809_ = v_isSharedCheck_890_;
goto v_resetjp_807_;
}
else
{
lean_dec(v_a_795_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_890_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_810_ = lean_unsigned_to_nat(1u);
v___x_811_ = lean_nat_add(v_idx_797_, v___x_810_);
lean_dec(v_idx_797_);
lean_inc(v___x_811_);
lean_inc_ref(v_array_796_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 1, v___x_811_);
v___x_813_ = v___x_808_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_array_796_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_811_);
v___x_813_ = v_reuseFailAlloc_889_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
uint8_t v___x_814_; 
v___x_814_ = lean_nat_dec_lt(v___x_811_, v___x_798_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; 
lean_dec(v___x_811_);
lean_dec_ref(v_array_796_);
v___x_815_ = lean_box(0);
v___x_816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_813_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
return v___x_816_;
}
else
{
uint8_t v_c_817_; uint8_t v___x_818_; uint8_t v___y_820_; uint8_t v___x_886_; 
v_c_817_ = lean_byte_array_fget(v_array_796_, v___x_811_);
v___x_818_ = 48;
v___x_886_ = lean_uint8_dec_le(v___x_818_, v_c_817_);
if (v___x_886_ == 0)
{
v___y_820_ = v___x_886_;
goto v___jp_819_;
}
else
{
uint8_t v___x_887_; uint8_t v___x_888_; 
v___x_887_ = 57;
v___x_888_ = lean_uint8_dec_le(v_c_817_, v___x_887_);
v___y_820_ = v___x_888_;
goto v___jp_819_;
}
v___jp_819_:
{
if (v___y_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec(v___x_811_);
lean_dec_ref(v_array_796_);
v___x_821_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_813_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
return v___x_822_;
}
else
{
lean_object* v___x_823_; lean_object* v_it_x27_824_; uint32_t v___x_825_; uint8_t v___x_826_; uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v_fst_830_; lean_object* v_snd_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_885_; 
lean_dec_ref(v___x_813_);
v___x_823_ = lean_nat_add(v___x_811_, v___x_810_);
lean_dec(v___x_811_);
v_it_x27_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_824_, 0, v_array_796_);
lean_ctor_set(v_it_x27_824_, 1, v___x_823_);
v___x_825_ = lean_uint8_to_uint32(v_c_817_);
v___x_826_ = lean_uint32_to_uint8(v___x_825_);
v___x_827_ = lean_uint8_sub(v___x_826_, v___x_818_);
v___x_828_ = lean_uint8_to_nat(v___x_827_);
v___x_829_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_824_, v___x_828_);
v_fst_830_ = lean_ctor_get(v___x_829_, 0);
v_snd_831_ = lean_ctor_get(v___x_829_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_885_ == 0)
{
v___x_833_ = v___x_829_;
v_isShared_834_ = v_isSharedCheck_885_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_snd_831_);
lean_inc(v_fst_830_);
lean_dec(v___x_829_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_885_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = lean_nat_dec_eq(v_fst_830_, v___x_835_);
if (v___x_836_ == 0)
{
lean_object* v_array_837_; lean_object* v_idx_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v_array_837_ = lean_ctor_get(v_snd_831_, 0);
v_idx_838_ = lean_ctor_get(v_snd_831_, 1);
v___x_839_ = lean_byte_array_size(v_array_837_);
v___x_840_ = lean_nat_dec_lt(v_idx_838_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; 
lean_del_object(v___x_833_);
lean_dec(v_fst_830_);
v___x_841_ = lean_box(0);
v___x_842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_842_, 0, v_snd_831_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
return v___x_842_;
}
else
{
uint8_t v___x_843_; uint8_t v_got_844_; uint8_t v___x_845_; 
v___x_843_ = 32;
v_got_844_ = lean_byte_array_fget(v_array_837_, v_idx_838_);
v___x_845_ = lean_uint8_dec_eq(v_got_844_, v___x_843_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_del_object(v___x_833_);
lean_dec(v_fst_830_);
v___x_846_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
v___x_847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_847_, 0, v_snd_831_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
return v___x_847_;
}
else
{
lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_880_; 
lean_inc(v_idx_838_);
lean_inc_ref(v_array_837_);
v_isSharedCheck_880_ = !lean_is_exclusive(v_snd_831_);
if (v_isSharedCheck_880_ == 0)
{
lean_object* v_unused_881_; lean_object* v_unused_882_; 
v_unused_881_ = lean_ctor_get(v_snd_831_, 1);
lean_dec(v_unused_881_);
v_unused_882_ = lean_ctor_get(v_snd_831_, 0);
lean_dec(v_unused_882_);
v___x_849_ = v_snd_831_;
v_isShared_850_ = v_isSharedCheck_880_;
goto v_resetjp_848_;
}
else
{
lean_dec(v_snd_831_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_880_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_851_ = lean_nat_add(v_idx_838_, v___x_810_);
lean_dec(v_idx_838_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 1, v___x_851_);
v___x_853_ = v___x_849_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_array_837_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v___x_851_);
v___x_853_ = v_reuseFailAlloc_879_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; 
v___x_854_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(v___x_853_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_pos_855_; lean_object* v_res_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_869_; 
v_pos_855_ = lean_ctor_get(v___x_854_, 0);
v_res_856_ = lean_ctor_get(v___x_854_, 1);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_869_ == 0)
{
v___x_858_ = v___x_854_;
v_isShared_859_ = v_isSharedCheck_869_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_res_856_);
lean_inc(v_pos_855_);
lean_dec(v___x_854_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_869_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_860_ = lean_nat_to_int(v_fst_830_);
v___x_861_ = lean_int_neg(v___x_860_);
lean_dec(v___x_860_);
v___x_862_ = lean_nat_abs(v___x_861_);
lean_dec(v___x_861_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v_res_856_);
lean_ctor_set(v___x_833_, 0, v___x_862_);
v___x_864_ = v___x_833_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_res_856_);
v___x_864_ = v_reuseFailAlloc_868_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_866_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 1, v___x_864_);
v___x_866_ = v___x_858_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_pos_855_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
else
{
lean_object* v_pos_870_; lean_object* v_err_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_del_object(v___x_833_);
lean_dec(v_fst_830_);
v_pos_870_ = lean_ctor_get(v___x_854_, 0);
v_err_871_ = lean_ctor_get(v___x_854_, 1);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_854_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_err_871_);
lean_inc(v_pos_870_);
lean_dec(v___x_854_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_pos_870_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_err_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
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
lean_object* v___x_883_; lean_object* v___x_884_; 
lean_del_object(v___x_833_);
lean_dec(v_fst_830_);
v___x_883_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
v___x_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_884_, 0, v_snd_831_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
return v___x_884_;
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(lean_object* v_acc_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_pos_896_; lean_object* v_err_897_; lean_object* v___x_912_; 
lean_inc_ref(v_a_894_);
v___x_912_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(v_a_894_);
if (lean_obj_tag(v___x_912_) == 0)
{
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_pos_913_; lean_object* v_res_914_; lean_object* v___x_915_; 
lean_dec_ref(v_a_894_);
v_pos_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_pos_913_);
v_res_914_ = lean_ctor_get(v___x_912_, 1);
lean_inc(v_res_914_);
lean_dec_ref_known(v___x_912_, 2);
v___x_915_ = lean_array_push(v_acc_893_, v_res_914_);
v_acc_893_ = v___x_915_;
v_a_894_ = v_pos_913_;
goto _start;
}
else
{
lean_object* v_pos_917_; lean_object* v_err_918_; 
v_pos_917_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_pos_917_);
v_err_918_ = lean_ctor_get(v___x_912_, 1);
lean_inc(v_err_918_);
lean_dec_ref_known(v___x_912_, 2);
v_pos_896_ = v_pos_917_;
v_err_897_ = v_err_918_;
goto v___jp_895_;
}
}
else
{
lean_object* v_err_919_; 
v_err_919_ = lean_ctor_get(v___x_912_, 1);
lean_inc(v_err_919_);
lean_dec_ref_known(v___x_912_, 2);
lean_inc_ref(v_a_894_);
v_pos_896_ = v_a_894_;
v_err_897_ = v_err_919_;
goto v___jp_895_;
}
v___jp_895_:
{
lean_object* v_idx_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_910_; 
v_idx_898_ = lean_ctor_get(v_a_894_, 1);
v_isSharedCheck_910_ = !lean_is_exclusive(v_a_894_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v_a_894_, 0);
lean_dec(v_unused_911_);
v___x_900_ = v_a_894_;
v_isShared_901_ = v_isSharedCheck_910_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_idx_898_);
lean_dec(v_a_894_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_910_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v_idx_902_; uint8_t v___x_903_; 
v_idx_902_ = lean_ctor_get(v_pos_896_, 1);
v___x_903_ = lean_nat_dec_eq(v_idx_898_, v_idx_902_);
lean_dec(v_idx_898_);
if (v___x_903_ == 0)
{
lean_object* v___x_905_; 
lean_dec_ref(v_acc_893_);
if (v_isShared_901_ == 0)
{
lean_ctor_set_tag(v___x_900_, 1);
lean_ctor_set(v___x_900_, 1, v_err_897_);
lean_ctor_set(v___x_900_, 0, v_pos_896_);
v___x_905_ = v___x_900_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_pos_896_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_err_897_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
else
{
lean_object* v___x_908_; 
lean_dec(v_err_897_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 1, v_acc_893_);
lean_ctor_set(v___x_900_, 0, v_pos_896_);
v___x_908_ = v___x_900_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_pos_896_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_acc_893_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(lean_object* v_ident_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(v_a_926_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_pos_928_; lean_object* v_res_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_1044_; 
v_pos_928_ = lean_ctor_get(v___x_927_, 0);
v_res_929_ = lean_ctor_get(v___x_927_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_931_ = v___x_927_;
v_isShared_932_ = v_isSharedCheck_1044_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_res_929_);
lean_inc(v_pos_928_);
lean_dec(v___x_927_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_1044_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v_array_933_; lean_object* v_idx_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v_array_933_ = lean_ctor_get(v_pos_928_, 0);
v_idx_934_ = lean_ctor_get(v_pos_928_, 1);
v___x_935_ = lean_byte_array_size(v_array_933_);
v___x_936_ = lean_nat_dec_lt(v_idx_934_, v___x_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; lean_object* v___x_939_; 
lean_dec(v_res_929_);
lean_dec(v_ident_925_);
v___x_937_ = lean_box(0);
if (v_isShared_932_ == 0)
{
lean_ctor_set_tag(v___x_931_, 1);
lean_ctor_set(v___x_931_, 1, v___x_937_);
v___x_939_ = v___x_931_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_pos_928_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
else
{
uint8_t v___x_941_; uint8_t v_got_942_; uint8_t v___x_943_; 
v___x_941_ = 32;
v_got_942_ = lean_byte_array_fget(v_array_933_, v_idx_934_);
v___x_943_ = lean_uint8_dec_eq(v_got_942_, v___x_941_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; lean_object* v___x_946_; 
lean_dec(v_res_929_);
lean_dec(v_ident_925_);
v___x_944_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
if (v_isShared_932_ == 0)
{
lean_ctor_set_tag(v___x_931_, 1);
lean_ctor_set(v___x_931_, 1, v___x_944_);
v___x_946_ = v___x_931_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_pos_928_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
else
{
lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_1041_; 
lean_inc(v_idx_934_);
lean_inc_ref(v_array_933_);
lean_del_object(v___x_931_);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_pos_928_);
if (v_isSharedCheck_1041_ == 0)
{
lean_object* v_unused_1042_; lean_object* v_unused_1043_; 
v_unused_1042_ = lean_ctor_get(v_pos_928_, 1);
lean_dec(v_unused_1042_);
v_unused_1043_ = lean_ctor_get(v_pos_928_, 0);
lean_dec(v_unused_1043_);
v___x_949_ = v_pos_928_;
v_isShared_950_ = v_isSharedCheck_1041_;
goto v_resetjp_948_;
}
else
{
lean_dec(v_pos_928_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_1041_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_951_ = lean_unsigned_to_nat(1u);
v___x_952_ = lean_nat_add(v_idx_934_, v___x_951_);
lean_dec(v_idx_934_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 1, v___x_952_);
v___x_954_ = v___x_949_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_array_933_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v___x_952_);
v___x_954_ = v_reuseFailAlloc_1040_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_955_; 
v___x_955_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(v___x_954_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_pos_956_; lean_object* v_res_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_pos_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_pos_956_);
v_res_957_ = lean_ctor_get(v___x_955_, 1);
lean_inc(v_res_957_);
lean_dec_ref_known(v___x_955_, 2);
v___x_958_ = lean_unsigned_to_nat(0u);
v___x_959_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0));
v___x_960_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(v___x_959_, v_pos_956_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_pos_961_; lean_object* v_res_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1021_; 
v_pos_961_ = lean_ctor_get(v___x_960_, 0);
v_res_962_ = lean_ctor_get(v___x_960_, 1);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_964_ = v___x_960_;
v_isShared_965_ = v_isSharedCheck_1021_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_res_962_);
lean_inc(v_pos_961_);
lean_dec(v___x_960_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1021_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v_array_966_; lean_object* v_idx_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
v_array_966_ = lean_ctor_get(v_pos_961_, 0);
v_idx_967_ = lean_ctor_get(v_pos_961_, 1);
v___x_968_ = lean_byte_array_size(v_array_966_);
v___x_969_ = lean_nat_dec_lt(v_idx_967_, v___x_968_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; lean_object* v___x_972_; 
lean_dec(v_res_962_);
lean_dec(v_res_957_);
lean_dec(v_res_929_);
lean_dec(v_ident_925_);
v___x_970_ = lean_box(0);
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 1);
lean_ctor_set(v___x_964_, 1, v___x_970_);
v___x_972_ = v___x_964_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_pos_961_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
else
{
uint8_t v___x_974_; uint8_t v_got_975_; uint8_t v___x_976_; 
v___x_974_ = 48;
v_got_975_ = lean_byte_array_fget(v_array_966_, v_idx_967_);
v___x_976_ = lean_uint8_dec_eq(v_got_975_, v___x_974_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; lean_object* v___x_979_; 
lean_dec(v_res_962_);
lean_dec(v_res_957_);
lean_dec(v_res_929_);
lean_dec(v_ident_925_);
v___x_977_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1));
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 1);
lean_ctor_set(v___x_964_, 1, v___x_977_);
v___x_979_ = v___x_964_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_pos_961_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
else
{
lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1018_; 
lean_inc(v_idx_967_);
lean_inc_ref(v_array_966_);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_pos_961_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; lean_object* v_unused_1020_; 
v_unused_1019_ = lean_ctor_get(v_pos_961_, 1);
lean_dec(v_unused_1019_);
v_unused_1020_ = lean_ctor_get(v_pos_961_, 0);
lean_dec(v_unused_1020_);
v___x_982_ = v_pos_961_;
v_isShared_983_ = v_isSharedCheck_1018_;
goto v_resetjp_981_;
}
else
{
lean_dec(v_pos_961_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1018_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v___x_986_; 
v___x_984_ = lean_nat_add(v_idx_967_, v___x_951_);
lean_dec(v_idx_967_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 1, v___x_984_);
v___x_986_ = v___x_982_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_array_966_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_984_);
v___x_986_ = v_reuseFailAlloc_1017_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_987_ = lean_array_get_size(v_res_929_);
v___x_988_ = lean_nat_dec_eq(v___x_987_, v___x_958_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_989_ = lean_array_get_size(v_res_962_);
v___x_990_ = lean_nat_dec_eq(v___x_989_, v___x_958_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_991_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_929_);
v___x_992_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_992_, 0, v_ident_925_);
lean_ctor_set(v___x_992_, 1, v_res_929_);
lean_ctor_set(v___x_992_, 2, v___x_991_);
lean_ctor_set(v___x_992_, 3, v_res_957_);
lean_ctor_set(v___x_992_, 4, v_res_962_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v___x_992_);
lean_ctor_set(v___x_964_, 0, v___x_986_);
v___x_994_ = v___x_964_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v___x_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
else
{
lean_object* v___x_996_; uint8_t v___x_997_; 
lean_dec(v_res_962_);
v___x_996_ = lean_array_get_size(v_res_957_);
v___x_997_ = lean_nat_dec_eq(v___x_996_, v___x_958_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_998_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_998_, 0, v_ident_925_);
lean_ctor_set(v___x_998_, 1, v_res_929_);
lean_ctor_set(v___x_998_, 2, v_res_957_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v___x_998_);
lean_ctor_set(v___x_964_, 0, v___x_986_);
v___x_1000_ = v___x_964_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
lean_dec(v_res_957_);
v___x_1002_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_929_);
v___x_1003_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_1003_, 0, v_ident_925_);
lean_ctor_set(v___x_1003_, 1, v_res_929_);
lean_ctor_set(v___x_1003_, 2, v___x_1002_);
lean_ctor_set(v___x_1003_, 3, v___x_959_);
lean_ctor_set(v___x_1003_, 4, v___x_959_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v___x_1003_);
lean_ctor_set(v___x_964_, 0, v___x_986_);
v___x_1005_ = v___x_964_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
else
{
lean_object* v___x_1007_; uint8_t v___x_1008_; 
lean_dec(v_res_929_);
v___x_1007_ = lean_array_get_size(v_res_962_);
lean_dec(v_res_962_);
v___x_1008_ = lean_nat_dec_eq(v___x_1007_, v___x_958_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1011_; 
lean_dec(v_res_957_);
lean_dec(v_ident_925_);
v___x_1009_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2));
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 1);
lean_ctor_set(v___x_964_, 1, v___x_1009_);
lean_ctor_set(v___x_964_, 0, v___x_986_);
v___x_1011_ = v___x_964_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
else
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1013_, 0, v_ident_925_);
lean_ctor_set(v___x_1013_, 1, v_res_957_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v___x_1013_);
lean_ctor_set(v___x_964_, 0, v___x_986_);
v___x_1015_ = v___x_964_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
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
lean_object* v_pos_1022_; lean_object* v_err_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v_res_957_);
lean_dec(v_res_929_);
lean_dec(v_ident_925_);
v_pos_1022_ = lean_ctor_get(v___x_960_, 0);
v_err_1023_ = lean_ctor_get(v___x_960_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_960_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_err_1023_);
lean_inc(v_pos_1022_);
lean_dec(v___x_960_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_pos_1022_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_err_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v_pos_1031_; lean_object* v_err_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v_res_929_);
lean_dec(v_ident_925_);
v_pos_1031_ = lean_ctor_get(v___x_955_, 0);
v_err_1032_ = lean_ctor_get(v___x_955_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_955_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_err_1032_);
lean_inc(v_pos_1031_);
lean_dec(v___x_955_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_pos_1031_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_err_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
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
lean_object* v_pos_1045_; lean_object* v_err_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec(v_ident_925_);
v_pos_1045_ = lean_ctor_get(v___x_927_, 0);
v_err_1046_ = lean_ctor_get(v___x_927_, 1);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_927_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_err_1046_);
lean_inc(v_pos_1045_);
lean_dec(v___x_927_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_pos_1045_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_err_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(lean_object* v_a_1054_){
_start:
{
lean_object* v_array_1055_; lean_object* v_idx_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v_array_1055_ = lean_ctor_get(v_a_1054_, 0);
v_idx_1056_ = lean_ctor_get(v_a_1054_, 1);
v___x_1057_ = lean_byte_array_size(v_array_1055_);
v___x_1058_ = lean_nat_dec_lt(v_idx_1056_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_box(0);
v___x_1060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_a_1054_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
return v___x_1060_;
}
else
{
uint8_t v_c_1061_; uint8_t v___x_1062_; uint8_t v___y_1064_; uint8_t v___x_1130_; 
v_c_1061_ = lean_byte_array_fget(v_array_1055_, v_idx_1056_);
v___x_1062_ = 48;
v___x_1130_ = lean_uint8_dec_le(v___x_1062_, v_c_1061_);
if (v___x_1130_ == 0)
{
v___y_1064_ = v___x_1130_;
goto v___jp_1063_;
}
else
{
uint8_t v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = 57;
v___x_1132_ = lean_uint8_dec_le(v_c_1061_, v___x_1131_);
v___y_1064_ = v___x_1132_;
goto v___jp_1063_;
}
v___jp_1063_:
{
if (v___y_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_1066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_a_1054_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
return v___x_1066_;
}
else
{
lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1127_; 
lean_inc(v_idx_1056_);
lean_inc_ref(v_array_1055_);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_a_1054_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; lean_object* v_unused_1129_; 
v_unused_1128_ = lean_ctor_get(v_a_1054_, 1);
lean_dec(v_unused_1128_);
v_unused_1129_ = lean_ctor_get(v_a_1054_, 0);
lean_dec(v_unused_1129_);
v___x_1068_ = v_a_1054_;
v_isShared_1069_ = v_isSharedCheck_1127_;
goto v_resetjp_1067_;
}
else
{
lean_dec(v_a_1054_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1127_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v_it_x27_1073_; 
v___x_1070_ = lean_unsigned_to_nat(1u);
v___x_1071_ = lean_nat_add(v_idx_1056_, v___x_1070_);
lean_dec(v_idx_1056_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 1, v___x_1071_);
v_it_x27_1073_ = v___x_1068_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_array_1055_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v___x_1071_);
v_it_x27_1073_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
uint32_t v___x_1074_; uint8_t v___x_1075_; uint8_t v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v_fst_1079_; lean_object* v_snd_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1125_; 
v___x_1074_ = lean_uint8_to_uint32(v_c_1061_);
v___x_1075_ = lean_uint32_to_uint8(v___x_1074_);
v___x_1076_ = lean_uint8_sub(v___x_1075_, v___x_1062_);
v___x_1077_ = lean_uint8_to_nat(v___x_1076_);
v___x_1078_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_1073_, v___x_1077_);
v_fst_1079_ = lean_ctor_get(v___x_1078_, 0);
v_snd_1080_ = lean_ctor_get(v___x_1078_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1082_ = v___x_1078_;
v_isShared_1083_ = v_isSharedCheck_1125_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_snd_1080_);
lean_inc(v_fst_1079_);
lean_dec(v___x_1078_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1125_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = lean_unsigned_to_nat(0u);
v___x_1085_ = lean_nat_dec_eq(v_fst_1079_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v_array_1086_; lean_object* v_idx_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v_array_1086_ = lean_ctor_get(v_snd_1080_, 0);
v_idx_1087_ = lean_ctor_get(v_snd_1080_, 1);
v___x_1088_ = lean_byte_array_size(v_array_1086_);
v___x_1089_ = lean_nat_dec_lt(v_idx_1087_, v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1092_; 
lean_dec(v_fst_1079_);
v___x_1090_ = lean_box(0);
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 1);
lean_ctor_set(v___x_1082_, 1, v___x_1090_);
lean_ctor_set(v___x_1082_, 0, v_snd_1080_);
v___x_1092_ = v___x_1082_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_snd_1080_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
else
{
uint8_t v___x_1094_; uint8_t v_got_1095_; uint8_t v___x_1096_; 
v___x_1094_ = 32;
v_got_1095_ = lean_byte_array_fget(v_array_1086_, v_idx_1087_);
v___x_1096_ = lean_uint8_dec_eq(v_got_1095_, v___x_1094_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
lean_dec(v_fst_1079_);
v___x_1097_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 1);
lean_ctor_set(v___x_1082_, 1, v___x_1097_);
lean_ctor_set(v___x_1082_, 0, v_snd_1080_);
v___x_1099_ = v___x_1082_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_snd_1080_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
else
{
lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1118_; 
lean_inc(v_idx_1087_);
lean_inc_ref(v_array_1086_);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_snd_1080_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; lean_object* v_unused_1120_; 
v_unused_1119_ = lean_ctor_get(v_snd_1080_, 1);
lean_dec(v_unused_1119_);
v_unused_1120_ = lean_ctor_get(v_snd_1080_, 0);
lean_dec(v_unused_1120_);
v___x_1102_ = v_snd_1080_;
v_isShared_1103_ = v_isSharedCheck_1118_;
goto v_resetjp_1101_;
}
else
{
lean_dec(v_snd_1080_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1118_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1104_ = lean_nat_add(v_idx_1087_, v___x_1070_);
lean_dec(v_idx_1087_);
lean_inc(v___x_1104_);
lean_inc_ref(v_array_1086_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 1, v___x_1104_);
v___x_1106_ = v___x_1102_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_array_1086_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
uint8_t v___x_1107_; 
v___x_1107_ = lean_nat_dec_lt(v___x_1104_, v___x_1088_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
lean_dec(v___x_1104_);
lean_dec_ref(v_array_1086_);
lean_dec(v_fst_1079_);
v___x_1108_ = lean_box(0);
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 1);
lean_ctor_set(v___x_1082_, 1, v___x_1108_);
lean_ctor_set(v___x_1082_, 0, v___x_1106_);
v___x_1110_ = v___x_1082_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
else
{
uint8_t v___x_1112_; uint8_t v___x_1113_; uint8_t v___x_1114_; 
lean_del_object(v___x_1082_);
v___x_1112_ = lean_byte_array_fget(v_array_1086_, v___x_1104_);
lean_dec(v___x_1104_);
lean_dec_ref(v_array_1086_);
v___x_1113_ = 100;
v___x_1114_ = lean_uint8_dec_eq(v___x_1112_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(v_fst_1079_, v___x_1106_);
return v___x_1115_;
}
else
{
lean_object* v___x_1116_; 
lean_dec(v_fst_1079_);
v___x_1116_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(v___x_1106_);
return v___x_1116_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1121_; lean_object* v___x_1123_; 
lean_dec(v_fst_1079_);
v___x_1121_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 1);
lean_ctor_set(v___x_1082_, 1, v___x_1121_);
lean_ctor_set(v___x_1082_, 0, v_snd_1080_);
v___x_1123_ = v___x_1082_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_snd_1080_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(lean_object* v_acc_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v_array_1138_; lean_object* v_idx_1139_; lean_object* v_pos_1141_; lean_object* v_idx_1142_; lean_object* v_err_1143_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v_array_1138_ = lean_ctor_get(v_a_1137_, 0);
v_idx_1139_ = lean_ctor_get(v_a_1137_, 1);
lean_inc(v_idx_1139_);
v___x_1149_ = lean_byte_array_size(v_array_1138_);
v___x_1150_ = lean_nat_dec_lt(v_idx_1139_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_box(0);
lean_inc(v_idx_1139_);
v_pos_1141_ = v_a_1137_;
v_idx_1142_ = v_idx_1139_;
v_err_1143_ = v___x_1151_;
goto v___jp_1140_;
}
else
{
uint8_t v_c_1152_; uint8_t v___x_1153_; uint8_t v___x_1154_; 
v_c_1152_ = lean_byte_array_fget(v_array_1138_, v_idx_1139_);
v___x_1153_ = 10;
v___x_1154_ = lean_uint8_dec_eq(v_c_1152_, v___x_1153_);
if (v___x_1154_ == 0)
{
uint8_t v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = 13;
v___x_1156_ = lean_uint8_dec_eq(v_c_1152_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1168_; 
lean_inc_ref(v_array_1138_);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_a_1137_);
if (v_isSharedCheck_1168_ == 0)
{
lean_object* v_unused_1169_; lean_object* v_unused_1170_; 
v_unused_1169_ = lean_ctor_get(v_a_1137_, 1);
lean_dec(v_unused_1169_);
v_unused_1170_ = lean_ctor_get(v_a_1137_, 0);
lean_dec(v_unused_1170_);
v___x_1158_ = v_a_1137_;
v_isShared_1159_ = v_isSharedCheck_1168_;
goto v_resetjp_1157_;
}
else
{
lean_dec(v_a_1137_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1168_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v_it_x27_1163_; 
v___x_1160_ = lean_unsigned_to_nat(1u);
v___x_1161_ = lean_nat_add(v_idx_1139_, v___x_1160_);
lean_dec(v_idx_1139_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 1, v___x_1161_);
v_it_x27_1163_ = v___x_1158_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_array_1138_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v___x_1161_);
v_it_x27_1163_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_box(v_c_1152_);
v___x_1165_ = lean_array_push(v_acc_1136_, v___x_1164_);
v_acc_1136_ = v___x_1165_;
v_a_1137_ = v_it_x27_1163_;
goto _start;
}
}
}
else
{
goto v___jp_1147_;
}
}
else
{
goto v___jp_1147_;
}
}
v___jp_1140_:
{
uint8_t v___x_1144_; 
v___x_1144_ = lean_nat_dec_eq(v_idx_1139_, v_idx_1142_);
lean_dec(v_idx_1142_);
lean_dec(v_idx_1139_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; 
lean_dec_ref(v_acc_1136_);
lean_inc(v_err_1143_);
v___x_1145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1145_, 0, v_pos_1141_);
lean_ctor_set(v___x_1145_, 1, v_err_1143_);
return v___x_1145_;
}
else
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1146_, 0, v_pos_1141_);
lean_ctor_set(v___x_1146_, 1, v_acc_1136_);
return v___x_1146_;
}
}
v___jp_1147_:
{
lean_object* v___x_1148_; 
v___x_1148_ = ((lean_object*)(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__1));
lean_inc(v_idx_1139_);
v_pos_1141_ = v_a_1137_;
v_idx_1142_ = v_idx_1139_;
v_err_1143_ = v___x_1148_;
goto v___jp_1140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(lean_object* v_actions_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v_pos_1176_; lean_object* v_array_1177_; lean_object* v_idx_1178_; lean_object* v_pos_1184_; lean_object* v___y_1188_; lean_object* v_array_1199_; lean_object* v_idx_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v_array_1199_ = lean_ctor_get(v_a_1174_, 0);
v_idx_1200_ = lean_ctor_get(v_a_1174_, 1);
v___x_1201_ = lean_byte_array_size(v_array_1199_);
v___x_1202_ = lean_nat_dec_lt(v_idx_1200_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_dec_ref(v_actions_1173_);
v___x_1203_ = lean_box(0);
v___x_1204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1204_, 0, v_a_1174_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
return v___x_1204_;
}
else
{
uint8_t v___x_1205_; uint8_t v___x_1206_; uint8_t v___x_1207_; 
v___x_1205_ = lean_byte_array_fget(v_array_1199_, v_idx_1200_);
v___x_1206_ = 99;
v___x_1207_ = lean_uint8_dec_eq(v___x_1205_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(v_a_1174_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_pos_1209_; lean_object* v_res_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1271_; 
v_pos_1209_ = lean_ctor_get(v___x_1208_, 0);
v_res_1210_ = lean_ctor_get(v___x_1208_, 1);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1212_ = v___x_1208_;
v_isShared_1213_ = v_isSharedCheck_1271_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_res_1210_);
lean_inc(v_pos_1209_);
lean_dec(v___x_1208_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1271_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v_pos_1215_; lean_object* v_array_1216_; lean_object* v_idx_1217_; lean_object* v_pos_1226_; lean_object* v___y_1230_; lean_object* v_array_1241_; lean_object* v_idx_1242_; lean_object* v___y_1244_; lean_object* v_pos_1245_; lean_object* v_idx_1246_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v_array_1241_ = lean_ctor_get(v_pos_1209_, 0);
v_idx_1242_ = lean_ctor_get(v_pos_1209_, 1);
lean_inc(v_idx_1242_);
v___x_1251_ = lean_byte_array_size(v_array_1241_);
v___x_1252_ = lean_nat_dec_lt(v_idx_1242_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_box(0);
lean_inc(v_pos_1209_);
v___x_1254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1254_, 0, v_pos_1209_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
lean_inc(v_idx_1242_);
v___y_1244_ = v___x_1254_;
v_pos_1245_ = v_pos_1209_;
v_idx_1246_ = v_idx_1242_;
goto v___jp_1243_;
}
else
{
uint8_t v___x_1255_; uint8_t v_got_1256_; uint8_t v___x_1257_; 
v___x_1255_ = 10;
v_got_1256_ = lean_byte_array_fget(v_array_1241_, v_idx_1242_);
v___x_1257_ = lean_uint8_dec_eq(v_got_1256_, v___x_1255_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
lean_inc(v_pos_1209_);
v___x_1259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1259_, 0, v_pos_1209_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
lean_inc(v_idx_1242_);
v___y_1244_ = v___x_1259_;
v_pos_1245_ = v_pos_1209_;
v_idx_1246_ = v_idx_1242_;
goto v___jp_1243_;
}
else
{
lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1268_; 
lean_inc_ref(v_array_1241_);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_pos_1209_);
if (v_isSharedCheck_1268_ == 0)
{
lean_object* v_unused_1269_; lean_object* v_unused_1270_; 
v_unused_1269_ = lean_ctor_get(v_pos_1209_, 1);
lean_dec(v_unused_1269_);
v_unused_1270_ = lean_ctor_get(v_pos_1209_, 0);
lean_dec(v_unused_1270_);
v___x_1261_ = v_pos_1209_;
v_isShared_1262_ = v_isSharedCheck_1268_;
goto v_resetjp_1260_;
}
else
{
lean_dec(v_pos_1209_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1268_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1263_ = lean_unsigned_to_nat(1u);
v___x_1264_ = lean_nat_add(v_idx_1242_, v___x_1263_);
lean_dec(v_idx_1242_);
lean_inc(v___x_1264_);
lean_inc_ref(v_array_1241_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v___x_1264_);
v___x_1266_ = v___x_1261_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_array_1241_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
v_pos_1215_ = v___x_1266_;
v_array_1216_ = v_array_1241_;
v_idx_1217_ = v___x_1264_;
goto v___jp_1214_;
}
}
}
}
v___jp_1214_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1218_ = lean_array_push(v_actions_1173_, v_res_1210_);
v___x_1219_ = lean_byte_array_size(v_array_1216_);
lean_dec_ref(v_array_1216_);
v___x_1220_ = lean_nat_dec_lt(v_idx_1217_, v___x_1219_);
lean_dec(v_idx_1217_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1222_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 1, v___x_1218_);
lean_ctor_set(v___x_1212_, 0, v_pos_1215_);
v___x_1222_ = v___x_1212_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_pos_1215_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_1218_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
else
{
lean_del_object(v___x_1212_);
v_actions_1173_ = v___x_1218_;
v_a_1174_ = v_pos_1215_;
goto _start;
}
}
v___jp_1225_:
{
lean_object* v_array_1227_; lean_object* v_idx_1228_; 
v_array_1227_ = lean_ctor_get(v_pos_1226_, 0);
lean_inc_ref(v_array_1227_);
v_idx_1228_ = lean_ctor_get(v_pos_1226_, 1);
lean_inc(v_idx_1228_);
v_pos_1215_ = v_pos_1226_;
v_array_1216_ = v_array_1227_;
v_idx_1217_ = v_idx_1228_;
goto v___jp_1214_;
}
v___jp_1229_:
{
if (lean_obj_tag(v___y_1230_) == 0)
{
lean_object* v_pos_1231_; 
v_pos_1231_ = lean_ctor_get(v___y_1230_, 0);
lean_inc(v_pos_1231_);
lean_dec_ref_known(v___y_1230_, 2);
v_pos_1226_ = v_pos_1231_;
goto v___jp_1225_;
}
else
{
lean_object* v_pos_1232_; lean_object* v_err_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_del_object(v___x_1212_);
lean_dec(v_res_1210_);
lean_dec_ref(v_actions_1173_);
v_pos_1232_ = lean_ctor_get(v___y_1230_, 0);
v_err_1233_ = lean_ctor_get(v___y_1230_, 1);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___y_1230_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___y_1230_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_err_1233_);
lean_inc(v_pos_1232_);
lean_dec(v___y_1230_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_pos_1232_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_err_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
v___jp_1243_:
{
uint8_t v___x_1247_; 
v___x_1247_ = lean_nat_dec_eq(v_idx_1242_, v_idx_1246_);
lean_dec(v_idx_1246_);
lean_dec(v_idx_1242_);
if (v___x_1247_ == 0)
{
lean_dec_ref(v_pos_1245_);
v___y_1230_ = v___y_1244_;
goto v___jp_1229_;
}
else
{
lean_object* v_utf8_1248_; lean_object* v___x_1249_; 
lean_dec_ref(v___y_1244_);
v_utf8_1248_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1);
v___x_1249_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1248_, v_pos_1245_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_pos_1250_; 
v_pos_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_pos_1250_);
lean_dec_ref_known(v___x_1249_, 2);
v_pos_1226_ = v_pos_1250_;
goto v___jp_1225_;
}
else
{
v___y_1230_ = v___x_1249_;
goto v___jp_1229_;
}
}
}
}
}
else
{
lean_object* v_pos_1272_; lean_object* v_err_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref(v_actions_1173_);
v_pos_1272_ = lean_ctor_get(v___x_1208_, 0);
v_err_1273_ = lean_ctor_get(v___x_1208_, 1);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1208_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_err_1273_);
lean_inc(v_pos_1272_);
lean_dec(v___x_1208_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_pos_1272_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_err_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0));
v___x_1282_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(v___x_1281_, v_a_1174_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_pos_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1321_; 
v_pos_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; 
v_unused_1322_ = lean_ctor_get(v___x_1282_, 1);
lean_dec(v_unused_1322_);
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1321_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_pos_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1321_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_array_1287_; lean_object* v_idx_1288_; lean_object* v___y_1290_; lean_object* v_pos_1291_; lean_object* v_idx_1292_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v_array_1287_ = lean_ctor_get(v_pos_1283_, 0);
v_idx_1288_ = lean_ctor_get(v_pos_1283_, 1);
lean_inc(v_idx_1288_);
v___x_1297_ = lean_byte_array_size(v_array_1287_);
v___x_1298_ = lean_nat_dec_lt(v_idx_1288_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1299_ = lean_box(0);
lean_inc(v_pos_1283_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set_tag(v___x_1285_, 1);
lean_ctor_set(v___x_1285_, 1, v___x_1299_);
v___x_1301_ = v___x_1285_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_pos_1283_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_inc(v_idx_1288_);
v___y_1290_ = v___x_1301_;
v_pos_1291_ = v_pos_1283_;
v_idx_1292_ = v_idx_1288_;
goto v___jp_1289_;
}
}
else
{
uint8_t v___x_1303_; uint8_t v_got_1304_; uint8_t v___x_1305_; 
v___x_1303_ = 10;
v_got_1304_ = lean_byte_array_fget(v_array_1287_, v_idx_1288_);
v___x_1305_ = lean_uint8_dec_eq(v_got_1304_, v___x_1303_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1306_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
lean_inc(v_pos_1283_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set_tag(v___x_1285_, 1);
lean_ctor_set(v___x_1285_, 1, v___x_1306_);
v___x_1308_ = v___x_1285_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_pos_1283_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_inc(v_idx_1288_);
v___y_1290_ = v___x_1308_;
v_pos_1291_ = v_pos_1283_;
v_idx_1292_ = v_idx_1288_;
goto v___jp_1289_;
}
}
else
{
lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1318_; 
lean_inc_ref(v_array_1287_);
lean_del_object(v___x_1285_);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_pos_1283_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; lean_object* v_unused_1320_; 
v_unused_1319_ = lean_ctor_get(v_pos_1283_, 1);
lean_dec(v_unused_1319_);
v_unused_1320_ = lean_ctor_get(v_pos_1283_, 0);
lean_dec(v_unused_1320_);
v___x_1311_ = v_pos_1283_;
v_isShared_1312_ = v_isSharedCheck_1318_;
goto v_resetjp_1310_;
}
else
{
lean_dec(v_pos_1283_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1318_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1313_ = lean_unsigned_to_nat(1u);
v___x_1314_ = lean_nat_add(v_idx_1288_, v___x_1313_);
lean_dec(v_idx_1288_);
lean_inc(v___x_1314_);
lean_inc_ref(v_array_1287_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 1, v___x_1314_);
v___x_1316_ = v___x_1311_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_array_1287_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
v_pos_1176_ = v___x_1316_;
v_array_1177_ = v_array_1287_;
v_idx_1178_ = v___x_1314_;
goto v___jp_1175_;
}
}
}
}
v___jp_1289_:
{
uint8_t v___x_1293_; 
v___x_1293_ = lean_nat_dec_eq(v_idx_1288_, v_idx_1292_);
lean_dec(v_idx_1292_);
lean_dec(v_idx_1288_);
if (v___x_1293_ == 0)
{
lean_dec_ref(v_pos_1291_);
v___y_1188_ = v___y_1290_;
goto v___jp_1187_;
}
else
{
lean_object* v_utf8_1294_; lean_object* v___x_1295_; 
lean_dec_ref(v___y_1290_);
v_utf8_1294_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1);
v___x_1295_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1294_, v_pos_1291_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_pos_1296_; 
v_pos_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_pos_1296_);
lean_dec_ref_known(v___x_1295_, 2);
v_pos_1184_ = v_pos_1296_;
goto v___jp_1183_;
}
else
{
v___y_1188_ = v___x_1295_;
goto v___jp_1187_;
}
}
}
}
}
else
{
lean_object* v_pos_1323_; lean_object* v_err_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec_ref(v_actions_1173_);
v_pos_1323_ = lean_ctor_get(v___x_1282_, 0);
v_err_1324_ = lean_ctor_get(v___x_1282_, 1);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1282_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_err_1324_);
lean_inc(v_pos_1323_);
lean_dec(v___x_1282_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_pos_1323_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_err_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
v___jp_1175_:
{
lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = lean_byte_array_size(v_array_1177_);
lean_dec_ref(v_array_1177_);
v___x_1180_ = lean_nat_dec_lt(v_idx_1178_, v___x_1179_);
lean_dec(v_idx_1178_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v_pos_1176_);
lean_ctor_set(v___x_1181_, 1, v_actions_1173_);
return v___x_1181_;
}
else
{
v_a_1174_ = v_pos_1176_;
goto _start;
}
}
v___jp_1183_:
{
lean_object* v_array_1185_; lean_object* v_idx_1186_; 
v_array_1185_ = lean_ctor_get(v_pos_1184_, 0);
lean_inc_ref(v_array_1185_);
v_idx_1186_ = lean_ctor_get(v_pos_1184_, 1);
lean_inc(v_idx_1186_);
v_pos_1176_ = v_pos_1184_;
v_array_1177_ = v_array_1185_;
v_idx_1178_ = v_idx_1186_;
goto v___jp_1175_;
}
v___jp_1187_:
{
if (lean_obj_tag(v___y_1188_) == 0)
{
lean_object* v_pos_1189_; 
v_pos_1189_ = lean_ctor_get(v___y_1188_, 0);
lean_inc(v_pos_1189_);
lean_dec_ref_known(v___y_1188_, 2);
v_pos_1184_ = v_pos_1189_;
goto v___jp_1183_;
}
else
{
lean_object* v_pos_1190_; lean_object* v_err_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec_ref(v_actions_1173_);
v_pos_1190_ = lean_ctor_get(v___y_1188_, 0);
v_err_1191_ = lean_ctor_get(v___y_1188_, 1);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___y_1188_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___y_1188_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_err_1191_);
lean_inc(v_pos_1190_);
lean_dec(v___y_1188_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_pos_1190_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_err_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(lean_object* v_a_1334_){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0));
v___x_1336_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(v___x_1335_, v_a_1334_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero(lean_object* v_a_1340_){
_start:
{
lean_object* v_array_1341_; lean_object* v_idx_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v_array_1341_ = lean_ctor_get(v_a_1340_, 0);
v_idx_1342_ = lean_ctor_get(v_a_1340_, 1);
v___x_1343_ = lean_byte_array_size(v_array_1341_);
v___x_1344_ = lean_nat_dec_lt(v_idx_1342_, v___x_1343_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_box(0);
v___x_1346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1346_, 0, v_a_1340_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
return v___x_1346_;
}
else
{
uint8_t v___x_1347_; uint8_t v_got_1348_; uint8_t v___x_1349_; 
v___x_1347_ = 0;
v_got_1348_ = lean_byte_array_fget(v_array_1341_, v_idx_1342_);
v___x_1349_ = lean_uint8_dec_eq(v_got_1348_, v___x_1347_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
v___x_1351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1351_, 0, v_a_1340_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
return v___x_1351_;
}
else
{
lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1362_; 
lean_inc(v_idx_1342_);
lean_inc_ref(v_array_1341_);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_a_1340_);
if (v_isSharedCheck_1362_ == 0)
{
lean_object* v_unused_1363_; lean_object* v_unused_1364_; 
v_unused_1363_ = lean_ctor_get(v_a_1340_, 1);
lean_dec(v_unused_1363_);
v_unused_1364_ = lean_ctor_get(v_a_1340_, 0);
lean_dec(v_unused_1364_);
v___x_1353_ = v_a_1340_;
v_isShared_1354_ = v_isSharedCheck_1362_;
goto v_resetjp_1352_;
}
else
{
lean_dec(v_a_1340_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1362_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1355_ = lean_unsigned_to_nat(1u);
v___x_1356_ = lean_nat_add(v_idx_1342_, v___x_1355_);
lean_dec(v_idx_1342_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 1, v___x_1356_);
v___x_1358_ = v___x_1353_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_array_1341_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = lean_box(0);
v___x_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
return v___x_1360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(uint64_t v_uidx_1371_, uint64_t v_shift_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_array_1374_; lean_object* v_idx_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v_array_1374_ = lean_ctor_get(v_a_1373_, 0);
v_idx_1375_ = lean_ctor_get(v_a_1373_, 1);
v___x_1376_ = lean_byte_array_size(v_array_1374_);
v___x_1377_ = lean_nat_dec_lt(v_idx_1375_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_box(0);
v___x_1379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1379_, 0, v_a_1373_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
return v___x_1379_;
}
else
{
lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1425_; 
lean_inc(v_idx_1375_);
lean_inc_ref(v_array_1374_);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_a_1373_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; lean_object* v_unused_1427_; 
v_unused_1426_ = lean_ctor_get(v_a_1373_, 1);
lean_dec(v_unused_1426_);
v_unused_1427_ = lean_ctor_get(v_a_1373_, 0);
lean_dec(v_unused_1427_);
v___x_1381_ = v_a_1373_;
v_isShared_1382_ = v_isSharedCheck_1425_;
goto v_resetjp_1380_;
}
else
{
lean_dec(v_a_1373_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1425_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
uint8_t v_c_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v_it_x27_1387_; 
v_c_1383_ = lean_byte_array_fget(v_array_1374_, v_idx_1375_);
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = lean_nat_add(v_idx_1375_, v___x_1384_);
lean_dec(v_idx_1375_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 1, v___x_1385_);
v_it_x27_1387_ = v___x_1381_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_array_1374_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v___x_1385_);
v_it_x27_1387_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
uint64_t v___x_1416_; uint8_t v___x_1417_; 
v___x_1416_ = 28ULL;
v___x_1417_ = lean_uint64_dec_eq(v_shift_1372_, v___x_1416_);
if (v___x_1417_ == 0)
{
goto v___jp_1388_;
}
else
{
uint8_t v___x_1418_; uint8_t v___x_1419_; uint8_t v___x_1420_; uint8_t v___x_1421_; 
v___x_1418_ = 240;
v___x_1419_ = lean_uint8_land(v_c_1383_, v___x_1418_);
v___x_1420_ = 0;
v___x_1421_ = lean_uint8_dec_eq(v___x_1419_, v___x_1420_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3));
v___x_1423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1423_, 0, v_it_x27_1387_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
return v___x_1423_;
}
else
{
goto v___jp_1388_;
}
}
v___jp_1388_:
{
uint8_t v___x_1389_; uint8_t v___x_1390_; 
v___x_1389_ = 0;
v___x_1390_ = lean_uint8_dec_eq(v_c_1383_, v___x_1389_);
if (v___x_1390_ == 0)
{
uint8_t v___x_1391_; uint8_t v___x_1392_; uint64_t v___x_1393_; uint64_t v___x_1394_; uint64_t v___x_1395_; uint8_t v___x_1396_; uint8_t v___x_1397_; uint8_t v___x_1398_; 
v___x_1391_ = 127;
v___x_1392_ = lean_uint8_land(v_c_1383_, v___x_1391_);
v___x_1393_ = lean_uint8_to_uint64(v___x_1392_);
v___x_1394_ = lean_uint64_shift_left(v___x_1393_, v_shift_1372_);
v___x_1395_ = lean_uint64_lor(v_uidx_1371_, v___x_1394_);
v___x_1396_ = 128;
v___x_1397_ = lean_uint8_land(v_c_1383_, v___x_1396_);
v___x_1398_ = lean_uint8_dec_eq(v___x_1397_, v___x_1389_);
if (v___x_1398_ == 0)
{
uint64_t v___x_1399_; uint64_t v___x_1400_; 
v___x_1399_ = 7ULL;
v___x_1400_ = lean_uint64_add(v_shift_1372_, v___x_1399_);
v_uidx_1371_ = v___x_1395_;
v_shift_1372_ = v___x_1400_;
v_a_1373_ = v_it_x27_1387_;
goto _start;
}
else
{
uint64_t v___x_1402_; uint64_t v___x_1403_; uint64_t v___x_1404_; uint64_t v___x_1405_; uint8_t v___x_1406_; 
v___x_1402_ = 1ULL;
v___x_1403_ = lean_uint64_shift_right(v___x_1395_, v___x_1402_);
v___x_1404_ = lean_uint64_land(v___x_1402_, v___x_1395_);
v___x_1405_ = 0ULL;
v___x_1406_ = lean_uint64_dec_eq(v___x_1404_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1407_ = lean_uint64_to_nat(v___x_1403_);
v___x_1408_ = lean_nat_to_int(v___x_1407_);
v___x_1409_ = lean_int_neg(v___x_1408_);
lean_dec(v___x_1408_);
v___x_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1410_, 0, v_it_x27_1387_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
return v___x_1410_;
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1411_ = lean_uint64_to_nat(v___x_1403_);
v___x_1412_ = lean_nat_to_int(v___x_1411_);
v___x_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1413_, 0, v_it_x27_1387_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
return v___x_1413_;
}
}
}
else
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1));
v___x_1415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1415_, 0, v_it_x27_1387_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
return v___x_1415_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___boxed(lean_object* v_uidx_1428_, lean_object* v_shift_1429_, lean_object* v_a_1430_){
_start:
{
uint64_t v_uidx_boxed_1431_; uint64_t v_shift_boxed_1432_; lean_object* v_res_1433_; 
v_uidx_boxed_1431_ = lean_unbox_uint64(v_uidx_1428_);
lean_dec_ref(v_uidx_1428_);
v_shift_boxed_1432_ = lean_unbox_uint64(v_shift_1429_);
lean_dec_ref(v_shift_1429_);
v_res_1433_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(v_uidx_boxed_1431_, v_shift_boxed_1432_, v_a_1430_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(lean_object* v_a_1434_){
_start:
{
uint64_t v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = 0ULL;
v___x_1436_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(v___x_1435_, v___x_1435_, v_a_1434_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg(lean_object* v_a_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1440_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_pos_1442_; lean_object* v_res_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1457_; 
v_pos_1442_ = lean_ctor_get(v___x_1441_, 0);
v_res_1443_ = lean_ctor_get(v___x_1441_, 1);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1445_ = v___x_1441_;
v_isShared_1446_ = v_isSharedCheck_1457_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_res_1443_);
lean_inc(v_pos_1442_);
lean_dec(v___x_1441_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1457_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1448_ = lean_int_dec_lt(v_res_1443_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
lean_dec(v_res_1443_);
v___x_1449_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1));
if (v_isShared_1446_ == 0)
{
lean_ctor_set_tag(v___x_1445_, 1);
lean_ctor_set(v___x_1445_, 1, v___x_1449_);
v___x_1451_ = v___x_1445_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_pos_1442_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
else
{
lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1453_ = lean_nat_abs(v_res_1443_);
lean_dec(v_res_1443_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 1, v___x_1453_);
v___x_1455_ = v___x_1445_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_pos_1442_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
else
{
lean_object* v_pos_1458_; lean_object* v_err_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
v_pos_1458_ = lean_ctor_get(v___x_1441_, 0);
v_err_1459_ = lean_ctor_get(v___x_1441_, 1);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1441_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_err_1459_);
lean_inc(v_pos_1458_);
lean_dec(v___x_1441_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_pos_1458_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_err_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos(lean_object* v_a_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1470_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_pos_1472_; lean_object* v_res_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1487_; 
v_pos_1472_ = lean_ctor_get(v___x_1471_, 0);
v_res_1473_ = lean_ctor_get(v___x_1471_, 1);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1475_ = v___x_1471_;
v_isShared_1476_ = v_isSharedCheck_1487_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_res_1473_);
lean_inc(v_pos_1472_);
lean_dec(v___x_1471_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1487_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1478_ = lean_int_dec_lt(v___x_1477_, v_res_1473_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1481_; 
lean_dec(v_res_1473_);
v___x_1479_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1476_ == 0)
{
lean_ctor_set_tag(v___x_1475_, 1);
lean_ctor_set(v___x_1475_, 1, v___x_1479_);
v___x_1481_ = v___x_1475_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_pos_1472_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1485_; 
v___x_1483_ = lean_nat_abs(v_res_1473_);
lean_dec(v_res_1473_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v___x_1483_);
v___x_1485_ = v___x_1475_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_pos_1472_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
else
{
lean_object* v_pos_1488_; lean_object* v_err_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
v_pos_1488_ = lean_ctor_get(v___x_1471_, 0);
v_err_1489_ = lean_ctor_get(v___x_1471_, 1);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1471_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_err_1489_);
lean_inc(v_pos_1488_);
lean_dec(v___x_1471_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_pos_1488_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_err_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId(lean_object* v_a_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1497_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_pos_1499_; lean_object* v_res_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1514_; 
v_pos_1499_ = lean_ctor_get(v___x_1498_, 0);
v_res_1500_ = lean_ctor_get(v___x_1498_, 1);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1502_ = v___x_1498_;
v_isShared_1503_ = v_isSharedCheck_1514_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_res_1500_);
lean_inc(v_pos_1499_);
lean_dec(v___x_1498_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1514_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1504_; uint8_t v___x_1505_; 
v___x_1504_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1505_ = lean_int_dec_lt(v___x_1504_, v_res_1500_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1508_; 
lean_dec(v_res_1500_);
v___x_1506_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1503_ == 0)
{
lean_ctor_set_tag(v___x_1502_, 1);
lean_ctor_set(v___x_1502_, 1, v___x_1506_);
v___x_1508_ = v___x_1502_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_pos_1499_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
else
{
lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1510_ = lean_nat_abs(v_res_1500_);
lean_dec(v_res_1500_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 1, v___x_1510_);
v___x_1512_ = v___x_1502_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_pos_1499_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
else
{
lean_object* v_pos_1515_; lean_object* v_err_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
v_pos_1515_ = lean_ctor_get(v___x_1498_, 0);
v_err_1516_ = lean_ctor_get(v___x_1498_, 1);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1498_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_err_1516_);
lean_inc(v_pos_1515_);
lean_dec(v___x_1498_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_pos_1515_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_err_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(lean_object* v_parser_1524_, lean_object* v_acc_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v_array_1527_; lean_object* v_idx_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v_array_1527_ = lean_ctor_get(v_a_1526_, 0);
v_idx_1528_ = lean_ctor_get(v_a_1526_, 1);
v___x_1529_ = lean_byte_array_size(v_array_1527_);
v___x_1530_ = lean_nat_dec_lt(v_idx_1528_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_dec_ref(v_acc_1525_);
lean_dec_ref(v_parser_1524_);
v___x_1531_ = lean_box(0);
v___x_1532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1532_, 0, v_a_1526_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
return v___x_1532_;
}
else
{
uint8_t v___x_1533_; uint8_t v___x_1534_; uint8_t v___x_1535_; 
v___x_1533_ = lean_byte_array_fget(v_array_1527_, v_idx_1528_);
v___x_1534_ = 0;
v___x_1535_ = lean_uint8_dec_eq(v___x_1533_, v___x_1534_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; 
lean_inc_ref(v_parser_1524_);
v___x_1536_ = lean_apply_1(v_parser_1524_, v_a_1526_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_pos_1537_; lean_object* v_res_1538_; lean_object* v___x_1539_; 
v_pos_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_pos_1537_);
v_res_1538_ = lean_ctor_get(v___x_1536_, 1);
lean_inc(v_res_1538_);
lean_dec_ref_known(v___x_1536_, 2);
v___x_1539_ = lean_array_push(v_acc_1525_, v_res_1538_);
v_acc_1525_ = v___x_1539_;
v_a_1526_ = v_pos_1537_;
goto _start;
}
else
{
lean_object* v_pos_1541_; lean_object* v_err_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_dec_ref(v_acc_1525_);
lean_dec_ref(v_parser_1524_);
v_pos_1541_ = lean_ctor_get(v___x_1536_, 0);
v_err_1542_ = lean_ctor_get(v___x_1536_, 1);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1536_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_err_1542_);
lean_inc(v_pos_1541_);
lean_dec(v___x_1536_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_pos_1541_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_err_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
else
{
lean_object* v___x_1550_; 
lean_dec_ref(v_parser_1524_);
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v_a_1526_);
lean_ctor_set(v___x_1550_, 1, v_acc_1525_);
return v___x_1550_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go(lean_object* v_00_u03b1_1551_, lean_object* v_parser_1552_, lean_object* v_acc_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(v_parser_1552_, v_acc_1553_, v_a_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(lean_object* v_parser_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0));
v___x_1561_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(v_parser_1558_, v___x_1560_, v_a_1559_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero(lean_object* v_00_u03b1_1562_, lean_object* v_parser_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v_parser_1563_, v_a_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(lean_object* v_parser_1566_, lean_object* v_acc_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v_array_1569_; lean_object* v_idx_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; 
v_array_1569_ = lean_ctor_get(v_a_1568_, 0);
v_idx_1570_ = lean_ctor_get(v_a_1568_, 1);
v___x_1571_ = lean_byte_array_size(v_array_1569_);
v___x_1572_ = lean_nat_dec_lt(v_idx_1570_, v___x_1571_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_dec_ref(v_acc_1567_);
lean_dec_ref(v_parser_1566_);
v___x_1573_ = lean_box(0);
v___x_1574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1574_, 0, v_a_1568_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
return v___x_1574_;
}
else
{
uint8_t v___x_1575_; uint8_t v___x_1576_; uint8_t v___x_1577_; uint8_t v___x_1578_; uint8_t v___x_1579_; 
v___x_1575_ = lean_byte_array_fget(v_array_1569_, v_idx_1570_);
v___x_1576_ = 1;
v___x_1577_ = lean_uint8_land(v___x_1576_, v___x_1575_);
v___x_1578_ = 0;
v___x_1579_ = lean_uint8_dec_eq(v___x_1577_, v___x_1578_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; 
lean_dec_ref(v_parser_1566_);
v___x_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1580_, 0, v_a_1568_);
lean_ctor_set(v___x_1580_, 1, v_acc_1567_);
return v___x_1580_;
}
else
{
uint8_t v___x_1581_; 
v___x_1581_ = lean_uint8_dec_eq(v___x_1575_, v___x_1578_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; 
lean_inc_ref(v_parser_1566_);
v___x_1582_ = lean_apply_1(v_parser_1566_, v_a_1568_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_pos_1583_; lean_object* v_res_1584_; lean_object* v___x_1585_; 
v_pos_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_pos_1583_);
v_res_1584_ = lean_ctor_get(v___x_1582_, 1);
lean_inc(v_res_1584_);
lean_dec_ref_known(v___x_1582_, 2);
v___x_1585_ = lean_array_push(v_acc_1567_, v_res_1584_);
v_acc_1567_ = v___x_1585_;
v_a_1568_ = v_pos_1583_;
goto _start;
}
else
{
lean_object* v_pos_1587_; lean_object* v_err_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec_ref(v_acc_1567_);
lean_dec_ref(v_parser_1566_);
v_pos_1587_ = lean_ctor_get(v___x_1582_, 0);
v_err_1588_ = lean_ctor_get(v___x_1582_, 1);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1582_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_err_1588_);
lean_inc(v_pos_1587_);
lean_dec(v___x_1582_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_pos_1587_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_err_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
else
{
lean_object* v___x_1596_; 
lean_dec_ref(v_parser_1566_);
v___x_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1596_, 0, v_a_1568_);
lean_ctor_set(v___x_1596_, 1, v_acc_1567_);
return v___x_1596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go(lean_object* v_00_u03b1_1597_, lean_object* v_parser_1598_, lean_object* v_acc_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(v_parser_1598_, v_acc_1599_, v_a_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(lean_object* v_parser_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0));
v___x_1605_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(v_parser_1602_, v___x_1604_, v_a_1603_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero(lean_object* v_00_u03b1_1606_, lean_object* v_parser_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(v_parser_1607_, v_a_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList(lean_object* v_a_1610_){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId), 1, 0);
v___x_1612_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(v___x_1611_, v_a_1610_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause(lean_object* v_a_1613_){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit), 1, 0);
v___x_1615_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v___x_1614_, v_a_1613_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(lean_object* v_acc_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_array_1618_; lean_object* v_idx_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v_array_1618_ = lean_ctor_get(v_a_1617_, 0);
v_idx_1619_ = lean_ctor_get(v_a_1617_, 1);
v___x_1620_ = lean_byte_array_size(v_array_1618_);
v___x_1621_ = lean_nat_dec_lt(v_idx_1619_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
lean_dec_ref(v_acc_1616_);
v___x_1622_ = lean_box(0);
v___x_1623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1623_, 0, v_a_1617_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
return v___x_1623_;
}
else
{
uint8_t v___x_1624_; uint8_t v___x_1625_; uint8_t v___x_1626_; uint8_t v___x_1627_; uint8_t v___x_1628_; 
v___x_1624_ = lean_byte_array_fget(v_array_1618_, v_idx_1619_);
v___x_1625_ = 1;
v___x_1626_ = lean_uint8_land(v___x_1625_, v___x_1624_);
v___x_1627_ = 0;
v___x_1628_ = lean_uint8_dec_eq(v___x_1626_, v___x_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1629_, 0, v_a_1617_);
lean_ctor_set(v___x_1629_, 1, v_acc_1616_);
return v___x_1629_;
}
else
{
uint8_t v___x_1630_; 
v___x_1630_ = lean_uint8_dec_eq(v___x_1624_, v___x_1627_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1617_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_pos_1632_; lean_object* v_res_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1646_; 
v_pos_1632_ = lean_ctor_get(v___x_1631_, 0);
v_res_1633_ = lean_ctor_get(v___x_1631_, 1);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1635_ = v___x_1631_;
v_isShared_1636_ = v_isSharedCheck_1646_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_res_1633_);
lean_inc(v_pos_1632_);
lean_dec(v___x_1631_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1646_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1638_ = lean_int_dec_lt(v___x_1637_, v_res_1633_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
lean_dec(v_res_1633_);
lean_dec_ref(v_acc_1616_);
v___x_1639_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1636_ == 0)
{
lean_ctor_set_tag(v___x_1635_, 1);
lean_ctor_set(v___x_1635_, 1, v___x_1639_);
v___x_1641_ = v___x_1635_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_pos_1632_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
else
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_del_object(v___x_1635_);
v___x_1643_ = lean_nat_abs(v_res_1633_);
lean_dec(v_res_1633_);
v___x_1644_ = lean_array_push(v_acc_1616_, v___x_1643_);
v_acc_1616_ = v___x_1644_;
v_a_1617_ = v_pos_1632_;
goto _start;
}
}
}
else
{
lean_object* v_pos_1647_; lean_object* v_err_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_dec_ref(v_acc_1616_);
v_pos_1647_ = lean_ctor_get(v___x_1631_, 0);
v_err_1648_ = lean_ctor_get(v___x_1631_, 1);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1631_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_err_1648_);
lean_inc(v_pos_1647_);
lean_dec(v___x_1631_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_pos_1647_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_err_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
else
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v_a_1617_);
lean_ctor_set(v___x_1656_, 1, v_acc_1616_);
return v___x_1656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(lean_object* v_a_1657_){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0));
v___x_1659_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(v___x_1658_, v_a_1657_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(lean_object* v_a_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1660_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_pos_1662_; lean_object* v_res_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1694_; 
v_pos_1662_ = lean_ctor_get(v___x_1661_, 0);
v_res_1663_ = lean_ctor_get(v___x_1661_, 1);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1665_ = v___x_1661_;
v_isShared_1666_ = v_isSharedCheck_1694_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_res_1663_);
lean_inc(v_pos_1662_);
lean_dec(v___x_1661_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1694_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; uint8_t v___x_1668_; 
v___x_1667_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1668_ = lean_int_dec_lt(v_res_1663_, v___x_1667_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; lean_object* v___x_1671_; 
lean_dec(v_res_1663_);
v___x_1669_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1));
if (v_isShared_1666_ == 0)
{
lean_ctor_set_tag(v___x_1665_, 1);
lean_ctor_set(v___x_1665_, 1, v___x_1669_);
v___x_1671_ = v___x_1665_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_pos_1662_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
else
{
lean_object* v___x_1673_; 
lean_del_object(v___x_1665_);
v___x_1673_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v_pos_1662_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_pos_1674_; lean_object* v_res_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1684_; 
v_pos_1674_ = lean_ctor_get(v___x_1673_, 0);
v_res_1675_ = lean_ctor_get(v___x_1673_, 1);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1677_ = v___x_1673_;
v_isShared_1678_ = v_isSharedCheck_1684_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_res_1675_);
lean_inc(v_pos_1674_);
lean_dec(v___x_1673_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1684_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1679_ = lean_nat_abs(v_res_1663_);
lean_dec(v_res_1663_);
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set(v___x_1680_, 1, v_res_1675_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 1, v___x_1680_);
v___x_1682_ = v___x_1677_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_pos_1674_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
else
{
lean_object* v_pos_1685_; lean_object* v_err_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_res_1663_);
v_pos_1685_ = lean_ctor_get(v___x_1673_, 0);
v_err_1686_ = lean_ctor_get(v___x_1673_, 1);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1673_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_err_1686_);
lean_inc(v_pos_1685_);
lean_dec(v___x_1673_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_pos_1685_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_err_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1695_; lean_object* v_err_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
v_pos_1695_ = lean_ctor_get(v___x_1661_, 0);
v_err_1696_ = lean_ctor_get(v___x_1661_, 1);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1661_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_err_1696_);
lean_inc(v_pos_1695_);
lean_dec(v___x_1661_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_pos_1695_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_err_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints(lean_object* v_a_1704_){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes), 1, 0);
v___x_1706_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v___x_1705_, v_a_1704_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(lean_object* v_acc_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v_array_1709_; lean_object* v_idx_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v_array_1709_ = lean_ctor_get(v_a_1708_, 0);
v_idx_1710_ = lean_ctor_get(v_a_1708_, 1);
v___x_1711_ = lean_byte_array_size(v_array_1709_);
v___x_1712_ = lean_nat_dec_lt(v_idx_1710_, v___x_1711_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec_ref(v_acc_1707_);
v___x_1713_ = lean_box(0);
v___x_1714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1714_, 0, v_a_1708_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
return v___x_1714_;
}
else
{
uint8_t v___x_1715_; uint8_t v___x_1716_; uint8_t v___x_1717_; 
v___x_1715_ = lean_byte_array_fget(v_array_1709_, v_idx_1710_);
v___x_1716_ = 0;
v___x_1717_ = lean_uint8_dec_eq(v___x_1715_, v___x_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1708_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_pos_1719_; lean_object* v_res_1720_; lean_object* v___x_1721_; 
v_pos_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_pos_1719_);
v_res_1720_ = lean_ctor_get(v___x_1718_, 1);
lean_inc(v_res_1720_);
lean_dec_ref_known(v___x_1718_, 2);
v___x_1721_ = lean_array_push(v_acc_1707_, v_res_1720_);
v_acc_1707_ = v___x_1721_;
v_a_1708_ = v_pos_1719_;
goto _start;
}
else
{
lean_object* v_pos_1723_; lean_object* v_err_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec_ref(v_acc_1707_);
v_pos_1723_ = lean_ctor_get(v___x_1718_, 0);
v_err_1724_ = lean_ctor_get(v___x_1718_, 1);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1718_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_err_1724_);
lean_inc(v_pos_1723_);
lean_dec(v___x_1718_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_pos_1723_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_err_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
else
{
lean_object* v___x_1732_; 
v___x_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1732_, 0, v_a_1708_);
lean_ctor_set(v___x_1732_, 1, v_acc_1707_);
return v___x_1732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(lean_object* v_a_1733_){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0));
v___x_1735_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(v___x_1734_, v_a_1733_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1_spec__2(lean_object* v_acc_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_array_1738_; lean_object* v_idx_1739_; lean_object* v___x_1740_; uint8_t v___x_1741_; 
v_array_1738_ = lean_ctor_get(v_a_1737_, 0);
v_idx_1739_ = lean_ctor_get(v_a_1737_, 1);
v___x_1740_ = lean_byte_array_size(v_array_1738_);
v___x_1741_ = lean_nat_dec_lt(v_idx_1739_, v___x_1740_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
lean_dec_ref(v_acc_1736_);
v___x_1742_ = lean_box(0);
v___x_1743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1743_, 0, v_a_1737_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
return v___x_1743_;
}
else
{
uint8_t v___x_1744_; uint8_t v___x_1745_; uint8_t v___x_1746_; 
v___x_1744_ = lean_byte_array_fget(v_array_1738_, v_idx_1739_);
v___x_1745_ = 0;
v___x_1746_ = lean_uint8_dec_eq(v___x_1744_, v___x_1745_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(v_a_1737_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_pos_1748_; lean_object* v_res_1749_; lean_object* v___x_1750_; 
v_pos_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_pos_1748_);
v_res_1749_ = lean_ctor_get(v___x_1747_, 1);
lean_inc(v_res_1749_);
lean_dec_ref_known(v___x_1747_, 2);
v___x_1750_ = lean_array_push(v_acc_1736_, v_res_1749_);
v_acc_1736_ = v___x_1750_;
v_a_1737_ = v_pos_1748_;
goto _start;
}
else
{
lean_object* v_pos_1752_; lean_object* v_err_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec_ref(v_acc_1736_);
v_pos_1752_ = lean_ctor_get(v___x_1747_, 0);
v_err_1753_ = lean_ctor_get(v___x_1747_, 1);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1747_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_err_1753_);
lean_inc(v_pos_1752_);
lean_dec(v___x_1747_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_pos_1752_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_err_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
else
{
lean_object* v___x_1761_; 
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v_a_1737_);
lean_ctor_set(v___x_1761_, 1, v_acc_1736_);
return v___x_1761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1(lean_object* v_a_1762_){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0));
v___x_1764_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1_spec__2(v___x_1763_, v_a_1762_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(lean_object* v_a_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1765_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_pos_1767_; lean_object* v_res_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1905_; 
v_pos_1767_ = lean_ctor_get(v___x_1766_, 0);
v_res_1768_ = lean_ctor_get(v___x_1766_, 1);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1770_ = v___x_1766_;
v_isShared_1771_ = v_isSharedCheck_1905_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_res_1768_);
lean_inc(v_pos_1767_);
lean_dec(v___x_1766_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1905_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1772_ = lean_unsigned_to_nat(0u);
v___x_1773_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1774_ = lean_int_dec_lt(v___x_1773_, v_res_1768_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
lean_dec(v_res_1768_);
v___x_1775_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1771_ == 0)
{
lean_ctor_set_tag(v___x_1770_, 1);
lean_ctor_set(v___x_1770_, 1, v___x_1775_);
v___x_1777_ = v___x_1770_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_pos_1767_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
else
{
lean_object* v___x_1779_; 
lean_del_object(v___x_1770_);
v___x_1779_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(v_pos_1767_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_pos_1780_; lean_object* v_res_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1895_; 
v_pos_1780_ = lean_ctor_get(v___x_1779_, 0);
v_res_1781_ = lean_ctor_get(v___x_1779_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1783_ = v___x_1779_;
v_isShared_1784_ = v_isSharedCheck_1895_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_res_1781_);
lean_inc(v_pos_1780_);
lean_dec(v___x_1779_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1895_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v_array_1785_; lean_object* v_idx_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; 
v_array_1785_ = lean_ctor_get(v_pos_1780_, 0);
v_idx_1786_ = lean_ctor_get(v_pos_1780_, 1);
v___x_1787_ = lean_byte_array_size(v_array_1785_);
v___x_1788_ = lean_nat_dec_lt(v_idx_1786_, v___x_1787_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; lean_object* v___x_1791_; 
lean_dec(v_res_1781_);
lean_dec(v_res_1768_);
v___x_1789_ = lean_box(0);
if (v_isShared_1784_ == 0)
{
lean_ctor_set_tag(v___x_1783_, 1);
lean_ctor_set(v___x_1783_, 1, v___x_1789_);
v___x_1791_ = v___x_1783_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_pos_1780_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
else
{
uint8_t v___x_1793_; uint8_t v_got_1794_; uint8_t v___x_1795_; 
v___x_1793_ = 0;
v_got_1794_ = lean_byte_array_fget(v_array_1785_, v_idx_1786_);
v___x_1795_ = lean_uint8_dec_eq(v_got_1794_, v___x_1793_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; lean_object* v___x_1798_; 
lean_dec(v_res_1781_);
lean_dec(v_res_1768_);
v___x_1796_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
if (v_isShared_1784_ == 0)
{
lean_ctor_set_tag(v___x_1783_, 1);
lean_ctor_set(v___x_1783_, 1, v___x_1796_);
v___x_1798_ = v___x_1783_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_pos_1780_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
else
{
lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1892_; 
lean_inc(v_idx_1786_);
lean_inc_ref(v_array_1785_);
lean_del_object(v___x_1783_);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_pos_1780_);
if (v_isSharedCheck_1892_ == 0)
{
lean_object* v_unused_1893_; lean_object* v_unused_1894_; 
v_unused_1893_ = lean_ctor_get(v_pos_1780_, 1);
lean_dec(v_unused_1893_);
v_unused_1894_ = lean_ctor_get(v_pos_1780_, 0);
lean_dec(v_unused_1894_);
v___x_1801_ = v_pos_1780_;
v_isShared_1802_ = v_isSharedCheck_1892_;
goto v_resetjp_1800_;
}
else
{
lean_dec(v_pos_1780_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1892_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1803_ = lean_unsigned_to_nat(1u);
v___x_1804_ = lean_nat_add(v_idx_1786_, v___x_1803_);
lean_dec(v_idx_1786_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v___x_1804_);
v___x_1806_ = v___x_1801_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_array_1785_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v___x_1806_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_pos_1808_; lean_object* v_res_1809_; lean_object* v___x_1810_; 
v_pos_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_pos_1808_);
v_res_1809_ = lean_ctor_get(v___x_1807_, 1);
lean_inc(v_res_1809_);
lean_dec_ref_known(v___x_1807_, 2);
v___x_1810_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1(v_pos_1808_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_pos_1811_; lean_object* v_res_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1872_; 
v_pos_1811_ = lean_ctor_get(v___x_1810_, 0);
v_res_1812_ = lean_ctor_get(v___x_1810_, 1);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1814_ = v___x_1810_;
v_isShared_1815_ = v_isSharedCheck_1872_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_res_1812_);
lean_inc(v_pos_1811_);
lean_dec(v___x_1810_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1872_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v_array_1816_; lean_object* v_idx_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; 
v_array_1816_ = lean_ctor_get(v_pos_1811_, 0);
v_idx_1817_ = lean_ctor_get(v_pos_1811_, 1);
v___x_1818_ = lean_byte_array_size(v_array_1816_);
v___x_1819_ = lean_nat_dec_lt(v_idx_1817_, v___x_1818_);
if (v___x_1819_ == 0)
{
lean_object* v___x_1820_; lean_object* v___x_1822_; 
lean_dec(v_res_1812_);
lean_dec(v_res_1809_);
lean_dec(v_res_1781_);
lean_dec(v_res_1768_);
v___x_1820_ = lean_box(0);
if (v_isShared_1815_ == 0)
{
lean_ctor_set_tag(v___x_1814_, 1);
lean_ctor_set(v___x_1814_, 1, v___x_1820_);
v___x_1822_ = v___x_1814_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_pos_1811_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
else
{
uint8_t v_got_1824_; uint8_t v___x_1825_; 
v_got_1824_ = lean_byte_array_fget(v_array_1816_, v_idx_1817_);
v___x_1825_ = lean_uint8_dec_eq(v_got_1824_, v___x_1793_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1828_; 
lean_dec(v_res_1812_);
lean_dec(v_res_1809_);
lean_dec(v_res_1781_);
lean_dec(v_res_1768_);
v___x_1826_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
if (v_isShared_1815_ == 0)
{
lean_ctor_set_tag(v___x_1814_, 1);
lean_ctor_set(v___x_1814_, 1, v___x_1826_);
v___x_1828_ = v___x_1814_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_pos_1811_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
else
{
lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1869_; 
lean_inc(v_idx_1817_);
lean_inc_ref(v_array_1816_);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_pos_1811_);
if (v_isSharedCheck_1869_ == 0)
{
lean_object* v_unused_1870_; lean_object* v_unused_1871_; 
v_unused_1870_ = lean_ctor_get(v_pos_1811_, 1);
lean_dec(v_unused_1870_);
v_unused_1871_ = lean_ctor_get(v_pos_1811_, 0);
lean_dec(v_unused_1871_);
v___x_1831_ = v_pos_1811_;
v_isShared_1832_ = v_isSharedCheck_1869_;
goto v_resetjp_1830_;
}
else
{
lean_dec(v_pos_1811_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1869_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1836_; 
v___x_1833_ = lean_nat_abs(v_res_1768_);
lean_dec(v_res_1768_);
v___x_1834_ = lean_nat_add(v_idx_1817_, v___x_1803_);
lean_dec(v_idx_1817_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 1, v___x_1834_);
v___x_1836_ = v___x_1831_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_array_1816_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = lean_array_get_size(v_res_1781_);
v___x_1838_ = lean_nat_dec_eq(v___x_1837_, v___x_1772_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1839_ = lean_array_get_size(v_res_1812_);
v___x_1840_ = lean_nat_dec_eq(v___x_1839_, v___x_1772_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1841_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_1781_);
v___x_1842_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1833_);
lean_ctor_set(v___x_1842_, 1, v_res_1781_);
lean_ctor_set(v___x_1842_, 2, v___x_1841_);
lean_ctor_set(v___x_1842_, 3, v_res_1809_);
lean_ctor_set(v___x_1842_, 4, v_res_1812_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 1, v___x_1842_);
lean_ctor_set(v___x_1814_, 0, v___x_1836_);
v___x_1844_ = v___x_1814_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
else
{
lean_object* v___x_1846_; uint8_t v___x_1847_; 
lean_dec(v_res_1812_);
v___x_1846_ = lean_array_get_size(v_res_1809_);
v___x_1847_ = lean_nat_dec_eq(v___x_1846_, v___x_1772_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1848_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1833_);
lean_ctor_set(v___x_1848_, 1, v_res_1781_);
lean_ctor_set(v___x_1848_, 2, v_res_1809_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 1, v___x_1848_);
lean_ctor_set(v___x_1814_, 0, v___x_1836_);
v___x_1850_ = v___x_1814_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
lean_dec(v_res_1809_);
v___x_1852_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_1781_);
v___x_1853_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0));
v___x_1854_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1833_);
lean_ctor_set(v___x_1854_, 1, v_res_1781_);
lean_ctor_set(v___x_1854_, 2, v___x_1852_);
lean_ctor_set(v___x_1854_, 3, v___x_1853_);
lean_ctor_set(v___x_1854_, 4, v___x_1853_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 1, v___x_1854_);
lean_ctor_set(v___x_1814_, 0, v___x_1836_);
v___x_1856_ = v___x_1814_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
else
{
lean_object* v___x_1858_; uint8_t v___x_1859_; 
lean_dec(v_res_1781_);
v___x_1858_ = lean_array_get_size(v_res_1812_);
lean_dec(v_res_1812_);
v___x_1859_ = lean_nat_dec_eq(v___x_1858_, v___x_1772_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; lean_object* v___x_1862_; 
lean_dec(v___x_1833_);
lean_dec(v_res_1809_);
v___x_1860_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2));
if (v_isShared_1815_ == 0)
{
lean_ctor_set_tag(v___x_1814_, 1);
lean_ctor_set(v___x_1814_, 1, v___x_1860_);
lean_ctor_set(v___x_1814_, 0, v___x_1836_);
v___x_1862_ = v___x_1814_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1866_; 
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1833_);
lean_ctor_set(v___x_1864_, 1, v_res_1809_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 1, v___x_1864_);
lean_ctor_set(v___x_1814_, 0, v___x_1836_);
v___x_1866_ = v___x_1814_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
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
lean_object* v_pos_1873_; lean_object* v_err_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec(v_res_1809_);
lean_dec(v_res_1781_);
lean_dec(v_res_1768_);
v_pos_1873_ = lean_ctor_get(v___x_1810_, 0);
v_err_1874_ = lean_ctor_get(v___x_1810_, 1);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1810_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_err_1874_);
lean_inc(v_pos_1873_);
lean_dec(v___x_1810_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_pos_1873_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_err_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
else
{
lean_object* v_pos_1882_; lean_object* v_err_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec(v_res_1781_);
lean_dec(v_res_1768_);
v_pos_1882_ = lean_ctor_get(v___x_1807_, 0);
v_err_1883_ = lean_ctor_get(v___x_1807_, 1);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1807_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_err_1883_);
lean_inc(v_pos_1882_);
lean_dec(v___x_1807_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_pos_1882_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_err_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
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
lean_object* v_pos_1896_; lean_object* v_err_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec(v_res_1768_);
v_pos_1896_ = lean_ctor_get(v___x_1779_, 0);
v_err_1897_ = lean_ctor_get(v___x_1779_, 1);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1779_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_err_1897_);
lean_inc(v_pos_1896_);
lean_dec(v___x_1779_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_pos_1896_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_err_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1906_; lean_object* v_err_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
v_pos_1906_ = lean_ctor_get(v___x_1766_, 0);
v_err_1907_ = lean_ctor_get(v___x_1766_, 1);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1766_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_err_1907_);
lean_inc(v_pos_1906_);
lean_dec(v___x_1766_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_pos_1906_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_err_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(lean_object* v_a_1915_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v_a_1915_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_pos_1917_; lean_object* v_res_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1952_; 
v_pos_1917_ = lean_ctor_get(v___x_1916_, 0);
v_res_1918_ = lean_ctor_get(v___x_1916_, 1);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1920_ = v___x_1916_;
v_isShared_1921_ = v_isSharedCheck_1952_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_res_1918_);
lean_inc(v_pos_1917_);
lean_dec(v___x_1916_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1952_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v_array_1922_; lean_object* v_idx_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v_array_1922_ = lean_ctor_get(v_pos_1917_, 0);
v_idx_1923_ = lean_ctor_get(v_pos_1917_, 1);
v___x_1924_ = lean_byte_array_size(v_array_1922_);
v___x_1925_ = lean_nat_dec_lt(v_idx_1923_, v___x_1924_);
if (v___x_1925_ == 0)
{
lean_object* v___x_1926_; lean_object* v___x_1928_; 
lean_dec(v_res_1918_);
v___x_1926_ = lean_box(0);
if (v_isShared_1921_ == 0)
{
lean_ctor_set_tag(v___x_1920_, 1);
lean_ctor_set(v___x_1920_, 1, v___x_1926_);
v___x_1928_ = v___x_1920_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_pos_1917_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
else
{
uint8_t v___x_1930_; uint8_t v_got_1931_; uint8_t v___x_1932_; 
v___x_1930_ = 0;
v_got_1931_ = lean_byte_array_fget(v_array_1922_, v_idx_1923_);
v___x_1932_ = lean_uint8_dec_eq(v_got_1931_, v___x_1930_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
lean_dec(v_res_1918_);
v___x_1933_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
if (v_isShared_1921_ == 0)
{
lean_ctor_set_tag(v___x_1920_, 1);
lean_ctor_set(v___x_1920_, 1, v___x_1933_);
v___x_1935_ = v___x_1920_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_pos_1917_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
else
{
lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1949_; 
lean_inc(v_idx_1923_);
lean_inc_ref(v_array_1922_);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_pos_1917_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; lean_object* v_unused_1951_; 
v_unused_1950_ = lean_ctor_get(v_pos_1917_, 1);
lean_dec(v_unused_1950_);
v_unused_1951_ = lean_ctor_get(v_pos_1917_, 0);
lean_dec(v_unused_1951_);
v___x_1938_ = v_pos_1917_;
v_isShared_1939_ = v_isSharedCheck_1949_;
goto v_resetjp_1937_;
}
else
{
lean_dec(v_pos_1917_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1949_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1943_; 
v___x_1940_ = lean_unsigned_to_nat(1u);
v___x_1941_ = lean_nat_add(v_idx_1923_, v___x_1940_);
lean_dec(v_idx_1923_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 1, v___x_1941_);
v___x_1943_ = v___x_1938_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_array_1922_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v___x_1941_);
v___x_1943_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
lean_object* v___x_1944_; lean_object* v___x_1946_; 
v___x_1944_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1944_, 0, v_res_1918_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 1, v___x_1944_);
lean_ctor_set(v___x_1920_, 0, v___x_1943_);
v___x_1946_ = v___x_1920_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
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
v_pos_1953_ = lean_ctor_get(v___x_1916_, 0);
v_err_1954_ = lean_ctor_get(v___x_1916_, 1);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1916_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_err_1954_);
lean_inc(v_pos_1953_);
lean_dec(v___x_1916_);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(lean_object* v_a_1963_){
_start:
{
lean_object* v_array_1964_; lean_object* v_idx_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; 
v_array_1964_ = lean_ctor_get(v_a_1963_, 0);
v_idx_1965_ = lean_ctor_get(v_a_1963_, 1);
v___x_1966_ = lean_byte_array_size(v_array_1964_);
v___x_1967_ = lean_nat_dec_lt(v_idx_1965_, v___x_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = lean_box(0);
v___x_1969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1969_, 0, v_a_1963_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
return v___x_1969_;
}
else
{
lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1991_; 
lean_inc(v_idx_1965_);
lean_inc_ref(v_array_1964_);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_a_1963_);
if (v_isSharedCheck_1991_ == 0)
{
lean_object* v_unused_1992_; lean_object* v_unused_1993_; 
v_unused_1992_ = lean_ctor_get(v_a_1963_, 1);
lean_dec(v_unused_1992_);
v_unused_1993_ = lean_ctor_get(v_a_1963_, 0);
lean_dec(v_unused_1993_);
v___x_1971_ = v_a_1963_;
v_isShared_1972_ = v_isSharedCheck_1991_;
goto v_resetjp_1970_;
}
else
{
lean_dec(v_a_1963_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1991_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
uint8_t v_c_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v_it_x27_1977_; 
v_c_1973_ = lean_byte_array_fget(v_array_1964_, v_idx_1965_);
v___x_1974_ = lean_unsigned_to_nat(1u);
v___x_1975_ = lean_nat_add(v_idx_1965_, v___x_1974_);
lean_dec(v_idx_1965_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 1, v___x_1975_);
v_it_x27_1977_ = v___x_1971_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_array_1964_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v___x_1975_);
v_it_x27_1977_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
uint8_t v___x_1978_; uint8_t v___x_1979_; 
v___x_1978_ = 97;
v___x_1979_ = lean_uint8_dec_eq(v_c_1973_, v___x_1978_);
if (v___x_1979_ == 0)
{
uint8_t v___x_1980_; uint8_t v___x_1981_; 
v___x_1980_ = 100;
v___x_1981_ = lean_uint8_dec_eq(v_c_1973_, v___x_1980_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1982_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0));
v___x_1983_ = lean_uint8_to_nat(v_c_1973_);
v___x_1984_ = l_Nat_reprFast(v___x_1983_);
v___x_1985_ = lean_string_append(v___x_1982_, v___x_1984_);
lean_dec_ref(v___x_1984_);
v___x_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
v___x_1987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1987_, 0, v_it_x27_1977_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
return v___x_1987_;
}
else
{
lean_object* v___x_1988_; 
v___x_1988_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(v_it_x27_1977_);
return v___x_1988_;
}
}
else
{
lean_object* v___x_1989_; 
v___x_1989_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(v_it_x27_1977_);
return v___x_1989_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(lean_object* v_acc_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v___x_1996_; 
lean_inc_ref(v_a_1995_);
v___x_1996_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(v_a_1995_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_pos_1997_; lean_object* v_res_1998_; lean_object* v___x_1999_; 
lean_dec_ref(v_a_1995_);
v_pos_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_pos_1997_);
v_res_1998_ = lean_ctor_get(v___x_1996_, 1);
lean_inc(v_res_1998_);
lean_dec_ref_known(v___x_1996_, 2);
v___x_1999_ = lean_array_push(v_acc_1994_, v_res_1998_);
v_acc_1994_ = v___x_1999_;
v_a_1995_ = v_pos_1997_;
goto _start;
}
else
{
lean_object* v_pos_2001_; lean_object* v_err_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2015_; 
v_pos_2001_ = lean_ctor_get(v___x_1996_, 0);
v_err_2002_ = lean_ctor_get(v___x_1996_, 1);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2004_ = v___x_1996_;
v_isShared_2005_ = v_isSharedCheck_2015_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_err_2002_);
lean_inc(v_pos_2001_);
lean_dec(v___x_1996_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2015_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v_idx_2006_; lean_object* v_idx_2007_; uint8_t v___x_2008_; 
v_idx_2006_ = lean_ctor_get(v_a_1995_, 1);
lean_inc(v_idx_2006_);
lean_dec_ref(v_a_1995_);
v_idx_2007_ = lean_ctor_get(v_pos_2001_, 1);
v___x_2008_ = lean_nat_dec_eq(v_idx_2006_, v_idx_2007_);
lean_dec(v_idx_2006_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2010_; 
lean_dec_ref(v_acc_1994_);
if (v_isShared_2005_ == 0)
{
v___x_2010_ = v___x_2004_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_pos_2001_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_err_2002_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
else
{
lean_object* v___x_2013_; 
lean_dec(v_err_2002_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set_tag(v___x_2004_, 0);
lean_ctor_set(v___x_2004_, 1, v_acc_1994_);
v___x_2013_ = v___x_2004_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_pos_2001_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_acc_1994_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(lean_object* v_a_2019_){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0));
v___x_2021_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(v___x_2020_, v_a_2019_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_pos_2022_; lean_object* v_array_2023_; lean_object* v_idx_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; 
v_pos_2022_ = lean_ctor_get(v___x_2021_, 0);
v_array_2023_ = lean_ctor_get(v_pos_2022_, 0);
v_idx_2024_ = lean_ctor_get(v_pos_2022_, 1);
v___x_2025_ = lean_byte_array_size(v_array_2023_);
v___x_2026_ = lean_nat_dec_lt(v_idx_2024_, v___x_2025_);
if (v___x_2026_ == 0)
{
return v___x_2021_;
}
else
{
lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2034_; 
lean_inc(v_pos_2022_);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; lean_object* v_unused_2036_; 
v_unused_2035_ = lean_ctor_get(v___x_2021_, 1);
lean_dec(v_unused_2035_);
v_unused_2036_ = lean_ctor_get(v___x_2021_, 0);
lean_dec(v_unused_2036_);
v___x_2028_ = v___x_2021_;
v_isShared_2029_ = v_isSharedCheck_2034_;
goto v_resetjp_2027_;
}
else
{
lean_dec(v___x_2021_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2034_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2030_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__1));
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 1);
lean_ctor_set(v___x_2028_, 1, v___x_2030_);
v___x_2032_ = v___x_2028_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_pos_2022_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
else
{
return v___x_2021_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_parseActions(lean_object* v_a_2037_){
_start:
{
lean_object* v_array_2038_; lean_object* v_idx_2039_; lean_object* v___x_2040_; uint8_t v___x_2041_; 
v_array_2038_ = lean_ctor_get(v_a_2037_, 0);
v_idx_2039_ = lean_ctor_get(v_a_2037_, 1);
v___x_2040_ = lean_byte_array_size(v_array_2038_);
v___x_2041_ = lean_nat_dec_lt(v_idx_2039_, v___x_2040_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = lean_box(0);
v___x_2043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2043_, 0, v_a_2037_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
return v___x_2043_;
}
else
{
uint8_t v___x_2044_; uint8_t v___x_2045_; uint8_t v___x_2046_; 
v___x_2044_ = lean_byte_array_fget(v_array_2038_, v_idx_2039_);
v___x_2045_ = 97;
v___x_2046_ = lean_uint8_dec_eq(v___x_2044_, v___x_2045_);
if (v___x_2046_ == 0)
{
uint8_t v___x_2047_; uint8_t v___x_2048_; 
v___x_2047_ = 100;
v___x_2048_ = lean_uint8_dec_eq(v___x_2044_, v___x_2047_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(v_a_2037_);
return v___x_2049_;
}
else
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(v_a_2037_);
return v___x_2050_;
}
}
else
{
lean_object* v___x_2051_; 
v___x_2051_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(v_a_2037_);
return v___x_2051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object* v_path_2052_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = l_IO_FS_readBinFile(v_path_2052_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2076_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2057_ = v___x_2054_;
v_isShared_2058_ = v_isSharedCheck_2076_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2054_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2076_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_parseActions), 1, 0);
v___x_2060_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_2059_, v_a_2055_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2071_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2063_ = v___x_2060_;
v_isShared_2064_ = v_isSharedCheck_2071_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2060_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2071_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
lean_ctor_set_tag(v___x_2063_, 18);
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2068_; 
if (v_isShared_2058_ == 0)
{
lean_ctor_set_tag(v___x_2057_, 1);
lean_ctor_set(v___x_2057_, 0, v___x_2066_);
v___x_2068_ = v___x_2057_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; 
v_a_2072_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2072_);
lean_dec_ref_known(v___x_2060_, 1);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v_a_2072_);
v___x_2074_ = v___x_2057_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
v_a_2077_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2054_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2054_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof___boxed(lean_object* v_path_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(v_path_2085_);
lean_dec_ref(v_path_2085_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_parseLRATProof(lean_object* v_proof_2088_){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_parseActions), 1, 0);
v___x_2090_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_2089_, v_proof_2088_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(lean_object* v_as_2092_, size_t v_i_2093_, size_t v_stop_2094_, lean_object* v_b_2095_){
_start:
{
uint8_t v___x_2096_; 
v___x_2096_ = lean_usize_dec_eq(v_i_2093_, v_stop_2094_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; size_t v___x_2102_; size_t v___x_2103_; 
v___x_2097_ = lean_array_uget_borrowed(v_as_2092_, v_i_2093_);
lean_inc(v___x_2097_);
v___x_2098_ = l_Nat_reprFast(v___x_2097_);
v___x_2099_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2100_ = lean_string_append(v___x_2098_, v___x_2099_);
v___x_2101_ = lean_string_append(v_b_2095_, v___x_2100_);
lean_dec_ref(v___x_2100_);
v___x_2102_ = ((size_t)1ULL);
v___x_2103_ = lean_usize_add(v_i_2093_, v___x_2102_);
v_i_2093_ = v___x_2103_;
v_b_2095_ = v___x_2101_;
goto _start;
}
else
{
return v_b_2095_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___boxed(lean_object* v_as_2105_, lean_object* v_i_2106_, lean_object* v_stop_2107_, lean_object* v_b_2108_){
_start:
{
size_t v_i_boxed_2109_; size_t v_stop_boxed_2110_; lean_object* v_res_2111_; 
v_i_boxed_2109_ = lean_unbox_usize(v_i_2106_);
lean_dec(v_i_2106_);
v_stop_boxed_2110_ = lean_unbox_usize(v_stop_2107_);
lean_dec(v_stop_2107_);
v_res_2111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_as_2105_, v_i_boxed_2109_, v_stop_boxed_2110_, v_b_2108_);
lean_dec_ref(v_as_2105_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(lean_object* v_ids_2113_){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2114_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2115_ = lean_unsigned_to_nat(0u);
v___x_2116_ = lean_array_get_size(v_ids_2113_);
v___x_2117_ = lean_nat_dec_lt(v___x_2115_, v___x_2116_);
if (v___x_2117_ == 0)
{
return v___x_2114_;
}
else
{
uint8_t v___x_2118_; 
v___x_2118_ = lean_nat_dec_le(v___x_2116_, v___x_2116_);
if (v___x_2118_ == 0)
{
if (v___x_2117_ == 0)
{
return v___x_2114_;
}
else
{
size_t v___x_2119_; size_t v___x_2120_; lean_object* v___x_2121_; 
v___x_2119_ = ((size_t)0ULL);
v___x_2120_ = lean_usize_of_nat(v___x_2116_);
v___x_2121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_ids_2113_, v___x_2119_, v___x_2120_, v___x_2114_);
return v___x_2121_;
}
}
else
{
size_t v___x_2122_; size_t v___x_2123_; lean_object* v___x_2124_; 
v___x_2122_ = ((size_t)0ULL);
v___x_2123_ = lean_usize_of_nat(v___x_2116_);
v___x_2124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_ids_2113_, v___x_2122_, v___x_2123_, v___x_2114_);
return v___x_2124_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___boxed(lean_object* v_ids_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_ids_2125_);
lean_dec_ref(v_ids_2125_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(lean_object* v_hint_2128_){
_start:
{
lean_object* v_fst_2129_; lean_object* v_snd_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_fst_2129_ = lean_ctor_get(v_hint_2128_, 0);
lean_inc(v_fst_2129_);
v_snd_2130_ = lean_ctor_get(v_hint_2128_, 1);
lean_inc(v_snd_2130_);
lean_dec_ref(v_hint_2128_);
v___x_2131_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0));
v___x_2132_ = l_Nat_reprFast(v_fst_2129_);
v___x_2133_ = lean_string_append(v___x_2131_, v___x_2132_);
lean_dec_ref(v___x_2132_);
v___x_2134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2135_ = lean_string_append(v___x_2133_, v___x_2134_);
v___x_2136_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_snd_2130_);
lean_dec(v_snd_2130_);
v___x_2137_ = lean_string_append(v___x_2135_, v___x_2136_);
lean_dec_ref(v___x_2136_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(lean_object* v_as_2138_, size_t v_i_2139_, size_t v_stop_2140_, lean_object* v_b_2141_){
_start:
{
uint8_t v___x_2142_; 
v___x_2142_ = lean_usize_dec_eq(v_i_2139_, v_stop_2140_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; size_t v___x_2146_; size_t v___x_2147_; 
v___x_2143_ = lean_array_uget_borrowed(v_as_2138_, v_i_2139_);
lean_inc(v___x_2143_);
v___x_2144_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(v___x_2143_);
v___x_2145_ = lean_string_append(v_b_2141_, v___x_2144_);
lean_dec_ref(v___x_2144_);
v___x_2146_ = ((size_t)1ULL);
v___x_2147_ = lean_usize_add(v_i_2139_, v___x_2146_);
v_i_2139_ = v___x_2147_;
v_b_2141_ = v___x_2145_;
goto _start;
}
else
{
return v_b_2141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0___boxed(lean_object* v_as_2149_, lean_object* v_i_2150_, lean_object* v_stop_2151_, lean_object* v_b_2152_){
_start:
{
size_t v_i_boxed_2153_; size_t v_stop_boxed_2154_; lean_object* v_res_2155_; 
v_i_boxed_2153_ = lean_unbox_usize(v_i_2150_);
lean_dec(v_i_2150_);
v_stop_boxed_2154_ = lean_unbox_usize(v_stop_2151_);
lean_dec(v_stop_2151_);
v_res_2155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_as_2149_, v_i_boxed_2153_, v_stop_boxed_2154_, v_b_2152_);
lean_dec_ref(v_as_2149_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(lean_object* v_hints_2156_){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; 
v___x_2157_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2158_ = lean_unsigned_to_nat(0u);
v___x_2159_ = lean_array_get_size(v_hints_2156_);
v___x_2160_ = lean_nat_dec_lt(v___x_2158_, v___x_2159_);
if (v___x_2160_ == 0)
{
return v___x_2157_;
}
else
{
uint8_t v___x_2161_; 
v___x_2161_ = lean_nat_dec_le(v___x_2159_, v___x_2159_);
if (v___x_2161_ == 0)
{
if (v___x_2160_ == 0)
{
return v___x_2157_;
}
else
{
size_t v___x_2162_; size_t v___x_2163_; lean_object* v___x_2164_; 
v___x_2162_ = ((size_t)0ULL);
v___x_2163_ = lean_usize_of_nat(v___x_2159_);
v___x_2164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_hints_2156_, v___x_2162_, v___x_2163_, v___x_2157_);
return v___x_2164_;
}
}
else
{
size_t v___x_2165_; size_t v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = ((size_t)0ULL);
v___x_2166_ = lean_usize_of_nat(v___x_2159_);
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_hints_2156_, v___x_2165_, v___x_2166_, v___x_2157_);
return v___x_2167_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___boxed(lean_object* v_hints_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(v_hints_2168_);
lean_dec_ref(v_hints_2168_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(lean_object* v_as_2170_, size_t v_i_2171_, size_t v_stop_2172_, lean_object* v_b_2173_){
_start:
{
uint8_t v___x_2174_; 
v___x_2174_ = lean_usize_dec_eq(v_i_2171_, v_stop_2172_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; size_t v___x_2180_; size_t v___x_2181_; 
v___x_2175_ = lean_array_uget_borrowed(v_as_2170_, v_i_2171_);
v___x_2176_ = l_Int_repr(v___x_2175_);
v___x_2177_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2178_ = lean_string_append(v___x_2176_, v___x_2177_);
v___x_2179_ = lean_string_append(v_b_2173_, v___x_2178_);
lean_dec_ref(v___x_2178_);
v___x_2180_ = ((size_t)1ULL);
v___x_2181_ = lean_usize_add(v_i_2171_, v___x_2180_);
v_i_2171_ = v___x_2181_;
v_b_2173_ = v___x_2179_;
goto _start;
}
else
{
return v_b_2173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0___boxed(lean_object* v_as_2183_, lean_object* v_i_2184_, lean_object* v_stop_2185_, lean_object* v_b_2186_){
_start:
{
size_t v_i_boxed_2187_; size_t v_stop_boxed_2188_; lean_object* v_res_2189_; 
v_i_boxed_2187_ = lean_unbox_usize(v_i_2184_);
lean_dec(v_i_2184_);
v_stop_boxed_2188_ = lean_unbox_usize(v_stop_2185_);
lean_dec(v_stop_2185_);
v_res_2189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_as_2183_, v_i_boxed_2187_, v_stop_boxed_2188_, v_b_2186_);
lean_dec_ref(v_as_2183_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(lean_object* v_clause_2190_){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; uint8_t v___x_2194_; 
v___x_2191_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2192_ = lean_unsigned_to_nat(0u);
v___x_2193_ = lean_array_get_size(v_clause_2190_);
v___x_2194_ = lean_nat_dec_lt(v___x_2192_, v___x_2193_);
if (v___x_2194_ == 0)
{
return v___x_2191_;
}
else
{
uint8_t v___x_2195_; 
v___x_2195_ = lean_nat_dec_le(v___x_2193_, v___x_2193_);
if (v___x_2195_ == 0)
{
if (v___x_2194_ == 0)
{
return v___x_2191_;
}
else
{
size_t v___x_2196_; size_t v___x_2197_; lean_object* v___x_2198_; 
v___x_2196_ = ((size_t)0ULL);
v___x_2197_ = lean_usize_of_nat(v___x_2193_);
v___x_2198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_clause_2190_, v___x_2196_, v___x_2197_, v___x_2191_);
return v___x_2198_;
}
}
else
{
size_t v___x_2199_; size_t v___x_2200_; lean_object* v___x_2201_; 
v___x_2199_ = ((size_t)0ULL);
v___x_2200_ = lean_usize_of_nat(v___x_2193_);
v___x_2201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_clause_2190_, v___x_2199_, v___x_2200_, v___x_2191_);
return v___x_2201_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___boxed(lean_object* v_clause_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_clause_2202_);
lean_dec_ref(v_clause_2202_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(lean_object* v_a_2208_){
_start:
{
switch(lean_obj_tag(v_a_2208_))
{
case 0:
{
lean_object* v_id_2209_; lean_object* v_rupHints_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v_id_2209_ = lean_ctor_get(v_a_2208_, 0);
lean_inc(v_id_2209_);
v_rupHints_2210_ = lean_ctor_get(v_a_2208_, 1);
lean_inc_ref(v_rupHints_2210_);
lean_dec_ref_known(v_a_2208_, 2);
v___x_2211_ = l_Nat_reprFast(v_id_2209_);
v___x_2212_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__0));
v___x_2213_ = lean_string_append(v___x_2211_, v___x_2212_);
v___x_2214_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2210_);
lean_dec_ref(v_rupHints_2210_);
v___x_2215_ = lean_string_append(v___x_2213_, v___x_2214_);
lean_dec_ref(v___x_2214_);
v___x_2216_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2217_ = lean_string_append(v___x_2215_, v___x_2216_);
return v___x_2217_;
}
case 1:
{
lean_object* v_id_2218_; lean_object* v_c_2219_; lean_object* v_rupHints_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v_id_2218_ = lean_ctor_get(v_a_2208_, 0);
lean_inc(v_id_2218_);
v_c_2219_ = lean_ctor_get(v_a_2208_, 1);
lean_inc(v_c_2219_);
v_rupHints_2220_ = lean_ctor_get(v_a_2208_, 2);
lean_inc_ref(v_rupHints_2220_);
lean_dec_ref_known(v_a_2208_, 3);
v___x_2221_ = l_Nat_reprFast(v_id_2218_);
v___x_2222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2223_ = lean_string_append(v___x_2221_, v___x_2222_);
v___x_2224_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_c_2219_);
lean_dec(v_c_2219_);
v___x_2225_ = lean_string_append(v___x_2223_, v___x_2224_);
lean_dec_ref(v___x_2224_);
v___x_2226_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2));
v___x_2227_ = lean_string_append(v___x_2225_, v___x_2226_);
v___x_2228_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2220_);
lean_dec_ref(v_rupHints_2220_);
v___x_2229_ = lean_string_append(v___x_2227_, v___x_2228_);
lean_dec_ref(v___x_2228_);
v___x_2230_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2231_ = lean_string_append(v___x_2229_, v___x_2230_);
return v___x_2231_;
}
case 2:
{
lean_object* v_id_2232_; lean_object* v_c_2233_; lean_object* v_rupHints_2234_; lean_object* v_ratHints_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v_id_2232_ = lean_ctor_get(v_a_2208_, 0);
lean_inc(v_id_2232_);
v_c_2233_ = lean_ctor_get(v_a_2208_, 1);
lean_inc(v_c_2233_);
v_rupHints_2234_ = lean_ctor_get(v_a_2208_, 3);
lean_inc_ref(v_rupHints_2234_);
v_ratHints_2235_ = lean_ctor_get(v_a_2208_, 4);
lean_inc_ref(v_ratHints_2235_);
lean_dec_ref_known(v_a_2208_, 5);
v___x_2236_ = l_Nat_reprFast(v_id_2232_);
v___x_2237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2238_ = lean_string_append(v___x_2236_, v___x_2237_);
v___x_2239_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_c_2233_);
lean_dec(v_c_2233_);
v___x_2240_ = lean_string_append(v___x_2238_, v___x_2239_);
lean_dec_ref(v___x_2239_);
v___x_2241_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2));
v___x_2242_ = lean_string_append(v___x_2240_, v___x_2241_);
v___x_2243_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2234_);
lean_dec_ref(v_rupHints_2234_);
v___x_2244_ = lean_string_append(v___x_2242_, v___x_2243_);
lean_dec_ref(v___x_2243_);
v___x_2245_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(v_ratHints_2235_);
lean_dec_ref(v_ratHints_2235_);
v___x_2246_ = lean_string_append(v___x_2244_, v___x_2245_);
lean_dec_ref(v___x_2245_);
v___x_2247_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2248_ = lean_string_append(v___x_2246_, v___x_2247_);
return v___x_2248_;
}
default: 
{
lean_object* v_ids_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v_ids_2249_ = lean_ctor_get(v_a_2208_, 0);
lean_inc_ref(v_ids_2249_);
lean_dec_ref_known(v_a_2208_, 1);
v___x_2250_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3));
v___x_2251_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_ids_2249_);
lean_dec_ref(v_ids_2249_);
v___x_2252_ = lean_string_append(v___x_2250_, v___x_2251_);
lean_dec_ref(v___x_2251_);
v___x_2253_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2254_ = lean_string_append(v___x_2252_, v___x_2253_);
return v___x_2254_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(lean_object* v_as_2256_, size_t v_i_2257_, size_t v_stop_2258_, lean_object* v_b_2259_){
_start:
{
uint8_t v___x_2260_; 
v___x_2260_ = lean_usize_dec_eq(v_i_2257_, v_stop_2258_);
if (v___x_2260_ == 0)
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; size_t v___x_2266_; size_t v___x_2267_; 
v___x_2261_ = lean_array_uget_borrowed(v_as_2256_, v_i_2257_);
lean_inc(v___x_2261_);
v___x_2262_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(v___x_2261_);
v___x_2263_ = lean_string_append(v_b_2259_, v___x_2262_);
lean_dec_ref(v___x_2262_);
v___x_2264_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___closed__0));
v___x_2265_ = lean_string_append(v___x_2263_, v___x_2264_);
v___x_2266_ = ((size_t)1ULL);
v___x_2267_ = lean_usize_add(v_i_2257_, v___x_2266_);
v_i_2257_ = v___x_2267_;
v_b_2259_ = v___x_2265_;
goto _start;
}
else
{
return v_b_2259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___boxed(lean_object* v_as_2269_, lean_object* v_i_2270_, lean_object* v_stop_2271_, lean_object* v_b_2272_){
_start:
{
size_t v_i_boxed_2273_; size_t v_stop_boxed_2274_; lean_object* v_res_2275_; 
v_i_boxed_2273_ = lean_unbox_usize(v_i_2270_);
lean_dec(v_i_2270_);
v_stop_boxed_2274_ = lean_unbox_usize(v_stop_2271_);
lean_dec(v_stop_2271_);
v_res_2275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_as_2269_, v_i_boxed_2273_, v_stop_boxed_2274_, v_b_2272_);
lean_dec_ref(v_as_2269_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString(lean_object* v_proof_2276_){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; 
v___x_2277_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2278_ = lean_unsigned_to_nat(0u);
v___x_2279_ = lean_array_get_size(v_proof_2276_);
v___x_2280_ = lean_nat_dec_lt(v___x_2278_, v___x_2279_);
if (v___x_2280_ == 0)
{
return v___x_2277_;
}
else
{
uint8_t v___x_2281_; 
v___x_2281_ = lean_nat_dec_le(v___x_2279_, v___x_2279_);
if (v___x_2281_ == 0)
{
if (v___x_2280_ == 0)
{
return v___x_2277_;
}
else
{
size_t v___x_2282_; size_t v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = ((size_t)0ULL);
v___x_2283_ = lean_usize_of_nat(v___x_2279_);
v___x_2284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_proof_2276_, v___x_2282_, v___x_2283_, v___x_2277_);
return v___x_2284_;
}
}
else
{
size_t v___x_2285_; size_t v___x_2286_; lean_object* v___x_2287_; 
v___x_2285_ = ((size_t)0ULL);
v___x_2286_ = lean_usize_of_nat(v___x_2279_);
v___x_2287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_proof_2276_, v___x_2285_, v___x_2286_, v___x_2277_);
return v___x_2287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString___boxed(lean_object* v_proof_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_proof_2288_);
lean_dec_ref(v_proof_2288_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startDelete(lean_object* v_acc_2290_){
_start:
{
uint8_t v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = 100;
v___x_2292_ = lean_byte_array_push(v_acc_2290_, v___x_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(lean_object* v_acc_2293_, uint64_t v_lit_2294_){
_start:
{
uint8_t v___y_2296_; uint64_t v___x_2301_; uint8_t v___x_2302_; 
v___x_2301_ = 0ULL;
v___x_2302_ = lean_uint64_dec_eq(v_lit_2294_, v___x_2301_);
if (v___x_2302_ == 0)
{
uint64_t v___x_2303_; uint8_t v___x_2304_; 
v___x_2303_ = 127ULL;
v___x_2304_ = lean_uint64_dec_lt(v___x_2303_, v_lit_2294_);
if (v___x_2304_ == 0)
{
uint8_t v___x_2305_; uint8_t v___x_2306_; uint8_t v___x_2307_; 
v___x_2305_ = lean_uint64_to_uint8(v_lit_2294_);
v___x_2306_ = 127;
v___x_2307_ = lean_uint8_land(v___x_2305_, v___x_2306_);
v___y_2296_ = v___x_2307_;
goto v___jp_2295_;
}
else
{
uint8_t v___x_2308_; uint8_t v___x_2309_; uint8_t v___x_2310_; uint8_t v___x_2311_; uint8_t v___x_2312_; 
v___x_2308_ = lean_uint64_to_uint8(v_lit_2294_);
v___x_2309_ = 127;
v___x_2310_ = lean_uint8_land(v___x_2308_, v___x_2309_);
v___x_2311_ = 128;
v___x_2312_ = lean_uint8_lor(v___x_2310_, v___x_2311_);
v___y_2296_ = v___x_2312_;
goto v___jp_2295_;
}
}
else
{
return v_acc_2293_;
}
v___jp_2295_:
{
lean_object* v_acc_2297_; uint64_t v___x_2298_; uint64_t v___x_2299_; 
v_acc_2297_ = lean_byte_array_push(v_acc_2293_, v___y_2296_);
v___x_2298_ = 7ULL;
v___x_2299_ = lean_uint64_shift_right(v_lit_2294_, v___x_2298_);
v_acc_2293_ = v_acc_2297_;
v_lit_2294_ = v___x_2299_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode___boxed(lean_object* v_acc_2313_, lean_object* v_lit_2314_){
_start:
{
uint64_t v_lit_boxed_2315_; lean_object* v_res_2316_; 
v_lit_boxed_2315_ = lean_unbox_uint64(v_lit_2314_);
lean_dec_ref(v_lit_2314_);
v_res_2316_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(v_acc_2313_, v_lit_boxed_2315_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(lean_object* v_msg_2317_){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = l_ByteArray_empty;
v___x_2319_ = lean_panic_fn_borrowed(v___x_2318_, v_msg_2317_);
return v___x_2319_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0(void){
_start:
{
lean_object* v___x_2320_; 
v___x_2320_ = lean_cstr_to_nat("18446744073709551615");
return v___x_2320_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2324_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3));
v___x_2325_ = lean_unsigned_to_nat(4u);
v___x_2326_ = lean_unsigned_to_nat(400u);
v___x_2327_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2));
v___x_2328_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1));
v___x_2329_ = l_mkPanicMessageWithDecl(v___x_2328_, v___x_2327_, v___x_2326_, v___x_2325_, v___x_2324_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(lean_object* v_acc_2330_, lean_object* v_lit_2331_){
_start:
{
lean_object* v___y_2333_; lean_object* v___x_2340_; uint8_t v___x_2341_; 
v___x_2340_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_2341_ = lean_int_dec_lt(v___x_2340_, v_lit_2331_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2342_ = lean_unsigned_to_nat(2u);
v___x_2343_ = lean_nat_abs(v_lit_2331_);
v___x_2344_ = lean_nat_mul(v___x_2342_, v___x_2343_);
lean_dec(v___x_2343_);
v___x_2345_ = lean_unsigned_to_nat(1u);
v___x_2346_ = lean_nat_add(v___x_2344_, v___x_2345_);
lean_dec(v___x_2344_);
v___y_2333_ = v___x_2346_;
goto v___jp_2332_;
}
else
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2347_ = lean_unsigned_to_nat(2u);
v___x_2348_ = lean_nat_abs(v_lit_2331_);
v___x_2349_ = lean_nat_mul(v___x_2347_, v___x_2348_);
lean_dec(v___x_2348_);
v___y_2333_ = v___x_2349_;
goto v___jp_2332_;
}
v___jp_2332_:
{
lean_object* v___x_2334_; uint8_t v___x_2335_; 
v___x_2334_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0);
v___x_2335_ = lean_nat_dec_le(v___y_2333_, v___x_2334_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec(v___y_2333_);
lean_dec_ref(v_acc_2330_);
v___x_2336_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4);
v___x_2337_ = l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(v___x_2336_);
return v___x_2337_;
}
else
{
uint64_t v_mapped_2338_; lean_object* v___x_2339_; 
v_mapped_2338_ = lean_uint64_of_nat(v___y_2333_);
lean_dec(v___y_2333_);
v___x_2339_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(v_acc_2330_, v_mapped_2338_);
return v___x_2339_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___boxed(lean_object* v_acc_2350_, lean_object* v_lit_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2350_, v_lit_2351_);
lean_dec(v_lit_2351_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_zeroByte(lean_object* v_acc_2353_){
_start:
{
uint8_t v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = 0;
v___x_2355_ = lean_byte_array_push(v_acc_2353_, v___x_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addNat(lean_object* v_acc_2356_, lean_object* v_n_2357_){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = lean_nat_to_int(v_n_2357_);
v___x_2359_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2356_, v___x_2358_);
lean_dec(v___x_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startAdd(lean_object* v_acc_2360_){
_start:
{
uint8_t v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = 97;
v___x_2362_ = lean_byte_array_push(v_acc_2360_, v___x_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(lean_object* v_as_2363_, size_t v_i_2364_, size_t v_stop_2365_, lean_object* v_b_2366_){
_start:
{
uint8_t v___x_2367_; 
v___x_2367_ = lean_usize_dec_eq(v_i_2364_, v_stop_2365_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; size_t v___x_2371_; size_t v___x_2372_; 
v___x_2368_ = lean_array_uget_borrowed(v_as_2363_, v_i_2364_);
lean_inc(v___x_2368_);
v___x_2369_ = lean_nat_to_int(v___x_2368_);
v___x_2370_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2366_, v___x_2369_);
lean_dec(v___x_2369_);
v___x_2371_ = ((size_t)1ULL);
v___x_2372_ = lean_usize_add(v_i_2364_, v___x_2371_);
v_i_2364_ = v___x_2372_;
v_b_2366_ = v___x_2370_;
goto _start;
}
else
{
return v_b_2366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0___boxed(lean_object* v_as_2374_, lean_object* v_i_2375_, lean_object* v_stop_2376_, lean_object* v_b_2377_){
_start:
{
size_t v_i_boxed_2378_; size_t v_stop_boxed_2379_; lean_object* v_res_2380_; 
v_i_boxed_2378_ = lean_unbox_usize(v_i_2375_);
lean_dec(v_i_2375_);
v_stop_boxed_2379_ = lean_unbox_usize(v_stop_2376_);
lean_dec(v_stop_2376_);
v_res_2380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(v_as_2374_, v_i_boxed_2378_, v_stop_boxed_2379_, v_b_2377_);
lean_dec_ref(v_as_2374_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(lean_object* v_as_2381_, size_t v_i_2382_, size_t v_stop_2383_, lean_object* v_b_2384_){
_start:
{
uint8_t v___x_2385_; 
v___x_2385_ = lean_usize_dec_eq(v_i_2382_, v_stop_2383_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; size_t v___x_2389_; size_t v___x_2390_; lean_object* v___x_2391_; 
v___x_2386_ = lean_array_uget_borrowed(v_as_2381_, v_i_2382_);
lean_inc(v___x_2386_);
v___x_2387_ = lean_nat_to_int(v___x_2386_);
v___x_2388_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2384_, v___x_2387_);
lean_dec(v___x_2387_);
v___x_2389_ = ((size_t)1ULL);
v___x_2390_ = lean_usize_add(v_i_2382_, v___x_2389_);
v___x_2391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(v_as_2381_, v___x_2390_, v_stop_2383_, v___x_2388_);
return v___x_2391_;
}
else
{
return v_b_2384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0___boxed(lean_object* v_as_2392_, lean_object* v_i_2393_, lean_object* v_stop_2394_, lean_object* v_b_2395_){
_start:
{
size_t v_i_boxed_2396_; size_t v_stop_boxed_2397_; lean_object* v_res_2398_; 
v_i_boxed_2396_ = lean_unbox_usize(v_i_2393_);
lean_dec(v_i_2393_);
v_stop_boxed_2397_ = lean_unbox_usize(v_stop_2394_);
lean_dec(v_stop_2394_);
v_res_2398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_as_2392_, v_i_boxed_2396_, v_stop_boxed_2397_, v_b_2395_);
lean_dec_ref(v_as_2392_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(lean_object* v_as_2399_, size_t v_i_2400_, size_t v_stop_2401_, lean_object* v_b_2402_){
_start:
{
lean_object* v___y_2404_; uint8_t v___x_2408_; 
v___x_2408_ = lean_usize_dec_eq(v_i_2400_, v_stop_2401_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; lean_object* v_fst_2410_; lean_object* v_snd_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v_acc_2415_; lean_object* v___x_2416_; uint8_t v___x_2417_; 
v___x_2409_ = lean_array_uget_borrowed(v_as_2399_, v_i_2400_);
v_fst_2410_ = lean_ctor_get(v___x_2409_, 0);
v_snd_2411_ = lean_ctor_get(v___x_2409_, 1);
v___x_2412_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_2410_);
v___x_2413_ = lean_nat_to_int(v_fst_2410_);
v___x_2414_ = lean_int_neg(v___x_2413_);
lean_dec(v___x_2413_);
v_acc_2415_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2402_, v___x_2414_);
lean_dec(v___x_2414_);
v___x_2416_ = lean_array_get_size(v_snd_2411_);
v___x_2417_ = lean_nat_dec_lt(v___x_2412_, v___x_2416_);
if (v___x_2417_ == 0)
{
v___y_2404_ = v_acc_2415_;
goto v___jp_2403_;
}
else
{
uint8_t v___x_2418_; 
v___x_2418_ = lean_nat_dec_le(v___x_2416_, v___x_2416_);
if (v___x_2418_ == 0)
{
if (v___x_2417_ == 0)
{
v___y_2404_ = v_acc_2415_;
goto v___jp_2403_;
}
else
{
size_t v___x_2419_; size_t v___x_2420_; lean_object* v___x_2421_; 
v___x_2419_ = ((size_t)0ULL);
v___x_2420_ = lean_usize_of_nat(v___x_2416_);
v___x_2421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2411_, v___x_2419_, v___x_2420_, v_acc_2415_);
v___y_2404_ = v___x_2421_;
goto v___jp_2403_;
}
}
else
{
size_t v___x_2422_; size_t v___x_2423_; lean_object* v___x_2424_; 
v___x_2422_ = ((size_t)0ULL);
v___x_2423_ = lean_usize_of_nat(v___x_2416_);
v___x_2424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2411_, v___x_2422_, v___x_2423_, v_acc_2415_);
v___y_2404_ = v___x_2424_;
goto v___jp_2403_;
}
}
}
else
{
return v_b_2402_;
}
v___jp_2403_:
{
size_t v___x_2405_; size_t v___x_2406_; 
v___x_2405_ = ((size_t)1ULL);
v___x_2406_ = lean_usize_add(v_i_2400_, v___x_2405_);
v_i_2400_ = v___x_2406_;
v_b_2402_ = v___y_2404_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3___boxed(lean_object* v_as_2425_, lean_object* v_i_2426_, lean_object* v_stop_2427_, lean_object* v_b_2428_){
_start:
{
size_t v_i_boxed_2429_; size_t v_stop_boxed_2430_; lean_object* v_res_2431_; 
v_i_boxed_2429_ = lean_unbox_usize(v_i_2426_);
lean_dec(v_i_2426_);
v_stop_boxed_2430_ = lean_unbox_usize(v_stop_2427_);
lean_dec(v_stop_2427_);
v_res_2431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(v_as_2425_, v_i_boxed_2429_, v_stop_boxed_2430_, v_b_2428_);
lean_dec_ref(v_as_2425_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(lean_object* v_as_2432_, size_t v_i_2433_, size_t v_stop_2434_, lean_object* v_b_2435_){
_start:
{
lean_object* v___y_2437_; uint8_t v___x_2441_; 
v___x_2441_ = lean_usize_dec_eq(v_i_2433_, v_stop_2434_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; lean_object* v_fst_2443_; lean_object* v_snd_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v_acc_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; 
v___x_2442_ = lean_array_uget_borrowed(v_as_2432_, v_i_2433_);
v_fst_2443_ = lean_ctor_get(v___x_2442_, 0);
v_snd_2444_ = lean_ctor_get(v___x_2442_, 1);
v___x_2445_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_2443_);
v___x_2446_ = lean_nat_to_int(v_fst_2443_);
v___x_2447_ = lean_int_neg(v___x_2446_);
lean_dec(v___x_2446_);
v_acc_2448_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2435_, v___x_2447_);
lean_dec(v___x_2447_);
v___x_2449_ = lean_array_get_size(v_snd_2444_);
v___x_2450_ = lean_nat_dec_lt(v___x_2445_, v___x_2449_);
if (v___x_2450_ == 0)
{
v___y_2437_ = v_acc_2448_;
goto v___jp_2436_;
}
else
{
uint8_t v___x_2451_; 
v___x_2451_ = lean_nat_dec_le(v___x_2449_, v___x_2449_);
if (v___x_2451_ == 0)
{
if (v___x_2450_ == 0)
{
v___y_2437_ = v_acc_2448_;
goto v___jp_2436_;
}
else
{
size_t v___x_2452_; size_t v___x_2453_; lean_object* v___x_2454_; 
v___x_2452_ = ((size_t)0ULL);
v___x_2453_ = lean_usize_of_nat(v___x_2449_);
v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2444_, v___x_2452_, v___x_2453_, v_acc_2448_);
v___y_2437_ = v___x_2454_;
goto v___jp_2436_;
}
}
else
{
size_t v___x_2455_; size_t v___x_2456_; lean_object* v___x_2457_; 
v___x_2455_ = ((size_t)0ULL);
v___x_2456_ = lean_usize_of_nat(v___x_2449_);
v___x_2457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2444_, v___x_2455_, v___x_2456_, v_acc_2448_);
v___y_2437_ = v___x_2457_;
goto v___jp_2436_;
}
}
}
else
{
return v_b_2435_;
}
v___jp_2436_:
{
size_t v___x_2438_; size_t v___x_2439_; lean_object* v___x_2440_; 
v___x_2438_ = ((size_t)1ULL);
v___x_2439_ = lean_usize_add(v_i_2433_, v___x_2438_);
v___x_2440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(v_as_2432_, v___x_2439_, v_stop_2434_, v___y_2437_);
return v___x_2440_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2___boxed(lean_object* v_as_2458_, lean_object* v_i_2459_, lean_object* v_stop_2460_, lean_object* v_b_2461_){
_start:
{
size_t v_i_boxed_2462_; size_t v_stop_boxed_2463_; lean_object* v_res_2464_; 
v_i_boxed_2462_ = lean_unbox_usize(v_i_2459_);
lean_dec(v_i_2459_);
v_stop_boxed_2463_ = lean_unbox_usize(v_stop_2460_);
lean_dec(v_stop_2460_);
v_res_2464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_as_2458_, v_i_boxed_2462_, v_stop_boxed_2463_, v_b_2461_);
lean_dec_ref(v_as_2458_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(lean_object* v_as_2465_, size_t v_i_2466_, size_t v_stop_2467_, lean_object* v_b_2468_){
_start:
{
uint8_t v___x_2469_; 
v___x_2469_ = lean_usize_dec_eq(v_i_2466_, v_stop_2467_);
if (v___x_2469_ == 0)
{
lean_object* v___x_2470_; lean_object* v___x_2471_; size_t v___x_2472_; size_t v___x_2473_; 
v___x_2470_ = lean_array_uget_borrowed(v_as_2465_, v_i_2466_);
v___x_2471_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2468_, v___x_2470_);
v___x_2472_ = ((size_t)1ULL);
v___x_2473_ = lean_usize_add(v_i_2466_, v___x_2472_);
v_i_2466_ = v___x_2473_;
v_b_2468_ = v___x_2471_;
goto _start;
}
else
{
return v_b_2468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1___boxed(lean_object* v_as_2475_, lean_object* v_i_2476_, lean_object* v_stop_2477_, lean_object* v_b_2478_){
_start:
{
size_t v_i_boxed_2479_; size_t v_stop_boxed_2480_; lean_object* v_res_2481_; 
v_i_boxed_2479_ = lean_unbox_usize(v_i_2476_);
lean_dec(v_i_2476_);
v_stop_boxed_2480_ = lean_unbox_usize(v_stop_2477_);
lean_dec(v_stop_2477_);
v_res_2481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_as_2475_, v_i_boxed_2479_, v_stop_boxed_2480_, v_b_2478_);
lean_dec_ref(v_as_2475_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(lean_object* v_proof_2482_, lean_object* v_idx_2483_, lean_object* v_acc_2484_){
_start:
{
lean_object* v___y_2486_; lean_object* v___y_2491_; lean_object* v___y_2495_; lean_object* v___y_2499_; lean_object* v___y_2503_; lean_object* v___x_2506_; uint8_t v___x_2507_; 
v___x_2506_ = lean_array_get_size(v_proof_2482_);
v___x_2507_ = lean_nat_dec_lt(v_idx_2483_, v___x_2506_);
if (v___x_2507_ == 0)
{
lean_dec(v_idx_2483_);
return v_acc_2484_;
}
else
{
lean_object* v___x_2508_; 
v___x_2508_ = lean_array_fget_borrowed(v_proof_2482_, v_idx_2483_);
switch(lean_obj_tag(v___x_2508_))
{
case 0:
{
lean_object* v_id_2509_; lean_object* v_rupHints_2510_; uint8_t v___x_2511_; lean_object* v_acc_2512_; lean_object* v___x_2513_; lean_object* v_acc_2514_; uint8_t v___x_2515_; lean_object* v_acc_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v_id_2509_ = lean_ctor_get(v___x_2508_, 0);
v_rupHints_2510_ = lean_ctor_get(v___x_2508_, 1);
v___x_2511_ = 97;
v_acc_2512_ = lean_byte_array_push(v_acc_2484_, v___x_2511_);
lean_inc(v_id_2509_);
v___x_2513_ = lean_nat_to_int(v_id_2509_);
v_acc_2514_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2512_, v___x_2513_);
lean_dec(v___x_2513_);
v___x_2515_ = 0;
v_acc_2516_ = lean_byte_array_push(v_acc_2514_, v___x_2515_);
v___x_2517_ = lean_unsigned_to_nat(0u);
v___x_2518_ = lean_array_get_size(v_rupHints_2510_);
v___x_2519_ = lean_nat_dec_lt(v___x_2517_, v___x_2518_);
if (v___x_2519_ == 0)
{
v___y_2495_ = v_acc_2516_;
goto v___jp_2494_;
}
else
{
uint8_t v___x_2520_; 
v___x_2520_ = lean_nat_dec_le(v___x_2518_, v___x_2518_);
if (v___x_2520_ == 0)
{
if (v___x_2519_ == 0)
{
v___y_2495_ = v_acc_2516_;
goto v___jp_2494_;
}
else
{
size_t v___x_2521_; size_t v___x_2522_; lean_object* v___x_2523_; 
v___x_2521_ = ((size_t)0ULL);
v___x_2522_ = lean_usize_of_nat(v___x_2518_);
v___x_2523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2510_, v___x_2521_, v___x_2522_, v_acc_2516_);
v___y_2495_ = v___x_2523_;
goto v___jp_2494_;
}
}
else
{
size_t v___x_2524_; size_t v___x_2525_; lean_object* v___x_2526_; 
v___x_2524_ = ((size_t)0ULL);
v___x_2525_ = lean_usize_of_nat(v___x_2518_);
v___x_2526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2510_, v___x_2524_, v___x_2525_, v_acc_2516_);
v___y_2495_ = v___x_2526_;
goto v___jp_2494_;
}
}
}
case 1:
{
lean_object* v_id_2527_; lean_object* v_c_2528_; lean_object* v_rupHints_2529_; uint8_t v___x_2530_; lean_object* v_acc_2531_; lean_object* v___x_2532_; lean_object* v_acc_2533_; lean_object* v___x_2534_; lean_object* v___y_2536_; lean_object* v___x_2548_; uint8_t v___x_2549_; 
v_id_2527_ = lean_ctor_get(v___x_2508_, 0);
v_c_2528_ = lean_ctor_get(v___x_2508_, 1);
v_rupHints_2529_ = lean_ctor_get(v___x_2508_, 2);
v___x_2530_ = 97;
v_acc_2531_ = lean_byte_array_push(v_acc_2484_, v___x_2530_);
lean_inc(v_id_2527_);
v___x_2532_ = lean_nat_to_int(v_id_2527_);
v_acc_2533_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2531_, v___x_2532_);
lean_dec(v___x_2532_);
v___x_2534_ = lean_unsigned_to_nat(0u);
v___x_2548_ = lean_array_get_size(v_c_2528_);
v___x_2549_ = lean_nat_dec_lt(v___x_2534_, v___x_2548_);
if (v___x_2549_ == 0)
{
v___y_2536_ = v_acc_2533_;
goto v___jp_2535_;
}
else
{
uint8_t v___x_2550_; 
v___x_2550_ = lean_nat_dec_le(v___x_2548_, v___x_2548_);
if (v___x_2550_ == 0)
{
if (v___x_2549_ == 0)
{
v___y_2536_ = v_acc_2533_;
goto v___jp_2535_;
}
else
{
size_t v___x_2551_; size_t v___x_2552_; lean_object* v___x_2553_; 
v___x_2551_ = ((size_t)0ULL);
v___x_2552_ = lean_usize_of_nat(v___x_2548_);
v___x_2553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2528_, v___x_2551_, v___x_2552_, v_acc_2533_);
v___y_2536_ = v___x_2553_;
goto v___jp_2535_;
}
}
else
{
size_t v___x_2554_; size_t v___x_2555_; lean_object* v___x_2556_; 
v___x_2554_ = ((size_t)0ULL);
v___x_2555_ = lean_usize_of_nat(v___x_2548_);
v___x_2556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2528_, v___x_2554_, v___x_2555_, v_acc_2533_);
v___y_2536_ = v___x_2556_;
goto v___jp_2535_;
}
}
v___jp_2535_:
{
uint8_t v___x_2537_; lean_object* v_acc_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2537_ = 0;
v_acc_2538_ = lean_byte_array_push(v___y_2536_, v___x_2537_);
v___x_2539_ = lean_array_get_size(v_rupHints_2529_);
v___x_2540_ = lean_nat_dec_lt(v___x_2534_, v___x_2539_);
if (v___x_2540_ == 0)
{
v___y_2499_ = v_acc_2538_;
goto v___jp_2498_;
}
else
{
uint8_t v___x_2541_; 
v___x_2541_ = lean_nat_dec_le(v___x_2539_, v___x_2539_);
if (v___x_2541_ == 0)
{
if (v___x_2540_ == 0)
{
v___y_2499_ = v_acc_2538_;
goto v___jp_2498_;
}
else
{
size_t v___x_2542_; size_t v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = ((size_t)0ULL);
v___x_2543_ = lean_usize_of_nat(v___x_2539_);
v___x_2544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2529_, v___x_2542_, v___x_2543_, v_acc_2538_);
v___y_2499_ = v___x_2544_;
goto v___jp_2498_;
}
}
else
{
size_t v___x_2545_; size_t v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = ((size_t)0ULL);
v___x_2546_ = lean_usize_of_nat(v___x_2539_);
v___x_2547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2529_, v___x_2545_, v___x_2546_, v_acc_2538_);
v___y_2499_ = v___x_2547_;
goto v___jp_2498_;
}
}
}
}
case 2:
{
lean_object* v_id_2557_; lean_object* v_c_2558_; lean_object* v_rupHints_2559_; lean_object* v_ratHints_2560_; uint8_t v___x_2561_; lean_object* v_acc_2562_; lean_object* v___x_2563_; lean_object* v_acc_2564_; lean_object* v___x_2565_; lean_object* v___y_2567_; lean_object* v___y_2578_; lean_object* v___x_2590_; uint8_t v___x_2591_; 
v_id_2557_ = lean_ctor_get(v___x_2508_, 0);
v_c_2558_ = lean_ctor_get(v___x_2508_, 1);
v_rupHints_2559_ = lean_ctor_get(v___x_2508_, 3);
v_ratHints_2560_ = lean_ctor_get(v___x_2508_, 4);
v___x_2561_ = 97;
v_acc_2562_ = lean_byte_array_push(v_acc_2484_, v___x_2561_);
lean_inc(v_id_2557_);
v___x_2563_ = lean_nat_to_int(v_id_2557_);
v_acc_2564_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2562_, v___x_2563_);
lean_dec(v___x_2563_);
v___x_2565_ = lean_unsigned_to_nat(0u);
v___x_2590_ = lean_array_get_size(v_c_2558_);
v___x_2591_ = lean_nat_dec_lt(v___x_2565_, v___x_2590_);
if (v___x_2591_ == 0)
{
v___y_2578_ = v_acc_2564_;
goto v___jp_2577_;
}
else
{
uint8_t v___x_2592_; 
v___x_2592_ = lean_nat_dec_le(v___x_2590_, v___x_2590_);
if (v___x_2592_ == 0)
{
if (v___x_2591_ == 0)
{
v___y_2578_ = v_acc_2564_;
goto v___jp_2577_;
}
else
{
size_t v___x_2593_; size_t v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = ((size_t)0ULL);
v___x_2594_ = lean_usize_of_nat(v___x_2590_);
v___x_2595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2558_, v___x_2593_, v___x_2594_, v_acc_2564_);
v___y_2578_ = v___x_2595_;
goto v___jp_2577_;
}
}
else
{
size_t v___x_2596_; size_t v___x_2597_; lean_object* v___x_2598_; 
v___x_2596_ = ((size_t)0ULL);
v___x_2597_ = lean_usize_of_nat(v___x_2590_);
v___x_2598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2558_, v___x_2596_, v___x_2597_, v_acc_2564_);
v___y_2578_ = v___x_2598_;
goto v___jp_2577_;
}
}
v___jp_2566_:
{
lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2568_ = lean_array_get_size(v_ratHints_2560_);
v___x_2569_ = lean_nat_dec_lt(v___x_2565_, v___x_2568_);
if (v___x_2569_ == 0)
{
v___y_2491_ = v___y_2567_;
goto v___jp_2490_;
}
else
{
uint8_t v___x_2570_; 
v___x_2570_ = lean_nat_dec_le(v___x_2568_, v___x_2568_);
if (v___x_2570_ == 0)
{
if (v___x_2569_ == 0)
{
v___y_2491_ = v___y_2567_;
goto v___jp_2490_;
}
else
{
size_t v___x_2571_; size_t v___x_2572_; lean_object* v___x_2573_; 
v___x_2571_ = ((size_t)0ULL);
v___x_2572_ = lean_usize_of_nat(v___x_2568_);
v___x_2573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_ratHints_2560_, v___x_2571_, v___x_2572_, v___y_2567_);
v___y_2491_ = v___x_2573_;
goto v___jp_2490_;
}
}
else
{
size_t v___x_2574_; size_t v___x_2575_; lean_object* v___x_2576_; 
v___x_2574_ = ((size_t)0ULL);
v___x_2575_ = lean_usize_of_nat(v___x_2568_);
v___x_2576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_ratHints_2560_, v___x_2574_, v___x_2575_, v___y_2567_);
v___y_2491_ = v___x_2576_;
goto v___jp_2490_;
}
}
}
v___jp_2577_:
{
uint8_t v___x_2579_; lean_object* v_acc_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; 
v___x_2579_ = 0;
v_acc_2580_ = lean_byte_array_push(v___y_2578_, v___x_2579_);
v___x_2581_ = lean_array_get_size(v_rupHints_2559_);
v___x_2582_ = lean_nat_dec_lt(v___x_2565_, v___x_2581_);
if (v___x_2582_ == 0)
{
v___y_2567_ = v_acc_2580_;
goto v___jp_2566_;
}
else
{
uint8_t v___x_2583_; 
v___x_2583_ = lean_nat_dec_le(v___x_2581_, v___x_2581_);
if (v___x_2583_ == 0)
{
if (v___x_2582_ == 0)
{
v___y_2567_ = v_acc_2580_;
goto v___jp_2566_;
}
else
{
size_t v___x_2584_; size_t v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = ((size_t)0ULL);
v___x_2585_ = lean_usize_of_nat(v___x_2581_);
v___x_2586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2559_, v___x_2584_, v___x_2585_, v_acc_2580_);
v___y_2567_ = v___x_2586_;
goto v___jp_2566_;
}
}
else
{
size_t v___x_2587_; size_t v___x_2588_; lean_object* v___x_2589_; 
v___x_2587_ = ((size_t)0ULL);
v___x_2588_ = lean_usize_of_nat(v___x_2581_);
v___x_2589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2559_, v___x_2587_, v___x_2588_, v_acc_2580_);
v___y_2567_ = v___x_2589_;
goto v___jp_2566_;
}
}
}
}
default: 
{
lean_object* v_ids_2599_; uint8_t v___x_2600_; lean_object* v_acc_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; uint8_t v___x_2604_; 
v_ids_2599_ = lean_ctor_get(v___x_2508_, 0);
v___x_2600_ = 100;
v_acc_2601_ = lean_byte_array_push(v_acc_2484_, v___x_2600_);
v___x_2602_ = lean_unsigned_to_nat(0u);
v___x_2603_ = lean_array_get_size(v_ids_2599_);
v___x_2604_ = lean_nat_dec_lt(v___x_2602_, v___x_2603_);
if (v___x_2604_ == 0)
{
v___y_2503_ = v_acc_2601_;
goto v___jp_2502_;
}
else
{
uint8_t v___x_2605_; 
v___x_2605_ = lean_nat_dec_le(v___x_2603_, v___x_2603_);
if (v___x_2605_ == 0)
{
if (v___x_2604_ == 0)
{
v___y_2503_ = v_acc_2601_;
goto v___jp_2502_;
}
else
{
size_t v___x_2606_; size_t v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = ((size_t)0ULL);
v___x_2607_ = lean_usize_of_nat(v___x_2603_);
v___x_2608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_ids_2599_, v___x_2606_, v___x_2607_, v_acc_2601_);
v___y_2503_ = v___x_2608_;
goto v___jp_2502_;
}
}
else
{
size_t v___x_2609_; size_t v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = ((size_t)0ULL);
v___x_2610_ = lean_usize_of_nat(v___x_2603_);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_ids_2599_, v___x_2609_, v___x_2610_, v_acc_2601_);
v___y_2503_ = v___x_2611_;
goto v___jp_2502_;
}
}
}
}
}
v___jp_2485_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2487_ = lean_unsigned_to_nat(1u);
v___x_2488_ = lean_nat_add(v_idx_2483_, v___x_2487_);
lean_dec(v_idx_2483_);
v_idx_2483_ = v___x_2488_;
v_acc_2484_ = v___y_2486_;
goto _start;
}
v___jp_2490_:
{
uint8_t v___x_2492_; lean_object* v_acc_2493_; 
v___x_2492_ = 0;
v_acc_2493_ = lean_byte_array_push(v___y_2491_, v___x_2492_);
v___y_2486_ = v_acc_2493_;
goto v___jp_2485_;
}
v___jp_2494_:
{
uint8_t v___x_2496_; lean_object* v_acc_2497_; 
v___x_2496_ = 0;
v_acc_2497_ = lean_byte_array_push(v___y_2495_, v___x_2496_);
v___y_2486_ = v_acc_2497_;
goto v___jp_2485_;
}
v___jp_2498_:
{
uint8_t v___x_2500_; lean_object* v_acc_2501_; 
v___x_2500_ = 0;
v_acc_2501_ = lean_byte_array_push(v___y_2499_, v___x_2500_);
v___y_2486_ = v_acc_2501_;
goto v___jp_2485_;
}
v___jp_2502_:
{
uint8_t v___x_2504_; lean_object* v_acc_2505_; 
v___x_2504_ = 0;
v_acc_2505_ = lean_byte_array_push(v___y_2503_, v___x_2504_);
v___y_2486_ = v_acc_2505_;
goto v___jp_2485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___boxed(lean_object* v_proof_2612_, lean_object* v_idx_2613_, lean_object* v_acc_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(v_proof_2612_, v_idx_2613_, v_acc_2614_);
lean_dec_ref(v_proof_2612_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(lean_object* v_proof_2616_){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2617_ = lean_unsigned_to_nat(0u);
v___x_2618_ = lean_unsigned_to_nat(4u);
v___x_2619_ = lean_array_get_size(v_proof_2616_);
v___x_2620_ = lean_nat_mul(v___x_2618_, v___x_2619_);
v___x_2621_ = lean_mk_empty_byte_array(v___x_2620_);
lean_dec(v___x_2620_);
v___x_2622_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(v_proof_2616_, v___x_2617_, v___x_2621_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary___boxed(lean_object* v_proof_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(v_proof_2623_);
lean_dec_ref(v_proof_2623_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object* v_path_2625_, lean_object* v_proof_2626_, uint8_t v_binaryProofs_2627_){
_start:
{
if (v_binaryProofs_2627_ == 0)
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_proof_2626_);
v___x_2630_ = lean_string_to_utf8(v___x_2629_);
lean_dec_ref(v___x_2629_);
v___x_2631_ = l_IO_FS_writeBinFile(v_path_2625_, v___x_2630_);
lean_dec_ref(v___x_2630_);
return v___x_2631_;
}
else
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2632_ = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(v_proof_2626_);
v___x_2633_ = l_IO_FS_writeBinFile(v_path_2625_, v___x_2632_);
lean_dec_ref(v___x_2632_);
return v___x_2633_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof___boxed(lean_object* v_path_2634_, lean_object* v_proof_2635_, lean_object* v_binaryProofs_2636_, lean_object* v_a_2637_){
_start:
{
uint8_t v_binaryProofs_boxed_2638_; lean_object* v_res_2639_; 
v_binaryProofs_boxed_2638_ = lean_unbox(v_binaryProofs_2636_);
v_res_2639_ = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(v_path_2634_, v_proof_2635_, v_binaryProofs_boxed_2638_);
lean_dec_ref(v_proof_2635_);
lean_dec_ref(v_path_2634_);
return v_res_2639_;
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
