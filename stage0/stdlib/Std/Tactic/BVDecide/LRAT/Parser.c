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
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t lean_uint32_to_uint8(uint32_t);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* v_array_72_; lean_object* v_idx_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v_array_72_ = lean_ctor_get(v_a_68_, 0);
v_idx_73_ = lean_ctor_get(v_a_68_, 1);
v___x_74_ = lean_byte_array_size(v_array_72_);
v___x_75_ = lean_nat_dec_lt(v_idx_73_, v___x_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_box(0);
v___x_77_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_77_, 0, v_a_68_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
return v___x_77_;
}
else
{
uint8_t v_c_78_; uint8_t v___x_79_; uint8_t v___x_80_; 
v_c_78_ = lean_byte_array_fget(v_array_72_, v_idx_73_);
v___x_79_ = 48;
v___x_80_ = lean_uint8_dec_le(v___x_79_, v_c_78_);
if (v___x_80_ == 0)
{
goto v___jp_69_;
}
else
{
uint8_t v___x_81_; uint8_t v___x_82_; 
v___x_81_ = 57;
v___x_82_ = lean_uint8_dec_le(v_c_78_, v___x_81_);
if (v___x_82_ == 0)
{
goto v___jp_69_;
}
else
{
lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_111_; 
lean_inc(v_idx_73_);
lean_inc_ref(v_array_72_);
v_isSharedCheck_111_ = !lean_is_exclusive(v_a_68_);
if (v_isSharedCheck_111_ == 0)
{
lean_object* v_unused_112_; lean_object* v_unused_113_; 
v_unused_112_ = lean_ctor_get(v_a_68_, 1);
lean_dec(v_unused_112_);
v_unused_113_ = lean_ctor_get(v_a_68_, 0);
lean_dec(v_unused_113_);
v___x_84_ = v_a_68_;
v_isShared_85_ = v_isSharedCheck_111_;
goto v_resetjp_83_;
}
else
{
lean_dec(v_a_68_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_111_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v_it_x27_89_; 
v___x_86_ = lean_unsigned_to_nat(1u);
v___x_87_ = lean_nat_add(v_idx_73_, v___x_86_);
lean_dec(v_idx_73_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v___x_87_);
v_it_x27_89_ = v___x_84_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_array_72_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v___x_87_);
v_it_x27_89_ = v_reuseFailAlloc_110_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
uint32_t v___x_90_; uint8_t v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v_fst_95_; lean_object* v_snd_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_109_; 
v___x_90_ = lean_uint8_to_uint32(v_c_78_);
v___x_91_ = lean_uint32_to_uint8(v___x_90_);
v___x_92_ = lean_uint8_sub(v___x_91_, v___x_79_);
v___x_93_ = lean_uint8_to_nat(v___x_92_);
v___x_94_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_89_, v___x_93_);
v_fst_95_ = lean_ctor_get(v___x_94_, 0);
v_snd_96_ = lean_ctor_get(v___x_94_, 1);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_109_ == 0)
{
v___x_98_ = v___x_94_;
v_isShared_99_ = v_isSharedCheck_109_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_snd_96_);
lean_inc(v_fst_95_);
lean_dec(v___x_94_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_109_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_nat_dec_eq(v_fst_95_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_103_; 
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v_fst_95_);
lean_ctor_set(v___x_98_, 0, v_snd_96_);
v___x_103_ = v___x_98_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_snd_96_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_fst_95_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
else
{
lean_object* v___x_105_; lean_object* v___x_107_; 
lean_dec(v_fst_95_);
v___x_105_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_99_ == 0)
{
lean_ctor_set_tag(v___x_98_, 1);
lean_ctor_set(v___x_98_, 1, v___x_105_);
lean_ctor_set(v___x_98_, 0, v_snd_96_);
v___x_107_ = v___x_98_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_snd_96_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v___x_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
}
}
}
v___jp_69_:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_71_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_71_, 0, v_a_68_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg(lean_object* v_a_117_){
_start:
{
lean_object* v_array_118_; lean_object* v_idx_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v_array_118_ = lean_ctor_get(v_a_117_, 0);
v_idx_119_ = lean_ctor_get(v_a_117_, 1);
v___x_120_ = lean_byte_array_size(v_array_118_);
v___x_121_ = lean_nat_dec_lt(v_idx_119_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_box(0);
v___x_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_123_, 0, v_a_117_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
return v___x_123_;
}
else
{
uint8_t v___x_124_; uint8_t v_got_125_; uint8_t v___x_126_; 
v___x_124_ = 45;
v_got_125_ = lean_byte_array_fget(v_array_118_, v_idx_119_);
v___x_126_ = lean_uint8_dec_eq(v_got_125_, v___x_124_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1));
v___x_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_128_, 0, v_a_117_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
return v___x_128_;
}
else
{
lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_172_; 
lean_inc(v_idx_119_);
lean_inc_ref(v_array_118_);
v_isSharedCheck_172_ = !lean_is_exclusive(v_a_117_);
if (v_isSharedCheck_172_ == 0)
{
lean_object* v_unused_173_; lean_object* v_unused_174_; 
v_unused_173_ = lean_ctor_get(v_a_117_, 1);
lean_dec(v_unused_173_);
v_unused_174_ = lean_ctor_get(v_a_117_, 0);
lean_dec(v_unused_174_);
v___x_130_ = v_a_117_;
v_isShared_131_ = v_isSharedCheck_172_;
goto v_resetjp_129_;
}
else
{
lean_dec(v_a_117_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_172_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lean_nat_add(v_idx_119_, v___x_132_);
lean_dec(v_idx_119_);
lean_inc(v___x_133_);
lean_inc_ref(v_array_118_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_133_);
v___x_135_ = v___x_130_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_array_118_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_133_);
v___x_135_ = v_reuseFailAlloc_171_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
uint8_t v___x_139_; 
v___x_139_ = lean_nat_dec_lt(v___x_133_, v___x_120_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec(v___x_133_);
lean_dec_ref(v_array_118_);
v___x_140_ = lean_box(0);
v___x_141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_135_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
return v___x_141_;
}
else
{
uint8_t v_c_142_; uint8_t v___x_143_; uint8_t v___x_144_; 
v_c_142_ = lean_byte_array_fget(v_array_118_, v___x_133_);
v___x_143_ = 48;
v___x_144_ = lean_uint8_dec_le(v___x_143_, v_c_142_);
if (v___x_144_ == 0)
{
lean_dec(v___x_133_);
lean_dec_ref(v_array_118_);
goto v___jp_136_;
}
else
{
uint8_t v___x_145_; uint8_t v___x_146_; 
v___x_145_ = 57;
v___x_146_ = lean_uint8_dec_le(v_c_142_, v___x_145_);
if (v___x_146_ == 0)
{
lean_dec(v___x_133_);
lean_dec_ref(v_array_118_);
goto v___jp_136_;
}
else
{
lean_object* v___x_147_; lean_object* v_it_x27_148_; uint32_t v___x_149_; uint8_t v___x_150_; uint8_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_fst_154_; lean_object* v_snd_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_170_; 
lean_dec_ref(v___x_135_);
v___x_147_ = lean_nat_add(v___x_133_, v___x_132_);
lean_dec(v___x_133_);
v_it_x27_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_148_, 0, v_array_118_);
lean_ctor_set(v_it_x27_148_, 1, v___x_147_);
v___x_149_ = lean_uint8_to_uint32(v_c_142_);
v___x_150_ = lean_uint32_to_uint8(v___x_149_);
v___x_151_ = lean_uint8_sub(v___x_150_, v___x_143_);
v___x_152_ = lean_uint8_to_nat(v___x_151_);
v___x_153_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_148_, v___x_152_);
v_fst_154_ = lean_ctor_get(v___x_153_, 0);
v_snd_155_ = lean_ctor_get(v___x_153_, 1);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_170_ == 0)
{
v___x_157_ = v___x_153_;
v_isShared_158_ = v_isSharedCheck_170_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_snd_155_);
lean_inc(v_fst_154_);
lean_dec(v___x_153_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_170_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = lean_nat_dec_eq(v_fst_154_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_161_ = lean_nat_to_int(v_fst_154_);
v___x_162_ = lean_int_neg(v___x_161_);
lean_dec(v___x_161_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 1, v___x_162_);
lean_ctor_set(v___x_157_, 0, v_snd_155_);
v___x_164_ = v___x_157_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_snd_155_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
else
{
lean_object* v___x_166_; lean_object* v___x_168_; 
lean_dec(v_fst_154_);
v___x_166_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_158_ == 0)
{
lean_ctor_set_tag(v___x_157_, 1);
lean_ctor_set(v___x_157_, 1, v___x_166_);
lean_ctor_set(v___x_157_, 0, v_snd_155_);
v___x_168_ = v___x_157_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_snd_155_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
}
}
v___jp_136_:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_135_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
return v___x_138_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseId(lean_object* v_a_175_){
_start:
{
lean_object* v_array_179_; lean_object* v_idx_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v_array_179_ = lean_ctor_get(v_a_175_, 0);
v_idx_180_ = lean_ctor_get(v_a_175_, 1);
v___x_181_ = lean_byte_array_size(v_array_179_);
v___x_182_ = lean_nat_dec_lt(v_idx_180_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_box(0);
v___x_184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_184_, 0, v_a_175_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
return v___x_184_;
}
else
{
uint8_t v_c_185_; uint8_t v___x_186_; uint8_t v___x_187_; 
v_c_185_ = lean_byte_array_fget(v_array_179_, v_idx_180_);
v___x_186_ = 48;
v___x_187_ = lean_uint8_dec_le(v___x_186_, v_c_185_);
if (v___x_187_ == 0)
{
goto v___jp_176_;
}
else
{
uint8_t v___x_188_; uint8_t v___x_189_; 
v___x_188_ = 57;
v___x_189_ = lean_uint8_dec_le(v_c_185_, v___x_188_);
if (v___x_189_ == 0)
{
goto v___jp_176_;
}
else
{
lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_218_; 
lean_inc(v_idx_180_);
lean_inc_ref(v_array_179_);
v_isSharedCheck_218_ = !lean_is_exclusive(v_a_175_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; lean_object* v_unused_220_; 
v_unused_219_ = lean_ctor_get(v_a_175_, 1);
lean_dec(v_unused_219_);
v_unused_220_ = lean_ctor_get(v_a_175_, 0);
lean_dec(v_unused_220_);
v___x_191_ = v_a_175_;
v_isShared_192_ = v_isSharedCheck_218_;
goto v_resetjp_190_;
}
else
{
lean_dec(v_a_175_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_218_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v_it_x27_196_; 
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = lean_nat_add(v_idx_180_, v___x_193_);
lean_dec(v_idx_180_);
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
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_array_179_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v___x_194_);
v_it_x27_196_ = v_reuseFailAlloc_217_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
uint32_t v___x_197_; uint8_t v___x_198_; uint8_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_fst_202_; lean_object* v_snd_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_216_; 
v___x_197_ = lean_uint8_to_uint32(v_c_185_);
v___x_198_ = lean_uint32_to_uint8(v___x_197_);
v___x_199_ = lean_uint8_sub(v___x_198_, v___x_186_);
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
v___jp_176_:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_178_, 0, v_a_175_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero(lean_object* v_a_224_){
_start:
{
lean_object* v_array_225_; lean_object* v_idx_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v_array_225_ = lean_ctor_get(v_a_224_, 0);
v_idx_226_ = lean_ctor_get(v_a_224_, 1);
v___x_227_ = lean_byte_array_size(v_array_225_);
v___x_228_ = lean_nat_dec_lt(v_idx_226_, v___x_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_box(0);
v___x_230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_230_, 0, v_a_224_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
return v___x_230_;
}
else
{
uint8_t v___x_231_; uint8_t v_got_232_; uint8_t v___x_233_; 
v___x_231_ = 48;
v_got_232_ = lean_byte_array_fget(v_array_225_, v_idx_226_);
v___x_233_ = lean_uint8_dec_eq(v_got_232_, v___x_231_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1));
v___x_235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_235_, 0, v_a_224_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
return v___x_235_;
}
else
{
lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_246_; 
lean_inc(v_idx_226_);
lean_inc_ref(v_array_225_);
v_isSharedCheck_246_ = !lean_is_exclusive(v_a_224_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; lean_object* v_unused_248_; 
v_unused_247_ = lean_ctor_get(v_a_224_, 1);
lean_dec(v_unused_247_);
v_unused_248_ = lean_ctor_get(v_a_224_, 0);
lean_dec(v_unused_248_);
v___x_237_ = v_a_224_;
v_isShared_238_ = v_isSharedCheck_246_;
goto v_resetjp_236_;
}
else
{
lean_dec(v_a_224_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_246_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_add(v_idx_226_, v___x_239_);
lean_dec(v_idx_226_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v___x_240_);
v___x_242_ = v___x_237_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_array_225_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v___x_240_);
v___x_242_ = v_reuseFailAlloc_245_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_box(0);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
return v___x_244_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs(lean_object* v_a_252_){
_start:
{
lean_object* v_array_256_; lean_object* v_idx_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v_array_256_ = lean_ctor_get(v_a_252_, 0);
v_idx_257_ = lean_ctor_get(v_a_252_, 1);
v___x_258_ = lean_byte_array_size(v_array_256_);
v___x_259_ = lean_nat_dec_lt(v_idx_257_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_box(0);
v___x_261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_261_, 0, v_a_252_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
return v___x_261_;
}
else
{
uint8_t v_c_262_; uint8_t v___x_263_; uint8_t v___x_264_; 
v_c_262_ = lean_byte_array_fget(v_array_256_, v_idx_257_);
v___x_263_ = 48;
v___x_264_ = lean_uint8_dec_le(v___x_263_, v_c_262_);
if (v___x_264_ == 0)
{
goto v___jp_253_;
}
else
{
uint8_t v___x_265_; uint8_t v___x_266_; 
v___x_265_ = 57;
v___x_266_ = lean_uint8_dec_le(v_c_262_, v___x_265_);
if (v___x_266_ == 0)
{
goto v___jp_253_;
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_it_x27_269_; uint32_t v___x_270_; uint8_t v___x_271_; uint8_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v_fst_275_; lean_object* v_snd_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_314_; 
v___x_267_ = lean_unsigned_to_nat(1u);
v___x_268_ = lean_nat_add(v_idx_257_, v___x_267_);
lean_inc_ref(v_array_256_);
v_it_x27_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_269_, 0, v_array_256_);
lean_ctor_set(v_it_x27_269_, 1, v___x_268_);
v___x_270_ = lean_uint8_to_uint32(v_c_262_);
v___x_271_ = lean_uint32_to_uint8(v___x_270_);
v___x_272_ = lean_uint8_sub(v___x_271_, v___x_263_);
v___x_273_ = lean_uint8_to_nat(v___x_272_);
v___x_274_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_269_, v___x_273_);
v_fst_275_ = lean_ctor_get(v___x_274_, 0);
v_snd_276_ = lean_ctor_get(v___x_274_, 1);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_314_ == 0)
{
v___x_278_ = v___x_274_;
v_isShared_279_ = v_isSharedCheck_314_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_snd_276_);
lean_inc(v_fst_275_);
lean_dec(v___x_274_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_314_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = lean_nat_dec_eq(v_fst_275_, v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v_array_282_; lean_object* v_idx_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
lean_dec_ref(v_a_252_);
v_array_282_ = lean_ctor_get(v_snd_276_, 0);
v_idx_283_ = lean_ctor_get(v_snd_276_, 1);
v___x_284_ = lean_byte_array_size(v_array_282_);
v___x_285_ = lean_nat_dec_lt(v_idx_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_288_; 
lean_dec(v_fst_275_);
v___x_286_ = lean_box(0);
if (v_isShared_279_ == 0)
{
lean_ctor_set_tag(v___x_278_, 1);
lean_ctor_set(v___x_278_, 1, v___x_286_);
lean_ctor_set(v___x_278_, 0, v_snd_276_);
v___x_288_ = v___x_278_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_snd_276_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
else
{
uint8_t v___x_290_; uint8_t v_got_291_; uint8_t v___x_292_; 
v___x_290_ = 32;
v_got_291_ = lean_byte_array_fget(v_array_282_, v_idx_283_);
v___x_292_ = lean_uint8_dec_eq(v_got_291_, v___x_290_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_295_; 
lean_dec(v_fst_275_);
v___x_293_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
if (v_isShared_279_ == 0)
{
lean_ctor_set_tag(v___x_278_, 1);
lean_ctor_set(v___x_278_, 1, v___x_293_);
lean_ctor_set(v___x_278_, 0, v_snd_276_);
v___x_295_ = v___x_278_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_snd_276_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
else
{
lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_307_; 
lean_inc(v_idx_283_);
lean_inc_ref(v_array_282_);
v_isSharedCheck_307_ = !lean_is_exclusive(v_snd_276_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; lean_object* v_unused_309_; 
v_unused_308_ = lean_ctor_get(v_snd_276_, 1);
lean_dec(v_unused_308_);
v_unused_309_ = lean_ctor_get(v_snd_276_, 0);
lean_dec(v_unused_309_);
v___x_298_ = v_snd_276_;
v_isShared_299_ = v_isSharedCheck_307_;
goto v_resetjp_297_;
}
else
{
lean_dec(v_snd_276_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_307_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_300_ = lean_nat_add(v_idx_283_, v___x_267_);
lean_dec(v_idx_283_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 1, v___x_300_);
v___x_302_ = v___x_298_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_array_282_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v___x_300_);
v___x_302_ = v_reuseFailAlloc_306_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_304_; 
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 1, v_fst_275_);
lean_ctor_set(v___x_278_, 0, v___x_302_);
v___x_304_ = v___x_278_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_fst_275_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
}
else
{
lean_object* v___x_310_; lean_object* v___x_312_; 
lean_dec(v_snd_276_);
lean_dec(v_fst_275_);
v___x_310_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_279_ == 0)
{
lean_ctor_set_tag(v___x_278_, 1);
lean_ctor_set(v___x_278_, 1, v___x_310_);
lean_ctor_set(v___x_278_, 0, v_a_252_);
v___x_312_ = v___x_278_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_252_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
}
v___jp_253_:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_255_, 0, v_a_252_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_spec__0(lean_object* v_acc_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_array_317_; lean_object* v_idx_318_; lean_object* v_pos_320_; lean_object* v_idx_321_; lean_object* v_err_322_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_array_317_ = lean_ctor_get(v_a_316_, 0);
v_idx_318_ = lean_ctor_get(v_a_316_, 1);
lean_inc(v_idx_318_);
v___x_328_ = lean_byte_array_size(v_array_317_);
v___x_329_ = lean_nat_dec_lt(v_idx_318_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
v___x_330_ = lean_box(0);
lean_inc(v_idx_318_);
v_pos_320_ = v_a_316_;
v_idx_321_ = v_idx_318_;
v_err_322_ = v___x_330_;
goto v___jp_319_;
}
else
{
uint8_t v_c_331_; uint8_t v___x_332_; uint8_t v___x_333_; 
v_c_331_ = lean_byte_array_fget(v_array_317_, v_idx_318_);
v___x_332_ = 48;
v___x_333_ = lean_uint8_dec_le(v___x_332_, v_c_331_);
if (v___x_333_ == 0)
{
goto v___jp_326_;
}
else
{
uint8_t v___x_334_; uint8_t v___x_335_; 
v___x_334_ = 57;
v___x_335_ = lean_uint8_dec_le(v_c_331_, v___x_334_);
if (v___x_335_ == 0)
{
goto v___jp_326_;
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v_it_x27_338_; uint32_t v___x_339_; uint8_t v___x_340_; uint8_t v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v_fst_344_; lean_object* v_snd_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = lean_nat_add(v_idx_318_, v___x_336_);
lean_inc_ref(v_array_317_);
v_it_x27_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_338_, 0, v_array_317_);
lean_ctor_set(v_it_x27_338_, 1, v___x_337_);
v___x_339_ = lean_uint8_to_uint32(v_c_331_);
v___x_340_ = lean_uint32_to_uint8(v___x_339_);
v___x_341_ = lean_uint8_sub(v___x_340_, v___x_332_);
v___x_342_ = lean_uint8_to_nat(v___x_341_);
v___x_343_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_338_, v___x_342_);
v_fst_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_fst_344_);
v_snd_345_ = lean_ctor_get(v___x_343_, 1);
lean_inc(v_snd_345_);
lean_dec_ref(v___x_343_);
v___x_346_ = lean_unsigned_to_nat(0u);
v___x_347_ = lean_nat_dec_eq(v_fst_344_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v_array_348_; lean_object* v_idx_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
lean_dec_ref(v_a_316_);
v_array_348_ = lean_ctor_get(v_snd_345_, 0);
v_idx_349_ = lean_ctor_get(v_snd_345_, 1);
lean_inc(v_idx_349_);
v___x_350_ = lean_byte_array_size(v_array_348_);
v___x_351_ = lean_nat_dec_lt(v_idx_349_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
lean_dec(v_fst_344_);
v___x_352_ = lean_box(0);
v_pos_320_ = v_snd_345_;
v_idx_321_ = v_idx_349_;
v_err_322_ = v___x_352_;
goto v___jp_319_;
}
else
{
uint8_t v___x_353_; uint8_t v_got_354_; uint8_t v___x_355_; 
v___x_353_ = 32;
v_got_354_ = lean_byte_array_fget(v_array_348_, v_idx_349_);
v___x_355_ = lean_uint8_dec_eq(v_got_354_, v___x_353_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
lean_dec(v_fst_344_);
v___x_356_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
v_pos_320_ = v_snd_345_;
v_idx_321_ = v_idx_349_;
v_err_322_ = v___x_356_;
goto v___jp_319_;
}
else
{
lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_366_; 
lean_inc_ref(v_array_348_);
lean_dec(v_idx_318_);
v_isSharedCheck_366_ = !lean_is_exclusive(v_snd_345_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; lean_object* v_unused_368_; 
v_unused_367_ = lean_ctor_get(v_snd_345_, 1);
lean_dec(v_unused_367_);
v_unused_368_ = lean_ctor_get(v_snd_345_, 0);
lean_dec(v_unused_368_);
v___x_358_ = v_snd_345_;
v_isShared_359_ = v_isSharedCheck_366_;
goto v_resetjp_357_;
}
else
{
lean_dec(v_snd_345_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_366_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_360_ = lean_nat_add(v_idx_349_, v___x_336_);
lean_dec(v_idx_349_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 1, v___x_360_);
v___x_362_ = v___x_358_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_array_348_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v___x_360_);
v___x_362_ = v_reuseFailAlloc_365_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; 
v___x_363_ = lean_array_push(v_acc_315_, v_fst_344_);
v_acc_315_ = v___x_363_;
v_a_316_ = v___x_362_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_369_; 
lean_dec(v_snd_345_);
lean_dec(v_fst_344_);
v___x_369_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
lean_inc(v_idx_318_);
v_pos_320_ = v_a_316_;
v_idx_321_ = v_idx_318_;
v_err_322_ = v___x_369_;
goto v___jp_319_;
}
}
}
}
v___jp_319_:
{
uint8_t v___x_323_; 
v___x_323_ = lean_nat_dec_eq(v_idx_318_, v_idx_321_);
lean_dec(v_idx_321_);
lean_dec(v_idx_318_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; 
lean_dec_ref(v_acc_315_);
lean_inc(v_err_322_);
v___x_324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_324_, 0, v_pos_320_);
lean_ctor_set(v___x_324_, 1, v_err_322_);
return v___x_324_;
}
else
{
lean_object* v___x_325_; 
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v_pos_320_);
lean_ctor_set(v___x_325_, 1, v_acc_315_);
return v___x_325_;
}
}
v___jp_326_:
{
lean_object* v___x_327_; 
v___x_327_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
lean_inc(v_idx_318_);
v_pos_320_ = v_a_316_;
v_idx_321_ = v_idx_318_;
v_err_322_ = v___x_327_;
goto v___jp_319_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(lean_object* v_a_372_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0));
v___x_374_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_spec__0(v___x_373_, v_a_372_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(lean_object* v_a_378_){
_start:
{
lean_object* v_array_379_; lean_object* v_idx_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v_array_379_ = lean_ctor_get(v_a_378_, 0);
v_idx_380_ = lean_ctor_get(v_a_378_, 1);
v___x_381_ = lean_byte_array_size(v_array_379_);
v___x_382_ = lean_nat_dec_lt(v_idx_380_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_box(0);
v___x_384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_384_, 0, v_a_378_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
return v___x_384_;
}
else
{
uint8_t v___x_385_; uint8_t v_got_386_; uint8_t v___x_387_; 
v___x_385_ = 100;
v_got_386_ = lean_byte_array_fget(v_array_379_, v_idx_380_);
v___x_387_ = lean_uint8_dec_eq(v_got_386_, v___x_385_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1));
v___x_389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_389_, 0, v_a_378_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
return v___x_389_;
}
else
{
lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_453_; 
lean_inc(v_idx_380_);
lean_inc_ref(v_array_379_);
v_isSharedCheck_453_ = !lean_is_exclusive(v_a_378_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; lean_object* v_unused_455_; 
v_unused_454_ = lean_ctor_get(v_a_378_, 1);
lean_dec(v_unused_454_);
v_unused_455_ = lean_ctor_get(v_a_378_, 0);
lean_dec(v_unused_455_);
v___x_391_ = v_a_378_;
v_isShared_392_ = v_isSharedCheck_453_;
goto v_resetjp_390_;
}
else
{
lean_dec(v_a_378_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_453_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = lean_nat_add(v_idx_380_, v___x_393_);
lean_dec(v_idx_380_);
lean_inc(v___x_394_);
lean_inc_ref(v_array_379_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 1, v___x_394_);
v___x_396_ = v___x_391_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_array_379_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v___x_394_);
v___x_396_ = v_reuseFailAlloc_452_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
uint8_t v___x_397_; 
v___x_397_ = lean_nat_dec_lt(v___x_394_, v___x_381_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec(v___x_394_);
lean_dec_ref(v_array_379_);
v___x_398_ = lean_box(0);
v___x_399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_396_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
return v___x_399_;
}
else
{
uint8_t v___x_400_; uint8_t v_got_401_; uint8_t v___x_402_; 
v___x_400_ = 32;
v_got_401_ = lean_byte_array_fget(v_array_379_, v___x_394_);
v___x_402_ = lean_uint8_dec_eq(v_got_401_, v___x_400_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec(v___x_394_);
lean_dec_ref(v_array_379_);
v___x_403_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
v___x_404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_396_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
return v___x_404_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec_ref(v___x_396_);
v___x_405_ = lean_nat_add(v___x_394_, v___x_393_);
lean_dec(v___x_394_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v_array_379_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(v___x_406_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_pos_408_; lean_object* v_res_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_442_; 
v_pos_408_ = lean_ctor_get(v___x_407_, 0);
v_res_409_ = lean_ctor_get(v___x_407_, 1);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_442_ == 0)
{
v___x_411_ = v___x_407_;
v_isShared_412_ = v_isSharedCheck_442_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_res_409_);
lean_inc(v_pos_408_);
lean_dec(v___x_407_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_442_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v_array_413_; lean_object* v_idx_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v_array_413_ = lean_ctor_get(v_pos_408_, 0);
v_idx_414_ = lean_ctor_get(v_pos_408_, 1);
v___x_415_ = lean_byte_array_size(v_array_413_);
v___x_416_ = lean_nat_dec_lt(v_idx_414_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_419_; 
lean_dec(v_res_409_);
v___x_417_ = lean_box(0);
if (v_isShared_412_ == 0)
{
lean_ctor_set_tag(v___x_411_, 1);
lean_ctor_set(v___x_411_, 1, v___x_417_);
v___x_419_ = v___x_411_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_pos_408_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
else
{
uint8_t v___x_421_; uint8_t v_got_422_; uint8_t v___x_423_; 
v___x_421_ = 48;
v_got_422_ = lean_byte_array_fget(v_array_413_, v_idx_414_);
v___x_423_ = lean_uint8_dec_eq(v_got_422_, v___x_421_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_426_; 
lean_dec(v_res_409_);
v___x_424_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1));
if (v_isShared_412_ == 0)
{
lean_ctor_set_tag(v___x_411_, 1);
lean_ctor_set(v___x_411_, 1, v___x_424_);
v___x_426_ = v___x_411_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_pos_408_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
else
{
lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_439_; 
lean_inc(v_idx_414_);
lean_inc_ref(v_array_413_);
v_isSharedCheck_439_ = !lean_is_exclusive(v_pos_408_);
if (v_isSharedCheck_439_ == 0)
{
lean_object* v_unused_440_; lean_object* v_unused_441_; 
v_unused_440_ = lean_ctor_get(v_pos_408_, 1);
lean_dec(v_unused_440_);
v_unused_441_ = lean_ctor_get(v_pos_408_, 0);
lean_dec(v_unused_441_);
v___x_429_ = v_pos_408_;
v_isShared_430_ = v_isSharedCheck_439_;
goto v_resetjp_428_;
}
else
{
lean_dec(v_pos_408_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_439_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_431_ = lean_nat_add(v_idx_414_, v___x_393_);
lean_dec(v_idx_414_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v___x_431_);
v___x_433_ = v___x_429_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_array_413_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v___x_431_);
v___x_433_ = v_reuseFailAlloc_438_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_434_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_434_, 0, v_res_409_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 1, v___x_434_);
lean_ctor_set(v___x_411_, 0, v___x_433_);
v___x_436_ = v___x_411_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_443_; lean_object* v_err_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
v_pos_443_ = lean_ctor_get(v___x_407_, 0);
v_err_444_ = lean_ctor_get(v___x_407_, 1);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_407_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_err_444_);
lean_inc(v_pos_443_);
lean_dec(v___x_407_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_pos_443_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_err_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseLit(lean_object* v_a_456_){
_start:
{
lean_object* v_array_460_; lean_object* v_idx_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v_array_460_ = lean_ctor_get(v_a_456_, 0);
v_idx_461_ = lean_ctor_get(v_a_456_, 1);
v___x_462_ = lean_byte_array_size(v_array_460_);
v___x_463_ = lean_nat_dec_lt(v_idx_461_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_box(0);
v___x_465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_465_, 0, v_a_456_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
return v___x_465_;
}
else
{
uint8_t v___x_466_; uint8_t v___x_467_; uint8_t v___x_468_; 
v___x_466_ = lean_byte_array_fget(v_array_460_, v_idx_461_);
v___x_467_ = 45;
v___x_468_ = lean_uint8_dec_eq(v___x_466_, v___x_467_);
if (v___x_468_ == 0)
{
uint8_t v___x_469_; uint8_t v___x_470_; 
v___x_469_ = 48;
v___x_470_ = lean_uint8_dec_le(v___x_469_, v___x_466_);
if (v___x_470_ == 0)
{
goto v___jp_457_;
}
else
{
uint8_t v___x_471_; uint8_t v___x_472_; 
v___x_471_ = 57;
v___x_472_ = lean_uint8_dec_le(v___x_466_, v___x_471_);
if (v___x_472_ == 0)
{
goto v___jp_457_;
}
else
{
lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_502_; 
lean_inc(v_idx_461_);
lean_inc_ref(v_array_460_);
v_isSharedCheck_502_ = !lean_is_exclusive(v_a_456_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; lean_object* v_unused_504_; 
v_unused_503_ = lean_ctor_get(v_a_456_, 1);
lean_dec(v_unused_503_);
v_unused_504_ = lean_ctor_get(v_a_456_, 0);
lean_dec(v_unused_504_);
v___x_474_ = v_a_456_;
v_isShared_475_ = v_isSharedCheck_502_;
goto v_resetjp_473_;
}
else
{
lean_dec(v_a_456_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_502_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v_it_x27_479_; 
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_add(v_idx_461_, v___x_476_);
lean_dec(v_idx_461_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 1, v___x_477_);
v_it_x27_479_ = v___x_474_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_array_460_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v___x_477_);
v_it_x27_479_ = v_reuseFailAlloc_501_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
uint32_t v___x_480_; uint8_t v___x_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v_fst_485_; lean_object* v_snd_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_500_; 
v___x_480_ = lean_uint8_to_uint32(v___x_466_);
v___x_481_ = lean_uint32_to_uint8(v___x_480_);
v___x_482_ = lean_uint8_sub(v___x_481_, v___x_469_);
v___x_483_ = lean_uint8_to_nat(v___x_482_);
v___x_484_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_479_, v___x_483_);
v_fst_485_ = lean_ctor_get(v___x_484_, 0);
v_snd_486_ = lean_ctor_get(v___x_484_, 1);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_500_ == 0)
{
v___x_488_ = v___x_484_;
v_isShared_489_ = v_isSharedCheck_500_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_snd_486_);
lean_inc(v_fst_485_);
lean_dec(v___x_484_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_500_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_unsigned_to_nat(0u);
v___x_491_ = lean_nat_dec_eq(v_fst_485_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_492_ = lean_nat_to_int(v_fst_485_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v___x_492_);
lean_ctor_set(v___x_488_, 0, v_snd_486_);
v___x_494_ = v___x_488_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_snd_486_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
else
{
lean_object* v___x_496_; lean_object* v___x_498_; 
lean_dec(v_fst_485_);
v___x_496_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_489_ == 0)
{
lean_ctor_set_tag(v___x_488_, 1);
lean_ctor_set(v___x_488_, 1, v___x_496_);
lean_ctor_set(v___x_488_, 0, v_snd_486_);
v___x_498_ = v___x_488_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_snd_486_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
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
lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_548_; 
lean_inc(v_idx_461_);
lean_inc_ref(v_array_460_);
v_isSharedCheck_548_ = !lean_is_exclusive(v_a_456_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; lean_object* v_unused_550_; 
v_unused_549_ = lean_ctor_get(v_a_456_, 1);
lean_dec(v_unused_549_);
v_unused_550_ = lean_ctor_get(v_a_456_, 0);
lean_dec(v_unused_550_);
v___x_506_ = v_a_456_;
v_isShared_507_ = v_isSharedCheck_548_;
goto v_resetjp_505_;
}
else
{
lean_dec(v_a_456_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_548_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_508_ = lean_unsigned_to_nat(1u);
v___x_509_ = lean_nat_add(v_idx_461_, v___x_508_);
lean_dec(v_idx_461_);
lean_inc(v___x_509_);
lean_inc_ref(v_array_460_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 1, v___x_509_);
v___x_511_ = v___x_506_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_array_460_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_509_);
v___x_511_ = v_reuseFailAlloc_547_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
uint8_t v___x_515_; 
v___x_515_ = lean_nat_dec_lt(v___x_509_, v___x_462_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec(v___x_509_);
lean_dec_ref(v_array_460_);
v___x_516_ = lean_box(0);
v___x_517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_511_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
return v___x_517_;
}
else
{
uint8_t v_c_518_; uint8_t v___x_519_; uint8_t v___x_520_; 
v_c_518_ = lean_byte_array_fget(v_array_460_, v___x_509_);
v___x_519_ = 48;
v___x_520_ = lean_uint8_dec_le(v___x_519_, v_c_518_);
if (v___x_520_ == 0)
{
lean_dec(v___x_509_);
lean_dec_ref(v_array_460_);
goto v___jp_512_;
}
else
{
uint8_t v___x_521_; uint8_t v___x_522_; 
v___x_521_ = 57;
v___x_522_ = lean_uint8_dec_le(v_c_518_, v___x_521_);
if (v___x_522_ == 0)
{
lean_dec(v___x_509_);
lean_dec_ref(v_array_460_);
goto v___jp_512_;
}
else
{
lean_object* v___x_523_; lean_object* v_it_x27_524_; uint32_t v___x_525_; uint8_t v___x_526_; uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v_fst_530_; lean_object* v_snd_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_546_; 
lean_dec_ref(v___x_511_);
v___x_523_ = lean_nat_add(v___x_509_, v___x_508_);
lean_dec(v___x_509_);
v_it_x27_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_524_, 0, v_array_460_);
lean_ctor_set(v_it_x27_524_, 1, v___x_523_);
v___x_525_ = lean_uint8_to_uint32(v_c_518_);
v___x_526_ = lean_uint32_to_uint8(v___x_525_);
v___x_527_ = lean_uint8_sub(v___x_526_, v___x_519_);
v___x_528_ = lean_uint8_to_nat(v___x_527_);
v___x_529_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_524_, v___x_528_);
v_fst_530_ = lean_ctor_get(v___x_529_, 0);
v_snd_531_ = lean_ctor_get(v___x_529_, 1);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_546_ == 0)
{
v___x_533_ = v___x_529_;
v_isShared_534_ = v_isSharedCheck_546_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_snd_531_);
lean_inc(v_fst_530_);
lean_dec(v___x_529_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_546_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = lean_nat_dec_eq(v_fst_530_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_537_ = lean_nat_to_int(v_fst_530_);
v___x_538_ = lean_int_neg(v___x_537_);
lean_dec(v___x_537_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 1, v___x_538_);
lean_ctor_set(v___x_533_, 0, v_snd_531_);
v___x_540_ = v___x_533_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_snd_531_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
else
{
lean_object* v___x_542_; lean_object* v___x_544_; 
lean_dec(v_fst_530_);
v___x_542_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_534_ == 0)
{
lean_ctor_set_tag(v___x_533_, 1);
lean_ctor_set(v___x_533_, 1, v___x_542_);
lean_ctor_set(v___x_533_, 0, v_snd_531_);
v___x_544_ = v___x_533_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_snd_531_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v___x_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
}
v___jp_512_:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_511_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
return v___x_514_;
}
}
}
}
}
v___jp_457_:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_459_, 0, v_a_456_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
return v___x_459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_litWs(lean_object* v_a_551_){
_start:
{
lean_object* v_pos_553_; lean_object* v_res_554_; lean_object* v_array_584_; lean_object* v_idx_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v_array_584_ = lean_ctor_get(v_a_551_, 0);
v_idx_585_ = lean_ctor_get(v_a_551_, 1);
v___x_586_ = lean_byte_array_size(v_array_584_);
v___x_587_ = lean_nat_dec_lt(v_idx_585_, v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_box(0);
v___x_589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_589_, 0, v_a_551_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
return v___x_589_;
}
else
{
uint8_t v___x_590_; uint8_t v___x_591_; uint8_t v___x_592_; 
v___x_590_ = lean_byte_array_fget(v_array_584_, v_idx_585_);
v___x_591_ = 45;
v___x_592_ = lean_uint8_dec_eq(v___x_590_, v___x_591_);
if (v___x_592_ == 0)
{
uint8_t v___x_593_; uint8_t v___x_594_; 
v___x_593_ = 48;
v___x_594_ = lean_uint8_dec_le(v___x_593_, v___x_590_);
if (v___x_594_ == 0)
{
goto v___jp_578_;
}
else
{
uint8_t v___x_595_; uint8_t v___x_596_; 
v___x_595_ = 57;
v___x_596_ = lean_uint8_dec_le(v___x_590_, v___x_595_);
if (v___x_596_ == 0)
{
goto v___jp_578_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v_it_x27_599_; uint32_t v___x_600_; uint8_t v___x_601_; uint8_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v_fst_605_; lean_object* v_snd_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_617_; 
v___x_597_ = lean_unsigned_to_nat(1u);
v___x_598_ = lean_nat_add(v_idx_585_, v___x_597_);
lean_inc_ref(v_array_584_);
v_it_x27_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_599_, 0, v_array_584_);
lean_ctor_set(v_it_x27_599_, 1, v___x_598_);
v___x_600_ = lean_uint8_to_uint32(v___x_590_);
v___x_601_ = lean_uint32_to_uint8(v___x_600_);
v___x_602_ = lean_uint8_sub(v___x_601_, v___x_593_);
v___x_603_ = lean_uint8_to_nat(v___x_602_);
v___x_604_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_599_, v___x_603_);
v_fst_605_ = lean_ctor_get(v___x_604_, 0);
v_snd_606_ = lean_ctor_get(v___x_604_, 1);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_617_ == 0)
{
v___x_608_ = v___x_604_;
v_isShared_609_ = v_isSharedCheck_617_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_snd_606_);
lean_inc(v_fst_605_);
lean_dec(v___x_604_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_617_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = lean_nat_dec_eq(v_fst_605_, v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
lean_del_object(v___x_608_);
lean_dec_ref(v_a_551_);
v___x_612_ = lean_nat_to_int(v_fst_605_);
v_pos_553_ = v_snd_606_;
v_res_554_ = v___x_612_;
goto v___jp_552_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_615_; 
lean_dec(v_snd_606_);
lean_dec(v_fst_605_);
v___x_613_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_609_ == 0)
{
lean_ctor_set_tag(v___x_608_, 1);
lean_ctor_set(v___x_608_, 1, v___x_613_);
lean_ctor_set(v___x_608_, 0, v_a_551_);
v___x_615_ = v___x_608_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_551_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_618_ = lean_unsigned_to_nat(1u);
v___x_619_ = lean_nat_add(v_idx_585_, v___x_618_);
v___x_620_ = lean_nat_dec_lt(v___x_619_, v___x_586_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec(v___x_619_);
v___x_621_ = lean_box(0);
v___x_622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_622_, 0, v_a_551_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
return v___x_622_;
}
else
{
uint8_t v_c_623_; uint8_t v___x_624_; uint8_t v___x_625_; 
v_c_623_ = lean_byte_array_fget(v_array_584_, v___x_619_);
v___x_624_ = 48;
v___x_625_ = lean_uint8_dec_le(v___x_624_, v_c_623_);
if (v___x_625_ == 0)
{
lean_dec(v___x_619_);
goto v___jp_581_;
}
else
{
uint8_t v___x_626_; uint8_t v___x_627_; 
v___x_626_ = 57;
v___x_627_ = lean_uint8_dec_le(v_c_623_, v___x_626_);
if (v___x_627_ == 0)
{
lean_dec(v___x_619_);
goto v___jp_581_;
}
else
{
lean_object* v___x_628_; lean_object* v_it_x27_629_; uint32_t v___x_630_; uint8_t v___x_631_; uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v_fst_635_; lean_object* v_snd_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_648_; 
v___x_628_ = lean_nat_add(v___x_619_, v___x_618_);
lean_dec(v___x_619_);
lean_inc_ref(v_array_584_);
v_it_x27_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_629_, 0, v_array_584_);
lean_ctor_set(v_it_x27_629_, 1, v___x_628_);
v___x_630_ = lean_uint8_to_uint32(v_c_623_);
v___x_631_ = lean_uint32_to_uint8(v___x_630_);
v___x_632_ = lean_uint8_sub(v___x_631_, v___x_624_);
v___x_633_ = lean_uint8_to_nat(v___x_632_);
v___x_634_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_629_, v___x_633_);
v_fst_635_ = lean_ctor_get(v___x_634_, 0);
v_snd_636_ = lean_ctor_get(v___x_634_, 1);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_648_ == 0)
{
v___x_638_ = v___x_634_;
v_isShared_639_ = v_isSharedCheck_648_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_snd_636_);
lean_inc(v_fst_635_);
lean_dec(v___x_634_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_648_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_nat_dec_eq(v_fst_635_, v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; 
lean_del_object(v___x_638_);
lean_dec_ref(v_a_551_);
v___x_642_ = lean_nat_to_int(v_fst_635_);
v___x_643_ = lean_int_neg(v___x_642_);
lean_dec(v___x_642_);
v_pos_553_ = v_snd_636_;
v_res_554_ = v___x_643_;
goto v___jp_552_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_646_; 
lean_dec(v_snd_636_);
lean_dec(v_fst_635_);
v___x_644_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_639_ == 0)
{
lean_ctor_set_tag(v___x_638_, 1);
lean_ctor_set(v___x_638_, 1, v___x_644_);
lean_ctor_set(v___x_638_, 0, v_a_551_);
v___x_646_ = v___x_638_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_551_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
}
}
}
v___jp_552_:
{
lean_object* v_array_555_; lean_object* v_idx_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_array_555_ = lean_ctor_get(v_pos_553_, 0);
v_idx_556_ = lean_ctor_get(v_pos_553_, 1);
v___x_557_ = lean_byte_array_size(v_array_555_);
v___x_558_ = lean_nat_dec_lt(v_idx_556_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec(v_res_554_);
v___x_559_ = lean_box(0);
v___x_560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_560_, 0, v_pos_553_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
return v___x_560_;
}
else
{
uint8_t v___x_561_; uint8_t v_got_562_; uint8_t v___x_563_; 
v___x_561_ = 32;
v_got_562_ = lean_byte_array_fget(v_array_555_, v_idx_556_);
v___x_563_ = lean_uint8_dec_eq(v_got_562_, v___x_561_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec(v_res_554_);
v___x_564_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
v___x_565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_565_, 0, v_pos_553_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
return v___x_565_;
}
else
{
lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_575_; 
lean_inc(v_idx_556_);
lean_inc_ref(v_array_555_);
v_isSharedCheck_575_ = !lean_is_exclusive(v_pos_553_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; lean_object* v_unused_577_; 
v_unused_576_ = lean_ctor_get(v_pos_553_, 1);
lean_dec(v_unused_576_);
v_unused_577_ = lean_ctor_get(v_pos_553_, 0);
lean_dec(v_unused_577_);
v___x_567_ = v_pos_553_;
v_isShared_568_ = v_isSharedCheck_575_;
goto v_resetjp_566_;
}
else
{
lean_dec(v_pos_553_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_575_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_569_ = lean_unsigned_to_nat(1u);
v___x_570_ = lean_nat_add(v_idx_556_, v___x_569_);
lean_dec(v_idx_556_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v___x_570_);
v___x_572_ = v___x_567_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_array_555_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v___x_570_);
v___x_572_ = v_reuseFailAlloc_574_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_573_; 
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v_res_554_);
return v___x_573_;
}
}
}
}
}
v___jp_578_:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_580_, 0, v_a_551_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
return v___x_580_;
}
v___jp_581_:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_583_, 0, v_a_551_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
return v___x_583_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__0(lean_object* v_a_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = lean_nat_to_int(v_a_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__1(lean_object* v_acc_651_, lean_object* v_a_652_){
_start:
{
lean_object* v_array_653_; lean_object* v_idx_654_; lean_object* v_pos_656_; lean_object* v_idx_657_; lean_object* v_err_658_; lean_object* v_pos_667_; lean_object* v_res_668_; lean_object* v___x_691_; uint8_t v___x_692_; 
v_array_653_ = lean_ctor_get(v_a_652_, 0);
v_idx_654_ = lean_ctor_get(v_a_652_, 1);
lean_inc(v_idx_654_);
v___x_691_ = lean_byte_array_size(v_array_653_);
v___x_692_ = lean_nat_dec_lt(v_idx_654_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
v___x_693_ = lean_box(0);
lean_inc(v_idx_654_);
v_pos_656_ = v_a_652_;
v_idx_657_ = v_idx_654_;
v_err_658_ = v___x_693_;
goto v___jp_655_;
}
else
{
uint8_t v___x_694_; uint8_t v___x_695_; uint8_t v___x_696_; 
v___x_694_ = lean_byte_array_fget(v_array_653_, v_idx_654_);
v___x_695_ = 45;
v___x_696_ = lean_uint8_dec_eq(v___x_694_, v___x_695_);
if (v___x_696_ == 0)
{
uint8_t v___x_697_; uint8_t v___x_698_; 
v___x_697_ = 48;
v___x_698_ = lean_uint8_dec_le(v___x_697_, v___x_694_);
if (v___x_698_ == 0)
{
goto v___jp_664_;
}
else
{
uint8_t v___x_699_; uint8_t v___x_700_; 
v___x_699_ = 57;
v___x_700_ = lean_uint8_dec_le(v___x_694_, v___x_699_);
if (v___x_700_ == 0)
{
goto v___jp_664_;
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v_it_x27_703_; uint32_t v___x_704_; uint8_t v___x_705_; uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v_fst_709_; lean_object* v_snd_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_701_ = lean_unsigned_to_nat(1u);
v___x_702_ = lean_nat_add(v_idx_654_, v___x_701_);
lean_inc_ref(v_array_653_);
v_it_x27_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_703_, 0, v_array_653_);
lean_ctor_set(v_it_x27_703_, 1, v___x_702_);
v___x_704_ = lean_uint8_to_uint32(v___x_694_);
v___x_705_ = lean_uint32_to_uint8(v___x_704_);
v___x_706_ = lean_uint8_sub(v___x_705_, v___x_697_);
v___x_707_ = lean_uint8_to_nat(v___x_706_);
v___x_708_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_703_, v___x_707_);
v_fst_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_fst_709_);
v_snd_710_ = lean_ctor_get(v___x_708_, 1);
lean_inc(v_snd_710_);
lean_dec_ref(v___x_708_);
v___x_711_ = lean_unsigned_to_nat(0u);
v___x_712_ = lean_nat_dec_eq(v_fst_709_, v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
lean_dec_ref(v_a_652_);
v___x_713_ = lean_nat_to_int(v_fst_709_);
v_pos_667_ = v_snd_710_;
v_res_668_ = v___x_713_;
goto v___jp_666_;
}
else
{
lean_object* v___x_714_; 
lean_dec(v_snd_710_);
lean_dec(v_fst_709_);
v___x_714_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
lean_inc(v_idx_654_);
v_pos_656_ = v_a_652_;
v_idx_657_ = v_idx_654_;
v_err_658_ = v___x_714_;
goto v___jp_655_;
}
}
}
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_715_ = lean_unsigned_to_nat(1u);
v___x_716_ = lean_nat_add(v_idx_654_, v___x_715_);
v___x_717_ = lean_nat_dec_lt(v___x_716_, v___x_691_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; 
lean_dec(v___x_716_);
v___x_718_ = lean_box(0);
lean_inc(v_idx_654_);
v_pos_656_ = v_a_652_;
v_idx_657_ = v_idx_654_;
v_err_658_ = v___x_718_;
goto v___jp_655_;
}
else
{
uint8_t v_c_719_; uint8_t v___x_720_; uint8_t v___x_721_; 
v_c_719_ = lean_byte_array_fget(v_array_653_, v___x_716_);
v___x_720_ = 48;
v___x_721_ = lean_uint8_dec_le(v___x_720_, v_c_719_);
if (v___x_721_ == 0)
{
lean_dec(v___x_716_);
goto v___jp_662_;
}
else
{
uint8_t v___x_722_; uint8_t v___x_723_; 
v___x_722_ = 57;
v___x_723_ = lean_uint8_dec_le(v_c_719_, v___x_722_);
if (v___x_723_ == 0)
{
lean_dec(v___x_716_);
goto v___jp_662_;
}
else
{
lean_object* v___x_724_; lean_object* v_it_x27_725_; uint32_t v___x_726_; uint8_t v___x_727_; uint8_t v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v_fst_731_; lean_object* v_snd_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_724_ = lean_nat_add(v___x_716_, v___x_715_);
lean_dec(v___x_716_);
lean_inc_ref(v_array_653_);
v_it_x27_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_725_, 0, v_array_653_);
lean_ctor_set(v_it_x27_725_, 1, v___x_724_);
v___x_726_ = lean_uint8_to_uint32(v_c_719_);
v___x_727_ = lean_uint32_to_uint8(v___x_726_);
v___x_728_ = lean_uint8_sub(v___x_727_, v___x_720_);
v___x_729_ = lean_uint8_to_nat(v___x_728_);
v___x_730_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_725_, v___x_729_);
v_fst_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_fst_731_);
v_snd_732_ = lean_ctor_get(v___x_730_, 1);
lean_inc(v_snd_732_);
lean_dec_ref(v___x_730_);
v___x_733_ = lean_unsigned_to_nat(0u);
v___x_734_ = lean_nat_dec_eq(v_fst_731_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; 
lean_dec_ref(v_a_652_);
v___x_735_ = lean_nat_to_int(v_fst_731_);
v___x_736_ = lean_int_neg(v___x_735_);
lean_dec(v___x_735_);
v_pos_667_ = v_snd_732_;
v_res_668_ = v___x_736_;
goto v___jp_666_;
}
else
{
lean_object* v___x_737_; 
lean_dec(v_snd_732_);
lean_dec(v_fst_731_);
v___x_737_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
lean_inc(v_idx_654_);
v_pos_656_ = v_a_652_;
v_idx_657_ = v_idx_654_;
v_err_658_ = v___x_737_;
goto v___jp_655_;
}
}
}
}
}
}
v___jp_655_:
{
uint8_t v___x_659_; 
v___x_659_ = lean_nat_dec_eq(v_idx_654_, v_idx_657_);
lean_dec(v_idx_657_);
lean_dec(v_idx_654_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
lean_dec_ref(v_acc_651_);
lean_inc(v_err_658_);
v___x_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_660_, 0, v_pos_656_);
lean_ctor_set(v___x_660_, 1, v_err_658_);
return v___x_660_;
}
else
{
lean_object* v___x_661_; 
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v_pos_656_);
lean_ctor_set(v___x_661_, 1, v_acc_651_);
return v___x_661_;
}
}
v___jp_662_:
{
lean_object* v___x_663_; 
v___x_663_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
lean_inc(v_idx_654_);
v_pos_656_ = v_a_652_;
v_idx_657_ = v_idx_654_;
v_err_658_ = v___x_663_;
goto v___jp_655_;
}
v___jp_664_:
{
lean_object* v___x_665_; 
v___x_665_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
lean_inc(v_idx_654_);
v_pos_656_ = v_a_652_;
v_idx_657_ = v_idx_654_;
v_err_658_ = v___x_665_;
goto v___jp_655_;
}
v___jp_666_:
{
lean_object* v_array_669_; lean_object* v_idx_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v_array_669_ = lean_ctor_get(v_pos_667_, 0);
v_idx_670_ = lean_ctor_get(v_pos_667_, 1);
lean_inc(v_idx_670_);
v___x_671_ = lean_byte_array_size(v_array_669_);
v___x_672_ = lean_nat_dec_lt(v_idx_670_, v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
lean_dec(v_res_668_);
v___x_673_ = lean_box(0);
v_pos_656_ = v_pos_667_;
v_idx_657_ = v_idx_670_;
v_err_658_ = v___x_673_;
goto v___jp_655_;
}
else
{
uint8_t v___x_674_; uint8_t v_got_675_; uint8_t v___x_676_; 
v___x_674_ = 32;
v_got_675_ = lean_byte_array_fget(v_array_669_, v_idx_670_);
v___x_676_ = lean_uint8_dec_eq(v_got_675_, v___x_674_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
lean_dec(v_res_668_);
v___x_677_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
v_pos_656_ = v_pos_667_;
v_idx_657_ = v_idx_670_;
v_err_658_ = v___x_677_;
goto v___jp_655_;
}
else
{
lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_688_; 
lean_inc_ref(v_array_669_);
lean_dec(v_idx_654_);
v_isSharedCheck_688_ = !lean_is_exclusive(v_pos_667_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; lean_object* v_unused_690_; 
v_unused_689_ = lean_ctor_get(v_pos_667_, 1);
lean_dec(v_unused_689_);
v_unused_690_ = lean_ctor_get(v_pos_667_, 0);
lean_dec(v_unused_690_);
v___x_679_ = v_pos_667_;
v_isShared_680_ = v_isSharedCheck_688_;
goto v_resetjp_678_;
}
else
{
lean_dec(v_pos_667_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_688_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_681_ = lean_unsigned_to_nat(1u);
v___x_682_ = lean_nat_add(v_idx_670_, v___x_681_);
lean_dec(v_idx_670_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 1, v___x_682_);
v___x_684_ = v___x_679_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_array_669_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v___x_682_);
v___x_684_ = v_reuseFailAlloc_687_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_685_; 
v___x_685_ = lean_array_push(v_acc_651_, v_res_668_);
v_acc_651_ = v___x_685_;
v_a_652_ = v___x_684_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(lean_object* v_a_740_){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0));
v___x_742_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__1(v___x_741_, v_a_740_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_pos_743_; lean_object* v_res_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_777_; 
v_pos_743_ = lean_ctor_get(v___x_742_, 0);
v_res_744_ = lean_ctor_get(v___x_742_, 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_777_ == 0)
{
v___x_746_ = v___x_742_;
v_isShared_747_ = v_isSharedCheck_777_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_res_744_);
lean_inc(v_pos_743_);
lean_dec(v___x_742_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_777_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v_array_748_; lean_object* v_idx_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v_array_748_ = lean_ctor_get(v_pos_743_, 0);
v_idx_749_ = lean_ctor_get(v_pos_743_, 1);
v___x_750_ = lean_byte_array_size(v_array_748_);
v___x_751_ = lean_nat_dec_lt(v_idx_749_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_754_; 
lean_dec(v_res_744_);
v___x_752_ = lean_box(0);
if (v_isShared_747_ == 0)
{
lean_ctor_set_tag(v___x_746_, 1);
lean_ctor_set(v___x_746_, 1, v___x_752_);
v___x_754_ = v___x_746_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_pos_743_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
else
{
uint8_t v___x_756_; uint8_t v_got_757_; uint8_t v___x_758_; 
v___x_756_ = 48;
v_got_757_ = lean_byte_array_fget(v_array_748_, v_idx_749_);
v___x_758_ = lean_uint8_dec_eq(v_got_757_, v___x_756_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_761_; 
lean_dec(v_res_744_);
v___x_759_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1));
if (v_isShared_747_ == 0)
{
lean_ctor_set_tag(v___x_746_, 1);
lean_ctor_set(v___x_746_, 1, v___x_759_);
v___x_761_ = v___x_746_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_pos_743_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
else
{
lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_774_; 
lean_inc(v_idx_749_);
lean_inc_ref(v_array_748_);
v_isSharedCheck_774_ = !lean_is_exclusive(v_pos_743_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; lean_object* v_unused_776_; 
v_unused_775_ = lean_ctor_get(v_pos_743_, 1);
lean_dec(v_unused_775_);
v_unused_776_ = lean_ctor_get(v_pos_743_, 0);
lean_dec(v_unused_776_);
v___x_764_ = v_pos_743_;
v_isShared_765_ = v_isSharedCheck_774_;
goto v_resetjp_763_;
}
else
{
lean_dec(v_pos_743_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_774_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_766_ = lean_unsigned_to_nat(1u);
v___x_767_ = lean_nat_add(v_idx_749_, v___x_766_);
lean_dec(v_idx_749_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 1, v___x_767_);
v___x_769_ = v___x_764_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_array_748_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_767_);
v___x_769_ = v_reuseFailAlloc_773_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_771_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_769_);
v___x_771_ = v___x_746_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_res_744_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
}
}
else
{
return v___x_742_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(lean_object* v_a_778_){
_start:
{
lean_object* v_array_779_; lean_object* v_idx_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v_array_779_ = lean_ctor_get(v_a_778_, 0);
v_idx_780_ = lean_ctor_get(v_a_778_, 1);
v___x_781_ = lean_byte_array_size(v_array_779_);
v___x_782_ = lean_nat_dec_lt(v_idx_780_, v___x_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_box(0);
v___x_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_784_, 0, v_a_778_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
return v___x_784_;
}
else
{
uint8_t v___x_785_; uint8_t v_got_786_; uint8_t v___x_787_; 
v___x_785_ = 45;
v_got_786_ = lean_byte_array_fget(v_array_779_, v_idx_780_);
v___x_787_ = lean_uint8_dec_eq(v_got_786_, v___x_785_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1));
v___x_789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_789_, 0, v_a_778_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
return v___x_789_;
}
else
{
lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_872_; 
lean_inc(v_idx_780_);
lean_inc_ref(v_array_779_);
v_isSharedCheck_872_ = !lean_is_exclusive(v_a_778_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; lean_object* v_unused_874_; 
v_unused_873_ = lean_ctor_get(v_a_778_, 1);
lean_dec(v_unused_873_);
v_unused_874_ = lean_ctor_get(v_a_778_, 0);
lean_dec(v_unused_874_);
v___x_791_ = v_a_778_;
v_isShared_792_ = v_isSharedCheck_872_;
goto v_resetjp_790_;
}
else
{
lean_dec(v_a_778_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_872_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_793_ = lean_unsigned_to_nat(1u);
v___x_794_ = lean_nat_add(v_idx_780_, v___x_793_);
lean_dec(v_idx_780_);
lean_inc(v___x_794_);
lean_inc_ref(v_array_779_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v___x_794_);
v___x_796_ = v___x_791_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_array_779_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v___x_794_);
v___x_796_ = v_reuseFailAlloc_871_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
uint8_t v___x_800_; 
v___x_800_ = lean_nat_dec_lt(v___x_794_, v___x_781_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec(v___x_794_);
lean_dec_ref(v_array_779_);
v___x_801_ = lean_box(0);
v___x_802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_796_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
return v___x_802_;
}
else
{
uint8_t v_c_803_; uint8_t v___x_804_; uint8_t v___x_805_; 
v_c_803_ = lean_byte_array_fget(v_array_779_, v___x_794_);
v___x_804_ = 48;
v___x_805_ = lean_uint8_dec_le(v___x_804_, v_c_803_);
if (v___x_805_ == 0)
{
lean_dec(v___x_794_);
lean_dec_ref(v_array_779_);
goto v___jp_797_;
}
else
{
uint8_t v___x_806_; uint8_t v___x_807_; 
v___x_806_ = 57;
v___x_807_ = lean_uint8_dec_le(v_c_803_, v___x_806_);
if (v___x_807_ == 0)
{
lean_dec(v___x_794_);
lean_dec_ref(v_array_779_);
goto v___jp_797_;
}
else
{
lean_object* v___x_808_; lean_object* v_it_x27_809_; uint32_t v___x_810_; uint8_t v___x_811_; uint8_t v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v_fst_815_; lean_object* v_snd_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_870_; 
lean_dec_ref(v___x_796_);
v___x_808_ = lean_nat_add(v___x_794_, v___x_793_);
lean_dec(v___x_794_);
v_it_x27_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_809_, 0, v_array_779_);
lean_ctor_set(v_it_x27_809_, 1, v___x_808_);
v___x_810_ = lean_uint8_to_uint32(v_c_803_);
v___x_811_ = lean_uint32_to_uint8(v___x_810_);
v___x_812_ = lean_uint8_sub(v___x_811_, v___x_804_);
v___x_813_ = lean_uint8_to_nat(v___x_812_);
v___x_814_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_809_, v___x_813_);
v_fst_815_ = lean_ctor_get(v___x_814_, 0);
v_snd_816_ = lean_ctor_get(v___x_814_, 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_870_ == 0)
{
v___x_818_ = v___x_814_;
v_isShared_819_ = v_isSharedCheck_870_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_snd_816_);
lean_inc(v_fst_815_);
lean_dec(v___x_814_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_870_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_820_ = lean_unsigned_to_nat(0u);
v___x_821_ = lean_nat_dec_eq(v_fst_815_, v___x_820_);
if (v___x_821_ == 0)
{
lean_object* v_array_822_; lean_object* v_idx_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v_array_822_ = lean_ctor_get(v_snd_816_, 0);
v_idx_823_ = lean_ctor_get(v_snd_816_, 1);
v___x_824_ = lean_byte_array_size(v_array_822_);
v___x_825_ = lean_nat_dec_lt(v_idx_823_, v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; 
lean_del_object(v___x_818_);
lean_dec(v_fst_815_);
v___x_826_ = lean_box(0);
v___x_827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_827_, 0, v_snd_816_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
return v___x_827_;
}
else
{
uint8_t v___x_828_; uint8_t v_got_829_; uint8_t v___x_830_; 
v___x_828_ = 32;
v_got_829_ = lean_byte_array_fget(v_array_822_, v_idx_823_);
v___x_830_ = lean_uint8_dec_eq(v_got_829_, v___x_828_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; 
lean_del_object(v___x_818_);
lean_dec(v_fst_815_);
v___x_831_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
v___x_832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_832_, 0, v_snd_816_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
return v___x_832_;
}
else
{
lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_865_; 
lean_inc(v_idx_823_);
lean_inc_ref(v_array_822_);
v_isSharedCheck_865_ = !lean_is_exclusive(v_snd_816_);
if (v_isSharedCheck_865_ == 0)
{
lean_object* v_unused_866_; lean_object* v_unused_867_; 
v_unused_866_ = lean_ctor_get(v_snd_816_, 1);
lean_dec(v_unused_866_);
v_unused_867_ = lean_ctor_get(v_snd_816_, 0);
lean_dec(v_unused_867_);
v___x_834_ = v_snd_816_;
v_isShared_835_ = v_isSharedCheck_865_;
goto v_resetjp_833_;
}
else
{
lean_dec(v_snd_816_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_865_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = lean_nat_add(v_idx_823_, v___x_793_);
lean_dec(v_idx_823_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 1, v___x_836_);
v___x_838_ = v___x_834_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_array_822_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v___x_836_);
v___x_838_ = v_reuseFailAlloc_864_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_839_; 
v___x_839_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(v___x_838_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_pos_840_; lean_object* v_res_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_854_; 
v_pos_840_ = lean_ctor_get(v___x_839_, 0);
v_res_841_ = lean_ctor_get(v___x_839_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_854_ == 0)
{
v___x_843_ = v___x_839_;
v_isShared_844_ = v_isSharedCheck_854_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_res_841_);
lean_inc(v_pos_840_);
lean_dec(v___x_839_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_854_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_845_ = lean_nat_to_int(v_fst_815_);
v___x_846_ = lean_int_neg(v___x_845_);
lean_dec(v___x_845_);
v___x_847_ = lean_nat_abs(v___x_846_);
lean_dec(v___x_846_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 1, v_res_841_);
lean_ctor_set(v___x_818_, 0, v___x_847_);
v___x_849_ = v___x_818_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_res_841_);
v___x_849_ = v_reuseFailAlloc_853_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_851_; 
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 1, v___x_849_);
v___x_851_ = v___x_843_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_pos_840_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v___x_849_);
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
else
{
lean_object* v_pos_855_; lean_object* v_err_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_del_object(v___x_818_);
lean_dec(v_fst_815_);
v_pos_855_ = lean_ctor_get(v___x_839_, 0);
v_err_856_ = lean_ctor_get(v___x_839_, 1);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_839_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_err_856_);
lean_inc(v_pos_855_);
lean_dec(v___x_839_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_pos_855_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_err_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
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
lean_object* v___x_868_; lean_object* v___x_869_; 
lean_del_object(v___x_818_);
lean_dec(v_fst_815_);
v___x_868_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
v___x_869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_869_, 0, v_snd_816_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
return v___x_869_;
}
}
}
}
}
v___jp_797_:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_796_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
return v___x_799_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(lean_object* v_acc_875_, lean_object* v_a_876_){
_start:
{
lean_object* v___x_877_; 
lean_inc_ref(v_a_876_);
v___x_877_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(v_a_876_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_pos_878_; lean_object* v_res_879_; lean_object* v___x_880_; 
lean_dec_ref(v_a_876_);
v_pos_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_pos_878_);
v_res_879_ = lean_ctor_get(v___x_877_, 1);
lean_inc(v_res_879_);
lean_dec_ref_known(v___x_877_, 2);
v___x_880_ = lean_array_push(v_acc_875_, v_res_879_);
v_acc_875_ = v___x_880_;
v_a_876_ = v_pos_878_;
goto _start;
}
else
{
lean_object* v_err_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_894_; 
v_err_882_ = lean_ctor_get(v___x_877_, 1);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v___x_877_, 0);
lean_dec(v_unused_895_);
v___x_884_ = v___x_877_;
v_isShared_885_ = v_isSharedCheck_894_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_err_882_);
lean_dec(v___x_877_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_894_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_idx_886_; uint8_t v___x_887_; 
v_idx_886_ = lean_ctor_get(v_a_876_, 1);
v___x_887_ = lean_nat_dec_eq(v_idx_886_, v_idx_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_889_; 
lean_dec_ref(v_acc_875_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v_a_876_);
v___x_889_ = v___x_884_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_876_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_err_882_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
else
{
lean_object* v___x_892_; 
lean_dec(v_err_882_);
if (v_isShared_885_ == 0)
{
lean_ctor_set_tag(v___x_884_, 0);
lean_ctor_set(v___x_884_, 1, v_acc_875_);
lean_ctor_set(v___x_884_, 0, v_a_876_);
v___x_892_ = v___x_884_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_876_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_acc_875_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(lean_object* v_ident_901_, lean_object* v_a_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(v_a_902_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_pos_904_; lean_object* v_res_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_1020_; 
v_pos_904_ = lean_ctor_get(v___x_903_, 0);
v_res_905_ = lean_ctor_get(v___x_903_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_907_ = v___x_903_;
v_isShared_908_ = v_isSharedCheck_1020_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_res_905_);
lean_inc(v_pos_904_);
lean_dec(v___x_903_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_1020_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v_array_909_; lean_object* v_idx_910_; lean_object* v___x_911_; uint8_t v___x_912_; 
v_array_909_ = lean_ctor_get(v_pos_904_, 0);
v_idx_910_ = lean_ctor_get(v_pos_904_, 1);
v___x_911_ = lean_byte_array_size(v_array_909_);
v___x_912_ = lean_nat_dec_lt(v_idx_910_, v___x_911_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; lean_object* v___x_915_; 
lean_dec(v_res_905_);
lean_dec(v_ident_901_);
v___x_913_ = lean_box(0);
if (v_isShared_908_ == 0)
{
lean_ctor_set_tag(v___x_907_, 1);
lean_ctor_set(v___x_907_, 1, v___x_913_);
v___x_915_ = v___x_907_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_pos_904_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v___x_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
else
{
uint8_t v___x_917_; uint8_t v_got_918_; uint8_t v___x_919_; 
v___x_917_ = 32;
v_got_918_ = lean_byte_array_fget(v_array_909_, v_idx_910_);
v___x_919_ = lean_uint8_dec_eq(v_got_918_, v___x_917_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_922_; 
lean_dec(v_res_905_);
lean_dec(v_ident_901_);
v___x_920_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
if (v_isShared_908_ == 0)
{
lean_ctor_set_tag(v___x_907_, 1);
lean_ctor_set(v___x_907_, 1, v___x_920_);
v___x_922_ = v___x_907_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_pos_904_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
else
{
lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_1017_; 
lean_inc(v_idx_910_);
lean_inc_ref(v_array_909_);
lean_del_object(v___x_907_);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_pos_904_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; lean_object* v_unused_1019_; 
v_unused_1018_ = lean_ctor_get(v_pos_904_, 1);
lean_dec(v_unused_1018_);
v_unused_1019_ = lean_ctor_get(v_pos_904_, 0);
lean_dec(v_unused_1019_);
v___x_925_ = v_pos_904_;
v_isShared_926_ = v_isSharedCheck_1017_;
goto v_resetjp_924_;
}
else
{
lean_dec(v_pos_904_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_1017_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_927_ = lean_unsigned_to_nat(1u);
v___x_928_ = lean_nat_add(v_idx_910_, v___x_927_);
lean_dec(v_idx_910_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 1, v___x_928_);
v___x_930_ = v___x_925_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_array_909_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v___x_928_);
v___x_930_ = v_reuseFailAlloc_1016_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_object* v___x_931_; 
v___x_931_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(v___x_930_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_pos_932_; lean_object* v_res_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_pos_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_pos_932_);
v_res_933_ = lean_ctor_get(v___x_931_, 1);
lean_inc(v_res_933_);
lean_dec_ref_known(v___x_931_, 2);
v___x_934_ = lean_unsigned_to_nat(0u);
v___x_935_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0));
v___x_936_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(v___x_935_, v_pos_932_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_pos_937_; lean_object* v_res_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_997_; 
v_pos_937_ = lean_ctor_get(v___x_936_, 0);
v_res_938_ = lean_ctor_get(v___x_936_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_997_ == 0)
{
v___x_940_ = v___x_936_;
v_isShared_941_ = v_isSharedCheck_997_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_res_938_);
lean_inc(v_pos_937_);
lean_dec(v___x_936_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_997_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v_array_942_; lean_object* v_idx_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v_array_942_ = lean_ctor_get(v_pos_937_, 0);
v_idx_943_ = lean_ctor_get(v_pos_937_, 1);
v___x_944_ = lean_byte_array_size(v_array_942_);
v___x_945_ = lean_nat_dec_lt(v_idx_943_, v___x_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_948_; 
lean_dec(v_res_938_);
lean_dec(v_res_933_);
lean_dec(v_res_905_);
lean_dec(v_ident_901_);
v___x_946_ = lean_box(0);
if (v_isShared_941_ == 0)
{
lean_ctor_set_tag(v___x_940_, 1);
lean_ctor_set(v___x_940_, 1, v___x_946_);
v___x_948_ = v___x_940_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_pos_937_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
else
{
uint8_t v___x_950_; uint8_t v_got_951_; uint8_t v___x_952_; 
v___x_950_ = 48;
v_got_951_ = lean_byte_array_fget(v_array_942_, v_idx_943_);
v___x_952_ = lean_uint8_dec_eq(v_got_951_, v___x_950_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; lean_object* v___x_955_; 
lean_dec(v_res_938_);
lean_dec(v_res_933_);
lean_dec(v_res_905_);
lean_dec(v_ident_901_);
v___x_953_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1));
if (v_isShared_941_ == 0)
{
lean_ctor_set_tag(v___x_940_, 1);
lean_ctor_set(v___x_940_, 1, v___x_953_);
v___x_955_ = v___x_940_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_pos_937_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v___x_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
else
{
lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_994_; 
lean_inc(v_idx_943_);
lean_inc_ref(v_array_942_);
v_isSharedCheck_994_ = !lean_is_exclusive(v_pos_937_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; lean_object* v_unused_996_; 
v_unused_995_ = lean_ctor_get(v_pos_937_, 1);
lean_dec(v_unused_995_);
v_unused_996_ = lean_ctor_get(v_pos_937_, 0);
lean_dec(v_unused_996_);
v___x_958_ = v_pos_937_;
v_isShared_959_ = v_isSharedCheck_994_;
goto v_resetjp_957_;
}
else
{
lean_dec(v_pos_937_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_994_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_960_ = lean_nat_add(v_idx_943_, v___x_927_);
lean_dec(v_idx_943_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 1, v___x_960_);
v___x_962_ = v___x_958_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_array_942_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v___x_960_);
v___x_962_ = v_reuseFailAlloc_993_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = lean_array_get_size(v_res_905_);
v___x_964_ = lean_nat_dec_eq(v___x_963_, v___x_934_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_965_ = lean_array_get_size(v_res_938_);
v___x_966_ = lean_nat_dec_eq(v___x_965_, v___x_934_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_967_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_905_);
v___x_968_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_968_, 0, v_ident_901_);
lean_ctor_set(v___x_968_, 1, v_res_905_);
lean_ctor_set(v___x_968_, 2, v___x_967_);
lean_ctor_set(v___x_968_, 3, v_res_933_);
lean_ctor_set(v___x_968_, 4, v_res_938_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_968_);
lean_ctor_set(v___x_940_, 0, v___x_962_);
v___x_970_ = v___x_940_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
else
{
lean_object* v___x_972_; uint8_t v___x_973_; 
lean_dec(v_res_938_);
v___x_972_ = lean_array_get_size(v_res_933_);
v___x_973_ = lean_nat_dec_eq(v___x_972_, v___x_934_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_974_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_974_, 0, v_ident_901_);
lean_ctor_set(v___x_974_, 1, v_res_905_);
lean_ctor_set(v___x_974_, 2, v_res_933_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_974_);
lean_ctor_set(v___x_940_, 0, v___x_962_);
v___x_976_ = v___x_940_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
else
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
lean_dec(v_res_933_);
v___x_978_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_905_);
v___x_979_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_979_, 0, v_ident_901_);
lean_ctor_set(v___x_979_, 1, v_res_905_);
lean_ctor_set(v___x_979_, 2, v___x_978_);
lean_ctor_set(v___x_979_, 3, v___x_935_);
lean_ctor_set(v___x_979_, 4, v___x_935_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_979_);
lean_ctor_set(v___x_940_, 0, v___x_962_);
v___x_981_ = v___x_940_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
else
{
lean_object* v___x_983_; uint8_t v___x_984_; 
lean_dec(v_res_905_);
v___x_983_ = lean_array_get_size(v_res_938_);
lean_dec(v_res_938_);
v___x_984_ = lean_nat_dec_eq(v___x_983_, v___x_934_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v___x_987_; 
lean_dec(v_res_933_);
lean_dec(v_ident_901_);
v___x_985_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2));
if (v_isShared_941_ == 0)
{
lean_ctor_set_tag(v___x_940_, 1);
lean_ctor_set(v___x_940_, 1, v___x_985_);
lean_ctor_set(v___x_940_, 0, v___x_962_);
v___x_987_ = v___x_940_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
else
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_989_, 0, v_ident_901_);
lean_ctor_set(v___x_989_, 1, v_res_933_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_989_);
lean_ctor_set(v___x_940_, 0, v___x_962_);
v___x_991_ = v___x_940_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
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
lean_object* v_pos_998_; lean_object* v_err_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec(v_res_933_);
lean_dec(v_res_905_);
lean_dec(v_ident_901_);
v_pos_998_ = lean_ctor_get(v___x_936_, 0);
v_err_999_ = lean_ctor_get(v___x_936_, 1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_936_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_err_999_);
lean_inc(v_pos_998_);
lean_dec(v___x_936_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_pos_998_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_err_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
else
{
lean_object* v_pos_1007_; lean_object* v_err_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec(v_res_905_);
lean_dec(v_ident_901_);
v_pos_1007_ = lean_ctor_get(v___x_931_, 0);
v_err_1008_ = lean_ctor_get(v___x_931_, 1);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_931_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_err_1008_);
lean_inc(v_pos_1007_);
lean_dec(v___x_931_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_pos_1007_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_err_1008_);
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
}
}
}
}
}
else
{
lean_object* v_pos_1021_; lean_object* v_err_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v_ident_901_);
v_pos_1021_ = lean_ctor_get(v___x_903_, 0);
v_err_1022_ = lean_ctor_get(v___x_903_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_903_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_err_1022_);
lean_inc(v_pos_1021_);
lean_dec(v___x_903_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_pos_1021_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_err_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(lean_object* v_a_1030_){
_start:
{
lean_object* v_array_1034_; lean_object* v_idx_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v_array_1034_ = lean_ctor_get(v_a_1030_, 0);
v_idx_1035_ = lean_ctor_get(v_a_1030_, 1);
v___x_1036_ = lean_byte_array_size(v_array_1034_);
v___x_1037_ = lean_nat_dec_lt(v_idx_1035_, v___x_1036_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_box(0);
v___x_1039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1039_, 0, v_a_1030_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
return v___x_1039_;
}
else
{
uint8_t v_c_1040_; uint8_t v___x_1041_; uint8_t v___x_1042_; 
v_c_1040_ = lean_byte_array_fget(v_array_1034_, v_idx_1035_);
v___x_1041_ = 48;
v___x_1042_ = lean_uint8_dec_le(v___x_1041_, v_c_1040_);
if (v___x_1042_ == 0)
{
goto v___jp_1031_;
}
else
{
uint8_t v___x_1043_; uint8_t v___x_1044_; 
v___x_1043_ = 57;
v___x_1044_ = lean_uint8_dec_le(v_c_1040_, v___x_1043_);
if (v___x_1044_ == 0)
{
goto v___jp_1031_;
}
else
{
lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1105_; 
lean_inc(v_idx_1035_);
lean_inc_ref(v_array_1034_);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_a_1030_);
if (v_isSharedCheck_1105_ == 0)
{
lean_object* v_unused_1106_; lean_object* v_unused_1107_; 
v_unused_1106_ = lean_ctor_get(v_a_1030_, 1);
lean_dec(v_unused_1106_);
v_unused_1107_ = lean_ctor_get(v_a_1030_, 0);
lean_dec(v_unused_1107_);
v___x_1046_ = v_a_1030_;
v_isShared_1047_ = v_isSharedCheck_1105_;
goto v_resetjp_1045_;
}
else
{
lean_dec(v_a_1030_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1105_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v_it_x27_1051_; 
v___x_1048_ = lean_unsigned_to_nat(1u);
v___x_1049_ = lean_nat_add(v_idx_1035_, v___x_1048_);
lean_dec(v_idx_1035_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 1, v___x_1049_);
v_it_x27_1051_ = v___x_1046_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_array_1034_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v___x_1049_);
v_it_x27_1051_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
uint32_t v___x_1052_; uint8_t v___x_1053_; uint8_t v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v_fst_1057_; lean_object* v_snd_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1103_; 
v___x_1052_ = lean_uint8_to_uint32(v_c_1040_);
v___x_1053_ = lean_uint32_to_uint8(v___x_1052_);
v___x_1054_ = lean_uint8_sub(v___x_1053_, v___x_1041_);
v___x_1055_ = lean_uint8_to_nat(v___x_1054_);
v___x_1056_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_1051_, v___x_1055_);
v_fst_1057_ = lean_ctor_get(v___x_1056_, 0);
v_snd_1058_ = lean_ctor_get(v___x_1056_, 1);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1060_ = v___x_1056_;
v_isShared_1061_ = v_isSharedCheck_1103_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_snd_1058_);
lean_inc(v_fst_1057_);
lean_dec(v___x_1056_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1103_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = lean_unsigned_to_nat(0u);
v___x_1063_ = lean_nat_dec_eq(v_fst_1057_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v_array_1064_; lean_object* v_idx_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v_array_1064_ = lean_ctor_get(v_snd_1058_, 0);
v_idx_1065_ = lean_ctor_get(v_snd_1058_, 1);
v___x_1066_ = lean_byte_array_size(v_array_1064_);
v___x_1067_ = lean_nat_dec_lt(v_idx_1065_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
lean_dec(v_fst_1057_);
v___x_1068_ = lean_box(0);
if (v_isShared_1061_ == 0)
{
lean_ctor_set_tag(v___x_1060_, 1);
lean_ctor_set(v___x_1060_, 1, v___x_1068_);
lean_ctor_set(v___x_1060_, 0, v_snd_1058_);
v___x_1070_ = v___x_1060_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_snd_1058_);
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
uint8_t v___x_1072_; uint8_t v_got_1073_; uint8_t v___x_1074_; 
v___x_1072_ = 32;
v_got_1073_ = lean_byte_array_fget(v_array_1064_, v_idx_1065_);
v___x_1074_ = lean_uint8_dec_eq(v_got_1073_, v___x_1072_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1077_; 
lean_dec(v_fst_1057_);
v___x_1075_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
if (v_isShared_1061_ == 0)
{
lean_ctor_set_tag(v___x_1060_, 1);
lean_ctor_set(v___x_1060_, 1, v___x_1075_);
lean_ctor_set(v___x_1060_, 0, v_snd_1058_);
v___x_1077_ = v___x_1060_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_snd_1058_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
else
{
lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1096_; 
lean_inc(v_idx_1065_);
lean_inc_ref(v_array_1064_);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_snd_1058_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; lean_object* v_unused_1098_; 
v_unused_1097_ = lean_ctor_get(v_snd_1058_, 1);
lean_dec(v_unused_1097_);
v_unused_1098_ = lean_ctor_get(v_snd_1058_, 0);
lean_dec(v_unused_1098_);
v___x_1080_ = v_snd_1058_;
v_isShared_1081_ = v_isSharedCheck_1096_;
goto v_resetjp_1079_;
}
else
{
lean_dec(v_snd_1058_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1096_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1082_ = lean_nat_add(v_idx_1065_, v___x_1048_);
lean_dec(v_idx_1065_);
lean_inc(v___x_1082_);
lean_inc_ref(v_array_1064_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v___x_1082_);
v___x_1084_ = v___x_1080_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_array_1064_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
uint8_t v___x_1085_; 
v___x_1085_ = lean_nat_dec_lt(v___x_1082_, v___x_1066_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
lean_dec(v___x_1082_);
lean_dec_ref(v_array_1064_);
lean_dec(v_fst_1057_);
v___x_1086_ = lean_box(0);
if (v_isShared_1061_ == 0)
{
lean_ctor_set_tag(v___x_1060_, 1);
lean_ctor_set(v___x_1060_, 1, v___x_1086_);
lean_ctor_set(v___x_1060_, 0, v___x_1084_);
v___x_1088_ = v___x_1060_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
else
{
uint8_t v___x_1090_; uint8_t v___x_1091_; uint8_t v___x_1092_; 
lean_del_object(v___x_1060_);
v___x_1090_ = lean_byte_array_fget(v_array_1064_, v___x_1082_);
lean_dec(v___x_1082_);
lean_dec_ref(v_array_1064_);
v___x_1091_ = 100;
v___x_1092_ = lean_uint8_dec_eq(v___x_1090_, v___x_1091_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(v_fst_1057_, v___x_1084_);
return v___x_1093_;
}
else
{
lean_object* v___x_1094_; 
lean_dec(v_fst_1057_);
v___x_1094_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(v___x_1084_);
return v___x_1094_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1101_; 
lean_dec(v_fst_1057_);
v___x_1099_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_1061_ == 0)
{
lean_ctor_set_tag(v___x_1060_, 1);
lean_ctor_set(v___x_1060_, 1, v___x_1099_);
lean_ctor_set(v___x_1060_, 0, v_snd_1058_);
v___x_1101_ = v___x_1060_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_snd_1058_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
}
}
}
v___jp_1031_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_1033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1033_, 0, v_a_1030_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
return v___x_1033_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(lean_object* v_acc_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_array_1113_; lean_object* v_idx_1114_; lean_object* v_pos_1116_; lean_object* v_idx_1117_; lean_object* v_err_1118_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v_array_1113_ = lean_ctor_get(v_a_1112_, 0);
v_idx_1114_ = lean_ctor_get(v_a_1112_, 1);
lean_inc(v_idx_1114_);
v___x_1124_ = lean_byte_array_size(v_array_1113_);
v___x_1125_ = lean_nat_dec_lt(v_idx_1114_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_box(0);
lean_inc(v_idx_1114_);
v_pos_1116_ = v_a_1112_;
v_idx_1117_ = v_idx_1114_;
v_err_1118_ = v___x_1126_;
goto v___jp_1115_;
}
else
{
uint8_t v_c_1127_; uint8_t v___x_1128_; uint8_t v___x_1129_; 
v_c_1127_ = lean_byte_array_fget(v_array_1113_, v_idx_1114_);
v___x_1128_ = 10;
v___x_1129_ = lean_uint8_dec_eq(v_c_1127_, v___x_1128_);
if (v___x_1129_ == 0)
{
uint8_t v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = 13;
v___x_1131_ = lean_uint8_dec_eq(v_c_1127_, v___x_1130_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1143_; 
lean_inc_ref(v_array_1113_);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_a_1112_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; lean_object* v_unused_1145_; 
v_unused_1144_ = lean_ctor_get(v_a_1112_, 1);
lean_dec(v_unused_1144_);
v_unused_1145_ = lean_ctor_get(v_a_1112_, 0);
lean_dec(v_unused_1145_);
v___x_1133_ = v_a_1112_;
v_isShared_1134_ = v_isSharedCheck_1143_;
goto v_resetjp_1132_;
}
else
{
lean_dec(v_a_1112_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1143_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v_it_x27_1138_; 
v___x_1135_ = lean_unsigned_to_nat(1u);
v___x_1136_ = lean_nat_add(v_idx_1114_, v___x_1135_);
lean_dec(v_idx_1114_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 1, v___x_1136_);
v_it_x27_1138_ = v___x_1133_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_array_1113_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v___x_1136_);
v_it_x27_1138_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_box(v_c_1127_);
v___x_1140_ = lean_array_push(v_acc_1111_, v___x_1139_);
v_acc_1111_ = v___x_1140_;
v_a_1112_ = v_it_x27_1138_;
goto _start;
}
}
}
else
{
goto v___jp_1122_;
}
}
else
{
goto v___jp_1122_;
}
}
v___jp_1115_:
{
uint8_t v___x_1119_; 
v___x_1119_ = lean_nat_dec_eq(v_idx_1114_, v_idx_1117_);
lean_dec(v_idx_1117_);
lean_dec(v_idx_1114_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; 
lean_dec_ref(v_acc_1111_);
lean_inc(v_err_1118_);
v___x_1120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1120_, 0, v_pos_1116_);
lean_ctor_set(v___x_1120_, 1, v_err_1118_);
return v___x_1120_;
}
else
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v_pos_1116_);
lean_ctor_set(v___x_1121_, 1, v_acc_1111_);
return v___x_1121_;
}
}
v___jp_1122_:
{
lean_object* v___x_1123_; 
v___x_1123_ = ((lean_object*)(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__1));
lean_inc(v_idx_1114_);
v_pos_1116_ = v_a_1112_;
v_idx_1117_ = v_idx_1114_;
v_err_1118_ = v___x_1123_;
goto v___jp_1115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(lean_object* v_actions_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v_pos_1151_; lean_object* v_array_1152_; lean_object* v_idx_1153_; lean_object* v_pos_1159_; lean_object* v_array_1162_; lean_object* v_idx_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v_array_1162_ = lean_ctor_get(v_a_1149_, 0);
v_idx_1163_ = lean_ctor_get(v_a_1149_, 1);
v___x_1164_ = lean_byte_array_size(v_array_1162_);
v___x_1165_ = lean_nat_dec_lt(v_idx_1163_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
lean_dec_ref(v_actions_1148_);
v___x_1166_ = lean_box(0);
v___x_1167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1167_, 0, v_a_1149_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
return v___x_1167_;
}
else
{
uint8_t v___x_1168_; uint8_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1168_ = lean_byte_array_fget(v_array_1162_, v_idx_1163_);
v___x_1169_ = 99;
v___x_1170_ = lean_uint8_dec_eq(v___x_1168_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(v_a_1149_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_pos_1172_; lean_object* v_res_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1241_; 
v_pos_1172_ = lean_ctor_get(v___x_1171_, 0);
v_res_1173_ = lean_ctor_get(v___x_1171_, 1);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1175_ = v___x_1171_;
v_isShared_1176_ = v_isSharedCheck_1241_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_res_1173_);
lean_inc(v_pos_1172_);
lean_dec(v___x_1171_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1241_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v_pos_1178_; lean_object* v_array_1179_; lean_object* v_idx_1180_; lean_object* v_pos_1189_; lean_object* v_array_1192_; lean_object* v_idx_1193_; lean_object* v___y_1195_; lean_object* v_pos_1196_; lean_object* v_idx_1197_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v_array_1192_ = lean_ctor_get(v_pos_1172_, 0);
v_idx_1193_ = lean_ctor_get(v_pos_1172_, 1);
lean_inc(v_idx_1193_);
v___x_1221_ = lean_byte_array_size(v_array_1192_);
v___x_1222_ = lean_nat_dec_lt(v_idx_1193_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_box(0);
lean_inc(v_pos_1172_);
v___x_1224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1224_, 0, v_pos_1172_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
lean_inc(v_idx_1193_);
v___y_1195_ = v___x_1224_;
v_pos_1196_ = v_pos_1172_;
v_idx_1197_ = v_idx_1193_;
goto v___jp_1194_;
}
else
{
uint8_t v___x_1225_; uint8_t v_got_1226_; uint8_t v___x_1227_; 
v___x_1225_ = 10;
v_got_1226_ = lean_byte_array_fget(v_array_1192_, v_idx_1193_);
v___x_1227_ = lean_uint8_dec_eq(v_got_1226_, v___x_1225_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
lean_inc(v_pos_1172_);
v___x_1229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1229_, 0, v_pos_1172_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
lean_inc(v_idx_1193_);
v___y_1195_ = v___x_1229_;
v_pos_1196_ = v_pos_1172_;
v_idx_1197_ = v_idx_1193_;
goto v___jp_1194_;
}
else
{
lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1238_; 
lean_inc_ref(v_array_1192_);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_pos_1172_);
if (v_isSharedCheck_1238_ == 0)
{
lean_object* v_unused_1239_; lean_object* v_unused_1240_; 
v_unused_1239_ = lean_ctor_get(v_pos_1172_, 1);
lean_dec(v_unused_1239_);
v_unused_1240_ = lean_ctor_get(v_pos_1172_, 0);
lean_dec(v_unused_1240_);
v___x_1231_ = v_pos_1172_;
v_isShared_1232_ = v_isSharedCheck_1238_;
goto v_resetjp_1230_;
}
else
{
lean_dec(v_pos_1172_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1238_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1233_ = lean_unsigned_to_nat(1u);
v___x_1234_ = lean_nat_add(v_idx_1193_, v___x_1233_);
lean_dec(v_idx_1193_);
lean_inc(v___x_1234_);
lean_inc_ref(v_array_1192_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1234_);
v___x_1236_ = v___x_1231_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_array_1192_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
v_pos_1178_ = v___x_1236_;
v_array_1179_ = v_array_1192_;
v_idx_1180_ = v___x_1234_;
goto v___jp_1177_;
}
}
}
}
v___jp_1177_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1181_ = lean_array_push(v_actions_1148_, v_res_1173_);
v___x_1182_ = lean_byte_array_size(v_array_1179_);
lean_dec_ref(v_array_1179_);
v___x_1183_ = lean_nat_dec_lt(v_idx_1180_, v___x_1182_);
lean_dec(v_idx_1180_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1185_; 
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v___x_1181_);
lean_ctor_set(v___x_1175_, 0, v_pos_1178_);
v___x_1185_ = v___x_1175_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_pos_1178_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v___x_1181_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
else
{
lean_del_object(v___x_1175_);
v_actions_1148_ = v___x_1181_;
v_a_1149_ = v_pos_1178_;
goto _start;
}
}
v___jp_1188_:
{
lean_object* v_array_1190_; lean_object* v_idx_1191_; 
v_array_1190_ = lean_ctor_get(v_pos_1189_, 0);
lean_inc_ref(v_array_1190_);
v_idx_1191_ = lean_ctor_get(v_pos_1189_, 1);
lean_inc(v_idx_1191_);
v_pos_1178_ = v_pos_1189_;
v_array_1179_ = v_array_1190_;
v_idx_1180_ = v_idx_1191_;
goto v___jp_1177_;
}
v___jp_1194_:
{
uint8_t v___x_1198_; 
v___x_1198_ = lean_nat_dec_eq(v_idx_1193_, v_idx_1197_);
lean_dec(v_idx_1197_);
lean_dec(v_idx_1193_);
if (v___x_1198_ == 0)
{
lean_dec_ref(v_pos_1196_);
if (lean_obj_tag(v___y_1195_) == 0)
{
lean_object* v_pos_1199_; 
v_pos_1199_ = lean_ctor_get(v___y_1195_, 0);
lean_inc(v_pos_1199_);
lean_dec_ref_known(v___y_1195_, 2);
v_pos_1189_ = v_pos_1199_;
goto v___jp_1188_;
}
else
{
lean_object* v_pos_1200_; lean_object* v_err_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_del_object(v___x_1175_);
lean_dec(v_res_1173_);
lean_dec_ref(v_actions_1148_);
v_pos_1200_ = lean_ctor_get(v___y_1195_, 0);
v_err_1201_ = lean_ctor_get(v___y_1195_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___y_1195_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___y_1195_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_err_1201_);
lean_inc(v_pos_1200_);
lean_dec(v___y_1195_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_pos_1200_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_err_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
else
{
lean_object* v_utf8_1209_; lean_object* v___x_1210_; 
lean_dec_ref(v___y_1195_);
v_utf8_1209_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1);
v___x_1210_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1209_, v_pos_1196_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_pos_1211_; 
v_pos_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_pos_1211_);
lean_dec_ref_known(v___x_1210_, 2);
v_pos_1189_ = v_pos_1211_;
goto v___jp_1188_;
}
else
{
lean_object* v_pos_1212_; lean_object* v_err_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_del_object(v___x_1175_);
lean_dec(v_res_1173_);
lean_dec_ref(v_actions_1148_);
v_pos_1212_ = lean_ctor_get(v___x_1210_, 0);
v_err_1213_ = lean_ctor_get(v___x_1210_, 1);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1210_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_err_1213_);
lean_inc(v_pos_1212_);
lean_dec(v___x_1210_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_pos_1212_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_err_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_1242_; lean_object* v_err_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec_ref(v_actions_1148_);
v_pos_1242_ = lean_ctor_get(v___x_1171_, 0);
v_err_1243_ = lean_ctor_get(v___x_1171_, 1);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1171_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_err_1243_);
lean_inc(v_pos_1242_);
lean_dec(v___x_1171_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_pos_1242_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_err_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
else
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0));
v___x_1252_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(v___x_1251_, v_a_1149_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_pos_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1310_; 
v_pos_1253_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1310_ == 0)
{
lean_object* v_unused_1311_; 
v_unused_1311_ = lean_ctor_get(v___x_1252_, 1);
lean_dec(v_unused_1311_);
v___x_1255_ = v___x_1252_;
v_isShared_1256_ = v_isSharedCheck_1310_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_pos_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1310_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v_array_1257_; lean_object* v_idx_1258_; lean_object* v___y_1260_; lean_object* v_pos_1261_; lean_object* v_idx_1262_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v_array_1257_ = lean_ctor_get(v_pos_1253_, 0);
v_idx_1258_ = lean_ctor_get(v_pos_1253_, 1);
lean_inc(v_idx_1258_);
v___x_1286_ = lean_byte_array_size(v_array_1257_);
v___x_1287_ = lean_nat_dec_lt(v_idx_1258_, v___x_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1288_ = lean_box(0);
lean_inc(v_pos_1253_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set_tag(v___x_1255_, 1);
lean_ctor_set(v___x_1255_, 1, v___x_1288_);
v___x_1290_ = v___x_1255_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_pos_1253_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_inc(v_idx_1258_);
v___y_1260_ = v___x_1290_;
v_pos_1261_ = v_pos_1253_;
v_idx_1262_ = v_idx_1258_;
goto v___jp_1259_;
}
}
else
{
uint8_t v___x_1292_; uint8_t v_got_1293_; uint8_t v___x_1294_; 
v___x_1292_ = 10;
v_got_1293_ = lean_byte_array_fget(v_array_1257_, v_idx_1258_);
v___x_1294_ = lean_uint8_dec_eq(v_got_1293_, v___x_1292_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; lean_object* v___x_1297_; 
v___x_1295_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
lean_inc(v_pos_1253_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set_tag(v___x_1255_, 1);
lean_ctor_set(v___x_1255_, 1, v___x_1295_);
v___x_1297_ = v___x_1255_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_pos_1253_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
lean_inc(v_idx_1258_);
v___y_1260_ = v___x_1297_;
v_pos_1261_ = v_pos_1253_;
v_idx_1262_ = v_idx_1258_;
goto v___jp_1259_;
}
}
else
{
lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1307_; 
lean_inc_ref(v_array_1257_);
lean_del_object(v___x_1255_);
v_isSharedCheck_1307_ = !lean_is_exclusive(v_pos_1253_);
if (v_isSharedCheck_1307_ == 0)
{
lean_object* v_unused_1308_; lean_object* v_unused_1309_; 
v_unused_1308_ = lean_ctor_get(v_pos_1253_, 1);
lean_dec(v_unused_1308_);
v_unused_1309_ = lean_ctor_get(v_pos_1253_, 0);
lean_dec(v_unused_1309_);
v___x_1300_ = v_pos_1253_;
v_isShared_1301_ = v_isSharedCheck_1307_;
goto v_resetjp_1299_;
}
else
{
lean_dec(v_pos_1253_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1307_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1302_ = lean_unsigned_to_nat(1u);
v___x_1303_ = lean_nat_add(v_idx_1258_, v___x_1302_);
lean_dec(v_idx_1258_);
lean_inc(v___x_1303_);
lean_inc_ref(v_array_1257_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 1, v___x_1303_);
v___x_1305_ = v___x_1300_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_array_1257_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
v_pos_1151_ = v___x_1305_;
v_array_1152_ = v_array_1257_;
v_idx_1153_ = v___x_1303_;
goto v___jp_1150_;
}
}
}
}
v___jp_1259_:
{
uint8_t v___x_1263_; 
v___x_1263_ = lean_nat_dec_eq(v_idx_1258_, v_idx_1262_);
lean_dec(v_idx_1262_);
lean_dec(v_idx_1258_);
if (v___x_1263_ == 0)
{
lean_dec_ref(v_pos_1261_);
if (lean_obj_tag(v___y_1260_) == 0)
{
lean_object* v_pos_1264_; 
v_pos_1264_ = lean_ctor_get(v___y_1260_, 0);
lean_inc(v_pos_1264_);
lean_dec_ref_known(v___y_1260_, 2);
v_pos_1159_ = v_pos_1264_;
goto v___jp_1158_;
}
else
{
lean_object* v_pos_1265_; lean_object* v_err_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v_actions_1148_);
v_pos_1265_ = lean_ctor_get(v___y_1260_, 0);
v_err_1266_ = lean_ctor_get(v___y_1260_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___y_1260_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___y_1260_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_err_1266_);
lean_inc(v_pos_1265_);
lean_dec(v___y_1260_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_pos_1265_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_err_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
else
{
lean_object* v_utf8_1274_; lean_object* v___x_1275_; 
lean_dec_ref(v___y_1260_);
v_utf8_1274_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1);
v___x_1275_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1274_, v_pos_1261_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_pos_1276_; 
v_pos_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_pos_1276_);
lean_dec_ref_known(v___x_1275_, 2);
v_pos_1159_ = v_pos_1276_;
goto v___jp_1158_;
}
else
{
lean_object* v_pos_1277_; lean_object* v_err_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec_ref(v_actions_1148_);
v_pos_1277_ = lean_ctor_get(v___x_1275_, 0);
v_err_1278_ = lean_ctor_get(v___x_1275_, 1);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1275_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_err_1278_);
lean_inc(v_pos_1277_);
lean_dec(v___x_1275_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_pos_1277_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_err_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_1312_; lean_object* v_err_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec_ref(v_actions_1148_);
v_pos_1312_ = lean_ctor_get(v___x_1252_, 0);
v_err_1313_ = lean_ctor_get(v___x_1252_, 1);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1252_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_err_1313_);
lean_inc(v_pos_1312_);
lean_dec(v___x_1252_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_pos_1312_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_err_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
v___jp_1150_:
{
lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1154_ = lean_byte_array_size(v_array_1152_);
lean_dec_ref(v_array_1152_);
v___x_1155_ = lean_nat_dec_lt(v_idx_1153_, v___x_1154_);
lean_dec(v_idx_1153_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v_pos_1151_);
lean_ctor_set(v___x_1156_, 1, v_actions_1148_);
return v___x_1156_;
}
else
{
v_a_1149_ = v_pos_1151_;
goto _start;
}
}
v___jp_1158_:
{
lean_object* v_array_1160_; lean_object* v_idx_1161_; 
v_array_1160_ = lean_ctor_get(v_pos_1159_, 0);
lean_inc_ref(v_array_1160_);
v_idx_1161_ = lean_ctor_get(v_pos_1159_, 1);
lean_inc(v_idx_1161_);
v_pos_1151_ = v_pos_1159_;
v_array_1152_ = v_array_1160_;
v_idx_1153_ = v_idx_1161_;
goto v___jp_1150_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(lean_object* v_a_1323_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0));
v___x_1325_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(v___x_1324_, v_a_1323_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero(lean_object* v_a_1329_){
_start:
{
lean_object* v_array_1330_; lean_object* v_idx_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v_array_1330_ = lean_ctor_get(v_a_1329_, 0);
v_idx_1331_ = lean_ctor_get(v_a_1329_, 1);
v___x_1332_ = lean_byte_array_size(v_array_1330_);
v___x_1333_ = lean_nat_dec_lt(v_idx_1331_, v___x_1332_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_box(0);
v___x_1335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1335_, 0, v_a_1329_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
return v___x_1335_;
}
else
{
uint8_t v___x_1336_; uint8_t v_got_1337_; uint8_t v___x_1338_; 
v___x_1336_ = 0;
v_got_1337_ = lean_byte_array_fget(v_array_1330_, v_idx_1331_);
v___x_1338_ = lean_uint8_dec_eq(v_got_1337_, v___x_1336_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
v___x_1340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1340_, 0, v_a_1329_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
return v___x_1340_;
}
else
{
lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1351_; 
lean_inc(v_idx_1331_);
lean_inc_ref(v_array_1330_);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_a_1329_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; lean_object* v_unused_1353_; 
v_unused_1352_ = lean_ctor_get(v_a_1329_, 1);
lean_dec(v_unused_1352_);
v_unused_1353_ = lean_ctor_get(v_a_1329_, 0);
lean_dec(v_unused_1353_);
v___x_1342_ = v_a_1329_;
v_isShared_1343_ = v_isSharedCheck_1351_;
goto v_resetjp_1341_;
}
else
{
lean_dec(v_a_1329_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1351_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
v___x_1344_ = lean_unsigned_to_nat(1u);
v___x_1345_ = lean_nat_add(v_idx_1331_, v___x_1344_);
lean_dec(v_idx_1331_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 1, v___x_1345_);
v___x_1347_ = v___x_1342_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_array_1330_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_box(0);
v___x_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1347_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
return v___x_1349_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(uint64_t v_uidx_1360_, uint64_t v_shift_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v_array_1363_; lean_object* v_idx_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v_array_1363_ = lean_ctor_get(v_a_1362_, 0);
v_idx_1364_ = lean_ctor_get(v_a_1362_, 1);
v___x_1365_ = lean_byte_array_size(v_array_1363_);
v___x_1366_ = lean_nat_dec_lt(v_idx_1364_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_box(0);
v___x_1368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1368_, 0, v_a_1362_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
return v___x_1368_;
}
else
{
lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1414_; 
lean_inc(v_idx_1364_);
lean_inc_ref(v_array_1363_);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_a_1362_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; lean_object* v_unused_1416_; 
v_unused_1415_ = lean_ctor_get(v_a_1362_, 1);
lean_dec(v_unused_1415_);
v_unused_1416_ = lean_ctor_get(v_a_1362_, 0);
lean_dec(v_unused_1416_);
v___x_1370_ = v_a_1362_;
v_isShared_1371_ = v_isSharedCheck_1414_;
goto v_resetjp_1369_;
}
else
{
lean_dec(v_a_1362_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1414_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
uint8_t v_c_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v_it_x27_1376_; 
v_c_1372_ = lean_byte_array_fget(v_array_1363_, v_idx_1364_);
v___x_1373_ = lean_unsigned_to_nat(1u);
v___x_1374_ = lean_nat_add(v_idx_1364_, v___x_1373_);
lean_dec(v_idx_1364_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 1, v___x_1374_);
v_it_x27_1376_ = v___x_1370_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_array_1363_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v___x_1374_);
v_it_x27_1376_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
uint64_t v___x_1405_; uint8_t v___x_1406_; 
v___x_1405_ = 28ULL;
v___x_1406_ = lean_uint64_dec_eq(v_shift_1361_, v___x_1405_);
if (v___x_1406_ == 0)
{
goto v___jp_1377_;
}
else
{
uint8_t v___x_1407_; uint8_t v___x_1408_; uint8_t v___x_1409_; uint8_t v___x_1410_; 
v___x_1407_ = 240;
v___x_1408_ = lean_uint8_land(v_c_1372_, v___x_1407_);
v___x_1409_ = 0;
v___x_1410_ = lean_uint8_dec_eq(v___x_1408_, v___x_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3));
v___x_1412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1412_, 0, v_it_x27_1376_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
return v___x_1412_;
}
else
{
goto v___jp_1377_;
}
}
v___jp_1377_:
{
uint8_t v___x_1378_; uint8_t v___x_1379_; 
v___x_1378_ = 0;
v___x_1379_ = lean_uint8_dec_eq(v_c_1372_, v___x_1378_);
if (v___x_1379_ == 0)
{
uint8_t v___x_1380_; uint8_t v___x_1381_; uint64_t v___x_1382_; uint64_t v___x_1383_; uint64_t v___x_1384_; uint8_t v___x_1385_; uint8_t v___x_1386_; uint8_t v___x_1387_; 
v___x_1380_ = 127;
v___x_1381_ = lean_uint8_land(v_c_1372_, v___x_1380_);
v___x_1382_ = lean_uint8_to_uint64(v___x_1381_);
v___x_1383_ = lean_uint64_shift_left(v___x_1382_, v_shift_1361_);
v___x_1384_ = lean_uint64_lor(v_uidx_1360_, v___x_1383_);
v___x_1385_ = 128;
v___x_1386_ = lean_uint8_land(v_c_1372_, v___x_1385_);
v___x_1387_ = lean_uint8_dec_eq(v___x_1386_, v___x_1378_);
if (v___x_1387_ == 0)
{
uint64_t v___x_1388_; uint64_t v___x_1389_; 
v___x_1388_ = 7ULL;
v___x_1389_ = lean_uint64_add(v_shift_1361_, v___x_1388_);
v_uidx_1360_ = v___x_1384_;
v_shift_1361_ = v___x_1389_;
v_a_1362_ = v_it_x27_1376_;
goto _start;
}
else
{
uint64_t v___x_1391_; uint64_t v___x_1392_; uint64_t v___x_1393_; uint64_t v___x_1394_; uint8_t v___x_1395_; 
v___x_1391_ = 1ULL;
v___x_1392_ = lean_uint64_shift_right(v___x_1384_, v___x_1391_);
v___x_1393_ = lean_uint64_land(v___x_1391_, v___x_1384_);
v___x_1394_ = 0ULL;
v___x_1395_ = lean_uint64_dec_eq(v___x_1393_, v___x_1394_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1396_ = lean_uint64_to_nat(v___x_1392_);
v___x_1397_ = lean_nat_to_int(v___x_1396_);
v___x_1398_ = lean_int_neg(v___x_1397_);
lean_dec(v___x_1397_);
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v_it_x27_1376_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
return v___x_1399_;
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1400_ = lean_uint64_to_nat(v___x_1392_);
v___x_1401_ = lean_nat_to_int(v___x_1400_);
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_it_x27_1376_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
return v___x_1402_;
}
}
}
else
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1));
v___x_1404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1404_, 0, v_it_x27_1376_);
lean_ctor_set(v___x_1404_, 1, v___x_1403_);
return v___x_1404_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___boxed(lean_object* v_uidx_1417_, lean_object* v_shift_1418_, lean_object* v_a_1419_){
_start:
{
uint64_t v_uidx_boxed_1420_; uint64_t v_shift_boxed_1421_; lean_object* v_res_1422_; 
v_uidx_boxed_1420_ = lean_unbox_uint64(v_uidx_1417_);
lean_dec_ref(v_uidx_1417_);
v_shift_boxed_1421_ = lean_unbox_uint64(v_shift_1418_);
lean_dec_ref(v_shift_1418_);
v_res_1422_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(v_uidx_boxed_1420_, v_shift_boxed_1421_, v_a_1419_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(lean_object* v_a_1423_){
_start:
{
uint64_t v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = 0ULL;
v___x_1425_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(v___x_1424_, v___x_1424_, v_a_1423_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg(lean_object* v_a_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1429_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_pos_1431_; lean_object* v_res_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1446_; 
v_pos_1431_ = lean_ctor_get(v___x_1430_, 0);
v_res_1432_ = lean_ctor_get(v___x_1430_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1434_ = v___x_1430_;
v_isShared_1435_ = v_isSharedCheck_1446_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_res_1432_);
lean_inc(v_pos_1431_);
lean_dec(v___x_1430_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1446_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1436_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1437_ = lean_int_dec_lt(v_res_1432_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
lean_dec(v_res_1432_);
v___x_1438_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1));
if (v_isShared_1435_ == 0)
{
lean_ctor_set_tag(v___x_1434_, 1);
lean_ctor_set(v___x_1434_, 1, v___x_1438_);
v___x_1440_ = v___x_1434_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_pos_1431_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
else
{
lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1442_ = lean_nat_abs(v_res_1432_);
lean_dec(v_res_1432_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 1, v___x_1442_);
v___x_1444_ = v___x_1434_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_pos_1431_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v_pos_1447_; lean_object* v_err_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
v_pos_1447_ = lean_ctor_get(v___x_1430_, 0);
v_err_1448_ = lean_ctor_get(v___x_1430_, 1);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1430_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_err_1448_);
lean_inc(v_pos_1447_);
lean_dec(v___x_1430_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_pos_1447_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_err_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos(lean_object* v_a_1459_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1459_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_pos_1461_; lean_object* v_res_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1476_; 
v_pos_1461_ = lean_ctor_get(v___x_1460_, 0);
v_res_1462_ = lean_ctor_get(v___x_1460_, 1);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1464_ = v___x_1460_;
v_isShared_1465_ = v_isSharedCheck_1476_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_res_1462_);
lean_inc(v_pos_1461_);
lean_dec(v___x_1460_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1476_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; uint8_t v___x_1467_; 
v___x_1466_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1467_ = lean_int_dec_lt(v___x_1466_, v_res_1462_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
lean_dec(v_res_1462_);
v___x_1468_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1465_ == 0)
{
lean_ctor_set_tag(v___x_1464_, 1);
lean_ctor_set(v___x_1464_, 1, v___x_1468_);
v___x_1470_ = v___x_1464_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_pos_1461_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1472_ = lean_nat_abs(v_res_1462_);
lean_dec(v_res_1462_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 1, v___x_1472_);
v___x_1474_ = v___x_1464_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_pos_1461_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
else
{
lean_object* v_pos_1477_; lean_object* v_err_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
v_pos_1477_ = lean_ctor_get(v___x_1460_, 0);
v_err_1478_ = lean_ctor_get(v___x_1460_, 1);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1460_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_err_1478_);
lean_inc(v_pos_1477_);
lean_dec(v___x_1460_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_pos_1477_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_err_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId(lean_object* v_a_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1486_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_pos_1488_; lean_object* v_res_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1503_; 
v_pos_1488_ = lean_ctor_get(v___x_1487_, 0);
v_res_1489_ = lean_ctor_get(v___x_1487_, 1);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1491_ = v___x_1487_;
v_isShared_1492_ = v_isSharedCheck_1503_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_res_1489_);
lean_inc(v_pos_1488_);
lean_dec(v___x_1487_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1503_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1493_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1494_ = lean_int_dec_lt(v___x_1493_, v_res_1489_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
lean_dec(v_res_1489_);
v___x_1495_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1492_ == 0)
{
lean_ctor_set_tag(v___x_1491_, 1);
lean_ctor_set(v___x_1491_, 1, v___x_1495_);
v___x_1497_ = v___x_1491_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_pos_1488_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1501_; 
v___x_1499_ = lean_nat_abs(v_res_1489_);
lean_dec(v_res_1489_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 1, v___x_1499_);
v___x_1501_ = v___x_1491_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_pos_1488_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
else
{
lean_object* v_pos_1504_; lean_object* v_err_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
v_pos_1504_ = lean_ctor_get(v___x_1487_, 0);
v_err_1505_ = lean_ctor_get(v___x_1487_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1487_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_err_1505_);
lean_inc(v_pos_1504_);
lean_dec(v___x_1487_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_pos_1504_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_err_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(lean_object* v_parser_1513_, lean_object* v_acc_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v_array_1516_; lean_object* v_idx_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v_array_1516_ = lean_ctor_get(v_a_1515_, 0);
v_idx_1517_ = lean_ctor_get(v_a_1515_, 1);
v___x_1518_ = lean_byte_array_size(v_array_1516_);
v___x_1519_ = lean_nat_dec_lt(v_idx_1517_, v___x_1518_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
lean_dec_ref(v_acc_1514_);
lean_dec_ref(v_parser_1513_);
v___x_1520_ = lean_box(0);
v___x_1521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1521_, 0, v_a_1515_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
return v___x_1521_;
}
else
{
uint8_t v___x_1522_; uint8_t v___x_1523_; uint8_t v___x_1524_; 
v___x_1522_ = lean_byte_array_fget(v_array_1516_, v_idx_1517_);
v___x_1523_ = 0;
v___x_1524_ = lean_uint8_dec_eq(v___x_1522_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; 
lean_inc_ref(v_parser_1513_);
v___x_1525_ = lean_apply_1(v_parser_1513_, v_a_1515_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_pos_1526_; lean_object* v_res_1527_; lean_object* v___x_1528_; 
v_pos_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_pos_1526_);
v_res_1527_ = lean_ctor_get(v___x_1525_, 1);
lean_inc(v_res_1527_);
lean_dec_ref_known(v___x_1525_, 2);
v___x_1528_ = lean_array_push(v_acc_1514_, v_res_1527_);
v_acc_1514_ = v___x_1528_;
v_a_1515_ = v_pos_1526_;
goto _start;
}
else
{
lean_object* v_pos_1530_; lean_object* v_err_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec_ref(v_acc_1514_);
lean_dec_ref(v_parser_1513_);
v_pos_1530_ = lean_ctor_get(v___x_1525_, 0);
v_err_1531_ = lean_ctor_get(v___x_1525_, 1);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1525_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_err_1531_);
lean_inc(v_pos_1530_);
lean_dec(v___x_1525_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_pos_1530_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_err_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
else
{
lean_object* v___x_1539_; 
lean_dec_ref(v_parser_1513_);
v___x_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1539_, 0, v_a_1515_);
lean_ctor_set(v___x_1539_, 1, v_acc_1514_);
return v___x_1539_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go(lean_object* v_00_u03b1_1540_, lean_object* v_parser_1541_, lean_object* v_acc_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(v_parser_1541_, v_acc_1542_, v_a_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(lean_object* v_parser_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0));
v___x_1550_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(v_parser_1547_, v___x_1549_, v_a_1548_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero(lean_object* v_00_u03b1_1551_, lean_object* v_parser_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v_parser_1552_, v_a_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(lean_object* v_parser_1555_, lean_object* v_acc_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v_array_1558_; lean_object* v_idx_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
v_array_1558_ = lean_ctor_get(v_a_1557_, 0);
v_idx_1559_ = lean_ctor_get(v_a_1557_, 1);
v___x_1560_ = lean_byte_array_size(v_array_1558_);
v___x_1561_ = lean_nat_dec_lt(v_idx_1559_, v___x_1560_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec_ref(v_acc_1556_);
lean_dec_ref(v_parser_1555_);
v___x_1562_ = lean_box(0);
v___x_1563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1563_, 0, v_a_1557_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
return v___x_1563_;
}
else
{
uint8_t v___x_1564_; uint8_t v___x_1565_; uint8_t v___x_1566_; uint8_t v___x_1567_; uint8_t v___x_1568_; 
v___x_1564_ = lean_byte_array_fget(v_array_1558_, v_idx_1559_);
v___x_1565_ = 1;
v___x_1566_ = lean_uint8_land(v___x_1565_, v___x_1564_);
v___x_1567_ = 0;
v___x_1568_ = lean_uint8_dec_eq(v___x_1566_, v___x_1567_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; 
lean_dec_ref(v_parser_1555_);
v___x_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1569_, 0, v_a_1557_);
lean_ctor_set(v___x_1569_, 1, v_acc_1556_);
return v___x_1569_;
}
else
{
uint8_t v___x_1570_; 
v___x_1570_ = lean_uint8_dec_eq(v___x_1564_, v___x_1567_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; 
lean_inc_ref(v_parser_1555_);
v___x_1571_ = lean_apply_1(v_parser_1555_, v_a_1557_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_pos_1572_; lean_object* v_res_1573_; lean_object* v___x_1574_; 
v_pos_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_pos_1572_);
v_res_1573_ = lean_ctor_get(v___x_1571_, 1);
lean_inc(v_res_1573_);
lean_dec_ref_known(v___x_1571_, 2);
v___x_1574_ = lean_array_push(v_acc_1556_, v_res_1573_);
v_acc_1556_ = v___x_1574_;
v_a_1557_ = v_pos_1572_;
goto _start;
}
else
{
lean_object* v_pos_1576_; lean_object* v_err_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref(v_acc_1556_);
lean_dec_ref(v_parser_1555_);
v_pos_1576_ = lean_ctor_get(v___x_1571_, 0);
v_err_1577_ = lean_ctor_get(v___x_1571_, 1);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1571_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_err_1577_);
lean_inc(v_pos_1576_);
lean_dec(v___x_1571_);
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
else
{
lean_object* v___x_1585_; 
lean_dec_ref(v_parser_1555_);
v___x_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1585_, 0, v_a_1557_);
lean_ctor_set(v___x_1585_, 1, v_acc_1556_);
return v___x_1585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go(lean_object* v_00_u03b1_1586_, lean_object* v_parser_1587_, lean_object* v_acc_1588_, lean_object* v_a_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(v_parser_1587_, v_acc_1588_, v_a_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(lean_object* v_parser_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0));
v___x_1594_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(v_parser_1591_, v___x_1593_, v_a_1592_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero(lean_object* v_00_u03b1_1595_, lean_object* v_parser_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(v_parser_1596_, v_a_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList(lean_object* v_a_1599_){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId), 1, 0);
v___x_1601_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(v___x_1600_, v_a_1599_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause(lean_object* v_a_1602_){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit), 1, 0);
v___x_1604_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v___x_1603_, v_a_1602_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(lean_object* v_acc_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v_array_1607_; lean_object* v_idx_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v_array_1607_ = lean_ctor_get(v_a_1606_, 0);
v_idx_1608_ = lean_ctor_get(v_a_1606_, 1);
v___x_1609_ = lean_byte_array_size(v_array_1607_);
v___x_1610_ = lean_nat_dec_lt(v_idx_1608_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_dec_ref(v_acc_1605_);
v___x_1611_ = lean_box(0);
v___x_1612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1612_, 0, v_a_1606_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
return v___x_1612_;
}
else
{
uint8_t v___x_1613_; uint8_t v___x_1614_; uint8_t v___x_1615_; uint8_t v___x_1616_; uint8_t v___x_1617_; 
v___x_1613_ = lean_byte_array_fget(v_array_1607_, v_idx_1608_);
v___x_1614_ = 1;
v___x_1615_ = lean_uint8_land(v___x_1614_, v___x_1613_);
v___x_1616_ = 0;
v___x_1617_ = lean_uint8_dec_eq(v___x_1615_, v___x_1616_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1618_, 0, v_a_1606_);
lean_ctor_set(v___x_1618_, 1, v_acc_1605_);
return v___x_1618_;
}
else
{
uint8_t v___x_1619_; 
v___x_1619_ = lean_uint8_dec_eq(v___x_1613_, v___x_1616_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1606_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_pos_1621_; lean_object* v_res_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1635_; 
v_pos_1621_ = lean_ctor_get(v___x_1620_, 0);
v_res_1622_ = lean_ctor_get(v___x_1620_, 1);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1624_ = v___x_1620_;
v_isShared_1625_ = v_isSharedCheck_1635_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_res_1622_);
lean_inc(v_pos_1621_);
lean_dec(v___x_1620_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1635_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1626_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1627_ = lean_int_dec_lt(v___x_1626_, v_res_1622_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1630_; 
lean_dec(v_res_1622_);
lean_dec_ref(v_acc_1605_);
v___x_1628_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1625_ == 0)
{
lean_ctor_set_tag(v___x_1624_, 1);
lean_ctor_set(v___x_1624_, 1, v___x_1628_);
v___x_1630_ = v___x_1624_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_pos_1621_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_del_object(v___x_1624_);
v___x_1632_ = lean_nat_abs(v_res_1622_);
lean_dec(v_res_1622_);
v___x_1633_ = lean_array_push(v_acc_1605_, v___x_1632_);
v_acc_1605_ = v___x_1633_;
v_a_1606_ = v_pos_1621_;
goto _start;
}
}
}
else
{
lean_object* v_pos_1636_; lean_object* v_err_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec_ref(v_acc_1605_);
v_pos_1636_ = lean_ctor_get(v___x_1620_, 0);
v_err_1637_ = lean_ctor_get(v___x_1620_, 1);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1620_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_err_1637_);
lean_inc(v_pos_1636_);
lean_dec(v___x_1620_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_pos_1636_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_err_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
else
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1645_, 0, v_a_1606_);
lean_ctor_set(v___x_1645_, 1, v_acc_1605_);
return v___x_1645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(lean_object* v_a_1646_){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0));
v___x_1648_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(v___x_1647_, v_a_1646_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(lean_object* v_a_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1649_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_pos_1651_; lean_object* v_res_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1683_; 
v_pos_1651_ = lean_ctor_get(v___x_1650_, 0);
v_res_1652_ = lean_ctor_get(v___x_1650_, 1);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1654_ = v___x_1650_;
v_isShared_1655_ = v_isSharedCheck_1683_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_res_1652_);
lean_inc(v_pos_1651_);
lean_dec(v___x_1650_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1683_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1656_; uint8_t v___x_1657_; 
v___x_1656_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1657_ = lean_int_dec_lt(v_res_1652_, v___x_1656_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; lean_object* v___x_1660_; 
lean_dec(v_res_1652_);
v___x_1658_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1));
if (v_isShared_1655_ == 0)
{
lean_ctor_set_tag(v___x_1654_, 1);
lean_ctor_set(v___x_1654_, 1, v___x_1658_);
v___x_1660_ = v___x_1654_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_pos_1651_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
else
{
lean_object* v___x_1662_; 
lean_del_object(v___x_1654_);
v___x_1662_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v_pos_1651_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_pos_1663_; lean_object* v_res_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1673_; 
v_pos_1663_ = lean_ctor_get(v___x_1662_, 0);
v_res_1664_ = lean_ctor_get(v___x_1662_, 1);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1666_ = v___x_1662_;
v_isShared_1667_ = v_isSharedCheck_1673_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_res_1664_);
lean_inc(v_pos_1663_);
lean_dec(v___x_1662_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1673_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1668_ = lean_nat_abs(v_res_1652_);
lean_dec(v_res_1652_);
v___x_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
lean_ctor_set(v___x_1669_, 1, v_res_1664_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 1, v___x_1669_);
v___x_1671_ = v___x_1666_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_pos_1663_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
else
{
lean_object* v_pos_1674_; lean_object* v_err_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
lean_dec(v_res_1652_);
v_pos_1674_ = lean_ctor_get(v___x_1662_, 0);
v_err_1675_ = lean_ctor_get(v___x_1662_, 1);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1662_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_err_1675_);
lean_inc(v_pos_1674_);
lean_dec(v___x_1662_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_pos_1674_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_err_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1684_; lean_object* v_err_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
v_pos_1684_ = lean_ctor_get(v___x_1650_, 0);
v_err_1685_ = lean_ctor_get(v___x_1650_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1650_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_err_1685_);
lean_inc(v_pos_1684_);
lean_dec(v___x_1650_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_pos_1684_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_err_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints(lean_object* v_a_1693_){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes), 1, 0);
v___x_1695_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v___x_1694_, v_a_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(lean_object* v_acc_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v_array_1698_; lean_object* v_idx_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; 
v_array_1698_ = lean_ctor_get(v_a_1697_, 0);
v_idx_1699_ = lean_ctor_get(v_a_1697_, 1);
v___x_1700_ = lean_byte_array_size(v_array_1698_);
v___x_1701_ = lean_nat_dec_lt(v_idx_1699_, v___x_1700_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
lean_dec_ref(v_acc_1696_);
v___x_1702_ = lean_box(0);
v___x_1703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1703_, 0, v_a_1697_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
return v___x_1703_;
}
else
{
uint8_t v___x_1704_; uint8_t v___x_1705_; uint8_t v___x_1706_; 
v___x_1704_ = lean_byte_array_fget(v_array_1698_, v_idx_1699_);
v___x_1705_ = 0;
v___x_1706_ = lean_uint8_dec_eq(v___x_1704_, v___x_1705_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1697_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_pos_1708_; lean_object* v_res_1709_; lean_object* v___x_1710_; 
v_pos_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_pos_1708_);
v_res_1709_ = lean_ctor_get(v___x_1707_, 1);
lean_inc(v_res_1709_);
lean_dec_ref_known(v___x_1707_, 2);
v___x_1710_ = lean_array_push(v_acc_1696_, v_res_1709_);
v_acc_1696_ = v___x_1710_;
v_a_1697_ = v_pos_1708_;
goto _start;
}
else
{
lean_object* v_pos_1712_; lean_object* v_err_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec_ref(v_acc_1696_);
v_pos_1712_ = lean_ctor_get(v___x_1707_, 0);
v_err_1713_ = lean_ctor_get(v___x_1707_, 1);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1707_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_err_1713_);
lean_inc(v_pos_1712_);
lean_dec(v___x_1707_);
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
lean_ctor_set(v___x_1721_, 0, v_a_1697_);
lean_ctor_set(v___x_1721_, 1, v_acc_1696_);
return v___x_1721_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(lean_object* v_a_1722_){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0));
v___x_1724_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(v___x_1723_, v_a_1722_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1_spec__2(lean_object* v_acc_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v_array_1727_; lean_object* v_idx_1728_; lean_object* v___x_1729_; uint8_t v___x_1730_; 
v_array_1727_ = lean_ctor_get(v_a_1726_, 0);
v_idx_1728_ = lean_ctor_get(v_a_1726_, 1);
v___x_1729_ = lean_byte_array_size(v_array_1727_);
v___x_1730_ = lean_nat_dec_lt(v_idx_1728_, v___x_1729_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
lean_dec_ref(v_acc_1725_);
v___x_1731_ = lean_box(0);
v___x_1732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1732_, 0, v_a_1726_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
return v___x_1732_;
}
else
{
uint8_t v___x_1733_; uint8_t v___x_1734_; uint8_t v___x_1735_; 
v___x_1733_ = lean_byte_array_fget(v_array_1727_, v_idx_1728_);
v___x_1734_ = 0;
v___x_1735_ = lean_uint8_dec_eq(v___x_1733_, v___x_1734_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(v_a_1726_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_pos_1737_; lean_object* v_res_1738_; lean_object* v___x_1739_; 
v_pos_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_pos_1737_);
v_res_1738_ = lean_ctor_get(v___x_1736_, 1);
lean_inc(v_res_1738_);
lean_dec_ref_known(v___x_1736_, 2);
v___x_1739_ = lean_array_push(v_acc_1725_, v_res_1738_);
v_acc_1725_ = v___x_1739_;
v_a_1726_ = v_pos_1737_;
goto _start;
}
else
{
lean_object* v_pos_1741_; lean_object* v_err_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec_ref(v_acc_1725_);
v_pos_1741_ = lean_ctor_get(v___x_1736_, 0);
v_err_1742_ = lean_ctor_get(v___x_1736_, 1);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1736_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_err_1742_);
lean_inc(v_pos_1741_);
lean_dec(v___x_1736_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_pos_1741_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_err_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
else
{
lean_object* v___x_1750_; 
v___x_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1750_, 0, v_a_1726_);
lean_ctor_set(v___x_1750_, 1, v_acc_1725_);
return v___x_1750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1(lean_object* v_a_1751_){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0));
v___x_1753_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1_spec__2(v___x_1752_, v_a_1751_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(lean_object* v_a_1754_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1754_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_pos_1756_; lean_object* v_res_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1894_; 
v_pos_1756_ = lean_ctor_get(v___x_1755_, 0);
v_res_1757_ = lean_ctor_get(v___x_1755_, 1);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1759_ = v___x_1755_;
v_isShared_1760_ = v_isSharedCheck_1894_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_res_1757_);
lean_inc(v_pos_1756_);
lean_dec(v___x_1755_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1894_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1761_ = lean_unsigned_to_nat(0u);
v___x_1762_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1763_ = lean_int_dec_lt(v___x_1762_, v_res_1757_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
lean_dec(v_res_1757_);
v___x_1764_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1760_ == 0)
{
lean_ctor_set_tag(v___x_1759_, 1);
lean_ctor_set(v___x_1759_, 1, v___x_1764_);
v___x_1766_ = v___x_1759_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_pos_1756_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
else
{
lean_object* v___x_1768_; 
lean_del_object(v___x_1759_);
v___x_1768_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(v_pos_1756_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_pos_1769_; lean_object* v_res_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1884_; 
v_pos_1769_ = lean_ctor_get(v___x_1768_, 0);
v_res_1770_ = lean_ctor_get(v___x_1768_, 1);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1772_ = v___x_1768_;
v_isShared_1773_ = v_isSharedCheck_1884_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_res_1770_);
lean_inc(v_pos_1769_);
lean_dec(v___x_1768_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1884_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v_array_1774_; lean_object* v_idx_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v_array_1774_ = lean_ctor_get(v_pos_1769_, 0);
v_idx_1775_ = lean_ctor_get(v_pos_1769_, 1);
v___x_1776_ = lean_byte_array_size(v_array_1774_);
v___x_1777_ = lean_nat_dec_lt(v_idx_1775_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1780_; 
lean_dec(v_res_1770_);
lean_dec(v_res_1757_);
v___x_1778_ = lean_box(0);
if (v_isShared_1773_ == 0)
{
lean_ctor_set_tag(v___x_1772_, 1);
lean_ctor_set(v___x_1772_, 1, v___x_1778_);
v___x_1780_ = v___x_1772_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_pos_1769_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
else
{
uint8_t v___x_1782_; uint8_t v_got_1783_; uint8_t v___x_1784_; 
v___x_1782_ = 0;
v_got_1783_ = lean_byte_array_fget(v_array_1774_, v_idx_1775_);
v___x_1784_ = lean_uint8_dec_eq(v_got_1783_, v___x_1782_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; lean_object* v___x_1787_; 
lean_dec(v_res_1770_);
lean_dec(v_res_1757_);
v___x_1785_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
if (v_isShared_1773_ == 0)
{
lean_ctor_set_tag(v___x_1772_, 1);
lean_ctor_set(v___x_1772_, 1, v___x_1785_);
v___x_1787_ = v___x_1772_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_pos_1769_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
else
{
lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1881_; 
lean_inc(v_idx_1775_);
lean_inc_ref(v_array_1774_);
lean_del_object(v___x_1772_);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_pos_1769_);
if (v_isSharedCheck_1881_ == 0)
{
lean_object* v_unused_1882_; lean_object* v_unused_1883_; 
v_unused_1882_ = lean_ctor_get(v_pos_1769_, 1);
lean_dec(v_unused_1882_);
v_unused_1883_ = lean_ctor_get(v_pos_1769_, 0);
lean_dec(v_unused_1883_);
v___x_1790_ = v_pos_1769_;
v_isShared_1791_ = v_isSharedCheck_1881_;
goto v_resetjp_1789_;
}
else
{
lean_dec(v_pos_1769_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1881_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1792_ = lean_unsigned_to_nat(1u);
v___x_1793_ = lean_nat_add(v_idx_1775_, v___x_1792_);
lean_dec(v_idx_1775_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 1, v___x_1793_);
v___x_1795_ = v___x_1790_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_array_1774_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v___x_1795_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_pos_1797_; lean_object* v_res_1798_; lean_object* v___x_1799_; 
v_pos_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_pos_1797_);
v_res_1798_ = lean_ctor_get(v___x_1796_, 1);
lean_inc(v_res_1798_);
lean_dec_ref_known(v___x_1796_, 2);
v___x_1799_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1(v_pos_1797_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_pos_1800_; lean_object* v_res_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1861_; 
v_pos_1800_ = lean_ctor_get(v___x_1799_, 0);
v_res_1801_ = lean_ctor_get(v___x_1799_, 1);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1803_ = v___x_1799_;
v_isShared_1804_ = v_isSharedCheck_1861_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_res_1801_);
lean_inc(v_pos_1800_);
lean_dec(v___x_1799_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1861_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v_array_1805_; lean_object* v_idx_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
v_array_1805_ = lean_ctor_get(v_pos_1800_, 0);
v_idx_1806_ = lean_ctor_get(v_pos_1800_, 1);
v___x_1807_ = lean_byte_array_size(v_array_1805_);
v___x_1808_ = lean_nat_dec_lt(v_idx_1806_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
lean_dec(v_res_1801_);
lean_dec(v_res_1798_);
lean_dec(v_res_1770_);
lean_dec(v_res_1757_);
v___x_1809_ = lean_box(0);
if (v_isShared_1804_ == 0)
{
lean_ctor_set_tag(v___x_1803_, 1);
lean_ctor_set(v___x_1803_, 1, v___x_1809_);
v___x_1811_ = v___x_1803_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_pos_1800_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
else
{
uint8_t v_got_1813_; uint8_t v___x_1814_; 
v_got_1813_ = lean_byte_array_fget(v_array_1805_, v_idx_1806_);
v___x_1814_ = lean_uint8_dec_eq(v_got_1813_, v___x_1782_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
lean_dec(v_res_1801_);
lean_dec(v_res_1798_);
lean_dec(v_res_1770_);
lean_dec(v_res_1757_);
v___x_1815_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
if (v_isShared_1804_ == 0)
{
lean_ctor_set_tag(v___x_1803_, 1);
lean_ctor_set(v___x_1803_, 1, v___x_1815_);
v___x_1817_ = v___x_1803_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_pos_1800_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
else
{
lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1858_; 
lean_inc(v_idx_1806_);
lean_inc_ref(v_array_1805_);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_pos_1800_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; lean_object* v_unused_1860_; 
v_unused_1859_ = lean_ctor_get(v_pos_1800_, 1);
lean_dec(v_unused_1859_);
v_unused_1860_ = lean_ctor_get(v_pos_1800_, 0);
lean_dec(v_unused_1860_);
v___x_1820_ = v_pos_1800_;
v_isShared_1821_ = v_isSharedCheck_1858_;
goto v_resetjp_1819_;
}
else
{
lean_dec(v_pos_1800_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1858_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1822_ = lean_nat_abs(v_res_1757_);
lean_dec(v_res_1757_);
v___x_1823_ = lean_nat_add(v_idx_1806_, v___x_1792_);
lean_dec(v_idx_1806_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 1, v___x_1823_);
v___x_1825_ = v___x_1820_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_array_1805_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1826_ = lean_array_get_size(v_res_1770_);
v___x_1827_ = lean_nat_dec_eq(v___x_1826_, v___x_1761_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1828_ = lean_array_get_size(v_res_1801_);
v___x_1829_ = lean_nat_dec_eq(v___x_1828_, v___x_1761_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1830_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_1770_);
v___x_1831_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1822_);
lean_ctor_set(v___x_1831_, 1, v_res_1770_);
lean_ctor_set(v___x_1831_, 2, v___x_1830_);
lean_ctor_set(v___x_1831_, 3, v_res_1798_);
lean_ctor_set(v___x_1831_, 4, v_res_1801_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 1, v___x_1831_);
lean_ctor_set(v___x_1803_, 0, v___x_1825_);
v___x_1833_ = v___x_1803_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
else
{
lean_object* v___x_1835_; uint8_t v___x_1836_; 
lean_dec(v_res_1801_);
v___x_1835_ = lean_array_get_size(v_res_1798_);
v___x_1836_ = lean_nat_dec_eq(v___x_1835_, v___x_1761_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1837_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1822_);
lean_ctor_set(v___x_1837_, 1, v_res_1770_);
lean_ctor_set(v___x_1837_, 2, v_res_1798_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 1, v___x_1837_);
lean_ctor_set(v___x_1803_, 0, v___x_1825_);
v___x_1839_ = v___x_1803_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
else
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1845_; 
lean_dec(v_res_1798_);
v___x_1841_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_1770_);
v___x_1842_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0));
v___x_1843_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1822_);
lean_ctor_set(v___x_1843_, 1, v_res_1770_);
lean_ctor_set(v___x_1843_, 2, v___x_1841_);
lean_ctor_set(v___x_1843_, 3, v___x_1842_);
lean_ctor_set(v___x_1843_, 4, v___x_1842_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 1, v___x_1843_);
lean_ctor_set(v___x_1803_, 0, v___x_1825_);
v___x_1845_ = v___x_1803_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
else
{
lean_object* v___x_1847_; uint8_t v___x_1848_; 
lean_dec(v_res_1770_);
v___x_1847_ = lean_array_get_size(v_res_1801_);
lean_dec(v_res_1801_);
v___x_1848_ = lean_nat_dec_eq(v___x_1847_, v___x_1761_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
lean_dec(v___x_1822_);
lean_dec(v_res_1798_);
v___x_1849_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2));
if (v_isShared_1804_ == 0)
{
lean_ctor_set_tag(v___x_1803_, 1);
lean_ctor_set(v___x_1803_, 1, v___x_1849_);
lean_ctor_set(v___x_1803_, 0, v___x_1825_);
v___x_1851_ = v___x_1803_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
else
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1822_);
lean_ctor_set(v___x_1853_, 1, v_res_1798_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 1, v___x_1853_);
lean_ctor_set(v___x_1803_, 0, v___x_1825_);
v___x_1855_ = v___x_1803_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
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
lean_object* v_pos_1862_; lean_object* v_err_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec(v_res_1798_);
lean_dec(v_res_1770_);
lean_dec(v_res_1757_);
v_pos_1862_ = lean_ctor_get(v___x_1799_, 0);
v_err_1863_ = lean_ctor_get(v___x_1799_, 1);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1799_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_err_1863_);
lean_inc(v_pos_1862_);
lean_dec(v___x_1799_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_pos_1862_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v_err_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
else
{
lean_object* v_pos_1871_; lean_object* v_err_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_dec(v_res_1770_);
lean_dec(v_res_1757_);
v_pos_1871_ = lean_ctor_get(v___x_1796_, 0);
v_err_1872_ = lean_ctor_get(v___x_1796_, 1);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1796_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_err_1872_);
lean_inc(v_pos_1871_);
lean_dec(v___x_1796_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_pos_1871_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v_err_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
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
lean_object* v_pos_1885_; lean_object* v_err_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_res_1757_);
v_pos_1885_ = lean_ctor_get(v___x_1768_, 0);
v_err_1886_ = lean_ctor_get(v___x_1768_, 1);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1768_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_err_1886_);
lean_inc(v_pos_1885_);
lean_dec(v___x_1768_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_pos_1885_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_err_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1895_; lean_object* v_err_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
v_pos_1895_ = lean_ctor_get(v___x_1755_, 0);
v_err_1896_ = lean_ctor_get(v___x_1755_, 1);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1755_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_err_1896_);
lean_inc(v_pos_1895_);
lean_dec(v___x_1755_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_pos_1895_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_err_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(lean_object* v_a_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v_a_1904_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_pos_1906_; lean_object* v_res_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1941_; 
v_pos_1906_ = lean_ctor_get(v___x_1905_, 0);
v_res_1907_ = lean_ctor_get(v___x_1905_, 1);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1909_ = v___x_1905_;
v_isShared_1910_ = v_isSharedCheck_1941_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_res_1907_);
lean_inc(v_pos_1906_);
lean_dec(v___x_1905_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1941_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v_array_1911_; lean_object* v_idx_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v_array_1911_ = lean_ctor_get(v_pos_1906_, 0);
v_idx_1912_ = lean_ctor_get(v_pos_1906_, 1);
v___x_1913_ = lean_byte_array_size(v_array_1911_);
v___x_1914_ = lean_nat_dec_lt(v_idx_1912_, v___x_1913_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; lean_object* v___x_1917_; 
lean_dec(v_res_1907_);
v___x_1915_ = lean_box(0);
if (v_isShared_1910_ == 0)
{
lean_ctor_set_tag(v___x_1909_, 1);
lean_ctor_set(v___x_1909_, 1, v___x_1915_);
v___x_1917_ = v___x_1909_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_pos_1906_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v___x_1915_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
else
{
uint8_t v___x_1919_; uint8_t v_got_1920_; uint8_t v___x_1921_; 
v___x_1919_ = 0;
v_got_1920_ = lean_byte_array_fget(v_array_1911_, v_idx_1912_);
v___x_1921_ = lean_uint8_dec_eq(v_got_1920_, v___x_1919_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; lean_object* v___x_1924_; 
lean_dec(v_res_1907_);
v___x_1922_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
if (v_isShared_1910_ == 0)
{
lean_ctor_set_tag(v___x_1909_, 1);
lean_ctor_set(v___x_1909_, 1, v___x_1922_);
v___x_1924_ = v___x_1909_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_pos_1906_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
else
{
lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1938_; 
lean_inc(v_idx_1912_);
lean_inc_ref(v_array_1911_);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_pos_1906_);
if (v_isSharedCheck_1938_ == 0)
{
lean_object* v_unused_1939_; lean_object* v_unused_1940_; 
v_unused_1939_ = lean_ctor_get(v_pos_1906_, 1);
lean_dec(v_unused_1939_);
v_unused_1940_ = lean_ctor_get(v_pos_1906_, 0);
lean_dec(v_unused_1940_);
v___x_1927_ = v_pos_1906_;
v_isShared_1928_ = v_isSharedCheck_1938_;
goto v_resetjp_1926_;
}
else
{
lean_dec(v_pos_1906_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1938_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1929_ = lean_unsigned_to_nat(1u);
v___x_1930_ = lean_nat_add(v_idx_1912_, v___x_1929_);
lean_dec(v_idx_1912_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 1, v___x_1930_);
v___x_1932_ = v___x_1927_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_array_1911_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1933_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1933_, 0, v_res_1907_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 1, v___x_1933_);
lean_ctor_set(v___x_1909_, 0, v___x_1932_);
v___x_1935_ = v___x_1909_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_1942_; lean_object* v_err_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
v_pos_1942_ = lean_ctor_get(v___x_1905_, 0);
v_err_1943_ = lean_ctor_get(v___x_1905_, 1);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1905_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_err_1943_);
lean_inc(v_pos_1942_);
lean_dec(v___x_1905_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_pos_1942_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_err_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(lean_object* v_a_1952_){
_start:
{
lean_object* v_array_1953_; lean_object* v_idx_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v_array_1953_ = lean_ctor_get(v_a_1952_, 0);
v_idx_1954_ = lean_ctor_get(v_a_1952_, 1);
v___x_1955_ = lean_byte_array_size(v_array_1953_);
v___x_1956_ = lean_nat_dec_lt(v_idx_1954_, v___x_1955_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = lean_box(0);
v___x_1958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1958_, 0, v_a_1952_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
return v___x_1958_;
}
else
{
lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1980_; 
lean_inc(v_idx_1954_);
lean_inc_ref(v_array_1953_);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_a_1952_);
if (v_isSharedCheck_1980_ == 0)
{
lean_object* v_unused_1981_; lean_object* v_unused_1982_; 
v_unused_1981_ = lean_ctor_get(v_a_1952_, 1);
lean_dec(v_unused_1981_);
v_unused_1982_ = lean_ctor_get(v_a_1952_, 0);
lean_dec(v_unused_1982_);
v___x_1960_ = v_a_1952_;
v_isShared_1961_ = v_isSharedCheck_1980_;
goto v_resetjp_1959_;
}
else
{
lean_dec(v_a_1952_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1980_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
uint8_t v_c_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v_it_x27_1966_; 
v_c_1962_ = lean_byte_array_fget(v_array_1953_, v_idx_1954_);
v___x_1963_ = lean_unsigned_to_nat(1u);
v___x_1964_ = lean_nat_add(v_idx_1954_, v___x_1963_);
lean_dec(v_idx_1954_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 1, v___x_1964_);
v_it_x27_1966_ = v___x_1960_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_array_1953_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v___x_1964_);
v_it_x27_1966_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
uint8_t v___x_1967_; uint8_t v___x_1968_; 
v___x_1967_ = 97;
v___x_1968_ = lean_uint8_dec_eq(v_c_1962_, v___x_1967_);
if (v___x_1968_ == 0)
{
uint8_t v___x_1969_; uint8_t v___x_1970_; 
v___x_1969_ = 100;
v___x_1970_ = lean_uint8_dec_eq(v_c_1962_, v___x_1969_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1971_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0));
v___x_1972_ = lean_uint8_to_nat(v_c_1962_);
v___x_1973_ = l_Nat_reprFast(v___x_1972_);
v___x_1974_ = lean_string_append(v___x_1971_, v___x_1973_);
lean_dec_ref(v___x_1973_);
v___x_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
v___x_1976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1976_, 0, v_it_x27_1966_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
return v___x_1976_;
}
else
{
lean_object* v___x_1977_; 
v___x_1977_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(v_it_x27_1966_);
return v___x_1977_;
}
}
else
{
lean_object* v___x_1978_; 
v___x_1978_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(v_it_x27_1966_);
return v___x_1978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(lean_object* v_acc_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v___x_1985_; 
lean_inc_ref(v_a_1984_);
v___x_1985_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(v_a_1984_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_pos_1986_; lean_object* v_res_1987_; lean_object* v___x_1988_; 
lean_dec_ref(v_a_1984_);
v_pos_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_pos_1986_);
v_res_1987_ = lean_ctor_get(v___x_1985_, 1);
lean_inc(v_res_1987_);
lean_dec_ref_known(v___x_1985_, 2);
v___x_1988_ = lean_array_push(v_acc_1983_, v_res_1987_);
v_acc_1983_ = v___x_1988_;
v_a_1984_ = v_pos_1986_;
goto _start;
}
else
{
lean_object* v_pos_1990_; lean_object* v_err_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2004_; 
v_pos_1990_ = lean_ctor_get(v___x_1985_, 0);
v_err_1991_ = lean_ctor_get(v___x_1985_, 1);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1993_ = v___x_1985_;
v_isShared_1994_ = v_isSharedCheck_2004_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_err_1991_);
lean_inc(v_pos_1990_);
lean_dec(v___x_1985_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2004_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v_idx_1995_; lean_object* v_idx_1996_; uint8_t v___x_1997_; 
v_idx_1995_ = lean_ctor_get(v_a_1984_, 1);
lean_inc(v_idx_1995_);
lean_dec_ref(v_a_1984_);
v_idx_1996_ = lean_ctor_get(v_pos_1990_, 1);
v___x_1997_ = lean_nat_dec_eq(v_idx_1995_, v_idx_1996_);
lean_dec(v_idx_1995_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1999_; 
lean_dec_ref(v_acc_1983_);
if (v_isShared_1994_ == 0)
{
v___x_1999_ = v___x_1993_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_pos_1990_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_err_1991_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
else
{
lean_object* v___x_2002_; 
lean_dec(v_err_1991_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set_tag(v___x_1993_, 0);
lean_ctor_set(v___x_1993_, 1, v_acc_1983_);
v___x_2002_ = v___x_1993_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_pos_1990_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_acc_1983_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(lean_object* v_a_2008_){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0));
v___x_2010_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(v___x_2009_, v_a_2008_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_pos_2011_; lean_object* v_array_2012_; lean_object* v_idx_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; 
v_pos_2011_ = lean_ctor_get(v___x_2010_, 0);
v_array_2012_ = lean_ctor_get(v_pos_2011_, 0);
v_idx_2013_ = lean_ctor_get(v_pos_2011_, 1);
v___x_2014_ = lean_byte_array_size(v_array_2012_);
v___x_2015_ = lean_nat_dec_lt(v_idx_2013_, v___x_2014_);
if (v___x_2015_ == 0)
{
return v___x_2010_;
}
else
{
lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2023_; 
lean_inc(v_pos_2011_);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2023_ == 0)
{
lean_object* v_unused_2024_; lean_object* v_unused_2025_; 
v_unused_2024_ = lean_ctor_get(v___x_2010_, 1);
lean_dec(v_unused_2024_);
v_unused_2025_ = lean_ctor_get(v___x_2010_, 0);
lean_dec(v_unused_2025_);
v___x_2017_ = v___x_2010_;
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
else
{
lean_dec(v___x_2010_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2019_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__1));
if (v_isShared_2018_ == 0)
{
lean_ctor_set_tag(v___x_2017_, 1);
lean_ctor_set(v___x_2017_, 1, v___x_2019_);
v___x_2021_ = v___x_2017_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_pos_2011_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
else
{
return v___x_2010_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_parseActions(lean_object* v_a_2026_){
_start:
{
lean_object* v_array_2027_; lean_object* v_idx_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
v_array_2027_ = lean_ctor_get(v_a_2026_, 0);
v_idx_2028_ = lean_ctor_get(v_a_2026_, 1);
v___x_2029_ = lean_byte_array_size(v_array_2027_);
v___x_2030_ = lean_nat_dec_lt(v_idx_2028_, v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = lean_box(0);
v___x_2032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2032_, 0, v_a_2026_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
return v___x_2032_;
}
else
{
uint8_t v___x_2033_; uint8_t v___x_2034_; uint8_t v___x_2035_; 
v___x_2033_ = lean_byte_array_fget(v_array_2027_, v_idx_2028_);
v___x_2034_ = 97;
v___x_2035_ = lean_uint8_dec_eq(v___x_2033_, v___x_2034_);
if (v___x_2035_ == 0)
{
uint8_t v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = 100;
v___x_2037_ = lean_uint8_dec_eq(v___x_2033_, v___x_2036_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(v_a_2026_);
return v___x_2038_;
}
else
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(v_a_2026_);
return v___x_2039_;
}
}
else
{
lean_object* v___x_2040_; 
v___x_2040_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(v_a_2026_);
return v___x_2040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object* v_path_2041_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = l_IO_FS_readBinFile(v_path_2041_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2065_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2046_ = v___x_2043_;
v_isShared_2047_ = v_isSharedCheck_2065_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2043_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2065_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_parseActions), 1, 0);
v___x_2049_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_2048_, v_a_2044_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2060_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2060_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2060_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
lean_ctor_set_tag(v___x_2052_, 18);
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2057_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set_tag(v___x_2046_, 1);
lean_ctor_set(v___x_2046_, 0, v___x_2055_);
v___x_2057_ = v___x_2046_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; 
v_a_2061_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2049_, 1);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v_a_2061_);
v___x_2063_ = v___x_2046_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2061_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
v_a_2066_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2043_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2043_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof___boxed(lean_object* v_path_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(v_path_2074_);
lean_dec_ref(v_path_2074_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_parseLRATProof(lean_object* v_proof_2077_){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_parseActions), 1, 0);
v___x_2079_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_2078_, v_proof_2077_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(lean_object* v_as_2081_, size_t v_i_2082_, size_t v_stop_2083_, lean_object* v_b_2084_){
_start:
{
uint8_t v___x_2085_; 
v___x_2085_ = lean_usize_dec_eq(v_i_2082_, v_stop_2083_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; size_t v___x_2091_; size_t v___x_2092_; 
v___x_2086_ = lean_array_uget_borrowed(v_as_2081_, v_i_2082_);
lean_inc(v___x_2086_);
v___x_2087_ = l_Nat_reprFast(v___x_2086_);
v___x_2088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2089_ = lean_string_append(v___x_2087_, v___x_2088_);
v___x_2090_ = lean_string_append(v_b_2084_, v___x_2089_);
lean_dec_ref(v___x_2089_);
v___x_2091_ = ((size_t)1ULL);
v___x_2092_ = lean_usize_add(v_i_2082_, v___x_2091_);
v_i_2082_ = v___x_2092_;
v_b_2084_ = v___x_2090_;
goto _start;
}
else
{
return v_b_2084_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___boxed(lean_object* v_as_2094_, lean_object* v_i_2095_, lean_object* v_stop_2096_, lean_object* v_b_2097_){
_start:
{
size_t v_i_boxed_2098_; size_t v_stop_boxed_2099_; lean_object* v_res_2100_; 
v_i_boxed_2098_ = lean_unbox_usize(v_i_2095_);
lean_dec(v_i_2095_);
v_stop_boxed_2099_ = lean_unbox_usize(v_stop_2096_);
lean_dec(v_stop_2096_);
v_res_2100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_as_2094_, v_i_boxed_2098_, v_stop_boxed_2099_, v_b_2097_);
lean_dec_ref(v_as_2094_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(lean_object* v_ids_2102_){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2103_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2104_ = lean_unsigned_to_nat(0u);
v___x_2105_ = lean_array_get_size(v_ids_2102_);
v___x_2106_ = lean_nat_dec_lt(v___x_2104_, v___x_2105_);
if (v___x_2106_ == 0)
{
return v___x_2103_;
}
else
{
size_t v___x_2107_; size_t v___x_2108_; lean_object* v___x_2109_; 
v___x_2107_ = ((size_t)0ULL);
v___x_2108_ = lean_usize_of_nat(v___x_2105_);
v___x_2109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_ids_2102_, v___x_2107_, v___x_2108_, v___x_2103_);
return v___x_2109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___boxed(lean_object* v_ids_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_ids_2110_);
lean_dec_ref(v_ids_2110_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(lean_object* v_hint_2113_){
_start:
{
lean_object* v_fst_2114_; lean_object* v_snd_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v_fst_2114_ = lean_ctor_get(v_hint_2113_, 0);
lean_inc(v_fst_2114_);
v_snd_2115_ = lean_ctor_get(v_hint_2113_, 1);
lean_inc(v_snd_2115_);
lean_dec_ref(v_hint_2113_);
v___x_2116_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0));
v___x_2117_ = l_Nat_reprFast(v_fst_2114_);
v___x_2118_ = lean_string_append(v___x_2116_, v___x_2117_);
lean_dec_ref(v___x_2117_);
v___x_2119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2120_ = lean_string_append(v___x_2118_, v___x_2119_);
v___x_2121_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_snd_2115_);
lean_dec(v_snd_2115_);
v___x_2122_ = lean_string_append(v___x_2120_, v___x_2121_);
lean_dec_ref(v___x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(lean_object* v_as_2123_, size_t v_i_2124_, size_t v_stop_2125_, lean_object* v_b_2126_){
_start:
{
uint8_t v___x_2127_; 
v___x_2127_ = lean_usize_dec_eq(v_i_2124_, v_stop_2125_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; size_t v___x_2131_; size_t v___x_2132_; 
v___x_2128_ = lean_array_uget_borrowed(v_as_2123_, v_i_2124_);
lean_inc(v___x_2128_);
v___x_2129_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(v___x_2128_);
v___x_2130_ = lean_string_append(v_b_2126_, v___x_2129_);
lean_dec_ref(v___x_2129_);
v___x_2131_ = ((size_t)1ULL);
v___x_2132_ = lean_usize_add(v_i_2124_, v___x_2131_);
v_i_2124_ = v___x_2132_;
v_b_2126_ = v___x_2130_;
goto _start;
}
else
{
return v_b_2126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0___boxed(lean_object* v_as_2134_, lean_object* v_i_2135_, lean_object* v_stop_2136_, lean_object* v_b_2137_){
_start:
{
size_t v_i_boxed_2138_; size_t v_stop_boxed_2139_; lean_object* v_res_2140_; 
v_i_boxed_2138_ = lean_unbox_usize(v_i_2135_);
lean_dec(v_i_2135_);
v_stop_boxed_2139_ = lean_unbox_usize(v_stop_2136_);
lean_dec(v_stop_2136_);
v_res_2140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_as_2134_, v_i_boxed_2138_, v_stop_boxed_2139_, v_b_2137_);
lean_dec_ref(v_as_2134_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(lean_object* v_hints_2141_){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
v___x_2142_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2143_ = lean_unsigned_to_nat(0u);
v___x_2144_ = lean_array_get_size(v_hints_2141_);
v___x_2145_ = lean_nat_dec_lt(v___x_2143_, v___x_2144_);
if (v___x_2145_ == 0)
{
return v___x_2142_;
}
else
{
size_t v___x_2146_; size_t v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = ((size_t)0ULL);
v___x_2147_ = lean_usize_of_nat(v___x_2144_);
v___x_2148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_hints_2141_, v___x_2146_, v___x_2147_, v___x_2142_);
return v___x_2148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___boxed(lean_object* v_hints_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(v_hints_2149_);
lean_dec_ref(v_hints_2149_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(lean_object* v_as_2151_, size_t v_i_2152_, size_t v_stop_2153_, lean_object* v_b_2154_){
_start:
{
uint8_t v___x_2155_; 
v___x_2155_ = lean_usize_dec_eq(v_i_2152_, v_stop_2153_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; size_t v___x_2161_; size_t v___x_2162_; 
v___x_2156_ = lean_array_uget_borrowed(v_as_2151_, v_i_2152_);
v___x_2157_ = l_Int_repr(v___x_2156_);
v___x_2158_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2159_ = lean_string_append(v___x_2157_, v___x_2158_);
v___x_2160_ = lean_string_append(v_b_2154_, v___x_2159_);
lean_dec_ref(v___x_2159_);
v___x_2161_ = ((size_t)1ULL);
v___x_2162_ = lean_usize_add(v_i_2152_, v___x_2161_);
v_i_2152_ = v___x_2162_;
v_b_2154_ = v___x_2160_;
goto _start;
}
else
{
return v_b_2154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0___boxed(lean_object* v_as_2164_, lean_object* v_i_2165_, lean_object* v_stop_2166_, lean_object* v_b_2167_){
_start:
{
size_t v_i_boxed_2168_; size_t v_stop_boxed_2169_; lean_object* v_res_2170_; 
v_i_boxed_2168_ = lean_unbox_usize(v_i_2165_);
lean_dec(v_i_2165_);
v_stop_boxed_2169_ = lean_unbox_usize(v_stop_2166_);
lean_dec(v_stop_2166_);
v_res_2170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_as_2164_, v_i_boxed_2168_, v_stop_boxed_2169_, v_b_2167_);
lean_dec_ref(v_as_2164_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(lean_object* v_clause_2171_){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2172_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2173_ = lean_unsigned_to_nat(0u);
v___x_2174_ = lean_array_get_size(v_clause_2171_);
v___x_2175_ = lean_nat_dec_lt(v___x_2173_, v___x_2174_);
if (v___x_2175_ == 0)
{
return v___x_2172_;
}
else
{
size_t v___x_2176_; size_t v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = ((size_t)0ULL);
v___x_2177_ = lean_usize_of_nat(v___x_2174_);
v___x_2178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_clause_2171_, v___x_2176_, v___x_2177_, v___x_2172_);
return v___x_2178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___boxed(lean_object* v_clause_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_clause_2179_);
lean_dec_ref(v_clause_2179_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(lean_object* v_a_2185_){
_start:
{
switch(lean_obj_tag(v_a_2185_))
{
case 0:
{
lean_object* v_id_2186_; lean_object* v_rupHints_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v_id_2186_ = lean_ctor_get(v_a_2185_, 0);
lean_inc(v_id_2186_);
v_rupHints_2187_ = lean_ctor_get(v_a_2185_, 1);
lean_inc_ref(v_rupHints_2187_);
lean_dec_ref_known(v_a_2185_, 2);
v___x_2188_ = l_Nat_reprFast(v_id_2186_);
v___x_2189_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__0));
v___x_2190_ = lean_string_append(v___x_2188_, v___x_2189_);
v___x_2191_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2187_);
lean_dec_ref(v_rupHints_2187_);
v___x_2192_ = lean_string_append(v___x_2190_, v___x_2191_);
lean_dec_ref(v___x_2191_);
v___x_2193_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2194_ = lean_string_append(v___x_2192_, v___x_2193_);
return v___x_2194_;
}
case 1:
{
lean_object* v_id_2195_; lean_object* v_c_2196_; lean_object* v_rupHints_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v_id_2195_ = lean_ctor_get(v_a_2185_, 0);
lean_inc(v_id_2195_);
v_c_2196_ = lean_ctor_get(v_a_2185_, 1);
lean_inc(v_c_2196_);
v_rupHints_2197_ = lean_ctor_get(v_a_2185_, 2);
lean_inc_ref(v_rupHints_2197_);
lean_dec_ref_known(v_a_2185_, 3);
v___x_2198_ = l_Nat_reprFast(v_id_2195_);
v___x_2199_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2200_ = lean_string_append(v___x_2198_, v___x_2199_);
v___x_2201_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_c_2196_);
lean_dec(v_c_2196_);
v___x_2202_ = lean_string_append(v___x_2200_, v___x_2201_);
lean_dec_ref(v___x_2201_);
v___x_2203_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2));
v___x_2204_ = lean_string_append(v___x_2202_, v___x_2203_);
v___x_2205_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2197_);
lean_dec_ref(v_rupHints_2197_);
v___x_2206_ = lean_string_append(v___x_2204_, v___x_2205_);
lean_dec_ref(v___x_2205_);
v___x_2207_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2208_ = lean_string_append(v___x_2206_, v___x_2207_);
return v___x_2208_;
}
case 2:
{
lean_object* v_id_2209_; lean_object* v_c_2210_; lean_object* v_rupHints_2211_; lean_object* v_ratHints_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v_id_2209_ = lean_ctor_get(v_a_2185_, 0);
lean_inc(v_id_2209_);
v_c_2210_ = lean_ctor_get(v_a_2185_, 1);
lean_inc(v_c_2210_);
v_rupHints_2211_ = lean_ctor_get(v_a_2185_, 3);
lean_inc_ref(v_rupHints_2211_);
v_ratHints_2212_ = lean_ctor_get(v_a_2185_, 4);
lean_inc_ref(v_ratHints_2212_);
lean_dec_ref_known(v_a_2185_, 5);
v___x_2213_ = l_Nat_reprFast(v_id_2209_);
v___x_2214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2215_ = lean_string_append(v___x_2213_, v___x_2214_);
v___x_2216_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_c_2210_);
lean_dec(v_c_2210_);
v___x_2217_ = lean_string_append(v___x_2215_, v___x_2216_);
lean_dec_ref(v___x_2216_);
v___x_2218_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2));
v___x_2219_ = lean_string_append(v___x_2217_, v___x_2218_);
v___x_2220_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2211_);
lean_dec_ref(v_rupHints_2211_);
v___x_2221_ = lean_string_append(v___x_2219_, v___x_2220_);
lean_dec_ref(v___x_2220_);
v___x_2222_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(v_ratHints_2212_);
lean_dec_ref(v_ratHints_2212_);
v___x_2223_ = lean_string_append(v___x_2221_, v___x_2222_);
lean_dec_ref(v___x_2222_);
v___x_2224_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2225_ = lean_string_append(v___x_2223_, v___x_2224_);
return v___x_2225_;
}
default: 
{
lean_object* v_ids_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v_ids_2226_ = lean_ctor_get(v_a_2185_, 0);
lean_inc_ref(v_ids_2226_);
lean_dec_ref_known(v_a_2185_, 1);
v___x_2227_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3));
v___x_2228_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_ids_2226_);
lean_dec_ref(v_ids_2226_);
v___x_2229_ = lean_string_append(v___x_2227_, v___x_2228_);
lean_dec_ref(v___x_2228_);
v___x_2230_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2231_ = lean_string_append(v___x_2229_, v___x_2230_);
return v___x_2231_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(lean_object* v_as_2233_, size_t v_i_2234_, size_t v_stop_2235_, lean_object* v_b_2236_){
_start:
{
uint8_t v___x_2237_; 
v___x_2237_ = lean_usize_dec_eq(v_i_2234_, v_stop_2235_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; size_t v___x_2243_; size_t v___x_2244_; 
v___x_2238_ = lean_array_uget_borrowed(v_as_2233_, v_i_2234_);
lean_inc(v___x_2238_);
v___x_2239_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(v___x_2238_);
v___x_2240_ = lean_string_append(v_b_2236_, v___x_2239_);
lean_dec_ref(v___x_2239_);
v___x_2241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___closed__0));
v___x_2242_ = lean_string_append(v___x_2240_, v___x_2241_);
v___x_2243_ = ((size_t)1ULL);
v___x_2244_ = lean_usize_add(v_i_2234_, v___x_2243_);
v_i_2234_ = v___x_2244_;
v_b_2236_ = v___x_2242_;
goto _start;
}
else
{
return v_b_2236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___boxed(lean_object* v_as_2246_, lean_object* v_i_2247_, lean_object* v_stop_2248_, lean_object* v_b_2249_){
_start:
{
size_t v_i_boxed_2250_; size_t v_stop_boxed_2251_; lean_object* v_res_2252_; 
v_i_boxed_2250_ = lean_unbox_usize(v_i_2247_);
lean_dec(v_i_2247_);
v_stop_boxed_2251_ = lean_unbox_usize(v_stop_2248_);
lean_dec(v_stop_2248_);
v_res_2252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_as_2246_, v_i_boxed_2250_, v_stop_boxed_2251_, v_b_2249_);
lean_dec_ref(v_as_2246_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString(lean_object* v_proof_2253_){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; uint8_t v___x_2257_; 
v___x_2254_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2255_ = lean_unsigned_to_nat(0u);
v___x_2256_ = lean_array_get_size(v_proof_2253_);
v___x_2257_ = lean_nat_dec_lt(v___x_2255_, v___x_2256_);
if (v___x_2257_ == 0)
{
return v___x_2254_;
}
else
{
size_t v___x_2258_; size_t v___x_2259_; lean_object* v___x_2260_; 
v___x_2258_ = ((size_t)0ULL);
v___x_2259_ = lean_usize_of_nat(v___x_2256_);
v___x_2260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_proof_2253_, v___x_2258_, v___x_2259_, v___x_2254_);
return v___x_2260_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString___boxed(lean_object* v_proof_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_proof_2261_);
lean_dec_ref(v_proof_2261_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startDelete(lean_object* v_acc_2263_){
_start:
{
uint8_t v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = 100;
v___x_2265_ = lean_byte_array_push(v_acc_2263_, v___x_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(lean_object* v_acc_2266_, uint64_t v_lit_2267_){
_start:
{
uint8_t v___y_2269_; uint64_t v___x_2274_; uint8_t v___x_2275_; 
v___x_2274_ = 0ULL;
v___x_2275_ = lean_uint64_dec_eq(v_lit_2267_, v___x_2274_);
if (v___x_2275_ == 0)
{
uint64_t v___x_2276_; uint8_t v___x_2277_; 
v___x_2276_ = 127ULL;
v___x_2277_ = lean_uint64_dec_lt(v___x_2276_, v_lit_2267_);
if (v___x_2277_ == 0)
{
uint8_t v___x_2278_; uint8_t v___x_2279_; uint8_t v___x_2280_; 
v___x_2278_ = lean_uint64_to_uint8(v_lit_2267_);
v___x_2279_ = 127;
v___x_2280_ = lean_uint8_land(v___x_2278_, v___x_2279_);
v___y_2269_ = v___x_2280_;
goto v___jp_2268_;
}
else
{
uint8_t v___x_2281_; uint8_t v___x_2282_; uint8_t v___x_2283_; uint8_t v___x_2284_; uint8_t v___x_2285_; 
v___x_2281_ = lean_uint64_to_uint8(v_lit_2267_);
v___x_2282_ = 127;
v___x_2283_ = lean_uint8_land(v___x_2281_, v___x_2282_);
v___x_2284_ = 128;
v___x_2285_ = lean_uint8_lor(v___x_2283_, v___x_2284_);
v___y_2269_ = v___x_2285_;
goto v___jp_2268_;
}
}
else
{
return v_acc_2266_;
}
v___jp_2268_:
{
lean_object* v_acc_2270_; uint64_t v___x_2271_; uint64_t v___x_2272_; 
v_acc_2270_ = lean_byte_array_push(v_acc_2266_, v___y_2269_);
v___x_2271_ = 7ULL;
v___x_2272_ = lean_uint64_shift_right(v_lit_2267_, v___x_2271_);
v_acc_2266_ = v_acc_2270_;
v_lit_2267_ = v___x_2272_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode___boxed(lean_object* v_acc_2286_, lean_object* v_lit_2287_){
_start:
{
uint64_t v_lit_boxed_2288_; lean_object* v_res_2289_; 
v_lit_boxed_2288_ = lean_unbox_uint64(v_lit_2287_);
lean_dec_ref(v_lit_2287_);
v_res_2289_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(v_acc_2286_, v_lit_boxed_2288_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(lean_object* v_msg_2290_){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = l_ByteArray_empty;
v___x_2292_ = lean_panic_fn_borrowed(v___x_2291_, v_msg_2290_);
return v___x_2292_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0(void){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = lean_cstr_to_nat("18446744073709551615");
return v___x_2293_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4(void){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2297_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3));
v___x_2298_ = lean_unsigned_to_nat(4u);
v___x_2299_ = lean_unsigned_to_nat(400u);
v___x_2300_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2));
v___x_2301_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1));
v___x_2302_ = l_mkPanicMessageWithDecl(v___x_2301_, v___x_2300_, v___x_2299_, v___x_2298_, v___x_2297_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(lean_object* v_acc_2303_, lean_object* v_lit_2304_){
_start:
{
lean_object* v___y_2306_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2313_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_2314_ = lean_int_dec_lt(v___x_2313_, v_lit_2304_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2315_ = lean_unsigned_to_nat(2u);
v___x_2316_ = lean_nat_abs(v_lit_2304_);
v___x_2317_ = lean_nat_mul(v___x_2315_, v___x_2316_);
lean_dec(v___x_2316_);
v___x_2318_ = lean_unsigned_to_nat(1u);
v___x_2319_ = lean_nat_add(v___x_2317_, v___x_2318_);
lean_dec(v___x_2317_);
v___y_2306_ = v___x_2319_;
goto v___jp_2305_;
}
else
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2320_ = lean_unsigned_to_nat(2u);
v___x_2321_ = lean_nat_abs(v_lit_2304_);
v___x_2322_ = lean_nat_mul(v___x_2320_, v___x_2321_);
lean_dec(v___x_2321_);
v___y_2306_ = v___x_2322_;
goto v___jp_2305_;
}
v___jp_2305_:
{
lean_object* v___x_2307_; uint8_t v___x_2308_; 
v___x_2307_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0);
v___x_2308_ = lean_nat_dec_le(v___y_2306_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
lean_dec(v___y_2306_);
lean_dec_ref(v_acc_2303_);
v___x_2309_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4);
v___x_2310_ = l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(v___x_2309_);
return v___x_2310_;
}
else
{
uint64_t v_mapped_2311_; lean_object* v___x_2312_; 
v_mapped_2311_ = lean_uint64_of_nat(v___y_2306_);
lean_dec(v___y_2306_);
v___x_2312_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(v_acc_2303_, v_mapped_2311_);
return v___x_2312_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___boxed(lean_object* v_acc_2323_, lean_object* v_lit_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2323_, v_lit_2324_);
lean_dec(v_lit_2324_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_zeroByte(lean_object* v_acc_2326_){
_start:
{
uint8_t v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = 0;
v___x_2328_ = lean_byte_array_push(v_acc_2326_, v___x_2327_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addNat(lean_object* v_acc_2329_, lean_object* v_n_2330_){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = lean_nat_to_int(v_n_2330_);
v___x_2332_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2329_, v___x_2331_);
lean_dec(v___x_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startAdd(lean_object* v_acc_2333_){
_start:
{
uint8_t v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = 97;
v___x_2335_ = lean_byte_array_push(v_acc_2333_, v___x_2334_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(lean_object* v_as_2336_, size_t v_i_2337_, size_t v_stop_2338_, lean_object* v_b_2339_){
_start:
{
uint8_t v___x_2340_; 
v___x_2340_ = lean_usize_dec_eq(v_i_2337_, v_stop_2338_);
if (v___x_2340_ == 0)
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; size_t v___x_2344_; size_t v___x_2345_; 
v___x_2341_ = lean_array_uget_borrowed(v_as_2336_, v_i_2337_);
lean_inc(v___x_2341_);
v___x_2342_ = lean_nat_to_int(v___x_2341_);
v___x_2343_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2339_, v___x_2342_);
lean_dec(v___x_2342_);
v___x_2344_ = ((size_t)1ULL);
v___x_2345_ = lean_usize_add(v_i_2337_, v___x_2344_);
v_i_2337_ = v___x_2345_;
v_b_2339_ = v___x_2343_;
goto _start;
}
else
{
return v_b_2339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0___boxed(lean_object* v_as_2347_, lean_object* v_i_2348_, lean_object* v_stop_2349_, lean_object* v_b_2350_){
_start:
{
size_t v_i_boxed_2351_; size_t v_stop_boxed_2352_; lean_object* v_res_2353_; 
v_i_boxed_2351_ = lean_unbox_usize(v_i_2348_);
lean_dec(v_i_2348_);
v_stop_boxed_2352_ = lean_unbox_usize(v_stop_2349_);
lean_dec(v_stop_2349_);
v_res_2353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(v_as_2347_, v_i_boxed_2351_, v_stop_boxed_2352_, v_b_2350_);
lean_dec_ref(v_as_2347_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(lean_object* v_as_2354_, size_t v_i_2355_, size_t v_stop_2356_, lean_object* v_b_2357_){
_start:
{
uint8_t v___x_2358_; 
v___x_2358_ = lean_usize_dec_eq(v_i_2355_, v_stop_2356_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; size_t v___x_2362_; size_t v___x_2363_; lean_object* v___x_2364_; 
v___x_2359_ = lean_array_uget_borrowed(v_as_2354_, v_i_2355_);
lean_inc(v___x_2359_);
v___x_2360_ = lean_nat_to_int(v___x_2359_);
v___x_2361_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2357_, v___x_2360_);
lean_dec(v___x_2360_);
v___x_2362_ = ((size_t)1ULL);
v___x_2363_ = lean_usize_add(v_i_2355_, v___x_2362_);
v___x_2364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(v_as_2354_, v___x_2363_, v_stop_2356_, v___x_2361_);
return v___x_2364_;
}
else
{
return v_b_2357_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0___boxed(lean_object* v_as_2365_, lean_object* v_i_2366_, lean_object* v_stop_2367_, lean_object* v_b_2368_){
_start:
{
size_t v_i_boxed_2369_; size_t v_stop_boxed_2370_; lean_object* v_res_2371_; 
v_i_boxed_2369_ = lean_unbox_usize(v_i_2366_);
lean_dec(v_i_2366_);
v_stop_boxed_2370_ = lean_unbox_usize(v_stop_2367_);
lean_dec(v_stop_2367_);
v_res_2371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_as_2365_, v_i_boxed_2369_, v_stop_boxed_2370_, v_b_2368_);
lean_dec_ref(v_as_2365_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(lean_object* v_as_2372_, size_t v_i_2373_, size_t v_stop_2374_, lean_object* v_b_2375_){
_start:
{
lean_object* v___y_2377_; uint8_t v___x_2381_; 
v___x_2381_ = lean_usize_dec_eq(v_i_2373_, v_stop_2374_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; lean_object* v_fst_2383_; lean_object* v_snd_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v_acc_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2382_ = lean_array_uget_borrowed(v_as_2372_, v_i_2373_);
v_fst_2383_ = lean_ctor_get(v___x_2382_, 0);
v_snd_2384_ = lean_ctor_get(v___x_2382_, 1);
v___x_2385_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_2383_);
v___x_2386_ = lean_nat_to_int(v_fst_2383_);
v___x_2387_ = lean_int_neg(v___x_2386_);
lean_dec(v___x_2386_);
v_acc_2388_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2375_, v___x_2387_);
lean_dec(v___x_2387_);
v___x_2389_ = lean_array_get_size(v_snd_2384_);
v___x_2390_ = lean_nat_dec_lt(v___x_2385_, v___x_2389_);
if (v___x_2390_ == 0)
{
v___y_2377_ = v_acc_2388_;
goto v___jp_2376_;
}
else
{
size_t v___x_2391_; size_t v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = ((size_t)0ULL);
v___x_2392_ = lean_usize_of_nat(v___x_2389_);
v___x_2393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2384_, v___x_2391_, v___x_2392_, v_acc_2388_);
v___y_2377_ = v___x_2393_;
goto v___jp_2376_;
}
}
else
{
return v_b_2375_;
}
v___jp_2376_:
{
size_t v___x_2378_; size_t v___x_2379_; 
v___x_2378_ = ((size_t)1ULL);
v___x_2379_ = lean_usize_add(v_i_2373_, v___x_2378_);
v_i_2373_ = v___x_2379_;
v_b_2375_ = v___y_2377_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3___boxed(lean_object* v_as_2394_, lean_object* v_i_2395_, lean_object* v_stop_2396_, lean_object* v_b_2397_){
_start:
{
size_t v_i_boxed_2398_; size_t v_stop_boxed_2399_; lean_object* v_res_2400_; 
v_i_boxed_2398_ = lean_unbox_usize(v_i_2395_);
lean_dec(v_i_2395_);
v_stop_boxed_2399_ = lean_unbox_usize(v_stop_2396_);
lean_dec(v_stop_2396_);
v_res_2400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(v_as_2394_, v_i_boxed_2398_, v_stop_boxed_2399_, v_b_2397_);
lean_dec_ref(v_as_2394_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(lean_object* v_as_2401_, size_t v_i_2402_, size_t v_stop_2403_, lean_object* v_b_2404_){
_start:
{
lean_object* v___y_2406_; uint8_t v___x_2410_; 
v___x_2410_ = lean_usize_dec_eq(v_i_2402_, v_stop_2403_);
if (v___x_2410_ == 0)
{
lean_object* v___x_2411_; lean_object* v_fst_2412_; lean_object* v_snd_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v_acc_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; 
v___x_2411_ = lean_array_uget_borrowed(v_as_2401_, v_i_2402_);
v_fst_2412_ = lean_ctor_get(v___x_2411_, 0);
v_snd_2413_ = lean_ctor_get(v___x_2411_, 1);
v___x_2414_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_2412_);
v___x_2415_ = lean_nat_to_int(v_fst_2412_);
v___x_2416_ = lean_int_neg(v___x_2415_);
lean_dec(v___x_2415_);
v_acc_2417_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2404_, v___x_2416_);
lean_dec(v___x_2416_);
v___x_2418_ = lean_array_get_size(v_snd_2413_);
v___x_2419_ = lean_nat_dec_lt(v___x_2414_, v___x_2418_);
if (v___x_2419_ == 0)
{
v___y_2406_ = v_acc_2417_;
goto v___jp_2405_;
}
else
{
size_t v___x_2420_; size_t v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = ((size_t)0ULL);
v___x_2421_ = lean_usize_of_nat(v___x_2418_);
v___x_2422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2413_, v___x_2420_, v___x_2421_, v_acc_2417_);
v___y_2406_ = v___x_2422_;
goto v___jp_2405_;
}
}
else
{
return v_b_2404_;
}
v___jp_2405_:
{
size_t v___x_2407_; size_t v___x_2408_; lean_object* v___x_2409_; 
v___x_2407_ = ((size_t)1ULL);
v___x_2408_ = lean_usize_add(v_i_2402_, v___x_2407_);
v___x_2409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(v_as_2401_, v___x_2408_, v_stop_2403_, v___y_2406_);
return v___x_2409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2___boxed(lean_object* v_as_2423_, lean_object* v_i_2424_, lean_object* v_stop_2425_, lean_object* v_b_2426_){
_start:
{
size_t v_i_boxed_2427_; size_t v_stop_boxed_2428_; lean_object* v_res_2429_; 
v_i_boxed_2427_ = lean_unbox_usize(v_i_2424_);
lean_dec(v_i_2424_);
v_stop_boxed_2428_ = lean_unbox_usize(v_stop_2425_);
lean_dec(v_stop_2425_);
v_res_2429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_as_2423_, v_i_boxed_2427_, v_stop_boxed_2428_, v_b_2426_);
lean_dec_ref(v_as_2423_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(lean_object* v_as_2430_, size_t v_i_2431_, size_t v_stop_2432_, lean_object* v_b_2433_){
_start:
{
uint8_t v___x_2434_; 
v___x_2434_ = lean_usize_dec_eq(v_i_2431_, v_stop_2432_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; lean_object* v___x_2436_; size_t v___x_2437_; size_t v___x_2438_; 
v___x_2435_ = lean_array_uget_borrowed(v_as_2430_, v_i_2431_);
v___x_2436_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2433_, v___x_2435_);
v___x_2437_ = ((size_t)1ULL);
v___x_2438_ = lean_usize_add(v_i_2431_, v___x_2437_);
v_i_2431_ = v___x_2438_;
v_b_2433_ = v___x_2436_;
goto _start;
}
else
{
return v_b_2433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1___boxed(lean_object* v_as_2440_, lean_object* v_i_2441_, lean_object* v_stop_2442_, lean_object* v_b_2443_){
_start:
{
size_t v_i_boxed_2444_; size_t v_stop_boxed_2445_; lean_object* v_res_2446_; 
v_i_boxed_2444_ = lean_unbox_usize(v_i_2441_);
lean_dec(v_i_2441_);
v_stop_boxed_2445_ = lean_unbox_usize(v_stop_2442_);
lean_dec(v_stop_2442_);
v_res_2446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_as_2440_, v_i_boxed_2444_, v_stop_boxed_2445_, v_b_2443_);
lean_dec_ref(v_as_2440_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(lean_object* v_proof_2447_, lean_object* v_idx_2448_, lean_object* v_acc_2449_){
_start:
{
lean_object* v___y_2451_; lean_object* v___y_2456_; lean_object* v___y_2460_; lean_object* v___y_2464_; lean_object* v___y_2468_; lean_object* v___x_2471_; uint8_t v___x_2472_; 
v___x_2471_ = lean_array_get_size(v_proof_2447_);
v___x_2472_ = lean_nat_dec_lt(v_idx_2448_, v___x_2471_);
if (v___x_2472_ == 0)
{
lean_dec(v_idx_2448_);
return v_acc_2449_;
}
else
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_array_fget_borrowed(v_proof_2447_, v_idx_2448_);
switch(lean_obj_tag(v___x_2473_))
{
case 0:
{
lean_object* v_id_2474_; lean_object* v_rupHints_2475_; uint8_t v___x_2476_; lean_object* v_acc_2477_; lean_object* v___x_2478_; lean_object* v_acc_2479_; uint8_t v___x_2480_; lean_object* v_acc_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; 
v_id_2474_ = lean_ctor_get(v___x_2473_, 0);
v_rupHints_2475_ = lean_ctor_get(v___x_2473_, 1);
v___x_2476_ = 97;
v_acc_2477_ = lean_byte_array_push(v_acc_2449_, v___x_2476_);
lean_inc(v_id_2474_);
v___x_2478_ = lean_nat_to_int(v_id_2474_);
v_acc_2479_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2477_, v___x_2478_);
lean_dec(v___x_2478_);
v___x_2480_ = 0;
v_acc_2481_ = lean_byte_array_push(v_acc_2479_, v___x_2480_);
v___x_2482_ = lean_unsigned_to_nat(0u);
v___x_2483_ = lean_array_get_size(v_rupHints_2475_);
v___x_2484_ = lean_nat_dec_lt(v___x_2482_, v___x_2483_);
if (v___x_2484_ == 0)
{
v___y_2460_ = v_acc_2481_;
goto v___jp_2459_;
}
else
{
size_t v___x_2485_; size_t v___x_2486_; lean_object* v___x_2487_; 
v___x_2485_ = ((size_t)0ULL);
v___x_2486_ = lean_usize_of_nat(v___x_2483_);
v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2475_, v___x_2485_, v___x_2486_, v_acc_2481_);
v___y_2460_ = v___x_2487_;
goto v___jp_2459_;
}
}
case 1:
{
lean_object* v_id_2488_; lean_object* v_c_2489_; lean_object* v_rupHints_2490_; uint8_t v___x_2491_; lean_object* v_acc_2492_; lean_object* v___x_2493_; lean_object* v_acc_2494_; lean_object* v___x_2495_; lean_object* v___y_2497_; lean_object* v___x_2505_; uint8_t v___x_2506_; 
v_id_2488_ = lean_ctor_get(v___x_2473_, 0);
v_c_2489_ = lean_ctor_get(v___x_2473_, 1);
v_rupHints_2490_ = lean_ctor_get(v___x_2473_, 2);
v___x_2491_ = 97;
v_acc_2492_ = lean_byte_array_push(v_acc_2449_, v___x_2491_);
lean_inc(v_id_2488_);
v___x_2493_ = lean_nat_to_int(v_id_2488_);
v_acc_2494_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2492_, v___x_2493_);
lean_dec(v___x_2493_);
v___x_2495_ = lean_unsigned_to_nat(0u);
v___x_2505_ = lean_array_get_size(v_c_2489_);
v___x_2506_ = lean_nat_dec_lt(v___x_2495_, v___x_2505_);
if (v___x_2506_ == 0)
{
v___y_2497_ = v_acc_2494_;
goto v___jp_2496_;
}
else
{
size_t v___x_2507_; size_t v___x_2508_; lean_object* v___x_2509_; 
v___x_2507_ = ((size_t)0ULL);
v___x_2508_ = lean_usize_of_nat(v___x_2505_);
v___x_2509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2489_, v___x_2507_, v___x_2508_, v_acc_2494_);
v___y_2497_ = v___x_2509_;
goto v___jp_2496_;
}
v___jp_2496_:
{
uint8_t v___x_2498_; lean_object* v_acc_2499_; lean_object* v___x_2500_; uint8_t v___x_2501_; 
v___x_2498_ = 0;
v_acc_2499_ = lean_byte_array_push(v___y_2497_, v___x_2498_);
v___x_2500_ = lean_array_get_size(v_rupHints_2490_);
v___x_2501_ = lean_nat_dec_lt(v___x_2495_, v___x_2500_);
if (v___x_2501_ == 0)
{
v___y_2464_ = v_acc_2499_;
goto v___jp_2463_;
}
else
{
size_t v___x_2502_; size_t v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = ((size_t)0ULL);
v___x_2503_ = lean_usize_of_nat(v___x_2500_);
v___x_2504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2490_, v___x_2502_, v___x_2503_, v_acc_2499_);
v___y_2464_ = v___x_2504_;
goto v___jp_2463_;
}
}
}
case 2:
{
lean_object* v_id_2510_; lean_object* v_c_2511_; lean_object* v_rupHints_2512_; lean_object* v_ratHints_2513_; uint8_t v___x_2514_; lean_object* v_acc_2515_; lean_object* v___x_2516_; lean_object* v_acc_2517_; lean_object* v___x_2518_; lean_object* v___y_2520_; lean_object* v___y_2527_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v_id_2510_ = lean_ctor_get(v___x_2473_, 0);
v_c_2511_ = lean_ctor_get(v___x_2473_, 1);
v_rupHints_2512_ = lean_ctor_get(v___x_2473_, 3);
v_ratHints_2513_ = lean_ctor_get(v___x_2473_, 4);
v___x_2514_ = 97;
v_acc_2515_ = lean_byte_array_push(v_acc_2449_, v___x_2514_);
lean_inc(v_id_2510_);
v___x_2516_ = lean_nat_to_int(v_id_2510_);
v_acc_2517_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2515_, v___x_2516_);
lean_dec(v___x_2516_);
v___x_2518_ = lean_unsigned_to_nat(0u);
v___x_2535_ = lean_array_get_size(v_c_2511_);
v___x_2536_ = lean_nat_dec_lt(v___x_2518_, v___x_2535_);
if (v___x_2536_ == 0)
{
v___y_2527_ = v_acc_2517_;
goto v___jp_2526_;
}
else
{
size_t v___x_2537_; size_t v___x_2538_; lean_object* v___x_2539_; 
v___x_2537_ = ((size_t)0ULL);
v___x_2538_ = lean_usize_of_nat(v___x_2535_);
v___x_2539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2511_, v___x_2537_, v___x_2538_, v_acc_2517_);
v___y_2527_ = v___x_2539_;
goto v___jp_2526_;
}
v___jp_2519_:
{
lean_object* v___x_2521_; uint8_t v___x_2522_; 
v___x_2521_ = lean_array_get_size(v_ratHints_2513_);
v___x_2522_ = lean_nat_dec_lt(v___x_2518_, v___x_2521_);
if (v___x_2522_ == 0)
{
v___y_2456_ = v___y_2520_;
goto v___jp_2455_;
}
else
{
size_t v___x_2523_; size_t v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = ((size_t)0ULL);
v___x_2524_ = lean_usize_of_nat(v___x_2521_);
v___x_2525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_ratHints_2513_, v___x_2523_, v___x_2524_, v___y_2520_);
v___y_2456_ = v___x_2525_;
goto v___jp_2455_;
}
}
v___jp_2526_:
{
uint8_t v___x_2528_; lean_object* v_acc_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v___x_2528_ = 0;
v_acc_2529_ = lean_byte_array_push(v___y_2527_, v___x_2528_);
v___x_2530_ = lean_array_get_size(v_rupHints_2512_);
v___x_2531_ = lean_nat_dec_lt(v___x_2518_, v___x_2530_);
if (v___x_2531_ == 0)
{
v___y_2520_ = v_acc_2529_;
goto v___jp_2519_;
}
else
{
size_t v___x_2532_; size_t v___x_2533_; lean_object* v___x_2534_; 
v___x_2532_ = ((size_t)0ULL);
v___x_2533_ = lean_usize_of_nat(v___x_2530_);
v___x_2534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2512_, v___x_2532_, v___x_2533_, v_acc_2529_);
v___y_2520_ = v___x_2534_;
goto v___jp_2519_;
}
}
}
default: 
{
lean_object* v_ids_2540_; uint8_t v___x_2541_; lean_object* v_acc_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v_ids_2540_ = lean_ctor_get(v___x_2473_, 0);
v___x_2541_ = 100;
v_acc_2542_ = lean_byte_array_push(v_acc_2449_, v___x_2541_);
v___x_2543_ = lean_unsigned_to_nat(0u);
v___x_2544_ = lean_array_get_size(v_ids_2540_);
v___x_2545_ = lean_nat_dec_lt(v___x_2543_, v___x_2544_);
if (v___x_2545_ == 0)
{
v___y_2468_ = v_acc_2542_;
goto v___jp_2467_;
}
else
{
size_t v___x_2546_; size_t v___x_2547_; lean_object* v___x_2548_; 
v___x_2546_ = ((size_t)0ULL);
v___x_2547_ = lean_usize_of_nat(v___x_2544_);
v___x_2548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_ids_2540_, v___x_2546_, v___x_2547_, v_acc_2542_);
v___y_2468_ = v___x_2548_;
goto v___jp_2467_;
}
}
}
}
v___jp_2450_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_unsigned_to_nat(1u);
v___x_2453_ = lean_nat_add(v_idx_2448_, v___x_2452_);
lean_dec(v_idx_2448_);
v_idx_2448_ = v___x_2453_;
v_acc_2449_ = v___y_2451_;
goto _start;
}
v___jp_2455_:
{
uint8_t v___x_2457_; lean_object* v_acc_2458_; 
v___x_2457_ = 0;
v_acc_2458_ = lean_byte_array_push(v___y_2456_, v___x_2457_);
v___y_2451_ = v_acc_2458_;
goto v___jp_2450_;
}
v___jp_2459_:
{
uint8_t v___x_2461_; lean_object* v_acc_2462_; 
v___x_2461_ = 0;
v_acc_2462_ = lean_byte_array_push(v___y_2460_, v___x_2461_);
v___y_2451_ = v_acc_2462_;
goto v___jp_2450_;
}
v___jp_2463_:
{
uint8_t v___x_2465_; lean_object* v_acc_2466_; 
v___x_2465_ = 0;
v_acc_2466_ = lean_byte_array_push(v___y_2464_, v___x_2465_);
v___y_2451_ = v_acc_2466_;
goto v___jp_2450_;
}
v___jp_2467_:
{
uint8_t v___x_2469_; lean_object* v_acc_2470_; 
v___x_2469_ = 0;
v_acc_2470_ = lean_byte_array_push(v___y_2468_, v___x_2469_);
v___y_2451_ = v_acc_2470_;
goto v___jp_2450_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___boxed(lean_object* v_proof_2549_, lean_object* v_idx_2550_, lean_object* v_acc_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(v_proof_2549_, v_idx_2550_, v_acc_2551_);
lean_dec_ref(v_proof_2549_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(lean_object* v_proof_2553_){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2554_ = lean_unsigned_to_nat(0u);
v___x_2555_ = lean_unsigned_to_nat(4u);
v___x_2556_ = lean_array_get_size(v_proof_2553_);
v___x_2557_ = lean_nat_mul(v___x_2555_, v___x_2556_);
v___x_2558_ = lean_mk_empty_byte_array(v___x_2557_);
lean_dec(v___x_2557_);
v___x_2559_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(v_proof_2553_, v___x_2554_, v___x_2558_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary___boxed(lean_object* v_proof_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(v_proof_2560_);
lean_dec_ref(v_proof_2560_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object* v_path_2562_, lean_object* v_proof_2563_, uint8_t v_binaryProofs_2564_){
_start:
{
if (v_binaryProofs_2564_ == 0)
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2566_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_proof_2563_);
v___x_2567_ = lean_string_to_utf8(v___x_2566_);
v___x_2568_ = l_IO_FS_writeBinFile(v_path_2562_, v___x_2567_);
lean_dec_ref(v___x_2567_);
return v___x_2568_;
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(v_proof_2563_);
v___x_2570_ = l_IO_FS_writeBinFile(v_path_2562_, v___x_2569_);
lean_dec_ref(v___x_2569_);
return v___x_2570_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof___boxed(lean_object* v_path_2571_, lean_object* v_proof_2572_, lean_object* v_binaryProofs_2573_, lean_object* v_a_2574_){
_start:
{
uint8_t v_binaryProofs_boxed_2575_; lean_object* v_res_2576_; 
v_binaryProofs_boxed_2575_ = lean_unbox(v_binaryProofs_2573_);
v_res_2576_ = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(v_path_2571_, v_proof_2572_, v_binaryProofs_boxed_2575_);
lean_dec_ref(v_proof_2572_);
lean_dec_ref(v_path_2571_);
return v_res_2576_;
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
