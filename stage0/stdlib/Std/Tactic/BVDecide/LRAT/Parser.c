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
if (v___x_463_ == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_box(0);
v___x_470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_470_, 0, v_a_456_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
return v___x_470_;
}
else
{
uint8_t v___x_471_; uint8_t v___x_472_; 
v___x_471_ = 48;
v___x_472_ = lean_uint8_dec_le(v___x_471_, v___x_466_);
if (v___x_472_ == 0)
{
goto v___jp_457_;
}
else
{
uint8_t v___x_473_; uint8_t v___x_474_; 
v___x_473_ = 57;
v___x_474_ = lean_uint8_dec_le(v___x_466_, v___x_473_);
if (v___x_474_ == 0)
{
goto v___jp_457_;
}
else
{
lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_504_; 
lean_inc(v_idx_461_);
lean_inc_ref(v_array_460_);
v_isSharedCheck_504_ = !lean_is_exclusive(v_a_456_);
if (v_isSharedCheck_504_ == 0)
{
lean_object* v_unused_505_; lean_object* v_unused_506_; 
v_unused_505_ = lean_ctor_get(v_a_456_, 1);
lean_dec(v_unused_505_);
v_unused_506_ = lean_ctor_get(v_a_456_, 0);
lean_dec(v_unused_506_);
v___x_476_ = v_a_456_;
v_isShared_477_ = v_isSharedCheck_504_;
goto v_resetjp_475_;
}
else
{
lean_dec(v_a_456_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_504_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v_it_x27_481_; 
v___x_478_ = lean_unsigned_to_nat(1u);
v___x_479_ = lean_nat_add(v_idx_461_, v___x_478_);
lean_dec(v_idx_461_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 1, v___x_479_);
v_it_x27_481_ = v___x_476_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_array_460_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v___x_479_);
v_it_x27_481_ = v_reuseFailAlloc_503_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
uint32_t v___x_482_; uint8_t v___x_483_; uint8_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v_fst_487_; lean_object* v_snd_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_502_; 
v___x_482_ = lean_uint8_to_uint32(v___x_466_);
v___x_483_ = lean_uint32_to_uint8(v___x_482_);
v___x_484_ = lean_uint8_sub(v___x_483_, v___x_471_);
v___x_485_ = lean_uint8_to_nat(v___x_484_);
v___x_486_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_481_, v___x_485_);
v_fst_487_ = lean_ctor_get(v___x_486_, 0);
v_snd_488_ = lean_ctor_get(v___x_486_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_502_ == 0)
{
v___x_490_ = v___x_486_;
v_isShared_491_ = v_isSharedCheck_502_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_snd_488_);
lean_inc(v_fst_487_);
lean_dec(v___x_486_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_502_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_492_ = lean_unsigned_to_nat(0u);
v___x_493_ = lean_nat_dec_eq(v_fst_487_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_494_ = lean_nat_to_int(v_fst_487_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 1, v___x_494_);
lean_ctor_set(v___x_490_, 0, v_snd_488_);
v___x_496_ = v___x_490_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_snd_488_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
else
{
lean_object* v___x_498_; lean_object* v___x_500_; 
lean_dec(v_fst_487_);
v___x_498_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_491_ == 0)
{
lean_ctor_set_tag(v___x_490_, 1);
lean_ctor_set(v___x_490_, 1, v___x_498_);
lean_ctor_set(v___x_490_, 0, v_snd_488_);
v___x_500_ = v___x_490_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_snd_488_);
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
}
}
else
{
if (v___x_463_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_box(0);
v___x_508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_508_, 0, v_a_456_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
return v___x_508_;
}
else
{
if (v___x_468_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1));
v___x_510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_510_, 0, v_a_456_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
return v___x_510_;
}
else
{
lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_554_; 
lean_inc(v_idx_461_);
lean_inc_ref(v_array_460_);
v_isSharedCheck_554_ = !lean_is_exclusive(v_a_456_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; lean_object* v_unused_556_; 
v_unused_555_ = lean_ctor_get(v_a_456_, 1);
lean_dec(v_unused_555_);
v_unused_556_ = lean_ctor_get(v_a_456_, 0);
lean_dec(v_unused_556_);
v___x_512_ = v_a_456_;
v_isShared_513_ = v_isSharedCheck_554_;
goto v_resetjp_511_;
}
else
{
lean_dec(v_a_456_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_554_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = lean_nat_add(v_idx_461_, v___x_514_);
lean_dec(v_idx_461_);
lean_inc(v___x_515_);
lean_inc_ref(v_array_460_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v___x_515_);
v___x_517_ = v___x_512_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_array_460_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v___x_515_);
v___x_517_ = v_reuseFailAlloc_553_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
uint8_t v___x_521_; 
v___x_521_ = lean_nat_dec_lt(v___x_515_, v___x_462_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec(v___x_515_);
lean_dec_ref(v_array_460_);
v___x_522_ = lean_box(0);
v___x_523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_517_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
return v___x_523_;
}
else
{
uint8_t v_c_524_; uint8_t v___x_525_; uint8_t v___x_526_; 
v_c_524_ = lean_byte_array_fget(v_array_460_, v___x_515_);
v___x_525_ = 48;
v___x_526_ = lean_uint8_dec_le(v___x_525_, v_c_524_);
if (v___x_526_ == 0)
{
lean_dec(v___x_515_);
lean_dec_ref(v_array_460_);
goto v___jp_518_;
}
else
{
uint8_t v___x_527_; uint8_t v___x_528_; 
v___x_527_ = 57;
v___x_528_ = lean_uint8_dec_le(v_c_524_, v___x_527_);
if (v___x_528_ == 0)
{
lean_dec(v___x_515_);
lean_dec_ref(v_array_460_);
goto v___jp_518_;
}
else
{
lean_object* v___x_529_; lean_object* v_it_x27_530_; uint32_t v___x_531_; uint8_t v___x_532_; uint8_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v_fst_536_; lean_object* v_snd_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_552_; 
lean_dec_ref(v___x_517_);
v___x_529_ = lean_nat_add(v___x_515_, v___x_514_);
lean_dec(v___x_515_);
v_it_x27_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_530_, 0, v_array_460_);
lean_ctor_set(v_it_x27_530_, 1, v___x_529_);
v___x_531_ = lean_uint8_to_uint32(v_c_524_);
v___x_532_ = lean_uint32_to_uint8(v___x_531_);
v___x_533_ = lean_uint8_sub(v___x_532_, v___x_525_);
v___x_534_ = lean_uint8_to_nat(v___x_533_);
v___x_535_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_530_, v___x_534_);
v_fst_536_ = lean_ctor_get(v___x_535_, 0);
v_snd_537_ = lean_ctor_get(v___x_535_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_552_ == 0)
{
v___x_539_ = v___x_535_;
v_isShared_540_ = v_isSharedCheck_552_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_snd_537_);
lean_inc(v_fst_536_);
lean_dec(v___x_535_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_552_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = lean_nat_dec_eq(v_fst_536_, v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_543_ = lean_nat_to_int(v_fst_536_);
v___x_544_ = lean_int_neg(v___x_543_);
lean_dec(v___x_543_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_544_);
lean_ctor_set(v___x_539_, 0, v_snd_537_);
v___x_546_ = v___x_539_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_snd_537_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_550_; 
lean_dec(v_fst_536_);
v___x_548_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_540_ == 0)
{
lean_ctor_set_tag(v___x_539_, 1);
lean_ctor_set(v___x_539_, 1, v___x_548_);
lean_ctor_set(v___x_539_, 0, v_snd_537_);
v___x_550_ = v___x_539_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_snd_537_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
}
v___jp_518_:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_517_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
return v___x_520_;
}
}
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_litWs(lean_object* v_a_557_){
_start:
{
lean_object* v_pos_559_; lean_object* v_res_560_; lean_object* v_array_590_; lean_object* v_idx_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_array_590_ = lean_ctor_get(v_a_557_, 0);
v_idx_591_ = lean_ctor_get(v_a_557_, 1);
v___x_592_ = lean_byte_array_size(v_array_590_);
v___x_593_ = lean_nat_dec_lt(v_idx_591_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_box(0);
v___x_595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_595_, 0, v_a_557_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
return v___x_595_;
}
else
{
uint8_t v___x_596_; uint8_t v___x_597_; uint8_t v___x_598_; 
v___x_596_ = lean_byte_array_fget(v_array_590_, v_idx_591_);
v___x_597_ = 45;
v___x_598_ = lean_uint8_dec_eq(v___x_596_, v___x_597_);
if (v___x_598_ == 0)
{
uint8_t v___x_599_; uint8_t v___x_600_; 
v___x_599_ = 48;
v___x_600_ = lean_uint8_dec_le(v___x_599_, v___x_596_);
if (v___x_600_ == 0)
{
goto v___jp_584_;
}
else
{
uint8_t v___x_601_; uint8_t v___x_602_; 
v___x_601_ = 57;
v___x_602_ = lean_uint8_dec_le(v___x_596_, v___x_601_);
if (v___x_602_ == 0)
{
goto v___jp_584_;
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v_it_x27_605_; uint32_t v___x_606_; uint8_t v___x_607_; uint8_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v_fst_611_; lean_object* v_snd_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_623_; 
v___x_603_ = lean_unsigned_to_nat(1u);
v___x_604_ = lean_nat_add(v_idx_591_, v___x_603_);
lean_inc_ref(v_array_590_);
v_it_x27_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_605_, 0, v_array_590_);
lean_ctor_set(v_it_x27_605_, 1, v___x_604_);
v___x_606_ = lean_uint8_to_uint32(v___x_596_);
v___x_607_ = lean_uint32_to_uint8(v___x_606_);
v___x_608_ = lean_uint8_sub(v___x_607_, v___x_599_);
v___x_609_ = lean_uint8_to_nat(v___x_608_);
v___x_610_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_605_, v___x_609_);
v_fst_611_ = lean_ctor_get(v___x_610_, 0);
v_snd_612_ = lean_ctor_get(v___x_610_, 1);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_623_ == 0)
{
v___x_614_ = v___x_610_;
v_isShared_615_ = v_isSharedCheck_623_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_snd_612_);
lean_inc(v_fst_611_);
lean_dec(v___x_610_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_623_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = lean_nat_dec_eq(v_fst_611_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
lean_del_object(v___x_614_);
lean_dec_ref(v_a_557_);
v___x_618_ = lean_nat_to_int(v_fst_611_);
v_pos_559_ = v_snd_612_;
v_res_560_ = v___x_618_;
goto v___jp_558_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_621_; 
lean_dec(v_snd_612_);
lean_dec(v_fst_611_);
v___x_619_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_615_ == 0)
{
lean_ctor_set_tag(v___x_614_, 1);
lean_ctor_set(v___x_614_, 1, v___x_619_);
lean_ctor_set(v___x_614_, 0, v_a_557_);
v___x_621_ = v___x_614_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_557_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = lean_nat_add(v_idx_591_, v___x_624_);
v___x_626_ = lean_nat_dec_lt(v___x_625_, v___x_592_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; 
lean_dec(v___x_625_);
v___x_627_ = lean_box(0);
v___x_628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_628_, 0, v_a_557_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
return v___x_628_;
}
else
{
uint8_t v_c_629_; uint8_t v___x_630_; uint8_t v___x_631_; 
v_c_629_ = lean_byte_array_fget(v_array_590_, v___x_625_);
v___x_630_ = 48;
v___x_631_ = lean_uint8_dec_le(v___x_630_, v_c_629_);
if (v___x_631_ == 0)
{
lean_dec(v___x_625_);
goto v___jp_587_;
}
else
{
uint8_t v___x_632_; uint8_t v___x_633_; 
v___x_632_ = 57;
v___x_633_ = lean_uint8_dec_le(v_c_629_, v___x_632_);
if (v___x_633_ == 0)
{
lean_dec(v___x_625_);
goto v___jp_587_;
}
else
{
lean_object* v___x_634_; lean_object* v_it_x27_635_; uint32_t v___x_636_; uint8_t v___x_637_; uint8_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v_fst_641_; lean_object* v_snd_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_654_; 
v___x_634_ = lean_nat_add(v___x_625_, v___x_624_);
lean_dec(v___x_625_);
lean_inc_ref(v_array_590_);
v_it_x27_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_635_, 0, v_array_590_);
lean_ctor_set(v_it_x27_635_, 1, v___x_634_);
v___x_636_ = lean_uint8_to_uint32(v_c_629_);
v___x_637_ = lean_uint32_to_uint8(v___x_636_);
v___x_638_ = lean_uint8_sub(v___x_637_, v___x_630_);
v___x_639_ = lean_uint8_to_nat(v___x_638_);
v___x_640_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_635_, v___x_639_);
v_fst_641_ = lean_ctor_get(v___x_640_, 0);
v_snd_642_ = lean_ctor_get(v___x_640_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_654_ == 0)
{
v___x_644_ = v___x_640_;
v_isShared_645_ = v_isSharedCheck_654_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_snd_642_);
lean_inc(v_fst_641_);
lean_dec(v___x_640_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_654_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = lean_nat_dec_eq(v_fst_641_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; 
lean_del_object(v___x_644_);
lean_dec_ref(v_a_557_);
v___x_648_ = lean_nat_to_int(v_fst_641_);
v___x_649_ = lean_int_neg(v___x_648_);
lean_dec(v___x_648_);
v_pos_559_ = v_snd_642_;
v_res_560_ = v___x_649_;
goto v___jp_558_;
}
else
{
lean_object* v___x_650_; lean_object* v___x_652_; 
lean_dec(v_snd_642_);
lean_dec(v_fst_641_);
v___x_650_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_645_ == 0)
{
lean_ctor_set_tag(v___x_644_, 1);
lean_ctor_set(v___x_644_, 1, v___x_650_);
lean_ctor_set(v___x_644_, 0, v_a_557_);
v___x_652_ = v___x_644_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_557_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
}
}
}
v___jp_558_:
{
lean_object* v_array_561_; lean_object* v_idx_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_array_561_ = lean_ctor_get(v_pos_559_, 0);
v_idx_562_ = lean_ctor_get(v_pos_559_, 1);
v___x_563_ = lean_byte_array_size(v_array_561_);
v___x_564_ = lean_nat_dec_lt(v_idx_562_, v___x_563_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v_res_560_);
v___x_565_ = lean_box(0);
v___x_566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_566_, 0, v_pos_559_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
return v___x_566_;
}
else
{
uint8_t v___x_567_; uint8_t v_got_568_; uint8_t v___x_569_; 
v___x_567_ = 32;
v_got_568_ = lean_byte_array_fget(v_array_561_, v_idx_562_);
v___x_569_ = lean_uint8_dec_eq(v_got_568_, v___x_567_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v_res_560_);
v___x_570_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
v___x_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_571_, 0, v_pos_559_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
return v___x_571_;
}
else
{
lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_581_; 
lean_inc(v_idx_562_);
lean_inc_ref(v_array_561_);
v_isSharedCheck_581_ = !lean_is_exclusive(v_pos_559_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; lean_object* v_unused_583_; 
v_unused_582_ = lean_ctor_get(v_pos_559_, 1);
lean_dec(v_unused_582_);
v_unused_583_ = lean_ctor_get(v_pos_559_, 0);
lean_dec(v_unused_583_);
v___x_573_ = v_pos_559_;
v_isShared_574_ = v_isSharedCheck_581_;
goto v_resetjp_572_;
}
else
{
lean_dec(v_pos_559_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_581_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_575_ = lean_unsigned_to_nat(1u);
v___x_576_ = lean_nat_add(v_idx_562_, v___x_575_);
lean_dec(v_idx_562_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 1, v___x_576_);
v___x_578_ = v___x_573_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_array_561_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v___x_576_);
v___x_578_ = v_reuseFailAlloc_580_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; 
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v_res_560_);
return v___x_579_;
}
}
}
}
}
v___jp_584_:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_586_, 0, v_a_557_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
return v___x_586_;
}
v___jp_587_:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_589_, 0, v_a_557_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__0(lean_object* v_a_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = lean_nat_to_int(v_a_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__1(lean_object* v_acc_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_array_659_; lean_object* v_idx_660_; lean_object* v_pos_662_; lean_object* v_idx_663_; lean_object* v_err_664_; lean_object* v_pos_673_; lean_object* v_res_674_; lean_object* v___x_697_; uint8_t v___x_698_; 
v_array_659_ = lean_ctor_get(v_a_658_, 0);
v_idx_660_ = lean_ctor_get(v_a_658_, 1);
lean_inc(v_idx_660_);
v___x_697_ = lean_byte_array_size(v_array_659_);
v___x_698_ = lean_nat_dec_lt(v_idx_660_, v___x_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; 
v___x_699_ = lean_box(0);
lean_inc(v_idx_660_);
v_pos_662_ = v_a_658_;
v_idx_663_ = v_idx_660_;
v_err_664_ = v___x_699_;
goto v___jp_661_;
}
else
{
uint8_t v___x_700_; uint8_t v___x_701_; uint8_t v___x_702_; 
v___x_700_ = lean_byte_array_fget(v_array_659_, v_idx_660_);
v___x_701_ = 45;
v___x_702_ = lean_uint8_dec_eq(v___x_700_, v___x_701_);
if (v___x_702_ == 0)
{
uint8_t v___x_703_; uint8_t v___x_704_; 
v___x_703_ = 48;
v___x_704_ = lean_uint8_dec_le(v___x_703_, v___x_700_);
if (v___x_704_ == 0)
{
goto v___jp_670_;
}
else
{
uint8_t v___x_705_; uint8_t v___x_706_; 
v___x_705_ = 57;
v___x_706_ = lean_uint8_dec_le(v___x_700_, v___x_705_);
if (v___x_706_ == 0)
{
goto v___jp_670_;
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v_it_x27_709_; uint32_t v___x_710_; uint8_t v___x_711_; uint8_t v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_fst_715_; lean_object* v_snd_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_707_ = lean_unsigned_to_nat(1u);
v___x_708_ = lean_nat_add(v_idx_660_, v___x_707_);
lean_inc_ref(v_array_659_);
v_it_x27_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_709_, 0, v_array_659_);
lean_ctor_set(v_it_x27_709_, 1, v___x_708_);
v___x_710_ = lean_uint8_to_uint32(v___x_700_);
v___x_711_ = lean_uint32_to_uint8(v___x_710_);
v___x_712_ = lean_uint8_sub(v___x_711_, v___x_703_);
v___x_713_ = lean_uint8_to_nat(v___x_712_);
v___x_714_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_709_, v___x_713_);
v_fst_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_fst_715_);
v_snd_716_ = lean_ctor_get(v___x_714_, 1);
lean_inc(v_snd_716_);
lean_dec_ref(v___x_714_);
v___x_717_ = lean_unsigned_to_nat(0u);
v___x_718_ = lean_nat_dec_eq(v_fst_715_, v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; 
lean_dec_ref(v_a_658_);
v___x_719_ = lean_nat_to_int(v_fst_715_);
v_pos_673_ = v_snd_716_;
v_res_674_ = v___x_719_;
goto v___jp_672_;
}
else
{
lean_object* v___x_720_; 
lean_dec(v_snd_716_);
lean_dec(v_fst_715_);
v___x_720_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
lean_inc(v_idx_660_);
v_pos_662_ = v_a_658_;
v_idx_663_ = v_idx_660_;
v_err_664_ = v___x_720_;
goto v___jp_661_;
}
}
}
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_721_ = lean_unsigned_to_nat(1u);
v___x_722_ = lean_nat_add(v_idx_660_, v___x_721_);
v___x_723_ = lean_nat_dec_lt(v___x_722_, v___x_697_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; 
lean_dec(v___x_722_);
v___x_724_ = lean_box(0);
lean_inc(v_idx_660_);
v_pos_662_ = v_a_658_;
v_idx_663_ = v_idx_660_;
v_err_664_ = v___x_724_;
goto v___jp_661_;
}
else
{
uint8_t v_c_725_; uint8_t v___x_726_; uint8_t v___x_727_; 
v_c_725_ = lean_byte_array_fget(v_array_659_, v___x_722_);
v___x_726_ = 48;
v___x_727_ = lean_uint8_dec_le(v___x_726_, v_c_725_);
if (v___x_727_ == 0)
{
lean_dec(v___x_722_);
goto v___jp_668_;
}
else
{
uint8_t v___x_728_; uint8_t v___x_729_; 
v___x_728_ = 57;
v___x_729_ = lean_uint8_dec_le(v_c_725_, v___x_728_);
if (v___x_729_ == 0)
{
lean_dec(v___x_722_);
goto v___jp_668_;
}
else
{
lean_object* v___x_730_; lean_object* v_it_x27_731_; uint32_t v___x_732_; uint8_t v___x_733_; uint8_t v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v_fst_737_; lean_object* v_snd_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_730_ = lean_nat_add(v___x_722_, v___x_721_);
lean_dec(v___x_722_);
lean_inc_ref(v_array_659_);
v_it_x27_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_731_, 0, v_array_659_);
lean_ctor_set(v_it_x27_731_, 1, v___x_730_);
v___x_732_ = lean_uint8_to_uint32(v_c_725_);
v___x_733_ = lean_uint32_to_uint8(v___x_732_);
v___x_734_ = lean_uint8_sub(v___x_733_, v___x_726_);
v___x_735_ = lean_uint8_to_nat(v___x_734_);
v___x_736_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_731_, v___x_735_);
v_fst_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_fst_737_);
v_snd_738_ = lean_ctor_get(v___x_736_, 1);
lean_inc(v_snd_738_);
lean_dec_ref(v___x_736_);
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_nat_dec_eq(v_fst_737_, v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; 
lean_dec_ref(v_a_658_);
v___x_741_ = lean_nat_to_int(v_fst_737_);
v___x_742_ = lean_int_neg(v___x_741_);
lean_dec(v___x_741_);
v_pos_673_ = v_snd_738_;
v_res_674_ = v___x_742_;
goto v___jp_672_;
}
else
{
lean_object* v___x_743_; 
lean_dec(v_snd_738_);
lean_dec(v_fst_737_);
v___x_743_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
lean_inc(v_idx_660_);
v_pos_662_ = v_a_658_;
v_idx_663_ = v_idx_660_;
v_err_664_ = v___x_743_;
goto v___jp_661_;
}
}
}
}
}
}
v___jp_661_:
{
uint8_t v___x_665_; 
v___x_665_ = lean_nat_dec_eq(v_idx_660_, v_idx_663_);
lean_dec(v_idx_663_);
lean_dec(v_idx_660_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
lean_dec_ref(v_acc_657_);
lean_inc(v_err_664_);
v___x_666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_666_, 0, v_pos_662_);
lean_ctor_set(v___x_666_, 1, v_err_664_);
return v___x_666_;
}
else
{
lean_object* v___x_667_; 
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v_pos_662_);
lean_ctor_set(v___x_667_, 1, v_acc_657_);
return v___x_667_;
}
}
v___jp_668_:
{
lean_object* v___x_669_; 
v___x_669_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
lean_inc(v_idx_660_);
v_pos_662_ = v_a_658_;
v_idx_663_ = v_idx_660_;
v_err_664_ = v___x_669_;
goto v___jp_661_;
}
v___jp_670_:
{
lean_object* v___x_671_; 
v___x_671_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
lean_inc(v_idx_660_);
v_pos_662_ = v_a_658_;
v_idx_663_ = v_idx_660_;
v_err_664_ = v___x_671_;
goto v___jp_661_;
}
v___jp_672_:
{
lean_object* v_array_675_; lean_object* v_idx_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v_array_675_ = lean_ctor_get(v_pos_673_, 0);
v_idx_676_ = lean_ctor_get(v_pos_673_, 1);
lean_inc(v_idx_676_);
v___x_677_ = lean_byte_array_size(v_array_675_);
v___x_678_ = lean_nat_dec_lt(v_idx_676_, v___x_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
lean_dec(v_res_674_);
v___x_679_ = lean_box(0);
v_pos_662_ = v_pos_673_;
v_idx_663_ = v_idx_676_;
v_err_664_ = v___x_679_;
goto v___jp_661_;
}
else
{
uint8_t v___x_680_; uint8_t v_got_681_; uint8_t v___x_682_; 
v___x_680_ = 32;
v_got_681_ = lean_byte_array_fget(v_array_675_, v_idx_676_);
v___x_682_ = lean_uint8_dec_eq(v_got_681_, v___x_680_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; 
lean_dec(v_res_674_);
v___x_683_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
v_pos_662_ = v_pos_673_;
v_idx_663_ = v_idx_676_;
v_err_664_ = v___x_683_;
goto v___jp_661_;
}
else
{
lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_694_; 
lean_inc_ref(v_array_675_);
lean_dec(v_idx_660_);
v_isSharedCheck_694_ = !lean_is_exclusive(v_pos_673_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; lean_object* v_unused_696_; 
v_unused_695_ = lean_ctor_get(v_pos_673_, 1);
lean_dec(v_unused_695_);
v_unused_696_ = lean_ctor_get(v_pos_673_, 0);
lean_dec(v_unused_696_);
v___x_685_ = v_pos_673_;
v_isShared_686_ = v_isSharedCheck_694_;
goto v_resetjp_684_;
}
else
{
lean_dec(v_pos_673_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_694_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = lean_nat_add(v_idx_676_, v___x_687_);
lean_dec(v_idx_676_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v___x_688_);
v___x_690_ = v___x_685_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_array_675_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v___x_688_);
v___x_690_ = v_reuseFailAlloc_693_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_691_; 
v___x_691_ = lean_array_push(v_acc_657_, v_res_674_);
v_acc_657_ = v___x_691_;
v_a_658_ = v___x_690_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(lean_object* v_a_746_){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0));
v___x_748_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__1(v___x_747_, v_a_746_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_pos_749_; lean_object* v_res_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_783_; 
v_pos_749_ = lean_ctor_get(v___x_748_, 0);
v_res_750_ = lean_ctor_get(v___x_748_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_783_ == 0)
{
v___x_752_ = v___x_748_;
v_isShared_753_ = v_isSharedCheck_783_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_res_750_);
lean_inc(v_pos_749_);
lean_dec(v___x_748_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_783_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v_array_754_; lean_object* v_idx_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v_array_754_ = lean_ctor_get(v_pos_749_, 0);
v_idx_755_ = lean_ctor_get(v_pos_749_, 1);
v___x_756_ = lean_byte_array_size(v_array_754_);
v___x_757_ = lean_nat_dec_lt(v_idx_755_, v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_760_; 
lean_dec(v_res_750_);
v___x_758_ = lean_box(0);
if (v_isShared_753_ == 0)
{
lean_ctor_set_tag(v___x_752_, 1);
lean_ctor_set(v___x_752_, 1, v___x_758_);
v___x_760_ = v___x_752_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_pos_749_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
else
{
uint8_t v___x_762_; uint8_t v_got_763_; uint8_t v___x_764_; 
v___x_762_ = 48;
v_got_763_ = lean_byte_array_fget(v_array_754_, v_idx_755_);
v___x_764_ = lean_uint8_dec_eq(v_got_763_, v___x_762_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_767_; 
lean_dec(v_res_750_);
v___x_765_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1));
if (v_isShared_753_ == 0)
{
lean_ctor_set_tag(v___x_752_, 1);
lean_ctor_set(v___x_752_, 1, v___x_765_);
v___x_767_ = v___x_752_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_pos_749_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
else
{
lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_780_; 
lean_inc(v_idx_755_);
lean_inc_ref(v_array_754_);
v_isSharedCheck_780_ = !lean_is_exclusive(v_pos_749_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; lean_object* v_unused_782_; 
v_unused_781_ = lean_ctor_get(v_pos_749_, 1);
lean_dec(v_unused_781_);
v_unused_782_ = lean_ctor_get(v_pos_749_, 0);
lean_dec(v_unused_782_);
v___x_770_ = v_pos_749_;
v_isShared_771_ = v_isSharedCheck_780_;
goto v_resetjp_769_;
}
else
{
lean_dec(v_pos_749_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_780_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_772_ = lean_unsigned_to_nat(1u);
v___x_773_ = lean_nat_add(v_idx_755_, v___x_772_);
lean_dec(v_idx_755_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v___x_773_);
v___x_775_ = v___x_770_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_array_754_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_773_);
v___x_775_ = v_reuseFailAlloc_779_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_777_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_775_);
v___x_777_ = v___x_752_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_res_750_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
}
}
else
{
return v___x_748_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(lean_object* v_a_784_){
_start:
{
lean_object* v_array_785_; lean_object* v_idx_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v_array_785_ = lean_ctor_get(v_a_784_, 0);
v_idx_786_ = lean_ctor_get(v_a_784_, 1);
v___x_787_ = lean_byte_array_size(v_array_785_);
v___x_788_ = lean_nat_dec_lt(v_idx_786_, v___x_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_box(0);
v___x_790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_790_, 0, v_a_784_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
return v___x_790_;
}
else
{
uint8_t v___x_791_; uint8_t v_got_792_; uint8_t v___x_793_; 
v___x_791_ = 45;
v_got_792_ = lean_byte_array_fget(v_array_785_, v_idx_786_);
v___x_793_ = lean_uint8_dec_eq(v_got_792_, v___x_791_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1));
v___x_795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_795_, 0, v_a_784_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
return v___x_795_;
}
else
{
lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_878_; 
lean_inc(v_idx_786_);
lean_inc_ref(v_array_785_);
v_isSharedCheck_878_ = !lean_is_exclusive(v_a_784_);
if (v_isSharedCheck_878_ == 0)
{
lean_object* v_unused_879_; lean_object* v_unused_880_; 
v_unused_879_ = lean_ctor_get(v_a_784_, 1);
lean_dec(v_unused_879_);
v_unused_880_ = lean_ctor_get(v_a_784_, 0);
lean_dec(v_unused_880_);
v___x_797_ = v_a_784_;
v_isShared_798_ = v_isSharedCheck_878_;
goto v_resetjp_796_;
}
else
{
lean_dec(v_a_784_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_878_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_799_ = lean_unsigned_to_nat(1u);
v___x_800_ = lean_nat_add(v_idx_786_, v___x_799_);
lean_dec(v_idx_786_);
lean_inc(v___x_800_);
lean_inc_ref(v_array_785_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v___x_800_);
v___x_802_ = v___x_797_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_array_785_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v___x_800_);
v___x_802_ = v_reuseFailAlloc_877_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
uint8_t v___x_806_; 
v___x_806_ = lean_nat_dec_lt(v___x_800_, v___x_787_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec(v___x_800_);
lean_dec_ref(v_array_785_);
v___x_807_ = lean_box(0);
v___x_808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_802_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
return v___x_808_;
}
else
{
uint8_t v_c_809_; uint8_t v___x_810_; uint8_t v___x_811_; 
v_c_809_ = lean_byte_array_fget(v_array_785_, v___x_800_);
v___x_810_ = 48;
v___x_811_ = lean_uint8_dec_le(v___x_810_, v_c_809_);
if (v___x_811_ == 0)
{
lean_dec(v___x_800_);
lean_dec_ref(v_array_785_);
goto v___jp_803_;
}
else
{
uint8_t v___x_812_; uint8_t v___x_813_; 
v___x_812_ = 57;
v___x_813_ = lean_uint8_dec_le(v_c_809_, v___x_812_);
if (v___x_813_ == 0)
{
lean_dec(v___x_800_);
lean_dec_ref(v_array_785_);
goto v___jp_803_;
}
else
{
lean_object* v___x_814_; lean_object* v_it_x27_815_; uint32_t v___x_816_; uint8_t v___x_817_; uint8_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v_fst_821_; lean_object* v_snd_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_876_; 
lean_dec_ref(v___x_802_);
v___x_814_ = lean_nat_add(v___x_800_, v___x_799_);
lean_dec(v___x_800_);
v_it_x27_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_815_, 0, v_array_785_);
lean_ctor_set(v_it_x27_815_, 1, v___x_814_);
v___x_816_ = lean_uint8_to_uint32(v_c_809_);
v___x_817_ = lean_uint32_to_uint8(v___x_816_);
v___x_818_ = lean_uint8_sub(v___x_817_, v___x_810_);
v___x_819_ = lean_uint8_to_nat(v___x_818_);
v___x_820_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_815_, v___x_819_);
v_fst_821_ = lean_ctor_get(v___x_820_, 0);
v_snd_822_ = lean_ctor_get(v___x_820_, 1);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_876_ == 0)
{
v___x_824_ = v___x_820_;
v_isShared_825_ = v_isSharedCheck_876_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_snd_822_);
lean_inc(v_fst_821_);
lean_dec(v___x_820_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_876_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_826_ = lean_unsigned_to_nat(0u);
v___x_827_ = lean_nat_dec_eq(v_fst_821_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v_array_828_; lean_object* v_idx_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v_array_828_ = lean_ctor_get(v_snd_822_, 0);
v_idx_829_ = lean_ctor_get(v_snd_822_, 1);
v___x_830_ = lean_byte_array_size(v_array_828_);
v___x_831_ = lean_nat_dec_lt(v_idx_829_, v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; 
lean_del_object(v___x_824_);
lean_dec(v_fst_821_);
v___x_832_ = lean_box(0);
v___x_833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_833_, 0, v_snd_822_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
return v___x_833_;
}
else
{
uint8_t v___x_834_; uint8_t v_got_835_; uint8_t v___x_836_; 
v___x_834_ = 32;
v_got_835_ = lean_byte_array_fget(v_array_828_, v_idx_829_);
v___x_836_ = lean_uint8_dec_eq(v_got_835_, v___x_834_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_838_; 
lean_del_object(v___x_824_);
lean_dec(v_fst_821_);
v___x_837_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
v___x_838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_838_, 0, v_snd_822_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
return v___x_838_;
}
else
{
lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_871_; 
lean_inc(v_idx_829_);
lean_inc_ref(v_array_828_);
v_isSharedCheck_871_ = !lean_is_exclusive(v_snd_822_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; lean_object* v_unused_873_; 
v_unused_872_ = lean_ctor_get(v_snd_822_, 1);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_snd_822_, 0);
lean_dec(v_unused_873_);
v___x_840_ = v_snd_822_;
v_isShared_841_ = v_isSharedCheck_871_;
goto v_resetjp_839_;
}
else
{
lean_dec(v_snd_822_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_871_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_842_ = lean_nat_add(v_idx_829_, v___x_799_);
lean_dec(v_idx_829_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v___x_842_);
v___x_844_ = v___x_840_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_array_828_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v___x_842_);
v___x_844_ = v_reuseFailAlloc_870_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_845_; 
v___x_845_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(v___x_844_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_pos_846_; lean_object* v_res_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_860_; 
v_pos_846_ = lean_ctor_get(v___x_845_, 0);
v_res_847_ = lean_ctor_get(v___x_845_, 1);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_860_ == 0)
{
v___x_849_ = v___x_845_;
v_isShared_850_ = v_isSharedCheck_860_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_res_847_);
lean_inc(v_pos_846_);
lean_dec(v___x_845_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_860_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_851_ = lean_nat_to_int(v_fst_821_);
v___x_852_ = lean_int_neg(v___x_851_);
lean_dec(v___x_851_);
v___x_853_ = lean_nat_abs(v___x_852_);
lean_dec(v___x_852_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 1, v_res_847_);
lean_ctor_set(v___x_824_, 0, v___x_853_);
v___x_855_ = v___x_824_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_res_847_);
v___x_855_ = v_reuseFailAlloc_859_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_857_; 
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 1, v___x_855_);
v___x_857_ = v___x_849_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_pos_846_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
else
{
lean_object* v_pos_861_; lean_object* v_err_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_del_object(v___x_824_);
lean_dec(v_fst_821_);
v_pos_861_ = lean_ctor_get(v___x_845_, 0);
v_err_862_ = lean_ctor_get(v___x_845_, 1);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_845_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_err_862_);
lean_inc(v_pos_861_);
lean_dec(v___x_845_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_pos_861_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_err_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
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
lean_object* v___x_874_; lean_object* v___x_875_; 
lean_del_object(v___x_824_);
lean_dec(v_fst_821_);
v___x_874_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
v___x_875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_875_, 0, v_snd_822_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
return v___x_875_;
}
}
}
}
}
v___jp_803_:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_802_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
return v___x_805_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(lean_object* v_acc_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_pos_884_; lean_object* v_err_885_; lean_object* v___x_900_; 
lean_inc_ref(v_a_882_);
v___x_900_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(v_a_882_);
if (lean_obj_tag(v___x_900_) == 0)
{
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_pos_901_; lean_object* v_res_902_; lean_object* v___x_903_; 
lean_dec_ref(v_a_882_);
v_pos_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_pos_901_);
v_res_902_ = lean_ctor_get(v___x_900_, 1);
lean_inc(v_res_902_);
lean_dec_ref_known(v___x_900_, 2);
v___x_903_ = lean_array_push(v_acc_881_, v_res_902_);
v_acc_881_ = v___x_903_;
v_a_882_ = v_pos_901_;
goto _start;
}
else
{
lean_object* v_pos_905_; lean_object* v_err_906_; 
v_pos_905_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_pos_905_);
v_err_906_ = lean_ctor_get(v___x_900_, 1);
lean_inc(v_err_906_);
lean_dec_ref_known(v___x_900_, 2);
v_pos_884_ = v_pos_905_;
v_err_885_ = v_err_906_;
goto v___jp_883_;
}
}
else
{
lean_object* v_err_907_; 
v_err_907_ = lean_ctor_get(v___x_900_, 1);
lean_inc(v_err_907_);
lean_dec_ref_known(v___x_900_, 2);
lean_inc_ref(v_a_882_);
v_pos_884_ = v_a_882_;
v_err_885_ = v_err_907_;
goto v___jp_883_;
}
v___jp_883_:
{
lean_object* v_idx_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_898_; 
v_idx_886_ = lean_ctor_get(v_a_882_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v_a_882_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v_a_882_, 0);
lean_dec(v_unused_899_);
v___x_888_ = v_a_882_;
v_isShared_889_ = v_isSharedCheck_898_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_idx_886_);
lean_dec(v_a_882_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_898_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v_idx_890_; uint8_t v___x_891_; 
v_idx_890_ = lean_ctor_get(v_pos_884_, 1);
v___x_891_ = lean_nat_dec_eq(v_idx_886_, v_idx_890_);
lean_dec(v_idx_886_);
if (v___x_891_ == 0)
{
lean_object* v___x_893_; 
lean_dec_ref(v_acc_881_);
if (v_isShared_889_ == 0)
{
lean_ctor_set_tag(v___x_888_, 1);
lean_ctor_set(v___x_888_, 1, v_err_885_);
lean_ctor_set(v___x_888_, 0, v_pos_884_);
v___x_893_ = v___x_888_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_pos_884_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_err_885_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
else
{
lean_object* v___x_896_; 
lean_dec(v_err_885_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v_acc_881_);
lean_ctor_set(v___x_888_, 0, v_pos_884_);
v___x_896_ = v___x_888_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_pos_884_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_acc_881_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(lean_object* v_ident_913_, lean_object* v_a_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(v_a_914_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_pos_916_; lean_object* v_res_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_1032_; 
v_pos_916_ = lean_ctor_get(v___x_915_, 0);
v_res_917_ = lean_ctor_get(v___x_915_, 1);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_919_ = v___x_915_;
v_isShared_920_ = v_isSharedCheck_1032_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_res_917_);
lean_inc(v_pos_916_);
lean_dec(v___x_915_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_1032_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v_array_921_; lean_object* v_idx_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v_array_921_ = lean_ctor_get(v_pos_916_, 0);
v_idx_922_ = lean_ctor_get(v_pos_916_, 1);
v___x_923_ = lean_byte_array_size(v_array_921_);
v___x_924_ = lean_nat_dec_lt(v_idx_922_, v___x_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_927_; 
lean_dec(v_res_917_);
lean_dec(v_ident_913_);
v___x_925_ = lean_box(0);
if (v_isShared_920_ == 0)
{
lean_ctor_set_tag(v___x_919_, 1);
lean_ctor_set(v___x_919_, 1, v___x_925_);
v___x_927_ = v___x_919_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_pos_916_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v___x_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
else
{
uint8_t v___x_929_; uint8_t v_got_930_; uint8_t v___x_931_; 
v___x_929_ = 32;
v_got_930_ = lean_byte_array_fget(v_array_921_, v_idx_922_);
v___x_931_ = lean_uint8_dec_eq(v_got_930_, v___x_929_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_934_; 
lean_dec(v_res_917_);
lean_dec(v_ident_913_);
v___x_932_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
if (v_isShared_920_ == 0)
{
lean_ctor_set_tag(v___x_919_, 1);
lean_ctor_set(v___x_919_, 1, v___x_932_);
v___x_934_ = v___x_919_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_pos_916_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
else
{
lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_1029_; 
lean_inc(v_idx_922_);
lean_inc_ref(v_array_921_);
lean_del_object(v___x_919_);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_pos_916_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; lean_object* v_unused_1031_; 
v_unused_1030_ = lean_ctor_get(v_pos_916_, 1);
lean_dec(v_unused_1030_);
v_unused_1031_ = lean_ctor_get(v_pos_916_, 0);
lean_dec(v_unused_1031_);
v___x_937_ = v_pos_916_;
v_isShared_938_ = v_isSharedCheck_1029_;
goto v_resetjp_936_;
}
else
{
lean_dec(v_pos_916_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_1029_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_nat_add(v_idx_922_, v___x_939_);
lean_dec(v_idx_922_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 1, v___x_940_);
v___x_942_ = v___x_937_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_array_921_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v___x_940_);
v___x_942_ = v_reuseFailAlloc_1028_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; 
v___x_943_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(v___x_942_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_pos_944_; lean_object* v_res_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_pos_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_pos_944_);
v_res_945_ = lean_ctor_get(v___x_943_, 1);
lean_inc(v_res_945_);
lean_dec_ref_known(v___x_943_, 2);
v___x_946_ = lean_unsigned_to_nat(0u);
v___x_947_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0));
v___x_948_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(v___x_947_, v_pos_944_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_pos_949_; lean_object* v_res_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_1009_; 
v_pos_949_ = lean_ctor_get(v___x_948_, 0);
v_res_950_ = lean_ctor_get(v___x_948_, 1);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_952_ = v___x_948_;
v_isShared_953_ = v_isSharedCheck_1009_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_res_950_);
lean_inc(v_pos_949_);
lean_dec(v___x_948_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_1009_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v_array_954_; lean_object* v_idx_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v_array_954_ = lean_ctor_get(v_pos_949_, 0);
v_idx_955_ = lean_ctor_get(v_pos_949_, 1);
v___x_956_ = lean_byte_array_size(v_array_954_);
v___x_957_ = lean_nat_dec_lt(v_idx_955_, v___x_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_960_; 
lean_dec(v_res_950_);
lean_dec(v_res_945_);
lean_dec(v_res_917_);
lean_dec(v_ident_913_);
v___x_958_ = lean_box(0);
if (v_isShared_953_ == 0)
{
lean_ctor_set_tag(v___x_952_, 1);
lean_ctor_set(v___x_952_, 1, v___x_958_);
v___x_960_ = v___x_952_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_pos_949_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v___x_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
else
{
uint8_t v___x_962_; uint8_t v_got_963_; uint8_t v___x_964_; 
v___x_962_ = 48;
v_got_963_ = lean_byte_array_fget(v_array_954_, v_idx_955_);
v___x_964_ = lean_uint8_dec_eq(v_got_963_, v___x_962_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_967_; 
lean_dec(v_res_950_);
lean_dec(v_res_945_);
lean_dec(v_res_917_);
lean_dec(v_ident_913_);
v___x_965_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1));
if (v_isShared_953_ == 0)
{
lean_ctor_set_tag(v___x_952_, 1);
lean_ctor_set(v___x_952_, 1, v___x_965_);
v___x_967_ = v___x_952_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_pos_949_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
else
{
lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_1006_; 
lean_inc(v_idx_955_);
lean_inc_ref(v_array_954_);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_pos_949_);
if (v_isSharedCheck_1006_ == 0)
{
lean_object* v_unused_1007_; lean_object* v_unused_1008_; 
v_unused_1007_ = lean_ctor_get(v_pos_949_, 1);
lean_dec(v_unused_1007_);
v_unused_1008_ = lean_ctor_get(v_pos_949_, 0);
lean_dec(v_unused_1008_);
v___x_970_ = v_pos_949_;
v_isShared_971_ = v_isSharedCheck_1006_;
goto v_resetjp_969_;
}
else
{
lean_dec(v_pos_949_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_1006_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_972_ = lean_nat_add(v_idx_955_, v___x_939_);
lean_dec(v_idx_955_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_972_);
v___x_974_ = v___x_970_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_array_954_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v___x_972_);
v___x_974_ = v_reuseFailAlloc_1005_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_975_ = lean_array_get_size(v_res_917_);
v___x_976_ = lean_nat_dec_eq(v___x_975_, v___x_946_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_977_ = lean_array_get_size(v_res_950_);
v___x_978_ = lean_nat_dec_eq(v___x_977_, v___x_946_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_979_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_917_);
v___x_980_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_980_, 0, v_ident_913_);
lean_ctor_set(v___x_980_, 1, v_res_917_);
lean_ctor_set(v___x_980_, 2, v___x_979_);
lean_ctor_set(v___x_980_, 3, v_res_945_);
lean_ctor_set(v___x_980_, 4, v_res_950_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v___x_980_);
lean_ctor_set(v___x_952_, 0, v___x_974_);
v___x_982_ = v___x_952_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
else
{
lean_object* v___x_984_; uint8_t v___x_985_; 
lean_dec(v_res_950_);
v___x_984_ = lean_array_get_size(v_res_945_);
v___x_985_ = lean_nat_dec_eq(v___x_984_, v___x_946_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_986_, 0, v_ident_913_);
lean_ctor_set(v___x_986_, 1, v_res_917_);
lean_ctor_set(v___x_986_, 2, v_res_945_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v___x_986_);
lean_ctor_set(v___x_952_, 0, v___x_974_);
v___x_988_ = v___x_952_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
lean_dec(v_res_945_);
v___x_990_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_917_);
v___x_991_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_991_, 0, v_ident_913_);
lean_ctor_set(v___x_991_, 1, v_res_917_);
lean_ctor_set(v___x_991_, 2, v___x_990_);
lean_ctor_set(v___x_991_, 3, v___x_947_);
lean_ctor_set(v___x_991_, 4, v___x_947_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v___x_991_);
lean_ctor_set(v___x_952_, 0, v___x_974_);
v___x_993_ = v___x_952_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_object* v___x_995_; uint8_t v___x_996_; 
lean_dec(v_res_917_);
v___x_995_ = lean_array_get_size(v_res_950_);
lean_dec(v_res_950_);
v___x_996_ = lean_nat_dec_eq(v___x_995_, v___x_946_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_999_; 
lean_dec(v_res_945_);
lean_dec(v_ident_913_);
v___x_997_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2));
if (v_isShared_953_ == 0)
{
lean_ctor_set_tag(v___x_952_, 1);
lean_ctor_set(v___x_952_, 1, v___x_997_);
lean_ctor_set(v___x_952_, 0, v___x_974_);
v___x_999_ = v___x_952_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1001_, 0, v_ident_913_);
lean_ctor_set(v___x_1001_, 1, v_res_945_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v___x_1001_);
lean_ctor_set(v___x_952_, 0, v___x_974_);
v___x_1003_ = v___x_952_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
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
lean_object* v_pos_1010_; lean_object* v_err_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec(v_res_945_);
lean_dec(v_res_917_);
lean_dec(v_ident_913_);
v_pos_1010_ = lean_ctor_get(v___x_948_, 0);
v_err_1011_ = lean_ctor_get(v___x_948_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_948_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_err_1011_);
lean_inc(v_pos_1010_);
lean_dec(v___x_948_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_pos_1010_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_err_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
else
{
lean_object* v_pos_1019_; lean_object* v_err_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_dec(v_res_917_);
lean_dec(v_ident_913_);
v_pos_1019_ = lean_ctor_get(v___x_943_, 0);
v_err_1020_ = lean_ctor_get(v___x_943_, 1);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_943_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_err_1020_);
lean_inc(v_pos_1019_);
lean_dec(v___x_943_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_pos_1019_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_err_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
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
lean_object* v_pos_1033_; lean_object* v_err_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec(v_ident_913_);
v_pos_1033_ = lean_ctor_get(v___x_915_, 0);
v_err_1034_ = lean_ctor_get(v___x_915_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_915_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_err_1034_);
lean_inc(v_pos_1033_);
lean_dec(v___x_915_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_pos_1033_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_err_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(lean_object* v_a_1042_){
_start:
{
lean_object* v_array_1046_; lean_object* v_idx_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v_array_1046_ = lean_ctor_get(v_a_1042_, 0);
v_idx_1047_ = lean_ctor_get(v_a_1042_, 1);
v___x_1048_ = lean_byte_array_size(v_array_1046_);
v___x_1049_ = lean_nat_dec_lt(v_idx_1047_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_box(0);
v___x_1051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_a_1042_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
return v___x_1051_;
}
else
{
uint8_t v_c_1052_; uint8_t v___x_1053_; uint8_t v___x_1054_; 
v_c_1052_ = lean_byte_array_fget(v_array_1046_, v_idx_1047_);
v___x_1053_ = 48;
v___x_1054_ = lean_uint8_dec_le(v___x_1053_, v_c_1052_);
if (v___x_1054_ == 0)
{
goto v___jp_1043_;
}
else
{
uint8_t v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = 57;
v___x_1056_ = lean_uint8_dec_le(v_c_1052_, v___x_1055_);
if (v___x_1056_ == 0)
{
goto v___jp_1043_;
}
else
{
lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1117_; 
lean_inc(v_idx_1047_);
lean_inc_ref(v_array_1046_);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_a_1042_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; lean_object* v_unused_1119_; 
v_unused_1118_ = lean_ctor_get(v_a_1042_, 1);
lean_dec(v_unused_1118_);
v_unused_1119_ = lean_ctor_get(v_a_1042_, 0);
lean_dec(v_unused_1119_);
v___x_1058_ = v_a_1042_;
v_isShared_1059_ = v_isSharedCheck_1117_;
goto v_resetjp_1057_;
}
else
{
lean_dec(v_a_1042_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1117_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v_it_x27_1063_; 
v___x_1060_ = lean_unsigned_to_nat(1u);
v___x_1061_ = lean_nat_add(v_idx_1047_, v___x_1060_);
lean_dec(v_idx_1047_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v___x_1061_);
v_it_x27_1063_ = v___x_1058_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_array_1046_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v___x_1061_);
v_it_x27_1063_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
uint32_t v___x_1064_; uint8_t v___x_1065_; uint8_t v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v_fst_1069_; lean_object* v_snd_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1115_; 
v___x_1064_ = lean_uint8_to_uint32(v_c_1052_);
v___x_1065_ = lean_uint32_to_uint8(v___x_1064_);
v___x_1066_ = lean_uint8_sub(v___x_1065_, v___x_1053_);
v___x_1067_ = lean_uint8_to_nat(v___x_1066_);
v___x_1068_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(v_it_x27_1063_, v___x_1067_);
v_fst_1069_ = lean_ctor_get(v___x_1068_, 0);
v_snd_1070_ = lean_ctor_get(v___x_1068_, 1);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1072_ = v___x_1068_;
v_isShared_1073_ = v_isSharedCheck_1115_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_snd_1070_);
lean_inc(v_fst_1069_);
lean_dec(v___x_1068_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1115_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = lean_nat_dec_eq(v_fst_1069_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v_array_1076_; lean_object* v_idx_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v_array_1076_ = lean_ctor_get(v_snd_1070_, 0);
v_idx_1077_ = lean_ctor_get(v_snd_1070_, 1);
v___x_1078_ = lean_byte_array_size(v_array_1076_);
v___x_1079_ = lean_nat_dec_lt(v_idx_1077_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
lean_dec(v_fst_1069_);
v___x_1080_ = lean_box(0);
if (v_isShared_1073_ == 0)
{
lean_ctor_set_tag(v___x_1072_, 1);
lean_ctor_set(v___x_1072_, 1, v___x_1080_);
lean_ctor_set(v___x_1072_, 0, v_snd_1070_);
v___x_1082_ = v___x_1072_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_snd_1070_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
else
{
uint8_t v___x_1084_; uint8_t v_got_1085_; uint8_t v___x_1086_; 
v___x_1084_ = 32;
v_got_1085_ = lean_byte_array_fget(v_array_1076_, v_idx_1077_);
v___x_1086_ = lean_uint8_dec_eq(v_got_1085_, v___x_1084_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
lean_dec(v_fst_1069_);
v___x_1087_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1));
if (v_isShared_1073_ == 0)
{
lean_ctor_set_tag(v___x_1072_, 1);
lean_ctor_set(v___x_1072_, 1, v___x_1087_);
lean_ctor_set(v___x_1072_, 0, v_snd_1070_);
v___x_1089_ = v___x_1072_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_snd_1070_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
else
{
lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1108_; 
lean_inc(v_idx_1077_);
lean_inc_ref(v_array_1076_);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_snd_1070_);
if (v_isSharedCheck_1108_ == 0)
{
lean_object* v_unused_1109_; lean_object* v_unused_1110_; 
v_unused_1109_ = lean_ctor_get(v_snd_1070_, 1);
lean_dec(v_unused_1109_);
v_unused_1110_ = lean_ctor_get(v_snd_1070_, 0);
lean_dec(v_unused_1110_);
v___x_1092_ = v_snd_1070_;
v_isShared_1093_ = v_isSharedCheck_1108_;
goto v_resetjp_1091_;
}
else
{
lean_dec(v_snd_1070_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1108_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1094_ = lean_nat_add(v_idx_1077_, v___x_1060_);
lean_dec(v_idx_1077_);
lean_inc(v___x_1094_);
lean_inc_ref(v_array_1076_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 1, v___x_1094_);
v___x_1096_ = v___x_1092_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_array_1076_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
uint8_t v___x_1097_; 
v___x_1097_ = lean_nat_dec_lt(v___x_1094_, v___x_1078_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
lean_dec(v___x_1094_);
lean_dec_ref(v_array_1076_);
lean_dec(v_fst_1069_);
v___x_1098_ = lean_box(0);
if (v_isShared_1073_ == 0)
{
lean_ctor_set_tag(v___x_1072_, 1);
lean_ctor_set(v___x_1072_, 1, v___x_1098_);
lean_ctor_set(v___x_1072_, 0, v___x_1096_);
v___x_1100_ = v___x_1072_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
else
{
uint8_t v___x_1102_; uint8_t v___x_1103_; uint8_t v___x_1104_; 
lean_del_object(v___x_1072_);
v___x_1102_ = lean_byte_array_fget(v_array_1076_, v___x_1094_);
lean_dec(v___x_1094_);
lean_dec_ref(v_array_1076_);
v___x_1103_ = 100;
v___x_1104_ = lean_uint8_dec_eq(v___x_1102_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(v_fst_1069_, v___x_1096_);
return v___x_1105_;
}
else
{
lean_object* v___x_1106_; 
lean_dec(v_fst_1069_);
v___x_1106_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(v___x_1096_);
return v___x_1106_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1111_; lean_object* v___x_1113_; 
lean_dec(v_fst_1069_);
v___x_1111_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3));
if (v_isShared_1073_ == 0)
{
lean_ctor_set_tag(v___x_1072_, 1);
lean_ctor_set(v___x_1072_, 1, v___x_1111_);
lean_ctor_set(v___x_1072_, 0, v_snd_1070_);
v___x_1113_ = v___x_1072_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_snd_1070_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
}
}
}
v___jp_1043_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
v___x_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1045_, 0, v_a_1042_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
return v___x_1045_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(lean_object* v_acc_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v_array_1125_; lean_object* v_idx_1126_; lean_object* v_pos_1128_; lean_object* v_idx_1129_; lean_object* v_err_1130_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v_array_1125_ = lean_ctor_get(v_a_1124_, 0);
v_idx_1126_ = lean_ctor_get(v_a_1124_, 1);
lean_inc(v_idx_1126_);
v___x_1136_ = lean_byte_array_size(v_array_1125_);
v___x_1137_ = lean_nat_dec_lt(v_idx_1126_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_box(0);
lean_inc(v_idx_1126_);
v_pos_1128_ = v_a_1124_;
v_idx_1129_ = v_idx_1126_;
v_err_1130_ = v___x_1138_;
goto v___jp_1127_;
}
else
{
uint8_t v_c_1139_; uint8_t v___x_1140_; uint8_t v___x_1141_; 
v_c_1139_ = lean_byte_array_fget(v_array_1125_, v_idx_1126_);
v___x_1140_ = 10;
v___x_1141_ = lean_uint8_dec_eq(v_c_1139_, v___x_1140_);
if (v___x_1141_ == 0)
{
uint8_t v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = 13;
v___x_1143_ = lean_uint8_dec_eq(v_c_1139_, v___x_1142_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1155_; 
lean_inc_ref(v_array_1125_);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_a_1124_);
if (v_isSharedCheck_1155_ == 0)
{
lean_object* v_unused_1156_; lean_object* v_unused_1157_; 
v_unused_1156_ = lean_ctor_get(v_a_1124_, 1);
lean_dec(v_unused_1156_);
v_unused_1157_ = lean_ctor_get(v_a_1124_, 0);
lean_dec(v_unused_1157_);
v___x_1145_ = v_a_1124_;
v_isShared_1146_ = v_isSharedCheck_1155_;
goto v_resetjp_1144_;
}
else
{
lean_dec(v_a_1124_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1155_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v_it_x27_1150_; 
v___x_1147_ = lean_unsigned_to_nat(1u);
v___x_1148_ = lean_nat_add(v_idx_1126_, v___x_1147_);
lean_dec(v_idx_1126_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v___x_1148_);
v_it_x27_1150_ = v___x_1145_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_array_1125_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v___x_1148_);
v_it_x27_1150_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_box(v_c_1139_);
v___x_1152_ = lean_array_push(v_acc_1123_, v___x_1151_);
v_acc_1123_ = v___x_1152_;
v_a_1124_ = v_it_x27_1150_;
goto _start;
}
}
}
else
{
goto v___jp_1134_;
}
}
else
{
goto v___jp_1134_;
}
}
v___jp_1127_:
{
uint8_t v___x_1131_; 
v___x_1131_ = lean_nat_dec_eq(v_idx_1126_, v_idx_1129_);
lean_dec(v_idx_1129_);
lean_dec(v_idx_1126_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
lean_dec_ref(v_acc_1123_);
lean_inc(v_err_1130_);
v___x_1132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1132_, 0, v_pos_1128_);
lean_ctor_set(v___x_1132_, 1, v_err_1130_);
return v___x_1132_;
}
else
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v_pos_1128_);
lean_ctor_set(v___x_1133_, 1, v_acc_1123_);
return v___x_1133_;
}
}
v___jp_1134_:
{
lean_object* v___x_1135_; 
v___x_1135_ = ((lean_object*)(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__1));
lean_inc(v_idx_1126_);
v_pos_1128_ = v_a_1124_;
v_idx_1129_ = v_idx_1126_;
v_err_1130_ = v___x_1135_;
goto v___jp_1127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(lean_object* v_actions_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_pos_1163_; lean_object* v_array_1164_; lean_object* v_idx_1165_; lean_object* v_pos_1171_; lean_object* v___y_1175_; lean_object* v_array_1186_; lean_object* v_idx_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v_array_1186_ = lean_ctor_get(v_a_1161_, 0);
v_idx_1187_ = lean_ctor_get(v_a_1161_, 1);
v___x_1188_ = lean_byte_array_size(v_array_1186_);
v___x_1189_ = lean_nat_dec_lt(v_idx_1187_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_dec_ref(v_actions_1160_);
v___x_1190_ = lean_box(0);
v___x_1191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1191_, 0, v_a_1161_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
return v___x_1191_;
}
else
{
uint8_t v___x_1192_; uint8_t v___x_1193_; uint8_t v___x_1194_; 
v___x_1192_ = lean_byte_array_fget(v_array_1186_, v_idx_1187_);
v___x_1193_ = 99;
v___x_1194_ = lean_uint8_dec_eq(v___x_1192_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(v_a_1161_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_pos_1196_; lean_object* v_res_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1258_; 
v_pos_1196_ = lean_ctor_get(v___x_1195_, 0);
v_res_1197_ = lean_ctor_get(v___x_1195_, 1);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1199_ = v___x_1195_;
v_isShared_1200_ = v_isSharedCheck_1258_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_res_1197_);
lean_inc(v_pos_1196_);
lean_dec(v___x_1195_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1258_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v_pos_1202_; lean_object* v_array_1203_; lean_object* v_idx_1204_; lean_object* v_pos_1213_; lean_object* v___y_1217_; lean_object* v_array_1228_; lean_object* v_idx_1229_; lean_object* v___y_1231_; lean_object* v_pos_1232_; lean_object* v_idx_1233_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v_array_1228_ = lean_ctor_get(v_pos_1196_, 0);
v_idx_1229_ = lean_ctor_get(v_pos_1196_, 1);
lean_inc(v_idx_1229_);
v___x_1238_ = lean_byte_array_size(v_array_1228_);
v___x_1239_ = lean_nat_dec_lt(v_idx_1229_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_box(0);
lean_inc(v_pos_1196_);
v___x_1241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1241_, 0, v_pos_1196_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
lean_inc(v_idx_1229_);
v___y_1231_ = v___x_1241_;
v_pos_1232_ = v_pos_1196_;
v_idx_1233_ = v_idx_1229_;
goto v___jp_1230_;
}
else
{
uint8_t v___x_1242_; uint8_t v_got_1243_; uint8_t v___x_1244_; 
v___x_1242_ = 10;
v_got_1243_ = lean_byte_array_fget(v_array_1228_, v_idx_1229_);
v___x_1244_ = lean_uint8_dec_eq(v_got_1243_, v___x_1242_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
lean_inc(v_pos_1196_);
v___x_1246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_pos_1196_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
lean_inc(v_idx_1229_);
v___y_1231_ = v___x_1246_;
v_pos_1232_ = v_pos_1196_;
v_idx_1233_ = v_idx_1229_;
goto v___jp_1230_;
}
else
{
lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1255_; 
lean_inc_ref(v_array_1228_);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_pos_1196_);
if (v_isSharedCheck_1255_ == 0)
{
lean_object* v_unused_1256_; lean_object* v_unused_1257_; 
v_unused_1256_ = lean_ctor_get(v_pos_1196_, 1);
lean_dec(v_unused_1256_);
v_unused_1257_ = lean_ctor_get(v_pos_1196_, 0);
lean_dec(v_unused_1257_);
v___x_1248_ = v_pos_1196_;
v_isShared_1249_ = v_isSharedCheck_1255_;
goto v_resetjp_1247_;
}
else
{
lean_dec(v_pos_1196_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1255_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1250_ = lean_unsigned_to_nat(1u);
v___x_1251_ = lean_nat_add(v_idx_1229_, v___x_1250_);
lean_dec(v_idx_1229_);
lean_inc(v___x_1251_);
lean_inc_ref(v_array_1228_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 1, v___x_1251_);
v___x_1253_ = v___x_1248_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_array_1228_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
v_pos_1202_ = v___x_1253_;
v_array_1203_ = v_array_1228_;
v_idx_1204_ = v___x_1251_;
goto v___jp_1201_;
}
}
}
}
v___jp_1201_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1205_ = lean_array_push(v_actions_1160_, v_res_1197_);
v___x_1206_ = lean_byte_array_size(v_array_1203_);
lean_dec_ref(v_array_1203_);
v___x_1207_ = lean_nat_dec_lt(v_idx_1204_, v___x_1206_);
lean_dec(v_idx_1204_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1209_; 
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 1, v___x_1205_);
lean_ctor_set(v___x_1199_, 0, v_pos_1202_);
v___x_1209_ = v___x_1199_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_pos_1202_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v___x_1205_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
else
{
lean_del_object(v___x_1199_);
v_actions_1160_ = v___x_1205_;
v_a_1161_ = v_pos_1202_;
goto _start;
}
}
v___jp_1212_:
{
lean_object* v_array_1214_; lean_object* v_idx_1215_; 
v_array_1214_ = lean_ctor_get(v_pos_1213_, 0);
lean_inc_ref(v_array_1214_);
v_idx_1215_ = lean_ctor_get(v_pos_1213_, 1);
lean_inc(v_idx_1215_);
v_pos_1202_ = v_pos_1213_;
v_array_1203_ = v_array_1214_;
v_idx_1204_ = v_idx_1215_;
goto v___jp_1201_;
}
v___jp_1216_:
{
if (lean_obj_tag(v___y_1217_) == 0)
{
lean_object* v_pos_1218_; 
v_pos_1218_ = lean_ctor_get(v___y_1217_, 0);
lean_inc(v_pos_1218_);
lean_dec_ref_known(v___y_1217_, 2);
v_pos_1213_ = v_pos_1218_;
goto v___jp_1212_;
}
else
{
lean_object* v_pos_1219_; lean_object* v_err_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_del_object(v___x_1199_);
lean_dec(v_res_1197_);
lean_dec_ref(v_actions_1160_);
v_pos_1219_ = lean_ctor_get(v___y_1217_, 0);
v_err_1220_ = lean_ctor_get(v___y_1217_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___y_1217_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___y_1217_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_err_1220_);
lean_inc(v_pos_1219_);
lean_dec(v___y_1217_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_pos_1219_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_err_1220_);
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
v___jp_1230_:
{
uint8_t v___x_1234_; 
v___x_1234_ = lean_nat_dec_eq(v_idx_1229_, v_idx_1233_);
lean_dec(v_idx_1233_);
lean_dec(v_idx_1229_);
if (v___x_1234_ == 0)
{
lean_dec_ref(v_pos_1232_);
v___y_1217_ = v___y_1231_;
goto v___jp_1216_;
}
else
{
lean_object* v_utf8_1235_; lean_object* v___x_1236_; 
lean_dec_ref(v___y_1231_);
v_utf8_1235_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1);
v___x_1236_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1235_, v_pos_1232_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_pos_1237_; 
v_pos_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_pos_1237_);
lean_dec_ref_known(v___x_1236_, 2);
v_pos_1213_ = v_pos_1237_;
goto v___jp_1212_;
}
else
{
v___y_1217_ = v___x_1236_;
goto v___jp_1216_;
}
}
}
}
}
else
{
lean_object* v_pos_1259_; lean_object* v_err_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec_ref(v_actions_1160_);
v_pos_1259_ = lean_ctor_get(v___x_1195_, 0);
v_err_1260_ = lean_ctor_get(v___x_1195_, 1);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1195_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_err_1260_);
lean_inc(v_pos_1259_);
lean_dec(v___x_1195_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_pos_1259_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_err_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0));
v___x_1269_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(v___x_1268_, v_a_1161_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_pos_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1308_; 
v_pos_1270_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1308_ == 0)
{
lean_object* v_unused_1309_; 
v_unused_1309_ = lean_ctor_get(v___x_1269_, 1);
lean_dec(v_unused_1309_);
v___x_1272_ = v___x_1269_;
v_isShared_1273_ = v_isSharedCheck_1308_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_pos_1270_);
lean_dec(v___x_1269_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1308_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v_array_1274_; lean_object* v_idx_1275_; lean_object* v___y_1277_; lean_object* v_pos_1278_; lean_object* v_idx_1279_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v_array_1274_ = lean_ctor_get(v_pos_1270_, 0);
v_idx_1275_ = lean_ctor_get(v_pos_1270_, 1);
lean_inc(v_idx_1275_);
v___x_1284_ = lean_byte_array_size(v_array_1274_);
v___x_1285_ = lean_nat_dec_lt(v_idx_1275_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1286_ = lean_box(0);
lean_inc(v_pos_1270_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set_tag(v___x_1272_, 1);
lean_ctor_set(v___x_1272_, 1, v___x_1286_);
v___x_1288_ = v___x_1272_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_pos_1270_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_inc(v_idx_1275_);
v___y_1277_ = v___x_1288_;
v_pos_1278_ = v_pos_1270_;
v_idx_1279_ = v_idx_1275_;
goto v___jp_1276_;
}
}
else
{
uint8_t v___x_1290_; uint8_t v_got_1291_; uint8_t v___x_1292_; 
v___x_1290_ = 10;
v_got_1291_ = lean_byte_array_fget(v_array_1274_, v_idx_1275_);
v___x_1292_ = lean_uint8_dec_eq(v_got_1291_, v___x_1290_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; lean_object* v___x_1295_; 
v___x_1293_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
lean_inc(v_pos_1270_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set_tag(v___x_1272_, 1);
lean_ctor_set(v___x_1272_, 1, v___x_1293_);
v___x_1295_ = v___x_1272_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_pos_1270_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v___x_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
lean_inc(v_idx_1275_);
v___y_1277_ = v___x_1295_;
v_pos_1278_ = v_pos_1270_;
v_idx_1279_ = v_idx_1275_;
goto v___jp_1276_;
}
}
else
{
lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1305_; 
lean_inc_ref(v_array_1274_);
lean_del_object(v___x_1272_);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_pos_1270_);
if (v_isSharedCheck_1305_ == 0)
{
lean_object* v_unused_1306_; lean_object* v_unused_1307_; 
v_unused_1306_ = lean_ctor_get(v_pos_1270_, 1);
lean_dec(v_unused_1306_);
v_unused_1307_ = lean_ctor_get(v_pos_1270_, 0);
lean_dec(v_unused_1307_);
v___x_1298_ = v_pos_1270_;
v_isShared_1299_ = v_isSharedCheck_1305_;
goto v_resetjp_1297_;
}
else
{
lean_dec(v_pos_1270_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1305_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1300_ = lean_unsigned_to_nat(1u);
v___x_1301_ = lean_nat_add(v_idx_1275_, v___x_1300_);
lean_dec(v_idx_1275_);
lean_inc(v___x_1301_);
lean_inc_ref(v_array_1274_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 1, v___x_1301_);
v___x_1303_ = v___x_1298_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_array_1274_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
v_pos_1163_ = v___x_1303_;
v_array_1164_ = v_array_1274_;
v_idx_1165_ = v___x_1301_;
goto v___jp_1162_;
}
}
}
}
v___jp_1276_:
{
uint8_t v___x_1280_; 
v___x_1280_ = lean_nat_dec_eq(v_idx_1275_, v_idx_1279_);
lean_dec(v_idx_1279_);
lean_dec(v_idx_1275_);
if (v___x_1280_ == 0)
{
lean_dec_ref(v_pos_1278_);
v___y_1175_ = v___y_1277_;
goto v___jp_1174_;
}
else
{
lean_object* v_utf8_1281_; lean_object* v___x_1282_; 
lean_dec_ref(v___y_1277_);
v_utf8_1281_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1);
v___x_1282_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_1281_, v_pos_1278_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_pos_1283_; 
v_pos_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_pos_1283_);
lean_dec_ref_known(v___x_1282_, 2);
v_pos_1171_ = v_pos_1283_;
goto v___jp_1170_;
}
else
{
v___y_1175_ = v___x_1282_;
goto v___jp_1174_;
}
}
}
}
}
else
{
lean_object* v_pos_1310_; lean_object* v_err_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec_ref(v_actions_1160_);
v_pos_1310_ = lean_ctor_get(v___x_1269_, 0);
v_err_1311_ = lean_ctor_get(v___x_1269_, 1);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1269_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_err_1311_);
lean_inc(v_pos_1310_);
lean_dec(v___x_1269_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_pos_1310_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_err_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
v___jp_1162_:
{
lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = lean_byte_array_size(v_array_1164_);
lean_dec_ref(v_array_1164_);
v___x_1167_ = lean_nat_dec_lt(v_idx_1165_, v___x_1166_);
lean_dec(v_idx_1165_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1168_, 0, v_pos_1163_);
lean_ctor_set(v___x_1168_, 1, v_actions_1160_);
return v___x_1168_;
}
else
{
v_a_1161_ = v_pos_1163_;
goto _start;
}
}
v___jp_1170_:
{
lean_object* v_array_1172_; lean_object* v_idx_1173_; 
v_array_1172_ = lean_ctor_get(v_pos_1171_, 0);
lean_inc_ref(v_array_1172_);
v_idx_1173_ = lean_ctor_get(v_pos_1171_, 1);
lean_inc(v_idx_1173_);
v_pos_1163_ = v_pos_1171_;
v_array_1164_ = v_array_1172_;
v_idx_1165_ = v_idx_1173_;
goto v___jp_1162_;
}
v___jp_1174_:
{
if (lean_obj_tag(v___y_1175_) == 0)
{
lean_object* v_pos_1176_; 
v_pos_1176_ = lean_ctor_get(v___y_1175_, 0);
lean_inc(v_pos_1176_);
lean_dec_ref_known(v___y_1175_, 2);
v_pos_1171_ = v_pos_1176_;
goto v___jp_1170_;
}
else
{
lean_object* v_pos_1177_; lean_object* v_err_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v_actions_1160_);
v_pos_1177_ = lean_ctor_get(v___y_1175_, 0);
v_err_1178_ = lean_ctor_get(v___y_1175_, 1);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___y_1175_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___y_1175_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_err_1178_);
lean_inc(v_pos_1177_);
lean_dec(v___y_1175_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_pos_1177_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_err_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(lean_object* v_a_1321_){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0));
v___x_1323_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(v___x_1322_, v_a_1321_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero(lean_object* v_a_1327_){
_start:
{
lean_object* v_array_1328_; lean_object* v_idx_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v_array_1328_ = lean_ctor_get(v_a_1327_, 0);
v_idx_1329_ = lean_ctor_get(v_a_1327_, 1);
v___x_1330_ = lean_byte_array_size(v_array_1328_);
v___x_1331_ = lean_nat_dec_lt(v_idx_1329_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = lean_box(0);
v___x_1333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1333_, 0, v_a_1327_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
return v___x_1333_;
}
else
{
uint8_t v___x_1334_; uint8_t v_got_1335_; uint8_t v___x_1336_; 
v___x_1334_ = 0;
v_got_1335_ = lean_byte_array_fget(v_array_1328_, v_idx_1329_);
v___x_1336_ = lean_uint8_dec_eq(v_got_1335_, v___x_1334_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
v___x_1338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1338_, 0, v_a_1327_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
return v___x_1338_;
}
else
{
lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1349_; 
lean_inc(v_idx_1329_);
lean_inc_ref(v_array_1328_);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_a_1327_);
if (v_isSharedCheck_1349_ == 0)
{
lean_object* v_unused_1350_; lean_object* v_unused_1351_; 
v_unused_1350_ = lean_ctor_get(v_a_1327_, 1);
lean_dec(v_unused_1350_);
v_unused_1351_ = lean_ctor_get(v_a_1327_, 0);
lean_dec(v_unused_1351_);
v___x_1340_ = v_a_1327_;
v_isShared_1341_ = v_isSharedCheck_1349_;
goto v_resetjp_1339_;
}
else
{
lean_dec(v_a_1327_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1349_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1342_ = lean_unsigned_to_nat(1u);
v___x_1343_ = lean_nat_add(v_idx_1329_, v___x_1342_);
lean_dec(v_idx_1329_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 1, v___x_1343_);
v___x_1345_ = v___x_1340_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_array_1328_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_box(0);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1345_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
return v___x_1347_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(uint64_t v_uidx_1358_, uint64_t v_shift_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_array_1361_; lean_object* v_idx_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v_array_1361_ = lean_ctor_get(v_a_1360_, 0);
v_idx_1362_ = lean_ctor_get(v_a_1360_, 1);
v___x_1363_ = lean_byte_array_size(v_array_1361_);
v___x_1364_ = lean_nat_dec_lt(v_idx_1362_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = lean_box(0);
v___x_1366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1366_, 0, v_a_1360_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
return v___x_1366_;
}
else
{
lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1412_; 
lean_inc(v_idx_1362_);
lean_inc_ref(v_array_1361_);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_a_1360_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; lean_object* v_unused_1414_; 
v_unused_1413_ = lean_ctor_get(v_a_1360_, 1);
lean_dec(v_unused_1413_);
v_unused_1414_ = lean_ctor_get(v_a_1360_, 0);
lean_dec(v_unused_1414_);
v___x_1368_ = v_a_1360_;
v_isShared_1369_ = v_isSharedCheck_1412_;
goto v_resetjp_1367_;
}
else
{
lean_dec(v_a_1360_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1412_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
uint8_t v_c_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v_it_x27_1374_; 
v_c_1370_ = lean_byte_array_fget(v_array_1361_, v_idx_1362_);
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_nat_add(v_idx_1362_, v___x_1371_);
lean_dec(v_idx_1362_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 1, v___x_1372_);
v_it_x27_1374_ = v___x_1368_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_array_1361_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v___x_1372_);
v_it_x27_1374_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
uint64_t v___x_1403_; uint8_t v___x_1404_; 
v___x_1403_ = 28ULL;
v___x_1404_ = lean_uint64_dec_eq(v_shift_1359_, v___x_1403_);
if (v___x_1404_ == 0)
{
goto v___jp_1375_;
}
else
{
uint8_t v___x_1405_; uint8_t v___x_1406_; uint8_t v___x_1407_; uint8_t v___x_1408_; 
v___x_1405_ = 240;
v___x_1406_ = lean_uint8_land(v_c_1370_, v___x_1405_);
v___x_1407_ = 0;
v___x_1408_ = lean_uint8_dec_eq(v___x_1406_, v___x_1407_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3));
v___x_1410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1410_, 0, v_it_x27_1374_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
return v___x_1410_;
}
else
{
goto v___jp_1375_;
}
}
v___jp_1375_:
{
uint8_t v___x_1376_; uint8_t v___x_1377_; 
v___x_1376_ = 0;
v___x_1377_ = lean_uint8_dec_eq(v_c_1370_, v___x_1376_);
if (v___x_1377_ == 0)
{
uint8_t v___x_1378_; uint8_t v___x_1379_; uint64_t v___x_1380_; uint64_t v___x_1381_; uint64_t v___x_1382_; uint8_t v___x_1383_; uint8_t v___x_1384_; uint8_t v___x_1385_; 
v___x_1378_ = 127;
v___x_1379_ = lean_uint8_land(v_c_1370_, v___x_1378_);
v___x_1380_ = lean_uint8_to_uint64(v___x_1379_);
v___x_1381_ = lean_uint64_shift_left(v___x_1380_, v_shift_1359_);
v___x_1382_ = lean_uint64_lor(v_uidx_1358_, v___x_1381_);
v___x_1383_ = 128;
v___x_1384_ = lean_uint8_land(v_c_1370_, v___x_1383_);
v___x_1385_ = lean_uint8_dec_eq(v___x_1384_, v___x_1376_);
if (v___x_1385_ == 0)
{
uint64_t v___x_1386_; uint64_t v___x_1387_; 
v___x_1386_ = 7ULL;
v___x_1387_ = lean_uint64_add(v_shift_1359_, v___x_1386_);
v_uidx_1358_ = v___x_1382_;
v_shift_1359_ = v___x_1387_;
v_a_1360_ = v_it_x27_1374_;
goto _start;
}
else
{
uint64_t v___x_1389_; uint64_t v___x_1390_; uint64_t v___x_1391_; uint64_t v___x_1392_; uint8_t v___x_1393_; 
v___x_1389_ = 1ULL;
v___x_1390_ = lean_uint64_shift_right(v___x_1382_, v___x_1389_);
v___x_1391_ = lean_uint64_land(v___x_1389_, v___x_1382_);
v___x_1392_ = 0ULL;
v___x_1393_ = lean_uint64_dec_eq(v___x_1391_, v___x_1392_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1394_ = lean_uint64_to_nat(v___x_1390_);
v___x_1395_ = lean_nat_to_int(v___x_1394_);
v___x_1396_ = lean_int_neg(v___x_1395_);
lean_dec(v___x_1395_);
v___x_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1397_, 0, v_it_x27_1374_);
lean_ctor_set(v___x_1397_, 1, v___x_1396_);
return v___x_1397_;
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = lean_uint64_to_nat(v___x_1390_);
v___x_1399_ = lean_nat_to_int(v___x_1398_);
v___x_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1400_, 0, v_it_x27_1374_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
return v___x_1400_;
}
}
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1));
v___x_1402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_it_x27_1374_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
return v___x_1402_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___boxed(lean_object* v_uidx_1415_, lean_object* v_shift_1416_, lean_object* v_a_1417_){
_start:
{
uint64_t v_uidx_boxed_1418_; uint64_t v_shift_boxed_1419_; lean_object* v_res_1420_; 
v_uidx_boxed_1418_ = lean_unbox_uint64(v_uidx_1415_);
lean_dec_ref(v_uidx_1415_);
v_shift_boxed_1419_ = lean_unbox_uint64(v_shift_1416_);
lean_dec_ref(v_shift_1416_);
v_res_1420_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(v_uidx_boxed_1418_, v_shift_boxed_1419_, v_a_1417_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(lean_object* v_a_1421_){
_start:
{
uint64_t v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = 0ULL;
v___x_1423_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(v___x_1422_, v___x_1422_, v_a_1421_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg(lean_object* v_a_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1427_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_pos_1429_; lean_object* v_res_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1444_; 
v_pos_1429_ = lean_ctor_get(v___x_1428_, 0);
v_res_1430_ = lean_ctor_get(v___x_1428_, 1);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1432_ = v___x_1428_;
v_isShared_1433_ = v_isSharedCheck_1444_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_res_1430_);
lean_inc(v_pos_1429_);
lean_dec(v___x_1428_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1444_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1435_ = lean_int_dec_lt(v_res_1430_, v___x_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
lean_dec(v_res_1430_);
v___x_1436_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1));
if (v_isShared_1433_ == 0)
{
lean_ctor_set_tag(v___x_1432_, 1);
lean_ctor_set(v___x_1432_, 1, v___x_1436_);
v___x_1438_ = v___x_1432_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_pos_1429_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1440_ = lean_nat_abs(v_res_1430_);
lean_dec(v_res_1430_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 1, v___x_1440_);
v___x_1442_ = v___x_1432_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_pos_1429_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
else
{
lean_object* v_pos_1445_; lean_object* v_err_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
v_pos_1445_ = lean_ctor_get(v___x_1428_, 0);
v_err_1446_ = lean_ctor_get(v___x_1428_, 1);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1428_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_err_1446_);
lean_inc(v_pos_1445_);
lean_dec(v___x_1428_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_pos_1445_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_err_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos(lean_object* v_a_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1457_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_pos_1459_; lean_object* v_res_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1474_; 
v_pos_1459_ = lean_ctor_get(v___x_1458_, 0);
v_res_1460_ = lean_ctor_get(v___x_1458_, 1);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1462_ = v___x_1458_;
v_isShared_1463_ = v_isSharedCheck_1474_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_res_1460_);
lean_inc(v_pos_1459_);
lean_dec(v___x_1458_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1474_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; uint8_t v___x_1465_; 
v___x_1464_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1465_ = lean_int_dec_lt(v___x_1464_, v_res_1460_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
lean_dec(v_res_1460_);
v___x_1466_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1463_ == 0)
{
lean_ctor_set_tag(v___x_1462_, 1);
lean_ctor_set(v___x_1462_, 1, v___x_1466_);
v___x_1468_ = v___x_1462_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_pos_1459_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1470_ = lean_nat_abs(v_res_1460_);
lean_dec(v_res_1460_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 1, v___x_1470_);
v___x_1472_ = v___x_1462_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_pos_1459_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
else
{
lean_object* v_pos_1475_; lean_object* v_err_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
v_pos_1475_ = lean_ctor_get(v___x_1458_, 0);
v_err_1476_ = lean_ctor_get(v___x_1458_, 1);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1458_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_err_1476_);
lean_inc(v_pos_1475_);
lean_dec(v___x_1458_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_pos_1475_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_err_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId(lean_object* v_a_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1484_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_pos_1486_; lean_object* v_res_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1501_; 
v_pos_1486_ = lean_ctor_get(v___x_1485_, 0);
v_res_1487_ = lean_ctor_get(v___x_1485_, 1);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1489_ = v___x_1485_;
v_isShared_1490_ = v_isSharedCheck_1501_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_res_1487_);
lean_inc(v_pos_1486_);
lean_dec(v___x_1485_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1501_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1491_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1492_ = lean_int_dec_lt(v___x_1491_, v_res_1487_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; lean_object* v___x_1495_; 
lean_dec(v_res_1487_);
v___x_1493_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1490_ == 0)
{
lean_ctor_set_tag(v___x_1489_, 1);
lean_ctor_set(v___x_1489_, 1, v___x_1493_);
v___x_1495_ = v___x_1489_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_pos_1486_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1497_ = lean_nat_abs(v_res_1487_);
lean_dec(v_res_1487_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v___x_1497_);
v___x_1499_ = v___x_1489_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_pos_1486_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
else
{
lean_object* v_pos_1502_; lean_object* v_err_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
v_pos_1502_ = lean_ctor_get(v___x_1485_, 0);
v_err_1503_ = lean_ctor_get(v___x_1485_, 1);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1485_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_err_1503_);
lean_inc(v_pos_1502_);
lean_dec(v___x_1485_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_pos_1502_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_err_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(lean_object* v_parser_1511_, lean_object* v_acc_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v_array_1514_; lean_object* v_idx_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; 
v_array_1514_ = lean_ctor_get(v_a_1513_, 0);
v_idx_1515_ = lean_ctor_get(v_a_1513_, 1);
v___x_1516_ = lean_byte_array_size(v_array_1514_);
v___x_1517_ = lean_nat_dec_lt(v_idx_1515_, v___x_1516_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec_ref(v_acc_1512_);
lean_dec_ref(v_parser_1511_);
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1519_, 0, v_a_1513_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
return v___x_1519_;
}
else
{
uint8_t v___x_1520_; uint8_t v___x_1521_; uint8_t v___x_1522_; 
v___x_1520_ = lean_byte_array_fget(v_array_1514_, v_idx_1515_);
v___x_1521_ = 0;
v___x_1522_ = lean_uint8_dec_eq(v___x_1520_, v___x_1521_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; 
lean_inc_ref(v_parser_1511_);
v___x_1523_ = lean_apply_1(v_parser_1511_, v_a_1513_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_pos_1524_; lean_object* v_res_1525_; lean_object* v___x_1526_; 
v_pos_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_pos_1524_);
v_res_1525_ = lean_ctor_get(v___x_1523_, 1);
lean_inc(v_res_1525_);
lean_dec_ref_known(v___x_1523_, 2);
v___x_1526_ = lean_array_push(v_acc_1512_, v_res_1525_);
v_acc_1512_ = v___x_1526_;
v_a_1513_ = v_pos_1524_;
goto _start;
}
else
{
lean_object* v_pos_1528_; lean_object* v_err_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_dec_ref(v_acc_1512_);
lean_dec_ref(v_parser_1511_);
v_pos_1528_ = lean_ctor_get(v___x_1523_, 0);
v_err_1529_ = lean_ctor_get(v___x_1523_, 1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1523_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_err_1529_);
lean_inc(v_pos_1528_);
lean_dec(v___x_1523_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_pos_1528_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_err_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
else
{
lean_object* v___x_1537_; 
lean_dec_ref(v_parser_1511_);
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v_a_1513_);
lean_ctor_set(v___x_1537_, 1, v_acc_1512_);
return v___x_1537_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go(lean_object* v_00_u03b1_1538_, lean_object* v_parser_1539_, lean_object* v_acc_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(v_parser_1539_, v_acc_1540_, v_a_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(lean_object* v_parser_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0));
v___x_1548_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(v_parser_1545_, v___x_1547_, v_a_1546_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero(lean_object* v_00_u03b1_1549_, lean_object* v_parser_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v_parser_1550_, v_a_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(lean_object* v_parser_1553_, lean_object* v_acc_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v_array_1556_; lean_object* v_idx_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v_array_1556_ = lean_ctor_get(v_a_1555_, 0);
v_idx_1557_ = lean_ctor_get(v_a_1555_, 1);
v___x_1558_ = lean_byte_array_size(v_array_1556_);
v___x_1559_ = lean_nat_dec_lt(v_idx_1557_, v___x_1558_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec_ref(v_acc_1554_);
lean_dec_ref(v_parser_1553_);
v___x_1560_ = lean_box(0);
v___x_1561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1561_, 0, v_a_1555_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
return v___x_1561_;
}
else
{
uint8_t v___x_1562_; uint8_t v___x_1563_; uint8_t v___x_1564_; uint8_t v___x_1565_; uint8_t v___x_1566_; 
v___x_1562_ = lean_byte_array_fget(v_array_1556_, v_idx_1557_);
v___x_1563_ = 1;
v___x_1564_ = lean_uint8_land(v___x_1563_, v___x_1562_);
v___x_1565_ = 0;
v___x_1566_ = lean_uint8_dec_eq(v___x_1564_, v___x_1565_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; 
lean_dec_ref(v_parser_1553_);
v___x_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1567_, 0, v_a_1555_);
lean_ctor_set(v___x_1567_, 1, v_acc_1554_);
return v___x_1567_;
}
else
{
uint8_t v___x_1568_; 
v___x_1568_ = lean_uint8_dec_eq(v___x_1562_, v___x_1565_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; 
lean_inc_ref(v_parser_1553_);
v___x_1569_ = lean_apply_1(v_parser_1553_, v_a_1555_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_pos_1570_; lean_object* v_res_1571_; lean_object* v___x_1572_; 
v_pos_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_pos_1570_);
v_res_1571_ = lean_ctor_get(v___x_1569_, 1);
lean_inc(v_res_1571_);
lean_dec_ref_known(v___x_1569_, 2);
v___x_1572_ = lean_array_push(v_acc_1554_, v_res_1571_);
v_acc_1554_ = v___x_1572_;
v_a_1555_ = v_pos_1570_;
goto _start;
}
else
{
lean_object* v_pos_1574_; lean_object* v_err_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec_ref(v_acc_1554_);
lean_dec_ref(v_parser_1553_);
v_pos_1574_ = lean_ctor_get(v___x_1569_, 0);
v_err_1575_ = lean_ctor_get(v___x_1569_, 1);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1569_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_err_1575_);
lean_inc(v_pos_1574_);
lean_dec(v___x_1569_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_pos_1574_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_err_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
else
{
lean_object* v___x_1583_; 
lean_dec_ref(v_parser_1553_);
v___x_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1583_, 0, v_a_1555_);
lean_ctor_set(v___x_1583_, 1, v_acc_1554_);
return v___x_1583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go(lean_object* v_00_u03b1_1584_, lean_object* v_parser_1585_, lean_object* v_acc_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(v_parser_1585_, v_acc_1586_, v_a_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(lean_object* v_parser_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0));
v___x_1592_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(v_parser_1589_, v___x_1591_, v_a_1590_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero(lean_object* v_00_u03b1_1593_, lean_object* v_parser_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(v_parser_1594_, v_a_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList(lean_object* v_a_1597_){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId), 1, 0);
v___x_1599_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(v___x_1598_, v_a_1597_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause(lean_object* v_a_1600_){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit), 1, 0);
v___x_1602_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v___x_1601_, v_a_1600_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(lean_object* v_acc_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_array_1605_; lean_object* v_idx_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; 
v_array_1605_ = lean_ctor_get(v_a_1604_, 0);
v_idx_1606_ = lean_ctor_get(v_a_1604_, 1);
v___x_1607_ = lean_byte_array_size(v_array_1605_);
v___x_1608_ = lean_nat_dec_lt(v_idx_1606_, v___x_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_dec_ref(v_acc_1603_);
v___x_1609_ = lean_box(0);
v___x_1610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1610_, 0, v_a_1604_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
return v___x_1610_;
}
else
{
uint8_t v___x_1611_; uint8_t v___x_1612_; uint8_t v___x_1613_; uint8_t v___x_1614_; uint8_t v___x_1615_; 
v___x_1611_ = lean_byte_array_fget(v_array_1605_, v_idx_1606_);
v___x_1612_ = 1;
v___x_1613_ = lean_uint8_land(v___x_1612_, v___x_1611_);
v___x_1614_ = 0;
v___x_1615_ = lean_uint8_dec_eq(v___x_1613_, v___x_1614_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v_a_1604_);
lean_ctor_set(v___x_1616_, 1, v_acc_1603_);
return v___x_1616_;
}
else
{
uint8_t v___x_1617_; 
v___x_1617_ = lean_uint8_dec_eq(v___x_1611_, v___x_1614_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1604_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_pos_1619_; lean_object* v_res_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1633_; 
v_pos_1619_ = lean_ctor_get(v___x_1618_, 0);
v_res_1620_ = lean_ctor_get(v___x_1618_, 1);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1622_ = v___x_1618_;
v_isShared_1623_ = v_isSharedCheck_1633_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_res_1620_);
lean_inc(v_pos_1619_);
lean_dec(v___x_1618_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1633_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1624_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1625_ = lean_int_dec_lt(v___x_1624_, v_res_1620_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1628_; 
lean_dec(v_res_1620_);
lean_dec_ref(v_acc_1603_);
v___x_1626_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1623_ == 0)
{
lean_ctor_set_tag(v___x_1622_, 1);
lean_ctor_set(v___x_1622_, 1, v___x_1626_);
v___x_1628_ = v___x_1622_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_pos_1619_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_del_object(v___x_1622_);
v___x_1630_ = lean_nat_abs(v_res_1620_);
lean_dec(v_res_1620_);
v___x_1631_ = lean_array_push(v_acc_1603_, v___x_1630_);
v_acc_1603_ = v___x_1631_;
v_a_1604_ = v_pos_1619_;
goto _start;
}
}
}
else
{
lean_object* v_pos_1634_; lean_object* v_err_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_dec_ref(v_acc_1603_);
v_pos_1634_ = lean_ctor_get(v___x_1618_, 0);
v_err_1635_ = lean_ctor_get(v___x_1618_, 1);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1618_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_err_1635_);
lean_inc(v_pos_1634_);
lean_dec(v___x_1618_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_pos_1634_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_err_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
else
{
lean_object* v___x_1643_; 
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v_a_1604_);
lean_ctor_set(v___x_1643_, 1, v_acc_1603_);
return v___x_1643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(lean_object* v_a_1644_){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0));
v___x_1646_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(v___x_1645_, v_a_1644_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(lean_object* v_a_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1647_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_pos_1649_; lean_object* v_res_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1681_; 
v_pos_1649_ = lean_ctor_get(v___x_1648_, 0);
v_res_1650_ = lean_ctor_get(v___x_1648_, 1);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1652_ = v___x_1648_;
v_isShared_1653_ = v_isSharedCheck_1681_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_res_1650_);
lean_inc(v_pos_1649_);
lean_dec(v___x_1648_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1681_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1655_ = lean_int_dec_lt(v_res_1650_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; lean_object* v___x_1658_; 
lean_dec(v_res_1650_);
v___x_1656_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1));
if (v_isShared_1653_ == 0)
{
lean_ctor_set_tag(v___x_1652_, 1);
lean_ctor_set(v___x_1652_, 1, v___x_1656_);
v___x_1658_ = v___x_1652_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_pos_1649_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
else
{
lean_object* v___x_1660_; 
lean_del_object(v___x_1652_);
v___x_1660_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v_pos_1649_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_pos_1661_; lean_object* v_res_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1671_; 
v_pos_1661_ = lean_ctor_get(v___x_1660_, 0);
v_res_1662_ = lean_ctor_get(v___x_1660_, 1);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1664_ = v___x_1660_;
v_isShared_1665_ = v_isSharedCheck_1671_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_res_1662_);
lean_inc(v_pos_1661_);
lean_dec(v___x_1660_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1671_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
v___x_1666_ = lean_nat_abs(v_res_1650_);
lean_dec(v_res_1650_);
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
lean_ctor_set(v___x_1667_, 1, v_res_1662_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 1, v___x_1667_);
v___x_1669_ = v___x_1664_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_pos_1661_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
else
{
lean_object* v_pos_1672_; lean_object* v_err_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec(v_res_1650_);
v_pos_1672_ = lean_ctor_get(v___x_1660_, 0);
v_err_1673_ = lean_ctor_get(v___x_1660_, 1);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1660_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_err_1673_);
lean_inc(v_pos_1672_);
lean_dec(v___x_1660_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_pos_1672_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_err_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1682_; lean_object* v_err_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
v_pos_1682_ = lean_ctor_get(v___x_1648_, 0);
v_err_1683_ = lean_ctor_get(v___x_1648_, 1);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1648_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_err_1683_);
lean_inc(v_pos_1682_);
lean_dec(v___x_1648_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_pos_1682_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_err_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints(lean_object* v_a_1691_){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes), 1, 0);
v___x_1693_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v___x_1692_, v_a_1691_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(lean_object* v_acc_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_array_1696_; lean_object* v_idx_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v_array_1696_ = lean_ctor_get(v_a_1695_, 0);
v_idx_1697_ = lean_ctor_get(v_a_1695_, 1);
v___x_1698_ = lean_byte_array_size(v_array_1696_);
v___x_1699_ = lean_nat_dec_lt(v_idx_1697_, v___x_1698_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
lean_dec_ref(v_acc_1694_);
v___x_1700_ = lean_box(0);
v___x_1701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1701_, 0, v_a_1695_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
return v___x_1701_;
}
else
{
uint8_t v___x_1702_; uint8_t v___x_1703_; uint8_t v___x_1704_; 
v___x_1702_ = lean_byte_array_fget(v_array_1696_, v_idx_1697_);
v___x_1703_ = 0;
v___x_1704_ = lean_uint8_dec_eq(v___x_1702_, v___x_1703_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1695_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_pos_1706_; lean_object* v_res_1707_; lean_object* v___x_1708_; 
v_pos_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_pos_1706_);
v_res_1707_ = lean_ctor_get(v___x_1705_, 1);
lean_inc(v_res_1707_);
lean_dec_ref_known(v___x_1705_, 2);
v___x_1708_ = lean_array_push(v_acc_1694_, v_res_1707_);
v_acc_1694_ = v___x_1708_;
v_a_1695_ = v_pos_1706_;
goto _start;
}
else
{
lean_object* v_pos_1710_; lean_object* v_err_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_dec_ref(v_acc_1694_);
v_pos_1710_ = lean_ctor_get(v___x_1705_, 0);
v_err_1711_ = lean_ctor_get(v___x_1705_, 1);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1705_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_err_1711_);
lean_inc(v_pos_1710_);
lean_dec(v___x_1705_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_pos_1710_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_err_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
else
{
lean_object* v___x_1719_; 
v___x_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1719_, 0, v_a_1695_);
lean_ctor_set(v___x_1719_, 1, v_acc_1694_);
return v___x_1719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(lean_object* v_a_1720_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0));
v___x_1722_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(v___x_1721_, v_a_1720_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1_spec__2(lean_object* v_acc_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v_array_1725_; lean_object* v_idx_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v_array_1725_ = lean_ctor_get(v_a_1724_, 0);
v_idx_1726_ = lean_ctor_get(v_a_1724_, 1);
v___x_1727_ = lean_byte_array_size(v_array_1725_);
v___x_1728_ = lean_nat_dec_lt(v_idx_1726_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec_ref(v_acc_1723_);
v___x_1729_ = lean_box(0);
v___x_1730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1730_, 0, v_a_1724_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
return v___x_1730_;
}
else
{
uint8_t v___x_1731_; uint8_t v___x_1732_; uint8_t v___x_1733_; 
v___x_1731_ = lean_byte_array_fget(v_array_1725_, v_idx_1726_);
v___x_1732_ = 0;
v___x_1733_ = lean_uint8_dec_eq(v___x_1731_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(v_a_1724_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_pos_1735_; lean_object* v_res_1736_; lean_object* v___x_1737_; 
v_pos_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_pos_1735_);
v_res_1736_ = lean_ctor_get(v___x_1734_, 1);
lean_inc(v_res_1736_);
lean_dec_ref_known(v___x_1734_, 2);
v___x_1737_ = lean_array_push(v_acc_1723_, v_res_1736_);
v_acc_1723_ = v___x_1737_;
v_a_1724_ = v_pos_1735_;
goto _start;
}
else
{
lean_object* v_pos_1739_; lean_object* v_err_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec_ref(v_acc_1723_);
v_pos_1739_ = lean_ctor_get(v___x_1734_, 0);
v_err_1740_ = lean_ctor_get(v___x_1734_, 1);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1734_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_err_1740_);
lean_inc(v_pos_1739_);
lean_dec(v___x_1734_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_pos_1739_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v_err_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
else
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v_a_1724_);
lean_ctor_set(v___x_1748_, 1, v_acc_1723_);
return v___x_1748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1(lean_object* v_a_1749_){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0));
v___x_1751_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1_spec__2(v___x_1750_, v_a_1749_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(lean_object* v_a_1752_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1752_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_pos_1754_; lean_object* v_res_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1892_; 
v_pos_1754_ = lean_ctor_get(v___x_1753_, 0);
v_res_1755_ = lean_ctor_get(v___x_1753_, 1);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1757_ = v___x_1753_;
v_isShared_1758_ = v_isSharedCheck_1892_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_res_1755_);
lean_inc(v_pos_1754_);
lean_dec(v___x_1753_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1892_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1759_ = lean_unsigned_to_nat(0u);
v___x_1760_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1761_ = lean_int_dec_lt(v___x_1760_, v_res_1755_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
lean_dec(v_res_1755_);
v___x_1762_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1758_ == 0)
{
lean_ctor_set_tag(v___x_1757_, 1);
lean_ctor_set(v___x_1757_, 1, v___x_1762_);
v___x_1764_ = v___x_1757_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_pos_1754_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
else
{
lean_object* v___x_1766_; 
lean_del_object(v___x_1757_);
v___x_1766_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(v_pos_1754_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_pos_1767_; lean_object* v_res_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1882_; 
v_pos_1767_ = lean_ctor_get(v___x_1766_, 0);
v_res_1768_ = lean_ctor_get(v___x_1766_, 1);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1770_ = v___x_1766_;
v_isShared_1771_ = v_isSharedCheck_1882_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_res_1768_);
lean_inc(v_pos_1767_);
lean_dec(v___x_1766_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1882_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v_array_1772_; lean_object* v_idx_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v_array_1772_ = lean_ctor_get(v_pos_1767_, 0);
v_idx_1773_ = lean_ctor_get(v_pos_1767_, 1);
v___x_1774_ = lean_byte_array_size(v_array_1772_);
v___x_1775_ = lean_nat_dec_lt(v_idx_1773_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; lean_object* v___x_1778_; 
lean_dec(v_res_1768_);
lean_dec(v_res_1755_);
v___x_1776_ = lean_box(0);
if (v_isShared_1771_ == 0)
{
lean_ctor_set_tag(v___x_1770_, 1);
lean_ctor_set(v___x_1770_, 1, v___x_1776_);
v___x_1778_ = v___x_1770_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_pos_1767_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
else
{
uint8_t v___x_1780_; uint8_t v_got_1781_; uint8_t v___x_1782_; 
v___x_1780_ = 0;
v_got_1781_ = lean_byte_array_fget(v_array_1772_, v_idx_1773_);
v___x_1782_ = lean_uint8_dec_eq(v_got_1781_, v___x_1780_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; lean_object* v___x_1785_; 
lean_dec(v_res_1768_);
lean_dec(v_res_1755_);
v___x_1783_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
if (v_isShared_1771_ == 0)
{
lean_ctor_set_tag(v___x_1770_, 1);
lean_ctor_set(v___x_1770_, 1, v___x_1783_);
v___x_1785_ = v___x_1770_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_pos_1767_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
else
{
lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1879_; 
lean_inc(v_idx_1773_);
lean_inc_ref(v_array_1772_);
lean_del_object(v___x_1770_);
v_isSharedCheck_1879_ = !lean_is_exclusive(v_pos_1767_);
if (v_isSharedCheck_1879_ == 0)
{
lean_object* v_unused_1880_; lean_object* v_unused_1881_; 
v_unused_1880_ = lean_ctor_get(v_pos_1767_, 1);
lean_dec(v_unused_1880_);
v_unused_1881_ = lean_ctor_get(v_pos_1767_, 0);
lean_dec(v_unused_1881_);
v___x_1788_ = v_pos_1767_;
v_isShared_1789_ = v_isSharedCheck_1879_;
goto v_resetjp_1787_;
}
else
{
lean_dec(v_pos_1767_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1879_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1790_ = lean_unsigned_to_nat(1u);
v___x_1791_ = lean_nat_add(v_idx_1773_, v___x_1790_);
lean_dec(v_idx_1773_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 1, v___x_1791_);
v___x_1793_ = v___x_1788_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_array_1772_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v___x_1793_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_pos_1795_; lean_object* v_res_1796_; lean_object* v___x_1797_; 
v_pos_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_pos_1795_);
v_res_1796_ = lean_ctor_get(v___x_1794_, 1);
lean_inc(v_res_1796_);
lean_dec_ref_known(v___x_1794_, 2);
v___x_1797_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1(v_pos_1795_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_pos_1798_; lean_object* v_res_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1859_; 
v_pos_1798_ = lean_ctor_get(v___x_1797_, 0);
v_res_1799_ = lean_ctor_get(v___x_1797_, 1);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1801_ = v___x_1797_;
v_isShared_1802_ = v_isSharedCheck_1859_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_res_1799_);
lean_inc(v_pos_1798_);
lean_dec(v___x_1797_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1859_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v_array_1803_; lean_object* v_idx_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v_array_1803_ = lean_ctor_get(v_pos_1798_, 0);
v_idx_1804_ = lean_ctor_get(v_pos_1798_, 1);
v___x_1805_ = lean_byte_array_size(v_array_1803_);
v___x_1806_ = lean_nat_dec_lt(v_idx_1804_, v___x_1805_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1809_; 
lean_dec(v_res_1799_);
lean_dec(v_res_1796_);
lean_dec(v_res_1768_);
lean_dec(v_res_1755_);
v___x_1807_ = lean_box(0);
if (v_isShared_1802_ == 0)
{
lean_ctor_set_tag(v___x_1801_, 1);
lean_ctor_set(v___x_1801_, 1, v___x_1807_);
v___x_1809_ = v___x_1801_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_pos_1798_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
else
{
uint8_t v_got_1811_; uint8_t v___x_1812_; 
v_got_1811_ = lean_byte_array_fget(v_array_1803_, v_idx_1804_);
v___x_1812_ = lean_uint8_dec_eq(v_got_1811_, v___x_1780_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1815_; 
lean_dec(v_res_1799_);
lean_dec(v_res_1796_);
lean_dec(v_res_1768_);
lean_dec(v_res_1755_);
v___x_1813_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
if (v_isShared_1802_ == 0)
{
lean_ctor_set_tag(v___x_1801_, 1);
lean_ctor_set(v___x_1801_, 1, v___x_1813_);
v___x_1815_ = v___x_1801_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_pos_1798_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
else
{
lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1856_; 
lean_inc(v_idx_1804_);
lean_inc_ref(v_array_1803_);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_pos_1798_);
if (v_isSharedCheck_1856_ == 0)
{
lean_object* v_unused_1857_; lean_object* v_unused_1858_; 
v_unused_1857_ = lean_ctor_get(v_pos_1798_, 1);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_pos_1798_, 0);
lean_dec(v_unused_1858_);
v___x_1818_ = v_pos_1798_;
v_isShared_1819_ = v_isSharedCheck_1856_;
goto v_resetjp_1817_;
}
else
{
lean_dec(v_pos_1798_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1856_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1820_ = lean_nat_abs(v_res_1755_);
lean_dec(v_res_1755_);
v___x_1821_ = lean_nat_add(v_idx_1804_, v___x_1790_);
lean_dec(v_idx_1804_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 1, v___x_1821_);
v___x_1823_ = v___x_1818_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_array_1803_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1824_ = lean_array_get_size(v_res_1768_);
v___x_1825_ = lean_nat_dec_eq(v___x_1824_, v___x_1759_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1826_ = lean_array_get_size(v_res_1799_);
v___x_1827_ = lean_nat_dec_eq(v___x_1826_, v___x_1759_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1831_; 
v___x_1828_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_1768_);
v___x_1829_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1820_);
lean_ctor_set(v___x_1829_, 1, v_res_1768_);
lean_ctor_set(v___x_1829_, 2, v___x_1828_);
lean_ctor_set(v___x_1829_, 3, v_res_1796_);
lean_ctor_set(v___x_1829_, 4, v_res_1799_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v___x_1829_);
lean_ctor_set(v___x_1801_, 0, v___x_1823_);
v___x_1831_ = v___x_1801_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
else
{
lean_object* v___x_1833_; uint8_t v___x_1834_; 
lean_dec(v_res_1799_);
v___x_1833_ = lean_array_get_size(v_res_1796_);
v___x_1834_ = lean_nat_dec_eq(v___x_1833_, v___x_1759_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1835_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1820_);
lean_ctor_set(v___x_1835_, 1, v_res_1768_);
lean_ctor_set(v___x_1835_, 2, v_res_1796_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v___x_1835_);
lean_ctor_set(v___x_1801_, 0, v___x_1823_);
v___x_1837_ = v___x_1801_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
lean_dec(v_res_1796_);
v___x_1839_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_1768_);
v___x_1840_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0));
v___x_1841_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1820_);
lean_ctor_set(v___x_1841_, 1, v_res_1768_);
lean_ctor_set(v___x_1841_, 2, v___x_1839_);
lean_ctor_set(v___x_1841_, 3, v___x_1840_);
lean_ctor_set(v___x_1841_, 4, v___x_1840_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v___x_1841_);
lean_ctor_set(v___x_1801_, 0, v___x_1823_);
v___x_1843_ = v___x_1801_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
else
{
lean_object* v___x_1845_; uint8_t v___x_1846_; 
lean_dec(v_res_1768_);
v___x_1845_ = lean_array_get_size(v_res_1799_);
lean_dec(v_res_1799_);
v___x_1846_ = lean_nat_dec_eq(v___x_1845_, v___x_1759_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
lean_dec(v___x_1820_);
lean_dec(v_res_1796_);
v___x_1847_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2));
if (v_isShared_1802_ == 0)
{
lean_ctor_set_tag(v___x_1801_, 1);
lean_ctor_set(v___x_1801_, 1, v___x_1847_);
lean_ctor_set(v___x_1801_, 0, v___x_1823_);
v___x_1849_ = v___x_1801_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1823_);
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
lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1820_);
lean_ctor_set(v___x_1851_, 1, v_res_1796_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v___x_1851_);
lean_ctor_set(v___x_1801_, 0, v___x_1823_);
v___x_1853_ = v___x_1801_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
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
lean_object* v_pos_1860_; lean_object* v_err_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_res_1796_);
lean_dec(v_res_1768_);
lean_dec(v_res_1755_);
v_pos_1860_ = lean_ctor_get(v___x_1797_, 0);
v_err_1861_ = lean_ctor_get(v___x_1797_, 1);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1797_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_err_1861_);
lean_inc(v_pos_1860_);
lean_dec(v___x_1797_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_pos_1860_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_err_1861_);
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
else
{
lean_object* v_pos_1869_; lean_object* v_err_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec(v_res_1768_);
lean_dec(v_res_1755_);
v_pos_1869_ = lean_ctor_get(v___x_1794_, 0);
v_err_1870_ = lean_ctor_get(v___x_1794_, 1);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1794_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_err_1870_);
lean_inc(v_pos_1869_);
lean_dec(v___x_1794_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_pos_1869_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_err_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
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
lean_object* v_pos_1883_; lean_object* v_err_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec(v_res_1755_);
v_pos_1883_ = lean_ctor_get(v___x_1766_, 0);
v_err_1884_ = lean_ctor_get(v___x_1766_, 1);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1766_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_err_1884_);
lean_inc(v_pos_1883_);
lean_dec(v___x_1766_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_pos_1883_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_err_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1893_; lean_object* v_err_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
v_pos_1893_ = lean_ctor_get(v___x_1753_, 0);
v_err_1894_ = lean_ctor_get(v___x_1753_, 1);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1753_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_err_1894_);
lean_inc(v_pos_1893_);
lean_dec(v___x_1753_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_pos_1893_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_err_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(lean_object* v_a_1902_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v_a_1902_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_pos_1904_; lean_object* v_res_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1939_; 
v_pos_1904_ = lean_ctor_get(v___x_1903_, 0);
v_res_1905_ = lean_ctor_get(v___x_1903_, 1);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1907_ = v___x_1903_;
v_isShared_1908_ = v_isSharedCheck_1939_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_res_1905_);
lean_inc(v_pos_1904_);
lean_dec(v___x_1903_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1939_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v_array_1909_; lean_object* v_idx_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; 
v_array_1909_ = lean_ctor_get(v_pos_1904_, 0);
v_idx_1910_ = lean_ctor_get(v_pos_1904_, 1);
v___x_1911_ = lean_byte_array_size(v_array_1909_);
v___x_1912_ = lean_nat_dec_lt(v_idx_1910_, v___x_1911_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
lean_dec(v_res_1905_);
v___x_1913_ = lean_box(0);
if (v_isShared_1908_ == 0)
{
lean_ctor_set_tag(v___x_1907_, 1);
lean_ctor_set(v___x_1907_, 1, v___x_1913_);
v___x_1915_ = v___x_1907_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_pos_1904_);
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
uint8_t v___x_1917_; uint8_t v_got_1918_; uint8_t v___x_1919_; 
v___x_1917_ = 0;
v_got_1918_ = lean_byte_array_fget(v_array_1909_, v_idx_1910_);
v___x_1919_ = lean_uint8_dec_eq(v_got_1918_, v___x_1917_);
if (v___x_1919_ == 0)
{
lean_object* v___x_1920_; lean_object* v___x_1922_; 
lean_dec(v_res_1905_);
v___x_1920_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
if (v_isShared_1908_ == 0)
{
lean_ctor_set_tag(v___x_1907_, 1);
lean_ctor_set(v___x_1907_, 1, v___x_1920_);
v___x_1922_ = v___x_1907_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_pos_1904_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v___x_1920_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
else
{
lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1936_; 
lean_inc(v_idx_1910_);
lean_inc_ref(v_array_1909_);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_pos_1904_);
if (v_isSharedCheck_1936_ == 0)
{
lean_object* v_unused_1937_; lean_object* v_unused_1938_; 
v_unused_1937_ = lean_ctor_get(v_pos_1904_, 1);
lean_dec(v_unused_1937_);
v_unused_1938_ = lean_ctor_get(v_pos_1904_, 0);
lean_dec(v_unused_1938_);
v___x_1925_ = v_pos_1904_;
v_isShared_1926_ = v_isSharedCheck_1936_;
goto v_resetjp_1924_;
}
else
{
lean_dec(v_pos_1904_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1936_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1927_ = lean_unsigned_to_nat(1u);
v___x_1928_ = lean_nat_add(v_idx_1910_, v___x_1927_);
lean_dec(v_idx_1910_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 1, v___x_1928_);
v___x_1930_ = v___x_1925_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_array_1909_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1931_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1931_, 0, v_res_1905_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 1, v___x_1931_);
lean_ctor_set(v___x_1907_, 0, v___x_1930_);
v___x_1933_ = v___x_1907_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1930_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_1940_; lean_object* v_err_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
v_pos_1940_ = lean_ctor_get(v___x_1903_, 0);
v_err_1941_ = lean_ctor_get(v___x_1903_, 1);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1903_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_err_1941_);
lean_inc(v_pos_1940_);
lean_dec(v___x_1903_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_pos_1940_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_err_1941_);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(lean_object* v_a_1950_){
_start:
{
lean_object* v_array_1951_; lean_object* v_idx_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
v_array_1951_ = lean_ctor_get(v_a_1950_, 0);
v_idx_1952_ = lean_ctor_get(v_a_1950_, 1);
v___x_1953_ = lean_byte_array_size(v_array_1951_);
v___x_1954_ = lean_nat_dec_lt(v_idx_1952_, v___x_1953_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_box(0);
v___x_1956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1956_, 0, v_a_1950_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
return v___x_1956_;
}
else
{
lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1978_; 
lean_inc(v_idx_1952_);
lean_inc_ref(v_array_1951_);
v_isSharedCheck_1978_ = !lean_is_exclusive(v_a_1950_);
if (v_isSharedCheck_1978_ == 0)
{
lean_object* v_unused_1979_; lean_object* v_unused_1980_; 
v_unused_1979_ = lean_ctor_get(v_a_1950_, 1);
lean_dec(v_unused_1979_);
v_unused_1980_ = lean_ctor_get(v_a_1950_, 0);
lean_dec(v_unused_1980_);
v___x_1958_ = v_a_1950_;
v_isShared_1959_ = v_isSharedCheck_1978_;
goto v_resetjp_1957_;
}
else
{
lean_dec(v_a_1950_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1978_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
uint8_t v_c_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v_it_x27_1964_; 
v_c_1960_ = lean_byte_array_fget(v_array_1951_, v_idx_1952_);
v___x_1961_ = lean_unsigned_to_nat(1u);
v___x_1962_ = lean_nat_add(v_idx_1952_, v___x_1961_);
lean_dec(v_idx_1952_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 1, v___x_1962_);
v_it_x27_1964_ = v___x_1958_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_array_1951_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v___x_1962_);
v_it_x27_1964_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
uint8_t v___x_1965_; uint8_t v___x_1966_; 
v___x_1965_ = 97;
v___x_1966_ = lean_uint8_dec_eq(v_c_1960_, v___x_1965_);
if (v___x_1966_ == 0)
{
uint8_t v___x_1967_; uint8_t v___x_1968_; 
v___x_1967_ = 100;
v___x_1968_ = lean_uint8_dec_eq(v_c_1960_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1969_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0));
v___x_1970_ = lean_uint8_to_nat(v_c_1960_);
v___x_1971_ = l_Nat_reprFast(v___x_1970_);
v___x_1972_ = lean_string_append(v___x_1969_, v___x_1971_);
lean_dec_ref(v___x_1971_);
v___x_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1972_);
v___x_1974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1974_, 0, v_it_x27_1964_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
return v___x_1974_;
}
else
{
lean_object* v___x_1975_; 
v___x_1975_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(v_it_x27_1964_);
return v___x_1975_;
}
}
else
{
lean_object* v___x_1976_; 
v___x_1976_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(v_it_x27_1964_);
return v___x_1976_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(lean_object* v_acc_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v___x_1983_; 
lean_inc_ref(v_a_1982_);
v___x_1983_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(v_a_1982_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_pos_1984_; lean_object* v_res_1985_; lean_object* v___x_1986_; 
lean_dec_ref(v_a_1982_);
v_pos_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_pos_1984_);
v_res_1985_ = lean_ctor_get(v___x_1983_, 1);
lean_inc(v_res_1985_);
lean_dec_ref_known(v___x_1983_, 2);
v___x_1986_ = lean_array_push(v_acc_1981_, v_res_1985_);
v_acc_1981_ = v___x_1986_;
v_a_1982_ = v_pos_1984_;
goto _start;
}
else
{
lean_object* v_pos_1988_; lean_object* v_err_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2002_; 
v_pos_1988_ = lean_ctor_get(v___x_1983_, 0);
v_err_1989_ = lean_ctor_get(v___x_1983_, 1);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1991_ = v___x_1983_;
v_isShared_1992_ = v_isSharedCheck_2002_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_err_1989_);
lean_inc(v_pos_1988_);
lean_dec(v___x_1983_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2002_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v_idx_1993_; lean_object* v_idx_1994_; uint8_t v___x_1995_; 
v_idx_1993_ = lean_ctor_get(v_a_1982_, 1);
lean_inc(v_idx_1993_);
lean_dec_ref(v_a_1982_);
v_idx_1994_ = lean_ctor_get(v_pos_1988_, 1);
v___x_1995_ = lean_nat_dec_eq(v_idx_1993_, v_idx_1994_);
lean_dec(v_idx_1993_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1997_; 
lean_dec_ref(v_acc_1981_);
if (v_isShared_1992_ == 0)
{
v___x_1997_ = v___x_1991_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_pos_1988_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_err_1989_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
else
{
lean_object* v___x_2000_; 
lean_dec(v_err_1989_);
if (v_isShared_1992_ == 0)
{
lean_ctor_set_tag(v___x_1991_, 0);
lean_ctor_set(v___x_1991_, 1, v_acc_1981_);
v___x_2000_ = v___x_1991_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_pos_1988_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_acc_1981_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(lean_object* v_a_2006_){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0));
v___x_2008_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(v___x_2007_, v_a_2006_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_pos_2009_; lean_object* v_array_2010_; lean_object* v_idx_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v_pos_2009_ = lean_ctor_get(v___x_2008_, 0);
v_array_2010_ = lean_ctor_get(v_pos_2009_, 0);
v_idx_2011_ = lean_ctor_get(v_pos_2009_, 1);
v___x_2012_ = lean_byte_array_size(v_array_2010_);
v___x_2013_ = lean_nat_dec_lt(v_idx_2011_, v___x_2012_);
if (v___x_2013_ == 0)
{
return v___x_2008_;
}
else
{
lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2021_; 
lean_inc(v_pos_2009_);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2021_ == 0)
{
lean_object* v_unused_2022_; lean_object* v_unused_2023_; 
v_unused_2022_ = lean_ctor_get(v___x_2008_, 1);
lean_dec(v_unused_2022_);
v_unused_2023_ = lean_ctor_get(v___x_2008_, 0);
lean_dec(v_unused_2023_);
v___x_2015_ = v___x_2008_;
v_isShared_2016_ = v_isSharedCheck_2021_;
goto v_resetjp_2014_;
}
else
{
lean_dec(v___x_2008_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2021_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2017_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__1));
if (v_isShared_2016_ == 0)
{
lean_ctor_set_tag(v___x_2015_, 1);
lean_ctor_set(v___x_2015_, 1, v___x_2017_);
v___x_2019_ = v___x_2015_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_pos_2009_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
else
{
return v___x_2008_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_parseActions(lean_object* v_a_2024_){
_start:
{
lean_object* v_array_2025_; lean_object* v_idx_2026_; lean_object* v___x_2027_; uint8_t v___x_2028_; 
v_array_2025_ = lean_ctor_get(v_a_2024_, 0);
v_idx_2026_ = lean_ctor_get(v_a_2024_, 1);
v___x_2027_ = lean_byte_array_size(v_array_2025_);
v___x_2028_ = lean_nat_dec_lt(v_idx_2026_, v___x_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = lean_box(0);
v___x_2030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2030_, 0, v_a_2024_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
return v___x_2030_;
}
else
{
uint8_t v___x_2031_; uint8_t v___x_2032_; uint8_t v___x_2033_; 
v___x_2031_ = lean_byte_array_fget(v_array_2025_, v_idx_2026_);
v___x_2032_ = 97;
v___x_2033_ = lean_uint8_dec_eq(v___x_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
uint8_t v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = 100;
v___x_2035_ = lean_uint8_dec_eq(v___x_2031_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(v_a_2024_);
return v___x_2036_;
}
else
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(v_a_2024_);
return v___x_2037_;
}
}
else
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(v_a_2024_);
return v___x_2038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object* v_path_2039_){
_start:
{
lean_object* v___x_2041_; 
v___x_2041_ = l_IO_FS_readBinFile(v_path_2039_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2063_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2063_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2063_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_parseActions), 1, 0);
v___x_2047_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_2046_, v_a_2042_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2058_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2050_ = v___x_2047_;
v_isShared_2051_ = v_isSharedCheck_2058_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2047_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2058_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
lean_ctor_set_tag(v___x_2050_, 18);
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2055_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set_tag(v___x_2044_, 1);
lean_ctor_set(v___x_2044_, 0, v___x_2053_);
v___x_2055_ = v___x_2044_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; 
v_a_2059_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2047_, 1);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v_a_2059_);
v___x_2061_ = v___x_2044_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
v_a_2064_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2041_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2041_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof___boxed(lean_object* v_path_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(v_path_2072_);
lean_dec_ref(v_path_2072_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_parseLRATProof(lean_object* v_proof_2075_){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_parseActions), 1, 0);
v___x_2077_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_2076_, v_proof_2075_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(lean_object* v_as_2079_, size_t v_i_2080_, size_t v_stop_2081_, lean_object* v_b_2082_){
_start:
{
uint8_t v___x_2083_; 
v___x_2083_ = lean_usize_dec_eq(v_i_2080_, v_stop_2081_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; size_t v___x_2089_; size_t v___x_2090_; 
v___x_2084_ = lean_array_uget_borrowed(v_as_2079_, v_i_2080_);
lean_inc(v___x_2084_);
v___x_2085_ = l_Nat_reprFast(v___x_2084_);
v___x_2086_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2087_ = lean_string_append(v___x_2085_, v___x_2086_);
v___x_2088_ = lean_string_append(v_b_2082_, v___x_2087_);
lean_dec_ref(v___x_2087_);
v___x_2089_ = ((size_t)1ULL);
v___x_2090_ = lean_usize_add(v_i_2080_, v___x_2089_);
v_i_2080_ = v___x_2090_;
v_b_2082_ = v___x_2088_;
goto _start;
}
else
{
return v_b_2082_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___boxed(lean_object* v_as_2092_, lean_object* v_i_2093_, lean_object* v_stop_2094_, lean_object* v_b_2095_){
_start:
{
size_t v_i_boxed_2096_; size_t v_stop_boxed_2097_; lean_object* v_res_2098_; 
v_i_boxed_2096_ = lean_unbox_usize(v_i_2093_);
lean_dec(v_i_2093_);
v_stop_boxed_2097_ = lean_unbox_usize(v_stop_2094_);
lean_dec(v_stop_2094_);
v_res_2098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_as_2092_, v_i_boxed_2096_, v_stop_boxed_2097_, v_b_2095_);
lean_dec_ref(v_as_2092_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(lean_object* v_ids_2100_){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2101_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2102_ = lean_unsigned_to_nat(0u);
v___x_2103_ = lean_array_get_size(v_ids_2100_);
v___x_2104_ = lean_nat_dec_lt(v___x_2102_, v___x_2103_);
if (v___x_2104_ == 0)
{
return v___x_2101_;
}
else
{
uint8_t v___x_2105_; 
v___x_2105_ = lean_nat_dec_le(v___x_2103_, v___x_2103_);
if (v___x_2105_ == 0)
{
if (v___x_2104_ == 0)
{
return v___x_2101_;
}
else
{
size_t v___x_2106_; size_t v___x_2107_; lean_object* v___x_2108_; 
v___x_2106_ = ((size_t)0ULL);
v___x_2107_ = lean_usize_of_nat(v___x_2103_);
v___x_2108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_ids_2100_, v___x_2106_, v___x_2107_, v___x_2101_);
return v___x_2108_;
}
}
else
{
size_t v___x_2109_; size_t v___x_2110_; lean_object* v___x_2111_; 
v___x_2109_ = ((size_t)0ULL);
v___x_2110_ = lean_usize_of_nat(v___x_2103_);
v___x_2111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_ids_2100_, v___x_2109_, v___x_2110_, v___x_2101_);
return v___x_2111_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___boxed(lean_object* v_ids_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_ids_2112_);
lean_dec_ref(v_ids_2112_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(lean_object* v_hint_2115_){
_start:
{
lean_object* v_fst_2116_; lean_object* v_snd_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v_fst_2116_ = lean_ctor_get(v_hint_2115_, 0);
lean_inc(v_fst_2116_);
v_snd_2117_ = lean_ctor_get(v_hint_2115_, 1);
lean_inc(v_snd_2117_);
lean_dec_ref(v_hint_2115_);
v___x_2118_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0));
v___x_2119_ = l_Nat_reprFast(v_fst_2116_);
v___x_2120_ = lean_string_append(v___x_2118_, v___x_2119_);
lean_dec_ref(v___x_2119_);
v___x_2121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2122_ = lean_string_append(v___x_2120_, v___x_2121_);
v___x_2123_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_snd_2117_);
lean_dec(v_snd_2117_);
v___x_2124_ = lean_string_append(v___x_2122_, v___x_2123_);
lean_dec_ref(v___x_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(lean_object* v_as_2125_, size_t v_i_2126_, size_t v_stop_2127_, lean_object* v_b_2128_){
_start:
{
uint8_t v___x_2129_; 
v___x_2129_ = lean_usize_dec_eq(v_i_2126_, v_stop_2127_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; size_t v___x_2133_; size_t v___x_2134_; 
v___x_2130_ = lean_array_uget_borrowed(v_as_2125_, v_i_2126_);
lean_inc(v___x_2130_);
v___x_2131_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(v___x_2130_);
v___x_2132_ = lean_string_append(v_b_2128_, v___x_2131_);
lean_dec_ref(v___x_2131_);
v___x_2133_ = ((size_t)1ULL);
v___x_2134_ = lean_usize_add(v_i_2126_, v___x_2133_);
v_i_2126_ = v___x_2134_;
v_b_2128_ = v___x_2132_;
goto _start;
}
else
{
return v_b_2128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0___boxed(lean_object* v_as_2136_, lean_object* v_i_2137_, lean_object* v_stop_2138_, lean_object* v_b_2139_){
_start:
{
size_t v_i_boxed_2140_; size_t v_stop_boxed_2141_; lean_object* v_res_2142_; 
v_i_boxed_2140_ = lean_unbox_usize(v_i_2137_);
lean_dec(v_i_2137_);
v_stop_boxed_2141_ = lean_unbox_usize(v_stop_2138_);
lean_dec(v_stop_2138_);
v_res_2142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_as_2136_, v_i_boxed_2140_, v_stop_boxed_2141_, v_b_2139_);
lean_dec_ref(v_as_2136_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(lean_object* v_hints_2143_){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2144_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2145_ = lean_unsigned_to_nat(0u);
v___x_2146_ = lean_array_get_size(v_hints_2143_);
v___x_2147_ = lean_nat_dec_lt(v___x_2145_, v___x_2146_);
if (v___x_2147_ == 0)
{
return v___x_2144_;
}
else
{
uint8_t v___x_2148_; 
v___x_2148_ = lean_nat_dec_le(v___x_2146_, v___x_2146_);
if (v___x_2148_ == 0)
{
if (v___x_2147_ == 0)
{
return v___x_2144_;
}
else
{
size_t v___x_2149_; size_t v___x_2150_; lean_object* v___x_2151_; 
v___x_2149_ = ((size_t)0ULL);
v___x_2150_ = lean_usize_of_nat(v___x_2146_);
v___x_2151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_hints_2143_, v___x_2149_, v___x_2150_, v___x_2144_);
return v___x_2151_;
}
}
else
{
size_t v___x_2152_; size_t v___x_2153_; lean_object* v___x_2154_; 
v___x_2152_ = ((size_t)0ULL);
v___x_2153_ = lean_usize_of_nat(v___x_2146_);
v___x_2154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_hints_2143_, v___x_2152_, v___x_2153_, v___x_2144_);
return v___x_2154_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___boxed(lean_object* v_hints_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(v_hints_2155_);
lean_dec_ref(v_hints_2155_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(lean_object* v_as_2157_, size_t v_i_2158_, size_t v_stop_2159_, lean_object* v_b_2160_){
_start:
{
uint8_t v___x_2161_; 
v___x_2161_ = lean_usize_dec_eq(v_i_2158_, v_stop_2159_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; size_t v___x_2167_; size_t v___x_2168_; 
v___x_2162_ = lean_array_uget_borrowed(v_as_2157_, v_i_2158_);
v___x_2163_ = l_Int_repr(v___x_2162_);
v___x_2164_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2165_ = lean_string_append(v___x_2163_, v___x_2164_);
v___x_2166_ = lean_string_append(v_b_2160_, v___x_2165_);
lean_dec_ref(v___x_2165_);
v___x_2167_ = ((size_t)1ULL);
v___x_2168_ = lean_usize_add(v_i_2158_, v___x_2167_);
v_i_2158_ = v___x_2168_;
v_b_2160_ = v___x_2166_;
goto _start;
}
else
{
return v_b_2160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0___boxed(lean_object* v_as_2170_, lean_object* v_i_2171_, lean_object* v_stop_2172_, lean_object* v_b_2173_){
_start:
{
size_t v_i_boxed_2174_; size_t v_stop_boxed_2175_; lean_object* v_res_2176_; 
v_i_boxed_2174_ = lean_unbox_usize(v_i_2171_);
lean_dec(v_i_2171_);
v_stop_boxed_2175_ = lean_unbox_usize(v_stop_2172_);
lean_dec(v_stop_2172_);
v_res_2176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_as_2170_, v_i_boxed_2174_, v_stop_boxed_2175_, v_b_2173_);
lean_dec_ref(v_as_2170_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(lean_object* v_clause_2177_){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v___x_2178_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2179_ = lean_unsigned_to_nat(0u);
v___x_2180_ = lean_array_get_size(v_clause_2177_);
v___x_2181_ = lean_nat_dec_lt(v___x_2179_, v___x_2180_);
if (v___x_2181_ == 0)
{
return v___x_2178_;
}
else
{
uint8_t v___x_2182_; 
v___x_2182_ = lean_nat_dec_le(v___x_2180_, v___x_2180_);
if (v___x_2182_ == 0)
{
if (v___x_2181_ == 0)
{
return v___x_2178_;
}
else
{
size_t v___x_2183_; size_t v___x_2184_; lean_object* v___x_2185_; 
v___x_2183_ = ((size_t)0ULL);
v___x_2184_ = lean_usize_of_nat(v___x_2180_);
v___x_2185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_clause_2177_, v___x_2183_, v___x_2184_, v___x_2178_);
return v___x_2185_;
}
}
else
{
size_t v___x_2186_; size_t v___x_2187_; lean_object* v___x_2188_; 
v___x_2186_ = ((size_t)0ULL);
v___x_2187_ = lean_usize_of_nat(v___x_2180_);
v___x_2188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_clause_2177_, v___x_2186_, v___x_2187_, v___x_2178_);
return v___x_2188_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___boxed(lean_object* v_clause_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_clause_2189_);
lean_dec_ref(v_clause_2189_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(lean_object* v_a_2195_){
_start:
{
switch(lean_obj_tag(v_a_2195_))
{
case 0:
{
lean_object* v_id_2196_; lean_object* v_rupHints_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_id_2196_ = lean_ctor_get(v_a_2195_, 0);
lean_inc(v_id_2196_);
v_rupHints_2197_ = lean_ctor_get(v_a_2195_, 1);
lean_inc_ref(v_rupHints_2197_);
lean_dec_ref_known(v_a_2195_, 2);
v___x_2198_ = l_Nat_reprFast(v_id_2196_);
v___x_2199_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__0));
v___x_2200_ = lean_string_append(v___x_2198_, v___x_2199_);
v___x_2201_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2197_);
lean_dec_ref(v_rupHints_2197_);
v___x_2202_ = lean_string_append(v___x_2200_, v___x_2201_);
lean_dec_ref(v___x_2201_);
v___x_2203_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2204_ = lean_string_append(v___x_2202_, v___x_2203_);
return v___x_2204_;
}
case 1:
{
lean_object* v_id_2205_; lean_object* v_c_2206_; lean_object* v_rupHints_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v_id_2205_ = lean_ctor_get(v_a_2195_, 0);
lean_inc(v_id_2205_);
v_c_2206_ = lean_ctor_get(v_a_2195_, 1);
lean_inc(v_c_2206_);
v_rupHints_2207_ = lean_ctor_get(v_a_2195_, 2);
lean_inc_ref(v_rupHints_2207_);
lean_dec_ref_known(v_a_2195_, 3);
v___x_2208_ = l_Nat_reprFast(v_id_2205_);
v___x_2209_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2210_ = lean_string_append(v___x_2208_, v___x_2209_);
v___x_2211_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_c_2206_);
lean_dec(v_c_2206_);
v___x_2212_ = lean_string_append(v___x_2210_, v___x_2211_);
lean_dec_ref(v___x_2211_);
v___x_2213_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2));
v___x_2214_ = lean_string_append(v___x_2212_, v___x_2213_);
v___x_2215_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2207_);
lean_dec_ref(v_rupHints_2207_);
v___x_2216_ = lean_string_append(v___x_2214_, v___x_2215_);
lean_dec_ref(v___x_2215_);
v___x_2217_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2218_ = lean_string_append(v___x_2216_, v___x_2217_);
return v___x_2218_;
}
case 2:
{
lean_object* v_id_2219_; lean_object* v_c_2220_; lean_object* v_rupHints_2221_; lean_object* v_ratHints_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_id_2219_ = lean_ctor_get(v_a_2195_, 0);
lean_inc(v_id_2219_);
v_c_2220_ = lean_ctor_get(v_a_2195_, 1);
lean_inc(v_c_2220_);
v_rupHints_2221_ = lean_ctor_get(v_a_2195_, 3);
lean_inc_ref(v_rupHints_2221_);
v_ratHints_2222_ = lean_ctor_get(v_a_2195_, 4);
lean_inc_ref(v_ratHints_2222_);
lean_dec_ref_known(v_a_2195_, 5);
v___x_2223_ = l_Nat_reprFast(v_id_2219_);
v___x_2224_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2225_ = lean_string_append(v___x_2223_, v___x_2224_);
v___x_2226_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_c_2220_);
lean_dec(v_c_2220_);
v___x_2227_ = lean_string_append(v___x_2225_, v___x_2226_);
lean_dec_ref(v___x_2226_);
v___x_2228_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2));
v___x_2229_ = lean_string_append(v___x_2227_, v___x_2228_);
v___x_2230_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2221_);
lean_dec_ref(v_rupHints_2221_);
v___x_2231_ = lean_string_append(v___x_2229_, v___x_2230_);
lean_dec_ref(v___x_2230_);
v___x_2232_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(v_ratHints_2222_);
lean_dec_ref(v_ratHints_2222_);
v___x_2233_ = lean_string_append(v___x_2231_, v___x_2232_);
lean_dec_ref(v___x_2232_);
v___x_2234_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2235_ = lean_string_append(v___x_2233_, v___x_2234_);
return v___x_2235_;
}
default: 
{
lean_object* v_ids_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v_ids_2236_ = lean_ctor_get(v_a_2195_, 0);
lean_inc_ref(v_ids_2236_);
lean_dec_ref_known(v_a_2195_, 1);
v___x_2237_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3));
v___x_2238_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_ids_2236_);
lean_dec_ref(v_ids_2236_);
v___x_2239_ = lean_string_append(v___x_2237_, v___x_2238_);
lean_dec_ref(v___x_2238_);
v___x_2240_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2241_ = lean_string_append(v___x_2239_, v___x_2240_);
return v___x_2241_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(lean_object* v_as_2243_, size_t v_i_2244_, size_t v_stop_2245_, lean_object* v_b_2246_){
_start:
{
uint8_t v___x_2247_; 
v___x_2247_ = lean_usize_dec_eq(v_i_2244_, v_stop_2245_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; size_t v___x_2253_; size_t v___x_2254_; 
v___x_2248_ = lean_array_uget_borrowed(v_as_2243_, v_i_2244_);
lean_inc(v___x_2248_);
v___x_2249_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(v___x_2248_);
v___x_2250_ = lean_string_append(v_b_2246_, v___x_2249_);
lean_dec_ref(v___x_2249_);
v___x_2251_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___closed__0));
v___x_2252_ = lean_string_append(v___x_2250_, v___x_2251_);
v___x_2253_ = ((size_t)1ULL);
v___x_2254_ = lean_usize_add(v_i_2244_, v___x_2253_);
v_i_2244_ = v___x_2254_;
v_b_2246_ = v___x_2252_;
goto _start;
}
else
{
return v_b_2246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___boxed(lean_object* v_as_2256_, lean_object* v_i_2257_, lean_object* v_stop_2258_, lean_object* v_b_2259_){
_start:
{
size_t v_i_boxed_2260_; size_t v_stop_boxed_2261_; lean_object* v_res_2262_; 
v_i_boxed_2260_ = lean_unbox_usize(v_i_2257_);
lean_dec(v_i_2257_);
v_stop_boxed_2261_ = lean_unbox_usize(v_stop_2258_);
lean_dec(v_stop_2258_);
v_res_2262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_as_2256_, v_i_boxed_2260_, v_stop_boxed_2261_, v_b_2259_);
lean_dec_ref(v_as_2256_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString(lean_object* v_proof_2263_){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; uint8_t v___x_2267_; 
v___x_2264_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2265_ = lean_unsigned_to_nat(0u);
v___x_2266_ = lean_array_get_size(v_proof_2263_);
v___x_2267_ = lean_nat_dec_lt(v___x_2265_, v___x_2266_);
if (v___x_2267_ == 0)
{
return v___x_2264_;
}
else
{
uint8_t v___x_2268_; 
v___x_2268_ = lean_nat_dec_le(v___x_2266_, v___x_2266_);
if (v___x_2268_ == 0)
{
if (v___x_2267_ == 0)
{
return v___x_2264_;
}
else
{
size_t v___x_2269_; size_t v___x_2270_; lean_object* v___x_2271_; 
v___x_2269_ = ((size_t)0ULL);
v___x_2270_ = lean_usize_of_nat(v___x_2266_);
v___x_2271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_proof_2263_, v___x_2269_, v___x_2270_, v___x_2264_);
return v___x_2271_;
}
}
else
{
size_t v___x_2272_; size_t v___x_2273_; lean_object* v___x_2274_; 
v___x_2272_ = ((size_t)0ULL);
v___x_2273_ = lean_usize_of_nat(v___x_2266_);
v___x_2274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_proof_2263_, v___x_2272_, v___x_2273_, v___x_2264_);
return v___x_2274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString___boxed(lean_object* v_proof_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_proof_2275_);
lean_dec_ref(v_proof_2275_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startDelete(lean_object* v_acc_2277_){
_start:
{
uint8_t v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = 100;
v___x_2279_ = lean_byte_array_push(v_acc_2277_, v___x_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(lean_object* v_acc_2280_, uint64_t v_lit_2281_){
_start:
{
uint8_t v___y_2283_; uint64_t v___x_2288_; uint8_t v___x_2289_; 
v___x_2288_ = 0ULL;
v___x_2289_ = lean_uint64_dec_eq(v_lit_2281_, v___x_2288_);
if (v___x_2289_ == 0)
{
uint64_t v___x_2290_; uint8_t v___x_2291_; 
v___x_2290_ = 127ULL;
v___x_2291_ = lean_uint64_dec_lt(v___x_2290_, v_lit_2281_);
if (v___x_2291_ == 0)
{
uint8_t v___x_2292_; uint8_t v___x_2293_; uint8_t v___x_2294_; 
v___x_2292_ = lean_uint64_to_uint8(v_lit_2281_);
v___x_2293_ = 127;
v___x_2294_ = lean_uint8_land(v___x_2292_, v___x_2293_);
v___y_2283_ = v___x_2294_;
goto v___jp_2282_;
}
else
{
uint8_t v___x_2295_; uint8_t v___x_2296_; uint8_t v___x_2297_; uint8_t v___x_2298_; uint8_t v___x_2299_; 
v___x_2295_ = lean_uint64_to_uint8(v_lit_2281_);
v___x_2296_ = 127;
v___x_2297_ = lean_uint8_land(v___x_2295_, v___x_2296_);
v___x_2298_ = 128;
v___x_2299_ = lean_uint8_lor(v___x_2297_, v___x_2298_);
v___y_2283_ = v___x_2299_;
goto v___jp_2282_;
}
}
else
{
return v_acc_2280_;
}
v___jp_2282_:
{
lean_object* v_acc_2284_; uint64_t v___x_2285_; uint64_t v___x_2286_; 
v_acc_2284_ = lean_byte_array_push(v_acc_2280_, v___y_2283_);
v___x_2285_ = 7ULL;
v___x_2286_ = lean_uint64_shift_right(v_lit_2281_, v___x_2285_);
v_acc_2280_ = v_acc_2284_;
v_lit_2281_ = v___x_2286_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode___boxed(lean_object* v_acc_2300_, lean_object* v_lit_2301_){
_start:
{
uint64_t v_lit_boxed_2302_; lean_object* v_res_2303_; 
v_lit_boxed_2302_ = lean_unbox_uint64(v_lit_2301_);
lean_dec_ref(v_lit_2301_);
v_res_2303_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(v_acc_2300_, v_lit_boxed_2302_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(lean_object* v_msg_2304_){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2305_ = l_ByteArray_empty;
v___x_2306_ = lean_panic_fn_borrowed(v___x_2305_, v_msg_2304_);
return v___x_2306_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0(void){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = lean_cstr_to_nat("18446744073709551615");
return v___x_2307_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4(void){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2311_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3));
v___x_2312_ = lean_unsigned_to_nat(4u);
v___x_2313_ = lean_unsigned_to_nat(400u);
v___x_2314_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2));
v___x_2315_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1));
v___x_2316_ = l_mkPanicMessageWithDecl(v___x_2315_, v___x_2314_, v___x_2313_, v___x_2312_, v___x_2311_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(lean_object* v_acc_2317_, lean_object* v_lit_2318_){
_start:
{
lean_object* v___y_2320_; lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___x_2327_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_2328_ = lean_int_dec_lt(v___x_2327_, v_lit_2318_);
if (v___x_2328_ == 0)
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2329_ = lean_unsigned_to_nat(2u);
v___x_2330_ = lean_nat_abs(v_lit_2318_);
v___x_2331_ = lean_nat_mul(v___x_2329_, v___x_2330_);
lean_dec(v___x_2330_);
v___x_2332_ = lean_unsigned_to_nat(1u);
v___x_2333_ = lean_nat_add(v___x_2331_, v___x_2332_);
lean_dec(v___x_2331_);
v___y_2320_ = v___x_2333_;
goto v___jp_2319_;
}
else
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2334_ = lean_unsigned_to_nat(2u);
v___x_2335_ = lean_nat_abs(v_lit_2318_);
v___x_2336_ = lean_nat_mul(v___x_2334_, v___x_2335_);
lean_dec(v___x_2335_);
v___y_2320_ = v___x_2336_;
goto v___jp_2319_;
}
v___jp_2319_:
{
lean_object* v___x_2321_; uint8_t v___x_2322_; 
v___x_2321_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0);
v___x_2322_ = lean_nat_dec_le(v___y_2320_, v___x_2321_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
lean_dec(v___y_2320_);
lean_dec_ref(v_acc_2317_);
v___x_2323_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4);
v___x_2324_ = l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(v___x_2323_);
return v___x_2324_;
}
else
{
uint64_t v_mapped_2325_; lean_object* v___x_2326_; 
v_mapped_2325_ = lean_uint64_of_nat(v___y_2320_);
lean_dec(v___y_2320_);
v___x_2326_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(v_acc_2317_, v_mapped_2325_);
return v___x_2326_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___boxed(lean_object* v_acc_2337_, lean_object* v_lit_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2337_, v_lit_2338_);
lean_dec(v_lit_2338_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_zeroByte(lean_object* v_acc_2340_){
_start:
{
uint8_t v___x_2341_; lean_object* v___x_2342_; 
v___x_2341_ = 0;
v___x_2342_ = lean_byte_array_push(v_acc_2340_, v___x_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addNat(lean_object* v_acc_2343_, lean_object* v_n_2344_){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = lean_nat_to_int(v_n_2344_);
v___x_2346_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2343_, v___x_2345_);
lean_dec(v___x_2345_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startAdd(lean_object* v_acc_2347_){
_start:
{
uint8_t v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = 97;
v___x_2349_ = lean_byte_array_push(v_acc_2347_, v___x_2348_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(lean_object* v_as_2350_, size_t v_i_2351_, size_t v_stop_2352_, lean_object* v_b_2353_){
_start:
{
uint8_t v___x_2354_; 
v___x_2354_ = lean_usize_dec_eq(v_i_2351_, v_stop_2352_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; size_t v___x_2358_; size_t v___x_2359_; 
v___x_2355_ = lean_array_uget_borrowed(v_as_2350_, v_i_2351_);
lean_inc(v___x_2355_);
v___x_2356_ = lean_nat_to_int(v___x_2355_);
v___x_2357_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2353_, v___x_2356_);
lean_dec(v___x_2356_);
v___x_2358_ = ((size_t)1ULL);
v___x_2359_ = lean_usize_add(v_i_2351_, v___x_2358_);
v_i_2351_ = v___x_2359_;
v_b_2353_ = v___x_2357_;
goto _start;
}
else
{
return v_b_2353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0___boxed(lean_object* v_as_2361_, lean_object* v_i_2362_, lean_object* v_stop_2363_, lean_object* v_b_2364_){
_start:
{
size_t v_i_boxed_2365_; size_t v_stop_boxed_2366_; lean_object* v_res_2367_; 
v_i_boxed_2365_ = lean_unbox_usize(v_i_2362_);
lean_dec(v_i_2362_);
v_stop_boxed_2366_ = lean_unbox_usize(v_stop_2363_);
lean_dec(v_stop_2363_);
v_res_2367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(v_as_2361_, v_i_boxed_2365_, v_stop_boxed_2366_, v_b_2364_);
lean_dec_ref(v_as_2361_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(lean_object* v_as_2368_, size_t v_i_2369_, size_t v_stop_2370_, lean_object* v_b_2371_){
_start:
{
uint8_t v___x_2372_; 
v___x_2372_ = lean_usize_dec_eq(v_i_2369_, v_stop_2370_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; size_t v___x_2376_; size_t v___x_2377_; lean_object* v___x_2378_; 
v___x_2373_ = lean_array_uget_borrowed(v_as_2368_, v_i_2369_);
lean_inc(v___x_2373_);
v___x_2374_ = lean_nat_to_int(v___x_2373_);
v___x_2375_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2371_, v___x_2374_);
lean_dec(v___x_2374_);
v___x_2376_ = ((size_t)1ULL);
v___x_2377_ = lean_usize_add(v_i_2369_, v___x_2376_);
v___x_2378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(v_as_2368_, v___x_2377_, v_stop_2370_, v___x_2375_);
return v___x_2378_;
}
else
{
return v_b_2371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0___boxed(lean_object* v_as_2379_, lean_object* v_i_2380_, lean_object* v_stop_2381_, lean_object* v_b_2382_){
_start:
{
size_t v_i_boxed_2383_; size_t v_stop_boxed_2384_; lean_object* v_res_2385_; 
v_i_boxed_2383_ = lean_unbox_usize(v_i_2380_);
lean_dec(v_i_2380_);
v_stop_boxed_2384_ = lean_unbox_usize(v_stop_2381_);
lean_dec(v_stop_2381_);
v_res_2385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_as_2379_, v_i_boxed_2383_, v_stop_boxed_2384_, v_b_2382_);
lean_dec_ref(v_as_2379_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(lean_object* v_as_2386_, size_t v_i_2387_, size_t v_stop_2388_, lean_object* v_b_2389_){
_start:
{
lean_object* v___y_2391_; uint8_t v___x_2395_; 
v___x_2395_ = lean_usize_dec_eq(v_i_2387_, v_stop_2388_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; lean_object* v_fst_2397_; lean_object* v_snd_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v_acc_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; 
v___x_2396_ = lean_array_uget_borrowed(v_as_2386_, v_i_2387_);
v_fst_2397_ = lean_ctor_get(v___x_2396_, 0);
v_snd_2398_ = lean_ctor_get(v___x_2396_, 1);
v___x_2399_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_2397_);
v___x_2400_ = lean_nat_to_int(v_fst_2397_);
v___x_2401_ = lean_int_neg(v___x_2400_);
lean_dec(v___x_2400_);
v_acc_2402_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2389_, v___x_2401_);
lean_dec(v___x_2401_);
v___x_2403_ = lean_array_get_size(v_snd_2398_);
v___x_2404_ = lean_nat_dec_lt(v___x_2399_, v___x_2403_);
if (v___x_2404_ == 0)
{
v___y_2391_ = v_acc_2402_;
goto v___jp_2390_;
}
else
{
uint8_t v___x_2405_; 
v___x_2405_ = lean_nat_dec_le(v___x_2403_, v___x_2403_);
if (v___x_2405_ == 0)
{
if (v___x_2404_ == 0)
{
v___y_2391_ = v_acc_2402_;
goto v___jp_2390_;
}
else
{
size_t v___x_2406_; size_t v___x_2407_; lean_object* v___x_2408_; 
v___x_2406_ = ((size_t)0ULL);
v___x_2407_ = lean_usize_of_nat(v___x_2403_);
v___x_2408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2398_, v___x_2406_, v___x_2407_, v_acc_2402_);
v___y_2391_ = v___x_2408_;
goto v___jp_2390_;
}
}
else
{
size_t v___x_2409_; size_t v___x_2410_; lean_object* v___x_2411_; 
v___x_2409_ = ((size_t)0ULL);
v___x_2410_ = lean_usize_of_nat(v___x_2403_);
v___x_2411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2398_, v___x_2409_, v___x_2410_, v_acc_2402_);
v___y_2391_ = v___x_2411_;
goto v___jp_2390_;
}
}
}
else
{
return v_b_2389_;
}
v___jp_2390_:
{
size_t v___x_2392_; size_t v___x_2393_; 
v___x_2392_ = ((size_t)1ULL);
v___x_2393_ = lean_usize_add(v_i_2387_, v___x_2392_);
v_i_2387_ = v___x_2393_;
v_b_2389_ = v___y_2391_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3___boxed(lean_object* v_as_2412_, lean_object* v_i_2413_, lean_object* v_stop_2414_, lean_object* v_b_2415_){
_start:
{
size_t v_i_boxed_2416_; size_t v_stop_boxed_2417_; lean_object* v_res_2418_; 
v_i_boxed_2416_ = lean_unbox_usize(v_i_2413_);
lean_dec(v_i_2413_);
v_stop_boxed_2417_ = lean_unbox_usize(v_stop_2414_);
lean_dec(v_stop_2414_);
v_res_2418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(v_as_2412_, v_i_boxed_2416_, v_stop_boxed_2417_, v_b_2415_);
lean_dec_ref(v_as_2412_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(lean_object* v_as_2419_, size_t v_i_2420_, size_t v_stop_2421_, lean_object* v_b_2422_){
_start:
{
lean_object* v___y_2424_; uint8_t v___x_2428_; 
v___x_2428_ = lean_usize_dec_eq(v_i_2420_, v_stop_2421_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; lean_object* v_fst_2430_; lean_object* v_snd_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v_acc_2435_; lean_object* v___x_2436_; uint8_t v___x_2437_; 
v___x_2429_ = lean_array_uget_borrowed(v_as_2419_, v_i_2420_);
v_fst_2430_ = lean_ctor_get(v___x_2429_, 0);
v_snd_2431_ = lean_ctor_get(v___x_2429_, 1);
v___x_2432_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_2430_);
v___x_2433_ = lean_nat_to_int(v_fst_2430_);
v___x_2434_ = lean_int_neg(v___x_2433_);
lean_dec(v___x_2433_);
v_acc_2435_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2422_, v___x_2434_);
lean_dec(v___x_2434_);
v___x_2436_ = lean_array_get_size(v_snd_2431_);
v___x_2437_ = lean_nat_dec_lt(v___x_2432_, v___x_2436_);
if (v___x_2437_ == 0)
{
v___y_2424_ = v_acc_2435_;
goto v___jp_2423_;
}
else
{
uint8_t v___x_2438_; 
v___x_2438_ = lean_nat_dec_le(v___x_2436_, v___x_2436_);
if (v___x_2438_ == 0)
{
if (v___x_2437_ == 0)
{
v___y_2424_ = v_acc_2435_;
goto v___jp_2423_;
}
else
{
size_t v___x_2439_; size_t v___x_2440_; lean_object* v___x_2441_; 
v___x_2439_ = ((size_t)0ULL);
v___x_2440_ = lean_usize_of_nat(v___x_2436_);
v___x_2441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2431_, v___x_2439_, v___x_2440_, v_acc_2435_);
v___y_2424_ = v___x_2441_;
goto v___jp_2423_;
}
}
else
{
size_t v___x_2442_; size_t v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = ((size_t)0ULL);
v___x_2443_ = lean_usize_of_nat(v___x_2436_);
v___x_2444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2431_, v___x_2442_, v___x_2443_, v_acc_2435_);
v___y_2424_ = v___x_2444_;
goto v___jp_2423_;
}
}
}
else
{
return v_b_2422_;
}
v___jp_2423_:
{
size_t v___x_2425_; size_t v___x_2426_; lean_object* v___x_2427_; 
v___x_2425_ = ((size_t)1ULL);
v___x_2426_ = lean_usize_add(v_i_2420_, v___x_2425_);
v___x_2427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(v_as_2419_, v___x_2426_, v_stop_2421_, v___y_2424_);
return v___x_2427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2___boxed(lean_object* v_as_2445_, lean_object* v_i_2446_, lean_object* v_stop_2447_, lean_object* v_b_2448_){
_start:
{
size_t v_i_boxed_2449_; size_t v_stop_boxed_2450_; lean_object* v_res_2451_; 
v_i_boxed_2449_ = lean_unbox_usize(v_i_2446_);
lean_dec(v_i_2446_);
v_stop_boxed_2450_ = lean_unbox_usize(v_stop_2447_);
lean_dec(v_stop_2447_);
v_res_2451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_as_2445_, v_i_boxed_2449_, v_stop_boxed_2450_, v_b_2448_);
lean_dec_ref(v_as_2445_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(lean_object* v_as_2452_, size_t v_i_2453_, size_t v_stop_2454_, lean_object* v_b_2455_){
_start:
{
uint8_t v___x_2456_; 
v___x_2456_ = lean_usize_dec_eq(v_i_2453_, v_stop_2454_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2457_; lean_object* v___x_2458_; size_t v___x_2459_; size_t v___x_2460_; 
v___x_2457_ = lean_array_uget_borrowed(v_as_2452_, v_i_2453_);
v___x_2458_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2455_, v___x_2457_);
v___x_2459_ = ((size_t)1ULL);
v___x_2460_ = lean_usize_add(v_i_2453_, v___x_2459_);
v_i_2453_ = v___x_2460_;
v_b_2455_ = v___x_2458_;
goto _start;
}
else
{
return v_b_2455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1___boxed(lean_object* v_as_2462_, lean_object* v_i_2463_, lean_object* v_stop_2464_, lean_object* v_b_2465_){
_start:
{
size_t v_i_boxed_2466_; size_t v_stop_boxed_2467_; lean_object* v_res_2468_; 
v_i_boxed_2466_ = lean_unbox_usize(v_i_2463_);
lean_dec(v_i_2463_);
v_stop_boxed_2467_ = lean_unbox_usize(v_stop_2464_);
lean_dec(v_stop_2464_);
v_res_2468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_as_2462_, v_i_boxed_2466_, v_stop_boxed_2467_, v_b_2465_);
lean_dec_ref(v_as_2462_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(lean_object* v_proof_2469_, lean_object* v_idx_2470_, lean_object* v_acc_2471_){
_start:
{
lean_object* v___y_2473_; lean_object* v___y_2478_; lean_object* v___y_2482_; lean_object* v___y_2486_; lean_object* v___y_2490_; lean_object* v___x_2493_; uint8_t v___x_2494_; 
v___x_2493_ = lean_array_get_size(v_proof_2469_);
v___x_2494_ = lean_nat_dec_lt(v_idx_2470_, v___x_2493_);
if (v___x_2494_ == 0)
{
lean_dec(v_idx_2470_);
return v_acc_2471_;
}
else
{
lean_object* v___x_2495_; 
v___x_2495_ = lean_array_fget_borrowed(v_proof_2469_, v_idx_2470_);
switch(lean_obj_tag(v___x_2495_))
{
case 0:
{
lean_object* v_id_2496_; lean_object* v_rupHints_2497_; uint8_t v___x_2498_; lean_object* v_acc_2499_; lean_object* v___x_2500_; lean_object* v_acc_2501_; uint8_t v___x_2502_; lean_object* v_acc_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; 
v_id_2496_ = lean_ctor_get(v___x_2495_, 0);
v_rupHints_2497_ = lean_ctor_get(v___x_2495_, 1);
v___x_2498_ = 97;
v_acc_2499_ = lean_byte_array_push(v_acc_2471_, v___x_2498_);
lean_inc(v_id_2496_);
v___x_2500_ = lean_nat_to_int(v_id_2496_);
v_acc_2501_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2499_, v___x_2500_);
lean_dec(v___x_2500_);
v___x_2502_ = 0;
v_acc_2503_ = lean_byte_array_push(v_acc_2501_, v___x_2502_);
v___x_2504_ = lean_unsigned_to_nat(0u);
v___x_2505_ = lean_array_get_size(v_rupHints_2497_);
v___x_2506_ = lean_nat_dec_lt(v___x_2504_, v___x_2505_);
if (v___x_2506_ == 0)
{
v___y_2482_ = v_acc_2503_;
goto v___jp_2481_;
}
else
{
uint8_t v___x_2507_; 
v___x_2507_ = lean_nat_dec_le(v___x_2505_, v___x_2505_);
if (v___x_2507_ == 0)
{
if (v___x_2506_ == 0)
{
v___y_2482_ = v_acc_2503_;
goto v___jp_2481_;
}
else
{
size_t v___x_2508_; size_t v___x_2509_; lean_object* v___x_2510_; 
v___x_2508_ = ((size_t)0ULL);
v___x_2509_ = lean_usize_of_nat(v___x_2505_);
v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2497_, v___x_2508_, v___x_2509_, v_acc_2503_);
v___y_2482_ = v___x_2510_;
goto v___jp_2481_;
}
}
else
{
size_t v___x_2511_; size_t v___x_2512_; lean_object* v___x_2513_; 
v___x_2511_ = ((size_t)0ULL);
v___x_2512_ = lean_usize_of_nat(v___x_2505_);
v___x_2513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2497_, v___x_2511_, v___x_2512_, v_acc_2503_);
v___y_2482_ = v___x_2513_;
goto v___jp_2481_;
}
}
}
case 1:
{
lean_object* v_id_2514_; lean_object* v_c_2515_; lean_object* v_rupHints_2516_; uint8_t v___x_2517_; lean_object* v_acc_2518_; lean_object* v___x_2519_; lean_object* v_acc_2520_; lean_object* v___x_2521_; lean_object* v___y_2523_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v_id_2514_ = lean_ctor_get(v___x_2495_, 0);
v_c_2515_ = lean_ctor_get(v___x_2495_, 1);
v_rupHints_2516_ = lean_ctor_get(v___x_2495_, 2);
v___x_2517_ = 97;
v_acc_2518_ = lean_byte_array_push(v_acc_2471_, v___x_2517_);
lean_inc(v_id_2514_);
v___x_2519_ = lean_nat_to_int(v_id_2514_);
v_acc_2520_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2518_, v___x_2519_);
lean_dec(v___x_2519_);
v___x_2521_ = lean_unsigned_to_nat(0u);
v___x_2535_ = lean_array_get_size(v_c_2515_);
v___x_2536_ = lean_nat_dec_lt(v___x_2521_, v___x_2535_);
if (v___x_2536_ == 0)
{
v___y_2523_ = v_acc_2520_;
goto v___jp_2522_;
}
else
{
uint8_t v___x_2537_; 
v___x_2537_ = lean_nat_dec_le(v___x_2535_, v___x_2535_);
if (v___x_2537_ == 0)
{
if (v___x_2536_ == 0)
{
v___y_2523_ = v_acc_2520_;
goto v___jp_2522_;
}
else
{
size_t v___x_2538_; size_t v___x_2539_; lean_object* v___x_2540_; 
v___x_2538_ = ((size_t)0ULL);
v___x_2539_ = lean_usize_of_nat(v___x_2535_);
v___x_2540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2515_, v___x_2538_, v___x_2539_, v_acc_2520_);
v___y_2523_ = v___x_2540_;
goto v___jp_2522_;
}
}
else
{
size_t v___x_2541_; size_t v___x_2542_; lean_object* v___x_2543_; 
v___x_2541_ = ((size_t)0ULL);
v___x_2542_ = lean_usize_of_nat(v___x_2535_);
v___x_2543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2515_, v___x_2541_, v___x_2542_, v_acc_2520_);
v___y_2523_ = v___x_2543_;
goto v___jp_2522_;
}
}
v___jp_2522_:
{
uint8_t v___x_2524_; lean_object* v_acc_2525_; lean_object* v___x_2526_; uint8_t v___x_2527_; 
v___x_2524_ = 0;
v_acc_2525_ = lean_byte_array_push(v___y_2523_, v___x_2524_);
v___x_2526_ = lean_array_get_size(v_rupHints_2516_);
v___x_2527_ = lean_nat_dec_lt(v___x_2521_, v___x_2526_);
if (v___x_2527_ == 0)
{
v___y_2486_ = v_acc_2525_;
goto v___jp_2485_;
}
else
{
uint8_t v___x_2528_; 
v___x_2528_ = lean_nat_dec_le(v___x_2526_, v___x_2526_);
if (v___x_2528_ == 0)
{
if (v___x_2527_ == 0)
{
v___y_2486_ = v_acc_2525_;
goto v___jp_2485_;
}
else
{
size_t v___x_2529_; size_t v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = ((size_t)0ULL);
v___x_2530_ = lean_usize_of_nat(v___x_2526_);
v___x_2531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2516_, v___x_2529_, v___x_2530_, v_acc_2525_);
v___y_2486_ = v___x_2531_;
goto v___jp_2485_;
}
}
else
{
size_t v___x_2532_; size_t v___x_2533_; lean_object* v___x_2534_; 
v___x_2532_ = ((size_t)0ULL);
v___x_2533_ = lean_usize_of_nat(v___x_2526_);
v___x_2534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2516_, v___x_2532_, v___x_2533_, v_acc_2525_);
v___y_2486_ = v___x_2534_;
goto v___jp_2485_;
}
}
}
}
case 2:
{
lean_object* v_id_2544_; lean_object* v_c_2545_; lean_object* v_rupHints_2546_; lean_object* v_ratHints_2547_; uint8_t v___x_2548_; lean_object* v_acc_2549_; lean_object* v___x_2550_; lean_object* v_acc_2551_; lean_object* v___x_2552_; lean_object* v___y_2554_; lean_object* v___y_2565_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v_id_2544_ = lean_ctor_get(v___x_2495_, 0);
v_c_2545_ = lean_ctor_get(v___x_2495_, 1);
v_rupHints_2546_ = lean_ctor_get(v___x_2495_, 3);
v_ratHints_2547_ = lean_ctor_get(v___x_2495_, 4);
v___x_2548_ = 97;
v_acc_2549_ = lean_byte_array_push(v_acc_2471_, v___x_2548_);
lean_inc(v_id_2544_);
v___x_2550_ = lean_nat_to_int(v_id_2544_);
v_acc_2551_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2549_, v___x_2550_);
lean_dec(v___x_2550_);
v___x_2552_ = lean_unsigned_to_nat(0u);
v___x_2577_ = lean_array_get_size(v_c_2545_);
v___x_2578_ = lean_nat_dec_lt(v___x_2552_, v___x_2577_);
if (v___x_2578_ == 0)
{
v___y_2565_ = v_acc_2551_;
goto v___jp_2564_;
}
else
{
uint8_t v___x_2579_; 
v___x_2579_ = lean_nat_dec_le(v___x_2577_, v___x_2577_);
if (v___x_2579_ == 0)
{
if (v___x_2578_ == 0)
{
v___y_2565_ = v_acc_2551_;
goto v___jp_2564_;
}
else
{
size_t v___x_2580_; size_t v___x_2581_; lean_object* v___x_2582_; 
v___x_2580_ = ((size_t)0ULL);
v___x_2581_ = lean_usize_of_nat(v___x_2577_);
v___x_2582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2545_, v___x_2580_, v___x_2581_, v_acc_2551_);
v___y_2565_ = v___x_2582_;
goto v___jp_2564_;
}
}
else
{
size_t v___x_2583_; size_t v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = ((size_t)0ULL);
v___x_2584_ = lean_usize_of_nat(v___x_2577_);
v___x_2585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2545_, v___x_2583_, v___x_2584_, v_acc_2551_);
v___y_2565_ = v___x_2585_;
goto v___jp_2564_;
}
}
v___jp_2553_:
{
lean_object* v___x_2555_; uint8_t v___x_2556_; 
v___x_2555_ = lean_array_get_size(v_ratHints_2547_);
v___x_2556_ = lean_nat_dec_lt(v___x_2552_, v___x_2555_);
if (v___x_2556_ == 0)
{
v___y_2478_ = v___y_2554_;
goto v___jp_2477_;
}
else
{
uint8_t v___x_2557_; 
v___x_2557_ = lean_nat_dec_le(v___x_2555_, v___x_2555_);
if (v___x_2557_ == 0)
{
if (v___x_2556_ == 0)
{
v___y_2478_ = v___y_2554_;
goto v___jp_2477_;
}
else
{
size_t v___x_2558_; size_t v___x_2559_; lean_object* v___x_2560_; 
v___x_2558_ = ((size_t)0ULL);
v___x_2559_ = lean_usize_of_nat(v___x_2555_);
v___x_2560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_ratHints_2547_, v___x_2558_, v___x_2559_, v___y_2554_);
v___y_2478_ = v___x_2560_;
goto v___jp_2477_;
}
}
else
{
size_t v___x_2561_; size_t v___x_2562_; lean_object* v___x_2563_; 
v___x_2561_ = ((size_t)0ULL);
v___x_2562_ = lean_usize_of_nat(v___x_2555_);
v___x_2563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_ratHints_2547_, v___x_2561_, v___x_2562_, v___y_2554_);
v___y_2478_ = v___x_2563_;
goto v___jp_2477_;
}
}
}
v___jp_2564_:
{
uint8_t v___x_2566_; lean_object* v_acc_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2566_ = 0;
v_acc_2567_ = lean_byte_array_push(v___y_2565_, v___x_2566_);
v___x_2568_ = lean_array_get_size(v_rupHints_2546_);
v___x_2569_ = lean_nat_dec_lt(v___x_2552_, v___x_2568_);
if (v___x_2569_ == 0)
{
v___y_2554_ = v_acc_2567_;
goto v___jp_2553_;
}
else
{
uint8_t v___x_2570_; 
v___x_2570_ = lean_nat_dec_le(v___x_2568_, v___x_2568_);
if (v___x_2570_ == 0)
{
if (v___x_2569_ == 0)
{
v___y_2554_ = v_acc_2567_;
goto v___jp_2553_;
}
else
{
size_t v___x_2571_; size_t v___x_2572_; lean_object* v___x_2573_; 
v___x_2571_ = ((size_t)0ULL);
v___x_2572_ = lean_usize_of_nat(v___x_2568_);
v___x_2573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2546_, v___x_2571_, v___x_2572_, v_acc_2567_);
v___y_2554_ = v___x_2573_;
goto v___jp_2553_;
}
}
else
{
size_t v___x_2574_; size_t v___x_2575_; lean_object* v___x_2576_; 
v___x_2574_ = ((size_t)0ULL);
v___x_2575_ = lean_usize_of_nat(v___x_2568_);
v___x_2576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2546_, v___x_2574_, v___x_2575_, v_acc_2567_);
v___y_2554_ = v___x_2576_;
goto v___jp_2553_;
}
}
}
}
default: 
{
lean_object* v_ids_2586_; uint8_t v___x_2587_; lean_object* v_acc_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; 
v_ids_2586_ = lean_ctor_get(v___x_2495_, 0);
v___x_2587_ = 100;
v_acc_2588_ = lean_byte_array_push(v_acc_2471_, v___x_2587_);
v___x_2589_ = lean_unsigned_to_nat(0u);
v___x_2590_ = lean_array_get_size(v_ids_2586_);
v___x_2591_ = lean_nat_dec_lt(v___x_2589_, v___x_2590_);
if (v___x_2591_ == 0)
{
v___y_2490_ = v_acc_2588_;
goto v___jp_2489_;
}
else
{
uint8_t v___x_2592_; 
v___x_2592_ = lean_nat_dec_le(v___x_2590_, v___x_2590_);
if (v___x_2592_ == 0)
{
if (v___x_2591_ == 0)
{
v___y_2490_ = v_acc_2588_;
goto v___jp_2489_;
}
else
{
size_t v___x_2593_; size_t v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = ((size_t)0ULL);
v___x_2594_ = lean_usize_of_nat(v___x_2590_);
v___x_2595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_ids_2586_, v___x_2593_, v___x_2594_, v_acc_2588_);
v___y_2490_ = v___x_2595_;
goto v___jp_2489_;
}
}
else
{
size_t v___x_2596_; size_t v___x_2597_; lean_object* v___x_2598_; 
v___x_2596_ = ((size_t)0ULL);
v___x_2597_ = lean_usize_of_nat(v___x_2590_);
v___x_2598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_ids_2586_, v___x_2596_, v___x_2597_, v_acc_2588_);
v___y_2490_ = v___x_2598_;
goto v___jp_2489_;
}
}
}
}
}
v___jp_2472_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = lean_unsigned_to_nat(1u);
v___x_2475_ = lean_nat_add(v_idx_2470_, v___x_2474_);
lean_dec(v_idx_2470_);
v_idx_2470_ = v___x_2475_;
v_acc_2471_ = v___y_2473_;
goto _start;
}
v___jp_2477_:
{
uint8_t v___x_2479_; lean_object* v_acc_2480_; 
v___x_2479_ = 0;
v_acc_2480_ = lean_byte_array_push(v___y_2478_, v___x_2479_);
v___y_2473_ = v_acc_2480_;
goto v___jp_2472_;
}
v___jp_2481_:
{
uint8_t v___x_2483_; lean_object* v_acc_2484_; 
v___x_2483_ = 0;
v_acc_2484_ = lean_byte_array_push(v___y_2482_, v___x_2483_);
v___y_2473_ = v_acc_2484_;
goto v___jp_2472_;
}
v___jp_2485_:
{
uint8_t v___x_2487_; lean_object* v_acc_2488_; 
v___x_2487_ = 0;
v_acc_2488_ = lean_byte_array_push(v___y_2486_, v___x_2487_);
v___y_2473_ = v_acc_2488_;
goto v___jp_2472_;
}
v___jp_2489_:
{
uint8_t v___x_2491_; lean_object* v_acc_2492_; 
v___x_2491_ = 0;
v_acc_2492_ = lean_byte_array_push(v___y_2490_, v___x_2491_);
v___y_2473_ = v_acc_2492_;
goto v___jp_2472_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___boxed(lean_object* v_proof_2599_, lean_object* v_idx_2600_, lean_object* v_acc_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(v_proof_2599_, v_idx_2600_, v_acc_2601_);
lean_dec_ref(v_proof_2599_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(lean_object* v_proof_2603_){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2604_ = lean_unsigned_to_nat(0u);
v___x_2605_ = lean_unsigned_to_nat(4u);
v___x_2606_ = lean_array_get_size(v_proof_2603_);
v___x_2607_ = lean_nat_mul(v___x_2605_, v___x_2606_);
v___x_2608_ = lean_mk_empty_byte_array(v___x_2607_);
lean_dec(v___x_2607_);
v___x_2609_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(v_proof_2603_, v___x_2604_, v___x_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary___boxed(lean_object* v_proof_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(v_proof_2610_);
lean_dec_ref(v_proof_2610_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object* v_path_2612_, lean_object* v_proof_2613_, uint8_t v_binaryProofs_2614_){
_start:
{
if (v_binaryProofs_2614_ == 0)
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2616_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_proof_2613_);
v___x_2617_ = lean_string_to_utf8(v___x_2616_);
lean_dec_ref(v___x_2616_);
v___x_2618_ = l_IO_FS_writeBinFile(v_path_2612_, v___x_2617_);
lean_dec_ref(v___x_2617_);
return v___x_2618_;
}
else
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2619_ = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(v_proof_2613_);
v___x_2620_ = l_IO_FS_writeBinFile(v_path_2612_, v___x_2619_);
lean_dec_ref(v___x_2619_);
return v___x_2620_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof___boxed(lean_object* v_path_2621_, lean_object* v_proof_2622_, lean_object* v_binaryProofs_2623_, lean_object* v_a_2624_){
_start:
{
uint8_t v_binaryProofs_boxed_2625_; lean_object* v_res_2626_; 
v_binaryProofs_boxed_2625_ = lean_unbox(v_binaryProofs_2623_);
v_res_2626_ = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(v_path_2621_, v_proof_2622_, v_binaryProofs_boxed_2625_);
lean_dec_ref(v_proof_2622_);
lean_dec_ref(v_path_2621_);
return v_res_2626_;
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
