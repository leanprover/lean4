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
lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(uint64_t v_uidx_1358_, uint64_t v_shift_1359_, lean_object* v_a_1360_){
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
LEAN_EXPORT void l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go_0interp(lean_interpreter_value* stack)
{
uint64_t v_uidx_1358_ = stack[0].m_num;
uint64_t v_shift_1359_ = stack[1].m_num;
lean_object* v_a_1360_ = stack[2].m_obj;
lean_object* v_res_1415_;
v_res_1415_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(v_uidx_1358_, v_shift_1359_, v_a_1360_);
stack->m_obj
 = v_res_1415_;
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___boxed(lean_object* v_uidx_1416_, lean_object* v_shift_1417_, lean_object* v_a_1418_){
_start:
{
uint64_t v_uidx_boxed_1419_; uint64_t v_shift_boxed_1420_; lean_object* v_res_1421_; 
v_uidx_boxed_1419_ = lean_unbox_uint64(v_uidx_1416_);
lean_dec_ref(v_uidx_1416_);
v_shift_boxed_1420_ = lean_unbox_uint64(v_shift_1417_);
lean_dec_ref(v_shift_1417_);
v_res_1421_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(v_uidx_boxed_1419_, v_shift_boxed_1420_, v_a_1418_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(lean_object* v_a_1422_){
_start:
{
uint64_t v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = 0ULL;
v___x_1424_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(v___x_1423_, v___x_1423_, v_a_1422_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg(lean_object* v_a_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1428_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_pos_1430_; lean_object* v_res_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1445_; 
v_pos_1430_ = lean_ctor_get(v___x_1429_, 0);
v_res_1431_ = lean_ctor_get(v___x_1429_, 1);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1433_ = v___x_1429_;
v_isShared_1434_ = v_isSharedCheck_1445_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_res_1431_);
lean_inc(v_pos_1430_);
lean_dec(v___x_1429_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1445_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1435_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1436_ = lean_int_dec_lt(v_res_1431_, v___x_1435_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1439_; 
lean_dec(v_res_1431_);
v___x_1437_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1));
if (v_isShared_1434_ == 0)
{
lean_ctor_set_tag(v___x_1433_, 1);
lean_ctor_set(v___x_1433_, 1, v___x_1437_);
v___x_1439_ = v___x_1433_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_pos_1430_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
else
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1441_ = lean_nat_abs(v_res_1431_);
lean_dec(v_res_1431_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 1, v___x_1441_);
v___x_1443_ = v___x_1433_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_pos_1430_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_object* v_pos_1446_; lean_object* v_err_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
v_pos_1446_ = lean_ctor_get(v___x_1429_, 0);
v_err_1447_ = lean_ctor_get(v___x_1429_, 1);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1429_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_err_1447_);
lean_inc(v_pos_1446_);
lean_dec(v___x_1429_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_pos_1446_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_err_1447_);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos(lean_object* v_a_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1458_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_pos_1460_; lean_object* v_res_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1475_; 
v_pos_1460_ = lean_ctor_get(v___x_1459_, 0);
v_res_1461_ = lean_ctor_get(v___x_1459_, 1);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1463_ = v___x_1459_;
v_isShared_1464_ = v_isSharedCheck_1475_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_res_1461_);
lean_inc(v_pos_1460_);
lean_dec(v___x_1459_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1475_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; uint8_t v___x_1466_; 
v___x_1465_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1466_ = lean_int_dec_lt(v___x_1465_, v_res_1461_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1469_; 
lean_dec(v_res_1461_);
v___x_1467_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1464_ == 0)
{
lean_ctor_set_tag(v___x_1463_, 1);
lean_ctor_set(v___x_1463_, 1, v___x_1467_);
v___x_1469_ = v___x_1463_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_pos_1460_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v___x_1467_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
else
{
lean_object* v___x_1471_; lean_object* v___x_1473_; 
v___x_1471_ = lean_nat_abs(v_res_1461_);
lean_dec(v_res_1461_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 1, v___x_1471_);
v___x_1473_ = v___x_1463_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_pos_1460_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
else
{
lean_object* v_pos_1476_; lean_object* v_err_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
v_pos_1476_ = lean_ctor_get(v___x_1459_, 0);
v_err_1477_ = lean_ctor_get(v___x_1459_, 1);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1459_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_err_1477_);
lean_inc(v_pos_1476_);
lean_dec(v___x_1459_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_pos_1476_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_err_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId(lean_object* v_a_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1485_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_pos_1487_; lean_object* v_res_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1502_; 
v_pos_1487_ = lean_ctor_get(v___x_1486_, 0);
v_res_1488_ = lean_ctor_get(v___x_1486_, 1);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1490_ = v___x_1486_;
v_isShared_1491_ = v_isSharedCheck_1502_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_res_1488_);
lean_inc(v_pos_1487_);
lean_dec(v___x_1486_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1502_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1492_; uint8_t v___x_1493_; 
v___x_1492_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1493_ = lean_int_dec_lt(v___x_1492_, v_res_1488_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1496_; 
lean_dec(v_res_1488_);
v___x_1494_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1491_ == 0)
{
lean_ctor_set_tag(v___x_1490_, 1);
lean_ctor_set(v___x_1490_, 1, v___x_1494_);
v___x_1496_ = v___x_1490_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_pos_1487_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
else
{
lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1498_ = lean_nat_abs(v_res_1488_);
lean_dec(v_res_1488_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v___x_1498_);
v___x_1500_ = v___x_1490_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_pos_1487_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
else
{
lean_object* v_pos_1503_; lean_object* v_err_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
v_pos_1503_ = lean_ctor_get(v___x_1486_, 0);
v_err_1504_ = lean_ctor_get(v___x_1486_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1486_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_err_1504_);
lean_inc(v_pos_1503_);
lean_dec(v___x_1486_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_pos_1503_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_err_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(lean_object* v_parser_1512_, lean_object* v_acc_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v_array_1515_; lean_object* v_idx_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
v_array_1515_ = lean_ctor_get(v_a_1514_, 0);
v_idx_1516_ = lean_ctor_get(v_a_1514_, 1);
v___x_1517_ = lean_byte_array_size(v_array_1515_);
v___x_1518_ = lean_nat_dec_lt(v_idx_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_dec_ref(v_acc_1513_);
lean_dec_ref(v_parser_1512_);
v___x_1519_ = lean_box(0);
v___x_1520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1520_, 0, v_a_1514_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
return v___x_1520_;
}
else
{
uint8_t v___x_1521_; uint8_t v___x_1522_; uint8_t v___x_1523_; 
v___x_1521_ = lean_byte_array_fget(v_array_1515_, v_idx_1516_);
v___x_1522_ = 0;
v___x_1523_ = lean_uint8_dec_eq(v___x_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; 
lean_inc_ref(v_parser_1512_);
v___x_1524_ = lean_apply_1(v_parser_1512_, v_a_1514_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_pos_1525_; lean_object* v_res_1526_; lean_object* v___x_1527_; 
v_pos_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_pos_1525_);
v_res_1526_ = lean_ctor_get(v___x_1524_, 1);
lean_inc(v_res_1526_);
lean_dec_ref_known(v___x_1524_, 2);
v___x_1527_ = lean_array_push(v_acc_1513_, v_res_1526_);
v_acc_1513_ = v___x_1527_;
v_a_1514_ = v_pos_1525_;
goto _start;
}
else
{
lean_object* v_pos_1529_; lean_object* v_err_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_dec_ref(v_acc_1513_);
lean_dec_ref(v_parser_1512_);
v_pos_1529_ = lean_ctor_get(v___x_1524_, 0);
v_err_1530_ = lean_ctor_get(v___x_1524_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1524_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_err_1530_);
lean_inc(v_pos_1529_);
lean_dec(v___x_1524_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_pos_1529_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_err_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
else
{
lean_object* v___x_1538_; 
lean_dec_ref(v_parser_1512_);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v_a_1514_);
lean_ctor_set(v___x_1538_, 1, v_acc_1513_);
return v___x_1538_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go(lean_object* v_00_u03b1_1539_, lean_object* v_parser_1540_, lean_object* v_acc_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(v_parser_1540_, v_acc_1541_, v_a_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(lean_object* v_parser_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0));
v___x_1549_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(v_parser_1546_, v___x_1548_, v_a_1547_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero(lean_object* v_00_u03b1_1550_, lean_object* v_parser_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v_parser_1551_, v_a_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(lean_object* v_parser_1554_, lean_object* v_acc_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v_array_1557_; lean_object* v_idx_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v_array_1557_ = lean_ctor_get(v_a_1556_, 0);
v_idx_1558_ = lean_ctor_get(v_a_1556_, 1);
v___x_1559_ = lean_byte_array_size(v_array_1557_);
v___x_1560_ = lean_nat_dec_lt(v_idx_1558_, v___x_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
lean_dec_ref(v_acc_1555_);
lean_dec_ref(v_parser_1554_);
v___x_1561_ = lean_box(0);
v___x_1562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_a_1556_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
return v___x_1562_;
}
else
{
uint8_t v___x_1563_; uint8_t v___x_1564_; uint8_t v___x_1565_; uint8_t v___x_1566_; uint8_t v___x_1567_; 
v___x_1563_ = lean_byte_array_fget(v_array_1557_, v_idx_1558_);
v___x_1564_ = 1;
v___x_1565_ = lean_uint8_land(v___x_1564_, v___x_1563_);
v___x_1566_ = 0;
v___x_1567_ = lean_uint8_dec_eq(v___x_1565_, v___x_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; 
lean_dec_ref(v_parser_1554_);
v___x_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1568_, 0, v_a_1556_);
lean_ctor_set(v___x_1568_, 1, v_acc_1555_);
return v___x_1568_;
}
else
{
uint8_t v___x_1569_; 
v___x_1569_ = lean_uint8_dec_eq(v___x_1563_, v___x_1566_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; 
lean_inc_ref(v_parser_1554_);
v___x_1570_ = lean_apply_1(v_parser_1554_, v_a_1556_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_pos_1571_; lean_object* v_res_1572_; lean_object* v___x_1573_; 
v_pos_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_pos_1571_);
v_res_1572_ = lean_ctor_get(v___x_1570_, 1);
lean_inc(v_res_1572_);
lean_dec_ref_known(v___x_1570_, 2);
v___x_1573_ = lean_array_push(v_acc_1555_, v_res_1572_);
v_acc_1555_ = v___x_1573_;
v_a_1556_ = v_pos_1571_;
goto _start;
}
else
{
lean_object* v_pos_1575_; lean_object* v_err_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec_ref(v_acc_1555_);
lean_dec_ref(v_parser_1554_);
v_pos_1575_ = lean_ctor_get(v___x_1570_, 0);
v_err_1576_ = lean_ctor_get(v___x_1570_, 1);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1570_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_err_1576_);
lean_inc(v_pos_1575_);
lean_dec(v___x_1570_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_pos_1575_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_err_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
else
{
lean_object* v___x_1584_; 
lean_dec_ref(v_parser_1554_);
v___x_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1584_, 0, v_a_1556_);
lean_ctor_set(v___x_1584_, 1, v_acc_1555_);
return v___x_1584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go(lean_object* v_00_u03b1_1585_, lean_object* v_parser_1586_, lean_object* v_acc_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(v_parser_1586_, v_acc_1587_, v_a_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(lean_object* v_parser_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0));
v___x_1593_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(v_parser_1590_, v___x_1592_, v_a_1591_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero(lean_object* v_00_u03b1_1594_, lean_object* v_parser_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(v_parser_1595_, v_a_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList(lean_object* v_a_1598_){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId), 1, 0);
v___x_1600_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(v___x_1599_, v_a_1598_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause(lean_object* v_a_1601_){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit), 1, 0);
v___x_1603_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v___x_1602_, v_a_1601_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(lean_object* v_acc_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v_array_1606_; lean_object* v_idx_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; 
v_array_1606_ = lean_ctor_get(v_a_1605_, 0);
v_idx_1607_ = lean_ctor_get(v_a_1605_, 1);
v___x_1608_ = lean_byte_array_size(v_array_1606_);
v___x_1609_ = lean_nat_dec_lt(v_idx_1607_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec_ref(v_acc_1604_);
v___x_1610_ = lean_box(0);
v___x_1611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1611_, 0, v_a_1605_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
return v___x_1611_;
}
else
{
uint8_t v___x_1612_; uint8_t v___x_1613_; uint8_t v___x_1614_; uint8_t v___x_1615_; uint8_t v___x_1616_; 
v___x_1612_ = lean_byte_array_fget(v_array_1606_, v_idx_1607_);
v___x_1613_ = 1;
v___x_1614_ = lean_uint8_land(v___x_1613_, v___x_1612_);
v___x_1615_ = 0;
v___x_1616_ = lean_uint8_dec_eq(v___x_1614_, v___x_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v_a_1605_);
lean_ctor_set(v___x_1617_, 1, v_acc_1604_);
return v___x_1617_;
}
else
{
uint8_t v___x_1618_; 
v___x_1618_ = lean_uint8_dec_eq(v___x_1612_, v___x_1615_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1605_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_pos_1620_; lean_object* v_res_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1634_; 
v_pos_1620_ = lean_ctor_get(v___x_1619_, 0);
v_res_1621_ = lean_ctor_get(v___x_1619_, 1);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1623_ = v___x_1619_;
v_isShared_1624_ = v_isSharedCheck_1634_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_res_1621_);
lean_inc(v_pos_1620_);
lean_dec(v___x_1619_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1634_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1626_ = lean_int_dec_lt(v___x_1625_, v_res_1621_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
lean_dec(v_res_1621_);
lean_dec_ref(v_acc_1604_);
v___x_1627_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1624_ == 0)
{
lean_ctor_set_tag(v___x_1623_, 1);
lean_ctor_set(v___x_1623_, 1, v___x_1627_);
v___x_1629_ = v___x_1623_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_pos_1620_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
lean_del_object(v___x_1623_);
v___x_1631_ = lean_nat_abs(v_res_1621_);
lean_dec(v_res_1621_);
v___x_1632_ = lean_array_push(v_acc_1604_, v___x_1631_);
v_acc_1604_ = v___x_1632_;
v_a_1605_ = v_pos_1620_;
goto _start;
}
}
}
else
{
lean_object* v_pos_1635_; lean_object* v_err_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec_ref(v_acc_1604_);
v_pos_1635_ = lean_ctor_get(v___x_1619_, 0);
v_err_1636_ = lean_ctor_get(v___x_1619_, 1);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1619_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_err_1636_);
lean_inc(v_pos_1635_);
lean_dec(v___x_1619_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_pos_1635_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v_err_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
else
{
lean_object* v___x_1644_; 
v___x_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1644_, 0, v_a_1605_);
lean_ctor_set(v___x_1644_, 1, v_acc_1604_);
return v___x_1644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(lean_object* v_a_1645_){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0));
v___x_1647_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(v___x_1646_, v_a_1645_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(lean_object* v_a_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1648_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_pos_1650_; lean_object* v_res_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1682_; 
v_pos_1650_ = lean_ctor_get(v___x_1649_, 0);
v_res_1651_ = lean_ctor_get(v___x_1649_, 1);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1653_ = v___x_1649_;
v_isShared_1654_ = v_isSharedCheck_1682_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_res_1651_);
lean_inc(v_pos_1650_);
lean_dec(v___x_1649_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1682_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1656_ = lean_int_dec_lt(v_res_1651_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
lean_dec(v_res_1651_);
v___x_1657_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1));
if (v_isShared_1654_ == 0)
{
lean_ctor_set_tag(v___x_1653_, 1);
lean_ctor_set(v___x_1653_, 1, v___x_1657_);
v___x_1659_ = v___x_1653_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_pos_1650_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
else
{
lean_object* v___x_1661_; 
lean_del_object(v___x_1653_);
v___x_1661_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v_pos_1650_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_pos_1662_; lean_object* v_res_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1672_; 
v_pos_1662_ = lean_ctor_get(v___x_1661_, 0);
v_res_1663_ = lean_ctor_get(v___x_1661_, 1);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1665_ = v___x_1661_;
v_isShared_1666_ = v_isSharedCheck_1672_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_res_1663_);
lean_inc(v_pos_1662_);
lean_dec(v___x_1661_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1672_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1667_ = lean_nat_abs(v_res_1651_);
lean_dec(v_res_1651_);
v___x_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
lean_ctor_set(v___x_1668_, 1, v_res_1663_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 1, v___x_1668_);
v___x_1670_ = v___x_1665_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_pos_1662_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
else
{
lean_object* v_pos_1673_; lean_object* v_err_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_dec(v_res_1651_);
v_pos_1673_ = lean_ctor_get(v___x_1661_, 0);
v_err_1674_ = lean_ctor_get(v___x_1661_, 1);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1661_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_err_1674_);
lean_inc(v_pos_1673_);
lean_dec(v___x_1661_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_pos_1673_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_err_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1683_; lean_object* v_err_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
v_pos_1683_ = lean_ctor_get(v___x_1649_, 0);
v_err_1684_ = lean_ctor_get(v___x_1649_, 1);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v___x_1649_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_err_1684_);
lean_inc(v_pos_1683_);
lean_dec(v___x_1649_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_pos_1683_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_err_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints(lean_object* v_a_1692_){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes), 1, 0);
v___x_1694_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(v___x_1693_, v_a_1692_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(lean_object* v_acc_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v_array_1697_; lean_object* v_idx_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v_array_1697_ = lean_ctor_get(v_a_1696_, 0);
v_idx_1698_ = lean_ctor_get(v_a_1696_, 1);
v___x_1699_ = lean_byte_array_size(v_array_1697_);
v___x_1700_ = lean_nat_dec_lt(v_idx_1698_, v___x_1699_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_dec_ref(v_acc_1695_);
v___x_1701_ = lean_box(0);
v___x_1702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1702_, 0, v_a_1696_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
return v___x_1702_;
}
else
{
uint8_t v___x_1703_; uint8_t v___x_1704_; uint8_t v___x_1705_; 
v___x_1703_ = lean_byte_array_fget(v_array_1697_, v_idx_1698_);
v___x_1704_ = 0;
v___x_1705_ = lean_uint8_dec_eq(v___x_1703_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1696_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_pos_1707_; lean_object* v_res_1708_; lean_object* v___x_1709_; 
v_pos_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_pos_1707_);
v_res_1708_ = lean_ctor_get(v___x_1706_, 1);
lean_inc(v_res_1708_);
lean_dec_ref_known(v___x_1706_, 2);
v___x_1709_ = lean_array_push(v_acc_1695_, v_res_1708_);
v_acc_1695_ = v___x_1709_;
v_a_1696_ = v_pos_1707_;
goto _start;
}
else
{
lean_object* v_pos_1711_; lean_object* v_err_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec_ref(v_acc_1695_);
v_pos_1711_ = lean_ctor_get(v___x_1706_, 0);
v_err_1712_ = lean_ctor_get(v___x_1706_, 1);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1706_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_err_1712_);
lean_inc(v_pos_1711_);
lean_dec(v___x_1706_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_pos_1711_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_err_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
else
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v_a_1696_);
lean_ctor_set(v___x_1720_, 1, v_acc_1695_);
return v___x_1720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(lean_object* v_a_1721_){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0));
v___x_1723_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(v___x_1722_, v_a_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1_spec__2(lean_object* v_acc_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_array_1726_; lean_object* v_idx_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v_array_1726_ = lean_ctor_get(v_a_1725_, 0);
v_idx_1727_ = lean_ctor_get(v_a_1725_, 1);
v___x_1728_ = lean_byte_array_size(v_array_1726_);
v___x_1729_ = lean_nat_dec_lt(v_idx_1727_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec_ref(v_acc_1724_);
v___x_1730_ = lean_box(0);
v___x_1731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1731_, 0, v_a_1725_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
return v___x_1731_;
}
else
{
uint8_t v___x_1732_; uint8_t v___x_1733_; uint8_t v___x_1734_; 
v___x_1732_ = lean_byte_array_fget(v_array_1726_, v_idx_1727_);
v___x_1733_ = 0;
v___x_1734_ = lean_uint8_dec_eq(v___x_1732_, v___x_1733_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(v_a_1725_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_pos_1736_; lean_object* v_res_1737_; lean_object* v___x_1738_; 
v_pos_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_pos_1736_);
v_res_1737_ = lean_ctor_get(v___x_1735_, 1);
lean_inc(v_res_1737_);
lean_dec_ref_known(v___x_1735_, 2);
v___x_1738_ = lean_array_push(v_acc_1724_, v_res_1737_);
v_acc_1724_ = v___x_1738_;
v_a_1725_ = v_pos_1736_;
goto _start;
}
else
{
lean_object* v_pos_1740_; lean_object* v_err_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec_ref(v_acc_1724_);
v_pos_1740_ = lean_ctor_get(v___x_1735_, 0);
v_err_1741_ = lean_ctor_get(v___x_1735_, 1);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1735_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_err_1741_);
lean_inc(v_pos_1740_);
lean_dec(v___x_1735_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_pos_1740_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_err_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
else
{
lean_object* v___x_1749_; 
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v_a_1725_);
lean_ctor_set(v___x_1749_, 1, v_acc_1724_);
return v___x_1749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1(lean_object* v_a_1750_){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0));
v___x_1752_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1_spec__2(v___x_1751_, v_a_1750_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(v_a_1753_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_pos_1755_; lean_object* v_res_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1893_; 
v_pos_1755_ = lean_ctor_get(v___x_1754_, 0);
v_res_1756_ = lean_ctor_get(v___x_1754_, 1);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1758_ = v___x_1754_;
v_isShared_1759_ = v_isSharedCheck_1893_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_res_1756_);
lean_inc(v_pos_1755_);
lean_dec(v___x_1754_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1893_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___x_1760_ = lean_unsigned_to_nat(0u);
v___x_1761_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_1762_ = lean_int_dec_lt(v___x_1761_, v_res_1756_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1765_; 
lean_dec(v_res_1756_);
v___x_1763_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (v_isShared_1759_ == 0)
{
lean_ctor_set_tag(v___x_1758_, 1);
lean_ctor_set(v___x_1758_, 1, v___x_1763_);
v___x_1765_ = v___x_1758_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_pos_1755_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
else
{
lean_object* v___x_1767_; 
lean_del_object(v___x_1758_);
v___x_1767_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(v_pos_1755_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_pos_1768_; lean_object* v_res_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1883_; 
v_pos_1768_ = lean_ctor_get(v___x_1767_, 0);
v_res_1769_ = lean_ctor_get(v___x_1767_, 1);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1771_ = v___x_1767_;
v_isShared_1772_ = v_isSharedCheck_1883_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_res_1769_);
lean_inc(v_pos_1768_);
lean_dec(v___x_1767_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1883_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v_array_1773_; lean_object* v_idx_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v_array_1773_ = lean_ctor_get(v_pos_1768_, 0);
v_idx_1774_ = lean_ctor_get(v_pos_1768_, 1);
v___x_1775_ = lean_byte_array_size(v_array_1773_);
v___x_1776_ = lean_nat_dec_lt(v_idx_1774_, v___x_1775_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; lean_object* v___x_1779_; 
lean_dec(v_res_1769_);
lean_dec(v_res_1756_);
v___x_1777_ = lean_box(0);
if (v_isShared_1772_ == 0)
{
lean_ctor_set_tag(v___x_1771_, 1);
lean_ctor_set(v___x_1771_, 1, v___x_1777_);
v___x_1779_ = v___x_1771_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_pos_1768_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
else
{
uint8_t v___x_1781_; uint8_t v_got_1782_; uint8_t v___x_1783_; 
v___x_1781_ = 0;
v_got_1782_ = lean_byte_array_fget(v_array_1773_, v_idx_1774_);
v___x_1783_ = lean_uint8_dec_eq(v_got_1782_, v___x_1781_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1786_; 
lean_dec(v_res_1769_);
lean_dec(v_res_1756_);
v___x_1784_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
if (v_isShared_1772_ == 0)
{
lean_ctor_set_tag(v___x_1771_, 1);
lean_ctor_set(v___x_1771_, 1, v___x_1784_);
v___x_1786_ = v___x_1771_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_pos_1768_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
else
{
lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1880_; 
lean_inc(v_idx_1774_);
lean_inc_ref(v_array_1773_);
lean_del_object(v___x_1771_);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_pos_1768_);
if (v_isSharedCheck_1880_ == 0)
{
lean_object* v_unused_1881_; lean_object* v_unused_1882_; 
v_unused_1881_ = lean_ctor_get(v_pos_1768_, 1);
lean_dec(v_unused_1881_);
v_unused_1882_ = lean_ctor_get(v_pos_1768_, 0);
lean_dec(v_unused_1882_);
v___x_1789_ = v_pos_1768_;
v_isShared_1790_ = v_isSharedCheck_1880_;
goto v_resetjp_1788_;
}
else
{
lean_dec(v_pos_1768_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1880_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; 
v___x_1791_ = lean_unsigned_to_nat(1u);
v___x_1792_ = lean_nat_add(v_idx_1774_, v___x_1791_);
lean_dec(v_idx_1774_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 1, v___x_1792_);
v___x_1794_ = v___x_1789_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_array_1773_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v___x_1794_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_pos_1796_; lean_object* v_res_1797_; lean_object* v___x_1798_; 
v_pos_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_pos_1796_);
v_res_1797_ = lean_ctor_get(v___x_1795_, 1);
lean_inc(v_res_1797_);
lean_dec_ref_known(v___x_1795_, 2);
v___x_1798_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1(v_pos_1796_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_pos_1799_; lean_object* v_res_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1860_; 
v_pos_1799_ = lean_ctor_get(v___x_1798_, 0);
v_res_1800_ = lean_ctor_get(v___x_1798_, 1);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1802_ = v___x_1798_;
v_isShared_1803_ = v_isSharedCheck_1860_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_res_1800_);
lean_inc(v_pos_1799_);
lean_dec(v___x_1798_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1860_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v_array_1804_; lean_object* v_idx_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v_array_1804_ = lean_ctor_get(v_pos_1799_, 0);
v_idx_1805_ = lean_ctor_get(v_pos_1799_, 1);
v___x_1806_ = lean_byte_array_size(v_array_1804_);
v___x_1807_ = lean_nat_dec_lt(v_idx_1805_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1810_; 
lean_dec(v_res_1800_);
lean_dec(v_res_1797_);
lean_dec(v_res_1769_);
lean_dec(v_res_1756_);
v___x_1808_ = lean_box(0);
if (v_isShared_1803_ == 0)
{
lean_ctor_set_tag(v___x_1802_, 1);
lean_ctor_set(v___x_1802_, 1, v___x_1808_);
v___x_1810_ = v___x_1802_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_pos_1799_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
else
{
uint8_t v_got_1812_; uint8_t v___x_1813_; 
v_got_1812_ = lean_byte_array_fget(v_array_1804_, v_idx_1805_);
v___x_1813_ = lean_uint8_dec_eq(v_got_1812_, v___x_1781_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
lean_dec(v_res_1800_);
lean_dec(v_res_1797_);
lean_dec(v_res_1769_);
lean_dec(v_res_1756_);
v___x_1814_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
if (v_isShared_1803_ == 0)
{
lean_ctor_set_tag(v___x_1802_, 1);
lean_ctor_set(v___x_1802_, 1, v___x_1814_);
v___x_1816_ = v___x_1802_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_pos_1799_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
else
{
lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1857_; 
lean_inc(v_idx_1805_);
lean_inc_ref(v_array_1804_);
v_isSharedCheck_1857_ = !lean_is_exclusive(v_pos_1799_);
if (v_isSharedCheck_1857_ == 0)
{
lean_object* v_unused_1858_; lean_object* v_unused_1859_; 
v_unused_1858_ = lean_ctor_get(v_pos_1799_, 1);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v_pos_1799_, 0);
lean_dec(v_unused_1859_);
v___x_1819_ = v_pos_1799_;
v_isShared_1820_ = v_isSharedCheck_1857_;
goto v_resetjp_1818_;
}
else
{
lean_dec(v_pos_1799_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1857_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1821_ = lean_nat_abs(v_res_1756_);
lean_dec(v_res_1756_);
v___x_1822_ = lean_nat_add(v_idx_1805_, v___x_1791_);
lean_dec(v_idx_1805_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 1, v___x_1822_);
v___x_1824_ = v___x_1819_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_array_1804_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = lean_array_get_size(v_res_1769_);
v___x_1826_ = lean_nat_dec_eq(v___x_1825_, v___x_1760_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1827_ = lean_array_get_size(v_res_1800_);
v___x_1828_ = lean_nat_dec_eq(v___x_1827_, v___x_1760_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1832_; 
v___x_1829_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_1769_);
v___x_1830_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1821_);
lean_ctor_set(v___x_1830_, 1, v_res_1769_);
lean_ctor_set(v___x_1830_, 2, v___x_1829_);
lean_ctor_set(v___x_1830_, 3, v_res_1797_);
lean_ctor_set(v___x_1830_, 4, v_res_1800_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 1, v___x_1830_);
lean_ctor_set(v___x_1802_, 0, v___x_1824_);
v___x_1832_ = v___x_1802_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v___x_1830_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
else
{
lean_object* v___x_1834_; uint8_t v___x_1835_; 
lean_dec(v_res_1800_);
v___x_1834_ = lean_array_get_size(v_res_1797_);
v___x_1835_ = lean_nat_dec_eq(v___x_1834_, v___x_1760_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1836_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1821_);
lean_ctor_set(v___x_1836_, 1, v_res_1769_);
lean_ctor_set(v___x_1836_, 2, v_res_1797_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 1, v___x_1836_);
lean_ctor_set(v___x_1802_, 0, v___x_1824_);
v___x_1838_ = v___x_1802_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
lean_dec(v_res_1797_);
v___x_1840_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(v_res_1769_);
v___x_1841_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0));
v___x_1842_ = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1821_);
lean_ctor_set(v___x_1842_, 1, v_res_1769_);
lean_ctor_set(v___x_1842_, 2, v___x_1840_);
lean_ctor_set(v___x_1842_, 3, v___x_1841_);
lean_ctor_set(v___x_1842_, 4, v___x_1841_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 1, v___x_1842_);
lean_ctor_set(v___x_1802_, 0, v___x_1824_);
v___x_1844_ = v___x_1802_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
else
{
lean_object* v___x_1846_; uint8_t v___x_1847_; 
lean_dec(v_res_1769_);
v___x_1846_ = lean_array_get_size(v_res_1800_);
lean_dec(v_res_1800_);
v___x_1847_ = lean_nat_dec_eq(v___x_1846_, v___x_1760_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
lean_dec(v___x_1821_);
lean_dec(v_res_1797_);
v___x_1848_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2));
if (v_isShared_1803_ == 0)
{
lean_ctor_set_tag(v___x_1802_, 1);
lean_ctor_set(v___x_1802_, 1, v___x_1848_);
lean_ctor_set(v___x_1802_, 0, v___x_1824_);
v___x_1850_ = v___x_1802_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1824_);
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
lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1821_);
lean_ctor_set(v___x_1852_, 1, v_res_1797_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 1, v___x_1852_);
lean_ctor_set(v___x_1802_, 0, v___x_1824_);
v___x_1854_ = v___x_1802_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
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
lean_object* v_pos_1861_; lean_object* v_err_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec(v_res_1797_);
lean_dec(v_res_1769_);
lean_dec(v_res_1756_);
v_pos_1861_ = lean_ctor_get(v___x_1798_, 0);
v_err_1862_ = lean_ctor_get(v___x_1798_, 1);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1798_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_err_1862_);
lean_inc(v_pos_1861_);
lean_dec(v___x_1798_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_pos_1861_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_err_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
else
{
lean_object* v_pos_1870_; lean_object* v_err_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec(v_res_1769_);
lean_dec(v_res_1756_);
v_pos_1870_ = lean_ctor_get(v___x_1795_, 0);
v_err_1871_ = lean_ctor_get(v___x_1795_, 1);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1795_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_err_1871_);
lean_inc(v_pos_1870_);
lean_dec(v___x_1795_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_pos_1870_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v_err_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
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
lean_object* v_pos_1884_; lean_object* v_err_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v_res_1756_);
v_pos_1884_ = lean_ctor_get(v___x_1767_, 0);
v_err_1885_ = lean_ctor_get(v___x_1767_, 1);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1767_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_err_1885_);
lean_inc(v_pos_1884_);
lean_dec(v___x_1767_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_pos_1884_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_err_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1894_; lean_object* v_err_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
v_pos_1894_ = lean_ctor_get(v___x_1754_, 0);
v_err_1895_ = lean_ctor_get(v___x_1754_, 1);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1754_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_err_1895_);
lean_inc(v_pos_1894_);
lean_dec(v___x_1754_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_pos_1894_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_err_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(lean_object* v_a_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(v_a_1903_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_pos_1905_; lean_object* v_res_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1940_; 
v_pos_1905_ = lean_ctor_get(v___x_1904_, 0);
v_res_1906_ = lean_ctor_get(v___x_1904_, 1);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1908_ = v___x_1904_;
v_isShared_1909_ = v_isSharedCheck_1940_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_res_1906_);
lean_inc(v_pos_1905_);
lean_dec(v___x_1904_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1940_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v_array_1910_; lean_object* v_idx_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
v_array_1910_ = lean_ctor_get(v_pos_1905_, 0);
v_idx_1911_ = lean_ctor_get(v_pos_1905_, 1);
v___x_1912_ = lean_byte_array_size(v_array_1910_);
v___x_1913_ = lean_nat_dec_lt(v_idx_1911_, v___x_1912_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
lean_dec(v_res_1906_);
v___x_1914_ = lean_box(0);
if (v_isShared_1909_ == 0)
{
lean_ctor_set_tag(v___x_1908_, 1);
lean_ctor_set(v___x_1908_, 1, v___x_1914_);
v___x_1916_ = v___x_1908_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_pos_1905_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
else
{
uint8_t v___x_1918_; uint8_t v_got_1919_; uint8_t v___x_1920_; 
v___x_1918_ = 0;
v_got_1919_ = lean_byte_array_fget(v_array_1910_, v_idx_1911_);
v___x_1920_ = lean_uint8_dec_eq(v_got_1919_, v___x_1918_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; lean_object* v___x_1923_; 
lean_dec(v_res_1906_);
v___x_1921_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1));
if (v_isShared_1909_ == 0)
{
lean_ctor_set_tag(v___x_1908_, 1);
lean_ctor_set(v___x_1908_, 1, v___x_1921_);
v___x_1923_ = v___x_1908_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_pos_1905_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
else
{
lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1937_; 
lean_inc(v_idx_1911_);
lean_inc_ref(v_array_1910_);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_pos_1905_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; lean_object* v_unused_1939_; 
v_unused_1938_ = lean_ctor_get(v_pos_1905_, 1);
lean_dec(v_unused_1938_);
v_unused_1939_ = lean_ctor_get(v_pos_1905_, 0);
lean_dec(v_unused_1939_);
v___x_1926_ = v_pos_1905_;
v_isShared_1927_ = v_isSharedCheck_1937_;
goto v_resetjp_1925_;
}
else
{
lean_dec(v_pos_1905_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1937_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1928_ = lean_unsigned_to_nat(1u);
v___x_1929_ = lean_nat_add(v_idx_1911_, v___x_1928_);
lean_dec(v_idx_1911_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 1, v___x_1929_);
v___x_1931_ = v___x_1926_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_array_1910_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1932_, 0, v_res_1906_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 1, v___x_1932_);
lean_ctor_set(v___x_1908_, 0, v___x_1931_);
v___x_1934_ = v___x_1908_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1931_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v___x_1932_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
}
}
}
else
{
lean_object* v_pos_1941_; lean_object* v_err_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
v_pos_1941_ = lean_ctor_get(v___x_1904_, 0);
v_err_1942_ = lean_ctor_get(v___x_1904_, 1);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1904_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_err_1942_);
lean_inc(v_pos_1941_);
lean_dec(v___x_1904_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_pos_1941_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_err_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(lean_object* v_a_1951_){
_start:
{
lean_object* v_array_1952_; lean_object* v_idx_1953_; lean_object* v___x_1954_; uint8_t v___x_1955_; 
v_array_1952_ = lean_ctor_get(v_a_1951_, 0);
v_idx_1953_ = lean_ctor_get(v_a_1951_, 1);
v___x_1954_ = lean_byte_array_size(v_array_1952_);
v___x_1955_ = lean_nat_dec_lt(v_idx_1953_, v___x_1954_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = lean_box(0);
v___x_1957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1957_, 0, v_a_1951_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
return v___x_1957_;
}
else
{
lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1979_; 
lean_inc(v_idx_1953_);
lean_inc_ref(v_array_1952_);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_a_1951_);
if (v_isSharedCheck_1979_ == 0)
{
lean_object* v_unused_1980_; lean_object* v_unused_1981_; 
v_unused_1980_ = lean_ctor_get(v_a_1951_, 1);
lean_dec(v_unused_1980_);
v_unused_1981_ = lean_ctor_get(v_a_1951_, 0);
lean_dec(v_unused_1981_);
v___x_1959_ = v_a_1951_;
v_isShared_1960_ = v_isSharedCheck_1979_;
goto v_resetjp_1958_;
}
else
{
lean_dec(v_a_1951_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1979_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
uint8_t v_c_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v_it_x27_1965_; 
v_c_1961_ = lean_byte_array_fget(v_array_1952_, v_idx_1953_);
v___x_1962_ = lean_unsigned_to_nat(1u);
v___x_1963_ = lean_nat_add(v_idx_1953_, v___x_1962_);
lean_dec(v_idx_1953_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 1, v___x_1963_);
v_it_x27_1965_ = v___x_1959_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_array_1952_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v___x_1963_);
v_it_x27_1965_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
uint8_t v___x_1966_; uint8_t v___x_1967_; 
v___x_1966_ = 97;
v___x_1967_ = lean_uint8_dec_eq(v_c_1961_, v___x_1966_);
if (v___x_1967_ == 0)
{
uint8_t v___x_1968_; uint8_t v___x_1969_; 
v___x_1968_ = 100;
v___x_1969_ = lean_uint8_dec_eq(v_c_1961_, v___x_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1970_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0));
v___x_1971_ = lean_uint8_to_nat(v_c_1961_);
v___x_1972_ = l_Nat_reprFast(v___x_1971_);
v___x_1973_ = lean_string_append(v___x_1970_, v___x_1972_);
lean_dec_ref(v___x_1972_);
v___x_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
v___x_1975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1975_, 0, v_it_x27_1965_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
return v___x_1975_;
}
else
{
lean_object* v___x_1976_; 
v___x_1976_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(v_it_x27_1965_);
return v___x_1976_;
}
}
else
{
lean_object* v___x_1977_; 
v___x_1977_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(v_it_x27_1965_);
return v___x_1977_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(lean_object* v_acc_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v___x_1984_; 
lean_inc_ref(v_a_1983_);
v___x_1984_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(v_a_1983_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_pos_1985_; lean_object* v_res_1986_; lean_object* v___x_1987_; 
lean_dec_ref(v_a_1983_);
v_pos_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_pos_1985_);
v_res_1986_ = lean_ctor_get(v___x_1984_, 1);
lean_inc(v_res_1986_);
lean_dec_ref_known(v___x_1984_, 2);
v___x_1987_ = lean_array_push(v_acc_1982_, v_res_1986_);
v_acc_1982_ = v___x_1987_;
v_a_1983_ = v_pos_1985_;
goto _start;
}
else
{
lean_object* v_pos_1989_; lean_object* v_err_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2003_; 
v_pos_1989_ = lean_ctor_get(v___x_1984_, 0);
v_err_1990_ = lean_ctor_get(v___x_1984_, 1);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1992_ = v___x_1984_;
v_isShared_1993_ = v_isSharedCheck_2003_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_err_1990_);
lean_inc(v_pos_1989_);
lean_dec(v___x_1984_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2003_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v_idx_1994_; lean_object* v_idx_1995_; uint8_t v___x_1996_; 
v_idx_1994_ = lean_ctor_get(v_a_1983_, 1);
lean_inc(v_idx_1994_);
lean_dec_ref(v_a_1983_);
v_idx_1995_ = lean_ctor_get(v_pos_1989_, 1);
v___x_1996_ = lean_nat_dec_eq(v_idx_1994_, v_idx_1995_);
lean_dec(v_idx_1994_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1998_; 
lean_dec_ref(v_acc_1982_);
if (v_isShared_1993_ == 0)
{
v___x_1998_ = v___x_1992_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_pos_1989_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_err_1990_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
else
{
lean_object* v___x_2001_; 
lean_dec(v_err_1990_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set_tag(v___x_1992_, 0);
lean_ctor_set(v___x_1992_, 1, v_acc_1982_);
v___x_2001_ = v___x_1992_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_pos_1989_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_acc_1982_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(lean_object* v_a_2007_){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0));
v___x_2009_ = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(v___x_2008_, v_a_2007_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_pos_2010_; lean_object* v_array_2011_; lean_object* v_idx_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v_pos_2010_ = lean_ctor_get(v___x_2009_, 0);
v_array_2011_ = lean_ctor_get(v_pos_2010_, 0);
v_idx_2012_ = lean_ctor_get(v_pos_2010_, 1);
v___x_2013_ = lean_byte_array_size(v_array_2011_);
v___x_2014_ = lean_nat_dec_lt(v_idx_2012_, v___x_2013_);
if (v___x_2014_ == 0)
{
return v___x_2009_;
}
else
{
lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2022_; 
lean_inc(v_pos_2010_);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2022_ == 0)
{
lean_object* v_unused_2023_; lean_object* v_unused_2024_; 
v_unused_2023_ = lean_ctor_get(v___x_2009_, 1);
lean_dec(v_unused_2023_);
v_unused_2024_ = lean_ctor_get(v___x_2009_, 0);
lean_dec(v_unused_2024_);
v___x_2016_ = v___x_2009_;
v_isShared_2017_ = v_isSharedCheck_2022_;
goto v_resetjp_2015_;
}
else
{
lean_dec(v___x_2009_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2022_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2018_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__1));
if (v_isShared_2017_ == 0)
{
lean_ctor_set_tag(v___x_2016_, 1);
lean_ctor_set(v___x_2016_, 1, v___x_2018_);
v___x_2020_ = v___x_2016_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_pos_2010_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
else
{
return v___x_2009_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_parseActions(lean_object* v_a_2025_){
_start:
{
lean_object* v_array_2026_; lean_object* v_idx_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
v_array_2026_ = lean_ctor_get(v_a_2025_, 0);
v_idx_2027_ = lean_ctor_get(v_a_2025_, 1);
v___x_2028_ = lean_byte_array_size(v_array_2026_);
v___x_2029_ = lean_nat_dec_lt(v_idx_2027_, v___x_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = lean_box(0);
v___x_2031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2031_, 0, v_a_2025_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
return v___x_2031_;
}
else
{
uint8_t v___x_2032_; uint8_t v___x_2033_; uint8_t v___x_2034_; 
v___x_2032_ = lean_byte_array_fget(v_array_2026_, v_idx_2027_);
v___x_2033_ = 97;
v___x_2034_ = lean_uint8_dec_eq(v___x_2032_, v___x_2033_);
if (v___x_2034_ == 0)
{
uint8_t v___x_2035_; uint8_t v___x_2036_; 
v___x_2035_ = 100;
v___x_2036_ = lean_uint8_dec_eq(v___x_2032_, v___x_2035_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(v_a_2025_);
return v___x_2037_;
}
else
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(v_a_2025_);
return v___x_2038_;
}
}
else
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(v_a_2025_);
return v___x_2039_;
}
}
}
}
lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object* v_path_2040_){
_start:
{
lean_object* v___x_2042_; 
v___x_2042_ = l_IO_FS_readBinFile(v_path_2040_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2064_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2045_ = v___x_2042_;
v_isShared_2046_ = v_isSharedCheck_2064_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2064_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_parseActions), 1, 0);
v___x_2048_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___x_2047_, v_a_2043_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2059_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2051_ = v___x_2048_;
v_isShared_2052_ = v_isSharedCheck_2059_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2048_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2059_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
lean_ctor_set_tag(v___x_2051_, 18);
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2056_; 
if (v_isShared_2046_ == 0)
{
lean_ctor_set_tag(v___x_2045_, 1);
lean_ctor_set(v___x_2045_, 0, v___x_2054_);
v___x_2056_ = v___x_2045_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; 
v_a_2060_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2060_);
lean_dec_ref_known(v___x_2048_, 1);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v_a_2060_);
v___x_2062_ = v___x_2045_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
v_a_2065_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2042_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2042_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_loadLRATProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_path_2040_ = stack[0].m_obj;
lean_object* v_res_2073_;
v_res_2073_ = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(v_path_2040_);
stack->m_obj
 = v_res_2073_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(lean_object* v_as_2081_, size_t v_i_2082_, size_t v_stop_2083_, lean_object* v_b_2084_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2081_ = stack[0].m_obj;
size_t v_i_2082_ = stack[1].m_num;
size_t v_stop_2083_ = stack[2].m_num;
lean_object* v_b_2084_ = stack[3].m_obj;
lean_object* v_res_2094_;
v_res_2094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_as_2081_, v_i_2082_, v_stop_2083_, v_b_2084_);
stack->m_obj
 = v_res_2094_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___boxed(lean_object* v_as_2095_, lean_object* v_i_2096_, lean_object* v_stop_2097_, lean_object* v_b_2098_){
_start:
{
size_t v_i_boxed_2099_; size_t v_stop_boxed_2100_; lean_object* v_res_2101_; 
v_i_boxed_2099_ = lean_unbox_usize(v_i_2096_);
lean_dec(v_i_2096_);
v_stop_boxed_2100_ = lean_unbox_usize(v_stop_2097_);
lean_dec(v_stop_2097_);
v_res_2101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_as_2095_, v_i_boxed_2099_, v_stop_boxed_2100_, v_b_2098_);
lean_dec_ref(v_as_2095_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(lean_object* v_ids_2103_){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v___x_2104_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2105_ = lean_unsigned_to_nat(0u);
v___x_2106_ = lean_array_get_size(v_ids_2103_);
v___x_2107_ = lean_nat_dec_lt(v___x_2105_, v___x_2106_);
if (v___x_2107_ == 0)
{
return v___x_2104_;
}
else
{
uint8_t v___x_2108_; 
v___x_2108_ = lean_nat_dec_le(v___x_2106_, v___x_2106_);
if (v___x_2108_ == 0)
{
if (v___x_2107_ == 0)
{
return v___x_2104_;
}
else
{
size_t v___x_2109_; size_t v___x_2110_; lean_object* v___x_2111_; 
v___x_2109_ = ((size_t)0ULL);
v___x_2110_ = lean_usize_of_nat(v___x_2106_);
v___x_2111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_ids_2103_, v___x_2109_, v___x_2110_, v___x_2104_);
return v___x_2111_;
}
}
else
{
size_t v___x_2112_; size_t v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = ((size_t)0ULL);
v___x_2113_ = lean_usize_of_nat(v___x_2106_);
v___x_2114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(v_ids_2103_, v___x_2112_, v___x_2113_, v___x_2104_);
return v___x_2114_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___boxed(lean_object* v_ids_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_ids_2115_);
lean_dec_ref(v_ids_2115_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(lean_object* v_hint_2118_){
_start:
{
lean_object* v_fst_2119_; lean_object* v_snd_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v_fst_2119_ = lean_ctor_get(v_hint_2118_, 0);
lean_inc(v_fst_2119_);
v_snd_2120_ = lean_ctor_get(v_hint_2118_, 1);
lean_inc(v_snd_2120_);
lean_dec_ref(v_hint_2118_);
v___x_2121_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0));
v___x_2122_ = l_Nat_reprFast(v_fst_2119_);
v___x_2123_ = lean_string_append(v___x_2121_, v___x_2122_);
lean_dec_ref(v___x_2122_);
v___x_2124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2125_ = lean_string_append(v___x_2123_, v___x_2124_);
v___x_2126_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_snd_2120_);
lean_dec(v_snd_2120_);
v___x_2127_ = lean_string_append(v___x_2125_, v___x_2126_);
lean_dec_ref(v___x_2126_);
return v___x_2127_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(lean_object* v_as_2128_, size_t v_i_2129_, size_t v_stop_2130_, lean_object* v_b_2131_){
_start:
{
uint8_t v___x_2132_; 
v___x_2132_ = lean_usize_dec_eq(v_i_2129_, v_stop_2130_);
if (v___x_2132_ == 0)
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; size_t v___x_2136_; size_t v___x_2137_; 
v___x_2133_ = lean_array_uget_borrowed(v_as_2128_, v_i_2129_);
lean_inc(v___x_2133_);
v___x_2134_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(v___x_2133_);
v___x_2135_ = lean_string_append(v_b_2131_, v___x_2134_);
lean_dec_ref(v___x_2134_);
v___x_2136_ = ((size_t)1ULL);
v___x_2137_ = lean_usize_add(v_i_2129_, v___x_2136_);
v_i_2129_ = v___x_2137_;
v_b_2131_ = v___x_2135_;
goto _start;
}
else
{
return v_b_2131_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2128_ = stack[0].m_obj;
size_t v_i_2129_ = stack[1].m_num;
size_t v_stop_2130_ = stack[2].m_num;
lean_object* v_b_2131_ = stack[3].m_obj;
lean_object* v_res_2139_;
v_res_2139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_as_2128_, v_i_2129_, v_stop_2130_, v_b_2131_);
stack->m_obj
 = v_res_2139_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0___boxed(lean_object* v_as_2140_, lean_object* v_i_2141_, lean_object* v_stop_2142_, lean_object* v_b_2143_){
_start:
{
size_t v_i_boxed_2144_; size_t v_stop_boxed_2145_; lean_object* v_res_2146_; 
v_i_boxed_2144_ = lean_unbox_usize(v_i_2141_);
lean_dec(v_i_2141_);
v_stop_boxed_2145_ = lean_unbox_usize(v_stop_2142_);
lean_dec(v_stop_2142_);
v_res_2146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_as_2140_, v_i_boxed_2144_, v_stop_boxed_2145_, v_b_2143_);
lean_dec_ref(v_as_2140_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(lean_object* v_hints_2147_){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2148_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2149_ = lean_unsigned_to_nat(0u);
v___x_2150_ = lean_array_get_size(v_hints_2147_);
v___x_2151_ = lean_nat_dec_lt(v___x_2149_, v___x_2150_);
if (v___x_2151_ == 0)
{
return v___x_2148_;
}
else
{
uint8_t v___x_2152_; 
v___x_2152_ = lean_nat_dec_le(v___x_2150_, v___x_2150_);
if (v___x_2152_ == 0)
{
if (v___x_2151_ == 0)
{
return v___x_2148_;
}
else
{
size_t v___x_2153_; size_t v___x_2154_; lean_object* v___x_2155_; 
v___x_2153_ = ((size_t)0ULL);
v___x_2154_ = lean_usize_of_nat(v___x_2150_);
v___x_2155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_hints_2147_, v___x_2153_, v___x_2154_, v___x_2148_);
return v___x_2155_;
}
}
else
{
size_t v___x_2156_; size_t v___x_2157_; lean_object* v___x_2158_; 
v___x_2156_ = ((size_t)0ULL);
v___x_2157_ = lean_usize_of_nat(v___x_2150_);
v___x_2158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(v_hints_2147_, v___x_2156_, v___x_2157_, v___x_2148_);
return v___x_2158_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___boxed(lean_object* v_hints_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(v_hints_2159_);
lean_dec_ref(v_hints_2159_);
return v_res_2160_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(lean_object* v_as_2161_, size_t v_i_2162_, size_t v_stop_2163_, lean_object* v_b_2164_){
_start:
{
uint8_t v___x_2165_; 
v___x_2165_ = lean_usize_dec_eq(v_i_2162_, v_stop_2163_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; size_t v___x_2171_; size_t v___x_2172_; 
v___x_2166_ = lean_array_uget_borrowed(v_as_2161_, v_i_2162_);
v___x_2167_ = l_Int_repr(v___x_2166_);
v___x_2168_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2169_ = lean_string_append(v___x_2167_, v___x_2168_);
v___x_2170_ = lean_string_append(v_b_2164_, v___x_2169_);
lean_dec_ref(v___x_2169_);
v___x_2171_ = ((size_t)1ULL);
v___x_2172_ = lean_usize_add(v_i_2162_, v___x_2171_);
v_i_2162_ = v___x_2172_;
v_b_2164_ = v___x_2170_;
goto _start;
}
else
{
return v_b_2164_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2161_ = stack[0].m_obj;
size_t v_i_2162_ = stack[1].m_num;
size_t v_stop_2163_ = stack[2].m_num;
lean_object* v_b_2164_ = stack[3].m_obj;
lean_object* v_res_2174_;
v_res_2174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_as_2161_, v_i_2162_, v_stop_2163_, v_b_2164_);
stack->m_obj
 = v_res_2174_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0___boxed(lean_object* v_as_2175_, lean_object* v_i_2176_, lean_object* v_stop_2177_, lean_object* v_b_2178_){
_start:
{
size_t v_i_boxed_2179_; size_t v_stop_boxed_2180_; lean_object* v_res_2181_; 
v_i_boxed_2179_ = lean_unbox_usize(v_i_2176_);
lean_dec(v_i_2176_);
v_stop_boxed_2180_ = lean_unbox_usize(v_stop_2177_);
lean_dec(v_stop_2177_);
v_res_2181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_as_2175_, v_i_boxed_2179_, v_stop_boxed_2180_, v_b_2178_);
lean_dec_ref(v_as_2175_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(lean_object* v_clause_2182_){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; 
v___x_2183_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2184_ = lean_unsigned_to_nat(0u);
v___x_2185_ = lean_array_get_size(v_clause_2182_);
v___x_2186_ = lean_nat_dec_lt(v___x_2184_, v___x_2185_);
if (v___x_2186_ == 0)
{
return v___x_2183_;
}
else
{
uint8_t v___x_2187_; 
v___x_2187_ = lean_nat_dec_le(v___x_2185_, v___x_2185_);
if (v___x_2187_ == 0)
{
if (v___x_2186_ == 0)
{
return v___x_2183_;
}
else
{
size_t v___x_2188_; size_t v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = ((size_t)0ULL);
v___x_2189_ = lean_usize_of_nat(v___x_2185_);
v___x_2190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_clause_2182_, v___x_2188_, v___x_2189_, v___x_2183_);
return v___x_2190_;
}
}
else
{
size_t v___x_2191_; size_t v___x_2192_; lean_object* v___x_2193_; 
v___x_2191_ = ((size_t)0ULL);
v___x_2192_ = lean_usize_of_nat(v___x_2185_);
v___x_2193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(v_clause_2182_, v___x_2191_, v___x_2192_, v___x_2183_);
return v___x_2193_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___boxed(lean_object* v_clause_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_clause_2194_);
lean_dec_ref(v_clause_2194_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(lean_object* v_a_2200_){
_start:
{
switch(lean_obj_tag(v_a_2200_))
{
case 0:
{
lean_object* v_id_2201_; lean_object* v_rupHints_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v_id_2201_ = lean_ctor_get(v_a_2200_, 0);
lean_inc(v_id_2201_);
v_rupHints_2202_ = lean_ctor_get(v_a_2200_, 1);
lean_inc_ref(v_rupHints_2202_);
lean_dec_ref_known(v_a_2200_, 2);
v___x_2203_ = l_Nat_reprFast(v_id_2201_);
v___x_2204_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__0));
v___x_2205_ = lean_string_append(v___x_2203_, v___x_2204_);
v___x_2206_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2202_);
lean_dec_ref(v_rupHints_2202_);
v___x_2207_ = lean_string_append(v___x_2205_, v___x_2206_);
lean_dec_ref(v___x_2206_);
v___x_2208_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2209_ = lean_string_append(v___x_2207_, v___x_2208_);
return v___x_2209_;
}
case 1:
{
lean_object* v_id_2210_; lean_object* v_c_2211_; lean_object* v_rupHints_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v_id_2210_ = lean_ctor_get(v_a_2200_, 0);
lean_inc(v_id_2210_);
v_c_2211_ = lean_ctor_get(v_a_2200_, 1);
lean_inc(v_c_2211_);
v_rupHints_2212_ = lean_ctor_get(v_a_2200_, 2);
lean_inc_ref(v_rupHints_2212_);
lean_dec_ref_known(v_a_2200_, 3);
v___x_2213_ = l_Nat_reprFast(v_id_2210_);
v___x_2214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2215_ = lean_string_append(v___x_2213_, v___x_2214_);
v___x_2216_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_c_2211_);
lean_dec(v_c_2211_);
v___x_2217_ = lean_string_append(v___x_2215_, v___x_2216_);
lean_dec_ref(v___x_2216_);
v___x_2218_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2));
v___x_2219_ = lean_string_append(v___x_2217_, v___x_2218_);
v___x_2220_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2212_);
lean_dec_ref(v_rupHints_2212_);
v___x_2221_ = lean_string_append(v___x_2219_, v___x_2220_);
lean_dec_ref(v___x_2220_);
v___x_2222_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2223_ = lean_string_append(v___x_2221_, v___x_2222_);
return v___x_2223_;
}
case 2:
{
lean_object* v_id_2224_; lean_object* v_c_2225_; lean_object* v_rupHints_2226_; lean_object* v_ratHints_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v_id_2224_ = lean_ctor_get(v_a_2200_, 0);
lean_inc(v_id_2224_);
v_c_2225_ = lean_ctor_get(v_a_2200_, 1);
lean_inc(v_c_2225_);
v_rupHints_2226_ = lean_ctor_get(v_a_2200_, 3);
lean_inc_ref(v_rupHints_2226_);
v_ratHints_2227_ = lean_ctor_get(v_a_2200_, 4);
lean_inc_ref(v_ratHints_2227_);
lean_dec_ref_known(v_a_2200_, 5);
v___x_2228_ = l_Nat_reprFast(v_id_2224_);
v___x_2229_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
v___x_2230_ = lean_string_append(v___x_2228_, v___x_2229_);
v___x_2231_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(v_c_2225_);
lean_dec(v_c_2225_);
v___x_2232_ = lean_string_append(v___x_2230_, v___x_2231_);
lean_dec_ref(v___x_2231_);
v___x_2233_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2));
v___x_2234_ = lean_string_append(v___x_2232_, v___x_2233_);
v___x_2235_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_rupHints_2226_);
lean_dec_ref(v_rupHints_2226_);
v___x_2236_ = lean_string_append(v___x_2234_, v___x_2235_);
lean_dec_ref(v___x_2235_);
v___x_2237_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(v_ratHints_2227_);
lean_dec_ref(v_ratHints_2227_);
v___x_2238_ = lean_string_append(v___x_2236_, v___x_2237_);
lean_dec_ref(v___x_2237_);
v___x_2239_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2240_ = lean_string_append(v___x_2238_, v___x_2239_);
return v___x_2240_;
}
default: 
{
lean_object* v_ids_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v_ids_2241_ = lean_ctor_get(v_a_2200_, 0);
lean_inc_ref(v_ids_2241_);
lean_dec_ref_known(v_a_2200_, 1);
v___x_2242_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3));
v___x_2243_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(v_ids_2241_);
lean_dec_ref(v_ids_2241_);
v___x_2244_ = lean_string_append(v___x_2242_, v___x_2243_);
lean_dec_ref(v___x_2243_);
v___x_2245_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
v___x_2246_ = lean_string_append(v___x_2244_, v___x_2245_);
return v___x_2246_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(lean_object* v_as_2248_, size_t v_i_2249_, size_t v_stop_2250_, lean_object* v_b_2251_){
_start:
{
uint8_t v___x_2252_; 
v___x_2252_ = lean_usize_dec_eq(v_i_2249_, v_stop_2250_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; size_t v___x_2258_; size_t v___x_2259_; 
v___x_2253_ = lean_array_uget_borrowed(v_as_2248_, v_i_2249_);
lean_inc(v___x_2253_);
v___x_2254_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(v___x_2253_);
v___x_2255_ = lean_string_append(v_b_2251_, v___x_2254_);
lean_dec_ref(v___x_2254_);
v___x_2256_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___closed__0));
v___x_2257_ = lean_string_append(v___x_2255_, v___x_2256_);
v___x_2258_ = ((size_t)1ULL);
v___x_2259_ = lean_usize_add(v_i_2249_, v___x_2258_);
v_i_2249_ = v___x_2259_;
v_b_2251_ = v___x_2257_;
goto _start;
}
else
{
return v_b_2251_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2248_ = stack[0].m_obj;
size_t v_i_2249_ = stack[1].m_num;
size_t v_stop_2250_ = stack[2].m_num;
lean_object* v_b_2251_ = stack[3].m_obj;
lean_object* v_res_2261_;
v_res_2261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_as_2248_, v_i_2249_, v_stop_2250_, v_b_2251_);
stack->m_obj
 = v_res_2261_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___boxed(lean_object* v_as_2262_, lean_object* v_i_2263_, lean_object* v_stop_2264_, lean_object* v_b_2265_){
_start:
{
size_t v_i_boxed_2266_; size_t v_stop_boxed_2267_; lean_object* v_res_2268_; 
v_i_boxed_2266_ = lean_unbox_usize(v_i_2263_);
lean_dec(v_i_2263_);
v_stop_boxed_2267_ = lean_unbox_usize(v_stop_2264_);
lean_dec(v_stop_2264_);
v_res_2268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_as_2262_, v_i_boxed_2266_, v_stop_boxed_2267_, v_b_2265_);
lean_dec_ref(v_as_2262_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString(lean_object* v_proof_2269_){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2270_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
v___x_2271_ = lean_unsigned_to_nat(0u);
v___x_2272_ = lean_array_get_size(v_proof_2269_);
v___x_2273_ = lean_nat_dec_lt(v___x_2271_, v___x_2272_);
if (v___x_2273_ == 0)
{
return v___x_2270_;
}
else
{
uint8_t v___x_2274_; 
v___x_2274_ = lean_nat_dec_le(v___x_2272_, v___x_2272_);
if (v___x_2274_ == 0)
{
if (v___x_2273_ == 0)
{
return v___x_2270_;
}
else
{
size_t v___x_2275_; size_t v___x_2276_; lean_object* v___x_2277_; 
v___x_2275_ = ((size_t)0ULL);
v___x_2276_ = lean_usize_of_nat(v___x_2272_);
v___x_2277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_proof_2269_, v___x_2275_, v___x_2276_, v___x_2270_);
return v___x_2277_;
}
}
else
{
size_t v___x_2278_; size_t v___x_2279_; lean_object* v___x_2280_; 
v___x_2278_ = ((size_t)0ULL);
v___x_2279_ = lean_usize_of_nat(v___x_2272_);
v___x_2280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(v_proof_2269_, v___x_2278_, v___x_2279_, v___x_2270_);
return v___x_2280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString___boxed(lean_object* v_proof_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_proof_2281_);
lean_dec_ref(v_proof_2281_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startDelete(lean_object* v_acc_2283_){
_start:
{
uint8_t v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = 100;
v___x_2285_ = lean_byte_array_push(v_acc_2283_, v___x_2284_);
return v___x_2285_;
}
}
lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(lean_object* v_acc_2286_, uint64_t v_lit_2287_){
_start:
{
uint8_t v___y_2289_; uint64_t v___x_2294_; uint8_t v___x_2295_; 
v___x_2294_ = 0ULL;
v___x_2295_ = lean_uint64_dec_eq(v_lit_2287_, v___x_2294_);
if (v___x_2295_ == 0)
{
uint64_t v___x_2296_; uint8_t v___x_2297_; 
v___x_2296_ = 127ULL;
v___x_2297_ = lean_uint64_dec_lt(v___x_2296_, v_lit_2287_);
if (v___x_2297_ == 0)
{
uint8_t v___x_2298_; uint8_t v___x_2299_; uint8_t v___x_2300_; 
v___x_2298_ = lean_uint64_to_uint8(v_lit_2287_);
v___x_2299_ = 127;
v___x_2300_ = lean_uint8_land(v___x_2298_, v___x_2299_);
v___y_2289_ = v___x_2300_;
goto v___jp_2288_;
}
else
{
uint8_t v___x_2301_; uint8_t v___x_2302_; uint8_t v___x_2303_; uint8_t v___x_2304_; uint8_t v___x_2305_; 
v___x_2301_ = lean_uint64_to_uint8(v_lit_2287_);
v___x_2302_ = 127;
v___x_2303_ = lean_uint8_land(v___x_2301_, v___x_2302_);
v___x_2304_ = 128;
v___x_2305_ = lean_uint8_lor(v___x_2303_, v___x_2304_);
v___y_2289_ = v___x_2305_;
goto v___jp_2288_;
}
}
else
{
return v_acc_2286_;
}
v___jp_2288_:
{
lean_object* v_acc_2290_; uint64_t v___x_2291_; uint64_t v___x_2292_; 
v_acc_2290_ = lean_byte_array_push(v_acc_2286_, v___y_2289_);
v___x_2291_ = 7ULL;
v___x_2292_ = lean_uint64_shift_right(v_lit_2287_, v___x_2291_);
v_acc_2286_ = v_acc_2290_;
v_lit_2287_ = v___x_2292_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode_0interp(lean_interpreter_value* stack)
{
lean_object* v_acc_2286_ = stack[0].m_obj;
uint64_t v_lit_2287_ = stack[1].m_num;
lean_object* v_res_2306_;
v_res_2306_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(v_acc_2286_, v_lit_2287_);
stack->m_obj
 = v_res_2306_;
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode___boxed(lean_object* v_acc_2307_, lean_object* v_lit_2308_){
_start:
{
uint64_t v_lit_boxed_2309_; lean_object* v_res_2310_; 
v_lit_boxed_2309_ = lean_unbox_uint64(v_lit_2308_);
lean_dec_ref(v_lit_2308_);
v_res_2310_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(v_acc_2307_, v_lit_boxed_2309_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(lean_object* v_msg_2311_){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = l_ByteArray_empty;
v___x_2313_ = lean_panic_fn_borrowed(v___x_2312_, v_msg_2311_);
return v___x_2313_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0(void){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = lean_cstr_to_nat("18446744073709551615");
return v___x_2314_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2318_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3));
v___x_2319_ = lean_unsigned_to_nat(4u);
v___x_2320_ = lean_unsigned_to_nat(400u);
v___x_2321_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2));
v___x_2322_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1));
v___x_2323_ = l_mkPanicMessageWithDecl(v___x_2322_, v___x_2321_, v___x_2320_, v___x_2319_, v___x_2318_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(lean_object* v_acc_2324_, lean_object* v_lit_2325_){
_start:
{
lean_object* v___y_2327_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v___x_2334_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
v___x_2335_ = lean_int_dec_lt(v___x_2334_, v_lit_2325_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2336_ = lean_unsigned_to_nat(2u);
v___x_2337_ = lean_nat_abs(v_lit_2325_);
v___x_2338_ = lean_nat_mul(v___x_2336_, v___x_2337_);
lean_dec(v___x_2337_);
v___x_2339_ = lean_unsigned_to_nat(1u);
v___x_2340_ = lean_nat_add(v___x_2338_, v___x_2339_);
lean_dec(v___x_2338_);
v___y_2327_ = v___x_2340_;
goto v___jp_2326_;
}
else
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2341_ = lean_unsigned_to_nat(2u);
v___x_2342_ = lean_nat_abs(v_lit_2325_);
v___x_2343_ = lean_nat_mul(v___x_2341_, v___x_2342_);
lean_dec(v___x_2342_);
v___y_2327_ = v___x_2343_;
goto v___jp_2326_;
}
v___jp_2326_:
{
lean_object* v___x_2328_; uint8_t v___x_2329_; 
v___x_2328_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0);
v___x_2329_ = lean_nat_dec_le(v___y_2327_, v___x_2328_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
lean_dec(v___y_2327_);
lean_dec_ref(v_acc_2324_);
v___x_2330_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4);
v___x_2331_ = l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(v___x_2330_);
return v___x_2331_;
}
else
{
uint64_t v_mapped_2332_; lean_object* v___x_2333_; 
v_mapped_2332_ = lean_uint64_of_nat(v___y_2327_);
lean_dec(v___y_2327_);
v___x_2333_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(v_acc_2324_, v_mapped_2332_);
return v___x_2333_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___boxed(lean_object* v_acc_2344_, lean_object* v_lit_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2344_, v_lit_2345_);
lean_dec(v_lit_2345_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_zeroByte(lean_object* v_acc_2347_){
_start:
{
uint8_t v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = 0;
v___x_2349_ = lean_byte_array_push(v_acc_2347_, v___x_2348_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addNat(lean_object* v_acc_2350_, lean_object* v_n_2351_){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_nat_to_int(v_n_2351_);
v___x_2353_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2350_, v___x_2352_);
lean_dec(v___x_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startAdd(lean_object* v_acc_2354_){
_start:
{
uint8_t v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = 97;
v___x_2356_ = lean_byte_array_push(v_acc_2354_, v___x_2355_);
return v___x_2356_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(lean_object* v_as_2357_, size_t v_i_2358_, size_t v_stop_2359_, lean_object* v_b_2360_){
_start:
{
uint8_t v___x_2361_; 
v___x_2361_ = lean_usize_dec_eq(v_i_2358_, v_stop_2359_);
if (v___x_2361_ == 0)
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; size_t v___x_2365_; size_t v___x_2366_; 
v___x_2362_ = lean_array_uget_borrowed(v_as_2357_, v_i_2358_);
lean_inc(v___x_2362_);
v___x_2363_ = lean_nat_to_int(v___x_2362_);
v___x_2364_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2360_, v___x_2363_);
lean_dec(v___x_2363_);
v___x_2365_ = ((size_t)1ULL);
v___x_2366_ = lean_usize_add(v_i_2358_, v___x_2365_);
v_i_2358_ = v___x_2366_;
v_b_2360_ = v___x_2364_;
goto _start;
}
else
{
return v_b_2360_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2357_ = stack[0].m_obj;
size_t v_i_2358_ = stack[1].m_num;
size_t v_stop_2359_ = stack[2].m_num;
lean_object* v_b_2360_ = stack[3].m_obj;
lean_object* v_res_2368_;
v_res_2368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(v_as_2357_, v_i_2358_, v_stop_2359_, v_b_2360_);
stack->m_obj
 = v_res_2368_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0___boxed(lean_object* v_as_2369_, lean_object* v_i_2370_, lean_object* v_stop_2371_, lean_object* v_b_2372_){
_start:
{
size_t v_i_boxed_2373_; size_t v_stop_boxed_2374_; lean_object* v_res_2375_; 
v_i_boxed_2373_ = lean_unbox_usize(v_i_2370_);
lean_dec(v_i_2370_);
v_stop_boxed_2374_ = lean_unbox_usize(v_stop_2371_);
lean_dec(v_stop_2371_);
v_res_2375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(v_as_2369_, v_i_boxed_2373_, v_stop_boxed_2374_, v_b_2372_);
lean_dec_ref(v_as_2369_);
return v_res_2375_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(lean_object* v_as_2376_, size_t v_i_2377_, size_t v_stop_2378_, lean_object* v_b_2379_){
_start:
{
uint8_t v___x_2380_; 
v___x_2380_ = lean_usize_dec_eq(v_i_2377_, v_stop_2378_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; size_t v___x_2384_; size_t v___x_2385_; lean_object* v___x_2386_; 
v___x_2381_ = lean_array_uget_borrowed(v_as_2376_, v_i_2377_);
lean_inc(v___x_2381_);
v___x_2382_ = lean_nat_to_int(v___x_2381_);
v___x_2383_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2379_, v___x_2382_);
lean_dec(v___x_2382_);
v___x_2384_ = ((size_t)1ULL);
v___x_2385_ = lean_usize_add(v_i_2377_, v___x_2384_);
v___x_2386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(v_as_2376_, v___x_2385_, v_stop_2378_, v___x_2383_);
return v___x_2386_;
}
else
{
return v_b_2379_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2376_ = stack[0].m_obj;
size_t v_i_2377_ = stack[1].m_num;
size_t v_stop_2378_ = stack[2].m_num;
lean_object* v_b_2379_ = stack[3].m_obj;
lean_object* v_res_2387_;
v_res_2387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_as_2376_, v_i_2377_, v_stop_2378_, v_b_2379_);
stack->m_obj
 = v_res_2387_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0___boxed(lean_object* v_as_2388_, lean_object* v_i_2389_, lean_object* v_stop_2390_, lean_object* v_b_2391_){
_start:
{
size_t v_i_boxed_2392_; size_t v_stop_boxed_2393_; lean_object* v_res_2394_; 
v_i_boxed_2392_ = lean_unbox_usize(v_i_2389_);
lean_dec(v_i_2389_);
v_stop_boxed_2393_ = lean_unbox_usize(v_stop_2390_);
lean_dec(v_stop_2390_);
v_res_2394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_as_2388_, v_i_boxed_2392_, v_stop_boxed_2393_, v_b_2391_);
lean_dec_ref(v_as_2388_);
return v_res_2394_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(lean_object* v_as_2395_, size_t v_i_2396_, size_t v_stop_2397_, lean_object* v_b_2398_){
_start:
{
lean_object* v___y_2400_; uint8_t v___x_2404_; 
v___x_2404_ = lean_usize_dec_eq(v_i_2396_, v_stop_2397_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; lean_object* v_fst_2406_; lean_object* v_snd_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v_acc_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; 
v___x_2405_ = lean_array_uget_borrowed(v_as_2395_, v_i_2396_);
v_fst_2406_ = lean_ctor_get(v___x_2405_, 0);
v_snd_2407_ = lean_ctor_get(v___x_2405_, 1);
v___x_2408_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_2406_);
v___x_2409_ = lean_nat_to_int(v_fst_2406_);
v___x_2410_ = lean_int_neg(v___x_2409_);
lean_dec(v___x_2409_);
v_acc_2411_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2398_, v___x_2410_);
lean_dec(v___x_2410_);
v___x_2412_ = lean_array_get_size(v_snd_2407_);
v___x_2413_ = lean_nat_dec_lt(v___x_2408_, v___x_2412_);
if (v___x_2413_ == 0)
{
v___y_2400_ = v_acc_2411_;
goto v___jp_2399_;
}
else
{
uint8_t v___x_2414_; 
v___x_2414_ = lean_nat_dec_le(v___x_2412_, v___x_2412_);
if (v___x_2414_ == 0)
{
if (v___x_2413_ == 0)
{
v___y_2400_ = v_acc_2411_;
goto v___jp_2399_;
}
else
{
size_t v___x_2415_; size_t v___x_2416_; lean_object* v___x_2417_; 
v___x_2415_ = ((size_t)0ULL);
v___x_2416_ = lean_usize_of_nat(v___x_2412_);
v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2407_, v___x_2415_, v___x_2416_, v_acc_2411_);
v___y_2400_ = v___x_2417_;
goto v___jp_2399_;
}
}
else
{
size_t v___x_2418_; size_t v___x_2419_; lean_object* v___x_2420_; 
v___x_2418_ = ((size_t)0ULL);
v___x_2419_ = lean_usize_of_nat(v___x_2412_);
v___x_2420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2407_, v___x_2418_, v___x_2419_, v_acc_2411_);
v___y_2400_ = v___x_2420_;
goto v___jp_2399_;
}
}
}
else
{
return v_b_2398_;
}
v___jp_2399_:
{
size_t v___x_2401_; size_t v___x_2402_; 
v___x_2401_ = ((size_t)1ULL);
v___x_2402_ = lean_usize_add(v_i_2396_, v___x_2401_);
v_i_2396_ = v___x_2402_;
v_b_2398_ = v___y_2400_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2395_ = stack[0].m_obj;
size_t v_i_2396_ = stack[1].m_num;
size_t v_stop_2397_ = stack[2].m_num;
lean_object* v_b_2398_ = stack[3].m_obj;
lean_object* v_res_2421_;
v_res_2421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(v_as_2395_, v_i_2396_, v_stop_2397_, v_b_2398_);
stack->m_obj
 = v_res_2421_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3___boxed(lean_object* v_as_2422_, lean_object* v_i_2423_, lean_object* v_stop_2424_, lean_object* v_b_2425_){
_start:
{
size_t v_i_boxed_2426_; size_t v_stop_boxed_2427_; lean_object* v_res_2428_; 
v_i_boxed_2426_ = lean_unbox_usize(v_i_2423_);
lean_dec(v_i_2423_);
v_stop_boxed_2427_ = lean_unbox_usize(v_stop_2424_);
lean_dec(v_stop_2424_);
v_res_2428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(v_as_2422_, v_i_boxed_2426_, v_stop_boxed_2427_, v_b_2425_);
lean_dec_ref(v_as_2422_);
return v_res_2428_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(lean_object* v_as_2429_, size_t v_i_2430_, size_t v_stop_2431_, lean_object* v_b_2432_){
_start:
{
lean_object* v___y_2434_; uint8_t v___x_2438_; 
v___x_2438_ = lean_usize_dec_eq(v_i_2430_, v_stop_2431_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; lean_object* v_fst_2440_; lean_object* v_snd_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v_acc_2445_; lean_object* v___x_2446_; uint8_t v___x_2447_; 
v___x_2439_ = lean_array_uget_borrowed(v_as_2429_, v_i_2430_);
v_fst_2440_ = lean_ctor_get(v___x_2439_, 0);
v_snd_2441_ = lean_ctor_get(v___x_2439_, 1);
v___x_2442_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_2440_);
v___x_2443_ = lean_nat_to_int(v_fst_2440_);
v___x_2444_ = lean_int_neg(v___x_2443_);
lean_dec(v___x_2443_);
v_acc_2445_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2432_, v___x_2444_);
lean_dec(v___x_2444_);
v___x_2446_ = lean_array_get_size(v_snd_2441_);
v___x_2447_ = lean_nat_dec_lt(v___x_2442_, v___x_2446_);
if (v___x_2447_ == 0)
{
v___y_2434_ = v_acc_2445_;
goto v___jp_2433_;
}
else
{
uint8_t v___x_2448_; 
v___x_2448_ = lean_nat_dec_le(v___x_2446_, v___x_2446_);
if (v___x_2448_ == 0)
{
if (v___x_2447_ == 0)
{
v___y_2434_ = v_acc_2445_;
goto v___jp_2433_;
}
else
{
size_t v___x_2449_; size_t v___x_2450_; lean_object* v___x_2451_; 
v___x_2449_ = ((size_t)0ULL);
v___x_2450_ = lean_usize_of_nat(v___x_2446_);
v___x_2451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2441_, v___x_2449_, v___x_2450_, v_acc_2445_);
v___y_2434_ = v___x_2451_;
goto v___jp_2433_;
}
}
else
{
size_t v___x_2452_; size_t v___x_2453_; lean_object* v___x_2454_; 
v___x_2452_ = ((size_t)0ULL);
v___x_2453_ = lean_usize_of_nat(v___x_2446_);
v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_snd_2441_, v___x_2452_, v___x_2453_, v_acc_2445_);
v___y_2434_ = v___x_2454_;
goto v___jp_2433_;
}
}
}
else
{
return v_b_2432_;
}
v___jp_2433_:
{
size_t v___x_2435_; size_t v___x_2436_; lean_object* v___x_2437_; 
v___x_2435_ = ((size_t)1ULL);
v___x_2436_ = lean_usize_add(v_i_2430_, v___x_2435_);
v___x_2437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(v_as_2429_, v___x_2436_, v_stop_2431_, v___y_2434_);
return v___x_2437_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2429_ = stack[0].m_obj;
size_t v_i_2430_ = stack[1].m_num;
size_t v_stop_2431_ = stack[2].m_num;
lean_object* v_b_2432_ = stack[3].m_obj;
lean_object* v_res_2455_;
v_res_2455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_as_2429_, v_i_2430_, v_stop_2431_, v_b_2432_);
stack->m_obj
 = v_res_2455_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2___boxed(lean_object* v_as_2456_, lean_object* v_i_2457_, lean_object* v_stop_2458_, lean_object* v_b_2459_){
_start:
{
size_t v_i_boxed_2460_; size_t v_stop_boxed_2461_; lean_object* v_res_2462_; 
v_i_boxed_2460_ = lean_unbox_usize(v_i_2457_);
lean_dec(v_i_2457_);
v_stop_boxed_2461_ = lean_unbox_usize(v_stop_2458_);
lean_dec(v_stop_2458_);
v_res_2462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_as_2456_, v_i_boxed_2460_, v_stop_boxed_2461_, v_b_2459_);
lean_dec_ref(v_as_2456_);
return v_res_2462_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(lean_object* v_as_2463_, size_t v_i_2464_, size_t v_stop_2465_, lean_object* v_b_2466_){
_start:
{
uint8_t v___x_2467_; 
v___x_2467_ = lean_usize_dec_eq(v_i_2464_, v_stop_2465_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; lean_object* v___x_2469_; size_t v___x_2470_; size_t v___x_2471_; 
v___x_2468_ = lean_array_uget_borrowed(v_as_2463_, v_i_2464_);
v___x_2469_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_b_2466_, v___x_2468_);
v___x_2470_ = ((size_t)1ULL);
v___x_2471_ = lean_usize_add(v_i_2464_, v___x_2470_);
v_i_2464_ = v___x_2471_;
v_b_2466_ = v___x_2469_;
goto _start;
}
else
{
return v_b_2466_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2463_ = stack[0].m_obj;
size_t v_i_2464_ = stack[1].m_num;
size_t v_stop_2465_ = stack[2].m_num;
lean_object* v_b_2466_ = stack[3].m_obj;
lean_object* v_res_2473_;
v_res_2473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_as_2463_, v_i_2464_, v_stop_2465_, v_b_2466_);
stack->m_obj
 = v_res_2473_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1___boxed(lean_object* v_as_2474_, lean_object* v_i_2475_, lean_object* v_stop_2476_, lean_object* v_b_2477_){
_start:
{
size_t v_i_boxed_2478_; size_t v_stop_boxed_2479_; lean_object* v_res_2480_; 
v_i_boxed_2478_ = lean_unbox_usize(v_i_2475_);
lean_dec(v_i_2475_);
v_stop_boxed_2479_ = lean_unbox_usize(v_stop_2476_);
lean_dec(v_stop_2476_);
v_res_2480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_as_2474_, v_i_boxed_2478_, v_stop_boxed_2479_, v_b_2477_);
lean_dec_ref(v_as_2474_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(lean_object* v_proof_2481_, lean_object* v_idx_2482_, lean_object* v_acc_2483_){
_start:
{
lean_object* v___y_2485_; lean_object* v___y_2490_; lean_object* v___y_2494_; lean_object* v___y_2498_; lean_object* v___y_2502_; lean_object* v___x_2505_; uint8_t v___x_2506_; 
v___x_2505_ = lean_array_get_size(v_proof_2481_);
v___x_2506_ = lean_nat_dec_lt(v_idx_2482_, v___x_2505_);
if (v___x_2506_ == 0)
{
lean_dec(v_idx_2482_);
return v_acc_2483_;
}
else
{
lean_object* v___x_2507_; 
v___x_2507_ = lean_array_fget_borrowed(v_proof_2481_, v_idx_2482_);
switch(lean_obj_tag(v___x_2507_))
{
case 0:
{
lean_object* v_id_2508_; lean_object* v_rupHints_2509_; uint8_t v___x_2510_; lean_object* v_acc_2511_; lean_object* v___x_2512_; lean_object* v_acc_2513_; uint8_t v___x_2514_; lean_object* v_acc_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
v_id_2508_ = lean_ctor_get(v___x_2507_, 0);
v_rupHints_2509_ = lean_ctor_get(v___x_2507_, 1);
v___x_2510_ = 97;
v_acc_2511_ = lean_byte_array_push(v_acc_2483_, v___x_2510_);
lean_inc(v_id_2508_);
v___x_2512_ = lean_nat_to_int(v_id_2508_);
v_acc_2513_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2511_, v___x_2512_);
lean_dec(v___x_2512_);
v___x_2514_ = 0;
v_acc_2515_ = lean_byte_array_push(v_acc_2513_, v___x_2514_);
v___x_2516_ = lean_unsigned_to_nat(0u);
v___x_2517_ = lean_array_get_size(v_rupHints_2509_);
v___x_2518_ = lean_nat_dec_lt(v___x_2516_, v___x_2517_);
if (v___x_2518_ == 0)
{
v___y_2494_ = v_acc_2515_;
goto v___jp_2493_;
}
else
{
uint8_t v___x_2519_; 
v___x_2519_ = lean_nat_dec_le(v___x_2517_, v___x_2517_);
if (v___x_2519_ == 0)
{
if (v___x_2518_ == 0)
{
v___y_2494_ = v_acc_2515_;
goto v___jp_2493_;
}
else
{
size_t v___x_2520_; size_t v___x_2521_; lean_object* v___x_2522_; 
v___x_2520_ = ((size_t)0ULL);
v___x_2521_ = lean_usize_of_nat(v___x_2517_);
v___x_2522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2509_, v___x_2520_, v___x_2521_, v_acc_2515_);
v___y_2494_ = v___x_2522_;
goto v___jp_2493_;
}
}
else
{
size_t v___x_2523_; size_t v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = ((size_t)0ULL);
v___x_2524_ = lean_usize_of_nat(v___x_2517_);
v___x_2525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2509_, v___x_2523_, v___x_2524_, v_acc_2515_);
v___y_2494_ = v___x_2525_;
goto v___jp_2493_;
}
}
}
case 1:
{
lean_object* v_id_2526_; lean_object* v_c_2527_; lean_object* v_rupHints_2528_; uint8_t v___x_2529_; lean_object* v_acc_2530_; lean_object* v___x_2531_; lean_object* v_acc_2532_; lean_object* v___x_2533_; lean_object* v___y_2535_; lean_object* v___x_2547_; uint8_t v___x_2548_; 
v_id_2526_ = lean_ctor_get(v___x_2507_, 0);
v_c_2527_ = lean_ctor_get(v___x_2507_, 1);
v_rupHints_2528_ = lean_ctor_get(v___x_2507_, 2);
v___x_2529_ = 97;
v_acc_2530_ = lean_byte_array_push(v_acc_2483_, v___x_2529_);
lean_inc(v_id_2526_);
v___x_2531_ = lean_nat_to_int(v_id_2526_);
v_acc_2532_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2530_, v___x_2531_);
lean_dec(v___x_2531_);
v___x_2533_ = lean_unsigned_to_nat(0u);
v___x_2547_ = lean_array_get_size(v_c_2527_);
v___x_2548_ = lean_nat_dec_lt(v___x_2533_, v___x_2547_);
if (v___x_2548_ == 0)
{
v___y_2535_ = v_acc_2532_;
goto v___jp_2534_;
}
else
{
uint8_t v___x_2549_; 
v___x_2549_ = lean_nat_dec_le(v___x_2547_, v___x_2547_);
if (v___x_2549_ == 0)
{
if (v___x_2548_ == 0)
{
v___y_2535_ = v_acc_2532_;
goto v___jp_2534_;
}
else
{
size_t v___x_2550_; size_t v___x_2551_; lean_object* v___x_2552_; 
v___x_2550_ = ((size_t)0ULL);
v___x_2551_ = lean_usize_of_nat(v___x_2547_);
v___x_2552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2527_, v___x_2550_, v___x_2551_, v_acc_2532_);
v___y_2535_ = v___x_2552_;
goto v___jp_2534_;
}
}
else
{
size_t v___x_2553_; size_t v___x_2554_; lean_object* v___x_2555_; 
v___x_2553_ = ((size_t)0ULL);
v___x_2554_ = lean_usize_of_nat(v___x_2547_);
v___x_2555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2527_, v___x_2553_, v___x_2554_, v_acc_2532_);
v___y_2535_ = v___x_2555_;
goto v___jp_2534_;
}
}
v___jp_2534_:
{
uint8_t v___x_2536_; lean_object* v_acc_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; 
v___x_2536_ = 0;
v_acc_2537_ = lean_byte_array_push(v___y_2535_, v___x_2536_);
v___x_2538_ = lean_array_get_size(v_rupHints_2528_);
v___x_2539_ = lean_nat_dec_lt(v___x_2533_, v___x_2538_);
if (v___x_2539_ == 0)
{
v___y_2498_ = v_acc_2537_;
goto v___jp_2497_;
}
else
{
uint8_t v___x_2540_; 
v___x_2540_ = lean_nat_dec_le(v___x_2538_, v___x_2538_);
if (v___x_2540_ == 0)
{
if (v___x_2539_ == 0)
{
v___y_2498_ = v_acc_2537_;
goto v___jp_2497_;
}
else
{
size_t v___x_2541_; size_t v___x_2542_; lean_object* v___x_2543_; 
v___x_2541_ = ((size_t)0ULL);
v___x_2542_ = lean_usize_of_nat(v___x_2538_);
v___x_2543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2528_, v___x_2541_, v___x_2542_, v_acc_2537_);
v___y_2498_ = v___x_2543_;
goto v___jp_2497_;
}
}
else
{
size_t v___x_2544_; size_t v___x_2545_; lean_object* v___x_2546_; 
v___x_2544_ = ((size_t)0ULL);
v___x_2545_ = lean_usize_of_nat(v___x_2538_);
v___x_2546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2528_, v___x_2544_, v___x_2545_, v_acc_2537_);
v___y_2498_ = v___x_2546_;
goto v___jp_2497_;
}
}
}
}
case 2:
{
lean_object* v_id_2556_; lean_object* v_c_2557_; lean_object* v_rupHints_2558_; lean_object* v_ratHints_2559_; uint8_t v___x_2560_; lean_object* v_acc_2561_; lean_object* v___x_2562_; lean_object* v_acc_2563_; lean_object* v___x_2564_; lean_object* v___y_2566_; lean_object* v___y_2577_; lean_object* v___x_2589_; uint8_t v___x_2590_; 
v_id_2556_ = lean_ctor_get(v___x_2507_, 0);
v_c_2557_ = lean_ctor_get(v___x_2507_, 1);
v_rupHints_2558_ = lean_ctor_get(v___x_2507_, 3);
v_ratHints_2559_ = lean_ctor_get(v___x_2507_, 4);
v___x_2560_ = 97;
v_acc_2561_ = lean_byte_array_push(v_acc_2483_, v___x_2560_);
lean_inc(v_id_2556_);
v___x_2562_ = lean_nat_to_int(v_id_2556_);
v_acc_2563_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(v_acc_2561_, v___x_2562_);
lean_dec(v___x_2562_);
v___x_2564_ = lean_unsigned_to_nat(0u);
v___x_2589_ = lean_array_get_size(v_c_2557_);
v___x_2590_ = lean_nat_dec_lt(v___x_2564_, v___x_2589_);
if (v___x_2590_ == 0)
{
v___y_2577_ = v_acc_2563_;
goto v___jp_2576_;
}
else
{
uint8_t v___x_2591_; 
v___x_2591_ = lean_nat_dec_le(v___x_2589_, v___x_2589_);
if (v___x_2591_ == 0)
{
if (v___x_2590_ == 0)
{
v___y_2577_ = v_acc_2563_;
goto v___jp_2576_;
}
else
{
size_t v___x_2592_; size_t v___x_2593_; lean_object* v___x_2594_; 
v___x_2592_ = ((size_t)0ULL);
v___x_2593_ = lean_usize_of_nat(v___x_2589_);
v___x_2594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2557_, v___x_2592_, v___x_2593_, v_acc_2563_);
v___y_2577_ = v___x_2594_;
goto v___jp_2576_;
}
}
else
{
size_t v___x_2595_; size_t v___x_2596_; lean_object* v___x_2597_; 
v___x_2595_ = ((size_t)0ULL);
v___x_2596_ = lean_usize_of_nat(v___x_2589_);
v___x_2597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(v_c_2557_, v___x_2595_, v___x_2596_, v_acc_2563_);
v___y_2577_ = v___x_2597_;
goto v___jp_2576_;
}
}
v___jp_2565_:
{
lean_object* v___x_2567_; uint8_t v___x_2568_; 
v___x_2567_ = lean_array_get_size(v_ratHints_2559_);
v___x_2568_ = lean_nat_dec_lt(v___x_2564_, v___x_2567_);
if (v___x_2568_ == 0)
{
v___y_2490_ = v___y_2566_;
goto v___jp_2489_;
}
else
{
uint8_t v___x_2569_; 
v___x_2569_ = lean_nat_dec_le(v___x_2567_, v___x_2567_);
if (v___x_2569_ == 0)
{
if (v___x_2568_ == 0)
{
v___y_2490_ = v___y_2566_;
goto v___jp_2489_;
}
else
{
size_t v___x_2570_; size_t v___x_2571_; lean_object* v___x_2572_; 
v___x_2570_ = ((size_t)0ULL);
v___x_2571_ = lean_usize_of_nat(v___x_2567_);
v___x_2572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_ratHints_2559_, v___x_2570_, v___x_2571_, v___y_2566_);
v___y_2490_ = v___x_2572_;
goto v___jp_2489_;
}
}
else
{
size_t v___x_2573_; size_t v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = ((size_t)0ULL);
v___x_2574_ = lean_usize_of_nat(v___x_2567_);
v___x_2575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(v_ratHints_2559_, v___x_2573_, v___x_2574_, v___y_2566_);
v___y_2490_ = v___x_2575_;
goto v___jp_2489_;
}
}
}
v___jp_2576_:
{
uint8_t v___x_2578_; lean_object* v_acc_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; 
v___x_2578_ = 0;
v_acc_2579_ = lean_byte_array_push(v___y_2577_, v___x_2578_);
v___x_2580_ = lean_array_get_size(v_rupHints_2558_);
v___x_2581_ = lean_nat_dec_lt(v___x_2564_, v___x_2580_);
if (v___x_2581_ == 0)
{
v___y_2566_ = v_acc_2579_;
goto v___jp_2565_;
}
else
{
uint8_t v___x_2582_; 
v___x_2582_ = lean_nat_dec_le(v___x_2580_, v___x_2580_);
if (v___x_2582_ == 0)
{
if (v___x_2581_ == 0)
{
v___y_2566_ = v_acc_2579_;
goto v___jp_2565_;
}
else
{
size_t v___x_2583_; size_t v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = ((size_t)0ULL);
v___x_2584_ = lean_usize_of_nat(v___x_2580_);
v___x_2585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2558_, v___x_2583_, v___x_2584_, v_acc_2579_);
v___y_2566_ = v___x_2585_;
goto v___jp_2565_;
}
}
else
{
size_t v___x_2586_; size_t v___x_2587_; lean_object* v___x_2588_; 
v___x_2586_ = ((size_t)0ULL);
v___x_2587_ = lean_usize_of_nat(v___x_2580_);
v___x_2588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_rupHints_2558_, v___x_2586_, v___x_2587_, v_acc_2579_);
v___y_2566_ = v___x_2588_;
goto v___jp_2565_;
}
}
}
}
default: 
{
lean_object* v_ids_2598_; uint8_t v___x_2599_; lean_object* v_acc_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; uint8_t v___x_2603_; 
v_ids_2598_ = lean_ctor_get(v___x_2507_, 0);
v___x_2599_ = 100;
v_acc_2600_ = lean_byte_array_push(v_acc_2483_, v___x_2599_);
v___x_2601_ = lean_unsigned_to_nat(0u);
v___x_2602_ = lean_array_get_size(v_ids_2598_);
v___x_2603_ = lean_nat_dec_lt(v___x_2601_, v___x_2602_);
if (v___x_2603_ == 0)
{
v___y_2502_ = v_acc_2600_;
goto v___jp_2501_;
}
else
{
uint8_t v___x_2604_; 
v___x_2604_ = lean_nat_dec_le(v___x_2602_, v___x_2602_);
if (v___x_2604_ == 0)
{
if (v___x_2603_ == 0)
{
v___y_2502_ = v_acc_2600_;
goto v___jp_2501_;
}
else
{
size_t v___x_2605_; size_t v___x_2606_; lean_object* v___x_2607_; 
v___x_2605_ = ((size_t)0ULL);
v___x_2606_ = lean_usize_of_nat(v___x_2602_);
v___x_2607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_ids_2598_, v___x_2605_, v___x_2606_, v_acc_2600_);
v___y_2502_ = v___x_2607_;
goto v___jp_2501_;
}
}
else
{
size_t v___x_2608_; size_t v___x_2609_; lean_object* v___x_2610_; 
v___x_2608_ = ((size_t)0ULL);
v___x_2609_ = lean_usize_of_nat(v___x_2602_);
v___x_2610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(v_ids_2598_, v___x_2608_, v___x_2609_, v_acc_2600_);
v___y_2502_ = v___x_2610_;
goto v___jp_2501_;
}
}
}
}
}
v___jp_2484_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = lean_unsigned_to_nat(1u);
v___x_2487_ = lean_nat_add(v_idx_2482_, v___x_2486_);
lean_dec(v_idx_2482_);
v_idx_2482_ = v___x_2487_;
v_acc_2483_ = v___y_2485_;
goto _start;
}
v___jp_2489_:
{
uint8_t v___x_2491_; lean_object* v_acc_2492_; 
v___x_2491_ = 0;
v_acc_2492_ = lean_byte_array_push(v___y_2490_, v___x_2491_);
v___y_2485_ = v_acc_2492_;
goto v___jp_2484_;
}
v___jp_2493_:
{
uint8_t v___x_2495_; lean_object* v_acc_2496_; 
v___x_2495_ = 0;
v_acc_2496_ = lean_byte_array_push(v___y_2494_, v___x_2495_);
v___y_2485_ = v_acc_2496_;
goto v___jp_2484_;
}
v___jp_2497_:
{
uint8_t v___x_2499_; lean_object* v_acc_2500_; 
v___x_2499_ = 0;
v_acc_2500_ = lean_byte_array_push(v___y_2498_, v___x_2499_);
v___y_2485_ = v_acc_2500_;
goto v___jp_2484_;
}
v___jp_2501_:
{
uint8_t v___x_2503_; lean_object* v_acc_2504_; 
v___x_2503_ = 0;
v_acc_2504_ = lean_byte_array_push(v___y_2502_, v___x_2503_);
v___y_2485_ = v_acc_2504_;
goto v___jp_2484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___boxed(lean_object* v_proof_2611_, lean_object* v_idx_2612_, lean_object* v_acc_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(v_proof_2611_, v_idx_2612_, v_acc_2613_);
lean_dec_ref(v_proof_2611_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(lean_object* v_proof_2615_){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2616_ = lean_unsigned_to_nat(0u);
v___x_2617_ = lean_unsigned_to_nat(4u);
v___x_2618_ = lean_array_get_size(v_proof_2615_);
v___x_2619_ = lean_nat_mul(v___x_2617_, v___x_2618_);
v___x_2620_ = lean_mk_empty_byte_array(v___x_2619_);
lean_dec(v___x_2619_);
v___x_2621_ = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(v_proof_2615_, v___x_2616_, v___x_2620_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary___boxed(lean_object* v_proof_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(v_proof_2622_);
lean_dec_ref(v_proof_2622_);
return v_res_2623_;
}
}
lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object* v_path_2624_, lean_object* v_proof_2625_, uint8_t v_binaryProofs_2626_){
_start:
{
if (v_binaryProofs_2626_ == 0)
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2628_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_proof_2625_);
v___x_2629_ = lean_string_to_utf8(v___x_2628_);
lean_dec_ref(v___x_2628_);
v___x_2630_ = l_IO_FS_writeBinFile(v_path_2624_, v___x_2629_);
lean_dec_ref(v___x_2629_);
return v___x_2630_;
}
else
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(v_proof_2625_);
v___x_2632_ = l_IO_FS_writeBinFile(v_path_2624_, v___x_2631_);
lean_dec_ref(v___x_2631_);
return v___x_2632_;
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_dumpLRATProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_path_2624_ = stack[0].m_obj;
lean_object* v_proof_2625_ = stack[1].m_obj;
uint8_t v_binaryProofs_2626_ = stack[2].m_num;
lean_object* v_res_2633_;
v_res_2633_ = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(v_path_2624_, v_proof_2625_, v_binaryProofs_2626_);
stack->m_obj
 = v_res_2633_;
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
