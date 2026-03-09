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
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0;
extern lean_object* l_Int_instInhabited;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___boxed(lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__0_value;
lean_object* lean_string_to_utf8(lean_object*);
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1;
uint8_t lean_uint32_to_uint8(uint32_t);
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expected: '"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3_value;
lean_object* lean_uint8_to_nat(uint8_t);
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4;
lean_object* l_Nat_reprFast(lean_object*);
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7_value;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint32_t lean_uint8_to_uint32(uint8_t);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(lean_object*, lean_object*);
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
lean_object* lean_int_neg(lean_object*);
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
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_spec__0(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_array_get_size(lean_object*);
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
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__0;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero(lean_object*);
static const lean_string_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Invalid zero byte in literal"};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__0 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__0_value;
static const lean_ctor_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__0_value)}};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1_value;
static const lean_string_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Excessive literal"};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2_value;
static const lean_ctor_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2_value)}};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3_value;
uint8_t lean_uint8_complement(uint8_t);
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4;
lean_object* lean_uint64_to_nat(uint64_t);
uint8_t lean_uint8_land(uint8_t, uint8_t);
uint64_t lean_uint8_to_uint64(uint8_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint64_t lean_uint64_add(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(uint64_t, uint64_t, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_land(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
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
lean_object* l_IO_FS_readBinFile(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_parseLRATProof(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0_value;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0_value;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
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
lean_object* lean_byte_array_push(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startDelete(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(lean_object*, uint64_t);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_uint64_to_uint8(uint64_t);
uint8_t lean_uint8_lor(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode___boxed(lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(lean_object*);
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0;
static const lean_string_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.Tactic.BVDecide.LRAT.Parser"};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1_value;
static const lean_string_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "_private.Std.Tactic.BVDecide.LRAT.Parser.0.Std.Tactic.BVDecide.LRAT.lratProofToBinary.addInt"};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2_value;
static const lean_string_object l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 91, .m_data = "assertion violation: mapped ≤ (2^64 - 1) -- our parser \"only\" supports 64 bit literals\n    "};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4;
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_byte_array(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary___boxed(lean_object*);
lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l_Int_instInhabited;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_borrowed(x_2, x_1, x_3);
x_5 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
x_6 = lean_int_dec_lt(x_5, x_4);
x_7 = lean_nat_abs(x_4);
x_8 = lean_box(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__0));
x_2 = lean_string_to_utf8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 10;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4(void) {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2);
x_2 = lean_uint8_to_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4);
x_2 = l_Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5);
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7));
x_2 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_21; uint8_t x_22; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_21 = lean_byte_array_size(x_2);
x_22 = lean_nat_dec_lt(x_3, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
lean_inc_ref(x_1);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_3);
x_4 = x_24;
x_5 = x_1;
x_6 = x_3;
goto block_20;
}
else
{
uint8_t x_25; uint8_t x_26; uint8_t x_27; 
x_25 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2);
x_26 = lean_byte_array_fget(x_2, x_3);
x_27 = lean_uint8_dec_eq(x_26, x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9);
lean_inc_ref(x_1);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_3);
x_4 = x_29;
x_5 = x_1;
x_6 = x_3;
goto block_20;
}
else
{
lean_object* x_30; uint8_t x_31; uint8_t x_40; 
lean_inc_ref(x_2);
x_40 = !lean_is_exclusive(x_1);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_1, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_1, 0);
lean_dec(x_42);
x_30 = x_1;
x_31 = x_40;
goto block_39;
}
else
{
lean_dec(x_1);
x_30 = lean_box(0);
x_31 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_3, x_32);
lean_dec(x_3);
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_33);
x_34 = x_30;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_33);
x_34 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
block_20:
{
uint8_t x_7; 
x_7 = lean_nat_dec_eq(x_3, x_6);
lean_dec(x_6);
lean_dec(x_3);
if (x_7 == 0)
{
lean_dec_ref(x_5);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_4);
x_8 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1);
x_9 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_18; 
x_10 = lean_ctor_get(x_9, 0);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_9, 1);
lean_dec(x_19);
x_11 = x_9;
x_12 = x_18;
goto block_17;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_13);
x_14 = x_11;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
return x_9;
}
}
}
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 48;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 57;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_byte_array_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_byte_array_fget(x_5, x_6);
x_12 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
x_13 = lean_uint8_dec_le(x_12, x_11);
if (x_13 == 0)
{
goto block_4;
}
else
{
uint8_t x_14; uint8_t x_15; 
x_14 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
x_15 = lean_uint8_dec_le(x_11, x_14);
if (x_15 == 0)
{
goto block_4;
}
else
{
lean_object* x_16; uint8_t x_17; uint8_t x_44; 
lean_inc(x_6);
lean_inc_ref(x_5);
x_44 = !lean_is_exclusive(x_1);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_1, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_1, 0);
lean_dec(x_46);
x_16 = x_1;
x_17 = x_44;
goto block_43;
}
else
{
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_19);
x_20 = x_16;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_5);
lean_ctor_set(x_42, 1, x_19);
x_20 = x_42;
goto block_41;
}
block_41:
{
uint32_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_40; 
x_21 = lean_uint8_to_uint32(x_11);
x_22 = lean_uint32_to_uint8(x_21);
x_23 = lean_uint8_sub(x_22, x_12);
x_24 = lean_uint8_to_nat(x_23);
x_25 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_20, x_24);
x_26 = lean_ctor_get(x_25, 0);
x_27 = lean_ctor_get(x_25, 1);
x_40 = !lean_is_exclusive(x_25);
if (x_40 == 0)
{
x_28 = x_25;
x_29 = x_40;
goto block_39;
}
else
{
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_eq(x_26, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
if (x_29 == 0)
{
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 0, x_27);
x_32 = x_28;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_26);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_26);
x_35 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 1, x_35);
lean_ctor_set(x_28, 0, x_27);
x_36 = x_28;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
}
}
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 45;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1(void) {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0);
x_2 = lean_uint8_to_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1);
x_2 = l_Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2);
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7));
x_2 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0);
x_9 = lean_byte_array_fget(x_2, x_3);
x_10 = lean_uint8_dec_eq(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_56; 
lean_inc(x_3);
lean_inc_ref(x_2);
x_56 = !lean_is_exclusive(x_1);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_1, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_1, 0);
lean_dec(x_58);
x_13 = x_1;
x_14 = x_56;
goto block_55;
}
else
{
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
lean_inc(x_16);
lean_inc_ref(x_2);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_16);
x_17 = x_13;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_2);
lean_ctor_set(x_54, 1, x_16);
x_17 = x_54;
goto block_53;
}
block_53:
{
uint8_t x_21; 
x_21 = lean_nat_dec_lt(x_16, x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
lean_dec_ref(x_2);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
else
{
uint8_t x_24; uint8_t x_25; uint8_t x_26; 
x_24 = lean_byte_array_fget(x_2, x_16);
x_25 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
x_26 = lean_uint8_dec_le(x_25, x_24);
if (x_26 == 0)
{
lean_dec(x_16);
lean_dec_ref(x_2);
goto block_20;
}
else
{
uint8_t x_27; uint8_t x_28; 
x_27 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
x_28 = lean_uint8_dec_le(x_24, x_27);
if (x_28 == 0)
{
lean_dec(x_16);
lean_dec_ref(x_2);
goto block_20;
}
else
{
lean_object* x_29; lean_object* x_30; uint32_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_52; 
lean_dec_ref(x_17);
x_29 = lean_nat_add(x_16, x_15);
lean_dec(x_16);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_uint8_to_uint32(x_24);
x_32 = lean_uint32_to_uint8(x_31);
x_33 = lean_uint8_sub(x_32, x_25);
x_34 = lean_uint8_to_nat(x_33);
x_35 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_30, x_34);
x_36 = lean_ctor_get(x_35, 0);
x_37 = lean_ctor_get(x_35, 1);
x_52 = !lean_is_exclusive(x_35);
if (x_52 == 0)
{
x_38 = x_35;
x_39 = x_52;
goto block_51;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_35);
x_38 = lean_box(0);
x_39 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_eq(x_36, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_nat_to_int(x_36);
x_43 = lean_int_neg(x_42);
lean_dec(x_42);
if (x_39 == 0)
{
lean_ctor_set(x_38, 1, x_43);
lean_ctor_set(x_38, 0, x_37);
x_44 = x_38;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_36);
x_47 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
if (x_39 == 0)
{
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_47);
lean_ctor_set(x_38, 0, x_37);
x_48 = x_38;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_37);
lean_ctor_set(x_50, 1, x_47);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseId(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_byte_array_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_byte_array_fget(x_5, x_6);
x_12 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
x_13 = lean_uint8_dec_le(x_12, x_11);
if (x_13 == 0)
{
goto block_4;
}
else
{
uint8_t x_14; uint8_t x_15; 
x_14 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
x_15 = lean_uint8_dec_le(x_11, x_14);
if (x_15 == 0)
{
goto block_4;
}
else
{
lean_object* x_16; uint8_t x_17; uint8_t x_44; 
lean_inc(x_6);
lean_inc_ref(x_5);
x_44 = !lean_is_exclusive(x_1);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_1, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_1, 0);
lean_dec(x_46);
x_16 = x_1;
x_17 = x_44;
goto block_43;
}
else
{
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_19);
x_20 = x_16;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_5);
lean_ctor_set(x_42, 1, x_19);
x_20 = x_42;
goto block_41;
}
block_41:
{
uint32_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_40; 
x_21 = lean_uint8_to_uint32(x_11);
x_22 = lean_uint32_to_uint8(x_21);
x_23 = lean_uint8_sub(x_22, x_12);
x_24 = lean_uint8_to_nat(x_23);
x_25 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_20, x_24);
x_26 = lean_ctor_get(x_25, 0);
x_27 = lean_ctor_get(x_25, 1);
x_40 = !lean_is_exclusive(x_25);
if (x_40 == 0)
{
x_28 = x_25;
x_29 = x_40;
goto block_39;
}
else
{
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_eq(x_26, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
if (x_29 == 0)
{
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 0, x_27);
x_32 = x_28;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_26);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_26);
x_35 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 1, x_35);
lean_ctor_set(x_28, 0, x_27);
x_36 = x_28;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
}
}
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0(void) {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
x_2 = lean_uint8_to_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__0);
x_2 = l_Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1);
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7));
x_2 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
x_9 = lean_byte_array_fget(x_2, x_3);
x_10 = lean_uint8_dec_eq(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_23; 
lean_inc(x_3);
lean_inc_ref(x_2);
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_1, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_1, 0);
lean_dec(x_25);
x_13 = x_1;
x_14 = x_23;
goto block_22;
}
else
{
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_16);
x_17 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_16);
x_17 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
}
static uint8_t _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 32;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1(void) {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
x_2 = lean_uint8_to_nat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1);
x_2 = l_Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2);
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7));
x_2 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_byte_array_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_byte_array_fget(x_5, x_6);
x_12 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
x_13 = lean_uint8_dec_le(x_12, x_11);
if (x_13 == 0)
{
goto block_4;
}
else
{
uint8_t x_14; uint8_t x_15; 
x_14 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
x_15 = lean_uint8_dec_le(x_11, x_14);
if (x_15 == 0)
{
goto block_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_63; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_6, x_16);
lean_inc_ref(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_uint8_to_uint32(x_11);
x_20 = lean_uint32_to_uint8(x_19);
x_21 = lean_uint8_sub(x_20, x_12);
x_22 = lean_uint8_to_nat(x_21);
x_23 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_18, x_22);
x_24 = lean_ctor_get(x_23, 0);
x_25 = lean_ctor_get(x_23, 1);
x_63 = !lean_is_exclusive(x_23);
if (x_63 == 0)
{
x_26 = x_23;
x_27 = x_63;
goto block_62;
}
else
{
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_eq(x_24, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec_ref(x_1);
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
x_32 = lean_byte_array_size(x_30);
x_33 = lean_nat_dec_lt(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_24);
x_34 = lean_box(0);
if (x_27 == 0)
{
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 1, x_34);
lean_ctor_set(x_26, 0, x_25);
x_35 = x_26;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
else
{
uint8_t x_38; uint8_t x_39; uint8_t x_40; 
x_38 = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
x_39 = lean_byte_array_fget(x_30, x_31);
x_40 = lean_uint8_dec_eq(x_39, x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_24);
x_41 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
if (x_27 == 0)
{
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 1, x_41);
lean_ctor_set(x_26, 0, x_25);
x_42 = x_26;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_25);
lean_ctor_set(x_44, 1, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
else
{
lean_object* x_45; uint8_t x_46; uint8_t x_55; 
lean_inc(x_31);
lean_inc_ref(x_30);
x_55 = !lean_is_exclusive(x_25);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_25, 1);
lean_dec(x_56);
x_57 = lean_ctor_get(x_25, 0);
lean_dec(x_57);
x_45 = x_25;
x_46 = x_55;
goto block_54;
}
else
{
lean_dec(x_25);
x_45 = lean_box(0);
x_46 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_nat_add(x_31, x_16);
lean_dec(x_31);
if (x_46 == 0)
{
lean_ctor_set(x_45, 1, x_47);
x_48 = x_45;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_30);
lean_ctor_set(x_53, 1, x_47);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 0, x_48);
x_49 = x_26;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_24);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_25);
lean_dec(x_24);
x_58 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
if (x_27 == 0)
{
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 1, x_58);
lean_ctor_set(x_26, 0, x_1);
x_59 = x_26;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_58);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
}
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_14; uint8_t x_15; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_14 = lean_byte_array_size(x_3);
x_15 = lean_nat_dec_lt(x_4, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_box(0);
lean_inc(x_4);
x_5 = x_2;
x_6 = x_4;
x_7 = x_16;
goto block_11;
}
else
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; 
x_17 = lean_byte_array_fget(x_3, x_4);
x_18 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
x_19 = lean_uint8_dec_le(x_18, x_17);
if (x_19 == 0)
{
goto block_13;
}
else
{
uint8_t x_20; uint8_t x_21; 
x_20 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
x_21 = lean_uint8_dec_le(x_17, x_20);
if (x_21 == 0)
{
goto block_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint32_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_4, x_22);
lean_inc_ref(x_3);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_uint8_to_uint32(x_17);
x_26 = lean_uint32_to_uint8(x_25);
x_27 = lean_uint8_sub(x_26, x_18);
x_28 = lean_uint8_to_nat(x_27);
x_29 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_24, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_eq(x_30, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec_ref(x_2);
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
x_36 = lean_byte_array_size(x_34);
x_37 = lean_nat_dec_lt(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_30);
x_38 = lean_box(0);
x_5 = x_31;
x_6 = x_35;
x_7 = x_38;
goto block_11;
}
else
{
uint8_t x_39; uint8_t x_40; uint8_t x_41; 
x_39 = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
x_40 = lean_byte_array_fget(x_34, x_35);
x_41 = lean_uint8_dec_eq(x_40, x_39);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_30);
x_42 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
x_5 = x_31;
x_6 = x_35;
x_7 = x_42;
goto block_11;
}
else
{
lean_object* x_43; uint8_t x_44; uint8_t x_52; 
lean_inc_ref(x_34);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_31);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_31, 1);
lean_dec(x_53);
x_54 = lean_ctor_get(x_31, 0);
lean_dec(x_54);
x_43 = x_31;
x_44 = x_52;
goto block_51;
}
else
{
lean_dec(x_31);
x_43 = lean_box(0);
x_44 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_nat_add(x_35, x_22);
lean_dec(x_35);
if (x_44 == 0)
{
lean_ctor_set(x_43, 1, x_45);
x_46 = x_43;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_34);
lean_ctor_set(x_50, 1, x_45);
x_46 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_47; 
x_47 = lean_array_push(x_1, x_30);
x_1 = x_47;
x_2 = x_46;
goto _start;
}
}
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_31);
lean_dec(x_30);
x_55 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
lean_inc(x_4);
x_5 = x_2;
x_6 = x_4;
x_7 = x_55;
goto block_11;
}
}
}
}
block_11:
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_1);
return x_10;
}
}
block_13:
{
lean_object* x_12; 
x_12 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
lean_inc(x_4);
x_5 = x_2;
x_6 = x_4;
x_7 = x_12;
goto block_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0));
x_3 = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_spec__0(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 100;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1(void) {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
x_2 = lean_uint8_to_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1);
x_2 = l_Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2);
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7));
x_2 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
x_9 = lean_byte_array_fget(x_2, x_3);
x_10 = lean_uint8_dec_eq(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_76; 
lean_inc(x_3);
lean_inc_ref(x_2);
x_76 = !lean_is_exclusive(x_1);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_1, 1);
lean_dec(x_77);
x_78 = lean_ctor_get(x_1, 0);
lean_dec(x_78);
x_13 = x_1;
x_14 = x_76;
goto block_75;
}
else
{
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
lean_inc(x_16);
lean_inc_ref(x_2);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_16);
x_17 = x_13;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_2);
lean_ctor_set(x_74, 1, x_16);
x_17 = x_74;
goto block_73;
}
block_73:
{
uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_16, x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec_ref(x_2);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; 
x_21 = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
x_22 = lean_byte_array_fget(x_2, x_16);
x_23 = lean_uint8_dec_eq(x_22, x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
lean_dec_ref(x_2);
x_24 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_17);
x_26 = lean_nat_add(x_16, x_15);
lean_dec(x_16);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_63; 
x_29 = lean_ctor_get(x_28, 0);
x_30 = lean_ctor_get(x_28, 1);
x_63 = !lean_is_exclusive(x_28);
if (x_63 == 0)
{
x_31 = x_28;
x_32 = x_63;
goto block_62;
}
else
{
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_28);
x_31 = lean_box(0);
x_32 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
x_35 = lean_byte_array_size(x_33);
x_36 = lean_nat_dec_lt(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_30);
x_37 = lean_box(0);
if (x_32 == 0)
{
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_37);
x_38 = x_31;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
else
{
uint8_t x_41; uint8_t x_42; uint8_t x_43; 
x_41 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
x_42 = lean_byte_array_fget(x_33, x_34);
x_43 = lean_uint8_dec_eq(x_42, x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_30);
x_44 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4);
if (x_32 == 0)
{
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_44);
x_45 = x_31;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_29);
lean_ctor_set(x_47, 1, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
else
{
lean_object* x_48; uint8_t x_49; uint8_t x_59; 
lean_inc(x_34);
lean_inc_ref(x_33);
x_59 = !lean_is_exclusive(x_29);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_29, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_29, 0);
lean_dec(x_61);
x_48 = x_29;
x_49 = x_59;
goto block_58;
}
else
{
lean_dec(x_29);
x_48 = lean_box(0);
x_49 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_nat_add(x_34, x_15);
lean_dec(x_34);
if (x_49 == 0)
{
lean_ctor_set(x_48, 1, x_50);
x_51 = x_48;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_33);
lean_ctor_set(x_57, 1, x_50);
x_51 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_30);
if (x_32 == 0)
{
lean_ctor_set(x_31, 1, x_52);
lean_ctor_set(x_31, 0, x_51);
x_53 = x_31;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_52);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
x_64 = lean_ctor_get(x_28, 0);
x_65 = lean_ctor_get(x_28, 1);
x_72 = !lean_is_exclusive(x_28);
if (x_72 == 0)
{
x_66 = x_28;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_28);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseLit(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_byte_array_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_byte_array_fget(x_5, x_6);
x_12 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0);
x_13 = lean_uint8_dec_eq(x_11, x_12);
if (x_13 == 0)
{
if (x_8 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
uint8_t x_16; uint8_t x_17; 
x_16 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
x_17 = lean_uint8_dec_le(x_16, x_11);
if (x_17 == 0)
{
goto block_4;
}
else
{
uint8_t x_18; uint8_t x_19; 
x_18 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
x_19 = lean_uint8_dec_le(x_11, x_18);
if (x_19 == 0)
{
goto block_4;
}
else
{
lean_object* x_20; uint8_t x_21; uint8_t x_49; 
lean_inc(x_6);
lean_inc_ref(x_5);
x_49 = !lean_is_exclusive(x_1);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_1, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
x_20 = x_1;
x_21 = x_49;
goto block_48;
}
else
{
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_6, x_22);
lean_dec(x_6);
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_23);
x_24 = x_20;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_23);
x_24 = x_47;
goto block_46;
}
block_46:
{
uint32_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_45; 
x_25 = lean_uint8_to_uint32(x_11);
x_26 = lean_uint32_to_uint8(x_25);
x_27 = lean_uint8_sub(x_26, x_16);
x_28 = lean_uint8_to_nat(x_27);
x_29 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_24, x_28);
x_30 = lean_ctor_get(x_29, 0);
x_31 = lean_ctor_get(x_29, 1);
x_45 = !lean_is_exclusive(x_29);
if (x_45 == 0)
{
x_32 = x_29;
x_33 = x_45;
goto block_44;
}
else
{
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_29);
x_32 = lean_box(0);
x_33 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_eq(x_30, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_nat_to_int(x_30);
if (x_33 == 0)
{
lean_ctor_set(x_32, 1, x_36);
lean_ctor_set(x_32, 0, x_31);
x_37 = x_32;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_30);
x_40 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
if (x_33 == 0)
{
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_40);
lean_ctor_set(x_32, 0, x_31);
x_41 = x_32;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_31);
lean_ctor_set(x_43, 1, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
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
if (x_8 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
else
{
if (x_13 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
else
{
lean_object* x_56; uint8_t x_57; uint8_t x_99; 
lean_inc(x_6);
lean_inc_ref(x_5);
x_99 = !lean_is_exclusive(x_1);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_1, 1);
lean_dec(x_100);
x_101 = lean_ctor_get(x_1, 0);
lean_dec(x_101);
x_56 = x_1;
x_57 = x_99;
goto block_98;
}
else
{
lean_dec(x_1);
x_56 = lean_box(0);
x_57 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_6, x_58);
lean_dec(x_6);
lean_inc(x_59);
lean_inc_ref(x_5);
if (x_57 == 0)
{
lean_ctor_set(x_56, 1, x_59);
x_60 = x_56;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_5);
lean_ctor_set(x_97, 1, x_59);
x_60 = x_97;
goto block_96;
}
block_96:
{
uint8_t x_64; 
x_64 = lean_nat_dec_lt(x_59, x_7);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_59);
lean_dec_ref(x_5);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
else
{
uint8_t x_67; uint8_t x_68; uint8_t x_69; 
x_67 = lean_byte_array_fget(x_5, x_59);
x_68 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
x_69 = lean_uint8_dec_le(x_68, x_67);
if (x_69 == 0)
{
lean_dec(x_59);
lean_dec_ref(x_5);
goto block_63;
}
else
{
uint8_t x_70; uint8_t x_71; 
x_70 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
x_71 = lean_uint8_dec_le(x_67, x_70);
if (x_71 == 0)
{
lean_dec(x_59);
lean_dec_ref(x_5);
goto block_63;
}
else
{
lean_object* x_72; lean_object* x_73; uint32_t x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_95; 
lean_dec_ref(x_60);
x_72 = lean_nat_add(x_59, x_58);
lean_dec(x_59);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_5);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_uint8_to_uint32(x_67);
x_75 = lean_uint32_to_uint8(x_74);
x_76 = lean_uint8_sub(x_75, x_68);
x_77 = lean_uint8_to_nat(x_76);
x_78 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_73, x_77);
x_79 = lean_ctor_get(x_78, 0);
x_80 = lean_ctor_get(x_78, 1);
x_95 = !lean_is_exclusive(x_78);
if (x_95 == 0)
{
x_81 = x_78;
x_82 = x_95;
goto block_94;
}
else
{
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_78);
x_81 = lean_box(0);
x_82 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_nat_dec_eq(x_79, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_nat_to_int(x_79);
x_86 = lean_int_neg(x_85);
lean_dec(x_85);
if (x_82 == 0)
{
lean_ctor_set(x_81, 1, x_86);
lean_ctor_set(x_81, 0, x_80);
x_87 = x_81;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_80);
lean_ctor_set(x_89, 1, x_86);
x_87 = x_89;
goto block_88;
}
block_88:
{
return x_87;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_79);
x_90 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
if (x_82 == 0)
{
lean_ctor_set_tag(x_81, 1);
lean_ctor_set(x_81, 1, x_90);
lean_ctor_set(x_81, 0, x_80);
x_91 = x_81;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_80);
lean_ctor_set(x_93, 1, x_90);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
}
}
}
}
}
}
block_63:
{
lean_object* x_61; lean_object* x_62; 
x_61 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
}
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_litWs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_byte_array_size(x_34);
x_37 = lean_nat_dec_lt(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
uint8_t x_40; uint8_t x_41; uint8_t x_42; 
x_40 = lean_byte_array_fget(x_34, x_35);
x_41 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0);
x_42 = lean_uint8_dec_eq(x_40, x_41);
if (x_42 == 0)
{
if (x_37 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
uint8_t x_45; uint8_t x_46; 
x_45 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
x_46 = lean_uint8_dec_le(x_45, x_40);
if (x_46 == 0)
{
goto block_30;
}
else
{
uint8_t x_47; uint8_t x_48; 
x_47 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
x_48 = lean_uint8_dec_le(x_40, x_47);
if (x_48 == 0)
{
goto block_30;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint32_t x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_69; 
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_35, x_49);
lean_inc_ref(x_34);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_34);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_uint8_to_uint32(x_40);
x_53 = lean_uint32_to_uint8(x_52);
x_54 = lean_uint8_sub(x_53, x_45);
x_55 = lean_uint8_to_nat(x_54);
x_56 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_51, x_55);
x_57 = lean_ctor_get(x_56, 0);
x_58 = lean_ctor_get(x_56, 1);
x_69 = !lean_is_exclusive(x_56);
if (x_69 == 0)
{
x_59 = x_56;
x_60 = x_69;
goto block_68;
}
else
{
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_56);
x_59 = lean_box(0);
x_60 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_nat_dec_eq(x_57, x_61);
if (x_62 == 0)
{
lean_object* x_63; 
lean_del_object(x_59);
lean_dec_ref(x_1);
x_63 = lean_nat_to_int(x_57);
x_2 = x_58;
x_3 = x_63;
goto block_27;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_58);
lean_dec(x_57);
x_64 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
if (x_60 == 0)
{
lean_ctor_set_tag(x_59, 1);
lean_ctor_set(x_59, 1, x_64);
lean_ctor_set(x_59, 0, x_1);
x_65 = x_59;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_64);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
}
}
}
else
{
if (x_37 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
else
{
if (x_42 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_add(x_35, x_74);
x_76 = lean_nat_dec_lt(x_75, x_36);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_75);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
else
{
uint8_t x_79; uint8_t x_80; uint8_t x_81; 
x_79 = lean_byte_array_fget(x_34, x_75);
x_80 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
x_81 = lean_uint8_dec_le(x_80, x_79);
if (x_81 == 0)
{
lean_dec(x_75);
goto block_33;
}
else
{
uint8_t x_82; uint8_t x_83; 
x_82 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
x_83 = lean_uint8_dec_le(x_79, x_82);
if (x_83 == 0)
{
lean_dec(x_75);
goto block_33;
}
else
{
lean_object* x_84; lean_object* x_85; uint32_t x_86; uint8_t x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_104; 
x_84 = lean_nat_add(x_75, x_74);
lean_dec(x_75);
lean_inc_ref(x_34);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_34);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_uint8_to_uint32(x_79);
x_87 = lean_uint32_to_uint8(x_86);
x_88 = lean_uint8_sub(x_87, x_80);
x_89 = lean_uint8_to_nat(x_88);
x_90 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_85, x_89);
x_91 = lean_ctor_get(x_90, 0);
x_92 = lean_ctor_get(x_90, 1);
x_104 = !lean_is_exclusive(x_90);
if (x_104 == 0)
{
x_93 = x_90;
x_94 = x_104;
goto block_103;
}
else
{
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_90);
x_93 = lean_box(0);
x_94 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_unsigned_to_nat(0u);
x_96 = lean_nat_dec_eq(x_91, x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_del_object(x_93);
lean_dec_ref(x_1);
x_97 = lean_nat_to_int(x_91);
x_98 = lean_int_neg(x_97);
lean_dec(x_97);
x_2 = x_92;
x_3 = x_98;
goto block_27;
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_92);
lean_dec(x_91);
x_99 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
if (x_94 == 0)
{
lean_ctor_set_tag(x_93, 1);
lean_ctor_set(x_93, 1, x_99);
lean_ctor_set(x_93, 0, x_1);
x_100 = x_93;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_1);
lean_ctor_set(x_102, 1, x_99);
x_100 = x_102;
goto block_101;
}
block_101:
{
return x_100;
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
block_27:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_byte_array_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_10 = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
x_11 = lean_byte_array_fget(x_4, x_5);
x_12 = lean_uint8_dec_eq(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; uint8_t x_24; 
lean_inc(x_5);
lean_inc_ref(x_4);
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_2, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_2, 0);
lean_dec(x_26);
x_15 = x_2;
x_16 = x_24;
goto block_23;
}
else
{
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_18);
x_19 = x_15;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_18);
x_19 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
}
}
}
block_30:
{
lean_object* x_28; lean_object* x_29; 
x_28 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
block_33:
{
lean_object* x_31; lean_object* x_32; 
x_31 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_16; lean_object* x_17; lean_object* x_41; uint8_t x_42; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_41 = lean_byte_array_size(x_3);
x_42 = lean_nat_dec_lt(x_4, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_box(0);
lean_inc(x_4);
x_5 = x_2;
x_6 = x_4;
x_7 = x_43;
goto block_11;
}
else
{
uint8_t x_44; uint8_t x_45; uint8_t x_46; 
x_44 = lean_byte_array_fget(x_3, x_4);
x_45 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0);
x_46 = lean_uint8_dec_eq(x_44, x_45);
if (x_46 == 0)
{
if (x_42 == 0)
{
lean_object* x_47; 
x_47 = lean_box(0);
lean_inc(x_4);
x_5 = x_2;
x_6 = x_4;
x_7 = x_47;
goto block_11;
}
else
{
uint8_t x_48; uint8_t x_49; 
x_48 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
x_49 = lean_uint8_dec_le(x_48, x_44);
if (x_49 == 0)
{
goto block_15;
}
else
{
uint8_t x_50; uint8_t x_51; 
x_50 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
x_51 = lean_uint8_dec_le(x_44, x_50);
if (x_51 == 0)
{
goto block_15;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint32_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_4, x_52);
lean_inc_ref(x_3);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_3);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_uint8_to_uint32(x_44);
x_56 = lean_uint32_to_uint8(x_55);
x_57 = lean_uint8_sub(x_56, x_48);
x_58 = lean_uint8_to_nat(x_57);
x_59 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_54, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec_ref(x_59);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_eq(x_60, x_62);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec_ref(x_2);
x_64 = lean_nat_to_int(x_60);
x_16 = x_61;
x_17 = x_64;
goto block_40;
}
else
{
lean_object* x_65; 
lean_dec(x_61);
lean_dec(x_60);
x_65 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
lean_inc(x_4);
x_5 = x_2;
x_6 = x_4;
x_7 = x_65;
goto block_11;
}
}
}
}
}
else
{
if (x_42 == 0)
{
lean_object* x_66; 
x_66 = lean_box(0);
lean_inc(x_4);
x_5 = x_2;
x_6 = x_4;
x_7 = x_66;
goto block_11;
}
else
{
if (x_46 == 0)
{
lean_object* x_67; 
x_67 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
lean_inc(x_4);
x_5 = x_2;
x_6 = x_4;
x_7 = x_67;
goto block_11;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_add(x_4, x_68);
x_70 = lean_nat_dec_lt(x_69, x_41);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_69);
x_71 = lean_box(0);
lean_inc(x_4);
x_5 = x_2;
x_6 = x_4;
x_7 = x_71;
goto block_11;
}
else
{
uint8_t x_72; uint8_t x_73; uint8_t x_74; 
x_72 = lean_byte_array_fget(x_3, x_69);
x_73 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
x_74 = lean_uint8_dec_le(x_73, x_72);
if (x_74 == 0)
{
lean_dec(x_69);
goto block_13;
}
else
{
uint8_t x_75; uint8_t x_76; 
x_75 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
x_76 = lean_uint8_dec_le(x_72, x_75);
if (x_76 == 0)
{
lean_dec(x_69);
goto block_13;
}
else
{
lean_object* x_77; lean_object* x_78; uint32_t x_79; uint8_t x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_77 = lean_nat_add(x_69, x_68);
lean_dec(x_69);
lean_inc_ref(x_3);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_3);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_uint8_to_uint32(x_72);
x_80 = lean_uint32_to_uint8(x_79);
x_81 = lean_uint8_sub(x_80, x_73);
x_82 = lean_uint8_to_nat(x_81);
x_83 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_78, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec_ref(x_83);
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_nat_dec_eq(x_84, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_2);
x_88 = lean_nat_to_int(x_84);
x_89 = lean_int_neg(x_88);
lean_dec(x_88);
x_16 = x_85;
x_17 = x_89;
goto block_40;
}
else
{
lean_object* x_90; 
lean_dec(x_85);
lean_dec(x_84);
x_90 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
lean_inc(x_4);
x_5 = x_2;
x_6 = x_4;
x_7 = x_90;
goto block_11;
}
}
}
}
}
}
}
}
block_11:
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_1);
return x_10;
}
}
block_13:
{
lean_object* x_12; 
x_12 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
lean_inc(x_4);
x_5 = x_2;
x_6 = x_4;
x_7 = x_12;
goto block_11;
}
block_15:
{
lean_object* x_14; 
x_14 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
lean_inc(x_4);
x_5 = x_2;
x_6 = x_4;
x_7 = x_14;
goto block_11;
}
block_40:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_byte_array_size(x_18);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_17);
x_22 = lean_box(0);
x_5 = x_16;
x_6 = x_19;
x_7 = x_22;
goto block_11;
}
else
{
uint8_t x_23; uint8_t x_24; uint8_t x_25; 
x_23 = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
x_24 = lean_byte_array_fget(x_18, x_19);
x_25 = lean_uint8_dec_eq(x_24, x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_17);
x_26 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
x_5 = x_16;
x_6 = x_19;
x_7 = x_26;
goto block_11;
}
else
{
lean_object* x_27; uint8_t x_28; uint8_t x_37; 
lean_inc_ref(x_18);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_16, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_16, 0);
lean_dec(x_39);
x_27 = x_16;
x_28 = x_37;
goto block_36;
}
else
{
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_19, x_29);
lean_dec(x_19);
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_30);
x_31 = x_27;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_18);
lean_ctor_set(x_35, 1, x_30);
x_31 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_32; 
x_32 = lean_array_push(x_1, x_17);
x_1 = x_32;
x_2 = x_31;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0));
x_3 = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__1(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_38; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_38 = !lean_is_exclusive(x_3);
if (x_38 == 0)
{
x_6 = x_3;
x_7 = x_38;
goto block_37;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_byte_array_size(x_8);
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_box(0);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_12);
x_13 = x_6;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; 
x_16 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
x_17 = lean_byte_array_fget(x_8, x_9);
x_18 = lean_uint8_dec_eq(x_17, x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
x_19 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_19);
x_20 = x_6;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
lean_object* x_23; uint8_t x_24; uint8_t x_34; 
lean_inc(x_9);
lean_inc_ref(x_8);
x_34 = !lean_is_exclusive(x_4);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_4, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_4, 0);
lean_dec(x_36);
x_23 = x_4;
x_24 = x_34;
goto block_33;
}
else
{
lean_dec(x_4);
x_23 = lean_box(0);
x_24 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_9, x_25);
lean_dec(x_9);
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_26);
x_27 = x_23;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_26);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_27);
x_28 = x_6;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_5);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__0);
x_9 = lean_byte_array_fget(x_2, x_3);
x_10 = lean_uint8_dec_eq(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_95; 
lean_inc(x_3);
lean_inc_ref(x_2);
x_95 = !lean_is_exclusive(x_1);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_1, 1);
lean_dec(x_96);
x_97 = lean_ctor_get(x_1, 0);
lean_dec(x_97);
x_13 = x_1;
x_14 = x_95;
goto block_94;
}
else
{
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
lean_inc(x_16);
lean_inc_ref(x_2);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_16);
x_17 = x_13;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_2);
lean_ctor_set(x_93, 1, x_16);
x_17 = x_93;
goto block_92;
}
block_92:
{
uint8_t x_21; 
x_21 = lean_nat_dec_lt(x_16, x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
lean_dec_ref(x_2);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
else
{
uint8_t x_24; uint8_t x_25; uint8_t x_26; 
x_24 = lean_byte_array_fget(x_2, x_16);
x_25 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
x_26 = lean_uint8_dec_le(x_25, x_24);
if (x_26 == 0)
{
lean_dec(x_16);
lean_dec_ref(x_2);
goto block_20;
}
else
{
uint8_t x_27; uint8_t x_28; 
x_27 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
x_28 = lean_uint8_dec_le(x_24, x_27);
if (x_28 == 0)
{
lean_dec(x_16);
lean_dec_ref(x_2);
goto block_20;
}
else
{
lean_object* x_29; lean_object* x_30; uint32_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_91; 
lean_dec_ref(x_17);
x_29 = lean_nat_add(x_16, x_15);
lean_dec(x_16);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_uint8_to_uint32(x_24);
x_32 = lean_uint32_to_uint8(x_31);
x_33 = lean_uint8_sub(x_32, x_25);
x_34 = lean_uint8_to_nat(x_33);
x_35 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_30, x_34);
x_36 = lean_ctor_get(x_35, 0);
x_37 = lean_ctor_get(x_35, 1);
x_91 = !lean_is_exclusive(x_35);
if (x_91 == 0)
{
x_38 = x_35;
x_39 = x_91;
goto block_90;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_35);
x_38 = lean_box(0);
x_39 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_eq(x_36, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
x_44 = lean_byte_array_size(x_42);
x_45 = lean_nat_dec_lt(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_del_object(x_38);
lean_dec(x_36);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_37);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
else
{
uint8_t x_48; uint8_t x_49; uint8_t x_50; 
x_48 = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
x_49 = lean_byte_array_fget(x_42, x_43);
x_50 = lean_uint8_dec_eq(x_49, x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_del_object(x_38);
lean_dec(x_36);
x_51 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_37);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
else
{
lean_object* x_53; uint8_t x_54; uint8_t x_85; 
lean_inc(x_43);
lean_inc_ref(x_42);
x_85 = !lean_is_exclusive(x_37);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_37, 1);
lean_dec(x_86);
x_87 = lean_ctor_get(x_37, 0);
lean_dec(x_87);
x_53 = x_37;
x_54 = x_85;
goto block_84;
}
else
{
lean_dec(x_37);
x_53 = lean_box(0);
x_54 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_nat_add(x_43, x_15);
lean_dec(x_43);
if (x_54 == 0)
{
lean_ctor_set(x_53, 1, x_55);
x_56 = x_53;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_42);
lean_ctor_set(x_83, 1, x_55);
x_56 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_57; 
x_57 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_72; 
x_58 = lean_ctor_get(x_57, 0);
x_59 = lean_ctor_get(x_57, 1);
x_72 = !lean_is_exclusive(x_57);
if (x_72 == 0)
{
x_60 = x_57;
x_61 = x_72;
goto block_71;
}
else
{
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_57);
x_60 = lean_box(0);
x_61 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_nat_to_int(x_36);
x_63 = lean_int_neg(x_62);
lean_dec(x_62);
x_64 = lean_nat_abs(x_63);
lean_dec(x_63);
if (x_39 == 0)
{
lean_ctor_set(x_38, 1, x_59);
lean_ctor_set(x_38, 0, x_64);
x_65 = x_38;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_59);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_61 == 0)
{
lean_ctor_set(x_60, 1, x_65);
x_66 = x_60;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_65);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_del_object(x_38);
lean_dec(x_36);
x_73 = lean_ctor_get(x_57, 0);
x_74 = lean_ctor_get(x_57, 1);
x_81 = !lean_is_exclusive(x_57);
if (x_81 == 0)
{
x_75 = x_57;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_57);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
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
lean_object* x_88; lean_object* x_89; 
lean_del_object(x_38);
lean_dec(x_36);
x_88 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_37);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_20; 
lean_inc_ref(x_2);
x_20 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(x_2);
if (lean_obj_tag(x_20) == 0)
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_2);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_array_push(x_1, x_22);
x_1 = x_23;
x_2 = x_21;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec_ref(x_20);
x_3 = x_25;
x_4 = x_26;
goto block_19;
}
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec_ref(x_20);
lean_inc_ref(x_2);
x_3 = x_2;
x_4 = x_27;
goto block_19;
}
block_19:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_17; 
x_5 = lean_ctor_get(x_2, 1);
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_2, 0);
lean_dec(x_18);
x_6 = x_2;
x_7 = x_17;
goto block_16;
}
else
{
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_nat_dec_eq(x_5, x_8);
lean_dec(x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec_ref(x_1);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 0, x_3);
x_10 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_4);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
else
{
lean_object* x_13; 
lean_dec(x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 0, x_3);
x_13 = x_6;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_1);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_113; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_113 = !lean_is_exclusive(x_3);
if (x_113 == 0)
{
x_6 = x_3;
x_7 = x_113;
goto block_112;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_byte_array_size(x_8);
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_box(0);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_12);
x_13 = x_6;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; 
x_16 = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
x_17 = lean_byte_array_fget(x_8, x_9);
x_18 = lean_uint8_dec_eq(x_17, x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_1);
x_19 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_19);
x_20 = x_6;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
lean_object* x_23; uint8_t x_24; uint8_t x_109; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_del_object(x_6);
x_109 = !lean_is_exclusive(x_4);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_4, 1);
lean_dec(x_110);
x_111 = lean_ctor_get(x_4, 0);
lean_dec(x_111);
x_23 = x_4;
x_24 = x_109;
goto block_108;
}
else
{
lean_dec(x_4);
x_23 = lean_box(0);
x_24 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_9, x_25);
lean_dec(x_9);
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_26);
x_27 = x_23;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_8);
lean_ctor_set(x_107, 1, x_26);
x_27 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_28; 
x_28 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_unsigned_to_nat(0u);
x_32 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0));
x_33 = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(x_32, x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_87; 
x_34 = lean_ctor_get(x_33, 0);
x_35 = lean_ctor_get(x_33, 1);
x_87 = !lean_is_exclusive(x_33);
if (x_87 == 0)
{
x_36 = x_33;
x_37 = x_87;
goto block_86;
}
else
{
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_33);
x_36 = lean_box(0);
x_37 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
x_40 = lean_byte_array_size(x_38);
x_41 = lean_nat_dec_lt(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_5);
lean_dec(x_1);
x_42 = lean_box(0);
if (x_37 == 0)
{
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 1, x_42);
x_43 = x_36;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_34);
lean_ctor_set(x_45, 1, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
else
{
uint8_t x_46; uint8_t x_47; uint8_t x_48; 
x_46 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
x_47 = lean_byte_array_fget(x_38, x_39);
x_48 = lean_uint8_dec_eq(x_47, x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_5);
lean_dec(x_1);
x_49 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4);
if (x_37 == 0)
{
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 1, x_49);
x_50 = x_36;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_34);
lean_ctor_set(x_52, 1, x_49);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
else
{
lean_object* x_53; uint8_t x_54; uint8_t x_83; 
lean_inc(x_39);
lean_inc_ref(x_38);
x_83 = !lean_is_exclusive(x_34);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_34, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_34, 0);
lean_dec(x_85);
x_53 = x_34;
x_54 = x_83;
goto block_82;
}
else
{
lean_dec(x_34);
x_53 = lean_box(0);
x_54 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_nat_add(x_39, x_25);
lean_dec(x_39);
if (x_54 == 0)
{
lean_ctor_set(x_53, 1, x_55);
x_56 = x_53;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_38);
lean_ctor_set(x_81, 1, x_55);
x_56 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_array_get_size(x_5);
x_58 = lean_nat_dec_eq(x_57, x_31);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_array_get_size(x_35);
x_60 = lean_nat_dec_eq(x_59, x_31);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_5);
x_62 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_5);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_30);
lean_ctor_set(x_62, 4, x_35);
if (x_37 == 0)
{
lean_ctor_set(x_36, 1, x_62);
lean_ctor_set(x_36, 0, x_56);
x_63 = x_36;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_56);
lean_ctor_set(x_65, 1, x_62);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_35);
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_5);
lean_ctor_set(x_66, 2, x_30);
if (x_37 == 0)
{
lean_ctor_set(x_36, 1, x_66);
lean_ctor_set(x_36, 0, x_56);
x_67 = x_36;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_56);
lean_ctor_set(x_69, 1, x_66);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
else
{
lean_object* x_70; uint8_t x_71; 
lean_dec(x_5);
x_70 = lean_array_get_size(x_35);
lean_dec(x_35);
x_71 = lean_nat_dec_eq(x_70, x_31);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_30);
lean_dec(x_1);
x_72 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2));
if (x_37 == 0)
{
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 1, x_72);
lean_ctor_set(x_36, 0, x_56);
x_73 = x_36;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_56);
lean_ctor_set(x_75, 1, x_72);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_30);
if (x_37 == 0)
{
lean_ctor_set(x_36, 1, x_76);
lean_ctor_set(x_36, 0, x_56);
x_77 = x_36;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_56);
lean_ctor_set(x_79, 1, x_76);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
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
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_96; 
lean_dec(x_30);
lean_dec(x_5);
lean_dec(x_1);
x_88 = lean_ctor_get(x_33, 0);
x_89 = lean_ctor_get(x_33, 1);
x_96 = !lean_is_exclusive(x_33);
if (x_96 == 0)
{
x_90 = x_33;
x_91 = x_96;
goto block_95;
}
else
{
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_33);
x_90 = lean_box(0);
x_91 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_92; 
if (x_91 == 0)
{
x_92 = x_90;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_89);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
lean_dec(x_5);
lean_dec(x_1);
x_97 = lean_ctor_get(x_28, 0);
x_98 = lean_ctor_get(x_28, 1);
x_105 = !lean_is_exclusive(x_28);
if (x_105 == 0)
{
x_99 = x_28;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_28);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
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
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_122; 
lean_dec(x_1);
x_114 = lean_ctor_get(x_3, 0);
x_115 = lean_ctor_get(x_3, 1);
x_122 = !lean_is_exclusive(x_3);
if (x_122 == 0)
{
x_116 = x_3;
x_117 = x_122;
goto block_121;
}
else
{
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_3);
x_116 = lean_box(0);
x_117 = x_122;
goto block_121;
}
block_121:
{
lean_object* x_118; 
if (x_117 == 0)
{
x_118 = x_116;
goto block_119;
}
else
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_114);
lean_ctor_set(x_120, 1, x_115);
x_118 = x_120;
goto block_119;
}
block_119:
{
return x_118;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_byte_array_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_byte_array_fget(x_5, x_6);
x_12 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__2);
x_13 = lean_uint8_dec_le(x_12, x_11);
if (x_13 == 0)
{
goto block_4;
}
else
{
uint8_t x_14; uint8_t x_15; 
x_14 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__3);
x_15 = lean_uint8_dec_le(x_11, x_14);
if (x_15 == 0)
{
goto block_4;
}
else
{
lean_object* x_16; uint8_t x_17; uint8_t x_76; 
lean_inc(x_6);
lean_inc_ref(x_5);
x_76 = !lean_is_exclusive(x_1);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_1, 1);
lean_dec(x_77);
x_78 = lean_ctor_get(x_1, 0);
lean_dec(x_78);
x_16 = x_1;
x_17 = x_76;
goto block_75;
}
else
{
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_19);
x_20 = x_16;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_5);
lean_ctor_set(x_74, 1, x_19);
x_20 = x_74;
goto block_73;
}
block_73:
{
uint32_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_72; 
x_21 = lean_uint8_to_uint32(x_11);
x_22 = lean_uint32_to_uint8(x_21);
x_23 = lean_uint8_sub(x_22, x_12);
x_24 = lean_uint8_to_nat(x_23);
x_25 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_20, x_24);
x_26 = lean_ctor_get(x_25, 0);
x_27 = lean_ctor_get(x_25, 1);
x_72 = !lean_is_exclusive(x_25);
if (x_72 == 0)
{
x_28 = x_25;
x_29 = x_72;
goto block_71;
}
else
{
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_eq(x_26, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
x_34 = lean_byte_array_size(x_32);
x_35 = lean_nat_dec_lt(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_26);
x_36 = lean_box(0);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 1, x_36);
lean_ctor_set(x_28, 0, x_27);
x_37 = x_28;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
else
{
uint8_t x_40; uint8_t x_41; uint8_t x_42; 
x_40 = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__0);
x_41 = lean_byte_array_fget(x_32, x_33);
x_42 = lean_uint8_dec_eq(x_41, x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_26);
x_43 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 1, x_43);
lean_ctor_set(x_28, 0, x_27);
x_44 = x_28;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_27);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
else
{
lean_object* x_47; uint8_t x_48; uint8_t x_64; 
lean_inc(x_33);
lean_inc_ref(x_32);
x_64 = !lean_is_exclusive(x_27);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_27, 1);
lean_dec(x_65);
x_66 = lean_ctor_get(x_27, 0);
lean_dec(x_66);
x_47 = x_27;
x_48 = x_64;
goto block_63;
}
else
{
lean_dec(x_27);
x_47 = lean_box(0);
x_48 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_nat_add(x_33, x_18);
lean_dec(x_33);
lean_inc(x_49);
lean_inc_ref(x_32);
if (x_48 == 0)
{
lean_ctor_set(x_47, 1, x_49);
x_50 = x_47;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_32);
lean_ctor_set(x_62, 1, x_49);
x_50 = x_62;
goto block_61;
}
block_61:
{
uint8_t x_51; 
x_51 = lean_nat_dec_lt(x_49, x_34);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_49);
lean_dec_ref(x_32);
lean_dec(x_26);
x_52 = lean_box(0);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 1, x_52);
lean_ctor_set(x_28, 0, x_50);
x_53 = x_28;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_52);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
else
{
uint8_t x_56; uint8_t x_57; uint8_t x_58; 
lean_del_object(x_28);
x_56 = lean_byte_array_fget(x_32, x_49);
lean_dec(x_49);
lean_dec_ref(x_32);
x_57 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
x_58 = lean_uint8_dec_eq(x_56, x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(x_26, x_50);
return x_59;
}
else
{
lean_object* x_60; 
lean_dec(x_26);
x_60 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(x_50);
return x_60;
}
}
}
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_26);
x_67 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__5));
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 1, x_67);
lean_ctor_set(x_28, 0, x_27);
x_68 = x_28;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_27);
lean_ctor_set(x_70, 1, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
}
}
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1));
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
static uint8_t _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 13;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 99;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_15; uint8_t x_16; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_15 = lean_byte_array_size(x_4);
x_16 = lean_nat_dec_lt(x_5, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_box(0);
lean_inc(x_5);
x_6 = x_3;
x_7 = x_5;
x_8 = x_17;
goto block_12;
}
else
{
uint8_t x_18; uint8_t x_19; uint8_t x_20; 
x_18 = lean_byte_array_fget(x_4, x_5);
x_19 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2);
x_20 = lean_uint8_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; uint8_t x_30; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_5, x_21);
lean_inc_ref(x_4);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_22);
x_29 = lean_uint8_once(&l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2, &l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2_once, _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__2);
x_30 = lean_uint8_dec_eq(x_18, x_29);
if (x_30 == 0)
{
uint8_t x_31; uint8_t x_32; 
x_31 = lean_uint8_once(&l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3, &l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3_once, _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3);
x_32 = lean_uint8_dec_eq(x_1, x_31);
x_24 = x_32;
goto block_28;
}
else
{
x_24 = x_20;
goto block_28;
}
block_28:
{
if (x_24 == 0)
{
lean_dec_ref(x_23);
goto block_14;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
lean_dec_ref(x_3);
x_25 = lean_box(x_18);
x_26 = lean_array_push(x_2, x_25);
x_2 = x_26;
x_3 = x_23;
goto _start;
}
}
}
else
{
goto block_14;
}
}
block_12:
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec_ref(x_2);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
}
block_14:
{
lean_object* x_13; 
x_13 = ((lean_object*)(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__1));
lean_inc(x_5);
x_6 = x_3;
x_7 = x_5;
x_8 = x_13;
goto block_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_11; lean_object* x_15; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_byte_array_size(x_27);
x_30 = lean_nat_dec_lt(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
else
{
uint8_t x_33; uint8_t x_34; uint8_t x_35; 
x_33 = lean_byte_array_fget(x_27, x_28);
x_34 = lean_uint8_once(&l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3, &l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3_once, _init_l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___closed__3);
x_35 = lean_uint8_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(x_2);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_99; 
x_37 = lean_ctor_get(x_36, 0);
x_38 = lean_ctor_get(x_36, 1);
x_99 = !lean_is_exclusive(x_36);
if (x_99 == 0)
{
x_39 = x_36;
x_40 = x_99;
goto block_98;
}
else
{
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_36);
x_39 = lean_box(0);
x_40 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_52; lean_object* x_56; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_78; uint8_t x_79; 
x_68 = lean_ctor_get(x_37, 0);
x_69 = lean_ctor_get(x_37, 1);
lean_inc(x_69);
x_78 = lean_byte_array_size(x_68);
x_79 = lean_nat_dec_lt(x_69, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_box(0);
lean_inc(x_37);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_37);
lean_ctor_set(x_81, 1, x_80);
lean_inc(x_69);
x_70 = x_81;
x_71 = x_37;
x_72 = x_69;
goto block_77;
}
else
{
uint8_t x_82; uint8_t x_83; uint8_t x_84; 
x_82 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2);
x_83 = lean_byte_array_fget(x_68, x_69);
x_84 = lean_uint8_dec_eq(x_83, x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9);
lean_inc(x_37);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_37);
lean_ctor_set(x_86, 1, x_85);
lean_inc(x_69);
x_70 = x_86;
x_71 = x_37;
x_72 = x_69;
goto block_77;
}
else
{
lean_object* x_87; uint8_t x_88; uint8_t x_95; 
lean_inc_ref(x_68);
x_95 = !lean_is_exclusive(x_37);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_37, 1);
lean_dec(x_96);
x_97 = lean_ctor_get(x_37, 0);
lean_dec(x_97);
x_87 = x_37;
x_88 = x_95;
goto block_94;
}
else
{
lean_dec(x_37);
x_87 = lean_box(0);
x_88 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_add(x_69, x_89);
lean_dec(x_69);
lean_inc(x_90);
lean_inc_ref(x_68);
if (x_88 == 0)
{
lean_ctor_set(x_87, 1, x_90);
x_91 = x_87;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_68);
lean_ctor_set(x_93, 1, x_90);
x_91 = x_93;
goto block_92;
}
block_92:
{
x_41 = x_91;
x_42 = x_68;
x_43 = x_90;
goto block_51;
}
}
}
}
block_51:
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_array_push(x_1, x_38);
x_45 = lean_byte_array_size(x_42);
lean_dec_ref(x_42);
x_46 = lean_nat_dec_lt(x_43, x_45);
lean_dec(x_43);
if (x_46 == 0)
{
lean_object* x_47; 
if (x_40 == 0)
{
lean_ctor_set(x_39, 1, x_44);
lean_ctor_set(x_39, 0, x_41);
x_47 = x_39;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
else
{
lean_del_object(x_39);
x_1 = x_44;
x_2 = x_41;
goto _start;
}
}
block_55:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
x_41 = x_52;
x_42 = x_53;
x_43 = x_54;
goto block_51;
}
block_67:
{
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_52 = x_57;
goto block_55;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_66; 
lean_del_object(x_39);
lean_dec(x_38);
lean_dec_ref(x_1);
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
x_66 = !lean_is_exclusive(x_56);
if (x_66 == 0)
{
x_60 = x_56;
x_61 = x_66;
goto block_65;
}
else
{
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_56);
x_60 = lean_box(0);
x_61 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_62; 
if (x_61 == 0)
{
x_62 = x_60;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_59);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
}
block_77:
{
uint8_t x_73; 
x_73 = lean_nat_dec_eq(x_69, x_72);
lean_dec(x_72);
lean_dec(x_69);
if (x_73 == 0)
{
lean_dec_ref(x_71);
x_56 = x_70;
goto block_67;
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_70);
x_74 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1);
x_75 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_74, x_71);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_52 = x_76;
goto block_55;
}
else
{
x_56 = x_75;
goto block_67;
}
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_108; 
lean_dec_ref(x_1);
x_100 = lean_ctor_get(x_36, 0);
x_101 = lean_ctor_get(x_36, 1);
x_108 = !lean_is_exclusive(x_36);
if (x_108 == 0)
{
x_102 = x_36;
x_103 = x_108;
goto block_107;
}
else
{
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_36);
x_102 = lean_box(0);
x_103 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_104; 
if (x_103 == 0)
{
x_104 = x_102;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_100);
lean_ctor_set(x_106, 1, x_101);
x_104 = x_106;
goto block_105;
}
block_105:
{
return x_104;
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__0));
x_110 = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(x_33, x_109, x_2);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_149; 
x_111 = lean_ctor_get(x_110, 0);
x_149 = !lean_is_exclusive(x_110);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_110, 1);
lean_dec(x_150);
x_112 = x_110;
x_113 = x_149;
goto block_148;
}
else
{
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_box(0);
x_113 = x_149;
goto block_148;
}
block_148:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_124; uint8_t x_125; 
x_114 = lean_ctor_get(x_111, 0);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
x_124 = lean_byte_array_size(x_114);
x_125 = lean_nat_dec_lt(x_115, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_box(0);
lean_inc(x_111);
if (x_113 == 0)
{
lean_ctor_set_tag(x_112, 1);
lean_ctor_set(x_112, 1, x_126);
x_127 = x_112;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_111);
lean_ctor_set(x_129, 1, x_126);
x_127 = x_129;
goto block_128;
}
block_128:
{
lean_inc(x_115);
x_116 = x_127;
x_117 = x_111;
x_118 = x_115;
goto block_123;
}
}
else
{
uint8_t x_130; uint8_t x_131; uint8_t x_132; 
x_130 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2);
x_131 = lean_byte_array_fget(x_114, x_115);
x_132 = lean_uint8_dec_eq(x_131, x_130);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9);
lean_inc(x_111);
if (x_113 == 0)
{
lean_ctor_set_tag(x_112, 1);
lean_ctor_set(x_112, 1, x_133);
x_134 = x_112;
goto block_135;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_111);
lean_ctor_set(x_136, 1, x_133);
x_134 = x_136;
goto block_135;
}
block_135:
{
lean_inc(x_115);
x_116 = x_134;
x_117 = x_111;
x_118 = x_115;
goto block_123;
}
}
else
{
lean_object* x_137; uint8_t x_138; uint8_t x_145; 
lean_inc_ref(x_114);
lean_del_object(x_112);
x_145 = !lean_is_exclusive(x_111);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_111, 1);
lean_dec(x_146);
x_147 = lean_ctor_get(x_111, 0);
lean_dec(x_147);
x_137 = x_111;
x_138 = x_145;
goto block_144;
}
else
{
lean_dec(x_111);
x_137 = lean_box(0);
x_138 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_unsigned_to_nat(1u);
x_140 = lean_nat_add(x_115, x_139);
lean_dec(x_115);
lean_inc(x_140);
lean_inc_ref(x_114);
if (x_138 == 0)
{
lean_ctor_set(x_137, 1, x_140);
x_141 = x_137;
goto block_142;
}
else
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_114);
lean_ctor_set(x_143, 1, x_140);
x_141 = x_143;
goto block_142;
}
block_142:
{
x_3 = x_141;
x_4 = x_114;
x_5 = x_140;
goto block_10;
}
}
}
}
block_123:
{
uint8_t x_119; 
x_119 = lean_nat_dec_eq(x_115, x_118);
lean_dec(x_118);
lean_dec(x_115);
if (x_119 == 0)
{
lean_dec_ref(x_117);
x_15 = x_116;
goto block_26;
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_116);
x_120 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1);
x_121 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_120, x_117);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
x_11 = x_122;
goto block_14;
}
else
{
x_15 = x_121;
goto block_26;
}
}
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; uint8_t x_159; 
lean_dec_ref(x_1);
x_151 = lean_ctor_get(x_110, 0);
x_152 = lean_ctor_get(x_110, 1);
x_159 = !lean_is_exclusive(x_110);
if (x_159 == 0)
{
x_153 = x_110;
x_154 = x_159;
goto block_158;
}
else
{
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_110);
x_153 = lean_box(0);
x_154 = x_159;
goto block_158;
}
block_158:
{
lean_object* x_155; 
if (x_154 == 0)
{
x_155 = x_153;
goto block_156;
}
else
{
lean_object* x_157; 
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_151);
lean_ctor_set(x_157, 1, x_152);
x_155 = x_157;
goto block_156;
}
block_156:
{
return x_155;
}
}
}
}
}
block_10:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_byte_array_size(x_4);
lean_dec_ref(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_1);
return x_8;
}
else
{
x_2 = x_3;
goto _start;
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_3 = x_11;
x_4 = x_12;
x_5 = x_13;
goto block_10;
}
block_26:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_11 = x_16;
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
x_19 = x_15;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0));
x_3 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__0);
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3));
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7));
x_2 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_8 = 0;
x_9 = lean_byte_array_fget(x_2, x_3);
x_10 = lean_uint8_dec_eq(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_23; 
lean_inc(x_3);
lean_inc_ref(x_2);
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_1, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_1, 0);
lean_dec(x_25);
x_13 = x_1;
x_14 = x_23;
goto block_22;
}
else
{
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_16);
x_17 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_16);
x_17 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
}
static uint8_t _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4(void) {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 15;
x_2 = lean_uint8_complement(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(uint64_t x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_byte_array_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; uint8_t x_60; 
lean_inc(x_5);
lean_inc_ref(x_4);
x_60 = !lean_is_exclusive(x_3);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_3, 1);
lean_dec(x_61);
x_62 = lean_ctor_get(x_3, 0);
lean_dec(x_62);
x_10 = x_3;
x_11 = x_60;
goto block_59;
}
else
{
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = x_60;
goto block_59;
}
block_59:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_byte_array_fget(x_4, x_5);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_14);
x_15 = x_10;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_4);
lean_ctor_set(x_58, 1, x_14);
x_15 = x_58;
goto block_57;
}
block_57:
{
uint64_t x_16; uint8_t x_17; uint8_t x_47; uint64_t x_51; uint8_t x_52; 
x_51 = 28;
x_52 = lean_uint64_dec_eq(x_2, x_51);
if (x_52 == 0)
{
x_47 = x_52;
goto block_50;
}
else
{
uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; 
x_53 = lean_uint8_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__4);
x_54 = lean_uint8_land(x_12, x_53);
x_55 = 0;
x_56 = lean_uint8_dec_eq(x_54, x_55);
if (x_56 == 0)
{
x_47 = x_52;
goto block_50;
}
else
{
goto block_46;
}
}
block_25:
{
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_uint64_to_nat(x_16);
x_19 = lean_nat_to_int(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_uint64_to_nat(x_16);
x_22 = lean_nat_to_int(x_21);
x_23 = lean_int_neg(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
block_46:
{
uint8_t x_26; uint8_t x_27; 
x_26 = 0;
x_27 = lean_uint8_dec_eq(x_12, x_26);
if (x_27 == 0)
{
uint8_t x_28; uint8_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; 
x_28 = 127;
x_29 = lean_uint8_land(x_12, x_28);
x_30 = lean_uint8_to_uint64(x_29);
x_31 = lean_uint64_shift_left(x_30, x_2);
x_32 = lean_uint64_lor(x_1, x_31);
x_33 = 128;
x_34 = lean_uint8_land(x_12, x_33);
x_35 = lean_uint8_dec_eq(x_34, x_26);
if (x_35 == 0)
{
uint64_t x_36; uint64_t x_37; 
x_36 = 7;
x_37 = lean_uint64_add(x_2, x_36);
x_1 = x_32;
x_2 = x_37;
x_3 = x_15;
goto _start;
}
else
{
uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint8_t x_43; 
x_39 = 1;
x_40 = lean_uint64_shift_right(x_32, x_39);
x_41 = lean_uint64_land(x_39, x_32);
x_42 = 0;
x_43 = lean_uint64_dec_eq(x_41, x_42);
if (x_43 == 0)
{
x_16 = x_40;
x_17 = x_35;
goto block_25;
}
else
{
x_16 = x_40;
x_17 = x_27;
goto block_25;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1));
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
block_50:
{
if (x_47 == 0)
{
goto block_46;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3));
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_15);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_5 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_6 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = 0;
x_3 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(x_2, x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_18; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_5 = x_2;
x_6 = x_18;
goto block_17;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
x_8 = lean_int_dec_lt(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1));
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_9);
x_10 = x_5;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_nat_abs(x_4);
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_13);
x_14 = x_5;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
x_21 = x_2;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_18; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_5 = x_2;
x_6 = x_18;
goto block_17;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
x_8 = lean_int_dec_lt(x_7, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_9);
x_10 = x_5;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_nat_abs(x_4);
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_13);
x_14 = x_5;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
x_21 = x_2;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_18; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_5 = x_2;
x_6 = x_18;
goto block_17;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
x_8 = lean_int_dec_lt(x_7, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_9);
x_10 = x_5;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_nat_abs(x_4);
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_13);
x_14 = x_5;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
x_21 = x_2;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_byte_array_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_10 = lean_byte_array_fget(x_4, x_5);
x_11 = 0;
x_12 = lean_uint8_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc_ref(x_1);
x_13 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_array_push(x_2, x_15);
x_2 = x_16;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
x_20 = x_13;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
else
{
lean_object* x_27; 
lean_dec_ref(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_2);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0));
x_4 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_byte_array_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint8_t x_10; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; 
x_10 = lean_byte_array_fget(x_4, x_5);
x_29 = 1;
x_30 = lean_uint8_land(x_29, x_10);
x_31 = 0;
x_32 = lean_uint8_dec_eq(x_30, x_31);
if (x_32 == 0)
{
if (x_7 == 0)
{
goto block_28;
}
else
{
lean_object* x_33; 
lean_dec_ref(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_3);
lean_ctor_set(x_33, 1, x_2);
return x_33;
}
}
else
{
goto block_28;
}
block_28:
{
uint8_t x_11; uint8_t x_12; 
x_11 = 0;
x_12 = lean_uint8_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc_ref(x_1);
x_13 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_array_push(x_2, x_15);
x_2 = x_16;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
x_20 = x_13;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
else
{
lean_object* x_27; 
lean_dec_ref(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_2);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg___closed__0));
x_4 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId), 1, 0);
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit), 1, 0);
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_byte_array_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; 
x_9 = lean_byte_array_fget(x_3, x_4);
x_39 = 1;
x_40 = lean_uint8_land(x_39, x_9);
x_41 = 0;
x_42 = lean_uint8_dec_eq(x_40, x_41);
if (x_42 == 0)
{
if (x_6 == 0)
{
goto block_38;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_1);
return x_43;
}
}
else
{
goto block_38;
}
block_38:
{
uint8_t x_10; uint8_t x_11; 
x_10 = 0;
x_11 = lean_uint8_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_27; 
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get(x_12, 1);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
x_15 = x_12;
x_16 = x_27;
goto block_26;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
x_18 = lean_int_dec_lt(x_17, x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_dec_ref(x_1);
x_19 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_19);
x_20 = x_15;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_del_object(x_15);
x_23 = lean_nat_abs(x_14);
lean_dec(x_14);
x_24 = lean_array_push(x_1, x_23);
x_1 = x_24;
x_2 = x_13;
goto _start;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec_ref(x_1);
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
x_36 = !lean_is_exclusive(x_12);
if (x_36 == 0)
{
x_30 = x_12;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_1);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__0));
x_3 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_35; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_35 = !lean_is_exclusive(x_2);
if (x_35 == 0)
{
x_5 = x_2;
x_6 = x_35;
goto block_34;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
x_8 = lean_int_dec_lt(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1));
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_9);
x_10 = x_5;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
else
{
lean_object* x_13; 
lean_del_object(x_5);
x_13 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_24; 
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_ctor_get(x_13, 1);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
x_16 = x_13;
x_17 = x_24;
goto block_23;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_nat_abs(x_4);
lean_dec(x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_19);
x_20 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec(x_4);
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
x_27 = x_13;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_2, 1);
x_44 = !lean_is_exclusive(x_2);
if (x_44 == 0)
{
x_38 = x_2;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_2);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes), 1, 0);
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_byte_array_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_9 = lean_byte_array_fget(x_3, x_4);
x_10 = 0;
x_11 = lean_uint8_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_array_push(x_1, x_14);
x_1 = x_15;
x_2 = x_13;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
x_19 = x_12;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_1);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___closed__0));
x_3 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_byte_array_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_9 = lean_byte_array_fget(x_3, x_4);
x_10 = 0;
x_11 = lean_uint8_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_array_push(x_1, x_14);
x_1 = x_15;
x_2 = x_13;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
x_19 = x_12;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_1);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__0));
x_3 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1_spec__2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_133; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_133 = !lean_is_exclusive(x_2);
if (x_133 == 0)
{
x_5 = x_2;
x_6 = x_133;
goto block_132;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
x_9 = lean_int_dec_lt(x_8, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1));
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_10);
x_11 = x_5;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_del_object(x_5);
x_14 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_122; 
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_ctor_get(x_14, 1);
x_122 = !lean_is_exclusive(x_14);
if (x_122 == 0)
{
x_17 = x_14;
x_18 = x_122;
goto block_121;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = x_122;
goto block_121;
}
block_121:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_byte_array_size(x_19);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_16);
lean_dec(x_4);
x_23 = lean_box(0);
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_23);
x_24 = x_17;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
else
{
uint8_t x_27; uint8_t x_28; uint8_t x_29; 
x_27 = 0;
x_28 = lean_byte_array_fget(x_19, x_20);
x_29 = lean_uint8_dec_eq(x_28, x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_16);
lean_dec(x_4);
x_30 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3);
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_30);
x_31 = x_17;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
else
{
lean_object* x_34; uint8_t x_35; uint8_t x_118; 
lean_inc(x_20);
lean_inc_ref(x_19);
lean_del_object(x_17);
x_118 = !lean_is_exclusive(x_15);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_15, 1);
lean_dec(x_119);
x_120 = lean_ctor_get(x_15, 0);
lean_dec(x_120);
x_34 = x_15;
x_35 = x_118;
goto block_117;
}
else
{
lean_dec(x_15);
x_34 = lean_box(0);
x_35 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_20, x_36);
lean_dec(x_20);
if (x_35 == 0)
{
lean_ctor_set(x_34, 1, x_37);
x_38 = x_34;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_19);
lean_ctor_set(x_116, 1, x_37);
x_38 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_39; 
x_39 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__1(x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_96; 
x_43 = lean_ctor_get(x_42, 0);
x_44 = lean_ctor_get(x_42, 1);
x_96 = !lean_is_exclusive(x_42);
if (x_96 == 0)
{
x_45 = x_42;
x_46 = x_96;
goto block_95;
}
else
{
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_42);
x_45 = lean_box(0);
x_46 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
x_49 = lean_byte_array_size(x_47);
x_50 = lean_nat_dec_lt(x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_16);
lean_dec(x_4);
x_51 = lean_box(0);
if (x_46 == 0)
{
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 1, x_51);
x_52 = x_45;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_51);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
else
{
uint8_t x_55; uint8_t x_56; 
x_55 = lean_byte_array_fget(x_47, x_48);
x_56 = lean_uint8_dec_eq(x_55, x_27);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_16);
lean_dec(x_4);
x_57 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3);
if (x_46 == 0)
{
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 1, x_57);
x_58 = x_45;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_43);
lean_ctor_set(x_60, 1, x_57);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
else
{
lean_object* x_61; uint8_t x_62; uint8_t x_92; 
lean_inc(x_48);
lean_inc_ref(x_47);
x_92 = !lean_is_exclusive(x_43);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_43, 1);
lean_dec(x_93);
x_94 = lean_ctor_get(x_43, 0);
lean_dec(x_94);
x_61 = x_43;
x_62 = x_92;
goto block_91;
}
else
{
lean_dec(x_43);
x_61 = lean_box(0);
x_62 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_nat_abs(x_4);
lean_dec(x_4);
x_64 = lean_nat_add(x_48, x_36);
lean_dec(x_48);
if (x_62 == 0)
{
lean_ctor_set(x_61, 1, x_64);
x_65 = x_61;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_47);
lean_ctor_set(x_90, 1, x_64);
x_65 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_array_get_size(x_16);
x_67 = lean_nat_dec_eq(x_66, x_7);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_array_get_size(x_44);
x_69 = lean_nat_dec_eq(x_68, x_7);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_16);
x_71 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_71, 1, x_16);
lean_ctor_set(x_71, 2, x_70);
lean_ctor_set(x_71, 3, x_41);
lean_ctor_set(x_71, 4, x_44);
if (x_46 == 0)
{
lean_ctor_set(x_45, 1, x_71);
lean_ctor_set(x_45, 0, x_65);
x_72 = x_45;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_65);
lean_ctor_set(x_74, 1, x_71);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_44);
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_63);
lean_ctor_set(x_75, 1, x_16);
lean_ctor_set(x_75, 2, x_41);
if (x_46 == 0)
{
lean_ctor_set(x_45, 1, x_75);
lean_ctor_set(x_45, 0, x_65);
x_76 = x_45;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_65);
lean_ctor_set(x_78, 1, x_75);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
else
{
lean_object* x_79; uint8_t x_80; 
lean_dec(x_16);
x_79 = lean_array_get_size(x_44);
lean_dec(x_44);
x_80 = lean_nat_dec_eq(x_79, x_7);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_63);
lean_dec(x_41);
x_81 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__2));
if (x_46 == 0)
{
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 1, x_81);
lean_ctor_set(x_45, 0, x_65);
x_82 = x_45;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_65);
lean_ctor_set(x_84, 1, x_81);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_63);
lean_ctor_set(x_85, 1, x_41);
if (x_46 == 0)
{
lean_ctor_set(x_45, 1, x_85);
lean_ctor_set(x_45, 0, x_65);
x_86 = x_45;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_65);
lean_ctor_set(x_88, 1, x_85);
x_86 = x_88;
goto block_87;
}
block_87:
{
return x_86;
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
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
lean_dec(x_41);
lean_dec(x_16);
lean_dec(x_4);
x_97 = lean_ctor_get(x_42, 0);
x_98 = lean_ctor_get(x_42, 1);
x_105 = !lean_is_exclusive(x_42);
if (x_105 == 0)
{
x_99 = x_42;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_42);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_114; 
lean_dec(x_16);
lean_dec(x_4);
x_106 = lean_ctor_get(x_39, 0);
x_107 = lean_ctor_get(x_39, 1);
x_114 = !lean_is_exclusive(x_39);
if (x_114 == 0)
{
x_108 = x_39;
x_109 = x_114;
goto block_113;
}
else
{
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_39);
x_108 = lean_box(0);
x_109 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_110; 
if (x_109 == 0)
{
x_110 = x_108;
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_106);
lean_ctor_set(x_112, 1, x_107);
x_110 = x_112;
goto block_111;
}
block_111:
{
return x_110;
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
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_131; 
lean_dec(x_4);
x_123 = lean_ctor_get(x_14, 0);
x_124 = lean_ctor_get(x_14, 1);
x_131 = !lean_is_exclusive(x_14);
if (x_131 == 0)
{
x_125 = x_14;
x_126 = x_131;
goto block_130;
}
else
{
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_14);
x_125 = lean_box(0);
x_126 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_127; 
if (x_126 == 0)
{
x_127 = x_125;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_123);
lean_ctor_set(x_129, 1, x_124);
x_127 = x_129;
goto block_128;
}
block_128:
{
return x_127;
}
}
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_142; 
x_134 = lean_ctor_get(x_2, 0);
x_135 = lean_ctor_get(x_2, 1);
x_142 = !lean_is_exclusive(x_2);
if (x_142 == 0)
{
x_136 = x_2;
x_137 = x_142;
goto block_141;
}
else
{
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_2);
x_136 = lean_box(0);
x_137 = x_142;
goto block_141;
}
block_141:
{
lean_object* x_138; 
if (x_137 == 0)
{
x_138 = x_136;
goto block_139;
}
else
{
lean_object* x_140; 
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_134);
lean_ctor_set(x_140, 1, x_135);
x_138 = x_140;
goto block_139;
}
block_139:
{
return x_138;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_38; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_38 = !lean_is_exclusive(x_2);
if (x_38 == 0)
{
x_5 = x_2;
x_6 = x_38;
goto block_37;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_byte_array_size(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = lean_box(0);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_11);
x_12 = x_5;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
else
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; 
x_15 = 0;
x_16 = lean_byte_array_fget(x_7, x_8);
x_17 = lean_uint8_dec_eq(x_16, x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_18 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_18);
x_19 = x_5;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; uint8_t x_23; uint8_t x_34; 
lean_inc(x_8);
lean_inc_ref(x_7);
x_34 = !lean_is_exclusive(x_3);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_3, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_3, 0);
lean_dec(x_36);
x_22 = x_3;
x_23 = x_34;
goto block_33;
}
else
{
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_8, x_24);
lean_dec(x_8);
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_25);
x_26 = x_22;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_25);
x_26 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_27);
lean_ctor_set(x_5, 0, x_26);
x_28 = x_5;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
x_47 = !lean_is_exclusive(x_2);
if (x_47 == 0)
{
x_41 = x_2;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0(void) {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 97;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; uint8_t x_29; 
lean_inc(x_3);
lean_inc_ref(x_2);
x_29 = !lean_is_exclusive(x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_1, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_1, 0);
lean_dec(x_31);
x_8 = x_1;
x_9 = x_29;
goto block_28;
}
else
{
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = x_29;
goto block_28;
}
block_28:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_byte_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
if (x_9 == 0)
{
lean_ctor_set(x_8, 1, x_12);
x_13 = x_8;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_12);
x_13 = x_27;
goto block_26;
}
block_26:
{
uint8_t x_14; uint8_t x_15; 
x_14 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
x_15 = lean_uint8_dec_eq(x_10, x_14);
if (x_15 == 0)
{
uint8_t x_16; uint8_t x_17; 
x_16 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
x_17 = lean_uint8_dec_eq(x_10, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1));
x_19 = lean_uint8_to_nat(x_10);
x_20 = l_Nat_reprFast(x_19);
x_21 = lean_string_append(x_18, x_20);
lean_dec_ref(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(x_13);
return x_24;
}
}
else
{
lean_object* x_25; 
x_25 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(x_13);
return x_25;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_2);
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_array_push(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_22; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
x_10 = x_3;
x_11 = x_22;
goto block_21;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_1);
if (x_11 == 0)
{
x_15 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_9);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; 
lean_dec(x_9);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 1, x_1);
x_18 = x_10;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_1);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions___closed__0));
x_3 = l_Std_Internal_Parsec_manyCore___at___00Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_byte_array_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
lean_object* x_9; uint8_t x_10; uint8_t x_16; 
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_3, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_3, 0);
lean_dec(x_18);
x_9 = x_3;
x_10 = x_16;
goto block_15;
}
else
{
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_11; lean_object* x_12; 
x_11 = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___closed__1));
if (x_10 == 0)
{
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 1, x_11);
x_12 = x_9;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_parseActions(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_byte_array_size(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_12 = lean_byte_array_fget(x_6, x_7);
x_13 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
x_14 = lean_uint8_dec_eq(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; 
x_15 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
x_16 = lean_uint8_dec_eq(x_12, x_15);
x_2 = x_16;
goto block_5;
}
else
{
x_2 = x_14;
goto block_5;
}
}
block_5:
{
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(x_1);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(x_1);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readBinFile(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_25; 
x_4 = lean_ctor_get(x_3, 0);
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
x_5 = x_3;
x_6 = x_25;
goto block_24;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_parseActions), 1, 0);
x_8 = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(x_7, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_19; 
x_9 = lean_ctor_get(x_8, 0);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
x_10 = x_8;
x_11 = x_19;
goto block_18;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_12; 
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 18);
x_12 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_17, 0, x_9);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_12);
x_13 = x_5;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec_ref(x_8);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_20);
x_21 = x_5;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
x_26 = lean_ctor_get(x_3, 0);
x_33 = !lean_is_exclusive(x_3);
if (x_33 == 0)
{
x_27 = x_3;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_3);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_parseLRATProof(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_parseActions), 1, 0);
x_3 = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_6);
x_7 = l_Nat_reprFast(x_6);
x_8 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_string_append(x_4, x_9);
lean_dec_ref(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
if (x_5 == 0)
{
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(x_1, x_10, x_11, x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0));
x_5 = l_Nat_reprFast(x_2);
x_6 = lean_string_append(x_4, x_5);
lean_dec_ref(x_5);
x_7 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
x_8 = lean_string_append(x_6, x_7);
x_9 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(x_3);
lean_dec(x_3);
x_10 = lean_string_append(x_8, x_9);
lean_dec_ref(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_6);
x_7 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(x_6);
x_8 = lean_string_append(x_4, x_7);
lean_dec_ref(x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
if (x_5 == 0)
{
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(x_1, x_10, x_11, x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_array_uget_borrowed(x_1, x_2);
x_15 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
x_16 = lean_int_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_nat_abs(x_14);
x_18 = l_Nat_reprFast(x_17);
x_5 = x_18;
goto block_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_nat_abs(x_14);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_19, x_20);
lean_dec(x_19);
x_22 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__0));
x_23 = lean_nat_add(x_21, x_20);
lean_dec(x_21);
x_24 = l_Nat_reprFast(x_23);
x_25 = lean_string_append(x_22, x_24);
lean_dec_ref(x_24);
x_5 = x_25;
goto block_12;
}
}
else
{
return x_4;
}
block_12:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_string_append(x_4, x_7);
lean_dec_ref(x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
if (x_5 == 0)
{
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(x_1, x_10, x_11, x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_Nat_reprFast(x_2);
x_5 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__0));
x_6 = lean_string_append(x_4, x_5);
x_7 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(x_3);
lean_dec_ref(x_3);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
x_10 = lean_string_append(x_8, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_1);
x_14 = l_Nat_reprFast(x_11);
x_15 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
x_16 = lean_string_append(x_14, x_15);
x_17 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(x_12);
lean_dec(x_12);
x_18 = lean_string_append(x_16, x_17);
lean_dec_ref(x_17);
x_19 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2));
x_20 = lean_string_append(x_18, x_19);
x_21 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(x_13);
lean_dec_ref(x_13);
x_22 = lean_string_append(x_20, x_21);
lean_dec_ref(x_21);
x_23 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
x_24 = lean_string_append(x_22, x_23);
return x_24;
}
case 2:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_28);
lean_dec_ref(x_1);
x_29 = l_Nat_reprFast(x_25);
x_30 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___closed__0));
x_31 = lean_string_append(x_29, x_30);
x_32 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(x_26);
lean_dec(x_26);
x_33 = lean_string_append(x_31, x_32);
lean_dec_ref(x_32);
x_34 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2));
x_35 = lean_string_append(x_33, x_34);
x_36 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(x_27);
lean_dec_ref(x_27);
x_37 = lean_string_append(x_35, x_36);
lean_dec_ref(x_36);
x_38 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(x_28);
lean_dec_ref(x_28);
x_39 = lean_string_append(x_37, x_38);
lean_dec_ref(x_38);
x_40 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
x_41 = lean_string_append(x_39, x_40);
return x_41;
}
default: 
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_42);
lean_dec_ref(x_1);
x_43 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3));
x_44 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(x_42);
lean_dec_ref(x_42);
x_45 = lean_string_append(x_43, x_44);
lean_dec_ref(x_44);
x_46 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1));
x_47 = lean_string_append(x_45, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_6);
x_7 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(x_6);
x_8 = lean_string_append(x_4, x_7);
lean_dec_ref(x_7);
x_9 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___closed__0));
x_10 = lean_string_append(x_8, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___closed__0));
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
if (x_5 == 0)
{
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(x_1, x_10, x_11, x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_lratProofToString(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startDelete(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
x_3 = lean_byte_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(lean_object* x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; uint64_t x_9; uint8_t x_10; 
x_9 = 0;
x_10 = lean_uint64_dec_eq(x_2, x_9);
if (x_10 == 0)
{
uint64_t x_11; uint8_t x_12; 
x_11 = 127;
x_12 = lean_uint64_dec_lt(x_11, x_2);
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; 
x_13 = lean_uint64_to_uint8(x_2);
x_14 = 127;
x_15 = lean_uint8_land(x_13, x_14);
x_3 = x_15;
goto block_8;
}
else
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; 
x_16 = lean_uint64_to_uint8(x_2);
x_17 = 127;
x_18 = lean_uint8_land(x_16, x_17);
x_19 = 128;
x_20 = lean_uint8_lor(x_18, x_19);
x_3 = x_20;
goto block_8;
}
}
else
{
return x_1;
}
block_8:
{
lean_object* x_4; uint64_t x_5; uint64_t x_6; 
x_4 = lean_byte_array_push(x_1, x_3);
x_5 = 7;
x_6 = lean_uint64_shift_right(x_2, x_5);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_4 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_ByteArray_empty;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("18446744073709551615");
return x_1;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3));
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(388u);
x_4 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2));
x_5 = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_11; uint8_t x_12; 
x_11 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__0);
x_12 = lean_int_dec_lt(x_11, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_abs(x_2);
x_15 = lean_nat_mul(x_13, x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_15, x_16);
lean_dec(x_15);
x_3 = x_17;
goto block_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_nat_abs(x_2);
x_20 = lean_nat_mul(x_18, x_19);
lean_dec(x_19);
x_3 = x_20;
goto block_10;
}
block_10:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__0);
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_6 = lean_obj_once(&l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4, &l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4_once, _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4);
x_7 = l_panic___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(x_6);
return x_7;
}
else
{
uint64_t x_8; lean_object* x_9; 
x_8 = lean_uint64_of_nat(x_3);
lean_dec(x_3);
x_9 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(x_1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_zeroByte(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 0;
x_3 = lean_byte_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_nat_to_int(x_2);
x_4 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_startAdd(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
x_3 = lean_byte_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_6);
x_7 = lean_nat_to_int(x_6);
x_8 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_4, x_7);
lean_dec(x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_6);
x_7 = lean_nat_to_int(x_6);
x_8 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_4, x_7);
lean_dec(x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(x_1, x_10, x_3, x_8);
return x_11;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
x_15 = lean_nat_to_int(x_12);
x_16 = lean_int_neg(x_15);
lean_dec(x_15);
x_17 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_4, x_16);
lean_dec(x_16);
x_18 = lean_array_get_size(x_13);
x_19 = lean_nat_dec_lt(x_14, x_18);
if (x_19 == 0)
{
x_5 = x_17;
goto block_9;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_18, x_18);
if (x_20 == 0)
{
if (x_19 == 0)
{
x_5 = x_17;
goto block_9;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_18);
x_23 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_13, x_21, x_22, x_17);
x_5 = x_23;
goto block_9;
}
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_18);
x_26 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_13, x_24, x_25, x_17);
x_5 = x_26;
goto block_9;
}
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
x_15 = lean_nat_to_int(x_12);
x_16 = lean_int_neg(x_15);
lean_dec(x_15);
x_17 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_4, x_16);
lean_dec(x_16);
x_18 = lean_array_get_size(x_13);
x_19 = lean_nat_dec_lt(x_14, x_18);
if (x_19 == 0)
{
x_5 = x_17;
goto block_9;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_18, x_18);
if (x_20 == 0)
{
if (x_19 == 0)
{
x_5 = x_17;
goto block_9;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_18);
x_23 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_13, x_21, x_22, x_17);
x_5 = x_23;
goto block_9;
}
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_18);
x_26 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_13, x_24, x_25, x_17);
x_5 = x_26;
goto block_9;
}
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2_spec__3(x_1, x_7, x_3, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_9; lean_object* x_13; lean_object* x_17; lean_object* x_21; lean_object* x_25; uint8_t x_26; 
x_25 = lean_array_get_size(x_1);
x_26 = lean_nat_dec_lt(x_2, x_25);
if (x_26 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_27; 
x_27 = lean_array_fget_borrowed(x_1, x_2);
switch (lean_obj_tag(x_27)) {
case 0:
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_28 = lean_ctor_get(x_27, 0);
x_29 = lean_ctor_get(x_27, 1);
x_30 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
x_31 = lean_byte_array_push(x_3, x_30);
lean_inc(x_28);
x_32 = lean_nat_to_int(x_28);
x_33 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_31, x_32);
lean_dec(x_32);
x_34 = 0;
x_35 = lean_byte_array_push(x_33, x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_array_get_size(x_29);
x_38 = lean_nat_dec_lt(x_36, x_37);
if (x_38 == 0)
{
x_13 = x_35;
goto block_16;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_37, x_37);
if (x_39 == 0)
{
if (x_38 == 0)
{
x_13 = x_35;
goto block_16;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_37);
x_42 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_29, x_40, x_41, x_35);
x_13 = x_42;
goto block_16;
}
}
else
{
size_t x_43; size_t x_44; lean_object* x_45; 
x_43 = 0;
x_44 = lean_usize_of_nat(x_37);
x_45 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_29, x_43, x_44, x_35);
x_13 = x_45;
goto block_16;
}
}
}
case 1:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_67; uint8_t x_68; 
x_46 = lean_ctor_get(x_27, 0);
x_47 = lean_ctor_get(x_27, 1);
x_48 = lean_ctor_get(x_27, 2);
x_49 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
x_50 = lean_byte_array_push(x_3, x_49);
lean_inc(x_46);
x_51 = lean_nat_to_int(x_46);
x_52 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_50, x_51);
lean_dec(x_51);
x_53 = lean_unsigned_to_nat(0u);
x_67 = lean_array_get_size(x_47);
x_68 = lean_nat_dec_lt(x_53, x_67);
if (x_68 == 0)
{
x_54 = x_52;
goto block_66;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_67, x_67);
if (x_69 == 0)
{
if (x_68 == 0)
{
x_54 = x_52;
goto block_66;
}
else
{
size_t x_70; size_t x_71; lean_object* x_72; 
x_70 = 0;
x_71 = lean_usize_of_nat(x_67);
x_72 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(x_47, x_70, x_71, x_52);
x_54 = x_72;
goto block_66;
}
}
else
{
size_t x_73; size_t x_74; lean_object* x_75; 
x_73 = 0;
x_74 = lean_usize_of_nat(x_67);
x_75 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(x_47, x_73, x_74, x_52);
x_54 = x_75;
goto block_66;
}
}
block_66:
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = 0;
x_56 = lean_byte_array_push(x_54, x_55);
x_57 = lean_array_get_size(x_48);
x_58 = lean_nat_dec_lt(x_53, x_57);
if (x_58 == 0)
{
x_17 = x_56;
goto block_20;
}
else
{
uint8_t x_59; 
x_59 = lean_nat_dec_le(x_57, x_57);
if (x_59 == 0)
{
if (x_58 == 0)
{
x_17 = x_56;
goto block_20;
}
else
{
size_t x_60; size_t x_61; lean_object* x_62; 
x_60 = 0;
x_61 = lean_usize_of_nat(x_57);
x_62 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_48, x_60, x_61, x_56);
x_17 = x_62;
goto block_20;
}
}
else
{
size_t x_63; size_t x_64; lean_object* x_65; 
x_63 = 0;
x_64 = lean_usize_of_nat(x_57);
x_65 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_48, x_63, x_64, x_56);
x_17 = x_65;
goto block_20;
}
}
}
}
case 2:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_96; lean_object* x_109; uint8_t x_110; 
x_76 = lean_ctor_get(x_27, 0);
x_77 = lean_ctor_get(x_27, 1);
x_78 = lean_ctor_get(x_27, 3);
x_79 = lean_ctor_get(x_27, 4);
x_80 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__0);
x_81 = lean_byte_array_push(x_3, x_80);
lean_inc(x_76);
x_82 = lean_nat_to_int(x_76);
x_83 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_81, x_82);
lean_dec(x_82);
x_84 = lean_unsigned_to_nat(0u);
x_109 = lean_array_get_size(x_77);
x_110 = lean_nat_dec_lt(x_84, x_109);
if (x_110 == 0)
{
x_96 = x_83;
goto block_108;
}
else
{
uint8_t x_111; 
x_111 = lean_nat_dec_le(x_109, x_109);
if (x_111 == 0)
{
if (x_110 == 0)
{
x_96 = x_83;
goto block_108;
}
else
{
size_t x_112; size_t x_113; lean_object* x_114; 
x_112 = 0;
x_113 = lean_usize_of_nat(x_109);
x_114 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(x_77, x_112, x_113, x_83);
x_96 = x_114;
goto block_108;
}
}
else
{
size_t x_115; size_t x_116; lean_object* x_117; 
x_115 = 0;
x_116 = lean_usize_of_nat(x_109);
x_117 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__1(x_77, x_115, x_116, x_83);
x_96 = x_117;
goto block_108;
}
}
block_95:
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_array_get_size(x_79);
x_87 = lean_nat_dec_lt(x_84, x_86);
if (x_87 == 0)
{
x_9 = x_85;
goto block_12;
}
else
{
uint8_t x_88; 
x_88 = lean_nat_dec_le(x_86, x_86);
if (x_88 == 0)
{
if (x_87 == 0)
{
x_9 = x_85;
goto block_12;
}
else
{
size_t x_89; size_t x_90; lean_object* x_91; 
x_89 = 0;
x_90 = lean_usize_of_nat(x_86);
x_91 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(x_79, x_89, x_90, x_85);
x_9 = x_91;
goto block_12;
}
}
else
{
size_t x_92; size_t x_93; lean_object* x_94; 
x_92 = 0;
x_93 = lean_usize_of_nat(x_86);
x_94 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(x_79, x_92, x_93, x_85);
x_9 = x_94;
goto block_12;
}
}
}
block_108:
{
uint8_t x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = 0;
x_98 = lean_byte_array_push(x_96, x_97);
x_99 = lean_array_get_size(x_78);
x_100 = lean_nat_dec_lt(x_84, x_99);
if (x_100 == 0)
{
x_85 = x_98;
goto block_95;
}
else
{
uint8_t x_101; 
x_101 = lean_nat_dec_le(x_99, x_99);
if (x_101 == 0)
{
if (x_100 == 0)
{
x_85 = x_98;
goto block_95;
}
else
{
size_t x_102; size_t x_103; lean_object* x_104; 
x_102 = 0;
x_103 = lean_usize_of_nat(x_99);
x_104 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_78, x_102, x_103, x_98);
x_85 = x_104;
goto block_95;
}
}
else
{
size_t x_105; size_t x_106; lean_object* x_107; 
x_105 = 0;
x_106 = lean_usize_of_nat(x_99);
x_107 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_78, x_105, x_106, x_98);
x_85 = x_107;
goto block_95;
}
}
}
}
default: 
{
lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_118 = lean_ctor_get(x_27, 0);
x_119 = lean_uint8_once(&l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0, &l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__0);
x_120 = lean_byte_array_push(x_3, x_119);
x_121 = lean_unsigned_to_nat(0u);
x_122 = lean_array_get_size(x_118);
x_123 = lean_nat_dec_lt(x_121, x_122);
if (x_123 == 0)
{
x_21 = x_120;
goto block_24;
}
else
{
uint8_t x_124; 
x_124 = lean_nat_dec_le(x_122, x_122);
if (x_124 == 0)
{
if (x_123 == 0)
{
x_21 = x_120;
goto block_24;
}
else
{
size_t x_125; size_t x_126; lean_object* x_127; 
x_125 = 0;
x_126 = lean_usize_of_nat(x_122);
x_127 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_118, x_125, x_126, x_120);
x_21 = x_127;
goto block_24;
}
}
else
{
size_t x_128; size_t x_129; lean_object* x_130; 
x_128 = 0;
x_129 = lean_usize_of_nat(x_122);
x_130 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_118, x_128, x_129, x_120);
x_21 = x_130;
goto block_24;
}
}
}
}
}
block_8:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_2, x_5);
lean_dec(x_2);
x_2 = x_6;
x_3 = x_4;
goto _start;
}
block_12:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = lean_byte_array_push(x_9, x_10);
x_4 = x_11;
goto block_8;
}
block_16:
{
uint8_t x_14; lean_object* x_15; 
x_14 = 0;
x_15 = lean_byte_array_push(x_13, x_14);
x_4 = x_15;
goto block_8;
}
block_20:
{
uint8_t x_18; lean_object* x_19; 
x_18 = 0;
x_19 = lean_byte_array_push(x_17, x_18);
x_4 = x_19;
goto block_8;
}
block_24:
{
uint8_t x_22; lean_object* x_23; 
x_22 = 0;
x_23 = lean_byte_array_push(x_21, x_22);
x_4 = x_23;
goto block_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(4u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_mul(x_3, x_4);
x_6 = lean_mk_empty_byte_array(x_5);
lean_dec(x_5);
x_7 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(x_1, x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_3 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Std_Tactic_BVDecide_LRAT_lratProofToString(x_2);
x_6 = lean_string_to_utf8(x_5);
lean_dec_ref(x_5);
x_7 = l_IO_FS_writeBinFile(x_1, x_6);
lean_dec_ref(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(x_2);
x_9 = l_IO_FS_writeBinFile(x_1, x_8);
lean_dec_ref(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(x_1, x_2, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
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
res = runtime_initialize_Init_System_IO(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Parsec(builtin)
;
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
res = initialize_Init_System_IO(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Parsec(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
}
#ifdef __cplusplus
}
#endif
