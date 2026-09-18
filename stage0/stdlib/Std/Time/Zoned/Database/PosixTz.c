// Lean compiler output
// Module: Std.Time.Zoned.Database.PosixTz
// Imports: public import Std.Internal.Parsec public import Std.Time.Zoned.ZoneRules
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__0 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__0_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " out of range"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__1 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__1_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "digit expected"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__2 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__2_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__2_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__3 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expected: '"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2_value;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__3;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5_value;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__6;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__7;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__8;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__9;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__10;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__11;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__12;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__2(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "second"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "minute"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hour "};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " out of range 0-"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "167"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "condition not satisfied"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName(lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "ASCII letter expected"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__1;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__3;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__4;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "day "};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " out of range 0-6"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1_value;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "week"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9_value;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__12;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__13;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__14;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "month"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__15 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__15_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec(lean_object*);
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__0;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Julian day"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__5 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__5_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__0 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__0_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "day"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__1 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSpec(lean_object*);
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__2;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__4;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__5;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "empty timezone name"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_parsePosixTz(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_parsePosixTz___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(lean_object* v_lo_6_, lean_object* v_hi_7_, lean_object* v_name_8_, lean_object* v_extra_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___y_12_; lean_object* v___y_13_; uint8_t v___y_14_; lean_object* v_fst_24_; lean_object* v_snd_25_; lean_object* v___x_26_; uint8_t v_decide_27_; 
v_fst_24_ = lean_ctor_get(v_a_10_, 0);
v_snd_25_ = lean_ctor_get(v_a_10_, 1);
v___x_26_ = lean_string_utf8_byte_size(v_fst_24_);
v_decide_27_ = lean_nat_dec_eq(v_snd_25_, v___x_26_);
if (v_decide_27_ == 0)
{
uint32_t v_c_28_; uint8_t v___y_30_; uint32_t v___x_68_; uint8_t v___x_69_; 
v_c_28_ = lean_string_utf8_get_fast(v_fst_24_, v_snd_25_);
v___x_68_ = 48;
v___x_69_ = lean_uint32_dec_le(v___x_68_, v_c_28_);
if (v___x_69_ == 0)
{
v___y_30_ = v___x_69_;
goto v___jp_29_;
}
else
{
uint32_t v___x_70_; uint8_t v___x_71_; 
v___x_70_ = 57;
v___x_71_ = lean_uint32_dec_le(v_c_28_, v___x_70_);
v___y_30_ = v___x_71_;
goto v___jp_29_;
}
v___jp_29_:
{
if (v___y_30_ == 0)
{
lean_object* v___x_31_; lean_object* v___x_32_; 
lean_dec_ref(v_extra_9_);
lean_dec_ref(v_name_8_);
v___x_31_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__3));
v___x_32_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_32_, 0, v_a_10_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
return v___x_32_;
}
else
{
lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_65_; 
lean_inc(v_snd_25_);
lean_inc(v_fst_24_);
v_isSharedCheck_65_ = !lean_is_exclusive(v_a_10_);
if (v_isSharedCheck_65_ == 0)
{
lean_object* v_unused_66_; lean_object* v_unused_67_; 
v_unused_66_ = lean_ctor_get(v_a_10_, 1);
lean_dec(v_unused_66_);
v_unused_67_ = lean_ctor_get(v_a_10_, 0);
lean_dec(v_unused_67_);
v___x_34_ = v_a_10_;
v_isShared_35_ = v_isSharedCheck_65_;
goto v_resetjp_33_;
}
else
{
lean_dec(v_a_10_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_65_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v_fst_41_; lean_object* v_snd_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_64_; 
v___x_36_ = lean_string_utf8_next_fast(v_fst_24_, v_snd_25_);
lean_dec(v_snd_25_);
v___x_37_ = lean_uint32_to_nat(v_c_28_);
v___x_38_ = lean_unsigned_to_nat(48u);
v___x_39_ = lean_nat_sub(v___x_37_, v___x_38_);
lean_dec(v___x_37_);
v___x_40_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_24_, v___x_36_, v___x_39_);
v_fst_41_ = lean_ctor_get(v___x_40_, 0);
v_snd_42_ = lean_ctor_get(v___x_40_, 1);
v_isSharedCheck_64_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_64_ == 0)
{
v___x_44_ = v___x_40_;
v_isShared_45_ = v_isSharedCheck_64_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_snd_42_);
lean_inc(v_fst_41_);
lean_dec(v___x_40_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_64_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_47_; 
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 1, v_snd_42_);
v___x_47_ = v___x_34_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_fst_24_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_snd_42_);
v___x_47_ = v_reuseFailAlloc_63_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
lean_object* v___x_48_; lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_48_ = lean_nat_to_int(v_fst_41_);
lean_inc(v___x_48_);
v___x_49_ = lean_apply_1(v_extra_9_, v___x_48_);
v___x_50_ = lean_unbox(v___x_49_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_59_; 
v___x_51_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__0));
v___x_52_ = lean_string_append(v_name_8_, v___x_51_);
v___x_53_ = l_Int_repr(v___x_48_);
lean_dec(v___x_48_);
v___x_54_ = lean_string_append(v___x_52_, v___x_53_);
lean_dec_ref(v___x_53_);
v___x_55_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__1));
v___x_56_ = lean_string_append(v___x_54_, v___x_55_);
v___x_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
if (v_isShared_45_ == 0)
{
lean_ctor_set_tag(v___x_44_, 1);
lean_ctor_set(v___x_44_, 1, v___x_57_);
lean_ctor_set(v___x_44_, 0, v___x_47_);
v___x_59_ = v___x_44_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v___x_47_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v___x_57_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
else
{
uint8_t v___x_61_; 
lean_del_object(v___x_44_);
v___x_61_ = lean_int_dec_le(v_lo_6_, v___x_48_);
if (v___x_61_ == 0)
{
v___y_12_ = v___x_48_;
v___y_13_ = v___x_47_;
v___y_14_ = v___x_61_;
goto v___jp_11_;
}
else
{
uint8_t v___x_62_; 
v___x_62_ = lean_int_dec_le(v___x_48_, v_hi_7_);
v___y_12_ = v___x_48_;
v___y_13_ = v___x_47_;
v___y_14_ = v___x_62_;
goto v___jp_11_;
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
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec_ref(v_extra_9_);
lean_dec_ref(v_name_8_);
v___x_72_ = lean_box(0);
v___x_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_73_, 0, v_a_10_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
return v___x_73_;
}
v___jp_11_:
{
if (v___y_14_ == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_15_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__0));
v___x_16_ = lean_string_append(v_name_8_, v___x_15_);
v___x_17_ = l_Int_repr(v___y_12_);
lean_dec(v___y_12_);
v___x_18_ = lean_string_append(v___x_16_, v___x_17_);
lean_dec_ref(v___x_17_);
v___x_19_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__1));
v___x_20_ = lean_string_append(v___x_18_, v___x_19_);
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
v___x_22_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_22_, 0, v___y_13_);
lean_ctor_set(v___x_22_, 1, v___x_21_);
return v___x_22_;
}
else
{
lean_object* v___x_23_; 
lean_dec_ref(v_name_8_);
v___x_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_23_, 0, v___y_13_);
lean_ctor_set(v___x_23_, 1, v___y_12_);
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___boxed(lean_object* v_lo_74_, lean_object* v_hi_75_, lean_object* v_name_76_, lean_object* v_extra_77_, lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v_lo_74_, v_hi_75_, v_name_76_, v_extra_77_, v_a_78_);
lean_dec(v_hi_75_);
lean_dec(v_lo_74_);
return v_res_79_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_to_int(v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__3(void){
_start:
{
uint32_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = 43;
v___x_85_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_86_ = lean_string_push(v___x_85_, v___x_84_);
return v___x_86_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__3);
v___x_88_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_89_ = lean_string_append(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__6(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_92_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4);
v___x_93_ = lean_string_append(v___x_92_, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__7(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__6, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__6_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__6);
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__8(void){
_start:
{
uint32_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = 45;
v___x_97_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_98_ = lean_string_push(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__9(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__8, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__8_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__8);
v___x_100_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_101_ = lean_string_append(v___x_100_, v___x_99_);
return v___x_101_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__10(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_103_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__9, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__9_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__9);
v___x_104_ = lean_string_append(v___x_103_, v___x_102_);
return v___x_104_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__11(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__10, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__10_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__10);
v___x_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__12(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_108_ = lean_int_neg(v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(lean_object* v_a_109_){
_start:
{
lean_object* v_fst_110_; lean_object* v_snd_111_; lean_object* v_err_113_; lean_object* v_err_121_; lean_object* v___x_142_; uint8_t v_decide_143_; 
v_fst_110_ = lean_ctor_get(v_a_109_, 0);
v_snd_111_ = lean_ctor_get(v_a_109_, 1);
v___x_142_ = lean_string_utf8_byte_size(v_fst_110_);
v_decide_143_ = lean_nat_dec_eq(v_snd_111_, v___x_142_);
if (v_decide_143_ == 0)
{
uint32_t v___x_144_; uint32_t v_c_145_; uint8_t v___x_146_; 
v___x_144_ = 45;
v_c_145_ = lean_string_utf8_get_fast(v_fst_110_, v_snd_111_);
v___x_146_ = lean_uint32_dec_eq(v_c_145_, v___x_144_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; 
v___x_147_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__11, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__11_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__11);
v_err_121_ = v___x_147_;
goto v___jp_120_;
}
else
{
lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_157_; 
lean_inc(v_snd_111_);
lean_inc(v_fst_110_);
v_isSharedCheck_157_ = !lean_is_exclusive(v_a_109_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; lean_object* v_unused_159_; 
v_unused_158_ = lean_ctor_get(v_a_109_, 1);
lean_dec(v_unused_158_);
v_unused_159_ = lean_ctor_get(v_a_109_, 0);
lean_dec(v_unused_159_);
v___x_149_ = v_a_109_;
v_isShared_150_ = v_isSharedCheck_157_;
goto v_resetjp_148_;
}
else
{
lean_dec(v_a_109_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_157_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v_it_x27_153_; 
v___x_151_ = lean_string_utf8_next_fast(v_fst_110_, v_snd_111_);
lean_dec(v_snd_111_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 1, v___x_151_);
v_it_x27_153_ = v___x_149_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_fst_110_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v___x_151_);
v_it_x27_153_ = v_reuseFailAlloc_156_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__12, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__12_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__12);
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v_it_x27_153_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
return v___x_155_;
}
}
}
}
else
{
lean_object* v___x_160_; 
v___x_160_ = lean_box(0);
v_err_121_ = v___x_160_;
goto v___jp_120_;
}
v___jp_112_:
{
uint8_t v_decide_114_; 
v_decide_114_ = lean_nat_dec_eq(v_snd_111_, v_snd_111_);
if (v_decide_114_ == 0)
{
lean_object* v___x_115_; 
lean_inc(v_err_113_);
v___x_115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_115_, 0, v_a_109_);
lean_ctor_set(v___x_115_, 1, v_err_113_);
return v___x_115_;
}
else
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v_a_109_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
return v___x_117_;
}
}
v___jp_118_:
{
lean_object* v___x_119_; 
v___x_119_ = lean_box(0);
v_err_113_ = v___x_119_;
goto v___jp_112_;
}
v___jp_120_:
{
uint8_t v_decide_122_; 
v_decide_122_ = lean_nat_dec_eq(v_snd_111_, v_snd_111_);
if (v_decide_122_ == 0)
{
lean_object* v___x_123_; 
lean_inc(v_err_121_);
v___x_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_123_, 0, v_a_109_);
lean_ctor_set(v___x_123_, 1, v_err_121_);
return v___x_123_;
}
else
{
lean_object* v___x_124_; uint8_t v_decide_125_; 
v___x_124_ = lean_string_utf8_byte_size(v_fst_110_);
v_decide_125_ = lean_nat_dec_eq(v_snd_111_, v___x_124_);
if (v_decide_125_ == 0)
{
if (v_decide_122_ == 0)
{
goto v___jp_118_;
}
else
{
uint32_t v___x_126_; uint32_t v_c_127_; uint8_t v___x_128_; 
v___x_126_ = 43;
v_c_127_ = lean_string_utf8_get_fast(v_fst_110_, v_snd_111_);
v___x_128_ = lean_uint32_dec_eq(v_c_127_, v___x_126_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__7, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__7_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__7);
v_err_113_ = v___x_129_;
goto v___jp_112_;
}
else
{
lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_139_; 
lean_inc(v_snd_111_);
lean_inc(v_fst_110_);
v_isSharedCheck_139_ = !lean_is_exclusive(v_a_109_);
if (v_isSharedCheck_139_ == 0)
{
lean_object* v_unused_140_; lean_object* v_unused_141_; 
v_unused_140_ = lean_ctor_get(v_a_109_, 1);
lean_dec(v_unused_140_);
v_unused_141_ = lean_ctor_get(v_a_109_, 0);
lean_dec(v_unused_141_);
v___x_131_ = v_a_109_;
v_isShared_132_ = v_isSharedCheck_139_;
goto v_resetjp_130_;
}
else
{
lean_dec(v_a_109_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_139_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; lean_object* v_it_x27_135_; 
v___x_133_ = lean_string_utf8_next_fast(v_fst_110_, v_snd_111_);
lean_dec(v_snd_111_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v___x_133_);
v_it_x27_135_ = v___x_131_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_fst_110_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_133_);
v_it_x27_135_ = v_reuseFailAlloc_138_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v_it_x27_135_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
return v___x_137_;
}
}
}
}
}
else
{
goto v___jp_118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__0(lean_object* v_a_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_nat_to_int(v_a_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__2(lean_object* v_a_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Rat_ofInt(v_a_163_);
return v___x_164_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0(uint8_t v___x_165_, lean_object* v_x_166_){
_start:
{
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed(lean_object* v___x_167_, lean_object* v_x_168_){
_start:
{
uint8_t v___x_4061__boxed_169_; uint8_t v_res_170_; lean_object* v_r_171_; 
v___x_4061__boxed_169_ = lean_unbox(v___x_167_);
v_res_170_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0(v___x_4061__boxed_169_, v_x_168_);
lean_dec(v_x_168_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(3600u);
v___x_173_ = lean_nat_to_int(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_unsigned_to_nat(60u);
v___x_175_ = lean_nat_to_int(v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = lean_nat_to_int(v___x_176_);
return v___x_177_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_unsigned_to_nat(59u);
v___x_179_ = lean_nat_to_int(v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(lean_object* v_maxHour_185_, lean_object* v_a_186_){
_start:
{
lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v_pos_190_; lean_object* v_res_191_; lean_object* v___y_200_; lean_object* v___y_201_; lean_object* v___y_202_; lean_object* v_err_203_; lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_213_; uint32_t v___y_214_; uint8_t v___y_215_; uint8_t v___y_238_; uint8_t v___y_239_; lean_object* v___y_240_; uint32_t v___y_241_; lean_object* v_pos_242_; lean_object* v_res_243_; uint8_t v___y_249_; uint8_t v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; uint32_t v___y_254_; lean_object* v_err_255_; lean_object* v_fst_259_; lean_object* v_snd_260_; uint8_t v___y_262_; uint8_t v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; uint32_t v___y_267_; uint8_t v___y_268_; lean_object* v___x_290_; uint8_t v_decide_291_; 
v_fst_259_ = lean_ctor_get(v_a_186_, 0);
v_snd_260_ = lean_ctor_get(v_a_186_, 1);
v___x_290_ = lean_string_utf8_byte_size(v_fst_259_);
v_decide_291_ = lean_nat_dec_eq(v_snd_260_, v___x_290_);
if (v_decide_291_ == 0)
{
uint32_t v_c_292_; uint8_t v___y_294_; uint32_t v___x_345_; uint8_t v___x_346_; 
v_c_292_ = lean_string_utf8_get_fast(v_fst_259_, v_snd_260_);
v___x_345_ = 48;
v___x_346_ = lean_uint32_dec_le(v___x_345_, v_c_292_);
if (v___x_346_ == 0)
{
v___y_294_ = v___x_346_;
goto v___jp_293_;
}
else
{
uint32_t v___x_347_; uint8_t v___x_348_; 
v___x_347_ = 57;
v___x_348_ = lean_uint32_dec_le(v_c_292_, v___x_347_);
v___y_294_ = v___x_348_;
goto v___jp_293_;
}
v___jp_293_:
{
if (v___y_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec(v_maxHour_185_);
v___x_295_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__3));
v___x_296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_296_, 0, v_a_186_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
return v___x_296_;
}
else
{
lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_342_; 
lean_inc(v_snd_260_);
lean_inc(v_fst_259_);
v_isSharedCheck_342_ = !lean_is_exclusive(v_a_186_);
if (v_isSharedCheck_342_ == 0)
{
lean_object* v_unused_343_; lean_object* v_unused_344_; 
v_unused_343_ = lean_ctor_get(v_a_186_, 1);
lean_dec(v_unused_343_);
v_unused_344_ = lean_ctor_get(v_a_186_, 0);
lean_dec(v_unused_344_);
v___x_298_ = v_a_186_;
v_isShared_299_ = v_isSharedCheck_342_;
goto v_resetjp_297_;
}
else
{
lean_dec(v_a_186_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_342_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v_fst_305_; lean_object* v_snd_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_341_; 
v___x_300_ = lean_string_utf8_next_fast(v_fst_259_, v_snd_260_);
lean_dec(v_snd_260_);
v___x_301_ = lean_uint32_to_nat(v_c_292_);
v___x_302_ = lean_unsigned_to_nat(48u);
v___x_303_ = lean_nat_sub(v___x_301_, v___x_302_);
lean_dec(v___x_301_);
v___x_304_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_259_, v___x_300_, v___x_303_);
v_fst_305_ = lean_ctor_get(v___x_304_, 0);
v_snd_306_ = lean_ctor_get(v___x_304_, 1);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_341_ == 0)
{
v___x_308_ = v___x_304_;
v_isShared_309_ = v_isSharedCheck_341_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_snd_306_);
lean_inc(v_fst_305_);
lean_dec(v___x_304_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_341_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
lean_inc(v_snd_306_);
lean_inc(v_fst_259_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 1, v_snd_306_);
v___x_311_ = v___x_298_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_fst_259_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_snd_306_);
v___x_311_ = v_reuseFailAlloc_340_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
uint8_t v___x_312_; 
v___x_312_ = lean_nat_dec_lt(v_maxHour_185_, v_fst_305_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; uint8_t v___x_314_; 
lean_dec(v_maxHour_185_);
v___x_313_ = lean_unsigned_to_nat(167u);
v___x_314_ = lean_nat_dec_le(v_fst_305_, v___x_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
lean_dec(v_snd_306_);
lean_dec(v_fst_259_);
v___x_315_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6));
v___x_316_ = l_Nat_reprFast(v_fst_305_);
v___x_317_ = lean_string_append(v___x_315_, v___x_316_);
lean_dec_ref(v___x_316_);
v___x_318_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7));
v___x_319_ = lean_string_append(v___x_317_, v___x_318_);
v___x_320_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8));
v___x_321_ = lean_string_append(v___x_319_, v___x_320_);
v___x_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
if (v_isShared_309_ == 0)
{
lean_ctor_set_tag(v___x_308_, 1);
lean_ctor_set(v___x_308_, 1, v___x_322_);
lean_ctor_set(v___x_308_, 0, v___x_311_);
v___x_324_ = v___x_308_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
else
{
lean_object* v___x_326_; uint32_t v___x_327_; uint8_t v_decide_328_; 
lean_del_object(v___x_308_);
v___x_326_ = lean_nat_to_int(v_fst_305_);
v___x_327_ = 58;
v_decide_328_ = lean_nat_dec_eq(v_snd_306_, v___x_290_);
if (v_decide_328_ == 0)
{
v___y_262_ = v___x_314_;
v___y_263_ = v___x_312_;
v___y_264_ = v___x_311_;
v___y_265_ = v___x_326_;
v___y_266_ = v_snd_306_;
v___y_267_ = v___x_327_;
v___y_268_ = v___x_314_;
goto v___jp_261_;
}
else
{
v___y_262_ = v___x_314_;
v___y_263_ = v___x_312_;
v___y_264_ = v___x_311_;
v___y_265_ = v___x_326_;
v___y_266_ = v_snd_306_;
v___y_267_ = v___x_327_;
v___y_268_ = v___x_312_;
goto v___jp_261_;
}
}
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
lean_dec(v_snd_306_);
lean_dec(v_fst_259_);
v___x_329_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6));
v___x_330_ = l_Nat_reprFast(v_fst_305_);
v___x_331_ = lean_string_append(v___x_329_, v___x_330_);
lean_dec_ref(v___x_330_);
v___x_332_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7));
v___x_333_ = lean_string_append(v___x_331_, v___x_332_);
v___x_334_ = l_Nat_reprFast(v_maxHour_185_);
v___x_335_ = lean_string_append(v___x_333_, v___x_334_);
lean_dec_ref(v___x_334_);
v___x_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
if (v_isShared_309_ == 0)
{
lean_ctor_set_tag(v___x_308_, 1);
lean_ctor_set(v___x_308_, 1, v___x_336_);
lean_ctor_set(v___x_308_, 0, v___x_311_);
v___x_338_ = v___x_308_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
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
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec(v_maxHour_185_);
v___x_349_ = lean_box(0);
v___x_350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_350_, 0, v_a_186_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
return v___x_350_;
}
v___jp_187_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_192_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0);
v___x_193_ = lean_int_mul(v___y_189_, v___x_192_);
lean_dec(v___y_189_);
v___x_194_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1);
v___x_195_ = lean_int_mul(v___y_188_, v___x_194_);
lean_dec(v___y_188_);
v___x_196_ = lean_int_add(v___x_193_, v___x_195_);
lean_dec(v___x_195_);
lean_dec(v___x_193_);
v___x_197_ = lean_int_add(v___x_196_, v_res_191_);
lean_dec(v_res_191_);
lean_dec(v___x_196_);
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v_pos_190_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
return v___x_198_;
}
v___jp_199_:
{
lean_object* v_snd_204_; uint8_t v_decide_205_; 
v_snd_204_ = lean_ctor_get(v___y_200_, 1);
v_decide_205_ = lean_nat_dec_eq(v_snd_204_, v_snd_204_);
if (v_decide_205_ == 0)
{
lean_object* v___x_206_; 
lean_dec(v___y_202_);
lean_dec(v___y_201_);
v___x_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_206_, 0, v___y_200_);
lean_ctor_set(v___x_206_, 1, v_err_203_);
return v___x_206_;
}
else
{
lean_object* v___x_207_; 
lean_dec(v_err_203_);
v___x_207_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2);
v___y_188_ = v___y_201_;
v___y_189_ = v___y_202_;
v_pos_190_ = v___y_200_;
v_res_191_ = v___x_207_;
goto v___jp_187_;
}
}
v___jp_208_:
{
if (v___y_215_ == 0)
{
lean_object* v___x_216_; 
lean_dec(v___y_213_);
lean_dec(v___y_210_);
v___x_216_ = lean_box(0);
v___y_200_ = v___y_209_;
v___y_201_ = v___y_211_;
v___y_202_ = v___y_212_;
v_err_203_ = v___x_216_;
goto v___jp_199_;
}
else
{
uint32_t v_c_217_; uint8_t v___x_218_; 
v_c_217_ = lean_string_utf8_get_fast(v___y_210_, v___y_213_);
v___x_218_ = lean_uint32_dec_eq(v_c_217_, v___y_214_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec(v___y_213_);
lean_dec(v___y_210_);
v___x_219_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_220_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_221_ = lean_string_push(v___x_220_, v___y_214_);
v___x_222_ = lean_string_append(v___x_219_, v___x_221_);
lean_dec_ref(v___x_221_);
v___x_223_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_224_ = lean_string_append(v___x_222_, v___x_223_);
v___x_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
v___y_200_ = v___y_209_;
v___y_201_ = v___y_211_;
v___y_202_ = v___y_212_;
v_err_203_ = v___x_225_;
goto v___jp_199_;
}
else
{
lean_object* v___x_226_; lean_object* v___f_227_; lean_object* v___x_228_; lean_object* v_it_x27_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_226_ = lean_box(v___x_218_);
v___f_227_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_227_, 0, v___x_226_);
v___x_228_ = lean_string_utf8_next_fast(v___y_210_, v___y_213_);
lean_dec(v___y_213_);
v_it_x27_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_229_, 0, v___y_210_);
lean_ctor_set(v_it_x27_229_, 1, v___x_228_);
v___x_230_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2);
v___x_231_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_232_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4));
v___x_233_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_230_, v___x_231_, v___x_232_, v___f_227_, v_it_x27_229_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_pos_234_; lean_object* v_res_235_; 
lean_dec_ref(v___y_209_);
v_pos_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_pos_234_);
v_res_235_ = lean_ctor_get(v___x_233_, 1);
lean_inc(v_res_235_);
lean_dec_ref_known(v___x_233_, 2);
v___y_188_ = v___y_211_;
v___y_189_ = v___y_212_;
v_pos_190_ = v_pos_234_;
v_res_191_ = v_res_235_;
goto v___jp_187_;
}
else
{
lean_object* v_err_236_; 
v_err_236_ = lean_ctor_get(v___x_233_, 1);
lean_inc(v_err_236_);
lean_dec_ref_known(v___x_233_, 2);
v___y_200_ = v___y_209_;
v___y_201_ = v___y_211_;
v___y_202_ = v___y_212_;
v_err_203_ = v_err_236_;
goto v___jp_199_;
}
}
}
}
v___jp_237_:
{
lean_object* v_fst_244_; lean_object* v_snd_245_; lean_object* v___x_246_; uint8_t v_decide_247_; 
v_fst_244_ = lean_ctor_get(v_pos_242_, 0);
lean_inc(v_fst_244_);
v_snd_245_ = lean_ctor_get(v_pos_242_, 1);
lean_inc(v_snd_245_);
v___x_246_ = lean_string_utf8_byte_size(v_fst_244_);
v_decide_247_ = lean_nat_dec_eq(v_snd_245_, v___x_246_);
if (v_decide_247_ == 0)
{
v___y_209_ = v_pos_242_;
v___y_210_ = v_fst_244_;
v___y_211_ = v_res_243_;
v___y_212_ = v___y_240_;
v___y_213_ = v_snd_245_;
v___y_214_ = v___y_241_;
v___y_215_ = v___y_238_;
goto v___jp_208_;
}
else
{
v___y_209_ = v_pos_242_;
v___y_210_ = v_fst_244_;
v___y_211_ = v_res_243_;
v___y_212_ = v___y_240_;
v___y_213_ = v_snd_245_;
v___y_214_ = v___y_241_;
v___y_215_ = v___y_239_;
goto v___jp_208_;
}
}
v___jp_248_:
{
uint8_t v_decide_256_; 
v_decide_256_ = lean_nat_dec_eq(v___y_253_, v___y_253_);
lean_dec(v___y_253_);
if (v_decide_256_ == 0)
{
lean_object* v___x_257_; 
lean_dec(v___y_252_);
v___x_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_257_, 0, v___y_251_);
lean_ctor_set(v___x_257_, 1, v_err_255_);
return v___x_257_;
}
else
{
lean_object* v___x_258_; 
lean_dec(v_err_255_);
v___x_258_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2);
v___y_238_ = v___y_249_;
v___y_239_ = v___y_250_;
v___y_240_ = v___y_252_;
v___y_241_ = v___y_254_;
v_pos_242_ = v___y_251_;
v_res_243_ = v___x_258_;
goto v___jp_237_;
}
}
v___jp_261_:
{
if (v___y_268_ == 0)
{
lean_object* v___x_269_; 
lean_dec(v_fst_259_);
v___x_269_ = lean_box(0);
v___y_249_ = v___y_262_;
v___y_250_ = v___y_263_;
v___y_251_ = v___y_264_;
v___y_252_ = v___y_265_;
v___y_253_ = v___y_266_;
v___y_254_ = v___y_267_;
v_err_255_ = v___x_269_;
goto v___jp_248_;
}
else
{
uint32_t v_c_270_; uint8_t v___x_271_; 
v_c_270_ = lean_string_utf8_get_fast(v_fst_259_, v___y_266_);
v___x_271_ = lean_uint32_dec_eq(v_c_270_, v___y_267_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec(v_fst_259_);
v___x_272_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_273_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_274_ = lean_string_push(v___x_273_, v___y_267_);
v___x_275_ = lean_string_append(v___x_272_, v___x_274_);
lean_dec_ref(v___x_274_);
v___x_276_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_277_ = lean_string_append(v___x_275_, v___x_276_);
v___x_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
v___y_249_ = v___y_262_;
v___y_250_ = v___y_263_;
v___y_251_ = v___y_264_;
v___y_252_ = v___y_265_;
v___y_253_ = v___y_266_;
v___y_254_ = v___y_267_;
v_err_255_ = v___x_278_;
goto v___jp_248_;
}
else
{
lean_object* v___x_279_; lean_object* v___f_280_; lean_object* v___x_281_; lean_object* v_it_x27_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_279_ = lean_box(v___x_271_);
v___f_280_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_280_, 0, v___x_279_);
v___x_281_ = lean_string_utf8_next_fast(v_fst_259_, v___y_266_);
v_it_x27_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_282_, 0, v_fst_259_);
lean_ctor_set(v_it_x27_282_, 1, v___x_281_);
v___x_283_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2);
v___x_284_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_285_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5));
v___x_286_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_283_, v___x_284_, v___x_285_, v___f_280_, v_it_x27_282_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_pos_287_; lean_object* v_res_288_; 
lean_dec(v___y_266_);
lean_dec_ref(v___y_264_);
v_pos_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_pos_287_);
v_res_288_ = lean_ctor_get(v___x_286_, 1);
lean_inc(v_res_288_);
lean_dec_ref_known(v___x_286_, 2);
v___y_238_ = v___y_262_;
v___y_239_ = v___y_263_;
v___y_240_ = v___y_265_;
v___y_241_ = v___y_267_;
v_pos_242_ = v_pos_287_;
v_res_243_ = v_res_288_;
goto v___jp_237_;
}
else
{
lean_object* v_err_289_; 
v_err_289_ = lean_ctor_get(v___x_286_, 1);
lean_inc(v_err_289_);
lean_dec_ref_known(v___x_286_, 2);
v___y_249_ = v___y_262_;
v___y_250_ = v___y_263_;
v___y_251_ = v___y_264_;
v___y_252_ = v___y_265_;
v___y_253_ = v___y_266_;
v___y_254_ = v___y_267_;
v_err_255_ = v_err_289_;
goto v___jp_248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__1(lean_object* v_a_351_){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_nat_to_int(v_a_351_);
v___x_353_ = l_Rat_ofInt(v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(lean_object* v_a_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(v_a_354_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_pos_356_; lean_object* v_res_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v_pos_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_pos_356_);
v_res_357_ = lean_ctor_get(v___x_355_, 1);
lean_inc(v_res_357_);
lean_dec_ref_known(v___x_355_, 2);
v___x_358_ = lean_unsigned_to_nat(24u);
v___x_359_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(v___x_358_, v_pos_356_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_pos_360_; lean_object* v_res_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_370_; 
v_pos_360_ = lean_ctor_get(v___x_359_, 0);
v_res_361_ = lean_ctor_get(v___x_359_, 1);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_370_ == 0)
{
v___x_363_ = v___x_359_;
v_isShared_364_ = v_isSharedCheck_370_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_res_361_);
lean_inc(v_pos_360_);
lean_dec(v___x_359_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_370_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_365_ = lean_int_neg(v_res_357_);
lean_dec(v_res_357_);
v___x_366_ = lean_int_mul(v___x_365_, v_res_361_);
lean_dec(v_res_361_);
lean_dec(v___x_365_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 1, v___x_366_);
v___x_368_ = v___x_363_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_pos_360_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
lean_object* v_pos_371_; lean_object* v_err_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec(v_res_357_);
v_pos_371_ = lean_ctor_get(v___x_359_, 0);
v_err_372_ = lean_ctor_get(v___x_359_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_359_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_err_372_);
lean_inc(v_pos_371_);
lean_dec(v___x_359_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_pos_371_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_err_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
else
{
lean_object* v_pos_380_; lean_object* v_err_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
v_pos_380_ = lean_ctor_get(v___x_355_, 0);
v_err_381_ = lean_ctor_get(v___x_355_, 1);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_355_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_err_381_);
lean_inc(v_pos_380_);
lean_dec(v___x_355_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_pos_380_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_err_381_);
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
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0(lean_object* v_acc_392_, lean_object* v_a_393_){
_start:
{
lean_object* v_fst_394_; lean_object* v_snd_395_; lean_object* v_pos_397_; lean_object* v_snd_398_; lean_object* v_err_399_; lean_object* v___x_403_; uint8_t v_decide_404_; 
v_fst_394_ = lean_ctor_get(v_a_393_, 0);
v_snd_395_ = lean_ctor_get(v_a_393_, 1);
lean_inc(v_snd_395_);
v___x_403_ = lean_string_utf8_byte_size(v_fst_394_);
v_decide_404_ = lean_nat_dec_eq(v_snd_395_, v___x_403_);
if (v_decide_404_ == 0)
{
uint32_t v_c_405_; lean_object* v___x_406_; lean_object* v_it_x27_407_; uint8_t v___y_412_; uint8_t v___y_413_; uint8_t v___y_416_; uint8_t v___y_427_; uint32_t v___x_432_; uint8_t v___x_433_; 
v_c_405_ = lean_string_utf8_get_fast(v_fst_394_, v_snd_395_);
v___x_406_ = lean_string_utf8_next_fast(v_fst_394_, v_snd_395_);
lean_inc(v_fst_394_);
v_it_x27_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_407_, 0, v_fst_394_);
lean_ctor_set(v_it_x27_407_, 1, v___x_406_);
v___x_432_ = 65;
v___x_433_ = lean_uint32_dec_le(v___x_432_, v_c_405_);
if (v___x_433_ == 0)
{
v___y_427_ = v___x_433_;
goto v___jp_426_;
}
else
{
uint32_t v___x_434_; uint8_t v___x_435_; 
v___x_434_ = 90;
v___x_435_ = lean_uint32_dec_le(v_c_405_, v___x_434_);
v___y_427_ = v___x_435_;
goto v___jp_426_;
}
v___jp_408_:
{
lean_object* v___x_409_; 
v___x_409_ = lean_string_push(v_acc_392_, v_c_405_);
v_acc_392_ = v___x_409_;
v_a_393_ = v_it_x27_407_;
goto _start;
}
v___jp_411_:
{
if (v___y_412_ == 0)
{
if (v___y_413_ == 0)
{
lean_object* v___x_414_; 
lean_dec_ref_known(v_it_x27_407_, 2);
v___x_414_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__1));
lean_inc(v_snd_395_);
v_pos_397_ = v_a_393_;
v_snd_398_ = v_snd_395_;
v_err_399_ = v___x_414_;
goto v___jp_396_;
}
else
{
lean_dec(v_snd_395_);
lean_dec_ref(v_a_393_);
goto v___jp_408_;
}
}
else
{
lean_dec(v_snd_395_);
lean_dec_ref(v_a_393_);
goto v___jp_408_;
}
}
v___jp_415_:
{
uint32_t v___x_417_; uint8_t v___x_418_; 
v___x_417_ = 43;
v___x_418_ = lean_uint32_dec_eq(v_c_405_, v___x_417_);
if (v___x_418_ == 0)
{
uint32_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = 45;
v___x_420_ = lean_uint32_dec_eq(v_c_405_, v___x_419_);
v___y_412_ = v___y_416_;
v___y_413_ = v___x_420_;
goto v___jp_411_;
}
else
{
v___y_412_ = v___y_416_;
v___y_413_ = v___x_418_;
goto v___jp_411_;
}
}
v___jp_421_:
{
uint32_t v___x_422_; uint8_t v___x_423_; 
v___x_422_ = 48;
v___x_423_ = lean_uint32_dec_le(v___x_422_, v_c_405_);
if (v___x_423_ == 0)
{
v___y_416_ = v___x_423_;
goto v___jp_415_;
}
else
{
uint32_t v___x_424_; uint8_t v___x_425_; 
v___x_424_ = 57;
v___x_425_ = lean_uint32_dec_le(v_c_405_, v___x_424_);
v___y_416_ = v___x_425_;
goto v___jp_415_;
}
}
v___jp_426_:
{
if (v___y_427_ == 0)
{
uint32_t v___x_428_; uint8_t v___x_429_; 
v___x_428_ = 97;
v___x_429_ = lean_uint32_dec_le(v___x_428_, v_c_405_);
if (v___x_429_ == 0)
{
goto v___jp_421_;
}
else
{
uint32_t v___x_430_; uint8_t v___x_431_; 
v___x_430_ = 122;
v___x_431_ = lean_uint32_dec_le(v_c_405_, v___x_430_);
if (v___x_431_ == 0)
{
goto v___jp_421_;
}
else
{
v___y_416_ = v___x_431_;
goto v___jp_415_;
}
}
}
else
{
v___y_416_ = v___y_427_;
goto v___jp_415_;
}
}
}
else
{
lean_object* v___x_436_; 
v___x_436_ = lean_box(0);
lean_inc(v_snd_395_);
v_pos_397_ = v_a_393_;
v_snd_398_ = v_snd_395_;
v_err_399_ = v___x_436_;
goto v___jp_396_;
}
v___jp_396_:
{
uint8_t v_decide_400_; 
v_decide_400_ = lean_nat_dec_eq(v_snd_395_, v_snd_398_);
lean_dec(v_snd_398_);
lean_dec(v_snd_395_);
if (v_decide_400_ == 0)
{
lean_object* v___x_401_; 
lean_dec_ref(v_acc_392_);
lean_inc(v_err_399_);
v___x_401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_401_, 0, v_pos_397_);
lean_ctor_set(v___x_401_, 1, v_err_399_);
return v___x_401_;
}
else
{
lean_object* v___x_402_; 
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v_pos_397_);
lean_ctor_set(v___x_402_, 1, v_acc_392_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName(lean_object* v_a_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_439_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0(v___x_438_, v_a_437_);
return v___x_439_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
if (lean_obj_tag(v_x_440_) == 0)
{
if (lean_obj_tag(v_x_441_) == 0)
{
uint8_t v___x_442_; 
v___x_442_ = 1;
return v___x_442_;
}
else
{
uint8_t v___x_443_; 
v___x_443_ = 0;
return v___x_443_;
}
}
else
{
if (lean_obj_tag(v_x_441_) == 0)
{
uint8_t v___x_444_; 
v___x_444_ = 0;
return v___x_444_;
}
else
{
lean_object* v_val_445_; lean_object* v_val_446_; uint32_t v___x_447_; uint32_t v___x_448_; uint8_t v___x_449_; 
v_val_445_ = lean_ctor_get(v_x_440_, 0);
v_val_446_ = lean_ctor_get(v_x_441_, 0);
v___x_447_ = lean_unbox_uint32(v_val_445_);
v___x_448_ = lean_unbox_uint32(v_val_446_);
v___x_449_ = lean_uint32_dec_eq(v___x_447_, v___x_448_);
return v___x_449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0___boxed(lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
uint8_t v_res_452_; lean_object* v_r_453_; 
v_res_452_ = l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_x_450_, v_x_451_);
lean_dec(v_x_451_);
lean_dec(v_x_450_);
v_r_453_ = lean_box(v_res_452_);
return v_r_453_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1(lean_object* v_acc_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_fst_459_; lean_object* v_snd_460_; lean_object* v_pos_462_; lean_object* v_snd_463_; lean_object* v_err_464_; lean_object* v___x_468_; uint8_t v_decide_469_; 
v_fst_459_ = lean_ctor_get(v_a_458_, 0);
v_snd_460_ = lean_ctor_get(v_a_458_, 1);
lean_inc(v_snd_460_);
v___x_468_ = lean_string_utf8_byte_size(v_fst_459_);
v_decide_469_ = lean_nat_dec_eq(v_snd_460_, v___x_468_);
if (v_decide_469_ == 0)
{
uint32_t v_c_470_; lean_object* v___x_471_; uint8_t v___y_477_; uint8_t v___y_478_; uint8_t v___y_481_; uint32_t v___x_486_; uint8_t v___x_487_; 
v_c_470_ = lean_string_utf8_get_fast(v_fst_459_, v_snd_460_);
v___x_471_ = lean_string_utf8_next_fast(v_fst_459_, v_snd_460_);
v___x_486_ = 65;
v___x_487_ = lean_uint32_dec_le(v___x_486_, v_c_470_);
if (v___x_487_ == 0)
{
v___y_481_ = v___x_487_;
goto v___jp_480_;
}
else
{
uint32_t v___x_488_; uint8_t v___x_489_; 
v___x_488_ = 90;
v___x_489_ = lean_uint32_dec_le(v_c_470_, v___x_488_);
v___y_481_ = v___x_489_;
goto v___jp_480_;
}
v___jp_472_:
{
lean_object* v_it_x27_473_; lean_object* v___x_474_; 
v_it_x27_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_473_, 0, v_fst_459_);
lean_ctor_set(v_it_x27_473_, 1, v___x_471_);
v___x_474_ = lean_string_push(v_acc_457_, v_c_470_);
v_acc_457_ = v___x_474_;
v_a_458_ = v_it_x27_473_;
goto _start;
}
v___jp_476_:
{
if (v___y_477_ == 0)
{
if (v___y_478_ == 0)
{
lean_object* v___x_479_; 
v___x_479_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__1));
lean_inc(v_snd_460_);
v_pos_462_ = v_a_458_;
v_snd_463_ = v_snd_460_;
v_err_464_ = v___x_479_;
goto v___jp_461_;
}
else
{
lean_inc(v_fst_459_);
lean_dec(v_snd_460_);
lean_dec_ref(v_a_458_);
goto v___jp_472_;
}
}
else
{
lean_inc(v_fst_459_);
lean_dec(v_snd_460_);
lean_dec_ref(v_a_458_);
goto v___jp_472_;
}
}
v___jp_480_:
{
uint32_t v___x_482_; uint8_t v___x_483_; 
v___x_482_ = 97;
v___x_483_ = lean_uint32_dec_le(v___x_482_, v_c_470_);
if (v___x_483_ == 0)
{
v___y_477_ = v___y_481_;
v___y_478_ = v___x_483_;
goto v___jp_476_;
}
else
{
uint32_t v___x_484_; uint8_t v___x_485_; 
v___x_484_ = 122;
v___x_485_ = lean_uint32_dec_le(v_c_470_, v___x_484_);
v___y_477_ = v___y_481_;
v___y_478_ = v___x_485_;
goto v___jp_476_;
}
}
}
else
{
lean_object* v___x_490_; 
v___x_490_ = lean_box(0);
lean_inc(v_snd_460_);
v_pos_462_ = v_a_458_;
v_snd_463_ = v_snd_460_;
v_err_464_ = v___x_490_;
goto v___jp_461_;
}
v___jp_461_:
{
uint8_t v_decide_465_; 
v_decide_465_ = lean_nat_dec_eq(v_snd_460_, v_snd_463_);
lean_dec(v_snd_463_);
lean_dec(v_snd_460_);
if (v_decide_465_ == 0)
{
lean_object* v___x_466_; 
lean_dec_ref(v_acc_457_);
lean_inc(v_err_464_);
v___x_466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_466_, 0, v_pos_462_);
lean_ctor_set(v___x_466_, 1, v_err_464_);
return v___x_466_;
}
else
{
lean_object* v___x_467_; 
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v_pos_462_);
lean_ctor_set(v___x_467_, 1, v_acc_457_);
return v___x_467_;
}
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_491_; lean_object* v___x_492_; 
v___x_491_ = 60;
v___x_492_ = lean_box_uint32(v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0___boxed__const__1;
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__1(void){
_start:
{
uint32_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = 62;
v___x_496_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_497_ = lean_string_push(v___x_496_, v___x_495_);
return v___x_497_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_498_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__1, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__1_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__1);
v___x_499_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_500_ = lean_string_append(v___x_499_, v___x_498_);
return v___x_500_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__3(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_502_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2);
v___x_503_ = lean_string_append(v___x_502_, v___x_501_);
return v___x_503_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__4(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__3);
v___x_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(lean_object* v_a_506_){
_start:
{
lean_object* v___y_508_; lean_object* v_pos_512_; lean_object* v_res_513_; lean_object* v_fst_567_; lean_object* v_snd_568_; lean_object* v___x_569_; uint8_t v_decide_570_; 
v_fst_567_ = lean_ctor_get(v_a_506_, 0);
v_snd_568_ = lean_ctor_get(v_a_506_, 1);
v___x_569_ = lean_string_utf8_byte_size(v_fst_567_);
v_decide_570_ = lean_nat_dec_eq(v_snd_568_, v___x_569_);
if (v_decide_570_ == 0)
{
uint32_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = lean_string_utf8_get_fast(v_fst_567_, v_snd_568_);
v___x_572_ = lean_box_uint32(v___x_571_);
v___x_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
v_pos_512_ = v_a_506_;
v_res_513_ = v___x_573_;
goto v___jp_511_;
}
else
{
lean_object* v___x_574_; 
v___x_574_ = lean_box(0);
v_pos_512_ = v_a_506_;
v_res_513_ = v___x_574_;
goto v___jp_511_;
}
v___jp_507_:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_box(0);
v___x_510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_510_, 0, v___y_508_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
return v___x_510_;
}
v___jp_511_:
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0);
v___x_515_ = l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_res_513_, v___x_514_);
lean_dec(v_res_513_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_517_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1(v___x_516_, v_pos_512_);
return v___x_517_;
}
else
{
lean_object* v_fst_518_; lean_object* v_snd_519_; lean_object* v___x_520_; uint8_t v_decide_521_; 
v_fst_518_ = lean_ctor_get(v_pos_512_, 0);
v_snd_519_ = lean_ctor_get(v_pos_512_, 1);
v___x_520_ = lean_string_utf8_byte_size(v_fst_518_);
v_decide_521_ = lean_nat_dec_eq(v_snd_519_, v___x_520_);
if (v_decide_521_ == 0)
{
if (v___x_515_ == 0)
{
v___y_508_ = v_pos_512_;
goto v___jp_507_;
}
else
{
lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_564_; 
lean_inc(v_snd_519_);
lean_inc(v_fst_518_);
v_isSharedCheck_564_ = !lean_is_exclusive(v_pos_512_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; lean_object* v_unused_566_; 
v_unused_565_ = lean_ctor_get(v_pos_512_, 1);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v_pos_512_, 0);
lean_dec(v_unused_566_);
v___x_523_ = v_pos_512_;
v_isShared_524_ = v_isSharedCheck_564_;
goto v_resetjp_522_;
}
else
{
lean_dec(v_pos_512_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_564_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_525_ = lean_string_utf8_next_fast(v_fst_518_, v_snd_519_);
lean_dec(v_snd_519_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v___x_525_);
v___x_527_ = v___x_523_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_fst_518_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v___x_525_);
v___x_527_ = v_reuseFailAlloc_563_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; 
v___x_528_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName(v___x_527_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_pos_529_; lean_object* v_res_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_562_; 
v_pos_529_ = lean_ctor_get(v___x_528_, 0);
v_res_530_ = lean_ctor_get(v___x_528_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_562_ == 0)
{
v___x_532_ = v___x_528_;
v_isShared_533_ = v_isSharedCheck_562_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_res_530_);
lean_inc(v_pos_529_);
lean_dec(v___x_528_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_562_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_fst_534_; lean_object* v_snd_535_; lean_object* v___x_536_; uint8_t v_decide_537_; 
v_fst_534_ = lean_ctor_get(v_pos_529_, 0);
v_snd_535_ = lean_ctor_get(v_pos_529_, 1);
v___x_536_ = lean_string_utf8_byte_size(v_fst_534_);
v_decide_537_ = lean_nat_dec_eq(v_snd_535_, v___x_536_);
if (v_decide_537_ == 0)
{
uint32_t v___x_538_; uint32_t v_c_539_; uint8_t v___x_540_; 
v___x_538_ = 62;
v_c_539_ = lean_string_utf8_get_fast(v_fst_534_, v_snd_535_);
v___x_540_ = lean_uint32_dec_eq(v_c_539_, v___x_538_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_543_; 
lean_dec(v_res_530_);
v___x_541_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__4);
if (v_isShared_533_ == 0)
{
lean_ctor_set_tag(v___x_532_, 1);
lean_ctor_set(v___x_532_, 1, v___x_541_);
v___x_543_ = v___x_532_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_pos_529_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
else
{
lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_555_; 
lean_inc(v_snd_535_);
lean_inc(v_fst_534_);
v_isSharedCheck_555_ = !lean_is_exclusive(v_pos_529_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; lean_object* v_unused_557_; 
v_unused_556_ = lean_ctor_get(v_pos_529_, 1);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_pos_529_, 0);
lean_dec(v_unused_557_);
v___x_546_ = v_pos_529_;
v_isShared_547_ = v_isSharedCheck_555_;
goto v_resetjp_545_;
}
else
{
lean_dec(v_pos_529_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_555_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v_it_x27_550_; 
v___x_548_ = lean_string_utf8_next_fast(v_fst_534_, v_snd_535_);
lean_dec(v_snd_535_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v___x_548_);
v_it_x27_550_ = v___x_546_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_fst_534_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v___x_548_);
v_it_x27_550_ = v_reuseFailAlloc_554_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_552_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v_it_x27_550_);
v___x_552_ = v___x_532_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_it_x27_550_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_res_530_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
else
{
lean_object* v___x_558_; lean_object* v___x_560_; 
lean_dec(v_res_530_);
v___x_558_ = lean_box(0);
if (v_isShared_533_ == 0)
{
lean_ctor_set_tag(v___x_532_, 1);
lean_ctor_set(v___x_532_, 1, v___x_558_);
v___x_560_ = v___x_532_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_pos_529_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
else
{
return v___x_528_;
}
}
}
}
}
else
{
v___y_508_ = v_pos_512_;
goto v___jp_507_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1(lean_object* v___x_575_, lean_object* v_x_576_){
_start:
{
uint8_t v___x_577_; 
v___x_577_ = lean_int_dec_le(v_x_576_, v___x_575_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1___boxed(lean_object* v___x_578_, lean_object* v_x_579_){
_start:
{
uint8_t v_res_580_; lean_object* v_r_581_; 
v_res_580_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1(v___x_578_, v_x_579_);
lean_dec(v_x_579_);
lean_dec(v___x_578_);
v_r_581_ = lean_box(v_res_580_);
return v_r_581_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2(void){
_start:
{
uint32_t v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = 77;
v___x_585_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_586_ = lean_string_push(v___x_585_, v___x_584_);
return v___x_586_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2);
v___x_588_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_589_ = lean_string_append(v___x_588_, v___x_587_);
return v___x_589_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_591_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3);
v___x_592_ = lean_string_append(v___x_591_, v___x_590_);
return v___x_592_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4);
v___x_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
return v___x_594_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_unsigned_to_nat(7u);
v___x_596_ = lean_nat_to_int(v___x_595_);
return v___x_596_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_unsigned_to_nat(5u);
v___x_598_ = lean_nat_to_int(v___x_597_);
return v___x_598_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8(void){
_start:
{
lean_object* v___x_599_; lean_object* v___f_600_; 
v___x_599_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7);
v___f_600_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1___boxed), 2, 1);
lean_closure_set(v___f_600_, 0, v___x_599_);
return v___f_600_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10(void){
_start:
{
uint32_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = 46;
v___x_603_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_604_ = lean_string_push(v___x_603_, v___x_602_);
return v___x_604_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10);
v___x_606_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_607_ = lean_string_append(v___x_606_, v___x_605_);
return v___x_607_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__12(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_609_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11);
v___x_610_ = lean_string_append(v___x_609_, v___x_608_);
return v___x_610_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__13(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__12, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__12_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__12);
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__14(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_unsigned_to_nat(12u);
v___x_614_ = lean_nat_to_int(v___x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec(lean_object* v_a_616_){
_start:
{
lean_object* v___y_618_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; uint8_t v___y_627_; lean_object* v___y_638_; lean_object* v_fst_641_; lean_object* v_snd_642_; lean_object* v___x_643_; uint8_t v_decide_644_; 
v_fst_641_ = lean_ctor_get(v_a_616_, 0);
v_snd_642_ = lean_ctor_get(v_a_616_, 1);
v___x_643_ = lean_string_utf8_byte_size(v_fst_641_);
v_decide_644_ = lean_nat_dec_eq(v_snd_642_, v___x_643_);
if (v_decide_644_ == 0)
{
uint32_t v___x_645_; uint32_t v_c_646_; uint8_t v___x_647_; 
v___x_645_ = 77;
v_c_646_ = lean_string_utf8_get_fast(v_fst_641_, v_snd_642_);
v___x_647_ = lean_uint32_dec_eq(v_c_646_, v___x_645_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5);
v___x_649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_649_, 0, v_a_616_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
return v___x_649_;
}
else
{
lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_810_; 
lean_inc(v_snd_642_);
lean_inc(v_fst_641_);
v_isSharedCheck_810_ = !lean_is_exclusive(v_a_616_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; lean_object* v_unused_812_; 
v_unused_811_ = lean_ctor_get(v_a_616_, 1);
lean_dec(v_unused_811_);
v_unused_812_ = lean_ctor_get(v_a_616_, 0);
lean_dec(v_unused_812_);
v___x_651_ = v_a_616_;
v_isShared_652_ = v_isSharedCheck_810_;
goto v_resetjp_650_;
}
else
{
lean_dec(v_a_616_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_810_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___f_654_; lean_object* v___x_655_; lean_object* v_it_x27_657_; 
v___x_653_ = lean_box(v___x_647_);
v___f_654_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_654_, 0, v___x_653_);
v___x_655_ = lean_string_utf8_next_fast(v_fst_641_, v_snd_642_);
lean_dec(v_snd_642_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 1, v___x_655_);
v_it_x27_657_ = v___x_651_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_fst_641_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v___x_655_);
v_it_x27_657_ = v_reuseFailAlloc_809_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; uint32_t v___y_673_; lean_object* v___y_674_; uint8_t v___y_675_; lean_object* v___y_706_; lean_object* v_pos_707_; lean_object* v_fst_708_; lean_object* v_snd_709_; lean_object* v_res_710_; lean_object* v_pos_719_; lean_object* v_res_720_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_658_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_765_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__14, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__14_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__14);
v___x_766_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__15));
v___x_767_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_658_, v___x_765_, v___x_766_, v___f_654_, v_it_x27_657_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_pos_768_; lean_object* v_res_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_797_; 
v_pos_768_ = lean_ctor_get(v___x_767_, 0);
v_res_769_ = lean_ctor_get(v___x_767_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_797_ == 0)
{
v___x_771_ = v___x_767_;
v_isShared_772_ = v_isSharedCheck_797_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_res_769_);
lean_inc(v_pos_768_);
lean_dec(v___x_767_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_797_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v_fst_778_; lean_object* v_snd_779_; lean_object* v___x_780_; uint8_t v_decide_781_; 
v_fst_778_ = lean_ctor_get(v_pos_768_, 0);
v_snd_779_ = lean_ctor_get(v_pos_768_, 1);
v___x_780_ = lean_string_utf8_byte_size(v_fst_778_);
v_decide_781_ = lean_nat_dec_eq(v_snd_779_, v___x_780_);
if (v_decide_781_ == 0)
{
if (v___x_647_ == 0)
{
lean_dec(v_res_769_);
goto v___jp_773_;
}
else
{
uint32_t v___x_782_; uint32_t v_c_783_; uint8_t v___x_784_; 
lean_del_object(v___x_771_);
v___x_782_ = 46;
v_c_783_ = lean_string_utf8_get_fast(v_fst_778_, v_snd_779_);
v___x_784_ = lean_uint32_dec_eq(v_c_783_, v___x_782_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; 
lean_dec(v_res_769_);
v___x_785_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__13, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__13_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__13);
v___x_786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_786_, 0, v_pos_768_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
return v___x_786_;
}
else
{
lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_794_; 
lean_inc(v_snd_779_);
lean_inc(v_fst_778_);
v_isSharedCheck_794_ = !lean_is_exclusive(v_pos_768_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; lean_object* v_unused_796_; 
v_unused_795_ = lean_ctor_get(v_pos_768_, 1);
lean_dec(v_unused_795_);
v_unused_796_ = lean_ctor_get(v_pos_768_, 0);
lean_dec(v_unused_796_);
v___x_788_ = v_pos_768_;
v_isShared_789_ = v_isSharedCheck_794_;
goto v_resetjp_787_;
}
else
{
lean_dec(v_pos_768_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_794_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v_it_x27_792_; 
v___x_790_ = lean_string_utf8_next_fast(v_fst_778_, v_snd_779_);
lean_dec(v_snd_779_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v___x_790_);
v_it_x27_792_ = v___x_788_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_fst_778_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v___x_790_);
v_it_x27_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
v_pos_719_ = v_it_x27_792_;
v_res_720_ = v_res_769_;
goto v___jp_718_;
}
}
}
}
}
else
{
lean_dec(v_res_769_);
goto v___jp_773_;
}
v___jp_773_:
{
lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_774_ = lean_box(0);
if (v_isShared_772_ == 0)
{
lean_ctor_set_tag(v___x_771_, 1);
lean_ctor_set(v___x_771_, 1, v___x_774_);
v___x_776_ = v___x_771_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_pos_768_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_pos_798_; lean_object* v_res_799_; 
v_pos_798_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_pos_798_);
v_res_799_ = lean_ctor_get(v___x_767_, 1);
lean_inc(v_res_799_);
lean_dec_ref_known(v___x_767_, 2);
v_pos_719_ = v_pos_798_;
v_res_720_ = v_res_799_;
goto v___jp_718_;
}
else
{
lean_object* v_pos_800_; lean_object* v_err_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
v_pos_800_ = lean_ctor_get(v___x_767_, 0);
v_err_801_ = lean_ctor_get(v___x_767_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_767_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_err_801_);
lean_inc(v_pos_800_);
lean_dec(v___x_767_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_pos_800_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_err_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
v___jp_659_:
{
uint8_t v___x_666_; 
v___x_666_ = lean_int_dec_le(v___x_658_, v___y_665_);
if (v___x_666_ == 0)
{
lean_dec(v___y_661_);
v___y_622_ = v___y_660_;
v___y_623_ = v___y_665_;
v___y_624_ = v___y_662_;
v___y_625_ = v___y_663_;
v___y_626_ = v___y_664_;
v___y_627_ = v___x_666_;
goto v___jp_621_;
}
else
{
uint8_t v___x_667_; 
v___x_667_ = lean_int_dec_le(v___y_665_, v___y_661_);
lean_dec(v___y_661_);
v___y_622_ = v___y_660_;
v___y_623_ = v___y_665_;
v___y_624_ = v___y_662_;
v___y_625_ = v___y_663_;
v___y_626_ = v___y_664_;
v___y_627_ = v___x_667_;
goto v___jp_621_;
}
}
v___jp_668_:
{
if (v___y_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; 
lean_dec(v___y_674_);
lean_dec(v___y_672_);
lean_dec(v___y_671_);
lean_dec(v___y_669_);
v___x_676_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__3));
v___x_677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_677_, 0, v___y_670_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
return v___x_677_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v_fst_683_; lean_object* v_snd_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_704_; 
lean_dec_ref(v___y_670_);
v___x_678_ = lean_string_utf8_next_fast(v___y_674_, v___y_669_);
lean_dec(v___y_669_);
v___x_679_ = lean_uint32_to_nat(v___y_673_);
v___x_680_ = lean_unsigned_to_nat(48u);
v___x_681_ = lean_nat_sub(v___x_679_, v___x_680_);
lean_dec(v___x_679_);
v___x_682_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v___y_674_, v___x_678_, v___x_681_);
v_fst_683_ = lean_ctor_get(v___x_682_, 0);
v_snd_684_ = lean_ctor_get(v___x_682_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_704_ == 0)
{
v___x_686_ = v___x_682_;
v_isShared_687_ = v_isSharedCheck_704_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_snd_684_);
lean_inc(v_fst_683_);
lean_dec(v___x_682_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_704_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___y_674_);
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___y_674_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_snd_684_);
v___x_689_ = v_reuseFailAlloc_703_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_690_ = lean_unsigned_to_nat(6u);
v___x_691_ = lean_nat_dec_lt(v___x_690_, v_fst_683_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_692_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6);
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = lean_nat_dec_eq(v_fst_683_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; 
lean_inc(v_fst_683_);
v___x_695_ = lean_nat_to_int(v_fst_683_);
v___y_660_ = v___x_689_;
v___y_661_ = v___x_692_;
v___y_662_ = v_fst_683_;
v___y_663_ = v___y_671_;
v___y_664_ = v___y_672_;
v___y_665_ = v___x_695_;
goto v___jp_659_;
}
else
{
v___y_660_ = v___x_689_;
v___y_661_ = v___x_692_;
v___y_662_ = v_fst_683_;
v___y_663_ = v___y_671_;
v___y_664_ = v___y_672_;
v___y_665_ = v___x_692_;
goto v___jp_659_;
}
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
lean_dec(v___y_672_);
lean_dec(v___y_671_);
v___x_696_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0));
v___x_697_ = l_Nat_reprFast(v_fst_683_);
v___x_698_ = lean_string_append(v___x_696_, v___x_697_);
lean_dec_ref(v___x_697_);
v___x_699_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1));
v___x_700_ = lean_string_append(v___x_698_, v___x_699_);
v___x_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
v___x_702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_689_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
return v___x_702_;
}
}
}
}
}
v___jp_705_:
{
lean_object* v___x_711_; uint8_t v_decide_712_; 
v___x_711_ = lean_string_utf8_byte_size(v_fst_708_);
v_decide_712_ = lean_nat_dec_eq(v_snd_709_, v___x_711_);
if (v_decide_712_ == 0)
{
if (v___x_647_ == 0)
{
lean_dec(v_res_710_);
lean_dec(v_snd_709_);
lean_dec(v_fst_708_);
lean_dec(v___y_706_);
v___y_618_ = v_pos_707_;
goto v___jp_617_;
}
else
{
uint32_t v_c_713_; uint32_t v___x_714_; uint8_t v___x_715_; 
v_c_713_ = lean_string_utf8_get_fast(v_fst_708_, v_snd_709_);
v___x_714_ = 48;
v___x_715_ = lean_uint32_dec_le(v___x_714_, v_c_713_);
if (v___x_715_ == 0)
{
v___y_669_ = v_snd_709_;
v___y_670_ = v_pos_707_;
v___y_671_ = v_res_710_;
v___y_672_ = v___y_706_;
v___y_673_ = v_c_713_;
v___y_674_ = v_fst_708_;
v___y_675_ = v___x_715_;
goto v___jp_668_;
}
else
{
uint32_t v___x_716_; uint8_t v___x_717_; 
v___x_716_ = 57;
v___x_717_ = lean_uint32_dec_le(v_c_713_, v___x_716_);
v___y_669_ = v_snd_709_;
v___y_670_ = v_pos_707_;
v___y_671_ = v_res_710_;
v___y_672_ = v___y_706_;
v___y_673_ = v_c_713_;
v___y_674_ = v_fst_708_;
v___y_675_ = v___x_717_;
goto v___jp_668_;
}
}
}
else
{
lean_dec(v_res_710_);
lean_dec(v_snd_709_);
lean_dec(v_fst_708_);
lean_dec(v___y_706_);
v___y_618_ = v_pos_707_;
goto v___jp_617_;
}
}
v___jp_718_:
{
lean_object* v___x_721_; lean_object* v___f_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_721_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7);
v___f_722_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8);
v___x_723_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9));
v___x_724_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_658_, v___x_721_, v___x_723_, v___f_722_, v_pos_719_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_pos_725_; lean_object* v_res_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_751_; 
v_pos_725_ = lean_ctor_get(v___x_724_, 0);
v_res_726_ = lean_ctor_get(v___x_724_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_751_ == 0)
{
v___x_728_ = v___x_724_;
v_isShared_729_ = v_isSharedCheck_751_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_res_726_);
lean_inc(v_pos_725_);
lean_dec(v___x_724_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_751_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v_fst_730_; lean_object* v_snd_731_; lean_object* v___x_732_; uint8_t v_decide_733_; 
v_fst_730_ = lean_ctor_get(v_pos_725_, 0);
v_snd_731_ = lean_ctor_get(v_pos_725_, 1);
v___x_732_ = lean_string_utf8_byte_size(v_fst_730_);
v_decide_733_ = lean_nat_dec_eq(v_snd_731_, v___x_732_);
if (v_decide_733_ == 0)
{
if (v___x_647_ == 0)
{
lean_del_object(v___x_728_);
lean_dec(v_res_726_);
lean_dec(v_res_720_);
v___y_638_ = v_pos_725_;
goto v___jp_637_;
}
else
{
uint32_t v___x_734_; uint32_t v_c_735_; uint8_t v___x_736_; 
v___x_734_ = 46;
v_c_735_ = lean_string_utf8_get_fast(v_fst_730_, v_snd_731_);
v___x_736_ = lean_uint32_dec_eq(v_c_735_, v___x_734_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_739_; 
lean_dec(v_res_726_);
lean_dec(v_res_720_);
v___x_737_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__13, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__13_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__13);
if (v_isShared_729_ == 0)
{
lean_ctor_set_tag(v___x_728_, 1);
lean_ctor_set(v___x_728_, 1, v___x_737_);
v___x_739_ = v___x_728_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_pos_725_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
else
{
lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_748_; 
lean_inc(v_snd_731_);
lean_inc(v_fst_730_);
lean_del_object(v___x_728_);
v_isSharedCheck_748_ = !lean_is_exclusive(v_pos_725_);
if (v_isSharedCheck_748_ == 0)
{
lean_object* v_unused_749_; lean_object* v_unused_750_; 
v_unused_749_ = lean_ctor_get(v_pos_725_, 1);
lean_dec(v_unused_749_);
v_unused_750_ = lean_ctor_get(v_pos_725_, 0);
lean_dec(v_unused_750_);
v___x_742_ = v_pos_725_;
v_isShared_743_ = v_isSharedCheck_748_;
goto v_resetjp_741_;
}
else
{
lean_dec(v_pos_725_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_748_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v_it_x27_746_; 
v___x_744_ = lean_string_utf8_next_fast(v_fst_730_, v_snd_731_);
lean_dec(v_snd_731_);
lean_inc(v_fst_730_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v___x_744_);
v_it_x27_746_ = v___x_742_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_fst_730_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v___x_744_);
v_it_x27_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
v___y_706_ = v_res_720_;
v_pos_707_ = v_it_x27_746_;
v_fst_708_ = v_fst_730_;
v_snd_709_ = v___x_744_;
v_res_710_ = v_res_726_;
goto v___jp_705_;
}
}
}
}
}
else
{
lean_del_object(v___x_728_);
lean_dec(v_res_726_);
lean_dec(v_res_720_);
v___y_638_ = v_pos_725_;
goto v___jp_637_;
}
}
}
else
{
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_pos_752_; lean_object* v_res_753_; lean_object* v_fst_754_; lean_object* v_snd_755_; 
v_pos_752_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_pos_752_);
v_res_753_ = lean_ctor_get(v___x_724_, 1);
lean_inc(v_res_753_);
lean_dec_ref_known(v___x_724_, 2);
v_fst_754_ = lean_ctor_get(v_pos_752_, 0);
lean_inc(v_fst_754_);
v_snd_755_ = lean_ctor_get(v_pos_752_, 1);
lean_inc(v_snd_755_);
v___y_706_ = v_res_720_;
v_pos_707_ = v_pos_752_;
v_fst_708_ = v_fst_754_;
v_snd_709_ = v_snd_755_;
v_res_710_ = v_res_753_;
goto v___jp_705_;
}
else
{
lean_object* v_pos_756_; lean_object* v_err_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec(v_res_720_);
v_pos_756_ = lean_ctor_get(v___x_724_, 0);
v_err_757_ = lean_ctor_get(v___x_724_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_724_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_err_757_);
lean_inc(v_pos_756_);
lean_dec(v___x_724_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_pos_756_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_err_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
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
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_box(0);
v___x_814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_814_, 0, v_a_616_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
return v___x_814_;
}
v___jp_617_:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_box(0);
v___x_620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_620_, 0, v___y_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
return v___x_620_;
}
v___jp_621_:
{
if (v___y_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec(v___y_626_);
lean_dec(v___y_625_);
lean_dec(v___y_623_);
v___x_628_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0));
v___x_629_ = l_Nat_reprFast(v___y_624_);
v___x_630_ = lean_string_append(v___x_628_, v___x_629_);
lean_dec_ref(v___x_629_);
v___x_631_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1));
v___x_632_ = lean_string_append(v___x_630_, v___x_631_);
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
v___x_634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_634_, 0, v___y_622_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec(v___y_624_);
v___x_635_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_635_, 0, v___y_626_);
lean_ctor_set(v___x_635_, 1, v___y_625_);
lean_ctor_set(v___x_635_, 2, v___y_623_);
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v___y_622_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
return v___x_636_;
}
}
v___jp_637_:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_box(0);
v___x_640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_640_, 0, v___y_638_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
return v___x_640_;
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__0(void){
_start:
{
uint32_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = 74;
v___x_816_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_817_ = lean_string_push(v___x_816_, v___x_815_);
return v___x_817_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__0);
v___x_819_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_820_ = lean_string_append(v___x_819_, v___x_818_);
return v___x_820_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_822_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1);
v___x_823_ = lean_string_append(v___x_822_, v___x_821_);
return v___x_823_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2);
v___x_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_unsigned_to_nat(365u);
v___x_827_ = lean_nat_to_int(v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec(lean_object* v_a_829_){
_start:
{
lean_object* v_fst_830_; lean_object* v_snd_831_; lean_object* v___x_832_; uint8_t v_decide_833_; 
v_fst_830_ = lean_ctor_get(v_a_829_, 0);
v_snd_831_ = lean_ctor_get(v_a_829_, 1);
v___x_832_ = lean_string_utf8_byte_size(v_fst_830_);
v_decide_833_ = lean_nat_dec_eq(v_snd_831_, v___x_832_);
if (v_decide_833_ == 0)
{
uint32_t v___x_834_; uint32_t v_c_835_; uint8_t v___x_836_; 
v___x_834_ = 74;
v_c_835_ = lean_string_utf8_get_fast(v_fst_830_, v_snd_831_);
v___x_836_ = lean_uint32_dec_eq(v_c_835_, v___x_834_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3);
v___x_838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_838_, 0, v_a_829_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
return v___x_838_;
}
else
{
lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_871_; 
lean_inc(v_snd_831_);
lean_inc(v_fst_830_);
v_isSharedCheck_871_ = !lean_is_exclusive(v_a_829_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; lean_object* v_unused_873_; 
v_unused_872_ = lean_ctor_get(v_a_829_, 1);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_a_829_, 0);
lean_dec(v_unused_873_);
v___x_840_ = v_a_829_;
v_isShared_841_ = v_isSharedCheck_871_;
goto v_resetjp_839_;
}
else
{
lean_dec(v_a_829_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_871_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v___f_843_; lean_object* v___x_844_; lean_object* v_it_x27_846_; 
v___x_842_ = lean_box(v___x_836_);
v___f_843_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_843_, 0, v___x_842_);
v___x_844_ = lean_string_utf8_next_fast(v_fst_830_, v_snd_831_);
lean_dec(v_snd_831_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v___x_844_);
v_it_x27_846_ = v___x_840_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_fst_830_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v___x_844_);
v_it_x27_846_ = v_reuseFailAlloc_870_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_847_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_848_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4);
v___x_849_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__5));
v___x_850_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_847_, v___x_848_, v___x_849_, v___f_843_, v_it_x27_846_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_pos_851_; lean_object* v_res_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_860_; 
v_pos_851_ = lean_ctor_get(v___x_850_, 0);
v_res_852_ = lean_ctor_get(v___x_850_, 1);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_860_ == 0)
{
v___x_854_ = v___x_850_;
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_res_852_);
lean_inc(v_pos_851_);
lean_dec(v___x_850_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v_res_852_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_856_);
v___x_858_ = v___x_854_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_pos_851_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
else
{
lean_object* v_pos_861_; lean_object* v_err_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
v_pos_861_ = lean_ctor_get(v___x_850_, 0);
v_err_862_ = lean_ctor_get(v___x_850_, 1);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_850_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_err_862_);
lean_inc(v_pos_861_);
lean_dec(v___x_850_);
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
else
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_box(0);
v___x_875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_875_, 0, v_a_829_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
return v___x_875_;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0(lean_object* v_x_876_){
_start:
{
uint8_t v___x_877_; 
v___x_877_ = 1;
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0___boxed(lean_object* v_x_878_){
_start:
{
uint8_t v_res_879_; lean_object* v_r_880_; 
v_res_879_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0(v_x_878_);
lean_dec(v_x_878_);
v_r_880_ = lean_box(v_res_879_);
return v_r_880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec(lean_object* v_a_883_){
_start:
{
lean_object* v___f_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___f_884_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__0));
v___x_885_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2);
v___x_886_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4);
v___x_887_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__1));
v___x_888_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_885_, v___x_886_, v___x_887_, v___f_884_, v_a_883_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_pos_889_; lean_object* v_res_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_898_; 
v_pos_889_ = lean_ctor_get(v___x_888_, 0);
v_res_890_ = lean_ctor_get(v___x_888_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_898_ == 0)
{
v___x_892_ = v___x_888_;
v_isShared_893_ = v_isSharedCheck_898_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_res_890_);
lean_inc(v_pos_889_);
lean_dec(v___x_888_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_898_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_894_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_894_, 0, v_res_890_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 1, v___x_894_);
v___x_896_ = v___x_892_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_pos_889_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
else
{
lean_object* v_pos_899_; lean_object* v_err_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
v_pos_899_ = lean_ctor_get(v___x_888_, 0);
v_err_900_ = lean_ctor_get(v___x_888_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_888_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_err_900_);
lean_inc(v_pos_899_);
lean_dec(v___x_888_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_pos_899_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_err_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(lean_object* v_stdOffset_908_, lean_object* v_a_909_){
_start:
{
lean_object* v_fst_910_; lean_object* v_snd_911_; lean_object* v___x_912_; uint8_t v_decide_913_; 
v_fst_910_ = lean_ctor_get(v_a_909_, 0);
v_snd_911_ = lean_ctor_get(v_a_909_, 1);
v___x_912_ = lean_string_utf8_byte_size(v_fst_910_);
v_decide_913_ = lean_nat_dec_eq(v_snd_911_, v___x_912_);
if (v_decide_913_ == 0)
{
uint32_t v___x_914_; uint32_t v___x_925_; uint8_t v___x_926_; 
v___x_914_ = lean_string_utf8_get_fast(v_fst_910_, v_snd_911_);
v___x_925_ = 48;
v___x_926_ = lean_uint32_dec_le(v___x_925_, v___x_914_);
if (v___x_926_ == 0)
{
goto v___jp_915_;
}
else
{
uint32_t v___x_927_; uint8_t v___x_928_; 
v___x_927_ = 57;
v___x_928_ = lean_uint32_dec_le(v___x_914_, v___x_927_);
if (v___x_928_ == 0)
{
goto v___jp_915_;
}
else
{
lean_object* v___x_929_; 
v___x_929_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_909_);
return v___x_929_;
}
}
v___jp_915_:
{
uint32_t v___x_916_; uint8_t v___x_917_; 
v___x_916_ = 43;
v___x_917_ = lean_uint32_dec_eq(v___x_914_, v___x_916_);
if (v___x_917_ == 0)
{
uint32_t v___x_918_; uint8_t v___x_919_; 
v___x_918_ = 45;
v___x_919_ = lean_uint32_dec_eq(v___x_914_, v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_920_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0);
v___x_921_ = lean_int_add(v_stdOffset_908_, v___x_920_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_a_909_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
return v___x_922_;
}
else
{
lean_object* v___x_923_; 
v___x_923_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_909_);
return v___x_923_;
}
}
else
{
lean_object* v___x_924_; 
v___x_924_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_909_);
return v___x_924_;
}
}
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0);
v___x_931_ = lean_int_add(v_stdOffset_908_, v___x_930_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v_a_909_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset___boxed(lean_object* v_stdOffset_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(v_stdOffset_933_, v_a_934_);
lean_dec(v_stdOffset_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSpec(lean_object* v_a_936_){
_start:
{
lean_object* v_snd_938_; lean_object* v___y_939_; lean_object* v_pos_940_; lean_object* v_snd_941_; lean_object* v___y_945_; lean_object* v_pos_946_; lean_object* v___x_962_; 
lean_inc_ref(v_a_936_);
v___x_962_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec(v_a_936_);
if (lean_obj_tag(v___x_962_) == 0)
{
if (lean_obj_tag(v___x_962_) == 0)
{
lean_dec_ref(v_a_936_);
return v___x_962_;
}
else
{
lean_object* v_pos_963_; 
v_pos_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_pos_963_);
v___y_945_ = v___x_962_;
v_pos_946_ = v_pos_963_;
goto v___jp_944_;
}
}
else
{
lean_object* v_err_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
v_err_964_ = lean_ctor_get(v___x_962_, 1);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; 
v_unused_972_ = lean_ctor_get(v___x_962_, 0);
lean_dec(v_unused_972_);
v___x_966_ = v___x_962_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_err_964_);
lean_dec(v___x_962_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
lean_inc_ref(v_a_936_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v_a_936_);
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_936_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_err_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_inc_ref(v_a_936_);
v___y_945_ = v___x_969_;
v_pos_946_ = v_a_936_;
goto v___jp_944_;
}
}
}
v___jp_937_:
{
uint8_t v_decide_942_; 
v_decide_942_ = lean_nat_dec_eq(v_snd_938_, v_snd_941_);
lean_dec(v_snd_941_);
lean_dec(v_snd_938_);
if (v_decide_942_ == 0)
{
lean_dec_ref(v_pos_940_);
return v___y_939_;
}
else
{
lean_object* v___x_943_; 
lean_dec_ref(v___y_939_);
v___x_943_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec(v_pos_940_);
return v___x_943_;
}
}
v___jp_944_:
{
lean_object* v_snd_947_; lean_object* v_snd_948_; uint8_t v_decide_949_; 
v_snd_947_ = lean_ctor_get(v_a_936_, 1);
lean_inc(v_snd_947_);
lean_dec_ref(v_a_936_);
v_snd_948_ = lean_ctor_get(v_pos_946_, 1);
lean_inc(v_snd_948_);
v_decide_949_ = lean_nat_dec_eq(v_snd_947_, v_snd_948_);
lean_dec(v_snd_947_);
if (v_decide_949_ == 0)
{
lean_dec(v_snd_948_);
lean_dec_ref(v_pos_946_);
return v___y_945_;
}
else
{
lean_object* v___x_950_; 
lean_dec_ref(v___y_945_);
lean_inc_ref(v_pos_946_);
v___x_950_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec(v_pos_946_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_dec_ref(v_pos_946_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_dec(v_snd_948_);
return v___x_950_;
}
else
{
lean_object* v_pos_951_; lean_object* v_snd_952_; 
v_pos_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_pos_951_);
v_snd_952_ = lean_ctor_get(v_pos_951_, 1);
lean_inc(v_snd_952_);
v_snd_938_ = v_snd_948_;
v___y_939_ = v___x_950_;
v_pos_940_ = v_pos_951_;
v_snd_941_ = v_snd_952_;
goto v___jp_937_;
}
}
else
{
lean_object* v_err_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
v_err_953_ = lean_ctor_get(v___x_950_, 1);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; 
v_unused_961_ = lean_ctor_get(v___x_950_, 0);
lean_dec(v_unused_961_);
v___x_955_ = v___x_950_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_err_953_);
lean_dec(v___x_950_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
lean_inc_ref(v_pos_946_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v_pos_946_);
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_pos_946_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_err_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_inc(v_snd_948_);
v_snd_938_ = v_snd_948_;
v___y_939_ = v___x_958_;
v_pos_940_ = v_pos_946_;
v_snd_941_ = v_snd_948_;
goto v___jp_937_;
}
}
}
}
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = lean_unsigned_to_nat(2u);
v___x_974_ = lean_nat_to_int(v___x_973_);
return v___x_974_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0);
v___x_976_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0);
v___x_977_ = lean_int_mul(v___x_976_, v___x_975_);
return v___x_977_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__2(void){
_start:
{
uint32_t v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = 47;
v___x_979_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_980_ = lean_string_push(v___x_979_, v___x_978_);
return v___x_980_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_981_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__2);
v___x_982_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_983_ = lean_string_append(v___x_982_, v___x_981_);
return v___x_983_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__4(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_984_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_985_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3);
v___x_986_ = lean_string_append(v___x_985_, v___x_984_);
return v___x_986_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__5(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__4);
v___x_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(uint8_t v_extended_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSpec(v_a_990_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_pos_992_; lean_object* v_res_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1037_; 
v_pos_992_ = lean_ctor_get(v___x_991_, 0);
v_res_993_ = lean_ctor_get(v___x_991_, 1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_995_ = v___x_991_;
v_isShared_996_ = v_isSharedCheck_1037_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_res_993_);
lean_inc(v_pos_992_);
lean_dec(v___x_991_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1037_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v_pos_998_; lean_object* v_res_999_; lean_object* v_fst_1004_; lean_object* v_snd_1005_; lean_object* v_pos_1007_; lean_object* v_snd_1008_; lean_object* v_err_1009_; lean_object* v___x_1013_; uint8_t v_decide_1014_; 
v_fst_1004_ = lean_ctor_get(v_pos_992_, 0);
v_snd_1005_ = lean_ctor_get(v_pos_992_, 1);
lean_inc(v_snd_1005_);
v___x_1013_ = lean_string_utf8_byte_size(v_fst_1004_);
v_decide_1014_ = lean_nat_dec_eq(v_snd_1005_, v___x_1013_);
if (v_decide_1014_ == 0)
{
uint32_t v___x_1015_; uint32_t v_c_1016_; uint8_t v___x_1017_; 
v___x_1015_ = 47;
v_c_1016_ = lean_string_utf8_get_fast(v_fst_1004_, v_snd_1005_);
v___x_1017_ = lean_uint32_dec_eq(v_c_1016_, v___x_1015_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__5);
lean_inc(v_snd_1005_);
v_pos_1007_ = v_pos_992_;
v_snd_1008_ = v_snd_1005_;
v_err_1009_ = v___x_1018_;
goto v___jp_1006_;
}
else
{
lean_object* v___x_1019_; lean_object* v_it_x27_1020_; lean_object* v___x_1021_; 
v___x_1019_ = lean_string_utf8_next_fast(v_fst_1004_, v_snd_1005_);
lean_inc(v_fst_1004_);
v_it_x27_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_1020_, 0, v_fst_1004_);
lean_ctor_set(v_it_x27_1020_, 1, v___x_1019_);
v___x_1021_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(v_it_x27_1020_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_pos_1022_; lean_object* v_res_1023_; lean_object* v___y_1025_; 
v_pos_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_pos_1022_);
v_res_1023_ = lean_ctor_get(v___x_1021_, 1);
lean_inc(v_res_1023_);
lean_dec_ref_known(v___x_1021_, 2);
if (v_extended_989_ == 0)
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_unsigned_to_nat(24u);
v___y_1025_ = v___x_1033_;
goto v___jp_1024_;
}
else
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_unsigned_to_nat(167u);
v___y_1025_ = v___x_1034_;
goto v___jp_1024_;
}
v___jp_1024_:
{
lean_object* v___x_1026_; 
v___x_1026_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(v___y_1025_, v_pos_1022_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_pos_1027_; lean_object* v_res_1028_; lean_object* v___x_1029_; 
lean_dec(v_snd_1005_);
lean_dec(v_pos_992_);
v_pos_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_pos_1027_);
v_res_1028_ = lean_ctor_get(v___x_1026_, 1);
lean_inc(v_res_1028_);
lean_dec_ref_known(v___x_1026_, 2);
v___x_1029_ = lean_int_mul(v_res_1023_, v_res_1028_);
lean_dec(v_res_1028_);
lean_dec(v_res_1023_);
v_pos_998_ = v_pos_1027_;
v_res_999_ = v___x_1029_;
goto v___jp_997_;
}
else
{
lean_dec(v_res_1023_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_pos_1030_; lean_object* v_res_1031_; 
lean_dec(v_snd_1005_);
lean_dec(v_pos_992_);
v_pos_1030_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_pos_1030_);
v_res_1031_ = lean_ctor_get(v___x_1026_, 1);
lean_inc(v_res_1031_);
lean_dec_ref_known(v___x_1026_, 2);
v_pos_998_ = v_pos_1030_;
v_res_999_ = v_res_1031_;
goto v___jp_997_;
}
else
{
lean_object* v_err_1032_; 
v_err_1032_ = lean_ctor_get(v___x_1026_, 1);
lean_inc(v_err_1032_);
lean_dec_ref_known(v___x_1026_, 2);
lean_inc(v_snd_1005_);
v_pos_1007_ = v_pos_992_;
v_snd_1008_ = v_snd_1005_;
v_err_1009_ = v_err_1032_;
goto v___jp_1006_;
}
}
}
}
else
{
lean_object* v_err_1035_; 
v_err_1035_ = lean_ctor_get(v___x_1021_, 1);
lean_inc(v_err_1035_);
lean_dec_ref_known(v___x_1021_, 2);
lean_inc(v_snd_1005_);
v_pos_1007_ = v_pos_992_;
v_snd_1008_ = v_snd_1005_;
v_err_1009_ = v_err_1035_;
goto v___jp_1006_;
}
}
}
else
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_box(0);
lean_inc(v_snd_1005_);
v_pos_1007_ = v_pos_992_;
v_snd_1008_ = v_snd_1005_;
v_err_1009_ = v___x_1036_;
goto v___jp_1006_;
}
v___jp_997_:
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1000_, 0, v_res_993_);
lean_ctor_set(v___x_1000_, 1, v_res_999_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 1, v___x_1000_);
lean_ctor_set(v___x_995_, 0, v_pos_998_);
v___x_1002_ = v___x_995_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_pos_998_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
v___jp_1006_:
{
uint8_t v_decide_1010_; 
v_decide_1010_ = lean_nat_dec_eq(v_snd_1005_, v_snd_1008_);
lean_dec(v_snd_1008_);
lean_dec(v_snd_1005_);
if (v_decide_1010_ == 0)
{
lean_object* v___x_1011_; 
lean_del_object(v___x_995_);
lean_dec(v_res_993_);
v___x_1011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1011_, 0, v_pos_1007_);
lean_ctor_set(v___x_1011_, 1, v_err_1009_);
return v___x_1011_;
}
else
{
lean_object* v___x_1012_; 
lean_dec(v_err_1009_);
v___x_1012_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1);
v_pos_998_ = v_pos_1007_;
v_res_999_ = v___x_1012_;
goto v___jp_997_;
}
}
}
}
else
{
lean_object* v_pos_1038_; lean_object* v_err_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
v_pos_1038_ = lean_ctor_get(v___x_991_, 0);
v_err_1039_ = lean_ctor_get(v___x_991_, 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_991_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_err_1039_);
lean_inc(v_pos_1038_);
lean_dec(v___x_991_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_pos_1038_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_err_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___boxed(lean_object* v_extended_1047_, lean_object* v_a_1048_){
_start:
{
uint8_t v_extended_boxed_1049_; lean_object* v_res_1050_; 
v_extended_boxed_1049_ = lean_unbox(v_extended_1047_);
v_res_1050_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_boxed_1049_, v_a_1048_);
return v_res_1050_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = 44;
v___x_1052_ = lean_box_uint32(v___x_1051_);
return v___x_1052_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0___boxed__const__1;
v___x_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP(uint8_t v_extended_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(v_a_1059_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_pos_1061_; lean_object* v_res_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1250_; 
v_pos_1061_ = lean_ctor_get(v___x_1060_, 0);
v_res_1062_ = lean_ctor_get(v___x_1060_, 1);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1064_ = v___x_1060_;
v_isShared_1065_ = v_isSharedCheck_1250_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_res_1062_);
lean_inc(v_pos_1061_);
lean_dec(v___x_1060_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1250_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1066_ = lean_string_utf8_byte_size(v_res_1062_);
v___x_1067_ = lean_unsigned_to_nat(0u);
v___x_1068_ = lean_nat_dec_eq(v___x_1066_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; 
v___x_1069_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_pos_1061_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_pos_1070_; lean_object* v_res_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1236_; 
v_pos_1070_ = lean_ctor_get(v___x_1069_, 0);
v_res_1071_ = lean_ctor_get(v___x_1069_, 1);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1073_ = v___x_1069_;
v_isShared_1074_ = v_isSharedCheck_1236_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_res_1071_);
lean_inc(v_pos_1070_);
lean_dec(v___x_1069_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1236_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; uint32_t v___y_1082_; lean_object* v___y_1122_; uint8_t v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; uint32_t v___y_1128_; uint8_t v___y_1129_; uint8_t v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v_pos_1164_; lean_object* v_res_1165_; lean_object* v___y_1179_; lean_object* v___y_1180_; uint8_t v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v_fst_1229_; lean_object* v_snd_1230_; lean_object* v___x_1231_; uint8_t v_decide_1232_; 
v_fst_1229_ = lean_ctor_get(v_pos_1070_, 0);
v_snd_1230_ = lean_ctor_get(v_pos_1070_, 1);
v___x_1231_ = lean_string_utf8_byte_size(v_fst_1229_);
v_decide_1232_ = lean_nat_dec_eq(v_snd_1230_, v___x_1231_);
if (v_decide_1232_ == 0)
{
goto v___jp_1188_;
}
else
{
if (v___x_1068_ == 0)
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_del_object(v___x_1073_);
lean_del_object(v___x_1064_);
v___x_1233_ = lean_box(0);
v___x_1234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1234_, 0, v_res_1062_);
lean_ctor_set(v___x_1234_, 1, v_res_1071_);
lean_ctor_set(v___x_1234_, 2, v___x_1233_);
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v_pos_1070_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
return v___x_1235_;
}
else
{
goto v___jp_1188_;
}
}
v___jp_1075_:
{
uint32_t v_c_1083_; uint8_t v___x_1084_; 
v_c_1083_ = lean_string_utf8_get_fast(v___y_1080_, v___y_1076_);
v___x_1084_ = lean_uint32_dec_eq(v_c_1083_, v___y_1082_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec(v___y_1076_);
lean_dec(v_res_1071_);
lean_dec(v_res_1062_);
v___x_1085_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_1086_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_1087_ = lean_string_push(v___x_1086_, v___y_1082_);
v___x_1088_ = lean_string_append(v___x_1085_, v___x_1087_);
lean_dec_ref(v___x_1087_);
v___x_1089_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_1090_ = lean_string_append(v___x_1088_, v___x_1089_);
v___x_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set_tag(v___x_1073_, 1);
lean_ctor_set(v___x_1073_, 1, v___x_1091_);
lean_ctor_set(v___x_1073_, 0, v___y_1077_);
v___x_1093_ = v___x_1073_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___y_1077_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
else
{
lean_object* v___x_1095_; lean_object* v_it_x27_1096_; lean_object* v___x_1097_; 
lean_dec_ref(v___y_1077_);
lean_del_object(v___x_1073_);
v___x_1095_ = lean_string_utf8_next_fast(v___y_1080_, v___y_1076_);
lean_dec(v___y_1076_);
v_it_x27_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_1096_, 0, v___y_1080_);
lean_ctor_set(v_it_x27_1096_, 1, v___x_1095_);
v___x_1097_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_1058_, v_it_x27_1096_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_pos_1098_; lean_object* v_res_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1111_; 
v_pos_1098_ = lean_ctor_get(v___x_1097_, 0);
v_res_1099_ = lean_ctor_get(v___x_1097_, 1);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1101_ = v___x_1097_;
v_isShared_1102_ = v_isSharedCheck_1111_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_res_1099_);
lean_inc(v_pos_1098_);
lean_dec(v___x_1097_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1111_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___y_1081_);
v___x_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_res_1099_);
v___x_1105_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1105_, 0, v___y_1079_);
lean_ctor_set(v___x_1105_, 1, v___y_1078_);
lean_ctor_set(v___x_1105_, 2, v___x_1103_);
lean_ctor_set(v___x_1105_, 3, v___x_1104_);
v___x_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
v___x_1107_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1107_, 0, v_res_1062_);
lean_ctor_set(v___x_1107_, 1, v_res_1071_);
lean_ctor_set(v___x_1107_, 2, v___x_1106_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 1, v___x_1107_);
v___x_1109_ = v___x_1101_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_pos_1098_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
else
{
lean_object* v_pos_1112_; lean_object* v_err_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec_ref(v___y_1081_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec(v_res_1071_);
lean_dec(v_res_1062_);
v_pos_1112_ = lean_ctor_get(v___x_1097_, 0);
v_err_1113_ = lean_ctor_get(v___x_1097_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1097_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_err_1113_);
lean_inc(v_pos_1112_);
lean_dec(v___x_1097_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_pos_1112_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_err_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
v___jp_1121_:
{
if (v___y_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
lean_dec(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_del_object(v___x_1073_);
lean_dec(v_res_1071_);
lean_dec(v_res_1062_);
v___x_1130_ = lean_box(0);
if (v_isShared_1065_ == 0)
{
lean_ctor_set_tag(v___x_1064_, 1);
lean_ctor_set(v___x_1064_, 1, v___x_1130_);
lean_ctor_set(v___x_1064_, 0, v___y_1122_);
v___x_1132_ = v___x_1064_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___y_1122_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
else
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec_ref(v___y_1122_);
lean_del_object(v___x_1064_);
v___x_1134_ = lean_string_utf8_next_fast(v___y_1127_, v___y_1126_);
lean_dec(v___y_1126_);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___y_1127_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_1058_, v___x_1135_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_pos_1137_; lean_object* v_res_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1150_; 
v_pos_1137_ = lean_ctor_get(v___x_1136_, 0);
v_res_1138_ = lean_ctor_get(v___x_1136_, 1);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1140_ = v___x_1136_;
v_isShared_1141_ = v_isSharedCheck_1150_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_res_1138_);
lean_inc(v_pos_1137_);
lean_dec(v___x_1136_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1150_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v_fst_1142_; lean_object* v_snd_1143_; lean_object* v___x_1144_; uint8_t v_decide_1145_; 
v_fst_1142_ = lean_ctor_get(v_pos_1137_, 0);
v_snd_1143_ = lean_ctor_get(v_pos_1137_, 1);
v___x_1144_ = lean_string_utf8_byte_size(v_fst_1142_);
v_decide_1145_ = lean_nat_dec_eq(v_snd_1143_, v___x_1144_);
if (v_decide_1145_ == 0)
{
lean_inc(v_snd_1143_);
lean_inc(v_fst_1142_);
lean_del_object(v___x_1140_);
v___y_1076_ = v_snd_1143_;
v___y_1077_ = v_pos_1137_;
v___y_1078_ = v___y_1124_;
v___y_1079_ = v___y_1125_;
v___y_1080_ = v_fst_1142_;
v___y_1081_ = v_res_1138_;
v___y_1082_ = v___y_1128_;
goto v___jp_1075_;
}
else
{
if (v___y_1123_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
lean_dec(v_res_1138_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_del_object(v___x_1073_);
lean_dec(v_res_1071_);
lean_dec(v_res_1062_);
v___x_1146_ = lean_box(0);
if (v_isShared_1141_ == 0)
{
lean_ctor_set_tag(v___x_1140_, 1);
lean_ctor_set(v___x_1140_, 1, v___x_1146_);
v___x_1148_ = v___x_1140_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_pos_1137_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
else
{
lean_inc(v_snd_1143_);
lean_inc(v_fst_1142_);
lean_del_object(v___x_1140_);
v___y_1076_ = v_snd_1143_;
v___y_1077_ = v_pos_1137_;
v___y_1078_ = v___y_1124_;
v___y_1079_ = v___y_1125_;
v___y_1080_ = v_fst_1142_;
v___y_1081_ = v_res_1138_;
v___y_1082_ = v___y_1128_;
goto v___jp_1075_;
}
}
}
}
else
{
lean_object* v_pos_1151_; lean_object* v_err_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_del_object(v___x_1073_);
lean_dec(v_res_1071_);
lean_dec(v_res_1062_);
v_pos_1151_ = lean_ctor_get(v___x_1136_, 0);
v_err_1152_ = lean_ctor_get(v___x_1136_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1136_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_err_1152_);
lean_inc(v_pos_1151_);
lean_dec(v___x_1136_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_pos_1151_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_err_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
v___jp_1160_:
{
uint32_t v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1166_ = 44;
v___x_1167_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0);
v___x_1168_ = l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_res_1165_, v___x_1167_);
lean_dec(v_res_1165_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_del_object(v___x_1073_);
lean_del_object(v___x_1064_);
v___x_1169_ = lean_box(0);
v___x_1170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1170_, 0, v___y_1163_);
lean_ctor_set(v___x_1170_, 1, v___y_1162_);
lean_ctor_set(v___x_1170_, 2, v___x_1169_);
lean_ctor_set(v___x_1170_, 3, v___x_1169_);
v___x_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
v___x_1172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1172_, 0, v_res_1062_);
lean_ctor_set(v___x_1172_, 1, v_res_1071_);
lean_ctor_set(v___x_1172_, 2, v___x_1171_);
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v_pos_1164_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
return v___x_1173_;
}
else
{
lean_object* v_fst_1174_; lean_object* v_snd_1175_; lean_object* v___x_1176_; uint8_t v_decide_1177_; 
v_fst_1174_ = lean_ctor_get(v_pos_1164_, 0);
lean_inc(v_fst_1174_);
v_snd_1175_ = lean_ctor_get(v_pos_1164_, 1);
lean_inc(v_snd_1175_);
v___x_1176_ = lean_string_utf8_byte_size(v_fst_1174_);
v_decide_1177_ = lean_nat_dec_eq(v_snd_1175_, v___x_1176_);
if (v_decide_1177_ == 0)
{
v___y_1122_ = v_pos_1164_;
v___y_1123_ = v___y_1161_;
v___y_1124_ = v___y_1162_;
v___y_1125_ = v___y_1163_;
v___y_1126_ = v_snd_1175_;
v___y_1127_ = v_fst_1174_;
v___y_1128_ = v___x_1166_;
v___y_1129_ = v___x_1168_;
goto v___jp_1121_;
}
else
{
v___y_1122_ = v_pos_1164_;
v___y_1123_ = v___y_1161_;
v___y_1124_ = v___y_1162_;
v___y_1125_ = v___y_1163_;
v___y_1126_ = v_snd_1175_;
v___y_1127_ = v_fst_1174_;
v___y_1128_ = v___x_1166_;
v___y_1129_ = v___y_1161_;
goto v___jp_1121_;
}
}
}
v___jp_1178_:
{
uint32_t v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = lean_string_utf8_get_fast(v___y_1182_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec(v___y_1182_);
v___x_1186_ = lean_box_uint32(v___x_1185_);
v___x_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
v___y_1161_ = v___y_1181_;
v___y_1162_ = v___y_1183_;
v___y_1163_ = v___y_1184_;
v_pos_1164_ = v___y_1179_;
v_res_1165_ = v___x_1187_;
goto v___jp_1160_;
}
v___jp_1188_:
{
lean_object* v___x_1189_; 
v___x_1189_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(v_pos_1070_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_pos_1190_; lean_object* v_res_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1219_; 
v_pos_1190_ = lean_ctor_get(v___x_1189_, 0);
v_res_1191_ = lean_ctor_get(v___x_1189_, 1);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1193_ = v___x_1189_;
v_isShared_1194_ = v_isSharedCheck_1219_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_res_1191_);
lean_inc(v_pos_1190_);
lean_dec(v___x_1189_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1219_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = lean_string_utf8_byte_size(v_res_1191_);
v___x_1196_ = lean_nat_dec_eq(v___x_1195_, v___x_1067_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; 
lean_del_object(v___x_1193_);
v___x_1197_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(v_res_1071_, v_pos_1190_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_pos_1198_; lean_object* v_res_1199_; lean_object* v_fst_1200_; lean_object* v_snd_1201_; lean_object* v___x_1202_; uint8_t v_decide_1203_; 
v_pos_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_pos_1198_);
v_res_1199_ = lean_ctor_get(v___x_1197_, 1);
lean_inc(v_res_1199_);
lean_dec_ref_known(v___x_1197_, 2);
v_fst_1200_ = lean_ctor_get(v_pos_1198_, 0);
v_snd_1201_ = lean_ctor_get(v_pos_1198_, 1);
v___x_1202_ = lean_string_utf8_byte_size(v_fst_1200_);
v_decide_1203_ = lean_nat_dec_eq(v_snd_1201_, v___x_1202_);
if (v_decide_1203_ == 0)
{
lean_inc(v_snd_1201_);
lean_inc(v_fst_1200_);
v___y_1179_ = v_pos_1198_;
v___y_1180_ = v_snd_1201_;
v___y_1181_ = v___x_1196_;
v___y_1182_ = v_fst_1200_;
v___y_1183_ = v_res_1199_;
v___y_1184_ = v_res_1191_;
goto v___jp_1178_;
}
else
{
if (v___x_1196_ == 0)
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_box(0);
v___y_1161_ = v___x_1196_;
v___y_1162_ = v_res_1199_;
v___y_1163_ = v_res_1191_;
v_pos_1164_ = v_pos_1198_;
v_res_1165_ = v___x_1204_;
goto v___jp_1160_;
}
else
{
lean_inc(v_snd_1201_);
lean_inc(v_fst_1200_);
v___y_1179_ = v_pos_1198_;
v___y_1180_ = v_snd_1201_;
v___y_1181_ = v___x_1196_;
v___y_1182_ = v_fst_1200_;
v___y_1183_ = v_res_1199_;
v___y_1184_ = v_res_1191_;
goto v___jp_1178_;
}
}
}
else
{
lean_object* v_pos_1205_; lean_object* v_err_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec(v_res_1191_);
lean_del_object(v___x_1073_);
lean_dec(v_res_1071_);
lean_del_object(v___x_1064_);
lean_dec(v_res_1062_);
v_pos_1205_ = lean_ctor_get(v___x_1197_, 0);
v_err_1206_ = lean_ctor_get(v___x_1197_, 1);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1197_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_err_1206_);
lean_inc(v_pos_1205_);
lean_dec(v___x_1197_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_pos_1205_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_err_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
lean_dec(v_res_1191_);
lean_del_object(v___x_1073_);
lean_del_object(v___x_1064_);
v___x_1214_ = lean_box(0);
v___x_1215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1215_, 0, v_res_1062_);
lean_ctor_set(v___x_1215_, 1, v_res_1071_);
lean_ctor_set(v___x_1215_, 2, v___x_1214_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v___x_1215_);
v___x_1217_ = v___x_1193_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_pos_1190_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
else
{
lean_object* v_pos_1220_; lean_object* v_err_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_del_object(v___x_1073_);
lean_dec(v_res_1071_);
lean_del_object(v___x_1064_);
lean_dec(v_res_1062_);
v_pos_1220_ = lean_ctor_get(v___x_1189_, 0);
v_err_1221_ = lean_ctor_get(v___x_1189_, 1);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1189_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_err_1221_);
lean_inc(v_pos_1220_);
lean_dec(v___x_1189_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_pos_1220_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_err_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1237_; lean_object* v_err_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
lean_del_object(v___x_1064_);
lean_dec(v_res_1062_);
v_pos_1237_ = lean_ctor_get(v___x_1069_, 0);
v_err_1238_ = lean_ctor_get(v___x_1069_, 1);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1069_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_err_1238_);
lean_inc(v_pos_1237_);
lean_dec(v___x_1069_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_pos_1237_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_err_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1248_; 
lean_dec(v_res_1062_);
v___x_1246_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2));
if (v_isShared_1065_ == 0)
{
lean_ctor_set_tag(v___x_1064_, 1);
lean_ctor_set(v___x_1064_, 1, v___x_1246_);
v___x_1248_ = v___x_1064_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_pos_1061_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v___x_1246_);
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
lean_object* v_pos_1251_; lean_object* v_err_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
v_pos_1251_ = lean_ctor_get(v___x_1060_, 0);
v_err_1252_ = lean_ctor_get(v___x_1060_, 1);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1060_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_err_1252_);
lean_inc(v_pos_1251_);
lean_dec(v___x_1060_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_pos_1251_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_err_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___boxed(lean_object* v_extended_1260_, lean_object* v_a_1261_){
_start:
{
uint8_t v_extended_boxed_1262_; lean_object* v_res_1263_; 
v_extended_boxed_1262_ = lean_unbox(v_extended_1260_);
v_res_1263_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP(v_extended_boxed_1262_, v_a_1261_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_parsePosixTz(lean_object* v_s_1264_, uint8_t v_extended_1265_){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1266_ = lean_box(v_extended_1265_);
v___x_1267_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___boxed), 2, 1);
lean_closure_set(v___x_1267_, 0, v___x_1266_);
v___x_1268_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_1267_, v_s_1264_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_parsePosixTz___boxed(lean_object* v_s_1269_, lean_object* v_extended_1270_){
_start:
{
uint8_t v_extended_boxed_1271_; lean_object* v_res_1272_; 
v_extended_boxed_1271_ = lean_unbox(v_extended_1270_);
v_res_1272_ = l_Std_Time_TimeZone_parsePosixTz(v_s_1269_, v_extended_boxed_1271_);
return v_res_1272_;
}
}
lean_object* runtime_initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_Database_PosixTz(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Internal_Parsec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_ZoneRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0___boxed__const__1 = _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0___boxed__const__1);
l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0___boxed__const__1 = _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Zoned_Database_PosixTz(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_Database_PosixTz(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Parsec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_ZoneRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_Database_PosixTz(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Zoned_Database_PosixTz(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Zoned_Database_PosixTz(builtin);
}
#ifdef __cplusplus
}
#endif
