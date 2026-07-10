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
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "digit expected"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__0 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__0_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__1 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__1_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__2 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__2_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " out of range"};
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
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hour "};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " out of range 0-"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "167"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2_value;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "second"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__11 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__11_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "minute"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__12 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__12_value;
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
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1(uint8_t, lean_object*);
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
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "week"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5_value;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9;
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
lean_object* v_fst_14_; lean_object* v_snd_15_; lean_object* v___x_16_; uint8_t v___x_17_; 
v_fst_14_ = lean_ctor_get(v_a_10_, 0);
v_snd_15_ = lean_ctor_get(v_a_10_, 1);
v___x_16_ = lean_string_utf8_byte_size(v_fst_14_);
v___x_17_ = lean_nat_dec_eq(v_snd_15_, v___x_16_);
if (v___x_17_ == 0)
{
uint32_t v_c_18_; uint32_t v___x_19_; uint8_t v___x_20_; 
v_c_18_ = lean_string_utf8_get_fast(v_fst_14_, v_snd_15_);
v___x_19_ = 48;
v___x_20_ = lean_uint32_dec_le(v___x_19_, v_c_18_);
if (v___x_20_ == 0)
{
lean_dec_ref(v_extra_9_);
lean_dec_ref(v_name_8_);
goto v___jp_11_;
}
else
{
uint32_t v___x_21_; uint8_t v___x_22_; 
v___x_21_ = 57;
v___x_22_ = lean_uint32_dec_le(v_c_18_, v___x_21_);
if (v___x_22_ == 0)
{
lean_dec_ref(v_extra_9_);
lean_dec_ref(v_name_8_);
goto v___jp_11_;
}
else
{
lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_66_; 
lean_inc(v_snd_15_);
lean_inc(v_fst_14_);
v_isSharedCheck_66_ = !lean_is_exclusive(v_a_10_);
if (v_isSharedCheck_66_ == 0)
{
lean_object* v_unused_67_; lean_object* v_unused_68_; 
v_unused_67_ = lean_ctor_get(v_a_10_, 1);
lean_dec(v_unused_67_);
v_unused_68_ = lean_ctor_get(v_a_10_, 0);
lean_dec(v_unused_68_);
v___x_24_ = v_a_10_;
v_isShared_25_ = v_isSharedCheck_66_;
goto v_resetjp_23_;
}
else
{
lean_dec(v_a_10_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_66_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v_fst_31_; lean_object* v_snd_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_65_; 
v___x_26_ = lean_string_utf8_next_fast(v_fst_14_, v_snd_15_);
lean_dec(v_snd_15_);
v___x_27_ = lean_uint32_to_nat(v_c_18_);
v___x_28_ = lean_unsigned_to_nat(48u);
v___x_29_ = lean_nat_sub(v___x_27_, v___x_28_);
lean_dec(v___x_27_);
v___x_30_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_14_, v___x_26_, v___x_29_);
v_fst_31_ = lean_ctor_get(v___x_30_, 0);
v_snd_32_ = lean_ctor_get(v___x_30_, 1);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_65_ == 0)
{
v___x_34_ = v___x_30_;
v_isShared_35_ = v_isSharedCheck_65_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_snd_32_);
lean_inc(v_fst_31_);
lean_dec(v___x_30_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_65_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 1, v_snd_32_);
v___x_37_ = v___x_24_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_fst_14_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_snd_32_);
v___x_37_ = v_reuseFailAlloc_64_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
lean_object* v___x_38_; lean_object* v___x_50_; uint8_t v___x_51_; uint8_t v___x_52_; 
v___x_38_ = lean_nat_to_int(v_fst_31_);
lean_inc(v___x_38_);
v___x_50_ = lean_apply_1(v_extra_9_, v___x_38_);
v___x_51_ = lean_unbox(v___x_50_);
v___x_52_ = lean_bool_not(v___x_51_);
if (v___x_52_ == 0)
{
uint8_t v___x_53_; 
v___x_53_ = lean_int_dec_le(v_lo_6_, v___x_38_);
if (v___x_53_ == 0)
{
goto v___jp_39_;
}
else
{
uint8_t v___x_54_; 
v___x_54_ = lean_int_dec_le(v___x_38_, v_hi_7_);
if (v___x_54_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v___x_55_; 
lean_del_object(v___x_34_);
lean_dec_ref(v_name_8_);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_37_);
lean_ctor_set(v___x_55_, 1, v___x_38_);
return v___x_55_;
}
}
}
else
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
lean_del_object(v___x_34_);
v___x_56_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__2));
v___x_57_ = lean_string_append(v_name_8_, v___x_56_);
v___x_58_ = l_Int_repr(v___x_38_);
lean_dec(v___x_38_);
v___x_59_ = lean_string_append(v___x_57_, v___x_58_);
lean_dec_ref(v___x_58_);
v___x_60_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__3));
v___x_61_ = lean_string_append(v___x_59_, v___x_60_);
v___x_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
v___x_63_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_37_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
return v___x_63_;
}
v___jp_39_:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_48_; 
v___x_40_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__2));
v___x_41_ = lean_string_append(v_name_8_, v___x_40_);
v___x_42_ = l_Int_repr(v___x_38_);
lean_dec(v___x_38_);
v___x_43_ = lean_string_append(v___x_41_, v___x_42_);
lean_dec_ref(v___x_42_);
v___x_44_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__3));
v___x_45_ = lean_string_append(v___x_43_, v___x_44_);
v___x_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
if (v_isShared_35_ == 0)
{
lean_ctor_set_tag(v___x_34_, 1);
lean_ctor_set(v___x_34_, 1, v___x_46_);
lean_ctor_set(v___x_34_, 0, v___x_37_);
v___x_48_ = v___x_34_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_37_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v___x_46_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
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
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec_ref(v_extra_9_);
lean_dec_ref(v_name_8_);
v___x_69_ = lean_box(0);
v___x_70_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_70_, 0, v_a_10_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
return v___x_70_;
}
v___jp_11_:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__1));
v___x_13_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_13_, 0, v_a_10_);
lean_ctor_set(v___x_13_, 1, v___x_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___boxed(lean_object* v_lo_71_, lean_object* v_hi_72_, lean_object* v_name_73_, lean_object* v_extra_74_, lean_object* v_a_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v_lo_71_, v_hi_72_, v_name_73_, v_extra_74_, v_a_75_);
lean_dec(v_hi_72_);
lean_dec(v_lo_71_);
return v_res_76_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_to_int(v___x_77_);
return v___x_78_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__3(void){
_start:
{
uint32_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = 43;
v___x_82_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_83_ = lean_string_push(v___x_82_, v___x_81_);
return v___x_83_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__3);
v___x_85_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_86_ = lean_string_append(v___x_85_, v___x_84_);
return v___x_86_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__6(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_89_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4);
v___x_90_ = lean_string_append(v___x_89_, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__7(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__6, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__6_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__6);
v___x_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__8(void){
_start:
{
uint32_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = 45;
v___x_94_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_95_ = lean_string_push(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__9(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__8, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__8_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__8);
v___x_97_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_98_ = lean_string_append(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__10(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_100_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__9, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__9_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__9);
v___x_101_ = lean_string_append(v___x_100_, v___x_99_);
return v___x_101_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__11(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__10, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__10_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__10);
v___x_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__12(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_105_ = lean_int_neg(v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(lean_object* v_a_106_){
_start:
{
lean_object* v_fst_107_; lean_object* v_snd_108_; lean_object* v_err_110_; lean_object* v_err_118_; lean_object* v___x_139_; uint8_t v___x_140_; 
v_fst_107_ = lean_ctor_get(v_a_106_, 0);
v_snd_108_ = lean_ctor_get(v_a_106_, 1);
v___x_139_ = lean_string_utf8_byte_size(v_fst_107_);
v___x_140_ = lean_nat_dec_eq(v_snd_108_, v___x_139_);
if (v___x_140_ == 0)
{
uint32_t v___x_141_; uint32_t v_c_142_; uint8_t v___x_143_; 
v___x_141_ = 45;
v_c_142_ = lean_string_utf8_get_fast(v_fst_107_, v_snd_108_);
v___x_143_ = lean_uint32_dec_eq(v_c_142_, v___x_141_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; 
v___x_144_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__11, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__11_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__11);
v_err_118_ = v___x_144_;
goto v___jp_117_;
}
else
{
lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_154_; 
lean_inc(v_snd_108_);
lean_inc(v_fst_107_);
v_isSharedCheck_154_ = !lean_is_exclusive(v_a_106_);
if (v_isSharedCheck_154_ == 0)
{
lean_object* v_unused_155_; lean_object* v_unused_156_; 
v_unused_155_ = lean_ctor_get(v_a_106_, 1);
lean_dec(v_unused_155_);
v_unused_156_ = lean_ctor_get(v_a_106_, 0);
lean_dec(v_unused_156_);
v___x_146_ = v_a_106_;
v_isShared_147_ = v_isSharedCheck_154_;
goto v_resetjp_145_;
}
else
{
lean_dec(v_a_106_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_154_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v_it_x27_150_; 
v___x_148_ = lean_string_utf8_next_fast(v_fst_107_, v_snd_108_);
lean_dec(v_snd_108_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 1, v___x_148_);
v_it_x27_150_ = v___x_146_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_fst_107_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v___x_148_);
v_it_x27_150_ = v_reuseFailAlloc_153_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__12, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__12_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__12);
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v_it_x27_150_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
return v___x_152_;
}
}
}
}
else
{
lean_object* v___x_157_; 
v___x_157_ = lean_box(0);
v_err_118_ = v___x_157_;
goto v___jp_117_;
}
v___jp_109_:
{
uint8_t v___x_111_; 
v___x_111_ = lean_nat_dec_eq(v_snd_108_, v_snd_108_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
lean_inc(v_err_110_);
v___x_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_112_, 0, v_a_106_);
lean_ctor_set(v___x_112_, 1, v_err_110_);
return v___x_112_;
}
else
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v_a_106_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
return v___x_114_;
}
}
v___jp_115_:
{
lean_object* v___x_116_; 
v___x_116_ = lean_box(0);
v_err_110_ = v___x_116_;
goto v___jp_109_;
}
v___jp_117_:
{
uint8_t v___x_119_; 
v___x_119_ = lean_nat_dec_eq(v_snd_108_, v_snd_108_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; 
lean_inc(v_err_118_);
v___x_120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_120_, 0, v_a_106_);
lean_ctor_set(v___x_120_, 1, v_err_118_);
return v___x_120_;
}
else
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_string_utf8_byte_size(v_fst_107_);
v___x_122_ = lean_nat_dec_eq(v_snd_108_, v___x_121_);
if (v___x_122_ == 0)
{
if (v___x_119_ == 0)
{
goto v___jp_115_;
}
else
{
uint32_t v___x_123_; uint32_t v_c_124_; uint8_t v___x_125_; 
v___x_123_ = 43;
v_c_124_ = lean_string_utf8_get_fast(v_fst_107_, v_snd_108_);
v___x_125_ = lean_uint32_dec_eq(v_c_124_, v___x_123_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
v___x_126_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__7, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__7_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__7);
v_err_110_ = v___x_126_;
goto v___jp_109_;
}
else
{
lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_136_; 
lean_inc(v_snd_108_);
lean_inc(v_fst_107_);
v_isSharedCheck_136_ = !lean_is_exclusive(v_a_106_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; lean_object* v_unused_138_; 
v_unused_137_ = lean_ctor_get(v_a_106_, 1);
lean_dec(v_unused_137_);
v_unused_138_ = lean_ctor_get(v_a_106_, 0);
lean_dec(v_unused_138_);
v___x_128_ = v_a_106_;
v_isShared_129_ = v_isSharedCheck_136_;
goto v_resetjp_127_;
}
else
{
lean_dec(v_a_106_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_136_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; lean_object* v_it_x27_132_; 
v___x_130_ = lean_string_utf8_next_fast(v_fst_107_, v_snd_108_);
lean_dec(v_snd_108_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v___x_130_);
v_it_x27_132_ = v___x_128_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_fst_107_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___x_130_);
v_it_x27_132_ = v_reuseFailAlloc_135_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v_it_x27_132_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
return v___x_134_;
}
}
}
}
}
else
{
goto v___jp_115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__0(lean_object* v_a_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = lean_nat_to_int(v_a_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__2(lean_object* v_a_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Rat_ofInt(v_a_160_);
return v___x_161_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0(uint8_t v___y_162_, lean_object* v_x_163_){
_start:
{
return v___y_162_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed(lean_object* v___y_164_, lean_object* v_x_165_){
_start:
{
uint8_t v___y_3741__boxed_166_; uint8_t v_res_167_; lean_object* v_r_168_; 
v___y_3741__boxed_166_ = lean_unbox(v___y_164_);
v_res_167_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0(v___y_3741__boxed_166_, v_x_165_);
lean_dec(v_x_165_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(3600u);
v___x_173_ = lean_nat_to_int(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_unsigned_to_nat(60u);
v___x_175_ = lean_nat_to_int(v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = lean_nat_to_int(v___x_176_);
return v___x_177_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6(void){
_start:
{
uint32_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = 58;
v___x_179_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_180_ = lean_string_push(v___x_179_, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6);
v___x_182_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_183_ = lean_string_append(v___x_182_, v___x_181_);
return v___x_183_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_185_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7);
v___x_186_ = lean_string_append(v___x_185_, v___x_184_);
return v___x_186_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8);
v___x_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
return v___x_188_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_unsigned_to_nat(59u);
v___x_190_ = lean_nat_to_int(v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(lean_object* v_maxHour_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_fst_198_; lean_object* v_snd_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v_fst_198_ = lean_ctor_get(v_a_194_, 0);
v_snd_199_ = lean_ctor_get(v_a_194_, 1);
v___x_200_ = lean_string_utf8_byte_size(v_fst_198_);
v___x_201_ = lean_nat_dec_eq(v_snd_199_, v___x_200_);
if (v___x_201_ == 0)
{
uint32_t v_c_202_; uint32_t v___x_203_; uint8_t v___x_204_; 
v_c_202_ = lean_string_utf8_get_fast(v_fst_198_, v_snd_199_);
v___x_203_ = 48;
v___x_204_ = lean_uint32_dec_le(v___x_203_, v_c_202_);
if (v___x_204_ == 0)
{
lean_dec(v_maxHour_193_);
goto v___jp_195_;
}
else
{
uint32_t v___x_205_; uint8_t v___x_206_; 
v___x_205_ = 57;
v___x_206_ = lean_uint32_dec_le(v_c_202_, v___x_205_);
if (v___x_206_ == 0)
{
lean_dec(v_maxHour_193_);
goto v___jp_195_;
}
else
{
lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_325_; 
lean_inc(v_snd_199_);
lean_inc(v_fst_198_);
v_isSharedCheck_325_ = !lean_is_exclusive(v_a_194_);
if (v_isSharedCheck_325_ == 0)
{
lean_object* v_unused_326_; lean_object* v_unused_327_; 
v_unused_326_ = lean_ctor_get(v_a_194_, 1);
lean_dec(v_unused_326_);
v_unused_327_ = lean_ctor_get(v_a_194_, 0);
lean_dec(v_unused_327_);
v___x_208_ = v_a_194_;
v_isShared_209_ = v_isSharedCheck_325_;
goto v_resetjp_207_;
}
else
{
lean_dec(v_a_194_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_325_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v_fst_215_; lean_object* v_snd_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_324_; 
v___x_210_ = lean_string_utf8_next_fast(v_fst_198_, v_snd_199_);
lean_dec(v_snd_199_);
v___x_211_ = lean_uint32_to_nat(v_c_202_);
v___x_212_ = lean_unsigned_to_nat(48u);
v___x_213_ = lean_nat_sub(v___x_211_, v___x_212_);
lean_dec(v___x_211_);
v___x_214_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_198_, v___x_210_, v___x_213_);
v_fst_215_ = lean_ctor_get(v___x_214_, 0);
v_snd_216_ = lean_ctor_get(v___x_214_, 1);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_324_ == 0)
{
v___x_218_ = v___x_214_;
v_isShared_219_ = v_isSharedCheck_324_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_snd_216_);
lean_inc(v_fst_215_);
lean_dec(v___x_214_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_324_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
lean_inc(v_snd_216_);
lean_inc(v_fst_198_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v_snd_216_);
v___x_221_ = v___x_208_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_fst_198_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_snd_216_);
v___x_221_ = v_reuseFailAlloc_323_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
uint8_t v___x_222_; 
v___x_222_ = lean_nat_dec_lt(v_maxHour_193_, v_fst_215_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; uint8_t v___x_224_; 
lean_dec(v_maxHour_193_);
v___x_223_ = lean_unsigned_to_nat(167u);
v___x_224_ = lean_nat_dec_le(v_fst_215_, v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
lean_dec(v_snd_216_);
lean_dec(v_fst_198_);
v___x_225_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0));
v___x_226_ = l_Nat_reprFast(v_fst_215_);
v___x_227_ = lean_string_append(v___x_225_, v___x_226_);
lean_dec_ref(v___x_226_);
v___x_228_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1));
v___x_229_ = lean_string_append(v___x_227_, v___x_228_);
v___x_230_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2));
v___x_231_ = lean_string_append(v___x_229_, v___x_230_);
v___x_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
if (v_isShared_219_ == 0)
{
lean_ctor_set_tag(v___x_218_, 1);
lean_ctor_set(v___x_218_, 1, v___x_232_);
lean_ctor_set(v___x_218_, 0, v___x_221_);
v___x_234_ = v___x_218_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
else
{
lean_object* v___x_236_; lean_object* v___y_238_; lean_object* v_pos_239_; lean_object* v_res_240_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v_err_253_; uint32_t v___x_258_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; uint8_t v___y_264_; lean_object* v_pos_281_; lean_object* v_fst_282_; lean_object* v_snd_283_; lean_object* v_res_284_; lean_object* v_err_288_; uint8_t v___y_293_; uint8_t v___x_311_; 
v___x_236_ = lean_nat_to_int(v_fst_215_);
v___x_258_ = 58;
v___x_311_ = lean_nat_dec_eq(v_snd_216_, v___x_200_);
if (v___x_311_ == 0)
{
v___y_293_ = v___x_224_;
goto v___jp_292_;
}
else
{
v___y_293_ = v___x_222_;
goto v___jp_292_;
}
v___jp_237_:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_241_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_242_ = lean_int_mul(v___x_236_, v___x_241_);
lean_dec(v___x_236_);
v___x_243_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4);
v___x_244_ = lean_int_mul(v___y_238_, v___x_243_);
lean_dec(v___y_238_);
v___x_245_ = lean_int_add(v___x_242_, v___x_244_);
lean_dec(v___x_244_);
lean_dec(v___x_242_);
v___x_246_ = lean_int_add(v___x_245_, v_res_240_);
lean_dec(v_res_240_);
lean_dec(v___x_245_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 1, v___x_246_);
lean_ctor_set(v___x_218_, 0, v_pos_239_);
v___x_248_ = v___x_218_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_pos_239_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
v___jp_250_:
{
lean_object* v_snd_254_; uint8_t v___x_255_; 
v_snd_254_ = lean_ctor_get(v___y_251_, 1);
v___x_255_ = lean_nat_dec_eq(v_snd_254_, v_snd_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
lean_dec(v___y_252_);
lean_dec(v___x_236_);
lean_del_object(v___x_218_);
v___x_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_256_, 0, v___y_251_);
lean_ctor_set(v___x_256_, 1, v_err_253_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; 
lean_dec(v_err_253_);
v___x_257_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___y_238_ = v___y_252_;
v_pos_239_ = v___y_251_;
v_res_240_ = v___x_257_;
goto v___jp_237_;
}
}
v___jp_259_:
{
if (v___y_264_ == 0)
{
lean_object* v___x_265_; 
lean_dec(v___y_262_);
lean_dec(v___y_261_);
v___x_265_ = lean_box(0);
v___y_251_ = v___y_260_;
v___y_252_ = v___y_263_;
v_err_253_ = v___x_265_;
goto v___jp_250_;
}
else
{
uint32_t v_c_266_; uint8_t v___x_267_; 
v_c_266_ = lean_string_utf8_get_fast(v___y_262_, v___y_261_);
v___x_267_ = lean_uint32_dec_eq(v_c_266_, v___x_258_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
lean_dec(v___y_262_);
lean_dec(v___y_261_);
v___x_268_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9);
v___y_251_ = v___y_260_;
v___y_252_ = v___y_263_;
v_err_253_ = v___x_268_;
goto v___jp_250_;
}
else
{
lean_object* v___x_269_; lean_object* v___f_270_; lean_object* v___x_271_; lean_object* v_it_x27_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_269_ = lean_box(v___y_264_);
v___f_270_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_270_, 0, v___x_269_);
v___x_271_ = lean_string_utf8_next_fast(v___y_262_, v___y_261_);
lean_dec(v___y_261_);
v_it_x27_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_272_, 0, v___y_262_);
lean_ctor_set(v_it_x27_272_, 1, v___x_271_);
v___x_273_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___x_274_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10);
v___x_275_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__11));
v___x_276_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_273_, v___x_274_, v___x_275_, v___f_270_, v_it_x27_272_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_pos_277_; lean_object* v_res_278_; 
lean_dec_ref(v___y_260_);
v_pos_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_pos_277_);
v_res_278_ = lean_ctor_get(v___x_276_, 1);
lean_inc(v_res_278_);
lean_dec_ref_known(v___x_276_, 2);
v___y_238_ = v___y_263_;
v_pos_239_ = v_pos_277_;
v_res_240_ = v_res_278_;
goto v___jp_237_;
}
else
{
lean_object* v_err_279_; 
v_err_279_ = lean_ctor_get(v___x_276_, 1);
lean_inc(v_err_279_);
lean_dec_ref_known(v___x_276_, 2);
v___y_251_ = v___y_260_;
v___y_252_ = v___y_263_;
v_err_253_ = v_err_279_;
goto v___jp_250_;
}
}
}
}
v___jp_280_:
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_string_utf8_byte_size(v_fst_282_);
v___x_286_ = lean_nat_dec_eq(v_snd_283_, v___x_285_);
if (v___x_286_ == 0)
{
v___y_260_ = v_pos_281_;
v___y_261_ = v_snd_283_;
v___y_262_ = v_fst_282_;
v___y_263_ = v_res_284_;
v___y_264_ = v___x_224_;
goto v___jp_259_;
}
else
{
v___y_260_ = v_pos_281_;
v___y_261_ = v_snd_283_;
v___y_262_ = v_fst_282_;
v___y_263_ = v_res_284_;
v___y_264_ = v___x_222_;
goto v___jp_259_;
}
}
v___jp_287_:
{
uint8_t v___x_289_; 
v___x_289_ = lean_nat_dec_eq(v_snd_216_, v_snd_216_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; 
lean_dec(v___x_236_);
lean_del_object(v___x_218_);
lean_dec(v_snd_216_);
lean_dec(v_fst_198_);
v___x_290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_221_);
lean_ctor_set(v___x_290_, 1, v_err_288_);
return v___x_290_;
}
else
{
lean_object* v___x_291_; 
lean_dec(v_err_288_);
v___x_291_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v_pos_281_ = v___x_221_;
v_fst_282_ = v_fst_198_;
v_snd_283_ = v_snd_216_;
v_res_284_ = v___x_291_;
goto v___jp_280_;
}
}
v___jp_292_:
{
if (v___y_293_ == 0)
{
lean_object* v___x_294_; 
v___x_294_ = lean_box(0);
v_err_288_ = v___x_294_;
goto v___jp_287_;
}
else
{
uint32_t v_c_295_; uint8_t v___x_296_; 
v_c_295_ = lean_string_utf8_get_fast(v_fst_198_, v_snd_216_);
v___x_296_ = lean_uint32_dec_eq(v_c_295_, v___x_258_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9);
v_err_288_ = v___x_297_;
goto v___jp_287_;
}
else
{
lean_object* v___x_298_; lean_object* v___f_299_; lean_object* v___x_300_; lean_object* v_it_x27_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_298_ = lean_box(v___y_293_);
v___f_299_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_299_, 0, v___x_298_);
v___x_300_ = lean_string_utf8_next_fast(v_fst_198_, v_snd_216_);
lean_inc(v_fst_198_);
v_it_x27_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_301_, 0, v_fst_198_);
lean_ctor_set(v_it_x27_301_, 1, v___x_300_);
v___x_302_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___x_303_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10);
v___x_304_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__12));
v___x_305_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_302_, v___x_303_, v___x_304_, v___f_299_, v_it_x27_301_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_pos_306_; lean_object* v_res_307_; lean_object* v_fst_308_; lean_object* v_snd_309_; 
lean_dec_ref(v___x_221_);
lean_dec(v_snd_216_);
lean_dec(v_fst_198_);
v_pos_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_pos_306_);
v_res_307_ = lean_ctor_get(v___x_305_, 1);
lean_inc(v_res_307_);
lean_dec_ref_known(v___x_305_, 2);
v_fst_308_ = lean_ctor_get(v_pos_306_, 0);
lean_inc(v_fst_308_);
v_snd_309_ = lean_ctor_get(v_pos_306_, 1);
lean_inc(v_snd_309_);
v_pos_281_ = v_pos_306_;
v_fst_282_ = v_fst_308_;
v_snd_283_ = v_snd_309_;
v_res_284_ = v_res_307_;
goto v___jp_280_;
}
else
{
lean_object* v_err_310_; 
v_err_310_ = lean_ctor_get(v___x_305_, 1);
lean_inc(v_err_310_);
lean_dec_ref_known(v___x_305_, 2);
v_err_288_ = v_err_310_;
goto v___jp_287_;
}
}
}
}
}
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_321_; 
lean_dec(v_snd_216_);
lean_dec(v_fst_198_);
v___x_312_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0));
v___x_313_ = l_Nat_reprFast(v_fst_215_);
v___x_314_ = lean_string_append(v___x_312_, v___x_313_);
lean_dec_ref(v___x_313_);
v___x_315_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1));
v___x_316_ = lean_string_append(v___x_314_, v___x_315_);
v___x_317_ = l_Nat_reprFast(v_maxHour_193_);
v___x_318_ = lean_string_append(v___x_316_, v___x_317_);
lean_dec_ref(v___x_317_);
v___x_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
if (v_isShared_219_ == 0)
{
lean_ctor_set_tag(v___x_218_, 1);
lean_ctor_set(v___x_218_, 1, v___x_319_);
lean_ctor_set(v___x_218_, 0, v___x_221_);
v___x_321_ = v___x_218_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
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
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec(v_maxHour_193_);
v___x_328_ = lean_box(0);
v___x_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_329_, 0, v_a_194_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
return v___x_329_;
}
v___jp_195_:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__1));
v___x_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_197_, 0, v_a_194_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__1(lean_object* v_a_330_){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_nat_to_int(v_a_330_);
v___x_332_ = l_Rat_ofInt(v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(lean_object* v_a_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(v_a_333_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_pos_335_; lean_object* v_res_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_pos_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_pos_335_);
v_res_336_ = lean_ctor_get(v___x_334_, 1);
lean_inc(v_res_336_);
lean_dec_ref_known(v___x_334_, 2);
v___x_337_ = lean_unsigned_to_nat(24u);
v___x_338_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(v___x_337_, v_pos_335_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_pos_339_; lean_object* v_res_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_349_; 
v_pos_339_ = lean_ctor_get(v___x_338_, 0);
v_res_340_ = lean_ctor_get(v___x_338_, 1);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_349_ == 0)
{
v___x_342_ = v___x_338_;
v_isShared_343_ = v_isSharedCheck_349_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_res_340_);
lean_inc(v_pos_339_);
lean_dec(v___x_338_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_349_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_344_ = lean_int_neg(v_res_336_);
lean_dec(v_res_336_);
v___x_345_ = lean_int_mul(v___x_344_, v_res_340_);
lean_dec(v_res_340_);
lean_dec(v___x_344_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 1, v___x_345_);
v___x_347_ = v___x_342_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_pos_339_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
else
{
lean_object* v_pos_350_; lean_object* v_err_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec(v_res_336_);
v_pos_350_ = lean_ctor_get(v___x_338_, 0);
v_err_351_ = lean_ctor_get(v___x_338_, 1);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_338_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_err_351_);
lean_inc(v_pos_350_);
lean_dec(v___x_338_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_pos_350_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_err_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
else
{
lean_object* v_pos_359_; lean_object* v_err_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
v_pos_359_ = lean_ctor_get(v___x_334_, 0);
v_err_360_ = lean_ctor_get(v___x_334_, 1);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_334_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_err_360_);
lean_inc(v_pos_359_);
lean_dec(v___x_334_);
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0(lean_object* v_acc_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_pos_374_; uint32_t v_res_375_; lean_object* v_fst_378_; lean_object* v_snd_379_; lean_object* v_pos_381_; lean_object* v_snd_382_; lean_object* v_err_383_; lean_object* v___x_389_; uint8_t v___x_390_; 
v_fst_378_ = lean_ctor_get(v_a_372_, 0);
v_snd_379_ = lean_ctor_get(v_a_372_, 1);
lean_inc(v_snd_379_);
v___x_389_ = lean_string_utf8_byte_size(v_fst_378_);
v___x_390_ = lean_nat_dec_eq(v_snd_379_, v___x_389_);
if (v___x_390_ == 0)
{
uint32_t v_c_391_; lean_object* v___x_392_; lean_object* v_it_x27_393_; uint8_t v___y_395_; uint8_t v___y_397_; uint8_t v___y_403_; uint32_t v___x_413_; uint8_t v___x_414_; 
v_c_391_ = lean_string_utf8_get_fast(v_fst_378_, v_snd_379_);
v___x_392_ = lean_string_utf8_next_fast(v_fst_378_, v_snd_379_);
lean_inc(v_fst_378_);
v_it_x27_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_393_, 0, v_fst_378_);
lean_ctor_set(v_it_x27_393_, 1, v___x_392_);
v___x_413_ = 65;
v___x_414_ = lean_uint32_dec_le(v___x_413_, v_c_391_);
if (v___x_414_ == 0)
{
goto v___jp_408_;
}
else
{
uint32_t v___x_415_; uint8_t v___x_416_; 
v___x_415_ = 90;
v___x_416_ = lean_uint32_dec_le(v_c_391_, v___x_415_);
if (v___x_416_ == 0)
{
goto v___jp_408_;
}
else
{
lean_dec(v_snd_379_);
lean_dec_ref(v_a_372_);
v_pos_374_ = v_it_x27_393_;
v_res_375_ = v_c_391_;
goto v___jp_373_;
}
}
v___jp_394_:
{
if (v___y_395_ == 0)
{
lean_dec_ref_known(v_it_x27_393_, 2);
goto v___jp_387_;
}
else
{
lean_dec(v_snd_379_);
lean_dec_ref(v_a_372_);
v_pos_374_ = v_it_x27_393_;
v_res_375_ = v_c_391_;
goto v___jp_373_;
}
}
v___jp_396_:
{
if (v___y_397_ == 0)
{
uint32_t v___x_398_; uint8_t v___x_399_; 
v___x_398_ = 43;
v___x_399_ = lean_uint32_dec_eq(v_c_391_, v___x_398_);
if (v___x_399_ == 0)
{
uint32_t v___x_400_; uint8_t v___x_401_; 
v___x_400_ = 45;
v___x_401_ = lean_uint32_dec_eq(v_c_391_, v___x_400_);
if (v___x_401_ == 0)
{
lean_dec_ref_known(v_it_x27_393_, 2);
goto v___jp_387_;
}
else
{
v___y_395_ = v___x_401_;
goto v___jp_394_;
}
}
else
{
v___y_395_ = v___x_399_;
goto v___jp_394_;
}
}
else
{
lean_dec(v_snd_379_);
lean_dec_ref(v_a_372_);
v_pos_374_ = v_it_x27_393_;
v_res_375_ = v_c_391_;
goto v___jp_373_;
}
}
v___jp_402_:
{
if (v___y_403_ == 0)
{
uint32_t v___x_404_; uint8_t v___x_405_; 
v___x_404_ = 48;
v___x_405_ = lean_uint32_dec_le(v___x_404_, v_c_391_);
if (v___x_405_ == 0)
{
v___y_397_ = v___x_405_;
goto v___jp_396_;
}
else
{
uint32_t v___x_406_; uint8_t v___x_407_; 
v___x_406_ = 57;
v___x_407_ = lean_uint32_dec_le(v_c_391_, v___x_406_);
v___y_397_ = v___x_407_;
goto v___jp_396_;
}
}
else
{
lean_dec(v_snd_379_);
lean_dec_ref(v_a_372_);
v_pos_374_ = v_it_x27_393_;
v_res_375_ = v_c_391_;
goto v___jp_373_;
}
}
v___jp_408_:
{
uint32_t v___x_409_; uint8_t v___x_410_; 
v___x_409_ = 97;
v___x_410_ = lean_uint32_dec_le(v___x_409_, v_c_391_);
if (v___x_410_ == 0)
{
v___y_403_ = v___x_410_;
goto v___jp_402_;
}
else
{
uint32_t v___x_411_; uint8_t v___x_412_; 
v___x_411_ = 122;
v___x_412_ = lean_uint32_dec_le(v_c_391_, v___x_411_);
v___y_403_ = v___x_412_;
goto v___jp_402_;
}
}
}
else
{
lean_object* v___x_417_; 
v___x_417_ = lean_box(0);
lean_inc(v_snd_379_);
v_pos_381_ = v_a_372_;
v_snd_382_ = v_snd_379_;
v_err_383_ = v___x_417_;
goto v___jp_380_;
}
v___jp_373_:
{
lean_object* v___x_376_; 
v___x_376_ = lean_string_push(v_acc_371_, v_res_375_);
v_acc_371_ = v___x_376_;
v_a_372_ = v_pos_374_;
goto _start;
}
v___jp_380_:
{
uint8_t v___x_384_; 
v___x_384_ = lean_nat_dec_eq(v_snd_379_, v_snd_382_);
lean_dec(v_snd_382_);
lean_dec(v_snd_379_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; 
lean_dec_ref(v_acc_371_);
lean_inc(v_err_383_);
v___x_385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_385_, 0, v_pos_381_);
lean_ctor_set(v___x_385_, 1, v_err_383_);
return v___x_385_;
}
else
{
lean_object* v___x_386_; 
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v_pos_381_);
lean_ctor_set(v___x_386_, 1, v_acc_371_);
return v___x_386_;
}
}
v___jp_387_:
{
lean_object* v___x_388_; 
v___x_388_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__1));
lean_inc(v_snd_379_);
v_pos_381_ = v_a_372_;
v_snd_382_ = v_snd_379_;
v_err_383_ = v___x_388_;
goto v___jp_380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName(lean_object* v_a_418_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_420_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0(v___x_419_, v_a_418_);
return v___x_420_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(lean_object* v_x_421_, lean_object* v_x_422_){
_start:
{
if (lean_obj_tag(v_x_421_) == 0)
{
if (lean_obj_tag(v_x_422_) == 0)
{
uint8_t v___x_423_; 
v___x_423_ = 1;
return v___x_423_;
}
else
{
uint8_t v___x_424_; 
v___x_424_ = 0;
return v___x_424_;
}
}
else
{
if (lean_obj_tag(v_x_422_) == 0)
{
uint8_t v___x_425_; 
v___x_425_ = 0;
return v___x_425_;
}
else
{
lean_object* v_val_426_; lean_object* v_val_427_; uint32_t v___x_428_; uint32_t v___x_429_; uint8_t v___x_430_; 
v_val_426_ = lean_ctor_get(v_x_421_, 0);
v_val_427_ = lean_ctor_get(v_x_422_, 0);
v___x_428_ = lean_unbox_uint32(v_val_426_);
v___x_429_ = lean_unbox_uint32(v_val_427_);
v___x_430_ = lean_uint32_dec_eq(v___x_428_, v___x_429_);
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0___boxed(lean_object* v_x_431_, lean_object* v_x_432_){
_start:
{
uint8_t v_res_433_; lean_object* v_r_434_; 
v_res_433_ = l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_x_431_, v_x_432_);
lean_dec(v_x_432_);
lean_dec(v_x_431_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1(lean_object* v_acc_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_pos_441_; uint32_t v_res_442_; lean_object* v_fst_445_; lean_object* v_snd_446_; lean_object* v_pos_448_; lean_object* v_snd_449_; lean_object* v_err_450_; lean_object* v___x_456_; uint8_t v___x_457_; 
v_fst_445_ = lean_ctor_get(v_a_439_, 0);
v_snd_446_ = lean_ctor_get(v_a_439_, 1);
lean_inc(v_snd_446_);
v___x_456_ = lean_string_utf8_byte_size(v_fst_445_);
v___x_457_ = lean_nat_dec_eq(v_snd_446_, v___x_456_);
if (v___x_457_ == 0)
{
uint32_t v_c_458_; lean_object* v___x_459_; lean_object* v_it_x27_460_; uint32_t v___x_466_; uint8_t v___x_467_; 
v_c_458_ = lean_string_utf8_get_fast(v_fst_445_, v_snd_446_);
v___x_459_ = lean_string_utf8_next_fast(v_fst_445_, v_snd_446_);
lean_inc(v_fst_445_);
v_it_x27_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_460_, 0, v_fst_445_);
lean_ctor_set(v_it_x27_460_, 1, v___x_459_);
v___x_466_ = 65;
v___x_467_ = lean_uint32_dec_le(v___x_466_, v_c_458_);
if (v___x_467_ == 0)
{
goto v___jp_461_;
}
else
{
uint32_t v___x_468_; uint8_t v___x_469_; 
v___x_468_ = 90;
v___x_469_ = lean_uint32_dec_le(v_c_458_, v___x_468_);
if (v___x_469_ == 0)
{
goto v___jp_461_;
}
else
{
lean_dec(v_snd_446_);
lean_dec_ref(v_a_439_);
v_pos_441_ = v_it_x27_460_;
v_res_442_ = v_c_458_;
goto v___jp_440_;
}
}
v___jp_461_:
{
uint32_t v___x_462_; uint8_t v___x_463_; 
v___x_462_ = 97;
v___x_463_ = lean_uint32_dec_le(v___x_462_, v_c_458_);
if (v___x_463_ == 0)
{
lean_dec_ref_known(v_it_x27_460_, 2);
goto v___jp_454_;
}
else
{
uint32_t v___x_464_; uint8_t v___x_465_; 
v___x_464_ = 122;
v___x_465_ = lean_uint32_dec_le(v_c_458_, v___x_464_);
if (v___x_465_ == 0)
{
lean_dec_ref_known(v_it_x27_460_, 2);
goto v___jp_454_;
}
else
{
lean_dec(v_snd_446_);
lean_dec_ref(v_a_439_);
v_pos_441_ = v_it_x27_460_;
v_res_442_ = v_c_458_;
goto v___jp_440_;
}
}
}
}
else
{
lean_object* v___x_470_; 
v___x_470_ = lean_box(0);
lean_inc(v_snd_446_);
v_pos_448_ = v_a_439_;
v_snd_449_ = v_snd_446_;
v_err_450_ = v___x_470_;
goto v___jp_447_;
}
v___jp_440_:
{
lean_object* v___x_443_; 
v___x_443_ = lean_string_push(v_acc_438_, v_res_442_);
v_acc_438_ = v___x_443_;
v_a_439_ = v_pos_441_;
goto _start;
}
v___jp_447_:
{
uint8_t v___x_451_; 
v___x_451_ = lean_nat_dec_eq(v_snd_446_, v_snd_449_);
lean_dec(v_snd_449_);
lean_dec(v_snd_446_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
lean_dec_ref(v_acc_438_);
lean_inc(v_err_450_);
v___x_452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_452_, 0, v_pos_448_);
lean_ctor_set(v___x_452_, 1, v_err_450_);
return v___x_452_;
}
else
{
lean_object* v___x_453_; 
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v_pos_448_);
lean_ctor_set(v___x_453_, 1, v_acc_438_);
return v___x_453_;
}
}
v___jp_454_:
{
lean_object* v___x_455_; 
v___x_455_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__1));
lean_inc(v_snd_446_);
v_pos_448_ = v_a_439_;
v_snd_449_ = v_snd_446_;
v_err_450_ = v___x_455_;
goto v___jp_447_;
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_471_; lean_object* v___x_472_; 
v___x_471_ = 60;
v___x_472_ = lean_box_uint32(v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0___boxed__const__1;
v___x_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__1(void){
_start:
{
uint32_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = 62;
v___x_476_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_477_ = lean_string_push(v___x_476_, v___x_475_);
return v___x_477_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__1, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__1_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__1);
v___x_479_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_480_ = lean_string_append(v___x_479_, v___x_478_);
return v___x_480_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__3(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_482_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2);
v___x_483_ = lean_string_append(v___x_482_, v___x_481_);
return v___x_483_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__4(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__3);
v___x_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(lean_object* v_a_486_){
_start:
{
lean_object* v___y_488_; lean_object* v_pos_492_; lean_object* v_res_493_; lean_object* v_fst_547_; lean_object* v_snd_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v_fst_547_ = lean_ctor_get(v_a_486_, 0);
v_snd_548_ = lean_ctor_get(v_a_486_, 1);
v___x_549_ = lean_string_utf8_byte_size(v_fst_547_);
v___x_550_ = lean_nat_dec_eq(v_snd_548_, v___x_549_);
if (v___x_550_ == 0)
{
uint32_t v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = lean_string_utf8_get_fast(v_fst_547_, v_snd_548_);
v___x_552_ = lean_box_uint32(v___x_551_);
v___x_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
v_pos_492_ = v_a_486_;
v_res_493_ = v___x_553_;
goto v___jp_491_;
}
else
{
lean_object* v___x_554_; 
v___x_554_ = lean_box(0);
v_pos_492_ = v_a_486_;
v_res_493_ = v___x_554_;
goto v___jp_491_;
}
v___jp_487_:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_box(0);
v___x_490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_490_, 0, v___y_488_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
return v___x_490_;
}
v___jp_491_:
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0);
v___x_495_ = l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_res_493_, v___x_494_);
lean_dec(v_res_493_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_497_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1(v___x_496_, v_pos_492_);
return v___x_497_;
}
else
{
lean_object* v_fst_498_; lean_object* v_snd_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v_fst_498_ = lean_ctor_get(v_pos_492_, 0);
v_snd_499_ = lean_ctor_get(v_pos_492_, 1);
v___x_500_ = lean_string_utf8_byte_size(v_fst_498_);
v___x_501_ = lean_nat_dec_eq(v_snd_499_, v___x_500_);
if (v___x_501_ == 0)
{
if (v___x_495_ == 0)
{
v___y_488_ = v_pos_492_;
goto v___jp_487_;
}
else
{
lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_544_; 
lean_inc(v_snd_499_);
lean_inc(v_fst_498_);
v_isSharedCheck_544_ = !lean_is_exclusive(v_pos_492_);
if (v_isSharedCheck_544_ == 0)
{
lean_object* v_unused_545_; lean_object* v_unused_546_; 
v_unused_545_ = lean_ctor_get(v_pos_492_, 1);
lean_dec(v_unused_545_);
v_unused_546_ = lean_ctor_get(v_pos_492_, 0);
lean_dec(v_unused_546_);
v___x_503_ = v_pos_492_;
v_isShared_504_ = v_isSharedCheck_544_;
goto v_resetjp_502_;
}
else
{
lean_dec(v_pos_492_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_544_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_505_ = lean_string_utf8_next_fast(v_fst_498_, v_snd_499_);
lean_dec(v_snd_499_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_505_);
v___x_507_ = v___x_503_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_fst_498_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v___x_505_);
v___x_507_ = v_reuseFailAlloc_543_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; 
v___x_508_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName(v___x_507_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_pos_509_; lean_object* v_res_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_542_; 
v_pos_509_ = lean_ctor_get(v___x_508_, 0);
v_res_510_ = lean_ctor_get(v___x_508_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_542_ == 0)
{
v___x_512_ = v___x_508_;
v_isShared_513_ = v_isSharedCheck_542_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_res_510_);
lean_inc(v_pos_509_);
lean_dec(v___x_508_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_542_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v_fst_514_; lean_object* v_snd_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v_fst_514_ = lean_ctor_get(v_pos_509_, 0);
v_snd_515_ = lean_ctor_get(v_pos_509_, 1);
v___x_516_ = lean_string_utf8_byte_size(v_fst_514_);
v___x_517_ = lean_nat_dec_eq(v_snd_515_, v___x_516_);
if (v___x_517_ == 0)
{
uint32_t v___x_518_; uint32_t v_c_519_; uint8_t v___x_520_; 
v___x_518_ = 62;
v_c_519_ = lean_string_utf8_get_fast(v_fst_514_, v_snd_515_);
v___x_520_ = lean_uint32_dec_eq(v_c_519_, v___x_518_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_523_; 
lean_dec(v_res_510_);
v___x_521_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__4);
if (v_isShared_513_ == 0)
{
lean_ctor_set_tag(v___x_512_, 1);
lean_ctor_set(v___x_512_, 1, v___x_521_);
v___x_523_ = v___x_512_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_pos_509_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
else
{
lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_535_; 
lean_inc(v_snd_515_);
lean_inc(v_fst_514_);
v_isSharedCheck_535_ = !lean_is_exclusive(v_pos_509_);
if (v_isSharedCheck_535_ == 0)
{
lean_object* v_unused_536_; lean_object* v_unused_537_; 
v_unused_536_ = lean_ctor_get(v_pos_509_, 1);
lean_dec(v_unused_536_);
v_unused_537_ = lean_ctor_get(v_pos_509_, 0);
lean_dec(v_unused_537_);
v___x_526_ = v_pos_509_;
v_isShared_527_ = v_isSharedCheck_535_;
goto v_resetjp_525_;
}
else
{
lean_dec(v_pos_509_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_535_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v_it_x27_530_; 
v___x_528_ = lean_string_utf8_next_fast(v_fst_514_, v_snd_515_);
lean_dec(v_snd_515_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v___x_528_);
v_it_x27_530_ = v___x_526_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_fst_514_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v___x_528_);
v_it_x27_530_ = v_reuseFailAlloc_534_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_532_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v_it_x27_530_);
v___x_532_ = v___x_512_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_it_x27_530_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_res_510_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
else
{
lean_object* v___x_538_; lean_object* v___x_540_; 
lean_dec(v_res_510_);
v___x_538_ = lean_box(0);
if (v_isShared_513_ == 0)
{
lean_ctor_set_tag(v___x_512_, 1);
lean_ctor_set(v___x_512_, 1, v___x_538_);
v___x_540_ = v___x_512_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_pos_509_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
else
{
return v___x_508_;
}
}
}
}
}
else
{
v___y_488_ = v_pos_492_;
goto v___jp_487_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__0(lean_object* v___x_555_, lean_object* v_x_556_){
_start:
{
uint8_t v___x_557_; 
v___x_557_ = lean_int_dec_le(v_x_556_, v___x_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__0___boxed(lean_object* v___x_558_, lean_object* v_x_559_){
_start:
{
uint8_t v_res_560_; lean_object* v_r_561_; 
v_res_560_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__0(v___x_558_, v_x_559_);
lean_dec(v_x_559_);
lean_dec(v___x_558_);
v_r_561_ = lean_box(v_res_560_);
return v_r_561_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1(uint8_t v___x_562_, lean_object* v_x_563_){
_start:
{
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1___boxed(lean_object* v___x_564_, lean_object* v_x_565_){
_start:
{
uint8_t v___x_2549__boxed_566_; uint8_t v_res_567_; lean_object* v_r_568_; 
v___x_2549__boxed_566_ = lean_unbox(v___x_564_);
v_res_567_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1(v___x_2549__boxed_566_, v_x_565_);
lean_dec(v_x_565_);
v_r_568_ = lean_box(v_res_567_);
return v_r_568_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_unsigned_to_nat(7u);
v___x_572_ = lean_nat_to_int(v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_unsigned_to_nat(5u);
v___x_574_ = lean_nat_to_int(v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4(void){
_start:
{
lean_object* v___x_575_; lean_object* v___f_576_; 
v___x_575_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3);
v___f_576_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_576_, 0, v___x_575_);
return v___f_576_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6(void){
_start:
{
uint32_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = 46;
v___x_579_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_580_ = lean_string_push(v___x_579_, v___x_578_);
return v___x_580_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_581_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6);
v___x_582_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_583_ = lean_string_append(v___x_582_, v___x_581_);
return v___x_583_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_585_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7);
v___x_586_ = lean_string_append(v___x_585_, v___x_584_);
return v___x_586_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8);
v___x_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
return v___x_588_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10(void){
_start:
{
uint32_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = 77;
v___x_590_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_591_ = lean_string_push(v___x_590_, v___x_589_);
return v___x_591_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10);
v___x_593_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_594_ = lean_string_append(v___x_593_, v___x_592_);
return v___x_594_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__12(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_596_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11);
v___x_597_ = lean_string_append(v___x_596_, v___x_595_);
return v___x_597_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__13(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__12, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__12_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__12);
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
return v___x_599_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__14(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_unsigned_to_nat(12u);
v___x_601_ = lean_nat_to_int(v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec(lean_object* v_a_603_){
_start:
{
lean_object* v___y_605_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_631_; lean_object* v___y_635_; lean_object* v___y_639_; lean_object* v___y_640_; uint8_t v___y_641_; lean_object* v_pos_642_; lean_object* v_fst_643_; lean_object* v_snd_644_; lean_object* v_res_645_; lean_object* v___y_681_; uint8_t v___y_682_; lean_object* v_pos_683_; lean_object* v_res_684_; lean_object* v___y_730_; lean_object* v_fst_733_; lean_object* v_snd_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v_fst_733_ = lean_ctor_get(v_a_603_, 0);
v_snd_734_ = lean_ctor_get(v_a_603_, 1);
v___x_735_ = lean_string_utf8_byte_size(v_fst_733_);
v___x_736_ = lean_nat_dec_eq(v_snd_734_, v___x_735_);
if (v___x_736_ == 0)
{
uint32_t v___x_737_; uint32_t v_c_738_; uint8_t v___x_739_; 
v___x_737_ = 77;
v_c_738_ = lean_string_utf8_get_fast(v_fst_733_, v_snd_734_);
v___x_739_ = lean_uint32_dec_eq(v_c_738_, v___x_737_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__13, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__13_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__13);
v___x_741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_741_, 0, v_a_603_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
return v___x_741_;
}
else
{
lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_793_; 
lean_inc(v_snd_734_);
lean_inc(v_fst_733_);
v_isSharedCheck_793_ = !lean_is_exclusive(v_a_603_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; lean_object* v_unused_795_; 
v_unused_794_ = lean_ctor_get(v_a_603_, 1);
lean_dec(v_unused_794_);
v_unused_795_ = lean_ctor_get(v_a_603_, 0);
lean_dec(v_unused_795_);
v___x_743_ = v_a_603_;
v_isShared_744_ = v_isSharedCheck_793_;
goto v_resetjp_742_;
}
else
{
lean_dec(v_a_603_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_793_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___f_746_; lean_object* v___x_747_; lean_object* v_it_x27_749_; 
v___x_745_ = lean_box(v___x_739_);
v___f_746_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1___boxed), 2, 1);
lean_closure_set(v___f_746_, 0, v___x_745_);
v___x_747_ = lean_string_utf8_next_fast(v_fst_733_, v_snd_734_);
lean_dec(v_snd_734_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v___x_747_);
v_it_x27_749_ = v___x_743_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_fst_733_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v___x_747_);
v_it_x27_749_ = v_reuseFailAlloc_792_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_750_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_751_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__14, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__14_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__14);
v___x_752_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__15));
v___x_753_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_750_, v___x_751_, v___x_752_, v___f_746_, v_it_x27_749_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_pos_754_; lean_object* v_res_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_780_; 
v_pos_754_ = lean_ctor_get(v___x_753_, 0);
v_res_755_ = lean_ctor_get(v___x_753_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_780_ == 0)
{
v___x_757_ = v___x_753_;
v_isShared_758_ = v_isSharedCheck_780_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_res_755_);
lean_inc(v_pos_754_);
lean_dec(v___x_753_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_780_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v_fst_759_; lean_object* v_snd_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v_fst_759_ = lean_ctor_get(v_pos_754_, 0);
v_snd_760_ = lean_ctor_get(v_pos_754_, 1);
v___x_761_ = lean_string_utf8_byte_size(v_fst_759_);
v___x_762_ = lean_nat_dec_eq(v_snd_760_, v___x_761_);
if (v___x_762_ == 0)
{
if (v___x_739_ == 0)
{
lean_del_object(v___x_757_);
lean_dec(v_res_755_);
v___y_730_ = v_pos_754_;
goto v___jp_729_;
}
else
{
uint32_t v___x_763_; uint32_t v_c_764_; uint8_t v___x_765_; 
v___x_763_ = 46;
v_c_764_ = lean_string_utf8_get_fast(v_fst_759_, v_snd_760_);
v___x_765_ = lean_uint32_dec_eq(v_c_764_, v___x_763_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_768_; 
lean_dec(v_res_755_);
v___x_766_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9);
if (v_isShared_758_ == 0)
{
lean_ctor_set_tag(v___x_757_, 1);
lean_ctor_set(v___x_757_, 1, v___x_766_);
v___x_768_ = v___x_757_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_pos_754_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
else
{
lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_777_; 
lean_inc(v_snd_760_);
lean_inc(v_fst_759_);
lean_del_object(v___x_757_);
v_isSharedCheck_777_ = !lean_is_exclusive(v_pos_754_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; lean_object* v_unused_779_; 
v_unused_778_ = lean_ctor_get(v_pos_754_, 1);
lean_dec(v_unused_778_);
v_unused_779_ = lean_ctor_get(v_pos_754_, 0);
lean_dec(v_unused_779_);
v___x_771_ = v_pos_754_;
v_isShared_772_ = v_isSharedCheck_777_;
goto v_resetjp_770_;
}
else
{
lean_dec(v_pos_754_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_777_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v_it_x27_775_; 
v___x_773_ = lean_string_utf8_next_fast(v_fst_759_, v_snd_760_);
lean_dec(v_snd_760_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v___x_773_);
v_it_x27_775_ = v___x_771_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_fst_759_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_773_);
v_it_x27_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
v___y_681_ = v___x_750_;
v___y_682_ = v___x_739_;
v_pos_683_ = v_it_x27_775_;
v_res_684_ = v_res_755_;
goto v___jp_680_;
}
}
}
}
}
else
{
lean_del_object(v___x_757_);
lean_dec(v_res_755_);
v___y_730_ = v_pos_754_;
goto v___jp_729_;
}
}
}
else
{
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_pos_781_; lean_object* v_res_782_; 
v_pos_781_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_pos_781_);
v_res_782_ = lean_ctor_get(v___x_753_, 1);
lean_inc(v_res_782_);
lean_dec_ref_known(v___x_753_, 2);
v___y_681_ = v___x_750_;
v___y_682_ = v___x_739_;
v_pos_683_ = v_pos_781_;
v_res_684_ = v_res_782_;
goto v___jp_680_;
}
else
{
lean_object* v_pos_783_; lean_object* v_err_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
v_pos_783_ = lean_ctor_get(v___x_753_, 0);
v_err_784_ = lean_ctor_get(v___x_753_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_753_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_err_784_);
lean_inc(v_pos_783_);
lean_dec(v___x_753_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_pos_783_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_err_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
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
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_box(0);
v___x_797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_797_, 0, v_a_603_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
return v___x_797_;
}
v___jp_604_:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_box(0);
v___x_607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_607_, 0, v___y_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
return v___x_607_;
}
v___jp_608_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_611_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0));
v___x_612_ = l_Nat_reprFast(v___y_610_);
v___x_613_ = lean_string_append(v___x_611_, v___x_612_);
lean_dec_ref(v___x_612_);
v___x_614_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1));
v___x_615_ = lean_string_append(v___x_613_, v___x_614_);
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
v___x_617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_617_, 0, v___y_609_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
return v___x_617_;
}
v___jp_618_:
{
uint8_t v___x_626_; 
v___x_626_ = lean_int_dec_le(v___y_619_, v___y_625_);
if (v___x_626_ == 0)
{
lean_dec(v___y_625_);
lean_dec(v___y_624_);
lean_dec(v___y_622_);
lean_dec(v___y_620_);
v___y_609_ = v___y_621_;
v___y_610_ = v___y_623_;
goto v___jp_608_;
}
else
{
uint8_t v___x_627_; 
v___x_627_ = lean_int_dec_le(v___y_625_, v___y_620_);
lean_dec(v___y_620_);
if (v___x_627_ == 0)
{
lean_dec(v___y_625_);
lean_dec(v___y_624_);
lean_dec(v___y_622_);
v___y_609_ = v___y_621_;
v___y_610_ = v___y_623_;
goto v___jp_608_;
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec(v___y_623_);
v___x_628_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_628_, 0, v___y_622_);
lean_ctor_set(v___x_628_, 1, v___y_624_);
lean_ctor_set(v___x_628_, 2, v___y_625_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___y_621_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
return v___x_629_;
}
}
}
v___jp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_box(0);
v___x_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_633_, 0, v___y_631_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
return v___x_633_;
}
v___jp_634_:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__1));
v___x_637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_637_, 0, v___y_635_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
return v___x_637_;
}
v___jp_638_:
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = lean_string_utf8_byte_size(v_fst_643_);
v___x_647_ = lean_nat_dec_eq(v_snd_644_, v___x_646_);
if (v___x_647_ == 0)
{
if (v___y_641_ == 0)
{
lean_dec(v_res_645_);
lean_dec(v_snd_644_);
lean_dec(v_fst_643_);
lean_dec(v___y_640_);
v___y_631_ = v_pos_642_;
goto v___jp_630_;
}
else
{
uint32_t v_c_648_; uint32_t v___x_649_; uint8_t v___x_650_; 
v_c_648_ = lean_string_utf8_get_fast(v_fst_643_, v_snd_644_);
v___x_649_ = 48;
v___x_650_ = lean_uint32_dec_le(v___x_649_, v_c_648_);
if (v___x_650_ == 0)
{
lean_dec(v_res_645_);
lean_dec(v_snd_644_);
lean_dec(v_fst_643_);
lean_dec(v___y_640_);
v___y_635_ = v_pos_642_;
goto v___jp_634_;
}
else
{
uint32_t v___x_651_; uint8_t v___x_652_; 
v___x_651_ = 57;
v___x_652_ = lean_uint32_dec_le(v_c_648_, v___x_651_);
if (v___x_652_ == 0)
{
lean_dec(v_res_645_);
lean_dec(v_snd_644_);
lean_dec(v_fst_643_);
lean_dec(v___y_640_);
v___y_635_ = v_pos_642_;
goto v___jp_634_;
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v_fst_658_; lean_object* v_snd_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_679_; 
lean_dec_ref(v_pos_642_);
v___x_653_ = lean_string_utf8_next_fast(v_fst_643_, v_snd_644_);
lean_dec(v_snd_644_);
v___x_654_ = lean_uint32_to_nat(v_c_648_);
v___x_655_ = lean_unsigned_to_nat(48u);
v___x_656_ = lean_nat_sub(v___x_654_, v___x_655_);
lean_dec(v___x_654_);
v___x_657_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_643_, v___x_653_, v___x_656_);
v_fst_658_ = lean_ctor_get(v___x_657_, 0);
v_snd_659_ = lean_ctor_get(v___x_657_, 1);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_679_ == 0)
{
v___x_661_ = v___x_657_;
v_isShared_662_ = v_isSharedCheck_679_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_snd_659_);
lean_inc(v_fst_658_);
lean_dec(v___x_657_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_679_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v_fst_643_);
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_fst_643_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_snd_659_);
v___x_664_ = v_reuseFailAlloc_678_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = lean_unsigned_to_nat(6u);
v___x_666_ = lean_nat_dec_lt(v___x_665_, v_fst_658_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_667_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2);
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = lean_nat_dec_eq(v_fst_658_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
lean_inc(v_fst_658_);
v___x_670_ = lean_nat_to_int(v_fst_658_);
v___y_619_ = v___y_639_;
v___y_620_ = v___x_667_;
v___y_621_ = v___x_664_;
v___y_622_ = v___y_640_;
v___y_623_ = v_fst_658_;
v___y_624_ = v_res_645_;
v___y_625_ = v___x_670_;
goto v___jp_618_;
}
else
{
v___y_619_ = v___y_639_;
v___y_620_ = v___x_667_;
v___y_621_ = v___x_664_;
v___y_622_ = v___y_640_;
v___y_623_ = v_fst_658_;
v___y_624_ = v_res_645_;
v___y_625_ = v___x_667_;
goto v___jp_618_;
}
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
lean_dec(v_res_645_);
lean_dec(v___y_640_);
v___x_671_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0));
v___x_672_ = l_Nat_reprFast(v_fst_658_);
v___x_673_ = lean_string_append(v___x_671_, v___x_672_);
lean_dec_ref(v___x_672_);
v___x_674_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1));
v___x_675_ = lean_string_append(v___x_673_, v___x_674_);
v___x_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
v___x_677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_664_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
return v___x_677_;
}
}
}
}
}
}
}
else
{
lean_dec(v_res_645_);
lean_dec(v_snd_644_);
lean_dec(v_fst_643_);
lean_dec(v___y_640_);
v___y_631_ = v_pos_642_;
goto v___jp_630_;
}
}
v___jp_680_:
{
lean_object* v___x_685_; lean_object* v___f_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_685_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3);
v___f_686_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4);
v___x_687_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5));
v___x_688_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___y_681_, v___x_685_, v___x_687_, v___f_686_, v_pos_683_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_pos_689_; lean_object* v_res_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_715_; 
v_pos_689_ = lean_ctor_get(v___x_688_, 0);
v_res_690_ = lean_ctor_get(v___x_688_, 1);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_715_ == 0)
{
v___x_692_ = v___x_688_;
v_isShared_693_ = v_isSharedCheck_715_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_res_690_);
lean_inc(v_pos_689_);
lean_dec(v___x_688_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_715_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_fst_694_; lean_object* v_snd_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v_fst_694_ = lean_ctor_get(v_pos_689_, 0);
v_snd_695_ = lean_ctor_get(v_pos_689_, 1);
v___x_696_ = lean_string_utf8_byte_size(v_fst_694_);
v___x_697_ = lean_nat_dec_eq(v_snd_695_, v___x_696_);
if (v___x_697_ == 0)
{
if (v___y_682_ == 0)
{
lean_del_object(v___x_692_);
lean_dec(v_res_690_);
lean_dec(v_res_684_);
v___y_605_ = v_pos_689_;
goto v___jp_604_;
}
else
{
uint32_t v___x_698_; uint32_t v_c_699_; uint8_t v___x_700_; 
v___x_698_ = 46;
v_c_699_ = lean_string_utf8_get_fast(v_fst_694_, v_snd_695_);
v___x_700_ = lean_uint32_dec_eq(v_c_699_, v___x_698_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_703_; 
lean_dec(v_res_690_);
lean_dec(v_res_684_);
v___x_701_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9);
if (v_isShared_693_ == 0)
{
lean_ctor_set_tag(v___x_692_, 1);
lean_ctor_set(v___x_692_, 1, v___x_701_);
v___x_703_ = v___x_692_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_pos_689_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
else
{
lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_712_; 
lean_inc(v_snd_695_);
lean_inc(v_fst_694_);
lean_del_object(v___x_692_);
v_isSharedCheck_712_ = !lean_is_exclusive(v_pos_689_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; lean_object* v_unused_714_; 
v_unused_713_ = lean_ctor_get(v_pos_689_, 1);
lean_dec(v_unused_713_);
v_unused_714_ = lean_ctor_get(v_pos_689_, 0);
lean_dec(v_unused_714_);
v___x_706_ = v_pos_689_;
v_isShared_707_ = v_isSharedCheck_712_;
goto v_resetjp_705_;
}
else
{
lean_dec(v_pos_689_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_712_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v_it_x27_710_; 
v___x_708_ = lean_string_utf8_next_fast(v_fst_694_, v_snd_695_);
lean_dec(v_snd_695_);
lean_inc(v_fst_694_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v___x_708_);
v_it_x27_710_ = v___x_706_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_fst_694_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v___x_708_);
v_it_x27_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
v___y_639_ = v___y_681_;
v___y_640_ = v_res_684_;
v___y_641_ = v___y_682_;
v_pos_642_ = v_it_x27_710_;
v_fst_643_ = v_fst_694_;
v_snd_644_ = v___x_708_;
v_res_645_ = v_res_690_;
goto v___jp_638_;
}
}
}
}
}
else
{
lean_del_object(v___x_692_);
lean_dec(v_res_690_);
lean_dec(v_res_684_);
v___y_605_ = v_pos_689_;
goto v___jp_604_;
}
}
}
else
{
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_pos_716_; lean_object* v_res_717_; lean_object* v_fst_718_; lean_object* v_snd_719_; 
v_pos_716_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_pos_716_);
v_res_717_ = lean_ctor_get(v___x_688_, 1);
lean_inc(v_res_717_);
lean_dec_ref_known(v___x_688_, 2);
v_fst_718_ = lean_ctor_get(v_pos_716_, 0);
lean_inc(v_fst_718_);
v_snd_719_ = lean_ctor_get(v_pos_716_, 1);
lean_inc(v_snd_719_);
v___y_639_ = v___y_681_;
v___y_640_ = v_res_684_;
v___y_641_ = v___y_682_;
v_pos_642_ = v_pos_716_;
v_fst_643_ = v_fst_718_;
v_snd_644_ = v_snd_719_;
v_res_645_ = v_res_717_;
goto v___jp_638_;
}
else
{
lean_object* v_pos_720_; lean_object* v_err_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec(v_res_684_);
v_pos_720_ = lean_ctor_get(v___x_688_, 0);
v_err_721_ = lean_ctor_get(v___x_688_, 1);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_688_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_err_721_);
lean_inc(v_pos_720_);
lean_dec(v___x_688_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_pos_720_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_err_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
}
v___jp_729_:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_box(0);
v___x_732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_732_, 0, v___y_730_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
return v___x_732_;
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__0(void){
_start:
{
uint32_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_798_ = 74;
v___x_799_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_800_ = lean_string_push(v___x_799_, v___x_798_);
return v___x_800_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__0);
v___x_802_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_803_ = lean_string_append(v___x_802_, v___x_801_);
return v___x_803_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_804_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_805_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1);
v___x_806_ = lean_string_append(v___x_805_, v___x_804_);
return v___x_806_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2);
v___x_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = lean_unsigned_to_nat(365u);
v___x_810_ = lean_nat_to_int(v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec(lean_object* v_a_812_){
_start:
{
lean_object* v_fst_813_; lean_object* v_snd_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_fst_813_ = lean_ctor_get(v_a_812_, 0);
v_snd_814_ = lean_ctor_get(v_a_812_, 1);
v___x_815_ = lean_string_utf8_byte_size(v_fst_813_);
v___x_816_ = lean_nat_dec_eq(v_snd_814_, v___x_815_);
if (v___x_816_ == 0)
{
uint32_t v___x_817_; uint32_t v_c_818_; uint8_t v___x_819_; 
v___x_817_ = 74;
v_c_818_ = lean_string_utf8_get_fast(v_fst_813_, v_snd_814_);
v___x_819_ = lean_uint32_dec_eq(v_c_818_, v___x_817_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3);
v___x_821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_821_, 0, v_a_812_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
return v___x_821_;
}
else
{
lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_854_; 
lean_inc(v_snd_814_);
lean_inc(v_fst_813_);
v_isSharedCheck_854_ = !lean_is_exclusive(v_a_812_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; lean_object* v_unused_856_; 
v_unused_855_ = lean_ctor_get(v_a_812_, 1);
lean_dec(v_unused_855_);
v_unused_856_ = lean_ctor_get(v_a_812_, 0);
lean_dec(v_unused_856_);
v___x_823_ = v_a_812_;
v_isShared_824_ = v_isSharedCheck_854_;
goto v_resetjp_822_;
}
else
{
lean_dec(v_a_812_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_854_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___f_826_; lean_object* v___x_827_; lean_object* v_it_x27_829_; 
v___x_825_ = lean_box(v___x_819_);
v___f_826_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1___boxed), 2, 1);
lean_closure_set(v___f_826_, 0, v___x_825_);
v___x_827_ = lean_string_utf8_next_fast(v_fst_813_, v_snd_814_);
lean_dec(v_snd_814_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v___x_827_);
v_it_x27_829_ = v___x_823_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_fst_813_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v___x_827_);
v_it_x27_829_ = v_reuseFailAlloc_853_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_830_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_831_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4);
v___x_832_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__5));
v___x_833_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_830_, v___x_831_, v___x_832_, v___f_826_, v_it_x27_829_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_pos_834_; lean_object* v_res_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_843_; 
v_pos_834_ = lean_ctor_get(v___x_833_, 0);
v_res_835_ = lean_ctor_get(v___x_833_, 1);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_843_ == 0)
{
v___x_837_ = v___x_833_;
v_isShared_838_ = v_isSharedCheck_843_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_res_835_);
lean_inc(v_pos_834_);
lean_dec(v___x_833_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_843_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_839_, 0, v_res_835_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v___x_839_);
v___x_841_ = v___x_837_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_pos_834_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
else
{
lean_object* v_pos_844_; lean_object* v_err_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_pos_844_ = lean_ctor_get(v___x_833_, 0);
v_err_845_ = lean_ctor_get(v___x_833_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_833_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_err_845_);
lean_inc(v_pos_844_);
lean_dec(v___x_833_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_pos_844_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_err_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_box(0);
v___x_858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_858_, 0, v_a_812_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
return v___x_858_;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0(lean_object* v_x_859_){
_start:
{
uint8_t v___x_860_; 
v___x_860_ = 1;
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0___boxed(lean_object* v_x_861_){
_start:
{
uint8_t v_res_862_; lean_object* v_r_863_; 
v_res_862_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0(v_x_861_);
lean_dec(v_x_861_);
v_r_863_ = lean_box(v_res_862_);
return v_r_863_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec(lean_object* v_a_866_){
_start:
{
lean_object* v___f_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___f_867_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__0));
v___x_868_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___x_869_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4);
v___x_870_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__1));
v___x_871_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_868_, v___x_869_, v___x_870_, v___f_867_, v_a_866_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_pos_872_; lean_object* v_res_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_881_; 
v_pos_872_ = lean_ctor_get(v___x_871_, 0);
v_res_873_ = lean_ctor_get(v___x_871_, 1);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_881_ == 0)
{
v___x_875_ = v___x_871_;
v_isShared_876_ = v_isSharedCheck_881_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_res_873_);
lean_inc(v_pos_872_);
lean_dec(v___x_871_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_881_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_877_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_877_, 0, v_res_873_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 1, v___x_877_);
v___x_879_ = v___x_875_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_pos_872_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
else
{
lean_object* v_pos_882_; lean_object* v_err_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
v_pos_882_ = lean_ctor_get(v___x_871_, 0);
v_err_883_ = lean_ctor_get(v___x_871_, 1);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_871_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_err_883_);
lean_inc(v_pos_882_);
lean_dec(v___x_871_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_pos_882_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_err_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(lean_object* v_stdOffset_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_fst_893_; lean_object* v_snd_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v_fst_893_ = lean_ctor_get(v_a_892_, 0);
v_snd_894_ = lean_ctor_get(v_a_892_, 1);
v___x_895_ = lean_string_utf8_byte_size(v_fst_893_);
v___x_896_ = lean_nat_dec_eq(v_snd_894_, v___x_895_);
if (v___x_896_ == 0)
{
uint32_t v___x_897_; uint8_t v___y_899_; uint32_t v___x_910_; uint8_t v___x_911_; 
v___x_897_ = lean_string_utf8_get_fast(v_fst_893_, v_snd_894_);
v___x_910_ = 48;
v___x_911_ = lean_uint32_dec_le(v___x_910_, v___x_897_);
if (v___x_911_ == 0)
{
v___y_899_ = v___x_911_;
goto v___jp_898_;
}
else
{
uint32_t v___x_912_; uint8_t v___x_913_; 
v___x_912_ = 57;
v___x_913_ = lean_uint32_dec_le(v___x_897_, v___x_912_);
v___y_899_ = v___x_913_;
goto v___jp_898_;
}
v___jp_898_:
{
if (v___y_899_ == 0)
{
uint32_t v___x_900_; uint8_t v___x_901_; 
v___x_900_ = 43;
v___x_901_ = lean_uint32_dec_eq(v___x_897_, v___x_900_);
if (v___x_901_ == 0)
{
uint32_t v___x_902_; uint8_t v___x_903_; 
v___x_902_ = 45;
v___x_903_ = lean_uint32_dec_eq(v___x_897_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_905_ = lean_int_add(v_stdOffset_891_, v___x_904_);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v_a_892_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
return v___x_906_;
}
else
{
lean_object* v___x_907_; 
v___x_907_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_892_);
return v___x_907_;
}
}
else
{
lean_object* v___x_908_; 
v___x_908_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_892_);
return v___x_908_;
}
}
else
{
lean_object* v___x_909_; 
v___x_909_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_892_);
return v___x_909_;
}
}
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_914_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_915_ = lean_int_add(v_stdOffset_891_, v___x_914_);
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v_a_892_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset___boxed(lean_object* v_stdOffset_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(v_stdOffset_917_, v_a_918_);
lean_dec(v_stdOffset_917_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSpec(lean_object* v_a_920_){
_start:
{
lean_object* v_snd_922_; lean_object* v___y_923_; lean_object* v_pos_924_; lean_object* v_snd_925_; lean_object* v___y_929_; lean_object* v_pos_930_; lean_object* v___x_946_; 
lean_inc_ref(v_a_920_);
v___x_946_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec(v_a_920_);
if (lean_obj_tag(v___x_946_) == 0)
{
if (lean_obj_tag(v___x_946_) == 0)
{
lean_dec_ref(v_a_920_);
return v___x_946_;
}
else
{
lean_object* v_pos_947_; 
v_pos_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_pos_947_);
v___y_929_ = v___x_946_;
v_pos_930_ = v_pos_947_;
goto v___jp_928_;
}
}
else
{
lean_object* v_err_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
v_err_948_ = lean_ctor_get(v___x_946_, 1);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_955_ == 0)
{
lean_object* v_unused_956_; 
v_unused_956_ = lean_ctor_get(v___x_946_, 0);
lean_dec(v_unused_956_);
v___x_950_ = v___x_946_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_err_948_);
lean_dec(v___x_946_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
lean_inc_ref(v_a_920_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v_a_920_);
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_920_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_err_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_inc_ref(v_a_920_);
v___y_929_ = v___x_953_;
v_pos_930_ = v_a_920_;
goto v___jp_928_;
}
}
}
v___jp_921_:
{
uint8_t v___x_926_; 
v___x_926_ = lean_nat_dec_eq(v_snd_922_, v_snd_925_);
lean_dec(v_snd_925_);
lean_dec(v_snd_922_);
if (v___x_926_ == 0)
{
lean_dec_ref(v_pos_924_);
return v___y_923_;
}
else
{
lean_object* v___x_927_; 
lean_dec_ref(v___y_923_);
v___x_927_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec(v_pos_924_);
return v___x_927_;
}
}
v___jp_928_:
{
lean_object* v_snd_931_; lean_object* v_snd_932_; uint8_t v___x_933_; 
v_snd_931_ = lean_ctor_get(v_a_920_, 1);
lean_inc(v_snd_931_);
lean_dec_ref(v_a_920_);
v_snd_932_ = lean_ctor_get(v_pos_930_, 1);
lean_inc(v_snd_932_);
v___x_933_ = lean_nat_dec_eq(v_snd_931_, v_snd_932_);
lean_dec(v_snd_931_);
if (v___x_933_ == 0)
{
lean_dec(v_snd_932_);
lean_dec_ref(v_pos_930_);
return v___y_929_;
}
else
{
lean_object* v___x_934_; 
lean_dec_ref(v___y_929_);
lean_inc_ref(v_pos_930_);
v___x_934_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec(v_pos_930_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_dec_ref(v_pos_930_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_dec(v_snd_932_);
return v___x_934_;
}
else
{
lean_object* v_pos_935_; lean_object* v_snd_936_; 
v_pos_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_pos_935_);
v_snd_936_ = lean_ctor_get(v_pos_935_, 1);
lean_inc(v_snd_936_);
v_snd_922_ = v_snd_932_;
v___y_923_ = v___x_934_;
v_pos_924_ = v_pos_935_;
v_snd_925_ = v_snd_936_;
goto v___jp_921_;
}
}
else
{
lean_object* v_err_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
v_err_937_ = lean_ctor_get(v___x_934_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_944_ == 0)
{
lean_object* v_unused_945_; 
v_unused_945_ = lean_ctor_get(v___x_934_, 0);
lean_dec(v_unused_945_);
v___x_939_ = v___x_934_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_err_937_);
lean_dec(v___x_934_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
lean_inc_ref(v_pos_930_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v_pos_930_);
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_pos_930_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_err_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_inc(v_snd_932_);
v_snd_922_ = v_snd_932_;
v___y_923_ = v___x_942_;
v_pos_924_ = v_pos_930_;
v_snd_925_ = v_snd_932_;
goto v___jp_921_;
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
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_unsigned_to_nat(2u);
v___x_958_ = lean_nat_to_int(v___x_957_);
return v___x_958_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_960_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0);
v___x_961_ = lean_int_mul(v___x_960_, v___x_959_);
return v___x_961_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__2(void){
_start:
{
uint32_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = 47;
v___x_963_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_964_ = lean_string_push(v___x_963_, v___x_962_);
return v___x_964_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_965_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__2);
v___x_966_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_967_ = lean_string_append(v___x_966_, v___x_965_);
return v___x_967_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__4(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_968_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_969_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3);
v___x_970_ = lean_string_append(v___x_969_, v___x_968_);
return v___x_970_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__5(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__4);
v___x_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(uint8_t v_extended_973_, lean_object* v_a_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSpec(v_a_974_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_pos_976_; lean_object* v_res_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1021_; 
v_pos_976_ = lean_ctor_get(v___x_975_, 0);
v_res_977_ = lean_ctor_get(v___x_975_, 1);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_979_ = v___x_975_;
v_isShared_980_ = v_isSharedCheck_1021_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_res_977_);
lean_inc(v_pos_976_);
lean_dec(v___x_975_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1021_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v_pos_982_; lean_object* v_res_983_; lean_object* v_fst_988_; lean_object* v_snd_989_; lean_object* v_pos_991_; lean_object* v_snd_992_; lean_object* v_err_993_; lean_object* v___x_997_; uint8_t v___x_998_; 
v_fst_988_ = lean_ctor_get(v_pos_976_, 0);
v_snd_989_ = lean_ctor_get(v_pos_976_, 1);
lean_inc(v_snd_989_);
v___x_997_ = lean_string_utf8_byte_size(v_fst_988_);
v___x_998_ = lean_nat_dec_eq(v_snd_989_, v___x_997_);
if (v___x_998_ == 0)
{
uint32_t v___x_999_; uint32_t v_c_1000_; uint8_t v___x_1001_; 
v___x_999_ = 47;
v_c_1000_ = lean_string_utf8_get_fast(v_fst_988_, v_snd_989_);
v___x_1001_ = lean_uint32_dec_eq(v_c_1000_, v___x_999_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__5);
lean_inc(v_snd_989_);
v_pos_991_ = v_pos_976_;
v_snd_992_ = v_snd_989_;
v_err_993_ = v___x_1002_;
goto v___jp_990_;
}
else
{
lean_object* v___x_1003_; lean_object* v_it_x27_1004_; lean_object* v___x_1005_; 
v___x_1003_ = lean_string_utf8_next_fast(v_fst_988_, v_snd_989_);
lean_inc(v_fst_988_);
v_it_x27_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_1004_, 0, v_fst_988_);
lean_ctor_set(v_it_x27_1004_, 1, v___x_1003_);
v___x_1005_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(v_it_x27_1004_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_pos_1006_; lean_object* v_res_1007_; lean_object* v___y_1009_; 
v_pos_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_pos_1006_);
v_res_1007_ = lean_ctor_get(v___x_1005_, 1);
lean_inc(v_res_1007_);
lean_dec_ref_known(v___x_1005_, 2);
if (v_extended_973_ == 0)
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_unsigned_to_nat(24u);
v___y_1009_ = v___x_1017_;
goto v___jp_1008_;
}
else
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_unsigned_to_nat(167u);
v___y_1009_ = v___x_1018_;
goto v___jp_1008_;
}
v___jp_1008_:
{
lean_object* v___x_1010_; 
v___x_1010_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(v___y_1009_, v_pos_1006_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_pos_1011_; lean_object* v_res_1012_; lean_object* v___x_1013_; 
lean_dec(v_snd_989_);
lean_dec(v_pos_976_);
v_pos_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_pos_1011_);
v_res_1012_ = lean_ctor_get(v___x_1010_, 1);
lean_inc(v_res_1012_);
lean_dec_ref_known(v___x_1010_, 2);
v___x_1013_ = lean_int_mul(v_res_1007_, v_res_1012_);
lean_dec(v_res_1012_);
lean_dec(v_res_1007_);
v_pos_982_ = v_pos_1011_;
v_res_983_ = v___x_1013_;
goto v___jp_981_;
}
else
{
lean_dec(v_res_1007_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_pos_1014_; lean_object* v_res_1015_; 
lean_dec(v_snd_989_);
lean_dec(v_pos_976_);
v_pos_1014_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_pos_1014_);
v_res_1015_ = lean_ctor_get(v___x_1010_, 1);
lean_inc(v_res_1015_);
lean_dec_ref_known(v___x_1010_, 2);
v_pos_982_ = v_pos_1014_;
v_res_983_ = v_res_1015_;
goto v___jp_981_;
}
else
{
lean_object* v_err_1016_; 
v_err_1016_ = lean_ctor_get(v___x_1010_, 1);
lean_inc(v_err_1016_);
lean_dec_ref_known(v___x_1010_, 2);
lean_inc(v_snd_989_);
v_pos_991_ = v_pos_976_;
v_snd_992_ = v_snd_989_;
v_err_993_ = v_err_1016_;
goto v___jp_990_;
}
}
}
}
else
{
lean_object* v_err_1019_; 
v_err_1019_ = lean_ctor_get(v___x_1005_, 1);
lean_inc(v_err_1019_);
lean_dec_ref_known(v___x_1005_, 2);
lean_inc(v_snd_989_);
v_pos_991_ = v_pos_976_;
v_snd_992_ = v_snd_989_;
v_err_993_ = v_err_1019_;
goto v___jp_990_;
}
}
}
else
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_box(0);
lean_inc(v_snd_989_);
v_pos_991_ = v_pos_976_;
v_snd_992_ = v_snd_989_;
v_err_993_ = v___x_1020_;
goto v___jp_990_;
}
v___jp_981_:
{
lean_object* v___x_984_; lean_object* v___x_986_; 
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v_res_977_);
lean_ctor_set(v___x_984_, 1, v_res_983_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v___x_984_);
lean_ctor_set(v___x_979_, 0, v_pos_982_);
v___x_986_ = v___x_979_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_pos_982_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
v___jp_990_:
{
uint8_t v___x_994_; 
v___x_994_ = lean_nat_dec_eq(v_snd_989_, v_snd_992_);
lean_dec(v_snd_992_);
lean_dec(v_snd_989_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; 
lean_del_object(v___x_979_);
lean_dec(v_res_977_);
v___x_995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_995_, 0, v_pos_991_);
lean_ctor_set(v___x_995_, 1, v_err_993_);
return v___x_995_;
}
else
{
lean_object* v___x_996_; 
lean_dec(v_err_993_);
v___x_996_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1);
v_pos_982_ = v_pos_991_;
v_res_983_ = v___x_996_;
goto v___jp_981_;
}
}
}
}
else
{
lean_object* v_pos_1022_; lean_object* v_err_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
v_pos_1022_ = lean_ctor_get(v___x_975_, 0);
v_err_1023_ = lean_ctor_get(v___x_975_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_975_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_err_1023_);
lean_inc(v_pos_1022_);
lean_dec(v___x_975_);
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
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___boxed(lean_object* v_extended_1031_, lean_object* v_a_1032_){
_start:
{
uint8_t v_extended_boxed_1033_; lean_object* v_res_1034_; 
v_extended_boxed_1033_ = lean_unbox(v_extended_1031_);
v_res_1034_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_boxed_1033_, v_a_1032_);
return v_res_1034_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = 44;
v___x_1036_ = lean_box_uint32(v___x_1035_);
return v___x_1036_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0___boxed__const__1;
v___x_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP(uint8_t v_extended_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(v_a_1043_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_pos_1045_; lean_object* v_res_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1236_; 
v_pos_1045_ = lean_ctor_get(v___x_1044_, 0);
v_res_1046_ = lean_ctor_get(v___x_1044_, 1);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1048_ = v___x_1044_;
v_isShared_1049_ = v_isSharedCheck_1236_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_res_1046_);
lean_inc(v_pos_1045_);
lean_dec(v___x_1044_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1236_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1050_ = lean_string_utf8_byte_size(v_res_1046_);
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = lean_nat_dec_eq(v___x_1050_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; 
v___x_1053_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_pos_1045_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_pos_1054_; lean_object* v_res_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1222_; 
v_pos_1054_ = lean_ctor_get(v___x_1053_, 0);
v_res_1055_ = lean_ctor_get(v___x_1053_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1057_ = v___x_1053_;
v_isShared_1058_ = v_isSharedCheck_1222_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_res_1055_);
lean_inc(v_pos_1054_);
lean_dec(v___x_1053_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1222_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; uint32_t v___y_1066_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; uint8_t v___y_1109_; lean_object* v___y_1110_; uint32_t v___y_1111_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v_pos_1141_; lean_object* v_res_1142_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; uint8_t v___y_1172_; lean_object* v_fst_1217_; lean_object* v_snd_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v_fst_1217_ = lean_ctor_get(v_pos_1054_, 0);
v_snd_1218_ = lean_ctor_get(v_pos_1054_, 1);
v___x_1219_ = lean_string_utf8_byte_size(v_fst_1217_);
v___x_1220_ = lean_nat_dec_eq(v_snd_1218_, v___x_1219_);
if (v___x_1220_ == 0)
{
uint8_t v___x_1221_; 
v___x_1221_ = 1;
v___y_1172_ = v___x_1221_;
goto v___jp_1171_;
}
else
{
v___y_1172_ = v___x_1052_;
goto v___jp_1171_;
}
v___jp_1059_:
{
uint32_t v_c_1067_; uint8_t v___x_1068_; 
v_c_1067_ = lean_string_utf8_get_fast(v___y_1063_, v___y_1062_);
v___x_1068_ = lean_uint32_dec_eq(v_c_1067_, v___y_1066_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
lean_dec_ref(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec(v___y_1060_);
lean_dec(v_res_1055_);
lean_dec(v_res_1046_);
v___x_1069_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_1070_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_1071_ = lean_string_push(v___x_1070_, v___y_1066_);
v___x_1072_ = lean_string_append(v___x_1069_, v___x_1071_);
lean_dec_ref(v___x_1071_);
v___x_1073_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_1074_ = lean_string_append(v___x_1072_, v___x_1073_);
v___x_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set_tag(v___x_1057_, 1);
lean_ctor_set(v___x_1057_, 1, v___x_1075_);
lean_ctor_set(v___x_1057_, 0, v___y_1061_);
v___x_1077_ = v___x_1057_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___y_1061_);
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
lean_object* v___x_1079_; lean_object* v_it_x27_1080_; lean_object* v___x_1081_; 
lean_dec_ref(v___y_1061_);
lean_del_object(v___x_1057_);
v___x_1079_ = lean_string_utf8_next_fast(v___y_1063_, v___y_1062_);
lean_dec(v___y_1062_);
v_it_x27_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_1080_, 0, v___y_1063_);
lean_ctor_set(v_it_x27_1080_, 1, v___x_1079_);
v___x_1081_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_1042_, v_it_x27_1080_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_pos_1082_; lean_object* v_res_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1095_; 
v_pos_1082_ = lean_ctor_get(v___x_1081_, 0);
v_res_1083_ = lean_ctor_get(v___x_1081_, 1);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1085_ = v___x_1081_;
v_isShared_1086_ = v_isSharedCheck_1095_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_res_1083_);
lean_inc(v_pos_1082_);
lean_dec(v___x_1081_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1095_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___y_1064_);
v___x_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_res_1083_);
v___x_1089_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1089_, 0, v___y_1065_);
lean_ctor_set(v___x_1089_, 1, v___y_1060_);
lean_ctor_set(v___x_1089_, 2, v___x_1087_);
lean_ctor_set(v___x_1089_, 3, v___x_1088_);
v___x_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
v___x_1091_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1091_, 0, v_res_1046_);
lean_ctor_set(v___x_1091_, 1, v_res_1055_);
lean_ctor_set(v___x_1091_, 2, v___x_1090_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 1, v___x_1091_);
v___x_1093_ = v___x_1085_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_pos_1082_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
else
{
lean_object* v_pos_1096_; lean_object* v_err_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1060_);
lean_dec(v_res_1055_);
lean_dec(v_res_1046_);
v_pos_1096_ = lean_ctor_get(v___x_1081_, 0);
v_err_1097_ = lean_ctor_get(v___x_1081_, 1);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1081_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_err_1097_);
lean_inc(v_pos_1096_);
lean_dec(v___x_1081_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_pos_1096_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_err_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
v___jp_1105_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = lean_string_utf8_next_fast(v___y_1106_, v___y_1108_);
lean_dec(v___y_1108_);
v___x_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___y_1106_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
v___x_1114_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_1042_, v___x_1113_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_pos_1115_; lean_object* v_res_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1128_; 
v_pos_1115_ = lean_ctor_get(v___x_1114_, 0);
v_res_1116_ = lean_ctor_get(v___x_1114_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1118_ = v___x_1114_;
v_isShared_1119_ = v_isSharedCheck_1128_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_res_1116_);
lean_inc(v_pos_1115_);
lean_dec(v___x_1114_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1128_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v_fst_1120_; lean_object* v_snd_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v_fst_1120_ = lean_ctor_get(v_pos_1115_, 0);
v_snd_1121_ = lean_ctor_get(v_pos_1115_, 1);
v___x_1122_ = lean_string_utf8_byte_size(v_fst_1120_);
v___x_1123_ = lean_nat_dec_eq(v_snd_1121_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_inc(v_snd_1121_);
lean_inc(v_fst_1120_);
lean_del_object(v___x_1118_);
v___y_1060_ = v___y_1107_;
v___y_1061_ = v_pos_1115_;
v___y_1062_ = v_snd_1121_;
v___y_1063_ = v_fst_1120_;
v___y_1064_ = v_res_1116_;
v___y_1065_ = v___y_1110_;
v___y_1066_ = v___y_1111_;
goto v___jp_1059_;
}
else
{
if (v___y_1109_ == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
lean_dec(v_res_1116_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1107_);
lean_del_object(v___x_1057_);
lean_dec(v_res_1055_);
lean_dec(v_res_1046_);
v___x_1124_ = lean_box(0);
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 1);
lean_ctor_set(v___x_1118_, 1, v___x_1124_);
v___x_1126_ = v___x_1118_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_pos_1115_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
else
{
lean_inc(v_snd_1121_);
lean_inc(v_fst_1120_);
lean_del_object(v___x_1118_);
v___y_1060_ = v___y_1107_;
v___y_1061_ = v_pos_1115_;
v___y_1062_ = v_snd_1121_;
v___y_1063_ = v_fst_1120_;
v___y_1064_ = v_res_1116_;
v___y_1065_ = v___y_1110_;
v___y_1066_ = v___y_1111_;
goto v___jp_1059_;
}
}
}
}
else
{
lean_object* v_pos_1129_; lean_object* v_err_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1107_);
lean_del_object(v___x_1057_);
lean_dec(v_res_1055_);
lean_dec(v_res_1046_);
v_pos_1129_ = lean_ctor_get(v___x_1114_, 0);
v_err_1130_ = lean_ctor_get(v___x_1114_, 1);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1114_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_err_1130_);
lean_inc(v_pos_1129_);
lean_dec(v___x_1114_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_pos_1129_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_err_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
v___jp_1138_:
{
uint32_t v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; uint8_t v___x_1146_; 
v___x_1143_ = 44;
v___x_1144_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0);
v___x_1145_ = l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_res_1142_, v___x_1144_);
lean_dec(v_res_1142_);
v___x_1146_ = lean_bool_not(v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v_fst_1147_; lean_object* v_snd_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v_fst_1147_ = lean_ctor_get(v_pos_1141_, 0);
v_snd_1148_ = lean_ctor_get(v_pos_1141_, 1);
v___x_1149_ = lean_string_utf8_byte_size(v_fst_1147_);
v___x_1150_ = lean_nat_dec_eq(v_snd_1148_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_inc(v_snd_1148_);
lean_inc(v_fst_1147_);
lean_dec_ref(v_pos_1141_);
lean_del_object(v___x_1048_);
v___y_1106_ = v_fst_1147_;
v___y_1107_ = v___y_1139_;
v___y_1108_ = v_snd_1148_;
v___y_1109_ = v___x_1146_;
v___y_1110_ = v___y_1140_;
v___y_1111_ = v___x_1143_;
goto v___jp_1105_;
}
else
{
if (v___x_1146_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_del_object(v___x_1057_);
lean_dec(v_res_1055_);
lean_dec(v_res_1046_);
v___x_1151_ = lean_box(0);
if (v_isShared_1049_ == 0)
{
lean_ctor_set_tag(v___x_1048_, 1);
lean_ctor_set(v___x_1048_, 1, v___x_1151_);
lean_ctor_set(v___x_1048_, 0, v_pos_1141_);
v___x_1153_ = v___x_1048_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_pos_1141_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
else
{
lean_inc(v_snd_1148_);
lean_inc(v_fst_1147_);
lean_dec_ref(v_pos_1141_);
lean_del_object(v___x_1048_);
v___y_1106_ = v_fst_1147_;
v___y_1107_ = v___y_1139_;
v___y_1108_ = v_snd_1148_;
v___y_1109_ = v___x_1146_;
v___y_1110_ = v___y_1140_;
v___y_1111_ = v___x_1143_;
goto v___jp_1105_;
}
}
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1160_; 
lean_del_object(v___x_1057_);
v___x_1155_ = lean_box(0);
v___x_1156_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1156_, 0, v___y_1140_);
lean_ctor_set(v___x_1156_, 1, v___y_1139_);
lean_ctor_set(v___x_1156_, 2, v___x_1155_);
lean_ctor_set(v___x_1156_, 3, v___x_1155_);
v___x_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
v___x_1158_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1158_, 0, v_res_1046_);
lean_ctor_set(v___x_1158_, 1, v_res_1055_);
lean_ctor_set(v___x_1158_, 2, v___x_1157_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 1, v___x_1158_);
lean_ctor_set(v___x_1048_, 0, v_pos_1141_);
v___x_1160_ = v___x_1048_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_pos_1141_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
v___jp_1162_:
{
uint32_t v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1168_ = lean_string_utf8_get_fast(v___y_1166_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec(v___y_1166_);
v___x_1169_ = lean_box_uint32(v___x_1168_);
v___x_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
v___y_1139_ = v___y_1164_;
v___y_1140_ = v___y_1167_;
v_pos_1141_ = v___y_1163_;
v_res_1142_ = v___x_1170_;
goto v___jp_1138_;
}
v___jp_1171_:
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_bool_not(v___y_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; 
v___x_1174_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(v_pos_1054_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_pos_1175_; lean_object* v_res_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1204_; 
v_pos_1175_ = lean_ctor_get(v___x_1174_, 0);
v_res_1176_ = lean_ctor_get(v___x_1174_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1178_ = v___x_1174_;
v_isShared_1179_ = v_isSharedCheck_1204_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_res_1176_);
lean_inc(v_pos_1175_);
lean_dec(v___x_1174_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1204_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = lean_string_utf8_byte_size(v_res_1176_);
v___x_1181_ = lean_nat_dec_eq(v___x_1180_, v___x_1051_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; 
lean_del_object(v___x_1178_);
v___x_1182_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(v_res_1055_, v_pos_1175_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_pos_1183_; lean_object* v_res_1184_; lean_object* v_fst_1185_; lean_object* v_snd_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v_pos_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_pos_1183_);
v_res_1184_ = lean_ctor_get(v___x_1182_, 1);
lean_inc(v_res_1184_);
lean_dec_ref_known(v___x_1182_, 2);
v_fst_1185_ = lean_ctor_get(v_pos_1183_, 0);
v_snd_1186_ = lean_ctor_get(v_pos_1183_, 1);
v___x_1187_ = lean_string_utf8_byte_size(v_fst_1185_);
v___x_1188_ = lean_nat_dec_eq(v_snd_1186_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_inc(v_snd_1186_);
lean_inc(v_fst_1185_);
v___y_1163_ = v_pos_1183_;
v___y_1164_ = v_res_1184_;
v___y_1165_ = v_snd_1186_;
v___y_1166_ = v_fst_1185_;
v___y_1167_ = v_res_1176_;
goto v___jp_1162_;
}
else
{
if (v___x_1181_ == 0)
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_box(0);
v___y_1139_ = v_res_1184_;
v___y_1140_ = v_res_1176_;
v_pos_1141_ = v_pos_1183_;
v_res_1142_ = v___x_1189_;
goto v___jp_1138_;
}
else
{
lean_inc(v_snd_1186_);
lean_inc(v_fst_1185_);
v___y_1163_ = v_pos_1183_;
v___y_1164_ = v_res_1184_;
v___y_1165_ = v_snd_1186_;
v___y_1166_ = v_fst_1185_;
v___y_1167_ = v_res_1176_;
goto v___jp_1162_;
}
}
}
else
{
lean_object* v_pos_1190_; lean_object* v_err_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec(v_res_1176_);
lean_del_object(v___x_1057_);
lean_dec(v_res_1055_);
lean_del_object(v___x_1048_);
lean_dec(v_res_1046_);
v_pos_1190_ = lean_ctor_get(v___x_1182_, 0);
v_err_1191_ = lean_ctor_get(v___x_1182_, 1);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1182_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_err_1191_);
lean_inc(v_pos_1190_);
lean_dec(v___x_1182_);
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
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
lean_dec(v_res_1176_);
lean_del_object(v___x_1057_);
lean_del_object(v___x_1048_);
v___x_1199_ = lean_box(0);
v___x_1200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1200_, 0, v_res_1046_);
lean_ctor_set(v___x_1200_, 1, v_res_1055_);
lean_ctor_set(v___x_1200_, 2, v___x_1199_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1200_);
v___x_1202_ = v___x_1178_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_pos_1175_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
else
{
lean_object* v_pos_1205_; lean_object* v_err_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_del_object(v___x_1057_);
lean_dec(v_res_1055_);
lean_del_object(v___x_1048_);
lean_dec(v_res_1046_);
v_pos_1205_ = lean_ctor_get(v___x_1174_, 0);
v_err_1206_ = lean_ctor_get(v___x_1174_, 1);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1174_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_err_1206_);
lean_inc(v_pos_1205_);
lean_dec(v___x_1174_);
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
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_del_object(v___x_1057_);
lean_del_object(v___x_1048_);
v___x_1214_ = lean_box(0);
v___x_1215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1215_, 0, v_res_1046_);
lean_ctor_set(v___x_1215_, 1, v_res_1055_);
lean_ctor_set(v___x_1215_, 2, v___x_1214_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v_pos_1054_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
return v___x_1216_;
}
}
}
}
else
{
lean_object* v_pos_1223_; lean_object* v_err_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_del_object(v___x_1048_);
lean_dec(v_res_1046_);
v_pos_1223_ = lean_ctor_get(v___x_1053_, 0);
v_err_1224_ = lean_ctor_get(v___x_1053_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1053_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_err_1224_);
lean_inc(v_pos_1223_);
lean_dec(v___x_1053_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_pos_1223_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_err_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1234_; 
lean_dec(v_res_1046_);
v___x_1232_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2));
if (v_isShared_1049_ == 0)
{
lean_ctor_set_tag(v___x_1048_, 1);
lean_ctor_set(v___x_1048_, 1, v___x_1232_);
v___x_1234_ = v___x_1048_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_pos_1045_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
else
{
lean_object* v_pos_1237_; lean_object* v_err_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
v_pos_1237_ = lean_ctor_get(v___x_1044_, 0);
v_err_1238_ = lean_ctor_get(v___x_1044_, 1);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1044_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_err_1238_);
lean_inc(v_pos_1237_);
lean_dec(v___x_1044_);
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
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___boxed(lean_object* v_extended_1246_, lean_object* v_a_1247_){
_start:
{
uint8_t v_extended_boxed_1248_; lean_object* v_res_1249_; 
v_extended_boxed_1248_ = lean_unbox(v_extended_1246_);
v_res_1249_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP(v_extended_boxed_1248_, v_a_1247_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_parsePosixTz(lean_object* v_s_1250_, uint8_t v_extended_1251_){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1252_ = lean_box(v_extended_1251_);
v___x_1253_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___boxed), 2, 1);
lean_closure_set(v___x_1253_, 0, v___x_1252_);
v___x_1254_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_1253_, v_s_1250_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_parsePosixTz___boxed(lean_object* v_s_1255_, lean_object* v_extended_1256_){
_start:
{
uint8_t v_extended_boxed_1257_; lean_object* v_res_1258_; 
v_extended_boxed_1257_ = lean_unbox(v_extended_1256_);
v_res_1258_ = l_Std_Time_TimeZone_parsePosixTz(v_s_1255_, v_extended_boxed_1257_);
return v_res_1258_;
}
}
lean_object* runtime_initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_Database_PosixTz(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
