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
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__3;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__4;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "empty timezone name"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__5 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__5_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__6 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__6_value;
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
lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_65_; 
lean_inc(v_snd_15_);
lean_inc(v_fst_14_);
v_isSharedCheck_65_ = !lean_is_exclusive(v_a_10_);
if (v_isSharedCheck_65_ == 0)
{
lean_object* v_unused_66_; lean_object* v_unused_67_; 
v_unused_66_ = lean_ctor_get(v_a_10_, 1);
lean_dec(v_unused_66_);
v_unused_67_ = lean_ctor_get(v_a_10_, 0);
lean_dec(v_unused_67_);
v___x_24_ = v_a_10_;
v_isShared_25_ = v_isSharedCheck_65_;
goto v_resetjp_23_;
}
else
{
lean_dec(v_a_10_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_65_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v_fst_31_; lean_object* v_snd_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_64_; 
v___x_26_ = lean_string_utf8_next_fast(v_fst_14_, v_snd_15_);
lean_dec(v_snd_15_);
v___x_27_ = lean_uint32_to_nat(v_c_18_);
v___x_28_ = lean_unsigned_to_nat(48u);
v___x_29_ = lean_nat_sub(v___x_27_, v___x_28_);
lean_dec(v___x_27_);
v___x_30_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_14_, v___x_26_, v___x_29_);
v_fst_31_ = lean_ctor_get(v___x_30_, 0);
v_snd_32_ = lean_ctor_get(v___x_30_, 1);
v_isSharedCheck_64_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_64_ == 0)
{
v___x_34_ = v___x_30_;
v_isShared_35_ = v_isSharedCheck_64_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_snd_32_);
lean_inc(v_fst_31_);
lean_dec(v___x_30_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_64_;
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
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_fst_14_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_snd_32_);
v___x_37_ = v_reuseFailAlloc_63_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
lean_object* v___x_38_; lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_38_ = lean_nat_to_int(v_fst_31_);
lean_inc(v___x_38_);
v___x_50_ = lean_apply_1(v_extra_9_, v___x_38_);
v___x_51_ = lean_unbox(v___x_50_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
lean_del_object(v___x_34_);
v___x_52_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__2));
v___x_53_ = lean_string_append(v_name_8_, v___x_52_);
v___x_54_ = l_Int_repr(v___x_38_);
lean_dec(v___x_38_);
v___x_55_ = lean_string_append(v___x_53_, v___x_54_);
lean_dec_ref(v___x_54_);
v___x_56_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__3));
v___x_57_ = lean_string_append(v___x_55_, v___x_56_);
v___x_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
v___x_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_37_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
return v___x_59_;
}
else
{
uint8_t v___x_60_; 
v___x_60_ = lean_int_dec_le(v_lo_6_, v___x_38_);
if (v___x_60_ == 0)
{
goto v___jp_39_;
}
else
{
uint8_t v___x_61_; 
v___x_61_ = lean_int_dec_le(v___x_38_, v_hi_7_);
if (v___x_61_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v___x_62_; 
lean_del_object(v___x_34_);
lean_dec_ref(v_name_8_);
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_37_);
lean_ctor_set(v___x_62_, 1, v___x_38_);
return v___x_62_;
}
}
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
lean_object* v___x_68_; lean_object* v___x_69_; 
lean_dec_ref(v_extra_9_);
lean_dec_ref(v_name_8_);
v___x_68_ = lean_box(0);
v___x_69_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_69_, 0, v_a_10_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
return v___x_69_;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___boxed(lean_object* v_lo_70_, lean_object* v_hi_71_, lean_object* v_name_72_, lean_object* v_extra_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v_lo_70_, v_hi_71_, v_name_72_, v_extra_73_, v_a_74_);
lean_dec(v_hi_71_);
lean_dec(v_lo_70_);
return v_res_75_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_unsigned_to_nat(1u);
v___x_77_ = lean_nat_to_int(v___x_76_);
return v___x_77_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__3(void){
_start:
{
uint32_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = 43;
v___x_81_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_82_ = lean_string_push(v___x_81_, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__3);
v___x_84_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_85_ = lean_string_append(v___x_84_, v___x_83_);
return v___x_85_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__6(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_88_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4);
v___x_89_ = lean_string_append(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__7(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__6, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__6_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__6);
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
return v___x_91_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__8(void){
_start:
{
uint32_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = 45;
v___x_93_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_94_ = lean_string_push(v___x_93_, v___x_92_);
return v___x_94_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__9(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__8, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__8_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__8);
v___x_96_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_97_ = lean_string_append(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__10(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_99_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__9, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__9_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__9);
v___x_100_ = lean_string_append(v___x_99_, v___x_98_);
return v___x_100_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__11(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__10, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__10_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__10);
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__12(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_104_ = lean_int_neg(v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(lean_object* v_a_105_){
_start:
{
lean_object* v_fst_106_; lean_object* v_snd_107_; lean_object* v_err_109_; lean_object* v_err_117_; lean_object* v___x_138_; uint8_t v___x_139_; 
v_fst_106_ = lean_ctor_get(v_a_105_, 0);
v_snd_107_ = lean_ctor_get(v_a_105_, 1);
v___x_138_ = lean_string_utf8_byte_size(v_fst_106_);
v___x_139_ = lean_nat_dec_eq(v_snd_107_, v___x_138_);
if (v___x_139_ == 0)
{
uint32_t v___x_140_; uint32_t v_c_141_; uint8_t v___x_142_; 
v___x_140_ = 45;
v_c_141_ = lean_string_utf8_get_fast(v_fst_106_, v_snd_107_);
v___x_142_ = lean_uint32_dec_eq(v_c_141_, v___x_140_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
v___x_143_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__11, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__11_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__11);
v_err_117_ = v___x_143_;
goto v___jp_116_;
}
else
{
lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_153_; 
lean_inc(v_snd_107_);
lean_inc(v_fst_106_);
v_isSharedCheck_153_ = !lean_is_exclusive(v_a_105_);
if (v_isSharedCheck_153_ == 0)
{
lean_object* v_unused_154_; lean_object* v_unused_155_; 
v_unused_154_ = lean_ctor_get(v_a_105_, 1);
lean_dec(v_unused_154_);
v_unused_155_ = lean_ctor_get(v_a_105_, 0);
lean_dec(v_unused_155_);
v___x_145_ = v_a_105_;
v_isShared_146_ = v_isSharedCheck_153_;
goto v_resetjp_144_;
}
else
{
lean_dec(v_a_105_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_153_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v_it_x27_149_; 
v___x_147_ = lean_string_utf8_next_fast(v_fst_106_, v_snd_107_);
lean_dec(v_snd_107_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v___x_147_);
v_it_x27_149_ = v___x_145_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_fst_106_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v___x_147_);
v_it_x27_149_ = v_reuseFailAlloc_152_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__12, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__12_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__12);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v_it_x27_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
return v___x_151_;
}
}
}
}
else
{
lean_object* v___x_156_; 
v___x_156_ = lean_box(0);
v_err_117_ = v___x_156_;
goto v___jp_116_;
}
v___jp_108_:
{
uint8_t v___x_110_; 
v___x_110_ = lean_nat_dec_eq(v_snd_107_, v_snd_107_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
lean_inc(v_err_109_);
v___x_111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_111_, 0, v_a_105_);
lean_ctor_set(v___x_111_, 1, v_err_109_);
return v___x_111_;
}
else
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v_a_105_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
return v___x_113_;
}
}
v___jp_114_:
{
lean_object* v___x_115_; 
v___x_115_ = lean_box(0);
v_err_109_ = v___x_115_;
goto v___jp_108_;
}
v___jp_116_:
{
uint8_t v___x_118_; 
v___x_118_ = lean_nat_dec_eq(v_snd_107_, v_snd_107_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; 
lean_inc(v_err_117_);
v___x_119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_119_, 0, v_a_105_);
lean_ctor_set(v___x_119_, 1, v_err_117_);
return v___x_119_;
}
else
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = lean_string_utf8_byte_size(v_fst_106_);
v___x_121_ = lean_nat_dec_eq(v_snd_107_, v___x_120_);
if (v___x_121_ == 0)
{
if (v___x_118_ == 0)
{
goto v___jp_114_;
}
else
{
uint32_t v___x_122_; uint32_t v_c_123_; uint8_t v___x_124_; 
v___x_122_ = 43;
v_c_123_ = lean_string_utf8_get_fast(v_fst_106_, v_snd_107_);
v___x_124_ = lean_uint32_dec_eq(v_c_123_, v___x_122_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
v___x_125_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__7, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__7_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__7);
v_err_109_ = v___x_125_;
goto v___jp_108_;
}
else
{
lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_135_; 
lean_inc(v_snd_107_);
lean_inc(v_fst_106_);
v_isSharedCheck_135_ = !lean_is_exclusive(v_a_105_);
if (v_isSharedCheck_135_ == 0)
{
lean_object* v_unused_136_; lean_object* v_unused_137_; 
v_unused_136_ = lean_ctor_get(v_a_105_, 1);
lean_dec(v_unused_136_);
v_unused_137_ = lean_ctor_get(v_a_105_, 0);
lean_dec(v_unused_137_);
v___x_127_ = v_a_105_;
v_isShared_128_ = v_isSharedCheck_135_;
goto v_resetjp_126_;
}
else
{
lean_dec(v_a_105_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_135_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v_it_x27_131_; 
v___x_129_ = lean_string_utf8_next_fast(v_fst_106_, v_snd_107_);
lean_dec(v_snd_107_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v___x_129_);
v_it_x27_131_ = v___x_127_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_fst_106_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v___x_129_);
v_it_x27_131_ = v_reuseFailAlloc_134_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v_it_x27_131_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
return v___x_133_;
}
}
}
}
}
else
{
goto v___jp_114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__0(lean_object* v_a_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_nat_to_int(v_a_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__2(lean_object* v_a_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Rat_ofInt(v_a_159_);
return v___x_160_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0(uint8_t v___y_161_, lean_object* v_x_162_){
_start:
{
return v___y_161_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed(lean_object* v___y_163_, lean_object* v_x_164_){
_start:
{
uint8_t v___y_3741__boxed_165_; uint8_t v_res_166_; lean_object* v_r_167_; 
v___y_3741__boxed_165_ = lean_unbox(v___y_163_);
v_res_166_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0(v___y_3741__boxed_165_, v_x_164_);
lean_dec(v_x_164_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_unsigned_to_nat(3600u);
v___x_172_ = lean_nat_to_int(v___x_171_);
return v___x_172_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_unsigned_to_nat(60u);
v___x_174_ = lean_nat_to_int(v___x_173_);
return v___x_174_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = lean_nat_to_int(v___x_175_);
return v___x_176_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6(void){
_start:
{
uint32_t v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = 58;
v___x_178_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_179_ = lean_string_push(v___x_178_, v___x_177_);
return v___x_179_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6);
v___x_181_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_182_ = lean_string_append(v___x_181_, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_184_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7);
v___x_185_ = lean_string_append(v___x_184_, v___x_183_);
return v___x_185_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8);
v___x_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
return v___x_187_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_unsigned_to_nat(59u);
v___x_189_ = lean_nat_to_int(v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(lean_object* v_maxHour_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_fst_197_; lean_object* v_snd_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_fst_197_ = lean_ctor_get(v_a_193_, 0);
v_snd_198_ = lean_ctor_get(v_a_193_, 1);
v___x_199_ = lean_string_utf8_byte_size(v_fst_197_);
v___x_200_ = lean_nat_dec_eq(v_snd_198_, v___x_199_);
if (v___x_200_ == 0)
{
uint32_t v_c_201_; uint32_t v___x_202_; uint8_t v___x_203_; 
v_c_201_ = lean_string_utf8_get_fast(v_fst_197_, v_snd_198_);
v___x_202_ = 48;
v___x_203_ = lean_uint32_dec_le(v___x_202_, v_c_201_);
if (v___x_203_ == 0)
{
lean_dec(v_maxHour_192_);
goto v___jp_194_;
}
else
{
uint32_t v___x_204_; uint8_t v___x_205_; 
v___x_204_ = 57;
v___x_205_ = lean_uint32_dec_le(v_c_201_, v___x_204_);
if (v___x_205_ == 0)
{
lean_dec(v_maxHour_192_);
goto v___jp_194_;
}
else
{
lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_324_; 
lean_inc(v_snd_198_);
lean_inc(v_fst_197_);
v_isSharedCheck_324_ = !lean_is_exclusive(v_a_193_);
if (v_isSharedCheck_324_ == 0)
{
lean_object* v_unused_325_; lean_object* v_unused_326_; 
v_unused_325_ = lean_ctor_get(v_a_193_, 1);
lean_dec(v_unused_325_);
v_unused_326_ = lean_ctor_get(v_a_193_, 0);
lean_dec(v_unused_326_);
v___x_207_ = v_a_193_;
v_isShared_208_ = v_isSharedCheck_324_;
goto v_resetjp_206_;
}
else
{
lean_dec(v_a_193_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_324_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v_fst_214_; lean_object* v_snd_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_323_; 
v___x_209_ = lean_string_utf8_next_fast(v_fst_197_, v_snd_198_);
lean_dec(v_snd_198_);
v___x_210_ = lean_uint32_to_nat(v_c_201_);
v___x_211_ = lean_unsigned_to_nat(48u);
v___x_212_ = lean_nat_sub(v___x_210_, v___x_211_);
lean_dec(v___x_210_);
v___x_213_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_197_, v___x_209_, v___x_212_);
v_fst_214_ = lean_ctor_get(v___x_213_, 0);
v_snd_215_ = lean_ctor_get(v___x_213_, 1);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_323_ == 0)
{
v___x_217_ = v___x_213_;
v_isShared_218_ = v_isSharedCheck_323_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_snd_215_);
lean_inc(v_fst_214_);
lean_dec(v___x_213_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_323_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
lean_inc(v_snd_215_);
lean_inc(v_fst_197_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 1, v_snd_215_);
v___x_220_ = v___x_207_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_fst_197_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_snd_215_);
v___x_220_ = v_reuseFailAlloc_322_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
uint8_t v___x_221_; 
v___x_221_ = lean_nat_dec_lt(v_maxHour_192_, v_fst_214_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; uint8_t v___x_223_; 
lean_dec(v_maxHour_192_);
v___x_222_ = lean_unsigned_to_nat(167u);
v___x_223_ = lean_nat_dec_le(v_fst_214_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
lean_dec(v_snd_215_);
lean_dec(v_fst_197_);
v___x_224_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0));
v___x_225_ = l_Nat_reprFast(v_fst_214_);
v___x_226_ = lean_string_append(v___x_224_, v___x_225_);
lean_dec_ref(v___x_225_);
v___x_227_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1));
v___x_228_ = lean_string_append(v___x_226_, v___x_227_);
v___x_229_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2));
v___x_230_ = lean_string_append(v___x_228_, v___x_229_);
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
if (v_isShared_218_ == 0)
{
lean_ctor_set_tag(v___x_217_, 1);
lean_ctor_set(v___x_217_, 1, v___x_231_);
lean_ctor_set(v___x_217_, 0, v___x_220_);
v___x_233_ = v___x_217_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
else
{
lean_object* v___x_235_; lean_object* v___y_237_; lean_object* v_pos_238_; lean_object* v_res_239_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v_err_252_; uint32_t v___x_257_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; uint8_t v___y_263_; lean_object* v_pos_280_; lean_object* v_fst_281_; lean_object* v_snd_282_; lean_object* v_res_283_; lean_object* v_err_287_; uint8_t v___y_292_; uint8_t v___x_310_; 
v___x_235_ = lean_nat_to_int(v_fst_214_);
v___x_257_ = 58;
v___x_310_ = lean_nat_dec_eq(v_snd_215_, v___x_199_);
if (v___x_310_ == 0)
{
v___y_292_ = v___x_223_;
goto v___jp_291_;
}
else
{
v___y_292_ = v___x_221_;
goto v___jp_291_;
}
v___jp_236_:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_240_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_241_ = lean_int_mul(v___x_235_, v___x_240_);
lean_dec(v___x_235_);
v___x_242_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4);
v___x_243_ = lean_int_mul(v___y_237_, v___x_242_);
lean_dec(v___y_237_);
v___x_244_ = lean_int_add(v___x_241_, v___x_243_);
lean_dec(v___x_243_);
lean_dec(v___x_241_);
v___x_245_ = lean_int_add(v___x_244_, v_res_239_);
lean_dec(v_res_239_);
lean_dec(v___x_244_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_245_);
lean_ctor_set(v___x_217_, 0, v_pos_238_);
v___x_247_ = v___x_217_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_pos_238_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
v___jp_249_:
{
lean_object* v_snd_253_; uint8_t v___x_254_; 
v_snd_253_ = lean_ctor_get(v___y_250_, 1);
v___x_254_ = lean_nat_dec_eq(v_snd_253_, v_snd_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
lean_dec(v___y_251_);
lean_dec(v___x_235_);
lean_del_object(v___x_217_);
v___x_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_255_, 0, v___y_250_);
lean_ctor_set(v___x_255_, 1, v_err_252_);
return v___x_255_;
}
else
{
lean_object* v___x_256_; 
lean_dec(v_err_252_);
v___x_256_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___y_237_ = v___y_251_;
v_pos_238_ = v___y_250_;
v_res_239_ = v___x_256_;
goto v___jp_236_;
}
}
v___jp_258_:
{
if (v___y_263_ == 0)
{
lean_object* v___x_264_; 
lean_dec(v___y_261_);
lean_dec(v___y_260_);
v___x_264_ = lean_box(0);
v___y_250_ = v___y_259_;
v___y_251_ = v___y_262_;
v_err_252_ = v___x_264_;
goto v___jp_249_;
}
else
{
uint32_t v_c_265_; uint8_t v___x_266_; 
v_c_265_ = lean_string_utf8_get_fast(v___y_261_, v___y_260_);
v___x_266_ = lean_uint32_dec_eq(v_c_265_, v___x_257_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
lean_dec(v___y_261_);
lean_dec(v___y_260_);
v___x_267_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9);
v___y_250_ = v___y_259_;
v___y_251_ = v___y_262_;
v_err_252_ = v___x_267_;
goto v___jp_249_;
}
else
{
lean_object* v___x_268_; lean_object* v___f_269_; lean_object* v___x_270_; lean_object* v_it_x27_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_268_ = lean_box(v___y_263_);
v___f_269_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_269_, 0, v___x_268_);
v___x_270_ = lean_string_utf8_next_fast(v___y_261_, v___y_260_);
lean_dec(v___y_260_);
v_it_x27_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_271_, 0, v___y_261_);
lean_ctor_set(v_it_x27_271_, 1, v___x_270_);
v___x_272_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___x_273_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10);
v___x_274_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__11));
v___x_275_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_272_, v___x_273_, v___x_274_, v___f_269_, v_it_x27_271_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_pos_276_; lean_object* v_res_277_; 
lean_dec_ref(v___y_259_);
v_pos_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_pos_276_);
v_res_277_ = lean_ctor_get(v___x_275_, 1);
lean_inc(v_res_277_);
lean_dec_ref_known(v___x_275_, 2);
v___y_237_ = v___y_262_;
v_pos_238_ = v_pos_276_;
v_res_239_ = v_res_277_;
goto v___jp_236_;
}
else
{
lean_object* v_err_278_; 
v_err_278_ = lean_ctor_get(v___x_275_, 1);
lean_inc(v_err_278_);
lean_dec_ref_known(v___x_275_, 2);
v___y_250_ = v___y_259_;
v___y_251_ = v___y_262_;
v_err_252_ = v_err_278_;
goto v___jp_249_;
}
}
}
}
v___jp_279_:
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = lean_string_utf8_byte_size(v_fst_281_);
v___x_285_ = lean_nat_dec_eq(v_snd_282_, v___x_284_);
if (v___x_285_ == 0)
{
v___y_259_ = v_pos_280_;
v___y_260_ = v_snd_282_;
v___y_261_ = v_fst_281_;
v___y_262_ = v_res_283_;
v___y_263_ = v___x_223_;
goto v___jp_258_;
}
else
{
v___y_259_ = v_pos_280_;
v___y_260_ = v_snd_282_;
v___y_261_ = v_fst_281_;
v___y_262_ = v_res_283_;
v___y_263_ = v___x_221_;
goto v___jp_258_;
}
}
v___jp_286_:
{
uint8_t v___x_288_; 
v___x_288_ = lean_nat_dec_eq(v_snd_215_, v_snd_215_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; 
lean_dec(v___x_235_);
lean_del_object(v___x_217_);
lean_dec(v_snd_215_);
lean_dec(v_fst_197_);
v___x_289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_220_);
lean_ctor_set(v___x_289_, 1, v_err_287_);
return v___x_289_;
}
else
{
lean_object* v___x_290_; 
lean_dec(v_err_287_);
v___x_290_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v_pos_280_ = v___x_220_;
v_fst_281_ = v_fst_197_;
v_snd_282_ = v_snd_215_;
v_res_283_ = v___x_290_;
goto v___jp_279_;
}
}
v___jp_291_:
{
if (v___y_292_ == 0)
{
lean_object* v___x_293_; 
v___x_293_ = lean_box(0);
v_err_287_ = v___x_293_;
goto v___jp_286_;
}
else
{
uint32_t v_c_294_; uint8_t v___x_295_; 
v_c_294_ = lean_string_utf8_get_fast(v_fst_197_, v_snd_215_);
v___x_295_ = lean_uint32_dec_eq(v_c_294_, v___x_257_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; 
v___x_296_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9);
v_err_287_ = v___x_296_;
goto v___jp_286_;
}
else
{
lean_object* v___x_297_; lean_object* v___f_298_; lean_object* v___x_299_; lean_object* v_it_x27_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_297_ = lean_box(v___y_292_);
v___f_298_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_298_, 0, v___x_297_);
v___x_299_ = lean_string_utf8_next_fast(v_fst_197_, v_snd_215_);
lean_inc(v_fst_197_);
v_it_x27_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_300_, 0, v_fst_197_);
lean_ctor_set(v_it_x27_300_, 1, v___x_299_);
v___x_301_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___x_302_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10);
v___x_303_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__12));
v___x_304_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_301_, v___x_302_, v___x_303_, v___f_298_, v_it_x27_300_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_pos_305_; lean_object* v_res_306_; lean_object* v_fst_307_; lean_object* v_snd_308_; 
lean_dec_ref(v___x_220_);
lean_dec(v_snd_215_);
lean_dec(v_fst_197_);
v_pos_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_pos_305_);
v_res_306_ = lean_ctor_get(v___x_304_, 1);
lean_inc(v_res_306_);
lean_dec_ref_known(v___x_304_, 2);
v_fst_307_ = lean_ctor_get(v_pos_305_, 0);
lean_inc(v_fst_307_);
v_snd_308_ = lean_ctor_get(v_pos_305_, 1);
lean_inc(v_snd_308_);
v_pos_280_ = v_pos_305_;
v_fst_281_ = v_fst_307_;
v_snd_282_ = v_snd_308_;
v_res_283_ = v_res_306_;
goto v___jp_279_;
}
else
{
lean_object* v_err_309_; 
v_err_309_ = lean_ctor_get(v___x_304_, 1);
lean_inc(v_err_309_);
lean_dec_ref_known(v___x_304_, 2);
v_err_287_ = v_err_309_;
goto v___jp_286_;
}
}
}
}
}
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
lean_dec(v_snd_215_);
lean_dec(v_fst_197_);
v___x_311_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0));
v___x_312_ = l_Nat_reprFast(v_fst_214_);
v___x_313_ = lean_string_append(v___x_311_, v___x_312_);
lean_dec_ref(v___x_312_);
v___x_314_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1));
v___x_315_ = lean_string_append(v___x_313_, v___x_314_);
v___x_316_ = l_Nat_reprFast(v_maxHour_192_);
v___x_317_ = lean_string_append(v___x_315_, v___x_316_);
lean_dec_ref(v___x_316_);
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
if (v_isShared_218_ == 0)
{
lean_ctor_set_tag(v___x_217_, 1);
lean_ctor_set(v___x_217_, 1, v___x_318_);
lean_ctor_set(v___x_217_, 0, v___x_220_);
v___x_320_ = v___x_217_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
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
lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec(v_maxHour_192_);
v___x_327_ = lean_box(0);
v___x_328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_328_, 0, v_a_193_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
return v___x_328_;
}
v___jp_194_:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__1));
v___x_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_196_, 0, v_a_193_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__1(lean_object* v_a_329_){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_nat_to_int(v_a_329_);
v___x_331_ = l_Rat_ofInt(v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(lean_object* v_a_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(v_a_332_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_pos_334_; lean_object* v_res_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_pos_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_pos_334_);
v_res_335_ = lean_ctor_get(v___x_333_, 1);
lean_inc(v_res_335_);
lean_dec_ref_known(v___x_333_, 2);
v___x_336_ = lean_unsigned_to_nat(24u);
v___x_337_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(v___x_336_, v_pos_334_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_pos_338_; lean_object* v_res_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_348_; 
v_pos_338_ = lean_ctor_get(v___x_337_, 0);
v_res_339_ = lean_ctor_get(v___x_337_, 1);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_348_ == 0)
{
v___x_341_ = v___x_337_;
v_isShared_342_ = v_isSharedCheck_348_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_res_339_);
lean_inc(v_pos_338_);
lean_dec(v___x_337_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_348_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_343_ = lean_int_neg(v_res_335_);
lean_dec(v_res_335_);
v___x_344_ = lean_int_mul(v___x_343_, v_res_339_);
lean_dec(v_res_339_);
lean_dec(v___x_343_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 1, v___x_344_);
v___x_346_ = v___x_341_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_pos_338_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
else
{
lean_object* v_pos_349_; lean_object* v_err_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec(v_res_335_);
v_pos_349_ = lean_ctor_get(v___x_337_, 0);
v_err_350_ = lean_ctor_get(v___x_337_, 1);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_337_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_err_350_);
lean_inc(v_pos_349_);
lean_dec(v___x_337_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_pos_349_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_err_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v_pos_358_; lean_object* v_err_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
v_pos_358_ = lean_ctor_get(v___x_333_, 0);
v_err_359_ = lean_ctor_get(v___x_333_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_333_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_err_359_);
lean_inc(v_pos_358_);
lean_dec(v___x_333_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_pos_358_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_err_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0(lean_object* v_acc_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_pos_373_; uint32_t v_res_374_; lean_object* v_fst_377_; lean_object* v_snd_378_; lean_object* v_pos_380_; lean_object* v_snd_381_; lean_object* v_err_382_; lean_object* v___x_388_; uint8_t v___x_389_; 
v_fst_377_ = lean_ctor_get(v_a_371_, 0);
v_snd_378_ = lean_ctor_get(v_a_371_, 1);
lean_inc(v_snd_378_);
v___x_388_ = lean_string_utf8_byte_size(v_fst_377_);
v___x_389_ = lean_nat_dec_eq(v_snd_378_, v___x_388_);
if (v___x_389_ == 0)
{
uint32_t v_c_390_; lean_object* v___x_391_; lean_object* v_it_x27_392_; uint8_t v___y_394_; uint8_t v___y_396_; uint8_t v___y_402_; uint32_t v___x_412_; uint8_t v___x_413_; 
v_c_390_ = lean_string_utf8_get_fast(v_fst_377_, v_snd_378_);
v___x_391_ = lean_string_utf8_next_fast(v_fst_377_, v_snd_378_);
lean_inc(v_fst_377_);
v_it_x27_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_392_, 0, v_fst_377_);
lean_ctor_set(v_it_x27_392_, 1, v___x_391_);
v___x_412_ = 65;
v___x_413_ = lean_uint32_dec_le(v___x_412_, v_c_390_);
if (v___x_413_ == 0)
{
goto v___jp_407_;
}
else
{
uint32_t v___x_414_; uint8_t v___x_415_; 
v___x_414_ = 90;
v___x_415_ = lean_uint32_dec_le(v_c_390_, v___x_414_);
if (v___x_415_ == 0)
{
goto v___jp_407_;
}
else
{
lean_dec(v_snd_378_);
lean_dec_ref(v_a_371_);
v_pos_373_ = v_it_x27_392_;
v_res_374_ = v_c_390_;
goto v___jp_372_;
}
}
v___jp_393_:
{
if (v___y_394_ == 0)
{
lean_dec_ref_known(v_it_x27_392_, 2);
goto v___jp_386_;
}
else
{
lean_dec(v_snd_378_);
lean_dec_ref(v_a_371_);
v_pos_373_ = v_it_x27_392_;
v_res_374_ = v_c_390_;
goto v___jp_372_;
}
}
v___jp_395_:
{
if (v___y_396_ == 0)
{
uint32_t v___x_397_; uint8_t v___x_398_; 
v___x_397_ = 43;
v___x_398_ = lean_uint32_dec_eq(v_c_390_, v___x_397_);
if (v___x_398_ == 0)
{
uint32_t v___x_399_; uint8_t v___x_400_; 
v___x_399_ = 45;
v___x_400_ = lean_uint32_dec_eq(v_c_390_, v___x_399_);
if (v___x_400_ == 0)
{
lean_dec_ref_known(v_it_x27_392_, 2);
goto v___jp_386_;
}
else
{
v___y_394_ = v___x_400_;
goto v___jp_393_;
}
}
else
{
v___y_394_ = v___x_398_;
goto v___jp_393_;
}
}
else
{
lean_dec(v_snd_378_);
lean_dec_ref(v_a_371_);
v_pos_373_ = v_it_x27_392_;
v_res_374_ = v_c_390_;
goto v___jp_372_;
}
}
v___jp_401_:
{
if (v___y_402_ == 0)
{
uint32_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = 48;
v___x_404_ = lean_uint32_dec_le(v___x_403_, v_c_390_);
if (v___x_404_ == 0)
{
v___y_396_ = v___x_404_;
goto v___jp_395_;
}
else
{
uint32_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = 57;
v___x_406_ = lean_uint32_dec_le(v_c_390_, v___x_405_);
v___y_396_ = v___x_406_;
goto v___jp_395_;
}
}
else
{
lean_dec(v_snd_378_);
lean_dec_ref(v_a_371_);
v_pos_373_ = v_it_x27_392_;
v_res_374_ = v_c_390_;
goto v___jp_372_;
}
}
v___jp_407_:
{
uint32_t v___x_408_; uint8_t v___x_409_; 
v___x_408_ = 97;
v___x_409_ = lean_uint32_dec_le(v___x_408_, v_c_390_);
if (v___x_409_ == 0)
{
v___y_402_ = v___x_409_;
goto v___jp_401_;
}
else
{
uint32_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = 122;
v___x_411_ = lean_uint32_dec_le(v_c_390_, v___x_410_);
v___y_402_ = v___x_411_;
goto v___jp_401_;
}
}
}
else
{
lean_object* v___x_416_; 
v___x_416_ = lean_box(0);
lean_inc(v_snd_378_);
v_pos_380_ = v_a_371_;
v_snd_381_ = v_snd_378_;
v_err_382_ = v___x_416_;
goto v___jp_379_;
}
v___jp_372_:
{
lean_object* v___x_375_; 
v___x_375_ = lean_string_push(v_acc_370_, v_res_374_);
v_acc_370_ = v___x_375_;
v_a_371_ = v_pos_373_;
goto _start;
}
v___jp_379_:
{
uint8_t v___x_383_; 
v___x_383_ = lean_nat_dec_eq(v_snd_378_, v_snd_381_);
lean_dec(v_snd_381_);
lean_dec(v_snd_378_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; 
lean_dec_ref(v_acc_370_);
lean_inc(v_err_382_);
v___x_384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_384_, 0, v_pos_380_);
lean_ctor_set(v___x_384_, 1, v_err_382_);
return v___x_384_;
}
else
{
lean_object* v___x_385_; 
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_pos_380_);
lean_ctor_set(v___x_385_, 1, v_acc_370_);
return v___x_385_;
}
}
v___jp_386_:
{
lean_object* v___x_387_; 
v___x_387_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__1));
lean_inc(v_snd_378_);
v_pos_380_ = v_a_371_;
v_snd_381_ = v_snd_378_;
v_err_382_ = v___x_387_;
goto v___jp_379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName(lean_object* v_a_417_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_419_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0(v___x_418_, v_a_417_);
return v___x_419_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
if (lean_obj_tag(v_x_420_) == 0)
{
if (lean_obj_tag(v_x_421_) == 0)
{
uint8_t v___x_422_; 
v___x_422_ = 1;
return v___x_422_;
}
else
{
uint8_t v___x_423_; 
v___x_423_ = 0;
return v___x_423_;
}
}
else
{
if (lean_obj_tag(v_x_421_) == 0)
{
uint8_t v___x_424_; 
v___x_424_ = 0;
return v___x_424_;
}
else
{
lean_object* v_val_425_; lean_object* v_val_426_; uint32_t v___x_427_; uint32_t v___x_428_; uint8_t v___x_429_; 
v_val_425_ = lean_ctor_get(v_x_420_, 0);
v_val_426_ = lean_ctor_get(v_x_421_, 0);
v___x_427_ = lean_unbox_uint32(v_val_425_);
v___x_428_ = lean_unbox_uint32(v_val_426_);
v___x_429_ = lean_uint32_dec_eq(v___x_427_, v___x_428_);
return v___x_429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0___boxed(lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
uint8_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_x_430_, v_x_431_);
lean_dec(v_x_431_);
lean_dec(v_x_430_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1(lean_object* v_acc_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_pos_440_; uint32_t v_res_441_; lean_object* v_fst_444_; lean_object* v_snd_445_; lean_object* v_pos_447_; lean_object* v_snd_448_; lean_object* v_err_449_; lean_object* v___x_455_; uint8_t v___x_456_; 
v_fst_444_ = lean_ctor_get(v_a_438_, 0);
v_snd_445_ = lean_ctor_get(v_a_438_, 1);
lean_inc(v_snd_445_);
v___x_455_ = lean_string_utf8_byte_size(v_fst_444_);
v___x_456_ = lean_nat_dec_eq(v_snd_445_, v___x_455_);
if (v___x_456_ == 0)
{
uint32_t v_c_457_; lean_object* v___x_458_; lean_object* v_it_x27_459_; uint32_t v___x_465_; uint8_t v___x_466_; 
v_c_457_ = lean_string_utf8_get_fast(v_fst_444_, v_snd_445_);
v___x_458_ = lean_string_utf8_next_fast(v_fst_444_, v_snd_445_);
lean_inc(v_fst_444_);
v_it_x27_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_459_, 0, v_fst_444_);
lean_ctor_set(v_it_x27_459_, 1, v___x_458_);
v___x_465_ = 65;
v___x_466_ = lean_uint32_dec_le(v___x_465_, v_c_457_);
if (v___x_466_ == 0)
{
goto v___jp_460_;
}
else
{
uint32_t v___x_467_; uint8_t v___x_468_; 
v___x_467_ = 90;
v___x_468_ = lean_uint32_dec_le(v_c_457_, v___x_467_);
if (v___x_468_ == 0)
{
goto v___jp_460_;
}
else
{
lean_dec(v_snd_445_);
lean_dec_ref(v_a_438_);
v_pos_440_ = v_it_x27_459_;
v_res_441_ = v_c_457_;
goto v___jp_439_;
}
}
v___jp_460_:
{
uint32_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = 97;
v___x_462_ = lean_uint32_dec_le(v___x_461_, v_c_457_);
if (v___x_462_ == 0)
{
lean_dec_ref_known(v_it_x27_459_, 2);
goto v___jp_453_;
}
else
{
uint32_t v___x_463_; uint8_t v___x_464_; 
v___x_463_ = 122;
v___x_464_ = lean_uint32_dec_le(v_c_457_, v___x_463_);
if (v___x_464_ == 0)
{
lean_dec_ref_known(v_it_x27_459_, 2);
goto v___jp_453_;
}
else
{
lean_dec(v_snd_445_);
lean_dec_ref(v_a_438_);
v_pos_440_ = v_it_x27_459_;
v_res_441_ = v_c_457_;
goto v___jp_439_;
}
}
}
}
else
{
lean_object* v___x_469_; 
v___x_469_ = lean_box(0);
lean_inc(v_snd_445_);
v_pos_447_ = v_a_438_;
v_snd_448_ = v_snd_445_;
v_err_449_ = v___x_469_;
goto v___jp_446_;
}
v___jp_439_:
{
lean_object* v___x_442_; 
v___x_442_ = lean_string_push(v_acc_437_, v_res_441_);
v_acc_437_ = v___x_442_;
v_a_438_ = v_pos_440_;
goto _start;
}
v___jp_446_:
{
uint8_t v___x_450_; 
v___x_450_ = lean_nat_dec_eq(v_snd_445_, v_snd_448_);
lean_dec(v_snd_448_);
lean_dec(v_snd_445_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; 
lean_dec_ref(v_acc_437_);
lean_inc(v_err_449_);
v___x_451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_451_, 0, v_pos_447_);
lean_ctor_set(v___x_451_, 1, v_err_449_);
return v___x_451_;
}
else
{
lean_object* v___x_452_; 
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v_pos_447_);
lean_ctor_set(v___x_452_, 1, v_acc_437_);
return v___x_452_;
}
}
v___jp_453_:
{
lean_object* v___x_454_; 
v___x_454_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__1));
lean_inc(v_snd_445_);
v_pos_447_ = v_a_438_;
v_snd_448_ = v_snd_445_;
v_err_449_ = v___x_454_;
goto v___jp_446_;
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_470_; lean_object* v___x_471_; 
v___x_470_ = 60;
v___x_471_ = lean_box_uint32(v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0___boxed__const__1;
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__1(void){
_start:
{
uint32_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = 62;
v___x_475_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_476_ = lean_string_push(v___x_475_, v___x_474_);
return v___x_476_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__1, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__1_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__1);
v___x_478_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_479_ = lean_string_append(v___x_478_, v___x_477_);
return v___x_479_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__3(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_481_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2);
v___x_482_ = lean_string_append(v___x_481_, v___x_480_);
return v___x_482_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__4(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__3);
v___x_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(lean_object* v_a_485_){
_start:
{
lean_object* v___y_487_; lean_object* v_pos_491_; lean_object* v_res_492_; lean_object* v_fst_546_; lean_object* v_snd_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v_fst_546_ = lean_ctor_get(v_a_485_, 0);
v_snd_547_ = lean_ctor_get(v_a_485_, 1);
v___x_548_ = lean_string_utf8_byte_size(v_fst_546_);
v___x_549_ = lean_nat_dec_eq(v_snd_547_, v___x_548_);
if (v___x_549_ == 0)
{
uint32_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = lean_string_utf8_get_fast(v_fst_546_, v_snd_547_);
v___x_551_ = lean_box_uint32(v___x_550_);
v___x_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
v_pos_491_ = v_a_485_;
v_res_492_ = v___x_552_;
goto v___jp_490_;
}
else
{
lean_object* v___x_553_; 
v___x_553_ = lean_box(0);
v_pos_491_ = v_a_485_;
v_res_492_ = v___x_553_;
goto v___jp_490_;
}
v___jp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_box(0);
v___x_489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_489_, 0, v___y_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
return v___x_489_;
}
v___jp_490_:
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0);
v___x_494_ = l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_res_492_, v___x_493_);
lean_dec(v_res_492_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_496_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1(v___x_495_, v_pos_491_);
return v___x_496_;
}
else
{
lean_object* v_fst_497_; lean_object* v_snd_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_fst_497_ = lean_ctor_get(v_pos_491_, 0);
v_snd_498_ = lean_ctor_get(v_pos_491_, 1);
v___x_499_ = lean_string_utf8_byte_size(v_fst_497_);
v___x_500_ = lean_nat_dec_eq(v_snd_498_, v___x_499_);
if (v___x_500_ == 0)
{
if (v___x_494_ == 0)
{
v___y_487_ = v_pos_491_;
goto v___jp_486_;
}
else
{
lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_543_; 
lean_inc(v_snd_498_);
lean_inc(v_fst_497_);
v_isSharedCheck_543_ = !lean_is_exclusive(v_pos_491_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; lean_object* v_unused_545_; 
v_unused_544_ = lean_ctor_get(v_pos_491_, 1);
lean_dec(v_unused_544_);
v_unused_545_ = lean_ctor_get(v_pos_491_, 0);
lean_dec(v_unused_545_);
v___x_502_ = v_pos_491_;
v_isShared_503_ = v_isSharedCheck_543_;
goto v_resetjp_501_;
}
else
{
lean_dec(v_pos_491_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_543_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = lean_string_utf8_next_fast(v_fst_497_, v_snd_498_);
lean_dec(v_snd_498_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 1, v___x_504_);
v___x_506_ = v___x_502_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_fst_497_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v___x_504_);
v___x_506_ = v_reuseFailAlloc_542_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_507_; 
v___x_507_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName(v___x_506_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_pos_508_; lean_object* v_res_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_541_; 
v_pos_508_ = lean_ctor_get(v___x_507_, 0);
v_res_509_ = lean_ctor_get(v___x_507_, 1);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_541_ == 0)
{
v___x_511_ = v___x_507_;
v_isShared_512_ = v_isSharedCheck_541_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_res_509_);
lean_inc(v_pos_508_);
lean_dec(v___x_507_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_541_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v_fst_513_; lean_object* v_snd_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v_fst_513_ = lean_ctor_get(v_pos_508_, 0);
v_snd_514_ = lean_ctor_get(v_pos_508_, 1);
v___x_515_ = lean_string_utf8_byte_size(v_fst_513_);
v___x_516_ = lean_nat_dec_eq(v_snd_514_, v___x_515_);
if (v___x_516_ == 0)
{
uint32_t v___x_517_; uint32_t v_c_518_; uint8_t v___x_519_; 
v___x_517_ = 62;
v_c_518_ = lean_string_utf8_get_fast(v_fst_513_, v_snd_514_);
v___x_519_ = lean_uint32_dec_eq(v_c_518_, v___x_517_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_522_; 
lean_dec(v_res_509_);
v___x_520_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__4);
if (v_isShared_512_ == 0)
{
lean_ctor_set_tag(v___x_511_, 1);
lean_ctor_set(v___x_511_, 1, v___x_520_);
v___x_522_ = v___x_511_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_pos_508_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
else
{
lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_534_; 
lean_inc(v_snd_514_);
lean_inc(v_fst_513_);
v_isSharedCheck_534_ = !lean_is_exclusive(v_pos_508_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; lean_object* v_unused_536_; 
v_unused_535_ = lean_ctor_get(v_pos_508_, 1);
lean_dec(v_unused_535_);
v_unused_536_ = lean_ctor_get(v_pos_508_, 0);
lean_dec(v_unused_536_);
v___x_525_ = v_pos_508_;
v_isShared_526_ = v_isSharedCheck_534_;
goto v_resetjp_524_;
}
else
{
lean_dec(v_pos_508_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_534_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v_it_x27_529_; 
v___x_527_ = lean_string_utf8_next_fast(v_fst_513_, v_snd_514_);
lean_dec(v_snd_514_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v___x_527_);
v_it_x27_529_ = v___x_525_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_fst_513_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_527_);
v_it_x27_529_ = v_reuseFailAlloc_533_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_531_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v_it_x27_529_);
v___x_531_ = v___x_511_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_it_x27_529_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_res_509_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
else
{
lean_object* v___x_537_; lean_object* v___x_539_; 
lean_dec(v_res_509_);
v___x_537_ = lean_box(0);
if (v_isShared_512_ == 0)
{
lean_ctor_set_tag(v___x_511_, 1);
lean_ctor_set(v___x_511_, 1, v___x_537_);
v___x_539_ = v___x_511_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_pos_508_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
else
{
return v___x_507_;
}
}
}
}
}
else
{
v___y_487_ = v_pos_491_;
goto v___jp_486_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__0(lean_object* v___x_554_, lean_object* v_x_555_){
_start:
{
uint8_t v___x_556_; 
v___x_556_ = lean_int_dec_le(v_x_555_, v___x_554_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__0___boxed(lean_object* v___x_557_, lean_object* v_x_558_){
_start:
{
uint8_t v_res_559_; lean_object* v_r_560_; 
v_res_559_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__0(v___x_557_, v_x_558_);
lean_dec(v_x_558_);
lean_dec(v___x_557_);
v_r_560_ = lean_box(v_res_559_);
return v_r_560_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1(uint8_t v___x_561_, lean_object* v_x_562_){
_start:
{
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1___boxed(lean_object* v___x_563_, lean_object* v_x_564_){
_start:
{
uint8_t v___x_2549__boxed_565_; uint8_t v_res_566_; lean_object* v_r_567_; 
v___x_2549__boxed_565_ = lean_unbox(v___x_563_);
v_res_566_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1(v___x_2549__boxed_565_, v_x_564_);
lean_dec(v_x_564_);
v_r_567_ = lean_box(v_res_566_);
return v_r_567_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_unsigned_to_nat(7u);
v___x_571_ = lean_nat_to_int(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_unsigned_to_nat(5u);
v___x_573_ = lean_nat_to_int(v___x_572_);
return v___x_573_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4(void){
_start:
{
lean_object* v___x_574_; lean_object* v___f_575_; 
v___x_574_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3);
v___f_575_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__0___boxed), 2, 1);
lean_closure_set(v___f_575_, 0, v___x_574_);
return v___f_575_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6(void){
_start:
{
uint32_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = 46;
v___x_578_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_579_ = lean_string_push(v___x_578_, v___x_577_);
return v___x_579_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_580_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6);
v___x_581_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_582_ = lean_string_append(v___x_581_, v___x_580_);
return v___x_582_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_584_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7);
v___x_585_ = lean_string_append(v___x_584_, v___x_583_);
return v___x_585_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8);
v___x_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10(void){
_start:
{
uint32_t v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = 77;
v___x_589_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_590_ = lean_string_push(v___x_589_, v___x_588_);
return v___x_590_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10);
v___x_592_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_593_ = lean_string_append(v___x_592_, v___x_591_);
return v___x_593_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__12(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_595_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11);
v___x_596_ = lean_string_append(v___x_595_, v___x_594_);
return v___x_596_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__13(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__12, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__12_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__12);
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__14(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_unsigned_to_nat(12u);
v___x_600_ = lean_nat_to_int(v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec(lean_object* v_a_602_){
_start:
{
lean_object* v___y_604_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_630_; lean_object* v___y_634_; lean_object* v___y_638_; lean_object* v___y_639_; uint8_t v___y_640_; lean_object* v_pos_641_; lean_object* v_fst_642_; lean_object* v_snd_643_; lean_object* v_res_644_; lean_object* v___y_680_; uint8_t v___y_681_; lean_object* v_pos_682_; lean_object* v_res_683_; lean_object* v___y_729_; lean_object* v_fst_732_; lean_object* v_snd_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v_fst_732_ = lean_ctor_get(v_a_602_, 0);
v_snd_733_ = lean_ctor_get(v_a_602_, 1);
v___x_734_ = lean_string_utf8_byte_size(v_fst_732_);
v___x_735_ = lean_nat_dec_eq(v_snd_733_, v___x_734_);
if (v___x_735_ == 0)
{
uint32_t v___x_736_; uint32_t v_c_737_; uint8_t v___x_738_; 
v___x_736_ = 77;
v_c_737_ = lean_string_utf8_get_fast(v_fst_732_, v_snd_733_);
v___x_738_ = lean_uint32_dec_eq(v_c_737_, v___x_736_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__13, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__13_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__13);
v___x_740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_740_, 0, v_a_602_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
return v___x_740_;
}
else
{
lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_792_; 
lean_inc(v_snd_733_);
lean_inc(v_fst_732_);
v_isSharedCheck_792_ = !lean_is_exclusive(v_a_602_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; lean_object* v_unused_794_; 
v_unused_793_ = lean_ctor_get(v_a_602_, 1);
lean_dec(v_unused_793_);
v_unused_794_ = lean_ctor_get(v_a_602_, 0);
lean_dec(v_unused_794_);
v___x_742_ = v_a_602_;
v_isShared_743_ = v_isSharedCheck_792_;
goto v_resetjp_741_;
}
else
{
lean_dec(v_a_602_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_792_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___f_745_; lean_object* v___x_746_; lean_object* v_it_x27_748_; 
v___x_744_ = lean_box(v___x_738_);
v___f_745_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1___boxed), 2, 1);
lean_closure_set(v___f_745_, 0, v___x_744_);
v___x_746_ = lean_string_utf8_next_fast(v_fst_732_, v_snd_733_);
lean_dec(v_snd_733_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v___x_746_);
v_it_x27_748_ = v___x_742_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_fst_732_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v___x_746_);
v_it_x27_748_ = v_reuseFailAlloc_791_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_749_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_750_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__14, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__14_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__14);
v___x_751_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__15));
v___x_752_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_749_, v___x_750_, v___x_751_, v___f_745_, v_it_x27_748_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_pos_753_; lean_object* v_res_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_779_; 
v_pos_753_ = lean_ctor_get(v___x_752_, 0);
v_res_754_ = lean_ctor_get(v___x_752_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_779_ == 0)
{
v___x_756_ = v___x_752_;
v_isShared_757_ = v_isSharedCheck_779_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_res_754_);
lean_inc(v_pos_753_);
lean_dec(v___x_752_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_779_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v_fst_758_; lean_object* v_snd_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v_fst_758_ = lean_ctor_get(v_pos_753_, 0);
v_snd_759_ = lean_ctor_get(v_pos_753_, 1);
v___x_760_ = lean_string_utf8_byte_size(v_fst_758_);
v___x_761_ = lean_nat_dec_eq(v_snd_759_, v___x_760_);
if (v___x_761_ == 0)
{
if (v___x_738_ == 0)
{
lean_del_object(v___x_756_);
lean_dec(v_res_754_);
v___y_729_ = v_pos_753_;
goto v___jp_728_;
}
else
{
uint32_t v___x_762_; uint32_t v_c_763_; uint8_t v___x_764_; 
v___x_762_ = 46;
v_c_763_ = lean_string_utf8_get_fast(v_fst_758_, v_snd_759_);
v___x_764_ = lean_uint32_dec_eq(v_c_763_, v___x_762_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_767_; 
lean_dec(v_res_754_);
v___x_765_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9);
if (v_isShared_757_ == 0)
{
lean_ctor_set_tag(v___x_756_, 1);
lean_ctor_set(v___x_756_, 1, v___x_765_);
v___x_767_ = v___x_756_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_pos_753_);
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
lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_776_; 
lean_inc(v_snd_759_);
lean_inc(v_fst_758_);
lean_del_object(v___x_756_);
v_isSharedCheck_776_ = !lean_is_exclusive(v_pos_753_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; lean_object* v_unused_778_; 
v_unused_777_ = lean_ctor_get(v_pos_753_, 1);
lean_dec(v_unused_777_);
v_unused_778_ = lean_ctor_get(v_pos_753_, 0);
lean_dec(v_unused_778_);
v___x_770_ = v_pos_753_;
v_isShared_771_ = v_isSharedCheck_776_;
goto v_resetjp_769_;
}
else
{
lean_dec(v_pos_753_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_776_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v_it_x27_774_; 
v___x_772_ = lean_string_utf8_next_fast(v_fst_758_, v_snd_759_);
lean_dec(v_snd_759_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v___x_772_);
v_it_x27_774_ = v___x_770_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_fst_758_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v___x_772_);
v_it_x27_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
v___y_680_ = v___x_749_;
v___y_681_ = v___x_738_;
v_pos_682_ = v_it_x27_774_;
v_res_683_ = v_res_754_;
goto v___jp_679_;
}
}
}
}
}
else
{
lean_del_object(v___x_756_);
lean_dec(v_res_754_);
v___y_729_ = v_pos_753_;
goto v___jp_728_;
}
}
}
else
{
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_pos_780_; lean_object* v_res_781_; 
v_pos_780_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_pos_780_);
v_res_781_ = lean_ctor_get(v___x_752_, 1);
lean_inc(v_res_781_);
lean_dec_ref_known(v___x_752_, 2);
v___y_680_ = v___x_749_;
v___y_681_ = v___x_738_;
v_pos_682_ = v_pos_780_;
v_res_683_ = v_res_781_;
goto v___jp_679_;
}
else
{
lean_object* v_pos_782_; lean_object* v_err_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
v_pos_782_ = lean_ctor_get(v___x_752_, 0);
v_err_783_ = lean_ctor_get(v___x_752_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_752_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_err_783_);
lean_inc(v_pos_782_);
lean_dec(v___x_752_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_pos_782_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_err_783_);
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
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_box(0);
v___x_796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_796_, 0, v_a_602_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
return v___x_796_;
}
v___jp_603_:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_box(0);
v___x_606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_606_, 0, v___y_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
return v___x_606_;
}
v___jp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_610_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0));
v___x_611_ = l_Nat_reprFast(v___y_609_);
v___x_612_ = lean_string_append(v___x_610_, v___x_611_);
lean_dec_ref(v___x_611_);
v___x_613_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1));
v___x_614_ = lean_string_append(v___x_612_, v___x_613_);
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
v___x_616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_616_, 0, v___y_608_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
return v___x_616_;
}
v___jp_617_:
{
uint8_t v___x_625_; 
v___x_625_ = lean_int_dec_le(v___y_618_, v___y_624_);
if (v___x_625_ == 0)
{
lean_dec(v___y_624_);
lean_dec(v___y_623_);
lean_dec(v___y_621_);
lean_dec(v___y_619_);
v___y_608_ = v___y_620_;
v___y_609_ = v___y_622_;
goto v___jp_607_;
}
else
{
uint8_t v___x_626_; 
v___x_626_ = lean_int_dec_le(v___y_624_, v___y_619_);
lean_dec(v___y_619_);
if (v___x_626_ == 0)
{
lean_dec(v___y_624_);
lean_dec(v___y_623_);
lean_dec(v___y_621_);
v___y_608_ = v___y_620_;
v___y_609_ = v___y_622_;
goto v___jp_607_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; 
lean_dec(v___y_622_);
v___x_627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_627_, 0, v___y_621_);
lean_ctor_set(v___x_627_, 1, v___y_623_);
lean_ctor_set(v___x_627_, 2, v___y_624_);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v___y_620_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
return v___x_628_;
}
}
}
v___jp_629_:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_box(0);
v___x_632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_632_, 0, v___y_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
return v___x_632_;
}
v___jp_633_:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__1));
v___x_636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_636_, 0, v___y_634_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
return v___x_636_;
}
v___jp_637_:
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = lean_string_utf8_byte_size(v_fst_642_);
v___x_646_ = lean_nat_dec_eq(v_snd_643_, v___x_645_);
if (v___x_646_ == 0)
{
if (v___y_640_ == 0)
{
lean_dec(v_res_644_);
lean_dec(v_snd_643_);
lean_dec(v_fst_642_);
lean_dec(v___y_639_);
v___y_630_ = v_pos_641_;
goto v___jp_629_;
}
else
{
uint32_t v_c_647_; uint32_t v___x_648_; uint8_t v___x_649_; 
v_c_647_ = lean_string_utf8_get_fast(v_fst_642_, v_snd_643_);
v___x_648_ = 48;
v___x_649_ = lean_uint32_dec_le(v___x_648_, v_c_647_);
if (v___x_649_ == 0)
{
lean_dec(v_res_644_);
lean_dec(v_snd_643_);
lean_dec(v_fst_642_);
lean_dec(v___y_639_);
v___y_634_ = v_pos_641_;
goto v___jp_633_;
}
else
{
uint32_t v___x_650_; uint8_t v___x_651_; 
v___x_650_ = 57;
v___x_651_ = lean_uint32_dec_le(v_c_647_, v___x_650_);
if (v___x_651_ == 0)
{
lean_dec(v_res_644_);
lean_dec(v_snd_643_);
lean_dec(v_fst_642_);
lean_dec(v___y_639_);
v___y_634_ = v_pos_641_;
goto v___jp_633_;
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v_fst_657_; lean_object* v_snd_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref(v_pos_641_);
v___x_652_ = lean_string_utf8_next_fast(v_fst_642_, v_snd_643_);
lean_dec(v_snd_643_);
v___x_653_ = lean_uint32_to_nat(v_c_647_);
v___x_654_ = lean_unsigned_to_nat(48u);
v___x_655_ = lean_nat_sub(v___x_653_, v___x_654_);
lean_dec(v___x_653_);
v___x_656_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_642_, v___x_652_, v___x_655_);
v_fst_657_ = lean_ctor_get(v___x_656_, 0);
v_snd_658_ = lean_ctor_get(v___x_656_, 1);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_678_ == 0)
{
v___x_660_ = v___x_656_;
v_isShared_661_ = v_isSharedCheck_678_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_snd_658_);
lean_inc(v_fst_657_);
lean_dec(v___x_656_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_678_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v_fst_642_);
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_fst_642_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_snd_658_);
v___x_663_ = v_reuseFailAlloc_677_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = lean_unsigned_to_nat(6u);
v___x_665_ = lean_nat_dec_lt(v___x_664_, v_fst_657_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_666_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2);
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = lean_nat_dec_eq(v_fst_657_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
lean_inc(v_fst_657_);
v___x_669_ = lean_nat_to_int(v_fst_657_);
v___y_618_ = v___y_638_;
v___y_619_ = v___x_666_;
v___y_620_ = v___x_663_;
v___y_621_ = v___y_639_;
v___y_622_ = v_fst_657_;
v___y_623_ = v_res_644_;
v___y_624_ = v___x_669_;
goto v___jp_617_;
}
else
{
v___y_618_ = v___y_638_;
v___y_619_ = v___x_666_;
v___y_620_ = v___x_663_;
v___y_621_ = v___y_639_;
v___y_622_ = v_fst_657_;
v___y_623_ = v_res_644_;
v___y_624_ = v___x_666_;
goto v___jp_617_;
}
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec(v_res_644_);
lean_dec(v___y_639_);
v___x_670_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0));
v___x_671_ = l_Nat_reprFast(v_fst_657_);
v___x_672_ = lean_string_append(v___x_670_, v___x_671_);
lean_dec_ref(v___x_671_);
v___x_673_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1));
v___x_674_ = lean_string_append(v___x_672_, v___x_673_);
v___x_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
v___x_676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_663_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
return v___x_676_;
}
}
}
}
}
}
}
else
{
lean_dec(v_res_644_);
lean_dec(v_snd_643_);
lean_dec(v_fst_642_);
lean_dec(v___y_639_);
v___y_630_ = v_pos_641_;
goto v___jp_629_;
}
}
v___jp_679_:
{
lean_object* v___x_684_; lean_object* v___f_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_684_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3);
v___f_685_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4);
v___x_686_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5));
v___x_687_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___y_680_, v___x_684_, v___x_686_, v___f_685_, v_pos_682_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_pos_688_; lean_object* v_res_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_714_; 
v_pos_688_ = lean_ctor_get(v___x_687_, 0);
v_res_689_ = lean_ctor_get(v___x_687_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_714_ == 0)
{
v___x_691_ = v___x_687_;
v_isShared_692_ = v_isSharedCheck_714_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_res_689_);
lean_inc(v_pos_688_);
lean_dec(v___x_687_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_714_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v_fst_693_; lean_object* v_snd_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v_fst_693_ = lean_ctor_get(v_pos_688_, 0);
v_snd_694_ = lean_ctor_get(v_pos_688_, 1);
v___x_695_ = lean_string_utf8_byte_size(v_fst_693_);
v___x_696_ = lean_nat_dec_eq(v_snd_694_, v___x_695_);
if (v___x_696_ == 0)
{
if (v___y_681_ == 0)
{
lean_del_object(v___x_691_);
lean_dec(v_res_689_);
lean_dec(v_res_683_);
v___y_604_ = v_pos_688_;
goto v___jp_603_;
}
else
{
uint32_t v___x_697_; uint32_t v_c_698_; uint8_t v___x_699_; 
v___x_697_ = 46;
v_c_698_ = lean_string_utf8_get_fast(v_fst_693_, v_snd_694_);
v___x_699_ = lean_uint32_dec_eq(v_c_698_, v___x_697_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_702_; 
lean_dec(v_res_689_);
lean_dec(v_res_683_);
v___x_700_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9);
if (v_isShared_692_ == 0)
{
lean_ctor_set_tag(v___x_691_, 1);
lean_ctor_set(v___x_691_, 1, v___x_700_);
v___x_702_ = v___x_691_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_pos_688_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
else
{
lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_711_; 
lean_inc(v_snd_694_);
lean_inc(v_fst_693_);
lean_del_object(v___x_691_);
v_isSharedCheck_711_ = !lean_is_exclusive(v_pos_688_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; lean_object* v_unused_713_; 
v_unused_712_ = lean_ctor_get(v_pos_688_, 1);
lean_dec(v_unused_712_);
v_unused_713_ = lean_ctor_get(v_pos_688_, 0);
lean_dec(v_unused_713_);
v___x_705_ = v_pos_688_;
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
else
{
lean_dec(v_pos_688_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v_it_x27_709_; 
v___x_707_ = lean_string_utf8_next_fast(v_fst_693_, v_snd_694_);
lean_dec(v_snd_694_);
lean_inc(v_fst_693_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 1, v___x_707_);
v_it_x27_709_ = v___x_705_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_fst_693_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_707_);
v_it_x27_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
v___y_638_ = v___y_680_;
v___y_639_ = v_res_683_;
v___y_640_ = v___y_681_;
v_pos_641_ = v_it_x27_709_;
v_fst_642_ = v_fst_693_;
v_snd_643_ = v___x_707_;
v_res_644_ = v_res_689_;
goto v___jp_637_;
}
}
}
}
}
else
{
lean_del_object(v___x_691_);
lean_dec(v_res_689_);
lean_dec(v_res_683_);
v___y_604_ = v_pos_688_;
goto v___jp_603_;
}
}
}
else
{
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_pos_715_; lean_object* v_res_716_; lean_object* v_fst_717_; lean_object* v_snd_718_; 
v_pos_715_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_pos_715_);
v_res_716_ = lean_ctor_get(v___x_687_, 1);
lean_inc(v_res_716_);
lean_dec_ref_known(v___x_687_, 2);
v_fst_717_ = lean_ctor_get(v_pos_715_, 0);
lean_inc(v_fst_717_);
v_snd_718_ = lean_ctor_get(v_pos_715_, 1);
lean_inc(v_snd_718_);
v___y_638_ = v___y_680_;
v___y_639_ = v_res_683_;
v___y_640_ = v___y_681_;
v_pos_641_ = v_pos_715_;
v_fst_642_ = v_fst_717_;
v_snd_643_ = v_snd_718_;
v_res_644_ = v_res_716_;
goto v___jp_637_;
}
else
{
lean_object* v_pos_719_; lean_object* v_err_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec(v_res_683_);
v_pos_719_ = lean_ctor_get(v___x_687_, 0);
v_err_720_ = lean_ctor_get(v___x_687_, 1);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_687_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_err_720_);
lean_inc(v_pos_719_);
lean_dec(v___x_687_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_pos_719_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_err_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
v___jp_728_:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_box(0);
v___x_731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_731_, 0, v___y_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
return v___x_731_;
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__0(void){
_start:
{
uint32_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_797_ = 74;
v___x_798_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_799_ = lean_string_push(v___x_798_, v___x_797_);
return v___x_799_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_800_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__0);
v___x_801_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_802_ = lean_string_append(v___x_801_, v___x_800_);
return v___x_802_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_803_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_804_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1);
v___x_805_ = lean_string_append(v___x_804_, v___x_803_);
return v___x_805_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2);
v___x_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
return v___x_807_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_unsigned_to_nat(365u);
v___x_809_ = lean_nat_to_int(v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec(lean_object* v_a_811_){
_start:
{
lean_object* v_fst_812_; lean_object* v_snd_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v_fst_812_ = lean_ctor_get(v_a_811_, 0);
v_snd_813_ = lean_ctor_get(v_a_811_, 1);
v___x_814_ = lean_string_utf8_byte_size(v_fst_812_);
v___x_815_ = lean_nat_dec_eq(v_snd_813_, v___x_814_);
if (v___x_815_ == 0)
{
uint32_t v___x_816_; uint32_t v_c_817_; uint8_t v___x_818_; 
v___x_816_ = 74;
v_c_817_ = lean_string_utf8_get_fast(v_fst_812_, v_snd_813_);
v___x_818_ = lean_uint32_dec_eq(v_c_817_, v___x_816_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3);
v___x_820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_820_, 0, v_a_811_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
return v___x_820_;
}
else
{
lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_853_; 
lean_inc(v_snd_813_);
lean_inc(v_fst_812_);
v_isSharedCheck_853_ = !lean_is_exclusive(v_a_811_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; lean_object* v_unused_855_; 
v_unused_854_ = lean_ctor_get(v_a_811_, 1);
lean_dec(v_unused_854_);
v_unused_855_ = lean_ctor_get(v_a_811_, 0);
lean_dec(v_unused_855_);
v___x_822_ = v_a_811_;
v_isShared_823_ = v_isSharedCheck_853_;
goto v_resetjp_821_;
}
else
{
lean_dec(v_a_811_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_853_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___f_825_; lean_object* v___x_826_; lean_object* v_it_x27_828_; 
v___x_824_ = lean_box(v___x_818_);
v___f_825_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1___boxed), 2, 1);
lean_closure_set(v___f_825_, 0, v___x_824_);
v___x_826_ = lean_string_utf8_next_fast(v_fst_812_, v_snd_813_);
lean_dec(v_snd_813_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v___x_826_);
v_it_x27_828_ = v___x_822_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_fst_812_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v___x_826_);
v_it_x27_828_ = v_reuseFailAlloc_852_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_829_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_830_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4);
v___x_831_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__5));
v___x_832_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_829_, v___x_830_, v___x_831_, v___f_825_, v_it_x27_828_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_pos_833_; lean_object* v_res_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_842_; 
v_pos_833_ = lean_ctor_get(v___x_832_, 0);
v_res_834_ = lean_ctor_get(v___x_832_, 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_842_ == 0)
{
v___x_836_ = v___x_832_;
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_res_834_);
lean_inc(v_pos_833_);
lean_dec(v___x_832_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v_res_834_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v___x_838_);
v___x_840_ = v___x_836_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_pos_833_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
else
{
lean_object* v_pos_843_; lean_object* v_err_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
v_pos_843_ = lean_ctor_get(v___x_832_, 0);
v_err_844_ = lean_ctor_get(v___x_832_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_832_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_err_844_);
lean_inc(v_pos_843_);
lean_dec(v___x_832_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_pos_843_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_err_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = lean_box(0);
v___x_857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_857_, 0, v_a_811_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
return v___x_857_;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0(lean_object* v_x_858_){
_start:
{
uint8_t v___x_859_; 
v___x_859_ = 1;
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0___boxed(lean_object* v_x_860_){
_start:
{
uint8_t v_res_861_; lean_object* v_r_862_; 
v_res_861_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0(v_x_860_);
lean_dec(v_x_860_);
v_r_862_ = lean_box(v_res_861_);
return v_r_862_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec(lean_object* v_a_865_){
_start:
{
lean_object* v___f_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___f_866_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__0));
v___x_867_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___x_868_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__4);
v___x_869_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__1));
v___x_870_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_867_, v___x_868_, v___x_869_, v___f_866_, v_a_865_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_pos_871_; lean_object* v_res_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_880_; 
v_pos_871_ = lean_ctor_get(v___x_870_, 0);
v_res_872_ = lean_ctor_get(v___x_870_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_880_ == 0)
{
v___x_874_ = v___x_870_;
v_isShared_875_ = v_isSharedCheck_880_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_res_872_);
lean_inc(v_pos_871_);
lean_dec(v___x_870_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_880_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_876_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_876_, 0, v_res_872_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 1, v___x_876_);
v___x_878_ = v___x_874_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_pos_871_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
else
{
lean_object* v_pos_881_; lean_object* v_err_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
v_pos_881_ = lean_ctor_get(v___x_870_, 0);
v_err_882_ = lean_ctor_get(v___x_870_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_870_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_err_882_);
lean_inc(v_pos_881_);
lean_dec(v___x_870_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_pos_881_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_err_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(lean_object* v_stdOffset_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_fst_892_; lean_object* v_snd_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v_fst_892_ = lean_ctor_get(v_a_891_, 0);
v_snd_893_ = lean_ctor_get(v_a_891_, 1);
v___x_894_ = lean_string_utf8_byte_size(v_fst_892_);
v___x_895_ = lean_nat_dec_eq(v_snd_893_, v___x_894_);
if (v___x_895_ == 0)
{
uint32_t v___x_896_; uint8_t v___y_898_; uint32_t v___x_909_; uint8_t v___x_910_; 
v___x_896_ = lean_string_utf8_get_fast(v_fst_892_, v_snd_893_);
v___x_909_ = 48;
v___x_910_ = lean_uint32_dec_le(v___x_909_, v___x_896_);
if (v___x_910_ == 0)
{
v___y_898_ = v___x_910_;
goto v___jp_897_;
}
else
{
uint32_t v___x_911_; uint8_t v___x_912_; 
v___x_911_ = 57;
v___x_912_ = lean_uint32_dec_le(v___x_896_, v___x_911_);
v___y_898_ = v___x_912_;
goto v___jp_897_;
}
v___jp_897_:
{
if (v___y_898_ == 0)
{
uint32_t v___x_899_; uint8_t v___x_900_; 
v___x_899_ = 43;
v___x_900_ = lean_uint32_dec_eq(v___x_896_, v___x_899_);
if (v___x_900_ == 0)
{
uint32_t v___x_901_; uint8_t v___x_902_; 
v___x_901_ = 45;
v___x_902_ = lean_uint32_dec_eq(v___x_896_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_904_ = lean_int_add(v_stdOffset_890_, v___x_903_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v_a_891_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
return v___x_905_;
}
else
{
lean_object* v___x_906_; 
v___x_906_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_891_);
return v___x_906_;
}
}
else
{
lean_object* v___x_907_; 
v___x_907_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_891_);
return v___x_907_;
}
}
else
{
lean_object* v___x_908_; 
v___x_908_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_891_);
return v___x_908_;
}
}
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_914_ = lean_int_add(v_stdOffset_890_, v___x_913_);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v_a_891_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
return v___x_915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset___boxed(lean_object* v_stdOffset_916_, lean_object* v_a_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(v_stdOffset_916_, v_a_917_);
lean_dec(v_stdOffset_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSpec(lean_object* v_a_919_){
_start:
{
lean_object* v_snd_921_; lean_object* v___y_922_; lean_object* v_pos_923_; lean_object* v_snd_924_; lean_object* v___y_928_; lean_object* v_pos_929_; lean_object* v___x_945_; 
lean_inc_ref(v_a_919_);
v___x_945_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec(v_a_919_);
if (lean_obj_tag(v___x_945_) == 0)
{
if (lean_obj_tag(v___x_945_) == 0)
{
lean_dec_ref(v_a_919_);
return v___x_945_;
}
else
{
lean_object* v_pos_946_; 
v_pos_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_pos_946_);
v___y_928_ = v___x_945_;
v_pos_929_ = v_pos_946_;
goto v___jp_927_;
}
}
else
{
lean_object* v_err_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
v_err_947_ = lean_ctor_get(v___x_945_, 1);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_954_ == 0)
{
lean_object* v_unused_955_; 
v_unused_955_ = lean_ctor_get(v___x_945_, 0);
lean_dec(v_unused_955_);
v___x_949_ = v___x_945_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_err_947_);
lean_dec(v___x_945_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
lean_inc_ref(v_a_919_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v_a_919_);
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_919_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_err_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_inc_ref(v_a_919_);
v___y_928_ = v___x_952_;
v_pos_929_ = v_a_919_;
goto v___jp_927_;
}
}
}
v___jp_920_:
{
uint8_t v___x_925_; 
v___x_925_ = lean_nat_dec_eq(v_snd_921_, v_snd_924_);
lean_dec(v_snd_924_);
lean_dec(v_snd_921_);
if (v___x_925_ == 0)
{
lean_dec_ref(v_pos_923_);
return v___y_922_;
}
else
{
lean_object* v___x_926_; 
lean_dec_ref(v___y_922_);
v___x_926_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec(v_pos_923_);
return v___x_926_;
}
}
v___jp_927_:
{
lean_object* v_snd_930_; lean_object* v_snd_931_; uint8_t v___x_932_; 
v_snd_930_ = lean_ctor_get(v_a_919_, 1);
lean_inc(v_snd_930_);
lean_dec_ref(v_a_919_);
v_snd_931_ = lean_ctor_get(v_pos_929_, 1);
lean_inc(v_snd_931_);
v___x_932_ = lean_nat_dec_eq(v_snd_930_, v_snd_931_);
lean_dec(v_snd_930_);
if (v___x_932_ == 0)
{
lean_dec(v_snd_931_);
lean_dec_ref(v_pos_929_);
return v___y_928_;
}
else
{
lean_object* v___x_933_; 
lean_dec_ref(v___y_928_);
lean_inc_ref(v_pos_929_);
v___x_933_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec(v_pos_929_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_dec_ref(v_pos_929_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_dec(v_snd_931_);
return v___x_933_;
}
else
{
lean_object* v_pos_934_; lean_object* v_snd_935_; 
v_pos_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_pos_934_);
v_snd_935_ = lean_ctor_get(v_pos_934_, 1);
lean_inc(v_snd_935_);
v_snd_921_ = v_snd_931_;
v___y_922_ = v___x_933_;
v_pos_923_ = v_pos_934_;
v_snd_924_ = v_snd_935_;
goto v___jp_920_;
}
}
else
{
lean_object* v_err_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
v_err_936_ = lean_ctor_get(v___x_933_, 1);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_943_ == 0)
{
lean_object* v_unused_944_; 
v_unused_944_ = lean_ctor_get(v___x_933_, 0);
lean_dec(v_unused_944_);
v___x_938_ = v___x_933_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_err_936_);
lean_dec(v___x_933_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
lean_inc_ref(v_pos_929_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v_pos_929_);
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_pos_929_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_err_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_inc(v_snd_931_);
v_snd_921_ = v_snd_931_;
v___y_922_ = v___x_941_;
v_pos_923_ = v_pos_929_;
v_snd_924_ = v_snd_931_;
goto v___jp_920_;
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
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_unsigned_to_nat(2u);
v___x_957_ = lean_nat_to_int(v___x_956_);
return v___x_957_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_958_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_959_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0);
v___x_960_ = lean_int_mul(v___x_959_, v___x_958_);
return v___x_960_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__2(void){
_start:
{
uint32_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_961_ = 47;
v___x_962_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_963_ = lean_string_push(v___x_962_, v___x_961_);
return v___x_963_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_964_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__2);
v___x_965_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_966_ = lean_string_append(v___x_965_, v___x_964_);
return v___x_966_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__4(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_968_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3);
v___x_969_ = lean_string_append(v___x_968_, v___x_967_);
return v___x_969_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__5(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__4);
v___x_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(uint8_t v_extended_972_, lean_object* v_a_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSpec(v_a_973_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_pos_975_; lean_object* v_res_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1020_; 
v_pos_975_ = lean_ctor_get(v___x_974_, 0);
v_res_976_ = lean_ctor_get(v___x_974_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_978_ = v___x_974_;
v_isShared_979_ = v_isSharedCheck_1020_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_res_976_);
lean_inc(v_pos_975_);
lean_dec(v___x_974_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1020_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_pos_981_; lean_object* v_res_982_; lean_object* v_fst_987_; lean_object* v_snd_988_; lean_object* v_pos_990_; lean_object* v_snd_991_; lean_object* v_err_992_; lean_object* v___x_996_; uint8_t v___x_997_; 
v_fst_987_ = lean_ctor_get(v_pos_975_, 0);
v_snd_988_ = lean_ctor_get(v_pos_975_, 1);
lean_inc(v_snd_988_);
v___x_996_ = lean_string_utf8_byte_size(v_fst_987_);
v___x_997_ = lean_nat_dec_eq(v_snd_988_, v___x_996_);
if (v___x_997_ == 0)
{
uint32_t v___x_998_; uint32_t v_c_999_; uint8_t v___x_1000_; 
v___x_998_ = 47;
v_c_999_ = lean_string_utf8_get_fast(v_fst_987_, v_snd_988_);
v___x_1000_ = lean_uint32_dec_eq(v_c_999_, v___x_998_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__5);
lean_inc(v_snd_988_);
v_pos_990_ = v_pos_975_;
v_snd_991_ = v_snd_988_;
v_err_992_ = v___x_1001_;
goto v___jp_989_;
}
else
{
lean_object* v___x_1002_; lean_object* v_it_x27_1003_; lean_object* v___x_1004_; 
v___x_1002_ = lean_string_utf8_next_fast(v_fst_987_, v_snd_988_);
lean_inc(v_fst_987_);
v_it_x27_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_1003_, 0, v_fst_987_);
lean_ctor_set(v_it_x27_1003_, 1, v___x_1002_);
v___x_1004_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(v_it_x27_1003_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_pos_1005_; lean_object* v_res_1006_; lean_object* v___y_1008_; 
v_pos_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_pos_1005_);
v_res_1006_ = lean_ctor_get(v___x_1004_, 1);
lean_inc(v_res_1006_);
lean_dec_ref_known(v___x_1004_, 2);
if (v_extended_972_ == 0)
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_unsigned_to_nat(24u);
v___y_1008_ = v___x_1016_;
goto v___jp_1007_;
}
else
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_unsigned_to_nat(167u);
v___y_1008_ = v___x_1017_;
goto v___jp_1007_;
}
v___jp_1007_:
{
lean_object* v___x_1009_; 
v___x_1009_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(v___y_1008_, v_pos_1005_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_pos_1010_; lean_object* v_res_1011_; lean_object* v___x_1012_; 
lean_dec(v_snd_988_);
lean_dec(v_pos_975_);
v_pos_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_pos_1010_);
v_res_1011_ = lean_ctor_get(v___x_1009_, 1);
lean_inc(v_res_1011_);
lean_dec_ref_known(v___x_1009_, 2);
v___x_1012_ = lean_int_mul(v_res_1006_, v_res_1011_);
lean_dec(v_res_1011_);
lean_dec(v_res_1006_);
v_pos_981_ = v_pos_1010_;
v_res_982_ = v___x_1012_;
goto v___jp_980_;
}
else
{
lean_dec(v_res_1006_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_pos_1013_; lean_object* v_res_1014_; 
lean_dec(v_snd_988_);
lean_dec(v_pos_975_);
v_pos_1013_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_pos_1013_);
v_res_1014_ = lean_ctor_get(v___x_1009_, 1);
lean_inc(v_res_1014_);
lean_dec_ref_known(v___x_1009_, 2);
v_pos_981_ = v_pos_1013_;
v_res_982_ = v_res_1014_;
goto v___jp_980_;
}
else
{
lean_object* v_err_1015_; 
v_err_1015_ = lean_ctor_get(v___x_1009_, 1);
lean_inc(v_err_1015_);
lean_dec_ref_known(v___x_1009_, 2);
lean_inc(v_snd_988_);
v_pos_990_ = v_pos_975_;
v_snd_991_ = v_snd_988_;
v_err_992_ = v_err_1015_;
goto v___jp_989_;
}
}
}
}
else
{
lean_object* v_err_1018_; 
v_err_1018_ = lean_ctor_get(v___x_1004_, 1);
lean_inc(v_err_1018_);
lean_dec_ref_known(v___x_1004_, 2);
lean_inc(v_snd_988_);
v_pos_990_ = v_pos_975_;
v_snd_991_ = v_snd_988_;
v_err_992_ = v_err_1018_;
goto v___jp_989_;
}
}
}
else
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_box(0);
lean_inc(v_snd_988_);
v_pos_990_ = v_pos_975_;
v_snd_991_ = v_snd_988_;
v_err_992_ = v___x_1019_;
goto v___jp_989_;
}
v___jp_980_:
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_983_, 0, v_res_976_);
lean_ctor_set(v___x_983_, 1, v_res_982_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v___x_983_);
lean_ctor_set(v___x_978_, 0, v_pos_981_);
v___x_985_ = v___x_978_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_pos_981_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
v___jp_989_:
{
uint8_t v___x_993_; 
v___x_993_ = lean_nat_dec_eq(v_snd_988_, v_snd_991_);
lean_dec(v_snd_991_);
lean_dec(v_snd_988_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; 
lean_del_object(v___x_978_);
lean_dec(v_res_976_);
v___x_994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_994_, 0, v_pos_990_);
lean_ctor_set(v___x_994_, 1, v_err_992_);
return v___x_994_;
}
else
{
lean_object* v___x_995_; 
lean_dec(v_err_992_);
v___x_995_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1);
v_pos_981_ = v_pos_990_;
v_res_982_ = v___x_995_;
goto v___jp_980_;
}
}
}
}
else
{
lean_object* v_pos_1021_; lean_object* v_err_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
v_pos_1021_ = lean_ctor_get(v___x_974_, 0);
v_err_1022_ = lean_ctor_get(v___x_974_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_974_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_err_1022_);
lean_inc(v_pos_1021_);
lean_dec(v___x_974_);
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
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___boxed(lean_object* v_extended_1030_, lean_object* v_a_1031_){
_start:
{
uint8_t v_extended_boxed_1032_; lean_object* v_res_1033_; 
v_extended_boxed_1032_ = lean_unbox(v_extended_1030_);
v_res_1033_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_boxed_1032_, v_a_1031_);
return v_res_1033_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = 44;
v___x_1035_ = lean_box_uint32(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0___boxed__const__1;
v___x_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
return v___x_1037_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1(void){
_start:
{
uint32_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = 44;
v___x_1039_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v___x_1040_ = lean_string_push(v___x_1039_, v___x_1038_);
return v___x_1040_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1041_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1);
v___x_1042_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1));
v___x_1043_ = lean_string_append(v___x_1042_, v___x_1041_);
return v___x_1043_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__3(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1044_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5));
v___x_1045_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2);
v___x_1046_ = lean_string_append(v___x_1045_, v___x_1044_);
return v___x_1046_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__4(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__3);
v___x_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP(uint8_t v_extended_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v___y_1055_; lean_object* v___x_1058_; 
v___x_1058_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(v_a_1053_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_pos_1059_; lean_object* v_res_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1247_; 
v_pos_1059_ = lean_ctor_get(v___x_1058_, 0);
v_res_1060_ = lean_ctor_get(v___x_1058_, 1);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1062_ = v___x_1058_;
v_isShared_1063_ = v_isSharedCheck_1247_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_res_1060_);
lean_inc(v_pos_1059_);
lean_dec(v___x_1058_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1247_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1064_ = lean_string_utf8_byte_size(v_res_1060_);
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = lean_nat_dec_eq(v___x_1064_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; 
v___x_1067_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_pos_1059_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_pos_1068_; lean_object* v_res_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1233_; 
v_pos_1068_ = lean_ctor_get(v___x_1067_, 0);
v_res_1069_ = lean_ctor_get(v___x_1067_, 1);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1071_ = v___x_1067_;
v_isShared_1072_ = v_isSharedCheck_1233_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_res_1069_);
lean_inc(v_pos_1068_);
lean_dec(v___x_1067_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1233_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v_pos_1074_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1092_; lean_object* v___y_1093_; uint8_t v___y_1094_; lean_object* v_pos_1095_; lean_object* v_res_1096_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; uint8_t v___y_1183_; lean_object* v___y_1184_; lean_object* v_fst_1229_; lean_object* v_snd_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v_fst_1229_ = lean_ctor_get(v_pos_1068_, 0);
v_snd_1230_ = lean_ctor_get(v_pos_1068_, 1);
v___x_1231_ = lean_string_utf8_byte_size(v_fst_1229_);
v___x_1232_ = lean_nat_dec_eq(v_snd_1230_, v___x_1231_);
if (v___x_1232_ == 0)
{
goto v___jp_1188_;
}
else
{
if (v___x_1066_ == 0)
{
lean_del_object(v___x_1062_);
v_pos_1074_ = v_pos_1068_;
goto v___jp_1073_;
}
else
{
goto v___jp_1188_;
}
}
v___jp_1073_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1075_ = lean_box(0);
v___x_1076_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1076_, 0, v_res_1060_);
lean_ctor_set(v___x_1076_, 1, v_res_1069_);
lean_ctor_set(v___x_1076_, 2, v___x_1075_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v___x_1076_);
lean_ctor_set(v___x_1071_, 0, v_pos_1074_);
v___x_1078_ = v___x_1071_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_pos_1074_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
v___jp_1080_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1084_ = lean_box(0);
v___x_1085_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1085_, 0, v___y_1082_);
lean_ctor_set(v___x_1085_, 1, v___y_1081_);
lean_ctor_set(v___x_1085_, 2, v___x_1084_);
lean_ctor_set(v___x_1085_, 3, v___x_1084_);
v___x_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1087_, 0, v_res_1060_);
lean_ctor_set(v___x_1087_, 1, v_res_1069_);
lean_ctor_set(v___x_1087_, 2, v___x_1086_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 1, v___x_1087_);
lean_ctor_set(v___x_1062_, 0, v___y_1083_);
v___x_1089_ = v___x_1062_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___y_1083_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
v___jp_1091_:
{
uint32_t v___x_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1097_ = 44;
v___x_1098_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0);
v___x_1099_ = l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_res_1096_, v___x_1098_);
lean_dec(v_res_1096_);
if (v___x_1099_ == 0)
{
v___y_1081_ = v___y_1092_;
v___y_1082_ = v___y_1093_;
v___y_1083_ = v_pos_1095_;
goto v___jp_1080_;
}
else
{
if (v___y_1094_ == 0)
{
lean_object* v_fst_1100_; lean_object* v_snd_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
lean_del_object(v___x_1062_);
v_fst_1100_ = lean_ctor_get(v_pos_1095_, 0);
v_snd_1101_ = lean_ctor_get(v_pos_1095_, 1);
v___x_1102_ = lean_string_utf8_byte_size(v_fst_1100_);
v___x_1103_ = lean_nat_dec_eq(v_snd_1101_, v___x_1102_);
if (v___x_1103_ == 0)
{
if (v___x_1099_ == 0)
{
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec(v_res_1069_);
lean_dec(v_res_1060_);
v___y_1055_ = v_pos_1095_;
goto v___jp_1054_;
}
else
{
lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1175_; 
lean_inc(v_snd_1101_);
lean_inc(v_fst_1100_);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_pos_1095_);
if (v_isSharedCheck_1175_ == 0)
{
lean_object* v_unused_1176_; lean_object* v_unused_1177_; 
v_unused_1176_ = lean_ctor_get(v_pos_1095_, 1);
lean_dec(v_unused_1176_);
v_unused_1177_ = lean_ctor_get(v_pos_1095_, 0);
lean_dec(v_unused_1177_);
v___x_1105_ = v_pos_1095_;
v_isShared_1106_ = v_isSharedCheck_1175_;
goto v_resetjp_1104_;
}
else
{
lean_dec(v_pos_1095_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1175_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1107_ = lean_string_utf8_next_fast(v_fst_1100_, v_snd_1101_);
lean_dec(v_snd_1101_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 1, v___x_1107_);
v___x_1109_ = v___x_1105_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_fst_1100_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1110_; 
v___x_1110_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_1052_, v___x_1109_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_pos_1111_; lean_object* v_res_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1164_; 
v_pos_1111_ = lean_ctor_get(v___x_1110_, 0);
v_res_1112_ = lean_ctor_get(v___x_1110_, 1);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1114_ = v___x_1110_;
v_isShared_1115_ = v_isSharedCheck_1164_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_res_1112_);
lean_inc(v_pos_1111_);
lean_dec(v___x_1110_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1164_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v_fst_1116_; lean_object* v_snd_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v_fst_1116_ = lean_ctor_get(v_pos_1111_, 0);
v_snd_1117_ = lean_ctor_get(v_pos_1111_, 1);
v___x_1118_ = lean_string_utf8_byte_size(v_fst_1116_);
v___x_1119_ = lean_nat_dec_eq(v_snd_1117_, v___x_1118_);
if (v___x_1119_ == 0)
{
uint32_t v_c_1120_; uint8_t v___x_1121_; 
v_c_1120_ = lean_string_utf8_get_fast(v_fst_1116_, v_snd_1117_);
v___x_1121_ = lean_uint32_dec_eq(v_c_1120_, v___x_1097_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1124_; 
lean_dec(v_res_1112_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec(v_res_1069_);
lean_dec(v_res_1060_);
v___x_1122_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__4);
if (v_isShared_1115_ == 0)
{
lean_ctor_set_tag(v___x_1114_, 1);
lean_ctor_set(v___x_1114_, 1, v___x_1122_);
v___x_1124_ = v___x_1114_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_pos_1111_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
else
{
lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1157_; 
lean_inc(v_snd_1117_);
lean_inc(v_fst_1116_);
lean_del_object(v___x_1114_);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_pos_1111_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; lean_object* v_unused_1159_; 
v_unused_1158_ = lean_ctor_get(v_pos_1111_, 1);
lean_dec(v_unused_1158_);
v_unused_1159_ = lean_ctor_get(v_pos_1111_, 0);
lean_dec(v_unused_1159_);
v___x_1127_ = v_pos_1111_;
v_isShared_1128_ = v_isSharedCheck_1157_;
goto v_resetjp_1126_;
}
else
{
lean_dec(v_pos_1111_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1157_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v_it_x27_1131_; 
v___x_1129_ = lean_string_utf8_next_fast(v_fst_1116_, v_snd_1117_);
lean_dec(v_snd_1117_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 1, v___x_1129_);
v_it_x27_1131_ = v___x_1127_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_fst_1116_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v___x_1129_);
v_it_x27_1131_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1132_; 
v___x_1132_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_1052_, v_it_x27_1131_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_pos_1133_; lean_object* v_res_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1146_; 
v_pos_1133_ = lean_ctor_get(v___x_1132_, 0);
v_res_1134_ = lean_ctor_get(v___x_1132_, 1);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1136_ = v___x_1132_;
v_isShared_1137_ = v_isSharedCheck_1146_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_res_1134_);
lean_inc(v_pos_1133_);
lean_dec(v___x_1132_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1146_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1138_, 0, v_res_1112_);
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v_res_1134_);
v___x_1140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1140_, 0, v___y_1093_);
lean_ctor_set(v___x_1140_, 1, v___y_1092_);
lean_ctor_set(v___x_1140_, 2, v___x_1138_);
lean_ctor_set(v___x_1140_, 3, v___x_1139_);
v___x_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
v___x_1142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1142_, 0, v_res_1060_);
lean_ctor_set(v___x_1142_, 1, v_res_1069_);
lean_ctor_set(v___x_1142_, 2, v___x_1141_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___x_1142_);
v___x_1144_ = v___x_1136_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_pos_1133_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
else
{
lean_object* v_pos_1147_; lean_object* v_err_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec(v_res_1112_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec(v_res_1069_);
lean_dec(v_res_1060_);
v_pos_1147_ = lean_ctor_get(v___x_1132_, 0);
v_err_1148_ = lean_ctor_get(v___x_1132_, 1);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1132_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_err_1148_);
lean_inc(v_pos_1147_);
lean_dec(v___x_1132_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_pos_1147_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_err_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1162_; 
lean_dec(v_res_1112_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec(v_res_1069_);
lean_dec(v_res_1060_);
v___x_1160_ = lean_box(0);
if (v_isShared_1115_ == 0)
{
lean_ctor_set_tag(v___x_1114_, 1);
lean_ctor_set(v___x_1114_, 1, v___x_1160_);
v___x_1162_ = v___x_1114_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_pos_1111_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
else
{
lean_object* v_pos_1165_; lean_object* v_err_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec(v_res_1069_);
lean_dec(v_res_1060_);
v_pos_1165_ = lean_ctor_get(v___x_1110_, 0);
v_err_1166_ = lean_ctor_get(v___x_1110_, 1);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1110_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_err_1166_);
lean_inc(v_pos_1165_);
lean_dec(v___x_1110_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_pos_1165_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_err_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec(v_res_1069_);
lean_dec(v_res_1060_);
v___y_1055_ = v_pos_1095_;
goto v___jp_1054_;
}
}
else
{
v___y_1081_ = v___y_1092_;
v___y_1082_ = v___y_1093_;
v___y_1083_ = v_pos_1095_;
goto v___jp_1080_;
}
}
}
v___jp_1178_:
{
uint32_t v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = lean_string_utf8_get_fast(v___y_1181_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec(v___y_1181_);
v___x_1186_ = lean_box_uint32(v___x_1185_);
v___x_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
v___y_1092_ = v___y_1179_;
v___y_1093_ = v___y_1180_;
v___y_1094_ = v___y_1183_;
v_pos_1095_ = v___y_1182_;
v_res_1096_ = v___x_1187_;
goto v___jp_1091_;
}
v___jp_1188_:
{
if (v___x_1066_ == 0)
{
lean_object* v___x_1189_; 
lean_del_object(v___x_1071_);
v___x_1189_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(v_pos_1068_);
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
v___x_1196_ = lean_nat_dec_eq(v___x_1195_, v___x_1065_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; 
lean_del_object(v___x_1193_);
v___x_1197_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(v_res_1069_, v_pos_1190_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_pos_1198_; lean_object* v_res_1199_; lean_object* v_fst_1200_; lean_object* v_snd_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v_pos_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_pos_1198_);
v_res_1199_ = lean_ctor_get(v___x_1197_, 1);
lean_inc(v_res_1199_);
lean_dec_ref_known(v___x_1197_, 2);
v_fst_1200_ = lean_ctor_get(v_pos_1198_, 0);
v_snd_1201_ = lean_ctor_get(v_pos_1198_, 1);
v___x_1202_ = lean_string_utf8_byte_size(v_fst_1200_);
v___x_1203_ = lean_nat_dec_eq(v_snd_1201_, v___x_1202_);
if (v___x_1203_ == 0)
{
lean_inc(v_snd_1201_);
lean_inc(v_fst_1200_);
v___y_1179_ = v_res_1199_;
v___y_1180_ = v_res_1191_;
v___y_1181_ = v_fst_1200_;
v___y_1182_ = v_pos_1198_;
v___y_1183_ = v___x_1196_;
v___y_1184_ = v_snd_1201_;
goto v___jp_1178_;
}
else
{
if (v___x_1196_ == 0)
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_box(0);
v___y_1092_ = v_res_1199_;
v___y_1093_ = v_res_1191_;
v___y_1094_ = v___x_1196_;
v_pos_1095_ = v_pos_1198_;
v_res_1096_ = v___x_1204_;
goto v___jp_1091_;
}
else
{
lean_inc(v_snd_1201_);
lean_inc(v_fst_1200_);
v___y_1179_ = v_res_1199_;
v___y_1180_ = v_res_1191_;
v___y_1181_ = v_fst_1200_;
v___y_1182_ = v_pos_1198_;
v___y_1183_ = v___x_1196_;
v___y_1184_ = v_snd_1201_;
goto v___jp_1178_;
}
}
}
else
{
lean_object* v_pos_1205_; lean_object* v_err_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec(v_res_1191_);
lean_dec(v_res_1069_);
lean_del_object(v___x_1062_);
lean_dec(v_res_1060_);
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
lean_del_object(v___x_1062_);
v___x_1214_ = lean_box(0);
v___x_1215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1215_, 0, v_res_1060_);
lean_ctor_set(v___x_1215_, 1, v_res_1069_);
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
lean_dec(v_res_1069_);
lean_del_object(v___x_1062_);
lean_dec(v_res_1060_);
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
else
{
lean_del_object(v___x_1062_);
v_pos_1074_ = v_pos_1068_;
goto v___jp_1073_;
}
}
}
}
else
{
lean_object* v_pos_1234_; lean_object* v_err_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_del_object(v___x_1062_);
lean_dec(v_res_1060_);
v_pos_1234_ = lean_ctor_get(v___x_1067_, 0);
v_err_1235_ = lean_ctor_get(v___x_1067_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1067_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_err_1235_);
lean_inc(v_pos_1234_);
lean_dec(v___x_1067_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_pos_1234_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_err_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1245_; 
lean_dec(v_res_1060_);
v___x_1243_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__6));
if (v_isShared_1063_ == 0)
{
lean_ctor_set_tag(v___x_1062_, 1);
lean_ctor_set(v___x_1062_, 1, v___x_1243_);
v___x_1245_ = v___x_1062_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_pos_1059_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
else
{
lean_object* v_pos_1248_; lean_object* v_err_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
v_pos_1248_ = lean_ctor_get(v___x_1058_, 0);
v_err_1249_ = lean_ctor_get(v___x_1058_, 1);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1058_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_err_1249_);
lean_inc(v_pos_1248_);
lean_dec(v___x_1058_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_pos_1248_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_err_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
v___jp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_box(0);
v___x_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___y_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
return v___x_1057_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___boxed(lean_object* v_extended_1257_, lean_object* v_a_1258_){
_start:
{
uint8_t v_extended_boxed_1259_; lean_object* v_res_1260_; 
v_extended_boxed_1259_ = lean_unbox(v_extended_1257_);
v_res_1260_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP(v_extended_boxed_1259_, v_a_1258_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_parsePosixTz(lean_object* v_s_1261_, uint8_t v_extended_1262_){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = lean_box(v_extended_1262_);
v___x_1264_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___boxed), 2, 1);
lean_closure_set(v___x_1264_, 0, v___x_1263_);
v___x_1265_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_1264_, v_s_1261_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_parsePosixTz___boxed(lean_object* v_s_1266_, lean_object* v_extended_1267_){
_start:
{
uint8_t v_extended_boxed_1268_; lean_object* v_res_1269_; 
v_extended_boxed_1268_ = lean_unbox(v_extended_1267_);
v_res_1269_ = l_Std_Time_TimeZone_parsePosixTz(v_s_1266_, v_extended_boxed_1268_);
return v_res_1269_;
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
