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
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
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
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: '+'"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__1_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: '-'"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__3 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__3_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4_value;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5;
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
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: ':'"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7_value;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "second"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "minute"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "condition not satisfied"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName___closed__0 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName(lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "ASCII letter expected"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: '>'"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__1 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__1_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__1_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'M'"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1_value;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "month"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: '.'"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5_value;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "week"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "day "};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " out of range 0-6"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10_value;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec(lean_object*);
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'J'"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__0 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__0_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1_value;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Julian day"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3_value;
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
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: '/'"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__2 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__2_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__2_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: ','"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "empty timezone name"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__3 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__3_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__4 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__4_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_parsePosixTz(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_parsePosixTz___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(lean_object* v_lo_6_, lean_object* v_hi_7_, lean_object* v_name_8_, lean_object* v_extra_9_, lean_object* v_a_10_){
_start:
{
lean_object* v_fst_14_; lean_object* v_snd_15_; lean_object* v___x_16_; uint8_t v_decide_17_; 
v_fst_14_ = lean_ctor_get(v_a_10_, 0);
v_snd_15_ = lean_ctor_get(v_a_10_, 1);
v___x_16_ = lean_string_utf8_byte_size(v_fst_14_);
v_decide_17_ = lean_nat_dec_eq(v_snd_15_, v___x_16_);
if (v_decide_17_ == 0)
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
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_85_ = lean_int_neg(v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(lean_object* v_a_86_){
_start:
{
lean_object* v_fst_87_; lean_object* v_snd_88_; lean_object* v_err_90_; lean_object* v_err_96_; lean_object* v___x_118_; uint8_t v_decide_119_; 
v_fst_87_ = lean_ctor_get(v_a_86_, 0);
v_snd_88_ = lean_ctor_get(v_a_86_, 1);
v___x_118_ = lean_string_utf8_byte_size(v_fst_87_);
v_decide_119_ = lean_nat_dec_eq(v_snd_88_, v___x_118_);
if (v_decide_119_ == 0)
{
uint32_t v___x_120_; uint32_t v_c_121_; uint8_t v___x_122_; 
v___x_120_ = 45;
v_c_121_ = lean_string_utf8_get_fast(v_fst_87_, v_snd_88_);
v___x_122_ = lean_uint32_dec_eq(v_c_121_, v___x_120_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
v___x_123_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4));
v_err_96_ = v___x_123_;
goto v___jp_95_;
}
else
{
lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_133_; 
lean_inc(v_snd_88_);
lean_inc(v_fst_87_);
v_isSharedCheck_133_ = !lean_is_exclusive(v_a_86_);
if (v_isSharedCheck_133_ == 0)
{
lean_object* v_unused_134_; lean_object* v_unused_135_; 
v_unused_134_ = lean_ctor_get(v_a_86_, 1);
lean_dec(v_unused_134_);
v_unused_135_ = lean_ctor_get(v_a_86_, 0);
lean_dec(v_unused_135_);
v___x_125_ = v_a_86_;
v_isShared_126_ = v_isSharedCheck_133_;
goto v_resetjp_124_;
}
else
{
lean_dec(v_a_86_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_133_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v_it_x27_129_; 
v___x_127_ = lean_string_utf8_next_fast(v_fst_87_, v_snd_88_);
lean_dec(v_snd_88_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_127_);
v_it_x27_129_ = v___x_125_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_fst_87_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v___x_127_);
v_it_x27_129_ = v_reuseFailAlloc_132_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v_it_x27_129_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
return v___x_131_;
}
}
}
}
else
{
lean_object* v___x_136_; 
v___x_136_ = lean_box(0);
v_err_96_ = v___x_136_;
goto v___jp_95_;
}
v___jp_89_:
{
uint8_t v_decide_91_; 
v_decide_91_ = lean_nat_dec_eq(v_snd_88_, v_snd_88_);
if (v_decide_91_ == 0)
{
lean_object* v___x_92_; 
lean_inc(v_err_90_);
v___x_92_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_92_, 0, v_a_86_);
lean_ctor_set(v___x_92_, 1, v_err_90_);
return v___x_92_;
}
else
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v_a_86_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
return v___x_94_;
}
}
v___jp_95_:
{
uint8_t v_decide_97_; 
v_decide_97_ = lean_nat_dec_eq(v_snd_88_, v_snd_88_);
if (v_decide_97_ == 0)
{
lean_object* v___x_98_; 
lean_inc(v_err_96_);
v___x_98_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_98_, 0, v_a_86_);
lean_ctor_set(v___x_98_, 1, v_err_96_);
return v___x_98_;
}
else
{
lean_object* v___x_99_; uint8_t v_decide_100_; 
v___x_99_ = lean_string_utf8_byte_size(v_fst_87_);
v_decide_100_ = lean_nat_dec_eq(v_snd_88_, v___x_99_);
if (v_decide_100_ == 0)
{
uint32_t v___x_101_; uint32_t v_c_102_; uint8_t v___x_103_; 
v___x_101_ = 43;
v_c_102_ = lean_string_utf8_get_fast(v_fst_87_, v_snd_88_);
v___x_103_ = lean_uint32_dec_eq(v_c_102_, v___x_101_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; 
v___x_104_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v_err_90_ = v___x_104_;
goto v___jp_89_;
}
else
{
lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_114_; 
lean_inc(v_snd_88_);
lean_inc(v_fst_87_);
v_isSharedCheck_114_ = !lean_is_exclusive(v_a_86_);
if (v_isSharedCheck_114_ == 0)
{
lean_object* v_unused_115_; lean_object* v_unused_116_; 
v_unused_115_ = lean_ctor_get(v_a_86_, 1);
lean_dec(v_unused_115_);
v_unused_116_ = lean_ctor_get(v_a_86_, 0);
lean_dec(v_unused_116_);
v___x_106_ = v_a_86_;
v_isShared_107_ = v_isSharedCheck_114_;
goto v_resetjp_105_;
}
else
{
lean_dec(v_a_86_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_114_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_108_; lean_object* v_it_x27_110_; 
v___x_108_ = lean_string_utf8_next_fast(v_fst_87_, v_snd_88_);
lean_dec(v_snd_88_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 1, v___x_108_);
v_it_x27_110_ = v___x_106_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_fst_87_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v___x_108_);
v_it_x27_110_ = v_reuseFailAlloc_113_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_112_, 0, v_it_x27_110_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
return v___x_112_;
}
}
}
}
else
{
lean_object* v___x_117_; 
v___x_117_ = lean_box(0);
v_err_90_ = v___x_117_;
goto v___jp_89_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__0(lean_object* v_a_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lean_nat_to_int(v_a_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__2(lean_object* v_a_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Rat_ofInt(v_a_139_);
return v___x_140_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0(uint8_t v___x_141_, lean_object* v_x_142_){
_start:
{
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed(lean_object* v___x_143_, lean_object* v_x_144_){
_start:
{
uint8_t v___x_4037__boxed_145_; uint8_t v_res_146_; lean_object* v_r_147_; 
v___x_4037__boxed_145_ = lean_unbox(v___x_143_);
v_res_146_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0(v___x_4037__boxed_145_, v_x_144_);
lean_dec(v_x_144_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_unsigned_to_nat(3600u);
v___x_152_ = lean_nat_to_int(v___x_151_);
return v___x_152_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(60u);
v___x_154_ = lean_nat_to_int(v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = lean_nat_to_int(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_unsigned_to_nat(59u);
v___x_161_ = lean_nat_to_int(v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(lean_object* v_maxHour_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_fst_169_; lean_object* v_snd_170_; lean_object* v___x_171_; uint8_t v_decide_172_; 
v_fst_169_ = lean_ctor_get(v_a_165_, 0);
v_snd_170_ = lean_ctor_get(v_a_165_, 1);
v___x_171_ = lean_string_utf8_byte_size(v_fst_169_);
v_decide_172_ = lean_nat_dec_eq(v_snd_170_, v___x_171_);
if (v_decide_172_ == 0)
{
uint32_t v_c_173_; uint32_t v___x_174_; uint8_t v___x_175_; 
v_c_173_ = lean_string_utf8_get_fast(v_fst_169_, v_snd_170_);
v___x_174_ = 48;
v___x_175_ = lean_uint32_dec_le(v___x_174_, v_c_173_);
if (v___x_175_ == 0)
{
lean_dec(v_maxHour_164_);
goto v___jp_166_;
}
else
{
uint32_t v___x_176_; uint8_t v___x_177_; 
v___x_176_ = 57;
v___x_177_ = lean_uint32_dec_le(v_c_173_, v___x_176_);
if (v___x_177_ == 0)
{
lean_dec(v_maxHour_164_);
goto v___jp_166_;
}
else
{
lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_288_; 
lean_inc(v_snd_170_);
lean_inc(v_fst_169_);
v_isSharedCheck_288_ = !lean_is_exclusive(v_a_165_);
if (v_isSharedCheck_288_ == 0)
{
lean_object* v_unused_289_; lean_object* v_unused_290_; 
v_unused_289_ = lean_ctor_get(v_a_165_, 1);
lean_dec(v_unused_289_);
v_unused_290_ = lean_ctor_get(v_a_165_, 0);
lean_dec(v_unused_290_);
v___x_179_ = v_a_165_;
v_isShared_180_ = v_isSharedCheck_288_;
goto v_resetjp_178_;
}
else
{
lean_dec(v_a_165_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_288_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v_fst_186_; lean_object* v_snd_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_287_; 
v___x_181_ = lean_string_utf8_next_fast(v_fst_169_, v_snd_170_);
lean_dec(v_snd_170_);
v___x_182_ = lean_uint32_to_nat(v_c_173_);
v___x_183_ = lean_unsigned_to_nat(48u);
v___x_184_ = lean_nat_sub(v___x_182_, v___x_183_);
lean_dec(v___x_182_);
v___x_185_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_169_, v___x_181_, v___x_184_);
v_fst_186_ = lean_ctor_get(v___x_185_, 0);
v_snd_187_ = lean_ctor_get(v___x_185_, 1);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_287_ == 0)
{
v___x_189_ = v___x_185_;
v_isShared_190_ = v_isSharedCheck_287_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_snd_187_);
lean_inc(v_fst_186_);
lean_dec(v___x_185_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_287_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
lean_inc(v_snd_187_);
lean_inc(v_fst_169_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v_snd_187_);
v___x_192_ = v___x_179_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_fst_169_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_snd_187_);
v___x_192_ = v_reuseFailAlloc_286_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
uint8_t v___x_193_; 
v___x_193_ = lean_nat_dec_lt(v_maxHour_164_, v_fst_186_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; uint8_t v___x_195_; 
lean_dec(v_maxHour_164_);
v___x_194_ = lean_unsigned_to_nat(167u);
v___x_195_ = lean_nat_dec_le(v_fst_186_, v___x_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
lean_dec(v_snd_187_);
lean_dec(v_fst_169_);
v___x_196_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0));
v___x_197_ = l_Nat_reprFast(v_fst_186_);
v___x_198_ = lean_string_append(v___x_196_, v___x_197_);
lean_dec_ref(v___x_197_);
v___x_199_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1));
v___x_200_ = lean_string_append(v___x_198_, v___x_199_);
v___x_201_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2));
v___x_202_ = lean_string_append(v___x_200_, v___x_201_);
v___x_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
if (v_isShared_190_ == 0)
{
lean_ctor_set_tag(v___x_189_, 1);
lean_ctor_set(v___x_189_, 1, v___x_203_);
lean_ctor_set(v___x_189_, 0, v___x_192_);
v___x_205_ = v___x_189_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
else
{
lean_object* v___x_207_; lean_object* v___y_209_; lean_object* v_pos_210_; lean_object* v_res_211_; lean_object* v___y_222_; lean_object* v_snd_223_; lean_object* v___y_224_; lean_object* v_err_225_; uint32_t v___x_229_; lean_object* v_pos_231_; lean_object* v_fst_232_; lean_object* v_snd_233_; lean_object* v_res_234_; lean_object* v_err_253_; uint8_t v_decide_257_; 
v___x_207_ = lean_nat_to_int(v_fst_186_);
v___x_229_ = 58;
v_decide_257_ = lean_nat_dec_eq(v_snd_187_, v___x_171_);
if (v_decide_257_ == 0)
{
uint32_t v_c_258_; uint8_t v___x_259_; 
v_c_258_ = lean_string_utf8_get_fast(v_fst_169_, v_snd_187_);
v___x_259_ = lean_uint32_dec_eq(v_c_258_, v___x_229_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
v___x_260_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7));
v_err_253_ = v___x_260_;
goto v___jp_252_;
}
else
{
lean_object* v___x_261_; lean_object* v___f_262_; lean_object* v___x_263_; lean_object* v_it_x27_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_261_ = lean_box(v___x_259_);
v___f_262_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_262_, 0, v___x_261_);
v___x_263_ = lean_string_utf8_next_fast(v_fst_169_, v_snd_187_);
lean_inc(v_fst_169_);
v_it_x27_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_264_, 0, v_fst_169_);
lean_ctor_set(v_it_x27_264_, 1, v___x_263_);
v___x_265_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___x_266_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8);
v___x_267_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10));
v___x_268_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_265_, v___x_266_, v___x_267_, v___f_262_, v_it_x27_264_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_pos_269_; lean_object* v_res_270_; lean_object* v_fst_271_; lean_object* v_snd_272_; 
lean_dec_ref(v___x_192_);
lean_dec(v_snd_187_);
lean_dec(v_fst_169_);
v_pos_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_pos_269_);
v_res_270_ = lean_ctor_get(v___x_268_, 1);
lean_inc(v_res_270_);
lean_dec_ref_known(v___x_268_, 2);
v_fst_271_ = lean_ctor_get(v_pos_269_, 0);
lean_inc(v_fst_271_);
v_snd_272_ = lean_ctor_get(v_pos_269_, 1);
lean_inc(v_snd_272_);
v_pos_231_ = v_pos_269_;
v_fst_232_ = v_fst_271_;
v_snd_233_ = v_snd_272_;
v_res_234_ = v_res_270_;
goto v___jp_230_;
}
else
{
lean_object* v_err_273_; 
v_err_273_ = lean_ctor_get(v___x_268_, 1);
lean_inc(v_err_273_);
lean_dec_ref_known(v___x_268_, 2);
v_err_253_ = v_err_273_;
goto v___jp_252_;
}
}
}
else
{
lean_object* v___x_274_; 
v___x_274_ = lean_box(0);
v_err_253_ = v___x_274_;
goto v___jp_252_;
}
v___jp_208_:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_212_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_213_ = lean_int_mul(v___x_207_, v___x_212_);
lean_dec(v___x_207_);
v___x_214_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4);
v___x_215_ = lean_int_mul(v___y_209_, v___x_214_);
lean_dec(v___y_209_);
v___x_216_ = lean_int_add(v___x_213_, v___x_215_);
lean_dec(v___x_215_);
lean_dec(v___x_213_);
v___x_217_ = lean_int_add(v___x_216_, v_res_211_);
lean_dec(v_res_211_);
lean_dec(v___x_216_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 1, v___x_217_);
lean_ctor_set(v___x_189_, 0, v_pos_210_);
v___x_219_ = v___x_189_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_pos_210_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
v___jp_221_:
{
uint8_t v_decide_226_; 
v_decide_226_ = lean_nat_dec_eq(v_snd_223_, v_snd_223_);
lean_dec(v_snd_223_);
if (v_decide_226_ == 0)
{
lean_object* v___x_227_; 
lean_dec(v___y_224_);
lean_dec(v___x_207_);
lean_del_object(v___x_189_);
v___x_227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_227_, 0, v___y_222_);
lean_ctor_set(v___x_227_, 1, v_err_225_);
return v___x_227_;
}
else
{
lean_object* v___x_228_; 
lean_dec(v_err_225_);
v___x_228_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___y_209_ = v___y_224_;
v_pos_210_ = v___y_222_;
v_res_211_ = v___x_228_;
goto v___jp_208_;
}
}
v___jp_230_:
{
lean_object* v___x_235_; uint8_t v_decide_236_; 
v___x_235_ = lean_string_utf8_byte_size(v_fst_232_);
v_decide_236_ = lean_nat_dec_eq(v_snd_233_, v___x_235_);
if (v_decide_236_ == 0)
{
uint32_t v_c_237_; uint8_t v___x_238_; 
v_c_237_ = lean_string_utf8_get_fast(v_fst_232_, v_snd_233_);
v___x_238_ = lean_uint32_dec_eq(v_c_237_, v___x_229_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
lean_dec(v_fst_232_);
v___x_239_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7));
v___y_222_ = v_pos_231_;
v_snd_223_ = v_snd_233_;
v___y_224_ = v_res_234_;
v_err_225_ = v___x_239_;
goto v___jp_221_;
}
else
{
lean_object* v___x_240_; lean_object* v___f_241_; lean_object* v___x_242_; lean_object* v_it_x27_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_240_ = lean_box(v___x_238_);
v___f_241_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_241_, 0, v___x_240_);
v___x_242_ = lean_string_utf8_next_fast(v_fst_232_, v_snd_233_);
v_it_x27_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_243_, 0, v_fst_232_);
lean_ctor_set(v_it_x27_243_, 1, v___x_242_);
v___x_244_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___x_245_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8);
v___x_246_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9));
v___x_247_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_244_, v___x_245_, v___x_246_, v___f_241_, v_it_x27_243_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_pos_248_; lean_object* v_res_249_; 
lean_dec(v_snd_233_);
lean_dec_ref(v_pos_231_);
v_pos_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_pos_248_);
v_res_249_ = lean_ctor_get(v___x_247_, 1);
lean_inc(v_res_249_);
lean_dec_ref_known(v___x_247_, 2);
v___y_209_ = v_res_234_;
v_pos_210_ = v_pos_248_;
v_res_211_ = v_res_249_;
goto v___jp_208_;
}
else
{
lean_object* v_err_250_; 
v_err_250_ = lean_ctor_get(v___x_247_, 1);
lean_inc(v_err_250_);
lean_dec_ref_known(v___x_247_, 2);
v___y_222_ = v_pos_231_;
v_snd_223_ = v_snd_233_;
v___y_224_ = v_res_234_;
v_err_225_ = v_err_250_;
goto v___jp_221_;
}
}
}
else
{
lean_object* v___x_251_; 
lean_dec(v_fst_232_);
v___x_251_ = lean_box(0);
v___y_222_ = v_pos_231_;
v_snd_223_ = v_snd_233_;
v___y_224_ = v_res_234_;
v_err_225_ = v___x_251_;
goto v___jp_221_;
}
}
v___jp_252_:
{
uint8_t v_decide_254_; 
v_decide_254_ = lean_nat_dec_eq(v_snd_187_, v_snd_187_);
if (v_decide_254_ == 0)
{
lean_object* v___x_255_; 
lean_dec(v___x_207_);
lean_del_object(v___x_189_);
lean_dec(v_snd_187_);
lean_dec(v_fst_169_);
v___x_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_192_);
lean_ctor_set(v___x_255_, 1, v_err_253_);
return v___x_255_;
}
else
{
lean_object* v___x_256_; 
lean_dec(v_err_253_);
v___x_256_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v_pos_231_ = v___x_192_;
v_fst_232_ = v_fst_169_;
v_snd_233_ = v_snd_187_;
v_res_234_ = v___x_256_;
goto v___jp_230_;
}
}
}
}
else
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
lean_dec(v_snd_187_);
lean_dec(v_fst_169_);
v___x_275_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0));
v___x_276_ = l_Nat_reprFast(v_fst_186_);
v___x_277_ = lean_string_append(v___x_275_, v___x_276_);
lean_dec_ref(v___x_276_);
v___x_278_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1));
v___x_279_ = lean_string_append(v___x_277_, v___x_278_);
v___x_280_ = l_Nat_reprFast(v_maxHour_164_);
v___x_281_ = lean_string_append(v___x_279_, v___x_280_);
lean_dec_ref(v___x_280_);
v___x_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
if (v_isShared_190_ == 0)
{
lean_ctor_set_tag(v___x_189_, 1);
lean_ctor_set(v___x_189_, 1, v___x_282_);
lean_ctor_set(v___x_189_, 0, v___x_192_);
v___x_284_ = v___x_189_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
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
lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec(v_maxHour_164_);
v___x_291_ = lean_box(0);
v___x_292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_292_, 0, v_a_165_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
return v___x_292_;
}
v___jp_166_:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__1));
v___x_168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_168_, 0, v_a_165_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__1(lean_object* v_a_293_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_nat_to_int(v_a_293_);
v___x_295_ = l_Rat_ofInt(v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(lean_object* v_a_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(v_a_296_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_pos_298_; lean_object* v_res_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_pos_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_pos_298_);
v_res_299_ = lean_ctor_get(v___x_297_, 1);
lean_inc(v_res_299_);
lean_dec_ref_known(v___x_297_, 2);
v___x_300_ = lean_unsigned_to_nat(24u);
v___x_301_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(v___x_300_, v_pos_298_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_pos_302_; lean_object* v_res_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_312_; 
v_pos_302_ = lean_ctor_get(v___x_301_, 0);
v_res_303_ = lean_ctor_get(v___x_301_, 1);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_312_ == 0)
{
v___x_305_ = v___x_301_;
v_isShared_306_ = v_isSharedCheck_312_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_res_303_);
lean_inc(v_pos_302_);
lean_dec(v___x_301_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_312_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_307_ = lean_int_neg(v_res_299_);
lean_dec(v_res_299_);
v___x_308_ = lean_int_mul(v___x_307_, v_res_303_);
lean_dec(v_res_303_);
lean_dec(v___x_307_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v___x_308_);
v___x_310_ = v___x_305_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_pos_302_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
else
{
lean_object* v_pos_313_; lean_object* v_err_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_dec(v_res_299_);
v_pos_313_ = lean_ctor_get(v___x_301_, 0);
v_err_314_ = lean_ctor_get(v___x_301_, 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_301_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_err_314_);
lean_inc(v_pos_313_);
lean_dec(v___x_301_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_pos_313_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_err_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
else
{
lean_object* v_pos_322_; lean_object* v_err_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
v_pos_322_ = lean_ctor_get(v___x_297_, 0);
v_err_323_ = lean_ctor_get(v___x_297_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_297_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_err_323_);
lean_inc(v_pos_322_);
lean_dec(v___x_297_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_pos_322_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_err_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0(lean_object* v_acc_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_pos_337_; uint32_t v_res_338_; lean_object* v_fst_341_; lean_object* v_snd_342_; lean_object* v_pos_344_; lean_object* v_snd_345_; lean_object* v_err_346_; lean_object* v___x_350_; uint8_t v_decide_351_; 
v_fst_341_ = lean_ctor_get(v_a_335_, 0);
v_snd_342_ = lean_ctor_get(v_a_335_, 1);
lean_inc(v_snd_342_);
v___x_350_ = lean_string_utf8_byte_size(v_fst_341_);
v_decide_351_ = lean_nat_dec_eq(v_snd_342_, v___x_350_);
if (v_decide_351_ == 0)
{
uint32_t v_c_352_; lean_object* v___x_353_; lean_object* v_it_x27_354_; uint32_t v___x_371_; uint8_t v___x_372_; 
v_c_352_ = lean_string_utf8_get_fast(v_fst_341_, v_snd_342_);
v___x_353_ = lean_string_utf8_next_fast(v_fst_341_, v_snd_342_);
lean_inc(v_fst_341_);
v_it_x27_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_354_, 0, v_fst_341_);
lean_ctor_set(v_it_x27_354_, 1, v___x_353_);
v___x_371_ = 65;
v___x_372_ = lean_uint32_dec_le(v___x_371_, v_c_352_);
if (v___x_372_ == 0)
{
goto v___jp_366_;
}
else
{
uint32_t v___x_373_; uint8_t v___x_374_; 
v___x_373_ = 90;
v___x_374_ = lean_uint32_dec_le(v_c_352_, v___x_373_);
if (v___x_374_ == 0)
{
goto v___jp_366_;
}
else
{
lean_dec(v_snd_342_);
lean_dec_ref(v_a_335_);
v_pos_337_ = v_it_x27_354_;
v_res_338_ = v_c_352_;
goto v___jp_336_;
}
}
v___jp_355_:
{
uint32_t v___x_356_; uint8_t v___x_357_; 
v___x_356_ = 43;
v___x_357_ = lean_uint32_dec_eq(v_c_352_, v___x_356_);
if (v___x_357_ == 0)
{
uint32_t v___x_358_; uint8_t v___x_359_; 
v___x_358_ = 45;
v___x_359_ = lean_uint32_dec_eq(v_c_352_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; 
lean_dec_ref_known(v_it_x27_354_, 2);
v___x_360_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__1));
lean_inc(v_snd_342_);
v_pos_344_ = v_a_335_;
v_snd_345_ = v_snd_342_;
v_err_346_ = v___x_360_;
goto v___jp_343_;
}
else
{
lean_dec(v_snd_342_);
lean_dec_ref(v_a_335_);
v_pos_337_ = v_it_x27_354_;
v_res_338_ = v_c_352_;
goto v___jp_336_;
}
}
else
{
lean_dec(v_snd_342_);
lean_dec_ref(v_a_335_);
v_pos_337_ = v_it_x27_354_;
v_res_338_ = v_c_352_;
goto v___jp_336_;
}
}
v___jp_361_:
{
uint32_t v___x_362_; uint8_t v___x_363_; 
v___x_362_ = 48;
v___x_363_ = lean_uint32_dec_le(v___x_362_, v_c_352_);
if (v___x_363_ == 0)
{
goto v___jp_355_;
}
else
{
uint32_t v___x_364_; uint8_t v___x_365_; 
v___x_364_ = 57;
v___x_365_ = lean_uint32_dec_le(v_c_352_, v___x_364_);
if (v___x_365_ == 0)
{
goto v___jp_355_;
}
else
{
lean_dec(v_snd_342_);
lean_dec_ref(v_a_335_);
v_pos_337_ = v_it_x27_354_;
v_res_338_ = v_c_352_;
goto v___jp_336_;
}
}
}
v___jp_366_:
{
uint32_t v___x_367_; uint8_t v___x_368_; 
v___x_367_ = 97;
v___x_368_ = lean_uint32_dec_le(v___x_367_, v_c_352_);
if (v___x_368_ == 0)
{
goto v___jp_361_;
}
else
{
uint32_t v___x_369_; uint8_t v___x_370_; 
v___x_369_ = 122;
v___x_370_ = lean_uint32_dec_le(v_c_352_, v___x_369_);
if (v___x_370_ == 0)
{
goto v___jp_361_;
}
else
{
lean_dec(v_snd_342_);
lean_dec_ref(v_a_335_);
v_pos_337_ = v_it_x27_354_;
v_res_338_ = v_c_352_;
goto v___jp_336_;
}
}
}
}
else
{
lean_object* v___x_375_; 
v___x_375_ = lean_box(0);
lean_inc(v_snd_342_);
v_pos_344_ = v_a_335_;
v_snd_345_ = v_snd_342_;
v_err_346_ = v___x_375_;
goto v___jp_343_;
}
v___jp_336_:
{
lean_object* v___x_339_; 
v___x_339_ = lean_string_push(v_acc_334_, v_res_338_);
v_acc_334_ = v___x_339_;
v_a_335_ = v_pos_337_;
goto _start;
}
v___jp_343_:
{
uint8_t v_decide_347_; 
v_decide_347_ = lean_nat_dec_eq(v_snd_342_, v_snd_345_);
lean_dec(v_snd_345_);
lean_dec(v_snd_342_);
if (v_decide_347_ == 0)
{
lean_object* v___x_348_; 
lean_dec_ref(v_acc_334_);
lean_inc(v_err_346_);
v___x_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_348_, 0, v_pos_344_);
lean_ctor_set(v___x_348_, 1, v_err_346_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v_pos_344_);
lean_ctor_set(v___x_349_, 1, v_acc_334_);
return v___x_349_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName(lean_object* v_a_377_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName___closed__0));
v___x_379_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0(v___x_378_, v_a_377_);
return v___x_379_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
if (lean_obj_tag(v_x_380_) == 0)
{
if (lean_obj_tag(v_x_381_) == 0)
{
uint8_t v___x_382_; 
v___x_382_ = 1;
return v___x_382_;
}
else
{
uint8_t v___x_383_; 
v___x_383_ = 0;
return v___x_383_;
}
}
else
{
if (lean_obj_tag(v_x_381_) == 0)
{
uint8_t v___x_384_; 
v___x_384_ = 0;
return v___x_384_;
}
else
{
lean_object* v_val_385_; lean_object* v_val_386_; uint32_t v___x_387_; uint32_t v___x_388_; uint8_t v___x_389_; 
v_val_385_ = lean_ctor_get(v_x_380_, 0);
v_val_386_ = lean_ctor_get(v_x_381_, 0);
v___x_387_ = lean_unbox_uint32(v_val_385_);
v___x_388_ = lean_unbox_uint32(v_val_386_);
v___x_389_ = lean_uint32_dec_eq(v___x_387_, v___x_388_);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0___boxed(lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
uint8_t v_res_392_; lean_object* v_r_393_; 
v_res_392_ = l_instBEqOption_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_x_390_, v_x_391_);
lean_dec(v_x_391_);
lean_dec(v_x_390_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1(lean_object* v_acc_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_pos_400_; uint32_t v_res_401_; lean_object* v_fst_404_; lean_object* v_snd_405_; lean_object* v_pos_407_; lean_object* v_snd_408_; lean_object* v_err_409_; lean_object* v___x_415_; uint8_t v_decide_416_; 
v_fst_404_ = lean_ctor_get(v_a_398_, 0);
v_snd_405_ = lean_ctor_get(v_a_398_, 1);
lean_inc(v_snd_405_);
v___x_415_ = lean_string_utf8_byte_size(v_fst_404_);
v_decide_416_ = lean_nat_dec_eq(v_snd_405_, v___x_415_);
if (v_decide_416_ == 0)
{
uint32_t v_c_417_; lean_object* v___x_418_; lean_object* v_it_x27_419_; uint32_t v___x_425_; uint8_t v___x_426_; 
v_c_417_ = lean_string_utf8_get_fast(v_fst_404_, v_snd_405_);
v___x_418_ = lean_string_utf8_next_fast(v_fst_404_, v_snd_405_);
lean_inc(v_fst_404_);
v_it_x27_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_419_, 0, v_fst_404_);
lean_ctor_set(v_it_x27_419_, 1, v___x_418_);
v___x_425_ = 65;
v___x_426_ = lean_uint32_dec_le(v___x_425_, v_c_417_);
if (v___x_426_ == 0)
{
goto v___jp_420_;
}
else
{
uint32_t v___x_427_; uint8_t v___x_428_; 
v___x_427_ = 90;
v___x_428_ = lean_uint32_dec_le(v_c_417_, v___x_427_);
if (v___x_428_ == 0)
{
goto v___jp_420_;
}
else
{
lean_dec(v_snd_405_);
lean_dec_ref(v_a_398_);
v_pos_400_ = v_it_x27_419_;
v_res_401_ = v_c_417_;
goto v___jp_399_;
}
}
v___jp_420_:
{
uint32_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = 97;
v___x_422_ = lean_uint32_dec_le(v___x_421_, v_c_417_);
if (v___x_422_ == 0)
{
lean_dec_ref_known(v_it_x27_419_, 2);
goto v___jp_413_;
}
else
{
uint32_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = 122;
v___x_424_ = lean_uint32_dec_le(v_c_417_, v___x_423_);
if (v___x_424_ == 0)
{
lean_dec_ref_known(v_it_x27_419_, 2);
goto v___jp_413_;
}
else
{
lean_dec(v_snd_405_);
lean_dec_ref(v_a_398_);
v_pos_400_ = v_it_x27_419_;
v_res_401_ = v_c_417_;
goto v___jp_399_;
}
}
}
}
else
{
lean_object* v___x_429_; 
v___x_429_ = lean_box(0);
lean_inc(v_snd_405_);
v_pos_407_ = v_a_398_;
v_snd_408_ = v_snd_405_;
v_err_409_ = v___x_429_;
goto v___jp_406_;
}
v___jp_399_:
{
lean_object* v___x_402_; 
v___x_402_ = lean_string_push(v_acc_397_, v_res_401_);
v_acc_397_ = v___x_402_;
v_a_398_ = v_pos_400_;
goto _start;
}
v___jp_406_:
{
uint8_t v_decide_410_; 
v_decide_410_ = lean_nat_dec_eq(v_snd_405_, v_snd_408_);
lean_dec(v_snd_408_);
lean_dec(v_snd_405_);
if (v_decide_410_ == 0)
{
lean_object* v___x_411_; 
lean_dec_ref(v_acc_397_);
lean_inc(v_err_409_);
v___x_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_411_, 0, v_pos_407_);
lean_ctor_set(v___x_411_, 1, v_err_409_);
return v___x_411_;
}
else
{
lean_object* v___x_412_; 
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v_pos_407_);
lean_ctor_set(v___x_412_, 1, v_acc_397_);
return v___x_412_;
}
}
v___jp_413_:
{
lean_object* v___x_414_; 
v___x_414_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__1));
lean_inc(v_snd_405_);
v_pos_407_ = v_a_398_;
v_snd_408_ = v_snd_405_;
v_err_409_ = v___x_414_;
goto v___jp_406_;
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_430_; lean_object* v___x_431_; 
v___x_430_ = 60;
v___x_431_ = lean_box_uint32(v___x_430_);
return v___x_431_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0___boxed__const__1;
v___x_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(lean_object* v_a_437_){
_start:
{
lean_object* v_pos_439_; lean_object* v_res_440_; lean_object* v_fst_496_; lean_object* v_snd_497_; lean_object* v___x_498_; uint8_t v_decide_499_; 
v_fst_496_ = lean_ctor_get(v_a_437_, 0);
v_snd_497_ = lean_ctor_get(v_a_437_, 1);
v___x_498_ = lean_string_utf8_byte_size(v_fst_496_);
v_decide_499_ = lean_nat_dec_eq(v_snd_497_, v___x_498_);
if (v_decide_499_ == 0)
{
uint32_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = lean_string_utf8_get_fast(v_fst_496_, v_snd_497_);
v___x_501_ = lean_box_uint32(v___x_500_);
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
v_pos_439_ = v_a_437_;
v_res_440_ = v___x_502_;
goto v___jp_438_;
}
else
{
lean_object* v___x_503_; 
v___x_503_ = lean_box(0);
v_pos_439_ = v_a_437_;
v_res_440_ = v___x_503_;
goto v___jp_438_;
}
v___jp_438_:
{
lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_441_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0);
v___x_442_ = l_instBEqOption_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_res_440_, v___x_441_);
lean_dec(v_res_440_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName___closed__0));
v___x_444_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1(v___x_443_, v_pos_439_);
return v___x_444_;
}
else
{
lean_object* v_fst_445_; lean_object* v_snd_446_; lean_object* v___x_447_; uint8_t v_decide_448_; 
v_fst_445_ = lean_ctor_get(v_pos_439_, 0);
v_snd_446_ = lean_ctor_get(v_pos_439_, 1);
v___x_447_ = lean_string_utf8_byte_size(v_fst_445_);
v_decide_448_ = lean_nat_dec_eq(v_snd_446_, v___x_447_);
if (v_decide_448_ == 0)
{
lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_491_; 
lean_inc(v_snd_446_);
lean_inc(v_fst_445_);
v_isSharedCheck_491_ = !lean_is_exclusive(v_pos_439_);
if (v_isSharedCheck_491_ == 0)
{
lean_object* v_unused_492_; lean_object* v_unused_493_; 
v_unused_492_ = lean_ctor_get(v_pos_439_, 1);
lean_dec(v_unused_492_);
v_unused_493_ = lean_ctor_get(v_pos_439_, 0);
lean_dec(v_unused_493_);
v___x_450_ = v_pos_439_;
v_isShared_451_ = v_isSharedCheck_491_;
goto v_resetjp_449_;
}
else
{
lean_dec(v_pos_439_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_491_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_452_ = lean_string_utf8_next_fast(v_fst_445_, v_snd_446_);
lean_dec(v_snd_446_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v___x_452_);
v___x_454_ = v___x_450_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_fst_445_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v___x_452_);
v___x_454_ = v_reuseFailAlloc_490_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_455_; 
v___x_455_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName(v___x_454_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_pos_456_; lean_object* v_res_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_489_; 
v_pos_456_ = lean_ctor_get(v___x_455_, 0);
v_res_457_ = lean_ctor_get(v___x_455_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_489_ == 0)
{
v___x_459_ = v___x_455_;
v_isShared_460_ = v_isSharedCheck_489_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_res_457_);
lean_inc(v_pos_456_);
lean_dec(v___x_455_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_489_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v_fst_461_; lean_object* v_snd_462_; lean_object* v___x_463_; uint8_t v_decide_464_; 
v_fst_461_ = lean_ctor_get(v_pos_456_, 0);
v_snd_462_ = lean_ctor_get(v_pos_456_, 1);
v___x_463_ = lean_string_utf8_byte_size(v_fst_461_);
v_decide_464_ = lean_nat_dec_eq(v_snd_462_, v___x_463_);
if (v_decide_464_ == 0)
{
uint32_t v___x_465_; uint32_t v_c_466_; uint8_t v___x_467_; 
v___x_465_ = 62;
v_c_466_ = lean_string_utf8_get_fast(v_fst_461_, v_snd_462_);
v___x_467_ = lean_uint32_dec_eq(v_c_466_, v___x_465_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_470_; 
lean_dec(v_res_457_);
v___x_468_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2));
if (v_isShared_460_ == 0)
{
lean_ctor_set_tag(v___x_459_, 1);
lean_ctor_set(v___x_459_, 1, v___x_468_);
v___x_470_ = v___x_459_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_pos_456_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
else
{
lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_482_; 
lean_inc(v_snd_462_);
lean_inc(v_fst_461_);
v_isSharedCheck_482_ = !lean_is_exclusive(v_pos_456_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; lean_object* v_unused_484_; 
v_unused_483_ = lean_ctor_get(v_pos_456_, 1);
lean_dec(v_unused_483_);
v_unused_484_ = lean_ctor_get(v_pos_456_, 0);
lean_dec(v_unused_484_);
v___x_473_ = v_pos_456_;
v_isShared_474_ = v_isSharedCheck_482_;
goto v_resetjp_472_;
}
else
{
lean_dec(v_pos_456_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_482_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v_it_x27_477_; 
v___x_475_ = lean_string_utf8_next_fast(v_fst_461_, v_snd_462_);
lean_dec(v_snd_462_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v___x_475_);
v_it_x27_477_ = v___x_473_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_fst_461_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v___x_475_);
v_it_x27_477_ = v_reuseFailAlloc_481_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_479_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v_it_x27_477_);
v___x_479_ = v___x_459_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_it_x27_477_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_res_457_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
else
{
lean_object* v___x_485_; lean_object* v___x_487_; 
lean_dec(v_res_457_);
v___x_485_ = lean_box(0);
if (v_isShared_460_ == 0)
{
lean_ctor_set_tag(v___x_459_, 1);
lean_ctor_set(v___x_459_, 1, v___x_485_);
v___x_487_ = v___x_459_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_pos_456_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
else
{
return v___x_455_;
}
}
}
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_box(0);
v___x_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_495_, 0, v_pos_439_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
return v___x_495_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1(lean_object* v___x_504_, lean_object* v_x_505_){
_start:
{
uint8_t v___x_506_; 
v___x_506_ = lean_int_dec_le(v_x_505_, v___x_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1___boxed(lean_object* v___x_507_, lean_object* v_x_508_){
_start:
{
uint8_t v_res_509_; lean_object* v_r_510_; 
v_res_509_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1(v___x_507_, v_x_508_);
lean_dec(v_x_508_);
lean_dec(v___x_507_);
v_r_510_ = lean_box(v_res_509_);
return v_r_510_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_unsigned_to_nat(12u);
v___x_515_ = lean_nat_to_int(v___x_514_);
return v___x_515_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_unsigned_to_nat(5u);
v___x_521_ = lean_nat_to_int(v___x_520_);
return v___x_521_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7(void){
_start:
{
lean_object* v___x_522_; lean_object* v___f_523_; 
v___x_522_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6);
v___f_523_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1___boxed), 2, 1);
lean_closure_set(v___f_523_, 0, v___x_522_);
return v___f_523_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_unsigned_to_nat(7u);
v___x_528_ = lean_nat_to_int(v___x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec(lean_object* v_a_529_){
_start:
{
lean_object* v_fst_530_; lean_object* v_snd_531_; lean_object* v___x_532_; uint8_t v_decide_533_; 
v_fst_530_ = lean_ctor_get(v_a_529_, 0);
v_snd_531_ = lean_ctor_get(v_a_529_, 1);
v___x_532_ = lean_string_utf8_byte_size(v_fst_530_);
v_decide_533_ = lean_nat_dec_eq(v_snd_531_, v___x_532_);
if (v_decide_533_ == 0)
{
uint32_t v___x_534_; uint32_t v_c_535_; uint8_t v___x_536_; 
v___x_534_ = 77;
v_c_535_ = lean_string_utf8_get_fast(v_fst_530_, v_snd_531_);
v___x_536_ = lean_uint32_dec_eq(v_c_535_, v___x_534_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1));
v___x_538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_538_, 0, v_a_529_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
return v___x_538_;
}
else
{
lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_693_; 
lean_inc(v_snd_531_);
lean_inc(v_fst_530_);
v_isSharedCheck_693_ = !lean_is_exclusive(v_a_529_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; lean_object* v_unused_695_; 
v_unused_694_ = lean_ctor_get(v_a_529_, 1);
lean_dec(v_unused_694_);
v_unused_695_ = lean_ctor_get(v_a_529_, 0);
lean_dec(v_unused_695_);
v___x_540_ = v_a_529_;
v_isShared_541_ = v_isSharedCheck_693_;
goto v_resetjp_539_;
}
else
{
lean_dec(v_a_529_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_693_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; lean_object* v___f_543_; lean_object* v___x_544_; lean_object* v_it_x27_546_; 
v___x_542_ = lean_box(v___x_536_);
v___f_543_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_543_, 0, v___x_542_);
v___x_544_ = lean_string_utf8_next_fast(v_fst_530_, v_snd_531_);
lean_dec(v_snd_531_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v___x_544_);
v_it_x27_546_ = v___x_540_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_fst_530_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___x_544_);
v_it_x27_546_ = v_reuseFailAlloc_692_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_547_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_548_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2);
v___x_549_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3));
v___x_550_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_547_, v___x_548_, v___x_549_, v___f_543_, v_it_x27_546_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_pos_551_; lean_object* v_res_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_682_; 
v_pos_551_ = lean_ctor_get(v___x_550_, 0);
v_res_552_ = lean_ctor_get(v___x_550_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_682_ == 0)
{
v___x_554_ = v___x_550_;
v_isShared_555_ = v_isSharedCheck_682_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_res_552_);
lean_inc(v_pos_551_);
lean_dec(v___x_550_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_682_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v_fst_556_; lean_object* v_snd_557_; lean_object* v___x_558_; uint8_t v_decide_559_; 
v_fst_556_ = lean_ctor_get(v_pos_551_, 0);
v_snd_557_ = lean_ctor_get(v_pos_551_, 1);
v___x_558_ = lean_string_utf8_byte_size(v_fst_556_);
v_decide_559_ = lean_nat_dec_eq(v_snd_557_, v___x_558_);
if (v_decide_559_ == 0)
{
uint32_t v___x_560_; uint32_t v_c_561_; uint8_t v___x_562_; 
v___x_560_ = 46;
v_c_561_ = lean_string_utf8_get_fast(v_fst_556_, v_snd_557_);
v___x_562_ = lean_uint32_dec_eq(v_c_561_, v___x_560_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_565_; 
lean_dec(v_res_552_);
v___x_563_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5));
if (v_isShared_555_ == 0)
{
lean_ctor_set_tag(v___x_554_, 1);
lean_ctor_set(v___x_554_, 1, v___x_563_);
v___x_565_ = v___x_554_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_pos_551_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
else
{
lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_675_; 
lean_inc(v_snd_557_);
lean_inc(v_fst_556_);
v_isSharedCheck_675_ = !lean_is_exclusive(v_pos_551_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; lean_object* v_unused_677_; 
v_unused_676_ = lean_ctor_get(v_pos_551_, 1);
lean_dec(v_unused_676_);
v_unused_677_ = lean_ctor_get(v_pos_551_, 0);
lean_dec(v_unused_677_);
v___x_568_ = v_pos_551_;
v_isShared_569_ = v_isSharedCheck_675_;
goto v_resetjp_567_;
}
else
{
lean_dec(v_pos_551_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_675_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v_it_x27_572_; 
v___x_570_ = lean_string_utf8_next_fast(v_fst_556_, v_snd_557_);
lean_dec(v_snd_557_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 1, v___x_570_);
v_it_x27_572_ = v___x_568_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_fst_556_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v___x_570_);
v_it_x27_572_ = v_reuseFailAlloc_674_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_573_; lean_object* v___f_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_573_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6);
v___f_574_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7);
v___x_575_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8));
v___x_576_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_547_, v___x_573_, v___x_575_, v___f_574_, v_it_x27_572_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_pos_577_; lean_object* v_res_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_664_; 
v_pos_577_ = lean_ctor_get(v___x_576_, 0);
v_res_578_ = lean_ctor_get(v___x_576_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_664_ == 0)
{
v___x_580_ = v___x_576_;
v_isShared_581_ = v_isSharedCheck_664_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_res_578_);
lean_inc(v_pos_577_);
lean_dec(v___x_576_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_664_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v_fst_582_; lean_object* v_snd_583_; lean_object* v___x_584_; uint8_t v_decide_585_; 
v_fst_582_ = lean_ctor_get(v_pos_577_, 0);
v_snd_583_ = lean_ctor_get(v_pos_577_, 1);
v___x_584_ = lean_string_utf8_byte_size(v_fst_582_);
v_decide_585_ = lean_nat_dec_eq(v_snd_583_, v___x_584_);
if (v_decide_585_ == 0)
{
uint32_t v_c_586_; uint8_t v___x_587_; 
v_c_586_ = lean_string_utf8_get_fast(v_fst_582_, v_snd_583_);
v___x_587_ = lean_uint32_dec_eq(v_c_586_, v___x_560_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_590_; 
lean_dec(v_res_578_);
lean_del_object(v___x_554_);
lean_dec(v_res_552_);
v___x_588_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5));
if (v_isShared_581_ == 0)
{
lean_ctor_set_tag(v___x_580_, 1);
lean_ctor_set(v___x_580_, 1, v___x_588_);
v___x_590_ = v___x_580_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_pos_577_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
else
{
lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_657_; 
lean_inc(v_snd_583_);
lean_inc(v_fst_582_);
v_isSharedCheck_657_ = !lean_is_exclusive(v_pos_577_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; lean_object* v_unused_659_; 
v_unused_658_ = lean_ctor_get(v_pos_577_, 1);
lean_dec(v_unused_658_);
v_unused_659_ = lean_ctor_get(v_pos_577_, 0);
lean_dec(v_unused_659_);
v___x_593_ = v_pos_577_;
v_isShared_594_ = v_isSharedCheck_657_;
goto v_resetjp_592_;
}
else
{
lean_dec(v_pos_577_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_657_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v_it_x27_597_; 
v___x_595_ = lean_string_utf8_next_fast(v_fst_582_, v_snd_583_);
lean_dec(v_snd_583_);
lean_inc(v_fst_582_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 1, v___x_595_);
v_it_x27_597_ = v___x_593_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_fst_582_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v___x_595_);
v_it_x27_597_ = v_reuseFailAlloc_656_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
uint8_t v_decide_603_; 
v_decide_603_ = lean_nat_dec_eq(v___x_595_, v___x_584_);
if (v_decide_603_ == 0)
{
uint32_t v_c_604_; uint32_t v___x_605_; uint8_t v___x_606_; 
v_c_604_ = lean_string_utf8_get_fast(v_fst_582_, v___x_595_);
v___x_605_ = 48;
v___x_606_ = lean_uint32_dec_le(v___x_605_, v_c_604_);
if (v___x_606_ == 0)
{
lean_dec(v_fst_582_);
lean_dec(v_res_578_);
lean_del_object(v___x_554_);
lean_dec(v_res_552_);
goto v___jp_598_;
}
else
{
uint32_t v___x_607_; uint8_t v___x_608_; 
v___x_607_ = 57;
v___x_608_ = lean_uint32_dec_le(v_c_604_, v___x_607_);
if (v___x_608_ == 0)
{
lean_dec(v_fst_582_);
lean_dec(v_res_578_);
lean_del_object(v___x_554_);
lean_dec(v_res_552_);
goto v___jp_598_;
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v_fst_614_; lean_object* v_snd_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_651_; 
lean_dec_ref(v_it_x27_597_);
lean_del_object(v___x_580_);
v___x_609_ = lean_string_utf8_next_fast(v_fst_582_, v___x_595_);
v___x_610_ = lean_uint32_to_nat(v_c_604_);
v___x_611_ = lean_unsigned_to_nat(48u);
v___x_612_ = lean_nat_sub(v___x_610_, v___x_611_);
lean_dec(v___x_610_);
v___x_613_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_582_, v___x_609_, v___x_612_);
v_fst_614_ = lean_ctor_get(v___x_613_, 0);
v_snd_615_ = lean_ctor_get(v___x_613_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_651_ == 0)
{
v___x_617_ = v___x_613_;
v_isShared_618_ = v_isSharedCheck_651_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_snd_615_);
lean_inc(v_fst_614_);
lean_dec(v___x_613_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_651_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v_fst_582_);
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_fst_582_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_snd_615_);
v___x_620_ = v_reuseFailAlloc_650_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = lean_unsigned_to_nat(6u);
v___x_632_ = lean_nat_dec_lt(v___x_631_, v_fst_614_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___y_635_; lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_633_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11);
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_nat_dec_eq(v_fst_614_, v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
lean_inc(v_fst_614_);
v___x_642_ = lean_nat_to_int(v_fst_614_);
v___y_635_ = v___x_642_;
goto v___jp_634_;
}
else
{
v___y_635_ = v___x_633_;
goto v___jp_634_;
}
v___jp_634_:
{
uint8_t v___x_636_; 
v___x_636_ = lean_int_dec_le(v___x_547_, v___y_635_);
if (v___x_636_ == 0)
{
lean_dec(v___y_635_);
lean_dec(v_res_578_);
lean_dec(v_res_552_);
goto v___jp_621_;
}
else
{
uint8_t v___x_637_; 
v___x_637_ = lean_int_dec_le(v___y_635_, v___x_633_);
if (v___x_637_ == 0)
{
lean_dec(v___y_635_);
lean_dec(v_res_578_);
lean_dec(v_res_552_);
goto v___jp_621_;
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec(v_fst_614_);
lean_del_object(v___x_554_);
v___x_638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_638_, 0, v_res_552_);
lean_ctor_set(v___x_638_, 1, v_res_578_);
lean_ctor_set(v___x_638_, 2, v___y_635_);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_620_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
return v___x_639_;
}
}
}
}
else
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec(v_res_578_);
lean_del_object(v___x_554_);
lean_dec(v_res_552_);
v___x_643_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9));
v___x_644_ = l_Nat_reprFast(v_fst_614_);
v___x_645_ = lean_string_append(v___x_643_, v___x_644_);
lean_dec_ref(v___x_644_);
v___x_646_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10));
v___x_647_ = lean_string_append(v___x_645_, v___x_646_);
v___x_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
v___x_649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_620_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
return v___x_649_;
}
v___jp_621_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_622_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9));
v___x_623_ = l_Nat_reprFast(v_fst_614_);
v___x_624_ = lean_string_append(v___x_622_, v___x_623_);
lean_dec_ref(v___x_623_);
v___x_625_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10));
v___x_626_ = lean_string_append(v___x_624_, v___x_625_);
v___x_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
if (v_isShared_555_ == 0)
{
lean_ctor_set_tag(v___x_554_, 1);
lean_ctor_set(v___x_554_, 1, v___x_627_);
lean_ctor_set(v___x_554_, 0, v___x_620_);
v___x_629_ = v___x_554_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_652_; lean_object* v___x_654_; 
lean_dec(v_fst_582_);
lean_del_object(v___x_580_);
lean_dec(v_res_578_);
lean_dec(v_res_552_);
v___x_652_ = lean_box(0);
if (v_isShared_555_ == 0)
{
lean_ctor_set_tag(v___x_554_, 1);
lean_ctor_set(v___x_554_, 1, v___x_652_);
lean_ctor_set(v___x_554_, 0, v_it_x27_597_);
v___x_654_ = v___x_554_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_it_x27_597_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
v___jp_598_:
{
lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_599_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__1));
if (v_isShared_581_ == 0)
{
lean_ctor_set_tag(v___x_580_, 1);
lean_ctor_set(v___x_580_, 1, v___x_599_);
lean_ctor_set(v___x_580_, 0, v_it_x27_597_);
v___x_601_ = v___x_580_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_it_x27_597_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
}
else
{
lean_object* v___x_660_; lean_object* v___x_662_; 
lean_dec(v_res_578_);
lean_del_object(v___x_554_);
lean_dec(v_res_552_);
v___x_660_ = lean_box(0);
if (v_isShared_581_ == 0)
{
lean_ctor_set_tag(v___x_580_, 1);
lean_ctor_set(v___x_580_, 1, v___x_660_);
v___x_662_ = v___x_580_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_pos_577_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
else
{
lean_object* v_pos_665_; lean_object* v_err_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_del_object(v___x_554_);
lean_dec(v_res_552_);
v_pos_665_ = lean_ctor_get(v___x_576_, 0);
v_err_666_ = lean_ctor_get(v___x_576_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_576_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_err_666_);
lean_inc(v_pos_665_);
lean_dec(v___x_576_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_pos_665_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_err_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_678_; lean_object* v___x_680_; 
lean_dec(v_res_552_);
v___x_678_ = lean_box(0);
if (v_isShared_555_ == 0)
{
lean_ctor_set_tag(v___x_554_, 1);
lean_ctor_set(v___x_554_, 1, v___x_678_);
v___x_680_ = v___x_554_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_pos_551_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
else
{
lean_object* v_pos_683_; lean_object* v_err_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
v_pos_683_ = lean_ctor_get(v___x_550_, 0);
v_err_684_ = lean_ctor_get(v___x_550_, 1);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_550_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_err_684_);
lean_inc(v_pos_683_);
lean_dec(v___x_550_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_pos_683_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_err_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_box(0);
v___x_697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_697_, 0, v_a_529_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
return v___x_697_;
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = lean_unsigned_to_nat(365u);
v___x_702_ = lean_nat_to_int(v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec(lean_object* v_a_704_){
_start:
{
lean_object* v_fst_705_; lean_object* v_snd_706_; lean_object* v___x_707_; uint8_t v_decide_708_; 
v_fst_705_ = lean_ctor_get(v_a_704_, 0);
v_snd_706_ = lean_ctor_get(v_a_704_, 1);
v___x_707_ = lean_string_utf8_byte_size(v_fst_705_);
v_decide_708_ = lean_nat_dec_eq(v_snd_706_, v___x_707_);
if (v_decide_708_ == 0)
{
uint32_t v___x_709_; uint32_t v_c_710_; uint8_t v___x_711_; 
v___x_709_ = 74;
v_c_710_ = lean_string_utf8_get_fast(v_fst_705_, v_snd_706_);
v___x_711_ = lean_uint32_dec_eq(v_c_710_, v___x_709_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1));
v___x_713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_713_, 0, v_a_704_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
return v___x_713_;
}
else
{
lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_746_; 
lean_inc(v_snd_706_);
lean_inc(v_fst_705_);
v_isSharedCheck_746_ = !lean_is_exclusive(v_a_704_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; lean_object* v_unused_748_; 
v_unused_747_ = lean_ctor_get(v_a_704_, 1);
lean_dec(v_unused_747_);
v_unused_748_ = lean_ctor_get(v_a_704_, 0);
lean_dec(v_unused_748_);
v___x_715_ = v_a_704_;
v_isShared_716_ = v_isSharedCheck_746_;
goto v_resetjp_714_;
}
else
{
lean_dec(v_a_704_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_746_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___f_718_; lean_object* v___x_719_; lean_object* v_it_x27_721_; 
v___x_717_ = lean_box(v___x_711_);
v___f_718_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_718_, 0, v___x_717_);
v___x_719_ = lean_string_utf8_next_fast(v_fst_705_, v_snd_706_);
lean_dec(v_snd_706_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 1, v___x_719_);
v_it_x27_721_ = v___x_715_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_fst_705_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___x_719_);
v_it_x27_721_ = v_reuseFailAlloc_745_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_722_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_723_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2);
v___x_724_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3));
v___x_725_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_722_, v___x_723_, v___x_724_, v___f_718_, v_it_x27_721_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_pos_726_; lean_object* v_res_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_735_; 
v_pos_726_ = lean_ctor_get(v___x_725_, 0);
v_res_727_ = lean_ctor_get(v___x_725_, 1);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_735_ == 0)
{
v___x_729_ = v___x_725_;
v_isShared_730_ = v_isSharedCheck_735_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_res_727_);
lean_inc(v_pos_726_);
lean_dec(v___x_725_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_735_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_731_, 0, v_res_727_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v___x_731_);
v___x_733_ = v___x_729_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_pos_726_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
else
{
lean_object* v_pos_736_; lean_object* v_err_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
v_pos_736_ = lean_ctor_get(v___x_725_, 0);
v_err_737_ = lean_ctor_get(v___x_725_, 1);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_725_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_err_737_);
lean_inc(v_pos_736_);
lean_dec(v___x_725_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_pos_736_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_err_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_box(0);
v___x_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_750_, 0, v_a_704_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
return v___x_750_;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0(lean_object* v_x_751_){
_start:
{
uint8_t v___x_752_; 
v___x_752_ = 1;
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0___boxed(lean_object* v_x_753_){
_start:
{
uint8_t v_res_754_; lean_object* v_r_755_; 
v_res_754_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0(v_x_753_);
lean_dec(v_x_753_);
v_r_755_ = lean_box(v_res_754_);
return v_r_755_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec(lean_object* v_a_758_){
_start:
{
lean_object* v___f_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___f_759_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__0));
v___x_760_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___x_761_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2);
v___x_762_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__1));
v___x_763_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_760_, v___x_761_, v___x_762_, v___f_759_, v_a_758_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_pos_764_; lean_object* v_res_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_773_; 
v_pos_764_ = lean_ctor_get(v___x_763_, 0);
v_res_765_ = lean_ctor_get(v___x_763_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_773_ == 0)
{
v___x_767_ = v___x_763_;
v_isShared_768_ = v_isSharedCheck_773_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_res_765_);
lean_inc(v_pos_764_);
lean_dec(v___x_763_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_773_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_769_, 0, v_res_765_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v___x_769_);
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_pos_764_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
else
{
lean_object* v_pos_774_; lean_object* v_err_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
v_pos_774_ = lean_ctor_get(v___x_763_, 0);
v_err_775_ = lean_ctor_get(v___x_763_, 1);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_763_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_err_775_);
lean_inc(v_pos_774_);
lean_dec(v___x_763_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_pos_774_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_err_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(lean_object* v_stdOffset_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_fst_785_; lean_object* v_snd_786_; lean_object* v___x_787_; uint8_t v_decide_788_; 
v_fst_785_ = lean_ctor_get(v_a_784_, 0);
v_snd_786_ = lean_ctor_get(v_a_784_, 1);
v___x_787_ = lean_string_utf8_byte_size(v_fst_785_);
v_decide_788_ = lean_nat_dec_eq(v_snd_786_, v___x_787_);
if (v_decide_788_ == 0)
{
uint32_t v___x_789_; uint32_t v___x_800_; uint8_t v___x_801_; 
v___x_789_ = lean_string_utf8_get_fast(v_fst_785_, v_snd_786_);
v___x_800_ = 48;
v___x_801_ = lean_uint32_dec_le(v___x_800_, v___x_789_);
if (v___x_801_ == 0)
{
goto v___jp_790_;
}
else
{
uint32_t v___x_802_; uint8_t v___x_803_; 
v___x_802_ = 57;
v___x_803_ = lean_uint32_dec_le(v___x_789_, v___x_802_);
if (v___x_803_ == 0)
{
goto v___jp_790_;
}
else
{
lean_object* v___x_804_; 
v___x_804_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_784_);
return v___x_804_;
}
}
v___jp_790_:
{
uint32_t v___x_791_; uint8_t v___x_792_; 
v___x_791_ = 43;
v___x_792_ = lean_uint32_dec_eq(v___x_789_, v___x_791_);
if (v___x_792_ == 0)
{
uint32_t v___x_793_; uint8_t v___x_794_; 
v___x_793_ = 45;
v___x_794_ = lean_uint32_dec_eq(v___x_789_, v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_795_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_796_ = lean_int_add(v_stdOffset_783_, v___x_795_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_a_784_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
return v___x_797_;
}
else
{
lean_object* v___x_798_; 
v___x_798_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_784_);
return v___x_798_;
}
}
else
{
lean_object* v___x_799_; 
v___x_799_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_784_);
return v___x_799_;
}
}
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_805_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_806_ = lean_int_add(v_stdOffset_783_, v___x_805_);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v_a_784_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
return v___x_807_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset___boxed(lean_object* v_stdOffset_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(v_stdOffset_808_, v_a_809_);
lean_dec(v_stdOffset_808_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSpec(lean_object* v_a_811_){
_start:
{
lean_object* v___x_812_; 
lean_inc_ref(v_a_811_);
v___x_812_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec(v_a_811_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_dec_ref(v_a_811_);
return v___x_812_;
}
else
{
lean_object* v_err_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_824_; 
v_err_813_ = lean_ctor_get(v___x_812_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v___x_812_, 0);
lean_dec(v_unused_825_);
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_824_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_err_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_824_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v_snd_817_; uint8_t v_decide_818_; 
v_snd_817_ = lean_ctor_get(v_a_811_, 1);
v_decide_818_ = lean_nat_dec_eq(v_snd_817_, v_snd_817_);
if (v_decide_818_ == 0)
{
lean_object* v___x_820_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v_a_811_);
v___x_820_ = v___x_815_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_811_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_err_813_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
else
{
lean_object* v___x_822_; 
lean_del_object(v___x_815_);
lean_dec(v_err_813_);
lean_inc_ref(v_a_811_);
v___x_822_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec(v_a_811_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_dec_ref(v_a_811_);
return v___x_822_;
}
else
{
lean_object* v___x_823_; 
lean_dec_ref_known(v___x_822_, 2);
v___x_823_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec(v_a_811_);
return v___x_823_;
}
}
}
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_unsigned_to_nat(2u);
v___x_827_ = lean_nat_to_int(v___x_826_);
return v___x_827_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_829_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0);
v___x_830_ = lean_int_mul(v___x_829_, v___x_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(uint8_t v_extended_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSpec(v_a_835_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_pos_837_; lean_object* v_res_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_880_; 
v_pos_837_ = lean_ctor_get(v___x_836_, 0);
v_res_838_ = lean_ctor_get(v___x_836_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_880_ == 0)
{
v___x_840_ = v___x_836_;
v_isShared_841_ = v_isSharedCheck_880_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_res_838_);
lean_inc(v_pos_837_);
lean_dec(v___x_836_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_880_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v_pos_843_; lean_object* v_res_844_; lean_object* v_fst_849_; lean_object* v_snd_850_; lean_object* v_pos_852_; lean_object* v_snd_853_; lean_object* v_err_854_; lean_object* v___x_858_; uint8_t v_decide_859_; 
v_fst_849_ = lean_ctor_get(v_pos_837_, 0);
v_snd_850_ = lean_ctor_get(v_pos_837_, 1);
lean_inc(v_snd_850_);
v___x_858_ = lean_string_utf8_byte_size(v_fst_849_);
v_decide_859_ = lean_nat_dec_eq(v_snd_850_, v___x_858_);
if (v_decide_859_ == 0)
{
uint32_t v___x_860_; uint32_t v_c_861_; uint8_t v___x_862_; 
v___x_860_ = 47;
v_c_861_ = lean_string_utf8_get_fast(v_fst_849_, v_snd_850_);
v___x_862_ = lean_uint32_dec_eq(v_c_861_, v___x_860_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; 
v___x_863_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3));
lean_inc(v_snd_850_);
v_pos_852_ = v_pos_837_;
v_snd_853_ = v_snd_850_;
v_err_854_ = v___x_863_;
goto v___jp_851_;
}
else
{
lean_object* v___x_864_; lean_object* v_it_x27_865_; lean_object* v___x_866_; 
v___x_864_ = lean_string_utf8_next_fast(v_fst_849_, v_snd_850_);
lean_inc(v_fst_849_);
v_it_x27_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_865_, 0, v_fst_849_);
lean_ctor_set(v_it_x27_865_, 1, v___x_864_);
v___x_866_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(v_it_x27_865_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_pos_867_; lean_object* v_res_868_; lean_object* v___y_870_; 
v_pos_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_pos_867_);
v_res_868_ = lean_ctor_get(v___x_866_, 1);
lean_inc(v_res_868_);
lean_dec_ref_known(v___x_866_, 2);
if (v_extended_834_ == 0)
{
lean_object* v___x_876_; 
v___x_876_ = lean_unsigned_to_nat(24u);
v___y_870_ = v___x_876_;
goto v___jp_869_;
}
else
{
lean_object* v___x_877_; 
v___x_877_ = lean_unsigned_to_nat(167u);
v___y_870_ = v___x_877_;
goto v___jp_869_;
}
v___jp_869_:
{
lean_object* v___x_871_; 
v___x_871_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(v___y_870_, v_pos_867_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_pos_872_; lean_object* v_res_873_; lean_object* v___x_874_; 
lean_dec(v_snd_850_);
lean_dec(v_pos_837_);
v_pos_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_pos_872_);
v_res_873_ = lean_ctor_get(v___x_871_, 1);
lean_inc(v_res_873_);
lean_dec_ref_known(v___x_871_, 2);
v___x_874_ = lean_int_mul(v_res_868_, v_res_873_);
lean_dec(v_res_873_);
lean_dec(v_res_868_);
v_pos_843_ = v_pos_872_;
v_res_844_ = v___x_874_;
goto v___jp_842_;
}
else
{
lean_object* v_err_875_; 
lean_dec(v_res_868_);
v_err_875_ = lean_ctor_get(v___x_871_, 1);
lean_inc(v_err_875_);
lean_dec_ref_known(v___x_871_, 2);
lean_inc(v_snd_850_);
v_pos_852_ = v_pos_837_;
v_snd_853_ = v_snd_850_;
v_err_854_ = v_err_875_;
goto v___jp_851_;
}
}
}
else
{
lean_object* v_err_878_; 
v_err_878_ = lean_ctor_get(v___x_866_, 1);
lean_inc(v_err_878_);
lean_dec_ref_known(v___x_866_, 2);
lean_inc(v_snd_850_);
v_pos_852_ = v_pos_837_;
v_snd_853_ = v_snd_850_;
v_err_854_ = v_err_878_;
goto v___jp_851_;
}
}
}
else
{
lean_object* v___x_879_; 
v___x_879_ = lean_box(0);
lean_inc(v_snd_850_);
v_pos_852_ = v_pos_837_;
v_snd_853_ = v_snd_850_;
v_err_854_ = v___x_879_;
goto v___jp_851_;
}
v___jp_842_:
{
lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v_res_838_);
lean_ctor_set(v___x_845_, 1, v_res_844_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v___x_845_);
lean_ctor_set(v___x_840_, 0, v_pos_843_);
v___x_847_ = v___x_840_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_pos_843_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
v___jp_851_:
{
uint8_t v_decide_855_; 
v_decide_855_ = lean_nat_dec_eq(v_snd_850_, v_snd_853_);
lean_dec(v_snd_853_);
lean_dec(v_snd_850_);
if (v_decide_855_ == 0)
{
lean_object* v___x_856_; 
lean_del_object(v___x_840_);
lean_dec(v_res_838_);
v___x_856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_856_, 0, v_pos_852_);
lean_ctor_set(v___x_856_, 1, v_err_854_);
return v___x_856_;
}
else
{
lean_object* v___x_857_; 
lean_dec(v_err_854_);
v___x_857_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1);
v_pos_843_ = v_pos_852_;
v_res_844_ = v___x_857_;
goto v___jp_842_;
}
}
}
}
else
{
lean_object* v_pos_881_; lean_object* v_err_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
v_pos_881_ = lean_ctor_get(v___x_836_, 0);
v_err_882_ = lean_ctor_get(v___x_836_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_836_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_err_882_);
lean_inc(v_pos_881_);
lean_dec(v___x_836_);
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
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___boxed(lean_object* v_extended_890_, lean_object* v_a_891_){
_start:
{
uint8_t v_extended_boxed_892_; lean_object* v_res_893_; 
v_extended_boxed_892_ = lean_unbox(v_extended_890_);
v_res_893_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_boxed_892_, v_a_891_);
return v_res_893_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_894_; lean_object* v___x_895_; 
v___x_894_ = 44;
v___x_895_ = lean_box_uint32(v___x_894_);
return v___x_895_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0___boxed__const__1;
v___x_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP(uint8_t v_extended_904_, lean_object* v_a_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(v_a_905_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_pos_907_; lean_object* v_res_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_1086_; 
v_pos_907_ = lean_ctor_get(v___x_906_, 0);
v_res_908_ = lean_ctor_get(v___x_906_, 1);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_910_ = v___x_906_;
v_isShared_911_ = v_isSharedCheck_1086_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_res_908_);
lean_inc(v_pos_907_);
lean_dec(v___x_906_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_1086_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_912_ = lean_string_utf8_byte_size(v_res_908_);
v___x_913_ = lean_unsigned_to_nat(0u);
v___x_914_ = lean_nat_dec_eq(v___x_912_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; 
lean_del_object(v___x_910_);
v___x_915_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_pos_907_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_pos_916_; lean_object* v_res_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_1072_; 
v_pos_916_ = lean_ctor_get(v___x_915_, 0);
v_res_917_ = lean_ctor_get(v___x_915_, 1);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_919_ = v___x_915_;
v_isShared_920_ = v_isSharedCheck_1072_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_res_917_);
lean_inc(v_pos_916_);
lean_dec(v___x_915_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_1072_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v_fst_921_; lean_object* v_snd_922_; lean_object* v___x_923_; uint8_t v_decide_924_; 
v_fst_921_ = lean_ctor_get(v_pos_916_, 0);
v_snd_922_ = lean_ctor_get(v_pos_916_, 1);
v___x_923_ = lean_string_utf8_byte_size(v_fst_921_);
v_decide_924_ = lean_nat_dec_eq(v_snd_922_, v___x_923_);
if (v_decide_924_ == 0)
{
lean_object* v___x_925_; 
lean_del_object(v___x_919_);
v___x_925_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(v_pos_916_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_pos_926_; lean_object* v_res_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_1057_; 
v_pos_926_ = lean_ctor_get(v___x_925_, 0);
v_res_927_ = lean_ctor_get(v___x_925_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_929_ = v___x_925_;
v_isShared_930_ = v_isSharedCheck_1057_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_res_927_);
lean_inc(v_pos_926_);
lean_dec(v___x_925_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_1057_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_931_ = lean_string_utf8_byte_size(v_res_927_);
v___x_932_ = lean_nat_dec_eq(v___x_931_, v___x_913_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; 
lean_del_object(v___x_929_);
v___x_933_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(v_res_917_, v_pos_926_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_pos_934_; lean_object* v_res_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_1042_; 
v_pos_934_ = lean_ctor_get(v___x_933_, 0);
v_res_935_ = lean_ctor_get(v___x_933_, 1);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_937_ = v___x_933_;
v_isShared_938_ = v_isSharedCheck_1042_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_res_935_);
lean_inc(v_pos_934_);
lean_dec(v___x_933_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_1042_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v_pos_940_; lean_object* v_res_941_; lean_object* v_fst_1034_; lean_object* v_snd_1035_; lean_object* v___x_1036_; uint8_t v_decide_1037_; 
v_fst_1034_ = lean_ctor_get(v_pos_934_, 0);
v_snd_1035_ = lean_ctor_get(v_pos_934_, 1);
v___x_1036_ = lean_string_utf8_byte_size(v_fst_1034_);
v_decide_1037_ = lean_nat_dec_eq(v_snd_1035_, v___x_1036_);
if (v_decide_1037_ == 0)
{
uint32_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = lean_string_utf8_get_fast(v_fst_1034_, v_snd_1035_);
v___x_1039_ = lean_box_uint32(v___x_1038_);
v___x_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
v_pos_940_ = v_pos_934_;
v_res_941_ = v___x_1040_;
goto v___jp_939_;
}
else
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_box(0);
v_pos_940_ = v_pos_934_;
v_res_941_ = v___x_1041_;
goto v___jp_939_;
}
v___jp_939_:
{
uint32_t v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_942_ = 44;
v___x_943_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0);
v___x_944_ = l_instBEqOption_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_res_941_, v___x_943_);
lean_dec(v_res_941_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_945_ = lean_box(0);
v___x_946_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_946_, 0, v_res_927_);
lean_ctor_set(v___x_946_, 1, v_res_935_);
lean_ctor_set(v___x_946_, 2, v___x_945_);
lean_ctor_set(v___x_946_, 3, v___x_945_);
v___x_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_948_, 0, v_res_908_);
lean_ctor_set(v___x_948_, 1, v_res_917_);
lean_ctor_set(v___x_948_, 2, v___x_947_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 1, v___x_948_);
lean_ctor_set(v___x_937_, 0, v_pos_940_);
v___x_950_ = v___x_937_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_pos_940_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
else
{
lean_object* v_fst_952_; lean_object* v_snd_953_; lean_object* v___x_954_; uint8_t v_decide_955_; 
v_fst_952_ = lean_ctor_get(v_pos_940_, 0);
v_snd_953_ = lean_ctor_get(v_pos_940_, 1);
v___x_954_ = lean_string_utf8_byte_size(v_fst_952_);
v_decide_955_ = lean_nat_dec_eq(v_snd_953_, v___x_954_);
if (v_decide_955_ == 0)
{
lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_1027_; 
lean_inc(v_snd_953_);
lean_inc(v_fst_952_);
lean_del_object(v___x_937_);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_pos_940_);
if (v_isSharedCheck_1027_ == 0)
{
lean_object* v_unused_1028_; lean_object* v_unused_1029_; 
v_unused_1028_ = lean_ctor_get(v_pos_940_, 1);
lean_dec(v_unused_1028_);
v_unused_1029_ = lean_ctor_get(v_pos_940_, 0);
lean_dec(v_unused_1029_);
v___x_957_ = v_pos_940_;
v_isShared_958_ = v_isSharedCheck_1027_;
goto v_resetjp_956_;
}
else
{
lean_dec(v_pos_940_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_1027_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_959_ = lean_string_utf8_next_fast(v_fst_952_, v_snd_953_);
lean_dec(v_snd_953_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v___x_959_);
v___x_961_ = v___x_957_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_fst_952_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v___x_959_);
v___x_961_ = v_reuseFailAlloc_1026_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; 
v___x_962_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_904_, v___x_961_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_pos_963_; lean_object* v_res_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_1016_; 
v_pos_963_ = lean_ctor_get(v___x_962_, 0);
v_res_964_ = lean_ctor_get(v___x_962_, 1);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_966_ = v___x_962_;
v_isShared_967_ = v_isSharedCheck_1016_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_res_964_);
lean_inc(v_pos_963_);
lean_dec(v___x_962_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_1016_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v_fst_968_; lean_object* v_snd_969_; lean_object* v___x_970_; uint8_t v_decide_971_; 
v_fst_968_ = lean_ctor_get(v_pos_963_, 0);
v_snd_969_ = lean_ctor_get(v_pos_963_, 1);
v___x_970_ = lean_string_utf8_byte_size(v_fst_968_);
v_decide_971_ = lean_nat_dec_eq(v_snd_969_, v___x_970_);
if (v_decide_971_ == 0)
{
uint32_t v_c_972_; uint8_t v___x_973_; 
v_c_972_ = lean_string_utf8_get_fast(v_fst_968_, v_snd_969_);
v___x_973_ = lean_uint32_dec_eq(v_c_972_, v___x_942_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v___x_976_; 
lean_dec(v_res_964_);
lean_dec(v_res_935_);
lean_dec(v_res_927_);
lean_dec(v_res_917_);
lean_dec(v_res_908_);
v___x_974_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2));
if (v_isShared_967_ == 0)
{
lean_ctor_set_tag(v___x_966_, 1);
lean_ctor_set(v___x_966_, 1, v___x_974_);
v___x_976_ = v___x_966_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_pos_963_);
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
lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1009_; 
lean_inc(v_snd_969_);
lean_inc(v_fst_968_);
lean_del_object(v___x_966_);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_pos_963_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; lean_object* v_unused_1011_; 
v_unused_1010_ = lean_ctor_get(v_pos_963_, 1);
lean_dec(v_unused_1010_);
v_unused_1011_ = lean_ctor_get(v_pos_963_, 0);
lean_dec(v_unused_1011_);
v___x_979_ = v_pos_963_;
v_isShared_980_ = v_isSharedCheck_1009_;
goto v_resetjp_978_;
}
else
{
lean_dec(v_pos_963_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1009_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; lean_object* v_it_x27_983_; 
v___x_981_ = lean_string_utf8_next_fast(v_fst_968_, v_snd_969_);
lean_dec(v_snd_969_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v___x_981_);
v_it_x27_983_ = v___x_979_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_fst_968_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v___x_981_);
v_it_x27_983_ = v_reuseFailAlloc_1008_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; 
v___x_984_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_904_, v_it_x27_983_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_pos_985_; lean_object* v_res_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_998_; 
v_pos_985_ = lean_ctor_get(v___x_984_, 0);
v_res_986_ = lean_ctor_get(v___x_984_, 1);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_998_ == 0)
{
v___x_988_ = v___x_984_;
v_isShared_989_ = v_isSharedCheck_998_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_res_986_);
lean_inc(v_pos_985_);
lean_dec(v___x_984_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_998_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_990_, 0, v_res_964_);
v___x_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_991_, 0, v_res_986_);
v___x_992_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_992_, 0, v_res_927_);
lean_ctor_set(v___x_992_, 1, v_res_935_);
lean_ctor_set(v___x_992_, 2, v___x_990_);
lean_ctor_set(v___x_992_, 3, v___x_991_);
v___x_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
v___x_994_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_994_, 0, v_res_908_);
lean_ctor_set(v___x_994_, 1, v_res_917_);
lean_ctor_set(v___x_994_, 2, v___x_993_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 1, v___x_994_);
v___x_996_ = v___x_988_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_pos_985_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
else
{
lean_object* v_pos_999_; lean_object* v_err_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec(v_res_964_);
lean_dec(v_res_935_);
lean_dec(v_res_927_);
lean_dec(v_res_917_);
lean_dec(v_res_908_);
v_pos_999_ = lean_ctor_get(v___x_984_, 0);
v_err_1000_ = lean_ctor_get(v___x_984_, 1);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_984_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_err_1000_);
lean_inc(v_pos_999_);
lean_dec(v___x_984_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_pos_999_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_err_1000_);
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
}
}
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1014_; 
lean_dec(v_res_964_);
lean_dec(v_res_935_);
lean_dec(v_res_927_);
lean_dec(v_res_917_);
lean_dec(v_res_908_);
v___x_1012_ = lean_box(0);
if (v_isShared_967_ == 0)
{
lean_ctor_set_tag(v___x_966_, 1);
lean_ctor_set(v___x_966_, 1, v___x_1012_);
v___x_1014_ = v___x_966_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_pos_963_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
else
{
lean_object* v_pos_1017_; lean_object* v_err_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec(v_res_935_);
lean_dec(v_res_927_);
lean_dec(v_res_917_);
lean_dec(v_res_908_);
v_pos_1017_ = lean_ctor_get(v___x_962_, 0);
v_err_1018_ = lean_ctor_get(v___x_962_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_962_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_err_1018_);
lean_inc(v_pos_1017_);
lean_dec(v___x_962_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_pos_1017_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_err_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
lean_dec(v_res_935_);
lean_dec(v_res_927_);
lean_dec(v_res_917_);
lean_dec(v_res_908_);
v___x_1030_ = lean_box(0);
if (v_isShared_938_ == 0)
{
lean_ctor_set_tag(v___x_937_, 1);
lean_ctor_set(v___x_937_, 1, v___x_1030_);
lean_ctor_set(v___x_937_, 0, v_pos_940_);
v___x_1032_ = v___x_937_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_pos_940_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1043_; lean_object* v_err_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec(v_res_927_);
lean_dec(v_res_917_);
lean_dec(v_res_908_);
v_pos_1043_ = lean_ctor_get(v___x_933_, 0);
v_err_1044_ = lean_ctor_get(v___x_933_, 1);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_933_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_err_1044_);
lean_inc(v_pos_1043_);
lean_dec(v___x_933_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_pos_1043_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_err_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
lean_dec(v_res_927_);
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1053_, 0, v_res_908_);
lean_ctor_set(v___x_1053_, 1, v_res_917_);
lean_ctor_set(v___x_1053_, 2, v___x_1052_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v___x_1053_);
v___x_1055_ = v___x_929_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_pos_926_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v_pos_1058_; lean_object* v_err_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec(v_res_917_);
lean_dec(v_res_908_);
v_pos_1058_ = lean_ctor_get(v___x_925_, 0);
v_err_1059_ = lean_ctor_get(v___x_925_, 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_925_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_err_1059_);
lean_inc(v_pos_1058_);
lean_dec(v___x_925_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_pos_1058_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_err_1059_);
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
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1067_ = lean_box(0);
v___x_1068_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1068_, 0, v_res_908_);
lean_ctor_set(v___x_1068_, 1, v_res_917_);
lean_ctor_set(v___x_1068_, 2, v___x_1067_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 1, v___x_1068_);
v___x_1070_ = v___x_919_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_pos_916_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
else
{
lean_object* v_pos_1073_; lean_object* v_err_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_dec(v_res_908_);
v_pos_1073_ = lean_ctor_get(v___x_915_, 0);
v_err_1074_ = lean_ctor_get(v___x_915_, 1);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_915_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_err_1074_);
lean_inc(v_pos_1073_);
lean_dec(v___x_915_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_pos_1073_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_err_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
lean_dec(v_res_908_);
v___x_1082_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__4));
if (v_isShared_911_ == 0)
{
lean_ctor_set_tag(v___x_910_, 1);
lean_ctor_set(v___x_910_, 1, v___x_1082_);
v___x_1084_ = v___x_910_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_pos_907_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
else
{
lean_object* v_pos_1087_; lean_object* v_err_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
v_pos_1087_ = lean_ctor_get(v___x_906_, 0);
v_err_1088_ = lean_ctor_get(v___x_906_, 1);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_906_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_err_1088_);
lean_inc(v_pos_1087_);
lean_dec(v___x_906_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_pos_1087_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_err_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___boxed(lean_object* v_extended_1096_, lean_object* v_a_1097_){
_start:
{
uint8_t v_extended_boxed_1098_; lean_object* v_res_1099_; 
v_extended_boxed_1098_ = lean_unbox(v_extended_1096_);
v_res_1099_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP(v_extended_boxed_1098_, v_a_1097_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_parsePosixTz(lean_object* v_s_1100_, uint8_t v_extended_1101_){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = lean_box(v_extended_1101_);
v___x_1103_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___boxed), 2, 1);
lean_closure_set(v___x_1103_, 0, v___x_1102_);
v___x_1104_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_1103_, v_s_1100_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_parsePosixTz___boxed(lean_object* v_s_1105_, lean_object* v_extended_1106_){
_start:
{
uint8_t v_extended_boxed_1107_; lean_object* v_res_1108_; 
v_extended_boxed_1107_ = lean_unbox(v_extended_1106_);
v_res_1108_ = l_Std_Time_TimeZone_parsePosixTz(v_s_1105_, v_extended_boxed_1107_);
return v_res_1108_;
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
