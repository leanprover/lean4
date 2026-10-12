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
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
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
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "day "};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " out of range 0-6"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: 'M'"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__2_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3_value;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "week"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: '.'"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__8_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9_value;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "month"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11_value;
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
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: ','"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__0_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2___boxed__const__1;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2;
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
lean_object* v_fst_87_; lean_object* v_snd_88_; lean_object* v_err_90_; lean_object* v_err_98_; lean_object* v___x_119_; uint8_t v_decide_120_; 
v_fst_87_ = lean_ctor_get(v_a_86_, 0);
v_snd_88_ = lean_ctor_get(v_a_86_, 1);
v___x_119_ = lean_string_utf8_byte_size(v_fst_87_);
v_decide_120_ = lean_nat_dec_eq(v_snd_88_, v___x_119_);
if (v_decide_120_ == 0)
{
uint32_t v___x_121_; uint32_t v_c_122_; uint8_t v___x_123_; 
v___x_121_ = 45;
v_c_122_ = lean_string_utf8_get_fast(v_fst_87_, v_snd_88_);
v___x_123_ = lean_uint32_dec_eq(v_c_122_, v___x_121_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; 
v___x_124_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4));
v_err_98_ = v___x_124_;
goto v___jp_97_;
}
else
{
lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_134_; 
lean_inc(v_snd_88_);
lean_inc(v_fst_87_);
v_isSharedCheck_134_ = !lean_is_exclusive(v_a_86_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; lean_object* v_unused_136_; 
v_unused_135_ = lean_ctor_get(v_a_86_, 1);
lean_dec(v_unused_135_);
v_unused_136_ = lean_ctor_get(v_a_86_, 0);
lean_dec(v_unused_136_);
v___x_126_ = v_a_86_;
v_isShared_127_ = v_isSharedCheck_134_;
goto v_resetjp_125_;
}
else
{
lean_dec(v_a_86_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_134_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v_it_x27_130_; 
v___x_128_ = lean_string_utf8_next_fast(v_fst_87_, v_snd_88_);
lean_dec(v_snd_88_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v___x_128_);
v_it_x27_130_ = v___x_126_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_fst_87_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___x_128_);
v_it_x27_130_ = v_reuseFailAlloc_133_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v_it_x27_130_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
return v___x_132_;
}
}
}
}
else
{
lean_object* v___x_137_; 
v___x_137_ = lean_box(0);
v_err_98_ = v___x_137_;
goto v___jp_97_;
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
lean_object* v___x_96_; 
v___x_96_ = lean_box(0);
v_err_90_ = v___x_96_;
goto v___jp_89_;
}
v___jp_97_:
{
uint8_t v_decide_99_; 
v_decide_99_ = lean_nat_dec_eq(v_snd_88_, v_snd_88_);
if (v_decide_99_ == 0)
{
lean_object* v___x_100_; 
lean_inc(v_err_98_);
v___x_100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_100_, 0, v_a_86_);
lean_ctor_set(v___x_100_, 1, v_err_98_);
return v___x_100_;
}
else
{
lean_object* v___x_101_; uint8_t v_decide_102_; 
v___x_101_ = lean_string_utf8_byte_size(v_fst_87_);
v_decide_102_ = lean_nat_dec_eq(v_snd_88_, v___x_101_);
if (v_decide_102_ == 0)
{
if (v_decide_99_ == 0)
{
goto v___jp_95_;
}
else
{
uint32_t v___x_103_; uint32_t v_c_104_; uint8_t v___x_105_; 
v___x_103_ = 43;
v_c_104_ = lean_string_utf8_get_fast(v_fst_87_, v_snd_88_);
v___x_105_ = lean_uint32_dec_eq(v_c_104_, v___x_103_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
v___x_106_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v_err_90_ = v___x_106_;
goto v___jp_89_;
}
else
{
lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_116_; 
lean_inc(v_snd_88_);
lean_inc(v_fst_87_);
v_isSharedCheck_116_ = !lean_is_exclusive(v_a_86_);
if (v_isSharedCheck_116_ == 0)
{
lean_object* v_unused_117_; lean_object* v_unused_118_; 
v_unused_117_ = lean_ctor_get(v_a_86_, 1);
lean_dec(v_unused_117_);
v_unused_118_ = lean_ctor_get(v_a_86_, 0);
lean_dec(v_unused_118_);
v___x_108_ = v_a_86_;
v_isShared_109_ = v_isSharedCheck_116_;
goto v_resetjp_107_;
}
else
{
lean_dec(v_a_86_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_116_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; lean_object* v_it_x27_112_; 
v___x_110_ = lean_string_utf8_next_fast(v_fst_87_, v_snd_88_);
lean_dec(v_snd_88_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 1, v___x_110_);
v_it_x27_112_ = v___x_108_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_fst_87_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v___x_110_);
v_it_x27_112_ = v_reuseFailAlloc_115_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v_it_x27_112_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
return v___x_114_;
}
}
}
}
}
else
{
goto v___jp_95_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__0(lean_object* v_a_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_nat_to_int(v_a_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__2(lean_object* v_a_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Rat_ofInt(v_a_140_);
return v___x_141_;
}
}
uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0(uint8_t v___x_142_, lean_object* v_x_143_){
_start:
{
return v___x_142_;
}
}
LEAN_EXPORT void l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_142_ = stack[0].m_num;
lean_object* v_x_143_ = stack[1].m_obj;
uint8_t v_res_144_;
v_res_144_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0(v___x_142_, v_x_143_);
stack->m_num = v_res_144_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed(lean_object* v___x_145_, lean_object* v_x_146_){
_start:
{
uint8_t v___x_3944__boxed_147_; uint8_t v_res_148_; lean_object* v_r_149_; 
v___x_3944__boxed_147_ = lean_unbox(v___x_145_);
v_res_148_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0(v___x_3944__boxed_147_, v_x_146_);
lean_dec(v_x_146_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(3600u);
v___x_154_ = lean_nat_to_int(v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_unsigned_to_nat(60u);
v___x_156_ = lean_nat_to_int(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = lean_nat_to_int(v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(59u);
v___x_163_ = lean_nat_to_int(v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(lean_object* v_maxHour_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_fst_171_; lean_object* v_snd_172_; lean_object* v___x_173_; uint8_t v_decide_174_; 
v_fst_171_ = lean_ctor_get(v_a_167_, 0);
v_snd_172_ = lean_ctor_get(v_a_167_, 1);
v___x_173_ = lean_string_utf8_byte_size(v_fst_171_);
v_decide_174_ = lean_nat_dec_eq(v_snd_172_, v___x_173_);
if (v_decide_174_ == 0)
{
uint32_t v_c_175_; uint32_t v___x_176_; uint8_t v___x_177_; 
v_c_175_ = lean_string_utf8_get_fast(v_fst_171_, v_snd_172_);
v___x_176_ = 48;
v___x_177_ = lean_uint32_dec_le(v___x_176_, v_c_175_);
if (v___x_177_ == 0)
{
lean_dec(v_maxHour_166_);
goto v___jp_168_;
}
else
{
uint32_t v___x_178_; uint8_t v___x_179_; 
v___x_178_ = 57;
v___x_179_ = lean_uint32_dec_le(v_c_175_, v___x_178_);
if (v___x_179_ == 0)
{
lean_dec(v_maxHour_166_);
goto v___jp_168_;
}
else
{
lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_298_; 
lean_inc(v_snd_172_);
lean_inc(v_fst_171_);
v_isSharedCheck_298_ = !lean_is_exclusive(v_a_167_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; lean_object* v_unused_300_; 
v_unused_299_ = lean_ctor_get(v_a_167_, 1);
lean_dec(v_unused_299_);
v_unused_300_ = lean_ctor_get(v_a_167_, 0);
lean_dec(v_unused_300_);
v___x_181_ = v_a_167_;
v_isShared_182_ = v_isSharedCheck_298_;
goto v_resetjp_180_;
}
else
{
lean_dec(v_a_167_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_298_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v_fst_188_; lean_object* v_snd_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_297_; 
v___x_183_ = lean_string_utf8_next_fast(v_fst_171_, v_snd_172_);
lean_dec(v_snd_172_);
v___x_184_ = lean_uint32_to_nat(v_c_175_);
v___x_185_ = lean_unsigned_to_nat(48u);
v___x_186_ = lean_nat_sub(v___x_184_, v___x_185_);
lean_dec(v___x_184_);
v___x_187_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_171_, v___x_183_, v___x_186_);
v_fst_188_ = lean_ctor_get(v___x_187_, 0);
v_snd_189_ = lean_ctor_get(v___x_187_, 1);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_297_ == 0)
{
v___x_191_ = v___x_187_;
v_isShared_192_ = v_isSharedCheck_297_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_snd_189_);
lean_inc(v_fst_188_);
lean_dec(v___x_187_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_297_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
lean_inc(v_snd_189_);
lean_inc(v_fst_171_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 1, v_snd_189_);
v___x_194_ = v___x_181_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_fst_171_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_snd_189_);
v___x_194_ = v_reuseFailAlloc_296_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
uint8_t v___x_195_; 
v___x_195_ = lean_nat_dec_lt(v_maxHour_166_, v_fst_188_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; uint8_t v___x_197_; 
lean_dec(v_maxHour_166_);
v___x_196_ = lean_unsigned_to_nat(167u);
v___x_197_ = lean_nat_dec_le(v_fst_188_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_207_; 
lean_dec(v_snd_189_);
lean_dec(v_fst_171_);
v___x_198_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0));
v___x_199_ = l_Nat_reprFast(v_fst_188_);
v___x_200_ = lean_string_append(v___x_198_, v___x_199_);
lean_dec_ref(v___x_199_);
v___x_201_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1));
v___x_202_ = lean_string_append(v___x_200_, v___x_201_);
v___x_203_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2));
v___x_204_ = lean_string_append(v___x_202_, v___x_203_);
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
if (v_isShared_192_ == 0)
{
lean_ctor_set_tag(v___x_191_, 1);
lean_ctor_set(v___x_191_, 1, v___x_205_);
lean_ctor_set(v___x_191_, 0, v___x_194_);
v___x_207_ = v___x_191_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v___x_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
else
{
lean_object* v___x_209_; lean_object* v___y_211_; lean_object* v_pos_212_; lean_object* v_res_213_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v_err_226_; uint32_t v___x_231_; lean_object* v___y_233_; lean_object* v___y_234_; lean_object* v___y_235_; lean_object* v___y_236_; uint8_t v___y_237_; lean_object* v_pos_254_; lean_object* v_fst_255_; lean_object* v_snd_256_; lean_object* v_res_257_; lean_object* v_err_261_; uint8_t v___y_266_; uint8_t v_decide_284_; 
v___x_209_ = lean_nat_to_int(v_fst_188_);
v___x_231_ = 58;
v_decide_284_ = lean_nat_dec_eq(v_snd_189_, v___x_173_);
if (v_decide_284_ == 0)
{
v___y_266_ = v___x_197_;
goto v___jp_265_;
}
else
{
v___y_266_ = v___x_195_;
goto v___jp_265_;
}
v___jp_210_:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_214_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_215_ = lean_int_mul(v___x_209_, v___x_214_);
lean_dec(v___x_209_);
v___x_216_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4);
v___x_217_ = lean_int_mul(v___y_211_, v___x_216_);
lean_dec(v___y_211_);
v___x_218_ = lean_int_add(v___x_215_, v___x_217_);
lean_dec(v___x_217_);
lean_dec(v___x_215_);
v___x_219_ = lean_int_add(v___x_218_, v_res_213_);
lean_dec(v_res_213_);
lean_dec(v___x_218_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v___x_219_);
lean_ctor_set(v___x_191_, 0, v_pos_212_);
v___x_221_ = v___x_191_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_pos_212_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
v___jp_223_:
{
lean_object* v_snd_227_; uint8_t v_decide_228_; 
v_snd_227_ = lean_ctor_get(v___y_225_, 1);
v_decide_228_ = lean_nat_dec_eq(v_snd_227_, v_snd_227_);
if (v_decide_228_ == 0)
{
lean_object* v___x_229_; 
lean_dec(v___y_224_);
lean_dec(v___x_209_);
lean_del_object(v___x_191_);
v___x_229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_229_, 0, v___y_225_);
lean_ctor_set(v___x_229_, 1, v_err_226_);
return v___x_229_;
}
else
{
lean_object* v___x_230_; 
lean_dec(v_err_226_);
v___x_230_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___y_211_ = v___y_224_;
v_pos_212_ = v___y_225_;
v_res_213_ = v___x_230_;
goto v___jp_210_;
}
}
v___jp_232_:
{
if (v___y_237_ == 0)
{
lean_object* v___x_238_; 
lean_dec(v___y_236_);
lean_dec(v___y_234_);
v___x_238_ = lean_box(0);
v___y_224_ = v___y_233_;
v___y_225_ = v___y_235_;
v_err_226_ = v___x_238_;
goto v___jp_223_;
}
else
{
uint32_t v_c_239_; uint8_t v___x_240_; 
v_c_239_ = lean_string_utf8_get_fast(v___y_236_, v___y_234_);
v___x_240_ = lean_uint32_dec_eq(v_c_239_, v___x_231_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; 
lean_dec(v___y_236_);
lean_dec(v___y_234_);
v___x_241_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7));
v___y_224_ = v___y_233_;
v___y_225_ = v___y_235_;
v_err_226_ = v___x_241_;
goto v___jp_223_;
}
else
{
lean_object* v___x_242_; lean_object* v___f_243_; lean_object* v___x_244_; lean_object* v_it_x27_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_242_ = lean_box(v___x_240_);
v___f_243_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_243_, 0, v___x_242_);
v___x_244_ = lean_string_utf8_next_fast(v___y_236_, v___y_234_);
lean_dec(v___y_234_);
v_it_x27_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_245_, 0, v___y_236_);
lean_ctor_set(v_it_x27_245_, 1, v___x_244_);
v___x_246_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___x_247_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8);
v___x_248_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9));
v___x_249_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_246_, v___x_247_, v___x_248_, v___f_243_, v_it_x27_245_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_pos_250_; lean_object* v_res_251_; 
lean_dec_ref(v___y_235_);
v_pos_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_pos_250_);
v_res_251_ = lean_ctor_get(v___x_249_, 1);
lean_inc(v_res_251_);
lean_dec_ref_known(v___x_249_, 2);
v___y_211_ = v___y_233_;
v_pos_212_ = v_pos_250_;
v_res_213_ = v_res_251_;
goto v___jp_210_;
}
else
{
lean_object* v_err_252_; 
v_err_252_ = lean_ctor_get(v___x_249_, 1);
lean_inc(v_err_252_);
lean_dec_ref_known(v___x_249_, 2);
v___y_224_ = v___y_233_;
v___y_225_ = v___y_235_;
v_err_226_ = v_err_252_;
goto v___jp_223_;
}
}
}
}
v___jp_253_:
{
lean_object* v___x_258_; uint8_t v_decide_259_; 
v___x_258_ = lean_string_utf8_byte_size(v_fst_255_);
v_decide_259_ = lean_nat_dec_eq(v_snd_256_, v___x_258_);
if (v_decide_259_ == 0)
{
v___y_233_ = v_res_257_;
v___y_234_ = v_snd_256_;
v___y_235_ = v_pos_254_;
v___y_236_ = v_fst_255_;
v___y_237_ = v___x_197_;
goto v___jp_232_;
}
else
{
v___y_233_ = v_res_257_;
v___y_234_ = v_snd_256_;
v___y_235_ = v_pos_254_;
v___y_236_ = v_fst_255_;
v___y_237_ = v___x_195_;
goto v___jp_232_;
}
}
v___jp_260_:
{
uint8_t v_decide_262_; 
v_decide_262_ = lean_nat_dec_eq(v_snd_189_, v_snd_189_);
if (v_decide_262_ == 0)
{
lean_object* v___x_263_; 
lean_dec(v___x_209_);
lean_del_object(v___x_191_);
lean_dec(v_snd_189_);
lean_dec(v_fst_171_);
v___x_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_194_);
lean_ctor_set(v___x_263_, 1, v_err_261_);
return v___x_263_;
}
else
{
lean_object* v___x_264_; 
lean_dec(v_err_261_);
v___x_264_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v_pos_254_ = v___x_194_;
v_fst_255_ = v_fst_171_;
v_snd_256_ = v_snd_189_;
v_res_257_ = v___x_264_;
goto v___jp_253_;
}
}
v___jp_265_:
{
if (v___y_266_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_box(0);
v_err_261_ = v___x_267_;
goto v___jp_260_;
}
else
{
uint32_t v_c_268_; uint8_t v___x_269_; 
v_c_268_ = lean_string_utf8_get_fast(v_fst_171_, v_snd_189_);
v___x_269_ = lean_uint32_dec_eq(v_c_268_, v___x_231_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; 
v___x_270_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7));
v_err_261_ = v___x_270_;
goto v___jp_260_;
}
else
{
lean_object* v___x_271_; lean_object* v___f_272_; lean_object* v___x_273_; lean_object* v_it_x27_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_271_ = lean_box(v___x_269_);
v___f_272_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_272_, 0, v___x_271_);
v___x_273_ = lean_string_utf8_next_fast(v_fst_171_, v_snd_189_);
lean_inc(v_fst_171_);
v_it_x27_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_274_, 0, v_fst_171_);
lean_ctor_set(v_it_x27_274_, 1, v___x_273_);
v___x_275_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___x_276_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8);
v___x_277_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10));
v___x_278_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_275_, v___x_276_, v___x_277_, v___f_272_, v_it_x27_274_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_pos_279_; lean_object* v_res_280_; lean_object* v_fst_281_; lean_object* v_snd_282_; 
lean_dec_ref(v___x_194_);
lean_dec(v_snd_189_);
lean_dec(v_fst_171_);
v_pos_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_pos_279_);
v_res_280_ = lean_ctor_get(v___x_278_, 1);
lean_inc(v_res_280_);
lean_dec_ref_known(v___x_278_, 2);
v_fst_281_ = lean_ctor_get(v_pos_279_, 0);
lean_inc(v_fst_281_);
v_snd_282_ = lean_ctor_get(v_pos_279_, 1);
lean_inc(v_snd_282_);
v_pos_254_ = v_pos_279_;
v_fst_255_ = v_fst_281_;
v_snd_256_ = v_snd_282_;
v_res_257_ = v_res_280_;
goto v___jp_253_;
}
else
{
lean_object* v_err_283_; 
v_err_283_ = lean_ctor_get(v___x_278_, 1);
lean_inc(v_err_283_);
lean_dec_ref_known(v___x_278_, 2);
v_err_261_ = v_err_283_;
goto v___jp_260_;
}
}
}
}
}
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_294_; 
lean_dec(v_snd_189_);
lean_dec(v_fst_171_);
v___x_285_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0));
v___x_286_ = l_Nat_reprFast(v_fst_188_);
v___x_287_ = lean_string_append(v___x_285_, v___x_286_);
lean_dec_ref(v___x_286_);
v___x_288_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1));
v___x_289_ = lean_string_append(v___x_287_, v___x_288_);
v___x_290_ = l_Nat_reprFast(v_maxHour_166_);
v___x_291_ = lean_string_append(v___x_289_, v___x_290_);
lean_dec_ref(v___x_290_);
v___x_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
if (v_isShared_192_ == 0)
{
lean_ctor_set_tag(v___x_191_, 1);
lean_ctor_set(v___x_191_, 1, v___x_292_);
lean_ctor_set(v___x_191_, 0, v___x_194_);
v___x_294_ = v___x_191_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
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
lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec(v_maxHour_166_);
v___x_301_ = lean_box(0);
v___x_302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_302_, 0, v_a_167_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
return v___x_302_;
}
v___jp_168_:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__1));
v___x_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_170_, 0, v_a_167_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__1(lean_object* v_a_303_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_nat_to_int(v_a_303_);
v___x_305_ = l_Rat_ofInt(v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(lean_object* v_a_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(v_a_306_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_pos_308_; lean_object* v_res_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_pos_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_pos_308_);
v_res_309_ = lean_ctor_get(v___x_307_, 1);
lean_inc(v_res_309_);
lean_dec_ref_known(v___x_307_, 2);
v___x_310_ = lean_unsigned_to_nat(24u);
v___x_311_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(v___x_310_, v_pos_308_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_pos_312_; lean_object* v_res_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_322_; 
v_pos_312_ = lean_ctor_get(v___x_311_, 0);
v_res_313_ = lean_ctor_get(v___x_311_, 1);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_322_ == 0)
{
v___x_315_ = v___x_311_;
v_isShared_316_ = v_isSharedCheck_322_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_res_313_);
lean_inc(v_pos_312_);
lean_dec(v___x_311_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_322_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_317_ = lean_int_neg(v_res_309_);
lean_dec(v_res_309_);
v___x_318_ = lean_int_mul(v___x_317_, v_res_313_);
lean_dec(v_res_313_);
lean_dec(v___x_317_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 1, v___x_318_);
v___x_320_ = v___x_315_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_pos_312_);
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
else
{
lean_object* v_pos_323_; lean_object* v_err_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec(v_res_309_);
v_pos_323_ = lean_ctor_get(v___x_311_, 0);
v_err_324_ = lean_ctor_get(v___x_311_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_311_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_err_324_);
lean_inc(v_pos_323_);
lean_dec(v___x_311_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_pos_323_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_err_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
else
{
lean_object* v_pos_332_; lean_object* v_err_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
v_pos_332_ = lean_ctor_get(v___x_307_, 0);
v_err_333_ = lean_ctor_get(v___x_307_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_307_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_err_333_);
lean_inc(v_pos_332_);
lean_dec(v___x_307_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_pos_332_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_err_333_);
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0(lean_object* v_acc_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_pos_347_; uint32_t v_res_348_; lean_object* v_fst_351_; lean_object* v_snd_352_; lean_object* v_pos_354_; lean_object* v_snd_355_; lean_object* v_err_356_; lean_object* v___x_360_; uint8_t v_decide_361_; 
v_fst_351_ = lean_ctor_get(v_a_345_, 0);
v_snd_352_ = lean_ctor_get(v_a_345_, 1);
lean_inc(v_snd_352_);
v___x_360_ = lean_string_utf8_byte_size(v_fst_351_);
v_decide_361_ = lean_nat_dec_eq(v_snd_352_, v___x_360_);
if (v_decide_361_ == 0)
{
uint32_t v_c_362_; lean_object* v___x_363_; lean_object* v_it_x27_364_; uint32_t v___x_381_; uint8_t v___x_382_; 
v_c_362_ = lean_string_utf8_get_fast(v_fst_351_, v_snd_352_);
v___x_363_ = lean_string_utf8_next_fast(v_fst_351_, v_snd_352_);
lean_inc(v_fst_351_);
v_it_x27_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_364_, 0, v_fst_351_);
lean_ctor_set(v_it_x27_364_, 1, v___x_363_);
v___x_381_ = 65;
v___x_382_ = lean_uint32_dec_le(v___x_381_, v_c_362_);
if (v___x_382_ == 0)
{
goto v___jp_376_;
}
else
{
uint32_t v___x_383_; uint8_t v___x_384_; 
v___x_383_ = 90;
v___x_384_ = lean_uint32_dec_le(v_c_362_, v___x_383_);
if (v___x_384_ == 0)
{
goto v___jp_376_;
}
else
{
lean_dec(v_snd_352_);
lean_dec_ref(v_a_345_);
v_pos_347_ = v_it_x27_364_;
v_res_348_ = v_c_362_;
goto v___jp_346_;
}
}
v___jp_365_:
{
uint32_t v___x_366_; uint8_t v___x_367_; 
v___x_366_ = 43;
v___x_367_ = lean_uint32_dec_eq(v_c_362_, v___x_366_);
if (v___x_367_ == 0)
{
uint32_t v___x_368_; uint8_t v___x_369_; 
v___x_368_ = 45;
v___x_369_ = lean_uint32_dec_eq(v_c_362_, v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
lean_dec_ref_known(v_it_x27_364_, 2);
v___x_370_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__1));
lean_inc(v_snd_352_);
v_pos_354_ = v_a_345_;
v_snd_355_ = v_snd_352_;
v_err_356_ = v___x_370_;
goto v___jp_353_;
}
else
{
lean_dec(v_snd_352_);
lean_dec_ref(v_a_345_);
v_pos_347_ = v_it_x27_364_;
v_res_348_ = v_c_362_;
goto v___jp_346_;
}
}
else
{
lean_dec(v_snd_352_);
lean_dec_ref(v_a_345_);
v_pos_347_ = v_it_x27_364_;
v_res_348_ = v_c_362_;
goto v___jp_346_;
}
}
v___jp_371_:
{
uint32_t v___x_372_; uint8_t v___x_373_; 
v___x_372_ = 48;
v___x_373_ = lean_uint32_dec_le(v___x_372_, v_c_362_);
if (v___x_373_ == 0)
{
goto v___jp_365_;
}
else
{
uint32_t v___x_374_; uint8_t v___x_375_; 
v___x_374_ = 57;
v___x_375_ = lean_uint32_dec_le(v_c_362_, v___x_374_);
if (v___x_375_ == 0)
{
goto v___jp_365_;
}
else
{
lean_dec(v_snd_352_);
lean_dec_ref(v_a_345_);
v_pos_347_ = v_it_x27_364_;
v_res_348_ = v_c_362_;
goto v___jp_346_;
}
}
}
v___jp_376_:
{
uint32_t v___x_377_; uint8_t v___x_378_; 
v___x_377_ = 97;
v___x_378_ = lean_uint32_dec_le(v___x_377_, v_c_362_);
if (v___x_378_ == 0)
{
goto v___jp_371_;
}
else
{
uint32_t v___x_379_; uint8_t v___x_380_; 
v___x_379_ = 122;
v___x_380_ = lean_uint32_dec_le(v_c_362_, v___x_379_);
if (v___x_380_ == 0)
{
goto v___jp_371_;
}
else
{
lean_dec(v_snd_352_);
lean_dec_ref(v_a_345_);
v_pos_347_ = v_it_x27_364_;
v_res_348_ = v_c_362_;
goto v___jp_346_;
}
}
}
}
else
{
lean_object* v___x_385_; 
v___x_385_ = lean_box(0);
lean_inc(v_snd_352_);
v_pos_354_ = v_a_345_;
v_snd_355_ = v_snd_352_;
v_err_356_ = v___x_385_;
goto v___jp_353_;
}
v___jp_346_:
{
lean_object* v___x_349_; 
v___x_349_ = lean_string_push(v_acc_344_, v_res_348_);
v_acc_344_ = v___x_349_;
v_a_345_ = v_pos_347_;
goto _start;
}
v___jp_353_:
{
uint8_t v_decide_357_; 
v_decide_357_ = lean_nat_dec_eq(v_snd_352_, v_snd_355_);
lean_dec(v_snd_355_);
lean_dec(v_snd_352_);
if (v_decide_357_ == 0)
{
lean_object* v___x_358_; 
lean_dec_ref(v_acc_344_);
lean_inc(v_err_356_);
v___x_358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_358_, 0, v_pos_354_);
lean_ctor_set(v___x_358_, 1, v_err_356_);
return v___x_358_;
}
else
{
lean_object* v___x_359_; 
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v_pos_354_);
lean_ctor_set(v___x_359_, 1, v_acc_344_);
return v___x_359_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName(lean_object* v_a_387_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName___closed__0));
v___x_389_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0(v___x_388_, v_a_387_);
return v___x_389_;
}
}
uint8_t l_instBEqOption_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
if (lean_obj_tag(v_x_391_) == 0)
{
uint8_t v___x_392_; 
v___x_392_ = 1;
return v___x_392_;
}
else
{
uint8_t v___x_393_; 
v___x_393_ = 0;
return v___x_393_;
}
}
else
{
if (lean_obj_tag(v_x_391_) == 0)
{
uint8_t v___x_394_; 
v___x_394_ = 0;
return v___x_394_;
}
else
{
lean_object* v_val_395_; lean_object* v_val_396_; uint32_t v___x_397_; uint32_t v___x_398_; uint8_t v___x_399_; 
v_val_395_ = lean_ctor_get(v_x_390_, 0);
v_val_396_ = lean_ctor_get(v_x_391_, 0);
v___x_397_ = lean_unbox_uint32(v_val_395_);
v___x_398_ = lean_unbox_uint32(v_val_396_);
v___x_399_ = lean_uint32_dec_eq(v___x_397_, v___x_398_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_390_ = stack[0].m_obj;
lean_object* v_x_391_ = stack[1].m_obj;
uint8_t v_res_400_;
v_res_400_ = l_instBEqOption_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_x_390_, v_x_391_);
stack->m_num = v_res_400_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0___boxed(lean_object* v_x_401_, lean_object* v_x_402_){
_start:
{
uint8_t v_res_403_; lean_object* v_r_404_; 
v_res_403_ = l_instBEqOption_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_x_401_, v_x_402_);
lean_dec(v_x_402_);
lean_dec(v_x_401_);
v_r_404_ = lean_box(v_res_403_);
return v_r_404_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1(lean_object* v_acc_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_pos_411_; uint32_t v_res_412_; lean_object* v_fst_415_; lean_object* v_snd_416_; lean_object* v_pos_418_; lean_object* v_snd_419_; lean_object* v_err_420_; lean_object* v___x_426_; uint8_t v_decide_427_; 
v_fst_415_ = lean_ctor_get(v_a_409_, 0);
v_snd_416_ = lean_ctor_get(v_a_409_, 1);
lean_inc(v_snd_416_);
v___x_426_ = lean_string_utf8_byte_size(v_fst_415_);
v_decide_427_ = lean_nat_dec_eq(v_snd_416_, v___x_426_);
if (v_decide_427_ == 0)
{
uint32_t v_c_428_; lean_object* v___x_429_; lean_object* v_it_x27_430_; uint32_t v___x_436_; uint8_t v___x_437_; 
v_c_428_ = lean_string_utf8_get_fast(v_fst_415_, v_snd_416_);
v___x_429_ = lean_string_utf8_next_fast(v_fst_415_, v_snd_416_);
lean_inc(v_fst_415_);
v_it_x27_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_430_, 0, v_fst_415_);
lean_ctor_set(v_it_x27_430_, 1, v___x_429_);
v___x_436_ = 65;
v___x_437_ = lean_uint32_dec_le(v___x_436_, v_c_428_);
if (v___x_437_ == 0)
{
goto v___jp_431_;
}
else
{
uint32_t v___x_438_; uint8_t v___x_439_; 
v___x_438_ = 90;
v___x_439_ = lean_uint32_dec_le(v_c_428_, v___x_438_);
if (v___x_439_ == 0)
{
goto v___jp_431_;
}
else
{
lean_dec(v_snd_416_);
lean_dec_ref(v_a_409_);
v_pos_411_ = v_it_x27_430_;
v_res_412_ = v_c_428_;
goto v___jp_410_;
}
}
v___jp_431_:
{
uint32_t v___x_432_; uint8_t v___x_433_; 
v___x_432_ = 97;
v___x_433_ = lean_uint32_dec_le(v___x_432_, v_c_428_);
if (v___x_433_ == 0)
{
lean_dec_ref_known(v_it_x27_430_, 2);
goto v___jp_424_;
}
else
{
uint32_t v___x_434_; uint8_t v___x_435_; 
v___x_434_ = 122;
v___x_435_ = lean_uint32_dec_le(v_c_428_, v___x_434_);
if (v___x_435_ == 0)
{
lean_dec_ref_known(v_it_x27_430_, 2);
goto v___jp_424_;
}
else
{
lean_dec(v_snd_416_);
lean_dec_ref(v_a_409_);
v_pos_411_ = v_it_x27_430_;
v_res_412_ = v_c_428_;
goto v___jp_410_;
}
}
}
}
else
{
lean_object* v___x_440_; 
v___x_440_ = lean_box(0);
lean_inc(v_snd_416_);
v_pos_418_ = v_a_409_;
v_snd_419_ = v_snd_416_;
v_err_420_ = v___x_440_;
goto v___jp_417_;
}
v___jp_410_:
{
lean_object* v___x_413_; 
v___x_413_ = lean_string_push(v_acc_408_, v_res_412_);
v_acc_408_ = v___x_413_;
v_a_409_ = v_pos_411_;
goto _start;
}
v___jp_417_:
{
uint8_t v_decide_421_; 
v_decide_421_ = lean_nat_dec_eq(v_snd_416_, v_snd_419_);
lean_dec(v_snd_419_);
lean_dec(v_snd_416_);
if (v_decide_421_ == 0)
{
lean_object* v___x_422_; 
lean_dec_ref(v_acc_408_);
lean_inc(v_err_420_);
v___x_422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_422_, 0, v_pos_418_);
lean_ctor_set(v___x_422_, 1, v_err_420_);
return v___x_422_;
}
else
{
lean_object* v___x_423_; 
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v_pos_418_);
lean_ctor_set(v___x_423_, 1, v_acc_408_);
return v___x_423_;
}
}
v___jp_424_:
{
lean_object* v___x_425_; 
v___x_425_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__1));
lean_inc(v_snd_416_);
v_pos_418_ = v_a_409_;
v_snd_419_ = v_snd_416_;
v_err_420_ = v___x_425_;
goto v___jp_417_;
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_441_; lean_object* v___x_442_; 
v___x_441_ = 60;
v___x_442_ = lean_box_uint32(v___x_441_);
return v___x_442_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0___boxed__const__1;
v___x_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(lean_object* v_a_448_){
_start:
{
lean_object* v___y_450_; lean_object* v_pos_454_; lean_object* v_res_455_; lean_object* v_fst_509_; lean_object* v_snd_510_; lean_object* v___x_511_; uint8_t v_decide_512_; 
v_fst_509_ = lean_ctor_get(v_a_448_, 0);
v_snd_510_ = lean_ctor_get(v_a_448_, 1);
v___x_511_ = lean_string_utf8_byte_size(v_fst_509_);
v_decide_512_ = lean_nat_dec_eq(v_snd_510_, v___x_511_);
if (v_decide_512_ == 0)
{
uint32_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_513_ = lean_string_utf8_get_fast(v_fst_509_, v_snd_510_);
v___x_514_ = lean_box_uint32(v___x_513_);
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
v_pos_454_ = v_a_448_;
v_res_455_ = v___x_515_;
goto v___jp_453_;
}
else
{
lean_object* v___x_516_; 
v___x_516_ = lean_box(0);
v_pos_454_ = v_a_448_;
v_res_455_ = v___x_516_;
goto v___jp_453_;
}
v___jp_449_:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_box(0);
v___x_452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_452_, 0, v___y_450_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
return v___x_452_;
}
v___jp_453_:
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0);
v___x_457_ = l_instBEqOption_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_res_455_, v___x_456_);
lean_dec(v_res_455_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName___closed__0));
v___x_459_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1(v___x_458_, v_pos_454_);
return v___x_459_;
}
else
{
lean_object* v_fst_460_; lean_object* v_snd_461_; lean_object* v___x_462_; uint8_t v_decide_463_; 
v_fst_460_ = lean_ctor_get(v_pos_454_, 0);
v_snd_461_ = lean_ctor_get(v_pos_454_, 1);
v___x_462_ = lean_string_utf8_byte_size(v_fst_460_);
v_decide_463_ = lean_nat_dec_eq(v_snd_461_, v___x_462_);
if (v_decide_463_ == 0)
{
if (v___x_457_ == 0)
{
v___y_450_ = v_pos_454_;
goto v___jp_449_;
}
else
{
lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_506_; 
lean_inc(v_snd_461_);
lean_inc(v_fst_460_);
v_isSharedCheck_506_ = !lean_is_exclusive(v_pos_454_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; lean_object* v_unused_508_; 
v_unused_507_ = lean_ctor_get(v_pos_454_, 1);
lean_dec(v_unused_507_);
v_unused_508_ = lean_ctor_get(v_pos_454_, 0);
lean_dec(v_unused_508_);
v___x_465_ = v_pos_454_;
v_isShared_466_ = v_isSharedCheck_506_;
goto v_resetjp_464_;
}
else
{
lean_dec(v_pos_454_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_506_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_467_ = lean_string_utf8_next_fast(v_fst_460_, v_snd_461_);
lean_dec(v_snd_461_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 1, v___x_467_);
v___x_469_ = v___x_465_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_fst_460_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v___x_467_);
v___x_469_ = v_reuseFailAlloc_505_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; 
v___x_470_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName(v___x_469_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_pos_471_; lean_object* v_res_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_504_; 
v_pos_471_ = lean_ctor_get(v___x_470_, 0);
v_res_472_ = lean_ctor_get(v___x_470_, 1);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_504_ == 0)
{
v___x_474_ = v___x_470_;
v_isShared_475_ = v_isSharedCheck_504_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_res_472_);
lean_inc(v_pos_471_);
lean_dec(v___x_470_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_504_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v_fst_476_; lean_object* v_snd_477_; lean_object* v___x_478_; uint8_t v_decide_479_; 
v_fst_476_ = lean_ctor_get(v_pos_471_, 0);
v_snd_477_ = lean_ctor_get(v_pos_471_, 1);
v___x_478_ = lean_string_utf8_byte_size(v_fst_476_);
v_decide_479_ = lean_nat_dec_eq(v_snd_477_, v___x_478_);
if (v_decide_479_ == 0)
{
uint32_t v___x_480_; uint32_t v_c_481_; uint8_t v___x_482_; 
v___x_480_ = 62;
v_c_481_ = lean_string_utf8_get_fast(v_fst_476_, v_snd_477_);
v___x_482_ = lean_uint32_dec_eq(v_c_481_, v___x_480_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_dec(v_res_472_);
v___x_483_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2));
if (v_isShared_475_ == 0)
{
lean_ctor_set_tag(v___x_474_, 1);
lean_ctor_set(v___x_474_, 1, v___x_483_);
v___x_485_ = v___x_474_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_pos_471_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
else
{
lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_497_; 
lean_inc(v_snd_477_);
lean_inc(v_fst_476_);
v_isSharedCheck_497_ = !lean_is_exclusive(v_pos_471_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; lean_object* v_unused_499_; 
v_unused_498_ = lean_ctor_get(v_pos_471_, 1);
lean_dec(v_unused_498_);
v_unused_499_ = lean_ctor_get(v_pos_471_, 0);
lean_dec(v_unused_499_);
v___x_488_ = v_pos_471_;
v_isShared_489_ = v_isSharedCheck_497_;
goto v_resetjp_487_;
}
else
{
lean_dec(v_pos_471_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_497_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; lean_object* v_it_x27_492_; 
v___x_490_ = lean_string_utf8_next_fast(v_fst_476_, v_snd_477_);
lean_dec(v_snd_477_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v___x_490_);
v_it_x27_492_ = v___x_488_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_fst_476_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v___x_490_);
v_it_x27_492_ = v_reuseFailAlloc_496_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_494_; 
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v_it_x27_492_);
v___x_494_ = v___x_474_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_it_x27_492_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_res_472_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
else
{
lean_object* v___x_500_; lean_object* v___x_502_; 
lean_dec(v_res_472_);
v___x_500_ = lean_box(0);
if (v_isShared_475_ == 0)
{
lean_ctor_set_tag(v___x_474_, 1);
lean_ctor_set(v___x_474_, 1, v___x_500_);
v___x_502_ = v___x_474_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_pos_471_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
else
{
return v___x_470_;
}
}
}
}
}
else
{
v___y_450_ = v_pos_454_;
goto v___jp_449_;
}
}
}
}
}
uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1(lean_object* v___x_517_, lean_object* v_x_518_){
_start:
{
uint8_t v___x_519_; 
v___x_519_ = lean_int_dec_le(v_x_518_, v___x_517_);
return v___x_519_;
}
}
LEAN_EXPORT void l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_517_ = stack[0].m_obj;
lean_object* v_x_518_ = stack[1].m_obj;
uint8_t v_res_520_;
v_res_520_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1(v___x_517_, v_x_518_);
stack->m_num = v_res_520_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1___boxed(lean_object* v___x_521_, lean_object* v_x_522_){
_start:
{
uint8_t v_res_523_; lean_object* v_r_524_; 
v_res_523_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1(v___x_521_, v_x_522_);
lean_dec(v_x_522_);
lean_dec(v___x_521_);
v_r_524_ = lean_box(v_res_523_);
return v_r_524_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_unsigned_to_nat(7u);
v___x_531_ = lean_nat_to_int(v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_unsigned_to_nat(5u);
v___x_533_ = lean_nat_to_int(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6(void){
_start:
{
lean_object* v___x_534_; lean_object* v___f_535_; 
v___x_534_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5);
v___f_535_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1___boxed), 2, 1);
lean_closure_set(v___f_535_, 0, v___x_534_);
return v___f_535_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_unsigned_to_nat(12u);
v___x_541_ = lean_nat_to_int(v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec(lean_object* v_a_543_){
_start:
{
lean_object* v___y_545_; lean_object* v___y_549_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_563_; lean_object* v_fst_566_; lean_object* v_snd_567_; lean_object* v___x_568_; uint8_t v_decide_569_; 
v_fst_566_ = lean_ctor_get(v_a_543_, 0);
v_snd_567_ = lean_ctor_get(v_a_543_, 1);
v___x_568_ = lean_string_utf8_byte_size(v_fst_566_);
v_decide_569_ = lean_nat_dec_eq(v_snd_567_, v___x_568_);
if (v_decide_569_ == 0)
{
uint32_t v___x_570_; uint32_t v_c_571_; uint8_t v___x_572_; 
v___x_570_ = 77;
v_c_571_ = lean_string_utf8_get_fast(v_fst_566_, v_snd_567_);
v___x_572_ = lean_uint32_dec_eq(v_c_571_, v___x_570_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3));
v___x_574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_574_, 0, v_a_543_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
return v___x_574_;
}
else
{
lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_727_; 
lean_inc(v_snd_567_);
lean_inc(v_fst_566_);
v_isSharedCheck_727_ = !lean_is_exclusive(v_a_543_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; lean_object* v_unused_729_; 
v_unused_728_ = lean_ctor_get(v_a_543_, 1);
lean_dec(v_unused_728_);
v_unused_729_ = lean_ctor_get(v_a_543_, 0);
lean_dec(v_unused_729_);
v___x_576_ = v_a_543_;
v_isShared_577_ = v_isSharedCheck_727_;
goto v_resetjp_575_;
}
else
{
lean_dec(v_a_543_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_727_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v___f_579_; lean_object* v___x_580_; lean_object* v_it_x27_582_; 
v___x_578_ = lean_box(v___x_572_);
v___f_579_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_579_, 0, v___x_578_);
v___x_580_ = lean_string_utf8_next_fast(v_fst_566_, v_snd_567_);
lean_dec(v_snd_567_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 1, v___x_580_);
v_it_x27_582_ = v___x_576_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_fst_566_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_580_);
v_it_x27_582_ = v_reuseFailAlloc_726_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_583_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_596_; lean_object* v_pos_597_; lean_object* v_fst_598_; lean_object* v_snd_599_; lean_object* v_res_600_; lean_object* v_pos_636_; lean_object* v_res_637_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_583_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_682_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10);
v___x_683_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11));
v___x_684_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_583_, v___x_682_, v___x_683_, v___f_579_, v_it_x27_582_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_pos_685_; lean_object* v_res_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_714_; 
v_pos_685_ = lean_ctor_get(v___x_684_, 0);
v_res_686_ = lean_ctor_get(v___x_684_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_714_ == 0)
{
v___x_688_ = v___x_684_;
v_isShared_689_ = v_isSharedCheck_714_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_res_686_);
lean_inc(v_pos_685_);
lean_dec(v___x_684_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_714_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_fst_695_; lean_object* v_snd_696_; lean_object* v___x_697_; uint8_t v_decide_698_; 
v_fst_695_ = lean_ctor_get(v_pos_685_, 0);
v_snd_696_ = lean_ctor_get(v_pos_685_, 1);
v___x_697_ = lean_string_utf8_byte_size(v_fst_695_);
v_decide_698_ = lean_nat_dec_eq(v_snd_696_, v___x_697_);
if (v_decide_698_ == 0)
{
if (v___x_572_ == 0)
{
lean_dec(v_res_686_);
goto v___jp_690_;
}
else
{
uint32_t v___x_699_; uint32_t v_c_700_; uint8_t v___x_701_; 
lean_del_object(v___x_688_);
v___x_699_ = 46;
v_c_700_ = lean_string_utf8_get_fast(v_fst_695_, v_snd_696_);
v___x_701_ = lean_uint32_dec_eq(v_c_700_, v___x_699_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec(v_res_686_);
v___x_702_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9));
v___x_703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_703_, 0, v_pos_685_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
return v___x_703_;
}
else
{
lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_711_; 
lean_inc(v_snd_696_);
lean_inc(v_fst_695_);
v_isSharedCheck_711_ = !lean_is_exclusive(v_pos_685_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; lean_object* v_unused_713_; 
v_unused_712_ = lean_ctor_get(v_pos_685_, 1);
lean_dec(v_unused_712_);
v_unused_713_ = lean_ctor_get(v_pos_685_, 0);
lean_dec(v_unused_713_);
v___x_705_ = v_pos_685_;
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
else
{
lean_dec(v_pos_685_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v_it_x27_709_; 
v___x_707_ = lean_string_utf8_next_fast(v_fst_695_, v_snd_696_);
lean_dec(v_snd_696_);
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
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_fst_695_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_707_);
v_it_x27_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
v_pos_636_ = v_it_x27_709_;
v_res_637_ = v_res_686_;
goto v___jp_635_;
}
}
}
}
}
else
{
lean_dec(v_res_686_);
goto v___jp_690_;
}
v___jp_690_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = lean_box(0);
if (v_isShared_689_ == 0)
{
lean_ctor_set_tag(v___x_688_, 1);
lean_ctor_set(v___x_688_, 1, v___x_691_);
v___x_693_ = v___x_688_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_pos_685_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_pos_715_; lean_object* v_res_716_; 
v_pos_715_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_pos_715_);
v_res_716_ = lean_ctor_get(v___x_684_, 1);
lean_inc(v_res_716_);
lean_dec_ref_known(v___x_684_, 2);
v_pos_636_ = v_pos_715_;
v_res_637_ = v_res_716_;
goto v___jp_635_;
}
else
{
lean_object* v_pos_717_; lean_object* v_err_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
v_pos_717_ = lean_ctor_get(v___x_684_, 0);
v_err_718_ = lean_ctor_get(v___x_684_, 1);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_684_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_err_718_);
lean_inc(v_pos_717_);
lean_dec(v___x_684_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_pos_717_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_err_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
v___jp_584_:
{
uint8_t v___x_591_; 
v___x_591_ = lean_int_dec_le(v___x_583_, v___y_590_);
if (v___x_591_ == 0)
{
lean_dec(v___y_590_);
lean_dec(v___y_589_);
lean_dec(v___y_587_);
lean_dec(v___y_585_);
v___y_553_ = v___y_586_;
v___y_554_ = v___y_588_;
goto v___jp_552_;
}
else
{
uint8_t v___x_592_; 
v___x_592_ = lean_int_dec_le(v___y_590_, v___y_587_);
lean_dec(v___y_587_);
if (v___x_592_ == 0)
{
lean_dec(v___y_590_);
lean_dec(v___y_589_);
lean_dec(v___y_585_);
v___y_553_ = v___y_586_;
v___y_554_ = v___y_588_;
goto v___jp_552_;
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec(v___y_588_);
v___x_593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_593_, 0, v___y_589_);
lean_ctor_set(v___x_593_, 1, v___y_585_);
lean_ctor_set(v___x_593_, 2, v___y_590_);
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v___y_586_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
return v___x_594_;
}
}
}
v___jp_595_:
{
lean_object* v___x_601_; uint8_t v_decide_602_; 
v___x_601_ = lean_string_utf8_byte_size(v_fst_598_);
v_decide_602_ = lean_nat_dec_eq(v_snd_599_, v___x_601_);
if (v_decide_602_ == 0)
{
if (v___x_572_ == 0)
{
lean_dec(v_res_600_);
lean_dec(v_snd_599_);
lean_dec(v_fst_598_);
lean_dec(v___y_596_);
v___y_549_ = v_pos_597_;
goto v___jp_548_;
}
else
{
uint32_t v_c_603_; uint32_t v___x_604_; uint8_t v___x_605_; 
v_c_603_ = lean_string_utf8_get_fast(v_fst_598_, v_snd_599_);
v___x_604_ = 48;
v___x_605_ = lean_uint32_dec_le(v___x_604_, v_c_603_);
if (v___x_605_ == 0)
{
lean_dec(v_res_600_);
lean_dec(v_snd_599_);
lean_dec(v_fst_598_);
lean_dec(v___y_596_);
v___y_545_ = v_pos_597_;
goto v___jp_544_;
}
else
{
uint32_t v___x_606_; uint8_t v___x_607_; 
v___x_606_ = 57;
v___x_607_ = lean_uint32_dec_le(v_c_603_, v___x_606_);
if (v___x_607_ == 0)
{
lean_dec(v_res_600_);
lean_dec(v_snd_599_);
lean_dec(v_fst_598_);
lean_dec(v___y_596_);
v___y_545_ = v_pos_597_;
goto v___jp_544_;
}
else
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v_fst_613_; lean_object* v_snd_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_634_; 
lean_dec_ref(v_pos_597_);
v___x_608_ = lean_string_utf8_next_fast(v_fst_598_, v_snd_599_);
lean_dec(v_snd_599_);
v___x_609_ = lean_uint32_to_nat(v_c_603_);
v___x_610_ = lean_unsigned_to_nat(48u);
v___x_611_ = lean_nat_sub(v___x_609_, v___x_610_);
lean_dec(v___x_609_);
v___x_612_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_598_, v___x_608_, v___x_611_);
v_fst_613_ = lean_ctor_get(v___x_612_, 0);
v_snd_614_ = lean_ctor_get(v___x_612_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_634_ == 0)
{
v___x_616_ = v___x_612_;
v_isShared_617_ = v_isSharedCheck_634_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_snd_614_);
lean_inc(v_fst_613_);
lean_dec(v___x_612_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_634_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v_fst_598_);
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_fst_598_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_snd_614_);
v___x_619_ = v_reuseFailAlloc_633_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = lean_unsigned_to_nat(6u);
v___x_621_ = lean_nat_dec_lt(v___x_620_, v_fst_613_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_622_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4);
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = lean_nat_dec_eq(v_fst_613_, v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; 
lean_inc(v_fst_613_);
v___x_625_ = lean_nat_to_int(v_fst_613_);
v___y_585_ = v_res_600_;
v___y_586_ = v___x_619_;
v___y_587_ = v___x_622_;
v___y_588_ = v_fst_613_;
v___y_589_ = v___y_596_;
v___y_590_ = v___x_625_;
goto v___jp_584_;
}
else
{
v___y_585_ = v_res_600_;
v___y_586_ = v___x_619_;
v___y_587_ = v___x_622_;
v___y_588_ = v_fst_613_;
v___y_589_ = v___y_596_;
v___y_590_ = v___x_622_;
goto v___jp_584_;
}
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec(v_res_600_);
lean_dec(v___y_596_);
v___x_626_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0));
v___x_627_ = l_Nat_reprFast(v_fst_613_);
v___x_628_ = lean_string_append(v___x_626_, v___x_627_);
lean_dec_ref(v___x_627_);
v___x_629_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1));
v___x_630_ = lean_string_append(v___x_628_, v___x_629_);
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
v___x_632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_619_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
return v___x_632_;
}
}
}
}
}
}
}
else
{
lean_dec(v_res_600_);
lean_dec(v_snd_599_);
lean_dec(v_fst_598_);
lean_dec(v___y_596_);
v___y_549_ = v_pos_597_;
goto v___jp_548_;
}
}
v___jp_635_:
{
lean_object* v___x_638_; lean_object* v___f_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_638_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5);
v___f_639_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6);
v___x_640_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7));
v___x_641_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_583_, v___x_638_, v___x_640_, v___f_639_, v_pos_636_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_pos_642_; lean_object* v_res_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_668_; 
v_pos_642_ = lean_ctor_get(v___x_641_, 0);
v_res_643_ = lean_ctor_get(v___x_641_, 1);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_668_ == 0)
{
v___x_645_ = v___x_641_;
v_isShared_646_ = v_isSharedCheck_668_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_res_643_);
lean_inc(v_pos_642_);
lean_dec(v___x_641_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_668_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v_fst_647_; lean_object* v_snd_648_; lean_object* v___x_649_; uint8_t v_decide_650_; 
v_fst_647_ = lean_ctor_get(v_pos_642_, 0);
v_snd_648_ = lean_ctor_get(v_pos_642_, 1);
v___x_649_ = lean_string_utf8_byte_size(v_fst_647_);
v_decide_650_ = lean_nat_dec_eq(v_snd_648_, v___x_649_);
if (v_decide_650_ == 0)
{
if (v___x_572_ == 0)
{
lean_del_object(v___x_645_);
lean_dec(v_res_643_);
lean_dec(v_res_637_);
v___y_563_ = v_pos_642_;
goto v___jp_562_;
}
else
{
uint32_t v___x_651_; uint32_t v_c_652_; uint8_t v___x_653_; 
v___x_651_ = 46;
v_c_652_ = lean_string_utf8_get_fast(v_fst_647_, v_snd_648_);
v___x_653_ = lean_uint32_dec_eq(v_c_652_, v___x_651_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_656_; 
lean_dec(v_res_643_);
lean_dec(v_res_637_);
v___x_654_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9));
if (v_isShared_646_ == 0)
{
lean_ctor_set_tag(v___x_645_, 1);
lean_ctor_set(v___x_645_, 1, v___x_654_);
v___x_656_ = v___x_645_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_pos_642_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
else
{
lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_665_; 
lean_inc(v_snd_648_);
lean_inc(v_fst_647_);
lean_del_object(v___x_645_);
v_isSharedCheck_665_ = !lean_is_exclusive(v_pos_642_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; lean_object* v_unused_667_; 
v_unused_666_ = lean_ctor_get(v_pos_642_, 1);
lean_dec(v_unused_666_);
v_unused_667_ = lean_ctor_get(v_pos_642_, 0);
lean_dec(v_unused_667_);
v___x_659_ = v_pos_642_;
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
else
{
lean_dec(v_pos_642_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v_it_x27_663_; 
v___x_661_ = lean_string_utf8_next_fast(v_fst_647_, v_snd_648_);
lean_dec(v_snd_648_);
lean_inc(v_fst_647_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_661_);
v_it_x27_663_ = v___x_659_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_fst_647_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_661_);
v_it_x27_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
v___y_596_ = v_res_637_;
v_pos_597_ = v_it_x27_663_;
v_fst_598_ = v_fst_647_;
v_snd_599_ = v___x_661_;
v_res_600_ = v_res_643_;
goto v___jp_595_;
}
}
}
}
}
else
{
lean_del_object(v___x_645_);
lean_dec(v_res_643_);
lean_dec(v_res_637_);
v___y_563_ = v_pos_642_;
goto v___jp_562_;
}
}
}
else
{
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_pos_669_; lean_object* v_res_670_; lean_object* v_fst_671_; lean_object* v_snd_672_; 
v_pos_669_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_pos_669_);
v_res_670_ = lean_ctor_get(v___x_641_, 1);
lean_inc(v_res_670_);
lean_dec_ref_known(v___x_641_, 2);
v_fst_671_ = lean_ctor_get(v_pos_669_, 0);
lean_inc(v_fst_671_);
v_snd_672_ = lean_ctor_get(v_pos_669_, 1);
lean_inc(v_snd_672_);
v___y_596_ = v_res_637_;
v_pos_597_ = v_pos_669_;
v_fst_598_ = v_fst_671_;
v_snd_599_ = v_snd_672_;
v_res_600_ = v_res_670_;
goto v___jp_595_;
}
else
{
lean_object* v_pos_673_; lean_object* v_err_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec(v_res_637_);
v_pos_673_ = lean_ctor_get(v___x_641_, 0);
v_err_674_ = lean_ctor_get(v___x_641_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_641_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_err_674_);
lean_inc(v_pos_673_);
lean_dec(v___x_641_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_pos_673_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_err_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
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
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_box(0);
v___x_731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_731_, 0, v_a_543_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
return v___x_731_;
}
v___jp_544_:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__1));
v___x_547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_547_, 0, v___y_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
return v___x_547_;
}
v___jp_548_:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_box(0);
v___x_551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_551_, 0, v___y_549_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
return v___x_551_;
}
v___jp_552_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_555_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0));
v___x_556_ = l_Nat_reprFast(v___y_554_);
v___x_557_ = lean_string_append(v___x_555_, v___x_556_);
lean_dec_ref(v___x_556_);
v___x_558_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1));
v___x_559_ = lean_string_append(v___x_557_, v___x_558_);
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
v___x_561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_561_, 0, v___y_553_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
return v___x_561_;
}
v___jp_562_:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_box(0);
v___x_565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_565_, 0, v___y_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
return v___x_565_;
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_unsigned_to_nat(365u);
v___x_736_ = lean_nat_to_int(v___x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec(lean_object* v_a_738_){
_start:
{
lean_object* v_fst_739_; lean_object* v_snd_740_; lean_object* v___x_741_; uint8_t v_decide_742_; 
v_fst_739_ = lean_ctor_get(v_a_738_, 0);
v_snd_740_ = lean_ctor_get(v_a_738_, 1);
v___x_741_ = lean_string_utf8_byte_size(v_fst_739_);
v_decide_742_ = lean_nat_dec_eq(v_snd_740_, v___x_741_);
if (v_decide_742_ == 0)
{
uint32_t v___x_743_; uint32_t v_c_744_; uint8_t v___x_745_; 
v___x_743_ = 74;
v_c_744_ = lean_string_utf8_get_fast(v_fst_739_, v_snd_740_);
v___x_745_ = lean_uint32_dec_eq(v_c_744_, v___x_743_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1));
v___x_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_747_, 0, v_a_738_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
return v___x_747_;
}
else
{
lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_780_; 
lean_inc(v_snd_740_);
lean_inc(v_fst_739_);
v_isSharedCheck_780_ = !lean_is_exclusive(v_a_738_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; lean_object* v_unused_782_; 
v_unused_781_ = lean_ctor_get(v_a_738_, 1);
lean_dec(v_unused_781_);
v_unused_782_ = lean_ctor_get(v_a_738_, 0);
lean_dec(v_unused_782_);
v___x_749_ = v_a_738_;
v_isShared_750_ = v_isSharedCheck_780_;
goto v_resetjp_748_;
}
else
{
lean_dec(v_a_738_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_780_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___f_752_; lean_object* v___x_753_; lean_object* v_it_x27_755_; 
v___x_751_ = lean_box(v___x_745_);
v___f_752_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_752_, 0, v___x_751_);
v___x_753_ = lean_string_utf8_next_fast(v_fst_739_, v_snd_740_);
lean_dec(v_snd_740_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_753_);
v_it_x27_755_ = v___x_749_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_fst_739_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_753_);
v_it_x27_755_ = v_reuseFailAlloc_779_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_756_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_757_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2);
v___x_758_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3));
v___x_759_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_756_, v___x_757_, v___x_758_, v___f_752_, v_it_x27_755_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_pos_760_; lean_object* v_res_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_769_; 
v_pos_760_ = lean_ctor_get(v___x_759_, 0);
v_res_761_ = lean_ctor_get(v___x_759_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_769_ == 0)
{
v___x_763_ = v___x_759_;
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_res_761_);
lean_inc(v_pos_760_);
lean_dec(v___x_759_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_765_, 0, v_res_761_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 1, v___x_765_);
v___x_767_ = v___x_763_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_pos_760_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
else
{
lean_object* v_pos_770_; lean_object* v_err_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
v_pos_770_ = lean_ctor_get(v___x_759_, 0);
v_err_771_ = lean_ctor_get(v___x_759_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_759_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_err_771_);
lean_inc(v_pos_770_);
lean_dec(v___x_759_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_pos_770_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_err_771_);
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
}
}
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_box(0);
v___x_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_784_, 0, v_a_738_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
return v___x_784_;
}
}
}
uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0(lean_object* v_x_785_){
_start:
{
uint8_t v___x_786_; 
v___x_786_ = 1;
return v___x_786_;
}
}
LEAN_EXPORT void l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_785_ = stack[0].m_obj;
uint8_t v_res_787_;
v_res_787_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0(v_x_785_);
stack->m_num = v_res_787_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0___boxed(lean_object* v_x_788_){
_start:
{
uint8_t v_res_789_; lean_object* v_r_790_; 
v_res_789_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0(v_x_788_);
lean_dec(v_x_788_);
v_r_790_ = lean_box(v_res_789_);
return v_r_790_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec(lean_object* v_a_793_){
_start:
{
lean_object* v___f_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___f_794_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__0));
v___x_795_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___x_796_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2);
v___x_797_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__1));
v___x_798_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_795_, v___x_796_, v___x_797_, v___f_794_, v_a_793_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_pos_799_; lean_object* v_res_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_808_; 
v_pos_799_ = lean_ctor_get(v___x_798_, 0);
v_res_800_ = lean_ctor_get(v___x_798_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_808_ == 0)
{
v___x_802_ = v___x_798_;
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_res_800_);
lean_inc(v_pos_799_);
lean_dec(v___x_798_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_804_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_804_, 0, v_res_800_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 1, v___x_804_);
v___x_806_ = v___x_802_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_pos_799_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
else
{
lean_object* v_pos_809_; lean_object* v_err_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
v_pos_809_ = lean_ctor_get(v___x_798_, 0);
v_err_810_ = lean_ctor_get(v___x_798_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_798_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_err_810_);
lean_inc(v_pos_809_);
lean_dec(v___x_798_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_pos_809_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_err_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(lean_object* v_stdOffset_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_fst_820_; lean_object* v_snd_821_; lean_object* v___x_822_; uint8_t v_decide_823_; 
v_fst_820_ = lean_ctor_get(v_a_819_, 0);
v_snd_821_ = lean_ctor_get(v_a_819_, 1);
v___x_822_ = lean_string_utf8_byte_size(v_fst_820_);
v_decide_823_ = lean_nat_dec_eq(v_snd_821_, v___x_822_);
if (v_decide_823_ == 0)
{
uint32_t v___x_824_; uint32_t v___x_835_; uint8_t v___x_836_; 
v___x_824_ = lean_string_utf8_get_fast(v_fst_820_, v_snd_821_);
v___x_835_ = 48;
v___x_836_ = lean_uint32_dec_le(v___x_835_, v___x_824_);
if (v___x_836_ == 0)
{
goto v___jp_825_;
}
else
{
uint32_t v___x_837_; uint8_t v___x_838_; 
v___x_837_ = 57;
v___x_838_ = lean_uint32_dec_le(v___x_824_, v___x_837_);
if (v___x_838_ == 0)
{
goto v___jp_825_;
}
else
{
lean_object* v___x_839_; 
v___x_839_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_819_);
return v___x_839_;
}
}
v___jp_825_:
{
uint32_t v___x_826_; uint8_t v___x_827_; 
v___x_826_ = 43;
v___x_827_ = lean_uint32_dec_eq(v___x_824_, v___x_826_);
if (v___x_827_ == 0)
{
uint32_t v___x_828_; uint8_t v___x_829_; 
v___x_828_ = 45;
v___x_829_ = lean_uint32_dec_eq(v___x_824_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_830_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_831_ = lean_int_add(v_stdOffset_818_, v___x_830_);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v_a_819_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
return v___x_832_;
}
else
{
lean_object* v___x_833_; 
v___x_833_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_819_);
return v___x_833_;
}
}
else
{
lean_object* v___x_834_; 
v___x_834_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_819_);
return v___x_834_;
}
}
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_840_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_841_ = lean_int_add(v_stdOffset_818_, v___x_840_);
v___x_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_842_, 0, v_a_819_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset___boxed(lean_object* v_stdOffset_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(v_stdOffset_843_, v_a_844_);
lean_dec(v_stdOffset_843_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSpec(lean_object* v_a_846_){
_start:
{
lean_object* v_snd_848_; lean_object* v___y_849_; lean_object* v_pos_850_; lean_object* v_snd_851_; lean_object* v___y_855_; lean_object* v_pos_856_; lean_object* v___x_872_; 
lean_inc_ref(v_a_846_);
v___x_872_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec(v_a_846_);
if (lean_obj_tag(v___x_872_) == 0)
{
if (lean_obj_tag(v___x_872_) == 0)
{
lean_dec_ref(v_a_846_);
return v___x_872_;
}
else
{
lean_object* v_pos_873_; 
v_pos_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_pos_873_);
v___y_855_ = v___x_872_;
v_pos_856_ = v_pos_873_;
goto v___jp_854_;
}
}
else
{
lean_object* v_err_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
v_err_874_ = lean_ctor_get(v___x_872_, 1);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_881_ == 0)
{
lean_object* v_unused_882_; 
v_unused_882_ = lean_ctor_get(v___x_872_, 0);
lean_dec(v_unused_882_);
v___x_876_ = v___x_872_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_err_874_);
lean_dec(v___x_872_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
lean_inc_ref(v_a_846_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v_a_846_);
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_846_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_err_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_inc_ref(v_a_846_);
v___y_855_ = v___x_879_;
v_pos_856_ = v_a_846_;
goto v___jp_854_;
}
}
}
v___jp_847_:
{
uint8_t v_decide_852_; 
v_decide_852_ = lean_nat_dec_eq(v_snd_848_, v_snd_851_);
lean_dec(v_snd_851_);
lean_dec(v_snd_848_);
if (v_decide_852_ == 0)
{
lean_dec_ref(v_pos_850_);
return v___y_849_;
}
else
{
lean_object* v___x_853_; 
lean_dec_ref(v___y_849_);
v___x_853_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec(v_pos_850_);
return v___x_853_;
}
}
v___jp_854_:
{
lean_object* v_snd_857_; lean_object* v_snd_858_; uint8_t v_decide_859_; 
v_snd_857_ = lean_ctor_get(v_a_846_, 1);
lean_inc(v_snd_857_);
lean_dec_ref(v_a_846_);
v_snd_858_ = lean_ctor_get(v_pos_856_, 1);
lean_inc(v_snd_858_);
v_decide_859_ = lean_nat_dec_eq(v_snd_857_, v_snd_858_);
lean_dec(v_snd_857_);
if (v_decide_859_ == 0)
{
lean_dec(v_snd_858_);
lean_dec_ref(v_pos_856_);
return v___y_855_;
}
else
{
lean_object* v___x_860_; 
lean_dec_ref(v___y_855_);
lean_inc_ref(v_pos_856_);
v___x_860_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec(v_pos_856_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_dec_ref(v_pos_856_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_dec(v_snd_858_);
return v___x_860_;
}
else
{
lean_object* v_pos_861_; lean_object* v_snd_862_; 
v_pos_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_pos_861_);
v_snd_862_ = lean_ctor_get(v_pos_861_, 1);
lean_inc(v_snd_862_);
v_snd_848_ = v_snd_858_;
v___y_849_ = v___x_860_;
v_pos_850_ = v_pos_861_;
v_snd_851_ = v_snd_862_;
goto v___jp_847_;
}
}
else
{
lean_object* v_err_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
v_err_863_ = lean_ctor_get(v___x_860_, 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; 
v_unused_871_ = lean_ctor_get(v___x_860_, 0);
lean_dec(v_unused_871_);
v___x_865_ = v___x_860_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_err_863_);
lean_dec(v___x_860_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
lean_inc_ref(v_pos_856_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v_pos_856_);
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_pos_856_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_err_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_inc(v_snd_858_);
v_snd_848_ = v_snd_858_;
v___y_849_ = v___x_868_;
v_pos_850_ = v_pos_856_;
v_snd_851_ = v_snd_858_;
goto v___jp_847_;
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
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_unsigned_to_nat(2u);
v___x_884_ = lean_nat_to_int(v___x_883_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_885_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_886_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0);
v___x_887_ = lean_int_mul(v___x_886_, v___x_885_);
return v___x_887_;
}
}
lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(uint8_t v_extended_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSpec(v_a_892_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_pos_894_; lean_object* v_res_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_939_; 
v_pos_894_ = lean_ctor_get(v___x_893_, 0);
v_res_895_ = lean_ctor_get(v___x_893_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_939_ == 0)
{
v___x_897_ = v___x_893_;
v_isShared_898_ = v_isSharedCheck_939_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_res_895_);
lean_inc(v_pos_894_);
lean_dec(v___x_893_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_939_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_pos_900_; lean_object* v_res_901_; lean_object* v_fst_906_; lean_object* v_snd_907_; lean_object* v_pos_909_; lean_object* v_snd_910_; lean_object* v_err_911_; lean_object* v___x_915_; uint8_t v_decide_916_; 
v_fst_906_ = lean_ctor_get(v_pos_894_, 0);
v_snd_907_ = lean_ctor_get(v_pos_894_, 1);
lean_inc(v_snd_907_);
v___x_915_ = lean_string_utf8_byte_size(v_fst_906_);
v_decide_916_ = lean_nat_dec_eq(v_snd_907_, v___x_915_);
if (v_decide_916_ == 0)
{
uint32_t v___x_917_; uint32_t v_c_918_; uint8_t v___x_919_; 
v___x_917_ = 47;
v_c_918_ = lean_string_utf8_get_fast(v_fst_906_, v_snd_907_);
v___x_919_ = lean_uint32_dec_eq(v_c_918_, v___x_917_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; 
v___x_920_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3));
lean_inc(v_snd_907_);
v_pos_909_ = v_pos_894_;
v_snd_910_ = v_snd_907_;
v_err_911_ = v___x_920_;
goto v___jp_908_;
}
else
{
lean_object* v___x_921_; lean_object* v_it_x27_922_; lean_object* v___x_923_; 
v___x_921_ = lean_string_utf8_next_fast(v_fst_906_, v_snd_907_);
lean_inc(v_fst_906_);
v_it_x27_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_922_, 0, v_fst_906_);
lean_ctor_set(v_it_x27_922_, 1, v___x_921_);
v___x_923_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(v_it_x27_922_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_pos_924_; lean_object* v_res_925_; lean_object* v___y_927_; 
v_pos_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_pos_924_);
v_res_925_ = lean_ctor_get(v___x_923_, 1);
lean_inc(v_res_925_);
lean_dec_ref_known(v___x_923_, 2);
if (v_extended_891_ == 0)
{
lean_object* v___x_935_; 
v___x_935_ = lean_unsigned_to_nat(24u);
v___y_927_ = v___x_935_;
goto v___jp_926_;
}
else
{
lean_object* v___x_936_; 
v___x_936_ = lean_unsigned_to_nat(167u);
v___y_927_ = v___x_936_;
goto v___jp_926_;
}
v___jp_926_:
{
lean_object* v___x_928_; 
v___x_928_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(v___y_927_, v_pos_924_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_pos_929_; lean_object* v_res_930_; lean_object* v___x_931_; 
lean_dec(v_snd_907_);
lean_dec(v_pos_894_);
v_pos_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_pos_929_);
v_res_930_ = lean_ctor_get(v___x_928_, 1);
lean_inc(v_res_930_);
lean_dec_ref_known(v___x_928_, 2);
v___x_931_ = lean_int_mul(v_res_925_, v_res_930_);
lean_dec(v_res_930_);
lean_dec(v_res_925_);
v_pos_900_ = v_pos_929_;
v_res_901_ = v___x_931_;
goto v___jp_899_;
}
else
{
lean_dec(v_res_925_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_pos_932_; lean_object* v_res_933_; 
lean_dec(v_snd_907_);
lean_dec(v_pos_894_);
v_pos_932_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_pos_932_);
v_res_933_ = lean_ctor_get(v___x_928_, 1);
lean_inc(v_res_933_);
lean_dec_ref_known(v___x_928_, 2);
v_pos_900_ = v_pos_932_;
v_res_901_ = v_res_933_;
goto v___jp_899_;
}
else
{
lean_object* v_err_934_; 
v_err_934_ = lean_ctor_get(v___x_928_, 1);
lean_inc(v_err_934_);
lean_dec_ref_known(v___x_928_, 2);
lean_inc(v_snd_907_);
v_pos_909_ = v_pos_894_;
v_snd_910_ = v_snd_907_;
v_err_911_ = v_err_934_;
goto v___jp_908_;
}
}
}
}
else
{
lean_object* v_err_937_; 
v_err_937_ = lean_ctor_get(v___x_923_, 1);
lean_inc(v_err_937_);
lean_dec_ref_known(v___x_923_, 2);
lean_inc(v_snd_907_);
v_pos_909_ = v_pos_894_;
v_snd_910_ = v_snd_907_;
v_err_911_ = v_err_937_;
goto v___jp_908_;
}
}
}
else
{
lean_object* v___x_938_; 
v___x_938_ = lean_box(0);
lean_inc(v_snd_907_);
v_pos_909_ = v_pos_894_;
v_snd_910_ = v_snd_907_;
v_err_911_ = v___x_938_;
goto v___jp_908_;
}
v___jp_899_:
{
lean_object* v___x_902_; lean_object* v___x_904_; 
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v_res_895_);
lean_ctor_set(v___x_902_, 1, v_res_901_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 1, v___x_902_);
lean_ctor_set(v___x_897_, 0, v_pos_900_);
v___x_904_ = v___x_897_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_pos_900_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
v___jp_908_:
{
uint8_t v_decide_912_; 
v_decide_912_ = lean_nat_dec_eq(v_snd_907_, v_snd_910_);
lean_dec(v_snd_910_);
lean_dec(v_snd_907_);
if (v_decide_912_ == 0)
{
lean_object* v___x_913_; 
lean_del_object(v___x_897_);
lean_dec(v_res_895_);
v___x_913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_913_, 0, v_pos_909_);
lean_ctor_set(v___x_913_, 1, v_err_911_);
return v___x_913_;
}
else
{
lean_object* v___x_914_; 
lean_dec(v_err_911_);
v___x_914_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1);
v_pos_900_ = v_pos_909_;
v_res_901_ = v___x_914_;
goto v___jp_899_;
}
}
}
}
else
{
lean_object* v_pos_940_; lean_object* v_err_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
v_pos_940_ = lean_ctor_get(v___x_893_, 0);
v_err_941_ = lean_ctor_get(v___x_893_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_893_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_err_941_);
lean_inc(v_pos_940_);
lean_dec(v___x_893_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_pos_940_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_err_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule_0interp(lean_interpreter_value* stack)
{
uint8_t v_extended_891_ = stack[0].m_num;
lean_object* v_a_892_ = stack[1].m_obj;
lean_object* v_res_949_;
v_res_949_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_891_, v_a_892_);
stack->m_obj
 = v_res_949_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___boxed(lean_object* v_extended_950_, lean_object* v_a_951_){
_start:
{
uint8_t v_extended_boxed_952_; lean_object* v_res_953_; 
v_extended_boxed_952_ = lean_unbox(v_extended_950_);
v_res_953_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_boxed_952_, v_a_951_);
return v_res_953_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_957_; lean_object* v___x_958_; 
v___x_957_ = 44;
v___x_958_ = lean_box_uint32(v___x_957_);
return v___x_958_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2___boxed__const__1;
v___x_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
}
lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP(uint8_t v_extended_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(v_a_965_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_pos_967_; lean_object* v_res_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_1150_; 
v_pos_967_ = lean_ctor_get(v___x_966_, 0);
v_res_968_ = lean_ctor_get(v___x_966_, 1);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_970_ = v___x_966_;
v_isShared_971_ = v_isSharedCheck_1150_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_res_968_);
lean_inc(v_pos_967_);
lean_dec(v___x_966_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_1150_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_972_ = lean_string_utf8_byte_size(v_res_968_);
v___x_973_ = lean_unsigned_to_nat(0u);
v___x_974_ = lean_nat_dec_eq(v___x_972_, v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; 
v___x_975_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_pos_967_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_pos_976_; lean_object* v_res_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1136_; 
v_pos_976_ = lean_ctor_get(v___x_975_, 0);
v_res_977_ = lean_ctor_get(v___x_975_, 1);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_979_ = v___x_975_;
v_isShared_980_ = v_isSharedCheck_1136_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_res_977_);
lean_inc(v_pos_976_);
lean_dec(v___x_975_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1136_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; uint32_t v___y_987_; lean_object* v___y_988_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; uint8_t v___y_1026_; lean_object* v___y_1027_; uint32_t v___y_1028_; uint8_t v___y_1029_; lean_object* v___y_1061_; lean_object* v___y_1062_; uint8_t v___y_1063_; lean_object* v_pos_1064_; lean_object* v_res_1065_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; uint8_t v___y_1083_; lean_object* v___y_1084_; lean_object* v_fst_1129_; lean_object* v_snd_1130_; lean_object* v___x_1131_; uint8_t v_decide_1132_; 
v_fst_1129_ = lean_ctor_get(v_pos_976_, 0);
v_snd_1130_ = lean_ctor_get(v_pos_976_, 1);
v___x_1131_ = lean_string_utf8_byte_size(v_fst_1129_);
v_decide_1132_ = lean_nat_dec_eq(v_snd_1130_, v___x_1131_);
if (v_decide_1132_ == 0)
{
goto v___jp_1088_;
}
else
{
if (v___x_974_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_del_object(v___x_979_);
lean_del_object(v___x_970_);
v___x_1133_ = lean_box(0);
v___x_1134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1134_, 0, v_res_968_);
lean_ctor_set(v___x_1134_, 1, v_res_977_);
lean_ctor_set(v___x_1134_, 2, v___x_1133_);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v_pos_976_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
return v___x_1135_;
}
else
{
goto v___jp_1088_;
}
}
v___jp_981_:
{
uint32_t v_c_989_; uint8_t v___x_990_; 
v_c_989_ = lean_string_utf8_get_fast(v___y_986_, v___y_983_);
v___x_990_ = lean_uint32_dec_eq(v_c_989_, v___y_987_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; lean_object* v___x_993_; 
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec(v___y_982_);
lean_dec(v_res_977_);
lean_dec(v_res_968_);
v___x_991_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1));
if (v_isShared_980_ == 0)
{
lean_ctor_set_tag(v___x_979_, 1);
lean_ctor_set(v___x_979_, 1, v___x_991_);
lean_ctor_set(v___x_979_, 0, v___y_988_);
v___x_993_ = v___x_979_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___y_988_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
else
{
lean_object* v___x_995_; lean_object* v_it_x27_996_; lean_object* v___x_997_; 
lean_dec_ref(v___y_988_);
lean_del_object(v___x_979_);
v___x_995_ = lean_string_utf8_next_fast(v___y_986_, v___y_983_);
lean_dec(v___y_983_);
v_it_x27_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_996_, 0, v___y_986_);
lean_ctor_set(v_it_x27_996_, 1, v___x_995_);
v___x_997_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_964_, v_it_x27_996_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_pos_998_; lean_object* v_res_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1011_; 
v_pos_998_ = lean_ctor_get(v___x_997_, 0);
v_res_999_ = lean_ctor_get(v___x_997_, 1);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1001_ = v___x_997_;
v_isShared_1002_ = v_isSharedCheck_1011_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_res_999_);
lean_inc(v_pos_998_);
lean_dec(v___x_997_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1011_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___y_985_);
v___x_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1004_, 0, v_res_999_);
v___x_1005_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1005_, 0, v___y_984_);
lean_ctor_set(v___x_1005_, 1, v___y_982_);
lean_ctor_set(v___x_1005_, 2, v___x_1003_);
lean_ctor_set(v___x_1005_, 3, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
v___x_1007_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1007_, 0, v_res_968_);
lean_ctor_set(v___x_1007_, 1, v_res_977_);
lean_ctor_set(v___x_1007_, 2, v___x_1006_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 1, v___x_1007_);
v___x_1009_ = v___x_1001_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_pos_998_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
else
{
lean_object* v_pos_1012_; lean_object* v_err_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec_ref(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_982_);
lean_dec(v_res_977_);
lean_dec(v_res_968_);
v_pos_1012_ = lean_ctor_get(v___x_997_, 0);
v_err_1013_ = lean_ctor_get(v___x_997_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_997_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_err_1013_);
lean_inc(v_pos_1012_);
lean_dec(v___x_997_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_pos_1012_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_err_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
v___jp_1021_:
{
if (v___y_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec(v___y_1022_);
lean_del_object(v___x_979_);
lean_dec(v_res_977_);
lean_dec(v_res_968_);
v___x_1030_ = lean_box(0);
if (v_isShared_971_ == 0)
{
lean_ctor_set_tag(v___x_970_, 1);
lean_ctor_set(v___x_970_, 1, v___x_1030_);
lean_ctor_set(v___x_970_, 0, v___y_1023_);
v___x_1032_ = v___x_970_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___y_1023_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
lean_dec_ref(v___y_1023_);
lean_del_object(v___x_970_);
v___x_1034_ = lean_string_utf8_next_fast(v___y_1027_, v___y_1024_);
lean_dec(v___y_1024_);
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___y_1027_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_964_, v___x_1035_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_pos_1037_; lean_object* v_res_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1050_; 
v_pos_1037_ = lean_ctor_get(v___x_1036_, 0);
v_res_1038_ = lean_ctor_get(v___x_1036_, 1);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1040_ = v___x_1036_;
v_isShared_1041_ = v_isSharedCheck_1050_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_res_1038_);
lean_inc(v_pos_1037_);
lean_dec(v___x_1036_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1050_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v_fst_1042_; lean_object* v_snd_1043_; lean_object* v___x_1044_; uint8_t v_decide_1045_; 
v_fst_1042_ = lean_ctor_get(v_pos_1037_, 0);
v_snd_1043_ = lean_ctor_get(v_pos_1037_, 1);
v___x_1044_ = lean_string_utf8_byte_size(v_fst_1042_);
v_decide_1045_ = lean_nat_dec_eq(v_snd_1043_, v___x_1044_);
if (v_decide_1045_ == 0)
{
lean_inc(v_snd_1043_);
lean_inc(v_fst_1042_);
lean_del_object(v___x_1040_);
v___y_982_ = v___y_1022_;
v___y_983_ = v_snd_1043_;
v___y_984_ = v___y_1025_;
v___y_985_ = v_res_1038_;
v___y_986_ = v_fst_1042_;
v___y_987_ = v___y_1028_;
v___y_988_ = v_pos_1037_;
goto v___jp_981_;
}
else
{
if (v___y_1026_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
lean_dec(v_res_1038_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1022_);
lean_del_object(v___x_979_);
lean_dec(v_res_977_);
lean_dec(v_res_968_);
v___x_1046_ = lean_box(0);
if (v_isShared_1041_ == 0)
{
lean_ctor_set_tag(v___x_1040_, 1);
lean_ctor_set(v___x_1040_, 1, v___x_1046_);
v___x_1048_ = v___x_1040_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_pos_1037_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
else
{
lean_inc(v_snd_1043_);
lean_inc(v_fst_1042_);
lean_del_object(v___x_1040_);
v___y_982_ = v___y_1022_;
v___y_983_ = v_snd_1043_;
v___y_984_ = v___y_1025_;
v___y_985_ = v_res_1038_;
v___y_986_ = v_fst_1042_;
v___y_987_ = v___y_1028_;
v___y_988_ = v_pos_1037_;
goto v___jp_981_;
}
}
}
}
else
{
lean_object* v_pos_1051_; lean_object* v_err_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1022_);
lean_del_object(v___x_979_);
lean_dec(v_res_977_);
lean_dec(v_res_968_);
v_pos_1051_ = lean_ctor_get(v___x_1036_, 0);
v_err_1052_ = lean_ctor_get(v___x_1036_, 1);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1036_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_err_1052_);
lean_inc(v_pos_1051_);
lean_dec(v___x_1036_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_pos_1051_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_err_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
v___jp_1060_:
{
uint32_t v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1066_ = 44;
v___x_1067_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2);
v___x_1068_ = l_instBEqOption_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_res_1065_, v___x_1067_);
lean_dec(v_res_1065_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_del_object(v___x_979_);
lean_del_object(v___x_970_);
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1070_, 0, v___y_1062_);
lean_ctor_set(v___x_1070_, 1, v___y_1061_);
lean_ctor_set(v___x_1070_, 2, v___x_1069_);
lean_ctor_set(v___x_1070_, 3, v___x_1069_);
v___x_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1072_, 0, v_res_968_);
lean_ctor_set(v___x_1072_, 1, v_res_977_);
lean_ctor_set(v___x_1072_, 2, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_pos_1064_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
return v___x_1073_;
}
else
{
lean_object* v_fst_1074_; lean_object* v_snd_1075_; lean_object* v___x_1076_; uint8_t v_decide_1077_; 
v_fst_1074_ = lean_ctor_get(v_pos_1064_, 0);
lean_inc(v_fst_1074_);
v_snd_1075_ = lean_ctor_get(v_pos_1064_, 1);
lean_inc(v_snd_1075_);
v___x_1076_ = lean_string_utf8_byte_size(v_fst_1074_);
v_decide_1077_ = lean_nat_dec_eq(v_snd_1075_, v___x_1076_);
if (v_decide_1077_ == 0)
{
v___y_1022_ = v___y_1061_;
v___y_1023_ = v_pos_1064_;
v___y_1024_ = v_snd_1075_;
v___y_1025_ = v___y_1062_;
v___y_1026_ = v___y_1063_;
v___y_1027_ = v_fst_1074_;
v___y_1028_ = v___x_1066_;
v___y_1029_ = v___x_1068_;
goto v___jp_1021_;
}
else
{
v___y_1022_ = v___y_1061_;
v___y_1023_ = v_pos_1064_;
v___y_1024_ = v_snd_1075_;
v___y_1025_ = v___y_1062_;
v___y_1026_ = v___y_1063_;
v___y_1027_ = v_fst_1074_;
v___y_1028_ = v___x_1066_;
v___y_1029_ = v___y_1063_;
goto v___jp_1021_;
}
}
}
v___jp_1078_:
{
uint32_t v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1085_ = lean_string_utf8_get_fast(v___y_1081_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec(v___y_1081_);
v___x_1086_ = lean_box_uint32(v___x_1085_);
v___x_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
v___y_1061_ = v___y_1079_;
v___y_1062_ = v___y_1082_;
v___y_1063_ = v___y_1083_;
v_pos_1064_ = v___y_1080_;
v_res_1065_ = v___x_1087_;
goto v___jp_1060_;
}
v___jp_1088_:
{
lean_object* v___x_1089_; 
v___x_1089_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(v_pos_976_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_pos_1090_; lean_object* v_res_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1119_; 
v_pos_1090_ = lean_ctor_get(v___x_1089_, 0);
v_res_1091_ = lean_ctor_get(v___x_1089_, 1);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1093_ = v___x_1089_;
v_isShared_1094_ = v_isSharedCheck_1119_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_res_1091_);
lean_inc(v_pos_1090_);
lean_dec(v___x_1089_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1119_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = lean_string_utf8_byte_size(v_res_1091_);
v___x_1096_ = lean_nat_dec_eq(v___x_1095_, v___x_973_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; 
lean_del_object(v___x_1093_);
v___x_1097_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(v_res_977_, v_pos_1090_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_pos_1098_; lean_object* v_res_1099_; lean_object* v_fst_1100_; lean_object* v_snd_1101_; lean_object* v___x_1102_; uint8_t v_decide_1103_; 
v_pos_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_pos_1098_);
v_res_1099_ = lean_ctor_get(v___x_1097_, 1);
lean_inc(v_res_1099_);
lean_dec_ref_known(v___x_1097_, 2);
v_fst_1100_ = lean_ctor_get(v_pos_1098_, 0);
v_snd_1101_ = lean_ctor_get(v_pos_1098_, 1);
v___x_1102_ = lean_string_utf8_byte_size(v_fst_1100_);
v_decide_1103_ = lean_nat_dec_eq(v_snd_1101_, v___x_1102_);
if (v_decide_1103_ == 0)
{
lean_inc(v_snd_1101_);
lean_inc(v_fst_1100_);
v___y_1079_ = v_res_1099_;
v___y_1080_ = v_pos_1098_;
v___y_1081_ = v_fst_1100_;
v___y_1082_ = v_res_1091_;
v___y_1083_ = v___x_1096_;
v___y_1084_ = v_snd_1101_;
goto v___jp_1078_;
}
else
{
if (v___x_1096_ == 0)
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_box(0);
v___y_1061_ = v_res_1099_;
v___y_1062_ = v_res_1091_;
v___y_1063_ = v___x_1096_;
v_pos_1064_ = v_pos_1098_;
v_res_1065_ = v___x_1104_;
goto v___jp_1060_;
}
else
{
lean_inc(v_snd_1101_);
lean_inc(v_fst_1100_);
v___y_1079_ = v_res_1099_;
v___y_1080_ = v_pos_1098_;
v___y_1081_ = v_fst_1100_;
v___y_1082_ = v_res_1091_;
v___y_1083_ = v___x_1096_;
v___y_1084_ = v_snd_1101_;
goto v___jp_1078_;
}
}
}
else
{
lean_object* v_pos_1105_; lean_object* v_err_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec(v_res_1091_);
lean_del_object(v___x_979_);
lean_dec(v_res_977_);
lean_del_object(v___x_970_);
lean_dec(v_res_968_);
v_pos_1105_ = lean_ctor_get(v___x_1097_, 0);
v_err_1106_ = lean_ctor_get(v___x_1097_, 1);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1097_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_err_1106_);
lean_inc(v_pos_1105_);
lean_dec(v___x_1097_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_pos_1105_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_err_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
else
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
lean_dec(v_res_1091_);
lean_del_object(v___x_979_);
lean_del_object(v___x_970_);
v___x_1114_ = lean_box(0);
v___x_1115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1115_, 0, v_res_968_);
lean_ctor_set(v___x_1115_, 1, v_res_977_);
lean_ctor_set(v___x_1115_, 2, v___x_1114_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v___x_1115_);
v___x_1117_ = v___x_1093_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_pos_1090_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
else
{
lean_object* v_pos_1120_; lean_object* v_err_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_del_object(v___x_979_);
lean_dec(v_res_977_);
lean_del_object(v___x_970_);
lean_dec(v_res_968_);
v_pos_1120_ = lean_ctor_get(v___x_1089_, 0);
v_err_1121_ = lean_ctor_get(v___x_1089_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1089_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_err_1121_);
lean_inc(v_pos_1120_);
lean_dec(v___x_1089_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_pos_1120_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_err_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1137_; lean_object* v_err_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_del_object(v___x_970_);
lean_dec(v_res_968_);
v_pos_1137_ = lean_ctor_get(v___x_975_, 0);
v_err_1138_ = lean_ctor_get(v___x_975_, 1);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_975_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_err_1138_);
lean_inc(v_pos_1137_);
lean_dec(v___x_975_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_pos_1137_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_err_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
else
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
lean_dec(v_res_968_);
v___x_1146_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__4));
if (v_isShared_971_ == 0)
{
lean_ctor_set_tag(v___x_970_, 1);
lean_ctor_set(v___x_970_, 1, v___x_1146_);
v___x_1148_ = v___x_970_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_pos_967_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
else
{
lean_object* v_pos_1151_; lean_object* v_err_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
v_pos_1151_ = lean_ctor_get(v___x_966_, 0);
v_err_1152_ = lean_ctor_get(v___x_966_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_966_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_err_1152_);
lean_inc(v_pos_1151_);
lean_dec(v___x_966_);
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
LEAN_EXPORT void l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP_0interp(lean_interpreter_value* stack)
{
uint8_t v_extended_964_ = stack[0].m_num;
lean_object* v_a_965_ = stack[1].m_obj;
lean_object* v_res_1160_;
v_res_1160_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP(v_extended_964_, v_a_965_);
stack->m_obj
 = v_res_1160_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___boxed(lean_object* v_extended_1161_, lean_object* v_a_1162_){
_start:
{
uint8_t v_extended_boxed_1163_; lean_object* v_res_1164_; 
v_extended_boxed_1163_ = lean_unbox(v_extended_1161_);
v_res_1164_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP(v_extended_boxed_1163_, v_a_1162_);
return v_res_1164_;
}
}
lean_object* l_Std_Time_TimeZone_parsePosixTz(lean_object* v_s_1165_, uint8_t v_extended_1166_){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1167_ = lean_box(v_extended_1166_);
v___x_1168_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___boxed), 2, 1);
lean_closure_set(v___x_1168_, 0, v___x_1167_);
v___x_1169_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_1168_, v_s_1165_);
return v___x_1169_;
}
}
LEAN_EXPORT void l_Std_Time_TimeZone_parsePosixTz_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1165_ = stack[0].m_obj;
uint8_t v_extended_1166_ = stack[1].m_num;
lean_object* v_res_1170_;
v_res_1170_ = l_Std_Time_TimeZone_parsePosixTz(v_s_1165_, v_extended_1166_);
stack->m_obj
 = v_res_1170_;
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_parsePosixTz___boxed(lean_object* v_s_1171_, lean_object* v_extended_1172_){
_start:
{
uint8_t v_extended_boxed_1173_; lean_object* v_res_1174_; 
v_extended_boxed_1173_ = lean_unbox(v_extended_1172_);
v_res_1174_ = l_Std_Time_TimeZone_parsePosixTz(v_s_1171_, v_extended_boxed_1173_);
return v_res_1174_;
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
l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2___boxed__const__1 = _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2___boxed__const__1();
lean_mark_persistent(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2___boxed__const__1);
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
