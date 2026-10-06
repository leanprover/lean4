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
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0(uint8_t v___x_142_, lean_object* v_x_143_){
_start:
{
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed(lean_object* v___x_144_, lean_object* v_x_145_){
_start:
{
uint8_t v___x_3940__boxed_146_; uint8_t v_res_147_; lean_object* v_r_148_; 
v___x_3940__boxed_146_ = lean_unbox(v___x_144_);
v_res_147_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0(v___x_3940__boxed_146_, v_x_145_);
lean_dec(v_x_145_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(3600u);
v___x_153_ = lean_nat_to_int(v___x_152_);
return v___x_153_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(60u);
v___x_155_ = lean_nat_to_int(v___x_154_);
return v___x_155_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_nat_to_int(v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_unsigned_to_nat(59u);
v___x_162_ = lean_nat_to_int(v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(lean_object* v_maxHour_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_fst_170_; lean_object* v_snd_171_; lean_object* v___x_172_; uint8_t v_decide_173_; 
v_fst_170_ = lean_ctor_get(v_a_166_, 0);
v_snd_171_ = lean_ctor_get(v_a_166_, 1);
v___x_172_ = lean_string_utf8_byte_size(v_fst_170_);
v_decide_173_ = lean_nat_dec_eq(v_snd_171_, v___x_172_);
if (v_decide_173_ == 0)
{
uint32_t v_c_174_; uint32_t v___x_175_; uint8_t v___x_176_; 
v_c_174_ = lean_string_utf8_get_fast(v_fst_170_, v_snd_171_);
v___x_175_ = 48;
v___x_176_ = lean_uint32_dec_le(v___x_175_, v_c_174_);
if (v___x_176_ == 0)
{
lean_dec(v_maxHour_165_);
goto v___jp_167_;
}
else
{
uint32_t v___x_177_; uint8_t v___x_178_; 
v___x_177_ = 57;
v___x_178_ = lean_uint32_dec_le(v_c_174_, v___x_177_);
if (v___x_178_ == 0)
{
lean_dec(v_maxHour_165_);
goto v___jp_167_;
}
else
{
lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_297_; 
lean_inc(v_snd_171_);
lean_inc(v_fst_170_);
v_isSharedCheck_297_ = !lean_is_exclusive(v_a_166_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; lean_object* v_unused_299_; 
v_unused_298_ = lean_ctor_get(v_a_166_, 1);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_a_166_, 0);
lean_dec(v_unused_299_);
v___x_180_ = v_a_166_;
v_isShared_181_ = v_isSharedCheck_297_;
goto v_resetjp_179_;
}
else
{
lean_dec(v_a_166_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_297_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v_fst_187_; lean_object* v_snd_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_296_; 
v___x_182_ = lean_string_utf8_next_fast(v_fst_170_, v_snd_171_);
lean_dec(v_snd_171_);
v___x_183_ = lean_uint32_to_nat(v_c_174_);
v___x_184_ = lean_unsigned_to_nat(48u);
v___x_185_ = lean_nat_sub(v___x_183_, v___x_184_);
lean_dec(v___x_183_);
v___x_186_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_170_, v___x_182_, v___x_185_);
v_fst_187_ = lean_ctor_get(v___x_186_, 0);
v_snd_188_ = lean_ctor_get(v___x_186_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_296_ == 0)
{
v___x_190_ = v___x_186_;
v_isShared_191_ = v_isSharedCheck_296_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_snd_188_);
lean_inc(v_fst_187_);
lean_dec(v___x_186_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_296_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
lean_inc(v_snd_188_);
lean_inc(v_fst_170_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 1, v_snd_188_);
v___x_193_ = v___x_180_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_fst_170_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_snd_188_);
v___x_193_ = v_reuseFailAlloc_295_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
uint8_t v___x_194_; 
v___x_194_ = lean_nat_dec_lt(v_maxHour_165_, v_fst_187_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; uint8_t v___x_196_; 
lean_dec(v_maxHour_165_);
v___x_195_ = lean_unsigned_to_nat(167u);
v___x_196_ = lean_nat_dec_le(v_fst_187_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_206_; 
lean_dec(v_snd_188_);
lean_dec(v_fst_170_);
v___x_197_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0));
v___x_198_ = l_Nat_reprFast(v_fst_187_);
v___x_199_ = lean_string_append(v___x_197_, v___x_198_);
lean_dec_ref(v___x_198_);
v___x_200_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1));
v___x_201_ = lean_string_append(v___x_199_, v___x_200_);
v___x_202_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2));
v___x_203_ = lean_string_append(v___x_201_, v___x_202_);
v___x_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
if (v_isShared_191_ == 0)
{
lean_ctor_set_tag(v___x_190_, 1);
lean_ctor_set(v___x_190_, 1, v___x_204_);
lean_ctor_set(v___x_190_, 0, v___x_193_);
v___x_206_ = v___x_190_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v___x_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
else
{
lean_object* v___x_208_; lean_object* v___y_210_; lean_object* v_pos_211_; lean_object* v_res_212_; lean_object* v___y_223_; lean_object* v___y_224_; lean_object* v_err_225_; uint32_t v___x_230_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___y_234_; lean_object* v___y_235_; uint8_t v___y_236_; lean_object* v_pos_253_; lean_object* v_fst_254_; lean_object* v_snd_255_; lean_object* v_res_256_; lean_object* v_err_260_; uint8_t v___y_265_; uint8_t v_decide_283_; 
v___x_208_ = lean_nat_to_int(v_fst_187_);
v___x_230_ = 58;
v_decide_283_ = lean_nat_dec_eq(v_snd_188_, v___x_172_);
if (v_decide_283_ == 0)
{
v___y_265_ = v___x_196_;
goto v___jp_264_;
}
else
{
v___y_265_ = v___x_194_;
goto v___jp_264_;
}
v___jp_209_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_213_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_214_ = lean_int_mul(v___x_208_, v___x_213_);
lean_dec(v___x_208_);
v___x_215_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4);
v___x_216_ = lean_int_mul(v___y_210_, v___x_215_);
lean_dec(v___y_210_);
v___x_217_ = lean_int_add(v___x_214_, v___x_216_);
lean_dec(v___x_216_);
lean_dec(v___x_214_);
v___x_218_ = lean_int_add(v___x_217_, v_res_212_);
lean_dec(v_res_212_);
lean_dec(v___x_217_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 1, v___x_218_);
lean_ctor_set(v___x_190_, 0, v_pos_211_);
v___x_220_ = v___x_190_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_pos_211_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
v___jp_222_:
{
lean_object* v_snd_226_; uint8_t v_decide_227_; 
v_snd_226_ = lean_ctor_get(v___y_224_, 1);
v_decide_227_ = lean_nat_dec_eq(v_snd_226_, v_snd_226_);
if (v_decide_227_ == 0)
{
lean_object* v___x_228_; 
lean_dec(v___y_223_);
lean_dec(v___x_208_);
lean_del_object(v___x_190_);
v___x_228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_228_, 0, v___y_224_);
lean_ctor_set(v___x_228_, 1, v_err_225_);
return v___x_228_;
}
else
{
lean_object* v___x_229_; 
lean_dec(v_err_225_);
v___x_229_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___y_210_ = v___y_223_;
v_pos_211_ = v___y_224_;
v_res_212_ = v___x_229_;
goto v___jp_209_;
}
}
v___jp_231_:
{
if (v___y_236_ == 0)
{
lean_object* v___x_237_; 
lean_dec(v___y_235_);
lean_dec(v___y_233_);
v___x_237_ = lean_box(0);
v___y_223_ = v___y_232_;
v___y_224_ = v___y_234_;
v_err_225_ = v___x_237_;
goto v___jp_222_;
}
else
{
uint32_t v_c_238_; uint8_t v___x_239_; 
v_c_238_ = lean_string_utf8_get_fast(v___y_235_, v___y_233_);
v___x_239_ = lean_uint32_dec_eq(v_c_238_, v___x_230_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; 
lean_dec(v___y_235_);
lean_dec(v___y_233_);
v___x_240_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7));
v___y_223_ = v___y_232_;
v___y_224_ = v___y_234_;
v_err_225_ = v___x_240_;
goto v___jp_222_;
}
else
{
lean_object* v___x_241_; lean_object* v___f_242_; lean_object* v___x_243_; lean_object* v_it_x27_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_241_ = lean_box(v___x_239_);
v___f_242_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_242_, 0, v___x_241_);
v___x_243_ = lean_string_utf8_next_fast(v___y_235_, v___y_233_);
lean_dec(v___y_233_);
v_it_x27_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_244_, 0, v___y_235_);
lean_ctor_set(v_it_x27_244_, 1, v___x_243_);
v___x_245_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___x_246_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8);
v___x_247_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9));
v___x_248_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_245_, v___x_246_, v___x_247_, v___f_242_, v_it_x27_244_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_pos_249_; lean_object* v_res_250_; 
lean_dec_ref(v___y_234_);
v_pos_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_pos_249_);
v_res_250_ = lean_ctor_get(v___x_248_, 1);
lean_inc(v_res_250_);
lean_dec_ref_known(v___x_248_, 2);
v___y_210_ = v___y_232_;
v_pos_211_ = v_pos_249_;
v_res_212_ = v_res_250_;
goto v___jp_209_;
}
else
{
lean_object* v_err_251_; 
v_err_251_ = lean_ctor_get(v___x_248_, 1);
lean_inc(v_err_251_);
lean_dec_ref_known(v___x_248_, 2);
v___y_223_ = v___y_232_;
v___y_224_ = v___y_234_;
v_err_225_ = v_err_251_;
goto v___jp_222_;
}
}
}
}
v___jp_252_:
{
lean_object* v___x_257_; uint8_t v_decide_258_; 
v___x_257_ = lean_string_utf8_byte_size(v_fst_254_);
v_decide_258_ = lean_nat_dec_eq(v_snd_255_, v___x_257_);
if (v_decide_258_ == 0)
{
v___y_232_ = v_res_256_;
v___y_233_ = v_snd_255_;
v___y_234_ = v_pos_253_;
v___y_235_ = v_fst_254_;
v___y_236_ = v___x_196_;
goto v___jp_231_;
}
else
{
v___y_232_ = v_res_256_;
v___y_233_ = v_snd_255_;
v___y_234_ = v_pos_253_;
v___y_235_ = v_fst_254_;
v___y_236_ = v___x_194_;
goto v___jp_231_;
}
}
v___jp_259_:
{
uint8_t v_decide_261_; 
v_decide_261_ = lean_nat_dec_eq(v_snd_188_, v_snd_188_);
if (v_decide_261_ == 0)
{
lean_object* v___x_262_; 
lean_dec(v___x_208_);
lean_del_object(v___x_190_);
lean_dec(v_snd_188_);
lean_dec(v_fst_170_);
v___x_262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_193_);
lean_ctor_set(v___x_262_, 1, v_err_260_);
return v___x_262_;
}
else
{
lean_object* v___x_263_; 
lean_dec(v_err_260_);
v___x_263_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v_pos_253_ = v___x_193_;
v_fst_254_ = v_fst_170_;
v_snd_255_ = v_snd_188_;
v_res_256_ = v___x_263_;
goto v___jp_252_;
}
}
v___jp_264_:
{
if (v___y_265_ == 0)
{
lean_object* v___x_266_; 
v___x_266_ = lean_box(0);
v_err_260_ = v___x_266_;
goto v___jp_259_;
}
else
{
uint32_t v_c_267_; uint8_t v___x_268_; 
v_c_267_ = lean_string_utf8_get_fast(v_fst_170_, v_snd_188_);
v___x_268_ = lean_uint32_dec_eq(v_c_267_, v___x_230_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7));
v_err_260_ = v___x_269_;
goto v___jp_259_;
}
else
{
lean_object* v___x_270_; lean_object* v___f_271_; lean_object* v___x_272_; lean_object* v_it_x27_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_270_ = lean_box(v___x_268_);
v___f_271_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_271_, 0, v___x_270_);
v___x_272_ = lean_string_utf8_next_fast(v_fst_170_, v_snd_188_);
lean_inc(v_fst_170_);
v_it_x27_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_273_, 0, v_fst_170_);
lean_ctor_set(v_it_x27_273_, 1, v___x_272_);
v___x_274_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___x_275_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8);
v___x_276_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10));
v___x_277_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_274_, v___x_275_, v___x_276_, v___f_271_, v_it_x27_273_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_pos_278_; lean_object* v_res_279_; lean_object* v_fst_280_; lean_object* v_snd_281_; 
lean_dec_ref(v___x_193_);
lean_dec(v_snd_188_);
lean_dec(v_fst_170_);
v_pos_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_pos_278_);
v_res_279_ = lean_ctor_get(v___x_277_, 1);
lean_inc(v_res_279_);
lean_dec_ref_known(v___x_277_, 2);
v_fst_280_ = lean_ctor_get(v_pos_278_, 0);
lean_inc(v_fst_280_);
v_snd_281_ = lean_ctor_get(v_pos_278_, 1);
lean_inc(v_snd_281_);
v_pos_253_ = v_pos_278_;
v_fst_254_ = v_fst_280_;
v_snd_255_ = v_snd_281_;
v_res_256_ = v_res_279_;
goto v___jp_252_;
}
else
{
lean_object* v_err_282_; 
v_err_282_ = lean_ctor_get(v___x_277_, 1);
lean_inc(v_err_282_);
lean_dec_ref_known(v___x_277_, 2);
v_err_260_ = v_err_282_;
goto v___jp_259_;
}
}
}
}
}
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
lean_dec(v_snd_188_);
lean_dec(v_fst_170_);
v___x_284_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0));
v___x_285_ = l_Nat_reprFast(v_fst_187_);
v___x_286_ = lean_string_append(v___x_284_, v___x_285_);
lean_dec_ref(v___x_285_);
v___x_287_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1));
v___x_288_ = lean_string_append(v___x_286_, v___x_287_);
v___x_289_ = l_Nat_reprFast(v_maxHour_165_);
v___x_290_ = lean_string_append(v___x_288_, v___x_289_);
lean_dec_ref(v___x_289_);
v___x_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
if (v_isShared_191_ == 0)
{
lean_ctor_set_tag(v___x_190_, 1);
lean_ctor_set(v___x_190_, 1, v___x_291_);
lean_ctor_set(v___x_190_, 0, v___x_193_);
v___x_293_ = v___x_190_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
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
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v_maxHour_165_);
v___x_300_ = lean_box(0);
v___x_301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_301_, 0, v_a_166_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
return v___x_301_;
}
v___jp_167_:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__1));
v___x_169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_169_, 0, v_a_166_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__1(lean_object* v_a_302_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_nat_to_int(v_a_302_);
v___x_304_ = l_Rat_ofInt(v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(lean_object* v_a_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(v_a_305_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_pos_307_; lean_object* v_res_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_pos_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_pos_307_);
v_res_308_ = lean_ctor_get(v___x_306_, 1);
lean_inc(v_res_308_);
lean_dec_ref_known(v___x_306_, 2);
v___x_309_ = lean_unsigned_to_nat(24u);
v___x_310_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(v___x_309_, v_pos_307_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_pos_311_; lean_object* v_res_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_321_; 
v_pos_311_ = lean_ctor_get(v___x_310_, 0);
v_res_312_ = lean_ctor_get(v___x_310_, 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_321_ == 0)
{
v___x_314_ = v___x_310_;
v_isShared_315_ = v_isSharedCheck_321_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_res_312_);
lean_inc(v_pos_311_);
lean_dec(v___x_310_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_321_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_316_ = lean_int_neg(v_res_308_);
lean_dec(v_res_308_);
v___x_317_ = lean_int_mul(v___x_316_, v_res_312_);
lean_dec(v_res_312_);
lean_dec(v___x_316_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v___x_317_);
v___x_319_ = v___x_314_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_pos_311_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
else
{
lean_object* v_pos_322_; lean_object* v_err_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
lean_dec(v_res_308_);
v_pos_322_ = lean_ctor_get(v___x_310_, 0);
v_err_323_ = lean_ctor_get(v___x_310_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_310_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_err_323_);
lean_inc(v_pos_322_);
lean_dec(v___x_310_);
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
else
{
lean_object* v_pos_331_; lean_object* v_err_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
v_pos_331_ = lean_ctor_get(v___x_306_, 0);
v_err_332_ = lean_ctor_get(v___x_306_, 1);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_306_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_err_332_);
lean_inc(v_pos_331_);
lean_dec(v___x_306_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_pos_331_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_err_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0(lean_object* v_acc_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_pos_346_; uint32_t v_res_347_; lean_object* v_fst_350_; lean_object* v_snd_351_; lean_object* v_pos_353_; lean_object* v_snd_354_; lean_object* v_err_355_; lean_object* v___x_359_; uint8_t v_decide_360_; 
v_fst_350_ = lean_ctor_get(v_a_344_, 0);
v_snd_351_ = lean_ctor_get(v_a_344_, 1);
lean_inc(v_snd_351_);
v___x_359_ = lean_string_utf8_byte_size(v_fst_350_);
v_decide_360_ = lean_nat_dec_eq(v_snd_351_, v___x_359_);
if (v_decide_360_ == 0)
{
uint32_t v_c_361_; lean_object* v___x_362_; lean_object* v_it_x27_363_; uint32_t v___x_380_; uint8_t v___x_381_; 
v_c_361_ = lean_string_utf8_get_fast(v_fst_350_, v_snd_351_);
v___x_362_ = lean_string_utf8_next_fast(v_fst_350_, v_snd_351_);
lean_inc(v_fst_350_);
v_it_x27_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_363_, 0, v_fst_350_);
lean_ctor_set(v_it_x27_363_, 1, v___x_362_);
v___x_380_ = 65;
v___x_381_ = lean_uint32_dec_le(v___x_380_, v_c_361_);
if (v___x_381_ == 0)
{
goto v___jp_375_;
}
else
{
uint32_t v___x_382_; uint8_t v___x_383_; 
v___x_382_ = 90;
v___x_383_ = lean_uint32_dec_le(v_c_361_, v___x_382_);
if (v___x_383_ == 0)
{
goto v___jp_375_;
}
else
{
lean_dec(v_snd_351_);
lean_dec_ref(v_a_344_);
v_pos_346_ = v_it_x27_363_;
v_res_347_ = v_c_361_;
goto v___jp_345_;
}
}
v___jp_364_:
{
uint32_t v___x_365_; uint8_t v___x_366_; 
v___x_365_ = 43;
v___x_366_ = lean_uint32_dec_eq(v_c_361_, v___x_365_);
if (v___x_366_ == 0)
{
uint32_t v___x_367_; uint8_t v___x_368_; 
v___x_367_ = 45;
v___x_368_ = lean_uint32_dec_eq(v_c_361_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; 
lean_dec_ref_known(v_it_x27_363_, 2);
v___x_369_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__1));
lean_inc(v_snd_351_);
v_pos_353_ = v_a_344_;
v_snd_354_ = v_snd_351_;
v_err_355_ = v___x_369_;
goto v___jp_352_;
}
else
{
lean_dec(v_snd_351_);
lean_dec_ref(v_a_344_);
v_pos_346_ = v_it_x27_363_;
v_res_347_ = v_c_361_;
goto v___jp_345_;
}
}
else
{
lean_dec(v_snd_351_);
lean_dec_ref(v_a_344_);
v_pos_346_ = v_it_x27_363_;
v_res_347_ = v_c_361_;
goto v___jp_345_;
}
}
v___jp_370_:
{
uint32_t v___x_371_; uint8_t v___x_372_; 
v___x_371_ = 48;
v___x_372_ = lean_uint32_dec_le(v___x_371_, v_c_361_);
if (v___x_372_ == 0)
{
goto v___jp_364_;
}
else
{
uint32_t v___x_373_; uint8_t v___x_374_; 
v___x_373_ = 57;
v___x_374_ = lean_uint32_dec_le(v_c_361_, v___x_373_);
if (v___x_374_ == 0)
{
goto v___jp_364_;
}
else
{
lean_dec(v_snd_351_);
lean_dec_ref(v_a_344_);
v_pos_346_ = v_it_x27_363_;
v_res_347_ = v_c_361_;
goto v___jp_345_;
}
}
}
v___jp_375_:
{
uint32_t v___x_376_; uint8_t v___x_377_; 
v___x_376_ = 97;
v___x_377_ = lean_uint32_dec_le(v___x_376_, v_c_361_);
if (v___x_377_ == 0)
{
goto v___jp_370_;
}
else
{
uint32_t v___x_378_; uint8_t v___x_379_; 
v___x_378_ = 122;
v___x_379_ = lean_uint32_dec_le(v_c_361_, v___x_378_);
if (v___x_379_ == 0)
{
goto v___jp_370_;
}
else
{
lean_dec(v_snd_351_);
lean_dec_ref(v_a_344_);
v_pos_346_ = v_it_x27_363_;
v_res_347_ = v_c_361_;
goto v___jp_345_;
}
}
}
}
else
{
lean_object* v___x_384_; 
v___x_384_ = lean_box(0);
lean_inc(v_snd_351_);
v_pos_353_ = v_a_344_;
v_snd_354_ = v_snd_351_;
v_err_355_ = v___x_384_;
goto v___jp_352_;
}
v___jp_345_:
{
lean_object* v___x_348_; 
v___x_348_ = lean_string_push(v_acc_343_, v_res_347_);
v_acc_343_ = v___x_348_;
v_a_344_ = v_pos_346_;
goto _start;
}
v___jp_352_:
{
uint8_t v_decide_356_; 
v_decide_356_ = lean_nat_dec_eq(v_snd_351_, v_snd_354_);
lean_dec(v_snd_354_);
lean_dec(v_snd_351_);
if (v_decide_356_ == 0)
{
lean_object* v___x_357_; 
lean_dec_ref(v_acc_343_);
lean_inc(v_err_355_);
v___x_357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_357_, 0, v_pos_353_);
lean_ctor_set(v___x_357_, 1, v_err_355_);
return v___x_357_;
}
else
{
lean_object* v___x_358_; 
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v_pos_353_);
lean_ctor_set(v___x_358_, 1, v_acc_343_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName(lean_object* v_a_386_){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName___closed__0));
v___x_388_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0(v___x_387_, v_a_386_);
return v___x_388_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(lean_object* v_x_389_, lean_object* v_x_390_){
_start:
{
if (lean_obj_tag(v_x_389_) == 0)
{
if (lean_obj_tag(v_x_390_) == 0)
{
uint8_t v___x_391_; 
v___x_391_ = 1;
return v___x_391_;
}
else
{
uint8_t v___x_392_; 
v___x_392_ = 0;
return v___x_392_;
}
}
else
{
if (lean_obj_tag(v_x_390_) == 0)
{
uint8_t v___x_393_; 
v___x_393_ = 0;
return v___x_393_;
}
else
{
lean_object* v_val_394_; lean_object* v_val_395_; uint32_t v___x_396_; uint32_t v___x_397_; uint8_t v___x_398_; 
v_val_394_ = lean_ctor_get(v_x_389_, 0);
v_val_395_ = lean_ctor_get(v_x_390_, 0);
v___x_396_ = lean_unbox_uint32(v_val_394_);
v___x_397_ = lean_unbox_uint32(v_val_395_);
v___x_398_ = lean_uint32_dec_eq(v___x_396_, v___x_397_);
return v___x_398_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0___boxed(lean_object* v_x_399_, lean_object* v_x_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = l_instBEqOption_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_x_399_, v_x_400_);
lean_dec(v_x_400_);
lean_dec(v_x_399_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1(lean_object* v_acc_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_pos_409_; uint32_t v_res_410_; lean_object* v_fst_413_; lean_object* v_snd_414_; lean_object* v_pos_416_; lean_object* v_snd_417_; lean_object* v_err_418_; lean_object* v___x_424_; uint8_t v_decide_425_; 
v_fst_413_ = lean_ctor_get(v_a_407_, 0);
v_snd_414_ = lean_ctor_get(v_a_407_, 1);
lean_inc(v_snd_414_);
v___x_424_ = lean_string_utf8_byte_size(v_fst_413_);
v_decide_425_ = lean_nat_dec_eq(v_snd_414_, v___x_424_);
if (v_decide_425_ == 0)
{
uint32_t v_c_426_; lean_object* v___x_427_; lean_object* v_it_x27_428_; uint32_t v___x_434_; uint8_t v___x_435_; 
v_c_426_ = lean_string_utf8_get_fast(v_fst_413_, v_snd_414_);
v___x_427_ = lean_string_utf8_next_fast(v_fst_413_, v_snd_414_);
lean_inc(v_fst_413_);
v_it_x27_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_428_, 0, v_fst_413_);
lean_ctor_set(v_it_x27_428_, 1, v___x_427_);
v___x_434_ = 65;
v___x_435_ = lean_uint32_dec_le(v___x_434_, v_c_426_);
if (v___x_435_ == 0)
{
goto v___jp_429_;
}
else
{
uint32_t v___x_436_; uint8_t v___x_437_; 
v___x_436_ = 90;
v___x_437_ = lean_uint32_dec_le(v_c_426_, v___x_436_);
if (v___x_437_ == 0)
{
goto v___jp_429_;
}
else
{
lean_dec(v_snd_414_);
lean_dec_ref(v_a_407_);
v_pos_409_ = v_it_x27_428_;
v_res_410_ = v_c_426_;
goto v___jp_408_;
}
}
v___jp_429_:
{
uint32_t v___x_430_; uint8_t v___x_431_; 
v___x_430_ = 97;
v___x_431_ = lean_uint32_dec_le(v___x_430_, v_c_426_);
if (v___x_431_ == 0)
{
lean_dec_ref_known(v_it_x27_428_, 2);
goto v___jp_422_;
}
else
{
uint32_t v___x_432_; uint8_t v___x_433_; 
v___x_432_ = 122;
v___x_433_ = lean_uint32_dec_le(v_c_426_, v___x_432_);
if (v___x_433_ == 0)
{
lean_dec_ref_known(v_it_x27_428_, 2);
goto v___jp_422_;
}
else
{
lean_dec(v_snd_414_);
lean_dec_ref(v_a_407_);
v_pos_409_ = v_it_x27_428_;
v_res_410_ = v_c_426_;
goto v___jp_408_;
}
}
}
}
else
{
lean_object* v___x_438_; 
v___x_438_ = lean_box(0);
lean_inc(v_snd_414_);
v_pos_416_ = v_a_407_;
v_snd_417_ = v_snd_414_;
v_err_418_ = v___x_438_;
goto v___jp_415_;
}
v___jp_408_:
{
lean_object* v___x_411_; 
v___x_411_ = lean_string_push(v_acc_406_, v_res_410_);
v_acc_406_ = v___x_411_;
v_a_407_ = v_pos_409_;
goto _start;
}
v___jp_415_:
{
uint8_t v_decide_419_; 
v_decide_419_ = lean_nat_dec_eq(v_snd_414_, v_snd_417_);
lean_dec(v_snd_417_);
lean_dec(v_snd_414_);
if (v_decide_419_ == 0)
{
lean_object* v___x_420_; 
lean_dec_ref(v_acc_406_);
lean_inc(v_err_418_);
v___x_420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_420_, 0, v_pos_416_);
lean_ctor_set(v___x_420_, 1, v_err_418_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; 
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v_pos_416_);
lean_ctor_set(v___x_421_, 1, v_acc_406_);
return v___x_421_;
}
}
v___jp_422_:
{
lean_object* v___x_423_; 
v___x_423_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__1));
lean_inc(v_snd_414_);
v_pos_416_ = v_a_407_;
v_snd_417_ = v_snd_414_;
v_err_418_ = v___x_423_;
goto v___jp_415_;
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_439_; lean_object* v___x_440_; 
v___x_439_ = 60;
v___x_440_ = lean_box_uint32(v___x_439_);
return v___x_440_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0___boxed__const__1;
v___x_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(lean_object* v_a_446_){
_start:
{
lean_object* v___y_448_; lean_object* v_pos_452_; lean_object* v_res_453_; lean_object* v_fst_507_; lean_object* v_snd_508_; lean_object* v___x_509_; uint8_t v_decide_510_; 
v_fst_507_ = lean_ctor_get(v_a_446_, 0);
v_snd_508_ = lean_ctor_get(v_a_446_, 1);
v___x_509_ = lean_string_utf8_byte_size(v_fst_507_);
v_decide_510_ = lean_nat_dec_eq(v_snd_508_, v___x_509_);
if (v_decide_510_ == 0)
{
uint32_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_511_ = lean_string_utf8_get_fast(v_fst_507_, v_snd_508_);
v___x_512_ = lean_box_uint32(v___x_511_);
v___x_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
v_pos_452_ = v_a_446_;
v_res_453_ = v___x_513_;
goto v___jp_451_;
}
else
{
lean_object* v___x_514_; 
v___x_514_ = lean_box(0);
v_pos_452_ = v_a_446_;
v_res_453_ = v___x_514_;
goto v___jp_451_;
}
v___jp_447_:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_box(0);
v___x_450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_450_, 0, v___y_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
return v___x_450_;
}
v___jp_451_:
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0);
v___x_455_ = l_instBEqOption_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_res_453_, v___x_454_);
lean_dec(v_res_453_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName___closed__0));
v___x_457_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1(v___x_456_, v_pos_452_);
return v___x_457_;
}
else
{
lean_object* v_fst_458_; lean_object* v_snd_459_; lean_object* v___x_460_; uint8_t v_decide_461_; 
v_fst_458_ = lean_ctor_get(v_pos_452_, 0);
v_snd_459_ = lean_ctor_get(v_pos_452_, 1);
v___x_460_ = lean_string_utf8_byte_size(v_fst_458_);
v_decide_461_ = lean_nat_dec_eq(v_snd_459_, v___x_460_);
if (v_decide_461_ == 0)
{
if (v___x_455_ == 0)
{
v___y_448_ = v_pos_452_;
goto v___jp_447_;
}
else
{
lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_504_; 
lean_inc(v_snd_459_);
lean_inc(v_fst_458_);
v_isSharedCheck_504_ = !lean_is_exclusive(v_pos_452_);
if (v_isSharedCheck_504_ == 0)
{
lean_object* v_unused_505_; lean_object* v_unused_506_; 
v_unused_505_ = lean_ctor_get(v_pos_452_, 1);
lean_dec(v_unused_505_);
v_unused_506_ = lean_ctor_get(v_pos_452_, 0);
lean_dec(v_unused_506_);
v___x_463_ = v_pos_452_;
v_isShared_464_ = v_isSharedCheck_504_;
goto v_resetjp_462_;
}
else
{
lean_dec(v_pos_452_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_504_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_465_ = lean_string_utf8_next_fast(v_fst_458_, v_snd_459_);
lean_dec(v_snd_459_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v___x_465_);
v___x_467_ = v___x_463_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_fst_458_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v___x_465_);
v___x_467_ = v_reuseFailAlloc_503_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_468_; 
v___x_468_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName(v___x_467_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_pos_469_; lean_object* v_res_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_502_; 
v_pos_469_ = lean_ctor_get(v___x_468_, 0);
v_res_470_ = lean_ctor_get(v___x_468_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_502_ == 0)
{
v___x_472_ = v___x_468_;
v_isShared_473_ = v_isSharedCheck_502_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_res_470_);
lean_inc(v_pos_469_);
lean_dec(v___x_468_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_502_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v_fst_474_; lean_object* v_snd_475_; lean_object* v___x_476_; uint8_t v_decide_477_; 
v_fst_474_ = lean_ctor_get(v_pos_469_, 0);
v_snd_475_ = lean_ctor_get(v_pos_469_, 1);
v___x_476_ = lean_string_utf8_byte_size(v_fst_474_);
v_decide_477_ = lean_nat_dec_eq(v_snd_475_, v___x_476_);
if (v_decide_477_ == 0)
{
uint32_t v___x_478_; uint32_t v_c_479_; uint8_t v___x_480_; 
v___x_478_ = 62;
v_c_479_ = lean_string_utf8_get_fast(v_fst_474_, v_snd_475_);
v___x_480_ = lean_uint32_dec_eq(v_c_479_, v___x_478_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_483_; 
lean_dec(v_res_470_);
v___x_481_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2));
if (v_isShared_473_ == 0)
{
lean_ctor_set_tag(v___x_472_, 1);
lean_ctor_set(v___x_472_, 1, v___x_481_);
v___x_483_ = v___x_472_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_pos_469_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
else
{
lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_495_; 
lean_inc(v_snd_475_);
lean_inc(v_fst_474_);
v_isSharedCheck_495_ = !lean_is_exclusive(v_pos_469_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; lean_object* v_unused_497_; 
v_unused_496_ = lean_ctor_get(v_pos_469_, 1);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v_pos_469_, 0);
lean_dec(v_unused_497_);
v___x_486_ = v_pos_469_;
v_isShared_487_ = v_isSharedCheck_495_;
goto v_resetjp_485_;
}
else
{
lean_dec(v_pos_469_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_495_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v_it_x27_490_; 
v___x_488_ = lean_string_utf8_next_fast(v_fst_474_, v_snd_475_);
lean_dec(v_snd_475_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 1, v___x_488_);
v_it_x27_490_ = v___x_486_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_fst_474_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v___x_488_);
v_it_x27_490_ = v_reuseFailAlloc_494_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v_it_x27_490_);
v___x_492_ = v___x_472_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_it_x27_490_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_res_470_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
else
{
lean_object* v___x_498_; lean_object* v___x_500_; 
lean_dec(v_res_470_);
v___x_498_ = lean_box(0);
if (v_isShared_473_ == 0)
{
lean_ctor_set_tag(v___x_472_, 1);
lean_ctor_set(v___x_472_, 1, v___x_498_);
v___x_500_ = v___x_472_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_pos_469_);
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
else
{
return v___x_468_;
}
}
}
}
}
else
{
v___y_448_ = v_pos_452_;
goto v___jp_447_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1(lean_object* v___x_515_, lean_object* v_x_516_){
_start:
{
uint8_t v___x_517_; 
v___x_517_ = lean_int_dec_le(v_x_516_, v___x_515_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1___boxed(lean_object* v___x_518_, lean_object* v_x_519_){
_start:
{
uint8_t v_res_520_; lean_object* v_r_521_; 
v_res_520_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1(v___x_518_, v_x_519_);
lean_dec(v_x_519_);
lean_dec(v___x_518_);
v_r_521_ = lean_box(v_res_520_);
return v_r_521_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_unsigned_to_nat(7u);
v___x_528_ = lean_nat_to_int(v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(5u);
v___x_530_ = lean_nat_to_int(v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6(void){
_start:
{
lean_object* v___x_531_; lean_object* v___f_532_; 
v___x_531_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5);
v___f_532_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1___boxed), 2, 1);
lean_closure_set(v___f_532_, 0, v___x_531_);
return v___f_532_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_unsigned_to_nat(12u);
v___x_538_ = lean_nat_to_int(v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec(lean_object* v_a_540_){
_start:
{
lean_object* v___y_542_; lean_object* v___y_546_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_560_; lean_object* v_fst_563_; lean_object* v_snd_564_; lean_object* v___x_565_; uint8_t v_decide_566_; 
v_fst_563_ = lean_ctor_get(v_a_540_, 0);
v_snd_564_ = lean_ctor_get(v_a_540_, 1);
v___x_565_ = lean_string_utf8_byte_size(v_fst_563_);
v_decide_566_ = lean_nat_dec_eq(v_snd_564_, v___x_565_);
if (v_decide_566_ == 0)
{
uint32_t v___x_567_; uint32_t v_c_568_; uint8_t v___x_569_; 
v___x_567_ = 77;
v_c_568_ = lean_string_utf8_get_fast(v_fst_563_, v_snd_564_);
v___x_569_ = lean_uint32_dec_eq(v_c_568_, v___x_567_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3));
v___x_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_571_, 0, v_a_540_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
return v___x_571_;
}
else
{
lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_724_; 
lean_inc(v_snd_564_);
lean_inc(v_fst_563_);
v_isSharedCheck_724_ = !lean_is_exclusive(v_a_540_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; lean_object* v_unused_726_; 
v_unused_725_ = lean_ctor_get(v_a_540_, 1);
lean_dec(v_unused_725_);
v_unused_726_ = lean_ctor_get(v_a_540_, 0);
lean_dec(v_unused_726_);
v___x_573_ = v_a_540_;
v_isShared_574_ = v_isSharedCheck_724_;
goto v_resetjp_572_;
}
else
{
lean_dec(v_a_540_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_724_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___f_576_; lean_object* v___x_577_; lean_object* v_it_x27_579_; 
v___x_575_ = lean_box(v___x_569_);
v___f_576_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_576_, 0, v___x_575_);
v___x_577_ = lean_string_utf8_next_fast(v_fst_563_, v_snd_564_);
lean_dec(v_snd_564_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 1, v___x_577_);
v_it_x27_579_ = v___x_573_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_fst_563_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_577_);
v_it_x27_579_ = v_reuseFailAlloc_723_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_593_; lean_object* v_pos_594_; lean_object* v_fst_595_; lean_object* v_snd_596_; lean_object* v_res_597_; lean_object* v_pos_633_; lean_object* v_res_634_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_580_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_679_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10);
v___x_680_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11));
v___x_681_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_580_, v___x_679_, v___x_680_, v___f_576_, v_it_x27_579_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_pos_682_; lean_object* v_res_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_711_; 
v_pos_682_ = lean_ctor_get(v___x_681_, 0);
v_res_683_ = lean_ctor_get(v___x_681_, 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_711_ == 0)
{
v___x_685_ = v___x_681_;
v_isShared_686_ = v_isSharedCheck_711_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_res_683_);
lean_inc(v_pos_682_);
lean_dec(v___x_681_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_711_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v_fst_692_; lean_object* v_snd_693_; lean_object* v___x_694_; uint8_t v_decide_695_; 
v_fst_692_ = lean_ctor_get(v_pos_682_, 0);
v_snd_693_ = lean_ctor_get(v_pos_682_, 1);
v___x_694_ = lean_string_utf8_byte_size(v_fst_692_);
v_decide_695_ = lean_nat_dec_eq(v_snd_693_, v___x_694_);
if (v_decide_695_ == 0)
{
if (v___x_569_ == 0)
{
lean_dec(v_res_683_);
goto v___jp_687_;
}
else
{
uint32_t v___x_696_; uint32_t v_c_697_; uint8_t v___x_698_; 
lean_del_object(v___x_685_);
v___x_696_ = 46;
v_c_697_ = lean_string_utf8_get_fast(v_fst_692_, v_snd_693_);
v___x_698_ = lean_uint32_dec_eq(v_c_697_, v___x_696_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; 
lean_dec(v_res_683_);
v___x_699_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9));
v___x_700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_700_, 0, v_pos_682_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
return v___x_700_;
}
else
{
lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_708_; 
lean_inc(v_snd_693_);
lean_inc(v_fst_692_);
v_isSharedCheck_708_ = !lean_is_exclusive(v_pos_682_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; lean_object* v_unused_710_; 
v_unused_709_ = lean_ctor_get(v_pos_682_, 1);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_pos_682_, 0);
lean_dec(v_unused_710_);
v___x_702_ = v_pos_682_;
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
else
{
lean_dec(v_pos_682_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v_it_x27_706_; 
v___x_704_ = lean_string_utf8_next_fast(v_fst_692_, v_snd_693_);
lean_dec(v_snd_693_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v___x_704_);
v_it_x27_706_ = v___x_702_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_fst_692_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_704_);
v_it_x27_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
v_pos_633_ = v_it_x27_706_;
v_res_634_ = v_res_683_;
goto v___jp_632_;
}
}
}
}
}
else
{
lean_dec(v_res_683_);
goto v___jp_687_;
}
v___jp_687_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = lean_box(0);
if (v_isShared_686_ == 0)
{
lean_ctor_set_tag(v___x_685_, 1);
lean_ctor_set(v___x_685_, 1, v___x_688_);
v___x_690_ = v___x_685_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_pos_682_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_pos_712_; lean_object* v_res_713_; 
v_pos_712_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_pos_712_);
v_res_713_ = lean_ctor_get(v___x_681_, 1);
lean_inc(v_res_713_);
lean_dec_ref_known(v___x_681_, 2);
v_pos_633_ = v_pos_712_;
v_res_634_ = v_res_713_;
goto v___jp_632_;
}
else
{
lean_object* v_pos_714_; lean_object* v_err_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
v_pos_714_ = lean_ctor_get(v___x_681_, 0);
v_err_715_ = lean_ctor_get(v___x_681_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_681_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_err_715_);
lean_inc(v_pos_714_);
lean_dec(v___x_681_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_pos_714_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_err_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
v___jp_581_:
{
uint8_t v___x_588_; 
v___x_588_ = lean_int_dec_le(v___x_580_, v___y_587_);
if (v___x_588_ == 0)
{
lean_dec(v___y_587_);
lean_dec(v___y_586_);
lean_dec(v___y_584_);
lean_dec(v___y_582_);
v___y_550_ = v___y_583_;
v___y_551_ = v___y_585_;
goto v___jp_549_;
}
else
{
uint8_t v___x_589_; 
v___x_589_ = lean_int_dec_le(v___y_587_, v___y_584_);
lean_dec(v___y_584_);
if (v___x_589_ == 0)
{
lean_dec(v___y_587_);
lean_dec(v___y_586_);
lean_dec(v___y_582_);
v___y_550_ = v___y_583_;
v___y_551_ = v___y_585_;
goto v___jp_549_;
}
else
{
lean_object* v___x_590_; lean_object* v___x_591_; 
lean_dec(v___y_585_);
v___x_590_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_590_, 0, v___y_586_);
lean_ctor_set(v___x_590_, 1, v___y_582_);
lean_ctor_set(v___x_590_, 2, v___y_587_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v___y_583_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
return v___x_591_;
}
}
}
v___jp_592_:
{
lean_object* v___x_598_; uint8_t v_decide_599_; 
v___x_598_ = lean_string_utf8_byte_size(v_fst_595_);
v_decide_599_ = lean_nat_dec_eq(v_snd_596_, v___x_598_);
if (v_decide_599_ == 0)
{
if (v___x_569_ == 0)
{
lean_dec(v_res_597_);
lean_dec(v_snd_596_);
lean_dec(v_fst_595_);
lean_dec(v___y_593_);
v___y_546_ = v_pos_594_;
goto v___jp_545_;
}
else
{
uint32_t v_c_600_; uint32_t v___x_601_; uint8_t v___x_602_; 
v_c_600_ = lean_string_utf8_get_fast(v_fst_595_, v_snd_596_);
v___x_601_ = 48;
v___x_602_ = lean_uint32_dec_le(v___x_601_, v_c_600_);
if (v___x_602_ == 0)
{
lean_dec(v_res_597_);
lean_dec(v_snd_596_);
lean_dec(v_fst_595_);
lean_dec(v___y_593_);
v___y_542_ = v_pos_594_;
goto v___jp_541_;
}
else
{
uint32_t v___x_603_; uint8_t v___x_604_; 
v___x_603_ = 57;
v___x_604_ = lean_uint32_dec_le(v_c_600_, v___x_603_);
if (v___x_604_ == 0)
{
lean_dec(v_res_597_);
lean_dec(v_snd_596_);
lean_dec(v_fst_595_);
lean_dec(v___y_593_);
v___y_542_ = v_pos_594_;
goto v___jp_541_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v_fst_610_; lean_object* v_snd_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref(v_pos_594_);
v___x_605_ = lean_string_utf8_next_fast(v_fst_595_, v_snd_596_);
lean_dec(v_snd_596_);
v___x_606_ = lean_uint32_to_nat(v_c_600_);
v___x_607_ = lean_unsigned_to_nat(48u);
v___x_608_ = lean_nat_sub(v___x_606_, v___x_607_);
lean_dec(v___x_606_);
v___x_609_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_595_, v___x_605_, v___x_608_);
v_fst_610_ = lean_ctor_get(v___x_609_, 0);
v_snd_611_ = lean_ctor_get(v___x_609_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_631_ == 0)
{
v___x_613_ = v___x_609_;
v_isShared_614_ = v_isSharedCheck_631_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_snd_611_);
lean_inc(v_fst_610_);
lean_dec(v___x_609_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_631_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v_fst_595_);
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_fst_595_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_snd_611_);
v___x_616_ = v_reuseFailAlloc_630_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = lean_unsigned_to_nat(6u);
v___x_618_ = lean_nat_dec_lt(v___x_617_, v_fst_610_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_619_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4);
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_nat_dec_eq(v_fst_610_, v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; 
lean_inc(v_fst_610_);
v___x_622_ = lean_nat_to_int(v_fst_610_);
v___y_582_ = v_res_597_;
v___y_583_ = v___x_616_;
v___y_584_ = v___x_619_;
v___y_585_ = v_fst_610_;
v___y_586_ = v___y_593_;
v___y_587_ = v___x_622_;
goto v___jp_581_;
}
else
{
v___y_582_ = v_res_597_;
v___y_583_ = v___x_616_;
v___y_584_ = v___x_619_;
v___y_585_ = v_fst_610_;
v___y_586_ = v___y_593_;
v___y_587_ = v___x_619_;
goto v___jp_581_;
}
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec(v_res_597_);
lean_dec(v___y_593_);
v___x_623_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0));
v___x_624_ = l_Nat_reprFast(v_fst_610_);
v___x_625_ = lean_string_append(v___x_623_, v___x_624_);
lean_dec_ref(v___x_624_);
v___x_626_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1));
v___x_627_ = lean_string_append(v___x_625_, v___x_626_);
v___x_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
v___x_629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_616_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
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
lean_dec(v_res_597_);
lean_dec(v_snd_596_);
lean_dec(v_fst_595_);
lean_dec(v___y_593_);
v___y_546_ = v_pos_594_;
goto v___jp_545_;
}
}
v___jp_632_:
{
lean_object* v___x_635_; lean_object* v___f_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_635_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5);
v___f_636_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6);
v___x_637_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7));
v___x_638_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_580_, v___x_635_, v___x_637_, v___f_636_, v_pos_633_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_pos_639_; lean_object* v_res_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_665_; 
v_pos_639_ = lean_ctor_get(v___x_638_, 0);
v_res_640_ = lean_ctor_get(v___x_638_, 1);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_665_ == 0)
{
v___x_642_ = v___x_638_;
v_isShared_643_ = v_isSharedCheck_665_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_res_640_);
lean_inc(v_pos_639_);
lean_dec(v___x_638_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_665_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_fst_644_; lean_object* v_snd_645_; lean_object* v___x_646_; uint8_t v_decide_647_; 
v_fst_644_ = lean_ctor_get(v_pos_639_, 0);
v_snd_645_ = lean_ctor_get(v_pos_639_, 1);
v___x_646_ = lean_string_utf8_byte_size(v_fst_644_);
v_decide_647_ = lean_nat_dec_eq(v_snd_645_, v___x_646_);
if (v_decide_647_ == 0)
{
if (v___x_569_ == 0)
{
lean_del_object(v___x_642_);
lean_dec(v_res_640_);
lean_dec(v_res_634_);
v___y_560_ = v_pos_639_;
goto v___jp_559_;
}
else
{
uint32_t v___x_648_; uint32_t v_c_649_; uint8_t v___x_650_; 
v___x_648_ = 46;
v_c_649_ = lean_string_utf8_get_fast(v_fst_644_, v_snd_645_);
v___x_650_ = lean_uint32_dec_eq(v_c_649_, v___x_648_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_653_; 
lean_dec(v_res_640_);
lean_dec(v_res_634_);
v___x_651_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9));
if (v_isShared_643_ == 0)
{
lean_ctor_set_tag(v___x_642_, 1);
lean_ctor_set(v___x_642_, 1, v___x_651_);
v___x_653_ = v___x_642_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_pos_639_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v___x_651_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
else
{
lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_662_; 
lean_inc(v_snd_645_);
lean_inc(v_fst_644_);
lean_del_object(v___x_642_);
v_isSharedCheck_662_ = !lean_is_exclusive(v_pos_639_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; lean_object* v_unused_664_; 
v_unused_663_ = lean_ctor_get(v_pos_639_, 1);
lean_dec(v_unused_663_);
v_unused_664_ = lean_ctor_get(v_pos_639_, 0);
lean_dec(v_unused_664_);
v___x_656_ = v_pos_639_;
v_isShared_657_ = v_isSharedCheck_662_;
goto v_resetjp_655_;
}
else
{
lean_dec(v_pos_639_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_662_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v_it_x27_660_; 
v___x_658_ = lean_string_utf8_next_fast(v_fst_644_, v_snd_645_);
lean_dec(v_snd_645_);
lean_inc(v_fst_644_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 1, v___x_658_);
v_it_x27_660_ = v___x_656_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_fst_644_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v___x_658_);
v_it_x27_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
v___y_593_ = v_res_634_;
v_pos_594_ = v_it_x27_660_;
v_fst_595_ = v_fst_644_;
v_snd_596_ = v___x_658_;
v_res_597_ = v_res_640_;
goto v___jp_592_;
}
}
}
}
}
else
{
lean_del_object(v___x_642_);
lean_dec(v_res_640_);
lean_dec(v_res_634_);
v___y_560_ = v_pos_639_;
goto v___jp_559_;
}
}
}
else
{
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_pos_666_; lean_object* v_res_667_; lean_object* v_fst_668_; lean_object* v_snd_669_; 
v_pos_666_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_pos_666_);
v_res_667_ = lean_ctor_get(v___x_638_, 1);
lean_inc(v_res_667_);
lean_dec_ref_known(v___x_638_, 2);
v_fst_668_ = lean_ctor_get(v_pos_666_, 0);
lean_inc(v_fst_668_);
v_snd_669_ = lean_ctor_get(v_pos_666_, 1);
lean_inc(v_snd_669_);
v___y_593_ = v_res_634_;
v_pos_594_ = v_pos_666_;
v_fst_595_ = v_fst_668_;
v_snd_596_ = v_snd_669_;
v_res_597_ = v_res_667_;
goto v___jp_592_;
}
else
{
lean_object* v_pos_670_; lean_object* v_err_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec(v_res_634_);
v_pos_670_ = lean_ctor_get(v___x_638_, 0);
v_err_671_ = lean_ctor_get(v___x_638_, 1);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_638_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_err_671_);
lean_inc(v_pos_670_);
lean_dec(v___x_638_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_pos_670_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_err_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
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
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_box(0);
v___x_728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_728_, 0, v_a_540_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
return v___x_728_;
}
v___jp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__1));
v___x_544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_544_, 0, v___y_542_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
return v___x_544_;
}
v___jp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_box(0);
v___x_548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_548_, 0, v___y_546_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
return v___x_548_;
}
v___jp_549_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_552_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0));
v___x_553_ = l_Nat_reprFast(v___y_551_);
v___x_554_ = lean_string_append(v___x_552_, v___x_553_);
lean_dec_ref(v___x_553_);
v___x_555_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1));
v___x_556_ = lean_string_append(v___x_554_, v___x_555_);
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
v___x_558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_558_, 0, v___y_550_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
return v___x_558_;
}
v___jp_559_:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_box(0);
v___x_562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_562_, 0, v___y_560_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
return v___x_562_;
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_unsigned_to_nat(365u);
v___x_733_ = lean_nat_to_int(v___x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec(lean_object* v_a_735_){
_start:
{
lean_object* v_fst_736_; lean_object* v_snd_737_; lean_object* v___x_738_; uint8_t v_decide_739_; 
v_fst_736_ = lean_ctor_get(v_a_735_, 0);
v_snd_737_ = lean_ctor_get(v_a_735_, 1);
v___x_738_ = lean_string_utf8_byte_size(v_fst_736_);
v_decide_739_ = lean_nat_dec_eq(v_snd_737_, v___x_738_);
if (v_decide_739_ == 0)
{
uint32_t v___x_740_; uint32_t v_c_741_; uint8_t v___x_742_; 
v___x_740_ = 74;
v_c_741_ = lean_string_utf8_get_fast(v_fst_736_, v_snd_737_);
v___x_742_ = lean_uint32_dec_eq(v_c_741_, v___x_740_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1));
v___x_744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_744_, 0, v_a_735_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
return v___x_744_;
}
else
{
lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_777_; 
lean_inc(v_snd_737_);
lean_inc(v_fst_736_);
v_isSharedCheck_777_ = !lean_is_exclusive(v_a_735_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; lean_object* v_unused_779_; 
v_unused_778_ = lean_ctor_get(v_a_735_, 1);
lean_dec(v_unused_778_);
v_unused_779_ = lean_ctor_get(v_a_735_, 0);
lean_dec(v_unused_779_);
v___x_746_ = v_a_735_;
v_isShared_747_ = v_isSharedCheck_777_;
goto v_resetjp_745_;
}
else
{
lean_dec(v_a_735_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_777_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___f_749_; lean_object* v___x_750_; lean_object* v_it_x27_752_; 
v___x_748_ = lean_box(v___x_742_);
v___f_749_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_749_, 0, v___x_748_);
v___x_750_ = lean_string_utf8_next_fast(v_fst_736_, v_snd_737_);
lean_dec(v_snd_737_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v___x_750_);
v_it_x27_752_ = v___x_746_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_fst_736_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_750_);
v_it_x27_752_ = v_reuseFailAlloc_776_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_753_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_754_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2);
v___x_755_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3));
v___x_756_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_753_, v___x_754_, v___x_755_, v___f_749_, v_it_x27_752_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_pos_757_; lean_object* v_res_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_766_; 
v_pos_757_ = lean_ctor_get(v___x_756_, 0);
v_res_758_ = lean_ctor_get(v___x_756_, 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_766_ == 0)
{
v___x_760_ = v___x_756_;
v_isShared_761_ = v_isSharedCheck_766_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_res_758_);
lean_inc(v_pos_757_);
lean_dec(v___x_756_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_766_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_762_, 0, v_res_758_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v___x_762_);
v___x_764_ = v___x_760_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_pos_757_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
else
{
lean_object* v_pos_767_; lean_object* v_err_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
v_pos_767_ = lean_ctor_get(v___x_756_, 0);
v_err_768_ = lean_ctor_get(v___x_756_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_756_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_err_768_);
lean_inc(v_pos_767_);
lean_dec(v___x_756_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_pos_767_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_err_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_box(0);
v___x_781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_781_, 0, v_a_735_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
return v___x_781_;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0(lean_object* v_x_782_){
_start:
{
uint8_t v___x_783_; 
v___x_783_ = 1;
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0___boxed(lean_object* v_x_784_){
_start:
{
uint8_t v_res_785_; lean_object* v_r_786_; 
v_res_785_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0(v_x_784_);
lean_dec(v_x_784_);
v_r_786_ = lean_box(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec(lean_object* v_a_789_){
_start:
{
lean_object* v___f_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___f_790_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__0));
v___x_791_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___x_792_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2);
v___x_793_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__1));
v___x_794_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_791_, v___x_792_, v___x_793_, v___f_790_, v_a_789_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_pos_795_; lean_object* v_res_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_804_; 
v_pos_795_ = lean_ctor_get(v___x_794_, 0);
v_res_796_ = lean_ctor_get(v___x_794_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_804_ == 0)
{
v___x_798_ = v___x_794_;
v_isShared_799_ = v_isSharedCheck_804_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_res_796_);
lean_inc(v_pos_795_);
lean_dec(v___x_794_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_804_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_800_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_800_, 0, v_res_796_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 1, v___x_800_);
v___x_802_ = v___x_798_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_pos_795_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
else
{
lean_object* v_pos_805_; lean_object* v_err_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
v_pos_805_ = lean_ctor_get(v___x_794_, 0);
v_err_806_ = lean_ctor_get(v___x_794_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_794_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_err_806_);
lean_inc(v_pos_805_);
lean_dec(v___x_794_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_pos_805_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_err_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(lean_object* v_stdOffset_814_, lean_object* v_a_815_){
_start:
{
lean_object* v_fst_816_; lean_object* v_snd_817_; lean_object* v___x_818_; uint8_t v_decide_819_; 
v_fst_816_ = lean_ctor_get(v_a_815_, 0);
v_snd_817_ = lean_ctor_get(v_a_815_, 1);
v___x_818_ = lean_string_utf8_byte_size(v_fst_816_);
v_decide_819_ = lean_nat_dec_eq(v_snd_817_, v___x_818_);
if (v_decide_819_ == 0)
{
uint32_t v___x_820_; uint32_t v___x_831_; uint8_t v___x_832_; 
v___x_820_ = lean_string_utf8_get_fast(v_fst_816_, v_snd_817_);
v___x_831_ = 48;
v___x_832_ = lean_uint32_dec_le(v___x_831_, v___x_820_);
if (v___x_832_ == 0)
{
goto v___jp_821_;
}
else
{
uint32_t v___x_833_; uint8_t v___x_834_; 
v___x_833_ = 57;
v___x_834_ = lean_uint32_dec_le(v___x_820_, v___x_833_);
if (v___x_834_ == 0)
{
goto v___jp_821_;
}
else
{
lean_object* v___x_835_; 
v___x_835_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_815_);
return v___x_835_;
}
}
v___jp_821_:
{
uint32_t v___x_822_; uint8_t v___x_823_; 
v___x_822_ = 43;
v___x_823_ = lean_uint32_dec_eq(v___x_820_, v___x_822_);
if (v___x_823_ == 0)
{
uint32_t v___x_824_; uint8_t v___x_825_; 
v___x_824_ = 45;
v___x_825_ = lean_uint32_dec_eq(v___x_820_, v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_826_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_827_ = lean_int_add(v_stdOffset_814_, v___x_826_);
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v_a_815_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
return v___x_828_;
}
else
{
lean_object* v___x_829_; 
v___x_829_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_815_);
return v___x_829_;
}
}
else
{
lean_object* v___x_830_; 
v___x_830_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_815_);
return v___x_830_;
}
}
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_836_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_837_ = lean_int_add(v_stdOffset_814_, v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v_a_815_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
return v___x_838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset___boxed(lean_object* v_stdOffset_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(v_stdOffset_839_, v_a_840_);
lean_dec(v_stdOffset_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSpec(lean_object* v_a_842_){
_start:
{
lean_object* v_snd_844_; lean_object* v___y_845_; lean_object* v_pos_846_; lean_object* v_snd_847_; lean_object* v___y_851_; lean_object* v_pos_852_; lean_object* v___x_868_; 
lean_inc_ref(v_a_842_);
v___x_868_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec(v_a_842_);
if (lean_obj_tag(v___x_868_) == 0)
{
if (lean_obj_tag(v___x_868_) == 0)
{
lean_dec_ref(v_a_842_);
return v___x_868_;
}
else
{
lean_object* v_pos_869_; 
v_pos_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_pos_869_);
v___y_851_ = v___x_868_;
v_pos_852_ = v_pos_869_;
goto v___jp_850_;
}
}
else
{
lean_object* v_err_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
v_err_870_ = lean_ctor_get(v___x_868_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_877_ == 0)
{
lean_object* v_unused_878_; 
v_unused_878_ = lean_ctor_get(v___x_868_, 0);
lean_dec(v_unused_878_);
v___x_872_ = v___x_868_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_err_870_);
lean_dec(v___x_868_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
lean_inc_ref(v_a_842_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v_a_842_);
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_842_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_err_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_inc_ref(v_a_842_);
v___y_851_ = v___x_875_;
v_pos_852_ = v_a_842_;
goto v___jp_850_;
}
}
}
v___jp_843_:
{
uint8_t v_decide_848_; 
v_decide_848_ = lean_nat_dec_eq(v_snd_844_, v_snd_847_);
lean_dec(v_snd_847_);
lean_dec(v_snd_844_);
if (v_decide_848_ == 0)
{
lean_dec_ref(v_pos_846_);
return v___y_845_;
}
else
{
lean_object* v___x_849_; 
lean_dec_ref(v___y_845_);
v___x_849_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec(v_pos_846_);
return v___x_849_;
}
}
v___jp_850_:
{
lean_object* v_snd_853_; lean_object* v_snd_854_; uint8_t v_decide_855_; 
v_snd_853_ = lean_ctor_get(v_a_842_, 1);
lean_inc(v_snd_853_);
lean_dec_ref(v_a_842_);
v_snd_854_ = lean_ctor_get(v_pos_852_, 1);
lean_inc(v_snd_854_);
v_decide_855_ = lean_nat_dec_eq(v_snd_853_, v_snd_854_);
lean_dec(v_snd_853_);
if (v_decide_855_ == 0)
{
lean_dec(v_snd_854_);
lean_dec_ref(v_pos_852_);
return v___y_851_;
}
else
{
lean_object* v___x_856_; 
lean_dec_ref(v___y_851_);
lean_inc_ref(v_pos_852_);
v___x_856_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec(v_pos_852_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_dec_ref(v_pos_852_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_dec(v_snd_854_);
return v___x_856_;
}
else
{
lean_object* v_pos_857_; lean_object* v_snd_858_; 
v_pos_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_pos_857_);
v_snd_858_ = lean_ctor_get(v_pos_857_, 1);
lean_inc(v_snd_858_);
v_snd_844_ = v_snd_854_;
v___y_845_ = v___x_856_;
v_pos_846_ = v_pos_857_;
v_snd_847_ = v_snd_858_;
goto v___jp_843_;
}
}
else
{
lean_object* v_err_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
v_err_859_ = lean_ctor_get(v___x_856_, 1);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; 
v_unused_867_ = lean_ctor_get(v___x_856_, 0);
lean_dec(v_unused_867_);
v___x_861_ = v___x_856_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_err_859_);
lean_dec(v___x_856_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
lean_inc_ref(v_pos_852_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v_pos_852_);
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_pos_852_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_err_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_inc(v_snd_854_);
v_snd_844_ = v_snd_854_;
v___y_845_ = v___x_864_;
v_pos_846_ = v_pos_852_;
v_snd_847_ = v_snd_854_;
goto v___jp_843_;
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
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_unsigned_to_nat(2u);
v___x_880_ = lean_nat_to_int(v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_881_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3);
v___x_882_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0);
v___x_883_ = lean_int_mul(v___x_882_, v___x_881_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(uint8_t v_extended_887_, lean_object* v_a_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSpec(v_a_888_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_pos_890_; lean_object* v_res_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_935_; 
v_pos_890_ = lean_ctor_get(v___x_889_, 0);
v_res_891_ = lean_ctor_get(v___x_889_, 1);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_935_ == 0)
{
v___x_893_ = v___x_889_;
v_isShared_894_ = v_isSharedCheck_935_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_res_891_);
lean_inc(v_pos_890_);
lean_dec(v___x_889_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_935_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v_pos_896_; lean_object* v_res_897_; lean_object* v_fst_902_; lean_object* v_snd_903_; lean_object* v_pos_905_; lean_object* v_snd_906_; lean_object* v_err_907_; lean_object* v___x_911_; uint8_t v_decide_912_; 
v_fst_902_ = lean_ctor_get(v_pos_890_, 0);
v_snd_903_ = lean_ctor_get(v_pos_890_, 1);
lean_inc(v_snd_903_);
v___x_911_ = lean_string_utf8_byte_size(v_fst_902_);
v_decide_912_ = lean_nat_dec_eq(v_snd_903_, v___x_911_);
if (v_decide_912_ == 0)
{
uint32_t v___x_913_; uint32_t v_c_914_; uint8_t v___x_915_; 
v___x_913_ = 47;
v_c_914_ = lean_string_utf8_get_fast(v_fst_902_, v_snd_903_);
v___x_915_ = lean_uint32_dec_eq(v_c_914_, v___x_913_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; 
v___x_916_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3));
lean_inc(v_snd_903_);
v_pos_905_ = v_pos_890_;
v_snd_906_ = v_snd_903_;
v_err_907_ = v___x_916_;
goto v___jp_904_;
}
else
{
lean_object* v___x_917_; lean_object* v_it_x27_918_; lean_object* v___x_919_; 
v___x_917_ = lean_string_utf8_next_fast(v_fst_902_, v_snd_903_);
lean_inc(v_fst_902_);
v_it_x27_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_918_, 0, v_fst_902_);
lean_ctor_set(v_it_x27_918_, 1, v___x_917_);
v___x_919_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(v_it_x27_918_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_pos_920_; lean_object* v_res_921_; lean_object* v___y_923_; 
v_pos_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_pos_920_);
v_res_921_ = lean_ctor_get(v___x_919_, 1);
lean_inc(v_res_921_);
lean_dec_ref_known(v___x_919_, 2);
if (v_extended_887_ == 0)
{
lean_object* v___x_931_; 
v___x_931_ = lean_unsigned_to_nat(24u);
v___y_923_ = v___x_931_;
goto v___jp_922_;
}
else
{
lean_object* v___x_932_; 
v___x_932_ = lean_unsigned_to_nat(167u);
v___y_923_ = v___x_932_;
goto v___jp_922_;
}
v___jp_922_:
{
lean_object* v___x_924_; 
v___x_924_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(v___y_923_, v_pos_920_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_pos_925_; lean_object* v_res_926_; lean_object* v___x_927_; 
lean_dec(v_snd_903_);
lean_dec(v_pos_890_);
v_pos_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_pos_925_);
v_res_926_ = lean_ctor_get(v___x_924_, 1);
lean_inc(v_res_926_);
lean_dec_ref_known(v___x_924_, 2);
v___x_927_ = lean_int_mul(v_res_921_, v_res_926_);
lean_dec(v_res_926_);
lean_dec(v_res_921_);
v_pos_896_ = v_pos_925_;
v_res_897_ = v___x_927_;
goto v___jp_895_;
}
else
{
lean_dec(v_res_921_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_pos_928_; lean_object* v_res_929_; 
lean_dec(v_snd_903_);
lean_dec(v_pos_890_);
v_pos_928_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_pos_928_);
v_res_929_ = lean_ctor_get(v___x_924_, 1);
lean_inc(v_res_929_);
lean_dec_ref_known(v___x_924_, 2);
v_pos_896_ = v_pos_928_;
v_res_897_ = v_res_929_;
goto v___jp_895_;
}
else
{
lean_object* v_err_930_; 
v_err_930_ = lean_ctor_get(v___x_924_, 1);
lean_inc(v_err_930_);
lean_dec_ref_known(v___x_924_, 2);
lean_inc(v_snd_903_);
v_pos_905_ = v_pos_890_;
v_snd_906_ = v_snd_903_;
v_err_907_ = v_err_930_;
goto v___jp_904_;
}
}
}
}
else
{
lean_object* v_err_933_; 
v_err_933_ = lean_ctor_get(v___x_919_, 1);
lean_inc(v_err_933_);
lean_dec_ref_known(v___x_919_, 2);
lean_inc(v_snd_903_);
v_pos_905_ = v_pos_890_;
v_snd_906_ = v_snd_903_;
v_err_907_ = v_err_933_;
goto v___jp_904_;
}
}
}
else
{
lean_object* v___x_934_; 
v___x_934_ = lean_box(0);
lean_inc(v_snd_903_);
v_pos_905_ = v_pos_890_;
v_snd_906_ = v_snd_903_;
v_err_907_ = v___x_934_;
goto v___jp_904_;
}
v___jp_895_:
{
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_898_, 0, v_res_891_);
lean_ctor_set(v___x_898_, 1, v_res_897_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 1, v___x_898_);
lean_ctor_set(v___x_893_, 0, v_pos_896_);
v___x_900_ = v___x_893_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_pos_896_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
v___jp_904_:
{
uint8_t v_decide_908_; 
v_decide_908_ = lean_nat_dec_eq(v_snd_903_, v_snd_906_);
lean_dec(v_snd_906_);
lean_dec(v_snd_903_);
if (v_decide_908_ == 0)
{
lean_object* v___x_909_; 
lean_del_object(v___x_893_);
lean_dec(v_res_891_);
v___x_909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_909_, 0, v_pos_905_);
lean_ctor_set(v___x_909_, 1, v_err_907_);
return v___x_909_;
}
else
{
lean_object* v___x_910_; 
lean_dec(v_err_907_);
v___x_910_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1);
v_pos_896_ = v_pos_905_;
v_res_897_ = v___x_910_;
goto v___jp_895_;
}
}
}
}
else
{
lean_object* v_pos_936_; lean_object* v_err_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
v_pos_936_ = lean_ctor_get(v___x_889_, 0);
v_err_937_ = lean_ctor_get(v___x_889_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_889_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_err_937_);
lean_inc(v_pos_936_);
lean_dec(v___x_889_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_pos_936_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_err_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___boxed(lean_object* v_extended_945_, lean_object* v_a_946_){
_start:
{
uint8_t v_extended_boxed_947_; lean_object* v_res_948_; 
v_extended_boxed_947_ = lean_unbox(v_extended_945_);
v_res_948_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_boxed_947_, v_a_946_);
return v_res_948_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_952_; lean_object* v___x_953_; 
v___x_952_ = 44;
v___x_953_ = lean_box_uint32(v___x_952_);
return v___x_953_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2___boxed__const__1;
v___x_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP(uint8_t v_extended_959_, lean_object* v_a_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(v_a_960_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_pos_962_; lean_object* v_res_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_1145_; 
v_pos_962_ = lean_ctor_get(v___x_961_, 0);
v_res_963_ = lean_ctor_get(v___x_961_, 1);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_965_ = v___x_961_;
v_isShared_966_ = v_isSharedCheck_1145_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_res_963_);
lean_inc(v_pos_962_);
lean_dec(v___x_961_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_1145_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
v___x_967_ = lean_string_utf8_byte_size(v_res_963_);
v___x_968_ = lean_unsigned_to_nat(0u);
v___x_969_ = lean_nat_dec_eq(v___x_967_, v___x_968_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; 
v___x_970_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_pos_962_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_pos_971_; lean_object* v_res_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_1131_; 
v_pos_971_ = lean_ctor_get(v___x_970_, 0);
v_res_972_ = lean_ctor_get(v___x_970_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_974_ = v___x_970_;
v_isShared_975_ = v_isSharedCheck_1131_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_res_972_);
lean_inc(v_pos_971_);
lean_dec(v___x_970_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_1131_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___y_977_; lean_object* v___y_978_; uint32_t v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_1017_; uint32_t v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; uint8_t v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; uint8_t v___y_1024_; uint8_t v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v_pos_1059_; lean_object* v_res_1060_; lean_object* v___y_1074_; uint8_t v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v_fst_1124_; lean_object* v_snd_1125_; lean_object* v___x_1126_; uint8_t v_decide_1127_; 
v_fst_1124_ = lean_ctor_get(v_pos_971_, 0);
v_snd_1125_ = lean_ctor_get(v_pos_971_, 1);
v___x_1126_ = lean_string_utf8_byte_size(v_fst_1124_);
v_decide_1127_ = lean_nat_dec_eq(v_snd_1125_, v___x_1126_);
if (v_decide_1127_ == 0)
{
goto v___jp_1083_;
}
else
{
if (v___x_969_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_del_object(v___x_974_);
lean_del_object(v___x_965_);
v___x_1128_ = lean_box(0);
v___x_1129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1129_, 0, v_res_963_);
lean_ctor_set(v___x_1129_, 1, v_res_972_);
lean_ctor_set(v___x_1129_, 2, v___x_1128_);
v___x_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1130_, 0, v_pos_971_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
return v___x_1130_;
}
else
{
goto v___jp_1083_;
}
}
v___jp_976_:
{
uint32_t v_c_984_; uint8_t v___x_985_; 
v_c_984_ = lean_string_utf8_get_fast(v___y_978_, v___y_983_);
v___x_985_ = lean_uint32_dec_eq(v_c_984_, v___y_979_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; lean_object* v___x_988_; 
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v_res_972_);
lean_dec(v_res_963_);
v___x_986_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1));
if (v_isShared_975_ == 0)
{
lean_ctor_set_tag(v___x_974_, 1);
lean_ctor_set(v___x_974_, 1, v___x_986_);
lean_ctor_set(v___x_974_, 0, v___y_980_);
v___x_988_ = v___x_974_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___y_980_);
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
lean_object* v___x_990_; lean_object* v_it_x27_991_; lean_object* v___x_992_; 
lean_dec_ref(v___y_980_);
lean_del_object(v___x_974_);
v___x_990_ = lean_string_utf8_next_fast(v___y_978_, v___y_983_);
lean_dec(v___y_983_);
v_it_x27_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_991_, 0, v___y_978_);
lean_ctor_set(v_it_x27_991_, 1, v___x_990_);
v___x_992_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_959_, v_it_x27_991_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_pos_993_; lean_object* v_res_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1006_; 
v_pos_993_ = lean_ctor_get(v___x_992_, 0);
v_res_994_ = lean_ctor_get(v___x_992_, 1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_996_ = v___x_992_;
v_isShared_997_ = v_isSharedCheck_1006_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_res_994_);
lean_inc(v_pos_993_);
lean_dec(v___x_992_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1006_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_998_, 0, v___y_977_);
v___x_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_999_, 0, v_res_994_);
v___x_1000_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1000_, 0, v___y_982_);
lean_ctor_set(v___x_1000_, 1, v___y_981_);
lean_ctor_set(v___x_1000_, 2, v___x_998_);
lean_ctor_set(v___x_1000_, 3, v___x_999_);
v___x_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1002_, 0, v_res_963_);
lean_ctor_set(v___x_1002_, 1, v_res_972_);
lean_ctor_set(v___x_1002_, 2, v___x_1001_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 1, v___x_1002_);
v___x_1004_ = v___x_996_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_pos_993_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
else
{
lean_object* v_pos_1007_; lean_object* v_err_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_977_);
lean_dec(v_res_972_);
lean_dec(v_res_963_);
v_pos_1007_ = lean_ctor_get(v___x_992_, 0);
v_err_1008_ = lean_ctor_get(v___x_992_, 1);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_992_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_err_1008_);
lean_inc(v_pos_1007_);
lean_dec(v___x_992_);
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
v___jp_1016_:
{
if (v___y_1024_ == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1027_; 
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec(v___y_1020_);
lean_dec(v___y_1017_);
lean_del_object(v___x_974_);
lean_dec(v_res_972_);
lean_dec(v_res_963_);
v___x_1025_ = lean_box(0);
if (v_isShared_966_ == 0)
{
lean_ctor_set_tag(v___x_965_, 1);
lean_ctor_set(v___x_965_, 1, v___x_1025_);
lean_ctor_set(v___x_965_, 0, v___y_1019_);
v___x_1027_ = v___x_965_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___y_1019_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
else
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
lean_dec_ref(v___y_1019_);
lean_del_object(v___x_965_);
v___x_1029_ = lean_string_utf8_next_fast(v___y_1020_, v___y_1017_);
lean_dec(v___y_1017_);
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___y_1020_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_959_, v___x_1030_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_pos_1032_; lean_object* v_res_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1045_; 
v_pos_1032_ = lean_ctor_get(v___x_1031_, 0);
v_res_1033_ = lean_ctor_get(v___x_1031_, 1);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1035_ = v___x_1031_;
v_isShared_1036_ = v_isSharedCheck_1045_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_res_1033_);
lean_inc(v_pos_1032_);
lean_dec(v___x_1031_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1045_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v_fst_1037_; lean_object* v_snd_1038_; lean_object* v___x_1039_; uint8_t v_decide_1040_; 
v_fst_1037_ = lean_ctor_get(v_pos_1032_, 0);
v_snd_1038_ = lean_ctor_get(v_pos_1032_, 1);
v___x_1039_ = lean_string_utf8_byte_size(v_fst_1037_);
v_decide_1040_ = lean_nat_dec_eq(v_snd_1038_, v___x_1039_);
if (v_decide_1040_ == 0)
{
lean_inc(v_snd_1038_);
lean_inc(v_fst_1037_);
lean_del_object(v___x_1035_);
v___y_977_ = v_res_1033_;
v___y_978_ = v_fst_1037_;
v___y_979_ = v___y_1018_;
v___y_980_ = v_pos_1032_;
v___y_981_ = v___y_1022_;
v___y_982_ = v___y_1023_;
v___y_983_ = v_snd_1038_;
goto v___jp_976_;
}
else
{
if (v___y_1021_ == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1043_; 
lean_dec(v_res_1033_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_del_object(v___x_974_);
lean_dec(v_res_972_);
lean_dec(v_res_963_);
v___x_1041_ = lean_box(0);
if (v_isShared_1036_ == 0)
{
lean_ctor_set_tag(v___x_1035_, 1);
lean_ctor_set(v___x_1035_, 1, v___x_1041_);
v___x_1043_ = v___x_1035_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_pos_1032_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
else
{
lean_inc(v_snd_1038_);
lean_inc(v_fst_1037_);
lean_del_object(v___x_1035_);
v___y_977_ = v_res_1033_;
v___y_978_ = v_fst_1037_;
v___y_979_ = v___y_1018_;
v___y_980_ = v_pos_1032_;
v___y_981_ = v___y_1022_;
v___y_982_ = v___y_1023_;
v___y_983_ = v_snd_1038_;
goto v___jp_976_;
}
}
}
}
else
{
lean_object* v_pos_1046_; lean_object* v_err_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_del_object(v___x_974_);
lean_dec(v_res_972_);
lean_dec(v_res_963_);
v_pos_1046_ = lean_ctor_get(v___x_1031_, 0);
v_err_1047_ = lean_ctor_get(v___x_1031_, 1);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1031_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_err_1047_);
lean_inc(v_pos_1046_);
lean_dec(v___x_1031_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_pos_1046_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_err_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
v___jp_1055_:
{
uint32_t v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1061_ = 44;
v___x_1062_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2);
v___x_1063_ = l_instBEqOption_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_res_1060_, v___x_1062_);
lean_dec(v_res_1060_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
lean_del_object(v___x_974_);
lean_del_object(v___x_965_);
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1065_, 0, v___y_1058_);
lean_ctor_set(v___x_1065_, 1, v___y_1057_);
lean_ctor_set(v___x_1065_, 2, v___x_1064_);
lean_ctor_set(v___x_1065_, 3, v___x_1064_);
v___x_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1067_, 0, v_res_963_);
lean_ctor_set(v___x_1067_, 1, v_res_972_);
lean_ctor_set(v___x_1067_, 2, v___x_1066_);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v_pos_1059_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
return v___x_1068_;
}
else
{
lean_object* v_fst_1069_; lean_object* v_snd_1070_; lean_object* v___x_1071_; uint8_t v_decide_1072_; 
v_fst_1069_ = lean_ctor_get(v_pos_1059_, 0);
lean_inc(v_fst_1069_);
v_snd_1070_ = lean_ctor_get(v_pos_1059_, 1);
lean_inc(v_snd_1070_);
v___x_1071_ = lean_string_utf8_byte_size(v_fst_1069_);
v_decide_1072_ = lean_nat_dec_eq(v_snd_1070_, v___x_1071_);
if (v_decide_1072_ == 0)
{
v___y_1017_ = v_snd_1070_;
v___y_1018_ = v___x_1061_;
v___y_1019_ = v_pos_1059_;
v___y_1020_ = v_fst_1069_;
v___y_1021_ = v___y_1056_;
v___y_1022_ = v___y_1057_;
v___y_1023_ = v___y_1058_;
v___y_1024_ = v___x_1063_;
goto v___jp_1016_;
}
else
{
v___y_1017_ = v_snd_1070_;
v___y_1018_ = v___x_1061_;
v___y_1019_ = v_pos_1059_;
v___y_1020_ = v_fst_1069_;
v___y_1021_ = v___y_1056_;
v___y_1022_ = v___y_1057_;
v___y_1023_ = v___y_1058_;
v___y_1024_ = v___y_1056_;
goto v___jp_1016_;
}
}
}
v___jp_1073_:
{
uint32_t v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1080_ = lean_string_utf8_get_fast(v___y_1077_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec(v___y_1077_);
v___x_1081_ = lean_box_uint32(v___x_1080_);
v___x_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
v___y_1056_ = v___y_1075_;
v___y_1057_ = v___y_1078_;
v___y_1058_ = v___y_1079_;
v_pos_1059_ = v___y_1074_;
v_res_1060_ = v___x_1082_;
goto v___jp_1055_;
}
v___jp_1083_:
{
lean_object* v___x_1084_; 
v___x_1084_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(v_pos_971_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_pos_1085_; lean_object* v_res_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1114_; 
v_pos_1085_ = lean_ctor_get(v___x_1084_, 0);
v_res_1086_ = lean_ctor_get(v___x_1084_, 1);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1088_ = v___x_1084_;
v_isShared_1089_ = v_isSharedCheck_1114_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_res_1086_);
lean_inc(v_pos_1085_);
lean_dec(v___x_1084_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1114_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1090_ = lean_string_utf8_byte_size(v_res_1086_);
v___x_1091_ = lean_nat_dec_eq(v___x_1090_, v___x_968_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; 
lean_del_object(v___x_1088_);
v___x_1092_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(v_res_972_, v_pos_1085_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_pos_1093_; lean_object* v_res_1094_; lean_object* v_fst_1095_; lean_object* v_snd_1096_; lean_object* v___x_1097_; uint8_t v_decide_1098_; 
v_pos_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_pos_1093_);
v_res_1094_ = lean_ctor_get(v___x_1092_, 1);
lean_inc(v_res_1094_);
lean_dec_ref_known(v___x_1092_, 2);
v_fst_1095_ = lean_ctor_get(v_pos_1093_, 0);
v_snd_1096_ = lean_ctor_get(v_pos_1093_, 1);
v___x_1097_ = lean_string_utf8_byte_size(v_fst_1095_);
v_decide_1098_ = lean_nat_dec_eq(v_snd_1096_, v___x_1097_);
if (v_decide_1098_ == 0)
{
lean_inc(v_snd_1096_);
lean_inc(v_fst_1095_);
v___y_1074_ = v_pos_1093_;
v___y_1075_ = v___x_1091_;
v___y_1076_ = v_snd_1096_;
v___y_1077_ = v_fst_1095_;
v___y_1078_ = v_res_1094_;
v___y_1079_ = v_res_1086_;
goto v___jp_1073_;
}
else
{
if (v___x_1091_ == 0)
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_box(0);
v___y_1056_ = v___x_1091_;
v___y_1057_ = v_res_1094_;
v___y_1058_ = v_res_1086_;
v_pos_1059_ = v_pos_1093_;
v_res_1060_ = v___x_1099_;
goto v___jp_1055_;
}
else
{
lean_inc(v_snd_1096_);
lean_inc(v_fst_1095_);
v___y_1074_ = v_pos_1093_;
v___y_1075_ = v___x_1091_;
v___y_1076_ = v_snd_1096_;
v___y_1077_ = v_fst_1095_;
v___y_1078_ = v_res_1094_;
v___y_1079_ = v_res_1086_;
goto v___jp_1073_;
}
}
}
else
{
lean_object* v_pos_1100_; lean_object* v_err_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec(v_res_1086_);
lean_del_object(v___x_974_);
lean_dec(v_res_972_);
lean_del_object(v___x_965_);
lean_dec(v_res_963_);
v_pos_1100_ = lean_ctor_get(v___x_1092_, 0);
v_err_1101_ = lean_ctor_get(v___x_1092_, 1);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1092_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_err_1101_);
lean_inc(v_pos_1100_);
lean_dec(v___x_1092_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_pos_1100_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_err_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
lean_dec(v_res_1086_);
lean_del_object(v___x_974_);
lean_del_object(v___x_965_);
v___x_1109_ = lean_box(0);
v___x_1110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1110_, 0, v_res_963_);
lean_ctor_set(v___x_1110_, 1, v_res_972_);
lean_ctor_set(v___x_1110_, 2, v___x_1109_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v___x_1110_);
v___x_1112_ = v___x_1088_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_pos_1085_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
else
{
lean_object* v_pos_1115_; lean_object* v_err_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_del_object(v___x_974_);
lean_dec(v_res_972_);
lean_del_object(v___x_965_);
lean_dec(v_res_963_);
v_pos_1115_ = lean_ctor_get(v___x_1084_, 0);
v_err_1116_ = lean_ctor_get(v___x_1084_, 1);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1084_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_err_1116_);
lean_inc(v_pos_1115_);
lean_dec(v___x_1084_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_pos_1115_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_err_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1132_; lean_object* v_err_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_del_object(v___x_965_);
lean_dec(v_res_963_);
v_pos_1132_ = lean_ctor_get(v___x_970_, 0);
v_err_1133_ = lean_ctor_get(v___x_970_, 1);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_970_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_err_1133_);
lean_inc(v_pos_1132_);
lean_dec(v___x_970_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_pos_1132_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_err_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
lean_dec(v_res_963_);
v___x_1141_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__4));
if (v_isShared_966_ == 0)
{
lean_ctor_set_tag(v___x_965_, 1);
lean_ctor_set(v___x_965_, 1, v___x_1141_);
v___x_1143_ = v___x_965_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_pos_962_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v___x_1141_);
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
lean_object* v_pos_1146_; lean_object* v_err_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
v_pos_1146_ = lean_ctor_get(v___x_961_, 0);
v_err_1147_ = lean_ctor_get(v___x_961_, 1);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_961_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_err_1147_);
lean_inc(v_pos_1146_);
lean_dec(v___x_961_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_pos_1146_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_err_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___boxed(lean_object* v_extended_1155_, lean_object* v_a_1156_){
_start:
{
uint8_t v_extended_boxed_1157_; lean_object* v_res_1158_; 
v_extended_boxed_1157_ = lean_unbox(v_extended_1155_);
v_res_1158_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP(v_extended_boxed_1157_, v_a_1156_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_parsePosixTz(lean_object* v_s_1159_, uint8_t v_extended_1160_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1161_ = lean_box(v_extended_1160_);
v___x_1162_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___boxed), 2, 1);
lean_closure_set(v___x_1162_, 0, v___x_1161_);
v___x_1163_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_1162_, v_s_1159_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_parsePosixTz___boxed(lean_object* v_s_1164_, lean_object* v_extended_1165_){
_start:
{
uint8_t v_extended_boxed_1166_; lean_object* v_res_1167_; 
v_extended_boxed_1166_ = lean_unbox(v_extended_1165_);
v_res_1167_ = l_Std_Time_TimeZone_parsePosixTz(v_s_1164_, v_extended_boxed_1166_);
return v_res_1167_;
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
