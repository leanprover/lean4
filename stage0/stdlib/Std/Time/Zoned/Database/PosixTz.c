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
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
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
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: ':'"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__3_value)}};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4_value;
static lean_once_cell_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "second"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "minute"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hour "};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " out of range 0-"};
static const lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9 = (const lean_object*)&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9_value;
static const lean_string_object l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "167"};
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
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_89_ = lean_int_neg(v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(lean_object* v_a_90_){
_start:
{
lean_object* v_fst_91_; lean_object* v_snd_92_; lean_object* v_err_94_; lean_object* v_err_102_; lean_object* v___x_123_; uint8_t v_decide_124_; 
v_fst_91_ = lean_ctor_get(v_a_90_, 0);
v_snd_92_ = lean_ctor_get(v_a_90_, 1);
v___x_123_ = lean_string_utf8_byte_size(v_fst_91_);
v_decide_124_ = lean_nat_dec_eq(v_snd_92_, v___x_123_);
if (v_decide_124_ == 0)
{
uint32_t v___x_125_; uint32_t v_c_126_; uint8_t v___x_127_; 
v___x_125_ = 45;
v_c_126_ = lean_string_utf8_get_fast(v_fst_91_, v_snd_92_);
v___x_127_ = lean_uint32_dec_eq(v_c_126_, v___x_125_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; 
v___x_128_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__4));
v_err_102_ = v___x_128_;
goto v___jp_101_;
}
else
{
lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_138_; 
lean_inc(v_snd_92_);
lean_inc(v_fst_91_);
v_isSharedCheck_138_ = !lean_is_exclusive(v_a_90_);
if (v_isSharedCheck_138_ == 0)
{
lean_object* v_unused_139_; lean_object* v_unused_140_; 
v_unused_139_ = lean_ctor_get(v_a_90_, 1);
lean_dec(v_unused_139_);
v_unused_140_ = lean_ctor_get(v_a_90_, 0);
lean_dec(v_unused_140_);
v___x_130_ = v_a_90_;
v_isShared_131_ = v_isSharedCheck_138_;
goto v_resetjp_129_;
}
else
{
lean_dec(v_a_90_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_138_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v_it_x27_134_; 
v___x_132_ = lean_string_utf8_next_fast(v_fst_91_, v_snd_92_);
lean_dec(v_snd_92_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_132_);
v_it_x27_134_ = v___x_130_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_fst_91_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v___x_132_);
v_it_x27_134_ = v_reuseFailAlloc_137_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__5);
v___x_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_136_, 0, v_it_x27_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
return v___x_136_;
}
}
}
}
else
{
lean_object* v___x_141_; 
v___x_141_ = lean_box(0);
v_err_102_ = v___x_141_;
goto v___jp_101_;
}
v___jp_93_:
{
uint8_t v_decide_95_; 
v_decide_95_ = lean_nat_dec_eq(v_snd_92_, v_snd_92_);
if (v_decide_95_ == 0)
{
lean_object* v___x_96_; 
lean_inc(v_err_94_);
v___x_96_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_96_, 0, v_a_90_);
lean_ctor_set(v___x_96_, 1, v_err_94_);
return v___x_96_;
}
else
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v_a_90_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
return v___x_98_;
}
}
v___jp_99_:
{
lean_object* v___x_100_; 
v___x_100_ = lean_box(0);
v_err_94_ = v___x_100_;
goto v___jp_93_;
}
v___jp_101_:
{
uint8_t v_decide_103_; 
v_decide_103_ = lean_nat_dec_eq(v_snd_92_, v_snd_92_);
if (v_decide_103_ == 0)
{
lean_object* v___x_104_; 
lean_inc(v_err_102_);
v___x_104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_104_, 0, v_a_90_);
lean_ctor_set(v___x_104_, 1, v_err_102_);
return v___x_104_;
}
else
{
lean_object* v___x_105_; uint8_t v_decide_106_; 
v___x_105_ = lean_string_utf8_byte_size(v_fst_91_);
v_decide_106_ = lean_nat_dec_eq(v_snd_92_, v___x_105_);
if (v_decide_106_ == 0)
{
if (v_decide_103_ == 0)
{
goto v___jp_99_;
}
else
{
uint32_t v___x_107_; uint32_t v_c_108_; uint8_t v___x_109_; 
v___x_107_ = 43;
v_c_108_ = lean_string_utf8_get_fast(v_fst_91_, v_snd_92_);
v___x_109_ = lean_uint32_dec_eq(v_c_108_, v___x_107_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
v___x_110_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__2));
v_err_94_ = v___x_110_;
goto v___jp_93_;
}
else
{
lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_120_; 
lean_inc(v_snd_92_);
lean_inc(v_fst_91_);
v_isSharedCheck_120_ = !lean_is_exclusive(v_a_90_);
if (v_isSharedCheck_120_ == 0)
{
lean_object* v_unused_121_; lean_object* v_unused_122_; 
v_unused_121_ = lean_ctor_get(v_a_90_, 1);
lean_dec(v_unused_121_);
v_unused_122_ = lean_ctor_get(v_a_90_, 0);
lean_dec(v_unused_122_);
v___x_112_ = v_a_90_;
v_isShared_113_ = v_isSharedCheck_120_;
goto v_resetjp_111_;
}
else
{
lean_dec(v_a_90_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_120_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_114_; lean_object* v_it_x27_116_; 
v___x_114_ = lean_string_utf8_next_fast(v_fst_91_, v_snd_92_);
lean_dec(v_snd_92_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 1, v___x_114_);
v_it_x27_116_ = v___x_112_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_fst_91_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v___x_114_);
v_it_x27_116_ = v_reuseFailAlloc_119_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v_it_x27_116_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
return v___x_118_;
}
}
}
}
}
else
{
goto v___jp_99_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__0(lean_object* v_a_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_nat_to_int(v_a_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__2(lean_object* v_a_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Rat_ofInt(v_a_144_);
return v___x_145_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0(uint8_t v___x_146_, lean_object* v_x_147_){
_start:
{
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed(lean_object* v___x_148_, lean_object* v_x_149_){
_start:
{
uint8_t v___x_3948__boxed_150_; uint8_t v_res_151_; lean_object* v_r_152_; 
v___x_3948__boxed_150_ = lean_unbox(v___x_148_);
v_res_151_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0(v___x_3948__boxed_150_, v_x_149_);
lean_dec(v_x_149_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(3600u);
v___x_154_ = lean_nat_to_int(v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_unsigned_to_nat(60u);
v___x_156_ = lean_nat_to_int(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = lean_nat_to_int(v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(59u);
v___x_163_ = lean_nat_to_int(v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(lean_object* v_maxHour_169_, lean_object* v_a_170_){
_start:
{
lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v_pos_174_; lean_object* v_res_175_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_186_; lean_object* v_err_187_; lean_object* v___y_193_; uint32_t v___y_194_; lean_object* v___y_195_; lean_object* v___y_196_; lean_object* v___y_197_; lean_object* v___y_198_; uint8_t v___y_199_; uint8_t v___y_216_; uint8_t v___y_217_; uint32_t v___y_218_; lean_object* v___y_219_; lean_object* v_pos_220_; lean_object* v_res_221_; uint8_t v___y_227_; uint8_t v___y_228_; lean_object* v___y_229_; lean_object* v___y_230_; uint32_t v___y_231_; lean_object* v___y_232_; lean_object* v_err_233_; lean_object* v_fst_237_; lean_object* v_snd_238_; uint8_t v___y_240_; uint8_t v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; uint32_t v___y_244_; lean_object* v___y_245_; uint8_t v___y_246_; lean_object* v___x_262_; uint8_t v_decide_263_; 
v_fst_237_ = lean_ctor_get(v_a_170_, 0);
v_snd_238_ = lean_ctor_get(v_a_170_, 1);
v___x_262_ = lean_string_utf8_byte_size(v_fst_237_);
v_decide_263_ = lean_nat_dec_eq(v_snd_238_, v___x_262_);
if (v_decide_263_ == 0)
{
uint32_t v_c_264_; uint8_t v___y_266_; uint32_t v___x_317_; uint8_t v___x_318_; 
v_c_264_ = lean_string_utf8_get_fast(v_fst_237_, v_snd_238_);
v___x_317_ = 48;
v___x_318_ = lean_uint32_dec_le(v___x_317_, v_c_264_);
if (v___x_318_ == 0)
{
v___y_266_ = v___x_318_;
goto v___jp_265_;
}
else
{
uint32_t v___x_319_; uint8_t v___x_320_; 
v___x_319_ = 57;
v___x_320_ = lean_uint32_dec_le(v_c_264_, v___x_319_);
v___y_266_ = v___x_320_;
goto v___jp_265_;
}
v___jp_265_:
{
if (v___y_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec(v_maxHour_169_);
v___x_267_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__3));
v___x_268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_268_, 0, v_a_170_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
return v___x_268_;
}
else
{
lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_314_; 
lean_inc(v_snd_238_);
lean_inc(v_fst_237_);
v_isSharedCheck_314_ = !lean_is_exclusive(v_a_170_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; lean_object* v_unused_316_; 
v_unused_315_ = lean_ctor_get(v_a_170_, 1);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_a_170_, 0);
lean_dec(v_unused_316_);
v___x_270_ = v_a_170_;
v_isShared_271_ = v_isSharedCheck_314_;
goto v_resetjp_269_;
}
else
{
lean_dec(v_a_170_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_314_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v_fst_277_; lean_object* v_snd_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_313_; 
v___x_272_ = lean_string_utf8_next_fast(v_fst_237_, v_snd_238_);
lean_dec(v_snd_238_);
v___x_273_ = lean_uint32_to_nat(v_c_264_);
v___x_274_ = lean_unsigned_to_nat(48u);
v___x_275_ = lean_nat_sub(v___x_273_, v___x_274_);
lean_dec(v___x_273_);
v___x_276_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_237_, v___x_272_, v___x_275_);
v_fst_277_ = lean_ctor_get(v___x_276_, 0);
v_snd_278_ = lean_ctor_get(v___x_276_, 1);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_313_ == 0)
{
v___x_280_ = v___x_276_;
v_isShared_281_ = v_isSharedCheck_313_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_snd_278_);
lean_inc(v_fst_277_);
lean_dec(v___x_276_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_313_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
lean_inc(v_snd_278_);
lean_inc(v_fst_237_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 1, v_snd_278_);
v___x_283_ = v___x_270_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_fst_237_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_snd_278_);
v___x_283_ = v_reuseFailAlloc_312_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
uint8_t v___x_284_; 
v___x_284_ = lean_nat_dec_lt(v_maxHour_169_, v_fst_277_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; uint8_t v___x_286_; 
lean_dec(v_maxHour_169_);
v___x_285_ = lean_unsigned_to_nat(167u);
v___x_286_ = lean_nat_dec_le(v_fst_277_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
lean_dec(v_snd_278_);
lean_dec(v_fst_237_);
v___x_287_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8));
v___x_288_ = l_Nat_reprFast(v_fst_277_);
v___x_289_ = lean_string_append(v___x_287_, v___x_288_);
lean_dec_ref(v___x_288_);
v___x_290_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9));
v___x_291_ = lean_string_append(v___x_289_, v___x_290_);
v___x_292_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__10));
v___x_293_ = lean_string_append(v___x_291_, v___x_292_);
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
if (v_isShared_281_ == 0)
{
lean_ctor_set_tag(v___x_280_, 1);
lean_ctor_set(v___x_280_, 1, v___x_294_);
lean_ctor_set(v___x_280_, 0, v___x_283_);
v___x_296_ = v___x_280_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
else
{
lean_object* v___x_298_; uint32_t v___x_299_; uint8_t v_decide_300_; 
lean_del_object(v___x_280_);
v___x_298_ = lean_nat_to_int(v_fst_277_);
v___x_299_ = 58;
v_decide_300_ = lean_nat_dec_eq(v_snd_278_, v___x_262_);
if (v_decide_300_ == 0)
{
v___y_240_ = v___x_286_;
v___y_241_ = v___x_284_;
v___y_242_ = v_snd_278_;
v___y_243_ = v___x_283_;
v___y_244_ = v___x_299_;
v___y_245_ = v___x_298_;
v___y_246_ = v___x_286_;
goto v___jp_239_;
}
else
{
v___y_240_ = v___x_286_;
v___y_241_ = v___x_284_;
v___y_242_ = v_snd_278_;
v___y_243_ = v___x_283_;
v___y_244_ = v___x_299_;
v___y_245_ = v___x_298_;
v___y_246_ = v___x_284_;
goto v___jp_239_;
}
}
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
lean_dec(v_snd_278_);
lean_dec(v_fst_237_);
v___x_301_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__8));
v___x_302_ = l_Nat_reprFast(v_fst_277_);
v___x_303_ = lean_string_append(v___x_301_, v___x_302_);
lean_dec_ref(v___x_302_);
v___x_304_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__9));
v___x_305_ = lean_string_append(v___x_303_, v___x_304_);
v___x_306_ = l_Nat_reprFast(v_maxHour_169_);
v___x_307_ = lean_string_append(v___x_305_, v___x_306_);
lean_dec_ref(v___x_306_);
v___x_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
if (v_isShared_281_ == 0)
{
lean_ctor_set_tag(v___x_280_, 1);
lean_ctor_set(v___x_280_, 1, v___x_308_);
lean_ctor_set(v___x_280_, 0, v___x_283_);
v___x_310_ = v___x_280_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_283_);
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
}
}
}
}
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec(v_maxHour_169_);
v___x_321_ = lean_box(0);
v___x_322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_322_, 0, v_a_170_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
return v___x_322_;
}
v___jp_171_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_176_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0);
v___x_177_ = lean_int_mul(v___y_173_, v___x_176_);
lean_dec(v___y_173_);
v___x_178_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__1);
v___x_179_ = lean_int_mul(v___y_172_, v___x_178_);
lean_dec(v___y_172_);
v___x_180_ = lean_int_add(v___x_177_, v___x_179_);
lean_dec(v___x_179_);
lean_dec(v___x_177_);
v___x_181_ = lean_int_add(v___x_180_, v_res_175_);
lean_dec(v_res_175_);
lean_dec(v___x_180_);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v_pos_174_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
return v___x_182_;
}
v___jp_183_:
{
lean_object* v_snd_188_; uint8_t v_decide_189_; 
v_snd_188_ = lean_ctor_get(v___y_185_, 1);
v_decide_189_ = lean_nat_dec_eq(v_snd_188_, v_snd_188_);
if (v_decide_189_ == 0)
{
lean_object* v___x_190_; 
lean_dec(v___y_186_);
lean_dec(v___y_184_);
v___x_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_190_, 0, v___y_185_);
lean_ctor_set(v___x_190_, 1, v_err_187_);
return v___x_190_;
}
else
{
lean_object* v___x_191_; 
lean_dec(v_err_187_);
v___x_191_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2);
v___y_172_ = v___y_184_;
v___y_173_ = v___y_186_;
v_pos_174_ = v___y_185_;
v_res_175_ = v___x_191_;
goto v___jp_171_;
}
}
v___jp_192_:
{
if (v___y_199_ == 0)
{
lean_object* v___x_200_; 
lean_dec(v___y_195_);
lean_dec(v___y_193_);
v___x_200_ = lean_box(0);
v___y_184_ = v___y_196_;
v___y_185_ = v___y_197_;
v___y_186_ = v___y_198_;
v_err_187_ = v___x_200_;
goto v___jp_183_;
}
else
{
uint32_t v_c_201_; uint8_t v___x_202_; 
v_c_201_ = lean_string_utf8_get_fast(v___y_193_, v___y_195_);
v___x_202_ = lean_uint32_dec_eq(v_c_201_, v___y_194_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
lean_dec(v___y_195_);
lean_dec(v___y_193_);
v___x_203_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4));
v___y_184_ = v___y_196_;
v___y_185_ = v___y_197_;
v___y_186_ = v___y_198_;
v_err_187_ = v___x_203_;
goto v___jp_183_;
}
else
{
lean_object* v___x_204_; lean_object* v___f_205_; lean_object* v___x_206_; lean_object* v_it_x27_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_204_ = lean_box(v___x_202_);
v___f_205_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_205_, 0, v___x_204_);
v___x_206_ = lean_string_utf8_next_fast(v___y_193_, v___y_195_);
lean_dec(v___y_195_);
v_it_x27_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_207_, 0, v___y_193_);
lean_ctor_set(v_it_x27_207_, 1, v___x_206_);
v___x_208_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2);
v___x_209_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___x_210_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__6));
v___x_211_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_208_, v___x_209_, v___x_210_, v___f_205_, v_it_x27_207_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_pos_212_; lean_object* v_res_213_; 
lean_dec_ref(v___y_197_);
v_pos_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_pos_212_);
v_res_213_ = lean_ctor_get(v___x_211_, 1);
lean_inc(v_res_213_);
lean_dec_ref_known(v___x_211_, 2);
v___y_172_ = v___y_196_;
v___y_173_ = v___y_198_;
v_pos_174_ = v_pos_212_;
v_res_175_ = v_res_213_;
goto v___jp_171_;
}
else
{
lean_object* v_err_214_; 
v_err_214_ = lean_ctor_get(v___x_211_, 1);
lean_inc(v_err_214_);
lean_dec_ref_known(v___x_211_, 2);
v___y_184_ = v___y_196_;
v___y_185_ = v___y_197_;
v___y_186_ = v___y_198_;
v_err_187_ = v_err_214_;
goto v___jp_183_;
}
}
}
}
v___jp_215_:
{
lean_object* v_fst_222_; lean_object* v_snd_223_; lean_object* v___x_224_; uint8_t v_decide_225_; 
v_fst_222_ = lean_ctor_get(v_pos_220_, 0);
lean_inc(v_fst_222_);
v_snd_223_ = lean_ctor_get(v_pos_220_, 1);
lean_inc(v_snd_223_);
v___x_224_ = lean_string_utf8_byte_size(v_fst_222_);
v_decide_225_ = lean_nat_dec_eq(v_snd_223_, v___x_224_);
if (v_decide_225_ == 0)
{
v___y_193_ = v_fst_222_;
v___y_194_ = v___y_218_;
v___y_195_ = v_snd_223_;
v___y_196_ = v_res_221_;
v___y_197_ = v_pos_220_;
v___y_198_ = v___y_219_;
v___y_199_ = v___y_216_;
goto v___jp_192_;
}
else
{
v___y_193_ = v_fst_222_;
v___y_194_ = v___y_218_;
v___y_195_ = v_snd_223_;
v___y_196_ = v_res_221_;
v___y_197_ = v_pos_220_;
v___y_198_ = v___y_219_;
v___y_199_ = v___y_217_;
goto v___jp_192_;
}
}
v___jp_226_:
{
uint8_t v_decide_234_; 
v_decide_234_ = lean_nat_dec_eq(v___y_230_, v___y_230_);
lean_dec(v___y_230_);
if (v_decide_234_ == 0)
{
lean_object* v___x_235_; 
lean_dec(v___y_232_);
v___x_235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_235_, 0, v___y_229_);
lean_ctor_set(v___x_235_, 1, v_err_233_);
return v___x_235_;
}
else
{
lean_object* v___x_236_; 
lean_dec(v_err_233_);
v___x_236_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2);
v___y_216_ = v___y_227_;
v___y_217_ = v___y_228_;
v___y_218_ = v___y_231_;
v___y_219_ = v___y_232_;
v_pos_220_ = v___y_229_;
v_res_221_ = v___x_236_;
goto v___jp_215_;
}
}
v___jp_239_:
{
if (v___y_246_ == 0)
{
lean_object* v___x_247_; 
lean_dec(v_fst_237_);
v___x_247_ = lean_box(0);
v___y_227_ = v___y_240_;
v___y_228_ = v___y_241_;
v___y_229_ = v___y_243_;
v___y_230_ = v___y_242_;
v___y_231_ = v___y_244_;
v___y_232_ = v___y_245_;
v_err_233_ = v___x_247_;
goto v___jp_226_;
}
else
{
uint32_t v_c_248_; uint8_t v___x_249_; 
v_c_248_ = lean_string_utf8_get_fast(v_fst_237_, v___y_242_);
v___x_249_ = lean_uint32_dec_eq(v_c_248_, v___y_244_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_dec(v_fst_237_);
v___x_250_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__4));
v___y_227_ = v___y_240_;
v___y_228_ = v___y_241_;
v___y_229_ = v___y_243_;
v___y_230_ = v___y_242_;
v___y_231_ = v___y_244_;
v___y_232_ = v___y_245_;
v_err_233_ = v___x_250_;
goto v___jp_226_;
}
else
{
lean_object* v___x_251_; lean_object* v___f_252_; lean_object* v___x_253_; lean_object* v_it_x27_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_251_ = lean_box(v___x_249_);
v___f_252_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_252_, 0, v___x_251_);
v___x_253_ = lean_string_utf8_next_fast(v_fst_237_, v___y_242_);
v_it_x27_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_254_, 0, v_fst_237_);
lean_ctor_set(v_it_x27_254_, 1, v___x_253_);
v___x_255_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2);
v___x_256_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__5);
v___x_257_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__7));
v___x_258_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_255_, v___x_256_, v___x_257_, v___f_252_, v_it_x27_254_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_pos_259_; lean_object* v_res_260_; 
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
v_pos_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_pos_259_);
v_res_260_ = lean_ctor_get(v___x_258_, 1);
lean_inc(v_res_260_);
lean_dec_ref_known(v___x_258_, 2);
v___y_216_ = v___y_240_;
v___y_217_ = v___y_241_;
v___y_218_ = v___y_244_;
v___y_219_ = v___y_245_;
v_pos_220_ = v_pos_259_;
v_res_221_ = v_res_260_;
goto v___jp_215_;
}
else
{
lean_object* v_err_261_; 
v_err_261_ = lean_ctor_get(v___x_258_, 1);
lean_inc(v_err_261_);
lean_dec_ref_known(v___x_258_, 2);
v___y_227_ = v___y_240_;
v___y_228_ = v___y_241_;
v___y_229_ = v___y_243_;
v___y_230_ = v___y_242_;
v___y_231_ = v___y_244_;
v___y_232_ = v___y_245_;
v_err_233_ = v_err_261_;
goto v___jp_226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS_spec__1(lean_object* v_a_323_){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_nat_to_int(v_a_323_);
v___x_325_ = l_Rat_ofInt(v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(lean_object* v_a_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(v_a_326_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_pos_328_; lean_object* v_res_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_pos_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_pos_328_);
v_res_329_ = lean_ctor_get(v___x_327_, 1);
lean_inc(v_res_329_);
lean_dec_ref_known(v___x_327_, 2);
v___x_330_ = lean_unsigned_to_nat(24u);
v___x_331_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(v___x_330_, v_pos_328_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_pos_332_; lean_object* v_res_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_342_; 
v_pos_332_ = lean_ctor_get(v___x_331_, 0);
v_res_333_ = lean_ctor_get(v___x_331_, 1);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_342_ == 0)
{
v___x_335_ = v___x_331_;
v_isShared_336_ = v_isSharedCheck_342_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_res_333_);
lean_inc(v_pos_332_);
lean_dec(v___x_331_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_342_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_337_ = lean_int_neg(v_res_329_);
lean_dec(v_res_329_);
v___x_338_ = lean_int_mul(v___x_337_, v_res_333_);
lean_dec(v_res_333_);
lean_dec(v___x_337_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v___x_338_);
v___x_340_ = v___x_335_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_pos_332_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
else
{
lean_object* v_pos_343_; lean_object* v_err_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v_res_329_);
v_pos_343_ = lean_ctor_get(v___x_331_, 0);
v_err_344_ = lean_ctor_get(v___x_331_, 1);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_331_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_err_344_);
lean_inc(v_pos_343_);
lean_dec(v___x_331_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_pos_343_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_err_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_object* v_pos_352_; lean_object* v_err_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
v_pos_352_ = lean_ctor_get(v___x_327_, 0);
v_err_353_ = lean_ctor_get(v___x_327_, 1);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_327_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_err_353_);
lean_inc(v_pos_352_);
lean_dec(v___x_327_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_pos_352_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_err_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0(lean_object* v_acc_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_fst_366_; lean_object* v_snd_367_; lean_object* v_pos_369_; lean_object* v_snd_370_; lean_object* v_err_371_; lean_object* v___x_375_; uint8_t v_decide_376_; 
v_fst_366_ = lean_ctor_get(v_a_365_, 0);
v_snd_367_ = lean_ctor_get(v_a_365_, 1);
lean_inc(v_snd_367_);
v___x_375_ = lean_string_utf8_byte_size(v_fst_366_);
v_decide_376_ = lean_nat_dec_eq(v_snd_367_, v___x_375_);
if (v_decide_376_ == 0)
{
uint32_t v_c_377_; lean_object* v___x_378_; lean_object* v_it_x27_379_; uint8_t v___y_384_; uint8_t v___y_385_; uint8_t v___y_388_; uint8_t v___y_399_; uint32_t v___x_404_; uint8_t v___x_405_; 
v_c_377_ = lean_string_utf8_get_fast(v_fst_366_, v_snd_367_);
v___x_378_ = lean_string_utf8_next_fast(v_fst_366_, v_snd_367_);
lean_inc(v_fst_366_);
v_it_x27_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_379_, 0, v_fst_366_);
lean_ctor_set(v_it_x27_379_, 1, v___x_378_);
v___x_404_ = 65;
v___x_405_ = lean_uint32_dec_le(v___x_404_, v_c_377_);
if (v___x_405_ == 0)
{
v___y_399_ = v___x_405_;
goto v___jp_398_;
}
else
{
uint32_t v___x_406_; uint8_t v___x_407_; 
v___x_406_ = 90;
v___x_407_ = lean_uint32_dec_le(v_c_377_, v___x_406_);
v___y_399_ = v___x_407_;
goto v___jp_398_;
}
v___jp_380_:
{
lean_object* v___x_381_; 
v___x_381_ = lean_string_push(v_acc_364_, v_c_377_);
v_acc_364_ = v___x_381_;
v_a_365_ = v_it_x27_379_;
goto _start;
}
v___jp_383_:
{
if (v___y_384_ == 0)
{
if (v___y_385_ == 0)
{
lean_object* v___x_386_; 
lean_dec_ref_known(v_it_x27_379_, 2);
v___x_386_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0___closed__1));
lean_inc(v_snd_367_);
v_pos_369_ = v_a_365_;
v_snd_370_ = v_snd_367_;
v_err_371_ = v___x_386_;
goto v___jp_368_;
}
else
{
lean_dec(v_snd_367_);
lean_dec_ref(v_a_365_);
goto v___jp_380_;
}
}
else
{
lean_dec(v_snd_367_);
lean_dec_ref(v_a_365_);
goto v___jp_380_;
}
}
v___jp_387_:
{
uint32_t v___x_389_; uint8_t v___x_390_; 
v___x_389_ = 43;
v___x_390_ = lean_uint32_dec_eq(v_c_377_, v___x_389_);
if (v___x_390_ == 0)
{
uint32_t v___x_391_; uint8_t v___x_392_; 
v___x_391_ = 45;
v___x_392_ = lean_uint32_dec_eq(v_c_377_, v___x_391_);
v___y_384_ = v___y_388_;
v___y_385_ = v___x_392_;
goto v___jp_383_;
}
else
{
v___y_384_ = v___y_388_;
v___y_385_ = v___x_390_;
goto v___jp_383_;
}
}
v___jp_393_:
{
uint32_t v___x_394_; uint8_t v___x_395_; 
v___x_394_ = 48;
v___x_395_ = lean_uint32_dec_le(v___x_394_, v_c_377_);
if (v___x_395_ == 0)
{
v___y_388_ = v___x_395_;
goto v___jp_387_;
}
else
{
uint32_t v___x_396_; uint8_t v___x_397_; 
v___x_396_ = 57;
v___x_397_ = lean_uint32_dec_le(v_c_377_, v___x_396_);
v___y_388_ = v___x_397_;
goto v___jp_387_;
}
}
v___jp_398_:
{
if (v___y_399_ == 0)
{
uint32_t v___x_400_; uint8_t v___x_401_; 
v___x_400_ = 97;
v___x_401_ = lean_uint32_dec_le(v___x_400_, v_c_377_);
if (v___x_401_ == 0)
{
goto v___jp_393_;
}
else
{
uint32_t v___x_402_; uint8_t v___x_403_; 
v___x_402_ = 122;
v___x_403_ = lean_uint32_dec_le(v_c_377_, v___x_402_);
if (v___x_403_ == 0)
{
goto v___jp_393_;
}
else
{
v___y_388_ = v___x_403_;
goto v___jp_387_;
}
}
}
else
{
v___y_388_ = v___y_399_;
goto v___jp_387_;
}
}
}
else
{
lean_object* v___x_408_; 
v___x_408_ = lean_box(0);
lean_inc(v_snd_367_);
v_pos_369_ = v_a_365_;
v_snd_370_ = v_snd_367_;
v_err_371_ = v___x_408_;
goto v___jp_368_;
}
v___jp_368_:
{
uint8_t v_decide_372_; 
v_decide_372_ = lean_nat_dec_eq(v_snd_367_, v_snd_370_);
lean_dec(v_snd_370_);
lean_dec(v_snd_367_);
if (v_decide_372_ == 0)
{
lean_object* v___x_373_; 
lean_dec_ref(v_acc_364_);
lean_inc(v_err_371_);
v___x_373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_373_, 0, v_pos_369_);
lean_ctor_set(v___x_373_, 1, v_err_371_);
return v___x_373_;
}
else
{
lean_object* v___x_374_; 
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v_pos_369_);
lean_ctor_set(v___x_374_, 1, v_acc_364_);
return v___x_374_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName(lean_object* v_a_410_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName___closed__0));
v___x_412_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName_spec__0(v___x_411_, v_a_410_);
return v___x_412_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
if (lean_obj_tag(v_x_413_) == 0)
{
if (lean_obj_tag(v_x_414_) == 0)
{
uint8_t v___x_415_; 
v___x_415_ = 1;
return v___x_415_;
}
else
{
uint8_t v___x_416_; 
v___x_416_ = 0;
return v___x_416_;
}
}
else
{
if (lean_obj_tag(v_x_414_) == 0)
{
uint8_t v___x_417_; 
v___x_417_ = 0;
return v___x_417_;
}
else
{
lean_object* v_val_418_; lean_object* v_val_419_; uint32_t v___x_420_; uint32_t v___x_421_; uint8_t v___x_422_; 
v_val_418_ = lean_ctor_get(v_x_413_, 0);
v_val_419_ = lean_ctor_get(v_x_414_, 0);
v___x_420_ = lean_unbox_uint32(v_val_418_);
v___x_421_ = lean_unbox_uint32(v_val_419_);
v___x_422_ = lean_uint32_dec_eq(v___x_420_, v___x_421_);
return v___x_422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0___boxed(lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
uint8_t v_res_425_; lean_object* v_r_426_; 
v_res_425_ = l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_x_423_, v_x_424_);
lean_dec(v_x_424_);
lean_dec(v_x_423_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1(lean_object* v_acc_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_fst_432_; lean_object* v_snd_433_; lean_object* v_pos_435_; lean_object* v_snd_436_; lean_object* v_err_437_; lean_object* v___x_441_; uint8_t v_decide_442_; 
v_fst_432_ = lean_ctor_get(v_a_431_, 0);
v_snd_433_ = lean_ctor_get(v_a_431_, 1);
lean_inc(v_snd_433_);
v___x_441_ = lean_string_utf8_byte_size(v_fst_432_);
v_decide_442_ = lean_nat_dec_eq(v_snd_433_, v___x_441_);
if (v_decide_442_ == 0)
{
uint32_t v_c_443_; lean_object* v___x_444_; uint8_t v___y_450_; uint8_t v___y_451_; uint8_t v___y_454_; uint32_t v___x_459_; uint8_t v___x_460_; 
v_c_443_ = lean_string_utf8_get_fast(v_fst_432_, v_snd_433_);
v___x_444_ = lean_string_utf8_next_fast(v_fst_432_, v_snd_433_);
v___x_459_ = 65;
v___x_460_ = lean_uint32_dec_le(v___x_459_, v_c_443_);
if (v___x_460_ == 0)
{
v___y_454_ = v___x_460_;
goto v___jp_453_;
}
else
{
uint32_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = 90;
v___x_462_ = lean_uint32_dec_le(v_c_443_, v___x_461_);
v___y_454_ = v___x_462_;
goto v___jp_453_;
}
v___jp_445_:
{
lean_object* v_it_x27_446_; lean_object* v___x_447_; 
v_it_x27_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_446_, 0, v_fst_432_);
lean_ctor_set(v_it_x27_446_, 1, v___x_444_);
v___x_447_ = lean_string_push(v_acc_430_, v_c_443_);
v_acc_430_ = v___x_447_;
v_a_431_ = v_it_x27_446_;
goto _start;
}
v___jp_449_:
{
if (v___y_450_ == 0)
{
if (v___y_451_ == 0)
{
lean_object* v___x_452_; 
v___x_452_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1___closed__1));
lean_inc(v_snd_433_);
v_pos_435_ = v_a_431_;
v_snd_436_ = v_snd_433_;
v_err_437_ = v___x_452_;
goto v___jp_434_;
}
else
{
lean_inc(v_fst_432_);
lean_dec(v_snd_433_);
lean_dec_ref(v_a_431_);
goto v___jp_445_;
}
}
else
{
lean_inc(v_fst_432_);
lean_dec(v_snd_433_);
lean_dec_ref(v_a_431_);
goto v___jp_445_;
}
}
v___jp_453_:
{
uint32_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = 97;
v___x_456_ = lean_uint32_dec_le(v___x_455_, v_c_443_);
if (v___x_456_ == 0)
{
v___y_450_ = v___y_454_;
v___y_451_ = v___x_456_;
goto v___jp_449_;
}
else
{
uint32_t v___x_457_; uint8_t v___x_458_; 
v___x_457_ = 122;
v___x_458_ = lean_uint32_dec_le(v_c_443_, v___x_457_);
v___y_450_ = v___y_454_;
v___y_451_ = v___x_458_;
goto v___jp_449_;
}
}
}
else
{
lean_object* v___x_463_; 
v___x_463_ = lean_box(0);
lean_inc(v_snd_433_);
v_pos_435_ = v_a_431_;
v_snd_436_ = v_snd_433_;
v_err_437_ = v___x_463_;
goto v___jp_434_;
}
v___jp_434_:
{
uint8_t v_decide_438_; 
v_decide_438_ = lean_nat_dec_eq(v_snd_433_, v_snd_436_);
lean_dec(v_snd_436_);
lean_dec(v_snd_433_);
if (v_decide_438_ == 0)
{
lean_object* v___x_439_; 
lean_dec_ref(v_acc_430_);
lean_inc(v_err_437_);
v___x_439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_439_, 0, v_pos_435_);
lean_ctor_set(v___x_439_, 1, v_err_437_);
return v___x_439_;
}
else
{
lean_object* v___x_440_; 
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v_pos_435_);
lean_ctor_set(v___x_440_, 1, v_acc_430_);
return v___x_440_;
}
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_464_; lean_object* v___x_465_; 
v___x_464_ = 60;
v___x_465_ = lean_box_uint32(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0___boxed__const__1;
v___x_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(lean_object* v_a_471_){
_start:
{
lean_object* v___y_473_; lean_object* v_pos_477_; lean_object* v_res_478_; lean_object* v_fst_532_; lean_object* v_snd_533_; lean_object* v___x_534_; uint8_t v_decide_535_; 
v_fst_532_ = lean_ctor_get(v_a_471_, 0);
v_snd_533_ = lean_ctor_get(v_a_471_, 1);
v___x_534_ = lean_string_utf8_byte_size(v_fst_532_);
v_decide_535_ = lean_nat_dec_eq(v_snd_533_, v___x_534_);
if (v_decide_535_ == 0)
{
uint32_t v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_536_ = lean_string_utf8_get_fast(v_fst_532_, v_snd_533_);
v___x_537_ = lean_box_uint32(v___x_536_);
v___x_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
v_pos_477_ = v_a_471_;
v_res_478_ = v___x_538_;
goto v___jp_476_;
}
else
{
lean_object* v___x_539_; 
v___x_539_ = lean_box(0);
v_pos_477_ = v_a_471_;
v_res_478_ = v___x_539_;
goto v___jp_476_;
}
v___jp_472_:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = lean_box(0);
v___x_475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_475_, 0, v___y_473_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
return v___x_475_;
}
v___jp_476_:
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__0);
v___x_480_ = l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_res_478_, v___x_479_);
lean_dec(v_res_478_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName___closed__0));
v___x_482_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__1(v___x_481_, v_pos_477_);
return v___x_482_;
}
else
{
lean_object* v_fst_483_; lean_object* v_snd_484_; lean_object* v___x_485_; uint8_t v_decide_486_; 
v_fst_483_ = lean_ctor_get(v_pos_477_, 0);
v_snd_484_ = lean_ctor_get(v_pos_477_, 1);
v___x_485_ = lean_string_utf8_byte_size(v_fst_483_);
v_decide_486_ = lean_nat_dec_eq(v_snd_484_, v___x_485_);
if (v_decide_486_ == 0)
{
if (v___x_480_ == 0)
{
v___y_473_ = v_pos_477_;
goto v___jp_472_;
}
else
{
lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_529_; 
lean_inc(v_snd_484_);
lean_inc(v_fst_483_);
v_isSharedCheck_529_ = !lean_is_exclusive(v_pos_477_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; lean_object* v_unused_531_; 
v_unused_530_ = lean_ctor_get(v_pos_477_, 1);
lean_dec(v_unused_530_);
v_unused_531_ = lean_ctor_get(v_pos_477_, 0);
lean_dec(v_unused_531_);
v___x_488_ = v_pos_477_;
v_isShared_489_ = v_isSharedCheck_529_;
goto v_resetjp_487_;
}
else
{
lean_dec(v_pos_477_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_529_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_490_ = lean_string_utf8_next_fast(v_fst_483_, v_snd_484_);
lean_dec(v_snd_484_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v___x_490_);
v___x_492_ = v___x_488_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_fst_483_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v___x_490_);
v___x_492_ = v_reuseFailAlloc_528_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; 
v___x_493_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_quotedName(v___x_492_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_pos_494_; lean_object* v_res_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_527_; 
v_pos_494_ = lean_ctor_get(v___x_493_, 0);
v_res_495_ = lean_ctor_get(v___x_493_, 1);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_527_ == 0)
{
v___x_497_ = v___x_493_;
v_isShared_498_ = v_isSharedCheck_527_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_res_495_);
lean_inc(v_pos_494_);
lean_dec(v___x_493_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_527_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v_fst_499_; lean_object* v_snd_500_; lean_object* v___x_501_; uint8_t v_decide_502_; 
v_fst_499_ = lean_ctor_get(v_pos_494_, 0);
v_snd_500_ = lean_ctor_get(v_pos_494_, 1);
v___x_501_ = lean_string_utf8_byte_size(v_fst_499_);
v_decide_502_ = lean_nat_dec_eq(v_snd_500_, v___x_501_);
if (v_decide_502_ == 0)
{
uint32_t v___x_503_; uint32_t v_c_504_; uint8_t v___x_505_; 
v___x_503_ = 62;
v_c_504_ = lean_string_utf8_get_fast(v_fst_499_, v_snd_500_);
v___x_505_ = lean_uint32_dec_eq(v_c_504_, v___x_503_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_508_; 
lean_dec(v_res_495_);
v___x_506_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName___closed__2));
if (v_isShared_498_ == 0)
{
lean_ctor_set_tag(v___x_497_, 1);
lean_ctor_set(v___x_497_, 1, v___x_506_);
v___x_508_ = v___x_497_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_pos_494_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
else
{
lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_520_; 
lean_inc(v_snd_500_);
lean_inc(v_fst_499_);
v_isSharedCheck_520_ = !lean_is_exclusive(v_pos_494_);
if (v_isSharedCheck_520_ == 0)
{
lean_object* v_unused_521_; lean_object* v_unused_522_; 
v_unused_521_ = lean_ctor_get(v_pos_494_, 1);
lean_dec(v_unused_521_);
v_unused_522_ = lean_ctor_get(v_pos_494_, 0);
lean_dec(v_unused_522_);
v___x_511_ = v_pos_494_;
v_isShared_512_ = v_isSharedCheck_520_;
goto v_resetjp_510_;
}
else
{
lean_dec(v_pos_494_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_520_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v_it_x27_515_; 
v___x_513_ = lean_string_utf8_next_fast(v_fst_499_, v_snd_500_);
lean_dec(v_snd_500_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v___x_513_);
v_it_x27_515_ = v___x_511_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_fst_499_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v___x_513_);
v_it_x27_515_ = v_reuseFailAlloc_519_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_517_; 
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v_it_x27_515_);
v___x_517_ = v___x_497_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_it_x27_515_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_res_495_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
else
{
lean_object* v___x_523_; lean_object* v___x_525_; 
lean_dec(v_res_495_);
v___x_523_ = lean_box(0);
if (v_isShared_498_ == 0)
{
lean_ctor_set_tag(v___x_497_, 1);
lean_ctor_set(v___x_497_, 1, v___x_523_);
v___x_525_ = v___x_497_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_pos_494_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
else
{
return v___x_493_;
}
}
}
}
}
else
{
v___y_473_ = v_pos_477_;
goto v___jp_472_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1(lean_object* v___x_540_, lean_object* v_x_541_){
_start:
{
uint8_t v___x_542_; 
v___x_542_ = lean_int_dec_le(v_x_541_, v___x_540_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1___boxed(lean_object* v___x_543_, lean_object* v_x_544_){
_start:
{
uint8_t v_res_545_; lean_object* v_r_546_; 
v_res_545_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1(v___x_543_, v_x_544_);
lean_dec(v_x_544_);
lean_dec(v___x_543_);
v_r_546_ = lean_box(v_res_545_);
return v_r_546_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_unsigned_to_nat(7u);
v___x_553_ = lean_nat_to_int(v___x_552_);
return v___x_553_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_unsigned_to_nat(5u);
v___x_555_ = lean_nat_to_int(v___x_554_);
return v___x_555_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6(void){
_start:
{
lean_object* v___x_556_; lean_object* v___f_557_; 
v___x_556_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5);
v___f_557_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___lam__1___boxed), 2, 1);
lean_closure_set(v___f_557_, 0, v___x_556_);
return v___f_557_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_unsigned_to_nat(12u);
v___x_563_ = lean_nat_to_int(v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec(lean_object* v_a_565_){
_start:
{
lean_object* v___y_567_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; uint8_t v___y_576_; lean_object* v___y_587_; lean_object* v_fst_590_; lean_object* v_snd_591_; lean_object* v___x_592_; uint8_t v_decide_593_; 
v_fst_590_ = lean_ctor_get(v_a_565_, 0);
v_snd_591_ = lean_ctor_get(v_a_565_, 1);
v___x_592_ = lean_string_utf8_byte_size(v_fst_590_);
v_decide_593_ = lean_nat_dec_eq(v_snd_591_, v___x_592_);
if (v_decide_593_ == 0)
{
uint32_t v___x_594_; uint32_t v_c_595_; uint8_t v___x_596_; 
v___x_594_ = 77;
v_c_595_ = lean_string_utf8_get_fast(v_fst_590_, v_snd_591_);
v___x_596_ = lean_uint32_dec_eq(v_c_595_, v___x_594_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__3));
v___x_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_598_, 0, v_a_565_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
return v___x_598_;
}
else
{
lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_759_; 
lean_inc(v_snd_591_);
lean_inc(v_fst_590_);
v_isSharedCheck_759_ = !lean_is_exclusive(v_a_565_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; lean_object* v_unused_761_; 
v_unused_760_ = lean_ctor_get(v_a_565_, 1);
lean_dec(v_unused_760_);
v_unused_761_ = lean_ctor_get(v_a_565_, 0);
lean_dec(v_unused_761_);
v___x_600_ = v_a_565_;
v_isShared_601_ = v_isSharedCheck_759_;
goto v_resetjp_599_;
}
else
{
lean_dec(v_a_565_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_759_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___f_603_; lean_object* v___x_604_; lean_object* v_it_x27_606_; 
v___x_602_ = lean_box(v___x_596_);
v___f_603_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_603_, 0, v___x_602_);
v___x_604_ = lean_string_utf8_next_fast(v_fst_590_, v_snd_591_);
lean_dec(v_snd_591_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 1, v___x_604_);
v_it_x27_606_ = v___x_600_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_fst_590_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v___x_604_);
v_it_x27_606_ = v_reuseFailAlloc_758_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_618_; uint32_t v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; uint8_t v___y_624_; lean_object* v___y_655_; lean_object* v_pos_656_; lean_object* v_fst_657_; lean_object* v_snd_658_; lean_object* v_res_659_; lean_object* v_pos_668_; lean_object* v_res_669_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_607_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_714_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__10);
v___x_715_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__11));
v___x_716_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_607_, v___x_714_, v___x_715_, v___f_603_, v_it_x27_606_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_pos_717_; lean_object* v_res_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_746_; 
v_pos_717_ = lean_ctor_get(v___x_716_, 0);
v_res_718_ = lean_ctor_get(v___x_716_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_746_ == 0)
{
v___x_720_ = v___x_716_;
v_isShared_721_ = v_isSharedCheck_746_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_res_718_);
lean_inc(v_pos_717_);
lean_dec(v___x_716_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_746_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v_fst_727_; lean_object* v_snd_728_; lean_object* v___x_729_; uint8_t v_decide_730_; 
v_fst_727_ = lean_ctor_get(v_pos_717_, 0);
v_snd_728_ = lean_ctor_get(v_pos_717_, 1);
v___x_729_ = lean_string_utf8_byte_size(v_fst_727_);
v_decide_730_ = lean_nat_dec_eq(v_snd_728_, v___x_729_);
if (v_decide_730_ == 0)
{
if (v___x_596_ == 0)
{
lean_dec(v_res_718_);
goto v___jp_722_;
}
else
{
uint32_t v___x_731_; uint32_t v_c_732_; uint8_t v___x_733_; 
lean_del_object(v___x_720_);
v___x_731_ = 46;
v_c_732_ = lean_string_utf8_get_fast(v_fst_727_, v_snd_728_);
v___x_733_ = lean_uint32_dec_eq(v_c_732_, v___x_731_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; 
lean_dec(v_res_718_);
v___x_734_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9));
v___x_735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_735_, 0, v_pos_717_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
return v___x_735_;
}
else
{
lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_743_; 
lean_inc(v_snd_728_);
lean_inc(v_fst_727_);
v_isSharedCheck_743_ = !lean_is_exclusive(v_pos_717_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; lean_object* v_unused_745_; 
v_unused_744_ = lean_ctor_get(v_pos_717_, 1);
lean_dec(v_unused_744_);
v_unused_745_ = lean_ctor_get(v_pos_717_, 0);
lean_dec(v_unused_745_);
v___x_737_ = v_pos_717_;
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
else
{
lean_dec(v_pos_717_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v_it_x27_741_; 
v___x_739_ = lean_string_utf8_next_fast(v_fst_727_, v_snd_728_);
lean_dec(v_snd_728_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 1, v___x_739_);
v_it_x27_741_ = v___x_737_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_fst_727_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v___x_739_);
v_it_x27_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
v_pos_668_ = v_it_x27_741_;
v_res_669_ = v_res_718_;
goto v___jp_667_;
}
}
}
}
}
else
{
lean_dec(v_res_718_);
goto v___jp_722_;
}
v___jp_722_:
{
lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_723_ = lean_box(0);
if (v_isShared_721_ == 0)
{
lean_ctor_set_tag(v___x_720_, 1);
lean_ctor_set(v___x_720_, 1, v___x_723_);
v___x_725_ = v___x_720_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_pos_717_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_723_);
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
else
{
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_pos_747_; lean_object* v_res_748_; 
v_pos_747_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_pos_747_);
v_res_748_ = lean_ctor_get(v___x_716_, 1);
lean_inc(v_res_748_);
lean_dec_ref_known(v___x_716_, 2);
v_pos_668_ = v_pos_747_;
v_res_669_ = v_res_748_;
goto v___jp_667_;
}
else
{
lean_object* v_pos_749_; lean_object* v_err_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
v_pos_749_ = lean_ctor_get(v___x_716_, 0);
v_err_750_ = lean_ctor_get(v___x_716_, 1);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_716_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_err_750_);
lean_inc(v_pos_749_);
lean_dec(v___x_716_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_pos_749_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_err_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
v___jp_608_:
{
uint8_t v___x_615_; 
v___x_615_ = lean_int_dec_le(v___x_607_, v___y_614_);
if (v___x_615_ == 0)
{
lean_dec(v___y_612_);
v___y_571_ = v___y_609_;
v___y_572_ = v___y_610_;
v___y_573_ = v___y_614_;
v___y_574_ = v___y_611_;
v___y_575_ = v___y_613_;
v___y_576_ = v___x_615_;
goto v___jp_570_;
}
else
{
uint8_t v___x_616_; 
v___x_616_ = lean_int_dec_le(v___y_614_, v___y_612_);
lean_dec(v___y_612_);
v___y_571_ = v___y_609_;
v___y_572_ = v___y_610_;
v___y_573_ = v___y_614_;
v___y_574_ = v___y_611_;
v___y_575_ = v___y_613_;
v___y_576_ = v___x_616_;
goto v___jp_570_;
}
}
v___jp_617_:
{
if (v___y_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v___y_623_);
lean_dec(v___y_622_);
lean_dec(v___y_620_);
lean_dec(v___y_618_);
v___x_625_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat___closed__3));
v___x_626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_626_, 0, v___y_621_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
return v___x_626_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v_fst_632_; lean_object* v_snd_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_653_; 
lean_dec_ref(v___y_621_);
v___x_627_ = lean_string_utf8_next_fast(v___y_622_, v___y_623_);
lean_dec(v___y_623_);
v___x_628_ = lean_uint32_to_nat(v___y_619_);
v___x_629_ = lean_unsigned_to_nat(48u);
v___x_630_ = lean_nat_sub(v___x_628_, v___x_629_);
lean_dec(v___x_628_);
v___x_631_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v___y_622_, v___x_627_, v___x_630_);
v_fst_632_ = lean_ctor_get(v___x_631_, 0);
v_snd_633_ = lean_ctor_get(v___x_631_, 1);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_653_ == 0)
{
v___x_635_ = v___x_631_;
v_isShared_636_ = v_isSharedCheck_653_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_snd_633_);
lean_inc(v_fst_632_);
lean_dec(v___x_631_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_653_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___y_622_);
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___y_622_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_snd_633_);
v___x_638_ = v_reuseFailAlloc_652_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_639_ = lean_unsigned_to_nat(6u);
v___x_640_ = lean_nat_dec_lt(v___x_639_, v_fst_632_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_641_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__4);
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = lean_nat_dec_eq(v_fst_632_, v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; 
lean_inc(v_fst_632_);
v___x_644_ = lean_nat_to_int(v_fst_632_);
v___y_609_ = v___x_638_;
v___y_610_ = v___y_618_;
v___y_611_ = v_fst_632_;
v___y_612_ = v___x_641_;
v___y_613_ = v___y_620_;
v___y_614_ = v___x_644_;
goto v___jp_608_;
}
else
{
v___y_609_ = v___x_638_;
v___y_610_ = v___y_618_;
v___y_611_ = v_fst_632_;
v___y_612_ = v___x_641_;
v___y_613_ = v___y_620_;
v___y_614_ = v___x_641_;
goto v___jp_608_;
}
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
lean_dec(v___y_620_);
lean_dec(v___y_618_);
v___x_645_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0));
v___x_646_ = l_Nat_reprFast(v_fst_632_);
v___x_647_ = lean_string_append(v___x_645_, v___x_646_);
lean_dec_ref(v___x_646_);
v___x_648_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1));
v___x_649_ = lean_string_append(v___x_647_, v___x_648_);
v___x_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
v___x_651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_638_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
return v___x_651_;
}
}
}
}
}
v___jp_654_:
{
lean_object* v___x_660_; uint8_t v_decide_661_; 
v___x_660_ = lean_string_utf8_byte_size(v_fst_657_);
v_decide_661_ = lean_nat_dec_eq(v_snd_658_, v___x_660_);
if (v_decide_661_ == 0)
{
if (v___x_596_ == 0)
{
lean_dec(v_res_659_);
lean_dec(v_snd_658_);
lean_dec(v_fst_657_);
lean_dec(v___y_655_);
v___y_567_ = v_pos_656_;
goto v___jp_566_;
}
else
{
uint32_t v_c_662_; uint32_t v___x_663_; uint8_t v___x_664_; 
v_c_662_ = lean_string_utf8_get_fast(v_fst_657_, v_snd_658_);
v___x_663_ = 48;
v___x_664_ = lean_uint32_dec_le(v___x_663_, v_c_662_);
if (v___x_664_ == 0)
{
v___y_618_ = v___y_655_;
v___y_619_ = v_c_662_;
v___y_620_ = v_res_659_;
v___y_621_ = v_pos_656_;
v___y_622_ = v_fst_657_;
v___y_623_ = v_snd_658_;
v___y_624_ = v___x_664_;
goto v___jp_617_;
}
else
{
uint32_t v___x_665_; uint8_t v___x_666_; 
v___x_665_ = 57;
v___x_666_ = lean_uint32_dec_le(v_c_662_, v___x_665_);
v___y_618_ = v___y_655_;
v___y_619_ = v_c_662_;
v___y_620_ = v_res_659_;
v___y_621_ = v_pos_656_;
v___y_622_ = v_fst_657_;
v___y_623_ = v_snd_658_;
v___y_624_ = v___x_666_;
goto v___jp_617_;
}
}
}
else
{
lean_dec(v_res_659_);
lean_dec(v_snd_658_);
lean_dec(v_fst_657_);
lean_dec(v___y_655_);
v___y_567_ = v_pos_656_;
goto v___jp_566_;
}
}
v___jp_667_:
{
lean_object* v___x_670_; lean_object* v___f_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_670_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__5);
v___f_671_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__6);
v___x_672_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__7));
v___x_673_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_607_, v___x_670_, v___x_672_, v___f_671_, v_pos_668_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_pos_674_; lean_object* v_res_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_700_; 
v_pos_674_ = lean_ctor_get(v___x_673_, 0);
v_res_675_ = lean_ctor_get(v___x_673_, 1);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_700_ == 0)
{
v___x_677_ = v___x_673_;
v_isShared_678_ = v_isSharedCheck_700_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_res_675_);
lean_inc(v_pos_674_);
lean_dec(v___x_673_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_700_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v_fst_679_; lean_object* v_snd_680_; lean_object* v___x_681_; uint8_t v_decide_682_; 
v_fst_679_ = lean_ctor_get(v_pos_674_, 0);
v_snd_680_ = lean_ctor_get(v_pos_674_, 1);
v___x_681_ = lean_string_utf8_byte_size(v_fst_679_);
v_decide_682_ = lean_nat_dec_eq(v_snd_680_, v___x_681_);
if (v_decide_682_ == 0)
{
if (v___x_596_ == 0)
{
lean_del_object(v___x_677_);
lean_dec(v_res_675_);
lean_dec(v_res_669_);
v___y_587_ = v_pos_674_;
goto v___jp_586_;
}
else
{
uint32_t v___x_683_; uint32_t v_c_684_; uint8_t v___x_685_; 
v___x_683_ = 46;
v_c_684_ = lean_string_utf8_get_fast(v_fst_679_, v_snd_680_);
v___x_685_ = lean_uint32_dec_eq(v_c_684_, v___x_683_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_688_; 
lean_dec(v_res_675_);
lean_dec(v_res_669_);
v___x_686_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__9));
if (v_isShared_678_ == 0)
{
lean_ctor_set_tag(v___x_677_, 1);
lean_ctor_set(v___x_677_, 1, v___x_686_);
v___x_688_ = v___x_677_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_pos_674_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
else
{
lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_697_; 
lean_inc(v_snd_680_);
lean_inc(v_fst_679_);
lean_del_object(v___x_677_);
v_isSharedCheck_697_ = !lean_is_exclusive(v_pos_674_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; lean_object* v_unused_699_; 
v_unused_698_ = lean_ctor_get(v_pos_674_, 1);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v_pos_674_, 0);
lean_dec(v_unused_699_);
v___x_691_ = v_pos_674_;
v_isShared_692_ = v_isSharedCheck_697_;
goto v_resetjp_690_;
}
else
{
lean_dec(v_pos_674_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_697_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v_it_x27_695_; 
v___x_693_ = lean_string_utf8_next_fast(v_fst_679_, v_snd_680_);
lean_dec(v_snd_680_);
lean_inc(v_fst_679_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v___x_693_);
v_it_x27_695_ = v___x_691_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_fst_679_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v___x_693_);
v_it_x27_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
v___y_655_ = v_res_669_;
v_pos_656_ = v_it_x27_695_;
v_fst_657_ = v_fst_679_;
v_snd_658_ = v___x_693_;
v_res_659_ = v_res_675_;
goto v___jp_654_;
}
}
}
}
}
else
{
lean_del_object(v___x_677_);
lean_dec(v_res_675_);
lean_dec(v_res_669_);
v___y_587_ = v_pos_674_;
goto v___jp_586_;
}
}
}
else
{
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_pos_701_; lean_object* v_res_702_; lean_object* v_fst_703_; lean_object* v_snd_704_; 
v_pos_701_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_pos_701_);
v_res_702_ = lean_ctor_get(v___x_673_, 1);
lean_inc(v_res_702_);
lean_dec_ref_known(v___x_673_, 2);
v_fst_703_ = lean_ctor_get(v_pos_701_, 0);
lean_inc(v_fst_703_);
v_snd_704_ = lean_ctor_get(v_pos_701_, 1);
lean_inc(v_snd_704_);
v___y_655_ = v_res_669_;
v_pos_656_ = v_pos_701_;
v_fst_657_ = v_fst_703_;
v_snd_658_ = v_snd_704_;
v_res_659_ = v_res_702_;
goto v___jp_654_;
}
else
{
lean_object* v_pos_705_; lean_object* v_err_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec(v_res_669_);
v_pos_705_ = lean_ctor_get(v___x_673_, 0);
v_err_706_ = lean_ctor_get(v___x_673_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_673_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_err_706_);
lean_inc(v_pos_705_);
lean_dec(v___x_673_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_pos_705_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_err_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
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
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_box(0);
v___x_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_763_, 0, v_a_565_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
return v___x_763_;
}
v___jp_566_:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_box(0);
v___x_569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_569_, 0, v___y_567_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
return v___x_569_;
}
v___jp_570_:
{
if (v___y_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v___y_575_);
lean_dec(v___y_573_);
lean_dec(v___y_572_);
v___x_577_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__0));
v___x_578_ = l_Nat_reprFast(v___y_574_);
v___x_579_ = lean_string_append(v___x_577_, v___x_578_);
lean_dec_ref(v___x_578_);
v___x_580_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec___closed__1));
v___x_581_ = lean_string_append(v___x_579_, v___x_580_);
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
v___x_583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_583_, 0, v___y_571_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
return v___x_583_;
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v___y_574_);
v___x_584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_584_, 0, v___y_572_);
lean_ctor_set(v___x_584_, 1, v___y_575_);
lean_ctor_set(v___x_584_, 2, v___y_573_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___y_571_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
return v___x_585_;
}
}
v___jp_586_:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_box(0);
v___x_589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_589_, 0, v___y_587_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
return v___x_589_;
}
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_unsigned_to_nat(365u);
v___x_768_ = lean_nat_to_int(v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec(lean_object* v_a_770_){
_start:
{
lean_object* v_fst_771_; lean_object* v_snd_772_; lean_object* v___x_773_; uint8_t v_decide_774_; 
v_fst_771_ = lean_ctor_get(v_a_770_, 0);
v_snd_772_ = lean_ctor_get(v_a_770_, 1);
v___x_773_ = lean_string_utf8_byte_size(v_fst_771_);
v_decide_774_ = lean_nat_dec_eq(v_snd_772_, v___x_773_);
if (v_decide_774_ == 0)
{
uint32_t v___x_775_; uint32_t v_c_776_; uint8_t v___x_777_; 
v___x_775_ = 74;
v_c_776_ = lean_string_utf8_get_fast(v_fst_771_, v_snd_772_);
v___x_777_ = lean_uint32_dec_eq(v_c_776_, v___x_775_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__1));
v___x_779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_779_, 0, v_a_770_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
return v___x_779_;
}
else
{
lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_812_; 
lean_inc(v_snd_772_);
lean_inc(v_fst_771_);
v_isSharedCheck_812_ = !lean_is_exclusive(v_a_770_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; lean_object* v_unused_814_; 
v_unused_813_ = lean_ctor_get(v_a_770_, 1);
lean_dec(v_unused_813_);
v_unused_814_ = lean_ctor_get(v_a_770_, 0);
lean_dec(v_unused_814_);
v___x_781_ = v_a_770_;
v_isShared_782_ = v_isSharedCheck_812_;
goto v_resetjp_780_;
}
else
{
lean_dec(v_a_770_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_812_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___f_784_; lean_object* v___x_785_; lean_object* v_it_x27_787_; 
v___x_783_ = lean_box(v___x_777_);
v___f_784_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_784_, 0, v___x_783_);
v___x_785_ = lean_string_utf8_next_fast(v_fst_771_, v_snd_772_);
lean_dec(v_snd_772_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v___x_785_);
v_it_x27_787_ = v___x_781_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_fst_771_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___x_785_);
v_it_x27_787_ = v_reuseFailAlloc_811_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_788_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign___closed__0);
v___x_789_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2);
v___x_790_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__3));
v___x_791_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_788_, v___x_789_, v___x_790_, v___f_784_, v_it_x27_787_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_pos_792_; lean_object* v_res_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_801_; 
v_pos_792_ = lean_ctor_get(v___x_791_, 0);
v_res_793_ = lean_ctor_get(v___x_791_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_801_ == 0)
{
v___x_795_ = v___x_791_;
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_res_793_);
lean_inc(v_pos_792_);
lean_dec(v___x_791_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_797_, 0, v_res_793_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v___x_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_pos_792_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
else
{
lean_object* v_pos_802_; lean_object* v_err_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
v_pos_802_ = lean_ctor_get(v___x_791_, 0);
v_err_803_ = lean_ctor_get(v___x_791_, 1);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_791_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_err_803_);
lean_inc(v_pos_802_);
lean_dec(v___x_791_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_pos_802_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_err_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_box(0);
v___x_816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_816_, 0, v_a_770_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
return v___x_816_;
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0(lean_object* v_x_817_){
_start:
{
uint8_t v___x_818_; 
v___x_818_ = 1;
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0___boxed(lean_object* v_x_819_){
_start:
{
uint8_t v_res_820_; lean_object* v_r_821_; 
v_res_820_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___lam__0(v_x_819_);
lean_dec(v_x_819_);
v_r_821_ = lean_box(v_res_820_);
return v_r_821_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec(lean_object* v_a_824_){
_start:
{
lean_object* v___f_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___f_825_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__0));
v___x_826_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__2);
v___x_827_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec___closed__2);
v___x_828_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec___closed__1));
v___x_829_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parseBoundedNat(v___x_826_, v___x_827_, v___x_828_, v___f_825_, v_a_824_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_pos_830_; lean_object* v_res_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_839_; 
v_pos_830_ = lean_ctor_get(v___x_829_, 0);
v_res_831_ = lean_ctor_get(v___x_829_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_839_ == 0)
{
v___x_833_ = v___x_829_;
v_isShared_834_ = v_isSharedCheck_839_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_res_831_);
lean_inc(v_pos_830_);
lean_dec(v___x_829_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_839_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_835_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_835_, 0, v_res_831_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v___x_835_);
v___x_837_ = v___x_833_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_pos_830_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
else
{
lean_object* v_pos_840_; lean_object* v_err_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
v_pos_840_ = lean_ctor_get(v___x_829_, 0);
v_err_841_ = lean_ctor_get(v___x_829_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_829_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_err_841_);
lean_inc(v_pos_840_);
lean_dec(v___x_829_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_pos_840_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_err_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(lean_object* v_stdOffset_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_fst_851_; lean_object* v_snd_852_; lean_object* v___x_853_; uint8_t v_decide_854_; 
v_fst_851_ = lean_ctor_get(v_a_850_, 0);
v_snd_852_ = lean_ctor_get(v_a_850_, 1);
v___x_853_ = lean_string_utf8_byte_size(v_fst_851_);
v_decide_854_ = lean_nat_dec_eq(v_snd_852_, v___x_853_);
if (v_decide_854_ == 0)
{
uint32_t v___x_855_; uint32_t v___x_866_; uint8_t v___x_867_; 
v___x_855_ = lean_string_utf8_get_fast(v_fst_851_, v_snd_852_);
v___x_866_ = 48;
v___x_867_ = lean_uint32_dec_le(v___x_866_, v___x_855_);
if (v___x_867_ == 0)
{
goto v___jp_856_;
}
else
{
uint32_t v___x_868_; uint8_t v___x_869_; 
v___x_868_ = 57;
v___x_869_ = lean_uint32_dec_le(v___x_855_, v___x_868_);
if (v___x_869_ == 0)
{
goto v___jp_856_;
}
else
{
lean_object* v___x_870_; 
v___x_870_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_850_);
return v___x_870_;
}
}
v___jp_856_:
{
uint32_t v___x_857_; uint8_t v___x_858_; 
v___x_857_ = 43;
v___x_858_ = lean_uint32_dec_eq(v___x_855_, v___x_857_);
if (v___x_858_ == 0)
{
uint32_t v___x_859_; uint8_t v___x_860_; 
v___x_859_ = 45;
v___x_860_ = lean_uint32_dec_eq(v___x_855_, v___x_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_861_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0);
v___x_862_ = lean_int_add(v_stdOffset_849_, v___x_861_);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v_a_850_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
return v___x_863_;
}
else
{
lean_object* v___x_864_; 
v___x_864_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_850_);
return v___x_864_;
}
}
else
{
lean_object* v___x_865_; 
v___x_865_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_a_850_);
return v___x_865_;
}
}
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_871_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0);
v___x_872_ = lean_int_add(v_stdOffset_849_, v___x_871_);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v_a_850_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
return v___x_873_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset___boxed(lean_object* v_stdOffset_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(v_stdOffset_874_, v_a_875_);
lean_dec(v_stdOffset_874_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSpec(lean_object* v_a_877_){
_start:
{
lean_object* v_snd_879_; lean_object* v___y_880_; lean_object* v_pos_881_; lean_object* v_snd_882_; lean_object* v___y_886_; lean_object* v_pos_887_; lean_object* v___x_903_; 
lean_inc_ref(v_a_877_);
v___x_903_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseMwdSpec(v_a_877_);
if (lean_obj_tag(v___x_903_) == 0)
{
if (lean_obj_tag(v___x_903_) == 0)
{
lean_dec_ref(v_a_877_);
return v___x_903_;
}
else
{
lean_object* v_pos_904_; 
v_pos_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_pos_904_);
v___y_886_ = v___x_903_;
v_pos_887_ = v_pos_904_;
goto v___jp_885_;
}
}
else
{
lean_object* v_err_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
v_err_905_ = lean_ctor_get(v___x_903_, 1);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; 
v_unused_913_ = lean_ctor_get(v___x_903_, 0);
lean_dec(v_unused_913_);
v___x_907_ = v___x_903_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_err_905_);
lean_dec(v___x_903_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
lean_inc_ref(v_a_877_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v_a_877_);
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_877_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_err_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_inc_ref(v_a_877_);
v___y_886_ = v___x_910_;
v_pos_887_ = v_a_877_;
goto v___jp_885_;
}
}
}
v___jp_878_:
{
uint8_t v_decide_883_; 
v_decide_883_ = lean_nat_dec_eq(v_snd_879_, v_snd_882_);
lean_dec(v_snd_882_);
lean_dec(v_snd_879_);
if (v_decide_883_ == 0)
{
lean_dec_ref(v_pos_881_);
return v___y_880_;
}
else
{
lean_object* v___x_884_; 
lean_dec_ref(v___y_880_);
v___x_884_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulian0Spec(v_pos_881_);
return v___x_884_;
}
}
v___jp_885_:
{
lean_object* v_snd_888_; lean_object* v_snd_889_; uint8_t v_decide_890_; 
v_snd_888_ = lean_ctor_get(v_a_877_, 1);
lean_inc(v_snd_888_);
lean_dec_ref(v_a_877_);
v_snd_889_ = lean_ctor_get(v_pos_887_, 1);
lean_inc(v_snd_889_);
v_decide_890_ = lean_nat_dec_eq(v_snd_888_, v_snd_889_);
lean_dec(v_snd_888_);
if (v_decide_890_ == 0)
{
lean_dec(v_snd_889_);
lean_dec_ref(v_pos_887_);
return v___y_886_;
}
else
{
lean_object* v___x_891_; 
lean_dec_ref(v___y_886_);
lean_inc_ref(v_pos_887_);
v___x_891_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseJulianSpec(v_pos_887_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_dec_ref(v_pos_887_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_dec(v_snd_889_);
return v___x_891_;
}
else
{
lean_object* v_pos_892_; lean_object* v_snd_893_; 
v_pos_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_pos_892_);
v_snd_893_ = lean_ctor_get(v_pos_892_, 1);
lean_inc(v_snd_893_);
v_snd_879_ = v_snd_889_;
v___y_880_ = v___x_891_;
v_pos_881_ = v_pos_892_;
v_snd_882_ = v_snd_893_;
goto v___jp_878_;
}
}
else
{
lean_object* v_err_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
v_err_894_ = lean_ctor_get(v___x_891_, 1);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; 
v_unused_902_ = lean_ctor_get(v___x_891_, 0);
lean_dec(v_unused_902_);
v___x_896_ = v___x_891_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_err_894_);
lean_dec(v___x_891_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
lean_inc_ref(v_pos_887_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v_pos_887_);
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_pos_887_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_err_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_inc(v_snd_889_);
v_snd_879_ = v_snd_889_;
v___y_880_ = v___x_899_;
v_pos_881_ = v_pos_887_;
v_snd_882_ = v_snd_889_;
goto v___jp_878_;
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
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_unsigned_to_nat(2u);
v___x_915_ = lean_nat_to_int(v___x_914_);
return v___x_915_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS___closed__0);
v___x_917_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__0);
v___x_918_ = lean_int_mul(v___x_917_, v___x_916_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(uint8_t v_extended_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSpec(v_a_923_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_pos_925_; lean_object* v_res_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_970_; 
v_pos_925_ = lean_ctor_get(v___x_924_, 0);
v_res_926_ = lean_ctor_get(v___x_924_, 1);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_970_ == 0)
{
v___x_928_ = v___x_924_;
v_isShared_929_ = v_isSharedCheck_970_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_res_926_);
lean_inc(v_pos_925_);
lean_dec(v___x_924_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_970_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v_pos_931_; lean_object* v_res_932_; lean_object* v_fst_937_; lean_object* v_snd_938_; lean_object* v_pos_940_; lean_object* v_snd_941_; lean_object* v_err_942_; lean_object* v___x_946_; uint8_t v_decide_947_; 
v_fst_937_ = lean_ctor_get(v_pos_925_, 0);
v_snd_938_ = lean_ctor_get(v_pos_925_, 1);
lean_inc(v_snd_938_);
v___x_946_ = lean_string_utf8_byte_size(v_fst_937_);
v_decide_947_ = lean_nat_dec_eq(v_snd_938_, v___x_946_);
if (v_decide_947_ == 0)
{
uint32_t v___x_948_; uint32_t v_c_949_; uint8_t v___x_950_; 
v___x_948_ = 47;
v_c_949_ = lean_string_utf8_get_fast(v_fst_937_, v_snd_938_);
v___x_950_ = lean_uint32_dec_eq(v_c_949_, v___x_948_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; 
v___x_951_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__3));
lean_inc(v_snd_938_);
v_pos_940_ = v_pos_925_;
v_snd_941_ = v_snd_938_;
v_err_942_ = v___x_951_;
goto v___jp_939_;
}
else
{
lean_object* v___x_952_; lean_object* v_it_x27_953_; lean_object* v___x_954_; 
v___x_952_ = lean_string_utf8_next_fast(v_fst_937_, v_snd_938_);
lean_inc(v_fst_937_);
v_it_x27_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_953_, 0, v_fst_937_);
lean_ctor_set(v_it_x27_953_, 1, v___x_952_);
v___x_954_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseSign(v_it_x27_953_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_pos_955_; lean_object* v_res_956_; lean_object* v___y_958_; 
v_pos_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_pos_955_);
v_res_956_ = lean_ctor_get(v___x_954_, 1);
lean_inc(v_res_956_);
lean_dec_ref_known(v___x_954_, 2);
if (v_extended_922_ == 0)
{
lean_object* v___x_966_; 
v___x_966_ = lean_unsigned_to_nat(24u);
v___y_958_ = v___x_966_;
goto v___jp_957_;
}
else
{
lean_object* v___x_967_; 
v___x_967_ = lean_unsigned_to_nat(167u);
v___y_958_ = v___x_967_;
goto v___jp_957_;
}
v___jp_957_:
{
lean_object* v___x_959_; 
v___x_959_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseHMS(v___y_958_, v_pos_955_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_pos_960_; lean_object* v_res_961_; lean_object* v___x_962_; 
lean_dec(v_snd_938_);
lean_dec(v_pos_925_);
v_pos_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_pos_960_);
v_res_961_ = lean_ctor_get(v___x_959_, 1);
lean_inc(v_res_961_);
lean_dec_ref_known(v___x_959_, 2);
v___x_962_ = lean_int_mul(v_res_956_, v_res_961_);
lean_dec(v_res_961_);
lean_dec(v_res_956_);
v_pos_931_ = v_pos_960_;
v_res_932_ = v___x_962_;
goto v___jp_930_;
}
else
{
lean_dec(v_res_956_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_pos_963_; lean_object* v_res_964_; 
lean_dec(v_snd_938_);
lean_dec(v_pos_925_);
v_pos_963_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_pos_963_);
v_res_964_ = lean_ctor_get(v___x_959_, 1);
lean_inc(v_res_964_);
lean_dec_ref_known(v___x_959_, 2);
v_pos_931_ = v_pos_963_;
v_res_932_ = v_res_964_;
goto v___jp_930_;
}
else
{
lean_object* v_err_965_; 
v_err_965_ = lean_ctor_get(v___x_959_, 1);
lean_inc(v_err_965_);
lean_dec_ref_known(v___x_959_, 2);
lean_inc(v_snd_938_);
v_pos_940_ = v_pos_925_;
v_snd_941_ = v_snd_938_;
v_err_942_ = v_err_965_;
goto v___jp_939_;
}
}
}
}
else
{
lean_object* v_err_968_; 
v_err_968_ = lean_ctor_get(v___x_954_, 1);
lean_inc(v_err_968_);
lean_dec_ref_known(v___x_954_, 2);
lean_inc(v_snd_938_);
v_pos_940_ = v_pos_925_;
v_snd_941_ = v_snd_938_;
v_err_942_ = v_err_968_;
goto v___jp_939_;
}
}
}
else
{
lean_object* v___x_969_; 
v___x_969_ = lean_box(0);
lean_inc(v_snd_938_);
v_pos_940_ = v_pos_925_;
v_snd_941_ = v_snd_938_;
v_err_942_ = v___x_969_;
goto v___jp_939_;
}
v___jp_930_:
{
lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v_res_926_);
lean_ctor_set(v___x_933_, 1, v_res_932_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 1, v___x_933_);
lean_ctor_set(v___x_928_, 0, v_pos_931_);
v___x_935_ = v___x_928_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_pos_931_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
v___jp_939_:
{
uint8_t v_decide_943_; 
v_decide_943_ = lean_nat_dec_eq(v_snd_938_, v_snd_941_);
lean_dec(v_snd_941_);
lean_dec(v_snd_938_);
if (v_decide_943_ == 0)
{
lean_object* v___x_944_; 
lean_del_object(v___x_928_);
lean_dec(v_res_926_);
v___x_944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_944_, 0, v_pos_940_);
lean_ctor_set(v___x_944_, 1, v_err_942_);
return v___x_944_;
}
else
{
lean_object* v___x_945_; 
lean_dec(v_err_942_);
v___x_945_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___closed__1);
v_pos_931_ = v_pos_940_;
v_res_932_ = v___x_945_;
goto v___jp_930_;
}
}
}
}
else
{
lean_object* v_pos_971_; lean_object* v_err_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
v_pos_971_ = lean_ctor_get(v___x_924_, 0);
v_err_972_ = lean_ctor_get(v___x_924_, 1);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_924_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_err_972_);
lean_inc(v_pos_971_);
lean_dec(v___x_924_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_pos_971_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_err_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule___boxed(lean_object* v_extended_980_, lean_object* v_a_981_){
_start:
{
uint8_t v_extended_boxed_982_; lean_object* v_res_983_; 
v_extended_boxed_982_ = lean_unbox(v_extended_980_);
v_res_983_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_boxed_982_, v_a_981_);
return v_res_983_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_987_; lean_object* v___x_988_; 
v___x_987_ = 44;
v___x_988_ = lean_box_uint32(v___x_987_);
return v___x_988_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2___boxed__const__1;
v___x_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP(uint8_t v_extended_994_, lean_object* v_a_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(v_a_995_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_pos_997_; lean_object* v_res_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1180_; 
v_pos_997_ = lean_ctor_get(v___x_996_, 0);
v_res_998_ = lean_ctor_get(v___x_996_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1000_ = v___x_996_;
v_isShared_1001_ = v_isSharedCheck_1180_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_res_998_);
lean_inc(v_pos_997_);
lean_dec(v___x_996_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1180_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1002_ = lean_string_utf8_byte_size(v_res_998_);
v___x_1003_ = lean_unsigned_to_nat(0u);
v___x_1004_ = lean_nat_dec_eq(v___x_1002_, v___x_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; 
v___x_1005_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseOffset(v_pos_997_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_pos_1006_; lean_object* v_res_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1166_; 
v_pos_1006_ = lean_ctor_get(v___x_1005_, 0);
v_res_1007_ = lean_ctor_get(v___x_1005_, 1);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1009_ = v___x_1005_;
v_isShared_1010_ = v_isSharedCheck_1166_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_res_1007_);
lean_inc(v_pos_1006_);
lean_dec(v___x_1005_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1166_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; uint32_t v___y_1017_; lean_object* v___y_1018_; uint8_t v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; uint32_t v___y_1057_; lean_object* v___y_1058_; uint8_t v___y_1059_; uint8_t v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v_pos_1094_; lean_object* v_res_1095_; lean_object* v___y_1109_; uint8_t v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v_fst_1159_; lean_object* v_snd_1160_; lean_object* v___x_1161_; uint8_t v_decide_1162_; 
v_fst_1159_ = lean_ctor_get(v_pos_1006_, 0);
v_snd_1160_ = lean_ctor_get(v_pos_1006_, 1);
v___x_1161_ = lean_string_utf8_byte_size(v_fst_1159_);
v_decide_1162_ = lean_nat_dec_eq(v_snd_1160_, v___x_1161_);
if (v_decide_1162_ == 0)
{
goto v___jp_1118_;
}
else
{
if (v___x_1004_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_del_object(v___x_1009_);
lean_del_object(v___x_1000_);
v___x_1163_ = lean_box(0);
v___x_1164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1164_, 0, v_res_998_);
lean_ctor_set(v___x_1164_, 1, v_res_1007_);
lean_ctor_set(v___x_1164_, 2, v___x_1163_);
v___x_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1165_, 0, v_pos_1006_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
return v___x_1165_;
}
else
{
goto v___jp_1118_;
}
}
v___jp_1011_:
{
uint32_t v_c_1019_; uint8_t v___x_1020_; 
v_c_1019_ = lean_string_utf8_get_fast(v___y_1018_, v___y_1015_);
v___x_1020_ = lean_uint32_dec_eq(v_c_1019_, v___y_1017_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1023_; 
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec(v_res_1007_);
lean_dec(v_res_998_);
v___x_1021_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__1));
if (v_isShared_1010_ == 0)
{
lean_ctor_set_tag(v___x_1009_, 1);
lean_ctor_set(v___x_1009_, 1, v___x_1021_);
lean_ctor_set(v___x_1009_, 0, v___y_1014_);
v___x_1023_ = v___x_1009_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___y_1014_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
else
{
lean_object* v___x_1025_; lean_object* v_it_x27_1026_; lean_object* v___x_1027_; 
lean_dec_ref(v___y_1014_);
lean_del_object(v___x_1009_);
v___x_1025_ = lean_string_utf8_next_fast(v___y_1018_, v___y_1015_);
lean_dec(v___y_1015_);
v_it_x27_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_1026_, 0, v___y_1018_);
lean_ctor_set(v_it_x27_1026_, 1, v___x_1025_);
v___x_1027_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_994_, v_it_x27_1026_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_pos_1028_; lean_object* v_res_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1041_; 
v_pos_1028_ = lean_ctor_get(v___x_1027_, 0);
v_res_1029_ = lean_ctor_get(v___x_1027_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1031_ = v___x_1027_;
v_isShared_1032_ = v_isSharedCheck_1041_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_res_1029_);
lean_inc(v_pos_1028_);
lean_dec(v___x_1027_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1041_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___y_1013_);
v___x_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1034_, 0, v_res_1029_);
v___x_1035_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1035_, 0, v___y_1016_);
lean_ctor_set(v___x_1035_, 1, v___y_1012_);
lean_ctor_set(v___x_1035_, 2, v___x_1033_);
lean_ctor_set(v___x_1035_, 3, v___x_1034_);
v___x_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
v___x_1037_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1037_, 0, v_res_998_);
lean_ctor_set(v___x_1037_, 1, v_res_1007_);
lean_ctor_set(v___x_1037_, 2, v___x_1036_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 1, v___x_1037_);
v___x_1039_ = v___x_1031_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_pos_1028_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
else
{
lean_object* v_pos_1042_; lean_object* v_err_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec_ref(v___y_1016_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec(v_res_1007_);
lean_dec(v_res_998_);
v_pos_1042_ = lean_ctor_get(v___x_1027_, 0);
v_err_1043_ = lean_ctor_get(v___x_1027_, 1);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1027_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_err_1043_);
lean_inc(v_pos_1042_);
lean_dec(v___x_1027_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_pos_1042_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_err_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
v___jp_1051_:
{
if (v___y_1059_ == 0)
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec(v___y_1053_);
lean_del_object(v___x_1009_);
lean_dec(v_res_1007_);
lean_dec(v_res_998_);
v___x_1060_ = lean_box(0);
if (v_isShared_1001_ == 0)
{
lean_ctor_set_tag(v___x_1000_, 1);
lean_ctor_set(v___x_1000_, 1, v___x_1060_);
lean_ctor_set(v___x_1000_, 0, v___y_1054_);
v___x_1062_ = v___x_1000_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___y_1054_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_dec_ref(v___y_1054_);
lean_del_object(v___x_1000_);
v___x_1064_ = lean_string_utf8_next_fast(v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___y_1055_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseRule(v_extended_994_, v___x_1065_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_pos_1067_; lean_object* v_res_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1080_; 
v_pos_1067_ = lean_ctor_get(v___x_1066_, 0);
v_res_1068_ = lean_ctor_get(v___x_1066_, 1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1070_ = v___x_1066_;
v_isShared_1071_ = v_isSharedCheck_1080_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_res_1068_);
lean_inc(v_pos_1067_);
lean_dec(v___x_1066_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1080_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v_fst_1072_; lean_object* v_snd_1073_; lean_object* v___x_1074_; uint8_t v_decide_1075_; 
v_fst_1072_ = lean_ctor_get(v_pos_1067_, 0);
v_snd_1073_ = lean_ctor_get(v_pos_1067_, 1);
v___x_1074_ = lean_string_utf8_byte_size(v_fst_1072_);
v_decide_1075_ = lean_nat_dec_eq(v_snd_1073_, v___x_1074_);
if (v_decide_1075_ == 0)
{
lean_inc(v_snd_1073_);
lean_inc(v_fst_1072_);
lean_del_object(v___x_1070_);
v___y_1012_ = v___y_1053_;
v___y_1013_ = v_res_1068_;
v___y_1014_ = v_pos_1067_;
v___y_1015_ = v_snd_1073_;
v___y_1016_ = v___y_1058_;
v___y_1017_ = v___y_1057_;
v___y_1018_ = v_fst_1072_;
goto v___jp_1011_;
}
else
{
if (v___y_1052_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
lean_dec(v_res_1068_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1053_);
lean_del_object(v___x_1009_);
lean_dec(v_res_1007_);
lean_dec(v_res_998_);
v___x_1076_ = lean_box(0);
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 1);
lean_ctor_set(v___x_1070_, 1, v___x_1076_);
v___x_1078_ = v___x_1070_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_pos_1067_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
else
{
lean_inc(v_snd_1073_);
lean_inc(v_fst_1072_);
lean_del_object(v___x_1070_);
v___y_1012_ = v___y_1053_;
v___y_1013_ = v_res_1068_;
v___y_1014_ = v_pos_1067_;
v___y_1015_ = v_snd_1073_;
v___y_1016_ = v___y_1058_;
v___y_1017_ = v___y_1057_;
v___y_1018_ = v_fst_1072_;
goto v___jp_1011_;
}
}
}
}
else
{
lean_object* v_pos_1081_; lean_object* v_err_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1053_);
lean_del_object(v___x_1009_);
lean_dec(v_res_1007_);
lean_dec(v_res_998_);
v_pos_1081_ = lean_ctor_get(v___x_1066_, 0);
v_err_1082_ = lean_ctor_get(v___x_1066_, 1);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1066_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_err_1082_);
lean_inc(v_pos_1081_);
lean_dec(v___x_1066_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_pos_1081_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_err_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
v___jp_1090_:
{
uint32_t v___x_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1096_ = 44;
v___x_1097_ = lean_obj_once(&l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2, &l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2_once, _init_l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__2);
v___x_1098_ = l_Option_instBEq_beq___at___00__private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName_spec__0(v_res_1095_, v___x_1097_);
lean_dec(v_res_1095_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_del_object(v___x_1009_);
lean_del_object(v___x_1000_);
v___x_1099_ = lean_box(0);
v___x_1100_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1100_, 0, v___y_1093_);
lean_ctor_set(v___x_1100_, 1, v___y_1092_);
lean_ctor_set(v___x_1100_, 2, v___x_1099_);
lean_ctor_set(v___x_1100_, 3, v___x_1099_);
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
v___x_1102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1102_, 0, v_res_998_);
lean_ctor_set(v___x_1102_, 1, v_res_1007_);
lean_ctor_set(v___x_1102_, 2, v___x_1101_);
v___x_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1103_, 0, v_pos_1094_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
return v___x_1103_;
}
else
{
lean_object* v_fst_1104_; lean_object* v_snd_1105_; lean_object* v___x_1106_; uint8_t v_decide_1107_; 
v_fst_1104_ = lean_ctor_get(v_pos_1094_, 0);
lean_inc(v_fst_1104_);
v_snd_1105_ = lean_ctor_get(v_pos_1094_, 1);
lean_inc(v_snd_1105_);
v___x_1106_ = lean_string_utf8_byte_size(v_fst_1104_);
v_decide_1107_ = lean_nat_dec_eq(v_snd_1105_, v___x_1106_);
if (v_decide_1107_ == 0)
{
v___y_1052_ = v___y_1091_;
v___y_1053_ = v___y_1092_;
v___y_1054_ = v_pos_1094_;
v___y_1055_ = v_fst_1104_;
v___y_1056_ = v_snd_1105_;
v___y_1057_ = v___x_1096_;
v___y_1058_ = v___y_1093_;
v___y_1059_ = v___x_1098_;
goto v___jp_1051_;
}
else
{
v___y_1052_ = v___y_1091_;
v___y_1053_ = v___y_1092_;
v___y_1054_ = v_pos_1094_;
v___y_1055_ = v_fst_1104_;
v___y_1056_ = v_snd_1105_;
v___y_1057_ = v___x_1096_;
v___y_1058_ = v___y_1093_;
v___y_1059_ = v___y_1091_;
goto v___jp_1051_;
}
}
}
v___jp_1108_:
{
uint32_t v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = lean_string_utf8_get_fast(v___y_1113_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec(v___y_1113_);
v___x_1116_ = lean_box_uint32(v___x_1115_);
v___x_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
v___y_1091_ = v___y_1110_;
v___y_1092_ = v___y_1109_;
v___y_1093_ = v___y_1114_;
v_pos_1094_ = v___y_1111_;
v_res_1095_ = v___x_1117_;
goto v___jp_1090_;
}
v___jp_1118_:
{
lean_object* v___x_1119_; 
v___x_1119_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseName(v_pos_1006_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_pos_1120_; lean_object* v_res_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1149_; 
v_pos_1120_ = lean_ctor_get(v___x_1119_, 0);
v_res_1121_ = lean_ctor_get(v___x_1119_, 1);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1123_ = v___x_1119_;
v_isShared_1124_ = v_isSharedCheck_1149_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_res_1121_);
lean_inc(v_pos_1120_);
lean_dec(v___x_1119_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1149_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = lean_string_utf8_byte_size(v_res_1121_);
v___x_1126_ = lean_nat_dec_eq(v___x_1125_, v___x_1003_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; 
lean_del_object(v___x_1123_);
v___x_1127_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_posixParseDstOffset(v_res_1007_, v_pos_1120_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_pos_1128_; lean_object* v_res_1129_; lean_object* v_fst_1130_; lean_object* v_snd_1131_; lean_object* v___x_1132_; uint8_t v_decide_1133_; 
v_pos_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_pos_1128_);
v_res_1129_ = lean_ctor_get(v___x_1127_, 1);
lean_inc(v_res_1129_);
lean_dec_ref_known(v___x_1127_, 2);
v_fst_1130_ = lean_ctor_get(v_pos_1128_, 0);
v_snd_1131_ = lean_ctor_get(v_pos_1128_, 1);
v___x_1132_ = lean_string_utf8_byte_size(v_fst_1130_);
v_decide_1133_ = lean_nat_dec_eq(v_snd_1131_, v___x_1132_);
if (v_decide_1133_ == 0)
{
lean_inc(v_snd_1131_);
lean_inc(v_fst_1130_);
v___y_1109_ = v_res_1129_;
v___y_1110_ = v___x_1126_;
v___y_1111_ = v_pos_1128_;
v___y_1112_ = v_snd_1131_;
v___y_1113_ = v_fst_1130_;
v___y_1114_ = v_res_1121_;
goto v___jp_1108_;
}
else
{
if (v___x_1126_ == 0)
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_box(0);
v___y_1091_ = v___x_1126_;
v___y_1092_ = v_res_1129_;
v___y_1093_ = v_res_1121_;
v_pos_1094_ = v_pos_1128_;
v_res_1095_ = v___x_1134_;
goto v___jp_1090_;
}
else
{
lean_inc(v_snd_1131_);
lean_inc(v_fst_1130_);
v___y_1109_ = v_res_1129_;
v___y_1110_ = v___x_1126_;
v___y_1111_ = v_pos_1128_;
v___y_1112_ = v_snd_1131_;
v___y_1113_ = v_fst_1130_;
v___y_1114_ = v_res_1121_;
goto v___jp_1108_;
}
}
}
else
{
lean_object* v_pos_1135_; lean_object* v_err_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec(v_res_1121_);
lean_del_object(v___x_1009_);
lean_dec(v_res_1007_);
lean_del_object(v___x_1000_);
lean_dec(v_res_998_);
v_pos_1135_ = lean_ctor_get(v___x_1127_, 0);
v_err_1136_ = lean_ctor_get(v___x_1127_, 1);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1127_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_err_1136_);
lean_inc(v_pos_1135_);
lean_dec(v___x_1127_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_pos_1135_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_err_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1147_; 
lean_dec(v_res_1121_);
lean_del_object(v___x_1009_);
lean_del_object(v___x_1000_);
v___x_1144_ = lean_box(0);
v___x_1145_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1145_, 0, v_res_998_);
lean_ctor_set(v___x_1145_, 1, v_res_1007_);
lean_ctor_set(v___x_1145_, 2, v___x_1144_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 1, v___x_1145_);
v___x_1147_ = v___x_1123_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_pos_1120_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
else
{
lean_object* v_pos_1150_; lean_object* v_err_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_del_object(v___x_1009_);
lean_dec(v_res_1007_);
lean_del_object(v___x_1000_);
lean_dec(v_res_998_);
v_pos_1150_ = lean_ctor_get(v___x_1119_, 0);
v_err_1151_ = lean_ctor_get(v___x_1119_, 1);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1119_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_err_1151_);
lean_inc(v_pos_1150_);
lean_dec(v___x_1119_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_pos_1150_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_err_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
}
else
{
lean_object* v_pos_1167_; lean_object* v_err_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_del_object(v___x_1000_);
lean_dec(v_res_998_);
v_pos_1167_ = lean_ctor_get(v___x_1005_, 0);
v_err_1168_ = lean_ctor_get(v___x_1005_, 1);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1005_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_err_1168_);
lean_inc(v_pos_1167_);
lean_dec(v___x_1005_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_pos_1167_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_err_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
lean_dec(v_res_998_);
v___x_1176_ = ((lean_object*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___closed__4));
if (v_isShared_1001_ == 0)
{
lean_ctor_set_tag(v___x_1000_, 1);
lean_ctor_set(v___x_1000_, 1, v___x_1176_);
v___x_1178_ = v___x_1000_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_pos_997_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
else
{
lean_object* v_pos_1181_; lean_object* v_err_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
v_pos_1181_ = lean_ctor_get(v___x_996_, 0);
v_err_1182_ = lean_ctor_get(v___x_996_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_996_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_err_1182_);
lean_inc(v_pos_1181_);
lean_dec(v___x_996_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_pos_1181_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_err_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___boxed(lean_object* v_extended_1190_, lean_object* v_a_1191_){
_start:
{
uint8_t v_extended_boxed_1192_; lean_object* v_res_1193_; 
v_extended_boxed_1192_ = lean_unbox(v_extended_1190_);
v_res_1193_ = l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP(v_extended_boxed_1192_, v_a_1191_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_parsePosixTz(lean_object* v_s_1194_, uint8_t v_extended_1195_){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = lean_box(v_extended_1195_);
v___x_1197_ = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Database_PosixTz_0__Std_Time_TimeZone_parsePosixTzP___boxed), 2, 1);
lean_closure_set(v___x_1197_, 0, v___x_1196_);
v___x_1198_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_1197_, v_s_1194_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_parsePosixTz___boxed(lean_object* v_s_1199_, lean_object* v_extended_1200_){
_start:
{
uint8_t v_extended_boxed_1201_; lean_object* v_res_1202_; 
v_extended_boxed_1201_ = lean_unbox(v_extended_1200_);
v_res_1202_ = l_Std_Time_TimeZone_parsePosixTz(v_s_1199_, v_extended_boxed_1201_);
return v_res_1202_;
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
