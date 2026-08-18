// Lean compiler output
// Module: Std.Time.Format.Basic
// Imports: public import Std.Time.Zoned public import Std.Time.Format.Modifier public import Std.Time.Format.DateFormat import Init.Data.String.TakeDrop import Init.Data.String.Search
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Time_parseModifier(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Time_DateFormat_enUS;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Std_Time_Weekday_ofOrdinal(lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_Internal_Parsec_String_pstring(lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x21(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Std_Time_Weekday_toOrdinal(uint8_t);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Std_Time_TimeZone_Offset_zero;
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_Std_Time_PlainTime_ofNanoseconds(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
lean_object* l_Std_Time_PlainDate_weekYear(lean_object*, uint8_t, lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*, uint8_t, lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfMonth(lean_object*, uint8_t);
lean_object* l_Std_Time_DateTime_alignedWeekOfMonth(lean_object*);
uint8_t l_Std_Time_HourMarker_ofOrdinal(lean_object*);
lean_object* l_Std_Time_HourMarker_toRelative(lean_object*);
lean_object* l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(lean_object*);
lean_object* l_Std_Time_PlainTime_toMilliseconds(lean_object*);
lean_object* l_Std_Time_PlainTime_toNanoseconds(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Second_instOfNatOrdinal(uint8_t, lean_object*);
lean_object* l_Std_Time_PlainDateTime_toWallTime(lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
lean_object* l_Std_Time_HourMarker_toAbsolute(uint8_t, lean_object*);
lean_object* l_Std_Time_TimeZone_Offset_toIsoString(lean_object*, uint8_t);
extern lean_object* l_Std_Time_instInhabitedDateTime;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_Time_instReprModifier_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_string_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_string_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_modifier_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_modifier_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_instReprFormatPart_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Std.Time.FormatPart.string"};
static const lean_object* l_Std_Time_instReprFormatPart_repr___closed__0 = (const lean_object*)&l_Std_Time_instReprFormatPart_repr___closed__0_value;
static const lean_ctor_object l_Std_Time_instReprFormatPart_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprFormatPart_repr___closed__0_value)}};
static const lean_object* l_Std_Time_instReprFormatPart_repr___closed__1 = (const lean_object*)&l_Std_Time_instReprFormatPart_repr___closed__1_value;
static const lean_ctor_object l_Std_Time_instReprFormatPart_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprFormatPart_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprFormatPart_repr___closed__2 = (const lean_object*)&l_Std_Time_instReprFormatPart_repr___closed__2_value;
static lean_once_cell_t l_Std_Time_instReprFormatPart_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprFormatPart_repr___closed__3;
static lean_once_cell_t l_Std_Time_instReprFormatPart_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprFormatPart_repr___closed__4;
static const lean_string_object l_Std_Time_instReprFormatPart_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Std.Time.FormatPart.modifier"};
static const lean_object* l_Std_Time_instReprFormatPart_repr___closed__5 = (const lean_object*)&l_Std_Time_instReprFormatPart_repr___closed__5_value;
static const lean_ctor_object l_Std_Time_instReprFormatPart_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprFormatPart_repr___closed__5_value)}};
static const lean_object* l_Std_Time_instReprFormatPart_repr___closed__6 = (const lean_object*)&l_Std_Time_instReprFormatPart_repr___closed__6_value;
static const lean_ctor_object l_Std_Time_instReprFormatPart_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprFormatPart_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_instReprFormatPart_repr___closed__7 = (const lean_object*)&l_Std_Time_instReprFormatPart_repr___closed__7_value;
LEAN_EXPORT lean_object* l_Std_Time_instReprFormatPart_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprFormatPart_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprFormatPart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprFormatPart_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprFormatPart___closed__0 = (const lean_object*)&l_Std_Time_instReprFormatPart___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprFormatPart = (const lean_object*)&l_Std_Time_instReprFormatPart___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instCoeStringFormatPart___lam__0(lean_object*);
static const lean_closure_object l_Std_Time_instCoeStringFormatPart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instCoeStringFormatPart___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instCoeStringFormatPart___closed__0 = (const lean_object*)&l_Std_Time_instCoeStringFormatPart___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instCoeStringFormatPart = (const lean_object*)&l_Std_Time_instCoeStringFormatPart___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instCoeModifierFormatPart___lam__0(lean_object*);
static const lean_closure_object l_Std_Time_instCoeModifierFormatPart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instCoeModifierFormatPart___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instCoeModifierFormatPart___closed__0 = (const lean_object*)&l_Std_Time_instCoeModifierFormatPart___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instCoeModifierFormatPart = (const lean_object*)&l_Std_Time_instCoeModifierFormatPart___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Awareness_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Awareness_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Awareness_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Awareness_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Awareness_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Awareness_only_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Awareness_only_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Awareness_any_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Awareness_any_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Awareness_instCoeTimeZone___lam__0(lean_object*);
static const lean_closure_object l_Std_Time_Awareness_instCoeTimeZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Awareness_instCoeTimeZone___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Awareness_instCoeTimeZone___closed__0 = (const lean_object*)&l_Std_Time_Awareness_instCoeTimeZone___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Awareness_instCoeTimeZone = (const lean_object*)&l_Std_Time_Awareness_instCoeTimeZone___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Awareness_getD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Awareness_getD___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_instInhabitedFormatConfig_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedFormatConfig_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedFormatConfig_default;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedFormatConfig;
static lean_once_cell_t l_Std_Time_instInhabitedGenericFormat_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedGenericFormat_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "condition not satisfied"};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expected: '"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(uint8_t, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0(uint8_t, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(uint8_t, uint32_t, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(uint32_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__3;
static const lean_closure_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__4 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__4_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_specParser_spec__0(lean_object*, lean_object*);
static const lean_array_object l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__0_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expected end of input"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__1_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__1_value)}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParser(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParse(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__0;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___boxed(lean_object*);
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "1"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__0_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "2"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__1_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "3"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__2 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__2_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "4"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__3 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason___closed__0_value;
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__1(lean_object*);
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(lean_object*, uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(lean_object*);
static lean_once_cell_t l_Std_Time_classifyDayPeriod___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_classifyDayPeriod___closed__0;
LEAN_EXPORT uint8_t l_Std_Time_classifyDayPeriod(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_classifyDayPeriod___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_classifyExtendedDayPeriod___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_classifyExtendedDayPeriod___closed__0;
static lean_once_cell_t l_Std_Time_classifyExtendedDayPeriod___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_classifyExtendedDayPeriod___closed__1;
static lean_once_cell_t l_Std_Time_classifyExtendedDayPeriod___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_classifyExtendedDayPeriod___closed__2;
LEAN_EXPORT uint8_t l_Std_Time_classifyExtendedDayPeriod(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_classifyExtendedDayPeriod___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "unk"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GMT"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Z"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "no match"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__0_value)}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__0_value)} };
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__2 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseMonthShort(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraShort(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraLong(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraNarrow(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerShort(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerLong(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerNarrow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___lam__0(lean_object*);
static const lean_closure_object l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(lean_object*);
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "need a natural number in the interval of "};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__0_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " to "};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__0;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__1;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__2;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__3;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid hour offset: "};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = ". Must be between 0 and 23."};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__1_value;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2;
static const lean_closure_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3_value;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "invalid second offset: "};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = ". Must be between 0 and 59."};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__7 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__7_value;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "invalid minute offset: "};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10_value;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__15;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__16;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__17;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__18;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(uint8_t, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1;
static const lean_closure_object l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))} };
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "need a natural number in the interval of 1 to 7"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__3 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__3_value)}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4_value;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6;
static const lean_closure_object l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1))} };
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__7 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__7_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_FormatType_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_FormatType_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(lean_object*, lean_object*);
static const lean_array_object l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__30;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_GenericFormat_spec_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Time.Format.Basic"};
static const lean_object* l_Std_Time_GenericFormat_spec_x21___closed__0 = (const lean_object*)&l_Std_Time_GenericFormat_spec_x21___closed__0_value;
static const lean_string_object l_Std_Time_GenericFormat_spec_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Std.Time.GenericFormat.spec!"};
static const lean_object* l_Std_Time_GenericFormat_spec_x21___closed__1 = (const lean_object*)&l_Std_Time_GenericFormat_spec_x21___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "could not parse the date"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go___closed__0_value)}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*37 + 0, .m_other = 37, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "invalid date."};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg___closed__0_value)}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(lean_object*);
static const lean_string_object l_Std_Time_GenericFormat_parse_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Std.Time.GenericFormat.parse!"};
static const lean_object* l_Std_Time_GenericFormat_parse_x21___closed__0 = (const lean_object*)&l_Std_Time_GenericFormat_parse_x21___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_GenericFormat_parseBuilder_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Time.GenericFormat.parseBuilder!"};
static const lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg___closed__0 = (const lean_object*)&l_Std_Time_GenericFormat_parseBuilder_x21___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instFormatGenericFormatFormatTypeString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Std_Time_FormatPart_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
lean_object* v_val_8_; lean_object* v___x_9_; 
v_val_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_val_8_);
lean_dec_ref(v_t_6_);
v___x_9_ = lean_apply_1(v_k_7_, v_val_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Std_Time_FormatPart_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Std_Time_FormatPart_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_string_elim___redArg(lean_object* v_t_22_, lean_object* v_string_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Std_Time_FormatPart_ctorElim___redArg(v_t_22_, v_string_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_string_elim(lean_object* v_motive_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_string_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Std_Time_FormatPart_ctorElim___redArg(v_t_26_, v_string_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_modifier_elim___redArg(lean_object* v_t_30_, lean_object* v_modifier_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Std_Time_FormatPart_ctorElim___redArg(v_t_30_, v_modifier_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_modifier_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_modifier_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Std_Time_FormatPart_ctorElim___redArg(v_t_34_, v_modifier_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Std_Time_instReprFormatPart_repr___closed__3(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_unsigned_to_nat(2u);
v___x_45_ = lean_nat_to_int(v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l_Std_Time_instReprFormatPart_repr___closed__4(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_unsigned_to_nat(1u);
v___x_47_ = lean_nat_to_int(v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprFormatPart_repr(lean_object* v_x_54_, lean_object* v_prec_55_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v_val_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_76_; 
v_val_56_ = lean_ctor_get(v_x_54_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v_x_54_);
if (v_isSharedCheck_76_ == 0)
{
v___x_58_ = v_x_54_;
v_isShared_59_ = v_isSharedCheck_76_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_val_56_);
lean_dec(v_x_54_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_76_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___y_61_; lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(1024u);
v___x_73_ = lean_nat_dec_le(v___x_72_, v_prec_55_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; 
v___x_74_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__3, &l_Std_Time_instReprFormatPart_repr___closed__3_once, _init_l_Std_Time_instReprFormatPart_repr___closed__3);
v___y_61_ = v___x_74_;
goto v___jp_60_;
}
else
{
lean_object* v___x_75_; 
v___x_75_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___y_61_ = v___x_75_;
goto v___jp_60_;
}
v___jp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_62_ = ((lean_object*)(l_Std_Time_instReprFormatPart_repr___closed__2));
v___x_63_ = l_String_quote(v_val_56_);
if (v_isShared_59_ == 0)
{
lean_ctor_set_tag(v___x_58_, 3);
lean_ctor_set(v___x_58_, 0, v___x_63_);
v___x_65_ = v___x_58_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_63_);
v___x_65_ = v_reuseFailAlloc_71_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_66_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_62_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
lean_inc(v___y_61_);
v___x_67_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_67_, 0, v___y_61_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = 0;
v___x_69_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set_uint8(v___x_69_, sizeof(void*)*1, v___x_68_);
v___x_70_ = l_Repr_addAppParen(v___x_69_, v_prec_55_);
return v___x_70_;
}
}
}
}
else
{
lean_object* v_modifier_77_; lean_object* v___y_79_; lean_object* v___x_88_; uint8_t v___x_89_; 
v_modifier_77_ = lean_ctor_get(v_x_54_, 0);
lean_inc_ref(v_modifier_77_);
lean_dec_ref_known(v_x_54_, 1);
v___x_88_ = lean_unsigned_to_nat(1024u);
v___x_89_ = lean_nat_dec_le(v___x_88_, v_prec_55_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
v___x_90_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__3, &l_Std_Time_instReprFormatPart_repr___closed__3_once, _init_l_Std_Time_instReprFormatPart_repr___closed__3);
v___y_79_ = v___x_90_;
goto v___jp_78_;
}
else
{
lean_object* v___x_91_; 
v___x_91_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___y_79_ = v___x_91_;
goto v___jp_78_;
}
v___jp_78_:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_80_ = ((lean_object*)(l_Std_Time_instReprFormatPart_repr___closed__7));
v___x_81_ = lean_unsigned_to_nat(1024u);
v___x_82_ = l_Std_Time_instReprModifier_repr(v_modifier_77_, v___x_81_);
v___x_83_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_80_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
lean_inc(v___y_79_);
v___x_84_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_84_, 0, v___y_79_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = 0;
v___x_86_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_86_, 0, v___x_84_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*1, v___x_85_);
v___x_87_ = l_Repr_addAppParen(v___x_86_, v_prec_55_);
return v___x_87_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprFormatPart_repr___boxed(lean_object* v_x_92_, lean_object* v_prec_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_Time_instReprFormatPart_repr(v_x_92_, v_prec_93_);
lean_dec(v_prec_93_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instCoeStringFormatPart___lam__0(lean_object* v_val_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v_val_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instCoeModifierFormatPart___lam__0(lean_object* v_modifier_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v_modifier_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_ctorIdx(lean_object* v_x_105_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_unsigned_to_nat(0u);
return v___x_106_;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = lean_unsigned_to_nat(1u);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_ctorIdx___boxed(lean_object* v_x_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Std_Time_Awareness_ctorIdx(v_x_108_);
lean_dec(v_x_108_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_ctorElim___redArg(lean_object* v_t_110_, lean_object* v_k_111_){
_start:
{
if (lean_obj_tag(v_t_110_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_113_; 
v_a_112_ = lean_ctor_get(v_t_110_, 0);
lean_inc_ref(v_a_112_);
lean_dec_ref_known(v_t_110_, 1);
v___x_113_ = lean_apply_1(v_k_111_, v_a_112_);
return v___x_113_;
}
else
{
return v_k_111_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_ctorElim(lean_object* v_motive_114_, lean_object* v_ctorIdx_115_, lean_object* v_t_116_, lean_object* v_h_117_, lean_object* v_k_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Std_Time_Awareness_ctorElim___redArg(v_t_116_, v_k_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_ctorElim___boxed(lean_object* v_motive_120_, lean_object* v_ctorIdx_121_, lean_object* v_t_122_, lean_object* v_h_123_, lean_object* v_k_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Std_Time_Awareness_ctorElim(v_motive_120_, v_ctorIdx_121_, v_t_122_, v_h_123_, v_k_124_);
lean_dec(v_ctorIdx_121_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_only_elim___redArg(lean_object* v_t_126_, lean_object* v_only_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Std_Time_Awareness_ctorElim___redArg(v_t_126_, v_only_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_only_elim(lean_object* v_motive_129_, lean_object* v_t_130_, lean_object* v_h_131_, lean_object* v_only_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Std_Time_Awareness_ctorElim___redArg(v_t_130_, v_only_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_any_elim___redArg(lean_object* v_t_134_, lean_object* v_any_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Std_Time_Awareness_ctorElim___redArg(v_t_134_, v_any_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_any_elim(lean_object* v_motive_137_, lean_object* v_t_138_, lean_object* v_h_139_, lean_object* v_any_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Std_Time_Awareness_ctorElim___redArg(v_t_138_, v_any_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_instCoeTimeZone___lam__0(lean_object* v_a_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v_a_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Awareness_getD(lean_object* v_x_146_, lean_object* v_default_147_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
lean_object* v_a_148_; 
v_a_148_ = lean_ctor_get(v_x_146_, 0);
lean_inc_ref(v_a_148_);
return v_a_148_;
}
else
{
lean_inc_ref(v_default_147_);
return v_default_147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Awareness_getD___boxed(lean_object* v_x_149_, lean_object* v_default_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Std_Time_Format_Basic_0__Std_Time_Awareness_getD(v_x_149_, v_default_150_);
lean_dec_ref(v_default_150_);
lean_dec(v_x_149_);
return v_res_151_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedFormatConfig_default___closed__0(void){
_start:
{
lean_object* v___x_152_; uint8_t v___x_153_; lean_object* v___x_154_; 
v___x_152_ = l_Std_Time_DateFormat_enUS;
v___x_153_ = 0;
v___x_154_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_154_, 0, v___x_152_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*1, v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedFormatConfig_default(void){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lean_obj_once(&l_Std_Time_instInhabitedFormatConfig_default___closed__0, &l_Std_Time_instInhabitedFormatConfig_default___closed__0_once, _init_l_Std_Time_instInhabitedFormatConfig_default___closed__0);
return v___x_155_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedFormatConfig(void){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_Time_instInhabitedFormatConfig_default;
return v___x_156_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_box(0);
v___x_158_ = l_Std_Time_instInhabitedFormatConfig_default;
v___x_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_157_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default(lean_object* v_awareness_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default___boxed(lean_object* v_awareness_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Std_Time_instInhabitedGenericFormat_default(v_awareness_162_);
lean_dec(v_awareness_162_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat(lean_object* v_a_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Std_Time_instInhabitedGenericFormat_default(v_a_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat___boxed(lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_Time_instInhabitedGenericFormat(v_a_166_);
lean_dec(v_a_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(lean_object* v_a_168_, lean_object* v_f_169_, lean_object* v___y_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_apply_1(v_a_168_, v___y_170_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_pos_172_; lean_object* v_res_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_181_; 
v_pos_172_ = lean_ctor_get(v___x_171_, 0);
v_res_173_ = lean_ctor_get(v___x_171_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_181_ == 0)
{
v___x_175_ = v___x_171_;
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_res_173_);
lean_inc(v_pos_172_);
lean_dec(v___x_171_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = lean_apply_1(v_f_169_, v_res_173_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___x_177_);
v___x_179_ = v___x_175_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_pos_172_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
else
{
lean_object* v_pos_182_; lean_object* v_err_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
lean_dec(v_f_169_);
v_pos_182_ = lean_ctor_get(v___x_171_, 0);
v_err_183_ = lean_ctor_get(v___x_171_, 1);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_190_ == 0)
{
v___x_185_ = v___x_171_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_err_183_);
lean_inc(v_pos_182_);
lean_dec(v___x_171_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_pos_182_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_err_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1(lean_object* v_00_u03b1_191_, lean_object* v_00_u03b2_192_, lean_object* v_a_193_, lean_object* v_f_194_, lean_object* v___y_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v_a_193_, v_f_194_, v___y_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0(lean_object* v_acc_200_, lean_object* v_a_201_){
_start:
{
lean_object* v_fst_202_; lean_object* v_snd_203_; lean_object* v_pos_205_; lean_object* v_snd_206_; lean_object* v_err_207_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_fst_202_ = lean_ctor_get(v_a_201_, 0);
v_snd_203_ = lean_ctor_get(v_a_201_, 1);
lean_inc(v_snd_203_);
v___x_211_ = lean_string_utf8_byte_size(v_fst_202_);
v___x_212_ = lean_nat_dec_eq(v_snd_203_, v___x_211_);
if (v___x_212_ == 0)
{
uint32_t v___x_213_; uint32_t v_c_214_; uint8_t v___x_215_; 
v___x_213_ = 34;
v_c_214_ = lean_string_utf8_get_fast(v_fst_202_, v_snd_203_);
v___x_215_ = lean_uint32_dec_eq(v_c_214_, v___x_213_);
if (v___x_215_ == 0)
{
lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_225_; 
lean_inc(v_fst_202_);
v_isSharedCheck_225_ = !lean_is_exclusive(v_a_201_);
if (v_isSharedCheck_225_ == 0)
{
lean_object* v_unused_226_; lean_object* v_unused_227_; 
v_unused_226_ = lean_ctor_get(v_a_201_, 1);
lean_dec(v_unused_226_);
v_unused_227_ = lean_ctor_get(v_a_201_, 0);
lean_dec(v_unused_227_);
v___x_217_ = v_a_201_;
v_isShared_218_ = v_isSharedCheck_225_;
goto v_resetjp_216_;
}
else
{
lean_dec(v_a_201_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_225_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v_it_x27_221_; 
v___x_219_ = lean_string_utf8_next_fast(v_fst_202_, v_snd_203_);
lean_dec(v_snd_203_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_219_);
v_it_x27_221_ = v___x_217_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_fst_202_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v___x_219_);
v_it_x27_221_ = v_reuseFailAlloc_224_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_222_; 
v___x_222_ = lean_string_push(v_acc_200_, v_c_214_);
v_acc_200_ = v___x_222_;
v_a_201_ = v_it_x27_221_;
goto _start;
}
}
}
else
{
lean_object* v___x_228_; 
v___x_228_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_203_);
v_pos_205_ = v_a_201_;
v_snd_206_ = v_snd_203_;
v_err_207_ = v___x_228_;
goto v___jp_204_;
}
}
else
{
lean_object* v___x_229_; 
v___x_229_ = lean_box(0);
lean_inc(v_snd_203_);
v_pos_205_ = v_a_201_;
v_snd_206_ = v_snd_203_;
v_err_207_ = v___x_229_;
goto v___jp_204_;
}
v___jp_204_:
{
uint8_t v___x_208_; 
v___x_208_ = lean_nat_dec_eq(v_snd_203_, v_snd_206_);
lean_dec(v_snd_206_);
lean_dec(v_snd_203_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
lean_dec_ref(v_acc_200_);
lean_inc(v_err_207_);
v___x_209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_209_, 0, v_pos_205_);
lean_ctor_set(v___x_209_, 1, v_err_207_);
return v___x_209_;
}
else
{
lean_object* v___x_210_; 
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v_pos_205_);
lean_ctor_set(v___x_210_, 1, v_acc_200_);
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0(lean_object* v_acc_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_fst_232_; lean_object* v_snd_233_; lean_object* v_pos_235_; lean_object* v_snd_236_; lean_object* v_err_237_; lean_object* v___x_241_; uint8_t v___x_242_; 
v_fst_232_ = lean_ctor_get(v_a_231_, 0);
v_snd_233_ = lean_ctor_get(v_a_231_, 1);
lean_inc(v_snd_233_);
v___x_241_ = lean_string_utf8_byte_size(v_fst_232_);
v___x_242_ = lean_nat_dec_eq(v_snd_233_, v___x_241_);
if (v___x_242_ == 0)
{
uint32_t v___x_243_; uint32_t v_c_244_; uint8_t v___x_245_; 
v___x_243_ = 34;
v_c_244_ = lean_string_utf8_get_fast(v_fst_232_, v_snd_233_);
v___x_245_ = lean_uint32_dec_eq(v_c_244_, v___x_243_);
if (v___x_245_ == 0)
{
lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_255_; 
lean_inc(v_fst_232_);
v_isSharedCheck_255_ = !lean_is_exclusive(v_a_231_);
if (v_isSharedCheck_255_ == 0)
{
lean_object* v_unused_256_; lean_object* v_unused_257_; 
v_unused_256_ = lean_ctor_get(v_a_231_, 1);
lean_dec(v_unused_256_);
v_unused_257_ = lean_ctor_get(v_a_231_, 0);
lean_dec(v_unused_257_);
v___x_247_ = v_a_231_;
v_isShared_248_ = v_isSharedCheck_255_;
goto v_resetjp_246_;
}
else
{
lean_dec(v_a_231_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_255_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v_it_x27_251_; 
v___x_249_ = lean_string_utf8_next_fast(v_fst_232_, v_snd_233_);
lean_dec(v_snd_233_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 1, v___x_249_);
v_it_x27_251_ = v___x_247_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_fst_232_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v___x_249_);
v_it_x27_251_ = v_reuseFailAlloc_254_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_string_push(v_acc_230_, v_c_244_);
v___x_253_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0(v___x_252_, v_it_x27_251_);
return v___x_253_;
}
}
}
else
{
lean_object* v___x_258_; 
v___x_258_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_233_);
v_pos_235_ = v_a_231_;
v_snd_236_ = v_snd_233_;
v_err_237_ = v___x_258_;
goto v___jp_234_;
}
}
else
{
lean_object* v___x_259_; 
v___x_259_ = lean_box(0);
lean_inc(v_snd_233_);
v_pos_235_ = v_a_231_;
v_snd_236_ = v_snd_233_;
v_err_237_ = v___x_259_;
goto v___jp_234_;
}
v___jp_234_:
{
uint8_t v___x_238_; 
v___x_238_ = lean_nat_dec_eq(v_snd_233_, v_snd_236_);
lean_dec(v_snd_236_);
lean_dec(v_snd_233_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
lean_dec_ref(v_acc_230_);
lean_inc(v_err_237_);
v___x_239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_239_, 0, v_pos_235_);
lean_ctor_set(v___x_239_, 1, v_err_237_);
return v___x_239_;
}
else
{
lean_object* v___x_240_; 
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v_pos_235_);
lean_ctor_set(v___x_240_, 1, v_acc_230_);
return v___x_240_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(uint8_t v___x_263_, uint32_t v___x_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_fst_269_; lean_object* v_snd_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_fst_269_ = lean_ctor_get(v___y_265_, 0);
v_snd_270_ = lean_ctor_get(v___y_265_, 1);
v___x_271_ = lean_string_utf8_byte_size(v_fst_269_);
v___x_272_ = lean_nat_dec_eq(v_snd_270_, v___x_271_);
if (v___x_272_ == 0)
{
if (v___x_263_ == 0)
{
goto v___jp_266_;
}
else
{
uint32_t v_c_273_; uint8_t v___x_274_; 
v_c_273_ = lean_string_utf8_get_fast(v_fst_269_, v_snd_270_);
v___x_274_ = lean_uint32_dec_eq(v_c_273_, v___x_264_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_275_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_276_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_277_ = lean_string_push(v___x_276_, v___x_264_);
v___x_278_ = lean_string_append(v___x_275_, v___x_277_);
lean_dec_ref(v___x_277_);
v___x_279_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_280_ = lean_string_append(v___x_278_, v___x_279_);
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
v___x_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_282_, 0, v___y_265_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
return v___x_282_;
}
else
{
lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_341_; 
lean_inc(v_snd_270_);
lean_inc(v_fst_269_);
v_isSharedCheck_341_ = !lean_is_exclusive(v___y_265_);
if (v_isSharedCheck_341_ == 0)
{
lean_object* v_unused_342_; lean_object* v_unused_343_; 
v_unused_342_ = lean_ctor_get(v___y_265_, 1);
lean_dec(v_unused_342_);
v_unused_343_ = lean_ctor_get(v___y_265_, 0);
lean_dec(v_unused_343_);
v___x_284_ = v___y_265_;
v_isShared_285_ = v_isSharedCheck_341_;
goto v_resetjp_283_;
}
else
{
lean_dec(v___y_265_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_341_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v_it_x27_288_; 
v___x_286_ = lean_string_utf8_next_fast(v_fst_269_, v_snd_270_);
lean_dec(v_snd_270_);
lean_inc(v_fst_269_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 1, v___x_286_);
v_it_x27_288_ = v___x_284_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_fst_269_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_286_);
v_it_x27_288_ = v_reuseFailAlloc_340_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
uint8_t v___x_292_; 
v___x_292_ = lean_nat_dec_eq(v___x_286_, v___x_271_);
if (v___x_292_ == 0)
{
if (v___x_274_ == 0)
{
lean_dec(v_fst_269_);
goto v___jp_289_;
}
else
{
uint32_t v___x_293_; uint8_t v___x_294_; 
v___x_293_ = lean_string_utf8_get_fast(v_fst_269_, v___x_286_);
v___x_294_ = lean_uint32_dec_eq(v___x_293_, v___x_264_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec_ref(v_it_x27_288_);
v___x_295_ = lean_string_utf8_next_fast(v_fst_269_, v___x_286_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v_fst_269_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_298_ = lean_string_push(v___x_297_, v___x_293_);
v___x_299_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0(v___x_298_, v___x_296_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_pos_300_; lean_object* v_res_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_337_; 
v_pos_300_ = lean_ctor_get(v___x_299_, 0);
v_res_301_ = lean_ctor_get(v___x_299_, 1);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_337_ == 0)
{
v___x_303_ = v___x_299_;
v_isShared_304_ = v_isSharedCheck_337_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_res_301_);
lean_inc(v_pos_300_);
lean_dec(v___x_299_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_337_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v_fst_305_; lean_object* v_snd_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_fst_305_ = lean_ctor_get(v_pos_300_, 0);
v_snd_306_ = lean_ctor_get(v_pos_300_, 1);
v___x_307_ = lean_string_utf8_byte_size(v_fst_305_);
v___x_308_ = lean_nat_dec_eq(v_snd_306_, v___x_307_);
if (v___x_308_ == 0)
{
uint32_t v_c_309_; uint8_t v___x_310_; 
v_c_309_ = lean_string_utf8_get_fast(v_fst_305_, v_snd_306_);
v___x_310_ = lean_uint32_dec_eq(v_c_309_, v___x_264_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
lean_dec(v_res_301_);
v___x_311_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_312_ = lean_string_push(v___x_297_, v___x_264_);
v___x_313_ = lean_string_append(v___x_311_, v___x_312_);
lean_dec_ref(v___x_312_);
v___x_314_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_315_ = lean_string_append(v___x_313_, v___x_314_);
v___x_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
if (v_isShared_304_ == 0)
{
lean_ctor_set_tag(v___x_303_, 1);
lean_ctor_set(v___x_303_, 1, v___x_316_);
v___x_318_ = v___x_303_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_pos_300_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
else
{
lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_330_; 
lean_inc(v_snd_306_);
lean_inc(v_fst_305_);
v_isSharedCheck_330_ = !lean_is_exclusive(v_pos_300_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; lean_object* v_unused_332_; 
v_unused_331_ = lean_ctor_get(v_pos_300_, 1);
lean_dec(v_unused_331_);
v_unused_332_ = lean_ctor_get(v_pos_300_, 0);
lean_dec(v_unused_332_);
v___x_321_ = v_pos_300_;
v_isShared_322_ = v_isSharedCheck_330_;
goto v_resetjp_320_;
}
else
{
lean_dec(v_pos_300_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_330_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v_it_x27_325_; 
v___x_323_ = lean_string_utf8_next_fast(v_fst_305_, v_snd_306_);
lean_dec(v_snd_306_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 1, v___x_323_);
v_it_x27_325_ = v___x_321_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_fst_305_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v___x_323_);
v_it_x27_325_ = v_reuseFailAlloc_329_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_327_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v_it_x27_325_);
v___x_327_ = v___x_303_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_it_x27_325_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_res_301_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
else
{
lean_object* v___x_333_; lean_object* v___x_335_; 
lean_dec(v_res_301_);
v___x_333_ = lean_box(0);
if (v_isShared_304_ == 0)
{
lean_ctor_set_tag(v___x_303_, 1);
lean_ctor_set(v___x_303_, 1, v___x_333_);
v___x_335_ = v___x_303_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_pos_300_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
else
{
return v___x_299_;
}
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec(v_fst_269_);
v___x_338_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_339_, 0, v_it_x27_288_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
return v___x_339_;
}
}
}
else
{
lean_dec(v_fst_269_);
goto v___jp_289_;
}
v___jp_289_:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_box(0);
v___x_291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_291_, 0, v_it_x27_288_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
return v___x_291_;
}
}
}
}
}
}
else
{
goto v___jp_266_;
}
v___jp_266_:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_box(0);
v___x_268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_268_, 0, v___y_265_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___boxed(lean_object* v___x_344_, lean_object* v___x_345_, lean_object* v___y_346_){
_start:
{
uint8_t v___x_9659__boxed_347_; uint32_t v___x_9660__boxed_348_; lean_object* v_res_349_; 
v___x_9659__boxed_347_ = lean_unbox(v___x_344_);
v___x_9660__boxed_348_ = lean_unbox_uint32(v___x_345_);
lean_dec(v___x_345_);
v_res_349_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(v___x_9659__boxed_347_, v___x_9660__boxed_348_, v___y_346_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2_spec__3(lean_object* v_acc_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_fst_352_; lean_object* v_snd_353_; lean_object* v_pos_355_; lean_object* v_snd_356_; lean_object* v_err_357_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_fst_352_ = lean_ctor_get(v_a_351_, 0);
v_snd_353_ = lean_ctor_get(v_a_351_, 1);
lean_inc(v_snd_353_);
v___x_361_ = lean_string_utf8_byte_size(v_fst_352_);
v___x_362_ = lean_nat_dec_eq(v_snd_353_, v___x_361_);
if (v___x_362_ == 0)
{
uint32_t v___x_363_; uint32_t v_c_364_; uint8_t v___x_365_; 
v___x_363_ = 39;
v_c_364_ = lean_string_utf8_get_fast(v_fst_352_, v_snd_353_);
v___x_365_ = lean_uint32_dec_eq(v_c_364_, v___x_363_);
if (v___x_365_ == 0)
{
lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_375_; 
lean_inc(v_fst_352_);
v_isSharedCheck_375_ = !lean_is_exclusive(v_a_351_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; lean_object* v_unused_377_; 
v_unused_376_ = lean_ctor_get(v_a_351_, 1);
lean_dec(v_unused_376_);
v_unused_377_ = lean_ctor_get(v_a_351_, 0);
lean_dec(v_unused_377_);
v___x_367_ = v_a_351_;
v_isShared_368_ = v_isSharedCheck_375_;
goto v_resetjp_366_;
}
else
{
lean_dec(v_a_351_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_375_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v_it_x27_371_; 
v___x_369_ = lean_string_utf8_next_fast(v_fst_352_, v_snd_353_);
lean_dec(v_snd_353_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 1, v___x_369_);
v_it_x27_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_fst_352_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v___x_369_);
v_it_x27_371_ = v_reuseFailAlloc_374_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; 
v___x_372_ = lean_string_push(v_acc_350_, v_c_364_);
v_acc_350_ = v___x_372_;
v_a_351_ = v_it_x27_371_;
goto _start;
}
}
}
else
{
lean_object* v___x_378_; 
v___x_378_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_353_);
v_pos_355_ = v_a_351_;
v_snd_356_ = v_snd_353_;
v_err_357_ = v___x_378_;
goto v___jp_354_;
}
}
else
{
lean_object* v___x_379_; 
v___x_379_ = lean_box(0);
lean_inc(v_snd_353_);
v_pos_355_ = v_a_351_;
v_snd_356_ = v_snd_353_;
v_err_357_ = v___x_379_;
goto v___jp_354_;
}
v___jp_354_:
{
uint8_t v___x_358_; 
v___x_358_ = lean_nat_dec_eq(v_snd_353_, v_snd_356_);
lean_dec(v_snd_356_);
lean_dec(v_snd_353_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; 
lean_dec_ref(v_acc_350_);
lean_inc(v_err_357_);
v___x_359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_359_, 0, v_pos_355_);
lean_ctor_set(v___x_359_, 1, v_err_357_);
return v___x_359_;
}
else
{
lean_object* v___x_360_; 
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v_pos_355_);
lean_ctor_set(v___x_360_, 1, v_acc_350_);
return v___x_360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2(lean_object* v_acc_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_fst_382_; lean_object* v_snd_383_; lean_object* v_pos_385_; lean_object* v_snd_386_; lean_object* v_err_387_; lean_object* v___x_391_; uint8_t v___x_392_; 
v_fst_382_ = lean_ctor_get(v_a_381_, 0);
v_snd_383_ = lean_ctor_get(v_a_381_, 1);
lean_inc(v_snd_383_);
v___x_391_ = lean_string_utf8_byte_size(v_fst_382_);
v___x_392_ = lean_nat_dec_eq(v_snd_383_, v___x_391_);
if (v___x_392_ == 0)
{
uint32_t v___x_393_; uint32_t v_c_394_; uint8_t v___x_395_; 
v___x_393_ = 39;
v_c_394_ = lean_string_utf8_get_fast(v_fst_382_, v_snd_383_);
v___x_395_ = lean_uint32_dec_eq(v_c_394_, v___x_393_);
if (v___x_395_ == 0)
{
lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_405_; 
lean_inc(v_fst_382_);
v_isSharedCheck_405_ = !lean_is_exclusive(v_a_381_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; lean_object* v_unused_407_; 
v_unused_406_ = lean_ctor_get(v_a_381_, 1);
lean_dec(v_unused_406_);
v_unused_407_ = lean_ctor_get(v_a_381_, 0);
lean_dec(v_unused_407_);
v___x_397_ = v_a_381_;
v_isShared_398_ = v_isSharedCheck_405_;
goto v_resetjp_396_;
}
else
{
lean_dec(v_a_381_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_405_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v_it_x27_401_; 
v___x_399_ = lean_string_utf8_next_fast(v_fst_382_, v_snd_383_);
lean_dec(v_snd_383_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 1, v___x_399_);
v_it_x27_401_ = v___x_397_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_fst_382_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_399_);
v_it_x27_401_ = v_reuseFailAlloc_404_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_string_push(v_acc_380_, v_c_394_);
v___x_403_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2_spec__3(v___x_402_, v_it_x27_401_);
return v___x_403_;
}
}
}
else
{
lean_object* v___x_408_; 
v___x_408_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_383_);
v_pos_385_ = v_a_381_;
v_snd_386_ = v_snd_383_;
v_err_387_ = v___x_408_;
goto v___jp_384_;
}
}
else
{
lean_object* v___x_409_; 
v___x_409_ = lean_box(0);
lean_inc(v_snd_383_);
v_pos_385_ = v_a_381_;
v_snd_386_ = v_snd_383_;
v_err_387_ = v___x_409_;
goto v___jp_384_;
}
v___jp_384_:
{
uint8_t v___x_388_; 
v___x_388_ = lean_nat_dec_eq(v_snd_383_, v_snd_386_);
lean_dec(v_snd_386_);
lean_dec(v_snd_383_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
lean_dec_ref(v_acc_380_);
lean_inc(v_err_387_);
v___x_389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_389_, 0, v_pos_385_);
lean_ctor_set(v___x_389_, 1, v_err_387_);
return v___x_389_;
}
else
{
lean_object* v___x_390_; 
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v_pos_385_);
lean_ctor_set(v___x_390_, 1, v_acc_380_);
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0(uint8_t v___x_410_, uint32_t v___x_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_fst_416_; lean_object* v_snd_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_fst_416_ = lean_ctor_get(v___y_412_, 0);
v_snd_417_ = lean_ctor_get(v___y_412_, 1);
v___x_418_ = lean_string_utf8_byte_size(v_fst_416_);
v___x_419_ = lean_nat_dec_eq(v_snd_417_, v___x_418_);
if (v___x_419_ == 0)
{
if (v___x_410_ == 0)
{
goto v___jp_413_;
}
else
{
uint32_t v_c_420_; uint8_t v___x_421_; 
v_c_420_ = lean_string_utf8_get_fast(v_fst_416_, v_snd_417_);
v___x_421_ = lean_uint32_dec_eq(v_c_420_, v___x_411_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_422_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_423_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_424_ = lean_string_push(v___x_423_, v___x_411_);
v___x_425_ = lean_string_append(v___x_422_, v___x_424_);
lean_dec_ref(v___x_424_);
v___x_426_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_427_ = lean_string_append(v___x_425_, v___x_426_);
v___x_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
v___x_429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_429_, 0, v___y_412_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
return v___x_429_;
}
else
{
lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_488_; 
lean_inc(v_snd_417_);
lean_inc(v_fst_416_);
v_isSharedCheck_488_ = !lean_is_exclusive(v___y_412_);
if (v_isSharedCheck_488_ == 0)
{
lean_object* v_unused_489_; lean_object* v_unused_490_; 
v_unused_489_ = lean_ctor_get(v___y_412_, 1);
lean_dec(v_unused_489_);
v_unused_490_ = lean_ctor_get(v___y_412_, 0);
lean_dec(v_unused_490_);
v___x_431_ = v___y_412_;
v_isShared_432_ = v_isSharedCheck_488_;
goto v_resetjp_430_;
}
else
{
lean_dec(v___y_412_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_488_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v_it_x27_435_; 
v___x_433_ = lean_string_utf8_next_fast(v_fst_416_, v_snd_417_);
lean_dec(v_snd_417_);
lean_inc(v_fst_416_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 1, v___x_433_);
v_it_x27_435_ = v___x_431_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_fst_416_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v___x_433_);
v_it_x27_435_ = v_reuseFailAlloc_487_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
uint8_t v___x_439_; 
v___x_439_ = lean_nat_dec_eq(v___x_433_, v___x_418_);
if (v___x_439_ == 0)
{
if (v___x_421_ == 0)
{
lean_dec(v_fst_416_);
goto v___jp_436_;
}
else
{
uint32_t v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_string_utf8_get_fast(v_fst_416_, v___x_433_);
v___x_441_ = lean_uint32_dec_eq(v___x_440_, v___x_411_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec_ref(v_it_x27_435_);
v___x_442_ = lean_string_utf8_next_fast(v_fst_416_, v___x_433_);
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v_fst_416_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_445_ = lean_string_push(v___x_444_, v___x_440_);
v___x_446_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2(v___x_445_, v___x_443_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_pos_447_; lean_object* v_res_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_484_; 
v_pos_447_ = lean_ctor_get(v___x_446_, 0);
v_res_448_ = lean_ctor_get(v___x_446_, 1);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_484_ == 0)
{
v___x_450_ = v___x_446_;
v_isShared_451_ = v_isSharedCheck_484_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_res_448_);
lean_inc(v_pos_447_);
lean_dec(v___x_446_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_484_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v_fst_452_; lean_object* v_snd_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v_fst_452_ = lean_ctor_get(v_pos_447_, 0);
v_snd_453_ = lean_ctor_get(v_pos_447_, 1);
v___x_454_ = lean_string_utf8_byte_size(v_fst_452_);
v___x_455_ = lean_nat_dec_eq(v_snd_453_, v___x_454_);
if (v___x_455_ == 0)
{
uint32_t v_c_456_; uint8_t v___x_457_; 
v_c_456_ = lean_string_utf8_get_fast(v_fst_452_, v_snd_453_);
v___x_457_ = lean_uint32_dec_eq(v_c_456_, v___x_411_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
lean_dec(v_res_448_);
v___x_458_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_459_ = lean_string_push(v___x_444_, v___x_411_);
v___x_460_ = lean_string_append(v___x_458_, v___x_459_);
lean_dec_ref(v___x_459_);
v___x_461_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_462_ = lean_string_append(v___x_460_, v___x_461_);
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
if (v_isShared_451_ == 0)
{
lean_ctor_set_tag(v___x_450_, 1);
lean_ctor_set(v___x_450_, 1, v___x_463_);
v___x_465_ = v___x_450_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_pos_447_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
else
{
lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_477_; 
lean_inc(v_snd_453_);
lean_inc(v_fst_452_);
v_isSharedCheck_477_ = !lean_is_exclusive(v_pos_447_);
if (v_isSharedCheck_477_ == 0)
{
lean_object* v_unused_478_; lean_object* v_unused_479_; 
v_unused_478_ = lean_ctor_get(v_pos_447_, 1);
lean_dec(v_unused_478_);
v_unused_479_ = lean_ctor_get(v_pos_447_, 0);
lean_dec(v_unused_479_);
v___x_468_ = v_pos_447_;
v_isShared_469_ = v_isSharedCheck_477_;
goto v_resetjp_467_;
}
else
{
lean_dec(v_pos_447_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_477_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v_it_x27_472_; 
v___x_470_ = lean_string_utf8_next_fast(v_fst_452_, v_snd_453_);
lean_dec(v_snd_453_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v___x_470_);
v_it_x27_472_ = v___x_468_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_fst_452_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v___x_470_);
v_it_x27_472_ = v_reuseFailAlloc_476_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_474_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v_it_x27_472_);
v___x_474_ = v___x_450_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_it_x27_472_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_res_448_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
else
{
lean_object* v___x_480_; lean_object* v___x_482_; 
lean_dec(v_res_448_);
v___x_480_ = lean_box(0);
if (v_isShared_451_ == 0)
{
lean_ctor_set_tag(v___x_450_, 1);
lean_ctor_set(v___x_450_, 1, v___x_480_);
v___x_482_ = v___x_450_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_pos_447_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
else
{
return v___x_446_;
}
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec(v_fst_416_);
v___x_485_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_486_, 0, v_it_x27_435_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
return v___x_486_;
}
}
}
else
{
lean_dec(v_fst_416_);
goto v___jp_436_;
}
v___jp_436_:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_box(0);
v___x_438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_438_, 0, v_it_x27_435_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
return v___x_438_;
}
}
}
}
}
}
else
{
goto v___jp_413_;
}
v___jp_413_:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_box(0);
v___x_415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_415_, 0, v___y_412_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___boxed(lean_object* v___x_491_, lean_object* v___x_492_, lean_object* v___y_493_){
_start:
{
uint8_t v___x_9926__boxed_494_; uint32_t v___x_9927__boxed_495_; lean_object* v_res_496_; 
v___x_9926__boxed_494_ = lean_unbox(v___x_491_);
v___x_9927__boxed_495_ = lean_unbox_uint32(v___x_492_);
lean_dec(v___x_492_);
v_res_496_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0(v___x_9926__boxed_494_, v___x_9927__boxed_495_, v___y_493_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__3(lean_object* v_acc_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_fst_499_; lean_object* v_snd_500_; lean_object* v_pos_502_; lean_object* v_snd_503_; lean_object* v_err_504_; lean_object* v___x_510_; uint8_t v___x_511_; 
v_fst_499_ = lean_ctor_get(v_a_498_, 0);
v_snd_500_ = lean_ctor_get(v_a_498_, 1);
lean_inc(v_snd_500_);
v___x_510_ = lean_string_utf8_byte_size(v_fst_499_);
v___x_511_ = lean_nat_dec_eq(v_snd_500_, v___x_510_);
if (v___x_511_ == 0)
{
uint32_t v___x_512_; uint32_t v___x_513_; uint32_t v_c_514_; lean_object* v___x_515_; lean_object* v_it_x27_516_; uint8_t v___x_517_; uint8_t v___x_518_; uint8_t v___y_520_; uint32_t v___x_528_; uint8_t v___x_529_; 
v___x_512_ = 34;
v___x_513_ = 39;
v_c_514_ = lean_string_utf8_get_fast(v_fst_499_, v_snd_500_);
v___x_515_ = lean_string_utf8_next_fast(v_fst_499_, v_snd_500_);
lean_inc(v_fst_499_);
v_it_x27_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_516_, 0, v_fst_499_);
lean_ctor_set(v_it_x27_516_, 1, v___x_515_);
v___x_517_ = lean_uint32_dec_eq(v_c_514_, v___x_512_);
v___x_518_ = lean_uint32_dec_eq(v_c_514_, v___x_513_);
v___x_528_ = 65;
v___x_529_ = lean_uint32_dec_le(v___x_528_, v_c_514_);
if (v___x_529_ == 0)
{
goto v___jp_523_;
}
else
{
uint32_t v___x_530_; uint8_t v___x_531_; 
v___x_530_ = 90;
v___x_531_ = lean_uint32_dec_le(v_c_514_, v___x_530_);
if (v___x_531_ == 0)
{
goto v___jp_523_;
}
else
{
lean_dec_ref_known(v_it_x27_516_, 2);
goto v___jp_508_;
}
}
v___jp_519_:
{
if (v___y_520_ == 0)
{
if (v___x_518_ == 0)
{
if (v___x_517_ == 0)
{
lean_object* v___x_521_; 
lean_dec(v_snd_500_);
lean_dec_ref(v_a_498_);
v___x_521_ = lean_string_push(v_acc_497_, v_c_514_);
v_acc_497_ = v___x_521_;
v_a_498_ = v_it_x27_516_;
goto _start;
}
else
{
lean_dec_ref_known(v_it_x27_516_, 2);
goto v___jp_508_;
}
}
else
{
lean_dec_ref_known(v_it_x27_516_, 2);
goto v___jp_508_;
}
}
else
{
lean_dec_ref_known(v_it_x27_516_, 2);
goto v___jp_508_;
}
}
v___jp_523_:
{
uint32_t v___x_524_; uint8_t v___x_525_; 
v___x_524_ = 97;
v___x_525_ = lean_uint32_dec_le(v___x_524_, v_c_514_);
if (v___x_525_ == 0)
{
v___y_520_ = v___x_525_;
goto v___jp_519_;
}
else
{
uint32_t v___x_526_; uint8_t v___x_527_; 
v___x_526_ = 122;
v___x_527_ = lean_uint32_dec_le(v_c_514_, v___x_526_);
v___y_520_ = v___x_527_;
goto v___jp_519_;
}
}
}
else
{
lean_object* v___x_532_; 
v___x_532_ = lean_box(0);
lean_inc(v_snd_500_);
v_pos_502_ = v_a_498_;
v_snd_503_ = v_snd_500_;
v_err_504_ = v___x_532_;
goto v___jp_501_;
}
v___jp_501_:
{
uint8_t v___x_505_; 
v___x_505_ = lean_nat_dec_eq(v_snd_500_, v_snd_503_);
lean_dec(v_snd_503_);
lean_dec(v_snd_500_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; 
lean_dec_ref(v_acc_497_);
lean_inc(v_err_504_);
v___x_506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_506_, 0, v_pos_502_);
lean_ctor_set(v___x_506_, 1, v_err_504_);
return v___x_506_;
}
else
{
lean_object* v___x_507_; 
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v_pos_502_);
lean_ctor_set(v___x_507_, 1, v_acc_497_);
return v___x_507_;
}
}
v___jp_508_:
{
lean_object* v___x_509_; 
v___x_509_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_500_);
v_pos_502_ = v_a_498_;
v_snd_503_ = v_snd_500_;
v_err_504_ = v___x_509_;
goto v___jp_501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(uint8_t v___x_533_, uint32_t v___x_534_, uint32_t v___x_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_fst_543_; lean_object* v_snd_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v_fst_543_ = lean_ctor_get(v___y_536_, 0);
v_snd_544_ = lean_ctor_get(v___y_536_, 1);
v___x_545_ = lean_string_utf8_byte_size(v_fst_543_);
v___x_546_ = lean_nat_dec_eq(v_snd_544_, v___x_545_);
if (v___x_546_ == 0)
{
if (v___x_533_ == 0)
{
goto v___jp_540_;
}
else
{
uint32_t v_c_547_; lean_object* v___x_548_; lean_object* v_it_x27_549_; uint8_t v___x_550_; uint8_t v___x_551_; uint8_t v___y_553_; uint32_t v___x_562_; uint8_t v___x_563_; 
v_c_547_ = lean_string_utf8_get_fast(v_fst_543_, v_snd_544_);
v___x_548_ = lean_string_utf8_next_fast(v_fst_543_, v_snd_544_);
lean_inc(v_fst_543_);
v_it_x27_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_549_, 0, v_fst_543_);
lean_ctor_set(v_it_x27_549_, 1, v___x_548_);
v___x_550_ = lean_uint32_dec_eq(v_c_547_, v___x_534_);
v___x_551_ = lean_uint32_dec_eq(v_c_547_, v___x_535_);
v___x_562_ = 65;
v___x_563_ = lean_uint32_dec_le(v___x_562_, v_c_547_);
if (v___x_563_ == 0)
{
goto v___jp_557_;
}
else
{
uint32_t v___x_564_; uint8_t v___x_565_; 
v___x_564_ = 90;
v___x_565_ = lean_uint32_dec_le(v_c_547_, v___x_564_);
if (v___x_565_ == 0)
{
goto v___jp_557_;
}
else
{
lean_dec_ref_known(v_it_x27_549_, 2);
goto v___jp_537_;
}
}
v___jp_552_:
{
if (v___y_553_ == 0)
{
if (v___x_551_ == 0)
{
if (v___x_550_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec_ref(v___y_536_);
v___x_554_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_555_ = lean_string_push(v___x_554_, v_c_547_);
v___x_556_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__3(v___x_555_, v_it_x27_549_);
return v___x_556_;
}
else
{
lean_dec_ref_known(v_it_x27_549_, 2);
goto v___jp_537_;
}
}
else
{
lean_dec_ref_known(v_it_x27_549_, 2);
goto v___jp_537_;
}
}
else
{
lean_dec_ref_known(v_it_x27_549_, 2);
goto v___jp_537_;
}
}
v___jp_557_:
{
uint32_t v___x_558_; uint8_t v___x_559_; 
v___x_558_ = 97;
v___x_559_ = lean_uint32_dec_le(v___x_558_, v_c_547_);
if (v___x_559_ == 0)
{
v___y_553_ = v___x_559_;
goto v___jp_552_;
}
else
{
uint32_t v___x_560_; uint8_t v___x_561_; 
v___x_560_ = 122;
v___x_561_ = lean_uint32_dec_le(v_c_547_, v___x_560_);
v___y_553_ = v___x_561_;
goto v___jp_552_;
}
}
}
}
else
{
goto v___jp_540_;
}
v___jp_537_:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_539_, 0, v___y_536_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
return v___x_539_;
}
v___jp_540_:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_box(0);
v___x_542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_542_, 0, v___y_536_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
return v___x_542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2___boxed(lean_object* v___x_566_, lean_object* v___x_567_, lean_object* v___x_568_, lean_object* v___y_569_){
_start:
{
uint8_t v___x_10150__boxed_570_; uint32_t v___x_10151__boxed_571_; uint32_t v___x_10152__boxed_572_; lean_object* v_res_573_; 
v___x_10150__boxed_570_ = lean_unbox(v___x_566_);
v___x_10151__boxed_571_ = lean_unbox_uint32(v___x_567_);
lean_dec(v___x_567_);
v___x_10152__boxed_572_ = lean_unbox_uint32(v___x_568_);
lean_dec(v___x_568_);
v_res_573_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(v___x_10150__boxed_570_, v___x_10151__boxed_571_, v___x_10152__boxed_572_, v___y_569_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(uint32_t v___y_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_576_ = lean_string_push(v___x_575_, v___y_574_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3___boxed(lean_object* v___y_578_){
_start:
{
uint32_t v___y_10214__boxed_579_; lean_object* v_res_580_; 
v___y_10214__boxed_579_ = lean_unbox_uint32(v___y_578_);
lean_dec(v___y_578_);
v_res_580_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(v___y_10214__boxed_579_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4(uint8_t v___x_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_fst_586_; lean_object* v_snd_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v_fst_586_ = lean_ctor_get(v___y_582_, 0);
v_snd_587_ = lean_ctor_get(v___y_582_, 1);
v___x_588_ = lean_string_utf8_byte_size(v_fst_586_);
v___x_589_ = lean_nat_dec_eq(v_snd_587_, v___x_588_);
if (v___x_589_ == 0)
{
if (v___x_581_ == 0)
{
goto v___jp_583_;
}
else
{
lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_600_; 
lean_inc(v_snd_587_);
lean_inc(v_fst_586_);
v_isSharedCheck_600_ = !lean_is_exclusive(v___y_582_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; lean_object* v_unused_602_; 
v_unused_601_ = lean_ctor_get(v___y_582_, 1);
lean_dec(v_unused_601_);
v_unused_602_ = lean_ctor_get(v___y_582_, 0);
lean_dec(v_unused_602_);
v___x_591_ = v___y_582_;
v_isShared_592_ = v_isSharedCheck_600_;
goto v_resetjp_590_;
}
else
{
lean_dec(v___y_582_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_600_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
uint32_t v_c_593_; lean_object* v___x_594_; lean_object* v_it_x27_596_; 
v_c_593_ = lean_string_utf8_get_fast(v_fst_586_, v_snd_587_);
v___x_594_ = lean_string_utf8_next_fast(v_fst_586_, v_snd_587_);
lean_dec(v_snd_587_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v___x_594_);
v_it_x27_596_ = v___x_591_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_fst_586_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v___x_594_);
v_it_x27_596_ = v_reuseFailAlloc_599_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_box_uint32(v_c_593_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v_it_x27_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
return v___x_598_;
}
}
}
}
else
{
goto v___jp_583_;
}
v___jp_583_:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_box(0);
v___x_585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_585_, 0, v___y_582_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4___boxed(lean_object* v___x_603_, lean_object* v___y_604_){
_start:
{
uint8_t v___x_10223__boxed_605_; lean_object* v_res_606_; 
v___x_10223__boxed_605_ = lean_unbox(v___x_603_);
v_res_606_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4(v___x_10223__boxed_605_, v___y_604_);
return v_res_606_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0(void){
_start:
{
uint32_t v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = 92;
v___x_608_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_609_ = lean_string_push(v___x_608_, v___x_607_);
return v___x_609_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0);
v___x_611_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_612_ = lean_string_append(v___x_611_, v___x_610_);
return v___x_612_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_614_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1);
v___x_615_ = lean_string_append(v___x_614_, v___x_613_);
return v___x_615_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__3(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2);
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1(void){
_start:
{
uint32_t v___x_619_; lean_object* v___x_620_; 
v___x_619_ = 34;
v___x_620_ = lean_box_uint32(v___x_619_);
return v___x_620_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2(void){
_start:
{
uint32_t v___x_621_; lean_object* v___x_622_; 
v___x_621_ = 39;
v___x_622_ = lean_box_uint32(v___x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart(lean_object* v_a_623_){
_start:
{
lean_object* v___x_624_; 
lean_inc_ref(v_a_623_);
v___x_624_ = l_Std_Time_parseModifier(v_a_623_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_pos_625_; lean_object* v_res_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_634_; 
lean_dec_ref(v_a_623_);
v_pos_625_ = lean_ctor_get(v___x_624_, 0);
v_res_626_ = lean_ctor_get(v___x_624_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_634_ == 0)
{
v___x_628_ = v___x_624_;
v_isShared_629_ = v_isSharedCheck_634_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_res_626_);
lean_inc(v_pos_625_);
lean_dec(v___x_624_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_634_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v_res_626_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v___x_630_);
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_pos_625_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
else
{
lean_object* v_pos_635_; lean_object* v_err_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_707_; 
v_pos_635_ = lean_ctor_get(v___x_624_, 0);
v_err_636_ = lean_ctor_get(v___x_624_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_707_ == 0)
{
v___x_638_ = v___x_624_;
v_isShared_639_ = v_isSharedCheck_707_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_err_636_);
lean_inc(v_pos_635_);
lean_dec(v___x_624_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_707_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v_snd_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_705_; 
v_snd_640_ = lean_ctor_get(v_a_623_, 1);
v_isSharedCheck_705_ = !lean_is_exclusive(v_a_623_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; 
v_unused_706_ = lean_ctor_get(v_a_623_, 0);
lean_dec(v_unused_706_);
v___x_642_ = v_a_623_;
v_isShared_643_ = v_isSharedCheck_705_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_snd_640_);
lean_dec(v_a_623_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_705_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_fst_644_; lean_object* v_snd_645_; uint8_t v___x_646_; 
v_fst_644_ = lean_ctor_get(v_pos_635_, 0);
v_snd_645_ = lean_ctor_get(v_pos_635_, 1);
v___x_646_ = lean_nat_dec_eq(v_snd_640_, v_snd_645_);
lean_dec(v_snd_640_);
if (v___x_646_ == 0)
{
lean_object* v___x_648_; 
lean_del_object(v___x_642_);
if (v_isShared_639_ == 0)
{
v___x_648_ = v___x_638_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_pos_635_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_err_636_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
else
{
lean_object* v___f_650_; lean_object* v___y_652_; lean_object* v_pos_653_; lean_object* v_snd_654_; lean_object* v___x_680_; uint8_t v___x_681_; 
lean_inc(v_snd_645_);
lean_dec(v_err_636_);
v___f_650_ = ((lean_object*)(l_Std_Time_instCoeStringFormatPart___closed__0));
v___x_680_ = lean_string_utf8_byte_size(v_fst_644_);
v___x_681_ = lean_nat_dec_eq(v_snd_645_, v___x_680_);
if (v___x_681_ == 0)
{
if (v___x_646_ == 0)
{
lean_del_object(v___x_642_);
goto v___jp_675_;
}
else
{
uint32_t v___x_682_; uint32_t v_c_683_; uint8_t v___x_684_; 
lean_del_object(v___x_638_);
v___x_682_ = 92;
v_c_683_ = lean_string_utf8_get_fast(v_fst_644_, v_snd_645_);
v___x_684_ = lean_uint32_dec_eq(v_c_683_, v___x_682_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_685_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__3);
lean_inc(v_pos_635_);
if (v_isShared_643_ == 0)
{
lean_ctor_set_tag(v___x_642_, 1);
lean_ctor_set(v___x_642_, 1, v___x_685_);
lean_ctor_set(v___x_642_, 0, v_pos_635_);
v___x_687_ = v___x_642_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_pos_635_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_inc(v_snd_645_);
v___y_652_ = v___x_687_;
v_pos_653_ = v_pos_635_;
v_snd_654_ = v_snd_645_;
goto v___jp_651_;
}
}
else
{
lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_702_; 
lean_inc(v_fst_644_);
lean_del_object(v___x_642_);
v_isSharedCheck_702_ = !lean_is_exclusive(v_pos_635_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; lean_object* v_unused_704_; 
v_unused_703_ = lean_ctor_get(v_pos_635_, 1);
lean_dec(v_unused_703_);
v_unused_704_ = lean_ctor_get(v_pos_635_, 0);
lean_dec(v_unused_704_);
v___x_690_ = v_pos_635_;
v_isShared_691_ = v_isSharedCheck_702_;
goto v_resetjp_689_;
}
else
{
lean_dec(v_pos_635_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_702_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___f_692_; lean_object* v___x_693_; lean_object* v___f_694_; lean_object* v___x_695_; lean_object* v_it_x27_697_; 
v___f_692_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__4));
v___x_693_ = lean_box(v___x_684_);
v___f_694_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4___boxed), 2, 1);
lean_closure_set(v___f_694_, 0, v___x_693_);
v___x_695_ = lean_string_utf8_next_fast(v_fst_644_, v_snd_645_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___x_695_);
v_it_x27_697_ = v___x_690_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_fst_644_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_695_);
v_it_x27_697_ = v_reuseFailAlloc_701_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_698_; 
v___x_698_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_694_, v___f_692_, v_it_x27_697_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_dec(v_snd_645_);
return v___x_698_;
}
else
{
lean_object* v_pos_699_; lean_object* v_snd_700_; 
v_pos_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_pos_699_);
v_snd_700_ = lean_ctor_get(v_pos_699_, 1);
lean_inc(v_snd_700_);
v___y_652_ = v___x_698_;
v_pos_653_ = v_pos_699_;
v_snd_654_ = v_snd_700_;
goto v___jp_651_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_642_);
goto v___jp_675_;
}
v___jp_651_:
{
uint8_t v___x_655_; 
v___x_655_ = lean_nat_dec_eq(v_snd_645_, v_snd_654_);
lean_dec(v_snd_645_);
if (v___x_655_ == 0)
{
lean_dec(v_snd_654_);
lean_dec_ref(v_pos_653_);
return v___y_652_;
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___f_658_; lean_object* v___x_659_; 
lean_dec_ref(v___y_652_);
v___x_656_ = lean_box(v___x_655_);
v___x_657_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1;
v___f_658_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___boxed), 3, 2);
lean_closure_set(v___f_658_, 0, v___x_656_);
lean_closure_set(v___f_658_, 1, v___x_657_);
v___x_659_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_658_, v___f_650_, v_pos_653_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_dec(v_snd_654_);
return v___x_659_;
}
else
{
lean_object* v_pos_660_; lean_object* v_snd_661_; uint8_t v___x_662_; 
v_pos_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_pos_660_);
v_snd_661_ = lean_ctor_get(v_pos_660_, 1);
lean_inc(v_snd_661_);
v___x_662_ = lean_nat_dec_eq(v_snd_654_, v_snd_661_);
lean_dec(v_snd_654_);
if (v___x_662_ == 0)
{
lean_dec(v_snd_661_);
lean_dec(v_pos_660_);
return v___x_659_;
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___f_665_; lean_object* v___x_666_; 
lean_dec_ref_known(v___x_659_, 2);
v___x_663_ = lean_box(v___x_662_);
v___x_664_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2;
v___f_665_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___boxed), 3, 2);
lean_closure_set(v___f_665_, 0, v___x_663_);
lean_closure_set(v___f_665_, 1, v___x_664_);
v___x_666_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_665_, v___f_650_, v_pos_660_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_dec(v_snd_661_);
return v___x_666_;
}
else
{
lean_object* v_pos_667_; lean_object* v_snd_668_; uint8_t v___x_669_; 
v_pos_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_pos_667_);
v_snd_668_ = lean_ctor_get(v_pos_667_, 1);
v___x_669_ = lean_nat_dec_eq(v_snd_661_, v_snd_668_);
lean_dec(v_snd_661_);
if (v___x_669_ == 0)
{
lean_dec(v_pos_667_);
return v___x_666_;
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___f_673_; lean_object* v___x_674_; 
lean_dec_ref_known(v___x_666_, 2);
v___x_670_ = lean_box(v___x_669_);
v___x_671_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1;
v___x_672_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2;
v___f_673_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2___boxed), 4, 3);
lean_closure_set(v___f_673_, 0, v___x_670_);
lean_closure_set(v___f_673_, 1, v___x_671_);
lean_closure_set(v___f_673_, 2, v___x_672_);
v___x_674_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_673_, v___f_650_, v_pos_667_);
return v___x_674_;
}
}
}
}
}
}
v___jp_675_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = lean_box(0);
lean_inc(v_pos_635_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 1, v___x_676_);
v___x_678_ = v___x_638_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_pos_635_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_inc(v_snd_645_);
v___y_652_ = v___x_678_;
v_pos_653_ = v_pos_635_;
v_snd_654_ = v_snd_645_;
goto v___jp_651_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_specParser_spec__0(lean_object* v_acc_708_, lean_object* v_a_709_){
_start:
{
lean_object* v___x_710_; 
lean_inc_ref(v_a_709_);
v___x_710_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart(v_a_709_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_pos_711_; lean_object* v_res_712_; lean_object* v___x_713_; 
lean_dec_ref(v_a_709_);
v_pos_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_pos_711_);
v_res_712_ = lean_ctor_get(v___x_710_, 1);
lean_inc(v_res_712_);
lean_dec_ref_known(v___x_710_, 2);
v___x_713_ = lean_array_push(v_acc_708_, v_res_712_);
v_acc_708_ = v___x_713_;
v_a_709_ = v_pos_711_;
goto _start;
}
else
{
lean_object* v_pos_715_; lean_object* v_err_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_729_; 
v_pos_715_ = lean_ctor_get(v___x_710_, 0);
v_err_716_ = lean_ctor_get(v___x_710_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_729_ == 0)
{
v___x_718_ = v___x_710_;
v_isShared_719_ = v_isSharedCheck_729_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_err_716_);
lean_inc(v_pos_715_);
lean_dec(v___x_710_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_729_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v_snd_720_; lean_object* v_snd_721_; uint8_t v___x_722_; 
v_snd_720_ = lean_ctor_get(v_a_709_, 1);
lean_inc(v_snd_720_);
lean_dec_ref(v_a_709_);
v_snd_721_ = lean_ctor_get(v_pos_715_, 1);
v___x_722_ = lean_nat_dec_eq(v_snd_720_, v_snd_721_);
lean_dec(v_snd_720_);
if (v___x_722_ == 0)
{
lean_object* v___x_724_; 
lean_dec_ref(v_acc_708_);
if (v_isShared_719_ == 0)
{
v___x_724_ = v___x_718_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_pos_715_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_err_716_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
else
{
lean_object* v___x_727_; 
lean_dec(v_err_716_);
if (v_isShared_719_ == 0)
{
lean_ctor_set_tag(v___x_718_, 0);
lean_ctor_set(v___x_718_, 1, v_acc_708_);
v___x_727_ = v___x_718_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_pos_715_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_acc_708_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParser(lean_object* v_a_735_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__0));
v___x_737_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_specParser_spec__0(v___x_736_, v_a_735_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_pos_738_; lean_object* v_res_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_755_; 
v_pos_738_ = lean_ctor_get(v___x_737_, 0);
v_res_739_ = lean_ctor_get(v___x_737_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_755_ == 0)
{
v___x_741_ = v___x_737_;
v_isShared_742_ = v_isSharedCheck_755_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_res_739_);
lean_inc(v_pos_738_);
lean_dec(v___x_737_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_755_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v_fst_743_; lean_object* v_snd_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v_fst_743_ = lean_ctor_get(v_pos_738_, 0);
v_snd_744_ = lean_ctor_get(v_pos_738_, 1);
v___x_745_ = lean_string_utf8_byte_size(v_fst_743_);
v___x_746_ = lean_nat_dec_eq(v_snd_744_, v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_749_; 
lean_dec(v_res_739_);
v___x_747_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_742_ == 0)
{
lean_ctor_set_tag(v___x_741_, 1);
lean_ctor_set(v___x_741_, 1, v___x_747_);
v___x_749_ = v___x_741_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_pos_738_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
else
{
lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_751_ = lean_array_to_list(v_res_739_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v___x_751_);
v___x_753_ = v___x_741_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_pos_738_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_object* v_pos_756_; lean_object* v_err_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
v_pos_756_ = lean_ctor_get(v___x_737_, 0);
v_err_757_ = lean_ctor_get(v___x_737_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_737_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_err_757_);
lean_inc(v_pos_756_);
lean_dec(v___x_737_);
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParse(lean_object* v_s_765_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_767_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_766_, v_s_765_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(uint32_t v_a_768_, lean_object* v_x_769_, lean_object* v_x_770_){
_start:
{
lean_object* v_zero_771_; uint8_t v_isZero_772_; 
v_zero_771_ = lean_unsigned_to_nat(0u);
v_isZero_772_ = lean_nat_dec_eq(v_x_769_, v_zero_771_);
if (v_isZero_772_ == 1)
{
lean_dec(v_x_769_);
return v_x_770_;
}
else
{
lean_object* v_one_773_; lean_object* v_n_774_; lean_object* v___x_775_; 
v_one_773_ = lean_unsigned_to_nat(1u);
v_n_774_ = lean_nat_sub(v_x_769_, v_one_773_);
lean_dec(v_x_769_);
v___x_775_ = lean_string_push(v_x_770_, v_a_768_);
v_x_769_ = v_n_774_;
v_x_770_ = v___x_775_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1___boxed(lean_object* v_a_777_, lean_object* v_x_778_, lean_object* v_x_779_){
_start:
{
uint32_t v_a_boxed_780_; lean_object* v_res_781_; 
v_a_boxed_780_ = lean_unbox_uint32(v_a_777_);
lean_dec(v_a_777_);
v_res_781_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_boxed_780_, v_x_778_, v_x_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(lean_object* v___x_782_, lean_object* v_s_783_, lean_object* v_a_784_, lean_object* v_b_785_){
_start:
{
lean_object* v_startInclusive_786_; lean_object* v_endExclusive_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_startInclusive_786_ = lean_ctor_get(v___x_782_, 1);
v_endExclusive_787_ = lean_ctor_get(v___x_782_, 2);
v___x_788_ = lean_nat_sub(v_endExclusive_787_, v_startInclusive_786_);
v___x_789_ = lean_nat_dec_eq(v_a_784_, v___x_788_);
lean_dec(v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_790_ = lean_string_utf8_next_fast(v_s_783_, v_a_784_);
lean_dec(v_a_784_);
v___x_791_ = lean_unsigned_to_nat(1u);
v___x_792_ = lean_nat_add(v_b_785_, v___x_791_);
lean_dec(v_b_785_);
v_a_784_ = v___x_790_;
v_b_785_ = v___x_792_;
goto _start;
}
else
{
lean_dec(v_a_784_);
return v_b_785_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg___boxed(lean_object* v___x_794_, lean_object* v_s_795_, lean_object* v_a_796_, lean_object* v_b_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_794_, v_s_795_, v_a_796_, v_b_797_);
lean_dec_ref(v_s_795_);
lean_dec_ref(v___x_794_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(lean_object* v_n_799_, uint32_t v_a_800_, lean_object* v_s_801_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_802_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = lean_string_utf8_byte_size(v_s_801_);
lean_inc_ref(v_s_801_);
v___x_805_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_805_, 0, v_s_801_);
lean_ctor_set(v___x_805_, 1, v___x_803_);
lean_ctor_set(v___x_805_, 2, v___x_804_);
v___x_806_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_805_, v_s_801_, v___x_803_, v___x_803_);
lean_dec_ref_known(v___x_805_, 3);
v___x_807_ = lean_nat_sub(v_n_799_, v___x_806_);
lean_dec(v___x_806_);
v___x_808_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_800_, v___x_807_, v___x_802_);
v___x_809_ = lean_string_append(v___x_808_, v_s_801_);
lean_dec_ref(v_s_801_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii___boxed(lean_object* v_n_810_, lean_object* v_a_811_, lean_object* v_s_812_){
_start:
{
uint32_t v_a_boxed_813_; lean_object* v_res_814_; 
v_a_boxed_813_ = lean_unbox_uint32(v_a_811_);
lean_dec(v_a_811_);
v_res_814_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v_n_810_, v_a_boxed_813_, v_s_812_);
lean_dec(v_n_810_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0(lean_object* v___x_815_, lean_object* v_s_816_, lean_object* v_inst_817_, lean_object* v_R_818_, lean_object* v_a_819_, lean_object* v_b_820_, lean_object* v_c_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_815_, v_s_816_, v_a_819_, v_b_820_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___boxed(lean_object* v___x_823_, lean_object* v_s_824_, lean_object* v_inst_825_, lean_object* v_R_826_, lean_object* v_a_827_, lean_object* v_b_828_, lean_object* v_c_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0(v___x_823_, v_s_824_, v_inst_825_, v_R_826_, v_a_827_, v_b_828_, v_c_829_);
lean_dec_ref(v_s_824_);
lean_dec_ref(v___x_823_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(lean_object* v_n_831_, uint32_t v_a_832_, lean_object* v_s_833_){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_834_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = lean_string_utf8_byte_size(v_s_833_);
lean_inc_ref(v_s_833_);
v___x_837_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_837_, 0, v_s_833_);
lean_ctor_set(v___x_837_, 1, v___x_835_);
lean_ctor_set(v___x_837_, 2, v___x_836_);
v___x_838_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_837_, v_s_833_, v___x_835_, v___x_835_);
lean_dec_ref_known(v___x_837_, 3);
v___x_839_ = lean_nat_sub(v_n_831_, v___x_838_);
lean_dec(v___x_838_);
v___x_840_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_832_, v___x_839_, v___x_834_);
v___x_841_ = lean_string_append(v_s_833_, v___x_840_);
lean_dec_ref(v___x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii___boxed(lean_object* v_n_842_, lean_object* v_a_843_, lean_object* v_s_844_){
_start:
{
uint32_t v_a_boxed_845_; lean_object* v_res_846_; 
v_a_boxed_845_ = lean_unbox_uint32(v_a_843_);
lean_dec(v_a_843_);
v_res_846_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_n_842_, v_a_boxed_845_, v_s_844_);
lean_dec(v_n_842_);
return v_res_846_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_unsigned_to_nat(0u);
v___x_848_ = lean_nat_to_int(v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad(lean_object* v_size_850_, lean_object* v_n_851_, uint8_t v_cut_852_){
_start:
{
lean_object* v_fst_854_; lean_object* v_snd_855_; lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_869_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_870_ = lean_int_dec_lt(v_n_851_, v___x_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; 
v___x_871_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v_fst_854_ = v___x_871_;
v_snd_855_ = v_n_851_;
goto v___jp_853_;
}
else
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_873_ = lean_int_neg(v_n_851_);
lean_dec(v_n_851_);
v_fst_854_ = v___x_872_;
v_snd_855_ = v___x_873_;
goto v___jp_853_;
}
v___jp_853_:
{
lean_object* v_numStr_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v_numStr_856_ = l_Int_repr(v_snd_855_);
lean_dec(v_snd_855_);
v___x_857_ = lean_string_utf8_byte_size(v_numStr_856_);
v___x_858_ = lean_nat_dec_lt(v_size_850_, v___x_857_);
if (v___x_858_ == 0)
{
uint32_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_859_ = 48;
v___x_860_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v_size_850_, v___x_859_, v_numStr_856_);
lean_inc_ref(v_fst_854_);
v___x_861_ = lean_string_append(v_fst_854_, v___x_860_);
lean_dec_ref(v___x_860_);
return v___x_861_;
}
else
{
if (v_cut_852_ == 0)
{
lean_object* v___x_862_; 
lean_inc_ref(v_fst_854_);
v___x_862_ = lean_string_append(v_fst_854_, v_numStr_856_);
lean_dec_ref(v_numStr_856_);
return v___x_862_;
}
else
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_863_ = lean_nat_sub(v___x_857_, v_size_850_);
v___x_864_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_numStr_856_);
v___x_865_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_865_, 0, v_numStr_856_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
lean_ctor_set(v___x_865_, 2, v___x_857_);
v___x_866_ = l_String_Slice_Pos_nextn(v___x_865_, v___x_864_, v___x_863_);
lean_dec_ref_known(v___x_865_, 3);
v___x_867_ = lean_string_utf8_extract_fast(v_numStr_856_, v___x_866_, v___x_857_);
lean_dec(v___x_866_);
lean_dec_ref(v_numStr_856_);
lean_inc_ref(v_fst_854_);
v___x_868_ = lean_string_append(v_fst_854_, v___x_867_);
lean_dec_ref(v___x_867_);
return v___x_868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad___boxed(lean_object* v_size_874_, lean_object* v_n_875_, lean_object* v_cut_876_){
_start:
{
uint8_t v_cut_boxed_877_; lean_object* v_res_878_; 
v_cut_boxed_877_ = lean_unbox(v_cut_876_);
v_res_878_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_size_874_, v_n_875_, v_cut_boxed_877_);
lean_dec(v_size_874_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate(lean_object* v_size_879_, lean_object* v_n_880_, uint8_t v_cut_881_){
_start:
{
lean_object* v_fst_883_; lean_object* v_snd_884_; lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_898_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_899_ = lean_int_dec_lt(v_n_880_, v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; 
v___x_900_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v_fst_883_ = v___x_900_;
v_snd_884_ = v_n_880_;
goto v___jp_882_;
}
else
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_902_ = lean_int_neg(v_n_880_);
lean_dec(v_n_880_);
v_fst_883_ = v___x_901_;
v_snd_884_ = v___x_902_;
goto v___jp_882_;
}
v___jp_882_:
{
lean_object* v_numStr_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v_numStr_885_ = l_Int_repr(v_snd_884_);
lean_dec(v_snd_884_);
v___x_886_ = lean_string_length(v_numStr_885_);
v___x_887_ = lean_nat_dec_lt(v_size_879_, v___x_886_);
if (v___x_887_ == 0)
{
uint32_t v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = 48;
v___x_889_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_size_879_, v___x_888_, v_numStr_885_);
lean_dec(v_size_879_);
lean_inc_ref(v_fst_883_);
v___x_890_ = lean_string_append(v_fst_883_, v___x_889_);
lean_dec_ref(v___x_889_);
return v___x_890_;
}
else
{
if (v_cut_881_ == 0)
{
lean_object* v___x_891_; 
lean_dec(v_size_879_);
lean_inc_ref(v_fst_883_);
v___x_891_ = lean_string_append(v_fst_883_, v_numStr_885_);
lean_dec_ref(v_numStr_885_);
return v___x_891_;
}
else
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_892_ = lean_unsigned_to_nat(0u);
v___x_893_ = lean_string_utf8_byte_size(v_numStr_885_);
lean_inc_ref(v_numStr_885_);
v___x_894_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_894_, 0, v_numStr_885_);
lean_ctor_set(v___x_894_, 1, v___x_892_);
lean_ctor_set(v___x_894_, 2, v___x_893_);
v___x_895_ = l_String_Slice_Pos_nextn(v___x_894_, v___x_892_, v_size_879_);
lean_dec_ref_known(v___x_894_, 3);
v___x_896_ = lean_string_utf8_extract_fast(v_numStr_885_, v___x_892_, v___x_895_);
lean_dec(v___x_895_);
lean_dec_ref(v_numStr_885_);
lean_inc_ref(v_fst_883_);
v___x_897_ = lean_string_append(v_fst_883_, v___x_896_);
lean_dec_ref(v___x_896_);
return v___x_897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate___boxed(lean_object* v_size_903_, lean_object* v_n_904_, lean_object* v_cut_905_){
_start:
{
uint8_t v_cut_boxed_906_; lean_object* v_res_907_; 
v_cut_boxed_906_ = lean_unbox(v_cut_905_);
v_res_907_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate(v_size_903_, v_n_904_, v_cut_boxed_906_);
return v_res_907_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__0(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_908_ = lean_unsigned_to_nat(2u);
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = lean_nat_mod(v___x_909_, v___x_908_);
return v___x_910_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__1(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_911_ = lean_unsigned_to_nat(2u);
v___x_912_ = lean_unsigned_to_nat(1u);
v___x_913_ = lean_nat_mod(v___x_912_, v___x_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(uint8_t v_x_914_){
_start:
{
if (v_x_914_ == 0)
{
lean_object* v___x_915_; 
v___x_915_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__0);
return v___x_915_;
}
else
{
lean_object* v___x_916_; 
v___x_916_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__1);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___boxed(lean_object* v_x_917_){
_start:
{
uint8_t v_x_52__boxed_918_; lean_object* v_res_919_; 
v_x_52__boxed_918_ = lean_unbox(v_x_917_);
v_res_919_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_x_52__boxed_918_);
return v_res_919_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_921_ = lean_int_neg(v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(lean_object* v_symbols_922_, lean_object* v_month_923_){
_start:
{
lean_object* v_monthLong_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_monthLong_924_ = lean_ctor_get(v_symbols_922_, 0);
v___x_925_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_926_ = lean_int_add(v_month_923_, v___x_925_);
v___x_927_ = l_Int_toNat(v___x_926_);
lean_dec(v___x_926_);
v___x_928_ = lean_array_fget_borrowed(v_monthLong_924_, v___x_927_);
lean_dec(v___x_927_);
lean_inc(v___x_928_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___boxed(lean_object* v_symbols_929_, lean_object* v_month_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_929_, v_month_930_);
lean_dec(v_month_930_);
lean_dec_ref(v_symbols_929_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(lean_object* v_symbols_932_, lean_object* v_month_933_){
_start:
{
lean_object* v_monthShort_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_monthShort_934_ = lean_ctor_get(v_symbols_932_, 1);
v___x_935_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_936_ = lean_int_add(v_month_933_, v___x_935_);
v___x_937_ = l_Int_toNat(v___x_936_);
lean_dec(v___x_936_);
v___x_938_ = lean_array_fget_borrowed(v_monthShort_934_, v___x_937_);
lean_dec(v___x_937_);
lean_inc(v___x_938_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort___boxed(lean_object* v_symbols_939_, lean_object* v_month_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_939_, v_month_940_);
lean_dec(v_month_940_);
lean_dec_ref(v_symbols_939_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(lean_object* v_symbols_942_, lean_object* v_month_943_){
_start:
{
lean_object* v_monthNarrow_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_monthNarrow_944_ = lean_ctor_get(v_symbols_942_, 2);
v___x_945_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_946_ = lean_int_add(v_month_943_, v___x_945_);
v___x_947_ = l_Int_toNat(v___x_946_);
lean_dec(v___x_946_);
v___x_948_ = lean_array_fget_borrowed(v_monthNarrow_944_, v___x_947_);
lean_dec(v___x_947_);
lean_inc(v___x_948_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow___boxed(lean_object* v_symbols_949_, lean_object* v_month_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_949_, v_month_950_);
lean_dec(v_month_950_);
lean_dec_ref(v_symbols_949_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(lean_object* v_symbols_952_, uint8_t v_wd_953_){
_start:
{
lean_object* v_weekdayLong_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_weekdayLong_954_ = lean_ctor_get(v_symbols_952_, 3);
v___x_955_ = l_Std_Time_Weekday_toOrdinal(v_wd_953_);
v___x_956_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_957_ = lean_int_add(v___x_955_, v___x_956_);
lean_dec(v___x_955_);
v___x_958_ = l_Int_toNat(v___x_957_);
lean_dec(v___x_957_);
v___x_959_ = lean_array_fget_borrowed(v_weekdayLong_954_, v___x_958_);
lean_dec(v___x_958_);
lean_inc(v___x_959_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong___boxed(lean_object* v_symbols_960_, lean_object* v_wd_961_){
_start:
{
uint8_t v_wd_boxed_962_; lean_object* v_res_963_; 
v_wd_boxed_962_ = lean_unbox(v_wd_961_);
v_res_963_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_960_, v_wd_boxed_962_);
lean_dec_ref(v_symbols_960_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(lean_object* v_symbols_964_, uint8_t v_wd_965_){
_start:
{
lean_object* v_weekdayShort_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_weekdayShort_966_ = lean_ctor_get(v_symbols_964_, 4);
v___x_967_ = l_Std_Time_Weekday_toOrdinal(v_wd_965_);
v___x_968_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_969_ = lean_int_add(v___x_967_, v___x_968_);
lean_dec(v___x_967_);
v___x_970_ = l_Int_toNat(v___x_969_);
lean_dec(v___x_969_);
v___x_971_ = lean_array_fget_borrowed(v_weekdayShort_966_, v___x_970_);
lean_dec(v___x_970_);
lean_inc(v___x_971_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort___boxed(lean_object* v_symbols_972_, lean_object* v_wd_973_){
_start:
{
uint8_t v_wd_boxed_974_; lean_object* v_res_975_; 
v_wd_boxed_974_ = lean_unbox(v_wd_973_);
v_res_975_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_972_, v_wd_boxed_974_);
lean_dec_ref(v_symbols_972_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(lean_object* v_symbols_976_, uint8_t v_wd_977_){
_start:
{
lean_object* v_weekdayNarrow_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_weekdayNarrow_978_ = lean_ctor_get(v_symbols_976_, 5);
v___x_979_ = l_Std_Time_Weekday_toOrdinal(v_wd_977_);
v___x_980_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_981_ = lean_int_add(v___x_979_, v___x_980_);
lean_dec(v___x_979_);
v___x_982_ = l_Int_toNat(v___x_981_);
lean_dec(v___x_981_);
v___x_983_ = lean_array_fget_borrowed(v_weekdayNarrow_978_, v___x_982_);
lean_dec(v___x_982_);
lean_inc(v___x_983_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow___boxed(lean_object* v_symbols_984_, lean_object* v_wd_985_){
_start:
{
uint8_t v_wd_boxed_986_; lean_object* v_res_987_; 
v_wd_boxed_986_ = lean_unbox(v_wd_985_);
v_res_987_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_984_, v_wd_boxed_986_);
lean_dec_ref(v_symbols_984_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(lean_object* v_symbols_988_, uint8_t v_wd_989_){
_start:
{
lean_object* v_weekdayTwoLetter_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_weekdayTwoLetter_990_ = lean_ctor_get(v_symbols_988_, 6);
v___x_991_ = l_Std_Time_Weekday_toOrdinal(v_wd_989_);
v___x_992_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_993_ = lean_int_add(v___x_991_, v___x_992_);
lean_dec(v___x_991_);
v___x_994_ = l_Int_toNat(v___x_993_);
lean_dec(v___x_993_);
v___x_995_ = lean_array_fget_borrowed(v_weekdayTwoLetter_990_, v___x_994_);
lean_dec(v___x_994_);
lean_inc(v___x_995_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter___boxed(lean_object* v_symbols_996_, lean_object* v_wd_997_){
_start:
{
uint8_t v_wd_boxed_998_; lean_object* v_res_999_; 
v_wd_boxed_998_ = lean_unbox(v_wd_997_);
v_res_999_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_996_, v_wd_boxed_998_);
lean_dec_ref(v_symbols_996_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(lean_object* v_symbols_1000_, uint8_t v_era_1001_){
_start:
{
lean_object* v_eraShort_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v_eraShort_1002_ = lean_ctor_get(v_symbols_1000_, 7);
v___x_1003_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_1001_);
v___x_1004_ = lean_array_fget_borrowed(v_eraShort_1002_, v___x_1003_);
lean_dec(v___x_1003_);
lean_inc(v___x_1004_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort___boxed(lean_object* v_symbols_1005_, lean_object* v_era_1006_){
_start:
{
uint8_t v_era_boxed_1007_; lean_object* v_res_1008_; 
v_era_boxed_1007_ = lean_unbox(v_era_1006_);
v_res_1008_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(v_symbols_1005_, v_era_boxed_1007_);
lean_dec_ref(v_symbols_1005_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(lean_object* v_symbols_1009_, uint8_t v_era_1010_){
_start:
{
lean_object* v_eraLong_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v_eraLong_1011_ = lean_ctor_get(v_symbols_1009_, 8);
v___x_1012_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_1010_);
v___x_1013_ = lean_array_fget_borrowed(v_eraLong_1011_, v___x_1012_);
lean_dec(v___x_1012_);
lean_inc(v___x_1013_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong___boxed(lean_object* v_symbols_1014_, lean_object* v_era_1015_){
_start:
{
uint8_t v_era_boxed_1016_; lean_object* v_res_1017_; 
v_era_boxed_1016_ = lean_unbox(v_era_1015_);
v_res_1017_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(v_symbols_1014_, v_era_boxed_1016_);
lean_dec_ref(v_symbols_1014_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(lean_object* v_symbols_1018_, uint8_t v_era_1019_){
_start:
{
lean_object* v_eraNarrow_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_eraNarrow_1020_ = lean_ctor_get(v_symbols_1018_, 9);
v___x_1021_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_1019_);
v___x_1022_ = lean_array_fget_borrowed(v_eraNarrow_1020_, v___x_1021_);
lean_dec(v___x_1021_);
lean_inc(v___x_1022_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow___boxed(lean_object* v_symbols_1023_, lean_object* v_era_1024_){
_start:
{
uint8_t v_era_boxed_1025_; lean_object* v_res_1026_; 
v_era_boxed_1025_ = lean_unbox(v_era_1024_);
v_res_1026_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(v_symbols_1023_, v_era_boxed_1025_);
lean_dec_ref(v_symbols_1023_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(lean_object* v_x_1031_){
_start:
{
lean_object* v_natZero_1032_; lean_object* v_intZero_1033_; uint8_t v_isNeg_1034_; lean_object* v_a_1035_; uint8_t v_isZero_1036_; lean_object* v_one_1037_; lean_object* v_n_1038_; uint8_t v_isZero_1039_; 
v_natZero_1032_ = lean_unsigned_to_nat(0u);
v_intZero_1033_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v_isNeg_1034_ = lean_int_dec_lt(v_x_1031_, v_intZero_1033_);
v_a_1035_ = lean_nat_abs(v_x_1031_);
v_isZero_1036_ = lean_nat_dec_eq(v_a_1035_, v_natZero_1032_);
v_one_1037_ = lean_unsigned_to_nat(1u);
v_n_1038_ = lean_nat_sub(v_a_1035_, v_one_1037_);
lean_dec(v_a_1035_);
v_isZero_1039_ = lean_nat_dec_eq(v_n_1038_, v_natZero_1032_);
if (v_isZero_1039_ == 1)
{
lean_object* v___x_1040_; 
lean_dec(v_n_1038_);
v___x_1040_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__0));
return v___x_1040_;
}
else
{
lean_object* v_n_1041_; uint8_t v_isZero_1042_; 
v_n_1041_ = lean_nat_sub(v_n_1038_, v_one_1037_);
lean_dec(v_n_1038_);
v_isZero_1042_ = lean_nat_dec_eq(v_n_1041_, v_natZero_1032_);
if (v_isZero_1042_ == 1)
{
lean_object* v___x_1043_; 
lean_dec(v_n_1041_);
v___x_1043_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__1));
return v___x_1043_;
}
else
{
lean_object* v_n_1044_; uint8_t v_isZero_1045_; 
v_n_1044_ = lean_nat_sub(v_n_1041_, v_one_1037_);
lean_dec(v_n_1041_);
v_isZero_1045_ = lean_nat_dec_eq(v_n_1044_, v_natZero_1032_);
if (v_isZero_1045_ == 1)
{
lean_object* v___x_1046_; 
lean_dec(v_n_1044_);
v___x_1046_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__2));
return v___x_1046_;
}
else
{
lean_object* v_n_1047_; uint8_t v_isZero_1048_; lean_object* v___x_1049_; 
v_n_1047_ = lean_nat_sub(v_n_1044_, v_one_1037_);
lean_dec(v_n_1044_);
v_isZero_1048_ = lean_nat_dec_eq(v_n_1047_, v_natZero_1032_);
lean_dec(v_n_1047_);
v___x_1049_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__3));
return v___x_1049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___boxed(lean_object* v_x_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_x_1050_);
lean_dec(v_x_1050_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(lean_object* v_symbols_1052_, lean_object* v_q_1053_){
_start:
{
lean_object* v_quarterShort_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v_quarterShort_1054_ = lean_ctor_get(v_symbols_1052_, 10);
v___x_1055_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1056_ = lean_int_add(v_q_1053_, v___x_1055_);
v___x_1057_ = l_Int_toNat(v___x_1056_);
lean_dec(v___x_1056_);
v___x_1058_ = lean_array_fget_borrowed(v_quarterShort_1054_, v___x_1057_);
lean_dec(v___x_1057_);
lean_inc(v___x_1058_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort___boxed(lean_object* v_symbols_1059_, lean_object* v_q_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1059_, v_q_1060_);
lean_dec(v_q_1060_);
lean_dec_ref(v_symbols_1059_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(lean_object* v_symbols_1062_, lean_object* v_q_1063_){
_start:
{
lean_object* v_quarterLong_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_quarterLong_1064_ = lean_ctor_get(v_symbols_1062_, 11);
v___x_1065_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1066_ = lean_int_add(v_q_1063_, v___x_1065_);
v___x_1067_ = l_Int_toNat(v___x_1066_);
lean_dec(v___x_1066_);
v___x_1068_ = lean_array_fget_borrowed(v_quarterLong_1064_, v___x_1067_);
lean_dec(v___x_1067_);
lean_inc(v___x_1068_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong___boxed(lean_object* v_symbols_1069_, lean_object* v_q_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1069_, v_q_1070_);
lean_dec(v_q_1070_);
lean_dec_ref(v_symbols_1069_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(lean_object* v_symbols_1072_, lean_object* v_q_1073_){
_start:
{
lean_object* v_quarterNarrow_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v_quarterNarrow_1074_ = lean_ctor_get(v_symbols_1072_, 12);
v___x_1075_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1076_ = lean_int_add(v_q_1073_, v___x_1075_);
v___x_1077_ = l_Int_toNat(v___x_1076_);
lean_dec(v___x_1076_);
v___x_1078_ = lean_array_fget_borrowed(v_quarterNarrow_1074_, v___x_1077_);
lean_dec(v___x_1077_);
lean_inc(v___x_1078_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow___boxed(lean_object* v_symbols_1079_, lean_object* v_q_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1079_, v_q_1080_);
lean_dec(v_q_1080_);
lean_dec_ref(v_symbols_1079_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(lean_object* v_symbols_1082_, uint8_t v_marker_1083_){
_start:
{
if (v_marker_1083_ == 0)
{
lean_object* v_amShort_1084_; 
v_amShort_1084_ = lean_ctor_get(v_symbols_1082_, 13);
lean_inc_ref(v_amShort_1084_);
return v_amShort_1084_;
}
else
{
lean_object* v_pmShort_1085_; 
v_pmShort_1085_ = lean_ctor_get(v_symbols_1082_, 14);
lean_inc_ref(v_pmShort_1085_);
return v_pmShort_1085_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort___boxed(lean_object* v_symbols_1086_, lean_object* v_marker_1087_){
_start:
{
uint8_t v_marker_boxed_1088_; lean_object* v_res_1089_; 
v_marker_boxed_1088_ = lean_unbox(v_marker_1087_);
v_res_1089_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(v_symbols_1086_, v_marker_boxed_1088_);
lean_dec_ref(v_symbols_1086_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong(lean_object* v_symbols_1090_, uint8_t v_marker_1091_){
_start:
{
if (v_marker_1091_ == 0)
{
lean_object* v_amLong_1092_; 
v_amLong_1092_ = lean_ctor_get(v_symbols_1090_, 15);
lean_inc_ref(v_amLong_1092_);
return v_amLong_1092_;
}
else
{
lean_object* v_pmLong_1093_; 
v_pmLong_1093_ = lean_ctor_get(v_symbols_1090_, 16);
lean_inc_ref(v_pmLong_1093_);
return v_pmLong_1093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong___boxed(lean_object* v_symbols_1094_, lean_object* v_marker_1095_){
_start:
{
uint8_t v_marker_boxed_1096_; lean_object* v_res_1097_; 
v_marker_boxed_1096_ = lean_unbox(v_marker_1095_);
v_res_1097_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong(v_symbols_1094_, v_marker_boxed_1096_);
lean_dec_ref(v_symbols_1094_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(lean_object* v_symbols_1098_, uint8_t v_marker_1099_){
_start:
{
if (v_marker_1099_ == 0)
{
lean_object* v_amNarrow_1100_; 
v_amNarrow_1100_ = lean_ctor_get(v_symbols_1098_, 17);
lean_inc_ref(v_amNarrow_1100_);
return v_amNarrow_1100_;
}
else
{
lean_object* v_pmNarrow_1101_; 
v_pmNarrow_1101_ = lean_ctor_get(v_symbols_1098_, 18);
lean_inc_ref(v_pmNarrow_1101_);
return v_pmNarrow_1101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow___boxed(lean_object* v_symbols_1102_, lean_object* v_marker_1103_){
_start:
{
uint8_t v_marker_boxed_1104_; lean_object* v_res_1105_; 
v_marker_boxed_1104_ = lean_unbox(v_marker_1103_);
v_res_1105_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(v_symbols_1102_, v_marker_boxed_1104_);
lean_dec_ref(v_symbols_1102_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(lean_object* v_dp_1106_, uint8_t v_period_1107_){
_start:
{
switch(v_period_1107_)
{
case 0:
{
lean_object* v_am_1108_; 
v_am_1108_ = lean_ctor_get(v_dp_1106_, 0);
lean_inc_ref(v_am_1108_);
return v_am_1108_;
}
case 1:
{
lean_object* v_pm_1109_; 
v_pm_1109_ = lean_ctor_get(v_dp_1106_, 1);
lean_inc_ref(v_pm_1109_);
return v_pm_1109_;
}
case 2:
{
lean_object* v_noon_1110_; 
v_noon_1110_ = lean_ctor_get(v_dp_1106_, 2);
lean_inc_ref(v_noon_1110_);
return v_noon_1110_;
}
default: 
{
lean_object* v_midnight_1111_; 
v_midnight_1111_ = lean_ctor_get(v_dp_1106_, 3);
lean_inc_ref(v_midnight_1111_);
return v_midnight_1111_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod___boxed(lean_object* v_dp_1112_, lean_object* v_period_1113_){
_start:
{
uint8_t v_period_boxed_1114_; lean_object* v_res_1115_; 
v_period_boxed_1114_ = lean_unbox(v_period_1113_);
v_res_1115_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dp_1112_, v_period_boxed_1114_);
lean_dec_ref(v_dp_1112_);
return v_res_1115_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = lean_unsigned_to_nat(6u);
v___x_1117_ = lean_unsigned_to_nat(0u);
v___x_1118_ = lean_nat_mod(v___x_1117_, v___x_1116_);
return v___x_1118_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = lean_unsigned_to_nat(6u);
v___x_1120_ = lean_unsigned_to_nat(1u);
v___x_1121_ = lean_nat_mod(v___x_1120_, v___x_1119_);
return v___x_1121_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = lean_unsigned_to_nat(6u);
v___x_1123_ = lean_unsigned_to_nat(2u);
v___x_1124_ = lean_nat_mod(v___x_1123_, v___x_1122_);
return v___x_1124_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = lean_unsigned_to_nat(6u);
v___x_1126_ = lean_unsigned_to_nat(3u);
v___x_1127_ = lean_nat_mod(v___x_1126_, v___x_1125_);
return v___x_1127_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = lean_unsigned_to_nat(6u);
v___x_1129_ = lean_unsigned_to_nat(4u);
v___x_1130_ = lean_nat_mod(v___x_1129_, v___x_1128_);
return v___x_1130_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1131_ = lean_unsigned_to_nat(6u);
v___x_1132_ = lean_unsigned_to_nat(5u);
v___x_1133_ = lean_nat_mod(v___x_1132_, v___x_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(uint8_t v_x_1134_){
_start:
{
switch(v_x_1134_)
{
case 0:
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0);
return v___x_1135_;
}
case 1:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1);
return v___x_1136_;
}
case 2:
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2);
return v___x_1137_;
}
case 3:
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3);
return v___x_1138_;
}
case 4:
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4);
return v___x_1139_;
}
default: 
{
lean_object* v___x_1140_; 
v___x_1140_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5);
return v___x_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___boxed(lean_object* v_x_1141_){
_start:
{
uint8_t v_x_148__boxed_1142_; lean_object* v_res_1143_; 
v_x_148__boxed_1142_ = lean_unbox(v_x_1141_);
v_res_1143_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(v_x_148__boxed_1142_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(lean_object* v_arr_1144_, uint8_t v_period_1145_){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(v_period_1145_);
v___x_1147_ = lean_array_fget_borrowed(v_arr_1144_, v___x_1146_);
lean_dec(v___x_1146_);
lean_inc(v___x_1147_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod___boxed(lean_object* v_arr_1148_, lean_object* v_period_1149_){
_start:
{
uint8_t v_period_boxed_1150_; lean_object* v_res_1151_; 
v_period_boxed_1150_ = lean_unbox(v_period_1149_);
v_res_1151_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_arr_1148_, v_period_boxed_1150_);
lean_dec_ref(v_arr_1148_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned(lean_object* v_data_1153_){
_start:
{
lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1154_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1155_ = lean_int_dec_lt(v_data_1153_, v___x_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_1157_ = l_Int_repr(v_data_1153_);
v___x_1158_ = lean_string_append(v___x_1156_, v___x_1157_);
lean_dec_ref(v___x_1157_);
return v___x_1158_;
}
else
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Int_repr(v_data_1153_);
return v___x_1159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___boxed(lean_object* v_data_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l___private_Std_Time_Format_Basic_0__Std_Time_toSigned(v_data_1160_);
lean_dec(v_data_1160_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(uint8_t v_x_1162_){
_start:
{
switch(v_x_1162_)
{
case 0:
{
lean_object* v___x_1163_; 
v___x_1163_ = lean_unsigned_to_nat(0u);
return v___x_1163_;
}
case 1:
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_unsigned_to_nat(1u);
return v___x_1164_;
}
default: 
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_unsigned_to_nat(2u);
return v___x_1165_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___boxed(lean_object* v_x_1166_){
_start:
{
uint8_t v_x_boxed_1167_; lean_object* v_res_1168_; 
v_x_boxed_1167_ = lean_unbox(v_x_1166_);
v_res_1168_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(v_x_boxed_1167_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg(lean_object* v_k_1169_){
_start:
{
lean_inc(v_k_1169_);
return v_k_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg___boxed(lean_object* v_k_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg(v_k_1170_);
lean_dec(v_k_1170_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(lean_object* v_motive_1172_, lean_object* v_ctorIdx_1173_, uint8_t v_t_1174_, lean_object* v_h_1175_, lean_object* v_k_1176_){
_start:
{
lean_inc(v_k_1176_);
return v_k_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___boxed(lean_object* v_motive_1177_, lean_object* v_ctorIdx_1178_, lean_object* v_t_1179_, lean_object* v_h_1180_, lean_object* v_k_1181_){
_start:
{
uint8_t v_t_boxed_1182_; lean_object* v_res_1183_; 
v_t_boxed_1182_ = lean_unbox(v_t_1179_);
v_res_1183_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(v_motive_1177_, v_ctorIdx_1178_, v_t_boxed_1182_, v_h_1180_, v_k_1181_);
lean_dec(v_k_1181_);
lean_dec(v_ctorIdx_1178_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg(lean_object* v_yes_1184_){
_start:
{
lean_inc(v_yes_1184_);
return v_yes_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg___boxed(lean_object* v_yes_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg(v_yes_1185_);
lean_dec(v_yes_1185_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(lean_object* v_motive_1187_, uint8_t v_t_1188_, lean_object* v_h_1189_, lean_object* v_yes_1190_){
_start:
{
lean_inc(v_yes_1190_);
return v_yes_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___boxed(lean_object* v_motive_1191_, lean_object* v_t_1192_, lean_object* v_h_1193_, lean_object* v_yes_1194_){
_start:
{
uint8_t v_t_boxed_1195_; lean_object* v_res_1196_; 
v_t_boxed_1195_ = lean_unbox(v_t_1192_);
v_res_1196_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(v_motive_1191_, v_t_boxed_1195_, v_h_1193_, v_yes_1194_);
lean_dec(v_yes_1194_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg(lean_object* v_no_1197_){
_start:
{
lean_inc(v_no_1197_);
return v_no_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg___boxed(lean_object* v_no_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg(v_no_1198_);
lean_dec(v_no_1198_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim(lean_object* v_motive_1200_, uint8_t v_t_1201_, lean_object* v_h_1202_, lean_object* v_no_1203_){
_start:
{
lean_inc(v_no_1203_);
return v_no_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___boxed(lean_object* v_motive_1204_, lean_object* v_t_1205_, lean_object* v_h_1206_, lean_object* v_no_1207_){
_start:
{
uint8_t v_t_boxed_1208_; lean_object* v_res_1209_; 
v_t_boxed_1208_ = lean_unbox(v_t_1205_);
v_res_1209_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim(v_motive_1204_, v_t_boxed_1208_, v_h_1206_, v_no_1207_);
lean_dec(v_no_1207_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg(lean_object* v_optional_1210_){
_start:
{
lean_inc(v_optional_1210_);
return v_optional_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg___boxed(lean_object* v_optional_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg(v_optional_1211_);
lean_dec(v_optional_1211_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(lean_object* v_motive_1213_, uint8_t v_t_1214_, lean_object* v_h_1215_, lean_object* v_optional_1216_){
_start:
{
lean_inc(v_optional_1216_);
return v_optional_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___boxed(lean_object* v_motive_1217_, lean_object* v_t_1218_, lean_object* v_h_1219_, lean_object* v_optional_1220_){
_start:
{
uint8_t v_t_boxed_1221_; lean_object* v_res_1222_; 
v_t_boxed_1221_ = lean_unbox(v_t_1218_);
v_res_1222_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(v_motive_1217_, v_t_boxed_1221_, v_h_1219_, v_optional_1220_);
lean_dec(v_optional_1220_);
return v_res_1222_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(uint8_t v_x_1223_, uint8_t v_y_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1225_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(v_x_1223_);
v___x_1226_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(v_y_1224_);
v___x_1227_ = lean_nat_dec_eq(v___x_1225_, v___x_1226_);
lean_dec(v___x_1226_);
lean_dec(v___x_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq___boxed(lean_object* v_x_1228_, lean_object* v_y_1229_){
_start:
{
uint8_t v_x_17__boxed_1230_; uint8_t v_y_18__boxed_1231_; uint8_t v_res_1232_; lean_object* v_r_1233_; 
v_x_17__boxed_1230_ = lean_unbox(v_x_1228_);
v_y_18__boxed_1231_ = lean_unbox(v_y_1229_);
v_res_1232_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_x_17__boxed_1230_, v_y_18__boxed_1231_);
v_r_1233_ = lean_box(v_res_1232_);
return v_r_1233_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__1(lean_object* v_a_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Rat_ofInt(v_a_1236_);
return v___x_1237_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = lean_unsigned_to_nat(1000000000u);
v___x_1240_ = lean_nat_to_int(v___x_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(lean_object* v_offset_1241_, uint8_t v_withMinutes_1242_, uint8_t v_withSeconds_1243_, uint8_t v_colon_1244_, uint8_t v_padHour_1245_){
_start:
{
uint32_t v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1258_; uint32_t v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; uint32_t v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; uint8_t v___y_1269_; uint32_t v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; uint8_t v___y_1274_; lean_object* v___y_1275_; uint32_t v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; uint8_t v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; uint32_t v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; uint8_t v___y_1298_; lean_object* v___y_1299_; uint32_t v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; uint8_t v___y_1306_; lean_object* v___y_1307_; uint8_t v___y_1308_; lean_object* v___y_1310_; uint32_t v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v_fst_1324_; lean_object* v_snd_1325_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1337_ = lean_int_dec_le(v___x_1336_, v_offset_1241_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1339_ = lean_int_neg(v_offset_1241_);
lean_dec(v_offset_1241_);
v_fst_1324_ = v___x_1338_;
v_snd_1325_ = v___x_1339_;
goto v___jp_1323_;
}
else
{
lean_object* v___x_1340_; 
v___x_1340_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v_fst_1324_ = v___x_1340_;
v_snd_1325_ = v_offset_1241_;
goto v___jp_1323_;
}
v___jp_1246_:
{
lean_object* v_second_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_second_1252_ = lean_ctor_get(v___y_1249_, 2);
lean_inc(v_second_1252_);
lean_dec_ref(v___y_1249_);
v___x_1253_ = lean_string_append(v___y_1248_, v___y_1251_);
v___x_1254_ = l_Int_repr(v_second_1252_);
lean_dec(v_second_1252_);
v___x_1255_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___y_1250_, v___y_1247_, v___x_1254_);
v___x_1256_ = lean_string_append(v___x_1253_, v___x_1255_);
lean_dec_ref(v___x_1255_);
return v___x_1256_;
}
v___jp_1257_:
{
if (v_colon_1244_ == 0)
{
lean_object* v___x_1262_; 
v___x_1262_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___y_1247_ = v___y_1259_;
v___y_1248_ = v___y_1258_;
v___y_1249_ = v___y_1260_;
v___y_1250_ = v___y_1261_;
v___y_1251_ = v___x_1262_;
goto v___jp_1246_;
}
else
{
lean_object* v___x_1263_; 
v___x_1263_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___y_1247_ = v___y_1259_;
v___y_1248_ = v___y_1258_;
v___y_1249_ = v___y_1260_;
v___y_1250_ = v___y_1261_;
v___y_1251_ = v___x_1263_;
goto v___jp_1246_;
}
}
v___jp_1264_:
{
if (v___y_1269_ == 0)
{
lean_dec_ref(v___y_1267_);
return v___y_1266_;
}
else
{
v___y_1258_ = v___y_1266_;
v___y_1259_ = v___y_1265_;
v___y_1260_ = v___y_1267_;
v___y_1261_ = v___y_1268_;
goto v___jp_1257_;
}
}
v___jp_1270_:
{
uint8_t v___x_1276_; 
v___x_1276_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withSeconds_1243_, v___y_1274_);
if (v___x_1276_ == 0)
{
uint8_t v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = 2;
v___x_1278_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withSeconds_1243_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_dec_ref(v___y_1272_);
return v___y_1275_;
}
else
{
lean_object* v_second_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v_second_1279_ = lean_ctor_get(v___y_1272_, 2);
v___x_1280_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1281_ = lean_int_dec_eq(v_second_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
v___y_1265_ = v___y_1271_;
v___y_1266_ = v___y_1275_;
v___y_1267_ = v___y_1272_;
v___y_1268_ = v___y_1273_;
v___y_1269_ = v___x_1278_;
goto v___jp_1264_;
}
else
{
v___y_1265_ = v___y_1271_;
v___y_1266_ = v___y_1275_;
v___y_1267_ = v___y_1272_;
v___y_1268_ = v___y_1273_;
v___y_1269_ = v___x_1276_;
goto v___jp_1264_;
}
}
}
else
{
v___y_1258_ = v___y_1275_;
v___y_1259_ = v___y_1271_;
v___y_1260_ = v___y_1272_;
v___y_1261_ = v___y_1273_;
goto v___jp_1257_;
}
}
v___jp_1282_:
{
lean_object* v_minute_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v_minute_1289_ = lean_ctor_get(v___y_1284_, 1);
v___x_1290_ = lean_string_append(v___y_1287_, v___y_1288_);
v___x_1291_ = l_Int_repr(v_minute_1289_);
v___x_1292_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___y_1285_, v___y_1283_, v___x_1291_);
v___x_1293_ = lean_string_append(v___x_1290_, v___x_1292_);
lean_dec_ref(v___x_1292_);
v___y_1271_ = v___y_1283_;
v___y_1272_ = v___y_1284_;
v___y_1273_ = v___y_1285_;
v___y_1274_ = v___y_1286_;
v___y_1275_ = v___x_1293_;
goto v___jp_1270_;
}
v___jp_1294_:
{
if (v_colon_1244_ == 0)
{
lean_object* v___x_1300_; 
v___x_1300_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___y_1283_ = v___y_1295_;
v___y_1284_ = v___y_1296_;
v___y_1285_ = v___y_1297_;
v___y_1286_ = v___y_1298_;
v___y_1287_ = v___y_1299_;
v___y_1288_ = v___x_1300_;
goto v___jp_1282_;
}
else
{
lean_object* v___x_1301_; 
v___x_1301_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___y_1283_ = v___y_1295_;
v___y_1284_ = v___y_1296_;
v___y_1285_ = v___y_1297_;
v___y_1286_ = v___y_1298_;
v___y_1287_ = v___y_1299_;
v___y_1288_ = v___x_1301_;
goto v___jp_1282_;
}
}
v___jp_1302_:
{
if (v___y_1308_ == 0)
{
v___y_1271_ = v___y_1303_;
v___y_1272_ = v___y_1304_;
v___y_1273_ = v___y_1305_;
v___y_1274_ = v___y_1306_;
v___y_1275_ = v___y_1307_;
goto v___jp_1270_;
}
else
{
v___y_1295_ = v___y_1303_;
v___y_1296_ = v___y_1304_;
v___y_1297_ = v___y_1305_;
v___y_1298_ = v___y_1306_;
v___y_1299_ = v___y_1307_;
goto v___jp_1294_;
}
}
v___jp_1309_:
{
lean_object* v_data_1315_; uint8_t v___x_1316_; uint8_t v___x_1317_; 
lean_inc_ref(v___y_1310_);
v_data_1315_ = lean_string_append(v___y_1310_, v___y_1314_);
lean_dec_ref(v___y_1314_);
v___x_1316_ = 0;
v___x_1317_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withMinutes_1242_, v___x_1316_);
if (v___x_1317_ == 0)
{
uint8_t v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = 2;
v___x_1319_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withMinutes_1242_, v___x_1318_);
if (v___x_1319_ == 0)
{
v___y_1271_ = v___y_1311_;
v___y_1272_ = v___y_1312_;
v___y_1273_ = v___y_1313_;
v___y_1274_ = v___x_1316_;
v___y_1275_ = v_data_1315_;
goto v___jp_1270_;
}
else
{
lean_object* v_minute_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v_minute_1320_ = lean_ctor_get(v___y_1312_, 1);
v___x_1321_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1322_ = lean_int_dec_eq(v_minute_1320_, v___x_1321_);
if (v___x_1322_ == 0)
{
v___y_1303_ = v___y_1311_;
v___y_1304_ = v___y_1312_;
v___y_1305_ = v___y_1313_;
v___y_1306_ = v___x_1316_;
v___y_1307_ = v_data_1315_;
v___y_1308_ = v___x_1319_;
goto v___jp_1302_;
}
else
{
v___y_1303_ = v___y_1311_;
v___y_1304_ = v___y_1312_;
v___y_1305_ = v___y_1313_;
v___y_1306_ = v___x_1316_;
v___y_1307_ = v_data_1315_;
v___y_1308_ = v___x_1317_;
goto v___jp_1302_;
}
}
}
else
{
v___y_1295_ = v___y_1311_;
v___y_1296_ = v___y_1312_;
v___y_1297_ = v___y_1313_;
v___y_1298_ = v___x_1316_;
v___y_1299_ = v_data_1315_;
goto v___jp_1294_;
}
}
v___jp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v_time_1328_; lean_object* v___x_1329_; uint32_t v___x_1330_; 
v___x_1326_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_1327_ = lean_int_mul(v_snd_1325_, v___x_1326_);
lean_dec(v_snd_1325_);
v_time_1328_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1327_);
lean_dec(v___x_1327_);
v___x_1329_ = lean_unsigned_to_nat(2u);
v___x_1330_ = 48;
if (v_padHour_1245_ == 0)
{
lean_object* v_hour_1331_; lean_object* v___x_1332_; 
v_hour_1331_ = lean_ctor_get(v_time_1328_, 0);
lean_inc(v_hour_1331_);
v___x_1332_ = l_Int_repr(v_hour_1331_);
lean_dec(v_hour_1331_);
v___y_1310_ = v_fst_1324_;
v___y_1311_ = v___x_1330_;
v___y_1312_ = v_time_1328_;
v___y_1313_ = v___x_1329_;
v___y_1314_ = v___x_1332_;
goto v___jp_1309_;
}
else
{
lean_object* v_hour_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v_hour_1333_ = lean_ctor_get(v_time_1328_, 0);
lean_inc(v_hour_1333_);
v___x_1334_ = l_Int_repr(v_hour_1333_);
lean_dec(v_hour_1333_);
v___x_1335_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1329_, v___x_1330_, v___x_1334_);
v___y_1310_ = v_fst_1324_;
v___y_1311_ = v___x_1330_;
v___y_1312_ = v_time_1328_;
v___y_1313_ = v___x_1329_;
v___y_1314_ = v___x_1335_;
goto v___jp_1309_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___boxed(lean_object* v_offset_1341_, lean_object* v_withMinutes_1342_, lean_object* v_withSeconds_1343_, lean_object* v_colon_1344_, lean_object* v_padHour_1345_){
_start:
{
uint8_t v_withMinutes_boxed_1346_; uint8_t v_withSeconds_boxed_1347_; uint8_t v_colon_boxed_1348_; uint8_t v_padHour_boxed_1349_; lean_object* v_res_1350_; 
v_withMinutes_boxed_1346_ = lean_unbox(v_withMinutes_1342_);
v_withSeconds_boxed_1347_ = lean_unbox(v_withSeconds_1343_);
v_colon_boxed_1348_ = lean_unbox(v_colon_1344_);
v_padHour_boxed_1349_ = lean_unbox(v_padHour_1345_);
v_res_1350_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1341_, v_withMinutes_boxed_1346_, v_withSeconds_boxed_1347_, v_colon_boxed_1348_, v_padHour_boxed_1349_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0_spec__0(lean_object* v_a_1351_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_nat_to_int(v_a_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(lean_object* v_a_1353_){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_nat_to_int(v_a_1353_);
v___x_1355_ = l_Rat_ofInt(v___x_1354_);
return v___x_1355_;
}
}
static lean_object* _init_l_Std_Time_classifyDayPeriod___closed__0(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_unsigned_to_nat(12u);
v___x_1357_ = lean_nat_to_int(v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_classifyDayPeriod(lean_object* v_hour_1358_, lean_object* v_minute_1359_, lean_object* v_second_1360_){
_start:
{
lean_object* v___y_1362_; lean_object* v___x_1366_; uint8_t v___x_1373_; 
v___x_1366_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1373_ = lean_int_dec_eq(v_hour_1358_, v___x_1366_);
if (v___x_1373_ == 0)
{
goto v___jp_1367_;
}
else
{
uint8_t v___x_1374_; 
v___x_1374_ = lean_int_dec_eq(v_minute_1359_, v___x_1366_);
if (v___x_1374_ == 0)
{
goto v___jp_1367_;
}
else
{
uint8_t v___x_1375_; 
v___x_1375_ = lean_int_dec_eq(v_second_1360_, v___x_1366_);
if (v___x_1375_ == 0)
{
goto v___jp_1367_;
}
else
{
uint8_t v___x_1376_; 
v___x_1376_ = 3;
return v___x_1376_;
}
}
}
v___jp_1361_:
{
uint8_t v___x_1363_; 
v___x_1363_ = lean_int_dec_lt(v_hour_1358_, v___y_1362_);
if (v___x_1363_ == 0)
{
uint8_t v___x_1364_; 
v___x_1364_ = 1;
return v___x_1364_;
}
else
{
uint8_t v___x_1365_; 
v___x_1365_ = 0;
return v___x_1365_;
}
}
v___jp_1367_:
{
lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1368_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1369_ = lean_int_dec_eq(v_hour_1358_, v___x_1368_);
if (v___x_1369_ == 0)
{
v___y_1362_ = v___x_1368_;
goto v___jp_1361_;
}
else
{
uint8_t v___x_1370_; 
v___x_1370_ = lean_int_dec_eq(v_minute_1359_, v___x_1366_);
if (v___x_1370_ == 0)
{
v___y_1362_ = v___x_1368_;
goto v___jp_1361_;
}
else
{
uint8_t v___x_1371_; 
v___x_1371_ = lean_int_dec_eq(v_second_1360_, v___x_1366_);
if (v___x_1371_ == 0)
{
v___y_1362_ = v___x_1368_;
goto v___jp_1361_;
}
else
{
uint8_t v___x_1372_; 
v___x_1372_ = 2;
return v___x_1372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyDayPeriod___boxed(lean_object* v_hour_1377_, lean_object* v_minute_1378_, lean_object* v_second_1379_){
_start:
{
uint8_t v_res_1380_; lean_object* v_r_1381_; 
v_res_1380_ = l_Std_Time_classifyDayPeriod(v_hour_1377_, v_minute_1378_, v_second_1379_);
lean_dec(v_second_1379_);
lean_dec(v_minute_1378_);
lean_dec(v_hour_1377_);
v_r_1381_ = lean_box(v_res_1380_);
return v_r_1381_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__0(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_unsigned_to_nat(6u);
v___x_1383_ = lean_nat_to_int(v___x_1382_);
return v___x_1383_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__1(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_unsigned_to_nat(18u);
v___x_1385_ = lean_nat_to_int(v___x_1384_);
return v___x_1385_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__2(void){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_unsigned_to_nat(21u);
v___x_1387_ = lean_nat_to_int(v___x_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_classifyExtendedDayPeriod(lean_object* v_hour_1388_, lean_object* v_minute_1389_, lean_object* v_second_1390_){
_start:
{
lean_object* v___y_1392_; lean_object* v___x_1405_; uint8_t v___x_1412_; 
v___x_1405_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1412_ = lean_int_dec_eq(v_hour_1388_, v___x_1405_);
if (v___x_1412_ == 0)
{
goto v___jp_1406_;
}
else
{
uint8_t v___x_1413_; 
v___x_1413_ = lean_int_dec_eq(v_minute_1389_, v___x_1405_);
if (v___x_1413_ == 0)
{
goto v___jp_1406_;
}
else
{
uint8_t v___x_1414_; 
v___x_1414_ = lean_int_dec_eq(v_second_1390_, v___x_1405_);
if (v___x_1414_ == 0)
{
goto v___jp_1406_;
}
else
{
uint8_t v___x_1415_; 
v___x_1415_ = 0;
return v___x_1415_;
}
}
}
v___jp_1391_:
{
lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1393_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__0, &l_Std_Time_classifyExtendedDayPeriod___closed__0_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__0);
v___x_1394_ = lean_int_dec_lt(v_hour_1388_, v___x_1393_);
if (v___x_1394_ == 0)
{
uint8_t v___x_1395_; 
v___x_1395_ = lean_int_dec_lt(v_hour_1388_, v___y_1392_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1396_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__1, &l_Std_Time_classifyExtendedDayPeriod___closed__1_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__1);
v___x_1397_ = lean_int_dec_lt(v_hour_1388_, v___x_1396_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1398_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__2, &l_Std_Time_classifyExtendedDayPeriod___closed__2_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__2);
v___x_1399_ = lean_int_dec_lt(v_hour_1388_, v___x_1398_);
if (v___x_1399_ == 0)
{
uint8_t v___x_1400_; 
v___x_1400_ = 1;
return v___x_1400_;
}
else
{
uint8_t v___x_1401_; 
v___x_1401_ = 5;
return v___x_1401_;
}
}
else
{
uint8_t v___x_1402_; 
v___x_1402_ = 4;
return v___x_1402_;
}
}
else
{
uint8_t v___x_1403_; 
v___x_1403_ = 2;
return v___x_1403_;
}
}
else
{
uint8_t v___x_1404_; 
v___x_1404_ = 1;
return v___x_1404_;
}
}
v___jp_1406_:
{
lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1407_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1408_ = lean_int_dec_eq(v_hour_1388_, v___x_1407_);
if (v___x_1408_ == 0)
{
v___y_1392_ = v___x_1407_;
goto v___jp_1391_;
}
else
{
uint8_t v___x_1409_; 
v___x_1409_ = lean_int_dec_eq(v_minute_1389_, v___x_1405_);
if (v___x_1409_ == 0)
{
v___y_1392_ = v___x_1407_;
goto v___jp_1391_;
}
else
{
uint8_t v___x_1410_; 
v___x_1410_ = lean_int_dec_eq(v_second_1390_, v___x_1405_);
if (v___x_1410_ == 0)
{
v___y_1392_ = v___x_1407_;
goto v___jp_1391_;
}
else
{
uint8_t v___x_1411_; 
v___x_1411_ = 3;
return v___x_1411_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyExtendedDayPeriod___boxed(lean_object* v_hour_1416_, lean_object* v_minute_1417_, lean_object* v_second_1418_){
_start:
{
uint8_t v_res_1419_; lean_object* v_r_1420_; 
v_res_1419_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1416_, v_minute_1417_, v_second_1418_);
lean_dec(v_second_1418_);
lean_dec(v_minute_1417_);
lean_dec(v_hour_1416_);
v_r_1420_ = lean_box(v_res_1419_);
return v_r_1420_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0(void){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = lean_unsigned_to_nat(100u);
v___x_1422_ = lean_nat_to_int(v___x_1421_);
return v___x_1422_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = lean_unsigned_to_nat(7u);
v___x_1424_ = lean_nat_to_int(v___x_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(lean_object* v_dateformat_1428_, lean_object* v_modifier_1429_, lean_object* v_data_1430_){
_start:
{
switch(lean_obj_tag(v_modifier_1429_))
{
case 0:
{
uint8_t v_presentation_1431_; 
v_presentation_1431_ = lean_ctor_get_uint8(v_modifier_1429_, 0);
lean_dec_ref_known(v_modifier_1429_, 0);
switch(v_presentation_1431_)
{
case 1:
{
lean_object* v_symbols_1432_; uint8_t v___x_1433_; lean_object* v___x_1434_; 
v_symbols_1432_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1433_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1434_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(v_symbols_1432_, v___x_1433_);
return v___x_1434_;
}
case 2:
{
lean_object* v_symbols_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; 
v_symbols_1435_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1436_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1437_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(v_symbols_1435_, v___x_1436_);
return v___x_1437_;
}
default: 
{
lean_object* v_symbols_1438_; uint8_t v___x_1439_; lean_object* v___x_1440_; 
v_symbols_1438_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1439_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1440_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(v_symbols_1438_, v___x_1439_);
return v___x_1440_;
}
}
}
case 1:
{
lean_object* v_presentation_1441_; 
v_presentation_1441_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc(v_presentation_1441_);
lean_dec_ref_known(v_modifier_1429_, 1);
switch(lean_obj_tag(v_presentation_1441_))
{
case 0:
{
lean_object* v___x_1442_; uint8_t v___x_1443_; lean_object* v___x_1444_; 
v___x_1442_ = lean_unsigned_to_nat(0u);
v___x_1443_ = 0;
v___x_1444_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1442_, v_data_1430_, v___x_1443_);
return v___x_1444_;
}
case 1:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; lean_object* v___x_1449_; 
v___x_1445_ = lean_unsigned_to_nat(2u);
v___x_1446_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1447_ = lean_int_emod(v_data_1430_, v___x_1446_);
lean_dec(v_data_1430_);
v___x_1448_ = 0;
v___x_1449_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1445_, v___x_1447_, v___x_1448_);
return v___x_1449_;
}
case 2:
{
lean_object* v___x_1450_; uint8_t v___x_1451_; lean_object* v___x_1452_; 
v___x_1450_ = lean_unsigned_to_nat(4u);
v___x_1451_ = 0;
v___x_1452_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1450_, v_data_1430_, v___x_1451_);
return v___x_1452_;
}
default: 
{
lean_object* v_num_1453_; uint8_t v___x_1454_; lean_object* v___x_1455_; 
v_num_1453_ = lean_ctor_get(v_presentation_1441_, 0);
lean_inc(v_num_1453_);
lean_dec_ref_known(v_presentation_1441_, 1);
v___x_1454_ = 0;
v___x_1455_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1453_, v_data_1430_, v___x_1454_);
lean_dec(v_num_1453_);
return v___x_1455_;
}
}
}
case 2:
{
lean_object* v_presentation_1456_; lean_object* v___x_1457_; lean_object* v___y_1459_; lean_object* v___x_1473_; uint8_t v___x_1474_; 
v_presentation_1456_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc(v_presentation_1456_);
lean_dec_ref_known(v_modifier_1429_, 1);
v___x_1457_ = lean_unsigned_to_nat(0u);
v___x_1473_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1474_ = lean_int_dec_le(v_data_1430_, v___x_1473_);
if (v___x_1474_ == 0)
{
v___y_1459_ = v_data_1430_;
goto v___jp_1458_;
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1475_ = lean_int_neg(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1476_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1477_ = lean_int_add(v___x_1475_, v___x_1476_);
lean_dec(v___x_1475_);
v___y_1459_ = v___x_1477_;
goto v___jp_1458_;
}
v___jp_1458_:
{
switch(lean_obj_tag(v_presentation_1456_))
{
case 0:
{
uint8_t v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = 0;
v___x_1461_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1457_, v___y_1459_, v___x_1460_);
return v___x_1461_;
}
case 1:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; lean_object* v___x_1466_; 
v___x_1462_ = lean_unsigned_to_nat(2u);
v___x_1463_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1464_ = lean_int_emod(v___y_1459_, v___x_1463_);
lean_dec(v___y_1459_);
v___x_1465_ = 0;
v___x_1466_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1462_, v___x_1464_, v___x_1465_);
return v___x_1466_;
}
case 2:
{
lean_object* v___x_1467_; uint8_t v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = lean_unsigned_to_nat(4u);
v___x_1468_ = 0;
v___x_1469_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1467_, v___y_1459_, v___x_1468_);
return v___x_1469_;
}
default: 
{
lean_object* v_num_1470_; uint8_t v___x_1471_; lean_object* v___x_1472_; 
v_num_1470_ = lean_ctor_get(v_presentation_1456_, 0);
lean_inc(v_num_1470_);
lean_dec_ref_known(v_presentation_1456_, 1);
v___x_1471_ = 0;
v___x_1472_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1470_, v___y_1459_, v___x_1471_);
lean_dec(v_num_1470_);
return v___x_1472_;
}
}
}
}
case 3:
{
lean_object* v_presentation_1478_; lean_object* v_snd_1479_; uint8_t v___x_1480_; lean_object* v___x_1481_; 
v_presentation_1478_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc(v_presentation_1478_);
lean_dec_ref_known(v_modifier_1429_, 1);
v_snd_1479_ = lean_ctor_get(v_data_1430_, 1);
lean_inc(v_snd_1479_);
lean_dec(v_data_1430_);
v___x_1480_ = 0;
v___x_1481_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1478_, v_snd_1479_, v___x_1480_);
lean_dec(v_presentation_1478_);
return v___x_1481_;
}
case 4:
{
lean_object* v_presentation_1482_; 
v_presentation_1482_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc_ref(v_presentation_1482_);
lean_dec_ref_known(v_modifier_1429_, 1);
if (lean_obj_tag(v_presentation_1482_) == 0)
{
lean_object* v_val_1483_; uint8_t v___x_1484_; lean_object* v___x_1485_; 
v_val_1483_ = lean_ctor_get(v_presentation_1482_, 0);
lean_inc(v_val_1483_);
lean_dec_ref_known(v_presentation_1482_, 1);
v___x_1484_ = 0;
v___x_1485_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1483_, v_data_1430_, v___x_1484_);
lean_dec(v_val_1483_);
return v___x_1485_;
}
else
{
lean_object* v_val_1486_; uint8_t v___x_1487_; 
v_val_1486_ = lean_ctor_get(v_presentation_1482_, 0);
lean_inc(v_val_1486_);
lean_dec_ref_known(v_presentation_1482_, 1);
v___x_1487_ = lean_unbox(v_val_1486_);
lean_dec(v_val_1486_);
switch(v___x_1487_)
{
case 1:
{
lean_object* v_symbols_1488_; lean_object* v___x_1489_; 
v_symbols_1488_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1489_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_1488_, v_data_1430_);
lean_dec(v_data_1430_);
return v___x_1489_;
}
case 2:
{
lean_object* v_symbols_1490_; lean_object* v___x_1491_; 
v_symbols_1490_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1491_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_1490_, v_data_1430_);
lean_dec(v_data_1430_);
return v___x_1491_;
}
default: 
{
lean_object* v_symbols_1492_; lean_object* v___x_1493_; 
v_symbols_1492_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1493_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_1492_, v_data_1430_);
lean_dec(v_data_1430_);
return v___x_1493_;
}
}
}
}
case 5:
{
lean_object* v_presentation_1494_; 
v_presentation_1494_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc_ref(v_presentation_1494_);
lean_dec_ref_known(v_modifier_1429_, 1);
if (lean_obj_tag(v_presentation_1494_) == 0)
{
lean_object* v_val_1495_; uint8_t v___x_1496_; lean_object* v___x_1497_; 
v_val_1495_ = lean_ctor_get(v_presentation_1494_, 0);
lean_inc(v_val_1495_);
lean_dec_ref_known(v_presentation_1494_, 1);
v___x_1496_ = 0;
v___x_1497_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1495_, v_data_1430_, v___x_1496_);
lean_dec(v_val_1495_);
return v___x_1497_;
}
else
{
lean_object* v_val_1498_; uint8_t v___x_1499_; 
v_val_1498_ = lean_ctor_get(v_presentation_1494_, 0);
lean_inc(v_val_1498_);
lean_dec_ref_known(v_presentation_1494_, 1);
v___x_1499_ = lean_unbox(v_val_1498_);
lean_dec(v_val_1498_);
switch(v___x_1499_)
{
case 1:
{
lean_object* v_symbols_1500_; lean_object* v___x_1501_; 
v_symbols_1500_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1501_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_1500_, v_data_1430_);
lean_dec(v_data_1430_);
return v___x_1501_;
}
case 2:
{
lean_object* v_symbols_1502_; lean_object* v___x_1503_; 
v_symbols_1502_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1503_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_1502_, v_data_1430_);
lean_dec(v_data_1430_);
return v___x_1503_;
}
default: 
{
lean_object* v_symbols_1504_; lean_object* v___x_1505_; 
v_symbols_1504_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1505_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_1504_, v_data_1430_);
lean_dec(v_data_1430_);
return v___x_1505_;
}
}
}
}
case 6:
{
lean_object* v_presentation_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; 
v_presentation_1506_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc(v_presentation_1506_);
lean_dec_ref_known(v_modifier_1429_, 1);
v___x_1507_ = 0;
v___x_1508_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1506_, v_data_1430_, v___x_1507_);
lean_dec(v_presentation_1506_);
return v___x_1508_;
}
case 7:
{
lean_object* v_presentation_1509_; 
v_presentation_1509_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc_ref(v_presentation_1509_);
lean_dec_ref_known(v_modifier_1429_, 1);
if (lean_obj_tag(v_presentation_1509_) == 0)
{
lean_object* v_val_1510_; uint8_t v___x_1511_; lean_object* v___x_1512_; 
v_val_1510_ = lean_ctor_get(v_presentation_1509_, 0);
lean_inc(v_val_1510_);
lean_dec_ref_known(v_presentation_1509_, 1);
v___x_1511_ = 0;
v___x_1512_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1510_, v_data_1430_, v___x_1511_);
lean_dec(v_val_1510_);
return v___x_1512_;
}
else
{
lean_object* v_val_1513_; uint8_t v___x_1514_; 
v_val_1513_ = lean_ctor_get(v_presentation_1509_, 0);
lean_inc(v_val_1513_);
lean_dec_ref_known(v_presentation_1509_, 1);
v___x_1514_ = lean_unbox(v_val_1513_);
lean_dec(v_val_1513_);
switch(v___x_1514_)
{
case 0:
{
lean_object* v_symbols_1515_; lean_object* v___x_1516_; 
v_symbols_1515_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1516_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1515_, v_data_1430_);
lean_dec(v_data_1430_);
return v___x_1516_;
}
case 1:
{
lean_object* v_symbols_1517_; lean_object* v___x_1518_; 
v_symbols_1517_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1518_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1517_, v_data_1430_);
lean_dec(v_data_1430_);
return v___x_1518_;
}
case 2:
{
lean_object* v_symbols_1519_; lean_object* v___x_1520_; 
v_symbols_1519_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1520_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1519_, v_data_1430_);
lean_dec(v_data_1430_);
return v___x_1520_;
}
default: 
{
lean_object* v___x_1521_; 
v___x_1521_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_data_1430_);
lean_dec(v_data_1430_);
return v___x_1521_;
}
}
}
}
case 8:
{
lean_object* v_presentation_1522_; 
v_presentation_1522_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc_ref(v_presentation_1522_);
lean_dec_ref_known(v_modifier_1429_, 1);
if (lean_obj_tag(v_presentation_1522_) == 0)
{
lean_object* v_val_1523_; uint8_t v___x_1524_; lean_object* v___x_1525_; 
v_val_1523_ = lean_ctor_get(v_presentation_1522_, 0);
lean_inc(v_val_1523_);
lean_dec_ref_known(v_presentation_1522_, 1);
v___x_1524_ = 0;
v___x_1525_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1523_, v_data_1430_, v___x_1524_);
lean_dec(v_val_1523_);
return v___x_1525_;
}
else
{
lean_object* v_val_1526_; uint8_t v___x_1527_; 
v_val_1526_ = lean_ctor_get(v_presentation_1522_, 0);
lean_inc(v_val_1526_);
lean_dec_ref_known(v_presentation_1522_, 1);
v___x_1527_ = lean_unbox(v_val_1526_);
lean_dec(v_val_1526_);
switch(v___x_1527_)
{
case 0:
{
lean_object* v_symbols_1528_; lean_object* v___x_1529_; 
v_symbols_1528_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1529_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1528_, v_data_1430_);
lean_dec(v_data_1430_);
return v___x_1529_;
}
case 1:
{
lean_object* v_symbols_1530_; lean_object* v___x_1531_; 
v_symbols_1530_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1531_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1530_, v_data_1430_);
lean_dec(v_data_1430_);
return v___x_1531_;
}
case 2:
{
lean_object* v_symbols_1532_; lean_object* v___x_1533_; 
v_symbols_1532_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1533_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1532_, v_data_1430_);
lean_dec(v_data_1430_);
return v___x_1533_;
}
default: 
{
lean_object* v___x_1534_; 
v___x_1534_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_data_1430_);
lean_dec(v_data_1430_);
return v___x_1534_;
}
}
}
}
case 9:
{
lean_object* v_presentation_1535_; lean_object* v___x_1536_; lean_object* v___y_1538_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v_presentation_1535_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc(v_presentation_1535_);
lean_dec_ref_known(v_modifier_1429_, 1);
v___x_1536_ = lean_unsigned_to_nat(0u);
v___x_1552_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1553_ = lean_int_dec_le(v_data_1430_, v___x_1552_);
if (v___x_1553_ == 0)
{
v___y_1538_ = v_data_1430_;
goto v___jp_1537_;
}
else
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = lean_int_neg(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1555_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1556_ = lean_int_add(v___x_1554_, v___x_1555_);
lean_dec(v___x_1554_);
v___y_1538_ = v___x_1556_;
goto v___jp_1537_;
}
v___jp_1537_:
{
switch(lean_obj_tag(v_presentation_1535_))
{
case 0:
{
uint8_t v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = 0;
v___x_1540_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1536_, v___y_1538_, v___x_1539_);
return v___x_1540_;
}
case 1:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; lean_object* v___x_1545_; 
v___x_1541_ = lean_unsigned_to_nat(2u);
v___x_1542_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1543_ = lean_int_emod(v___y_1538_, v___x_1542_);
lean_dec(v___y_1538_);
v___x_1544_ = 0;
v___x_1545_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1541_, v___x_1543_, v___x_1544_);
return v___x_1545_;
}
case 2:
{
lean_object* v___x_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; 
v___x_1546_ = lean_unsigned_to_nat(4u);
v___x_1547_ = 0;
v___x_1548_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1546_, v___y_1538_, v___x_1547_);
return v___x_1548_;
}
default: 
{
lean_object* v_num_1549_; uint8_t v___x_1550_; lean_object* v___x_1551_; 
v_num_1549_ = lean_ctor_get(v_presentation_1535_, 0);
lean_inc(v_num_1549_);
lean_dec_ref_known(v_presentation_1535_, 1);
v___x_1550_ = 0;
v___x_1551_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1549_, v___y_1538_, v___x_1550_);
lean_dec(v_num_1549_);
return v___x_1551_;
}
}
}
}
case 10:
{
lean_object* v_presentation_1557_; uint8_t v___x_1558_; lean_object* v___x_1559_; 
v_presentation_1557_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc(v_presentation_1557_);
lean_dec_ref_known(v_modifier_1429_, 1);
v___x_1558_ = 0;
v___x_1559_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1557_, v_data_1430_, v___x_1558_);
lean_dec(v_presentation_1557_);
return v___x_1559_;
}
case 11:
{
lean_object* v_presentation_1560_; uint8_t v___x_1561_; lean_object* v___x_1562_; 
v_presentation_1560_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc(v_presentation_1560_);
lean_dec_ref_known(v_modifier_1429_, 1);
v___x_1561_ = 0;
v___x_1562_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1560_, v_data_1430_, v___x_1561_);
lean_dec(v_presentation_1560_);
return v___x_1562_;
}
case 12:
{
uint8_t v_presentation_1563_; 
v_presentation_1563_ = lean_ctor_get_uint8(v_modifier_1429_, 0);
lean_dec_ref_known(v_modifier_1429_, 0);
switch(v_presentation_1563_)
{
case 0:
{
lean_object* v_symbols_1564_; uint8_t v___x_1565_; lean_object* v___x_1566_; 
v_symbols_1564_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1565_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1566_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1564_, v___x_1565_);
return v___x_1566_;
}
case 1:
{
lean_object* v_symbols_1567_; uint8_t v___x_1568_; lean_object* v___x_1569_; 
v_symbols_1567_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1568_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1569_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1567_, v___x_1568_);
return v___x_1569_;
}
case 2:
{
lean_object* v_symbols_1570_; uint8_t v___x_1571_; lean_object* v___x_1572_; 
v_symbols_1570_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1571_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1572_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1570_, v___x_1571_);
return v___x_1572_;
}
default: 
{
lean_object* v_symbols_1573_; uint8_t v___x_1574_; lean_object* v___x_1575_; 
v_symbols_1573_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1574_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1575_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1573_, v___x_1574_);
return v___x_1575_;
}
}
}
case 13:
{
lean_object* v_presentation_1576_; 
v_presentation_1576_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc_ref(v_presentation_1576_);
lean_dec_ref_known(v_modifier_1429_, 1);
if (lean_obj_tag(v_presentation_1576_) == 0)
{
lean_object* v_val_1577_; uint8_t v_firstDayOfWeek_1578_; lean_object* v_firstOrd_1579_; uint8_t v___x_1580_; lean_object* v_dayOrd_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; lean_object* v___x_1589_; 
v_val_1577_ = lean_ctor_get(v_presentation_1576_, 0);
lean_inc(v_val_1577_);
lean_dec_ref_known(v_presentation_1576_, 1);
v_firstDayOfWeek_1578_ = lean_ctor_get_uint8(v_dateformat_1428_, sizeof(void*)*2);
v_firstOrd_1579_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_1578_);
v___x_1580_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v_dayOrd_1581_ = l_Std_Time_Weekday_toOrdinal(v___x_1580_);
v___x_1582_ = lean_int_sub(v_dayOrd_1581_, v_firstOrd_1579_);
lean_dec(v_firstOrd_1579_);
lean_dec(v_dayOrd_1581_);
v___x_1583_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_1584_ = lean_int_add(v___x_1582_, v___x_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_int_emod(v___x_1584_, v___x_1583_);
lean_dec(v___x_1584_);
v___x_1586_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1587_ = lean_int_add(v___x_1585_, v___x_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = 0;
v___x_1589_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1577_, v___x_1587_, v___x_1588_);
lean_dec(v_val_1577_);
return v___x_1589_;
}
else
{
lean_object* v_val_1590_; uint8_t v___x_1591_; 
v_val_1590_ = lean_ctor_get(v_presentation_1576_, 0);
lean_inc(v_val_1590_);
lean_dec_ref_known(v_presentation_1576_, 1);
v___x_1591_ = lean_unbox(v_val_1590_);
lean_dec(v_val_1590_);
switch(v___x_1591_)
{
case 0:
{
lean_object* v_symbols_1592_; uint8_t v___x_1593_; lean_object* v___x_1594_; 
v_symbols_1592_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1593_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1594_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1592_, v___x_1593_);
return v___x_1594_;
}
case 1:
{
lean_object* v_symbols_1595_; uint8_t v___x_1596_; lean_object* v___x_1597_; 
v_symbols_1595_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1596_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1597_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1595_, v___x_1596_);
return v___x_1597_;
}
case 2:
{
lean_object* v_symbols_1598_; uint8_t v___x_1599_; lean_object* v___x_1600_; 
v_symbols_1598_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1599_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1600_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1598_, v___x_1599_);
return v___x_1600_;
}
default: 
{
lean_object* v_symbols_1601_; uint8_t v___x_1602_; lean_object* v___x_1603_; 
v_symbols_1601_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1602_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1603_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1601_, v___x_1602_);
return v___x_1603_;
}
}
}
}
case 14:
{
lean_object* v_presentation_1604_; 
v_presentation_1604_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc_ref(v_presentation_1604_);
lean_dec_ref_known(v_modifier_1429_, 1);
if (lean_obj_tag(v_presentation_1604_) == 0)
{
lean_object* v_val_1605_; uint8_t v_firstDayOfWeek_1606_; lean_object* v_firstOrd_1607_; uint8_t v___x_1608_; lean_object* v_dayOrd_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; lean_object* v___x_1617_; 
v_val_1605_ = lean_ctor_get(v_presentation_1604_, 0);
lean_inc(v_val_1605_);
lean_dec_ref_known(v_presentation_1604_, 1);
v_firstDayOfWeek_1606_ = lean_ctor_get_uint8(v_dateformat_1428_, sizeof(void*)*2);
v_firstOrd_1607_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_1606_);
v___x_1608_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v_dayOrd_1609_ = l_Std_Time_Weekday_toOrdinal(v___x_1608_);
v___x_1610_ = lean_int_sub(v_dayOrd_1609_, v_firstOrd_1607_);
lean_dec(v_firstOrd_1607_);
lean_dec(v_dayOrd_1609_);
v___x_1611_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_1612_ = lean_int_add(v___x_1610_, v___x_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_int_emod(v___x_1612_, v___x_1611_);
lean_dec(v___x_1612_);
v___x_1614_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1615_ = lean_int_add(v___x_1613_, v___x_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = 0;
v___x_1617_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1605_, v___x_1615_, v___x_1616_);
lean_dec(v_val_1605_);
return v___x_1617_;
}
else
{
lean_object* v_val_1618_; uint8_t v___x_1619_; 
v_val_1618_ = lean_ctor_get(v_presentation_1604_, 0);
lean_inc(v_val_1618_);
lean_dec_ref_known(v_presentation_1604_, 1);
v___x_1619_ = lean_unbox(v_val_1618_);
lean_dec(v_val_1618_);
switch(v___x_1619_)
{
case 0:
{
lean_object* v_symbols_1620_; uint8_t v___x_1621_; lean_object* v___x_1622_; 
v_symbols_1620_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1621_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1622_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1620_, v___x_1621_);
return v___x_1622_;
}
case 1:
{
lean_object* v_symbols_1623_; uint8_t v___x_1624_; lean_object* v___x_1625_; 
v_symbols_1623_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1624_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1625_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1623_, v___x_1624_);
return v___x_1625_;
}
case 2:
{
lean_object* v_symbols_1626_; uint8_t v___x_1627_; lean_object* v___x_1628_; 
v_symbols_1626_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1627_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1628_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1626_, v___x_1627_);
return v___x_1628_;
}
default: 
{
lean_object* v_symbols_1629_; uint8_t v___x_1630_; lean_object* v___x_1631_; 
v_symbols_1629_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1630_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1631_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1629_, v___x_1630_);
return v___x_1631_;
}
}
}
}
case 15:
{
lean_object* v_presentation_1632_; uint8_t v___x_1633_; lean_object* v___x_1634_; 
v_presentation_1632_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc(v_presentation_1632_);
lean_dec_ref_known(v_modifier_1429_, 1);
v___x_1633_ = 0;
v___x_1634_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1632_, v_data_1430_, v___x_1633_);
lean_dec(v_presentation_1632_);
return v___x_1634_;
}
case 16:
{
uint8_t v_presentation_1635_; 
v_presentation_1635_ = lean_ctor_get_uint8(v_modifier_1429_, 0);
lean_dec_ref_known(v_modifier_1429_, 0);
if (v_presentation_1635_ == 2)
{
lean_object* v_symbols_1636_; uint8_t v___x_1637_; lean_object* v___x_1638_; 
v_symbols_1636_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1637_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1638_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(v_symbols_1636_, v___x_1637_);
return v___x_1638_;
}
else
{
lean_object* v_symbols_1639_; uint8_t v___x_1640_; lean_object* v___x_1641_; 
v_symbols_1639_ = lean_ctor_get(v_dateformat_1428_, 1);
v___x_1640_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1641_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(v_symbols_1639_, v___x_1640_);
return v___x_1641_;
}
}
case 17:
{
uint8_t v_presentation_1642_; 
v_presentation_1642_ = lean_ctor_get_uint8(v_modifier_1429_, 0);
lean_dec_ref_known(v_modifier_1429_, 0);
switch(v_presentation_1642_)
{
case 1:
{
lean_object* v_symbols_1643_; lean_object* v_dayPeriodLong_1644_; uint8_t v___x_1645_; lean_object* v___x_1646_; 
v_symbols_1643_ = lean_ctor_get(v_dateformat_1428_, 1);
v_dayPeriodLong_1644_ = lean_ctor_get(v_symbols_1643_, 20);
v___x_1645_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1646_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodLong_1644_, v___x_1645_);
return v___x_1646_;
}
case 2:
{
lean_object* v_symbols_1647_; lean_object* v_dayPeriodNarrow_1648_; uint8_t v___x_1649_; lean_object* v___x_1650_; 
v_symbols_1647_ = lean_ctor_get(v_dateformat_1428_, 1);
v_dayPeriodNarrow_1648_ = lean_ctor_get(v_symbols_1647_, 21);
v___x_1649_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1650_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodNarrow_1648_, v___x_1649_);
return v___x_1650_;
}
default: 
{
lean_object* v_symbols_1651_; lean_object* v_dayPeriodShort_1652_; uint8_t v___x_1653_; lean_object* v___x_1654_; 
v_symbols_1651_ = lean_ctor_get(v_dateformat_1428_, 1);
v_dayPeriodShort_1652_ = lean_ctor_get(v_symbols_1651_, 19);
v___x_1653_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1654_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodShort_1652_, v___x_1653_);
return v___x_1654_;
}
}
}
case 18:
{
uint8_t v_presentation_1655_; 
v_presentation_1655_ = lean_ctor_get_uint8(v_modifier_1429_, 0);
lean_dec_ref_known(v_modifier_1429_, 0);
switch(v_presentation_1655_)
{
case 1:
{
lean_object* v_symbols_1656_; lean_object* v_extendedDayPeriodLong_1657_; uint8_t v___x_1658_; lean_object* v___x_1659_; 
v_symbols_1656_ = lean_ctor_get(v_dateformat_1428_, 1);
v_extendedDayPeriodLong_1657_ = lean_ctor_get(v_symbols_1656_, 23);
v___x_1658_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1659_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodLong_1657_, v___x_1658_);
return v___x_1659_;
}
case 2:
{
lean_object* v_symbols_1660_; lean_object* v_extendedDayPeriodNarrow_1661_; uint8_t v___x_1662_; lean_object* v___x_1663_; 
v_symbols_1660_ = lean_ctor_get(v_dateformat_1428_, 1);
v_extendedDayPeriodNarrow_1661_ = lean_ctor_get(v_symbols_1660_, 24);
v___x_1662_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1663_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodNarrow_1661_, v___x_1662_);
return v___x_1663_;
}
default: 
{
lean_object* v_symbols_1664_; lean_object* v_extendedDayPeriodShort_1665_; uint8_t v___x_1666_; lean_object* v___x_1667_; 
v_symbols_1664_ = lean_ctor_get(v_dateformat_1428_, 1);
v_extendedDayPeriodShort_1665_ = lean_ctor_get(v_symbols_1664_, 22);
v___x_1666_ = lean_unbox(v_data_1430_);
lean_dec(v_data_1430_);
v___x_1667_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodShort_1665_, v___x_1666_);
return v___x_1667_;
}
}
}
case 19:
{
lean_object* v_presentation_1668_; uint8_t v___x_1669_; lean_object* v___x_1670_; 
v_presentation_1668_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc(v_presentation_1668_);
lean_dec_ref_known(v_modifier_1429_, 1);
v___x_1669_ = 0;
v___x_1670_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1668_, v_data_1430_, v___x_1669_);
lean_dec(v_presentation_1668_);
return v___x_1670_;
}
case 20:
{
lean_object* v_presentation_1671_; uint8_t v___x_1672_; lean_object* v___x_1673_; 
v_presentation_1671_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc(v_presentation_1671_);
lean_dec_ref_known(v_modifier_1429_, 1);
v___x_1672_ = 0;
v___x_1673_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1671_, v_data_1430_, v___x_1672_);
lean_dec(v_presentation_1671_);
return v___x_1673_;
}
case 21:
{
lean_object* v_presentation_1674_; uint8_t v___x_1675_; lean_object* v___x_1676_; 
v_presentation_1674_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc(v_presentation_1674_);
lean_dec_ref_known(v_modifier_1429_, 1);
v___x_1675_ = 0;
v___x_1676_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1674_, v_data_1430_, v___x_1675_);
lean_dec(v_presentation_1674_);
return v___x_1676_;
}
case 22:
{
lean_object* v_presentation_1677_; uint8_t v___x_1678_; lean_object* v___x_1679_; 
v_presentation_1677_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc(v_presentation_1677_);
lean_dec_ref_known(v_modifier_1429_, 1);
v___x_1678_ = 0;
v___x_1679_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1677_, v_data_1430_, v___x_1678_);
lean_dec(v_presentation_1677_);
return v___x_1679_;
}
case 23:
{
lean_object* v_presentation_1680_; uint8_t v___x_1681_; lean_object* v___x_1682_; 
v_presentation_1680_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc(v_presentation_1680_);
lean_dec_ref_known(v_modifier_1429_, 1);
v___x_1681_ = 0;
v___x_1682_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1680_, v_data_1430_, v___x_1681_);
lean_dec(v_presentation_1680_);
return v___x_1682_;
}
case 24:
{
lean_object* v_presentation_1683_; uint8_t v___x_1684_; lean_object* v___x_1685_; 
v_presentation_1683_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc(v_presentation_1683_);
lean_dec_ref_known(v_modifier_1429_, 1);
v___x_1684_ = 0;
v___x_1685_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1683_, v_data_1430_, v___x_1684_);
lean_dec(v_presentation_1683_);
return v___x_1685_;
}
case 25:
{
lean_object* v_presentation_1686_; 
v_presentation_1686_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc(v_presentation_1686_);
lean_dec_ref_known(v_modifier_1429_, 1);
if (lean_obj_tag(v_presentation_1686_) == 0)
{
lean_object* v___x_1687_; uint8_t v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = lean_unsigned_to_nat(9u);
v___x_1688_ = 0;
v___x_1689_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1687_, v_data_1430_, v___x_1688_);
return v___x_1689_;
}
else
{
lean_object* v_digits_1690_; lean_object* v___x_1691_; uint32_t v___x_1692_; lean_object* v___x_1693_; lean_object* v_s_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v_digits_1690_ = lean_ctor_get(v_presentation_1686_, 0);
lean_inc(v_digits_1690_);
lean_dec_ref_known(v_presentation_1686_, 1);
v___x_1691_ = lean_unsigned_to_nat(9u);
v___x_1692_ = 48;
v___x_1693_ = l_Int_repr(v_data_1430_);
lean_dec(v_data_1430_);
v_s_1694_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1691_, v___x_1692_, v___x_1693_);
v___x_1695_ = lean_unsigned_to_nat(0u);
v___x_1696_ = lean_string_utf8_byte_size(v_s_1694_);
lean_inc_ref(v_s_1694_);
v___x_1697_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1697_, 0, v_s_1694_);
lean_ctor_set(v___x_1697_, 1, v___x_1695_);
lean_ctor_set(v___x_1697_, 2, v___x_1696_);
v___x_1698_ = l_String_Slice_Pos_nextn(v___x_1697_, v___x_1695_, v_digits_1690_);
lean_dec_ref_known(v___x_1697_, 3);
v___x_1699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1699_, 0, v_s_1694_);
lean_ctor_set(v___x_1699_, 1, v___x_1695_);
lean_ctor_set(v___x_1699_, 2, v___x_1698_);
v___x_1700_ = l_String_Slice_toString(v___x_1699_);
lean_dec_ref_known(v___x_1699_, 3);
return v___x_1700_;
}
}
case 26:
{
lean_object* v_presentation_1701_; uint8_t v___x_1702_; lean_object* v___x_1703_; 
v_presentation_1701_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc(v_presentation_1701_);
lean_dec_ref_known(v_modifier_1429_, 1);
v___x_1702_ = 0;
v___x_1703_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1701_, v_data_1430_, v___x_1702_);
lean_dec(v_presentation_1701_);
return v___x_1703_;
}
case 27:
{
lean_object* v_presentation_1704_; uint8_t v___x_1705_; lean_object* v___x_1706_; 
v_presentation_1704_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc(v_presentation_1704_);
lean_dec_ref_known(v_modifier_1429_, 1);
v___x_1705_ = 0;
v___x_1706_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1704_, v_data_1430_, v___x_1705_);
lean_dec(v_presentation_1704_);
return v___x_1706_;
}
case 28:
{
lean_object* v_presentation_1707_; uint8_t v___x_1708_; lean_object* v___x_1709_; 
v_presentation_1707_ = lean_ctor_get(v_modifier_1429_, 0);
lean_inc(v_presentation_1707_);
lean_dec_ref_known(v_modifier_1429_, 1);
v___x_1708_ = 0;
v___x_1709_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1707_, v_data_1430_, v___x_1708_);
lean_dec(v_presentation_1707_);
return v___x_1709_;
}
case 29:
{
uint8_t v_presentation_1710_; 
v_presentation_1710_ = lean_ctor_get_uint8(v_modifier_1429_, 0);
lean_dec_ref_known(v_modifier_1429_, 0);
if (v_presentation_1710_ == 0)
{
lean_object* v___x_1711_; 
lean_dec(v_data_1430_);
v___x_1711_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
return v___x_1711_;
}
else
{
return v_data_1430_;
}
}
case 32:
{
uint8_t v_presentation_1712_; 
v_presentation_1712_ = lean_ctor_get_uint8(v_modifier_1429_, 0);
lean_dec_ref_known(v_modifier_1429_, 0);
if (v_presentation_1712_ == 0)
{
lean_object* v_fst_1714_; lean_object* v_snd_1715_; lean_object* v___x_1738_; uint8_t v___x_1739_; 
v___x_1738_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1739_ = lean_int_dec_eq(v_data_1430_, v___x_1738_);
if (v___x_1739_ == 0)
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_int_dec_le(v___x_1738_, v_data_1430_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1742_ = lean_int_neg(v_data_1430_);
lean_dec(v_data_1430_);
v_fst_1714_ = v___x_1741_;
v_snd_1715_ = v___x_1742_;
goto v___jp_1713_;
}
else
{
lean_object* v___x_1743_; 
v___x_1743_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v_fst_1714_ = v___x_1743_;
v_snd_1715_ = v_data_1430_;
goto v___jp_1713_;
}
}
else
{
lean_object* v___x_1744_; 
lean_dec(v_data_1430_);
v___x_1744_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1744_;
}
v___jp_1713_:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v_t_1718_; lean_object* v_hour_1719_; lean_object* v_minute_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
v___x_1716_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_1717_ = lean_int_mul(v_snd_1715_, v___x_1716_);
lean_dec(v_snd_1715_);
v_t_1718_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1717_);
lean_dec(v___x_1717_);
v_hour_1719_ = lean_ctor_get(v_t_1718_, 0);
lean_inc(v_hour_1719_);
v_minute_1720_ = lean_ctor_get(v_t_1718_, 1);
lean_inc(v_minute_1720_);
lean_dec_ref(v_t_1718_);
v___x_1721_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1722_ = lean_int_dec_eq(v_minute_1720_, v___x_1721_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; uint32_t v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1723_ = lean_unsigned_to_nat(2u);
v___x_1724_ = 48;
v___x_1725_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1726_ = lean_string_append(v___x_1725_, v_fst_1714_);
v___x_1727_ = l_Int_repr(v_hour_1719_);
lean_dec(v_hour_1719_);
v___x_1728_ = lean_string_append(v___x_1726_, v___x_1727_);
lean_dec_ref(v___x_1727_);
v___x_1729_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___x_1730_ = lean_string_append(v___x_1728_, v___x_1729_);
v___x_1731_ = l_Int_repr(v_minute_1720_);
lean_dec(v_minute_1720_);
v___x_1732_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1723_, v___x_1724_, v___x_1731_);
v___x_1733_ = lean_string_append(v___x_1730_, v___x_1732_);
lean_dec_ref(v___x_1732_);
return v___x_1733_;
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_dec(v_minute_1720_);
v___x_1734_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1735_ = lean_string_append(v___x_1734_, v_fst_1714_);
v___x_1736_ = l_Int_repr(v_hour_1719_);
lean_dec(v_hour_1719_);
v___x_1737_ = lean_string_append(v___x_1735_, v___x_1736_);
lean_dec_ref(v___x_1736_);
return v___x_1737_;
}
}
}
else
{
lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1745_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1746_ = lean_int_dec_eq(v_data_1430_, v___x_1745_);
if (v___x_1746_ == 0)
{
uint8_t v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; uint8_t v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1747_ = 1;
v___x_1748_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1749_ = 0;
v___x_1750_ = 1;
v___x_1751_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1430_, v___x_1749_, v___x_1750_, v___x_1747_, v___x_1747_);
v___x_1752_ = lean_string_append(v___x_1748_, v___x_1751_);
lean_dec_ref(v___x_1751_);
return v___x_1752_;
}
else
{
lean_object* v___x_1753_; 
lean_dec(v_data_1430_);
v___x_1753_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1753_;
}
}
}
case 33:
{
uint8_t v_presentation_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v_presentation_1754_ = lean_ctor_get_uint8(v_modifier_1429_, 0);
lean_dec_ref_known(v_modifier_1429_, 0);
v___x_1755_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1756_ = lean_int_dec_eq(v_data_1430_, v___x_1755_);
if (v___x_1756_ == 0)
{
uint8_t v___x_1757_; 
v___x_1757_ = 1;
switch(v_presentation_1754_)
{
case 0:
{
uint8_t v___x_1758_; uint8_t v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = 2;
v___x_1759_ = 1;
v___x_1760_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1430_, v___x_1758_, v___x_1759_, v___x_1756_, v___x_1757_);
return v___x_1760_;
}
case 1:
{
uint8_t v___x_1761_; uint8_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = 0;
v___x_1762_ = 1;
v___x_1763_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1430_, v___x_1761_, v___x_1762_, v___x_1756_, v___x_1757_);
return v___x_1763_;
}
case 2:
{
uint8_t v___x_1764_; uint8_t v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = 0;
v___x_1765_ = 1;
v___x_1766_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1430_, v___x_1764_, v___x_1765_, v___x_1757_, v___x_1757_);
return v___x_1766_;
}
case 3:
{
uint8_t v___x_1767_; uint8_t v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = 0;
v___x_1768_ = 2;
v___x_1769_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1430_, v___x_1767_, v___x_1768_, v___x_1756_, v___x_1757_);
return v___x_1769_;
}
default: 
{
uint8_t v___x_1770_; uint8_t v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = 0;
v___x_1771_ = 2;
v___x_1772_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1430_, v___x_1770_, v___x_1771_, v___x_1757_, v___x_1757_);
return v___x_1772_;
}
}
}
else
{
lean_object* v___x_1773_; 
lean_dec(v_data_1430_);
v___x_1773_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
return v___x_1773_;
}
}
case 34:
{
uint8_t v_presentation_1774_; 
v_presentation_1774_ = lean_ctor_get_uint8(v_modifier_1429_, 0);
lean_dec_ref_known(v_modifier_1429_, 0);
switch(v_presentation_1774_)
{
case 0:
{
uint8_t v___x_1775_; uint8_t v___x_1776_; uint8_t v___x_1777_; uint8_t v___x_1778_; lean_object* v___x_1779_; 
v___x_1775_ = 2;
v___x_1776_ = 1;
v___x_1777_ = 0;
v___x_1778_ = 1;
v___x_1779_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1430_, v___x_1775_, v___x_1776_, v___x_1777_, v___x_1778_);
return v___x_1779_;
}
case 1:
{
uint8_t v___x_1780_; uint8_t v___x_1781_; uint8_t v___x_1782_; uint8_t v___x_1783_; lean_object* v___x_1784_; 
v___x_1780_ = 0;
v___x_1781_ = 1;
v___x_1782_ = 0;
v___x_1783_ = 1;
v___x_1784_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1430_, v___x_1780_, v___x_1781_, v___x_1782_, v___x_1783_);
return v___x_1784_;
}
case 2:
{
uint8_t v___x_1785_; uint8_t v___x_1786_; uint8_t v___x_1787_; lean_object* v___x_1788_; 
v___x_1785_ = 0;
v___x_1786_ = 1;
v___x_1787_ = 1;
v___x_1788_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1430_, v___x_1785_, v___x_1786_, v___x_1787_, v___x_1787_);
return v___x_1788_;
}
case 3:
{
uint8_t v___x_1789_; uint8_t v___x_1790_; uint8_t v___x_1791_; uint8_t v___x_1792_; lean_object* v___x_1793_; 
v___x_1789_ = 0;
v___x_1790_ = 2;
v___x_1791_ = 0;
v___x_1792_ = 1;
v___x_1793_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1430_, v___x_1789_, v___x_1790_, v___x_1791_, v___x_1792_);
return v___x_1793_;
}
default: 
{
uint8_t v___x_1794_; uint8_t v___x_1795_; uint8_t v___x_1796_; lean_object* v___x_1797_; 
v___x_1794_ = 0;
v___x_1795_ = 2;
v___x_1796_ = 1;
v___x_1797_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1430_, v___x_1794_, v___x_1795_, v___x_1796_, v___x_1796_);
return v___x_1797_;
}
}
}
case 35:
{
uint8_t v_presentation_1798_; 
v_presentation_1798_ = lean_ctor_get_uint8(v_modifier_1429_, 0);
lean_dec_ref_known(v_modifier_1429_, 0);
switch(v_presentation_1798_)
{
case 0:
{
uint8_t v___x_1799_; uint8_t v___x_1800_; uint8_t v___x_1801_; uint8_t v___x_1802_; lean_object* v___x_1803_; 
v___x_1799_ = 0;
v___x_1800_ = 2;
v___x_1801_ = 0;
v___x_1802_ = 1;
v___x_1803_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1430_, v___x_1799_, v___x_1800_, v___x_1801_, v___x_1802_);
return v___x_1803_;
}
case 1:
{
lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1804_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1805_ = lean_int_dec_eq(v_data_1430_, v___x_1804_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; uint8_t v___x_1807_; uint8_t v___x_1808_; uint8_t v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1806_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1807_ = 0;
v___x_1808_ = 1;
v___x_1809_ = 1;
v___x_1810_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1430_, v___x_1807_, v___x_1808_, v___x_1809_, v___x_1809_);
v___x_1811_ = lean_string_append(v___x_1806_, v___x_1810_);
lean_dec_ref(v___x_1810_);
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; 
lean_dec(v_data_1430_);
v___x_1812_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1812_;
}
}
default: 
{
lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1813_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1814_ = lean_int_dec_eq(v_data_1430_, v___x_1813_);
if (v___x_1814_ == 0)
{
uint8_t v___x_1815_; uint8_t v___x_1816_; uint8_t v___x_1817_; lean_object* v___x_1818_; 
v___x_1815_ = 1;
v___x_1816_ = 0;
v___x_1817_ = 2;
v___x_1818_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1430_, v___x_1816_, v___x_1817_, v___x_1815_, v___x_1815_);
return v___x_1818_;
}
else
{
lean_object* v___x_1819_; 
lean_dec(v_data_1430_);
v___x_1819_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
return v___x_1819_;
}
}
}
}
default: 
{
lean_dec_ref(v_modifier_1429_);
return v_data_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___boxed(lean_object* v_dateformat_1820_, lean_object* v_modifier_1821_, lean_object* v_data_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_1820_, v_modifier_1821_, v_data_1822_);
lean_dec_ref(v_dateformat_1820_);
return v_res_1823_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = lean_unsigned_to_nat(400u);
v___x_1825_ = lean_nat_to_int(v___x_1824_);
return v___x_1825_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = lean_unsigned_to_nat(4u);
v___x_1827_ = lean_nat_to_int(v___x_1826_);
return v___x_1827_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2(void){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1829_ = lean_string_utf8_byte_size(v___x_1828_);
return v___x_1829_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_1831_ = lean_string_utf8_byte_size(v___x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(lean_object* v_modifier_1832_, lean_object* v_dateformat_1833_, lean_object* v_date_1834_){
_start:
{
uint8_t v___y_1836_; lean_object* v_month_1837_; lean_object* v_day_1838_; uint8_t v___y_1839_; lean_object* v___y_1845_; uint8_t v___y_1846_; lean_object* v_month_1847_; lean_object* v_day_1848_; lean_object* v___y_1849_; uint8_t v_firstDayOfWeek_1853_; lean_object* v_minimalDaysInFirstWeek_1854_; lean_object* v_date_1855_; lean_object* v_timezone_1856_; uint8_t v___y_1875_; 
v_firstDayOfWeek_1853_ = lean_ctor_get_uint8(v_dateformat_1833_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_1854_ = lean_ctor_get(v_dateformat_1833_, 0);
v_date_1855_ = lean_ctor_get(v_date_1834_, 0);
v_timezone_1856_ = lean_ctor_get(v_date_1834_, 3);
switch(lean_obj_tag(v_modifier_1832_))
{
case 0:
{
lean_object* v___x_1888_; lean_object* v_date_1889_; lean_object* v_year_1890_; uint8_t v___x_1891_; lean_object* v___x_1892_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1888_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc_ref(v_date_1889_);
lean_dec(v___x_1888_);
v_year_1890_ = lean_ctor_get(v_date_1889_, 0);
lean_inc(v_year_1890_);
lean_dec_ref(v_date_1889_);
v___x_1891_ = l_Std_Time_Year_Offset_era(v_year_1890_);
lean_dec(v_year_1890_);
v___x_1892_ = lean_box(v___x_1891_);
return v___x_1892_;
}
case 1:
{
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
goto v___jp_1870_;
}
case 2:
{
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
goto v___jp_1870_;
}
case 3:
{
lean_object* v___x_1893_; lean_object* v_date_1894_; lean_object* v_year_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1903_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1893_ = lean_thunk_get_own(v_date_1855_);
v_date_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc_ref(v_date_1894_);
lean_dec(v___x_1893_);
v_year_1895_ = lean_ctor_get(v_date_1894_, 0);
lean_inc(v_year_1895_);
lean_dec_ref(v_date_1894_);
v___x_1896_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_1897_ = lean_int_mod(v_year_1895_, v___x_1896_);
v___x_1898_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1903_ = lean_int_dec_eq(v___x_1897_, v___x_1898_);
lean_dec(v___x_1897_);
if (v___x_1903_ == 0)
{
lean_dec(v_year_1895_);
v___y_1875_ = v___x_1903_;
goto v___jp_1874_;
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; uint8_t v___x_1906_; 
v___x_1904_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1905_ = lean_int_mod(v_year_1895_, v___x_1904_);
v___x_1906_ = lean_int_dec_eq(v___x_1905_, v___x_1898_);
lean_dec(v___x_1905_);
if (v___x_1906_ == 0)
{
if (v___x_1903_ == 0)
{
goto v___jp_1899_;
}
else
{
lean_dec(v_year_1895_);
v___y_1875_ = v___x_1903_;
goto v___jp_1874_;
}
}
else
{
goto v___jp_1899_;
}
}
v___jp_1899_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; 
v___x_1900_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_1901_ = lean_int_mod(v_year_1895_, v___x_1900_);
lean_dec(v_year_1895_);
v___x_1902_ = lean_int_dec_eq(v___x_1901_, v___x_1898_);
lean_dec(v___x_1901_);
v___y_1875_ = v___x_1902_;
goto v___jp_1874_;
}
}
case 4:
{
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
goto v___jp_1866_;
}
case 5:
{
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
goto v___jp_1866_;
}
case 6:
{
lean_object* v___x_1907_; lean_object* v_date_1908_; lean_object* v_day_1909_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1907_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc_ref(v_date_1908_);
lean_dec(v___x_1907_);
v_day_1909_ = lean_ctor_get(v_date_1908_, 2);
lean_inc(v_day_1909_);
lean_dec_ref(v_date_1908_);
return v_day_1909_;
}
case 7:
{
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
goto v___jp_1862_;
}
case 8:
{
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
goto v___jp_1862_;
}
case 9:
{
lean_object* v___x_1910_; lean_object* v_date_1911_; lean_object* v___x_1912_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1910_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc_ref(v_date_1911_);
lean_dec(v___x_1910_);
v___x_1912_ = l_Std_Time_PlainDate_weekYear(v_date_1911_, v_firstDayOfWeek_1853_, v_minimalDaysInFirstWeek_1854_);
return v___x_1912_;
}
case 10:
{
lean_object* v___x_1913_; lean_object* v_date_1914_; lean_object* v___x_1915_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1913_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc_ref(v_date_1914_);
lean_dec(v___x_1913_);
v___x_1915_ = l_Std_Time_PlainDate_weekOfYear(v_date_1914_, v_firstDayOfWeek_1853_, v_minimalDaysInFirstWeek_1854_);
return v___x_1915_;
}
case 11:
{
lean_object* v___x_1916_; lean_object* v_date_1917_; lean_object* v___x_1918_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1916_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc_ref(v_date_1917_);
lean_dec(v___x_1916_);
v___x_1918_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1917_, v_firstDayOfWeek_1853_);
return v___x_1918_;
}
case 12:
{
lean_object* v___x_1919_; lean_object* v_date_1920_; uint8_t v___x_1921_; lean_object* v___x_1922_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1919_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc_ref(v_date_1920_);
lean_dec(v___x_1919_);
v___x_1921_ = l_Std_Time_PlainDate_weekday(v_date_1920_);
v___x_1922_ = lean_box(v___x_1921_);
return v___x_1922_;
}
case 13:
{
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
goto v___jp_1857_;
}
case 14:
{
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
goto v___jp_1857_;
}
case 15:
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Std_Time_DateTime_alignedWeekOfMonth(v_date_1834_);
lean_dec_ref(v_date_1834_);
return v___x_1923_;
}
case 16:
{
lean_object* v___x_1924_; lean_object* v_time_1925_; lean_object* v_hour_1926_; uint8_t v___x_1927_; lean_object* v___x_1928_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1924_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1925_ = lean_ctor_get(v___x_1924_, 1);
lean_inc_ref(v_time_1925_);
lean_dec(v___x_1924_);
v_hour_1926_ = lean_ctor_get(v_time_1925_, 0);
lean_inc(v_hour_1926_);
lean_dec_ref(v_time_1925_);
v___x_1927_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1926_);
lean_dec(v_hour_1926_);
v___x_1928_ = lean_box(v___x_1927_);
return v___x_1928_;
}
case 17:
{
lean_object* v___x_1929_; lean_object* v_time_1930_; lean_object* v_hour_1931_; lean_object* v_minute_1932_; lean_object* v_second_1933_; uint8_t v___x_1934_; lean_object* v___x_1935_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1929_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1930_ = lean_ctor_get(v___x_1929_, 1);
lean_inc_ref(v_time_1930_);
lean_dec(v___x_1929_);
v_hour_1931_ = lean_ctor_get(v_time_1930_, 0);
lean_inc(v_hour_1931_);
v_minute_1932_ = lean_ctor_get(v_time_1930_, 1);
lean_inc(v_minute_1932_);
v_second_1933_ = lean_ctor_get(v_time_1930_, 2);
lean_inc(v_second_1933_);
lean_dec_ref(v_time_1930_);
v___x_1934_ = l_Std_Time_classifyDayPeriod(v_hour_1931_, v_minute_1932_, v_second_1933_);
lean_dec(v_second_1933_);
lean_dec(v_minute_1932_);
lean_dec(v_hour_1931_);
v___x_1935_ = lean_box(v___x_1934_);
return v___x_1935_;
}
case 18:
{
lean_object* v___x_1936_; lean_object* v_time_1937_; lean_object* v_hour_1938_; lean_object* v_minute_1939_; lean_object* v_second_1940_; uint8_t v___x_1941_; lean_object* v___x_1942_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1936_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1937_ = lean_ctor_get(v___x_1936_, 1);
lean_inc_ref(v_time_1937_);
lean_dec(v___x_1936_);
v_hour_1938_ = lean_ctor_get(v_time_1937_, 0);
lean_inc(v_hour_1938_);
v_minute_1939_ = lean_ctor_get(v_time_1937_, 1);
lean_inc(v_minute_1939_);
v_second_1940_ = lean_ctor_get(v_time_1937_, 2);
lean_inc(v_second_1940_);
lean_dec_ref(v_time_1937_);
v___x_1941_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1938_, v_minute_1939_, v_second_1940_);
lean_dec(v_second_1940_);
lean_dec(v_minute_1939_);
lean_dec(v_hour_1938_);
v___x_1942_ = lean_box(v___x_1941_);
return v___x_1942_;
}
case 19:
{
lean_object* v___x_1943_; lean_object* v_time_1944_; lean_object* v_hour_1945_; lean_object* v___x_1946_; lean_object* v_fst_1947_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1943_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1944_ = lean_ctor_get(v___x_1943_, 1);
lean_inc_ref(v_time_1944_);
lean_dec(v___x_1943_);
v_hour_1945_ = lean_ctor_get(v_time_1944_, 0);
lean_inc(v_hour_1945_);
lean_dec_ref(v_time_1944_);
v___x_1946_ = l_Std_Time_HourMarker_toRelative(v_hour_1945_);
v_fst_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_fst_1947_);
lean_dec_ref(v___x_1946_);
return v_fst_1947_;
}
case 20:
{
lean_object* v___x_1948_; lean_object* v_time_1949_; lean_object* v_hour_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1948_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1949_ = lean_ctor_get(v___x_1948_, 1);
lean_inc_ref(v_time_1949_);
lean_dec(v___x_1948_);
v_hour_1950_ = lean_ctor_get(v_time_1949_, 0);
lean_inc(v_hour_1950_);
lean_dec_ref(v_time_1949_);
v___x_1951_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1952_ = lean_int_emod(v_hour_1950_, v___x_1951_);
lean_dec(v_hour_1950_);
return v___x_1952_;
}
case 21:
{
lean_object* v___x_1953_; lean_object* v_time_1954_; lean_object* v_hour_1955_; lean_object* v___x_1956_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1953_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1954_ = lean_ctor_get(v___x_1953_, 1);
lean_inc_ref(v_time_1954_);
lean_dec(v___x_1953_);
v_hour_1955_ = lean_ctor_get(v_time_1954_, 0);
lean_inc(v_hour_1955_);
lean_dec_ref(v_time_1954_);
v___x_1956_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_1955_);
lean_dec(v_hour_1955_);
return v___x_1956_;
}
case 22:
{
lean_object* v___x_1957_; lean_object* v_time_1958_; lean_object* v_hour_1959_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1957_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1958_ = lean_ctor_get(v___x_1957_, 1);
lean_inc_ref(v_time_1958_);
lean_dec(v___x_1957_);
v_hour_1959_ = lean_ctor_get(v_time_1958_, 0);
lean_inc(v_hour_1959_);
lean_dec_ref(v_time_1958_);
return v_hour_1959_;
}
case 23:
{
lean_object* v___x_1960_; lean_object* v_time_1961_; lean_object* v_minute_1962_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1960_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1961_ = lean_ctor_get(v___x_1960_, 1);
lean_inc_ref(v_time_1961_);
lean_dec(v___x_1960_);
v_minute_1962_ = lean_ctor_get(v_time_1961_, 1);
lean_inc(v_minute_1962_);
lean_dec_ref(v_time_1961_);
return v_minute_1962_;
}
case 24:
{
lean_object* v___x_1963_; lean_object* v_time_1964_; lean_object* v_second_1965_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1963_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1964_ = lean_ctor_get(v___x_1963_, 1);
lean_inc_ref(v_time_1964_);
lean_dec(v___x_1963_);
v_second_1965_ = lean_ctor_get(v_time_1964_, 2);
lean_inc(v_second_1965_);
lean_dec_ref(v_time_1964_);
return v_second_1965_;
}
case 25:
{
lean_object* v___x_1966_; lean_object* v_time_1967_; lean_object* v_nanosecond_1968_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1966_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1967_ = lean_ctor_get(v___x_1966_, 1);
lean_inc_ref(v_time_1967_);
lean_dec(v___x_1966_);
v_nanosecond_1968_ = lean_ctor_get(v_time_1967_, 3);
lean_inc(v_nanosecond_1968_);
lean_dec_ref(v_time_1967_);
return v_nanosecond_1968_;
}
case 26:
{
lean_object* v___x_1969_; lean_object* v_time_1970_; lean_object* v___x_1971_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1969_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1970_ = lean_ctor_get(v___x_1969_, 1);
lean_inc_ref(v_time_1970_);
lean_dec(v___x_1969_);
v___x_1971_ = l_Std_Time_PlainTime_toMilliseconds(v_time_1970_);
lean_dec_ref(v_time_1970_);
return v___x_1971_;
}
case 27:
{
lean_object* v___x_1972_; lean_object* v_time_1973_; lean_object* v_nanosecond_1974_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1972_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1973_ = lean_ctor_get(v___x_1972_, 1);
lean_inc_ref(v_time_1973_);
lean_dec(v___x_1972_);
v_nanosecond_1974_ = lean_ctor_get(v_time_1973_, 3);
lean_inc(v_nanosecond_1974_);
lean_dec_ref(v_time_1973_);
return v_nanosecond_1974_;
}
case 28:
{
lean_object* v___x_1975_; lean_object* v_time_1976_; lean_object* v___x_1977_; 
lean_inc_ref(v_date_1855_);
lean_dec_ref(v_date_1834_);
v___x_1975_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_time_1976_ = lean_ctor_get(v___x_1975_, 1);
lean_inc_ref(v_time_1976_);
lean_dec(v___x_1975_);
v___x_1977_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1976_);
lean_dec_ref(v_time_1976_);
return v___x_1977_;
}
case 29:
{
uint8_t v_presentation_1978_; 
lean_inc_ref(v_timezone_1856_);
lean_dec_ref(v_date_1834_);
v_presentation_1978_ = lean_ctor_get_uint8(v_modifier_1832_, 0);
if (v_presentation_1978_ == 0)
{
lean_object* v___x_1979_; 
lean_dec_ref(v_timezone_1856_);
v___x_1979_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
return v___x_1979_;
}
else
{
lean_object* v_offset_1980_; lean_object* v_name_1981_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
v_offset_1980_ = lean_ctor_get(v_timezone_1856_, 0);
lean_inc(v_offset_1980_);
v_name_1981_ = lean_ctor_get(v_timezone_1856_, 1);
lean_inc_ref(v_name_1981_);
lean_dec_ref(v_timezone_1856_);
v___x_1996_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_1997_ = lean_string_utf8_byte_size(v_name_1981_);
v___x_1998_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_1999_ = lean_nat_dec_le(v___x_1998_, v___x_1997_);
if (v___x_1999_ == 0)
{
goto v___jp_1989_;
}
else
{
lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_2000_ = lean_unsigned_to_nat(0u);
v___x_2001_ = lean_string_memcmp(v_name_1981_, v___x_1996_, v___x_2000_, v___x_2000_, v___x_1998_);
if (v___x_2001_ == 0)
{
goto v___jp_1989_;
}
else
{
lean_dec_ref(v_name_1981_);
goto v___jp_1982_;
}
}
v___jp_1982_:
{
uint8_t v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1983_ = 1;
v___x_1984_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1985_ = 0;
v___x_1986_ = 1;
v___x_1987_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1980_, v___x_1985_, v___x_1986_, v___x_1983_, v___x_1983_);
v___x_1988_ = lean_string_append(v___x_1984_, v___x_1987_);
lean_dec_ref(v___x_1987_);
return v___x_1988_;
}
v___jp_1989_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
v___x_1990_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1991_ = lean_string_utf8_byte_size(v_name_1981_);
v___x_1992_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_1993_ = lean_nat_dec_le(v___x_1992_, v___x_1991_);
if (v___x_1993_ == 0)
{
lean_dec(v_offset_1980_);
return v_name_1981_;
}
else
{
lean_object* v___x_1994_; uint8_t v___x_1995_; 
v___x_1994_ = lean_unsigned_to_nat(0u);
v___x_1995_ = lean_string_memcmp(v_name_1981_, v___x_1990_, v___x_1994_, v___x_1994_, v___x_1992_);
if (v___x_1995_ == 0)
{
lean_dec(v_offset_1980_);
return v_name_1981_;
}
else
{
lean_dec_ref(v_name_1981_);
goto v___jp_1982_;
}
}
}
}
}
case 30:
{
uint8_t v_presentation_2002_; 
lean_inc_ref(v_timezone_1856_);
lean_dec_ref(v_date_1834_);
v_presentation_2002_ = lean_ctor_get_uint8(v_modifier_1832_, 0);
if (v_presentation_2002_ == 0)
{
lean_object* v_offset_2003_; lean_object* v_abbreviation_2004_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v_offset_2003_ = lean_ctor_get(v_timezone_1856_, 0);
lean_inc(v_offset_2003_);
v_abbreviation_2004_ = lean_ctor_get(v_timezone_1856_, 2);
lean_inc_ref(v_abbreviation_2004_);
lean_dec_ref(v_timezone_1856_);
v___x_2019_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2020_ = lean_string_utf8_byte_size(v_abbreviation_2004_);
v___x_2021_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_2022_ = lean_nat_dec_le(v___x_2021_, v___x_2020_);
if (v___x_2022_ == 0)
{
goto v___jp_2012_;
}
else
{
lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = lean_unsigned_to_nat(0u);
v___x_2024_ = lean_string_memcmp(v_abbreviation_2004_, v___x_2019_, v___x_2023_, v___x_2023_, v___x_2021_);
if (v___x_2024_ == 0)
{
goto v___jp_2012_;
}
else
{
lean_dec_ref(v_abbreviation_2004_);
goto v___jp_2005_;
}
}
v___jp_2005_:
{
uint8_t v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; uint8_t v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2006_ = 1;
v___x_2007_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2008_ = 0;
v___x_2009_ = 1;
v___x_2010_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2003_, v___x_2008_, v___x_2009_, v___x_2006_, v___x_2006_);
v___x_2011_ = lean_string_append(v___x_2007_, v___x_2010_);
lean_dec_ref(v___x_2010_);
return v___x_2011_;
}
v___jp_2012_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2013_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2014_ = lean_string_utf8_byte_size(v_abbreviation_2004_);
v___x_2015_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_2016_ = lean_nat_dec_le(v___x_2015_, v___x_2014_);
if (v___x_2016_ == 0)
{
lean_dec(v_offset_2003_);
return v_abbreviation_2004_;
}
else
{
lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = lean_unsigned_to_nat(0u);
v___x_2018_ = lean_string_memcmp(v_abbreviation_2004_, v___x_2013_, v___x_2017_, v___x_2017_, v___x_2015_);
if (v___x_2018_ == 0)
{
lean_dec(v_offset_2003_);
return v_abbreviation_2004_;
}
else
{
lean_dec_ref(v_abbreviation_2004_);
goto v___jp_2005_;
}
}
}
}
else
{
lean_object* v_offset_2025_; lean_object* v_name_2026_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v_offset_2025_ = lean_ctor_get(v_timezone_1856_, 0);
lean_inc(v_offset_2025_);
v_name_2026_ = lean_ctor_get(v_timezone_1856_, 1);
lean_inc_ref(v_name_2026_);
lean_dec_ref(v_timezone_1856_);
v___x_2041_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2042_ = lean_string_utf8_byte_size(v_name_2026_);
v___x_2043_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_2044_ = lean_nat_dec_le(v___x_2043_, v___x_2042_);
if (v___x_2044_ == 0)
{
goto v___jp_2034_;
}
else
{
lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2045_ = lean_unsigned_to_nat(0u);
v___x_2046_ = lean_string_memcmp(v_name_2026_, v___x_2041_, v___x_2045_, v___x_2045_, v___x_2043_);
if (v___x_2046_ == 0)
{
goto v___jp_2034_;
}
else
{
lean_dec_ref(v_name_2026_);
goto v___jp_2027_;
}
}
v___jp_2027_:
{
uint8_t v___x_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; uint8_t v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2028_ = 1;
v___x_2029_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2030_ = 0;
v___x_2031_ = 1;
v___x_2032_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2025_, v___x_2030_, v___x_2031_, v___x_2028_, v___x_2028_);
v___x_2033_ = lean_string_append(v___x_2029_, v___x_2032_);
lean_dec_ref(v___x_2032_);
return v___x_2033_;
}
v___jp_2034_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2035_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2036_ = lean_string_utf8_byte_size(v_name_2026_);
v___x_2037_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_2038_ = lean_nat_dec_le(v___x_2037_, v___x_2036_);
if (v___x_2038_ == 0)
{
lean_dec(v_offset_2025_);
return v_name_2026_;
}
else
{
lean_object* v___x_2039_; uint8_t v___x_2040_; 
v___x_2039_ = lean_unsigned_to_nat(0u);
v___x_2040_ = lean_string_memcmp(v_name_2026_, v___x_2035_, v___x_2039_, v___x_2039_, v___x_2037_);
if (v___x_2040_ == 0)
{
lean_dec(v_offset_2025_);
return v_name_2026_;
}
else
{
lean_dec_ref(v_name_2026_);
goto v___jp_2027_;
}
}
}
}
}
case 31:
{
uint8_t v_presentation_2047_; 
lean_inc_ref(v_timezone_1856_);
lean_dec_ref(v_date_1834_);
v_presentation_2047_ = lean_ctor_get_uint8(v_modifier_1832_, 0);
if (v_presentation_2047_ == 0)
{
lean_object* v_offset_2048_; lean_object* v_abbreviation_2049_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v_offset_2048_ = lean_ctor_get(v_timezone_1856_, 0);
lean_inc(v_offset_2048_);
v_abbreviation_2049_ = lean_ctor_get(v_timezone_1856_, 2);
lean_inc_ref(v_abbreviation_2049_);
lean_dec_ref(v_timezone_1856_);
v___x_2064_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2065_ = lean_string_utf8_byte_size(v_abbreviation_2049_);
v___x_2066_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_2067_ = lean_nat_dec_le(v___x_2066_, v___x_2065_);
if (v___x_2067_ == 0)
{
goto v___jp_2057_;
}
else
{
lean_object* v___x_2068_; uint8_t v___x_2069_; 
v___x_2068_ = lean_unsigned_to_nat(0u);
v___x_2069_ = lean_string_memcmp(v_abbreviation_2049_, v___x_2064_, v___x_2068_, v___x_2068_, v___x_2066_);
if (v___x_2069_ == 0)
{
goto v___jp_2057_;
}
else
{
lean_dec_ref(v_abbreviation_2049_);
goto v___jp_2050_;
}
}
v___jp_2050_:
{
uint8_t v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; uint8_t v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2051_ = 1;
v___x_2052_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2053_ = 0;
v___x_2054_ = 1;
v___x_2055_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2048_, v___x_2053_, v___x_2054_, v___x_2051_, v___x_2051_);
v___x_2056_ = lean_string_append(v___x_2052_, v___x_2055_);
lean_dec_ref(v___x_2055_);
return v___x_2056_;
}
v___jp_2057_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2058_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2059_ = lean_string_utf8_byte_size(v_abbreviation_2049_);
v___x_2060_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_2061_ = lean_nat_dec_le(v___x_2060_, v___x_2059_);
if (v___x_2061_ == 0)
{
lean_dec(v_offset_2048_);
return v_abbreviation_2049_;
}
else
{
lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2062_ = lean_unsigned_to_nat(0u);
v___x_2063_ = lean_string_memcmp(v_abbreviation_2049_, v___x_2058_, v___x_2062_, v___x_2062_, v___x_2060_);
if (v___x_2063_ == 0)
{
lean_dec(v_offset_2048_);
return v_abbreviation_2049_;
}
else
{
lean_dec_ref(v_abbreviation_2049_);
goto v___jp_2050_;
}
}
}
}
else
{
lean_object* v_offset_2070_; lean_object* v_name_2071_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v_offset_2070_ = lean_ctor_get(v_timezone_1856_, 0);
lean_inc(v_offset_2070_);
v_name_2071_ = lean_ctor_get(v_timezone_1856_, 1);
lean_inc_ref(v_name_2071_);
lean_dec_ref(v_timezone_1856_);
v___x_2086_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2087_ = lean_string_utf8_byte_size(v_name_2071_);
v___x_2088_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_2089_ = lean_nat_dec_le(v___x_2088_, v___x_2087_);
if (v___x_2089_ == 0)
{
goto v___jp_2079_;
}
else
{
lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2090_ = lean_unsigned_to_nat(0u);
v___x_2091_ = lean_string_memcmp(v_name_2071_, v___x_2086_, v___x_2090_, v___x_2090_, v___x_2088_);
if (v___x_2091_ == 0)
{
goto v___jp_2079_;
}
else
{
lean_dec_ref(v_name_2071_);
goto v___jp_2072_;
}
}
v___jp_2072_:
{
uint8_t v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; uint8_t v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2073_ = 1;
v___x_2074_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2075_ = 0;
v___x_2076_ = 1;
v___x_2077_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2070_, v___x_2075_, v___x_2076_, v___x_2073_, v___x_2073_);
v___x_2078_ = lean_string_append(v___x_2074_, v___x_2077_);
lean_dec_ref(v___x_2077_);
return v___x_2078_;
}
v___jp_2079_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2080_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2081_ = lean_string_utf8_byte_size(v_name_2071_);
v___x_2082_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_2083_ = lean_nat_dec_le(v___x_2082_, v___x_2081_);
if (v___x_2083_ == 0)
{
lean_dec(v_offset_2070_);
return v_name_2071_;
}
else
{
lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2084_ = lean_unsigned_to_nat(0u);
v___x_2085_ = lean_string_memcmp(v_name_2071_, v___x_2080_, v___x_2084_, v___x_2084_, v___x_2082_);
if (v___x_2085_ == 0)
{
lean_dec(v_offset_2070_);
return v_name_2071_;
}
else
{
lean_dec_ref(v_name_2071_);
goto v___jp_2072_;
}
}
}
}
}
default: 
{
lean_object* v_offset_2092_; 
lean_inc_ref(v_timezone_1856_);
lean_dec_ref(v_date_1834_);
v_offset_2092_ = lean_ctor_get(v_timezone_1856_, 0);
lean_inc(v_offset_2092_);
lean_dec_ref(v_timezone_1856_);
return v_offset_2092_;
}
}
v___jp_1835_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_month_1837_);
lean_ctor_set(v___x_1840_, 1, v_day_1838_);
v___x_1841_ = l_Std_Time_ValidDate_dayOfYear(v___y_1839_, v___x_1840_);
lean_dec_ref_known(v___x_1840_, 2);
v___x_1842_ = lean_box(v___y_1836_);
v___x_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
lean_ctor_set(v___x_1843_, 1, v___x_1841_);
return v___x_1843_;
}
v___jp_1844_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; 
v___x_1850_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_1851_ = lean_int_mod(v___y_1849_, v___x_1850_);
lean_dec(v___y_1849_);
v___x_1852_ = lean_int_dec_eq(v___x_1851_, v___y_1845_);
lean_dec(v___x_1851_);
v___y_1836_ = v___y_1846_;
v_month_1837_ = v_month_1847_;
v_day_1838_ = v_day_1848_;
v___y_1839_ = v___x_1852_;
goto v___jp_1835_;
}
v___jp_1857_:
{
lean_object* v___x_1858_; lean_object* v_date_1859_; uint8_t v___x_1860_; lean_object* v___x_1861_; 
v___x_1858_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc_ref(v_date_1859_);
lean_dec(v___x_1858_);
v___x_1860_ = l_Std_Time_PlainDate_weekday(v_date_1859_);
v___x_1861_ = lean_box(v___x_1860_);
return v___x_1861_;
}
v___jp_1862_:
{
lean_object* v___x_1863_; lean_object* v_date_1864_; lean_object* v___x_1865_; 
v___x_1863_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc_ref(v_date_1864_);
lean_dec(v___x_1863_);
v___x_1865_ = l_Std_Time_PlainDate_quarter(v_date_1864_);
lean_dec_ref(v_date_1864_);
return v___x_1865_;
}
v___jp_1866_:
{
lean_object* v___x_1867_; lean_object* v_date_1868_; lean_object* v_month_1869_; 
v___x_1867_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc_ref(v_date_1868_);
lean_dec(v___x_1867_);
v_month_1869_ = lean_ctor_get(v_date_1868_, 1);
lean_inc(v_month_1869_);
lean_dec_ref(v_date_1868_);
return v_month_1869_;
}
v___jp_1870_:
{
lean_object* v___x_1871_; lean_object* v_date_1872_; lean_object* v_year_1873_; 
v___x_1871_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc_ref(v_date_1872_);
lean_dec(v___x_1871_);
v_year_1873_ = lean_ctor_get(v_date_1872_, 0);
lean_inc(v_year_1873_);
lean_dec_ref(v_date_1872_);
return v_year_1873_;
}
v___jp_1874_:
{
lean_object* v___x_1876_; lean_object* v_date_1877_; lean_object* v_year_1878_; lean_object* v_month_1879_; lean_object* v_day_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; uint8_t v___x_1884_; 
v___x_1876_ = lean_thunk_get_own(v_date_1855_);
lean_dec_ref(v_date_1855_);
v_date_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc_ref(v_date_1877_);
lean_dec(v___x_1876_);
v_year_1878_ = lean_ctor_get(v_date_1877_, 0);
lean_inc(v_year_1878_);
v_month_1879_ = lean_ctor_get(v_date_1877_, 1);
lean_inc(v_month_1879_);
v_day_1880_ = lean_ctor_get(v_date_1877_, 2);
lean_inc(v_day_1880_);
lean_dec_ref(v_date_1877_);
v___x_1881_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_1882_ = lean_int_mod(v_year_1878_, v___x_1881_);
v___x_1883_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1884_ = lean_int_dec_eq(v___x_1882_, v___x_1883_);
lean_dec(v___x_1882_);
if (v___x_1884_ == 0)
{
lean_dec(v_year_1878_);
v___y_1836_ = v___y_1875_;
v_month_1837_ = v_month_1879_;
v_day_1838_ = v_day_1880_;
v___y_1839_ = v___x_1884_;
goto v___jp_1835_;
}
else
{
lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v___x_1885_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1886_ = lean_int_mod(v_year_1878_, v___x_1885_);
v___x_1887_ = lean_int_dec_eq(v___x_1886_, v___x_1883_);
lean_dec(v___x_1886_);
if (v___x_1887_ == 0)
{
if (v___x_1884_ == 0)
{
v___y_1845_ = v___x_1883_;
v___y_1846_ = v___y_1875_;
v_month_1847_ = v_month_1879_;
v_day_1848_ = v_day_1880_;
v___y_1849_ = v_year_1878_;
goto v___jp_1844_;
}
else
{
lean_dec(v_year_1878_);
v___y_1836_ = v___y_1875_;
v_month_1837_ = v_month_1879_;
v_day_1838_ = v_day_1880_;
v___y_1839_ = v___x_1884_;
goto v___jp_1835_;
}
}
else
{
v___y_1845_ = v___x_1883_;
v___y_1846_ = v___y_1875_;
v_month_1847_ = v_month_1879_;
v_day_1848_ = v_day_1880_;
v___y_1849_ = v_year_1878_;
goto v___jp_1844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___boxed(lean_object* v_modifier_2093_, lean_object* v_dateformat_2094_, lean_object* v_date_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(v_modifier_2093_, v_dateformat_2094_, v_date_2095_);
lean_dec_ref(v_dateformat_2094_);
lean_dec_ref(v_modifier_2093_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___lam__0(lean_object* v___x_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2097_);
v___x_2100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___y_2098_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___lam__0(lean_object* v___x_2101_, lean_object* v_b_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v_fst_2104_; lean_object* v_snd_2105_; lean_object* v___x_2106_; 
v_fst_2104_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_fst_2104_);
v_snd_2105_ = lean_ctor_get(v___x_2101_, 1);
lean_inc(v_snd_2105_);
lean_dec_ref(v___x_2101_);
lean_inc_ref(v___y_2103_);
v___x_2106_ = lean_apply_1(v_b_2102_, v___y_2103_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_dec(v_snd_2105_);
lean_dec(v_fst_2104_);
lean_dec_ref(v___y_2103_);
return v___x_2106_;
}
else
{
lean_object* v_pos_2107_; lean_object* v_snd_2108_; lean_object* v_snd_2109_; uint8_t v___x_2110_; 
v_pos_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_pos_2107_);
v_snd_2108_ = lean_ctor_get(v___y_2103_, 1);
lean_inc(v_snd_2108_);
lean_dec_ref(v___y_2103_);
v_snd_2109_ = lean_ctor_get(v_pos_2107_, 1);
v___x_2110_ = lean_nat_dec_eq(v_snd_2108_, v_snd_2109_);
lean_dec(v_snd_2108_);
if (v___x_2110_ == 0)
{
lean_dec(v_pos_2107_);
lean_dec(v_snd_2105_);
lean_dec(v_fst_2104_);
return v___x_2106_;
}
else
{
lean_object* v___x_2111_; 
lean_dec_ref_known(v___x_2106_, 2);
v___x_2111_ = l_Std_Internal_Parsec_String_pstring(v_fst_2104_, v_pos_2107_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_pos_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
v_pos_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; 
v_unused_2120_ = lean_ctor_get(v___x_2111_, 1);
lean_dec(v_unused_2120_);
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_pos_2112_);
lean_dec(v___x_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 1, v_snd_2105_);
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_pos_2112_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_snd_2105_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
else
{
lean_object* v_pos_2121_; lean_object* v_err_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v_snd_2105_);
v_pos_2121_ = lean_ctor_get(v___x_2111_, 0);
v_err_2122_ = lean_ctor_get(v___x_2111_, 1);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2111_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_err_2122_);
lean_inc(v_pos_2121_);
lean_dec(v___x_2111_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_pos_2121_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_err_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(lean_object* v_as_2130_, size_t v_i_2131_, size_t v_stop_2132_, lean_object* v_b_2133_, lean_object* v___y_2134_){
_start:
{
uint8_t v___x_2135_; 
v___x_2135_ = lean_usize_dec_eq(v_i_2131_, v_stop_2132_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; lean_object* v___f_2137_; size_t v___x_2138_; size_t v___x_2139_; 
v___x_2136_ = lean_array_uget_borrowed(v_as_2130_, v_i_2131_);
lean_inc(v___x_2136_);
v___f_2137_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2137_, 0, v___x_2136_);
lean_closure_set(v___f_2137_, 1, v_b_2133_);
v___x_2138_ = ((size_t)1ULL);
v___x_2139_ = lean_usize_add(v_i_2131_, v___x_2138_);
v_i_2131_ = v___x_2139_;
v_b_2133_ = v___f_2137_;
goto _start;
}
else
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_apply_1(v_b_2133_, v___y_2134_);
return v___x_2141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___boxed(lean_object* v_as_2142_, lean_object* v_i_2143_, lean_object* v_stop_2144_, lean_object* v_b_2145_, lean_object* v___y_2146_){
_start:
{
size_t v_i_boxed_2147_; size_t v_stop_boxed_2148_; lean_object* v_res_2149_; 
v_i_boxed_2147_ = lean_unbox_usize(v_i_2143_);
lean_dec(v_i_2143_);
v_stop_boxed_2148_ = lean_unbox_usize(v_stop_2144_);
lean_dec(v_stop_2144_);
v_res_2149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_as_2142_, v_i_boxed_2147_, v_stop_boxed_2148_, v_b_2145_, v___y_2146_);
lean_dec_ref(v_as_2142_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(lean_object* v_pairs_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
v___x_2157_ = lean_unsigned_to_nat(0u);
v___x_2158_ = lean_array_get_size(v_pairs_2155_);
v___x_2159_ = lean_nat_dec_lt(v___x_2157_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__1));
v___x_2161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2161_, 0, v_a_2156_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
return v___x_2161_;
}
else
{
lean_object* v___f_2162_; uint8_t v___x_2163_; 
v___f_2162_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__2));
v___x_2163_ = lean_nat_dec_le(v___x_2158_, v___x_2158_);
if (v___x_2163_ == 0)
{
if (v___x_2159_ == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__1));
v___x_2165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2165_, 0, v_a_2156_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
return v___x_2165_;
}
else
{
size_t v___x_2166_; size_t v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = ((size_t)0ULL);
v___x_2167_ = lean_usize_of_nat(v___x_2158_);
v___x_2168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_pairs_2155_, v___x_2166_, v___x_2167_, v___f_2162_, v_a_2156_);
return v___x_2168_;
}
}
else
{
size_t v___x_2169_; size_t v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = ((size_t)0ULL);
v___x_2170_ = lean_usize_of_nat(v___x_2158_);
v___x_2171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_pairs_2155_, v___x_2169_, v___x_2170_, v___f_2162_, v_a_2156_);
return v___x_2171_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___boxed(lean_object* v_pairs_2172_, lean_object* v_a_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2172_, v_a_2173_);
lean_dec_ref(v_pairs_2172_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols(lean_object* v_00_u03b1_2175_, lean_object* v_pairs_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2176_, v_a_2177_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___boxed(lean_object* v_00_u03b1_2179_, lean_object* v_pairs_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols(v_00_u03b1_2179_, v_pairs_2180_, v_a_2181_);
lean_dec_ref(v_pairs_2180_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0(lean_object* v_00_u03b1_2183_, lean_object* v_as_2184_, size_t v_i_2185_, size_t v_stop_2186_, lean_object* v_b_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_as_2184_, v_i_2185_, v_stop_2186_, v_b_2187_, v___y_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___boxed(lean_object* v_00_u03b1_2190_, lean_object* v_as_2191_, lean_object* v_i_2192_, lean_object* v_stop_2193_, lean_object* v_b_2194_, lean_object* v___y_2195_){
_start:
{
size_t v_i_boxed_2196_; size_t v_stop_boxed_2197_; lean_object* v_res_2198_; 
v_i_boxed_2196_ = lean_unbox_usize(v_i_2192_);
lean_dec(v_i_2192_);
v_stop_boxed_2197_ = lean_unbox_usize(v_stop_2193_);
lean_dec(v_stop_2193_);
v_res_2198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0(v_00_u03b1_2190_, v_as_2191_, v_i_boxed_2196_, v_stop_boxed_2197_, v_b_2194_, v___y_2195_);
lean_dec_ref(v_as_2191_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(size_t v_sz_2199_, size_t v_i_2200_, lean_object* v_bs_2201_){
_start:
{
uint8_t v___x_2202_; 
v___x_2202_ = lean_usize_dec_lt(v_i_2200_, v_sz_2199_);
if (v___x_2202_ == 0)
{
return v_bs_2201_;
}
else
{
lean_object* v_v_2203_; lean_object* v___x_2204_; lean_object* v_bs_x27_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; size_t v___x_2211_; size_t v___x_2212_; lean_object* v___x_2213_; 
v_v_2203_ = lean_array_uget(v_bs_2201_, v_i_2200_);
v___x_2204_ = lean_unsigned_to_nat(0u);
v_bs_x27_2205_ = lean_array_uset(v_bs_2201_, v_i_2200_, v___x_2204_);
v___x_2206_ = lean_usize_to_nat(v_i_2200_);
v___x_2207_ = lean_nat_to_int(v___x_2206_);
v___x_2208_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2209_ = lean_int_add(v___x_2207_, v___x_2208_);
lean_dec(v___x_2207_);
v___x_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2210_, 0, v_v_2203_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
v___x_2211_ = ((size_t)1ULL);
v___x_2212_ = lean_usize_add(v_i_2200_, v___x_2211_);
v___x_2213_ = lean_array_uset(v_bs_x27_2205_, v_i_2200_, v___x_2210_);
v_i_2200_ = v___x_2212_;
v_bs_2201_ = v___x_2213_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg___boxed(lean_object* v_sz_2215_, lean_object* v_i_2216_, lean_object* v_bs_2217_){
_start:
{
size_t v_sz_boxed_2218_; size_t v_i_boxed_2219_; lean_object* v_res_2220_; 
v_sz_boxed_2218_ = lean_unbox_usize(v_sz_2215_);
lean_dec(v_sz_2215_);
v_i_boxed_2219_ = lean_unbox_usize(v_i_2216_);
lean_dec(v_i_2216_);
v_res_2220_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_boxed_2218_, v_i_boxed_2219_, v_bs_2217_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(lean_object* v_as_2221_, size_t v_sz_2222_, size_t v_i_2223_, lean_object* v_bs_2224_){
_start:
{
uint8_t v___x_2225_; 
v___x_2225_ = lean_usize_dec_lt(v_i_2223_, v_sz_2222_);
if (v___x_2225_ == 0)
{
return v_bs_2224_;
}
else
{
lean_object* v_v_2226_; lean_object* v___x_2227_; lean_object* v_bs_x27_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; size_t v___x_2234_; size_t v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v_v_2226_ = lean_array_uget(v_bs_2224_, v_i_2223_);
v___x_2227_ = lean_unsigned_to_nat(0u);
v_bs_x27_2228_ = lean_array_uset(v_bs_2224_, v_i_2223_, v___x_2227_);
v___x_2229_ = lean_usize_to_nat(v_i_2223_);
v___x_2230_ = lean_nat_to_int(v___x_2229_);
v___x_2231_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2232_ = lean_int_add(v___x_2230_, v___x_2231_);
lean_dec(v___x_2230_);
v___x_2233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2233_, 0, v_v_2226_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
v___x_2234_ = ((size_t)1ULL);
v___x_2235_ = lean_usize_add(v_i_2223_, v___x_2234_);
v___x_2236_ = lean_array_uset(v_bs_x27_2228_, v_i_2223_, v___x_2233_);
v___x_2237_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_2222_, v___x_2235_, v___x_2236_);
return v___x_2237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0___boxed(lean_object* v_as_2238_, lean_object* v_sz_2239_, lean_object* v_i_2240_, lean_object* v_bs_2241_){
_start:
{
size_t v_sz_boxed_2242_; size_t v_i_boxed_2243_; lean_object* v_res_2244_; 
v_sz_boxed_2242_ = lean_unbox_usize(v_sz_2239_);
lean_dec(v_sz_2239_);
v_i_boxed_2243_ = lean_unbox_usize(v_i_2240_);
lean_dec(v_i_2240_);
v_res_2244_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_as_2238_, v_sz_boxed_2242_, v_i_boxed_2243_, v_bs_2241_);
lean_dec_ref(v_as_2238_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(lean_object* v_arr_2245_){
_start:
{
size_t v_sz_2246_; size_t v___x_2247_; lean_object* v___x_2248_; 
v_sz_2246_ = lean_array_size(v_arr_2245_);
v___x_2247_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2245_);
v___x_2248_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_arr_2245_, v_sz_2246_, v___x_2247_, v_arr_2245_);
lean_dec_ref(v_arr_2245_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0(lean_object* v_as_2249_, size_t v_sz_2250_, size_t v_i_2251_, lean_object* v_bs_2252_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_2250_, v_i_2251_, v_bs_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___boxed(lean_object* v_as_2254_, lean_object* v_sz_2255_, lean_object* v_i_2256_, lean_object* v_bs_2257_){
_start:
{
size_t v_sz_boxed_2258_; size_t v_i_boxed_2259_; lean_object* v_res_2260_; 
v_sz_boxed_2258_ = lean_unbox_usize(v_sz_2255_);
lean_dec(v_sz_2255_);
v_i_boxed_2259_ = lean_unbox_usize(v_i_2256_);
lean_dec(v_i_2256_);
v_res_2260_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0(v_as_2254_, v_sz_boxed_2258_, v_i_boxed_2259_, v_bs_2257_);
lean_dec_ref(v_as_2254_);
return v_res_2260_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(lean_object* v_x_2261_){
_start:
{
lean_object* v___x_2262_; uint8_t v___x_2263_; 
v___x_2262_ = lean_unsigned_to_nat(0u);
v___x_2263_ = lean_nat_dec_eq(v_x_2261_, v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; uint8_t v___x_2265_; 
v___x_2264_ = lean_unsigned_to_nat(1u);
v___x_2265_ = lean_nat_dec_eq(v_x_2261_, v___x_2264_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2266_; uint8_t v___x_2267_; 
v___x_2266_ = lean_unsigned_to_nat(2u);
v___x_2267_ = lean_nat_dec_eq(v_x_2261_, v___x_2266_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; uint8_t v___x_2269_; 
v___x_2268_ = lean_unsigned_to_nat(3u);
v___x_2269_ = lean_nat_dec_eq(v_x_2261_, v___x_2268_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; uint8_t v___x_2271_; 
v___x_2270_ = lean_unsigned_to_nat(4u);
v___x_2271_ = lean_nat_dec_eq(v_x_2261_, v___x_2270_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2272_ = lean_unsigned_to_nat(5u);
v___x_2273_ = lean_nat_dec_eq(v_x_2261_, v___x_2272_);
if (v___x_2273_ == 0)
{
uint8_t v___x_2274_; 
v___x_2274_ = 5;
return v___x_2274_;
}
else
{
uint8_t v___x_2275_; 
v___x_2275_ = 4;
return v___x_2275_;
}
}
else
{
uint8_t v___x_2276_; 
v___x_2276_ = 3;
return v___x_2276_;
}
}
else
{
uint8_t v___x_2277_; 
v___x_2277_ = 2;
return v___x_2277_;
}
}
else
{
uint8_t v___x_2278_; 
v___x_2278_ = 1;
return v___x_2278_;
}
}
else
{
uint8_t v___x_2279_; 
v___x_2279_ = 0;
return v___x_2279_;
}
}
else
{
uint8_t v___x_2280_; 
v___x_2280_ = 6;
return v___x_2280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex___boxed(lean_object* v_x_2281_){
_start:
{
uint8_t v_res_2282_; lean_object* v_r_2283_; 
v_res_2282_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(v_x_2281_);
lean_dec(v_x_2281_);
v_r_2283_ = lean_box(v_res_2282_);
return v_r_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(size_t v_sz_2284_, size_t v_i_2285_, lean_object* v_bs_2286_){
_start:
{
uint8_t v___x_2287_; 
v___x_2287_ = lean_usize_dec_lt(v_i_2285_, v_sz_2284_);
if (v___x_2287_ == 0)
{
return v_bs_2286_;
}
else
{
lean_object* v_v_2288_; lean_object* v___x_2289_; lean_object* v_bs_x27_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; size_t v___x_2298_; size_t v___x_2299_; lean_object* v___x_2300_; 
v_v_2288_ = lean_array_uget(v_bs_2286_, v_i_2285_);
v___x_2289_ = lean_unsigned_to_nat(0u);
v_bs_x27_2290_ = lean_array_uset(v_bs_2286_, v_i_2285_, v___x_2289_);
v___x_2291_ = lean_usize_to_nat(v_i_2285_);
v___x_2292_ = lean_nat_to_int(v___x_2291_);
v___x_2293_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2294_ = lean_int_add(v___x_2292_, v___x_2293_);
lean_dec(v___x_2292_);
v___x_2295_ = l_Std_Time_Weekday_ofOrdinal(v___x_2294_);
lean_dec(v___x_2294_);
v___x_2296_ = lean_box(v___x_2295_);
v___x_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2297_, 0, v_v_2288_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = ((size_t)1ULL);
v___x_2299_ = lean_usize_add(v_i_2285_, v___x_2298_);
v___x_2300_ = lean_array_uset(v_bs_x27_2290_, v_i_2285_, v___x_2297_);
v_i_2285_ = v___x_2299_;
v_bs_2286_ = v___x_2300_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg___boxed(lean_object* v_sz_2302_, lean_object* v_i_2303_, lean_object* v_bs_2304_){
_start:
{
size_t v_sz_boxed_2305_; size_t v_i_boxed_2306_; lean_object* v_res_2307_; 
v_sz_boxed_2305_ = lean_unbox_usize(v_sz_2302_);
lean_dec(v_sz_2302_);
v_i_boxed_2306_ = lean_unbox_usize(v_i_2303_);
lean_dec(v_i_2303_);
v_res_2307_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_boxed_2305_, v_i_boxed_2306_, v_bs_2304_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(lean_object* v_as_2308_, size_t v_sz_2309_, size_t v_i_2310_, lean_object* v_bs_2311_){
_start:
{
uint8_t v___x_2312_; 
v___x_2312_ = lean_usize_dec_lt(v_i_2310_, v_sz_2309_);
if (v___x_2312_ == 0)
{
return v_bs_2311_;
}
else
{
lean_object* v_v_2313_; lean_object* v___x_2314_; lean_object* v_bs_x27_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; size_t v___x_2323_; size_t v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_v_2313_ = lean_array_uget(v_bs_2311_, v_i_2310_);
v___x_2314_ = lean_unsigned_to_nat(0u);
v_bs_x27_2315_ = lean_array_uset(v_bs_2311_, v_i_2310_, v___x_2314_);
v___x_2316_ = lean_usize_to_nat(v_i_2310_);
v___x_2317_ = lean_nat_to_int(v___x_2316_);
v___x_2318_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2319_ = lean_int_add(v___x_2317_, v___x_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = l_Std_Time_Weekday_ofOrdinal(v___x_2319_);
lean_dec(v___x_2319_);
v___x_2321_ = lean_box(v___x_2320_);
v___x_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2322_, 0, v_v_2313_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = ((size_t)1ULL);
v___x_2324_ = lean_usize_add(v_i_2310_, v___x_2323_);
v___x_2325_ = lean_array_uset(v_bs_x27_2315_, v_i_2310_, v___x_2322_);
v___x_2326_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_2309_, v___x_2324_, v___x_2325_);
return v___x_2326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0___boxed(lean_object* v_as_2327_, lean_object* v_sz_2328_, lean_object* v_i_2329_, lean_object* v_bs_2330_){
_start:
{
size_t v_sz_boxed_2331_; size_t v_i_boxed_2332_; lean_object* v_res_2333_; 
v_sz_boxed_2331_ = lean_unbox_usize(v_sz_2328_);
lean_dec(v_sz_2328_);
v_i_boxed_2332_ = lean_unbox_usize(v_i_2329_);
lean_dec(v_i_2329_);
v_res_2333_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(v_as_2327_, v_sz_boxed_2331_, v_i_boxed_2332_, v_bs_2330_);
lean_dec_ref(v_as_2327_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(lean_object* v_arr_2334_){
_start:
{
size_t v_sz_2335_; size_t v___x_2336_; lean_object* v___x_2337_; 
v_sz_2335_ = lean_array_size(v_arr_2334_);
v___x_2336_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2334_);
v___x_2337_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(v_arr_2334_, v_sz_2335_, v___x_2336_, v_arr_2334_);
lean_dec_ref(v_arr_2334_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0(lean_object* v_as_2338_, size_t v_sz_2339_, size_t v_i_2340_, lean_object* v_bs_2341_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_2339_, v_i_2340_, v_bs_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___boxed(lean_object* v_as_2343_, lean_object* v_sz_2344_, lean_object* v_i_2345_, lean_object* v_bs_2346_){
_start:
{
size_t v_sz_boxed_2347_; size_t v_i_boxed_2348_; lean_object* v_res_2349_; 
v_sz_boxed_2347_ = lean_unbox_usize(v_sz_2344_);
lean_dec(v_sz_2344_);
v_i_boxed_2348_ = lean_unbox_usize(v_i_2345_);
lean_dec(v_i_2345_);
v_res_2349_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0(v_as_2343_, v_sz_boxed_2347_, v_i_boxed_2348_, v_bs_2346_);
lean_dec_ref(v_as_2343_);
return v_res_2349_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(lean_object* v_x_2350_){
_start:
{
lean_object* v___x_2351_; uint8_t v___x_2352_; 
v___x_2351_ = lean_unsigned_to_nat(0u);
v___x_2352_ = lean_nat_dec_eq(v_x_2350_, v___x_2351_);
if (v___x_2352_ == 0)
{
uint8_t v___x_2353_; 
v___x_2353_ = 1;
return v___x_2353_;
}
else
{
uint8_t v___x_2354_; 
v___x_2354_ = 0;
return v___x_2354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex___boxed(lean_object* v_x_2355_){
_start:
{
uint8_t v_res_2356_; lean_object* v_r_2357_; 
v_res_2356_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(v_x_2355_);
lean_dec(v_x_2355_);
v_r_2357_ = lean_box(v_res_2356_);
return v_r_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(size_t v_sz_2358_, size_t v_i_2359_, lean_object* v_bs_2360_){
_start:
{
uint8_t v___x_2361_; 
v___x_2361_ = lean_usize_dec_lt(v_i_2359_, v_sz_2358_);
if (v___x_2361_ == 0)
{
return v_bs_2360_;
}
else
{
lean_object* v_v_2362_; lean_object* v___x_2363_; lean_object* v_bs_x27_2364_; lean_object* v___x_2365_; uint8_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; size_t v___x_2369_; size_t v___x_2370_; lean_object* v___x_2371_; 
v_v_2362_ = lean_array_uget(v_bs_2360_, v_i_2359_);
v___x_2363_ = lean_unsigned_to_nat(0u);
v_bs_x27_2364_ = lean_array_uset(v_bs_2360_, v_i_2359_, v___x_2363_);
v___x_2365_ = lean_usize_to_nat(v_i_2359_);
v___x_2366_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(v___x_2365_);
lean_dec(v___x_2365_);
v___x_2367_ = lean_box(v___x_2366_);
v___x_2368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2368_, 0, v_v_2362_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
v___x_2369_ = ((size_t)1ULL);
v___x_2370_ = lean_usize_add(v_i_2359_, v___x_2369_);
v___x_2371_ = lean_array_uset(v_bs_x27_2364_, v_i_2359_, v___x_2368_);
v_i_2359_ = v___x_2370_;
v_bs_2360_ = v___x_2371_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg___boxed(lean_object* v_sz_2373_, lean_object* v_i_2374_, lean_object* v_bs_2375_){
_start:
{
size_t v_sz_boxed_2376_; size_t v_i_boxed_2377_; lean_object* v_res_2378_; 
v_sz_boxed_2376_ = lean_unbox_usize(v_sz_2373_);
lean_dec(v_sz_2373_);
v_i_boxed_2377_ = lean_unbox_usize(v_i_2374_);
lean_dec(v_i_2374_);
v_res_2378_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_boxed_2376_, v_i_boxed_2377_, v_bs_2375_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(lean_object* v_arr_2379_){
_start:
{
size_t v_sz_2380_; size_t v___x_2381_; lean_object* v___x_2382_; 
v_sz_2380_ = lean_array_size(v_arr_2379_);
v___x_2381_ = ((size_t)0ULL);
v___x_2382_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_2380_, v___x_2381_, v_arr_2379_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0(lean_object* v_as_2383_, size_t v_sz_2384_, size_t v_i_2385_, lean_object* v_bs_2386_){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_2384_, v_i_2385_, v_bs_2386_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___boxed(lean_object* v_as_2388_, lean_object* v_sz_2389_, lean_object* v_i_2390_, lean_object* v_bs_2391_){
_start:
{
size_t v_sz_boxed_2392_; size_t v_i_boxed_2393_; lean_object* v_res_2394_; 
v_sz_boxed_2392_ = lean_unbox_usize(v_sz_2389_);
lean_dec(v_sz_2389_);
v_i_boxed_2393_ = lean_unbox_usize(v_i_2390_);
lean_dec(v_i_2390_);
v_res_2394_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0(v_as_2388_, v_sz_boxed_2392_, v_i_boxed_2393_, v_bs_2391_);
lean_dec_ref(v_as_2388_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(lean_object* v_arr_2395_){
_start:
{
size_t v_sz_2396_; size_t v___x_2397_; lean_object* v___x_2398_; 
v_sz_2396_ = lean_array_size(v_arr_2395_);
v___x_2397_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2395_);
v___x_2398_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_arr_2395_, v_sz_2396_, v___x_2397_, v_arr_2395_);
lean_dec_ref(v_arr_2395_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(lean_object* v_symbols_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v_monthLong_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v_monthLong_2401_ = lean_ctor_get(v_symbols_2399_, 0);
lean_inc_ref(v_monthLong_2401_);
lean_dec_ref(v_symbols_2399_);
v___x_2402_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthLong_2401_);
v___x_2403_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2402_, v_a_2400_);
lean_dec_ref(v___x_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseMonthShort(lean_object* v_symbols_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v_monthShort_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v_monthShort_2406_ = lean_ctor_get(v_symbols_2404_, 1);
lean_inc_ref(v_monthShort_2406_);
lean_dec_ref(v_symbols_2404_);
v___x_2407_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthShort_2406_);
v___x_2408_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2407_, v_a_2405_);
lean_dec_ref(v___x_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(lean_object* v_symbols_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v_monthNarrow_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v_monthNarrow_2411_ = lean_ctor_get(v_symbols_2409_, 2);
lean_inc_ref(v_monthNarrow_2411_);
lean_dec_ref(v_symbols_2409_);
v___x_2412_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthNarrow_2411_);
v___x_2413_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2412_, v_a_2410_);
lean_dec_ref(v___x_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(lean_object* v_symbols_2414_, lean_object* v_a_2415_){
_start:
{
lean_object* v_weekdayLong_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v_weekdayLong_2416_ = lean_ctor_get(v_symbols_2414_, 3);
lean_inc_ref(v_weekdayLong_2416_);
lean_dec_ref(v_symbols_2414_);
v___x_2417_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayLong_2416_);
v___x_2418_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2417_, v_a_2415_);
lean_dec_ref(v___x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(lean_object* v_symbols_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v_weekdayShort_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v_weekdayShort_2421_ = lean_ctor_get(v_symbols_2419_, 4);
lean_inc_ref(v_weekdayShort_2421_);
lean_dec_ref(v_symbols_2419_);
v___x_2422_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayShort_2421_);
v___x_2423_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2422_, v_a_2420_);
lean_dec_ref(v___x_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(lean_object* v_symbols_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_weekdayNarrow_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v_weekdayNarrow_2426_ = lean_ctor_get(v_symbols_2424_, 5);
lean_inc_ref(v_weekdayNarrow_2426_);
lean_dec_ref(v_symbols_2424_);
v___x_2427_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayNarrow_2426_);
v___x_2428_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2427_, v_a_2425_);
lean_dec_ref(v___x_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(lean_object* v_symbols_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v_weekdayTwoLetter_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v_weekdayTwoLetter_2431_ = lean_ctor_get(v_symbols_2429_, 6);
lean_inc_ref(v_weekdayTwoLetter_2431_);
lean_dec_ref(v_symbols_2429_);
v___x_2432_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayTwoLetter_2431_);
v___x_2433_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2432_, v_a_2430_);
lean_dec_ref(v___x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraShort(lean_object* v_symbols_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v_eraShort_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v_eraShort_2436_ = lean_ctor_get(v_symbols_2434_, 7);
lean_inc_ref(v_eraShort_2436_);
lean_dec_ref(v_symbols_2434_);
v___x_2437_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraShort_2436_);
v___x_2438_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2437_, v_a_2435_);
lean_dec_ref(v___x_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraLong(lean_object* v_symbols_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v_eraLong_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v_eraLong_2441_ = lean_ctor_get(v_symbols_2439_, 8);
lean_inc_ref(v_eraLong_2441_);
lean_dec_ref(v_symbols_2439_);
v___x_2442_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraLong_2441_);
v___x_2443_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2442_, v_a_2440_);
lean_dec_ref(v___x_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraNarrow(lean_object* v_symbols_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v_eraNarrow_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v_eraNarrow_2446_ = lean_ctor_get(v_symbols_2444_, 9);
lean_inc_ref(v_eraNarrow_2446_);
lean_dec_ref(v_symbols_2444_);
v___x_2447_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraNarrow_2446_);
v___x_2448_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2447_, v_a_2445_);
lean_dec_ref(v___x_2447_);
return v___x_2448_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = lean_unsigned_to_nat(3u);
v___x_2450_ = lean_nat_to_int(v___x_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber(lean_object* v_a_2451_){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__0));
lean_inc_ref(v_a_2451_);
v___x_2453_ = l_Std_Internal_Parsec_String_pstring(v___x_2452_, v_a_2451_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_pos_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2462_; 
lean_dec_ref(v_a_2451_);
v_pos_2454_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2462_ == 0)
{
lean_object* v_unused_2463_; 
v_unused_2463_ = lean_ctor_get(v___x_2453_, 1);
lean_dec(v_unused_2463_);
v___x_2456_ = v___x_2453_;
v_isShared_2457_ = v_isSharedCheck_2462_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_pos_2454_);
lean_dec(v___x_2453_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2462_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2458_; lean_object* v___x_2460_; 
v___x_2458_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 1, v___x_2458_);
v___x_2460_ = v___x_2456_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_pos_2454_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v___x_2458_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
else
{
lean_object* v_pos_2464_; lean_object* v_err_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2542_; 
v_pos_2464_ = lean_ctor_get(v___x_2453_, 0);
v_err_2465_ = lean_ctor_get(v___x_2453_, 1);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2467_ = v___x_2453_;
v_isShared_2468_ = v_isSharedCheck_2542_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_err_2465_);
lean_inc(v_pos_2464_);
lean_dec(v___x_2453_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2542_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v_snd_2469_; lean_object* v_snd_2470_; uint8_t v___x_2471_; 
v_snd_2469_ = lean_ctor_get(v_a_2451_, 1);
lean_inc(v_snd_2469_);
lean_dec_ref(v_a_2451_);
v_snd_2470_ = lean_ctor_get(v_pos_2464_, 1);
v___x_2471_ = lean_nat_dec_eq(v_snd_2469_, v_snd_2470_);
lean_dec(v_snd_2469_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2473_; 
if (v_isShared_2468_ == 0)
{
v___x_2473_ = v___x_2467_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_pos_2464_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v_err_2465_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
else
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
lean_inc(v_snd_2470_);
lean_del_object(v___x_2467_);
lean_dec(v_err_2465_);
v___x_2475_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__1));
v___x_2476_ = l_Std_Internal_Parsec_String_pstring(v___x_2475_, v_pos_2464_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_pos_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2485_; 
lean_dec(v_snd_2470_);
v_pos_2477_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2485_ == 0)
{
lean_object* v_unused_2486_; 
v_unused_2486_ = lean_ctor_get(v___x_2476_, 1);
lean_dec(v_unused_2486_);
v___x_2479_ = v___x_2476_;
v_isShared_2480_ = v_isSharedCheck_2485_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_pos_2477_);
lean_dec(v___x_2476_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2485_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2481_; lean_object* v___x_2483_; 
v___x_2481_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__3, &l_Std_Time_instReprFormatPart_repr___closed__3_once, _init_l_Std_Time_instReprFormatPart_repr___closed__3);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 1, v___x_2481_);
v___x_2483_ = v___x_2479_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_pos_2477_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
else
{
lean_object* v_pos_2487_; lean_object* v_err_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2541_; 
v_pos_2487_ = lean_ctor_get(v___x_2476_, 0);
v_err_2488_ = lean_ctor_get(v___x_2476_, 1);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2490_ = v___x_2476_;
v_isShared_2491_ = v_isSharedCheck_2541_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_err_2488_);
lean_inc(v_pos_2487_);
lean_dec(v___x_2476_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2541_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v_snd_2492_; uint8_t v___x_2493_; 
v_snd_2492_ = lean_ctor_get(v_pos_2487_, 1);
v___x_2493_ = lean_nat_dec_eq(v_snd_2470_, v_snd_2492_);
lean_dec(v_snd_2470_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2495_; 
if (v_isShared_2491_ == 0)
{
v___x_2495_ = v___x_2490_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_pos_2487_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_err_2488_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
else
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
lean_inc(v_snd_2492_);
lean_del_object(v___x_2490_);
lean_dec(v_err_2488_);
v___x_2497_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__2));
v___x_2498_ = l_Std_Internal_Parsec_String_pstring(v___x_2497_, v_pos_2487_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_pos_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v_snd_2492_);
v_pos_2499_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2507_ == 0)
{
lean_object* v_unused_2508_; 
v_unused_2508_ = lean_ctor_get(v___x_2498_, 1);
lean_dec(v_unused_2508_);
v___x_2501_ = v___x_2498_;
v_isShared_2502_ = v_isSharedCheck_2507_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_pos_2499_);
lean_dec(v___x_2498_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2507_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2503_; lean_object* v___x_2505_; 
v___x_2503_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v___x_2503_);
v___x_2505_ = v___x_2501_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_pos_2499_);
lean_ctor_set(v_reuseFailAlloc_2506_, 1, v___x_2503_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
else
{
lean_object* v_pos_2509_; lean_object* v_err_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2540_; 
v_pos_2509_ = lean_ctor_get(v___x_2498_, 0);
v_err_2510_ = lean_ctor_get(v___x_2498_, 1);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2512_ = v___x_2498_;
v_isShared_2513_ = v_isSharedCheck_2540_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_err_2510_);
lean_inc(v_pos_2509_);
lean_dec(v___x_2498_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2540_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v_snd_2514_; uint8_t v___x_2515_; 
v_snd_2514_ = lean_ctor_get(v_pos_2509_, 1);
v___x_2515_ = lean_nat_dec_eq(v_snd_2492_, v_snd_2514_);
lean_dec(v_snd_2492_);
if (v___x_2515_ == 0)
{
lean_object* v___x_2517_; 
if (v_isShared_2513_ == 0)
{
v___x_2517_ = v___x_2512_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_pos_2509_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_err_2510_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
else
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
lean_del_object(v___x_2512_);
lean_dec(v_err_2510_);
v___x_2519_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__3));
v___x_2520_ = l_Std_Internal_Parsec_String_pstring(v___x_2519_, v_pos_2509_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_pos_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2529_; 
v_pos_2521_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2529_ == 0)
{
lean_object* v_unused_2530_; 
v_unused_2530_ = lean_ctor_get(v___x_2520_, 1);
lean_dec(v_unused_2530_);
v___x_2523_ = v___x_2520_;
v_isShared_2524_ = v_isSharedCheck_2529_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_pos_2521_);
lean_dec(v___x_2520_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2529_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2525_; lean_object* v___x_2527_; 
v___x_2525_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 1, v___x_2525_);
v___x_2527_ = v___x_2523_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_pos_2521_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v___x_2525_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
else
{
lean_object* v_pos_2531_; lean_object* v_err_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
v_pos_2531_ = lean_ctor_get(v___x_2520_, 0);
v_err_2532_ = lean_ctor_get(v___x_2520_, 1);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2520_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_err_2532_);
lean_inc(v_pos_2531_);
lean_dec(v___x_2520_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_pos_2531_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_err_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
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
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(lean_object* v_symbols_2543_, lean_object* v_a_2544_){
_start:
{
lean_object* v_quarterLong_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v_quarterLong_2545_ = lean_ctor_get(v_symbols_2543_, 11);
lean_inc_ref(v_quarterLong_2545_);
lean_dec_ref(v_symbols_2543_);
v___x_2546_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterLong_2545_);
v___x_2547_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2546_, v_a_2544_);
lean_dec_ref(v___x_2546_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(lean_object* v_symbols_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v_quarterShort_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v_quarterShort_2550_ = lean_ctor_get(v_symbols_2548_, 10);
lean_inc_ref(v_quarterShort_2550_);
lean_dec_ref(v_symbols_2548_);
v___x_2551_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterShort_2550_);
v___x_2552_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2551_, v_a_2549_);
lean_dec_ref(v___x_2551_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(lean_object* v_symbols_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v_quarterNarrow_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v_quarterNarrow_2555_ = lean_ctor_get(v_symbols_2553_, 12);
lean_inc_ref(v_quarterNarrow_2555_);
lean_dec_ref(v_symbols_2553_);
v___x_2556_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterNarrow_2555_);
v___x_2557_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2556_, v_a_2554_);
lean_dec_ref(v___x_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerShort(lean_object* v_symbols_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v_amShort_2560_; lean_object* v_pmShort_2561_; lean_object* v___x_2562_; 
v_amShort_2560_ = lean_ctor_get(v_symbols_2558_, 13);
lean_inc_ref(v_amShort_2560_);
v_pmShort_2561_ = lean_ctor_get(v_symbols_2558_, 14);
lean_inc_ref(v_pmShort_2561_);
lean_dec_ref(v_symbols_2558_);
lean_inc_ref(v_a_2559_);
v___x_2562_ = l_Std_Internal_Parsec_String_pstring(v_amShort_2560_, v_a_2559_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_pos_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2572_; 
lean_dec_ref(v_pmShort_2561_);
lean_dec_ref(v_a_2559_);
v_pos_2563_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2572_ == 0)
{
lean_object* v_unused_2573_; 
v_unused_2573_ = lean_ctor_get(v___x_2562_, 1);
lean_dec(v_unused_2573_);
v___x_2565_ = v___x_2562_;
v_isShared_2566_ = v_isSharedCheck_2572_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_pos_2563_);
lean_dec(v___x_2562_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2572_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
uint8_t v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2570_; 
v___x_2567_ = 0;
v___x_2568_ = lean_box(v___x_2567_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 1, v___x_2568_);
v___x_2570_ = v___x_2565_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_pos_2563_);
lean_ctor_set(v_reuseFailAlloc_2571_, 1, v___x_2568_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
else
{
lean_object* v_pos_2574_; lean_object* v_err_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2606_; 
v_pos_2574_ = lean_ctor_get(v___x_2562_, 0);
v_err_2575_ = lean_ctor_get(v___x_2562_, 1);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2577_ = v___x_2562_;
v_isShared_2578_ = v_isSharedCheck_2606_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_err_2575_);
lean_inc(v_pos_2574_);
lean_dec(v___x_2562_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2606_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v_snd_2579_; lean_object* v_snd_2580_; uint8_t v___x_2581_; 
v_snd_2579_ = lean_ctor_get(v_a_2559_, 1);
lean_inc(v_snd_2579_);
lean_dec_ref(v_a_2559_);
v_snd_2580_ = lean_ctor_get(v_pos_2574_, 1);
v___x_2581_ = lean_nat_dec_eq(v_snd_2579_, v_snd_2580_);
lean_dec(v_snd_2579_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2583_; 
lean_dec_ref(v_pmShort_2561_);
if (v_isShared_2578_ == 0)
{
v___x_2583_ = v___x_2577_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_pos_2574_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v_err_2575_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
else
{
lean_object* v___x_2585_; 
lean_del_object(v___x_2577_);
lean_dec(v_err_2575_);
v___x_2585_ = l_Std_Internal_Parsec_String_pstring(v_pmShort_2561_, v_pos_2574_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_pos_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2595_; 
v_pos_2586_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2595_ == 0)
{
lean_object* v_unused_2596_; 
v_unused_2596_ = lean_ctor_get(v___x_2585_, 1);
lean_dec(v_unused_2596_);
v___x_2588_ = v___x_2585_;
v_isShared_2589_ = v_isSharedCheck_2595_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_pos_2586_);
lean_dec(v___x_2585_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2595_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
uint8_t v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2593_; 
v___x_2590_ = 1;
v___x_2591_ = lean_box(v___x_2590_);
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 1, v___x_2591_);
v___x_2593_ = v___x_2588_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_pos_2586_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
else
{
lean_object* v_pos_2597_; lean_object* v_err_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
v_pos_2597_ = lean_ctor_get(v___x_2585_, 0);
v_err_2598_ = lean_ctor_get(v___x_2585_, 1);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2585_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_err_2598_);
lean_inc(v_pos_2597_);
lean_dec(v___x_2585_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_pos_2597_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_err_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerLong(lean_object* v_symbols_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v_amLong_2609_; lean_object* v_pmLong_2610_; lean_object* v___x_2611_; 
v_amLong_2609_ = lean_ctor_get(v_symbols_2607_, 15);
lean_inc_ref(v_amLong_2609_);
v_pmLong_2610_ = lean_ctor_get(v_symbols_2607_, 16);
lean_inc_ref(v_pmLong_2610_);
lean_dec_ref(v_symbols_2607_);
lean_inc_ref(v_a_2608_);
v___x_2611_ = l_Std_Internal_Parsec_String_pstring(v_amLong_2609_, v_a_2608_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_pos_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2621_; 
lean_dec_ref(v_pmLong_2610_);
lean_dec_ref(v_a_2608_);
v_pos_2612_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2621_ == 0)
{
lean_object* v_unused_2622_; 
v_unused_2622_ = lean_ctor_get(v___x_2611_, 1);
lean_dec(v_unused_2622_);
v___x_2614_ = v___x_2611_;
v_isShared_2615_ = v_isSharedCheck_2621_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_pos_2612_);
lean_dec(v___x_2611_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2621_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
uint8_t v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2619_; 
v___x_2616_ = 0;
v___x_2617_ = lean_box(v___x_2616_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 1, v___x_2617_);
v___x_2619_ = v___x_2614_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_pos_2612_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v___x_2617_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
else
{
lean_object* v_pos_2623_; lean_object* v_err_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2655_; 
v_pos_2623_ = lean_ctor_get(v___x_2611_, 0);
v_err_2624_ = lean_ctor_get(v___x_2611_, 1);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2626_ = v___x_2611_;
v_isShared_2627_ = v_isSharedCheck_2655_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_err_2624_);
lean_inc(v_pos_2623_);
lean_dec(v___x_2611_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2655_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v_snd_2628_; lean_object* v_snd_2629_; uint8_t v___x_2630_; 
v_snd_2628_ = lean_ctor_get(v_a_2608_, 1);
lean_inc(v_snd_2628_);
lean_dec_ref(v_a_2608_);
v_snd_2629_ = lean_ctor_get(v_pos_2623_, 1);
v___x_2630_ = lean_nat_dec_eq(v_snd_2628_, v_snd_2629_);
lean_dec(v_snd_2628_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2632_; 
lean_dec_ref(v_pmLong_2610_);
if (v_isShared_2627_ == 0)
{
v___x_2632_ = v___x_2626_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_pos_2623_);
lean_ctor_set(v_reuseFailAlloc_2633_, 1, v_err_2624_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
else
{
lean_object* v___x_2634_; 
lean_del_object(v___x_2626_);
lean_dec(v_err_2624_);
v___x_2634_ = l_Std_Internal_Parsec_String_pstring(v_pmLong_2610_, v_pos_2623_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_pos_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2644_; 
v_pos_2635_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2644_ == 0)
{
lean_object* v_unused_2645_; 
v_unused_2645_ = lean_ctor_get(v___x_2634_, 1);
lean_dec(v_unused_2645_);
v___x_2637_ = v___x_2634_;
v_isShared_2638_ = v_isSharedCheck_2644_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_pos_2635_);
lean_dec(v___x_2634_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2644_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
uint8_t v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2642_; 
v___x_2639_ = 1;
v___x_2640_ = lean_box(v___x_2639_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 1, v___x_2640_);
v___x_2642_ = v___x_2637_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_pos_2635_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v___x_2640_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
else
{
lean_object* v_pos_2646_; lean_object* v_err_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
v_pos_2646_ = lean_ctor_get(v___x_2634_, 0);
v_err_2647_ = lean_ctor_get(v___x_2634_, 1);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2634_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_err_2647_);
lean_inc(v_pos_2646_);
lean_dec(v___x_2634_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_pos_2646_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_err_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerNarrow(lean_object* v_symbols_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v_amNarrow_2658_; lean_object* v_pmNarrow_2659_; lean_object* v___x_2660_; 
v_amNarrow_2658_ = lean_ctor_get(v_symbols_2656_, 17);
lean_inc_ref(v_amNarrow_2658_);
v_pmNarrow_2659_ = lean_ctor_get(v_symbols_2656_, 18);
lean_inc_ref(v_pmNarrow_2659_);
lean_dec_ref(v_symbols_2656_);
lean_inc_ref(v_a_2657_);
v___x_2660_ = l_Std_Internal_Parsec_String_pstring(v_amNarrow_2658_, v_a_2657_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_pos_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2670_; 
lean_dec_ref(v_pmNarrow_2659_);
lean_dec_ref(v_a_2657_);
v_pos_2661_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2670_ == 0)
{
lean_object* v_unused_2671_; 
v_unused_2671_ = lean_ctor_get(v___x_2660_, 1);
lean_dec(v_unused_2671_);
v___x_2663_ = v___x_2660_;
v_isShared_2664_ = v_isSharedCheck_2670_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_pos_2661_);
lean_dec(v___x_2660_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2670_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
uint8_t v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2668_; 
v___x_2665_ = 0;
v___x_2666_ = lean_box(v___x_2665_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 1, v___x_2666_);
v___x_2668_ = v___x_2663_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_pos_2661_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v___x_2666_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
else
{
lean_object* v_pos_2672_; lean_object* v_err_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2704_; 
v_pos_2672_ = lean_ctor_get(v___x_2660_, 0);
v_err_2673_ = lean_ctor_get(v___x_2660_, 1);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2675_ = v___x_2660_;
v_isShared_2676_ = v_isSharedCheck_2704_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_err_2673_);
lean_inc(v_pos_2672_);
lean_dec(v___x_2660_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2704_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v_snd_2677_; lean_object* v_snd_2678_; uint8_t v___x_2679_; 
v_snd_2677_ = lean_ctor_get(v_a_2657_, 1);
lean_inc(v_snd_2677_);
lean_dec_ref(v_a_2657_);
v_snd_2678_ = lean_ctor_get(v_pos_2672_, 1);
v___x_2679_ = lean_nat_dec_eq(v_snd_2677_, v_snd_2678_);
lean_dec(v_snd_2677_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2681_; 
lean_dec_ref(v_pmNarrow_2659_);
if (v_isShared_2676_ == 0)
{
v___x_2681_ = v___x_2675_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_pos_2672_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_err_2673_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
else
{
lean_object* v___x_2683_; 
lean_del_object(v___x_2675_);
lean_dec(v_err_2673_);
v___x_2683_ = l_Std_Internal_Parsec_String_pstring(v_pmNarrow_2659_, v_pos_2672_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_pos_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2693_; 
v_pos_2684_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2693_ == 0)
{
lean_object* v_unused_2694_; 
v_unused_2694_ = lean_ctor_get(v___x_2683_, 1);
lean_dec(v_unused_2694_);
v___x_2686_ = v___x_2683_;
v_isShared_2687_ = v_isSharedCheck_2693_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_pos_2684_);
lean_dec(v___x_2683_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2693_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
uint8_t v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2691_; 
v___x_2688_ = 1;
v___x_2689_ = lean_box(v___x_2688_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 1, v___x_2689_);
v___x_2691_ = v___x_2686_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_pos_2684_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v___x_2689_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
else
{
lean_object* v_pos_2695_; lean_object* v_err_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
v_pos_2695_ = lean_ctor_get(v___x_2683_, 0);
v_err_2696_ = lean_ctor_get(v___x_2683_, 1);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2683_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_err_2696_);
lean_inc(v_pos_2695_);
lean_dec(v___x_2683_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_pos_2695_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v_err_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(lean_object* v_dp_2705_, lean_object* v_a_2706_){
_start:
{
lean_object* v_am_2707_; lean_object* v_pm_2708_; lean_object* v_noon_2709_; lean_object* v_midnight_2710_; lean_object* v___x_2711_; 
v_am_2707_ = lean_ctor_get(v_dp_2705_, 0);
lean_inc_ref(v_am_2707_);
v_pm_2708_ = lean_ctor_get(v_dp_2705_, 1);
lean_inc_ref(v_pm_2708_);
v_noon_2709_ = lean_ctor_get(v_dp_2705_, 2);
lean_inc_ref(v_noon_2709_);
v_midnight_2710_ = lean_ctor_get(v_dp_2705_, 3);
lean_inc_ref(v_midnight_2710_);
lean_dec_ref(v_dp_2705_);
lean_inc_ref(v_a_2706_);
v___x_2711_ = l_Std_Internal_Parsec_String_pstring(v_midnight_2710_, v_a_2706_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_pos_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2721_; 
lean_dec_ref(v_noon_2709_);
lean_dec_ref(v_pm_2708_);
lean_dec_ref(v_am_2707_);
lean_dec_ref(v_a_2706_);
v_pos_2712_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2721_ == 0)
{
lean_object* v_unused_2722_; 
v_unused_2722_ = lean_ctor_get(v___x_2711_, 1);
lean_dec(v_unused_2722_);
v___x_2714_ = v___x_2711_;
v_isShared_2715_ = v_isSharedCheck_2721_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_pos_2712_);
lean_dec(v___x_2711_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2721_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
uint8_t v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2716_ = 3;
v___x_2717_ = lean_box(v___x_2716_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 1, v___x_2717_);
v___x_2719_ = v___x_2714_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_pos_2712_);
lean_ctor_set(v_reuseFailAlloc_2720_, 1, v___x_2717_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
else
{
lean_object* v_pos_2723_; lean_object* v_err_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2801_; 
v_pos_2723_ = lean_ctor_get(v___x_2711_, 0);
v_err_2724_ = lean_ctor_get(v___x_2711_, 1);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2726_ = v___x_2711_;
v_isShared_2727_ = v_isSharedCheck_2801_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_err_2724_);
lean_inc(v_pos_2723_);
lean_dec(v___x_2711_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2801_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v_snd_2728_; lean_object* v_snd_2729_; uint8_t v___x_2730_; 
v_snd_2728_ = lean_ctor_get(v_a_2706_, 1);
lean_inc(v_snd_2728_);
lean_dec_ref(v_a_2706_);
v_snd_2729_ = lean_ctor_get(v_pos_2723_, 1);
v___x_2730_ = lean_nat_dec_eq(v_snd_2728_, v_snd_2729_);
lean_dec(v_snd_2728_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2732_; 
lean_dec_ref(v_noon_2709_);
lean_dec_ref(v_pm_2708_);
lean_dec_ref(v_am_2707_);
if (v_isShared_2727_ == 0)
{
v___x_2732_ = v___x_2726_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_pos_2723_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_err_2724_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
else
{
lean_object* v___x_2734_; 
lean_inc(v_snd_2729_);
lean_del_object(v___x_2726_);
lean_dec(v_err_2724_);
v___x_2734_ = l_Std_Internal_Parsec_String_pstring(v_noon_2709_, v_pos_2723_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_pos_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2744_; 
lean_dec(v_snd_2729_);
lean_dec_ref(v_pm_2708_);
lean_dec_ref(v_am_2707_);
v_pos_2735_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2744_ == 0)
{
lean_object* v_unused_2745_; 
v_unused_2745_ = lean_ctor_get(v___x_2734_, 1);
lean_dec(v_unused_2745_);
v___x_2737_ = v___x_2734_;
v_isShared_2738_ = v_isSharedCheck_2744_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_pos_2735_);
lean_dec(v___x_2734_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2744_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
uint8_t v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2739_ = 2;
v___x_2740_ = lean_box(v___x_2739_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 1, v___x_2740_);
v___x_2742_ = v___x_2737_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_pos_2735_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v___x_2740_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
else
{
lean_object* v_pos_2746_; lean_object* v_err_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2800_; 
v_pos_2746_ = lean_ctor_get(v___x_2734_, 0);
v_err_2747_ = lean_ctor_get(v___x_2734_, 1);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2749_ = v___x_2734_;
v_isShared_2750_ = v_isSharedCheck_2800_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_err_2747_);
lean_inc(v_pos_2746_);
lean_dec(v___x_2734_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2800_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v_snd_2751_; uint8_t v___x_2752_; 
v_snd_2751_ = lean_ctor_get(v_pos_2746_, 1);
v___x_2752_ = lean_nat_dec_eq(v_snd_2729_, v_snd_2751_);
lean_dec(v_snd_2729_);
if (v___x_2752_ == 0)
{
lean_object* v___x_2754_; 
lean_dec_ref(v_pm_2708_);
lean_dec_ref(v_am_2707_);
if (v_isShared_2750_ == 0)
{
v___x_2754_ = v___x_2749_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_pos_2746_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v_err_2747_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
else
{
lean_object* v___x_2756_; 
lean_inc(v_snd_2751_);
lean_del_object(v___x_2749_);
lean_dec(v_err_2747_);
v___x_2756_ = l_Std_Internal_Parsec_String_pstring(v_am_2707_, v_pos_2746_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_pos_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2766_; 
lean_dec(v_snd_2751_);
lean_dec_ref(v_pm_2708_);
v_pos_2757_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2766_ == 0)
{
lean_object* v_unused_2767_; 
v_unused_2767_ = lean_ctor_get(v___x_2756_, 1);
lean_dec(v_unused_2767_);
v___x_2759_ = v___x_2756_;
v_isShared_2760_ = v_isSharedCheck_2766_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_pos_2757_);
lean_dec(v___x_2756_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2766_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
uint8_t v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2764_; 
v___x_2761_ = 0;
v___x_2762_ = lean_box(v___x_2761_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 1, v___x_2762_);
v___x_2764_ = v___x_2759_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_pos_2757_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
else
{
lean_object* v_pos_2768_; lean_object* v_err_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2799_; 
v_pos_2768_ = lean_ctor_get(v___x_2756_, 0);
v_err_2769_ = lean_ctor_get(v___x_2756_, 1);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2771_ = v___x_2756_;
v_isShared_2772_ = v_isSharedCheck_2799_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_err_2769_);
lean_inc(v_pos_2768_);
lean_dec(v___x_2756_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2799_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v_snd_2773_; uint8_t v___x_2774_; 
v_snd_2773_ = lean_ctor_get(v_pos_2768_, 1);
v___x_2774_ = lean_nat_dec_eq(v_snd_2751_, v_snd_2773_);
lean_dec(v_snd_2751_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2776_; 
lean_dec_ref(v_pm_2708_);
if (v_isShared_2772_ == 0)
{
v___x_2776_ = v___x_2771_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_pos_2768_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_err_2769_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
else
{
lean_object* v___x_2778_; 
lean_del_object(v___x_2771_);
lean_dec(v_err_2769_);
v___x_2778_ = l_Std_Internal_Parsec_String_pstring(v_pm_2708_, v_pos_2768_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_pos_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2788_; 
v_pos_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2788_ == 0)
{
lean_object* v_unused_2789_; 
v_unused_2789_ = lean_ctor_get(v___x_2778_, 1);
lean_dec(v_unused_2789_);
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2788_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_pos_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2788_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
uint8_t v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2786_; 
v___x_2783_ = 1;
v___x_2784_ = lean_box(v___x_2783_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 1, v___x_2784_);
v___x_2786_ = v___x_2781_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_pos_2779_);
lean_ctor_set(v_reuseFailAlloc_2787_, 1, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
else
{
lean_object* v_pos_2790_; lean_object* v_err_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
v_pos_2790_ = lean_ctor_get(v___x_2778_, 0);
v_err_2791_ = lean_ctor_get(v___x_2778_, 1);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2778_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_err_2791_);
lean_inc(v_pos_2790_);
lean_dec(v___x_2778_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_pos_2790_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v_err_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
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
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(lean_object* v_arr_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; uint8_t v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; uint8_t v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v_pairs_2841_; lean_object* v___x_2842_; 
v___x_2804_ = lean_unsigned_to_nat(6u);
v___x_2805_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0);
v___x_2806_ = lean_array_fget_borrowed(v_arr_2802_, v___x_2805_);
v___x_2807_ = 0;
v___x_2808_ = lean_box(v___x_2807_);
lean_inc(v___x_2806_);
v___x_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2806_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
v___x_2810_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1);
v___x_2811_ = lean_array_fget_borrowed(v_arr_2802_, v___x_2810_);
v___x_2812_ = 1;
v___x_2813_ = lean_box(v___x_2812_);
lean_inc(v___x_2811_);
v___x_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2811_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
v___x_2815_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2);
v___x_2816_ = lean_array_fget_borrowed(v_arr_2802_, v___x_2815_);
v___x_2817_ = 2;
v___x_2818_ = lean_box(v___x_2817_);
lean_inc(v___x_2816_);
v___x_2819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2816_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
v___x_2820_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3);
v___x_2821_ = lean_array_fget_borrowed(v_arr_2802_, v___x_2820_);
v___x_2822_ = 3;
v___x_2823_ = lean_box(v___x_2822_);
lean_inc(v___x_2821_);
v___x_2824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2821_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4);
v___x_2826_ = lean_array_fget_borrowed(v_arr_2802_, v___x_2825_);
v___x_2827_ = 4;
v___x_2828_ = lean_box(v___x_2827_);
lean_inc(v___x_2826_);
v___x_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2826_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
v___x_2830_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5);
v___x_2831_ = lean_array_fget_borrowed(v_arr_2802_, v___x_2830_);
v___x_2832_ = 5;
v___x_2833_ = lean_box(v___x_2832_);
lean_inc(v___x_2831_);
v___x_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2831_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
v___x_2835_ = lean_mk_empty_array_with_capacity(v___x_2804_);
v___x_2836_ = lean_array_push(v___x_2835_, v___x_2809_);
v___x_2837_ = lean_array_push(v___x_2836_, v___x_2814_);
v___x_2838_ = lean_array_push(v___x_2837_, v___x_2819_);
v___x_2839_ = lean_array_push(v___x_2838_, v___x_2824_);
v___x_2840_ = lean_array_push(v___x_2839_, v___x_2829_);
v_pairs_2841_ = lean_array_push(v___x_2840_, v___x_2834_);
v___x_2842_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2841_, v_a_2803_);
lean_dec_ref(v_pairs_2841_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom___boxed(lean_object* v_arr_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_arr_2843_, v_a_2844_);
lean_dec_ref(v_arr_2843_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(lean_object* v_parse_2846_, lean_object* v_size_2847_, lean_object* v_acc_2848_, lean_object* v_count_2849_, lean_object* v_a_2850_){
_start:
{
uint8_t v___x_2851_; 
v___x_2851_ = lean_nat_dec_le(v_size_2847_, v_count_2849_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; 
lean_inc_ref(v_parse_2846_);
v___x_2852_ = lean_apply_1(v_parse_2846_, v_a_2850_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_pos_2853_; lean_object* v_res_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v_pos_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_pos_2853_);
v_res_2854_ = lean_ctor_get(v___x_2852_, 1);
lean_inc(v_res_2854_);
lean_dec_ref_known(v___x_2852_, 2);
v___x_2855_ = lean_array_push(v_acc_2848_, v_res_2854_);
v___x_2856_ = lean_unsigned_to_nat(1u);
v___x_2857_ = lean_nat_add(v_count_2849_, v___x_2856_);
lean_dec(v_count_2849_);
v_acc_2848_ = v___x_2855_;
v_count_2849_ = v___x_2857_;
v_a_2850_ = v_pos_2853_;
goto _start;
}
else
{
lean_object* v_pos_2859_; lean_object* v_err_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec(v_count_2849_);
lean_dec_ref(v_acc_2848_);
lean_dec_ref(v_parse_2846_);
v_pos_2859_ = lean_ctor_get(v___x_2852_, 0);
v_err_2860_ = lean_ctor_get(v___x_2852_, 1);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2852_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_err_2860_);
lean_inc(v_pos_2859_);
lean_dec(v___x_2852_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_pos_2859_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v_err_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
else
{
lean_object* v___x_2868_; 
lean_dec(v_count_2849_);
lean_dec_ref(v_parse_2846_);
v___x_2868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2868_, 0, v_a_2850_);
lean_ctor_set(v___x_2868_, 1, v_acc_2848_);
return v___x_2868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg___boxed(lean_object* v_parse_2869_, lean_object* v_size_2870_, lean_object* v_acc_2871_, lean_object* v_count_2872_, lean_object* v_a_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2869_, v_size_2870_, v_acc_2871_, v_count_2872_, v_a_2873_);
lean_dec(v_size_2870_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go(lean_object* v_00_u03b1_2875_, lean_object* v_parse_2876_, lean_object* v_size_2877_, lean_object* v_acc_2878_, lean_object* v_count_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2876_, v_size_2877_, v_acc_2878_, v_count_2879_, v_a_2880_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___boxed(lean_object* v_00_u03b1_2882_, lean_object* v_parse_2883_, lean_object* v_size_2884_, lean_object* v_acc_2885_, lean_object* v_count_2886_, lean_object* v_a_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go(v_00_u03b1_2882_, v_parse_2883_, v_size_2884_, v_acc_2885_, v_count_2886_, v_a_2887_);
lean_dec(v_size_2884_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(lean_object* v_parse_2891_, lean_object* v_size_2892_, lean_object* v_a_2893_){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2894_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___closed__0));
v___x_2895_ = lean_unsigned_to_nat(12u);
v___x_2896_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2891_, v_size_2892_, v___x_2894_, v___x_2895_, v_a_2893_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___boxed(lean_object* v_parse_2897_, lean_object* v_size_2898_, lean_object* v_a_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(v_parse_2897_, v_size_2898_, v_a_2899_);
lean_dec(v_size_2898_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly(lean_object* v_00_u03b1_2901_, lean_object* v_parse_2902_, lean_object* v_size_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(v_parse_2902_, v_size_2903_, v_a_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___boxed(lean_object* v_00_u03b1_2906_, lean_object* v_parse_2907_, lean_object* v_size_2908_, lean_object* v_a_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly(v_00_u03b1_2906_, v_parse_2907_, v_size_2908_, v_a_2909_);
lean_dec(v_size_2908_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(lean_object* v_parse_2911_, lean_object* v_size_2912_, lean_object* v_acc_2913_, lean_object* v_count_2914_, lean_object* v_a_2915_){
_start:
{
uint8_t v___x_2916_; 
v___x_2916_ = lean_nat_dec_le(v_size_2912_, v_count_2914_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; 
lean_inc_ref(v_parse_2911_);
v___x_2917_ = lean_apply_1(v_parse_2911_, v_a_2915_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_pos_2918_; lean_object* v_res_2919_; uint32_t v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v_pos_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_pos_2918_);
v_res_2919_ = lean_ctor_get(v___x_2917_, 1);
lean_inc(v_res_2919_);
lean_dec_ref_known(v___x_2917_, 2);
v___x_2920_ = lean_unbox_uint32(v_res_2919_);
lean_dec(v_res_2919_);
v___x_2921_ = lean_string_push(v_acc_2913_, v___x_2920_);
v___x_2922_ = lean_unsigned_to_nat(1u);
v___x_2923_ = lean_nat_add(v_count_2914_, v___x_2922_);
lean_dec(v_count_2914_);
v_acc_2913_ = v___x_2921_;
v_count_2914_ = v___x_2923_;
v_a_2915_ = v_pos_2918_;
goto _start;
}
else
{
lean_object* v_pos_2925_; lean_object* v_err_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec(v_count_2914_);
lean_dec_ref(v_acc_2913_);
lean_dec_ref(v_parse_2911_);
v_pos_2925_ = lean_ctor_get(v___x_2917_, 0);
v_err_2926_ = lean_ctor_get(v___x_2917_, 1);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2917_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_err_2926_);
lean_inc(v_pos_2925_);
lean_dec(v___x_2917_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_pos_2925_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v_err_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
else
{
lean_object* v___x_2934_; 
lean_dec(v_count_2914_);
lean_dec_ref(v_parse_2911_);
v___x_2934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2934_, 0, v_a_2915_);
lean_ctor_set(v___x_2934_, 1, v_acc_2913_);
return v___x_2934_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go___boxed(lean_object* v_parse_2935_, lean_object* v_size_2936_, lean_object* v_acc_2937_, lean_object* v_count_2938_, lean_object* v_a_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(v_parse_2935_, v_size_2936_, v_acc_2937_, v_count_2938_, v_a_2939_);
lean_dec(v_size_2936_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(lean_object* v_parse_2941_, lean_object* v_size_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2944_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_2945_ = lean_unsigned_to_nat(0u);
v___x_2946_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(v_parse_2941_, v_size_2942_, v___x_2944_, v___x_2945_, v_a_2943_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars___boxed(lean_object* v_parse_2947_, lean_object* v_size_2948_, lean_object* v_a_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v_parse_2947_, v_size_2948_, v_a_2949_);
lean_dec(v_size_2948_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(lean_object* v_parser_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v_pos_2954_; lean_object* v_res_2955_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
lean_inc_ref(v_a_2952_);
v___x_2988_ = l_Std_Internal_Parsec_String_pstring(v___x_2987_, v_a_2952_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_pos_2989_; lean_object* v_res_2990_; lean_object* v___x_2991_; 
lean_dec_ref(v_a_2952_);
v_pos_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_pos_2989_);
v_res_2990_ = lean_ctor_get(v___x_2988_, 1);
lean_inc(v_res_2990_);
lean_dec_ref_known(v___x_2988_, 2);
v___x_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2991_, 0, v_res_2990_);
v_pos_2954_ = v_pos_2989_;
v_res_2955_ = v___x_2991_;
goto v___jp_2953_;
}
else
{
lean_object* v_pos_2992_; lean_object* v_err_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3004_; 
v_pos_2992_ = lean_ctor_get(v___x_2988_, 0);
v_err_2993_ = lean_ctor_get(v___x_2988_, 1);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2995_ = v___x_2988_;
v_isShared_2996_ = v_isSharedCheck_3004_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_err_2993_);
lean_inc(v_pos_2992_);
lean_dec(v___x_2988_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3004_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v_snd_2997_; lean_object* v_snd_2998_; uint8_t v___x_2999_; 
v_snd_2997_ = lean_ctor_get(v_a_2952_, 1);
lean_inc(v_snd_2997_);
lean_dec_ref(v_a_2952_);
v_snd_2998_ = lean_ctor_get(v_pos_2992_, 1);
v___x_2999_ = lean_nat_dec_eq(v_snd_2997_, v_snd_2998_);
lean_dec(v_snd_2997_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3001_; 
lean_dec_ref(v_parser_2951_);
if (v_isShared_2996_ == 0)
{
v___x_3001_ = v___x_2995_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_pos_2992_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v_err_2993_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
else
{
lean_object* v___x_3003_; 
lean_del_object(v___x_2995_);
lean_dec(v_err_2993_);
v___x_3003_ = lean_box(0);
v_pos_2954_ = v_pos_2992_;
v_res_2955_ = v___x_3003_;
goto v___jp_2953_;
}
}
}
v___jp_2953_:
{
lean_object* v___x_2956_; 
v___x_2956_ = lean_apply_1(v_parser_2951_, v_pos_2954_);
if (lean_obj_tag(v___x_2956_) == 0)
{
if (lean_obj_tag(v_res_2955_) == 0)
{
lean_object* v_pos_2957_; lean_object* v_res_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2966_; 
v_pos_2957_ = lean_ctor_get(v___x_2956_, 0);
v_res_2958_ = lean_ctor_get(v___x_2956_, 1);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2960_ = v___x_2956_;
v_isShared_2961_ = v_isSharedCheck_2966_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_res_2958_);
lean_inc(v_pos_2957_);
lean_dec(v___x_2956_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2966_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2962_; lean_object* v___x_2964_; 
v___x_2962_ = lean_nat_to_int(v_res_2958_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 1, v___x_2962_);
v___x_2964_ = v___x_2960_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_pos_2957_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v___x_2962_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
else
{
lean_object* v_pos_2967_; lean_object* v_res_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2977_; 
lean_dec_ref_known(v_res_2955_, 1);
v_pos_2967_ = lean_ctor_get(v___x_2956_, 0);
v_res_2968_ = lean_ctor_get(v___x_2956_, 1);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2970_ = v___x_2956_;
v_isShared_2971_ = v_isSharedCheck_2977_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_res_2968_);
lean_inc(v_pos_2967_);
lean_dec(v___x_2956_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2977_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2975_; 
v___x_2972_ = lean_nat_to_int(v_res_2968_);
v___x_2973_ = lean_int_neg(v___x_2972_);
lean_dec(v___x_2972_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 1, v___x_2973_);
v___x_2975_ = v___x_2970_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_pos_2967_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
else
{
lean_object* v_pos_2978_; lean_object* v_err_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_dec(v_res_2955_);
v_pos_2978_ = lean_ctor_get(v___x_2956_, 0);
v_err_2979_ = lean_ctor_get(v___x_2956_, 1);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2956_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_err_2979_);
lean_inc(v_pos_2978_);
lean_dec(v___x_2956_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_pos_2978_);
lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_err_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___lam__0(lean_object* v___y_3005_){
_start:
{
lean_object* v_fst_3006_; lean_object* v_snd_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v_fst_3006_ = lean_ctor_get(v___y_3005_, 0);
v_snd_3007_ = lean_ctor_get(v___y_3005_, 1);
v___x_3008_ = lean_string_utf8_byte_size(v_fst_3006_);
v___x_3009_ = lean_nat_dec_eq(v_snd_3007_, v___x_3008_);
if (v___x_3009_ == 0)
{
uint32_t v_c_3010_; lean_object* v___x_3011_; lean_object* v_it_x27_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; uint8_t v___y_3016_; uint32_t v___x_3019_; uint8_t v___x_3020_; 
v_c_3010_ = lean_string_utf8_get_fast(v_fst_3006_, v_snd_3007_);
v___x_3011_ = lean_string_utf8_next_fast(v_fst_3006_, v_snd_3007_);
lean_inc(v_fst_3006_);
v_it_x27_3012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3012_, 0, v_fst_3006_);
lean_ctor_set(v_it_x27_3012_, 1, v___x_3011_);
v___x_3013_ = lean_box_uint32(v_c_3010_);
v___x_3014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3014_, 0, v_it_x27_3012_);
lean_ctor_set(v___x_3014_, 1, v___x_3013_);
v___x_3019_ = 48;
v___x_3020_ = lean_uint32_dec_le(v___x_3019_, v_c_3010_);
if (v___x_3020_ == 0)
{
v___y_3016_ = v___x_3020_;
goto v___jp_3015_;
}
else
{
uint32_t v___x_3021_; uint8_t v___x_3022_; 
v___x_3021_ = 57;
v___x_3022_ = lean_uint32_dec_le(v_c_3010_, v___x_3021_);
v___y_3016_ = v___x_3022_;
goto v___jp_3015_;
}
v___jp_3015_:
{
if (v___y_3016_ == 0)
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
lean_dec_ref_known(v___x_3014_, 2);
v___x_3017_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___y_3005_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
return v___x_3018_;
}
else
{
lean_dec_ref(v___y_3005_);
return v___x_3014_;
}
}
}
else
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = lean_box(0);
v___x_3024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___y_3005_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
return v___x_3024_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(lean_object* v_size_3026_, lean_object* v_a_3027_){
_start:
{
lean_object* v___f_3028_; lean_object* v___x_3029_; 
v___f_3028_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3029_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3028_, v_size_3026_, v_a_3027_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_pos_3030_; lean_object* v_res_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3042_; 
v_pos_3030_ = lean_ctor_get(v___x_3029_, 0);
v_res_3031_ = lean_ctor_get(v___x_3029_, 1);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3033_ = v___x_3029_;
v_isShared_3034_ = v_isSharedCheck_3042_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_res_3031_);
lean_inc(v_pos_3030_);
lean_dec(v___x_3029_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3042_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3040_; 
v___x_3035_ = lean_unsigned_to_nat(0u);
v___x_3036_ = lean_string_utf8_byte_size(v_res_3031_);
v___x_3037_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3037_, 0, v_res_3031_);
lean_ctor_set(v___x_3037_, 1, v___x_3035_);
lean_ctor_set(v___x_3037_, 2, v___x_3036_);
v___x_3038_ = l_String_Slice_toNat_x21(v___x_3037_);
lean_dec_ref_known(v___x_3037_, 3);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 1, v___x_3038_);
v___x_3040_ = v___x_3033_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_pos_3030_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
else
{
lean_object* v_pos_3043_; lean_object* v_err_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
v_pos_3043_ = lean_ctor_get(v___x_3029_, 0);
v_err_3044_ = lean_ctor_get(v___x_3029_, 1);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3029_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_err_3044_);
lean_inc(v_pos_3043_);
lean_dec(v___x_3029_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_pos_3043_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_err_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed(lean_object* v_size_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_size_3052_, v_a_3053_);
lean_dec(v_size_3052_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(lean_object* v_acc_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v_fst_3057_; lean_object* v_snd_3058_; lean_object* v_pos_3060_; lean_object* v_snd_3061_; lean_object* v_err_3062_; lean_object* v___x_3066_; uint8_t v___x_3067_; 
v_fst_3057_ = lean_ctor_get(v_a_3056_, 0);
v_snd_3058_ = lean_ctor_get(v_a_3056_, 1);
lean_inc(v_snd_3058_);
v___x_3066_ = lean_string_utf8_byte_size(v_fst_3057_);
v___x_3067_ = lean_nat_dec_eq(v_snd_3058_, v___x_3066_);
if (v___x_3067_ == 0)
{
uint32_t v_c_3068_; lean_object* v___x_3069_; lean_object* v_it_x27_3070_; uint8_t v___y_3072_; uint32_t v___x_3076_; uint8_t v___x_3077_; 
v_c_3068_ = lean_string_utf8_get_fast(v_fst_3057_, v_snd_3058_);
v___x_3069_ = lean_string_utf8_next_fast(v_fst_3057_, v_snd_3058_);
lean_inc(v_fst_3057_);
v_it_x27_3070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3070_, 0, v_fst_3057_);
lean_ctor_set(v_it_x27_3070_, 1, v___x_3069_);
v___x_3076_ = 48;
v___x_3077_ = lean_uint32_dec_le(v___x_3076_, v_c_3068_);
if (v___x_3077_ == 0)
{
v___y_3072_ = v___x_3077_;
goto v___jp_3071_;
}
else
{
uint32_t v___x_3078_; uint8_t v___x_3079_; 
v___x_3078_ = 57;
v___x_3079_ = lean_uint32_dec_le(v_c_3068_, v___x_3078_);
v___y_3072_ = v___x_3079_;
goto v___jp_3071_;
}
v___jp_3071_:
{
if (v___y_3072_ == 0)
{
lean_object* v___x_3073_; 
lean_dec_ref_known(v_it_x27_3070_, 2);
v___x_3073_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3058_);
v_pos_3060_ = v_a_3056_;
v_snd_3061_ = v_snd_3058_;
v_err_3062_ = v___x_3073_;
goto v___jp_3059_;
}
else
{
lean_object* v___x_3074_; 
lean_dec(v_snd_3058_);
lean_dec_ref(v_a_3056_);
v___x_3074_ = lean_string_push(v_acc_3055_, v_c_3068_);
v_acc_3055_ = v___x_3074_;
v_a_3056_ = v_it_x27_3070_;
goto _start;
}
}
}
else
{
lean_object* v___x_3080_; 
v___x_3080_ = lean_box(0);
lean_inc(v_snd_3058_);
v_pos_3060_ = v_a_3056_;
v_snd_3061_ = v_snd_3058_;
v_err_3062_ = v___x_3080_;
goto v___jp_3059_;
}
v___jp_3059_:
{
uint8_t v___x_3063_; 
v___x_3063_ = lean_nat_dec_eq(v_snd_3058_, v_snd_3061_);
lean_dec(v_snd_3061_);
lean_dec(v_snd_3058_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3064_; 
lean_dec_ref(v_acc_3055_);
lean_inc(v_err_3062_);
v___x_3064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3064_, 0, v_pos_3060_);
lean_ctor_set(v___x_3064_, 1, v_err_3062_);
return v___x_3064_;
}
else
{
lean_object* v___x_3065_; 
v___x_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3065_, 0, v_pos_3060_);
lean_ctor_set(v___x_3065_, 1, v_acc_3055_);
return v___x_3065_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(lean_object* v_size_3081_, lean_object* v_a_3082_){
_start:
{
lean_object* v_pos_3084_; lean_object* v_res_3085_; lean_object* v___y_3092_; lean_object* v___f_3104_; lean_object* v___x_3105_; 
v___f_3104_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3105_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3104_, v_size_3081_, v_a_3082_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_pos_3106_; lean_object* v_res_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v_pos_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_pos_3106_);
v_res_3107_ = lean_ctor_get(v___x_3105_, 1);
lean_inc(v_res_3107_);
lean_dec_ref_known(v___x_3105_, 2);
v___x_3108_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3109_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(v___x_3108_, v_pos_3106_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_pos_3110_; lean_object* v_res_3111_; lean_object* v___x_3112_; 
v_pos_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_pos_3110_);
v_res_3111_ = lean_ctor_get(v___x_3109_, 1);
lean_inc(v_res_3111_);
lean_dec_ref_known(v___x_3109_, 2);
v___x_3112_ = lean_string_append(v_res_3107_, v_res_3111_);
lean_dec(v_res_3111_);
v_pos_3084_ = v_pos_3110_;
v_res_3085_ = v___x_3112_;
goto v___jp_3083_;
}
else
{
lean_dec(v_res_3107_);
v___y_3092_ = v___x_3109_;
goto v___jp_3091_;
}
}
else
{
v___y_3092_ = v___x_3105_;
goto v___jp_3091_;
}
v___jp_3083_:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3086_ = lean_unsigned_to_nat(0u);
v___x_3087_ = lean_string_utf8_byte_size(v_res_3085_);
v___x_3088_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3088_, 0, v_res_3085_);
lean_ctor_set(v___x_3088_, 1, v___x_3086_);
lean_ctor_set(v___x_3088_, 2, v___x_3087_);
v___x_3089_ = l_String_Slice_toNat_x21(v___x_3088_);
lean_dec_ref_known(v___x_3088_, 3);
v___x_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3090_, 0, v_pos_3084_);
lean_ctor_set(v___x_3090_, 1, v___x_3089_);
return v___x_3090_;
}
v___jp_3091_:
{
if (lean_obj_tag(v___y_3092_) == 0)
{
lean_object* v_pos_3093_; lean_object* v_res_3094_; 
v_pos_3093_ = lean_ctor_get(v___y_3092_, 0);
lean_inc(v_pos_3093_);
v_res_3094_ = lean_ctor_get(v___y_3092_, 1);
lean_inc(v_res_3094_);
lean_dec_ref_known(v___y_3092_, 2);
v_pos_3084_ = v_pos_3093_;
v_res_3085_ = v_res_3094_;
goto v___jp_3083_;
}
else
{
lean_object* v_pos_3095_; lean_object* v_err_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
v_pos_3095_ = lean_ctor_get(v___y_3092_, 0);
v_err_3096_ = lean_ctor_get(v___y_3092_, 1);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___y_3092_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___y_3092_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_err_3096_);
lean_inc(v_pos_3095_);
lean_dec(v___y_3092_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_pos_3095_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v_err_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___boxed(lean_object* v_size_3113_, lean_object* v_a_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v_size_3113_, v_a_3114_);
lean_dec(v_size_3113_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(lean_object* v_size_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v___x_3118_; uint8_t v___x_3119_; 
v___x_3118_ = lean_unsigned_to_nat(1u);
v___x_3119_ = lean_nat_dec_eq(v_size_3116_, v___x_3118_);
if (v___x_3119_ == 0)
{
lean_object* v___x_3120_; 
v___x_3120_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_size_3116_, v_a_3117_);
return v___x_3120_;
}
else
{
lean_object* v___x_3121_; 
v___x_3121_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v___x_3118_, v_a_3117_);
return v___x_3121_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed(lean_object* v_size_3122_, lean_object* v_a_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_size_3122_, v_a_3123_);
lean_dec(v_size_3122_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(lean_object* v_size_3125_, lean_object* v_pad_3126_, lean_object* v_a_3127_){
_start:
{
lean_object* v_pos_3129_; lean_object* v_res_3130_; lean_object* v___f_3136_; lean_object* v___x_3137_; 
v___f_3136_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3137_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3136_, v_size_3125_, v_a_3127_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_pos_3138_; lean_object* v_res_3139_; uint32_t v___x_3140_; lean_object* v___x_3141_; 
v_pos_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_pos_3138_);
v_res_3139_ = lean_ctor_get(v___x_3137_, 1);
lean_inc(v_res_3139_);
lean_dec_ref_known(v___x_3137_, 2);
v___x_3140_ = 48;
v___x_3141_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_pad_3126_, v___x_3140_, v_res_3139_);
v_pos_3129_ = v_pos_3138_;
v_res_3130_ = v___x_3141_;
goto v___jp_3128_;
}
else
{
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_pos_3142_; lean_object* v_res_3143_; 
v_pos_3142_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_pos_3142_);
v_res_3143_ = lean_ctor_get(v___x_3137_, 1);
lean_inc(v_res_3143_);
lean_dec_ref_known(v___x_3137_, 2);
v_pos_3129_ = v_pos_3142_;
v_res_3130_ = v_res_3143_;
goto v___jp_3128_;
}
else
{
lean_object* v_pos_3144_; lean_object* v_err_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
v_pos_3144_ = lean_ctor_get(v___x_3137_, 0);
v_err_3145_ = lean_ctor_get(v___x_3137_, 1);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3137_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_err_3145_);
lean_inc(v_pos_3144_);
lean_dec(v___x_3137_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_pos_3144_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v_err_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
v___jp_3128_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3131_ = lean_unsigned_to_nat(0u);
v___x_3132_ = lean_string_utf8_byte_size(v_res_3130_);
v___x_3133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3133_, 0, v_res_3130_);
lean_ctor_set(v___x_3133_, 1, v___x_3131_);
lean_ctor_set(v___x_3133_, 2, v___x_3132_);
v___x_3134_ = l_String_Slice_toNat_x21(v___x_3133_);
lean_dec_ref_known(v___x_3133_, 3);
v___x_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3135_, 0, v_pos_3129_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
return v___x_3135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed(lean_object* v_size_3153_, lean_object* v_pad_3154_, lean_object* v_a_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(v_size_3153_, v_pad_3154_, v_a_3155_);
lean_dec(v_pad_3154_);
lean_dec(v_size_3153_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(lean_object* v_acc_3157_, lean_object* v_a_3158_){
_start:
{
lean_object* v_pos_3160_; uint32_t v_res_3161_; lean_object* v_fst_3164_; lean_object* v_snd_3165_; lean_object* v_pos_3167_; lean_object* v_snd_3168_; lean_object* v_err_3169_; lean_object* v___x_3173_; uint8_t v___x_3174_; 
v_fst_3164_ = lean_ctor_get(v_a_3158_, 0);
v_snd_3165_ = lean_ctor_get(v_a_3158_, 1);
lean_inc(v_snd_3165_);
v___x_3173_ = lean_string_utf8_byte_size(v_fst_3164_);
v___x_3174_ = lean_nat_dec_eq(v_snd_3165_, v___x_3173_);
if (v___x_3174_ == 0)
{
uint32_t v_c_3175_; lean_object* v___x_3176_; lean_object* v_it_x27_3177_; uint8_t v___y_3179_; uint8_t v___y_3180_; uint8_t v___y_3189_; uint32_t v___x_3199_; uint8_t v___x_3200_; 
v_c_3175_ = lean_string_utf8_get_fast(v_fst_3164_, v_snd_3165_);
v___x_3176_ = lean_string_utf8_next_fast(v_fst_3164_, v_snd_3165_);
lean_inc(v_fst_3164_);
v_it_x27_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3177_, 0, v_fst_3164_);
lean_ctor_set(v_it_x27_3177_, 1, v___x_3176_);
v___x_3199_ = 65;
v___x_3200_ = lean_uint32_dec_le(v___x_3199_, v_c_3175_);
if (v___x_3200_ == 0)
{
goto v___jp_3194_;
}
else
{
uint32_t v___x_3201_; uint8_t v___x_3202_; 
v___x_3201_ = 90;
v___x_3202_ = lean_uint32_dec_le(v_c_3175_, v___x_3201_);
if (v___x_3202_ == 0)
{
goto v___jp_3194_;
}
else
{
lean_dec(v_snd_3165_);
lean_dec_ref(v_a_3158_);
v_pos_3160_ = v_it_x27_3177_;
v_res_3161_ = v_c_3175_;
goto v___jp_3159_;
}
}
v___jp_3178_:
{
if (v___y_3180_ == 0)
{
uint32_t v___x_3181_; uint8_t v___x_3182_; 
v___x_3181_ = 95;
v___x_3182_ = lean_uint32_dec_eq(v_c_3175_, v___x_3181_);
if (v___x_3182_ == 0)
{
uint32_t v___x_3183_; uint8_t v___x_3184_; 
v___x_3183_ = 45;
v___x_3184_ = lean_uint32_dec_eq(v_c_3175_, v___x_3183_);
if (v___x_3184_ == 0)
{
uint32_t v___x_3185_; uint8_t v___x_3186_; 
v___x_3185_ = 47;
v___x_3186_ = lean_uint32_dec_eq(v_c_3175_, v___x_3185_);
if (v___x_3186_ == 0)
{
if (v___y_3179_ == 0)
{
lean_object* v___x_3187_; 
lean_dec_ref_known(v_it_x27_3177_, 2);
v___x_3187_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3165_);
v_pos_3167_ = v_a_3158_;
v_snd_3168_ = v_snd_3165_;
v_err_3169_ = v___x_3187_;
goto v___jp_3166_;
}
else
{
lean_dec(v_snd_3165_);
lean_dec_ref(v_a_3158_);
v_pos_3160_ = v_it_x27_3177_;
v_res_3161_ = v_c_3175_;
goto v___jp_3159_;
}
}
else
{
lean_dec(v_snd_3165_);
lean_dec_ref(v_a_3158_);
v_pos_3160_ = v_it_x27_3177_;
v_res_3161_ = v_c_3175_;
goto v___jp_3159_;
}
}
else
{
lean_dec(v_snd_3165_);
lean_dec_ref(v_a_3158_);
v_pos_3160_ = v_it_x27_3177_;
v_res_3161_ = v_c_3175_;
goto v___jp_3159_;
}
}
else
{
lean_dec(v_snd_3165_);
lean_dec_ref(v_a_3158_);
v_pos_3160_ = v_it_x27_3177_;
v_res_3161_ = v_c_3175_;
goto v___jp_3159_;
}
}
else
{
lean_dec(v_snd_3165_);
lean_dec_ref(v_a_3158_);
v_pos_3160_ = v_it_x27_3177_;
v_res_3161_ = v_c_3175_;
goto v___jp_3159_;
}
}
v___jp_3188_:
{
if (v___y_3189_ == 0)
{
uint32_t v___x_3190_; uint8_t v___x_3191_; 
v___x_3190_ = 48;
v___x_3191_ = lean_uint32_dec_le(v___x_3190_, v_c_3175_);
if (v___x_3191_ == 0)
{
v___y_3179_ = v___y_3189_;
v___y_3180_ = v___x_3191_;
goto v___jp_3178_;
}
else
{
uint32_t v___x_3192_; uint8_t v___x_3193_; 
v___x_3192_ = 57;
v___x_3193_ = lean_uint32_dec_le(v_c_3175_, v___x_3192_);
v___y_3179_ = v___y_3189_;
v___y_3180_ = v___x_3193_;
goto v___jp_3178_;
}
}
else
{
lean_dec(v_snd_3165_);
lean_dec_ref(v_a_3158_);
v_pos_3160_ = v_it_x27_3177_;
v_res_3161_ = v_c_3175_;
goto v___jp_3159_;
}
}
v___jp_3194_:
{
uint32_t v___x_3195_; uint8_t v___x_3196_; 
v___x_3195_ = 97;
v___x_3196_ = lean_uint32_dec_le(v___x_3195_, v_c_3175_);
if (v___x_3196_ == 0)
{
v___y_3189_ = v___x_3196_;
goto v___jp_3188_;
}
else
{
uint32_t v___x_3197_; uint8_t v___x_3198_; 
v___x_3197_ = 122;
v___x_3198_ = lean_uint32_dec_le(v_c_3175_, v___x_3197_);
v___y_3189_ = v___x_3198_;
goto v___jp_3188_;
}
}
}
else
{
lean_object* v___x_3203_; 
v___x_3203_ = lean_box(0);
lean_inc(v_snd_3165_);
v_pos_3167_ = v_a_3158_;
v_snd_3168_ = v_snd_3165_;
v_err_3169_ = v___x_3203_;
goto v___jp_3166_;
}
v___jp_3159_:
{
lean_object* v___x_3162_; 
v___x_3162_ = lean_string_push(v_acc_3157_, v_res_3161_);
v_acc_3157_ = v___x_3162_;
v_a_3158_ = v_pos_3160_;
goto _start;
}
v___jp_3166_:
{
uint8_t v___x_3170_; 
v___x_3170_ = lean_nat_dec_eq(v_snd_3165_, v_snd_3168_);
lean_dec(v_snd_3168_);
lean_dec(v_snd_3165_);
if (v___x_3170_ == 0)
{
lean_object* v___x_3171_; 
lean_dec_ref(v_acc_3157_);
lean_inc(v_err_3169_);
v___x_3171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3171_, 0, v_pos_3167_);
lean_ctor_set(v___x_3171_, 1, v_err_3169_);
return v___x_3171_;
}
else
{
lean_object* v___x_3172_; 
v___x_3172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3172_, 0, v_pos_3167_);
lean_ctor_set(v___x_3172_, 1, v_acc_3157_);
return v___x_3172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(lean_object* v_acc_3204_, lean_object* v_a_3205_){
_start:
{
lean_object* v_pos_3207_; uint32_t v_res_3208_; lean_object* v_fst_3211_; lean_object* v_snd_3212_; lean_object* v_pos_3214_; lean_object* v_snd_3215_; lean_object* v_err_3216_; lean_object* v___x_3220_; uint8_t v___x_3221_; 
v_fst_3211_ = lean_ctor_get(v_a_3205_, 0);
v_snd_3212_ = lean_ctor_get(v_a_3205_, 1);
lean_inc(v_snd_3212_);
v___x_3220_ = lean_string_utf8_byte_size(v_fst_3211_);
v___x_3221_ = lean_nat_dec_eq(v_snd_3212_, v___x_3220_);
if (v___x_3221_ == 0)
{
uint32_t v_c_3222_; lean_object* v___x_3223_; lean_object* v_it_x27_3224_; uint8_t v___y_3226_; uint8_t v___y_3227_; uint8_t v___y_3236_; uint32_t v___x_3246_; uint8_t v___x_3247_; 
v_c_3222_ = lean_string_utf8_get_fast(v_fst_3211_, v_snd_3212_);
v___x_3223_ = lean_string_utf8_next_fast(v_fst_3211_, v_snd_3212_);
lean_inc(v_fst_3211_);
v_it_x27_3224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3224_, 0, v_fst_3211_);
lean_ctor_set(v_it_x27_3224_, 1, v___x_3223_);
v___x_3246_ = 65;
v___x_3247_ = lean_uint32_dec_le(v___x_3246_, v_c_3222_);
if (v___x_3247_ == 0)
{
goto v___jp_3241_;
}
else
{
uint32_t v___x_3248_; uint8_t v___x_3249_; 
v___x_3248_ = 90;
v___x_3249_ = lean_uint32_dec_le(v_c_3222_, v___x_3248_);
if (v___x_3249_ == 0)
{
goto v___jp_3241_;
}
else
{
lean_dec(v_snd_3212_);
lean_dec_ref(v_a_3205_);
v_pos_3207_ = v_it_x27_3224_;
v_res_3208_ = v_c_3222_;
goto v___jp_3206_;
}
}
v___jp_3225_:
{
if (v___y_3227_ == 0)
{
uint32_t v___x_3228_; uint8_t v___x_3229_; 
v___x_3228_ = 95;
v___x_3229_ = lean_uint32_dec_eq(v_c_3222_, v___x_3228_);
if (v___x_3229_ == 0)
{
uint32_t v___x_3230_; uint8_t v___x_3231_; 
v___x_3230_ = 45;
v___x_3231_ = lean_uint32_dec_eq(v_c_3222_, v___x_3230_);
if (v___x_3231_ == 0)
{
uint32_t v___x_3232_; uint8_t v___x_3233_; 
v___x_3232_ = 47;
v___x_3233_ = lean_uint32_dec_eq(v_c_3222_, v___x_3232_);
if (v___x_3233_ == 0)
{
if (v___y_3226_ == 0)
{
lean_object* v___x_3234_; 
lean_dec_ref_known(v_it_x27_3224_, 2);
v___x_3234_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3212_);
v_pos_3214_ = v_a_3205_;
v_snd_3215_ = v_snd_3212_;
v_err_3216_ = v___x_3234_;
goto v___jp_3213_;
}
else
{
lean_dec(v_snd_3212_);
lean_dec_ref(v_a_3205_);
v_pos_3207_ = v_it_x27_3224_;
v_res_3208_ = v_c_3222_;
goto v___jp_3206_;
}
}
else
{
lean_dec(v_snd_3212_);
lean_dec_ref(v_a_3205_);
v_pos_3207_ = v_it_x27_3224_;
v_res_3208_ = v_c_3222_;
goto v___jp_3206_;
}
}
else
{
lean_dec(v_snd_3212_);
lean_dec_ref(v_a_3205_);
v_pos_3207_ = v_it_x27_3224_;
v_res_3208_ = v_c_3222_;
goto v___jp_3206_;
}
}
else
{
lean_dec(v_snd_3212_);
lean_dec_ref(v_a_3205_);
v_pos_3207_ = v_it_x27_3224_;
v_res_3208_ = v_c_3222_;
goto v___jp_3206_;
}
}
else
{
lean_dec(v_snd_3212_);
lean_dec_ref(v_a_3205_);
v_pos_3207_ = v_it_x27_3224_;
v_res_3208_ = v_c_3222_;
goto v___jp_3206_;
}
}
v___jp_3235_:
{
if (v___y_3236_ == 0)
{
uint32_t v___x_3237_; uint8_t v___x_3238_; 
v___x_3237_ = 48;
v___x_3238_ = lean_uint32_dec_le(v___x_3237_, v_c_3222_);
if (v___x_3238_ == 0)
{
v___y_3226_ = v___y_3236_;
v___y_3227_ = v___x_3238_;
goto v___jp_3225_;
}
else
{
uint32_t v___x_3239_; uint8_t v___x_3240_; 
v___x_3239_ = 57;
v___x_3240_ = lean_uint32_dec_le(v_c_3222_, v___x_3239_);
v___y_3226_ = v___y_3236_;
v___y_3227_ = v___x_3240_;
goto v___jp_3225_;
}
}
else
{
lean_dec(v_snd_3212_);
lean_dec_ref(v_a_3205_);
v_pos_3207_ = v_it_x27_3224_;
v_res_3208_ = v_c_3222_;
goto v___jp_3206_;
}
}
v___jp_3241_:
{
uint32_t v___x_3242_; uint8_t v___x_3243_; 
v___x_3242_ = 97;
v___x_3243_ = lean_uint32_dec_le(v___x_3242_, v_c_3222_);
if (v___x_3243_ == 0)
{
v___y_3236_ = v___x_3243_;
goto v___jp_3235_;
}
else
{
uint32_t v___x_3244_; uint8_t v___x_3245_; 
v___x_3244_ = 122;
v___x_3245_ = lean_uint32_dec_le(v_c_3222_, v___x_3244_);
v___y_3236_ = v___x_3245_;
goto v___jp_3235_;
}
}
}
else
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_box(0);
lean_inc(v_snd_3212_);
v_pos_3214_ = v_a_3205_;
v_snd_3215_ = v_snd_3212_;
v_err_3216_ = v___x_3250_;
goto v___jp_3213_;
}
v___jp_3206_:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3209_ = lean_string_push(v_acc_3204_, v_res_3208_);
v___x_3210_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(v___x_3209_, v_pos_3207_);
return v___x_3210_;
}
v___jp_3213_:
{
uint8_t v___x_3217_; 
v___x_3217_ = lean_nat_dec_eq(v_snd_3212_, v_snd_3215_);
lean_dec(v_snd_3215_);
lean_dec(v_snd_3212_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; 
lean_dec_ref(v_acc_3204_);
lean_inc(v_err_3216_);
v___x_3218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3218_, 0, v_pos_3214_);
lean_ctor_set(v___x_3218_, 1, v_err_3216_);
return v___x_3218_;
}
else
{
lean_object* v___x_3219_; 
v___x_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3219_, 0, v_pos_3214_);
lean_ctor_set(v___x_3219_, 1, v_acc_3204_);
return v___x_3219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(lean_object* v_a_3251_){
_start:
{
lean_object* v_fst_3252_; lean_object* v_snd_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; 
v_fst_3252_ = lean_ctor_get(v_a_3251_, 0);
v_snd_3253_ = lean_ctor_get(v_a_3251_, 1);
v___x_3254_ = lean_string_utf8_byte_size(v_fst_3252_);
v___x_3255_ = lean_nat_dec_eq(v_snd_3253_, v___x_3254_);
if (v___x_3255_ == 0)
{
uint32_t v_c_3256_; lean_object* v___x_3257_; uint8_t v___y_3264_; uint8_t v___y_3265_; uint8_t v___y_3275_; uint32_t v___x_3285_; uint8_t v___x_3286_; 
v_c_3256_ = lean_string_utf8_get_fast(v_fst_3252_, v_snd_3253_);
v___x_3257_ = lean_string_utf8_next_fast(v_fst_3252_, v_snd_3253_);
v___x_3285_ = 65;
v___x_3286_ = lean_uint32_dec_le(v___x_3285_, v_c_3256_);
if (v___x_3286_ == 0)
{
goto v___jp_3280_;
}
else
{
uint32_t v___x_3287_; uint8_t v___x_3288_; 
v___x_3287_ = 90;
v___x_3288_ = lean_uint32_dec_le(v_c_3256_, v___x_3287_);
if (v___x_3288_ == 0)
{
goto v___jp_3280_;
}
else
{
lean_inc(v_fst_3252_);
lean_dec_ref(v_a_3251_);
goto v___jp_3258_;
}
}
v___jp_3258_:
{
lean_object* v_it_x27_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v_it_x27_3259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3259_, 0, v_fst_3252_);
lean_ctor_set(v_it_x27_3259_, 1, v___x_3257_);
v___x_3260_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3261_ = lean_string_push(v___x_3260_, v_c_3256_);
v___x_3262_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(v___x_3261_, v_it_x27_3259_);
return v___x_3262_;
}
v___jp_3263_:
{
if (v___y_3265_ == 0)
{
uint32_t v___x_3266_; uint8_t v___x_3267_; 
v___x_3266_ = 95;
v___x_3267_ = lean_uint32_dec_eq(v_c_3256_, v___x_3266_);
if (v___x_3267_ == 0)
{
uint32_t v___x_3268_; uint8_t v___x_3269_; 
v___x_3268_ = 45;
v___x_3269_ = lean_uint32_dec_eq(v_c_3256_, v___x_3268_);
if (v___x_3269_ == 0)
{
uint32_t v___x_3270_; uint8_t v___x_3271_; 
v___x_3270_ = 47;
v___x_3271_ = lean_uint32_dec_eq(v_c_3256_, v___x_3270_);
if (v___x_3271_ == 0)
{
if (v___y_3264_ == 0)
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3272_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3273_, 0, v_a_3251_);
lean_ctor_set(v___x_3273_, 1, v___x_3272_);
return v___x_3273_;
}
else
{
lean_inc(v_fst_3252_);
lean_dec_ref(v_a_3251_);
goto v___jp_3258_;
}
}
else
{
lean_inc(v_fst_3252_);
lean_dec_ref(v_a_3251_);
goto v___jp_3258_;
}
}
else
{
lean_inc(v_fst_3252_);
lean_dec_ref(v_a_3251_);
goto v___jp_3258_;
}
}
else
{
lean_inc(v_fst_3252_);
lean_dec_ref(v_a_3251_);
goto v___jp_3258_;
}
}
else
{
lean_inc(v_fst_3252_);
lean_dec_ref(v_a_3251_);
goto v___jp_3258_;
}
}
v___jp_3274_:
{
if (v___y_3275_ == 0)
{
uint32_t v___x_3276_; uint8_t v___x_3277_; 
v___x_3276_ = 48;
v___x_3277_ = lean_uint32_dec_le(v___x_3276_, v_c_3256_);
if (v___x_3277_ == 0)
{
v___y_3264_ = v___y_3275_;
v___y_3265_ = v___x_3277_;
goto v___jp_3263_;
}
else
{
uint32_t v___x_3278_; uint8_t v___x_3279_; 
v___x_3278_ = 57;
v___x_3279_ = lean_uint32_dec_le(v_c_3256_, v___x_3278_);
v___y_3264_ = v___y_3275_;
v___y_3265_ = v___x_3279_;
goto v___jp_3263_;
}
}
else
{
lean_inc(v_fst_3252_);
lean_dec_ref(v_a_3251_);
goto v___jp_3258_;
}
}
v___jp_3280_:
{
uint32_t v___x_3281_; uint8_t v___x_3282_; 
v___x_3281_ = 97;
v___x_3282_ = lean_uint32_dec_le(v___x_3281_, v_c_3256_);
if (v___x_3282_ == 0)
{
v___y_3275_ = v___x_3282_;
goto v___jp_3274_;
}
else
{
uint32_t v___x_3283_; uint8_t v___x_3284_; 
v___x_3283_ = 122;
v___x_3284_ = lean_uint32_dec_le(v_c_3256_, v___x_3283_);
v___y_3275_ = v___x_3284_;
goto v___jp_3274_;
}
}
}
else
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = lean_box(0);
v___x_3290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3290_, 0, v_a_3251_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
return v___x_3290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(lean_object* v_n_3293_, lean_object* v_m_3294_, lean_object* v_parser_3295_, lean_object* v_a_3296_){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = lean_apply_1(v_parser_3295_, v_a_3296_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_pos_3298_; lean_object* v_res_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3319_; 
v_pos_3298_ = lean_ctor_get(v___x_3297_, 0);
v_res_3299_ = lean_ctor_get(v___x_3297_, 1);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3301_ = v___x_3297_;
v_isShared_3302_ = v_isSharedCheck_3319_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_res_3299_);
lean_inc(v_pos_3298_);
lean_dec(v___x_3297_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3319_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
uint8_t v___x_3315_; 
v___x_3315_ = lean_nat_dec_le(v_n_3293_, v_res_3299_);
if (v___x_3315_ == 0)
{
lean_dec(v_res_3299_);
goto v___jp_3303_;
}
else
{
uint8_t v___x_3316_; 
v___x_3316_ = lean_nat_dec_le(v_res_3299_, v_m_3294_);
if (v___x_3316_ == 0)
{
lean_dec(v_res_3299_);
goto v___jp_3303_;
}
else
{
lean_object* v___x_3317_; lean_object* v___x_3318_; 
lean_del_object(v___x_3301_);
lean_dec(v_m_3294_);
lean_dec(v_n_3293_);
v___x_3317_ = lean_nat_to_int(v_res_3299_);
v___x_3318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3318_, 0, v_pos_3298_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
return v___x_3318_;
}
}
v___jp_3303_:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3313_; 
v___x_3304_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__0));
v___x_3305_ = l_Nat_reprFast(v_n_3293_);
v___x_3306_ = lean_string_append(v___x_3304_, v___x_3305_);
lean_dec_ref(v___x_3305_);
v___x_3307_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__1));
v___x_3308_ = lean_string_append(v___x_3306_, v___x_3307_);
v___x_3309_ = l_Nat_reprFast(v_m_3294_);
v___x_3310_ = lean_string_append(v___x_3308_, v___x_3309_);
lean_dec_ref(v___x_3309_);
v___x_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
if (v_isShared_3302_ == 0)
{
lean_ctor_set_tag(v___x_3301_, 1);
lean_ctor_set(v___x_3301_, 1, v___x_3311_);
v___x_3313_ = v___x_3301_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_pos_3298_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
else
{
lean_object* v_pos_3320_; lean_object* v_err_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
lean_dec(v_m_3294_);
lean_dec(v_n_3293_);
v_pos_3320_ = lean_ctor_get(v___x_3297_, 0);
v_err_3321_ = lean_ctor_get(v___x_3297_, 1);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v___x_3297_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_err_3321_);
lean_inc(v_pos_3320_);
lean_dec(v___x_3297_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_pos_3320_);
lean_ctor_set(v_reuseFailAlloc_3327_, 1, v_err_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(lean_object* v_a_3329_){
_start:
{
lean_object* v_fst_3330_; lean_object* v_snd_3331_; lean_object* v___x_3332_; uint8_t v___x_3333_; 
v_fst_3330_ = lean_ctor_get(v_a_3329_, 0);
v_snd_3331_ = lean_ctor_get(v_a_3329_, 1);
v___x_3332_ = lean_string_utf8_byte_size(v_fst_3330_);
v___x_3333_ = lean_nat_dec_eq(v_snd_3331_, v___x_3332_);
if (v___x_3333_ == 0)
{
uint32_t v_c_3334_; lean_object* v___x_3335_; lean_object* v_pos_3337_; lean_object* v_snd_3338_; lean_object* v_err_3339_; lean_object* v_it_x27_3346_; uint32_t v___y_3348_; lean_object* v___y_3349_; uint8_t v___y_3350_; uint8_t v___y_3362_; uint32_t v___x_3382_; uint8_t v___x_3383_; 
v_c_3334_ = lean_string_utf8_get_fast(v_fst_3330_, v_snd_3331_);
v___x_3335_ = lean_string_utf8_next_fast(v_fst_3330_, v_snd_3331_);
lean_inc(v_fst_3330_);
v_it_x27_3346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3346_, 0, v_fst_3330_);
lean_ctor_set(v_it_x27_3346_, 1, v___x_3335_);
v___x_3382_ = 48;
v___x_3383_ = lean_uint32_dec_le(v___x_3382_, v_c_3334_);
if (v___x_3383_ == 0)
{
v___y_3362_ = v___x_3383_;
goto v___jp_3361_;
}
else
{
uint32_t v___x_3384_; uint8_t v___x_3385_; 
v___x_3384_ = 57;
v___x_3385_ = lean_uint32_dec_le(v_c_3334_, v___x_3384_);
v___y_3362_ = v___x_3385_;
goto v___jp_3361_;
}
v___jp_3336_:
{
uint8_t v___x_3340_; 
v___x_3340_ = lean_nat_dec_eq(v___x_3335_, v_snd_3338_);
lean_dec(v_snd_3338_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3341_; 
lean_inc(v_err_3339_);
v___x_3341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3341_, 0, v_pos_3337_);
lean_ctor_set(v___x_3341_, 1, v_err_3339_);
return v___x_3341_;
}
else
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3342_ = lean_uint32_to_nat(v_c_3334_);
v___x_3343_ = lean_unsigned_to_nat(48u);
v___x_3344_ = lean_nat_sub(v___x_3342_, v___x_3343_);
lean_dec(v___x_3342_);
v___x_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3345_, 0, v_pos_3337_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
return v___x_3345_;
}
}
v___jp_3347_:
{
if (v___y_3350_ == 0)
{
lean_object* v___x_3351_; 
lean_dec_ref(v___y_3349_);
v___x_3351_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v_pos_3337_ = v_it_x27_3346_;
v_snd_3338_ = v___x_3335_;
v_err_3339_ = v___x_3351_;
goto v___jp_3336_;
}
else
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
lean_dec_ref_known(v_it_x27_3346_, 2);
v___x_3352_ = lean_uint32_to_nat(v_c_3334_);
v___x_3353_ = lean_unsigned_to_nat(48u);
v___x_3354_ = lean_nat_sub(v___x_3352_, v___x_3353_);
lean_dec(v___x_3352_);
v___x_3355_ = lean_unsigned_to_nat(10u);
v___x_3356_ = lean_nat_mul(v___x_3354_, v___x_3355_);
lean_dec(v___x_3354_);
v___x_3357_ = lean_uint32_to_nat(v___y_3348_);
v___x_3358_ = lean_nat_sub(v___x_3357_, v___x_3353_);
lean_dec(v___x_3357_);
v___x_3359_ = lean_nat_add(v___x_3356_, v___x_3358_);
lean_dec(v___x_3358_);
lean_dec(v___x_3356_);
v___x_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___y_3349_);
lean_ctor_set(v___x_3360_, 1, v___x_3359_);
return v___x_3360_;
}
}
v___jp_3361_:
{
if (v___y_3362_ == 0)
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
lean_dec_ref_known(v_it_x27_3346_, 2);
v___x_3363_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3364_, 0, v_a_3329_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
return v___x_3364_;
}
else
{
lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3379_; 
lean_inc(v_fst_3330_);
v_isSharedCheck_3379_ = !lean_is_exclusive(v_a_3329_);
if (v_isSharedCheck_3379_ == 0)
{
lean_object* v_unused_3380_; lean_object* v_unused_3381_; 
v_unused_3380_ = lean_ctor_get(v_a_3329_, 1);
lean_dec(v_unused_3380_);
v_unused_3381_ = lean_ctor_get(v_a_3329_, 0);
lean_dec(v_unused_3381_);
v___x_3366_ = v_a_3329_;
v_isShared_3367_ = v_isSharedCheck_3379_;
goto v_resetjp_3365_;
}
else
{
lean_dec(v_a_3329_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3379_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
uint8_t v___x_3368_; 
v___x_3368_ = lean_nat_dec_eq(v___x_3335_, v___x_3332_);
if (v___x_3368_ == 0)
{
uint32_t v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3372_; 
v___x_3369_ = lean_string_utf8_get_fast(v_fst_3330_, v___x_3335_);
v___x_3370_ = lean_string_utf8_next_fast(v_fst_3330_, v___x_3335_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 1, v___x_3370_);
v___x_3372_ = v___x_3366_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_fst_3330_);
lean_ctor_set(v_reuseFailAlloc_3377_, 1, v___x_3370_);
v___x_3372_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
uint32_t v___x_3373_; uint8_t v___x_3374_; 
v___x_3373_ = 48;
v___x_3374_ = lean_uint32_dec_le(v___x_3373_, v___x_3369_);
if (v___x_3374_ == 0)
{
v___y_3348_ = v___x_3369_;
v___y_3349_ = v___x_3372_;
v___y_3350_ = v___x_3374_;
goto v___jp_3347_;
}
else
{
uint32_t v___x_3375_; uint8_t v___x_3376_; 
v___x_3375_ = 57;
v___x_3376_ = lean_uint32_dec_le(v___x_3369_, v___x_3375_);
v___y_3348_ = v___x_3369_;
v___y_3349_ = v___x_3372_;
v___y_3350_ = v___x_3376_;
goto v___jp_3347_;
}
}
}
else
{
lean_object* v___x_3378_; 
lean_del_object(v___x_3366_);
lean_dec(v_fst_3330_);
v___x_3378_ = lean_box(0);
v_pos_3337_ = v_it_x27_3346_;
v_snd_3338_ = v___x_3335_;
v_err_3339_ = v___x_3378_;
goto v___jp_3336_;
}
}
}
}
}
else
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = lean_box(0);
v___x_3387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3387_, 0, v_a_3329_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
return v___x_3387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(lean_object* v_a_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = lean_nat_to_int(v_a_3388_);
v___x_3391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___y_3389_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
return v___x_3391_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__0(void){
_start:
{
uint32_t v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3392_ = 58;
v___x_3393_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3394_ = lean_string_push(v___x_3393_, v___x_3392_);
return v___x_3394_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3395_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__0);
v___x_3396_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_3397_ = lean_string_append(v___x_3396_, v___x_3395_);
return v___x_3397_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__2(void){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3398_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3399_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__1);
v___x_3400_ = lean_string_append(v___x_3399_, v___x_3398_);
return v___x_3400_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__2);
v___x_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
return v___x_3402_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = 58;
v___x_3404_ = lean_box_uint32(v___x_3403_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1(uint8_t v_withColon_3405_, lean_object* v___y_3406_){
_start:
{
if (v_withColon_3405_ == 0)
{
lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3407_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___boxed__const__1;
v___x_3408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___y_3406_);
lean_ctor_set(v___x_3408_, 1, v___x_3407_);
return v___x_3408_;
}
else
{
lean_object* v_fst_3409_; lean_object* v_snd_3410_; lean_object* v___x_3411_; uint8_t v___x_3412_; 
v_fst_3409_ = lean_ctor_get(v___y_3406_, 0);
v_snd_3410_ = lean_ctor_get(v___y_3406_, 1);
v___x_3411_ = lean_string_utf8_byte_size(v_fst_3409_);
v___x_3412_ = lean_nat_dec_eq(v_snd_3410_, v___x_3411_);
if (v___x_3412_ == 0)
{
uint32_t v___x_3413_; uint32_t v_c_3414_; uint8_t v___x_3415_; 
v___x_3413_ = 58;
v_c_3414_ = lean_string_utf8_get_fast(v_fst_3409_, v_snd_3410_);
v___x_3415_ = lean_uint32_dec_eq(v_c_3414_, v___x_3413_);
if (v___x_3415_ == 0)
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3416_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___closed__3);
v___x_3417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___y_3406_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
return v___x_3417_;
}
else
{
lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3427_; 
lean_inc(v_snd_3410_);
lean_inc(v_fst_3409_);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___y_3406_);
if (v_isSharedCheck_3427_ == 0)
{
lean_object* v_unused_3428_; lean_object* v_unused_3429_; 
v_unused_3428_ = lean_ctor_get(v___y_3406_, 1);
lean_dec(v_unused_3428_);
v_unused_3429_ = lean_ctor_get(v___y_3406_, 0);
lean_dec(v_unused_3429_);
v___x_3419_ = v___y_3406_;
v_isShared_3420_ = v_isSharedCheck_3427_;
goto v_resetjp_3418_;
}
else
{
lean_dec(v___y_3406_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3427_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3421_; lean_object* v_it_x27_3423_; 
v___x_3421_ = lean_string_utf8_next_fast(v_fst_3409_, v_snd_3410_);
lean_dec(v_snd_3410_);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 1, v___x_3421_);
v_it_x27_3423_ = v___x_3419_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_fst_3409_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v___x_3421_);
v_it_x27_3423_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3424_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___boxed__const__1;
v___x_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3425_, 0, v_it_x27_3423_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
return v___x_3425_;
}
}
}
}
else
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = lean_box(0);
v___x_3431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___y_3406_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
return v___x_3431_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___boxed(lean_object* v_withColon_3432_, lean_object* v___y_3433_){
_start:
{
uint8_t v_withColon_boxed_3434_; lean_object* v_res_3435_; 
v_withColon_boxed_3434_ = lean_unbox(v_withColon_3432_);
v_res_3435_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1(v_withColon_boxed_3434_, v___y_3433_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(lean_object* v___y_3436_, lean_object* v___f_3437_, lean_object* v_n_3438_, uint8_t v_reason_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v_pos_3442_; lean_object* v_err_3443_; 
switch(v_reason_3439_)
{
case 0:
{
lean_object* v___x_3459_; 
v___x_3459_ = lean_apply_1(v___y_3436_, v___y_3440_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_pos_3460_; lean_object* v___x_3461_; 
v_pos_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_pos_3460_);
lean_dec_ref_known(v___x_3459_, 2);
v___x_3461_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3460_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_pos_3462_; lean_object* v_res_3463_; lean_object* v___x_3464_; 
v_pos_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_pos_3462_);
v_res_3463_ = lean_ctor_get(v___x_3461_, 1);
lean_inc(v_res_3463_);
lean_dec_ref_known(v___x_3461_, 2);
v___x_3464_ = lean_apply_2(v___f_3437_, v_res_3463_, v_pos_3462_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_pos_3465_; lean_object* v_res_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3474_; 
v_pos_3465_ = lean_ctor_get(v___x_3464_, 0);
v_res_3466_ = lean_ctor_get(v___x_3464_, 1);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3468_ = v___x_3464_;
v_isShared_3469_ = v_isSharedCheck_3474_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_res_3466_);
lean_inc(v_pos_3465_);
lean_dec(v___x_3464_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3474_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3470_; lean_object* v___x_3472_; 
v___x_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3470_, 0, v_res_3466_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 1, v___x_3470_);
v___x_3472_ = v___x_3468_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_pos_3465_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
else
{
lean_object* v_pos_3475_; lean_object* v_err_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
v_pos_3475_ = lean_ctor_get(v___x_3464_, 0);
v_err_3476_ = lean_ctor_get(v___x_3464_, 1);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v___x_3464_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_err_3476_);
lean_inc(v_pos_3475_);
lean_dec(v___x_3464_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3481_; 
if (v_isShared_3479_ == 0)
{
v___x_3481_ = v___x_3478_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_pos_3475_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v_err_3476_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
else
{
lean_object* v_pos_3484_; lean_object* v_err_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_dec_ref(v___f_3437_);
v_pos_3484_ = lean_ctor_get(v___x_3461_, 0);
v_err_3485_ = lean_ctor_get(v___x_3461_, 1);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3461_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_err_3485_);
lean_inc(v_pos_3484_);
lean_dec(v___x_3461_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_pos_3484_);
lean_ctor_set(v_reuseFailAlloc_3491_, 1, v_err_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
else
{
lean_object* v_pos_3493_; lean_object* v_err_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec_ref(v___f_3437_);
v_pos_3493_ = lean_ctor_get(v___x_3459_, 0);
v_err_3494_ = lean_ctor_get(v___x_3459_, 1);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3459_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_err_3494_);
lean_inc(v_pos_3493_);
lean_dec(v___x_3459_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_pos_3493_);
lean_ctor_set(v_reuseFailAlloc_3500_, 1, v_err_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
case 1:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
lean_dec_ref(v___f_3437_);
lean_dec_ref(v___y_3436_);
v___x_3502_ = lean_box(0);
v___x_3503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___y_3440_);
lean_ctor_set(v___x_3503_, 1, v___x_3502_);
return v___x_3503_;
}
default: 
{
lean_object* v___x_3504_; 
lean_inc_ref(v___y_3440_);
v___x_3504_ = lean_apply_1(v___y_3436_, v___y_3440_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v_pos_3505_; lean_object* v___x_3506_; 
v_pos_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_pos_3505_);
lean_dec_ref_known(v___x_3504_, 2);
v___x_3506_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3505_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_pos_3507_; lean_object* v_res_3508_; lean_object* v___x_3509_; 
v_pos_3507_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_pos_3507_);
v_res_3508_ = lean_ctor_get(v___x_3506_, 1);
lean_inc(v_res_3508_);
lean_dec_ref_known(v___x_3506_, 2);
v___x_3509_ = lean_apply_2(v___f_3437_, v_res_3508_, v_pos_3507_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_pos_3510_; lean_object* v_res_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3519_; 
lean_dec_ref(v___y_3440_);
v_pos_3510_ = lean_ctor_get(v___x_3509_, 0);
v_res_3511_ = lean_ctor_get(v___x_3509_, 1);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3513_ = v___x_3509_;
v_isShared_3514_ = v_isSharedCheck_3519_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_res_3511_);
lean_inc(v_pos_3510_);
lean_dec(v___x_3509_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3519_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3515_; lean_object* v___x_3517_; 
v___x_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3515_, 0, v_res_3511_);
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 1, v___x_3515_);
v___x_3517_ = v___x_3513_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_pos_3510_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v___x_3515_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
else
{
lean_object* v_pos_3520_; lean_object* v_err_3521_; 
v_pos_3520_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_pos_3520_);
v_err_3521_ = lean_ctor_get(v___x_3509_, 1);
lean_inc(v_err_3521_);
lean_dec_ref_known(v___x_3509_, 2);
v_pos_3442_ = v_pos_3520_;
v_err_3443_ = v_err_3521_;
goto v___jp_3441_;
}
}
else
{
lean_object* v_pos_3522_; lean_object* v_err_3523_; 
lean_dec_ref(v___f_3437_);
v_pos_3522_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_pos_3522_);
v_err_3523_ = lean_ctor_get(v___x_3506_, 1);
lean_inc(v_err_3523_);
lean_dec_ref_known(v___x_3506_, 2);
v_pos_3442_ = v_pos_3522_;
v_err_3443_ = v_err_3523_;
goto v___jp_3441_;
}
}
else
{
lean_object* v_pos_3524_; lean_object* v_err_3525_; 
lean_dec_ref(v___f_3437_);
v_pos_3524_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_pos_3524_);
v_err_3525_ = lean_ctor_get(v___x_3504_, 1);
lean_inc(v_err_3525_);
lean_dec_ref_known(v___x_3504_, 2);
v_pos_3442_ = v_pos_3524_;
v_err_3443_ = v_err_3525_;
goto v___jp_3441_;
}
}
}
v___jp_3441_:
{
lean_object* v_snd_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3457_; 
v_snd_3444_ = lean_ctor_get(v___y_3440_, 1);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___y_3440_);
if (v_isSharedCheck_3457_ == 0)
{
lean_object* v_unused_3458_; 
v_unused_3458_ = lean_ctor_get(v___y_3440_, 0);
lean_dec(v_unused_3458_);
v___x_3446_ = v___y_3440_;
v_isShared_3447_ = v_isSharedCheck_3457_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_snd_3444_);
lean_dec(v___y_3440_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3457_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v_snd_3448_; uint8_t v___x_3449_; 
v_snd_3448_ = lean_ctor_get(v_pos_3442_, 1);
v___x_3449_ = lean_nat_dec_eq(v_snd_3444_, v_snd_3448_);
lean_dec(v_snd_3444_);
if (v___x_3449_ == 0)
{
lean_object* v___x_3451_; 
if (v_isShared_3447_ == 0)
{
lean_ctor_set_tag(v___x_3446_, 1);
lean_ctor_set(v___x_3446_, 1, v_err_3443_);
lean_ctor_set(v___x_3446_, 0, v_pos_3442_);
v___x_3451_ = v___x_3446_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_pos_3442_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v_err_3443_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
else
{
lean_object* v___x_3453_; lean_object* v___x_3455_; 
lean_dec(v_err_3443_);
v___x_3453_ = lean_box(0);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 1, v___x_3453_);
lean_ctor_set(v___x_3446_, 0, v_pos_3442_);
v___x_3455_ = v___x_3446_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_pos_3442_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2___boxed(lean_object* v___y_3526_, lean_object* v___f_3527_, lean_object* v_n_3528_, lean_object* v_reason_3529_, lean_object* v___y_3530_){
_start:
{
uint8_t v_reason_boxed_3531_; lean_object* v_res_3532_; 
v_reason_boxed_3531_ = lean_unbox(v_reason_3529_);
v_res_3532_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3526_, v___f_3527_, v_n_3528_, v_reason_boxed_3531_, v___y_3530_);
lean_dec_ref(v_n_3528_);
return v_res_3532_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = lean_unsigned_to_nat(3600u);
v___x_3536_ = lean_nat_to_int(v___x_3535_);
return v___x_3536_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4(void){
_start:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3538_ = lean_unsigned_to_nat(1u);
v___x_3539_ = l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(v___x_3538_);
return v___x_3539_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5(void){
_start:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3540_ = lean_unsigned_to_nat(59u);
v___x_3541_ = lean_nat_to_int(v___x_3540_);
return v___x_3541_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3544_ = lean_unsigned_to_nat(23u);
v___x_3545_ = lean_nat_to_int(v___x_3544_);
return v___x_3545_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9(void){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3546_ = lean_unsigned_to_nat(60u);
v___x_3547_ = l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(v___x_3546_);
return v___x_3547_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11(void){
_start:
{
uint32_t v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3549_ = 45;
v___x_3550_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3551_ = lean_string_push(v___x_3550_, v___x_3549_);
return v___x_3551_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3552_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11);
v___x_3553_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_3554_ = lean_string_append(v___x_3553_, v___x_3552_);
return v___x_3554_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13(void){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3555_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3556_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12);
v___x_3557_ = lean_string_append(v___x_3556_, v___x_3555_);
return v___x_3557_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14(void){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3558_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13);
v___x_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3558_);
return v___x_3559_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__15(void){
_start:
{
uint32_t v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3560_ = 43;
v___x_3561_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3562_ = lean_string_push(v___x_3561_, v___x_3560_);
return v___x_3562_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__16(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3563_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__15);
v___x_3564_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_3565_ = lean_string_append(v___x_3564_, v___x_3563_);
return v___x_3565_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__17(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3566_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3567_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__16);
v___x_3568_ = lean_string_append(v___x_3567_, v___x_3566_);
return v___x_3568_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__18(void){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3569_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__17);
v___x_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3569_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(uint8_t v_withMinutes_3571_, uint8_t v_withSeconds_3572_, uint8_t v_withColon_3573_, lean_object* v_a_3574_){
_start:
{
lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3617_; lean_object* v_fst_3620_; lean_object* v_snd_3621_; lean_object* v___f_3622_; lean_object* v___x_3623_; lean_object* v___y_3624_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v_pos_3670_; lean_object* v_res_3671_; lean_object* v_pos_3729_; lean_object* v_fst_3730_; lean_object* v_snd_3731_; lean_object* v_err_3732_; lean_object* v___x_3745_; uint8_t v___x_3746_; 
v_fst_3620_ = lean_ctor_get(v_a_3574_, 0);
lean_inc(v_fst_3620_);
v_snd_3621_ = lean_ctor_get(v_a_3574_, 1);
lean_inc(v_snd_3621_);
v___f_3622_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3));
v___x_3623_ = lean_box(v_withColon_3573_);
v___y_3624_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___boxed), 2, 1);
lean_closure_set(v___y_3624_, 0, v___x_3623_);
v___x_3745_ = lean_string_utf8_byte_size(v_fst_3620_);
v___x_3746_ = lean_nat_dec_eq(v_snd_3621_, v___x_3745_);
if (v___x_3746_ == 0)
{
uint32_t v___x_3747_; uint32_t v_c_3748_; uint8_t v___x_3749_; 
v___x_3747_ = 43;
v_c_3748_ = lean_string_utf8_get_fast(v_fst_3620_, v_snd_3621_);
v___x_3749_ = lean_uint32_dec_eq(v_c_3748_, v___x_3747_);
if (v___x_3749_ == 0)
{
lean_object* v___x_3750_; 
v___x_3750_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__18, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__18_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__18);
lean_inc(v_snd_3621_);
v_pos_3729_ = v_a_3574_;
v_fst_3730_ = v_fst_3620_;
v_snd_3731_ = v_snd_3621_;
v_err_3732_ = v___x_3750_;
goto v___jp_3728_;
}
else
{
lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3759_; 
v_isSharedCheck_3759_ = !lean_is_exclusive(v_a_3574_);
if (v_isSharedCheck_3759_ == 0)
{
lean_object* v_unused_3760_; lean_object* v_unused_3761_; 
v_unused_3760_ = lean_ctor_get(v_a_3574_, 1);
lean_dec(v_unused_3760_);
v_unused_3761_ = lean_ctor_get(v_a_3574_, 0);
lean_dec(v_unused_3761_);
v___x_3752_ = v_a_3574_;
v_isShared_3753_ = v_isSharedCheck_3759_;
goto v_resetjp_3751_;
}
else
{
lean_dec(v_a_3574_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3759_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3754_; lean_object* v_it_x27_3756_; 
v___x_3754_ = lean_string_utf8_next_fast(v_fst_3620_, v_snd_3621_);
lean_dec(v_snd_3621_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 1, v___x_3754_);
v_it_x27_3756_ = v___x_3752_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_fst_3620_);
lean_ctor_set(v_reuseFailAlloc_3758_, 1, v___x_3754_);
v_it_x27_3756_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3757_; 
v___x_3757_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v_pos_3670_ = v_it_x27_3756_;
v_res_3671_ = v___x_3757_;
goto v___jp_3669_;
}
}
}
}
else
{
lean_object* v___x_3762_; 
v___x_3762_ = lean_box(0);
lean_inc(v_snd_3621_);
v_pos_3729_ = v_a_3574_;
v_fst_3730_ = v_fst_3620_;
v_snd_3731_ = v_snd_3621_;
v_err_3732_ = v___x_3762_;
goto v___jp_3728_;
}
v___jp_3575_:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3578_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0));
v___x_3579_ = l_Int_repr(v___y_3577_);
lean_dec(v___y_3577_);
v___x_3580_ = lean_string_append(v___x_3578_, v___x_3579_);
lean_dec_ref(v___x_3579_);
v___x_3581_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__1));
v___x_3582_ = lean_string_append(v___x_3580_, v___x_3581_);
v___x_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3582_);
v___x_3584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___y_3576_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
return v___x_3584_;
}
v___jp_3585_:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3590_ = lean_int_add(v___y_3587_, v___y_3589_);
lean_dec(v___y_3589_);
lean_dec(v___y_3587_);
v___x_3591_ = lean_int_mul(v___x_3590_, v___y_3586_);
lean_dec(v___x_3590_);
v___x_3592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___y_3588_);
lean_ctor_set(v___x_3592_, 1, v___x_3591_);
return v___x_3592_;
}
v___jp_3593_:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3600_ = lean_nat_to_int(v___y_3596_);
v___x_3601_ = lean_int_mul(v___y_3599_, v___x_3600_);
lean_dec(v___x_3600_);
lean_dec(v___y_3599_);
v___x_3602_ = lean_int_add(v___y_3594_, v___x_3601_);
lean_dec(v___x_3601_);
lean_dec(v___y_3594_);
if (lean_obj_tag(v___y_3597_) == 0)
{
lean_object* v___x_3603_; 
v___x_3603_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_3586_ = v___y_3595_;
v___y_3587_ = v___x_3602_;
v___y_3588_ = v___y_3598_;
v___y_3589_ = v___x_3603_;
goto v___jp_3585_;
}
else
{
lean_object* v_val_3604_; 
v_val_3604_ = lean_ctor_get(v___y_3597_, 0);
lean_inc(v_val_3604_);
lean_dec_ref_known(v___y_3597_, 1);
v___y_3586_ = v___y_3595_;
v___y_3587_ = v___x_3602_;
v___y_3588_ = v___y_3598_;
v___y_3589_ = v_val_3604_;
goto v___jp_3585_;
}
}
v___jp_3605_:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3612_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2);
v___x_3613_ = lean_int_mul(v___y_3610_, v___x_3612_);
lean_dec(v___y_3610_);
if (lean_obj_tag(v___y_3606_) == 0)
{
lean_object* v___x_3614_; 
v___x_3614_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_3594_ = v___x_3613_;
v___y_3595_ = v___y_3607_;
v___y_3596_ = v___y_3608_;
v___y_3597_ = v___y_3609_;
v___y_3598_ = v___y_3611_;
v___y_3599_ = v___x_3614_;
goto v___jp_3593_;
}
else
{
lean_object* v_val_3615_; 
v_val_3615_ = lean_ctor_get(v___y_3606_, 0);
lean_inc(v_val_3615_);
lean_dec_ref_known(v___y_3606_, 1);
v___y_3594_ = v___x_3613_;
v___y_3595_ = v___y_3607_;
v___y_3596_ = v___y_3608_;
v___y_3597_ = v___y_3609_;
v___y_3598_ = v___y_3611_;
v___y_3599_ = v_val_3615_;
goto v___jp_3593_;
}
}
v___jp_3616_:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3618_ = lean_box(0);
v___x_3619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___y_3617_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
return v___x_3619_;
}
v___jp_3625_:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4);
v___x_3632_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3624_, v___f_3622_, v___x_3631_, v_withSeconds_3572_, v___y_3630_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_res_3633_; 
v_res_3633_ = lean_ctor_get(v___x_3632_, 1);
lean_inc(v_res_3633_);
if (lean_obj_tag(v_res_3633_) == 1)
{
lean_object* v_pos_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3657_; 
v_pos_3634_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3657_ == 0)
{
lean_object* v_unused_3658_; 
v_unused_3658_ = lean_ctor_get(v___x_3632_, 1);
lean_dec(v_unused_3658_);
v___x_3636_ = v___x_3632_;
v_isShared_3637_ = v_isSharedCheck_3657_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_pos_3634_);
lean_dec(v___x_3632_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3657_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v_val_3638_; lean_object* v___x_3639_; uint8_t v___x_3640_; 
v_val_3638_ = lean_ctor_get(v_res_3633_, 0);
v___x_3639_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5);
v___x_3640_ = lean_int_dec_lt(v___x_3639_, v_val_3638_);
if (v___x_3640_ == 0)
{
lean_del_object(v___x_3636_);
v___y_3606_ = v___y_3626_;
v___y_3607_ = v___y_3627_;
v___y_3608_ = v___y_3628_;
v___y_3609_ = v_res_3633_;
v___y_3610_ = v___y_3629_;
v___y_3611_ = v_pos_3634_;
goto v___jp_3605_;
}
else
{
lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3655_; 
lean_inc(v_val_3638_);
lean_dec(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec(v___y_3626_);
v_isSharedCheck_3655_ = !lean_is_exclusive(v_res_3633_);
if (v_isSharedCheck_3655_ == 0)
{
lean_object* v_unused_3656_; 
v_unused_3656_ = lean_ctor_get(v_res_3633_, 0);
lean_dec(v_unused_3656_);
v___x_3642_ = v_res_3633_;
v_isShared_3643_ = v_isSharedCheck_3655_;
goto v_resetjp_3641_;
}
else
{
lean_dec(v_res_3633_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3655_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3650_; 
v___x_3644_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6));
v___x_3645_ = l_Int_repr(v_val_3638_);
lean_dec(v_val_3638_);
v___x_3646_ = lean_string_append(v___x_3644_, v___x_3645_);
lean_dec_ref(v___x_3645_);
v___x_3647_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__7));
v___x_3648_ = lean_string_append(v___x_3646_, v___x_3647_);
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 0, v___x_3648_);
v___x_3650_ = v___x_3642_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3648_);
v___x_3650_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
lean_object* v___x_3652_; 
if (v_isShared_3637_ == 0)
{
lean_ctor_set_tag(v___x_3636_, 1);
lean_ctor_set(v___x_3636_, 1, v___x_3650_);
v___x_3652_ = v___x_3636_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_pos_3634_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v___x_3650_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3659_; 
v_pos_3659_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_pos_3659_);
lean_dec_ref_known(v___x_3632_, 2);
v___y_3606_ = v___y_3626_;
v___y_3607_ = v___y_3627_;
v___y_3608_ = v___y_3628_;
v___y_3609_ = v_res_3633_;
v___y_3610_ = v___y_3629_;
v___y_3611_ = v_pos_3659_;
goto v___jp_3605_;
}
}
else
{
lean_object* v_pos_3660_; lean_object* v_err_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
lean_dec(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec(v___y_3626_);
v_pos_3660_ = lean_ctor_get(v___x_3632_, 0);
v_err_3661_ = lean_ctor_get(v___x_3632_, 1);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3632_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_err_3661_);
lean_inc(v_pos_3660_);
lean_dec(v___x_3632_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
if (v_isShared_3664_ == 0)
{
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_pos_3660_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_err_3661_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
v___jp_3669_:
{
lean_object* v___x_3672_; 
v___x_3672_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3670_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_pos_3673_; lean_object* v_res_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; uint8_t v___x_3677_; 
v_pos_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc(v_pos_3673_);
v_res_3674_ = lean_ctor_get(v___x_3672_, 1);
lean_inc(v_res_3674_);
lean_dec_ref_known(v___x_3672_, 2);
v___x_3675_ = lean_nat_to_int(v_res_3674_);
v___x_3676_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_3677_ = lean_int_dec_lt(v___x_3675_, v___x_3676_);
if (v___x_3677_ == 0)
{
lean_object* v___x_3678_; uint8_t v___x_3679_; 
v___x_3678_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8);
v___x_3679_ = lean_int_dec_lt(v___x_3678_, v___x_3675_);
if (v___x_3679_ == 0)
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3680_ = lean_unsigned_to_nat(60u);
v___x_3681_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9);
lean_inc_ref(v___y_3624_);
v___x_3682_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3624_, v___f_3622_, v___x_3681_, v_withMinutes_3571_, v_pos_3673_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_res_3683_; 
v_res_3683_ = lean_ctor_get(v___x_3682_, 1);
lean_inc(v_res_3683_);
if (lean_obj_tag(v_res_3683_) == 1)
{
lean_object* v_pos_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3707_; 
v_pos_3684_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3707_ == 0)
{
lean_object* v_unused_3708_; 
v_unused_3708_ = lean_ctor_get(v___x_3682_, 1);
lean_dec(v_unused_3708_);
v___x_3686_ = v___x_3682_;
v_isShared_3687_ = v_isSharedCheck_3707_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_pos_3684_);
lean_dec(v___x_3682_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3707_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v_val_3688_; lean_object* v___x_3689_; uint8_t v___x_3690_; 
v_val_3688_ = lean_ctor_get(v_res_3683_, 0);
v___x_3689_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5);
v___x_3690_ = lean_int_dec_lt(v___x_3689_, v_val_3688_);
if (v___x_3690_ == 0)
{
lean_del_object(v___x_3686_);
v___y_3626_ = v_res_3683_;
v___y_3627_ = v_res_3671_;
v___y_3628_ = v___x_3680_;
v___y_3629_ = v___x_3675_;
v___y_3630_ = v_pos_3684_;
goto v___jp_3625_;
}
else
{
lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3705_; 
lean_inc(v_val_3688_);
lean_dec(v___x_3675_);
lean_dec_ref(v___y_3624_);
v_isSharedCheck_3705_ = !lean_is_exclusive(v_res_3683_);
if (v_isSharedCheck_3705_ == 0)
{
lean_object* v_unused_3706_; 
v_unused_3706_ = lean_ctor_get(v_res_3683_, 0);
lean_dec(v_unused_3706_);
v___x_3692_ = v_res_3683_;
v_isShared_3693_ = v_isSharedCheck_3705_;
goto v_resetjp_3691_;
}
else
{
lean_dec(v_res_3683_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3705_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3700_; 
v___x_3694_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10));
v___x_3695_ = l_Int_repr(v_val_3688_);
lean_dec(v_val_3688_);
v___x_3696_ = lean_string_append(v___x_3694_, v___x_3695_);
lean_dec_ref(v___x_3695_);
v___x_3697_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__7));
v___x_3698_ = lean_string_append(v___x_3696_, v___x_3697_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 0, v___x_3698_);
v___x_3700_ = v___x_3692_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3698_);
v___x_3700_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
lean_object* v___x_3702_; 
if (v_isShared_3687_ == 0)
{
lean_ctor_set_tag(v___x_3686_, 1);
lean_ctor_set(v___x_3686_, 1, v___x_3700_);
v___x_3702_ = v___x_3686_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_pos_3684_);
lean_ctor_set(v_reuseFailAlloc_3703_, 1, v___x_3700_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3709_; 
v_pos_3709_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_pos_3709_);
lean_dec_ref_known(v___x_3682_, 2);
v___y_3626_ = v_res_3683_;
v___y_3627_ = v_res_3671_;
v___y_3628_ = v___x_3680_;
v___y_3629_ = v___x_3675_;
v___y_3630_ = v_pos_3709_;
goto v___jp_3625_;
}
}
else
{
lean_object* v_pos_3710_; lean_object* v_err_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_dec(v___x_3675_);
lean_dec_ref(v___y_3624_);
v_pos_3710_ = lean_ctor_get(v___x_3682_, 0);
v_err_3711_ = lean_ctor_get(v___x_3682_, 1);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3682_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_err_3711_);
lean_inc(v_pos_3710_);
lean_dec(v___x_3682_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_pos_3710_);
lean_ctor_set(v_reuseFailAlloc_3717_, 1, v_err_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
else
{
lean_dec_ref(v___y_3624_);
v___y_3576_ = v_pos_3673_;
v___y_3577_ = v___x_3675_;
goto v___jp_3575_;
}
}
else
{
lean_dec_ref(v___y_3624_);
v___y_3576_ = v_pos_3673_;
v___y_3577_ = v___x_3675_;
goto v___jp_3575_;
}
}
else
{
lean_object* v_pos_3719_; lean_object* v_err_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
lean_dec_ref(v___y_3624_);
v_pos_3719_ = lean_ctor_get(v___x_3672_, 0);
v_err_3720_ = lean_ctor_get(v___x_3672_, 1);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3672_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_err_3720_);
lean_inc(v_pos_3719_);
lean_dec(v___x_3672_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_pos_3719_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v_err_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
v___jp_3728_:
{
uint8_t v___x_3733_; 
v___x_3733_ = lean_nat_dec_eq(v_snd_3621_, v_snd_3731_);
lean_dec(v_snd_3621_);
if (v___x_3733_ == 0)
{
lean_object* v___x_3734_; 
lean_dec(v_snd_3731_);
lean_dec(v_fst_3730_);
lean_dec_ref(v___y_3624_);
lean_inc(v_err_3732_);
v___x_3734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3734_, 0, v_pos_3729_);
lean_ctor_set(v___x_3734_, 1, v_err_3732_);
return v___x_3734_;
}
else
{
lean_object* v___x_3735_; uint8_t v___x_3736_; 
v___x_3735_ = lean_string_utf8_byte_size(v_fst_3730_);
v___x_3736_ = lean_nat_dec_eq(v_snd_3731_, v___x_3735_);
if (v___x_3736_ == 0)
{
if (v___x_3733_ == 0)
{
lean_dec(v_snd_3731_);
lean_dec(v_fst_3730_);
lean_dec_ref(v___y_3624_);
v___y_3617_ = v_pos_3729_;
goto v___jp_3616_;
}
else
{
uint32_t v___x_3737_; uint32_t v_c_3738_; uint8_t v___x_3739_; 
v___x_3737_ = 45;
v_c_3738_ = lean_string_utf8_get_fast(v_fst_3730_, v_snd_3731_);
v___x_3739_ = lean_uint32_dec_eq(v_c_3738_, v___x_3737_);
if (v___x_3739_ == 0)
{
lean_object* v___x_3740_; lean_object* v___x_3741_; 
lean_dec(v_snd_3731_);
lean_dec(v_fst_3730_);
lean_dec_ref(v___y_3624_);
v___x_3740_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14);
v___x_3741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3741_, 0, v_pos_3729_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
return v___x_3741_;
}
else
{
lean_object* v___x_3742_; lean_object* v_it_x27_3743_; lean_object* v___x_3744_; 
lean_dec_ref(v_pos_3729_);
v___x_3742_ = lean_string_utf8_next_fast(v_fst_3730_, v_snd_3731_);
lean_dec(v_snd_3731_);
v_it_x27_3743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3743_, 0, v_fst_3730_);
lean_ctor_set(v_it_x27_3743_, 1, v___x_3742_);
v___x_3744_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v_pos_3670_ = v_it_x27_3743_;
v_res_3671_ = v___x_3744_;
goto v___jp_3669_;
}
}
}
else
{
lean_dec(v_snd_3731_);
lean_dec(v_fst_3730_);
lean_dec_ref(v___y_3624_);
v___y_3617_ = v_pos_3729_;
goto v___jp_3616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___boxed(lean_object* v_withMinutes_3763_, lean_object* v_withSeconds_3764_, lean_object* v_withColon_3765_, lean_object* v_a_3766_){
_start:
{
uint8_t v_withMinutes_boxed_3767_; uint8_t v_withSeconds_boxed_3768_; uint8_t v_withColon_boxed_3769_; lean_object* v_res_3770_; 
v_withMinutes_boxed_3767_ = lean_unbox(v_withMinutes_3763_);
v_withSeconds_boxed_3768_ = lean_unbox(v_withSeconds_3764_);
v_withColon_boxed_3769_ = lean_unbox(v_withColon_3765_);
v_res_3770_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v_withMinutes_boxed_3767_, v_withSeconds_boxed_3768_, v_withColon_boxed_3769_, v_a_3766_);
return v_res_3770_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1(void){
_start:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3773_ = lean_unsigned_to_nat(2000u);
v___x_3774_ = lean_nat_to_int(v___x_3773_);
return v___x_3774_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5(void){
_start:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
v___x_3780_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3781_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_3782_ = lean_int_sub(v___x_3781_, v___x_3780_);
return v___x_3782_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6(void){
_start:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v_range_3785_; 
v___x_3783_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3784_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5);
v_range_3785_ = lean_int_add(v___x_3784_, v___x_3783_);
return v_range_3785_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(lean_object* v_config_3788_, lean_object* v_x_3789_, lean_object* v_a_3790_){
_start:
{
lean_object* v___y_3792_; 
switch(lean_obj_tag(v_x_3789_))
{
case 0:
{
uint8_t v_presentation_3818_; 
v_presentation_3818_ = lean_ctor_get_uint8(v_x_3789_, 0);
lean_dec_ref_known(v_x_3789_, 0);
switch(v_presentation_3818_)
{
case 1:
{
lean_object* v_dateformat_3819_; lean_object* v_symbols_3820_; lean_object* v___x_3821_; 
v_dateformat_3819_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_3819_);
lean_dec_ref(v_config_3788_);
v_symbols_3820_ = lean_ctor_get(v_dateformat_3819_, 1);
lean_inc_ref(v_symbols_3820_);
lean_dec_ref(v_dateformat_3819_);
v___x_3821_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraLong(v_symbols_3820_, v_a_3790_);
return v___x_3821_;
}
case 2:
{
lean_object* v_dateformat_3822_; lean_object* v_symbols_3823_; lean_object* v___x_3824_; 
v_dateformat_3822_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_3822_);
lean_dec_ref(v_config_3788_);
v_symbols_3823_ = lean_ctor_get(v_dateformat_3822_, 1);
lean_inc_ref(v_symbols_3823_);
lean_dec_ref(v_dateformat_3822_);
v___x_3824_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraNarrow(v_symbols_3823_, v_a_3790_);
return v___x_3824_;
}
default: 
{
lean_object* v_dateformat_3825_; lean_object* v_symbols_3826_; lean_object* v___x_3827_; 
v_dateformat_3825_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_3825_);
lean_dec_ref(v_config_3788_);
v_symbols_3826_ = lean_ctor_get(v_dateformat_3825_, 1);
lean_inc_ref(v_symbols_3826_);
lean_dec_ref(v_dateformat_3825_);
v___x_3827_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraShort(v_symbols_3826_, v_a_3790_);
return v___x_3827_;
}
}
}
case 1:
{
lean_object* v_presentation_3828_; 
lean_dec_ref(v_config_3788_);
v_presentation_3828_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_presentation_3828_);
lean_dec_ref_known(v_x_3789_, 1);
switch(lean_obj_tag(v_presentation_3828_))
{
case 0:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; 
v___x_3829_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0));
v___x_3830_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3829_, v_a_3790_);
return v___x_3830_;
}
case 1:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3831_ = lean_unsigned_to_nat(2u);
v___x_3832_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3831_, v_a_3790_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_pos_3833_; lean_object* v_res_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3844_; 
v_pos_3833_ = lean_ctor_get(v___x_3832_, 0);
v_res_3834_ = lean_ctor_get(v___x_3832_, 1);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3836_ = v___x_3832_;
v_isShared_3837_ = v_isSharedCheck_3844_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_res_3834_);
lean_inc(v_pos_3833_);
lean_dec(v___x_3832_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3844_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3842_; 
v___x_3838_ = lean_nat_to_int(v_res_3834_);
v___x_3839_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_3840_ = lean_int_add(v___x_3839_, v___x_3838_);
lean_dec(v___x_3838_);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 1, v___x_3840_);
v___x_3842_ = v___x_3836_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_pos_3833_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v___x_3840_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
else
{
lean_object* v_pos_3845_; lean_object* v_err_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3853_; 
v_pos_3845_ = lean_ctor_get(v___x_3832_, 0);
v_err_3846_ = lean_ctor_get(v___x_3832_, 1);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3848_ = v___x_3832_;
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_err_3846_);
lean_inc(v_pos_3845_);
lean_dec(v___x_3832_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3849_ == 0)
{
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_pos_3845_);
lean_ctor_set(v_reuseFailAlloc_3852_, 1, v_err_3846_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
case 2:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3854_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2));
v___x_3855_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3854_, v_a_3790_);
return v___x_3855_;
}
default: 
{
lean_object* v_num_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v_num_3856_ = lean_ctor_get(v_presentation_3828_, 0);
lean_inc(v_num_3856_);
lean_dec_ref_known(v_presentation_3828_, 1);
v___x_3857_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed), 2, 1);
lean_closure_set(v___x_3857_, 0, v_num_3856_);
v___x_3858_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3857_, v_a_3790_);
return v___x_3858_;
}
}
}
case 2:
{
lean_object* v_presentation_3859_; 
lean_dec_ref(v_config_3788_);
v_presentation_3859_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_presentation_3859_);
lean_dec_ref_known(v_x_3789_, 1);
switch(lean_obj_tag(v_presentation_3859_))
{
case 0:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3860_ = lean_unsigned_to_nat(1u);
v___x_3861_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v___x_3860_, v_a_3790_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v_pos_3862_; lean_object* v_res_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3871_; 
v_pos_3862_ = lean_ctor_get(v___x_3861_, 0);
v_res_3863_ = lean_ctor_get(v___x_3861_, 1);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3865_ = v___x_3861_;
v_isShared_3866_ = v_isSharedCheck_3871_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_res_3863_);
lean_inc(v_pos_3862_);
lean_dec(v___x_3861_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3871_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3867_; lean_object* v___x_3869_; 
v___x_3867_ = lean_nat_to_int(v_res_3863_);
if (v_isShared_3866_ == 0)
{
lean_ctor_set(v___x_3865_, 1, v___x_3867_);
v___x_3869_ = v___x_3865_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_pos_3862_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v___x_3867_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
else
{
lean_object* v_pos_3872_; lean_object* v_err_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
v_pos_3872_ = lean_ctor_get(v___x_3861_, 0);
v_err_3873_ = lean_ctor_get(v___x_3861_, 1);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___x_3861_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_err_3873_);
lean_inc(v_pos_3872_);
lean_dec(v___x_3861_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_pos_3872_);
lean_ctor_set(v_reuseFailAlloc_3879_, 1, v_err_3873_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
case 1:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3881_ = lean_unsigned_to_nat(2u);
v___x_3882_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3881_, v_a_3790_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_pos_3883_; lean_object* v_res_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3894_; 
v_pos_3883_ = lean_ctor_get(v___x_3882_, 0);
v_res_3884_ = lean_ctor_get(v___x_3882_, 1);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3886_ = v___x_3882_;
v_isShared_3887_ = v_isSharedCheck_3894_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_res_3884_);
lean_inc(v_pos_3883_);
lean_dec(v___x_3882_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3894_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3892_; 
v___x_3888_ = lean_nat_to_int(v_res_3884_);
v___x_3889_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_3890_ = lean_int_add(v___x_3889_, v___x_3888_);
lean_dec(v___x_3888_);
if (v_isShared_3887_ == 0)
{
lean_ctor_set(v___x_3886_, 1, v___x_3890_);
v___x_3892_ = v___x_3886_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_pos_3883_);
lean_ctor_set(v_reuseFailAlloc_3893_, 1, v___x_3890_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
else
{
lean_object* v_pos_3895_; lean_object* v_err_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3903_; 
v_pos_3895_ = lean_ctor_get(v___x_3882_, 0);
v_err_3896_ = lean_ctor_get(v___x_3882_, 1);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3898_ = v___x_3882_;
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_err_3896_);
lean_inc(v_pos_3895_);
lean_dec(v___x_3882_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3901_; 
if (v_isShared_3899_ == 0)
{
v___x_3901_ = v___x_3898_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_pos_3895_);
lean_ctor_set(v_reuseFailAlloc_3902_, 1, v_err_3896_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
case 2:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3904_ = lean_unsigned_to_nat(4u);
v___x_3905_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3904_, v_a_3790_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_pos_3906_; lean_object* v_res_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3915_; 
v_pos_3906_ = lean_ctor_get(v___x_3905_, 0);
v_res_3907_ = lean_ctor_get(v___x_3905_, 1);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3909_ = v___x_3905_;
v_isShared_3910_ = v_isSharedCheck_3915_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_res_3907_);
lean_inc(v_pos_3906_);
lean_dec(v___x_3905_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3915_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3911_; lean_object* v___x_3913_; 
v___x_3911_ = lean_nat_to_int(v_res_3907_);
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 1, v___x_3911_);
v___x_3913_ = v___x_3909_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_pos_3906_);
lean_ctor_set(v_reuseFailAlloc_3914_, 1, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
else
{
lean_object* v_pos_3916_; lean_object* v_err_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3924_; 
v_pos_3916_ = lean_ctor_get(v___x_3905_, 0);
v_err_3917_ = lean_ctor_get(v___x_3905_, 1);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3919_ = v___x_3905_;
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_err_3917_);
lean_inc(v_pos_3916_);
lean_dec(v___x_3905_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
if (v_isShared_3920_ == 0)
{
v___x_3922_ = v___x_3919_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_pos_3916_);
lean_ctor_set(v_reuseFailAlloc_3923_, 1, v_err_3917_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
default: 
{
lean_object* v_num_3925_; lean_object* v___x_3926_; 
v_num_3925_ = lean_ctor_get(v_presentation_3859_, 0);
lean_inc(v_num_3925_);
lean_dec_ref_known(v_presentation_3859_, 1);
v___x_3926_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_num_3925_, v_a_3790_);
lean_dec(v_num_3925_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v_pos_3927_; lean_object* v_res_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3936_; 
v_pos_3927_ = lean_ctor_get(v___x_3926_, 0);
v_res_3928_ = lean_ctor_get(v___x_3926_, 1);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3930_ = v___x_3926_;
v_isShared_3931_ = v_isSharedCheck_3936_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_res_3928_);
lean_inc(v_pos_3927_);
lean_dec(v___x_3926_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3936_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3932_; lean_object* v___x_3934_; 
v___x_3932_ = lean_nat_to_int(v_res_3928_);
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 1, v___x_3932_);
v___x_3934_ = v___x_3930_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_pos_3927_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
else
{
lean_object* v_pos_3937_; lean_object* v_err_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
v_pos_3937_ = lean_ctor_get(v___x_3926_, 0);
v_err_3938_ = lean_ctor_get(v___x_3926_, 1);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3940_ = v___x_3926_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_err_3938_);
lean_inc(v_pos_3937_);
lean_dec(v___x_3926_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_pos_3937_);
lean_ctor_set(v_reuseFailAlloc_3944_, 1, v_err_3938_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
}
}
case 3:
{
lean_object* v_presentation_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
lean_dec_ref(v_config_3788_);
v_presentation_3946_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_presentation_3946_);
lean_dec_ref_known(v_x_3789_, 1);
v___x_3947_ = lean_unsigned_to_nat(1u);
v___x_3948_ = lean_unsigned_to_nat(366u);
v___x_3949_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3949_, 0, v_presentation_3946_);
v___x_3950_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3947_, v___x_3948_, v___x_3949_, v_a_3790_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v_pos_3951_; lean_object* v_res_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3962_; 
v_pos_3951_ = lean_ctor_get(v___x_3950_, 0);
v_res_3952_ = lean_ctor_get(v___x_3950_, 1);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3954_ = v___x_3950_;
v_isShared_3955_ = v_isSharedCheck_3962_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_res_3952_);
lean_inc(v_pos_3951_);
lean_dec(v___x_3950_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3962_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
uint8_t v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3960_; 
v___x_3956_ = 1;
v___x_3957_ = lean_box(v___x_3956_);
v___x_3958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3957_);
lean_ctor_set(v___x_3958_, 1, v_res_3952_);
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 1, v___x_3958_);
v___x_3960_ = v___x_3954_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_pos_3951_);
lean_ctor_set(v_reuseFailAlloc_3961_, 1, v___x_3958_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
else
{
lean_object* v_pos_3963_; lean_object* v_err_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
v_pos_3963_ = lean_ctor_get(v___x_3950_, 0);
v_err_3964_ = lean_ctor_get(v___x_3950_, 1);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3950_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_err_3964_);
lean_inc(v_pos_3963_);
lean_dec(v___x_3950_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_pos_3963_);
lean_ctor_set(v_reuseFailAlloc_3970_, 1, v_err_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
case 4:
{
lean_object* v_presentation_3972_; 
v_presentation_3972_ = lean_ctor_get(v_x_3789_, 0);
lean_inc_ref(v_presentation_3972_);
lean_dec_ref_known(v_x_3789_, 1);
if (lean_obj_tag(v_presentation_3972_) == 0)
{
lean_object* v_val_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
lean_dec_ref(v_config_3788_);
v_val_3973_ = lean_ctor_get(v_presentation_3972_, 0);
lean_inc(v_val_3973_);
lean_dec_ref_known(v_presentation_3972_, 1);
v___x_3974_ = lean_unsigned_to_nat(1u);
v___x_3975_ = lean_unsigned_to_nat(12u);
v___x_3976_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3976_, 0, v_val_3973_);
v___x_3977_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3974_, v___x_3975_, v___x_3976_, v_a_3790_);
return v___x_3977_;
}
else
{
lean_object* v_val_3978_; uint8_t v___x_3979_; 
v_val_3978_ = lean_ctor_get(v_presentation_3972_, 0);
lean_inc(v_val_3978_);
lean_dec_ref_known(v_presentation_3972_, 1);
v___x_3979_ = lean_unbox(v_val_3978_);
lean_dec(v_val_3978_);
switch(v___x_3979_)
{
case 1:
{
lean_object* v_dateformat_3980_; lean_object* v_symbols_3981_; lean_object* v___x_3982_; 
v_dateformat_3980_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_3980_);
lean_dec_ref(v_config_3788_);
v_symbols_3981_ = lean_ctor_get(v_dateformat_3980_, 1);
lean_inc_ref(v_symbols_3981_);
lean_dec_ref(v_dateformat_3980_);
v___x_3982_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(v_symbols_3981_, v_a_3790_);
return v___x_3982_;
}
case 2:
{
lean_object* v_dateformat_3983_; lean_object* v_symbols_3984_; lean_object* v___x_3985_; 
v_dateformat_3983_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_3983_);
lean_dec_ref(v_config_3788_);
v_symbols_3984_ = lean_ctor_get(v_dateformat_3983_, 1);
lean_inc_ref(v_symbols_3984_);
lean_dec_ref(v_dateformat_3983_);
v___x_3985_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(v_symbols_3984_, v_a_3790_);
return v___x_3985_;
}
default: 
{
lean_object* v_dateformat_3986_; lean_object* v_symbols_3987_; lean_object* v___x_3988_; 
v_dateformat_3986_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_3986_);
lean_dec_ref(v_config_3788_);
v_symbols_3987_ = lean_ctor_get(v_dateformat_3986_, 1);
lean_inc_ref(v_symbols_3987_);
lean_dec_ref(v_dateformat_3986_);
v___x_3988_ = l_Std_Time_parseMonthShort(v_symbols_3987_, v_a_3790_);
return v___x_3988_;
}
}
}
}
case 5:
{
lean_object* v_presentation_3989_; 
v_presentation_3989_ = lean_ctor_get(v_x_3789_, 0);
lean_inc_ref(v_presentation_3989_);
lean_dec_ref_known(v_x_3789_, 1);
if (lean_obj_tag(v_presentation_3989_) == 0)
{
lean_object* v_val_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
lean_dec_ref(v_config_3788_);
v_val_3990_ = lean_ctor_get(v_presentation_3989_, 0);
lean_inc(v_val_3990_);
lean_dec_ref_known(v_presentation_3989_, 1);
v___x_3991_ = lean_unsigned_to_nat(1u);
v___x_3992_ = lean_unsigned_to_nat(12u);
v___x_3993_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3993_, 0, v_val_3990_);
v___x_3994_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3991_, v___x_3992_, v___x_3993_, v_a_3790_);
return v___x_3994_;
}
else
{
lean_object* v_val_3995_; uint8_t v___x_3996_; 
v_val_3995_ = lean_ctor_get(v_presentation_3989_, 0);
lean_inc(v_val_3995_);
lean_dec_ref_known(v_presentation_3989_, 1);
v___x_3996_ = lean_unbox(v_val_3995_);
lean_dec(v_val_3995_);
switch(v___x_3996_)
{
case 1:
{
lean_object* v_dateformat_3997_; lean_object* v_symbols_3998_; lean_object* v___x_3999_; 
v_dateformat_3997_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_3997_);
lean_dec_ref(v_config_3788_);
v_symbols_3998_ = lean_ctor_get(v_dateformat_3997_, 1);
lean_inc_ref(v_symbols_3998_);
lean_dec_ref(v_dateformat_3997_);
v___x_3999_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(v_symbols_3998_, v_a_3790_);
return v___x_3999_;
}
case 2:
{
lean_object* v_dateformat_4000_; lean_object* v_symbols_4001_; lean_object* v___x_4002_; 
v_dateformat_4000_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4000_);
lean_dec_ref(v_config_3788_);
v_symbols_4001_ = lean_ctor_get(v_dateformat_4000_, 1);
lean_inc_ref(v_symbols_4001_);
lean_dec_ref(v_dateformat_4000_);
v___x_4002_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(v_symbols_4001_, v_a_3790_);
return v___x_4002_;
}
default: 
{
lean_object* v_dateformat_4003_; lean_object* v_symbols_4004_; lean_object* v___x_4005_; 
v_dateformat_4003_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4003_);
lean_dec_ref(v_config_3788_);
v_symbols_4004_ = lean_ctor_get(v_dateformat_4003_, 1);
lean_inc_ref(v_symbols_4004_);
lean_dec_ref(v_dateformat_4003_);
v___x_4005_ = l_Std_Time_parseMonthShort(v_symbols_4004_, v_a_3790_);
return v___x_4005_;
}
}
}
}
case 6:
{
lean_object* v_presentation_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
lean_dec_ref(v_config_3788_);
v_presentation_4006_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_presentation_4006_);
lean_dec_ref_known(v_x_3789_, 1);
v___x_4007_ = lean_unsigned_to_nat(1u);
v___x_4008_ = lean_unsigned_to_nat(31u);
v___x_4009_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4009_, 0, v_presentation_4006_);
v___x_4010_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4007_, v___x_4008_, v___x_4009_, v_a_3790_);
return v___x_4010_;
}
case 7:
{
lean_object* v_presentation_4011_; 
v_presentation_4011_ = lean_ctor_get(v_x_3789_, 0);
lean_inc_ref(v_presentation_4011_);
lean_dec_ref_known(v_x_3789_, 1);
if (lean_obj_tag(v_presentation_4011_) == 0)
{
lean_object* v_val_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; 
lean_dec_ref(v_config_3788_);
v_val_4012_ = lean_ctor_get(v_presentation_4011_, 0);
lean_inc(v_val_4012_);
lean_dec_ref_known(v_presentation_4011_, 1);
v___x_4013_ = lean_unsigned_to_nat(1u);
v___x_4014_ = lean_unsigned_to_nat(4u);
v___x_4015_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4015_, 0, v_val_4012_);
v___x_4016_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4013_, v___x_4014_, v___x_4015_, v_a_3790_);
return v___x_4016_;
}
else
{
lean_object* v_val_4017_; uint8_t v___x_4018_; 
v_val_4017_ = lean_ctor_get(v_presentation_4011_, 0);
lean_inc(v_val_4017_);
lean_dec_ref_known(v_presentation_4011_, 1);
v___x_4018_ = lean_unbox(v_val_4017_);
lean_dec(v_val_4017_);
switch(v___x_4018_)
{
case 0:
{
lean_object* v_dateformat_4019_; lean_object* v_symbols_4020_; lean_object* v___x_4021_; 
v_dateformat_4019_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4019_);
lean_dec_ref(v_config_3788_);
v_symbols_4020_ = lean_ctor_get(v_dateformat_4019_, 1);
lean_inc_ref(v_symbols_4020_);
lean_dec_ref(v_dateformat_4019_);
v___x_4021_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(v_symbols_4020_, v_a_3790_);
return v___x_4021_;
}
case 1:
{
lean_object* v_dateformat_4022_; lean_object* v_symbols_4023_; lean_object* v___x_4024_; 
v_dateformat_4022_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4022_);
lean_dec_ref(v_config_3788_);
v_symbols_4023_ = lean_ctor_get(v_dateformat_4022_, 1);
lean_inc_ref(v_symbols_4023_);
lean_dec_ref(v_dateformat_4022_);
v___x_4024_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(v_symbols_4023_, v_a_3790_);
return v___x_4024_;
}
default: 
{
lean_object* v_dateformat_4025_; lean_object* v_symbols_4026_; lean_object* v___x_4027_; 
v_dateformat_4025_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4025_);
lean_dec_ref(v_config_3788_);
v_symbols_4026_ = lean_ctor_get(v_dateformat_4025_, 1);
lean_inc_ref(v_symbols_4026_);
lean_dec_ref(v_dateformat_4025_);
v___x_4027_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(v_symbols_4026_, v_a_3790_);
return v___x_4027_;
}
}
}
}
case 8:
{
lean_object* v_presentation_4028_; 
v_presentation_4028_ = lean_ctor_get(v_x_3789_, 0);
lean_inc_ref(v_presentation_4028_);
lean_dec_ref_known(v_x_3789_, 1);
if (lean_obj_tag(v_presentation_4028_) == 0)
{
lean_object* v_val_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
lean_dec_ref(v_config_3788_);
v_val_4029_ = lean_ctor_get(v_presentation_4028_, 0);
lean_inc(v_val_4029_);
lean_dec_ref_known(v_presentation_4028_, 1);
v___x_4030_ = lean_unsigned_to_nat(1u);
v___x_4031_ = lean_unsigned_to_nat(4u);
v___x_4032_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4032_, 0, v_val_4029_);
v___x_4033_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4030_, v___x_4031_, v___x_4032_, v_a_3790_);
return v___x_4033_;
}
else
{
lean_object* v_val_4034_; uint8_t v___x_4035_; 
v_val_4034_ = lean_ctor_get(v_presentation_4028_, 0);
lean_inc(v_val_4034_);
lean_dec_ref_known(v_presentation_4028_, 1);
v___x_4035_ = lean_unbox(v_val_4034_);
lean_dec(v_val_4034_);
switch(v___x_4035_)
{
case 0:
{
lean_object* v_dateformat_4036_; lean_object* v_symbols_4037_; lean_object* v___x_4038_; 
v_dateformat_4036_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4036_);
lean_dec_ref(v_config_3788_);
v_symbols_4037_ = lean_ctor_get(v_dateformat_4036_, 1);
lean_inc_ref(v_symbols_4037_);
lean_dec_ref(v_dateformat_4036_);
v___x_4038_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(v_symbols_4037_, v_a_3790_);
return v___x_4038_;
}
case 1:
{
lean_object* v_dateformat_4039_; lean_object* v_symbols_4040_; lean_object* v___x_4041_; 
v_dateformat_4039_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4039_);
lean_dec_ref(v_config_3788_);
v_symbols_4040_ = lean_ctor_get(v_dateformat_4039_, 1);
lean_inc_ref(v_symbols_4040_);
lean_dec_ref(v_dateformat_4039_);
v___x_4041_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(v_symbols_4040_, v_a_3790_);
return v___x_4041_;
}
default: 
{
lean_object* v_dateformat_4042_; lean_object* v_symbols_4043_; lean_object* v___x_4044_; 
v_dateformat_4042_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4042_);
lean_dec_ref(v_config_3788_);
v_symbols_4043_ = lean_ctor_get(v_dateformat_4042_, 1);
lean_inc_ref(v_symbols_4043_);
lean_dec_ref(v_dateformat_4042_);
v___x_4044_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(v_symbols_4043_, v_a_3790_);
return v___x_4044_;
}
}
}
}
case 9:
{
lean_object* v_presentation_4045_; 
lean_dec_ref(v_config_3788_);
v_presentation_4045_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_presentation_4045_);
lean_dec_ref_known(v_x_3789_, 1);
switch(lean_obj_tag(v_presentation_4045_))
{
case 0:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4046_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0));
v___x_4047_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4046_, v_a_3790_);
return v___x_4047_;
}
case 1:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4048_ = lean_unsigned_to_nat(2u);
v___x_4049_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_4048_, v_a_3790_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_pos_4050_; lean_object* v_res_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4061_; 
v_pos_4050_ = lean_ctor_get(v___x_4049_, 0);
v_res_4051_ = lean_ctor_get(v___x_4049_, 1);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4053_ = v___x_4049_;
v_isShared_4054_ = v_isSharedCheck_4061_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_res_4051_);
lean_inc(v_pos_4050_);
lean_dec(v___x_4049_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4061_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4059_; 
v___x_4055_ = lean_nat_to_int(v_res_4051_);
v___x_4056_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_4057_ = lean_int_add(v___x_4056_, v___x_4055_);
lean_dec(v___x_4055_);
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 1, v___x_4057_);
v___x_4059_ = v___x_4053_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_pos_4050_);
lean_ctor_set(v_reuseFailAlloc_4060_, 1, v___x_4057_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
else
{
lean_object* v_pos_4062_; lean_object* v_err_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
v_pos_4062_ = lean_ctor_get(v___x_4049_, 0);
v_err_4063_ = lean_ctor_get(v___x_4049_, 1);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4065_ = v___x_4049_;
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_err_4063_);
lean_inc(v_pos_4062_);
lean_dec(v___x_4049_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_pos_4062_);
lean_ctor_set(v_reuseFailAlloc_4069_, 1, v_err_4063_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
case 2:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4071_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2));
v___x_4072_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4071_, v_a_3790_);
return v___x_4072_;
}
default: 
{
lean_object* v_num_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v_num_4073_ = lean_ctor_get(v_presentation_4045_, 0);
lean_inc(v_num_4073_);
lean_dec_ref_known(v_presentation_4045_, 1);
v___x_4074_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed), 2, 1);
lean_closure_set(v___x_4074_, 0, v_num_4073_);
v___x_4075_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4074_, v_a_3790_);
return v___x_4075_;
}
}
}
case 10:
{
lean_object* v_presentation_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
lean_dec_ref(v_config_3788_);
v_presentation_4076_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_presentation_4076_);
lean_dec_ref_known(v_x_3789_, 1);
v___x_4077_ = lean_unsigned_to_nat(1u);
v___x_4078_ = lean_unsigned_to_nat(53u);
v___x_4079_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4079_, 0, v_presentation_4076_);
v___x_4080_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4077_, v___x_4078_, v___x_4079_, v_a_3790_);
return v___x_4080_;
}
case 11:
{
lean_object* v_presentation_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; 
lean_dec_ref(v_config_3788_);
v_presentation_4081_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_presentation_4081_);
lean_dec_ref_known(v_x_3789_, 1);
v___x_4082_ = lean_unsigned_to_nat(1u);
v___x_4083_ = lean_unsigned_to_nat(6u);
v___x_4084_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4084_, 0, v_presentation_4081_);
v___x_4085_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4082_, v___x_4083_, v___x_4084_, v_a_3790_);
return v___x_4085_;
}
case 12:
{
uint8_t v_presentation_4086_; 
v_presentation_4086_ = lean_ctor_get_uint8(v_x_3789_, 0);
lean_dec_ref_known(v_x_3789_, 0);
switch(v_presentation_4086_)
{
case 1:
{
lean_object* v_dateformat_4087_; lean_object* v_symbols_4088_; lean_object* v___x_4089_; 
v_dateformat_4087_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4087_);
lean_dec_ref(v_config_3788_);
v_symbols_4088_ = lean_ctor_get(v_dateformat_4087_, 1);
lean_inc_ref(v_symbols_4088_);
lean_dec_ref(v_dateformat_4087_);
v___x_4089_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4088_, v_a_3790_);
return v___x_4089_;
}
case 2:
{
lean_object* v_dateformat_4090_; lean_object* v_symbols_4091_; lean_object* v___x_4092_; 
v_dateformat_4090_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4090_);
lean_dec_ref(v_config_3788_);
v_symbols_4091_ = lean_ctor_get(v_dateformat_4090_, 1);
lean_inc_ref(v_symbols_4091_);
lean_dec_ref(v_dateformat_4090_);
v___x_4092_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4091_, v_a_3790_);
return v___x_4092_;
}
default: 
{
lean_object* v_dateformat_4093_; lean_object* v_symbols_4094_; lean_object* v___x_4095_; 
v_dateformat_4093_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4093_);
lean_dec_ref(v_config_3788_);
v_symbols_4094_ = lean_ctor_get(v_dateformat_4093_, 1);
lean_inc_ref(v_symbols_4094_);
lean_dec_ref(v_dateformat_4093_);
v___x_4095_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4094_, v_a_3790_);
return v___x_4095_;
}
}
}
case 13:
{
lean_object* v_presentation_4096_; 
v_presentation_4096_ = lean_ctor_get(v_x_3789_, 0);
lean_inc_ref(v_presentation_4096_);
lean_dec_ref_known(v_x_3789_, 1);
if (lean_obj_tag(v_presentation_4096_) == 0)
{
lean_object* v_val_4097_; lean_object* v___x_4098_; 
v_val_4097_ = lean_ctor_get(v_presentation_4096_, 0);
lean_inc(v_val_4097_);
lean_dec_ref_known(v_presentation_4096_, 1);
v___x_4098_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_val_4097_, v_a_3790_);
lean_dec(v_val_4097_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v_pos_4099_; lean_object* v_res_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4136_; 
v_pos_4099_ = lean_ctor_get(v___x_4098_, 0);
v_res_4100_ = lean_ctor_get(v___x_4098_, 1);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4102_ = v___x_4098_;
v_isShared_4103_ = v_isSharedCheck_4136_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_res_4100_);
lean_inc(v_pos_4099_);
lean_dec(v___x_4098_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4136_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
uint8_t v___y_4105_; lean_object* v___x_4132_; uint8_t v___x_4133_; 
v___x_4132_ = lean_unsigned_to_nat(1u);
v___x_4133_ = lean_nat_dec_le(v___x_4132_, v_res_4100_);
if (v___x_4133_ == 0)
{
v___y_4105_ = v___x_4133_;
goto v___jp_4104_;
}
else
{
lean_object* v___x_4134_; uint8_t v___x_4135_; 
v___x_4134_ = lean_unsigned_to_nat(7u);
v___x_4135_ = lean_nat_dec_le(v_res_4100_, v___x_4134_);
v___y_4105_ = v___x_4135_;
goto v___jp_4104_;
}
v___jp_4104_:
{
if (v___y_4105_ == 0)
{
lean_object* v___x_4106_; lean_object* v___x_4108_; 
lean_dec(v_res_4100_);
lean_dec_ref(v_config_3788_);
v___x_4106_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4));
if (v_isShared_4103_ == 0)
{
lean_ctor_set_tag(v___x_4102_, 1);
lean_ctor_set(v___x_4102_, 1, v___x_4106_);
v___x_4108_ = v___x_4102_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_pos_4099_);
lean_ctor_set(v_reuseFailAlloc_4109_, 1, v___x_4106_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
else
{
lean_object* v_dateformat_4110_; uint8_t v_firstDayOfWeek_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v_range_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; uint8_t v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4130_; 
v_dateformat_4110_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4110_);
lean_dec_ref(v_config_3788_);
v_firstDayOfWeek_4111_ = lean_ctor_get_uint8(v_dateformat_4110_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_4110_);
v___x_4112_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_4111_);
v___x_4113_ = lean_nat_to_int(v_res_4100_);
v___x_4114_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_4115_ = lean_int_sub(v___x_4113_, v___x_4114_);
lean_dec(v___x_4113_);
v___x_4116_ = lean_int_add(v___x_4115_, v___x_4112_);
lean_dec(v___x_4112_);
lean_dec(v___x_4115_);
v___x_4117_ = lean_int_sub(v___x_4116_, v___x_4114_);
lean_dec(v___x_4116_);
v___x_4118_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_4119_ = lean_int_emod(v___x_4117_, v___x_4118_);
lean_dec(v___x_4117_);
v___x_4120_ = lean_int_add(v___x_4119_, v___x_4114_);
lean_dec(v___x_4119_);
v_range_4121_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6);
v___x_4122_ = lean_int_sub(v___x_4120_, v___x_4114_);
lean_dec(v___x_4120_);
v___x_4123_ = lean_int_emod(v___x_4122_, v_range_4121_);
lean_dec(v___x_4122_);
v___x_4124_ = lean_int_add(v___x_4123_, v_range_4121_);
lean_dec(v___x_4123_);
v___x_4125_ = lean_int_emod(v___x_4124_, v_range_4121_);
lean_dec(v___x_4124_);
v___x_4126_ = lean_int_add(v___x_4125_, v___x_4114_);
lean_dec(v___x_4125_);
v___x_4127_ = l_Std_Time_Weekday_ofOrdinal(v___x_4126_);
lean_dec(v___x_4126_);
v___x_4128_ = lean_box(v___x_4127_);
if (v_isShared_4103_ == 0)
{
lean_ctor_set(v___x_4102_, 1, v___x_4128_);
v___x_4130_ = v___x_4102_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_pos_4099_);
lean_ctor_set(v_reuseFailAlloc_4131_, 1, v___x_4128_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
}
}
else
{
lean_object* v_pos_4137_; lean_object* v_err_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4145_; 
lean_dec_ref(v_config_3788_);
v_pos_4137_ = lean_ctor_get(v___x_4098_, 0);
v_err_4138_ = lean_ctor_get(v___x_4098_, 1);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4140_ = v___x_4098_;
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_err_4138_);
lean_inc(v_pos_4137_);
lean_dec(v___x_4098_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4143_; 
if (v_isShared_4141_ == 0)
{
v___x_4143_ = v___x_4140_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_pos_4137_);
lean_ctor_set(v_reuseFailAlloc_4144_, 1, v_err_4138_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
}
else
{
lean_object* v_val_4146_; uint8_t v___x_4147_; 
v_val_4146_ = lean_ctor_get(v_presentation_4096_, 0);
lean_inc(v_val_4146_);
lean_dec_ref_known(v_presentation_4096_, 1);
v___x_4147_ = lean_unbox(v_val_4146_);
lean_dec(v_val_4146_);
switch(v___x_4147_)
{
case 0:
{
lean_object* v_dateformat_4148_; lean_object* v_symbols_4149_; lean_object* v___x_4150_; 
v_dateformat_4148_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4148_);
lean_dec_ref(v_config_3788_);
v_symbols_4149_ = lean_ctor_get(v_dateformat_4148_, 1);
lean_inc_ref(v_symbols_4149_);
lean_dec_ref(v_dateformat_4148_);
v___x_4150_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4149_, v_a_3790_);
return v___x_4150_;
}
case 1:
{
lean_object* v_dateformat_4151_; lean_object* v_symbols_4152_; lean_object* v___x_4153_; 
v_dateformat_4151_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4151_);
lean_dec_ref(v_config_3788_);
v_symbols_4152_ = lean_ctor_get(v_dateformat_4151_, 1);
lean_inc_ref(v_symbols_4152_);
lean_dec_ref(v_dateformat_4151_);
v___x_4153_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4152_, v_a_3790_);
return v___x_4153_;
}
case 2:
{
lean_object* v_dateformat_4154_; lean_object* v_symbols_4155_; lean_object* v___x_4156_; 
v_dateformat_4154_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4154_);
lean_dec_ref(v_config_3788_);
v_symbols_4155_ = lean_ctor_get(v_dateformat_4154_, 1);
lean_inc_ref(v_symbols_4155_);
lean_dec_ref(v_dateformat_4154_);
v___x_4156_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4155_, v_a_3790_);
return v___x_4156_;
}
default: 
{
lean_object* v_dateformat_4157_; lean_object* v_symbols_4158_; lean_object* v___x_4159_; 
v_dateformat_4157_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4157_);
lean_dec_ref(v_config_3788_);
v_symbols_4158_ = lean_ctor_get(v_dateformat_4157_, 1);
lean_inc_ref(v_symbols_4158_);
lean_dec_ref(v_dateformat_4157_);
v___x_4159_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(v_symbols_4158_, v_a_3790_);
return v___x_4159_;
}
}
}
}
case 14:
{
lean_object* v_presentation_4160_; 
v_presentation_4160_ = lean_ctor_get(v_x_3789_, 0);
lean_inc_ref(v_presentation_4160_);
lean_dec_ref_known(v_x_3789_, 1);
if (lean_obj_tag(v_presentation_4160_) == 0)
{
lean_object* v_val_4161_; lean_object* v___x_4162_; 
v_val_4161_ = lean_ctor_get(v_presentation_4160_, 0);
lean_inc(v_val_4161_);
lean_dec_ref_known(v_presentation_4160_, 1);
v___x_4162_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_val_4161_, v_a_3790_);
lean_dec(v_val_4161_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_pos_4163_; lean_object* v_res_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4200_; 
v_pos_4163_ = lean_ctor_get(v___x_4162_, 0);
v_res_4164_ = lean_ctor_get(v___x_4162_, 1);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4166_ = v___x_4162_;
v_isShared_4167_ = v_isSharedCheck_4200_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_res_4164_);
lean_inc(v_pos_4163_);
lean_dec(v___x_4162_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4200_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
uint8_t v___y_4169_; lean_object* v___x_4196_; uint8_t v___x_4197_; 
v___x_4196_ = lean_unsigned_to_nat(1u);
v___x_4197_ = lean_nat_dec_le(v___x_4196_, v_res_4164_);
if (v___x_4197_ == 0)
{
v___y_4169_ = v___x_4197_;
goto v___jp_4168_;
}
else
{
lean_object* v___x_4198_; uint8_t v___x_4199_; 
v___x_4198_ = lean_unsigned_to_nat(7u);
v___x_4199_ = lean_nat_dec_le(v_res_4164_, v___x_4198_);
v___y_4169_ = v___x_4199_;
goto v___jp_4168_;
}
v___jp_4168_:
{
if (v___y_4169_ == 0)
{
lean_object* v___x_4170_; lean_object* v___x_4172_; 
lean_dec(v_res_4164_);
lean_dec_ref(v_config_3788_);
v___x_4170_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4));
if (v_isShared_4167_ == 0)
{
lean_ctor_set_tag(v___x_4166_, 1);
lean_ctor_set(v___x_4166_, 1, v___x_4170_);
v___x_4172_ = v___x_4166_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_pos_4163_);
lean_ctor_set(v_reuseFailAlloc_4173_, 1, v___x_4170_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
else
{
lean_object* v_dateformat_4174_; uint8_t v_firstDayOfWeek_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v_range_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; uint8_t v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4194_; 
v_dateformat_4174_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4174_);
lean_dec_ref(v_config_3788_);
v_firstDayOfWeek_4175_ = lean_ctor_get_uint8(v_dateformat_4174_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_4174_);
v___x_4176_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_4175_);
v___x_4177_ = lean_nat_to_int(v_res_4164_);
v___x_4178_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_4179_ = lean_int_sub(v___x_4177_, v___x_4178_);
lean_dec(v___x_4177_);
v___x_4180_ = lean_int_add(v___x_4179_, v___x_4176_);
lean_dec(v___x_4176_);
lean_dec(v___x_4179_);
v___x_4181_ = lean_int_sub(v___x_4180_, v___x_4178_);
lean_dec(v___x_4180_);
v___x_4182_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_4183_ = lean_int_emod(v___x_4181_, v___x_4182_);
lean_dec(v___x_4181_);
v___x_4184_ = lean_int_add(v___x_4183_, v___x_4178_);
lean_dec(v___x_4183_);
v_range_4185_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6);
v___x_4186_ = lean_int_sub(v___x_4184_, v___x_4178_);
lean_dec(v___x_4184_);
v___x_4187_ = lean_int_emod(v___x_4186_, v_range_4185_);
lean_dec(v___x_4186_);
v___x_4188_ = lean_int_add(v___x_4187_, v_range_4185_);
lean_dec(v___x_4187_);
v___x_4189_ = lean_int_emod(v___x_4188_, v_range_4185_);
lean_dec(v___x_4188_);
v___x_4190_ = lean_int_add(v___x_4189_, v___x_4178_);
lean_dec(v___x_4189_);
v___x_4191_ = l_Std_Time_Weekday_ofOrdinal(v___x_4190_);
lean_dec(v___x_4190_);
v___x_4192_ = lean_box(v___x_4191_);
if (v_isShared_4167_ == 0)
{
lean_ctor_set(v___x_4166_, 1, v___x_4192_);
v___x_4194_ = v___x_4166_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_pos_4163_);
lean_ctor_set(v_reuseFailAlloc_4195_, 1, v___x_4192_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
}
}
}
else
{
lean_object* v_pos_4201_; lean_object* v_err_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4209_; 
lean_dec_ref(v_config_3788_);
v_pos_4201_ = lean_ctor_get(v___x_4162_, 0);
v_err_4202_ = lean_ctor_get(v___x_4162_, 1);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4204_ = v___x_4162_;
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_err_4202_);
lean_inc(v_pos_4201_);
lean_dec(v___x_4162_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_pos_4201_);
lean_ctor_set(v_reuseFailAlloc_4208_, 1, v_err_4202_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
else
{
lean_object* v_val_4210_; uint8_t v___x_4211_; 
v_val_4210_ = lean_ctor_get(v_presentation_4160_, 0);
lean_inc(v_val_4210_);
lean_dec_ref_known(v_presentation_4160_, 1);
v___x_4211_ = lean_unbox(v_val_4210_);
lean_dec(v_val_4210_);
switch(v___x_4211_)
{
case 0:
{
lean_object* v_dateformat_4212_; lean_object* v_symbols_4213_; lean_object* v___x_4214_; 
v_dateformat_4212_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4212_);
lean_dec_ref(v_config_3788_);
v_symbols_4213_ = lean_ctor_get(v_dateformat_4212_, 1);
lean_inc_ref(v_symbols_4213_);
lean_dec_ref(v_dateformat_4212_);
v___x_4214_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4213_, v_a_3790_);
return v___x_4214_;
}
case 1:
{
lean_object* v_dateformat_4215_; lean_object* v_symbols_4216_; lean_object* v___x_4217_; 
v_dateformat_4215_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4215_);
lean_dec_ref(v_config_3788_);
v_symbols_4216_ = lean_ctor_get(v_dateformat_4215_, 1);
lean_inc_ref(v_symbols_4216_);
lean_dec_ref(v_dateformat_4215_);
v___x_4217_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4216_, v_a_3790_);
return v___x_4217_;
}
case 2:
{
lean_object* v_dateformat_4218_; lean_object* v_symbols_4219_; lean_object* v___x_4220_; 
v_dateformat_4218_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4218_);
lean_dec_ref(v_config_3788_);
v_symbols_4219_ = lean_ctor_get(v_dateformat_4218_, 1);
lean_inc_ref(v_symbols_4219_);
lean_dec_ref(v_dateformat_4218_);
v___x_4220_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4219_, v_a_3790_);
return v___x_4220_;
}
default: 
{
lean_object* v_dateformat_4221_; lean_object* v_symbols_4222_; lean_object* v___x_4223_; 
v_dateformat_4221_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4221_);
lean_dec_ref(v_config_3788_);
v_symbols_4222_ = lean_ctor_get(v_dateformat_4221_, 1);
lean_inc_ref(v_symbols_4222_);
lean_dec_ref(v_dateformat_4221_);
v___x_4223_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(v_symbols_4222_, v_a_3790_);
return v___x_4223_;
}
}
}
}
case 15:
{
lean_object* v_presentation_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
lean_dec_ref(v_config_3788_);
v_presentation_4224_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_presentation_4224_);
lean_dec_ref_known(v_x_3789_, 1);
v___x_4225_ = lean_unsigned_to_nat(1u);
v___x_4226_ = lean_unsigned_to_nat(5u);
v___x_4227_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4227_, 0, v_presentation_4224_);
v___x_4228_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4225_, v___x_4226_, v___x_4227_, v_a_3790_);
return v___x_4228_;
}
case 16:
{
uint8_t v_presentation_4229_; 
v_presentation_4229_ = lean_ctor_get_uint8(v_x_3789_, 0);
lean_dec_ref_known(v_x_3789_, 0);
switch(v_presentation_4229_)
{
case 1:
{
lean_object* v_dateformat_4230_; lean_object* v_symbols_4231_; lean_object* v___x_4232_; 
v_dateformat_4230_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4230_);
lean_dec_ref(v_config_3788_);
v_symbols_4231_ = lean_ctor_get(v_dateformat_4230_, 1);
lean_inc_ref(v_symbols_4231_);
lean_dec_ref(v_dateformat_4230_);
v___x_4232_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerLong(v_symbols_4231_, v_a_3790_);
return v___x_4232_;
}
case 2:
{
lean_object* v_dateformat_4233_; lean_object* v_symbols_4234_; lean_object* v___x_4235_; 
v_dateformat_4233_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4233_);
lean_dec_ref(v_config_3788_);
v_symbols_4234_ = lean_ctor_get(v_dateformat_4233_, 1);
lean_inc_ref(v_symbols_4234_);
lean_dec_ref(v_dateformat_4233_);
v___x_4235_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerNarrow(v_symbols_4234_, v_a_3790_);
return v___x_4235_;
}
default: 
{
lean_object* v_dateformat_4236_; lean_object* v_symbols_4237_; lean_object* v___x_4238_; 
v_dateformat_4236_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4236_);
lean_dec_ref(v_config_3788_);
v_symbols_4237_ = lean_ctor_get(v_dateformat_4236_, 1);
lean_inc_ref(v_symbols_4237_);
lean_dec_ref(v_dateformat_4236_);
v___x_4238_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerShort(v_symbols_4237_, v_a_3790_);
return v___x_4238_;
}
}
}
case 17:
{
uint8_t v_presentation_4239_; 
v_presentation_4239_ = lean_ctor_get_uint8(v_x_3789_, 0);
lean_dec_ref_known(v_x_3789_, 0);
switch(v_presentation_4239_)
{
case 1:
{
lean_object* v_dateformat_4240_; lean_object* v_symbols_4241_; lean_object* v_dayPeriodLong_4242_; lean_object* v___x_4243_; 
v_dateformat_4240_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4240_);
lean_dec_ref(v_config_3788_);
v_symbols_4241_ = lean_ctor_get(v_dateformat_4240_, 1);
lean_inc_ref(v_symbols_4241_);
lean_dec_ref(v_dateformat_4240_);
v_dayPeriodLong_4242_ = lean_ctor_get(v_symbols_4241_, 20);
lean_inc_ref(v_dayPeriodLong_4242_);
lean_dec_ref(v_symbols_4241_);
v___x_4243_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodLong_4242_, v_a_3790_);
return v___x_4243_;
}
case 2:
{
lean_object* v_dateformat_4244_; lean_object* v_symbols_4245_; lean_object* v_dayPeriodNarrow_4246_; lean_object* v___x_4247_; 
v_dateformat_4244_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4244_);
lean_dec_ref(v_config_3788_);
v_symbols_4245_ = lean_ctor_get(v_dateformat_4244_, 1);
lean_inc_ref(v_symbols_4245_);
lean_dec_ref(v_dateformat_4244_);
v_dayPeriodNarrow_4246_ = lean_ctor_get(v_symbols_4245_, 21);
lean_inc_ref(v_dayPeriodNarrow_4246_);
lean_dec_ref(v_symbols_4245_);
v___x_4247_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodNarrow_4246_, v_a_3790_);
return v___x_4247_;
}
default: 
{
lean_object* v_dateformat_4248_; lean_object* v_symbols_4249_; lean_object* v_dayPeriodShort_4250_; lean_object* v___x_4251_; 
v_dateformat_4248_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4248_);
lean_dec_ref(v_config_3788_);
v_symbols_4249_ = lean_ctor_get(v_dateformat_4248_, 1);
lean_inc_ref(v_symbols_4249_);
lean_dec_ref(v_dateformat_4248_);
v_dayPeriodShort_4250_ = lean_ctor_get(v_symbols_4249_, 19);
lean_inc_ref(v_dayPeriodShort_4250_);
lean_dec_ref(v_symbols_4249_);
v___x_4251_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodShort_4250_, v_a_3790_);
return v___x_4251_;
}
}
}
case 18:
{
uint8_t v_presentation_4252_; 
v_presentation_4252_ = lean_ctor_get_uint8(v_x_3789_, 0);
lean_dec_ref_known(v_x_3789_, 0);
switch(v_presentation_4252_)
{
case 1:
{
lean_object* v_dateformat_4253_; lean_object* v_symbols_4254_; lean_object* v_extendedDayPeriodLong_4255_; lean_object* v___x_4256_; 
v_dateformat_4253_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4253_);
lean_dec_ref(v_config_3788_);
v_symbols_4254_ = lean_ctor_get(v_dateformat_4253_, 1);
lean_inc_ref(v_symbols_4254_);
lean_dec_ref(v_dateformat_4253_);
v_extendedDayPeriodLong_4255_ = lean_ctor_get(v_symbols_4254_, 23);
lean_inc_ref(v_extendedDayPeriodLong_4255_);
lean_dec_ref(v_symbols_4254_);
v___x_4256_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodLong_4255_, v_a_3790_);
lean_dec_ref(v_extendedDayPeriodLong_4255_);
return v___x_4256_;
}
case 2:
{
lean_object* v_dateformat_4257_; lean_object* v_symbols_4258_; lean_object* v_extendedDayPeriodNarrow_4259_; lean_object* v___x_4260_; 
v_dateformat_4257_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4257_);
lean_dec_ref(v_config_3788_);
v_symbols_4258_ = lean_ctor_get(v_dateformat_4257_, 1);
lean_inc_ref(v_symbols_4258_);
lean_dec_ref(v_dateformat_4257_);
v_extendedDayPeriodNarrow_4259_ = lean_ctor_get(v_symbols_4258_, 24);
lean_inc_ref(v_extendedDayPeriodNarrow_4259_);
lean_dec_ref(v_symbols_4258_);
v___x_4260_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodNarrow_4259_, v_a_3790_);
lean_dec_ref(v_extendedDayPeriodNarrow_4259_);
return v___x_4260_;
}
default: 
{
lean_object* v_dateformat_4261_; lean_object* v_symbols_4262_; lean_object* v_extendedDayPeriodShort_4263_; lean_object* v___x_4264_; 
v_dateformat_4261_ = lean_ctor_get(v_config_3788_, 0);
lean_inc_ref(v_dateformat_4261_);
lean_dec_ref(v_config_3788_);
v_symbols_4262_ = lean_ctor_get(v_dateformat_4261_, 1);
lean_inc_ref(v_symbols_4262_);
lean_dec_ref(v_dateformat_4261_);
v_extendedDayPeriodShort_4263_ = lean_ctor_get(v_symbols_4262_, 22);
lean_inc_ref(v_extendedDayPeriodShort_4263_);
lean_dec_ref(v_symbols_4262_);
v___x_4264_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodShort_4263_, v_a_3790_);
lean_dec_ref(v_extendedDayPeriodShort_4263_);
return v___x_4264_;
}
}
}
case 19:
{
lean_object* v_presentation_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
lean_dec_ref(v_config_3788_);
v_presentation_4265_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_presentation_4265_);
lean_dec_ref_known(v_x_3789_, 1);
v___x_4266_ = lean_unsigned_to_nat(1u);
v___x_4267_ = lean_unsigned_to_nat(12u);
v___x_4268_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4268_, 0, v_presentation_4265_);
v___x_4269_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4266_, v___x_4267_, v___x_4268_, v_a_3790_);
return v___x_4269_;
}
case 20:
{
lean_object* v_presentation_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
lean_dec_ref(v_config_3788_);
v_presentation_4270_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_presentation_4270_);
lean_dec_ref_known(v_x_3789_, 1);
v___x_4271_ = lean_unsigned_to_nat(0u);
v___x_4272_ = lean_unsigned_to_nat(11u);
v___x_4273_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4273_, 0, v_presentation_4270_);
v___x_4274_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4271_, v___x_4272_, v___x_4273_, v_a_3790_);
return v___x_4274_;
}
case 21:
{
lean_object* v_presentation_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
lean_dec_ref(v_config_3788_);
v_presentation_4275_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_presentation_4275_);
lean_dec_ref_known(v_x_3789_, 1);
v___x_4276_ = lean_unsigned_to_nat(1u);
v___x_4277_ = lean_unsigned_to_nat(24u);
v___x_4278_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4278_, 0, v_presentation_4275_);
v___x_4279_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4276_, v___x_4277_, v___x_4278_, v_a_3790_);
return v___x_4279_;
}
case 22:
{
lean_object* v_presentation_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
lean_dec_ref(v_config_3788_);
v_presentation_4280_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_presentation_4280_);
lean_dec_ref_known(v_x_3789_, 1);
v___x_4281_ = lean_unsigned_to_nat(0u);
v___x_4282_ = lean_unsigned_to_nat(23u);
v___x_4283_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4283_, 0, v_presentation_4280_);
v___x_4284_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4281_, v___x_4282_, v___x_4283_, v_a_3790_);
return v___x_4284_;
}
case 23:
{
lean_object* v_presentation_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
lean_dec_ref(v_config_3788_);
v_presentation_4285_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_presentation_4285_);
lean_dec_ref_known(v_x_3789_, 1);
v___x_4286_ = lean_unsigned_to_nat(0u);
v___x_4287_ = lean_unsigned_to_nat(59u);
v___x_4288_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4288_, 0, v_presentation_4285_);
v___x_4289_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4286_, v___x_4287_, v___x_4288_, v_a_3790_);
return v___x_4289_;
}
case 24:
{
uint8_t v_allowLeapSeconds_4290_; 
v_allowLeapSeconds_4290_ = lean_ctor_get_uint8(v_config_3788_, sizeof(void*)*1);
lean_dec_ref(v_config_3788_);
if (v_allowLeapSeconds_4290_ == 0)
{
lean_object* v_presentation_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v_presentation_4291_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_presentation_4291_);
lean_dec_ref_known(v_x_3789_, 1);
v___x_4292_ = lean_unsigned_to_nat(0u);
v___x_4293_ = lean_unsigned_to_nat(59u);
v___x_4294_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4294_, 0, v_presentation_4291_);
v___x_4295_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4292_, v___x_4293_, v___x_4294_, v_a_3790_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_pos_4296_; lean_object* v_res_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4304_; 
v_pos_4296_ = lean_ctor_get(v___x_4295_, 0);
v_res_4297_ = lean_ctor_get(v___x_4295_, 1);
v_isSharedCheck_4304_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_4299_ = v___x_4295_;
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_res_4297_);
lean_inc(v_pos_4296_);
lean_dec(v___x_4295_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4302_; 
if (v_isShared_4300_ == 0)
{
v___x_4302_ = v___x_4299_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_pos_4296_);
lean_ctor_set(v_reuseFailAlloc_4303_, 1, v_res_4297_);
v___x_4302_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
return v___x_4302_;
}
}
}
else
{
return v___x_4295_;
}
}
else
{
lean_object* v_presentation_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v_presentation_4305_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_presentation_4305_);
lean_dec_ref_known(v_x_3789_, 1);
v___x_4306_ = lean_unsigned_to_nat(0u);
v___x_4307_ = lean_unsigned_to_nat(60u);
v___x_4308_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4308_, 0, v_presentation_4305_);
v___x_4309_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4306_, v___x_4307_, v___x_4308_, v_a_3790_);
return v___x_4309_;
}
}
case 25:
{
lean_object* v_presentation_4310_; 
lean_dec_ref(v_config_3788_);
v_presentation_4310_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_presentation_4310_);
lean_dec_ref_known(v_x_3789_, 1);
if (lean_obj_tag(v_presentation_4310_) == 0)
{
lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4311_ = lean_unsigned_to_nat(0u);
v___x_4312_ = lean_unsigned_to_nat(999999999u);
v___x_4313_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__7));
v___x_4314_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4311_, v___x_4312_, v___x_4313_, v_a_3790_);
return v___x_4314_;
}
else
{
lean_object* v_digits_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v_digits_4315_ = lean_ctor_get(v_presentation_4310_, 0);
lean_inc(v_digits_4315_);
lean_dec_ref_known(v_presentation_4310_, 1);
v___x_4316_ = lean_unsigned_to_nat(0u);
v___x_4317_ = lean_unsigned_to_nat(999999999u);
v___x_4318_ = lean_unsigned_to_nat(9u);
v___x_4319_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed), 3, 2);
lean_closure_set(v___x_4319_, 0, v_digits_4315_);
lean_closure_set(v___x_4319_, 1, v___x_4318_);
v___x_4320_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4316_, v___x_4317_, v___x_4319_, v_a_3790_);
return v___x_4320_;
}
}
case 26:
{
lean_object* v_presentation_4321_; lean_object* v___x_4322_; 
lean_dec_ref(v_config_3788_);
v_presentation_4321_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_presentation_4321_);
lean_dec_ref_known(v_x_3789_, 1);
v___x_4322_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_presentation_4321_, v_a_3790_);
lean_dec(v_presentation_4321_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_pos_4323_; lean_object* v_res_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4332_; 
v_pos_4323_ = lean_ctor_get(v___x_4322_, 0);
v_res_4324_ = lean_ctor_get(v___x_4322_, 1);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4326_ = v___x_4322_;
v_isShared_4327_ = v_isSharedCheck_4332_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_res_4324_);
lean_inc(v_pos_4323_);
lean_dec(v___x_4322_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4332_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4328_; lean_object* v___x_4330_; 
v___x_4328_ = lean_nat_to_int(v_res_4324_);
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 1, v___x_4328_);
v___x_4330_ = v___x_4326_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_pos_4323_);
lean_ctor_set(v_reuseFailAlloc_4331_, 1, v___x_4328_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
else
{
lean_object* v_pos_4333_; lean_object* v_err_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
v_pos_4333_ = lean_ctor_get(v___x_4322_, 0);
v_err_4334_ = lean_ctor_get(v___x_4322_, 1);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4322_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_err_4334_);
lean_inc(v_pos_4333_);
lean_dec(v___x_4322_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_pos_4333_);
lean_ctor_set(v_reuseFailAlloc_4340_, 1, v_err_4334_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
}
case 27:
{
lean_object* v_presentation_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
lean_dec_ref(v_config_3788_);
v_presentation_4342_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_presentation_4342_);
lean_dec_ref_known(v_x_3789_, 1);
v___x_4343_ = lean_unsigned_to_nat(0u);
v___x_4344_ = lean_unsigned_to_nat(999999999u);
v___x_4345_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4345_, 0, v_presentation_4342_);
v___x_4346_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4343_, v___x_4344_, v___x_4345_, v_a_3790_);
return v___x_4346_;
}
case 28:
{
lean_object* v_presentation_4347_; lean_object* v___x_4348_; 
lean_dec_ref(v_config_3788_);
v_presentation_4347_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_presentation_4347_);
lean_dec_ref_known(v_x_3789_, 1);
v___x_4348_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_presentation_4347_, v_a_3790_);
lean_dec(v_presentation_4347_);
if (lean_obj_tag(v___x_4348_) == 0)
{
lean_object* v_pos_4349_; lean_object* v_res_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4358_; 
v_pos_4349_ = lean_ctor_get(v___x_4348_, 0);
v_res_4350_ = lean_ctor_get(v___x_4348_, 1);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4348_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4352_ = v___x_4348_;
v_isShared_4353_ = v_isSharedCheck_4358_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_res_4350_);
lean_inc(v_pos_4349_);
lean_dec(v___x_4348_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4358_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4354_; lean_object* v___x_4356_; 
v___x_4354_ = lean_nat_to_int(v_res_4350_);
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 1, v___x_4354_);
v___x_4356_ = v___x_4352_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_pos_4349_);
lean_ctor_set(v_reuseFailAlloc_4357_, 1, v___x_4354_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
}
else
{
lean_object* v_pos_4359_; lean_object* v_err_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
v_pos_4359_ = lean_ctor_get(v___x_4348_, 0);
v_err_4360_ = lean_ctor_get(v___x_4348_, 1);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4348_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___x_4348_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_err_4360_);
lean_inc(v_pos_4359_);
lean_dec(v___x_4348_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_pos_4359_);
lean_ctor_set(v_reuseFailAlloc_4366_, 1, v_err_4360_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
case 29:
{
uint8_t v_presentation_4368_; 
lean_dec_ref(v_config_3788_);
v_presentation_4368_ = lean_ctor_get_uint8(v_x_3789_, 0);
lean_dec_ref_known(v_x_3789_, 0);
if (v_presentation_4368_ == 0)
{
lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4369_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
v___x_4370_ = l_Std_Internal_Parsec_String_pstring(v___x_4369_, v_a_3790_);
if (lean_obj_tag(v___x_4370_) == 0)
{
lean_object* v_pos_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4378_; 
v_pos_4371_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4378_ == 0)
{
lean_object* v_unused_4379_; 
v_unused_4379_ = lean_ctor_get(v___x_4370_, 1);
lean_dec(v_unused_4379_);
v___x_4373_ = v___x_4370_;
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_pos_4371_);
lean_dec(v___x_4370_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4376_; 
if (v_isShared_4374_ == 0)
{
lean_ctor_set(v___x_4373_, 1, v___x_4369_);
v___x_4376_ = v___x_4373_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_pos_4371_);
lean_ctor_set(v_reuseFailAlloc_4377_, 1, v___x_4369_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
}
else
{
return v___x_4370_;
}
}
else
{
lean_object* v___x_4380_; 
v___x_4380_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(v_a_3790_);
return v___x_4380_;
}
}
case 32:
{
uint8_t v_presentation_4381_; 
lean_dec_ref(v_config_3788_);
v_presentation_4381_ = lean_ctor_get_uint8(v_x_3789_, 0);
lean_dec_ref_known(v_x_3789_, 0);
if (v_presentation_4381_ == 0)
{
lean_object* v___x_4382_; lean_object* v___x_4383_; 
v___x_4382_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4383_ = l_Std_Internal_Parsec_String_pstring(v___x_4382_, v_a_3790_);
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_object* v_pos_4384_; uint8_t v___x_4385_; uint8_t v___x_4386_; uint8_t v___x_4387_; lean_object* v___x_4388_; 
v_pos_4384_ = lean_ctor_get(v___x_4383_, 0);
lean_inc(v_pos_4384_);
lean_dec_ref_known(v___x_4383_, 2);
v___x_4385_ = 2;
v___x_4386_ = 1;
v___x_4387_ = 1;
v___x_4388_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4385_, v___x_4386_, v___x_4387_, v_pos_4384_);
return v___x_4388_;
}
else
{
lean_object* v_pos_4389_; lean_object* v_err_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4397_; 
v_pos_4389_ = lean_ctor_get(v___x_4383_, 0);
v_err_4390_ = lean_ctor_get(v___x_4383_, 1);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4392_ = v___x_4383_;
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_err_4390_);
lean_inc(v_pos_4389_);
lean_dec(v___x_4383_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_pos_4389_);
lean_ctor_set(v_reuseFailAlloc_4396_, 1, v_err_4390_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
}
else
{
lean_object* v___x_4398_; lean_object* v___x_4399_; 
v___x_4398_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4399_ = l_Std_Internal_Parsec_String_pstring(v___x_4398_, v_a_3790_);
if (lean_obj_tag(v___x_4399_) == 0)
{
lean_object* v_pos_4400_; uint8_t v___x_4401_; uint8_t v___x_4402_; uint8_t v___x_4403_; lean_object* v___x_4404_; 
v_pos_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc(v_pos_4400_);
lean_dec_ref_known(v___x_4399_, 2);
v___x_4401_ = 0;
v___x_4402_ = 2;
v___x_4403_ = 1;
v___x_4404_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4401_, v___x_4402_, v___x_4403_, v_pos_4400_);
return v___x_4404_;
}
else
{
lean_object* v_pos_4405_; lean_object* v_err_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4413_; 
v_pos_4405_ = lean_ctor_get(v___x_4399_, 0);
v_err_4406_ = lean_ctor_get(v___x_4399_, 1);
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4408_ = v___x_4399_;
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_err_4406_);
lean_inc(v_pos_4405_);
lean_dec(v___x_4399_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4411_; 
if (v_isShared_4409_ == 0)
{
v___x_4411_ = v___x_4408_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_pos_4405_);
lean_ctor_set(v_reuseFailAlloc_4412_, 1, v_err_4406_);
v___x_4411_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
return v___x_4411_;
}
}
}
}
}
case 33:
{
uint8_t v_presentation_4414_; 
lean_dec_ref(v_config_3788_);
v_presentation_4414_ = lean_ctor_get_uint8(v_x_3789_, 0);
lean_dec_ref_known(v_x_3789_, 0);
switch(v_presentation_4414_)
{
case 0:
{
uint8_t v___x_4415_; uint8_t v___x_4416_; uint8_t v___x_4417_; lean_object* v___x_4418_; 
v___x_4415_ = 2;
v___x_4416_ = 1;
v___x_4417_ = 0;
lean_inc_ref(v_a_3790_);
v___x_4418_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4415_, v___x_4416_, v___x_4417_, v_a_3790_);
v___y_3792_ = v___x_4418_;
goto v___jp_3791_;
}
case 1:
{
uint8_t v___x_4419_; uint8_t v___x_4420_; uint8_t v___x_4421_; lean_object* v___x_4422_; 
v___x_4419_ = 0;
v___x_4420_ = 1;
v___x_4421_ = 0;
lean_inc_ref(v_a_3790_);
v___x_4422_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4419_, v___x_4420_, v___x_4421_, v_a_3790_);
v___y_3792_ = v___x_4422_;
goto v___jp_3791_;
}
case 2:
{
uint8_t v___x_4423_; uint8_t v___x_4424_; uint8_t v___x_4425_; lean_object* v___x_4426_; 
v___x_4423_ = 0;
v___x_4424_ = 1;
v___x_4425_ = 1;
lean_inc_ref(v_a_3790_);
v___x_4426_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4423_, v___x_4424_, v___x_4425_, v_a_3790_);
v___y_3792_ = v___x_4426_;
goto v___jp_3791_;
}
case 3:
{
uint8_t v___x_4427_; uint8_t v___x_4428_; uint8_t v___x_4429_; lean_object* v___x_4430_; 
v___x_4427_ = 0;
v___x_4428_ = 2;
v___x_4429_ = 0;
lean_inc_ref(v_a_3790_);
v___x_4430_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4427_, v___x_4428_, v___x_4429_, v_a_3790_);
v___y_3792_ = v___x_4430_;
goto v___jp_3791_;
}
default: 
{
uint8_t v___x_4431_; uint8_t v___x_4432_; uint8_t v___x_4433_; lean_object* v___x_4434_; 
v___x_4431_ = 0;
v___x_4432_ = 2;
v___x_4433_ = 1;
lean_inc_ref(v_a_3790_);
v___x_4434_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4431_, v___x_4432_, v___x_4433_, v_a_3790_);
v___y_3792_ = v___x_4434_;
goto v___jp_3791_;
}
}
}
case 34:
{
uint8_t v_presentation_4435_; 
lean_dec_ref(v_config_3788_);
v_presentation_4435_ = lean_ctor_get_uint8(v_x_3789_, 0);
lean_dec_ref_known(v_x_3789_, 0);
switch(v_presentation_4435_)
{
case 0:
{
uint8_t v___x_4436_; uint8_t v___x_4437_; uint8_t v___x_4438_; lean_object* v___x_4439_; 
v___x_4436_ = 2;
v___x_4437_ = 1;
v___x_4438_ = 0;
v___x_4439_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4436_, v___x_4437_, v___x_4438_, v_a_3790_);
return v___x_4439_;
}
case 1:
{
uint8_t v___x_4440_; uint8_t v___x_4441_; uint8_t v___x_4442_; lean_object* v___x_4443_; 
v___x_4440_ = 0;
v___x_4441_ = 1;
v___x_4442_ = 0;
v___x_4443_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4440_, v___x_4441_, v___x_4442_, v_a_3790_);
return v___x_4443_;
}
case 2:
{
uint8_t v___x_4444_; uint8_t v___x_4445_; uint8_t v___x_4446_; lean_object* v___x_4447_; 
v___x_4444_ = 0;
v___x_4445_ = 2;
v___x_4446_ = 1;
v___x_4447_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4444_, v___x_4445_, v___x_4446_, v_a_3790_);
return v___x_4447_;
}
case 3:
{
uint8_t v___x_4448_; uint8_t v___x_4449_; uint8_t v___x_4450_; lean_object* v___x_4451_; 
v___x_4448_ = 0;
v___x_4449_ = 2;
v___x_4450_ = 0;
v___x_4451_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4448_, v___x_4449_, v___x_4450_, v_a_3790_);
return v___x_4451_;
}
default: 
{
uint8_t v___x_4452_; uint8_t v___x_4453_; lean_object* v___x_4454_; 
v___x_4452_ = 0;
v___x_4453_ = 1;
v___x_4454_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4452_, v___x_4452_, v___x_4453_, v_a_3790_);
return v___x_4454_;
}
}
}
case 35:
{
uint8_t v_presentation_4455_; 
lean_dec_ref(v_config_3788_);
v_presentation_4455_ = lean_ctor_get_uint8(v_x_3789_, 0);
lean_dec_ref_known(v_x_3789_, 0);
switch(v_presentation_4455_)
{
case 0:
{
uint8_t v___x_4456_; uint8_t v___x_4457_; uint8_t v___x_4458_; lean_object* v___x_4459_; 
v___x_4456_ = 0;
v___x_4457_ = 1;
v___x_4458_ = 0;
v___x_4459_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4456_, v___x_4457_, v___x_4458_, v_a_3790_);
return v___x_4459_;
}
case 1:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; 
v___x_4460_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4461_ = l_Std_Internal_Parsec_String_pstring(v___x_4460_, v_a_3790_);
if (lean_obj_tag(v___x_4461_) == 0)
{
lean_object* v_pos_4462_; uint8_t v___x_4463_; uint8_t v___x_4464_; uint8_t v___x_4465_; lean_object* v___x_4466_; 
v_pos_4462_ = lean_ctor_get(v___x_4461_, 0);
lean_inc_n(v_pos_4462_, 2);
lean_dec_ref_known(v___x_4461_, 2);
v___x_4463_ = 0;
v___x_4464_ = 1;
v___x_4465_ = 1;
v___x_4466_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4463_, v___x_4464_, v___x_4465_, v_pos_4462_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_dec(v_pos_4462_);
return v___x_4466_;
}
else
{
lean_object* v_pos_4467_; lean_object* v_snd_4468_; lean_object* v_snd_4469_; uint8_t v___x_4470_; 
v_pos_4467_ = lean_ctor_get(v___x_4466_, 0);
lean_inc(v_pos_4467_);
v_snd_4468_ = lean_ctor_get(v_pos_4462_, 1);
lean_inc(v_snd_4468_);
lean_dec(v_pos_4462_);
v_snd_4469_ = lean_ctor_get(v_pos_4467_, 1);
v___x_4470_ = lean_nat_dec_eq(v_snd_4468_, v_snd_4469_);
lean_dec(v_snd_4468_);
if (v___x_4470_ == 0)
{
lean_dec(v_pos_4467_);
return v___x_4466_;
}
else
{
lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4478_; 
v_isSharedCheck_4478_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4478_ == 0)
{
lean_object* v_unused_4479_; lean_object* v_unused_4480_; 
v_unused_4479_ = lean_ctor_get(v___x_4466_, 1);
lean_dec(v_unused_4479_);
v_unused_4480_ = lean_ctor_get(v___x_4466_, 0);
lean_dec(v_unused_4480_);
v___x_4472_ = v___x_4466_;
v_isShared_4473_ = v_isSharedCheck_4478_;
goto v_resetjp_4471_;
}
else
{
lean_dec(v___x_4466_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4478_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4474_; lean_object* v___x_4476_; 
v___x_4474_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_4473_ == 0)
{
lean_ctor_set_tag(v___x_4472_, 0);
lean_ctor_set(v___x_4472_, 1, v___x_4474_);
v___x_4476_ = v___x_4472_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_pos_4467_);
lean_ctor_set(v_reuseFailAlloc_4477_, 1, v___x_4474_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
return v___x_4476_;
}
}
}
}
}
else
{
lean_object* v_pos_4481_; lean_object* v_err_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4489_; 
v_pos_4481_ = lean_ctor_get(v___x_4461_, 0);
v_err_4482_ = lean_ctor_get(v___x_4461_, 1);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4461_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4484_ = v___x_4461_;
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_err_4482_);
lean_inc(v_pos_4481_);
lean_dec(v___x_4461_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4487_; 
if (v_isShared_4485_ == 0)
{
v___x_4487_ = v___x_4484_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_pos_4481_);
lean_ctor_set(v_reuseFailAlloc_4488_, 1, v_err_4482_);
v___x_4487_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
return v___x_4487_;
}
}
}
}
default: 
{
lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4490_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
lean_inc_ref(v_a_3790_);
v___x_4491_ = l_Std_Internal_Parsec_String_pstring(v___x_4490_, v_a_3790_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v_pos_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4500_; 
lean_dec_ref(v_a_3790_);
v_pos_4492_ = lean_ctor_get(v___x_4491_, 0);
v_isSharedCheck_4500_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4500_ == 0)
{
lean_object* v_unused_4501_; 
v_unused_4501_ = lean_ctor_get(v___x_4491_, 1);
lean_dec(v_unused_4501_);
v___x_4494_ = v___x_4491_;
v_isShared_4495_ = v_isSharedCheck_4500_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_pos_4492_);
lean_dec(v___x_4491_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4500_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4496_; lean_object* v___x_4498_; 
v___x_4496_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_4495_ == 0)
{
lean_ctor_set(v___x_4494_, 1, v___x_4496_);
v___x_4498_ = v___x_4494_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_pos_4492_);
lean_ctor_set(v_reuseFailAlloc_4499_, 1, v___x_4496_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
return v___x_4498_;
}
}
}
else
{
lean_object* v_pos_4502_; lean_object* v_err_4503_; lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4516_; 
v_pos_4502_ = lean_ctor_get(v___x_4491_, 0);
v_err_4503_ = lean_ctor_get(v___x_4491_, 1);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4505_ = v___x_4491_;
v_isShared_4506_ = v_isSharedCheck_4516_;
goto v_resetjp_4504_;
}
else
{
lean_inc(v_err_4503_);
lean_inc(v_pos_4502_);
lean_dec(v___x_4491_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4516_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
lean_object* v_snd_4507_; lean_object* v_snd_4508_; uint8_t v___x_4509_; 
v_snd_4507_ = lean_ctor_get(v_a_3790_, 1);
lean_inc(v_snd_4507_);
lean_dec_ref(v_a_3790_);
v_snd_4508_ = lean_ctor_get(v_pos_4502_, 1);
v___x_4509_ = lean_nat_dec_eq(v_snd_4507_, v_snd_4508_);
lean_dec(v_snd_4507_);
if (v___x_4509_ == 0)
{
lean_object* v___x_4511_; 
if (v_isShared_4506_ == 0)
{
v___x_4511_ = v___x_4505_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_pos_4502_);
lean_ctor_set(v_reuseFailAlloc_4512_, 1, v_err_4503_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
else
{
uint8_t v___x_4513_; uint8_t v___x_4514_; lean_object* v___x_4515_; 
lean_del_object(v___x_4505_);
lean_dec(v_err_4503_);
v___x_4513_ = 0;
v___x_4514_ = 2;
v___x_4515_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4513_, v___x_4514_, v___x_4509_, v_pos_4502_);
return v___x_4515_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_4517_; 
lean_dec_ref(v_x_3789_);
lean_dec_ref(v_config_3788_);
v___x_4517_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(v_a_3790_);
return v___x_4517_;
}
}
v___jp_3791_:
{
if (lean_obj_tag(v___y_3792_) == 0)
{
lean_dec_ref(v_a_3790_);
return v___y_3792_;
}
else
{
lean_object* v_pos_3793_; lean_object* v_snd_3794_; lean_object* v_snd_3795_; uint8_t v___x_3796_; 
v_pos_3793_ = lean_ctor_get(v___y_3792_, 0);
v_snd_3794_ = lean_ctor_get(v_a_3790_, 1);
lean_inc(v_snd_3794_);
lean_dec_ref(v_a_3790_);
v_snd_3795_ = lean_ctor_get(v_pos_3793_, 1);
v___x_3796_ = lean_nat_dec_eq(v_snd_3794_, v_snd_3795_);
lean_dec(v_snd_3794_);
if (v___x_3796_ == 0)
{
return v___y_3792_;
}
else
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
lean_inc(v_pos_3793_);
lean_dec_ref_known(v___y_3792_, 2);
v___x_3797_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
v___x_3798_ = l_Std_Internal_Parsec_String_pstring(v___x_3797_, v_pos_3793_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v_pos_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3807_; 
v_pos_3799_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3807_ == 0)
{
lean_object* v_unused_3808_; 
v_unused_3808_ = lean_ctor_get(v___x_3798_, 1);
lean_dec(v_unused_3808_);
v___x_3801_ = v___x_3798_;
v_isShared_3802_ = v_isSharedCheck_3807_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_pos_3799_);
lean_dec(v___x_3798_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3807_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3803_; lean_object* v___x_3805_; 
v___x_3803_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 1, v___x_3803_);
v___x_3805_ = v___x_3801_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_pos_3799_);
lean_ctor_set(v_reuseFailAlloc_3806_, 1, v___x_3803_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
else
{
lean_object* v_pos_3809_; lean_object* v_err_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
v_pos_3809_ = lean_ctor_get(v___x_3798_, 0);
v_err_3810_ = lean_ctor_get(v___x_3798_, 1);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3798_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_err_3810_);
lean_inc(v_pos_3809_);
lean_dec(v___x_3798_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_pos_3809_);
lean_ctor_set(v_reuseFailAlloc_3816_, 1, v_err_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(lean_object* v_dateformat_4518_, lean_object* v_date_4519_, lean_object* v_part_4520_){
_start:
{
if (lean_obj_tag(v_part_4520_) == 0)
{
lean_object* v_val_4521_; 
lean_dec_ref(v_date_4519_);
v_val_4521_ = lean_ctor_get(v_part_4520_, 0);
lean_inc_ref(v_val_4521_);
lean_dec_ref_known(v_part_4520_, 1);
return v_val_4521_;
}
else
{
lean_object* v_modifier_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v_modifier_4522_ = lean_ctor_get(v_part_4520_, 0);
lean_inc_ref(v_modifier_4522_);
lean_dec_ref_known(v_part_4520_, 1);
v___x_4523_ = l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(v_modifier_4522_, v_dateformat_4518_, v_date_4519_);
v___x_4524_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_4518_, v_modifier_4522_, v___x_4523_);
return v___x_4524_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate___boxed(lean_object* v_dateformat_4525_, lean_object* v_date_4526_, lean_object* v_part_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_4525_, v_date_4526_, v_part_4527_);
lean_dec_ref(v_dateformat_4525_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_FormatType_match__1_splitter___redArg(lean_object* v_x_4529_, lean_object* v_h__1_4530_, lean_object* v_h__2_4531_, lean_object* v_h__3_4532_){
_start:
{
if (lean_obj_tag(v_x_4529_) == 0)
{
lean_object* v___x_4533_; lean_object* v___x_4534_; 
lean_dec(v_h__2_4531_);
lean_dec(v_h__1_4530_);
v___x_4533_ = lean_box(0);
v___x_4534_ = lean_apply_1(v_h__3_4532_, v___x_4533_);
return v___x_4534_;
}
else
{
lean_object* v_head_4535_; 
lean_dec(v_h__3_4532_);
v_head_4535_ = lean_ctor_get(v_x_4529_, 0);
lean_inc(v_head_4535_);
if (lean_obj_tag(v_head_4535_) == 0)
{
lean_object* v_tail_4536_; lean_object* v_val_4537_; lean_object* v___x_4538_; 
lean_dec(v_h__1_4530_);
v_tail_4536_ = lean_ctor_get(v_x_4529_, 1);
lean_inc(v_tail_4536_);
lean_dec_ref_known(v_x_4529_, 2);
v_val_4537_ = lean_ctor_get(v_head_4535_, 0);
lean_inc_ref(v_val_4537_);
lean_dec_ref_known(v_head_4535_, 1);
v___x_4538_ = lean_apply_2(v_h__2_4531_, v_val_4537_, v_tail_4536_);
return v___x_4538_;
}
else
{
lean_object* v_tail_4539_; lean_object* v_modifier_4540_; lean_object* v___x_4541_; 
lean_dec(v_h__2_4531_);
v_tail_4539_ = lean_ctor_get(v_x_4529_, 1);
lean_inc(v_tail_4539_);
lean_dec_ref_known(v_x_4529_, 2);
v_modifier_4540_ = lean_ctor_get(v_head_4535_, 0);
lean_inc_ref(v_modifier_4540_);
lean_dec_ref_known(v_head_4535_, 1);
v___x_4541_ = lean_apply_2(v_h__1_4530_, v_modifier_4540_, v_tail_4539_);
return v___x_4541_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_FormatType_match__1_splitter(lean_object* v_motive_4542_, lean_object* v_x_4543_, lean_object* v_h__1_4544_, lean_object* v_h__2_4545_, lean_object* v_h__3_4546_){
_start:
{
if (lean_obj_tag(v_x_4543_) == 0)
{
lean_object* v___x_4547_; lean_object* v___x_4548_; 
lean_dec(v_h__2_4545_);
lean_dec(v_h__1_4544_);
v___x_4547_ = lean_box(0);
v___x_4548_ = lean_apply_1(v_h__3_4546_, v___x_4547_);
return v___x_4548_;
}
else
{
lean_object* v_head_4549_; 
lean_dec(v_h__3_4546_);
v_head_4549_ = lean_ctor_get(v_x_4543_, 0);
lean_inc(v_head_4549_);
if (lean_obj_tag(v_head_4549_) == 0)
{
lean_object* v_tail_4550_; lean_object* v_val_4551_; lean_object* v___x_4552_; 
lean_dec(v_h__1_4544_);
v_tail_4550_ = lean_ctor_get(v_x_4543_, 1);
lean_inc(v_tail_4550_);
lean_dec_ref_known(v_x_4543_, 2);
v_val_4551_ = lean_ctor_get(v_head_4549_, 0);
lean_inc_ref(v_val_4551_);
lean_dec_ref_known(v_head_4549_, 1);
v___x_4552_ = lean_apply_2(v_h__2_4545_, v_val_4551_, v_tail_4550_);
return v___x_4552_;
}
else
{
lean_object* v_tail_4553_; lean_object* v_modifier_4554_; lean_object* v___x_4555_; 
lean_dec(v_h__2_4545_);
v_tail_4553_ = lean_ctor_get(v_x_4543_, 1);
lean_inc(v_tail_4553_);
lean_dec_ref_known(v_x_4543_, 2);
v_modifier_4554_ = lean_ctor_get(v_head_4549_, 0);
lean_inc_ref(v_modifier_4554_);
lean_dec_ref_known(v_head_4549_, 1);
v___x_4555_ = lean_apply_2(v_h__1_4544_, v_modifier_4554_, v_tail_4553_);
return v___x_4555_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(lean_object* v_date_4556_, lean_object* v_modifier_4557_, lean_object* v_data_4558_){
_start:
{
switch(lean_obj_tag(v_modifier_4557_))
{
case 0:
{
lean_object* v_y_4559_; lean_object* v_u_4560_; lean_object* v_Y_4561_; lean_object* v_D_4562_; lean_object* v_M_4563_; lean_object* v_L_4564_; lean_object* v_d_4565_; lean_object* v_Q_4566_; lean_object* v_q_4567_; lean_object* v_w_4568_; lean_object* v_W_4569_; lean_object* v_E_4570_; lean_object* v_e_4571_; lean_object* v_c_4572_; lean_object* v_F_4573_; lean_object* v_a_4574_; lean_object* v_b_4575_; lean_object* v_B_4576_; lean_object* v_h_4577_; lean_object* v_K_4578_; lean_object* v_k_4579_; lean_object* v_H_4580_; lean_object* v_m_4581_; lean_object* v_s_4582_; lean_object* v_S_4583_; lean_object* v_A_4584_; lean_object* v_n_4585_; lean_object* v_N_4586_; lean_object* v_V_4587_; lean_object* v_z_4588_; lean_object* v_zabbrev_4589_; lean_object* v_v_4590_; lean_object* v_O_4591_; lean_object* v_X_4592_; lean_object* v_x_4593_; lean_object* v_Z_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4602_; 
lean_dec_ref_known(v_modifier_4557_, 0);
v_y_4559_ = lean_ctor_get(v_date_4556_, 1);
v_u_4560_ = lean_ctor_get(v_date_4556_, 2);
v_Y_4561_ = lean_ctor_get(v_date_4556_, 3);
v_D_4562_ = lean_ctor_get(v_date_4556_, 4);
v_M_4563_ = lean_ctor_get(v_date_4556_, 5);
v_L_4564_ = lean_ctor_get(v_date_4556_, 6);
v_d_4565_ = lean_ctor_get(v_date_4556_, 7);
v_Q_4566_ = lean_ctor_get(v_date_4556_, 8);
v_q_4567_ = lean_ctor_get(v_date_4556_, 9);
v_w_4568_ = lean_ctor_get(v_date_4556_, 10);
v_W_4569_ = lean_ctor_get(v_date_4556_, 11);
v_E_4570_ = lean_ctor_get(v_date_4556_, 12);
v_e_4571_ = lean_ctor_get(v_date_4556_, 13);
v_c_4572_ = lean_ctor_get(v_date_4556_, 14);
v_F_4573_ = lean_ctor_get(v_date_4556_, 15);
v_a_4574_ = lean_ctor_get(v_date_4556_, 16);
v_b_4575_ = lean_ctor_get(v_date_4556_, 17);
v_B_4576_ = lean_ctor_get(v_date_4556_, 18);
v_h_4577_ = lean_ctor_get(v_date_4556_, 19);
v_K_4578_ = lean_ctor_get(v_date_4556_, 20);
v_k_4579_ = lean_ctor_get(v_date_4556_, 21);
v_H_4580_ = lean_ctor_get(v_date_4556_, 22);
v_m_4581_ = lean_ctor_get(v_date_4556_, 23);
v_s_4582_ = lean_ctor_get(v_date_4556_, 24);
v_S_4583_ = lean_ctor_get(v_date_4556_, 25);
v_A_4584_ = lean_ctor_get(v_date_4556_, 26);
v_n_4585_ = lean_ctor_get(v_date_4556_, 27);
v_N_4586_ = lean_ctor_get(v_date_4556_, 28);
v_V_4587_ = lean_ctor_get(v_date_4556_, 29);
v_z_4588_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_4589_ = lean_ctor_get(v_date_4556_, 31);
v_v_4590_ = lean_ctor_get(v_date_4556_, 32);
v_O_4591_ = lean_ctor_get(v_date_4556_, 33);
v_X_4592_ = lean_ctor_get(v_date_4556_, 34);
v_x_4593_ = lean_ctor_get(v_date_4556_, 35);
v_Z_4594_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_4602_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_4602_ == 0)
{
lean_object* v_unused_4603_; 
v_unused_4603_ = lean_ctor_get(v_date_4556_, 0);
lean_dec(v_unused_4603_);
v___x_4596_ = v_date_4556_;
v_isShared_4597_ = v_isSharedCheck_4602_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_Z_4594_);
lean_inc(v_x_4593_);
lean_inc(v_X_4592_);
lean_inc(v_O_4591_);
lean_inc(v_v_4590_);
lean_inc(v_zabbrev_4589_);
lean_inc(v_z_4588_);
lean_inc(v_V_4587_);
lean_inc(v_N_4586_);
lean_inc(v_n_4585_);
lean_inc(v_A_4584_);
lean_inc(v_S_4583_);
lean_inc(v_s_4582_);
lean_inc(v_m_4581_);
lean_inc(v_H_4580_);
lean_inc(v_k_4579_);
lean_inc(v_K_4578_);
lean_inc(v_h_4577_);
lean_inc(v_B_4576_);
lean_inc(v_b_4575_);
lean_inc(v_a_4574_);
lean_inc(v_F_4573_);
lean_inc(v_c_4572_);
lean_inc(v_e_4571_);
lean_inc(v_E_4570_);
lean_inc(v_W_4569_);
lean_inc(v_w_4568_);
lean_inc(v_q_4567_);
lean_inc(v_Q_4566_);
lean_inc(v_d_4565_);
lean_inc(v_L_4564_);
lean_inc(v_M_4563_);
lean_inc(v_D_4562_);
lean_inc(v_Y_4561_);
lean_inc(v_u_4560_);
lean_inc(v_y_4559_);
lean_dec(v_date_4556_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4602_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v___x_4598_; lean_object* v___x_4600_; 
v___x_4598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4598_, 0, v_data_4558_);
if (v_isShared_4597_ == 0)
{
lean_ctor_set(v___x_4596_, 0, v___x_4598_);
v___x_4600_ = v___x_4596_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v___x_4598_);
lean_ctor_set(v_reuseFailAlloc_4601_, 1, v_y_4559_);
lean_ctor_set(v_reuseFailAlloc_4601_, 2, v_u_4560_);
lean_ctor_set(v_reuseFailAlloc_4601_, 3, v_Y_4561_);
lean_ctor_set(v_reuseFailAlloc_4601_, 4, v_D_4562_);
lean_ctor_set(v_reuseFailAlloc_4601_, 5, v_M_4563_);
lean_ctor_set(v_reuseFailAlloc_4601_, 6, v_L_4564_);
lean_ctor_set(v_reuseFailAlloc_4601_, 7, v_d_4565_);
lean_ctor_set(v_reuseFailAlloc_4601_, 8, v_Q_4566_);
lean_ctor_set(v_reuseFailAlloc_4601_, 9, v_q_4567_);
lean_ctor_set(v_reuseFailAlloc_4601_, 10, v_w_4568_);
lean_ctor_set(v_reuseFailAlloc_4601_, 11, v_W_4569_);
lean_ctor_set(v_reuseFailAlloc_4601_, 12, v_E_4570_);
lean_ctor_set(v_reuseFailAlloc_4601_, 13, v_e_4571_);
lean_ctor_set(v_reuseFailAlloc_4601_, 14, v_c_4572_);
lean_ctor_set(v_reuseFailAlloc_4601_, 15, v_F_4573_);
lean_ctor_set(v_reuseFailAlloc_4601_, 16, v_a_4574_);
lean_ctor_set(v_reuseFailAlloc_4601_, 17, v_b_4575_);
lean_ctor_set(v_reuseFailAlloc_4601_, 18, v_B_4576_);
lean_ctor_set(v_reuseFailAlloc_4601_, 19, v_h_4577_);
lean_ctor_set(v_reuseFailAlloc_4601_, 20, v_K_4578_);
lean_ctor_set(v_reuseFailAlloc_4601_, 21, v_k_4579_);
lean_ctor_set(v_reuseFailAlloc_4601_, 22, v_H_4580_);
lean_ctor_set(v_reuseFailAlloc_4601_, 23, v_m_4581_);
lean_ctor_set(v_reuseFailAlloc_4601_, 24, v_s_4582_);
lean_ctor_set(v_reuseFailAlloc_4601_, 25, v_S_4583_);
lean_ctor_set(v_reuseFailAlloc_4601_, 26, v_A_4584_);
lean_ctor_set(v_reuseFailAlloc_4601_, 27, v_n_4585_);
lean_ctor_set(v_reuseFailAlloc_4601_, 28, v_N_4586_);
lean_ctor_set(v_reuseFailAlloc_4601_, 29, v_V_4587_);
lean_ctor_set(v_reuseFailAlloc_4601_, 30, v_z_4588_);
lean_ctor_set(v_reuseFailAlloc_4601_, 31, v_zabbrev_4589_);
lean_ctor_set(v_reuseFailAlloc_4601_, 32, v_v_4590_);
lean_ctor_set(v_reuseFailAlloc_4601_, 33, v_O_4591_);
lean_ctor_set(v_reuseFailAlloc_4601_, 34, v_X_4592_);
lean_ctor_set(v_reuseFailAlloc_4601_, 35, v_x_4593_);
lean_ctor_set(v_reuseFailAlloc_4601_, 36, v_Z_4594_);
v___x_4600_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
return v___x_4600_;
}
}
}
case 1:
{
lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4654_; 
v_isSharedCheck_4654_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_4654_ == 0)
{
lean_object* v_unused_4655_; 
v_unused_4655_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_4655_);
v___x_4605_ = v_modifier_4557_;
v_isShared_4606_ = v_isSharedCheck_4654_;
goto v_resetjp_4604_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4654_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v_G_4607_; lean_object* v_y_4608_; lean_object* v_Y_4609_; lean_object* v_D_4610_; lean_object* v_M_4611_; lean_object* v_L_4612_; lean_object* v_d_4613_; lean_object* v_Q_4614_; lean_object* v_q_4615_; lean_object* v_w_4616_; lean_object* v_W_4617_; lean_object* v_E_4618_; lean_object* v_e_4619_; lean_object* v_c_4620_; lean_object* v_F_4621_; lean_object* v_a_4622_; lean_object* v_b_4623_; lean_object* v_B_4624_; lean_object* v_h_4625_; lean_object* v_K_4626_; lean_object* v_k_4627_; lean_object* v_H_4628_; lean_object* v_m_4629_; lean_object* v_s_4630_; lean_object* v_S_4631_; lean_object* v_A_4632_; lean_object* v_n_4633_; lean_object* v_N_4634_; lean_object* v_V_4635_; lean_object* v_z_4636_; lean_object* v_zabbrev_4637_; lean_object* v_v_4638_; lean_object* v_O_4639_; lean_object* v_X_4640_; lean_object* v_x_4641_; lean_object* v_Z_4642_; lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4652_; 
v_G_4607_ = lean_ctor_get(v_date_4556_, 0);
v_y_4608_ = lean_ctor_get(v_date_4556_, 1);
v_Y_4609_ = lean_ctor_get(v_date_4556_, 3);
v_D_4610_ = lean_ctor_get(v_date_4556_, 4);
v_M_4611_ = lean_ctor_get(v_date_4556_, 5);
v_L_4612_ = lean_ctor_get(v_date_4556_, 6);
v_d_4613_ = lean_ctor_get(v_date_4556_, 7);
v_Q_4614_ = lean_ctor_get(v_date_4556_, 8);
v_q_4615_ = lean_ctor_get(v_date_4556_, 9);
v_w_4616_ = lean_ctor_get(v_date_4556_, 10);
v_W_4617_ = lean_ctor_get(v_date_4556_, 11);
v_E_4618_ = lean_ctor_get(v_date_4556_, 12);
v_e_4619_ = lean_ctor_get(v_date_4556_, 13);
v_c_4620_ = lean_ctor_get(v_date_4556_, 14);
v_F_4621_ = lean_ctor_get(v_date_4556_, 15);
v_a_4622_ = lean_ctor_get(v_date_4556_, 16);
v_b_4623_ = lean_ctor_get(v_date_4556_, 17);
v_B_4624_ = lean_ctor_get(v_date_4556_, 18);
v_h_4625_ = lean_ctor_get(v_date_4556_, 19);
v_K_4626_ = lean_ctor_get(v_date_4556_, 20);
v_k_4627_ = lean_ctor_get(v_date_4556_, 21);
v_H_4628_ = lean_ctor_get(v_date_4556_, 22);
v_m_4629_ = lean_ctor_get(v_date_4556_, 23);
v_s_4630_ = lean_ctor_get(v_date_4556_, 24);
v_S_4631_ = lean_ctor_get(v_date_4556_, 25);
v_A_4632_ = lean_ctor_get(v_date_4556_, 26);
v_n_4633_ = lean_ctor_get(v_date_4556_, 27);
v_N_4634_ = lean_ctor_get(v_date_4556_, 28);
v_V_4635_ = lean_ctor_get(v_date_4556_, 29);
v_z_4636_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_4637_ = lean_ctor_get(v_date_4556_, 31);
v_v_4638_ = lean_ctor_get(v_date_4556_, 32);
v_O_4639_ = lean_ctor_get(v_date_4556_, 33);
v_X_4640_ = lean_ctor_get(v_date_4556_, 34);
v_x_4641_ = lean_ctor_get(v_date_4556_, 35);
v_Z_4642_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_4652_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_4652_ == 0)
{
lean_object* v_unused_4653_; 
v_unused_4653_ = lean_ctor_get(v_date_4556_, 2);
lean_dec(v_unused_4653_);
v___x_4644_ = v_date_4556_;
v_isShared_4645_ = v_isSharedCheck_4652_;
goto v_resetjp_4643_;
}
else
{
lean_inc(v_Z_4642_);
lean_inc(v_x_4641_);
lean_inc(v_X_4640_);
lean_inc(v_O_4639_);
lean_inc(v_v_4638_);
lean_inc(v_zabbrev_4637_);
lean_inc(v_z_4636_);
lean_inc(v_V_4635_);
lean_inc(v_N_4634_);
lean_inc(v_n_4633_);
lean_inc(v_A_4632_);
lean_inc(v_S_4631_);
lean_inc(v_s_4630_);
lean_inc(v_m_4629_);
lean_inc(v_H_4628_);
lean_inc(v_k_4627_);
lean_inc(v_K_4626_);
lean_inc(v_h_4625_);
lean_inc(v_B_4624_);
lean_inc(v_b_4623_);
lean_inc(v_a_4622_);
lean_inc(v_F_4621_);
lean_inc(v_c_4620_);
lean_inc(v_e_4619_);
lean_inc(v_E_4618_);
lean_inc(v_W_4617_);
lean_inc(v_w_4616_);
lean_inc(v_q_4615_);
lean_inc(v_Q_4614_);
lean_inc(v_d_4613_);
lean_inc(v_L_4612_);
lean_inc(v_M_4611_);
lean_inc(v_D_4610_);
lean_inc(v_Y_4609_);
lean_inc(v_y_4608_);
lean_inc(v_G_4607_);
lean_dec(v_date_4556_);
v___x_4644_ = lean_box(0);
v_isShared_4645_ = v_isSharedCheck_4652_;
goto v_resetjp_4643_;
}
v_resetjp_4643_:
{
lean_object* v___x_4647_; 
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 0, v_data_4558_);
v___x_4647_ = v___x_4605_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_data_4558_);
v___x_4647_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
lean_object* v___x_4649_; 
if (v_isShared_4645_ == 0)
{
lean_ctor_set(v___x_4644_, 2, v___x_4647_);
v___x_4649_ = v___x_4644_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_G_4607_);
lean_ctor_set(v_reuseFailAlloc_4650_, 1, v_y_4608_);
lean_ctor_set(v_reuseFailAlloc_4650_, 2, v___x_4647_);
lean_ctor_set(v_reuseFailAlloc_4650_, 3, v_Y_4609_);
lean_ctor_set(v_reuseFailAlloc_4650_, 4, v_D_4610_);
lean_ctor_set(v_reuseFailAlloc_4650_, 5, v_M_4611_);
lean_ctor_set(v_reuseFailAlloc_4650_, 6, v_L_4612_);
lean_ctor_set(v_reuseFailAlloc_4650_, 7, v_d_4613_);
lean_ctor_set(v_reuseFailAlloc_4650_, 8, v_Q_4614_);
lean_ctor_set(v_reuseFailAlloc_4650_, 9, v_q_4615_);
lean_ctor_set(v_reuseFailAlloc_4650_, 10, v_w_4616_);
lean_ctor_set(v_reuseFailAlloc_4650_, 11, v_W_4617_);
lean_ctor_set(v_reuseFailAlloc_4650_, 12, v_E_4618_);
lean_ctor_set(v_reuseFailAlloc_4650_, 13, v_e_4619_);
lean_ctor_set(v_reuseFailAlloc_4650_, 14, v_c_4620_);
lean_ctor_set(v_reuseFailAlloc_4650_, 15, v_F_4621_);
lean_ctor_set(v_reuseFailAlloc_4650_, 16, v_a_4622_);
lean_ctor_set(v_reuseFailAlloc_4650_, 17, v_b_4623_);
lean_ctor_set(v_reuseFailAlloc_4650_, 18, v_B_4624_);
lean_ctor_set(v_reuseFailAlloc_4650_, 19, v_h_4625_);
lean_ctor_set(v_reuseFailAlloc_4650_, 20, v_K_4626_);
lean_ctor_set(v_reuseFailAlloc_4650_, 21, v_k_4627_);
lean_ctor_set(v_reuseFailAlloc_4650_, 22, v_H_4628_);
lean_ctor_set(v_reuseFailAlloc_4650_, 23, v_m_4629_);
lean_ctor_set(v_reuseFailAlloc_4650_, 24, v_s_4630_);
lean_ctor_set(v_reuseFailAlloc_4650_, 25, v_S_4631_);
lean_ctor_set(v_reuseFailAlloc_4650_, 26, v_A_4632_);
lean_ctor_set(v_reuseFailAlloc_4650_, 27, v_n_4633_);
lean_ctor_set(v_reuseFailAlloc_4650_, 28, v_N_4634_);
lean_ctor_set(v_reuseFailAlloc_4650_, 29, v_V_4635_);
lean_ctor_set(v_reuseFailAlloc_4650_, 30, v_z_4636_);
lean_ctor_set(v_reuseFailAlloc_4650_, 31, v_zabbrev_4637_);
lean_ctor_set(v_reuseFailAlloc_4650_, 32, v_v_4638_);
lean_ctor_set(v_reuseFailAlloc_4650_, 33, v_O_4639_);
lean_ctor_set(v_reuseFailAlloc_4650_, 34, v_X_4640_);
lean_ctor_set(v_reuseFailAlloc_4650_, 35, v_x_4641_);
lean_ctor_set(v_reuseFailAlloc_4650_, 36, v_Z_4642_);
v___x_4649_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
return v___x_4649_;
}
}
}
}
}
case 2:
{
lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4706_; 
v_isSharedCheck_4706_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_4706_ == 0)
{
lean_object* v_unused_4707_; 
v_unused_4707_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_4707_);
v___x_4657_ = v_modifier_4557_;
v_isShared_4658_ = v_isSharedCheck_4706_;
goto v_resetjp_4656_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4706_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v_G_4659_; lean_object* v_u_4660_; lean_object* v_Y_4661_; lean_object* v_D_4662_; lean_object* v_M_4663_; lean_object* v_L_4664_; lean_object* v_d_4665_; lean_object* v_Q_4666_; lean_object* v_q_4667_; lean_object* v_w_4668_; lean_object* v_W_4669_; lean_object* v_E_4670_; lean_object* v_e_4671_; lean_object* v_c_4672_; lean_object* v_F_4673_; lean_object* v_a_4674_; lean_object* v_b_4675_; lean_object* v_B_4676_; lean_object* v_h_4677_; lean_object* v_K_4678_; lean_object* v_k_4679_; lean_object* v_H_4680_; lean_object* v_m_4681_; lean_object* v_s_4682_; lean_object* v_S_4683_; lean_object* v_A_4684_; lean_object* v_n_4685_; lean_object* v_N_4686_; lean_object* v_V_4687_; lean_object* v_z_4688_; lean_object* v_zabbrev_4689_; lean_object* v_v_4690_; lean_object* v_O_4691_; lean_object* v_X_4692_; lean_object* v_x_4693_; lean_object* v_Z_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4704_; 
v_G_4659_ = lean_ctor_get(v_date_4556_, 0);
v_u_4660_ = lean_ctor_get(v_date_4556_, 2);
v_Y_4661_ = lean_ctor_get(v_date_4556_, 3);
v_D_4662_ = lean_ctor_get(v_date_4556_, 4);
v_M_4663_ = lean_ctor_get(v_date_4556_, 5);
v_L_4664_ = lean_ctor_get(v_date_4556_, 6);
v_d_4665_ = lean_ctor_get(v_date_4556_, 7);
v_Q_4666_ = lean_ctor_get(v_date_4556_, 8);
v_q_4667_ = lean_ctor_get(v_date_4556_, 9);
v_w_4668_ = lean_ctor_get(v_date_4556_, 10);
v_W_4669_ = lean_ctor_get(v_date_4556_, 11);
v_E_4670_ = lean_ctor_get(v_date_4556_, 12);
v_e_4671_ = lean_ctor_get(v_date_4556_, 13);
v_c_4672_ = lean_ctor_get(v_date_4556_, 14);
v_F_4673_ = lean_ctor_get(v_date_4556_, 15);
v_a_4674_ = lean_ctor_get(v_date_4556_, 16);
v_b_4675_ = lean_ctor_get(v_date_4556_, 17);
v_B_4676_ = lean_ctor_get(v_date_4556_, 18);
v_h_4677_ = lean_ctor_get(v_date_4556_, 19);
v_K_4678_ = lean_ctor_get(v_date_4556_, 20);
v_k_4679_ = lean_ctor_get(v_date_4556_, 21);
v_H_4680_ = lean_ctor_get(v_date_4556_, 22);
v_m_4681_ = lean_ctor_get(v_date_4556_, 23);
v_s_4682_ = lean_ctor_get(v_date_4556_, 24);
v_S_4683_ = lean_ctor_get(v_date_4556_, 25);
v_A_4684_ = lean_ctor_get(v_date_4556_, 26);
v_n_4685_ = lean_ctor_get(v_date_4556_, 27);
v_N_4686_ = lean_ctor_get(v_date_4556_, 28);
v_V_4687_ = lean_ctor_get(v_date_4556_, 29);
v_z_4688_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_4689_ = lean_ctor_get(v_date_4556_, 31);
v_v_4690_ = lean_ctor_get(v_date_4556_, 32);
v_O_4691_ = lean_ctor_get(v_date_4556_, 33);
v_X_4692_ = lean_ctor_get(v_date_4556_, 34);
v_x_4693_ = lean_ctor_get(v_date_4556_, 35);
v_Z_4694_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_4704_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_4704_ == 0)
{
lean_object* v_unused_4705_; 
v_unused_4705_ = lean_ctor_get(v_date_4556_, 1);
lean_dec(v_unused_4705_);
v___x_4696_ = v_date_4556_;
v_isShared_4697_ = v_isSharedCheck_4704_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_Z_4694_);
lean_inc(v_x_4693_);
lean_inc(v_X_4692_);
lean_inc(v_O_4691_);
lean_inc(v_v_4690_);
lean_inc(v_zabbrev_4689_);
lean_inc(v_z_4688_);
lean_inc(v_V_4687_);
lean_inc(v_N_4686_);
lean_inc(v_n_4685_);
lean_inc(v_A_4684_);
lean_inc(v_S_4683_);
lean_inc(v_s_4682_);
lean_inc(v_m_4681_);
lean_inc(v_H_4680_);
lean_inc(v_k_4679_);
lean_inc(v_K_4678_);
lean_inc(v_h_4677_);
lean_inc(v_B_4676_);
lean_inc(v_b_4675_);
lean_inc(v_a_4674_);
lean_inc(v_F_4673_);
lean_inc(v_c_4672_);
lean_inc(v_e_4671_);
lean_inc(v_E_4670_);
lean_inc(v_W_4669_);
lean_inc(v_w_4668_);
lean_inc(v_q_4667_);
lean_inc(v_Q_4666_);
lean_inc(v_d_4665_);
lean_inc(v_L_4664_);
lean_inc(v_M_4663_);
lean_inc(v_D_4662_);
lean_inc(v_Y_4661_);
lean_inc(v_u_4660_);
lean_inc(v_G_4659_);
lean_dec(v_date_4556_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4704_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4699_; 
if (v_isShared_4658_ == 0)
{
lean_ctor_set_tag(v___x_4657_, 1);
lean_ctor_set(v___x_4657_, 0, v_data_4558_);
v___x_4699_ = v___x_4657_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_data_4558_);
v___x_4699_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
lean_object* v___x_4701_; 
if (v_isShared_4697_ == 0)
{
lean_ctor_set(v___x_4696_, 1, v___x_4699_);
v___x_4701_ = v___x_4696_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4702_; 
v_reuseFailAlloc_4702_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4702_, 0, v_G_4659_);
lean_ctor_set(v_reuseFailAlloc_4702_, 1, v___x_4699_);
lean_ctor_set(v_reuseFailAlloc_4702_, 2, v_u_4660_);
lean_ctor_set(v_reuseFailAlloc_4702_, 3, v_Y_4661_);
lean_ctor_set(v_reuseFailAlloc_4702_, 4, v_D_4662_);
lean_ctor_set(v_reuseFailAlloc_4702_, 5, v_M_4663_);
lean_ctor_set(v_reuseFailAlloc_4702_, 6, v_L_4664_);
lean_ctor_set(v_reuseFailAlloc_4702_, 7, v_d_4665_);
lean_ctor_set(v_reuseFailAlloc_4702_, 8, v_Q_4666_);
lean_ctor_set(v_reuseFailAlloc_4702_, 9, v_q_4667_);
lean_ctor_set(v_reuseFailAlloc_4702_, 10, v_w_4668_);
lean_ctor_set(v_reuseFailAlloc_4702_, 11, v_W_4669_);
lean_ctor_set(v_reuseFailAlloc_4702_, 12, v_E_4670_);
lean_ctor_set(v_reuseFailAlloc_4702_, 13, v_e_4671_);
lean_ctor_set(v_reuseFailAlloc_4702_, 14, v_c_4672_);
lean_ctor_set(v_reuseFailAlloc_4702_, 15, v_F_4673_);
lean_ctor_set(v_reuseFailAlloc_4702_, 16, v_a_4674_);
lean_ctor_set(v_reuseFailAlloc_4702_, 17, v_b_4675_);
lean_ctor_set(v_reuseFailAlloc_4702_, 18, v_B_4676_);
lean_ctor_set(v_reuseFailAlloc_4702_, 19, v_h_4677_);
lean_ctor_set(v_reuseFailAlloc_4702_, 20, v_K_4678_);
lean_ctor_set(v_reuseFailAlloc_4702_, 21, v_k_4679_);
lean_ctor_set(v_reuseFailAlloc_4702_, 22, v_H_4680_);
lean_ctor_set(v_reuseFailAlloc_4702_, 23, v_m_4681_);
lean_ctor_set(v_reuseFailAlloc_4702_, 24, v_s_4682_);
lean_ctor_set(v_reuseFailAlloc_4702_, 25, v_S_4683_);
lean_ctor_set(v_reuseFailAlloc_4702_, 26, v_A_4684_);
lean_ctor_set(v_reuseFailAlloc_4702_, 27, v_n_4685_);
lean_ctor_set(v_reuseFailAlloc_4702_, 28, v_N_4686_);
lean_ctor_set(v_reuseFailAlloc_4702_, 29, v_V_4687_);
lean_ctor_set(v_reuseFailAlloc_4702_, 30, v_z_4688_);
lean_ctor_set(v_reuseFailAlloc_4702_, 31, v_zabbrev_4689_);
lean_ctor_set(v_reuseFailAlloc_4702_, 32, v_v_4690_);
lean_ctor_set(v_reuseFailAlloc_4702_, 33, v_O_4691_);
lean_ctor_set(v_reuseFailAlloc_4702_, 34, v_X_4692_);
lean_ctor_set(v_reuseFailAlloc_4702_, 35, v_x_4693_);
lean_ctor_set(v_reuseFailAlloc_4702_, 36, v_Z_4694_);
v___x_4701_ = v_reuseFailAlloc_4702_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
return v___x_4701_;
}
}
}
}
}
case 3:
{
lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4758_; 
v_isSharedCheck_4758_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_4758_ == 0)
{
lean_object* v_unused_4759_; 
v_unused_4759_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_4759_);
v___x_4709_ = v_modifier_4557_;
v_isShared_4710_ = v_isSharedCheck_4758_;
goto v_resetjp_4708_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4758_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v_G_4711_; lean_object* v_y_4712_; lean_object* v_u_4713_; lean_object* v_Y_4714_; lean_object* v_M_4715_; lean_object* v_L_4716_; lean_object* v_d_4717_; lean_object* v_Q_4718_; lean_object* v_q_4719_; lean_object* v_w_4720_; lean_object* v_W_4721_; lean_object* v_E_4722_; lean_object* v_e_4723_; lean_object* v_c_4724_; lean_object* v_F_4725_; lean_object* v_a_4726_; lean_object* v_b_4727_; lean_object* v_B_4728_; lean_object* v_h_4729_; lean_object* v_K_4730_; lean_object* v_k_4731_; lean_object* v_H_4732_; lean_object* v_m_4733_; lean_object* v_s_4734_; lean_object* v_S_4735_; lean_object* v_A_4736_; lean_object* v_n_4737_; lean_object* v_N_4738_; lean_object* v_V_4739_; lean_object* v_z_4740_; lean_object* v_zabbrev_4741_; lean_object* v_v_4742_; lean_object* v_O_4743_; lean_object* v_X_4744_; lean_object* v_x_4745_; lean_object* v_Z_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4756_; 
v_G_4711_ = lean_ctor_get(v_date_4556_, 0);
v_y_4712_ = lean_ctor_get(v_date_4556_, 1);
v_u_4713_ = lean_ctor_get(v_date_4556_, 2);
v_Y_4714_ = lean_ctor_get(v_date_4556_, 3);
v_M_4715_ = lean_ctor_get(v_date_4556_, 5);
v_L_4716_ = lean_ctor_get(v_date_4556_, 6);
v_d_4717_ = lean_ctor_get(v_date_4556_, 7);
v_Q_4718_ = lean_ctor_get(v_date_4556_, 8);
v_q_4719_ = lean_ctor_get(v_date_4556_, 9);
v_w_4720_ = lean_ctor_get(v_date_4556_, 10);
v_W_4721_ = lean_ctor_get(v_date_4556_, 11);
v_E_4722_ = lean_ctor_get(v_date_4556_, 12);
v_e_4723_ = lean_ctor_get(v_date_4556_, 13);
v_c_4724_ = lean_ctor_get(v_date_4556_, 14);
v_F_4725_ = lean_ctor_get(v_date_4556_, 15);
v_a_4726_ = lean_ctor_get(v_date_4556_, 16);
v_b_4727_ = lean_ctor_get(v_date_4556_, 17);
v_B_4728_ = lean_ctor_get(v_date_4556_, 18);
v_h_4729_ = lean_ctor_get(v_date_4556_, 19);
v_K_4730_ = lean_ctor_get(v_date_4556_, 20);
v_k_4731_ = lean_ctor_get(v_date_4556_, 21);
v_H_4732_ = lean_ctor_get(v_date_4556_, 22);
v_m_4733_ = lean_ctor_get(v_date_4556_, 23);
v_s_4734_ = lean_ctor_get(v_date_4556_, 24);
v_S_4735_ = lean_ctor_get(v_date_4556_, 25);
v_A_4736_ = lean_ctor_get(v_date_4556_, 26);
v_n_4737_ = lean_ctor_get(v_date_4556_, 27);
v_N_4738_ = lean_ctor_get(v_date_4556_, 28);
v_V_4739_ = lean_ctor_get(v_date_4556_, 29);
v_z_4740_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_4741_ = lean_ctor_get(v_date_4556_, 31);
v_v_4742_ = lean_ctor_get(v_date_4556_, 32);
v_O_4743_ = lean_ctor_get(v_date_4556_, 33);
v_X_4744_ = lean_ctor_get(v_date_4556_, 34);
v_x_4745_ = lean_ctor_get(v_date_4556_, 35);
v_Z_4746_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_4756_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_4756_ == 0)
{
lean_object* v_unused_4757_; 
v_unused_4757_ = lean_ctor_get(v_date_4556_, 4);
lean_dec(v_unused_4757_);
v___x_4748_ = v_date_4556_;
v_isShared_4749_ = v_isSharedCheck_4756_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_Z_4746_);
lean_inc(v_x_4745_);
lean_inc(v_X_4744_);
lean_inc(v_O_4743_);
lean_inc(v_v_4742_);
lean_inc(v_zabbrev_4741_);
lean_inc(v_z_4740_);
lean_inc(v_V_4739_);
lean_inc(v_N_4738_);
lean_inc(v_n_4737_);
lean_inc(v_A_4736_);
lean_inc(v_S_4735_);
lean_inc(v_s_4734_);
lean_inc(v_m_4733_);
lean_inc(v_H_4732_);
lean_inc(v_k_4731_);
lean_inc(v_K_4730_);
lean_inc(v_h_4729_);
lean_inc(v_B_4728_);
lean_inc(v_b_4727_);
lean_inc(v_a_4726_);
lean_inc(v_F_4725_);
lean_inc(v_c_4724_);
lean_inc(v_e_4723_);
lean_inc(v_E_4722_);
lean_inc(v_W_4721_);
lean_inc(v_w_4720_);
lean_inc(v_q_4719_);
lean_inc(v_Q_4718_);
lean_inc(v_d_4717_);
lean_inc(v_L_4716_);
lean_inc(v_M_4715_);
lean_inc(v_Y_4714_);
lean_inc(v_u_4713_);
lean_inc(v_y_4712_);
lean_inc(v_G_4711_);
lean_dec(v_date_4556_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4756_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4751_; 
if (v_isShared_4710_ == 0)
{
lean_ctor_set_tag(v___x_4709_, 1);
lean_ctor_set(v___x_4709_, 0, v_data_4558_);
v___x_4751_ = v___x_4709_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_data_4558_);
v___x_4751_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
lean_object* v___x_4753_; 
if (v_isShared_4749_ == 0)
{
lean_ctor_set(v___x_4748_, 4, v___x_4751_);
v___x_4753_ = v___x_4748_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_G_4711_);
lean_ctor_set(v_reuseFailAlloc_4754_, 1, v_y_4712_);
lean_ctor_set(v_reuseFailAlloc_4754_, 2, v_u_4713_);
lean_ctor_set(v_reuseFailAlloc_4754_, 3, v_Y_4714_);
lean_ctor_set(v_reuseFailAlloc_4754_, 4, v___x_4751_);
lean_ctor_set(v_reuseFailAlloc_4754_, 5, v_M_4715_);
lean_ctor_set(v_reuseFailAlloc_4754_, 6, v_L_4716_);
lean_ctor_set(v_reuseFailAlloc_4754_, 7, v_d_4717_);
lean_ctor_set(v_reuseFailAlloc_4754_, 8, v_Q_4718_);
lean_ctor_set(v_reuseFailAlloc_4754_, 9, v_q_4719_);
lean_ctor_set(v_reuseFailAlloc_4754_, 10, v_w_4720_);
lean_ctor_set(v_reuseFailAlloc_4754_, 11, v_W_4721_);
lean_ctor_set(v_reuseFailAlloc_4754_, 12, v_E_4722_);
lean_ctor_set(v_reuseFailAlloc_4754_, 13, v_e_4723_);
lean_ctor_set(v_reuseFailAlloc_4754_, 14, v_c_4724_);
lean_ctor_set(v_reuseFailAlloc_4754_, 15, v_F_4725_);
lean_ctor_set(v_reuseFailAlloc_4754_, 16, v_a_4726_);
lean_ctor_set(v_reuseFailAlloc_4754_, 17, v_b_4727_);
lean_ctor_set(v_reuseFailAlloc_4754_, 18, v_B_4728_);
lean_ctor_set(v_reuseFailAlloc_4754_, 19, v_h_4729_);
lean_ctor_set(v_reuseFailAlloc_4754_, 20, v_K_4730_);
lean_ctor_set(v_reuseFailAlloc_4754_, 21, v_k_4731_);
lean_ctor_set(v_reuseFailAlloc_4754_, 22, v_H_4732_);
lean_ctor_set(v_reuseFailAlloc_4754_, 23, v_m_4733_);
lean_ctor_set(v_reuseFailAlloc_4754_, 24, v_s_4734_);
lean_ctor_set(v_reuseFailAlloc_4754_, 25, v_S_4735_);
lean_ctor_set(v_reuseFailAlloc_4754_, 26, v_A_4736_);
lean_ctor_set(v_reuseFailAlloc_4754_, 27, v_n_4737_);
lean_ctor_set(v_reuseFailAlloc_4754_, 28, v_N_4738_);
lean_ctor_set(v_reuseFailAlloc_4754_, 29, v_V_4739_);
lean_ctor_set(v_reuseFailAlloc_4754_, 30, v_z_4740_);
lean_ctor_set(v_reuseFailAlloc_4754_, 31, v_zabbrev_4741_);
lean_ctor_set(v_reuseFailAlloc_4754_, 32, v_v_4742_);
lean_ctor_set(v_reuseFailAlloc_4754_, 33, v_O_4743_);
lean_ctor_set(v_reuseFailAlloc_4754_, 34, v_X_4744_);
lean_ctor_set(v_reuseFailAlloc_4754_, 35, v_x_4745_);
lean_ctor_set(v_reuseFailAlloc_4754_, 36, v_Z_4746_);
v___x_4753_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
return v___x_4753_;
}
}
}
}
}
case 4:
{
lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4810_; 
v_isSharedCheck_4810_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_4810_ == 0)
{
lean_object* v_unused_4811_; 
v_unused_4811_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_4811_);
v___x_4761_ = v_modifier_4557_;
v_isShared_4762_ = v_isSharedCheck_4810_;
goto v_resetjp_4760_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4810_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v_G_4763_; lean_object* v_y_4764_; lean_object* v_u_4765_; lean_object* v_Y_4766_; lean_object* v_D_4767_; lean_object* v_L_4768_; lean_object* v_d_4769_; lean_object* v_Q_4770_; lean_object* v_q_4771_; lean_object* v_w_4772_; lean_object* v_W_4773_; lean_object* v_E_4774_; lean_object* v_e_4775_; lean_object* v_c_4776_; lean_object* v_F_4777_; lean_object* v_a_4778_; lean_object* v_b_4779_; lean_object* v_B_4780_; lean_object* v_h_4781_; lean_object* v_K_4782_; lean_object* v_k_4783_; lean_object* v_H_4784_; lean_object* v_m_4785_; lean_object* v_s_4786_; lean_object* v_S_4787_; lean_object* v_A_4788_; lean_object* v_n_4789_; lean_object* v_N_4790_; lean_object* v_V_4791_; lean_object* v_z_4792_; lean_object* v_zabbrev_4793_; lean_object* v_v_4794_; lean_object* v_O_4795_; lean_object* v_X_4796_; lean_object* v_x_4797_; lean_object* v_Z_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4808_; 
v_G_4763_ = lean_ctor_get(v_date_4556_, 0);
v_y_4764_ = lean_ctor_get(v_date_4556_, 1);
v_u_4765_ = lean_ctor_get(v_date_4556_, 2);
v_Y_4766_ = lean_ctor_get(v_date_4556_, 3);
v_D_4767_ = lean_ctor_get(v_date_4556_, 4);
v_L_4768_ = lean_ctor_get(v_date_4556_, 6);
v_d_4769_ = lean_ctor_get(v_date_4556_, 7);
v_Q_4770_ = lean_ctor_get(v_date_4556_, 8);
v_q_4771_ = lean_ctor_get(v_date_4556_, 9);
v_w_4772_ = lean_ctor_get(v_date_4556_, 10);
v_W_4773_ = lean_ctor_get(v_date_4556_, 11);
v_E_4774_ = lean_ctor_get(v_date_4556_, 12);
v_e_4775_ = lean_ctor_get(v_date_4556_, 13);
v_c_4776_ = lean_ctor_get(v_date_4556_, 14);
v_F_4777_ = lean_ctor_get(v_date_4556_, 15);
v_a_4778_ = lean_ctor_get(v_date_4556_, 16);
v_b_4779_ = lean_ctor_get(v_date_4556_, 17);
v_B_4780_ = lean_ctor_get(v_date_4556_, 18);
v_h_4781_ = lean_ctor_get(v_date_4556_, 19);
v_K_4782_ = lean_ctor_get(v_date_4556_, 20);
v_k_4783_ = lean_ctor_get(v_date_4556_, 21);
v_H_4784_ = lean_ctor_get(v_date_4556_, 22);
v_m_4785_ = lean_ctor_get(v_date_4556_, 23);
v_s_4786_ = lean_ctor_get(v_date_4556_, 24);
v_S_4787_ = lean_ctor_get(v_date_4556_, 25);
v_A_4788_ = lean_ctor_get(v_date_4556_, 26);
v_n_4789_ = lean_ctor_get(v_date_4556_, 27);
v_N_4790_ = lean_ctor_get(v_date_4556_, 28);
v_V_4791_ = lean_ctor_get(v_date_4556_, 29);
v_z_4792_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_4793_ = lean_ctor_get(v_date_4556_, 31);
v_v_4794_ = lean_ctor_get(v_date_4556_, 32);
v_O_4795_ = lean_ctor_get(v_date_4556_, 33);
v_X_4796_ = lean_ctor_get(v_date_4556_, 34);
v_x_4797_ = lean_ctor_get(v_date_4556_, 35);
v_Z_4798_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_4808_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_4808_ == 0)
{
lean_object* v_unused_4809_; 
v_unused_4809_ = lean_ctor_get(v_date_4556_, 5);
lean_dec(v_unused_4809_);
v___x_4800_ = v_date_4556_;
v_isShared_4801_ = v_isSharedCheck_4808_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_Z_4798_);
lean_inc(v_x_4797_);
lean_inc(v_X_4796_);
lean_inc(v_O_4795_);
lean_inc(v_v_4794_);
lean_inc(v_zabbrev_4793_);
lean_inc(v_z_4792_);
lean_inc(v_V_4791_);
lean_inc(v_N_4790_);
lean_inc(v_n_4789_);
lean_inc(v_A_4788_);
lean_inc(v_S_4787_);
lean_inc(v_s_4786_);
lean_inc(v_m_4785_);
lean_inc(v_H_4784_);
lean_inc(v_k_4783_);
lean_inc(v_K_4782_);
lean_inc(v_h_4781_);
lean_inc(v_B_4780_);
lean_inc(v_b_4779_);
lean_inc(v_a_4778_);
lean_inc(v_F_4777_);
lean_inc(v_c_4776_);
lean_inc(v_e_4775_);
lean_inc(v_E_4774_);
lean_inc(v_W_4773_);
lean_inc(v_w_4772_);
lean_inc(v_q_4771_);
lean_inc(v_Q_4770_);
lean_inc(v_d_4769_);
lean_inc(v_L_4768_);
lean_inc(v_D_4767_);
lean_inc(v_Y_4766_);
lean_inc(v_u_4765_);
lean_inc(v_y_4764_);
lean_inc(v_G_4763_);
lean_dec(v_date_4556_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4808_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4803_; 
if (v_isShared_4762_ == 0)
{
lean_ctor_set_tag(v___x_4761_, 1);
lean_ctor_set(v___x_4761_, 0, v_data_4558_);
v___x_4803_ = v___x_4761_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_data_4558_);
v___x_4803_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
lean_object* v___x_4805_; 
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 5, v___x_4803_);
v___x_4805_ = v___x_4800_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_G_4763_);
lean_ctor_set(v_reuseFailAlloc_4806_, 1, v_y_4764_);
lean_ctor_set(v_reuseFailAlloc_4806_, 2, v_u_4765_);
lean_ctor_set(v_reuseFailAlloc_4806_, 3, v_Y_4766_);
lean_ctor_set(v_reuseFailAlloc_4806_, 4, v_D_4767_);
lean_ctor_set(v_reuseFailAlloc_4806_, 5, v___x_4803_);
lean_ctor_set(v_reuseFailAlloc_4806_, 6, v_L_4768_);
lean_ctor_set(v_reuseFailAlloc_4806_, 7, v_d_4769_);
lean_ctor_set(v_reuseFailAlloc_4806_, 8, v_Q_4770_);
lean_ctor_set(v_reuseFailAlloc_4806_, 9, v_q_4771_);
lean_ctor_set(v_reuseFailAlloc_4806_, 10, v_w_4772_);
lean_ctor_set(v_reuseFailAlloc_4806_, 11, v_W_4773_);
lean_ctor_set(v_reuseFailAlloc_4806_, 12, v_E_4774_);
lean_ctor_set(v_reuseFailAlloc_4806_, 13, v_e_4775_);
lean_ctor_set(v_reuseFailAlloc_4806_, 14, v_c_4776_);
lean_ctor_set(v_reuseFailAlloc_4806_, 15, v_F_4777_);
lean_ctor_set(v_reuseFailAlloc_4806_, 16, v_a_4778_);
lean_ctor_set(v_reuseFailAlloc_4806_, 17, v_b_4779_);
lean_ctor_set(v_reuseFailAlloc_4806_, 18, v_B_4780_);
lean_ctor_set(v_reuseFailAlloc_4806_, 19, v_h_4781_);
lean_ctor_set(v_reuseFailAlloc_4806_, 20, v_K_4782_);
lean_ctor_set(v_reuseFailAlloc_4806_, 21, v_k_4783_);
lean_ctor_set(v_reuseFailAlloc_4806_, 22, v_H_4784_);
lean_ctor_set(v_reuseFailAlloc_4806_, 23, v_m_4785_);
lean_ctor_set(v_reuseFailAlloc_4806_, 24, v_s_4786_);
lean_ctor_set(v_reuseFailAlloc_4806_, 25, v_S_4787_);
lean_ctor_set(v_reuseFailAlloc_4806_, 26, v_A_4788_);
lean_ctor_set(v_reuseFailAlloc_4806_, 27, v_n_4789_);
lean_ctor_set(v_reuseFailAlloc_4806_, 28, v_N_4790_);
lean_ctor_set(v_reuseFailAlloc_4806_, 29, v_V_4791_);
lean_ctor_set(v_reuseFailAlloc_4806_, 30, v_z_4792_);
lean_ctor_set(v_reuseFailAlloc_4806_, 31, v_zabbrev_4793_);
lean_ctor_set(v_reuseFailAlloc_4806_, 32, v_v_4794_);
lean_ctor_set(v_reuseFailAlloc_4806_, 33, v_O_4795_);
lean_ctor_set(v_reuseFailAlloc_4806_, 34, v_X_4796_);
lean_ctor_set(v_reuseFailAlloc_4806_, 35, v_x_4797_);
lean_ctor_set(v_reuseFailAlloc_4806_, 36, v_Z_4798_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
}
}
}
case 5:
{
lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4862_; 
v_isSharedCheck_4862_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_4862_ == 0)
{
lean_object* v_unused_4863_; 
v_unused_4863_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_4863_);
v___x_4813_ = v_modifier_4557_;
v_isShared_4814_ = v_isSharedCheck_4862_;
goto v_resetjp_4812_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4862_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v_G_4815_; lean_object* v_y_4816_; lean_object* v_u_4817_; lean_object* v_Y_4818_; lean_object* v_D_4819_; lean_object* v_M_4820_; lean_object* v_d_4821_; lean_object* v_Q_4822_; lean_object* v_q_4823_; lean_object* v_w_4824_; lean_object* v_W_4825_; lean_object* v_E_4826_; lean_object* v_e_4827_; lean_object* v_c_4828_; lean_object* v_F_4829_; lean_object* v_a_4830_; lean_object* v_b_4831_; lean_object* v_B_4832_; lean_object* v_h_4833_; lean_object* v_K_4834_; lean_object* v_k_4835_; lean_object* v_H_4836_; lean_object* v_m_4837_; lean_object* v_s_4838_; lean_object* v_S_4839_; lean_object* v_A_4840_; lean_object* v_n_4841_; lean_object* v_N_4842_; lean_object* v_V_4843_; lean_object* v_z_4844_; lean_object* v_zabbrev_4845_; lean_object* v_v_4846_; lean_object* v_O_4847_; lean_object* v_X_4848_; lean_object* v_x_4849_; lean_object* v_Z_4850_; lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4860_; 
v_G_4815_ = lean_ctor_get(v_date_4556_, 0);
v_y_4816_ = lean_ctor_get(v_date_4556_, 1);
v_u_4817_ = lean_ctor_get(v_date_4556_, 2);
v_Y_4818_ = lean_ctor_get(v_date_4556_, 3);
v_D_4819_ = lean_ctor_get(v_date_4556_, 4);
v_M_4820_ = lean_ctor_get(v_date_4556_, 5);
v_d_4821_ = lean_ctor_get(v_date_4556_, 7);
v_Q_4822_ = lean_ctor_get(v_date_4556_, 8);
v_q_4823_ = lean_ctor_get(v_date_4556_, 9);
v_w_4824_ = lean_ctor_get(v_date_4556_, 10);
v_W_4825_ = lean_ctor_get(v_date_4556_, 11);
v_E_4826_ = lean_ctor_get(v_date_4556_, 12);
v_e_4827_ = lean_ctor_get(v_date_4556_, 13);
v_c_4828_ = lean_ctor_get(v_date_4556_, 14);
v_F_4829_ = lean_ctor_get(v_date_4556_, 15);
v_a_4830_ = lean_ctor_get(v_date_4556_, 16);
v_b_4831_ = lean_ctor_get(v_date_4556_, 17);
v_B_4832_ = lean_ctor_get(v_date_4556_, 18);
v_h_4833_ = lean_ctor_get(v_date_4556_, 19);
v_K_4834_ = lean_ctor_get(v_date_4556_, 20);
v_k_4835_ = lean_ctor_get(v_date_4556_, 21);
v_H_4836_ = lean_ctor_get(v_date_4556_, 22);
v_m_4837_ = lean_ctor_get(v_date_4556_, 23);
v_s_4838_ = lean_ctor_get(v_date_4556_, 24);
v_S_4839_ = lean_ctor_get(v_date_4556_, 25);
v_A_4840_ = lean_ctor_get(v_date_4556_, 26);
v_n_4841_ = lean_ctor_get(v_date_4556_, 27);
v_N_4842_ = lean_ctor_get(v_date_4556_, 28);
v_V_4843_ = lean_ctor_get(v_date_4556_, 29);
v_z_4844_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_4845_ = lean_ctor_get(v_date_4556_, 31);
v_v_4846_ = lean_ctor_get(v_date_4556_, 32);
v_O_4847_ = lean_ctor_get(v_date_4556_, 33);
v_X_4848_ = lean_ctor_get(v_date_4556_, 34);
v_x_4849_ = lean_ctor_get(v_date_4556_, 35);
v_Z_4850_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_4860_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_4860_ == 0)
{
lean_object* v_unused_4861_; 
v_unused_4861_ = lean_ctor_get(v_date_4556_, 6);
lean_dec(v_unused_4861_);
v___x_4852_ = v_date_4556_;
v_isShared_4853_ = v_isSharedCheck_4860_;
goto v_resetjp_4851_;
}
else
{
lean_inc(v_Z_4850_);
lean_inc(v_x_4849_);
lean_inc(v_X_4848_);
lean_inc(v_O_4847_);
lean_inc(v_v_4846_);
lean_inc(v_zabbrev_4845_);
lean_inc(v_z_4844_);
lean_inc(v_V_4843_);
lean_inc(v_N_4842_);
lean_inc(v_n_4841_);
lean_inc(v_A_4840_);
lean_inc(v_S_4839_);
lean_inc(v_s_4838_);
lean_inc(v_m_4837_);
lean_inc(v_H_4836_);
lean_inc(v_k_4835_);
lean_inc(v_K_4834_);
lean_inc(v_h_4833_);
lean_inc(v_B_4832_);
lean_inc(v_b_4831_);
lean_inc(v_a_4830_);
lean_inc(v_F_4829_);
lean_inc(v_c_4828_);
lean_inc(v_e_4827_);
lean_inc(v_E_4826_);
lean_inc(v_W_4825_);
lean_inc(v_w_4824_);
lean_inc(v_q_4823_);
lean_inc(v_Q_4822_);
lean_inc(v_d_4821_);
lean_inc(v_M_4820_);
lean_inc(v_D_4819_);
lean_inc(v_Y_4818_);
lean_inc(v_u_4817_);
lean_inc(v_y_4816_);
lean_inc(v_G_4815_);
lean_dec(v_date_4556_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4860_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v___x_4855_; 
if (v_isShared_4814_ == 0)
{
lean_ctor_set_tag(v___x_4813_, 1);
lean_ctor_set(v___x_4813_, 0, v_data_4558_);
v___x_4855_ = v___x_4813_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_data_4558_);
v___x_4855_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
lean_object* v___x_4857_; 
if (v_isShared_4853_ == 0)
{
lean_ctor_set(v___x_4852_, 6, v___x_4855_);
v___x_4857_ = v___x_4852_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_G_4815_);
lean_ctor_set(v_reuseFailAlloc_4858_, 1, v_y_4816_);
lean_ctor_set(v_reuseFailAlloc_4858_, 2, v_u_4817_);
lean_ctor_set(v_reuseFailAlloc_4858_, 3, v_Y_4818_);
lean_ctor_set(v_reuseFailAlloc_4858_, 4, v_D_4819_);
lean_ctor_set(v_reuseFailAlloc_4858_, 5, v_M_4820_);
lean_ctor_set(v_reuseFailAlloc_4858_, 6, v___x_4855_);
lean_ctor_set(v_reuseFailAlloc_4858_, 7, v_d_4821_);
lean_ctor_set(v_reuseFailAlloc_4858_, 8, v_Q_4822_);
lean_ctor_set(v_reuseFailAlloc_4858_, 9, v_q_4823_);
lean_ctor_set(v_reuseFailAlloc_4858_, 10, v_w_4824_);
lean_ctor_set(v_reuseFailAlloc_4858_, 11, v_W_4825_);
lean_ctor_set(v_reuseFailAlloc_4858_, 12, v_E_4826_);
lean_ctor_set(v_reuseFailAlloc_4858_, 13, v_e_4827_);
lean_ctor_set(v_reuseFailAlloc_4858_, 14, v_c_4828_);
lean_ctor_set(v_reuseFailAlloc_4858_, 15, v_F_4829_);
lean_ctor_set(v_reuseFailAlloc_4858_, 16, v_a_4830_);
lean_ctor_set(v_reuseFailAlloc_4858_, 17, v_b_4831_);
lean_ctor_set(v_reuseFailAlloc_4858_, 18, v_B_4832_);
lean_ctor_set(v_reuseFailAlloc_4858_, 19, v_h_4833_);
lean_ctor_set(v_reuseFailAlloc_4858_, 20, v_K_4834_);
lean_ctor_set(v_reuseFailAlloc_4858_, 21, v_k_4835_);
lean_ctor_set(v_reuseFailAlloc_4858_, 22, v_H_4836_);
lean_ctor_set(v_reuseFailAlloc_4858_, 23, v_m_4837_);
lean_ctor_set(v_reuseFailAlloc_4858_, 24, v_s_4838_);
lean_ctor_set(v_reuseFailAlloc_4858_, 25, v_S_4839_);
lean_ctor_set(v_reuseFailAlloc_4858_, 26, v_A_4840_);
lean_ctor_set(v_reuseFailAlloc_4858_, 27, v_n_4841_);
lean_ctor_set(v_reuseFailAlloc_4858_, 28, v_N_4842_);
lean_ctor_set(v_reuseFailAlloc_4858_, 29, v_V_4843_);
lean_ctor_set(v_reuseFailAlloc_4858_, 30, v_z_4844_);
lean_ctor_set(v_reuseFailAlloc_4858_, 31, v_zabbrev_4845_);
lean_ctor_set(v_reuseFailAlloc_4858_, 32, v_v_4846_);
lean_ctor_set(v_reuseFailAlloc_4858_, 33, v_O_4847_);
lean_ctor_set(v_reuseFailAlloc_4858_, 34, v_X_4848_);
lean_ctor_set(v_reuseFailAlloc_4858_, 35, v_x_4849_);
lean_ctor_set(v_reuseFailAlloc_4858_, 36, v_Z_4850_);
v___x_4857_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
return v___x_4857_;
}
}
}
}
}
case 6:
{
lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4914_; 
v_isSharedCheck_4914_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_4914_ == 0)
{
lean_object* v_unused_4915_; 
v_unused_4915_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_4915_);
v___x_4865_ = v_modifier_4557_;
v_isShared_4866_ = v_isSharedCheck_4914_;
goto v_resetjp_4864_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4914_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
lean_object* v_G_4867_; lean_object* v_y_4868_; lean_object* v_u_4869_; lean_object* v_Y_4870_; lean_object* v_D_4871_; lean_object* v_M_4872_; lean_object* v_L_4873_; lean_object* v_Q_4874_; lean_object* v_q_4875_; lean_object* v_w_4876_; lean_object* v_W_4877_; lean_object* v_E_4878_; lean_object* v_e_4879_; lean_object* v_c_4880_; lean_object* v_F_4881_; lean_object* v_a_4882_; lean_object* v_b_4883_; lean_object* v_B_4884_; lean_object* v_h_4885_; lean_object* v_K_4886_; lean_object* v_k_4887_; lean_object* v_H_4888_; lean_object* v_m_4889_; lean_object* v_s_4890_; lean_object* v_S_4891_; lean_object* v_A_4892_; lean_object* v_n_4893_; lean_object* v_N_4894_; lean_object* v_V_4895_; lean_object* v_z_4896_; lean_object* v_zabbrev_4897_; lean_object* v_v_4898_; lean_object* v_O_4899_; lean_object* v_X_4900_; lean_object* v_x_4901_; lean_object* v_Z_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4912_; 
v_G_4867_ = lean_ctor_get(v_date_4556_, 0);
v_y_4868_ = lean_ctor_get(v_date_4556_, 1);
v_u_4869_ = lean_ctor_get(v_date_4556_, 2);
v_Y_4870_ = lean_ctor_get(v_date_4556_, 3);
v_D_4871_ = lean_ctor_get(v_date_4556_, 4);
v_M_4872_ = lean_ctor_get(v_date_4556_, 5);
v_L_4873_ = lean_ctor_get(v_date_4556_, 6);
v_Q_4874_ = lean_ctor_get(v_date_4556_, 8);
v_q_4875_ = lean_ctor_get(v_date_4556_, 9);
v_w_4876_ = lean_ctor_get(v_date_4556_, 10);
v_W_4877_ = lean_ctor_get(v_date_4556_, 11);
v_E_4878_ = lean_ctor_get(v_date_4556_, 12);
v_e_4879_ = lean_ctor_get(v_date_4556_, 13);
v_c_4880_ = lean_ctor_get(v_date_4556_, 14);
v_F_4881_ = lean_ctor_get(v_date_4556_, 15);
v_a_4882_ = lean_ctor_get(v_date_4556_, 16);
v_b_4883_ = lean_ctor_get(v_date_4556_, 17);
v_B_4884_ = lean_ctor_get(v_date_4556_, 18);
v_h_4885_ = lean_ctor_get(v_date_4556_, 19);
v_K_4886_ = lean_ctor_get(v_date_4556_, 20);
v_k_4887_ = lean_ctor_get(v_date_4556_, 21);
v_H_4888_ = lean_ctor_get(v_date_4556_, 22);
v_m_4889_ = lean_ctor_get(v_date_4556_, 23);
v_s_4890_ = lean_ctor_get(v_date_4556_, 24);
v_S_4891_ = lean_ctor_get(v_date_4556_, 25);
v_A_4892_ = lean_ctor_get(v_date_4556_, 26);
v_n_4893_ = lean_ctor_get(v_date_4556_, 27);
v_N_4894_ = lean_ctor_get(v_date_4556_, 28);
v_V_4895_ = lean_ctor_get(v_date_4556_, 29);
v_z_4896_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_4897_ = lean_ctor_get(v_date_4556_, 31);
v_v_4898_ = lean_ctor_get(v_date_4556_, 32);
v_O_4899_ = lean_ctor_get(v_date_4556_, 33);
v_X_4900_ = lean_ctor_get(v_date_4556_, 34);
v_x_4901_ = lean_ctor_get(v_date_4556_, 35);
v_Z_4902_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_4912_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_4912_ == 0)
{
lean_object* v_unused_4913_; 
v_unused_4913_ = lean_ctor_get(v_date_4556_, 7);
lean_dec(v_unused_4913_);
v___x_4904_ = v_date_4556_;
v_isShared_4905_ = v_isSharedCheck_4912_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_Z_4902_);
lean_inc(v_x_4901_);
lean_inc(v_X_4900_);
lean_inc(v_O_4899_);
lean_inc(v_v_4898_);
lean_inc(v_zabbrev_4897_);
lean_inc(v_z_4896_);
lean_inc(v_V_4895_);
lean_inc(v_N_4894_);
lean_inc(v_n_4893_);
lean_inc(v_A_4892_);
lean_inc(v_S_4891_);
lean_inc(v_s_4890_);
lean_inc(v_m_4889_);
lean_inc(v_H_4888_);
lean_inc(v_k_4887_);
lean_inc(v_K_4886_);
lean_inc(v_h_4885_);
lean_inc(v_B_4884_);
lean_inc(v_b_4883_);
lean_inc(v_a_4882_);
lean_inc(v_F_4881_);
lean_inc(v_c_4880_);
lean_inc(v_e_4879_);
lean_inc(v_E_4878_);
lean_inc(v_W_4877_);
lean_inc(v_w_4876_);
lean_inc(v_q_4875_);
lean_inc(v_Q_4874_);
lean_inc(v_L_4873_);
lean_inc(v_M_4872_);
lean_inc(v_D_4871_);
lean_inc(v_Y_4870_);
lean_inc(v_u_4869_);
lean_inc(v_y_4868_);
lean_inc(v_G_4867_);
lean_dec(v_date_4556_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4912_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v___x_4907_; 
if (v_isShared_4866_ == 0)
{
lean_ctor_set_tag(v___x_4865_, 1);
lean_ctor_set(v___x_4865_, 0, v_data_4558_);
v___x_4907_ = v___x_4865_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_data_4558_);
v___x_4907_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
lean_object* v___x_4909_; 
if (v_isShared_4905_ == 0)
{
lean_ctor_set(v___x_4904_, 7, v___x_4907_);
v___x_4909_ = v___x_4904_;
goto v_reusejp_4908_;
}
else
{
lean_object* v_reuseFailAlloc_4910_; 
v_reuseFailAlloc_4910_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4910_, 0, v_G_4867_);
lean_ctor_set(v_reuseFailAlloc_4910_, 1, v_y_4868_);
lean_ctor_set(v_reuseFailAlloc_4910_, 2, v_u_4869_);
lean_ctor_set(v_reuseFailAlloc_4910_, 3, v_Y_4870_);
lean_ctor_set(v_reuseFailAlloc_4910_, 4, v_D_4871_);
lean_ctor_set(v_reuseFailAlloc_4910_, 5, v_M_4872_);
lean_ctor_set(v_reuseFailAlloc_4910_, 6, v_L_4873_);
lean_ctor_set(v_reuseFailAlloc_4910_, 7, v___x_4907_);
lean_ctor_set(v_reuseFailAlloc_4910_, 8, v_Q_4874_);
lean_ctor_set(v_reuseFailAlloc_4910_, 9, v_q_4875_);
lean_ctor_set(v_reuseFailAlloc_4910_, 10, v_w_4876_);
lean_ctor_set(v_reuseFailAlloc_4910_, 11, v_W_4877_);
lean_ctor_set(v_reuseFailAlloc_4910_, 12, v_E_4878_);
lean_ctor_set(v_reuseFailAlloc_4910_, 13, v_e_4879_);
lean_ctor_set(v_reuseFailAlloc_4910_, 14, v_c_4880_);
lean_ctor_set(v_reuseFailAlloc_4910_, 15, v_F_4881_);
lean_ctor_set(v_reuseFailAlloc_4910_, 16, v_a_4882_);
lean_ctor_set(v_reuseFailAlloc_4910_, 17, v_b_4883_);
lean_ctor_set(v_reuseFailAlloc_4910_, 18, v_B_4884_);
lean_ctor_set(v_reuseFailAlloc_4910_, 19, v_h_4885_);
lean_ctor_set(v_reuseFailAlloc_4910_, 20, v_K_4886_);
lean_ctor_set(v_reuseFailAlloc_4910_, 21, v_k_4887_);
lean_ctor_set(v_reuseFailAlloc_4910_, 22, v_H_4888_);
lean_ctor_set(v_reuseFailAlloc_4910_, 23, v_m_4889_);
lean_ctor_set(v_reuseFailAlloc_4910_, 24, v_s_4890_);
lean_ctor_set(v_reuseFailAlloc_4910_, 25, v_S_4891_);
lean_ctor_set(v_reuseFailAlloc_4910_, 26, v_A_4892_);
lean_ctor_set(v_reuseFailAlloc_4910_, 27, v_n_4893_);
lean_ctor_set(v_reuseFailAlloc_4910_, 28, v_N_4894_);
lean_ctor_set(v_reuseFailAlloc_4910_, 29, v_V_4895_);
lean_ctor_set(v_reuseFailAlloc_4910_, 30, v_z_4896_);
lean_ctor_set(v_reuseFailAlloc_4910_, 31, v_zabbrev_4897_);
lean_ctor_set(v_reuseFailAlloc_4910_, 32, v_v_4898_);
lean_ctor_set(v_reuseFailAlloc_4910_, 33, v_O_4899_);
lean_ctor_set(v_reuseFailAlloc_4910_, 34, v_X_4900_);
lean_ctor_set(v_reuseFailAlloc_4910_, 35, v_x_4901_);
lean_ctor_set(v_reuseFailAlloc_4910_, 36, v_Z_4902_);
v___x_4909_ = v_reuseFailAlloc_4910_;
goto v_reusejp_4908_;
}
v_reusejp_4908_:
{
return v___x_4909_;
}
}
}
}
}
case 7:
{
lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4966_; 
v_isSharedCheck_4966_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_4966_ == 0)
{
lean_object* v_unused_4967_; 
v_unused_4967_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_4967_);
v___x_4917_ = v_modifier_4557_;
v_isShared_4918_ = v_isSharedCheck_4966_;
goto v_resetjp_4916_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4966_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v_G_4919_; lean_object* v_y_4920_; lean_object* v_u_4921_; lean_object* v_Y_4922_; lean_object* v_D_4923_; lean_object* v_M_4924_; lean_object* v_L_4925_; lean_object* v_d_4926_; lean_object* v_q_4927_; lean_object* v_w_4928_; lean_object* v_W_4929_; lean_object* v_E_4930_; lean_object* v_e_4931_; lean_object* v_c_4932_; lean_object* v_F_4933_; lean_object* v_a_4934_; lean_object* v_b_4935_; lean_object* v_B_4936_; lean_object* v_h_4937_; lean_object* v_K_4938_; lean_object* v_k_4939_; lean_object* v_H_4940_; lean_object* v_m_4941_; lean_object* v_s_4942_; lean_object* v_S_4943_; lean_object* v_A_4944_; lean_object* v_n_4945_; lean_object* v_N_4946_; lean_object* v_V_4947_; lean_object* v_z_4948_; lean_object* v_zabbrev_4949_; lean_object* v_v_4950_; lean_object* v_O_4951_; lean_object* v_X_4952_; lean_object* v_x_4953_; lean_object* v_Z_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_4964_; 
v_G_4919_ = lean_ctor_get(v_date_4556_, 0);
v_y_4920_ = lean_ctor_get(v_date_4556_, 1);
v_u_4921_ = lean_ctor_get(v_date_4556_, 2);
v_Y_4922_ = lean_ctor_get(v_date_4556_, 3);
v_D_4923_ = lean_ctor_get(v_date_4556_, 4);
v_M_4924_ = lean_ctor_get(v_date_4556_, 5);
v_L_4925_ = lean_ctor_get(v_date_4556_, 6);
v_d_4926_ = lean_ctor_get(v_date_4556_, 7);
v_q_4927_ = lean_ctor_get(v_date_4556_, 9);
v_w_4928_ = lean_ctor_get(v_date_4556_, 10);
v_W_4929_ = lean_ctor_get(v_date_4556_, 11);
v_E_4930_ = lean_ctor_get(v_date_4556_, 12);
v_e_4931_ = lean_ctor_get(v_date_4556_, 13);
v_c_4932_ = lean_ctor_get(v_date_4556_, 14);
v_F_4933_ = lean_ctor_get(v_date_4556_, 15);
v_a_4934_ = lean_ctor_get(v_date_4556_, 16);
v_b_4935_ = lean_ctor_get(v_date_4556_, 17);
v_B_4936_ = lean_ctor_get(v_date_4556_, 18);
v_h_4937_ = lean_ctor_get(v_date_4556_, 19);
v_K_4938_ = lean_ctor_get(v_date_4556_, 20);
v_k_4939_ = lean_ctor_get(v_date_4556_, 21);
v_H_4940_ = lean_ctor_get(v_date_4556_, 22);
v_m_4941_ = lean_ctor_get(v_date_4556_, 23);
v_s_4942_ = lean_ctor_get(v_date_4556_, 24);
v_S_4943_ = lean_ctor_get(v_date_4556_, 25);
v_A_4944_ = lean_ctor_get(v_date_4556_, 26);
v_n_4945_ = lean_ctor_get(v_date_4556_, 27);
v_N_4946_ = lean_ctor_get(v_date_4556_, 28);
v_V_4947_ = lean_ctor_get(v_date_4556_, 29);
v_z_4948_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_4949_ = lean_ctor_get(v_date_4556_, 31);
v_v_4950_ = lean_ctor_get(v_date_4556_, 32);
v_O_4951_ = lean_ctor_get(v_date_4556_, 33);
v_X_4952_ = lean_ctor_get(v_date_4556_, 34);
v_x_4953_ = lean_ctor_get(v_date_4556_, 35);
v_Z_4954_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_4964_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_4964_ == 0)
{
lean_object* v_unused_4965_; 
v_unused_4965_ = lean_ctor_get(v_date_4556_, 8);
lean_dec(v_unused_4965_);
v___x_4956_ = v_date_4556_;
v_isShared_4957_ = v_isSharedCheck_4964_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_Z_4954_);
lean_inc(v_x_4953_);
lean_inc(v_X_4952_);
lean_inc(v_O_4951_);
lean_inc(v_v_4950_);
lean_inc(v_zabbrev_4949_);
lean_inc(v_z_4948_);
lean_inc(v_V_4947_);
lean_inc(v_N_4946_);
lean_inc(v_n_4945_);
lean_inc(v_A_4944_);
lean_inc(v_S_4943_);
lean_inc(v_s_4942_);
lean_inc(v_m_4941_);
lean_inc(v_H_4940_);
lean_inc(v_k_4939_);
lean_inc(v_K_4938_);
lean_inc(v_h_4937_);
lean_inc(v_B_4936_);
lean_inc(v_b_4935_);
lean_inc(v_a_4934_);
lean_inc(v_F_4933_);
lean_inc(v_c_4932_);
lean_inc(v_e_4931_);
lean_inc(v_E_4930_);
lean_inc(v_W_4929_);
lean_inc(v_w_4928_);
lean_inc(v_q_4927_);
lean_inc(v_d_4926_);
lean_inc(v_L_4925_);
lean_inc(v_M_4924_);
lean_inc(v_D_4923_);
lean_inc(v_Y_4922_);
lean_inc(v_u_4921_);
lean_inc(v_y_4920_);
lean_inc(v_G_4919_);
lean_dec(v_date_4556_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_4964_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v___x_4959_; 
if (v_isShared_4918_ == 0)
{
lean_ctor_set_tag(v___x_4917_, 1);
lean_ctor_set(v___x_4917_, 0, v_data_4558_);
v___x_4959_ = v___x_4917_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4963_; 
v_reuseFailAlloc_4963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4963_, 0, v_data_4558_);
v___x_4959_ = v_reuseFailAlloc_4963_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
lean_object* v___x_4961_; 
if (v_isShared_4957_ == 0)
{
lean_ctor_set(v___x_4956_, 8, v___x_4959_);
v___x_4961_ = v___x_4956_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_G_4919_);
lean_ctor_set(v_reuseFailAlloc_4962_, 1, v_y_4920_);
lean_ctor_set(v_reuseFailAlloc_4962_, 2, v_u_4921_);
lean_ctor_set(v_reuseFailAlloc_4962_, 3, v_Y_4922_);
lean_ctor_set(v_reuseFailAlloc_4962_, 4, v_D_4923_);
lean_ctor_set(v_reuseFailAlloc_4962_, 5, v_M_4924_);
lean_ctor_set(v_reuseFailAlloc_4962_, 6, v_L_4925_);
lean_ctor_set(v_reuseFailAlloc_4962_, 7, v_d_4926_);
lean_ctor_set(v_reuseFailAlloc_4962_, 8, v___x_4959_);
lean_ctor_set(v_reuseFailAlloc_4962_, 9, v_q_4927_);
lean_ctor_set(v_reuseFailAlloc_4962_, 10, v_w_4928_);
lean_ctor_set(v_reuseFailAlloc_4962_, 11, v_W_4929_);
lean_ctor_set(v_reuseFailAlloc_4962_, 12, v_E_4930_);
lean_ctor_set(v_reuseFailAlloc_4962_, 13, v_e_4931_);
lean_ctor_set(v_reuseFailAlloc_4962_, 14, v_c_4932_);
lean_ctor_set(v_reuseFailAlloc_4962_, 15, v_F_4933_);
lean_ctor_set(v_reuseFailAlloc_4962_, 16, v_a_4934_);
lean_ctor_set(v_reuseFailAlloc_4962_, 17, v_b_4935_);
lean_ctor_set(v_reuseFailAlloc_4962_, 18, v_B_4936_);
lean_ctor_set(v_reuseFailAlloc_4962_, 19, v_h_4937_);
lean_ctor_set(v_reuseFailAlloc_4962_, 20, v_K_4938_);
lean_ctor_set(v_reuseFailAlloc_4962_, 21, v_k_4939_);
lean_ctor_set(v_reuseFailAlloc_4962_, 22, v_H_4940_);
lean_ctor_set(v_reuseFailAlloc_4962_, 23, v_m_4941_);
lean_ctor_set(v_reuseFailAlloc_4962_, 24, v_s_4942_);
lean_ctor_set(v_reuseFailAlloc_4962_, 25, v_S_4943_);
lean_ctor_set(v_reuseFailAlloc_4962_, 26, v_A_4944_);
lean_ctor_set(v_reuseFailAlloc_4962_, 27, v_n_4945_);
lean_ctor_set(v_reuseFailAlloc_4962_, 28, v_N_4946_);
lean_ctor_set(v_reuseFailAlloc_4962_, 29, v_V_4947_);
lean_ctor_set(v_reuseFailAlloc_4962_, 30, v_z_4948_);
lean_ctor_set(v_reuseFailAlloc_4962_, 31, v_zabbrev_4949_);
lean_ctor_set(v_reuseFailAlloc_4962_, 32, v_v_4950_);
lean_ctor_set(v_reuseFailAlloc_4962_, 33, v_O_4951_);
lean_ctor_set(v_reuseFailAlloc_4962_, 34, v_X_4952_);
lean_ctor_set(v_reuseFailAlloc_4962_, 35, v_x_4953_);
lean_ctor_set(v_reuseFailAlloc_4962_, 36, v_Z_4954_);
v___x_4961_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
return v___x_4961_;
}
}
}
}
}
case 8:
{
lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_5018_; 
v_isSharedCheck_5018_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_5018_ == 0)
{
lean_object* v_unused_5019_; 
v_unused_5019_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_5019_);
v___x_4969_ = v_modifier_4557_;
v_isShared_4970_ = v_isSharedCheck_5018_;
goto v_resetjp_4968_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_5018_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v_G_4971_; lean_object* v_y_4972_; lean_object* v_u_4973_; lean_object* v_Y_4974_; lean_object* v_D_4975_; lean_object* v_M_4976_; lean_object* v_L_4977_; lean_object* v_d_4978_; lean_object* v_Q_4979_; lean_object* v_w_4980_; lean_object* v_W_4981_; lean_object* v_E_4982_; lean_object* v_e_4983_; lean_object* v_c_4984_; lean_object* v_F_4985_; lean_object* v_a_4986_; lean_object* v_b_4987_; lean_object* v_B_4988_; lean_object* v_h_4989_; lean_object* v_K_4990_; lean_object* v_k_4991_; lean_object* v_H_4992_; lean_object* v_m_4993_; lean_object* v_s_4994_; lean_object* v_S_4995_; lean_object* v_A_4996_; lean_object* v_n_4997_; lean_object* v_N_4998_; lean_object* v_V_4999_; lean_object* v_z_5000_; lean_object* v_zabbrev_5001_; lean_object* v_v_5002_; lean_object* v_O_5003_; lean_object* v_X_5004_; lean_object* v_x_5005_; lean_object* v_Z_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5016_; 
v_G_4971_ = lean_ctor_get(v_date_4556_, 0);
v_y_4972_ = lean_ctor_get(v_date_4556_, 1);
v_u_4973_ = lean_ctor_get(v_date_4556_, 2);
v_Y_4974_ = lean_ctor_get(v_date_4556_, 3);
v_D_4975_ = lean_ctor_get(v_date_4556_, 4);
v_M_4976_ = lean_ctor_get(v_date_4556_, 5);
v_L_4977_ = lean_ctor_get(v_date_4556_, 6);
v_d_4978_ = lean_ctor_get(v_date_4556_, 7);
v_Q_4979_ = lean_ctor_get(v_date_4556_, 8);
v_w_4980_ = lean_ctor_get(v_date_4556_, 10);
v_W_4981_ = lean_ctor_get(v_date_4556_, 11);
v_E_4982_ = lean_ctor_get(v_date_4556_, 12);
v_e_4983_ = lean_ctor_get(v_date_4556_, 13);
v_c_4984_ = lean_ctor_get(v_date_4556_, 14);
v_F_4985_ = lean_ctor_get(v_date_4556_, 15);
v_a_4986_ = lean_ctor_get(v_date_4556_, 16);
v_b_4987_ = lean_ctor_get(v_date_4556_, 17);
v_B_4988_ = lean_ctor_get(v_date_4556_, 18);
v_h_4989_ = lean_ctor_get(v_date_4556_, 19);
v_K_4990_ = lean_ctor_get(v_date_4556_, 20);
v_k_4991_ = lean_ctor_get(v_date_4556_, 21);
v_H_4992_ = lean_ctor_get(v_date_4556_, 22);
v_m_4993_ = lean_ctor_get(v_date_4556_, 23);
v_s_4994_ = lean_ctor_get(v_date_4556_, 24);
v_S_4995_ = lean_ctor_get(v_date_4556_, 25);
v_A_4996_ = lean_ctor_get(v_date_4556_, 26);
v_n_4997_ = lean_ctor_get(v_date_4556_, 27);
v_N_4998_ = lean_ctor_get(v_date_4556_, 28);
v_V_4999_ = lean_ctor_get(v_date_4556_, 29);
v_z_5000_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5001_ = lean_ctor_get(v_date_4556_, 31);
v_v_5002_ = lean_ctor_get(v_date_4556_, 32);
v_O_5003_ = lean_ctor_get(v_date_4556_, 33);
v_X_5004_ = lean_ctor_get(v_date_4556_, 34);
v_x_5005_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5006_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5016_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5016_ == 0)
{
lean_object* v_unused_5017_; 
v_unused_5017_ = lean_ctor_get(v_date_4556_, 9);
lean_dec(v_unused_5017_);
v___x_5008_ = v_date_4556_;
v_isShared_5009_ = v_isSharedCheck_5016_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_Z_5006_);
lean_inc(v_x_5005_);
lean_inc(v_X_5004_);
lean_inc(v_O_5003_);
lean_inc(v_v_5002_);
lean_inc(v_zabbrev_5001_);
lean_inc(v_z_5000_);
lean_inc(v_V_4999_);
lean_inc(v_N_4998_);
lean_inc(v_n_4997_);
lean_inc(v_A_4996_);
lean_inc(v_S_4995_);
lean_inc(v_s_4994_);
lean_inc(v_m_4993_);
lean_inc(v_H_4992_);
lean_inc(v_k_4991_);
lean_inc(v_K_4990_);
lean_inc(v_h_4989_);
lean_inc(v_B_4988_);
lean_inc(v_b_4987_);
lean_inc(v_a_4986_);
lean_inc(v_F_4985_);
lean_inc(v_c_4984_);
lean_inc(v_e_4983_);
lean_inc(v_E_4982_);
lean_inc(v_W_4981_);
lean_inc(v_w_4980_);
lean_inc(v_Q_4979_);
lean_inc(v_d_4978_);
lean_inc(v_L_4977_);
lean_inc(v_M_4976_);
lean_inc(v_D_4975_);
lean_inc(v_Y_4974_);
lean_inc(v_u_4973_);
lean_inc(v_y_4972_);
lean_inc(v_G_4971_);
lean_dec(v_date_4556_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5016_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v___x_5011_; 
if (v_isShared_4970_ == 0)
{
lean_ctor_set_tag(v___x_4969_, 1);
lean_ctor_set(v___x_4969_, 0, v_data_4558_);
v___x_5011_ = v___x_4969_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v_data_4558_);
v___x_5011_ = v_reuseFailAlloc_5015_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
lean_object* v___x_5013_; 
if (v_isShared_5009_ == 0)
{
lean_ctor_set(v___x_5008_, 9, v___x_5011_);
v___x_5013_ = v___x_5008_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_G_4971_);
lean_ctor_set(v_reuseFailAlloc_5014_, 1, v_y_4972_);
lean_ctor_set(v_reuseFailAlloc_5014_, 2, v_u_4973_);
lean_ctor_set(v_reuseFailAlloc_5014_, 3, v_Y_4974_);
lean_ctor_set(v_reuseFailAlloc_5014_, 4, v_D_4975_);
lean_ctor_set(v_reuseFailAlloc_5014_, 5, v_M_4976_);
lean_ctor_set(v_reuseFailAlloc_5014_, 6, v_L_4977_);
lean_ctor_set(v_reuseFailAlloc_5014_, 7, v_d_4978_);
lean_ctor_set(v_reuseFailAlloc_5014_, 8, v_Q_4979_);
lean_ctor_set(v_reuseFailAlloc_5014_, 9, v___x_5011_);
lean_ctor_set(v_reuseFailAlloc_5014_, 10, v_w_4980_);
lean_ctor_set(v_reuseFailAlloc_5014_, 11, v_W_4981_);
lean_ctor_set(v_reuseFailAlloc_5014_, 12, v_E_4982_);
lean_ctor_set(v_reuseFailAlloc_5014_, 13, v_e_4983_);
lean_ctor_set(v_reuseFailAlloc_5014_, 14, v_c_4984_);
lean_ctor_set(v_reuseFailAlloc_5014_, 15, v_F_4985_);
lean_ctor_set(v_reuseFailAlloc_5014_, 16, v_a_4986_);
lean_ctor_set(v_reuseFailAlloc_5014_, 17, v_b_4987_);
lean_ctor_set(v_reuseFailAlloc_5014_, 18, v_B_4988_);
lean_ctor_set(v_reuseFailAlloc_5014_, 19, v_h_4989_);
lean_ctor_set(v_reuseFailAlloc_5014_, 20, v_K_4990_);
lean_ctor_set(v_reuseFailAlloc_5014_, 21, v_k_4991_);
lean_ctor_set(v_reuseFailAlloc_5014_, 22, v_H_4992_);
lean_ctor_set(v_reuseFailAlloc_5014_, 23, v_m_4993_);
lean_ctor_set(v_reuseFailAlloc_5014_, 24, v_s_4994_);
lean_ctor_set(v_reuseFailAlloc_5014_, 25, v_S_4995_);
lean_ctor_set(v_reuseFailAlloc_5014_, 26, v_A_4996_);
lean_ctor_set(v_reuseFailAlloc_5014_, 27, v_n_4997_);
lean_ctor_set(v_reuseFailAlloc_5014_, 28, v_N_4998_);
lean_ctor_set(v_reuseFailAlloc_5014_, 29, v_V_4999_);
lean_ctor_set(v_reuseFailAlloc_5014_, 30, v_z_5000_);
lean_ctor_set(v_reuseFailAlloc_5014_, 31, v_zabbrev_5001_);
lean_ctor_set(v_reuseFailAlloc_5014_, 32, v_v_5002_);
lean_ctor_set(v_reuseFailAlloc_5014_, 33, v_O_5003_);
lean_ctor_set(v_reuseFailAlloc_5014_, 34, v_X_5004_);
lean_ctor_set(v_reuseFailAlloc_5014_, 35, v_x_5005_);
lean_ctor_set(v_reuseFailAlloc_5014_, 36, v_Z_5006_);
v___x_5013_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
return v___x_5013_;
}
}
}
}
}
case 9:
{
lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5070_; 
v_isSharedCheck_5070_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_5070_ == 0)
{
lean_object* v_unused_5071_; 
v_unused_5071_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_5071_);
v___x_5021_ = v_modifier_4557_;
v_isShared_5022_ = v_isSharedCheck_5070_;
goto v_resetjp_5020_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5070_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v_G_5023_; lean_object* v_y_5024_; lean_object* v_u_5025_; lean_object* v_D_5026_; lean_object* v_M_5027_; lean_object* v_L_5028_; lean_object* v_d_5029_; lean_object* v_Q_5030_; lean_object* v_q_5031_; lean_object* v_w_5032_; lean_object* v_W_5033_; lean_object* v_E_5034_; lean_object* v_e_5035_; lean_object* v_c_5036_; lean_object* v_F_5037_; lean_object* v_a_5038_; lean_object* v_b_5039_; lean_object* v_B_5040_; lean_object* v_h_5041_; lean_object* v_K_5042_; lean_object* v_k_5043_; lean_object* v_H_5044_; lean_object* v_m_5045_; lean_object* v_s_5046_; lean_object* v_S_5047_; lean_object* v_A_5048_; lean_object* v_n_5049_; lean_object* v_N_5050_; lean_object* v_V_5051_; lean_object* v_z_5052_; lean_object* v_zabbrev_5053_; lean_object* v_v_5054_; lean_object* v_O_5055_; lean_object* v_X_5056_; lean_object* v_x_5057_; lean_object* v_Z_5058_; lean_object* v___x_5060_; uint8_t v_isShared_5061_; uint8_t v_isSharedCheck_5068_; 
v_G_5023_ = lean_ctor_get(v_date_4556_, 0);
v_y_5024_ = lean_ctor_get(v_date_4556_, 1);
v_u_5025_ = lean_ctor_get(v_date_4556_, 2);
v_D_5026_ = lean_ctor_get(v_date_4556_, 4);
v_M_5027_ = lean_ctor_get(v_date_4556_, 5);
v_L_5028_ = lean_ctor_get(v_date_4556_, 6);
v_d_5029_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5030_ = lean_ctor_get(v_date_4556_, 8);
v_q_5031_ = lean_ctor_get(v_date_4556_, 9);
v_w_5032_ = lean_ctor_get(v_date_4556_, 10);
v_W_5033_ = lean_ctor_get(v_date_4556_, 11);
v_E_5034_ = lean_ctor_get(v_date_4556_, 12);
v_e_5035_ = lean_ctor_get(v_date_4556_, 13);
v_c_5036_ = lean_ctor_get(v_date_4556_, 14);
v_F_5037_ = lean_ctor_get(v_date_4556_, 15);
v_a_5038_ = lean_ctor_get(v_date_4556_, 16);
v_b_5039_ = lean_ctor_get(v_date_4556_, 17);
v_B_5040_ = lean_ctor_get(v_date_4556_, 18);
v_h_5041_ = lean_ctor_get(v_date_4556_, 19);
v_K_5042_ = lean_ctor_get(v_date_4556_, 20);
v_k_5043_ = lean_ctor_get(v_date_4556_, 21);
v_H_5044_ = lean_ctor_get(v_date_4556_, 22);
v_m_5045_ = lean_ctor_get(v_date_4556_, 23);
v_s_5046_ = lean_ctor_get(v_date_4556_, 24);
v_S_5047_ = lean_ctor_get(v_date_4556_, 25);
v_A_5048_ = lean_ctor_get(v_date_4556_, 26);
v_n_5049_ = lean_ctor_get(v_date_4556_, 27);
v_N_5050_ = lean_ctor_get(v_date_4556_, 28);
v_V_5051_ = lean_ctor_get(v_date_4556_, 29);
v_z_5052_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5053_ = lean_ctor_get(v_date_4556_, 31);
v_v_5054_ = lean_ctor_get(v_date_4556_, 32);
v_O_5055_ = lean_ctor_get(v_date_4556_, 33);
v_X_5056_ = lean_ctor_get(v_date_4556_, 34);
v_x_5057_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5058_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5068_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5068_ == 0)
{
lean_object* v_unused_5069_; 
v_unused_5069_ = lean_ctor_get(v_date_4556_, 3);
lean_dec(v_unused_5069_);
v___x_5060_ = v_date_4556_;
v_isShared_5061_ = v_isSharedCheck_5068_;
goto v_resetjp_5059_;
}
else
{
lean_inc(v_Z_5058_);
lean_inc(v_x_5057_);
lean_inc(v_X_5056_);
lean_inc(v_O_5055_);
lean_inc(v_v_5054_);
lean_inc(v_zabbrev_5053_);
lean_inc(v_z_5052_);
lean_inc(v_V_5051_);
lean_inc(v_N_5050_);
lean_inc(v_n_5049_);
lean_inc(v_A_5048_);
lean_inc(v_S_5047_);
lean_inc(v_s_5046_);
lean_inc(v_m_5045_);
lean_inc(v_H_5044_);
lean_inc(v_k_5043_);
lean_inc(v_K_5042_);
lean_inc(v_h_5041_);
lean_inc(v_B_5040_);
lean_inc(v_b_5039_);
lean_inc(v_a_5038_);
lean_inc(v_F_5037_);
lean_inc(v_c_5036_);
lean_inc(v_e_5035_);
lean_inc(v_E_5034_);
lean_inc(v_W_5033_);
lean_inc(v_w_5032_);
lean_inc(v_q_5031_);
lean_inc(v_Q_5030_);
lean_inc(v_d_5029_);
lean_inc(v_L_5028_);
lean_inc(v_M_5027_);
lean_inc(v_D_5026_);
lean_inc(v_u_5025_);
lean_inc(v_y_5024_);
lean_inc(v_G_5023_);
lean_dec(v_date_4556_);
v___x_5060_ = lean_box(0);
v_isShared_5061_ = v_isSharedCheck_5068_;
goto v_resetjp_5059_;
}
v_resetjp_5059_:
{
lean_object* v___x_5063_; 
if (v_isShared_5022_ == 0)
{
lean_ctor_set_tag(v___x_5021_, 1);
lean_ctor_set(v___x_5021_, 0, v_data_4558_);
v___x_5063_ = v___x_5021_;
goto v_reusejp_5062_;
}
else
{
lean_object* v_reuseFailAlloc_5067_; 
v_reuseFailAlloc_5067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5067_, 0, v_data_4558_);
v___x_5063_ = v_reuseFailAlloc_5067_;
goto v_reusejp_5062_;
}
v_reusejp_5062_:
{
lean_object* v___x_5065_; 
if (v_isShared_5061_ == 0)
{
lean_ctor_set(v___x_5060_, 3, v___x_5063_);
v___x_5065_ = v___x_5060_;
goto v_reusejp_5064_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_G_5023_);
lean_ctor_set(v_reuseFailAlloc_5066_, 1, v_y_5024_);
lean_ctor_set(v_reuseFailAlloc_5066_, 2, v_u_5025_);
lean_ctor_set(v_reuseFailAlloc_5066_, 3, v___x_5063_);
lean_ctor_set(v_reuseFailAlloc_5066_, 4, v_D_5026_);
lean_ctor_set(v_reuseFailAlloc_5066_, 5, v_M_5027_);
lean_ctor_set(v_reuseFailAlloc_5066_, 6, v_L_5028_);
lean_ctor_set(v_reuseFailAlloc_5066_, 7, v_d_5029_);
lean_ctor_set(v_reuseFailAlloc_5066_, 8, v_Q_5030_);
lean_ctor_set(v_reuseFailAlloc_5066_, 9, v_q_5031_);
lean_ctor_set(v_reuseFailAlloc_5066_, 10, v_w_5032_);
lean_ctor_set(v_reuseFailAlloc_5066_, 11, v_W_5033_);
lean_ctor_set(v_reuseFailAlloc_5066_, 12, v_E_5034_);
lean_ctor_set(v_reuseFailAlloc_5066_, 13, v_e_5035_);
lean_ctor_set(v_reuseFailAlloc_5066_, 14, v_c_5036_);
lean_ctor_set(v_reuseFailAlloc_5066_, 15, v_F_5037_);
lean_ctor_set(v_reuseFailAlloc_5066_, 16, v_a_5038_);
lean_ctor_set(v_reuseFailAlloc_5066_, 17, v_b_5039_);
lean_ctor_set(v_reuseFailAlloc_5066_, 18, v_B_5040_);
lean_ctor_set(v_reuseFailAlloc_5066_, 19, v_h_5041_);
lean_ctor_set(v_reuseFailAlloc_5066_, 20, v_K_5042_);
lean_ctor_set(v_reuseFailAlloc_5066_, 21, v_k_5043_);
lean_ctor_set(v_reuseFailAlloc_5066_, 22, v_H_5044_);
lean_ctor_set(v_reuseFailAlloc_5066_, 23, v_m_5045_);
lean_ctor_set(v_reuseFailAlloc_5066_, 24, v_s_5046_);
lean_ctor_set(v_reuseFailAlloc_5066_, 25, v_S_5047_);
lean_ctor_set(v_reuseFailAlloc_5066_, 26, v_A_5048_);
lean_ctor_set(v_reuseFailAlloc_5066_, 27, v_n_5049_);
lean_ctor_set(v_reuseFailAlloc_5066_, 28, v_N_5050_);
lean_ctor_set(v_reuseFailAlloc_5066_, 29, v_V_5051_);
lean_ctor_set(v_reuseFailAlloc_5066_, 30, v_z_5052_);
lean_ctor_set(v_reuseFailAlloc_5066_, 31, v_zabbrev_5053_);
lean_ctor_set(v_reuseFailAlloc_5066_, 32, v_v_5054_);
lean_ctor_set(v_reuseFailAlloc_5066_, 33, v_O_5055_);
lean_ctor_set(v_reuseFailAlloc_5066_, 34, v_X_5056_);
lean_ctor_set(v_reuseFailAlloc_5066_, 35, v_x_5057_);
lean_ctor_set(v_reuseFailAlloc_5066_, 36, v_Z_5058_);
v___x_5065_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5064_;
}
v_reusejp_5064_:
{
return v___x_5065_;
}
}
}
}
}
case 10:
{
lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5122_; 
v_isSharedCheck_5122_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_5122_ == 0)
{
lean_object* v_unused_5123_; 
v_unused_5123_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_5123_);
v___x_5073_ = v_modifier_4557_;
v_isShared_5074_ = v_isSharedCheck_5122_;
goto v_resetjp_5072_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5122_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v_G_5075_; lean_object* v_y_5076_; lean_object* v_u_5077_; lean_object* v_Y_5078_; lean_object* v_D_5079_; lean_object* v_M_5080_; lean_object* v_L_5081_; lean_object* v_d_5082_; lean_object* v_Q_5083_; lean_object* v_q_5084_; lean_object* v_W_5085_; lean_object* v_E_5086_; lean_object* v_e_5087_; lean_object* v_c_5088_; lean_object* v_F_5089_; lean_object* v_a_5090_; lean_object* v_b_5091_; lean_object* v_B_5092_; lean_object* v_h_5093_; lean_object* v_K_5094_; lean_object* v_k_5095_; lean_object* v_H_5096_; lean_object* v_m_5097_; lean_object* v_s_5098_; lean_object* v_S_5099_; lean_object* v_A_5100_; lean_object* v_n_5101_; lean_object* v_N_5102_; lean_object* v_V_5103_; lean_object* v_z_5104_; lean_object* v_zabbrev_5105_; lean_object* v_v_5106_; lean_object* v_O_5107_; lean_object* v_X_5108_; lean_object* v_x_5109_; lean_object* v_Z_5110_; lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5120_; 
v_G_5075_ = lean_ctor_get(v_date_4556_, 0);
v_y_5076_ = lean_ctor_get(v_date_4556_, 1);
v_u_5077_ = lean_ctor_get(v_date_4556_, 2);
v_Y_5078_ = lean_ctor_get(v_date_4556_, 3);
v_D_5079_ = lean_ctor_get(v_date_4556_, 4);
v_M_5080_ = lean_ctor_get(v_date_4556_, 5);
v_L_5081_ = lean_ctor_get(v_date_4556_, 6);
v_d_5082_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5083_ = lean_ctor_get(v_date_4556_, 8);
v_q_5084_ = lean_ctor_get(v_date_4556_, 9);
v_W_5085_ = lean_ctor_get(v_date_4556_, 11);
v_E_5086_ = lean_ctor_get(v_date_4556_, 12);
v_e_5087_ = lean_ctor_get(v_date_4556_, 13);
v_c_5088_ = lean_ctor_get(v_date_4556_, 14);
v_F_5089_ = lean_ctor_get(v_date_4556_, 15);
v_a_5090_ = lean_ctor_get(v_date_4556_, 16);
v_b_5091_ = lean_ctor_get(v_date_4556_, 17);
v_B_5092_ = lean_ctor_get(v_date_4556_, 18);
v_h_5093_ = lean_ctor_get(v_date_4556_, 19);
v_K_5094_ = lean_ctor_get(v_date_4556_, 20);
v_k_5095_ = lean_ctor_get(v_date_4556_, 21);
v_H_5096_ = lean_ctor_get(v_date_4556_, 22);
v_m_5097_ = lean_ctor_get(v_date_4556_, 23);
v_s_5098_ = lean_ctor_get(v_date_4556_, 24);
v_S_5099_ = lean_ctor_get(v_date_4556_, 25);
v_A_5100_ = lean_ctor_get(v_date_4556_, 26);
v_n_5101_ = lean_ctor_get(v_date_4556_, 27);
v_N_5102_ = lean_ctor_get(v_date_4556_, 28);
v_V_5103_ = lean_ctor_get(v_date_4556_, 29);
v_z_5104_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5105_ = lean_ctor_get(v_date_4556_, 31);
v_v_5106_ = lean_ctor_get(v_date_4556_, 32);
v_O_5107_ = lean_ctor_get(v_date_4556_, 33);
v_X_5108_ = lean_ctor_get(v_date_4556_, 34);
v_x_5109_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5110_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5120_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5120_ == 0)
{
lean_object* v_unused_5121_; 
v_unused_5121_ = lean_ctor_get(v_date_4556_, 10);
lean_dec(v_unused_5121_);
v___x_5112_ = v_date_4556_;
v_isShared_5113_ = v_isSharedCheck_5120_;
goto v_resetjp_5111_;
}
else
{
lean_inc(v_Z_5110_);
lean_inc(v_x_5109_);
lean_inc(v_X_5108_);
lean_inc(v_O_5107_);
lean_inc(v_v_5106_);
lean_inc(v_zabbrev_5105_);
lean_inc(v_z_5104_);
lean_inc(v_V_5103_);
lean_inc(v_N_5102_);
lean_inc(v_n_5101_);
lean_inc(v_A_5100_);
lean_inc(v_S_5099_);
lean_inc(v_s_5098_);
lean_inc(v_m_5097_);
lean_inc(v_H_5096_);
lean_inc(v_k_5095_);
lean_inc(v_K_5094_);
lean_inc(v_h_5093_);
lean_inc(v_B_5092_);
lean_inc(v_b_5091_);
lean_inc(v_a_5090_);
lean_inc(v_F_5089_);
lean_inc(v_c_5088_);
lean_inc(v_e_5087_);
lean_inc(v_E_5086_);
lean_inc(v_W_5085_);
lean_inc(v_q_5084_);
lean_inc(v_Q_5083_);
lean_inc(v_d_5082_);
lean_inc(v_L_5081_);
lean_inc(v_M_5080_);
lean_inc(v_D_5079_);
lean_inc(v_Y_5078_);
lean_inc(v_u_5077_);
lean_inc(v_y_5076_);
lean_inc(v_G_5075_);
lean_dec(v_date_4556_);
v___x_5112_ = lean_box(0);
v_isShared_5113_ = v_isSharedCheck_5120_;
goto v_resetjp_5111_;
}
v_resetjp_5111_:
{
lean_object* v___x_5115_; 
if (v_isShared_5074_ == 0)
{
lean_ctor_set_tag(v___x_5073_, 1);
lean_ctor_set(v___x_5073_, 0, v_data_4558_);
v___x_5115_ = v___x_5073_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v_data_4558_);
v___x_5115_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
lean_object* v___x_5117_; 
if (v_isShared_5113_ == 0)
{
lean_ctor_set(v___x_5112_, 10, v___x_5115_);
v___x_5117_ = v___x_5112_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_G_5075_);
lean_ctor_set(v_reuseFailAlloc_5118_, 1, v_y_5076_);
lean_ctor_set(v_reuseFailAlloc_5118_, 2, v_u_5077_);
lean_ctor_set(v_reuseFailAlloc_5118_, 3, v_Y_5078_);
lean_ctor_set(v_reuseFailAlloc_5118_, 4, v_D_5079_);
lean_ctor_set(v_reuseFailAlloc_5118_, 5, v_M_5080_);
lean_ctor_set(v_reuseFailAlloc_5118_, 6, v_L_5081_);
lean_ctor_set(v_reuseFailAlloc_5118_, 7, v_d_5082_);
lean_ctor_set(v_reuseFailAlloc_5118_, 8, v_Q_5083_);
lean_ctor_set(v_reuseFailAlloc_5118_, 9, v_q_5084_);
lean_ctor_set(v_reuseFailAlloc_5118_, 10, v___x_5115_);
lean_ctor_set(v_reuseFailAlloc_5118_, 11, v_W_5085_);
lean_ctor_set(v_reuseFailAlloc_5118_, 12, v_E_5086_);
lean_ctor_set(v_reuseFailAlloc_5118_, 13, v_e_5087_);
lean_ctor_set(v_reuseFailAlloc_5118_, 14, v_c_5088_);
lean_ctor_set(v_reuseFailAlloc_5118_, 15, v_F_5089_);
lean_ctor_set(v_reuseFailAlloc_5118_, 16, v_a_5090_);
lean_ctor_set(v_reuseFailAlloc_5118_, 17, v_b_5091_);
lean_ctor_set(v_reuseFailAlloc_5118_, 18, v_B_5092_);
lean_ctor_set(v_reuseFailAlloc_5118_, 19, v_h_5093_);
lean_ctor_set(v_reuseFailAlloc_5118_, 20, v_K_5094_);
lean_ctor_set(v_reuseFailAlloc_5118_, 21, v_k_5095_);
lean_ctor_set(v_reuseFailAlloc_5118_, 22, v_H_5096_);
lean_ctor_set(v_reuseFailAlloc_5118_, 23, v_m_5097_);
lean_ctor_set(v_reuseFailAlloc_5118_, 24, v_s_5098_);
lean_ctor_set(v_reuseFailAlloc_5118_, 25, v_S_5099_);
lean_ctor_set(v_reuseFailAlloc_5118_, 26, v_A_5100_);
lean_ctor_set(v_reuseFailAlloc_5118_, 27, v_n_5101_);
lean_ctor_set(v_reuseFailAlloc_5118_, 28, v_N_5102_);
lean_ctor_set(v_reuseFailAlloc_5118_, 29, v_V_5103_);
lean_ctor_set(v_reuseFailAlloc_5118_, 30, v_z_5104_);
lean_ctor_set(v_reuseFailAlloc_5118_, 31, v_zabbrev_5105_);
lean_ctor_set(v_reuseFailAlloc_5118_, 32, v_v_5106_);
lean_ctor_set(v_reuseFailAlloc_5118_, 33, v_O_5107_);
lean_ctor_set(v_reuseFailAlloc_5118_, 34, v_X_5108_);
lean_ctor_set(v_reuseFailAlloc_5118_, 35, v_x_5109_);
lean_ctor_set(v_reuseFailAlloc_5118_, 36, v_Z_5110_);
v___x_5117_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
return v___x_5117_;
}
}
}
}
}
case 11:
{
lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5174_; 
v_isSharedCheck_5174_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_5174_ == 0)
{
lean_object* v_unused_5175_; 
v_unused_5175_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_5175_);
v___x_5125_ = v_modifier_4557_;
v_isShared_5126_ = v_isSharedCheck_5174_;
goto v_resetjp_5124_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5174_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v_G_5127_; lean_object* v_y_5128_; lean_object* v_u_5129_; lean_object* v_Y_5130_; lean_object* v_D_5131_; lean_object* v_M_5132_; lean_object* v_L_5133_; lean_object* v_d_5134_; lean_object* v_Q_5135_; lean_object* v_q_5136_; lean_object* v_w_5137_; lean_object* v_E_5138_; lean_object* v_e_5139_; lean_object* v_c_5140_; lean_object* v_F_5141_; lean_object* v_a_5142_; lean_object* v_b_5143_; lean_object* v_B_5144_; lean_object* v_h_5145_; lean_object* v_K_5146_; lean_object* v_k_5147_; lean_object* v_H_5148_; lean_object* v_m_5149_; lean_object* v_s_5150_; lean_object* v_S_5151_; lean_object* v_A_5152_; lean_object* v_n_5153_; lean_object* v_N_5154_; lean_object* v_V_5155_; lean_object* v_z_5156_; lean_object* v_zabbrev_5157_; lean_object* v_v_5158_; lean_object* v_O_5159_; lean_object* v_X_5160_; lean_object* v_x_5161_; lean_object* v_Z_5162_; lean_object* v___x_5164_; uint8_t v_isShared_5165_; uint8_t v_isSharedCheck_5172_; 
v_G_5127_ = lean_ctor_get(v_date_4556_, 0);
v_y_5128_ = lean_ctor_get(v_date_4556_, 1);
v_u_5129_ = lean_ctor_get(v_date_4556_, 2);
v_Y_5130_ = lean_ctor_get(v_date_4556_, 3);
v_D_5131_ = lean_ctor_get(v_date_4556_, 4);
v_M_5132_ = lean_ctor_get(v_date_4556_, 5);
v_L_5133_ = lean_ctor_get(v_date_4556_, 6);
v_d_5134_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5135_ = lean_ctor_get(v_date_4556_, 8);
v_q_5136_ = lean_ctor_get(v_date_4556_, 9);
v_w_5137_ = lean_ctor_get(v_date_4556_, 10);
v_E_5138_ = lean_ctor_get(v_date_4556_, 12);
v_e_5139_ = lean_ctor_get(v_date_4556_, 13);
v_c_5140_ = lean_ctor_get(v_date_4556_, 14);
v_F_5141_ = lean_ctor_get(v_date_4556_, 15);
v_a_5142_ = lean_ctor_get(v_date_4556_, 16);
v_b_5143_ = lean_ctor_get(v_date_4556_, 17);
v_B_5144_ = lean_ctor_get(v_date_4556_, 18);
v_h_5145_ = lean_ctor_get(v_date_4556_, 19);
v_K_5146_ = lean_ctor_get(v_date_4556_, 20);
v_k_5147_ = lean_ctor_get(v_date_4556_, 21);
v_H_5148_ = lean_ctor_get(v_date_4556_, 22);
v_m_5149_ = lean_ctor_get(v_date_4556_, 23);
v_s_5150_ = lean_ctor_get(v_date_4556_, 24);
v_S_5151_ = lean_ctor_get(v_date_4556_, 25);
v_A_5152_ = lean_ctor_get(v_date_4556_, 26);
v_n_5153_ = lean_ctor_get(v_date_4556_, 27);
v_N_5154_ = lean_ctor_get(v_date_4556_, 28);
v_V_5155_ = lean_ctor_get(v_date_4556_, 29);
v_z_5156_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5157_ = lean_ctor_get(v_date_4556_, 31);
v_v_5158_ = lean_ctor_get(v_date_4556_, 32);
v_O_5159_ = lean_ctor_get(v_date_4556_, 33);
v_X_5160_ = lean_ctor_get(v_date_4556_, 34);
v_x_5161_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5162_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5172_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5172_ == 0)
{
lean_object* v_unused_5173_; 
v_unused_5173_ = lean_ctor_get(v_date_4556_, 11);
lean_dec(v_unused_5173_);
v___x_5164_ = v_date_4556_;
v_isShared_5165_ = v_isSharedCheck_5172_;
goto v_resetjp_5163_;
}
else
{
lean_inc(v_Z_5162_);
lean_inc(v_x_5161_);
lean_inc(v_X_5160_);
lean_inc(v_O_5159_);
lean_inc(v_v_5158_);
lean_inc(v_zabbrev_5157_);
lean_inc(v_z_5156_);
lean_inc(v_V_5155_);
lean_inc(v_N_5154_);
lean_inc(v_n_5153_);
lean_inc(v_A_5152_);
lean_inc(v_S_5151_);
lean_inc(v_s_5150_);
lean_inc(v_m_5149_);
lean_inc(v_H_5148_);
lean_inc(v_k_5147_);
lean_inc(v_K_5146_);
lean_inc(v_h_5145_);
lean_inc(v_B_5144_);
lean_inc(v_b_5143_);
lean_inc(v_a_5142_);
lean_inc(v_F_5141_);
lean_inc(v_c_5140_);
lean_inc(v_e_5139_);
lean_inc(v_E_5138_);
lean_inc(v_w_5137_);
lean_inc(v_q_5136_);
lean_inc(v_Q_5135_);
lean_inc(v_d_5134_);
lean_inc(v_L_5133_);
lean_inc(v_M_5132_);
lean_inc(v_D_5131_);
lean_inc(v_Y_5130_);
lean_inc(v_u_5129_);
lean_inc(v_y_5128_);
lean_inc(v_G_5127_);
lean_dec(v_date_4556_);
v___x_5164_ = lean_box(0);
v_isShared_5165_ = v_isSharedCheck_5172_;
goto v_resetjp_5163_;
}
v_resetjp_5163_:
{
lean_object* v___x_5167_; 
if (v_isShared_5126_ == 0)
{
lean_ctor_set_tag(v___x_5125_, 1);
lean_ctor_set(v___x_5125_, 0, v_data_4558_);
v___x_5167_ = v___x_5125_;
goto v_reusejp_5166_;
}
else
{
lean_object* v_reuseFailAlloc_5171_; 
v_reuseFailAlloc_5171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_data_4558_);
v___x_5167_ = v_reuseFailAlloc_5171_;
goto v_reusejp_5166_;
}
v_reusejp_5166_:
{
lean_object* v___x_5169_; 
if (v_isShared_5165_ == 0)
{
lean_ctor_set(v___x_5164_, 11, v___x_5167_);
v___x_5169_ = v___x_5164_;
goto v_reusejp_5168_;
}
else
{
lean_object* v_reuseFailAlloc_5170_; 
v_reuseFailAlloc_5170_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_G_5127_);
lean_ctor_set(v_reuseFailAlloc_5170_, 1, v_y_5128_);
lean_ctor_set(v_reuseFailAlloc_5170_, 2, v_u_5129_);
lean_ctor_set(v_reuseFailAlloc_5170_, 3, v_Y_5130_);
lean_ctor_set(v_reuseFailAlloc_5170_, 4, v_D_5131_);
lean_ctor_set(v_reuseFailAlloc_5170_, 5, v_M_5132_);
lean_ctor_set(v_reuseFailAlloc_5170_, 6, v_L_5133_);
lean_ctor_set(v_reuseFailAlloc_5170_, 7, v_d_5134_);
lean_ctor_set(v_reuseFailAlloc_5170_, 8, v_Q_5135_);
lean_ctor_set(v_reuseFailAlloc_5170_, 9, v_q_5136_);
lean_ctor_set(v_reuseFailAlloc_5170_, 10, v_w_5137_);
lean_ctor_set(v_reuseFailAlloc_5170_, 11, v___x_5167_);
lean_ctor_set(v_reuseFailAlloc_5170_, 12, v_E_5138_);
lean_ctor_set(v_reuseFailAlloc_5170_, 13, v_e_5139_);
lean_ctor_set(v_reuseFailAlloc_5170_, 14, v_c_5140_);
lean_ctor_set(v_reuseFailAlloc_5170_, 15, v_F_5141_);
lean_ctor_set(v_reuseFailAlloc_5170_, 16, v_a_5142_);
lean_ctor_set(v_reuseFailAlloc_5170_, 17, v_b_5143_);
lean_ctor_set(v_reuseFailAlloc_5170_, 18, v_B_5144_);
lean_ctor_set(v_reuseFailAlloc_5170_, 19, v_h_5145_);
lean_ctor_set(v_reuseFailAlloc_5170_, 20, v_K_5146_);
lean_ctor_set(v_reuseFailAlloc_5170_, 21, v_k_5147_);
lean_ctor_set(v_reuseFailAlloc_5170_, 22, v_H_5148_);
lean_ctor_set(v_reuseFailAlloc_5170_, 23, v_m_5149_);
lean_ctor_set(v_reuseFailAlloc_5170_, 24, v_s_5150_);
lean_ctor_set(v_reuseFailAlloc_5170_, 25, v_S_5151_);
lean_ctor_set(v_reuseFailAlloc_5170_, 26, v_A_5152_);
lean_ctor_set(v_reuseFailAlloc_5170_, 27, v_n_5153_);
lean_ctor_set(v_reuseFailAlloc_5170_, 28, v_N_5154_);
lean_ctor_set(v_reuseFailAlloc_5170_, 29, v_V_5155_);
lean_ctor_set(v_reuseFailAlloc_5170_, 30, v_z_5156_);
lean_ctor_set(v_reuseFailAlloc_5170_, 31, v_zabbrev_5157_);
lean_ctor_set(v_reuseFailAlloc_5170_, 32, v_v_5158_);
lean_ctor_set(v_reuseFailAlloc_5170_, 33, v_O_5159_);
lean_ctor_set(v_reuseFailAlloc_5170_, 34, v_X_5160_);
lean_ctor_set(v_reuseFailAlloc_5170_, 35, v_x_5161_);
lean_ctor_set(v_reuseFailAlloc_5170_, 36, v_Z_5162_);
v___x_5169_ = v_reuseFailAlloc_5170_;
goto v_reusejp_5168_;
}
v_reusejp_5168_:
{
return v___x_5169_;
}
}
}
}
}
case 12:
{
lean_object* v_G_5176_; lean_object* v_y_5177_; lean_object* v_u_5178_; lean_object* v_Y_5179_; lean_object* v_D_5180_; lean_object* v_M_5181_; lean_object* v_L_5182_; lean_object* v_d_5183_; lean_object* v_Q_5184_; lean_object* v_q_5185_; lean_object* v_w_5186_; lean_object* v_W_5187_; lean_object* v_e_5188_; lean_object* v_c_5189_; lean_object* v_F_5190_; lean_object* v_a_5191_; lean_object* v_b_5192_; lean_object* v_B_5193_; lean_object* v_h_5194_; lean_object* v_K_5195_; lean_object* v_k_5196_; lean_object* v_H_5197_; lean_object* v_m_5198_; lean_object* v_s_5199_; lean_object* v_S_5200_; lean_object* v_A_5201_; lean_object* v_n_5202_; lean_object* v_N_5203_; lean_object* v_V_5204_; lean_object* v_z_5205_; lean_object* v_zabbrev_5206_; lean_object* v_v_5207_; lean_object* v_O_5208_; lean_object* v_X_5209_; lean_object* v_x_5210_; lean_object* v_Z_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5219_; 
lean_dec_ref_known(v_modifier_4557_, 0);
v_G_5176_ = lean_ctor_get(v_date_4556_, 0);
v_y_5177_ = lean_ctor_get(v_date_4556_, 1);
v_u_5178_ = lean_ctor_get(v_date_4556_, 2);
v_Y_5179_ = lean_ctor_get(v_date_4556_, 3);
v_D_5180_ = lean_ctor_get(v_date_4556_, 4);
v_M_5181_ = lean_ctor_get(v_date_4556_, 5);
v_L_5182_ = lean_ctor_get(v_date_4556_, 6);
v_d_5183_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5184_ = lean_ctor_get(v_date_4556_, 8);
v_q_5185_ = lean_ctor_get(v_date_4556_, 9);
v_w_5186_ = lean_ctor_get(v_date_4556_, 10);
v_W_5187_ = lean_ctor_get(v_date_4556_, 11);
v_e_5188_ = lean_ctor_get(v_date_4556_, 13);
v_c_5189_ = lean_ctor_get(v_date_4556_, 14);
v_F_5190_ = lean_ctor_get(v_date_4556_, 15);
v_a_5191_ = lean_ctor_get(v_date_4556_, 16);
v_b_5192_ = lean_ctor_get(v_date_4556_, 17);
v_B_5193_ = lean_ctor_get(v_date_4556_, 18);
v_h_5194_ = lean_ctor_get(v_date_4556_, 19);
v_K_5195_ = lean_ctor_get(v_date_4556_, 20);
v_k_5196_ = lean_ctor_get(v_date_4556_, 21);
v_H_5197_ = lean_ctor_get(v_date_4556_, 22);
v_m_5198_ = lean_ctor_get(v_date_4556_, 23);
v_s_5199_ = lean_ctor_get(v_date_4556_, 24);
v_S_5200_ = lean_ctor_get(v_date_4556_, 25);
v_A_5201_ = lean_ctor_get(v_date_4556_, 26);
v_n_5202_ = lean_ctor_get(v_date_4556_, 27);
v_N_5203_ = lean_ctor_get(v_date_4556_, 28);
v_V_5204_ = lean_ctor_get(v_date_4556_, 29);
v_z_5205_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5206_ = lean_ctor_get(v_date_4556_, 31);
v_v_5207_ = lean_ctor_get(v_date_4556_, 32);
v_O_5208_ = lean_ctor_get(v_date_4556_, 33);
v_X_5209_ = lean_ctor_get(v_date_4556_, 34);
v_x_5210_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5211_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5219_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5219_ == 0)
{
lean_object* v_unused_5220_; 
v_unused_5220_ = lean_ctor_get(v_date_4556_, 12);
lean_dec(v_unused_5220_);
v___x_5213_ = v_date_4556_;
v_isShared_5214_ = v_isSharedCheck_5219_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_Z_5211_);
lean_inc(v_x_5210_);
lean_inc(v_X_5209_);
lean_inc(v_O_5208_);
lean_inc(v_v_5207_);
lean_inc(v_zabbrev_5206_);
lean_inc(v_z_5205_);
lean_inc(v_V_5204_);
lean_inc(v_N_5203_);
lean_inc(v_n_5202_);
lean_inc(v_A_5201_);
lean_inc(v_S_5200_);
lean_inc(v_s_5199_);
lean_inc(v_m_5198_);
lean_inc(v_H_5197_);
lean_inc(v_k_5196_);
lean_inc(v_K_5195_);
lean_inc(v_h_5194_);
lean_inc(v_B_5193_);
lean_inc(v_b_5192_);
lean_inc(v_a_5191_);
lean_inc(v_F_5190_);
lean_inc(v_c_5189_);
lean_inc(v_e_5188_);
lean_inc(v_W_5187_);
lean_inc(v_w_5186_);
lean_inc(v_q_5185_);
lean_inc(v_Q_5184_);
lean_inc(v_d_5183_);
lean_inc(v_L_5182_);
lean_inc(v_M_5181_);
lean_inc(v_D_5180_);
lean_inc(v_Y_5179_);
lean_inc(v_u_5178_);
lean_inc(v_y_5177_);
lean_inc(v_G_5176_);
lean_dec(v_date_4556_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5219_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v___x_5215_; lean_object* v___x_5217_; 
v___x_5215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5215_, 0, v_data_4558_);
if (v_isShared_5214_ == 0)
{
lean_ctor_set(v___x_5213_, 12, v___x_5215_);
v___x_5217_ = v___x_5213_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v_G_5176_);
lean_ctor_set(v_reuseFailAlloc_5218_, 1, v_y_5177_);
lean_ctor_set(v_reuseFailAlloc_5218_, 2, v_u_5178_);
lean_ctor_set(v_reuseFailAlloc_5218_, 3, v_Y_5179_);
lean_ctor_set(v_reuseFailAlloc_5218_, 4, v_D_5180_);
lean_ctor_set(v_reuseFailAlloc_5218_, 5, v_M_5181_);
lean_ctor_set(v_reuseFailAlloc_5218_, 6, v_L_5182_);
lean_ctor_set(v_reuseFailAlloc_5218_, 7, v_d_5183_);
lean_ctor_set(v_reuseFailAlloc_5218_, 8, v_Q_5184_);
lean_ctor_set(v_reuseFailAlloc_5218_, 9, v_q_5185_);
lean_ctor_set(v_reuseFailAlloc_5218_, 10, v_w_5186_);
lean_ctor_set(v_reuseFailAlloc_5218_, 11, v_W_5187_);
lean_ctor_set(v_reuseFailAlloc_5218_, 12, v___x_5215_);
lean_ctor_set(v_reuseFailAlloc_5218_, 13, v_e_5188_);
lean_ctor_set(v_reuseFailAlloc_5218_, 14, v_c_5189_);
lean_ctor_set(v_reuseFailAlloc_5218_, 15, v_F_5190_);
lean_ctor_set(v_reuseFailAlloc_5218_, 16, v_a_5191_);
lean_ctor_set(v_reuseFailAlloc_5218_, 17, v_b_5192_);
lean_ctor_set(v_reuseFailAlloc_5218_, 18, v_B_5193_);
lean_ctor_set(v_reuseFailAlloc_5218_, 19, v_h_5194_);
lean_ctor_set(v_reuseFailAlloc_5218_, 20, v_K_5195_);
lean_ctor_set(v_reuseFailAlloc_5218_, 21, v_k_5196_);
lean_ctor_set(v_reuseFailAlloc_5218_, 22, v_H_5197_);
lean_ctor_set(v_reuseFailAlloc_5218_, 23, v_m_5198_);
lean_ctor_set(v_reuseFailAlloc_5218_, 24, v_s_5199_);
lean_ctor_set(v_reuseFailAlloc_5218_, 25, v_S_5200_);
lean_ctor_set(v_reuseFailAlloc_5218_, 26, v_A_5201_);
lean_ctor_set(v_reuseFailAlloc_5218_, 27, v_n_5202_);
lean_ctor_set(v_reuseFailAlloc_5218_, 28, v_N_5203_);
lean_ctor_set(v_reuseFailAlloc_5218_, 29, v_V_5204_);
lean_ctor_set(v_reuseFailAlloc_5218_, 30, v_z_5205_);
lean_ctor_set(v_reuseFailAlloc_5218_, 31, v_zabbrev_5206_);
lean_ctor_set(v_reuseFailAlloc_5218_, 32, v_v_5207_);
lean_ctor_set(v_reuseFailAlloc_5218_, 33, v_O_5208_);
lean_ctor_set(v_reuseFailAlloc_5218_, 34, v_X_5209_);
lean_ctor_set(v_reuseFailAlloc_5218_, 35, v_x_5210_);
lean_ctor_set(v_reuseFailAlloc_5218_, 36, v_Z_5211_);
v___x_5217_ = v_reuseFailAlloc_5218_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
return v___x_5217_;
}
}
}
case 13:
{
lean_object* v___x_5222_; uint8_t v_isShared_5223_; uint8_t v_isSharedCheck_5271_; 
v_isSharedCheck_5271_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_5271_ == 0)
{
lean_object* v_unused_5272_; 
v_unused_5272_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_5272_);
v___x_5222_ = v_modifier_4557_;
v_isShared_5223_ = v_isSharedCheck_5271_;
goto v_resetjp_5221_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_5222_ = lean_box(0);
v_isShared_5223_ = v_isSharedCheck_5271_;
goto v_resetjp_5221_;
}
v_resetjp_5221_:
{
lean_object* v_G_5224_; lean_object* v_y_5225_; lean_object* v_u_5226_; lean_object* v_Y_5227_; lean_object* v_D_5228_; lean_object* v_M_5229_; lean_object* v_L_5230_; lean_object* v_d_5231_; lean_object* v_Q_5232_; lean_object* v_q_5233_; lean_object* v_w_5234_; lean_object* v_W_5235_; lean_object* v_E_5236_; lean_object* v_c_5237_; lean_object* v_F_5238_; lean_object* v_a_5239_; lean_object* v_b_5240_; lean_object* v_B_5241_; lean_object* v_h_5242_; lean_object* v_K_5243_; lean_object* v_k_5244_; lean_object* v_H_5245_; lean_object* v_m_5246_; lean_object* v_s_5247_; lean_object* v_S_5248_; lean_object* v_A_5249_; lean_object* v_n_5250_; lean_object* v_N_5251_; lean_object* v_V_5252_; lean_object* v_z_5253_; lean_object* v_zabbrev_5254_; lean_object* v_v_5255_; lean_object* v_O_5256_; lean_object* v_X_5257_; lean_object* v_x_5258_; lean_object* v_Z_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5269_; 
v_G_5224_ = lean_ctor_get(v_date_4556_, 0);
v_y_5225_ = lean_ctor_get(v_date_4556_, 1);
v_u_5226_ = lean_ctor_get(v_date_4556_, 2);
v_Y_5227_ = lean_ctor_get(v_date_4556_, 3);
v_D_5228_ = lean_ctor_get(v_date_4556_, 4);
v_M_5229_ = lean_ctor_get(v_date_4556_, 5);
v_L_5230_ = lean_ctor_get(v_date_4556_, 6);
v_d_5231_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5232_ = lean_ctor_get(v_date_4556_, 8);
v_q_5233_ = lean_ctor_get(v_date_4556_, 9);
v_w_5234_ = lean_ctor_get(v_date_4556_, 10);
v_W_5235_ = lean_ctor_get(v_date_4556_, 11);
v_E_5236_ = lean_ctor_get(v_date_4556_, 12);
v_c_5237_ = lean_ctor_get(v_date_4556_, 14);
v_F_5238_ = lean_ctor_get(v_date_4556_, 15);
v_a_5239_ = lean_ctor_get(v_date_4556_, 16);
v_b_5240_ = lean_ctor_get(v_date_4556_, 17);
v_B_5241_ = lean_ctor_get(v_date_4556_, 18);
v_h_5242_ = lean_ctor_get(v_date_4556_, 19);
v_K_5243_ = lean_ctor_get(v_date_4556_, 20);
v_k_5244_ = lean_ctor_get(v_date_4556_, 21);
v_H_5245_ = lean_ctor_get(v_date_4556_, 22);
v_m_5246_ = lean_ctor_get(v_date_4556_, 23);
v_s_5247_ = lean_ctor_get(v_date_4556_, 24);
v_S_5248_ = lean_ctor_get(v_date_4556_, 25);
v_A_5249_ = lean_ctor_get(v_date_4556_, 26);
v_n_5250_ = lean_ctor_get(v_date_4556_, 27);
v_N_5251_ = lean_ctor_get(v_date_4556_, 28);
v_V_5252_ = lean_ctor_get(v_date_4556_, 29);
v_z_5253_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5254_ = lean_ctor_get(v_date_4556_, 31);
v_v_5255_ = lean_ctor_get(v_date_4556_, 32);
v_O_5256_ = lean_ctor_get(v_date_4556_, 33);
v_X_5257_ = lean_ctor_get(v_date_4556_, 34);
v_x_5258_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5259_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5269_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5269_ == 0)
{
lean_object* v_unused_5270_; 
v_unused_5270_ = lean_ctor_get(v_date_4556_, 13);
lean_dec(v_unused_5270_);
v___x_5261_ = v_date_4556_;
v_isShared_5262_ = v_isSharedCheck_5269_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_Z_5259_);
lean_inc(v_x_5258_);
lean_inc(v_X_5257_);
lean_inc(v_O_5256_);
lean_inc(v_v_5255_);
lean_inc(v_zabbrev_5254_);
lean_inc(v_z_5253_);
lean_inc(v_V_5252_);
lean_inc(v_N_5251_);
lean_inc(v_n_5250_);
lean_inc(v_A_5249_);
lean_inc(v_S_5248_);
lean_inc(v_s_5247_);
lean_inc(v_m_5246_);
lean_inc(v_H_5245_);
lean_inc(v_k_5244_);
lean_inc(v_K_5243_);
lean_inc(v_h_5242_);
lean_inc(v_B_5241_);
lean_inc(v_b_5240_);
lean_inc(v_a_5239_);
lean_inc(v_F_5238_);
lean_inc(v_c_5237_);
lean_inc(v_E_5236_);
lean_inc(v_W_5235_);
lean_inc(v_w_5234_);
lean_inc(v_q_5233_);
lean_inc(v_Q_5232_);
lean_inc(v_d_5231_);
lean_inc(v_L_5230_);
lean_inc(v_M_5229_);
lean_inc(v_D_5228_);
lean_inc(v_Y_5227_);
lean_inc(v_u_5226_);
lean_inc(v_y_5225_);
lean_inc(v_G_5224_);
lean_dec(v_date_4556_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5269_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v___x_5264_; 
if (v_isShared_5223_ == 0)
{
lean_ctor_set_tag(v___x_5222_, 1);
lean_ctor_set(v___x_5222_, 0, v_data_4558_);
v___x_5264_ = v___x_5222_;
goto v_reusejp_5263_;
}
else
{
lean_object* v_reuseFailAlloc_5268_; 
v_reuseFailAlloc_5268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5268_, 0, v_data_4558_);
v___x_5264_ = v_reuseFailAlloc_5268_;
goto v_reusejp_5263_;
}
v_reusejp_5263_:
{
lean_object* v___x_5266_; 
if (v_isShared_5262_ == 0)
{
lean_ctor_set(v___x_5261_, 13, v___x_5264_);
v___x_5266_ = v___x_5261_;
goto v_reusejp_5265_;
}
else
{
lean_object* v_reuseFailAlloc_5267_; 
v_reuseFailAlloc_5267_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5267_, 0, v_G_5224_);
lean_ctor_set(v_reuseFailAlloc_5267_, 1, v_y_5225_);
lean_ctor_set(v_reuseFailAlloc_5267_, 2, v_u_5226_);
lean_ctor_set(v_reuseFailAlloc_5267_, 3, v_Y_5227_);
lean_ctor_set(v_reuseFailAlloc_5267_, 4, v_D_5228_);
lean_ctor_set(v_reuseFailAlloc_5267_, 5, v_M_5229_);
lean_ctor_set(v_reuseFailAlloc_5267_, 6, v_L_5230_);
lean_ctor_set(v_reuseFailAlloc_5267_, 7, v_d_5231_);
lean_ctor_set(v_reuseFailAlloc_5267_, 8, v_Q_5232_);
lean_ctor_set(v_reuseFailAlloc_5267_, 9, v_q_5233_);
lean_ctor_set(v_reuseFailAlloc_5267_, 10, v_w_5234_);
lean_ctor_set(v_reuseFailAlloc_5267_, 11, v_W_5235_);
lean_ctor_set(v_reuseFailAlloc_5267_, 12, v_E_5236_);
lean_ctor_set(v_reuseFailAlloc_5267_, 13, v___x_5264_);
lean_ctor_set(v_reuseFailAlloc_5267_, 14, v_c_5237_);
lean_ctor_set(v_reuseFailAlloc_5267_, 15, v_F_5238_);
lean_ctor_set(v_reuseFailAlloc_5267_, 16, v_a_5239_);
lean_ctor_set(v_reuseFailAlloc_5267_, 17, v_b_5240_);
lean_ctor_set(v_reuseFailAlloc_5267_, 18, v_B_5241_);
lean_ctor_set(v_reuseFailAlloc_5267_, 19, v_h_5242_);
lean_ctor_set(v_reuseFailAlloc_5267_, 20, v_K_5243_);
lean_ctor_set(v_reuseFailAlloc_5267_, 21, v_k_5244_);
lean_ctor_set(v_reuseFailAlloc_5267_, 22, v_H_5245_);
lean_ctor_set(v_reuseFailAlloc_5267_, 23, v_m_5246_);
lean_ctor_set(v_reuseFailAlloc_5267_, 24, v_s_5247_);
lean_ctor_set(v_reuseFailAlloc_5267_, 25, v_S_5248_);
lean_ctor_set(v_reuseFailAlloc_5267_, 26, v_A_5249_);
lean_ctor_set(v_reuseFailAlloc_5267_, 27, v_n_5250_);
lean_ctor_set(v_reuseFailAlloc_5267_, 28, v_N_5251_);
lean_ctor_set(v_reuseFailAlloc_5267_, 29, v_V_5252_);
lean_ctor_set(v_reuseFailAlloc_5267_, 30, v_z_5253_);
lean_ctor_set(v_reuseFailAlloc_5267_, 31, v_zabbrev_5254_);
lean_ctor_set(v_reuseFailAlloc_5267_, 32, v_v_5255_);
lean_ctor_set(v_reuseFailAlloc_5267_, 33, v_O_5256_);
lean_ctor_set(v_reuseFailAlloc_5267_, 34, v_X_5257_);
lean_ctor_set(v_reuseFailAlloc_5267_, 35, v_x_5258_);
lean_ctor_set(v_reuseFailAlloc_5267_, 36, v_Z_5259_);
v___x_5266_ = v_reuseFailAlloc_5267_;
goto v_reusejp_5265_;
}
v_reusejp_5265_:
{
return v___x_5266_;
}
}
}
}
}
case 14:
{
lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5323_; 
v_isSharedCheck_5323_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_5323_ == 0)
{
lean_object* v_unused_5324_; 
v_unused_5324_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_5324_);
v___x_5274_ = v_modifier_4557_;
v_isShared_5275_ = v_isSharedCheck_5323_;
goto v_resetjp_5273_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5323_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
lean_object* v_G_5276_; lean_object* v_y_5277_; lean_object* v_u_5278_; lean_object* v_Y_5279_; lean_object* v_D_5280_; lean_object* v_M_5281_; lean_object* v_L_5282_; lean_object* v_d_5283_; lean_object* v_Q_5284_; lean_object* v_q_5285_; lean_object* v_w_5286_; lean_object* v_W_5287_; lean_object* v_E_5288_; lean_object* v_e_5289_; lean_object* v_F_5290_; lean_object* v_a_5291_; lean_object* v_b_5292_; lean_object* v_B_5293_; lean_object* v_h_5294_; lean_object* v_K_5295_; lean_object* v_k_5296_; lean_object* v_H_5297_; lean_object* v_m_5298_; lean_object* v_s_5299_; lean_object* v_S_5300_; lean_object* v_A_5301_; lean_object* v_n_5302_; lean_object* v_N_5303_; lean_object* v_V_5304_; lean_object* v_z_5305_; lean_object* v_zabbrev_5306_; lean_object* v_v_5307_; lean_object* v_O_5308_; lean_object* v_X_5309_; lean_object* v_x_5310_; lean_object* v_Z_5311_; lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5321_; 
v_G_5276_ = lean_ctor_get(v_date_4556_, 0);
v_y_5277_ = lean_ctor_get(v_date_4556_, 1);
v_u_5278_ = lean_ctor_get(v_date_4556_, 2);
v_Y_5279_ = lean_ctor_get(v_date_4556_, 3);
v_D_5280_ = lean_ctor_get(v_date_4556_, 4);
v_M_5281_ = lean_ctor_get(v_date_4556_, 5);
v_L_5282_ = lean_ctor_get(v_date_4556_, 6);
v_d_5283_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5284_ = lean_ctor_get(v_date_4556_, 8);
v_q_5285_ = lean_ctor_get(v_date_4556_, 9);
v_w_5286_ = lean_ctor_get(v_date_4556_, 10);
v_W_5287_ = lean_ctor_get(v_date_4556_, 11);
v_E_5288_ = lean_ctor_get(v_date_4556_, 12);
v_e_5289_ = lean_ctor_get(v_date_4556_, 13);
v_F_5290_ = lean_ctor_get(v_date_4556_, 15);
v_a_5291_ = lean_ctor_get(v_date_4556_, 16);
v_b_5292_ = lean_ctor_get(v_date_4556_, 17);
v_B_5293_ = lean_ctor_get(v_date_4556_, 18);
v_h_5294_ = lean_ctor_get(v_date_4556_, 19);
v_K_5295_ = lean_ctor_get(v_date_4556_, 20);
v_k_5296_ = lean_ctor_get(v_date_4556_, 21);
v_H_5297_ = lean_ctor_get(v_date_4556_, 22);
v_m_5298_ = lean_ctor_get(v_date_4556_, 23);
v_s_5299_ = lean_ctor_get(v_date_4556_, 24);
v_S_5300_ = lean_ctor_get(v_date_4556_, 25);
v_A_5301_ = lean_ctor_get(v_date_4556_, 26);
v_n_5302_ = lean_ctor_get(v_date_4556_, 27);
v_N_5303_ = lean_ctor_get(v_date_4556_, 28);
v_V_5304_ = lean_ctor_get(v_date_4556_, 29);
v_z_5305_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5306_ = lean_ctor_get(v_date_4556_, 31);
v_v_5307_ = lean_ctor_get(v_date_4556_, 32);
v_O_5308_ = lean_ctor_get(v_date_4556_, 33);
v_X_5309_ = lean_ctor_get(v_date_4556_, 34);
v_x_5310_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5311_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5321_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5321_ == 0)
{
lean_object* v_unused_5322_; 
v_unused_5322_ = lean_ctor_get(v_date_4556_, 14);
lean_dec(v_unused_5322_);
v___x_5313_ = v_date_4556_;
v_isShared_5314_ = v_isSharedCheck_5321_;
goto v_resetjp_5312_;
}
else
{
lean_inc(v_Z_5311_);
lean_inc(v_x_5310_);
lean_inc(v_X_5309_);
lean_inc(v_O_5308_);
lean_inc(v_v_5307_);
lean_inc(v_zabbrev_5306_);
lean_inc(v_z_5305_);
lean_inc(v_V_5304_);
lean_inc(v_N_5303_);
lean_inc(v_n_5302_);
lean_inc(v_A_5301_);
lean_inc(v_S_5300_);
lean_inc(v_s_5299_);
lean_inc(v_m_5298_);
lean_inc(v_H_5297_);
lean_inc(v_k_5296_);
lean_inc(v_K_5295_);
lean_inc(v_h_5294_);
lean_inc(v_B_5293_);
lean_inc(v_b_5292_);
lean_inc(v_a_5291_);
lean_inc(v_F_5290_);
lean_inc(v_e_5289_);
lean_inc(v_E_5288_);
lean_inc(v_W_5287_);
lean_inc(v_w_5286_);
lean_inc(v_q_5285_);
lean_inc(v_Q_5284_);
lean_inc(v_d_5283_);
lean_inc(v_L_5282_);
lean_inc(v_M_5281_);
lean_inc(v_D_5280_);
lean_inc(v_Y_5279_);
lean_inc(v_u_5278_);
lean_inc(v_y_5277_);
lean_inc(v_G_5276_);
lean_dec(v_date_4556_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5321_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
lean_object* v___x_5316_; 
if (v_isShared_5275_ == 0)
{
lean_ctor_set_tag(v___x_5274_, 1);
lean_ctor_set(v___x_5274_, 0, v_data_4558_);
v___x_5316_ = v___x_5274_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5320_; 
v_reuseFailAlloc_5320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5320_, 0, v_data_4558_);
v___x_5316_ = v_reuseFailAlloc_5320_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
lean_object* v___x_5318_; 
if (v_isShared_5314_ == 0)
{
lean_ctor_set(v___x_5313_, 14, v___x_5316_);
v___x_5318_ = v___x_5313_;
goto v_reusejp_5317_;
}
else
{
lean_object* v_reuseFailAlloc_5319_; 
v_reuseFailAlloc_5319_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5319_, 0, v_G_5276_);
lean_ctor_set(v_reuseFailAlloc_5319_, 1, v_y_5277_);
lean_ctor_set(v_reuseFailAlloc_5319_, 2, v_u_5278_);
lean_ctor_set(v_reuseFailAlloc_5319_, 3, v_Y_5279_);
lean_ctor_set(v_reuseFailAlloc_5319_, 4, v_D_5280_);
lean_ctor_set(v_reuseFailAlloc_5319_, 5, v_M_5281_);
lean_ctor_set(v_reuseFailAlloc_5319_, 6, v_L_5282_);
lean_ctor_set(v_reuseFailAlloc_5319_, 7, v_d_5283_);
lean_ctor_set(v_reuseFailAlloc_5319_, 8, v_Q_5284_);
lean_ctor_set(v_reuseFailAlloc_5319_, 9, v_q_5285_);
lean_ctor_set(v_reuseFailAlloc_5319_, 10, v_w_5286_);
lean_ctor_set(v_reuseFailAlloc_5319_, 11, v_W_5287_);
lean_ctor_set(v_reuseFailAlloc_5319_, 12, v_E_5288_);
lean_ctor_set(v_reuseFailAlloc_5319_, 13, v_e_5289_);
lean_ctor_set(v_reuseFailAlloc_5319_, 14, v___x_5316_);
lean_ctor_set(v_reuseFailAlloc_5319_, 15, v_F_5290_);
lean_ctor_set(v_reuseFailAlloc_5319_, 16, v_a_5291_);
lean_ctor_set(v_reuseFailAlloc_5319_, 17, v_b_5292_);
lean_ctor_set(v_reuseFailAlloc_5319_, 18, v_B_5293_);
lean_ctor_set(v_reuseFailAlloc_5319_, 19, v_h_5294_);
lean_ctor_set(v_reuseFailAlloc_5319_, 20, v_K_5295_);
lean_ctor_set(v_reuseFailAlloc_5319_, 21, v_k_5296_);
lean_ctor_set(v_reuseFailAlloc_5319_, 22, v_H_5297_);
lean_ctor_set(v_reuseFailAlloc_5319_, 23, v_m_5298_);
lean_ctor_set(v_reuseFailAlloc_5319_, 24, v_s_5299_);
lean_ctor_set(v_reuseFailAlloc_5319_, 25, v_S_5300_);
lean_ctor_set(v_reuseFailAlloc_5319_, 26, v_A_5301_);
lean_ctor_set(v_reuseFailAlloc_5319_, 27, v_n_5302_);
lean_ctor_set(v_reuseFailAlloc_5319_, 28, v_N_5303_);
lean_ctor_set(v_reuseFailAlloc_5319_, 29, v_V_5304_);
lean_ctor_set(v_reuseFailAlloc_5319_, 30, v_z_5305_);
lean_ctor_set(v_reuseFailAlloc_5319_, 31, v_zabbrev_5306_);
lean_ctor_set(v_reuseFailAlloc_5319_, 32, v_v_5307_);
lean_ctor_set(v_reuseFailAlloc_5319_, 33, v_O_5308_);
lean_ctor_set(v_reuseFailAlloc_5319_, 34, v_X_5309_);
lean_ctor_set(v_reuseFailAlloc_5319_, 35, v_x_5310_);
lean_ctor_set(v_reuseFailAlloc_5319_, 36, v_Z_5311_);
v___x_5318_ = v_reuseFailAlloc_5319_;
goto v_reusejp_5317_;
}
v_reusejp_5317_:
{
return v___x_5318_;
}
}
}
}
}
case 15:
{
lean_object* v___x_5326_; uint8_t v_isShared_5327_; uint8_t v_isSharedCheck_5375_; 
v_isSharedCheck_5375_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_5375_ == 0)
{
lean_object* v_unused_5376_; 
v_unused_5376_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_5376_);
v___x_5326_ = v_modifier_4557_;
v_isShared_5327_ = v_isSharedCheck_5375_;
goto v_resetjp_5325_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_5326_ = lean_box(0);
v_isShared_5327_ = v_isSharedCheck_5375_;
goto v_resetjp_5325_;
}
v_resetjp_5325_:
{
lean_object* v_G_5328_; lean_object* v_y_5329_; lean_object* v_u_5330_; lean_object* v_Y_5331_; lean_object* v_D_5332_; lean_object* v_M_5333_; lean_object* v_L_5334_; lean_object* v_d_5335_; lean_object* v_Q_5336_; lean_object* v_q_5337_; lean_object* v_w_5338_; lean_object* v_W_5339_; lean_object* v_E_5340_; lean_object* v_e_5341_; lean_object* v_c_5342_; lean_object* v_a_5343_; lean_object* v_b_5344_; lean_object* v_B_5345_; lean_object* v_h_5346_; lean_object* v_K_5347_; lean_object* v_k_5348_; lean_object* v_H_5349_; lean_object* v_m_5350_; lean_object* v_s_5351_; lean_object* v_S_5352_; lean_object* v_A_5353_; lean_object* v_n_5354_; lean_object* v_N_5355_; lean_object* v_V_5356_; lean_object* v_z_5357_; lean_object* v_zabbrev_5358_; lean_object* v_v_5359_; lean_object* v_O_5360_; lean_object* v_X_5361_; lean_object* v_x_5362_; lean_object* v_Z_5363_; lean_object* v___x_5365_; uint8_t v_isShared_5366_; uint8_t v_isSharedCheck_5373_; 
v_G_5328_ = lean_ctor_get(v_date_4556_, 0);
v_y_5329_ = lean_ctor_get(v_date_4556_, 1);
v_u_5330_ = lean_ctor_get(v_date_4556_, 2);
v_Y_5331_ = lean_ctor_get(v_date_4556_, 3);
v_D_5332_ = lean_ctor_get(v_date_4556_, 4);
v_M_5333_ = lean_ctor_get(v_date_4556_, 5);
v_L_5334_ = lean_ctor_get(v_date_4556_, 6);
v_d_5335_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5336_ = lean_ctor_get(v_date_4556_, 8);
v_q_5337_ = lean_ctor_get(v_date_4556_, 9);
v_w_5338_ = lean_ctor_get(v_date_4556_, 10);
v_W_5339_ = lean_ctor_get(v_date_4556_, 11);
v_E_5340_ = lean_ctor_get(v_date_4556_, 12);
v_e_5341_ = lean_ctor_get(v_date_4556_, 13);
v_c_5342_ = lean_ctor_get(v_date_4556_, 14);
v_a_5343_ = lean_ctor_get(v_date_4556_, 16);
v_b_5344_ = lean_ctor_get(v_date_4556_, 17);
v_B_5345_ = lean_ctor_get(v_date_4556_, 18);
v_h_5346_ = lean_ctor_get(v_date_4556_, 19);
v_K_5347_ = lean_ctor_get(v_date_4556_, 20);
v_k_5348_ = lean_ctor_get(v_date_4556_, 21);
v_H_5349_ = lean_ctor_get(v_date_4556_, 22);
v_m_5350_ = lean_ctor_get(v_date_4556_, 23);
v_s_5351_ = lean_ctor_get(v_date_4556_, 24);
v_S_5352_ = lean_ctor_get(v_date_4556_, 25);
v_A_5353_ = lean_ctor_get(v_date_4556_, 26);
v_n_5354_ = lean_ctor_get(v_date_4556_, 27);
v_N_5355_ = lean_ctor_get(v_date_4556_, 28);
v_V_5356_ = lean_ctor_get(v_date_4556_, 29);
v_z_5357_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5358_ = lean_ctor_get(v_date_4556_, 31);
v_v_5359_ = lean_ctor_get(v_date_4556_, 32);
v_O_5360_ = lean_ctor_get(v_date_4556_, 33);
v_X_5361_ = lean_ctor_get(v_date_4556_, 34);
v_x_5362_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5363_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5373_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5373_ == 0)
{
lean_object* v_unused_5374_; 
v_unused_5374_ = lean_ctor_get(v_date_4556_, 15);
lean_dec(v_unused_5374_);
v___x_5365_ = v_date_4556_;
v_isShared_5366_ = v_isSharedCheck_5373_;
goto v_resetjp_5364_;
}
else
{
lean_inc(v_Z_5363_);
lean_inc(v_x_5362_);
lean_inc(v_X_5361_);
lean_inc(v_O_5360_);
lean_inc(v_v_5359_);
lean_inc(v_zabbrev_5358_);
lean_inc(v_z_5357_);
lean_inc(v_V_5356_);
lean_inc(v_N_5355_);
lean_inc(v_n_5354_);
lean_inc(v_A_5353_);
lean_inc(v_S_5352_);
lean_inc(v_s_5351_);
lean_inc(v_m_5350_);
lean_inc(v_H_5349_);
lean_inc(v_k_5348_);
lean_inc(v_K_5347_);
lean_inc(v_h_5346_);
lean_inc(v_B_5345_);
lean_inc(v_b_5344_);
lean_inc(v_a_5343_);
lean_inc(v_c_5342_);
lean_inc(v_e_5341_);
lean_inc(v_E_5340_);
lean_inc(v_W_5339_);
lean_inc(v_w_5338_);
lean_inc(v_q_5337_);
lean_inc(v_Q_5336_);
lean_inc(v_d_5335_);
lean_inc(v_L_5334_);
lean_inc(v_M_5333_);
lean_inc(v_D_5332_);
lean_inc(v_Y_5331_);
lean_inc(v_u_5330_);
lean_inc(v_y_5329_);
lean_inc(v_G_5328_);
lean_dec(v_date_4556_);
v___x_5365_ = lean_box(0);
v_isShared_5366_ = v_isSharedCheck_5373_;
goto v_resetjp_5364_;
}
v_resetjp_5364_:
{
lean_object* v___x_5368_; 
if (v_isShared_5327_ == 0)
{
lean_ctor_set_tag(v___x_5326_, 1);
lean_ctor_set(v___x_5326_, 0, v_data_4558_);
v___x_5368_ = v___x_5326_;
goto v_reusejp_5367_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v_data_4558_);
v___x_5368_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5367_;
}
v_reusejp_5367_:
{
lean_object* v___x_5370_; 
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 15, v___x_5368_);
v___x_5370_ = v___x_5365_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v_G_5328_);
lean_ctor_set(v_reuseFailAlloc_5371_, 1, v_y_5329_);
lean_ctor_set(v_reuseFailAlloc_5371_, 2, v_u_5330_);
lean_ctor_set(v_reuseFailAlloc_5371_, 3, v_Y_5331_);
lean_ctor_set(v_reuseFailAlloc_5371_, 4, v_D_5332_);
lean_ctor_set(v_reuseFailAlloc_5371_, 5, v_M_5333_);
lean_ctor_set(v_reuseFailAlloc_5371_, 6, v_L_5334_);
lean_ctor_set(v_reuseFailAlloc_5371_, 7, v_d_5335_);
lean_ctor_set(v_reuseFailAlloc_5371_, 8, v_Q_5336_);
lean_ctor_set(v_reuseFailAlloc_5371_, 9, v_q_5337_);
lean_ctor_set(v_reuseFailAlloc_5371_, 10, v_w_5338_);
lean_ctor_set(v_reuseFailAlloc_5371_, 11, v_W_5339_);
lean_ctor_set(v_reuseFailAlloc_5371_, 12, v_E_5340_);
lean_ctor_set(v_reuseFailAlloc_5371_, 13, v_e_5341_);
lean_ctor_set(v_reuseFailAlloc_5371_, 14, v_c_5342_);
lean_ctor_set(v_reuseFailAlloc_5371_, 15, v___x_5368_);
lean_ctor_set(v_reuseFailAlloc_5371_, 16, v_a_5343_);
lean_ctor_set(v_reuseFailAlloc_5371_, 17, v_b_5344_);
lean_ctor_set(v_reuseFailAlloc_5371_, 18, v_B_5345_);
lean_ctor_set(v_reuseFailAlloc_5371_, 19, v_h_5346_);
lean_ctor_set(v_reuseFailAlloc_5371_, 20, v_K_5347_);
lean_ctor_set(v_reuseFailAlloc_5371_, 21, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5371_, 22, v_H_5349_);
lean_ctor_set(v_reuseFailAlloc_5371_, 23, v_m_5350_);
lean_ctor_set(v_reuseFailAlloc_5371_, 24, v_s_5351_);
lean_ctor_set(v_reuseFailAlloc_5371_, 25, v_S_5352_);
lean_ctor_set(v_reuseFailAlloc_5371_, 26, v_A_5353_);
lean_ctor_set(v_reuseFailAlloc_5371_, 27, v_n_5354_);
lean_ctor_set(v_reuseFailAlloc_5371_, 28, v_N_5355_);
lean_ctor_set(v_reuseFailAlloc_5371_, 29, v_V_5356_);
lean_ctor_set(v_reuseFailAlloc_5371_, 30, v_z_5357_);
lean_ctor_set(v_reuseFailAlloc_5371_, 31, v_zabbrev_5358_);
lean_ctor_set(v_reuseFailAlloc_5371_, 32, v_v_5359_);
lean_ctor_set(v_reuseFailAlloc_5371_, 33, v_O_5360_);
lean_ctor_set(v_reuseFailAlloc_5371_, 34, v_X_5361_);
lean_ctor_set(v_reuseFailAlloc_5371_, 35, v_x_5362_);
lean_ctor_set(v_reuseFailAlloc_5371_, 36, v_Z_5363_);
v___x_5370_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
return v___x_5370_;
}
}
}
}
}
case 16:
{
lean_object* v_G_5377_; lean_object* v_y_5378_; lean_object* v_u_5379_; lean_object* v_Y_5380_; lean_object* v_D_5381_; lean_object* v_M_5382_; lean_object* v_L_5383_; lean_object* v_d_5384_; lean_object* v_Q_5385_; lean_object* v_q_5386_; lean_object* v_w_5387_; lean_object* v_W_5388_; lean_object* v_E_5389_; lean_object* v_e_5390_; lean_object* v_c_5391_; lean_object* v_F_5392_; lean_object* v_b_5393_; lean_object* v_B_5394_; lean_object* v_h_5395_; lean_object* v_K_5396_; lean_object* v_k_5397_; lean_object* v_H_5398_; lean_object* v_m_5399_; lean_object* v_s_5400_; lean_object* v_S_5401_; lean_object* v_A_5402_; lean_object* v_n_5403_; lean_object* v_N_5404_; lean_object* v_V_5405_; lean_object* v_z_5406_; lean_object* v_zabbrev_5407_; lean_object* v_v_5408_; lean_object* v_O_5409_; lean_object* v_X_5410_; lean_object* v_x_5411_; lean_object* v_Z_5412_; lean_object* v___x_5414_; uint8_t v_isShared_5415_; uint8_t v_isSharedCheck_5420_; 
lean_dec_ref_known(v_modifier_4557_, 0);
v_G_5377_ = lean_ctor_get(v_date_4556_, 0);
v_y_5378_ = lean_ctor_get(v_date_4556_, 1);
v_u_5379_ = lean_ctor_get(v_date_4556_, 2);
v_Y_5380_ = lean_ctor_get(v_date_4556_, 3);
v_D_5381_ = lean_ctor_get(v_date_4556_, 4);
v_M_5382_ = lean_ctor_get(v_date_4556_, 5);
v_L_5383_ = lean_ctor_get(v_date_4556_, 6);
v_d_5384_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5385_ = lean_ctor_get(v_date_4556_, 8);
v_q_5386_ = lean_ctor_get(v_date_4556_, 9);
v_w_5387_ = lean_ctor_get(v_date_4556_, 10);
v_W_5388_ = lean_ctor_get(v_date_4556_, 11);
v_E_5389_ = lean_ctor_get(v_date_4556_, 12);
v_e_5390_ = lean_ctor_get(v_date_4556_, 13);
v_c_5391_ = lean_ctor_get(v_date_4556_, 14);
v_F_5392_ = lean_ctor_get(v_date_4556_, 15);
v_b_5393_ = lean_ctor_get(v_date_4556_, 17);
v_B_5394_ = lean_ctor_get(v_date_4556_, 18);
v_h_5395_ = lean_ctor_get(v_date_4556_, 19);
v_K_5396_ = lean_ctor_get(v_date_4556_, 20);
v_k_5397_ = lean_ctor_get(v_date_4556_, 21);
v_H_5398_ = lean_ctor_get(v_date_4556_, 22);
v_m_5399_ = lean_ctor_get(v_date_4556_, 23);
v_s_5400_ = lean_ctor_get(v_date_4556_, 24);
v_S_5401_ = lean_ctor_get(v_date_4556_, 25);
v_A_5402_ = lean_ctor_get(v_date_4556_, 26);
v_n_5403_ = lean_ctor_get(v_date_4556_, 27);
v_N_5404_ = lean_ctor_get(v_date_4556_, 28);
v_V_5405_ = lean_ctor_get(v_date_4556_, 29);
v_z_5406_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5407_ = lean_ctor_get(v_date_4556_, 31);
v_v_5408_ = lean_ctor_get(v_date_4556_, 32);
v_O_5409_ = lean_ctor_get(v_date_4556_, 33);
v_X_5410_ = lean_ctor_get(v_date_4556_, 34);
v_x_5411_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5412_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5420_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5420_ == 0)
{
lean_object* v_unused_5421_; 
v_unused_5421_ = lean_ctor_get(v_date_4556_, 16);
lean_dec(v_unused_5421_);
v___x_5414_ = v_date_4556_;
v_isShared_5415_ = v_isSharedCheck_5420_;
goto v_resetjp_5413_;
}
else
{
lean_inc(v_Z_5412_);
lean_inc(v_x_5411_);
lean_inc(v_X_5410_);
lean_inc(v_O_5409_);
lean_inc(v_v_5408_);
lean_inc(v_zabbrev_5407_);
lean_inc(v_z_5406_);
lean_inc(v_V_5405_);
lean_inc(v_N_5404_);
lean_inc(v_n_5403_);
lean_inc(v_A_5402_);
lean_inc(v_S_5401_);
lean_inc(v_s_5400_);
lean_inc(v_m_5399_);
lean_inc(v_H_5398_);
lean_inc(v_k_5397_);
lean_inc(v_K_5396_);
lean_inc(v_h_5395_);
lean_inc(v_B_5394_);
lean_inc(v_b_5393_);
lean_inc(v_F_5392_);
lean_inc(v_c_5391_);
lean_inc(v_e_5390_);
lean_inc(v_E_5389_);
lean_inc(v_W_5388_);
lean_inc(v_w_5387_);
lean_inc(v_q_5386_);
lean_inc(v_Q_5385_);
lean_inc(v_d_5384_);
lean_inc(v_L_5383_);
lean_inc(v_M_5382_);
lean_inc(v_D_5381_);
lean_inc(v_Y_5380_);
lean_inc(v_u_5379_);
lean_inc(v_y_5378_);
lean_inc(v_G_5377_);
lean_dec(v_date_4556_);
v___x_5414_ = lean_box(0);
v_isShared_5415_ = v_isSharedCheck_5420_;
goto v_resetjp_5413_;
}
v_resetjp_5413_:
{
lean_object* v___x_5416_; lean_object* v___x_5418_; 
v___x_5416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5416_, 0, v_data_4558_);
if (v_isShared_5415_ == 0)
{
lean_ctor_set(v___x_5414_, 16, v___x_5416_);
v___x_5418_ = v___x_5414_;
goto v_reusejp_5417_;
}
else
{
lean_object* v_reuseFailAlloc_5419_; 
v_reuseFailAlloc_5419_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5419_, 0, v_G_5377_);
lean_ctor_set(v_reuseFailAlloc_5419_, 1, v_y_5378_);
lean_ctor_set(v_reuseFailAlloc_5419_, 2, v_u_5379_);
lean_ctor_set(v_reuseFailAlloc_5419_, 3, v_Y_5380_);
lean_ctor_set(v_reuseFailAlloc_5419_, 4, v_D_5381_);
lean_ctor_set(v_reuseFailAlloc_5419_, 5, v_M_5382_);
lean_ctor_set(v_reuseFailAlloc_5419_, 6, v_L_5383_);
lean_ctor_set(v_reuseFailAlloc_5419_, 7, v_d_5384_);
lean_ctor_set(v_reuseFailAlloc_5419_, 8, v_Q_5385_);
lean_ctor_set(v_reuseFailAlloc_5419_, 9, v_q_5386_);
lean_ctor_set(v_reuseFailAlloc_5419_, 10, v_w_5387_);
lean_ctor_set(v_reuseFailAlloc_5419_, 11, v_W_5388_);
lean_ctor_set(v_reuseFailAlloc_5419_, 12, v_E_5389_);
lean_ctor_set(v_reuseFailAlloc_5419_, 13, v_e_5390_);
lean_ctor_set(v_reuseFailAlloc_5419_, 14, v_c_5391_);
lean_ctor_set(v_reuseFailAlloc_5419_, 15, v_F_5392_);
lean_ctor_set(v_reuseFailAlloc_5419_, 16, v___x_5416_);
lean_ctor_set(v_reuseFailAlloc_5419_, 17, v_b_5393_);
lean_ctor_set(v_reuseFailAlloc_5419_, 18, v_B_5394_);
lean_ctor_set(v_reuseFailAlloc_5419_, 19, v_h_5395_);
lean_ctor_set(v_reuseFailAlloc_5419_, 20, v_K_5396_);
lean_ctor_set(v_reuseFailAlloc_5419_, 21, v_k_5397_);
lean_ctor_set(v_reuseFailAlloc_5419_, 22, v_H_5398_);
lean_ctor_set(v_reuseFailAlloc_5419_, 23, v_m_5399_);
lean_ctor_set(v_reuseFailAlloc_5419_, 24, v_s_5400_);
lean_ctor_set(v_reuseFailAlloc_5419_, 25, v_S_5401_);
lean_ctor_set(v_reuseFailAlloc_5419_, 26, v_A_5402_);
lean_ctor_set(v_reuseFailAlloc_5419_, 27, v_n_5403_);
lean_ctor_set(v_reuseFailAlloc_5419_, 28, v_N_5404_);
lean_ctor_set(v_reuseFailAlloc_5419_, 29, v_V_5405_);
lean_ctor_set(v_reuseFailAlloc_5419_, 30, v_z_5406_);
lean_ctor_set(v_reuseFailAlloc_5419_, 31, v_zabbrev_5407_);
lean_ctor_set(v_reuseFailAlloc_5419_, 32, v_v_5408_);
lean_ctor_set(v_reuseFailAlloc_5419_, 33, v_O_5409_);
lean_ctor_set(v_reuseFailAlloc_5419_, 34, v_X_5410_);
lean_ctor_set(v_reuseFailAlloc_5419_, 35, v_x_5411_);
lean_ctor_set(v_reuseFailAlloc_5419_, 36, v_Z_5412_);
v___x_5418_ = v_reuseFailAlloc_5419_;
goto v_reusejp_5417_;
}
v_reusejp_5417_:
{
return v___x_5418_;
}
}
}
case 17:
{
lean_object* v_G_5422_; lean_object* v_y_5423_; lean_object* v_u_5424_; lean_object* v_Y_5425_; lean_object* v_D_5426_; lean_object* v_M_5427_; lean_object* v_L_5428_; lean_object* v_d_5429_; lean_object* v_Q_5430_; lean_object* v_q_5431_; lean_object* v_w_5432_; lean_object* v_W_5433_; lean_object* v_E_5434_; lean_object* v_e_5435_; lean_object* v_c_5436_; lean_object* v_F_5437_; lean_object* v_a_5438_; lean_object* v_B_5439_; lean_object* v_h_5440_; lean_object* v_K_5441_; lean_object* v_k_5442_; lean_object* v_H_5443_; lean_object* v_m_5444_; lean_object* v_s_5445_; lean_object* v_S_5446_; lean_object* v_A_5447_; lean_object* v_n_5448_; lean_object* v_N_5449_; lean_object* v_V_5450_; lean_object* v_z_5451_; lean_object* v_zabbrev_5452_; lean_object* v_v_5453_; lean_object* v_O_5454_; lean_object* v_X_5455_; lean_object* v_x_5456_; lean_object* v_Z_5457_; lean_object* v___x_5459_; uint8_t v_isShared_5460_; uint8_t v_isSharedCheck_5465_; 
lean_dec_ref_known(v_modifier_4557_, 0);
v_G_5422_ = lean_ctor_get(v_date_4556_, 0);
v_y_5423_ = lean_ctor_get(v_date_4556_, 1);
v_u_5424_ = lean_ctor_get(v_date_4556_, 2);
v_Y_5425_ = lean_ctor_get(v_date_4556_, 3);
v_D_5426_ = lean_ctor_get(v_date_4556_, 4);
v_M_5427_ = lean_ctor_get(v_date_4556_, 5);
v_L_5428_ = lean_ctor_get(v_date_4556_, 6);
v_d_5429_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5430_ = lean_ctor_get(v_date_4556_, 8);
v_q_5431_ = lean_ctor_get(v_date_4556_, 9);
v_w_5432_ = lean_ctor_get(v_date_4556_, 10);
v_W_5433_ = lean_ctor_get(v_date_4556_, 11);
v_E_5434_ = lean_ctor_get(v_date_4556_, 12);
v_e_5435_ = lean_ctor_get(v_date_4556_, 13);
v_c_5436_ = lean_ctor_get(v_date_4556_, 14);
v_F_5437_ = lean_ctor_get(v_date_4556_, 15);
v_a_5438_ = lean_ctor_get(v_date_4556_, 16);
v_B_5439_ = lean_ctor_get(v_date_4556_, 18);
v_h_5440_ = lean_ctor_get(v_date_4556_, 19);
v_K_5441_ = lean_ctor_get(v_date_4556_, 20);
v_k_5442_ = lean_ctor_get(v_date_4556_, 21);
v_H_5443_ = lean_ctor_get(v_date_4556_, 22);
v_m_5444_ = lean_ctor_get(v_date_4556_, 23);
v_s_5445_ = lean_ctor_get(v_date_4556_, 24);
v_S_5446_ = lean_ctor_get(v_date_4556_, 25);
v_A_5447_ = lean_ctor_get(v_date_4556_, 26);
v_n_5448_ = lean_ctor_get(v_date_4556_, 27);
v_N_5449_ = lean_ctor_get(v_date_4556_, 28);
v_V_5450_ = lean_ctor_get(v_date_4556_, 29);
v_z_5451_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5452_ = lean_ctor_get(v_date_4556_, 31);
v_v_5453_ = lean_ctor_get(v_date_4556_, 32);
v_O_5454_ = lean_ctor_get(v_date_4556_, 33);
v_X_5455_ = lean_ctor_get(v_date_4556_, 34);
v_x_5456_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5457_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5465_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5465_ == 0)
{
lean_object* v_unused_5466_; 
v_unused_5466_ = lean_ctor_get(v_date_4556_, 17);
lean_dec(v_unused_5466_);
v___x_5459_ = v_date_4556_;
v_isShared_5460_ = v_isSharedCheck_5465_;
goto v_resetjp_5458_;
}
else
{
lean_inc(v_Z_5457_);
lean_inc(v_x_5456_);
lean_inc(v_X_5455_);
lean_inc(v_O_5454_);
lean_inc(v_v_5453_);
lean_inc(v_zabbrev_5452_);
lean_inc(v_z_5451_);
lean_inc(v_V_5450_);
lean_inc(v_N_5449_);
lean_inc(v_n_5448_);
lean_inc(v_A_5447_);
lean_inc(v_S_5446_);
lean_inc(v_s_5445_);
lean_inc(v_m_5444_);
lean_inc(v_H_5443_);
lean_inc(v_k_5442_);
lean_inc(v_K_5441_);
lean_inc(v_h_5440_);
lean_inc(v_B_5439_);
lean_inc(v_a_5438_);
lean_inc(v_F_5437_);
lean_inc(v_c_5436_);
lean_inc(v_e_5435_);
lean_inc(v_E_5434_);
lean_inc(v_W_5433_);
lean_inc(v_w_5432_);
lean_inc(v_q_5431_);
lean_inc(v_Q_5430_);
lean_inc(v_d_5429_);
lean_inc(v_L_5428_);
lean_inc(v_M_5427_);
lean_inc(v_D_5426_);
lean_inc(v_Y_5425_);
lean_inc(v_u_5424_);
lean_inc(v_y_5423_);
lean_inc(v_G_5422_);
lean_dec(v_date_4556_);
v___x_5459_ = lean_box(0);
v_isShared_5460_ = v_isSharedCheck_5465_;
goto v_resetjp_5458_;
}
v_resetjp_5458_:
{
lean_object* v___x_5461_; lean_object* v___x_5463_; 
v___x_5461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5461_, 0, v_data_4558_);
if (v_isShared_5460_ == 0)
{
lean_ctor_set(v___x_5459_, 17, v___x_5461_);
v___x_5463_ = v___x_5459_;
goto v_reusejp_5462_;
}
else
{
lean_object* v_reuseFailAlloc_5464_; 
v_reuseFailAlloc_5464_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5464_, 0, v_G_5422_);
lean_ctor_set(v_reuseFailAlloc_5464_, 1, v_y_5423_);
lean_ctor_set(v_reuseFailAlloc_5464_, 2, v_u_5424_);
lean_ctor_set(v_reuseFailAlloc_5464_, 3, v_Y_5425_);
lean_ctor_set(v_reuseFailAlloc_5464_, 4, v_D_5426_);
lean_ctor_set(v_reuseFailAlloc_5464_, 5, v_M_5427_);
lean_ctor_set(v_reuseFailAlloc_5464_, 6, v_L_5428_);
lean_ctor_set(v_reuseFailAlloc_5464_, 7, v_d_5429_);
lean_ctor_set(v_reuseFailAlloc_5464_, 8, v_Q_5430_);
lean_ctor_set(v_reuseFailAlloc_5464_, 9, v_q_5431_);
lean_ctor_set(v_reuseFailAlloc_5464_, 10, v_w_5432_);
lean_ctor_set(v_reuseFailAlloc_5464_, 11, v_W_5433_);
lean_ctor_set(v_reuseFailAlloc_5464_, 12, v_E_5434_);
lean_ctor_set(v_reuseFailAlloc_5464_, 13, v_e_5435_);
lean_ctor_set(v_reuseFailAlloc_5464_, 14, v_c_5436_);
lean_ctor_set(v_reuseFailAlloc_5464_, 15, v_F_5437_);
lean_ctor_set(v_reuseFailAlloc_5464_, 16, v_a_5438_);
lean_ctor_set(v_reuseFailAlloc_5464_, 17, v___x_5461_);
lean_ctor_set(v_reuseFailAlloc_5464_, 18, v_B_5439_);
lean_ctor_set(v_reuseFailAlloc_5464_, 19, v_h_5440_);
lean_ctor_set(v_reuseFailAlloc_5464_, 20, v_K_5441_);
lean_ctor_set(v_reuseFailAlloc_5464_, 21, v_k_5442_);
lean_ctor_set(v_reuseFailAlloc_5464_, 22, v_H_5443_);
lean_ctor_set(v_reuseFailAlloc_5464_, 23, v_m_5444_);
lean_ctor_set(v_reuseFailAlloc_5464_, 24, v_s_5445_);
lean_ctor_set(v_reuseFailAlloc_5464_, 25, v_S_5446_);
lean_ctor_set(v_reuseFailAlloc_5464_, 26, v_A_5447_);
lean_ctor_set(v_reuseFailAlloc_5464_, 27, v_n_5448_);
lean_ctor_set(v_reuseFailAlloc_5464_, 28, v_N_5449_);
lean_ctor_set(v_reuseFailAlloc_5464_, 29, v_V_5450_);
lean_ctor_set(v_reuseFailAlloc_5464_, 30, v_z_5451_);
lean_ctor_set(v_reuseFailAlloc_5464_, 31, v_zabbrev_5452_);
lean_ctor_set(v_reuseFailAlloc_5464_, 32, v_v_5453_);
lean_ctor_set(v_reuseFailAlloc_5464_, 33, v_O_5454_);
lean_ctor_set(v_reuseFailAlloc_5464_, 34, v_X_5455_);
lean_ctor_set(v_reuseFailAlloc_5464_, 35, v_x_5456_);
lean_ctor_set(v_reuseFailAlloc_5464_, 36, v_Z_5457_);
v___x_5463_ = v_reuseFailAlloc_5464_;
goto v_reusejp_5462_;
}
v_reusejp_5462_:
{
return v___x_5463_;
}
}
}
case 18:
{
lean_object* v_G_5467_; lean_object* v_y_5468_; lean_object* v_u_5469_; lean_object* v_Y_5470_; lean_object* v_D_5471_; lean_object* v_M_5472_; lean_object* v_L_5473_; lean_object* v_d_5474_; lean_object* v_Q_5475_; lean_object* v_q_5476_; lean_object* v_w_5477_; lean_object* v_W_5478_; lean_object* v_E_5479_; lean_object* v_e_5480_; lean_object* v_c_5481_; lean_object* v_F_5482_; lean_object* v_a_5483_; lean_object* v_b_5484_; lean_object* v_h_5485_; lean_object* v_K_5486_; lean_object* v_k_5487_; lean_object* v_H_5488_; lean_object* v_m_5489_; lean_object* v_s_5490_; lean_object* v_S_5491_; lean_object* v_A_5492_; lean_object* v_n_5493_; lean_object* v_N_5494_; lean_object* v_V_5495_; lean_object* v_z_5496_; lean_object* v_zabbrev_5497_; lean_object* v_v_5498_; lean_object* v_O_5499_; lean_object* v_X_5500_; lean_object* v_x_5501_; lean_object* v_Z_5502_; lean_object* v___x_5504_; uint8_t v_isShared_5505_; uint8_t v_isSharedCheck_5510_; 
lean_dec_ref_known(v_modifier_4557_, 0);
v_G_5467_ = lean_ctor_get(v_date_4556_, 0);
v_y_5468_ = lean_ctor_get(v_date_4556_, 1);
v_u_5469_ = lean_ctor_get(v_date_4556_, 2);
v_Y_5470_ = lean_ctor_get(v_date_4556_, 3);
v_D_5471_ = lean_ctor_get(v_date_4556_, 4);
v_M_5472_ = lean_ctor_get(v_date_4556_, 5);
v_L_5473_ = lean_ctor_get(v_date_4556_, 6);
v_d_5474_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5475_ = lean_ctor_get(v_date_4556_, 8);
v_q_5476_ = lean_ctor_get(v_date_4556_, 9);
v_w_5477_ = lean_ctor_get(v_date_4556_, 10);
v_W_5478_ = lean_ctor_get(v_date_4556_, 11);
v_E_5479_ = lean_ctor_get(v_date_4556_, 12);
v_e_5480_ = lean_ctor_get(v_date_4556_, 13);
v_c_5481_ = lean_ctor_get(v_date_4556_, 14);
v_F_5482_ = lean_ctor_get(v_date_4556_, 15);
v_a_5483_ = lean_ctor_get(v_date_4556_, 16);
v_b_5484_ = lean_ctor_get(v_date_4556_, 17);
v_h_5485_ = lean_ctor_get(v_date_4556_, 19);
v_K_5486_ = lean_ctor_get(v_date_4556_, 20);
v_k_5487_ = lean_ctor_get(v_date_4556_, 21);
v_H_5488_ = lean_ctor_get(v_date_4556_, 22);
v_m_5489_ = lean_ctor_get(v_date_4556_, 23);
v_s_5490_ = lean_ctor_get(v_date_4556_, 24);
v_S_5491_ = lean_ctor_get(v_date_4556_, 25);
v_A_5492_ = lean_ctor_get(v_date_4556_, 26);
v_n_5493_ = lean_ctor_get(v_date_4556_, 27);
v_N_5494_ = lean_ctor_get(v_date_4556_, 28);
v_V_5495_ = lean_ctor_get(v_date_4556_, 29);
v_z_5496_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5497_ = lean_ctor_get(v_date_4556_, 31);
v_v_5498_ = lean_ctor_get(v_date_4556_, 32);
v_O_5499_ = lean_ctor_get(v_date_4556_, 33);
v_X_5500_ = lean_ctor_get(v_date_4556_, 34);
v_x_5501_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5502_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5510_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5510_ == 0)
{
lean_object* v_unused_5511_; 
v_unused_5511_ = lean_ctor_get(v_date_4556_, 18);
lean_dec(v_unused_5511_);
v___x_5504_ = v_date_4556_;
v_isShared_5505_ = v_isSharedCheck_5510_;
goto v_resetjp_5503_;
}
else
{
lean_inc(v_Z_5502_);
lean_inc(v_x_5501_);
lean_inc(v_X_5500_);
lean_inc(v_O_5499_);
lean_inc(v_v_5498_);
lean_inc(v_zabbrev_5497_);
lean_inc(v_z_5496_);
lean_inc(v_V_5495_);
lean_inc(v_N_5494_);
lean_inc(v_n_5493_);
lean_inc(v_A_5492_);
lean_inc(v_S_5491_);
lean_inc(v_s_5490_);
lean_inc(v_m_5489_);
lean_inc(v_H_5488_);
lean_inc(v_k_5487_);
lean_inc(v_K_5486_);
lean_inc(v_h_5485_);
lean_inc(v_b_5484_);
lean_inc(v_a_5483_);
lean_inc(v_F_5482_);
lean_inc(v_c_5481_);
lean_inc(v_e_5480_);
lean_inc(v_E_5479_);
lean_inc(v_W_5478_);
lean_inc(v_w_5477_);
lean_inc(v_q_5476_);
lean_inc(v_Q_5475_);
lean_inc(v_d_5474_);
lean_inc(v_L_5473_);
lean_inc(v_M_5472_);
lean_inc(v_D_5471_);
lean_inc(v_Y_5470_);
lean_inc(v_u_5469_);
lean_inc(v_y_5468_);
lean_inc(v_G_5467_);
lean_dec(v_date_4556_);
v___x_5504_ = lean_box(0);
v_isShared_5505_ = v_isSharedCheck_5510_;
goto v_resetjp_5503_;
}
v_resetjp_5503_:
{
lean_object* v___x_5506_; lean_object* v___x_5508_; 
v___x_5506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5506_, 0, v_data_4558_);
if (v_isShared_5505_ == 0)
{
lean_ctor_set(v___x_5504_, 18, v___x_5506_);
v___x_5508_ = v___x_5504_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5509_; 
v_reuseFailAlloc_5509_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5509_, 0, v_G_5467_);
lean_ctor_set(v_reuseFailAlloc_5509_, 1, v_y_5468_);
lean_ctor_set(v_reuseFailAlloc_5509_, 2, v_u_5469_);
lean_ctor_set(v_reuseFailAlloc_5509_, 3, v_Y_5470_);
lean_ctor_set(v_reuseFailAlloc_5509_, 4, v_D_5471_);
lean_ctor_set(v_reuseFailAlloc_5509_, 5, v_M_5472_);
lean_ctor_set(v_reuseFailAlloc_5509_, 6, v_L_5473_);
lean_ctor_set(v_reuseFailAlloc_5509_, 7, v_d_5474_);
lean_ctor_set(v_reuseFailAlloc_5509_, 8, v_Q_5475_);
lean_ctor_set(v_reuseFailAlloc_5509_, 9, v_q_5476_);
lean_ctor_set(v_reuseFailAlloc_5509_, 10, v_w_5477_);
lean_ctor_set(v_reuseFailAlloc_5509_, 11, v_W_5478_);
lean_ctor_set(v_reuseFailAlloc_5509_, 12, v_E_5479_);
lean_ctor_set(v_reuseFailAlloc_5509_, 13, v_e_5480_);
lean_ctor_set(v_reuseFailAlloc_5509_, 14, v_c_5481_);
lean_ctor_set(v_reuseFailAlloc_5509_, 15, v_F_5482_);
lean_ctor_set(v_reuseFailAlloc_5509_, 16, v_a_5483_);
lean_ctor_set(v_reuseFailAlloc_5509_, 17, v_b_5484_);
lean_ctor_set(v_reuseFailAlloc_5509_, 18, v___x_5506_);
lean_ctor_set(v_reuseFailAlloc_5509_, 19, v_h_5485_);
lean_ctor_set(v_reuseFailAlloc_5509_, 20, v_K_5486_);
lean_ctor_set(v_reuseFailAlloc_5509_, 21, v_k_5487_);
lean_ctor_set(v_reuseFailAlloc_5509_, 22, v_H_5488_);
lean_ctor_set(v_reuseFailAlloc_5509_, 23, v_m_5489_);
lean_ctor_set(v_reuseFailAlloc_5509_, 24, v_s_5490_);
lean_ctor_set(v_reuseFailAlloc_5509_, 25, v_S_5491_);
lean_ctor_set(v_reuseFailAlloc_5509_, 26, v_A_5492_);
lean_ctor_set(v_reuseFailAlloc_5509_, 27, v_n_5493_);
lean_ctor_set(v_reuseFailAlloc_5509_, 28, v_N_5494_);
lean_ctor_set(v_reuseFailAlloc_5509_, 29, v_V_5495_);
lean_ctor_set(v_reuseFailAlloc_5509_, 30, v_z_5496_);
lean_ctor_set(v_reuseFailAlloc_5509_, 31, v_zabbrev_5497_);
lean_ctor_set(v_reuseFailAlloc_5509_, 32, v_v_5498_);
lean_ctor_set(v_reuseFailAlloc_5509_, 33, v_O_5499_);
lean_ctor_set(v_reuseFailAlloc_5509_, 34, v_X_5500_);
lean_ctor_set(v_reuseFailAlloc_5509_, 35, v_x_5501_);
lean_ctor_set(v_reuseFailAlloc_5509_, 36, v_Z_5502_);
v___x_5508_ = v_reuseFailAlloc_5509_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
return v___x_5508_;
}
}
}
case 19:
{
lean_object* v___x_5513_; uint8_t v_isShared_5514_; uint8_t v_isSharedCheck_5562_; 
v_isSharedCheck_5562_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_5562_ == 0)
{
lean_object* v_unused_5563_; 
v_unused_5563_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_5563_);
v___x_5513_ = v_modifier_4557_;
v_isShared_5514_ = v_isSharedCheck_5562_;
goto v_resetjp_5512_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_5513_ = lean_box(0);
v_isShared_5514_ = v_isSharedCheck_5562_;
goto v_resetjp_5512_;
}
v_resetjp_5512_:
{
lean_object* v_G_5515_; lean_object* v_y_5516_; lean_object* v_u_5517_; lean_object* v_Y_5518_; lean_object* v_D_5519_; lean_object* v_M_5520_; lean_object* v_L_5521_; lean_object* v_d_5522_; lean_object* v_Q_5523_; lean_object* v_q_5524_; lean_object* v_w_5525_; lean_object* v_W_5526_; lean_object* v_E_5527_; lean_object* v_e_5528_; lean_object* v_c_5529_; lean_object* v_F_5530_; lean_object* v_a_5531_; lean_object* v_b_5532_; lean_object* v_B_5533_; lean_object* v_K_5534_; lean_object* v_k_5535_; lean_object* v_H_5536_; lean_object* v_m_5537_; lean_object* v_s_5538_; lean_object* v_S_5539_; lean_object* v_A_5540_; lean_object* v_n_5541_; lean_object* v_N_5542_; lean_object* v_V_5543_; lean_object* v_z_5544_; lean_object* v_zabbrev_5545_; lean_object* v_v_5546_; lean_object* v_O_5547_; lean_object* v_X_5548_; lean_object* v_x_5549_; lean_object* v_Z_5550_; lean_object* v___x_5552_; uint8_t v_isShared_5553_; uint8_t v_isSharedCheck_5560_; 
v_G_5515_ = lean_ctor_get(v_date_4556_, 0);
v_y_5516_ = lean_ctor_get(v_date_4556_, 1);
v_u_5517_ = lean_ctor_get(v_date_4556_, 2);
v_Y_5518_ = lean_ctor_get(v_date_4556_, 3);
v_D_5519_ = lean_ctor_get(v_date_4556_, 4);
v_M_5520_ = lean_ctor_get(v_date_4556_, 5);
v_L_5521_ = lean_ctor_get(v_date_4556_, 6);
v_d_5522_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5523_ = lean_ctor_get(v_date_4556_, 8);
v_q_5524_ = lean_ctor_get(v_date_4556_, 9);
v_w_5525_ = lean_ctor_get(v_date_4556_, 10);
v_W_5526_ = lean_ctor_get(v_date_4556_, 11);
v_E_5527_ = lean_ctor_get(v_date_4556_, 12);
v_e_5528_ = lean_ctor_get(v_date_4556_, 13);
v_c_5529_ = lean_ctor_get(v_date_4556_, 14);
v_F_5530_ = lean_ctor_get(v_date_4556_, 15);
v_a_5531_ = lean_ctor_get(v_date_4556_, 16);
v_b_5532_ = lean_ctor_get(v_date_4556_, 17);
v_B_5533_ = lean_ctor_get(v_date_4556_, 18);
v_K_5534_ = lean_ctor_get(v_date_4556_, 20);
v_k_5535_ = lean_ctor_get(v_date_4556_, 21);
v_H_5536_ = lean_ctor_get(v_date_4556_, 22);
v_m_5537_ = lean_ctor_get(v_date_4556_, 23);
v_s_5538_ = lean_ctor_get(v_date_4556_, 24);
v_S_5539_ = lean_ctor_get(v_date_4556_, 25);
v_A_5540_ = lean_ctor_get(v_date_4556_, 26);
v_n_5541_ = lean_ctor_get(v_date_4556_, 27);
v_N_5542_ = lean_ctor_get(v_date_4556_, 28);
v_V_5543_ = lean_ctor_get(v_date_4556_, 29);
v_z_5544_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5545_ = lean_ctor_get(v_date_4556_, 31);
v_v_5546_ = lean_ctor_get(v_date_4556_, 32);
v_O_5547_ = lean_ctor_get(v_date_4556_, 33);
v_X_5548_ = lean_ctor_get(v_date_4556_, 34);
v_x_5549_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5550_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5560_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5560_ == 0)
{
lean_object* v_unused_5561_; 
v_unused_5561_ = lean_ctor_get(v_date_4556_, 19);
lean_dec(v_unused_5561_);
v___x_5552_ = v_date_4556_;
v_isShared_5553_ = v_isSharedCheck_5560_;
goto v_resetjp_5551_;
}
else
{
lean_inc(v_Z_5550_);
lean_inc(v_x_5549_);
lean_inc(v_X_5548_);
lean_inc(v_O_5547_);
lean_inc(v_v_5546_);
lean_inc(v_zabbrev_5545_);
lean_inc(v_z_5544_);
lean_inc(v_V_5543_);
lean_inc(v_N_5542_);
lean_inc(v_n_5541_);
lean_inc(v_A_5540_);
lean_inc(v_S_5539_);
lean_inc(v_s_5538_);
lean_inc(v_m_5537_);
lean_inc(v_H_5536_);
lean_inc(v_k_5535_);
lean_inc(v_K_5534_);
lean_inc(v_B_5533_);
lean_inc(v_b_5532_);
lean_inc(v_a_5531_);
lean_inc(v_F_5530_);
lean_inc(v_c_5529_);
lean_inc(v_e_5528_);
lean_inc(v_E_5527_);
lean_inc(v_W_5526_);
lean_inc(v_w_5525_);
lean_inc(v_q_5524_);
lean_inc(v_Q_5523_);
lean_inc(v_d_5522_);
lean_inc(v_L_5521_);
lean_inc(v_M_5520_);
lean_inc(v_D_5519_);
lean_inc(v_Y_5518_);
lean_inc(v_u_5517_);
lean_inc(v_y_5516_);
lean_inc(v_G_5515_);
lean_dec(v_date_4556_);
v___x_5552_ = lean_box(0);
v_isShared_5553_ = v_isSharedCheck_5560_;
goto v_resetjp_5551_;
}
v_resetjp_5551_:
{
lean_object* v___x_5555_; 
if (v_isShared_5514_ == 0)
{
lean_ctor_set_tag(v___x_5513_, 1);
lean_ctor_set(v___x_5513_, 0, v_data_4558_);
v___x_5555_ = v___x_5513_;
goto v_reusejp_5554_;
}
else
{
lean_object* v_reuseFailAlloc_5559_; 
v_reuseFailAlloc_5559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5559_, 0, v_data_4558_);
v___x_5555_ = v_reuseFailAlloc_5559_;
goto v_reusejp_5554_;
}
v_reusejp_5554_:
{
lean_object* v___x_5557_; 
if (v_isShared_5553_ == 0)
{
lean_ctor_set(v___x_5552_, 19, v___x_5555_);
v___x_5557_ = v___x_5552_;
goto v_reusejp_5556_;
}
else
{
lean_object* v_reuseFailAlloc_5558_; 
v_reuseFailAlloc_5558_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5558_, 0, v_G_5515_);
lean_ctor_set(v_reuseFailAlloc_5558_, 1, v_y_5516_);
lean_ctor_set(v_reuseFailAlloc_5558_, 2, v_u_5517_);
lean_ctor_set(v_reuseFailAlloc_5558_, 3, v_Y_5518_);
lean_ctor_set(v_reuseFailAlloc_5558_, 4, v_D_5519_);
lean_ctor_set(v_reuseFailAlloc_5558_, 5, v_M_5520_);
lean_ctor_set(v_reuseFailAlloc_5558_, 6, v_L_5521_);
lean_ctor_set(v_reuseFailAlloc_5558_, 7, v_d_5522_);
lean_ctor_set(v_reuseFailAlloc_5558_, 8, v_Q_5523_);
lean_ctor_set(v_reuseFailAlloc_5558_, 9, v_q_5524_);
lean_ctor_set(v_reuseFailAlloc_5558_, 10, v_w_5525_);
lean_ctor_set(v_reuseFailAlloc_5558_, 11, v_W_5526_);
lean_ctor_set(v_reuseFailAlloc_5558_, 12, v_E_5527_);
lean_ctor_set(v_reuseFailAlloc_5558_, 13, v_e_5528_);
lean_ctor_set(v_reuseFailAlloc_5558_, 14, v_c_5529_);
lean_ctor_set(v_reuseFailAlloc_5558_, 15, v_F_5530_);
lean_ctor_set(v_reuseFailAlloc_5558_, 16, v_a_5531_);
lean_ctor_set(v_reuseFailAlloc_5558_, 17, v_b_5532_);
lean_ctor_set(v_reuseFailAlloc_5558_, 18, v_B_5533_);
lean_ctor_set(v_reuseFailAlloc_5558_, 19, v___x_5555_);
lean_ctor_set(v_reuseFailAlloc_5558_, 20, v_K_5534_);
lean_ctor_set(v_reuseFailAlloc_5558_, 21, v_k_5535_);
lean_ctor_set(v_reuseFailAlloc_5558_, 22, v_H_5536_);
lean_ctor_set(v_reuseFailAlloc_5558_, 23, v_m_5537_);
lean_ctor_set(v_reuseFailAlloc_5558_, 24, v_s_5538_);
lean_ctor_set(v_reuseFailAlloc_5558_, 25, v_S_5539_);
lean_ctor_set(v_reuseFailAlloc_5558_, 26, v_A_5540_);
lean_ctor_set(v_reuseFailAlloc_5558_, 27, v_n_5541_);
lean_ctor_set(v_reuseFailAlloc_5558_, 28, v_N_5542_);
lean_ctor_set(v_reuseFailAlloc_5558_, 29, v_V_5543_);
lean_ctor_set(v_reuseFailAlloc_5558_, 30, v_z_5544_);
lean_ctor_set(v_reuseFailAlloc_5558_, 31, v_zabbrev_5545_);
lean_ctor_set(v_reuseFailAlloc_5558_, 32, v_v_5546_);
lean_ctor_set(v_reuseFailAlloc_5558_, 33, v_O_5547_);
lean_ctor_set(v_reuseFailAlloc_5558_, 34, v_X_5548_);
lean_ctor_set(v_reuseFailAlloc_5558_, 35, v_x_5549_);
lean_ctor_set(v_reuseFailAlloc_5558_, 36, v_Z_5550_);
v___x_5557_ = v_reuseFailAlloc_5558_;
goto v_reusejp_5556_;
}
v_reusejp_5556_:
{
return v___x_5557_;
}
}
}
}
}
case 20:
{
lean_object* v___x_5565_; uint8_t v_isShared_5566_; uint8_t v_isSharedCheck_5614_; 
v_isSharedCheck_5614_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_5614_ == 0)
{
lean_object* v_unused_5615_; 
v_unused_5615_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_5615_);
v___x_5565_ = v_modifier_4557_;
v_isShared_5566_ = v_isSharedCheck_5614_;
goto v_resetjp_5564_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_5565_ = lean_box(0);
v_isShared_5566_ = v_isSharedCheck_5614_;
goto v_resetjp_5564_;
}
v_resetjp_5564_:
{
lean_object* v_G_5567_; lean_object* v_y_5568_; lean_object* v_u_5569_; lean_object* v_Y_5570_; lean_object* v_D_5571_; lean_object* v_M_5572_; lean_object* v_L_5573_; lean_object* v_d_5574_; lean_object* v_Q_5575_; lean_object* v_q_5576_; lean_object* v_w_5577_; lean_object* v_W_5578_; lean_object* v_E_5579_; lean_object* v_e_5580_; lean_object* v_c_5581_; lean_object* v_F_5582_; lean_object* v_a_5583_; lean_object* v_b_5584_; lean_object* v_B_5585_; lean_object* v_h_5586_; lean_object* v_k_5587_; lean_object* v_H_5588_; lean_object* v_m_5589_; lean_object* v_s_5590_; lean_object* v_S_5591_; lean_object* v_A_5592_; lean_object* v_n_5593_; lean_object* v_N_5594_; lean_object* v_V_5595_; lean_object* v_z_5596_; lean_object* v_zabbrev_5597_; lean_object* v_v_5598_; lean_object* v_O_5599_; lean_object* v_X_5600_; lean_object* v_x_5601_; lean_object* v_Z_5602_; lean_object* v___x_5604_; uint8_t v_isShared_5605_; uint8_t v_isSharedCheck_5612_; 
v_G_5567_ = lean_ctor_get(v_date_4556_, 0);
v_y_5568_ = lean_ctor_get(v_date_4556_, 1);
v_u_5569_ = lean_ctor_get(v_date_4556_, 2);
v_Y_5570_ = lean_ctor_get(v_date_4556_, 3);
v_D_5571_ = lean_ctor_get(v_date_4556_, 4);
v_M_5572_ = lean_ctor_get(v_date_4556_, 5);
v_L_5573_ = lean_ctor_get(v_date_4556_, 6);
v_d_5574_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5575_ = lean_ctor_get(v_date_4556_, 8);
v_q_5576_ = lean_ctor_get(v_date_4556_, 9);
v_w_5577_ = lean_ctor_get(v_date_4556_, 10);
v_W_5578_ = lean_ctor_get(v_date_4556_, 11);
v_E_5579_ = lean_ctor_get(v_date_4556_, 12);
v_e_5580_ = lean_ctor_get(v_date_4556_, 13);
v_c_5581_ = lean_ctor_get(v_date_4556_, 14);
v_F_5582_ = lean_ctor_get(v_date_4556_, 15);
v_a_5583_ = lean_ctor_get(v_date_4556_, 16);
v_b_5584_ = lean_ctor_get(v_date_4556_, 17);
v_B_5585_ = lean_ctor_get(v_date_4556_, 18);
v_h_5586_ = lean_ctor_get(v_date_4556_, 19);
v_k_5587_ = lean_ctor_get(v_date_4556_, 21);
v_H_5588_ = lean_ctor_get(v_date_4556_, 22);
v_m_5589_ = lean_ctor_get(v_date_4556_, 23);
v_s_5590_ = lean_ctor_get(v_date_4556_, 24);
v_S_5591_ = lean_ctor_get(v_date_4556_, 25);
v_A_5592_ = lean_ctor_get(v_date_4556_, 26);
v_n_5593_ = lean_ctor_get(v_date_4556_, 27);
v_N_5594_ = lean_ctor_get(v_date_4556_, 28);
v_V_5595_ = lean_ctor_get(v_date_4556_, 29);
v_z_5596_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5597_ = lean_ctor_get(v_date_4556_, 31);
v_v_5598_ = lean_ctor_get(v_date_4556_, 32);
v_O_5599_ = lean_ctor_get(v_date_4556_, 33);
v_X_5600_ = lean_ctor_get(v_date_4556_, 34);
v_x_5601_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5602_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5612_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5612_ == 0)
{
lean_object* v_unused_5613_; 
v_unused_5613_ = lean_ctor_get(v_date_4556_, 20);
lean_dec(v_unused_5613_);
v___x_5604_ = v_date_4556_;
v_isShared_5605_ = v_isSharedCheck_5612_;
goto v_resetjp_5603_;
}
else
{
lean_inc(v_Z_5602_);
lean_inc(v_x_5601_);
lean_inc(v_X_5600_);
lean_inc(v_O_5599_);
lean_inc(v_v_5598_);
lean_inc(v_zabbrev_5597_);
lean_inc(v_z_5596_);
lean_inc(v_V_5595_);
lean_inc(v_N_5594_);
lean_inc(v_n_5593_);
lean_inc(v_A_5592_);
lean_inc(v_S_5591_);
lean_inc(v_s_5590_);
lean_inc(v_m_5589_);
lean_inc(v_H_5588_);
lean_inc(v_k_5587_);
lean_inc(v_h_5586_);
lean_inc(v_B_5585_);
lean_inc(v_b_5584_);
lean_inc(v_a_5583_);
lean_inc(v_F_5582_);
lean_inc(v_c_5581_);
lean_inc(v_e_5580_);
lean_inc(v_E_5579_);
lean_inc(v_W_5578_);
lean_inc(v_w_5577_);
lean_inc(v_q_5576_);
lean_inc(v_Q_5575_);
lean_inc(v_d_5574_);
lean_inc(v_L_5573_);
lean_inc(v_M_5572_);
lean_inc(v_D_5571_);
lean_inc(v_Y_5570_);
lean_inc(v_u_5569_);
lean_inc(v_y_5568_);
lean_inc(v_G_5567_);
lean_dec(v_date_4556_);
v___x_5604_ = lean_box(0);
v_isShared_5605_ = v_isSharedCheck_5612_;
goto v_resetjp_5603_;
}
v_resetjp_5603_:
{
lean_object* v___x_5607_; 
if (v_isShared_5566_ == 0)
{
lean_ctor_set_tag(v___x_5565_, 1);
lean_ctor_set(v___x_5565_, 0, v_data_4558_);
v___x_5607_ = v___x_5565_;
goto v_reusejp_5606_;
}
else
{
lean_object* v_reuseFailAlloc_5611_; 
v_reuseFailAlloc_5611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5611_, 0, v_data_4558_);
v___x_5607_ = v_reuseFailAlloc_5611_;
goto v_reusejp_5606_;
}
v_reusejp_5606_:
{
lean_object* v___x_5609_; 
if (v_isShared_5605_ == 0)
{
lean_ctor_set(v___x_5604_, 20, v___x_5607_);
v___x_5609_ = v___x_5604_;
goto v_reusejp_5608_;
}
else
{
lean_object* v_reuseFailAlloc_5610_; 
v_reuseFailAlloc_5610_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5610_, 0, v_G_5567_);
lean_ctor_set(v_reuseFailAlloc_5610_, 1, v_y_5568_);
lean_ctor_set(v_reuseFailAlloc_5610_, 2, v_u_5569_);
lean_ctor_set(v_reuseFailAlloc_5610_, 3, v_Y_5570_);
lean_ctor_set(v_reuseFailAlloc_5610_, 4, v_D_5571_);
lean_ctor_set(v_reuseFailAlloc_5610_, 5, v_M_5572_);
lean_ctor_set(v_reuseFailAlloc_5610_, 6, v_L_5573_);
lean_ctor_set(v_reuseFailAlloc_5610_, 7, v_d_5574_);
lean_ctor_set(v_reuseFailAlloc_5610_, 8, v_Q_5575_);
lean_ctor_set(v_reuseFailAlloc_5610_, 9, v_q_5576_);
lean_ctor_set(v_reuseFailAlloc_5610_, 10, v_w_5577_);
lean_ctor_set(v_reuseFailAlloc_5610_, 11, v_W_5578_);
lean_ctor_set(v_reuseFailAlloc_5610_, 12, v_E_5579_);
lean_ctor_set(v_reuseFailAlloc_5610_, 13, v_e_5580_);
lean_ctor_set(v_reuseFailAlloc_5610_, 14, v_c_5581_);
lean_ctor_set(v_reuseFailAlloc_5610_, 15, v_F_5582_);
lean_ctor_set(v_reuseFailAlloc_5610_, 16, v_a_5583_);
lean_ctor_set(v_reuseFailAlloc_5610_, 17, v_b_5584_);
lean_ctor_set(v_reuseFailAlloc_5610_, 18, v_B_5585_);
lean_ctor_set(v_reuseFailAlloc_5610_, 19, v_h_5586_);
lean_ctor_set(v_reuseFailAlloc_5610_, 20, v___x_5607_);
lean_ctor_set(v_reuseFailAlloc_5610_, 21, v_k_5587_);
lean_ctor_set(v_reuseFailAlloc_5610_, 22, v_H_5588_);
lean_ctor_set(v_reuseFailAlloc_5610_, 23, v_m_5589_);
lean_ctor_set(v_reuseFailAlloc_5610_, 24, v_s_5590_);
lean_ctor_set(v_reuseFailAlloc_5610_, 25, v_S_5591_);
lean_ctor_set(v_reuseFailAlloc_5610_, 26, v_A_5592_);
lean_ctor_set(v_reuseFailAlloc_5610_, 27, v_n_5593_);
lean_ctor_set(v_reuseFailAlloc_5610_, 28, v_N_5594_);
lean_ctor_set(v_reuseFailAlloc_5610_, 29, v_V_5595_);
lean_ctor_set(v_reuseFailAlloc_5610_, 30, v_z_5596_);
lean_ctor_set(v_reuseFailAlloc_5610_, 31, v_zabbrev_5597_);
lean_ctor_set(v_reuseFailAlloc_5610_, 32, v_v_5598_);
lean_ctor_set(v_reuseFailAlloc_5610_, 33, v_O_5599_);
lean_ctor_set(v_reuseFailAlloc_5610_, 34, v_X_5600_);
lean_ctor_set(v_reuseFailAlloc_5610_, 35, v_x_5601_);
lean_ctor_set(v_reuseFailAlloc_5610_, 36, v_Z_5602_);
v___x_5609_ = v_reuseFailAlloc_5610_;
goto v_reusejp_5608_;
}
v_reusejp_5608_:
{
return v___x_5609_;
}
}
}
}
}
case 21:
{
lean_object* v___x_5617_; uint8_t v_isShared_5618_; uint8_t v_isSharedCheck_5666_; 
v_isSharedCheck_5666_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_5666_ == 0)
{
lean_object* v_unused_5667_; 
v_unused_5667_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_5667_);
v___x_5617_ = v_modifier_4557_;
v_isShared_5618_ = v_isSharedCheck_5666_;
goto v_resetjp_5616_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_5617_ = lean_box(0);
v_isShared_5618_ = v_isSharedCheck_5666_;
goto v_resetjp_5616_;
}
v_resetjp_5616_:
{
lean_object* v_G_5619_; lean_object* v_y_5620_; lean_object* v_u_5621_; lean_object* v_Y_5622_; lean_object* v_D_5623_; lean_object* v_M_5624_; lean_object* v_L_5625_; lean_object* v_d_5626_; lean_object* v_Q_5627_; lean_object* v_q_5628_; lean_object* v_w_5629_; lean_object* v_W_5630_; lean_object* v_E_5631_; lean_object* v_e_5632_; lean_object* v_c_5633_; lean_object* v_F_5634_; lean_object* v_a_5635_; lean_object* v_b_5636_; lean_object* v_B_5637_; lean_object* v_h_5638_; lean_object* v_K_5639_; lean_object* v_H_5640_; lean_object* v_m_5641_; lean_object* v_s_5642_; lean_object* v_S_5643_; lean_object* v_A_5644_; lean_object* v_n_5645_; lean_object* v_N_5646_; lean_object* v_V_5647_; lean_object* v_z_5648_; lean_object* v_zabbrev_5649_; lean_object* v_v_5650_; lean_object* v_O_5651_; lean_object* v_X_5652_; lean_object* v_x_5653_; lean_object* v_Z_5654_; lean_object* v___x_5656_; uint8_t v_isShared_5657_; uint8_t v_isSharedCheck_5664_; 
v_G_5619_ = lean_ctor_get(v_date_4556_, 0);
v_y_5620_ = lean_ctor_get(v_date_4556_, 1);
v_u_5621_ = lean_ctor_get(v_date_4556_, 2);
v_Y_5622_ = lean_ctor_get(v_date_4556_, 3);
v_D_5623_ = lean_ctor_get(v_date_4556_, 4);
v_M_5624_ = lean_ctor_get(v_date_4556_, 5);
v_L_5625_ = lean_ctor_get(v_date_4556_, 6);
v_d_5626_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5627_ = lean_ctor_get(v_date_4556_, 8);
v_q_5628_ = lean_ctor_get(v_date_4556_, 9);
v_w_5629_ = lean_ctor_get(v_date_4556_, 10);
v_W_5630_ = lean_ctor_get(v_date_4556_, 11);
v_E_5631_ = lean_ctor_get(v_date_4556_, 12);
v_e_5632_ = lean_ctor_get(v_date_4556_, 13);
v_c_5633_ = lean_ctor_get(v_date_4556_, 14);
v_F_5634_ = lean_ctor_get(v_date_4556_, 15);
v_a_5635_ = lean_ctor_get(v_date_4556_, 16);
v_b_5636_ = lean_ctor_get(v_date_4556_, 17);
v_B_5637_ = lean_ctor_get(v_date_4556_, 18);
v_h_5638_ = lean_ctor_get(v_date_4556_, 19);
v_K_5639_ = lean_ctor_get(v_date_4556_, 20);
v_H_5640_ = lean_ctor_get(v_date_4556_, 22);
v_m_5641_ = lean_ctor_get(v_date_4556_, 23);
v_s_5642_ = lean_ctor_get(v_date_4556_, 24);
v_S_5643_ = lean_ctor_get(v_date_4556_, 25);
v_A_5644_ = lean_ctor_get(v_date_4556_, 26);
v_n_5645_ = lean_ctor_get(v_date_4556_, 27);
v_N_5646_ = lean_ctor_get(v_date_4556_, 28);
v_V_5647_ = lean_ctor_get(v_date_4556_, 29);
v_z_5648_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5649_ = lean_ctor_get(v_date_4556_, 31);
v_v_5650_ = lean_ctor_get(v_date_4556_, 32);
v_O_5651_ = lean_ctor_get(v_date_4556_, 33);
v_X_5652_ = lean_ctor_get(v_date_4556_, 34);
v_x_5653_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5654_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5664_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5664_ == 0)
{
lean_object* v_unused_5665_; 
v_unused_5665_ = lean_ctor_get(v_date_4556_, 21);
lean_dec(v_unused_5665_);
v___x_5656_ = v_date_4556_;
v_isShared_5657_ = v_isSharedCheck_5664_;
goto v_resetjp_5655_;
}
else
{
lean_inc(v_Z_5654_);
lean_inc(v_x_5653_);
lean_inc(v_X_5652_);
lean_inc(v_O_5651_);
lean_inc(v_v_5650_);
lean_inc(v_zabbrev_5649_);
lean_inc(v_z_5648_);
lean_inc(v_V_5647_);
lean_inc(v_N_5646_);
lean_inc(v_n_5645_);
lean_inc(v_A_5644_);
lean_inc(v_S_5643_);
lean_inc(v_s_5642_);
lean_inc(v_m_5641_);
lean_inc(v_H_5640_);
lean_inc(v_K_5639_);
lean_inc(v_h_5638_);
lean_inc(v_B_5637_);
lean_inc(v_b_5636_);
lean_inc(v_a_5635_);
lean_inc(v_F_5634_);
lean_inc(v_c_5633_);
lean_inc(v_e_5632_);
lean_inc(v_E_5631_);
lean_inc(v_W_5630_);
lean_inc(v_w_5629_);
lean_inc(v_q_5628_);
lean_inc(v_Q_5627_);
lean_inc(v_d_5626_);
lean_inc(v_L_5625_);
lean_inc(v_M_5624_);
lean_inc(v_D_5623_);
lean_inc(v_Y_5622_);
lean_inc(v_u_5621_);
lean_inc(v_y_5620_);
lean_inc(v_G_5619_);
lean_dec(v_date_4556_);
v___x_5656_ = lean_box(0);
v_isShared_5657_ = v_isSharedCheck_5664_;
goto v_resetjp_5655_;
}
v_resetjp_5655_:
{
lean_object* v___x_5659_; 
if (v_isShared_5618_ == 0)
{
lean_ctor_set_tag(v___x_5617_, 1);
lean_ctor_set(v___x_5617_, 0, v_data_4558_);
v___x_5659_ = v___x_5617_;
goto v_reusejp_5658_;
}
else
{
lean_object* v_reuseFailAlloc_5663_; 
v_reuseFailAlloc_5663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5663_, 0, v_data_4558_);
v___x_5659_ = v_reuseFailAlloc_5663_;
goto v_reusejp_5658_;
}
v_reusejp_5658_:
{
lean_object* v___x_5661_; 
if (v_isShared_5657_ == 0)
{
lean_ctor_set(v___x_5656_, 21, v___x_5659_);
v___x_5661_ = v___x_5656_;
goto v_reusejp_5660_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_G_5619_);
lean_ctor_set(v_reuseFailAlloc_5662_, 1, v_y_5620_);
lean_ctor_set(v_reuseFailAlloc_5662_, 2, v_u_5621_);
lean_ctor_set(v_reuseFailAlloc_5662_, 3, v_Y_5622_);
lean_ctor_set(v_reuseFailAlloc_5662_, 4, v_D_5623_);
lean_ctor_set(v_reuseFailAlloc_5662_, 5, v_M_5624_);
lean_ctor_set(v_reuseFailAlloc_5662_, 6, v_L_5625_);
lean_ctor_set(v_reuseFailAlloc_5662_, 7, v_d_5626_);
lean_ctor_set(v_reuseFailAlloc_5662_, 8, v_Q_5627_);
lean_ctor_set(v_reuseFailAlloc_5662_, 9, v_q_5628_);
lean_ctor_set(v_reuseFailAlloc_5662_, 10, v_w_5629_);
lean_ctor_set(v_reuseFailAlloc_5662_, 11, v_W_5630_);
lean_ctor_set(v_reuseFailAlloc_5662_, 12, v_E_5631_);
lean_ctor_set(v_reuseFailAlloc_5662_, 13, v_e_5632_);
lean_ctor_set(v_reuseFailAlloc_5662_, 14, v_c_5633_);
lean_ctor_set(v_reuseFailAlloc_5662_, 15, v_F_5634_);
lean_ctor_set(v_reuseFailAlloc_5662_, 16, v_a_5635_);
lean_ctor_set(v_reuseFailAlloc_5662_, 17, v_b_5636_);
lean_ctor_set(v_reuseFailAlloc_5662_, 18, v_B_5637_);
lean_ctor_set(v_reuseFailAlloc_5662_, 19, v_h_5638_);
lean_ctor_set(v_reuseFailAlloc_5662_, 20, v_K_5639_);
lean_ctor_set(v_reuseFailAlloc_5662_, 21, v___x_5659_);
lean_ctor_set(v_reuseFailAlloc_5662_, 22, v_H_5640_);
lean_ctor_set(v_reuseFailAlloc_5662_, 23, v_m_5641_);
lean_ctor_set(v_reuseFailAlloc_5662_, 24, v_s_5642_);
lean_ctor_set(v_reuseFailAlloc_5662_, 25, v_S_5643_);
lean_ctor_set(v_reuseFailAlloc_5662_, 26, v_A_5644_);
lean_ctor_set(v_reuseFailAlloc_5662_, 27, v_n_5645_);
lean_ctor_set(v_reuseFailAlloc_5662_, 28, v_N_5646_);
lean_ctor_set(v_reuseFailAlloc_5662_, 29, v_V_5647_);
lean_ctor_set(v_reuseFailAlloc_5662_, 30, v_z_5648_);
lean_ctor_set(v_reuseFailAlloc_5662_, 31, v_zabbrev_5649_);
lean_ctor_set(v_reuseFailAlloc_5662_, 32, v_v_5650_);
lean_ctor_set(v_reuseFailAlloc_5662_, 33, v_O_5651_);
lean_ctor_set(v_reuseFailAlloc_5662_, 34, v_X_5652_);
lean_ctor_set(v_reuseFailAlloc_5662_, 35, v_x_5653_);
lean_ctor_set(v_reuseFailAlloc_5662_, 36, v_Z_5654_);
v___x_5661_ = v_reuseFailAlloc_5662_;
goto v_reusejp_5660_;
}
v_reusejp_5660_:
{
return v___x_5661_;
}
}
}
}
}
case 22:
{
lean_object* v___x_5669_; uint8_t v_isShared_5670_; uint8_t v_isSharedCheck_5718_; 
v_isSharedCheck_5718_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_5718_ == 0)
{
lean_object* v_unused_5719_; 
v_unused_5719_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_5719_);
v___x_5669_ = v_modifier_4557_;
v_isShared_5670_ = v_isSharedCheck_5718_;
goto v_resetjp_5668_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_5669_ = lean_box(0);
v_isShared_5670_ = v_isSharedCheck_5718_;
goto v_resetjp_5668_;
}
v_resetjp_5668_:
{
lean_object* v_G_5671_; lean_object* v_y_5672_; lean_object* v_u_5673_; lean_object* v_Y_5674_; lean_object* v_D_5675_; lean_object* v_M_5676_; lean_object* v_L_5677_; lean_object* v_d_5678_; lean_object* v_Q_5679_; lean_object* v_q_5680_; lean_object* v_w_5681_; lean_object* v_W_5682_; lean_object* v_E_5683_; lean_object* v_e_5684_; lean_object* v_c_5685_; lean_object* v_F_5686_; lean_object* v_a_5687_; lean_object* v_b_5688_; lean_object* v_B_5689_; lean_object* v_h_5690_; lean_object* v_K_5691_; lean_object* v_k_5692_; lean_object* v_m_5693_; lean_object* v_s_5694_; lean_object* v_S_5695_; lean_object* v_A_5696_; lean_object* v_n_5697_; lean_object* v_N_5698_; lean_object* v_V_5699_; lean_object* v_z_5700_; lean_object* v_zabbrev_5701_; lean_object* v_v_5702_; lean_object* v_O_5703_; lean_object* v_X_5704_; lean_object* v_x_5705_; lean_object* v_Z_5706_; lean_object* v___x_5708_; uint8_t v_isShared_5709_; uint8_t v_isSharedCheck_5716_; 
v_G_5671_ = lean_ctor_get(v_date_4556_, 0);
v_y_5672_ = lean_ctor_get(v_date_4556_, 1);
v_u_5673_ = lean_ctor_get(v_date_4556_, 2);
v_Y_5674_ = lean_ctor_get(v_date_4556_, 3);
v_D_5675_ = lean_ctor_get(v_date_4556_, 4);
v_M_5676_ = lean_ctor_get(v_date_4556_, 5);
v_L_5677_ = lean_ctor_get(v_date_4556_, 6);
v_d_5678_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5679_ = lean_ctor_get(v_date_4556_, 8);
v_q_5680_ = lean_ctor_get(v_date_4556_, 9);
v_w_5681_ = lean_ctor_get(v_date_4556_, 10);
v_W_5682_ = lean_ctor_get(v_date_4556_, 11);
v_E_5683_ = lean_ctor_get(v_date_4556_, 12);
v_e_5684_ = lean_ctor_get(v_date_4556_, 13);
v_c_5685_ = lean_ctor_get(v_date_4556_, 14);
v_F_5686_ = lean_ctor_get(v_date_4556_, 15);
v_a_5687_ = lean_ctor_get(v_date_4556_, 16);
v_b_5688_ = lean_ctor_get(v_date_4556_, 17);
v_B_5689_ = lean_ctor_get(v_date_4556_, 18);
v_h_5690_ = lean_ctor_get(v_date_4556_, 19);
v_K_5691_ = lean_ctor_get(v_date_4556_, 20);
v_k_5692_ = lean_ctor_get(v_date_4556_, 21);
v_m_5693_ = lean_ctor_get(v_date_4556_, 23);
v_s_5694_ = lean_ctor_get(v_date_4556_, 24);
v_S_5695_ = lean_ctor_get(v_date_4556_, 25);
v_A_5696_ = lean_ctor_get(v_date_4556_, 26);
v_n_5697_ = lean_ctor_get(v_date_4556_, 27);
v_N_5698_ = lean_ctor_get(v_date_4556_, 28);
v_V_5699_ = lean_ctor_get(v_date_4556_, 29);
v_z_5700_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5701_ = lean_ctor_get(v_date_4556_, 31);
v_v_5702_ = lean_ctor_get(v_date_4556_, 32);
v_O_5703_ = lean_ctor_get(v_date_4556_, 33);
v_X_5704_ = lean_ctor_get(v_date_4556_, 34);
v_x_5705_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5706_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5716_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5716_ == 0)
{
lean_object* v_unused_5717_; 
v_unused_5717_ = lean_ctor_get(v_date_4556_, 22);
lean_dec(v_unused_5717_);
v___x_5708_ = v_date_4556_;
v_isShared_5709_ = v_isSharedCheck_5716_;
goto v_resetjp_5707_;
}
else
{
lean_inc(v_Z_5706_);
lean_inc(v_x_5705_);
lean_inc(v_X_5704_);
lean_inc(v_O_5703_);
lean_inc(v_v_5702_);
lean_inc(v_zabbrev_5701_);
lean_inc(v_z_5700_);
lean_inc(v_V_5699_);
lean_inc(v_N_5698_);
lean_inc(v_n_5697_);
lean_inc(v_A_5696_);
lean_inc(v_S_5695_);
lean_inc(v_s_5694_);
lean_inc(v_m_5693_);
lean_inc(v_k_5692_);
lean_inc(v_K_5691_);
lean_inc(v_h_5690_);
lean_inc(v_B_5689_);
lean_inc(v_b_5688_);
lean_inc(v_a_5687_);
lean_inc(v_F_5686_);
lean_inc(v_c_5685_);
lean_inc(v_e_5684_);
lean_inc(v_E_5683_);
lean_inc(v_W_5682_);
lean_inc(v_w_5681_);
lean_inc(v_q_5680_);
lean_inc(v_Q_5679_);
lean_inc(v_d_5678_);
lean_inc(v_L_5677_);
lean_inc(v_M_5676_);
lean_inc(v_D_5675_);
lean_inc(v_Y_5674_);
lean_inc(v_u_5673_);
lean_inc(v_y_5672_);
lean_inc(v_G_5671_);
lean_dec(v_date_4556_);
v___x_5708_ = lean_box(0);
v_isShared_5709_ = v_isSharedCheck_5716_;
goto v_resetjp_5707_;
}
v_resetjp_5707_:
{
lean_object* v___x_5711_; 
if (v_isShared_5670_ == 0)
{
lean_ctor_set_tag(v___x_5669_, 1);
lean_ctor_set(v___x_5669_, 0, v_data_4558_);
v___x_5711_ = v___x_5669_;
goto v_reusejp_5710_;
}
else
{
lean_object* v_reuseFailAlloc_5715_; 
v_reuseFailAlloc_5715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5715_, 0, v_data_4558_);
v___x_5711_ = v_reuseFailAlloc_5715_;
goto v_reusejp_5710_;
}
v_reusejp_5710_:
{
lean_object* v___x_5713_; 
if (v_isShared_5709_ == 0)
{
lean_ctor_set(v___x_5708_, 22, v___x_5711_);
v___x_5713_ = v___x_5708_;
goto v_reusejp_5712_;
}
else
{
lean_object* v_reuseFailAlloc_5714_; 
v_reuseFailAlloc_5714_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5714_, 0, v_G_5671_);
lean_ctor_set(v_reuseFailAlloc_5714_, 1, v_y_5672_);
lean_ctor_set(v_reuseFailAlloc_5714_, 2, v_u_5673_);
lean_ctor_set(v_reuseFailAlloc_5714_, 3, v_Y_5674_);
lean_ctor_set(v_reuseFailAlloc_5714_, 4, v_D_5675_);
lean_ctor_set(v_reuseFailAlloc_5714_, 5, v_M_5676_);
lean_ctor_set(v_reuseFailAlloc_5714_, 6, v_L_5677_);
lean_ctor_set(v_reuseFailAlloc_5714_, 7, v_d_5678_);
lean_ctor_set(v_reuseFailAlloc_5714_, 8, v_Q_5679_);
lean_ctor_set(v_reuseFailAlloc_5714_, 9, v_q_5680_);
lean_ctor_set(v_reuseFailAlloc_5714_, 10, v_w_5681_);
lean_ctor_set(v_reuseFailAlloc_5714_, 11, v_W_5682_);
lean_ctor_set(v_reuseFailAlloc_5714_, 12, v_E_5683_);
lean_ctor_set(v_reuseFailAlloc_5714_, 13, v_e_5684_);
lean_ctor_set(v_reuseFailAlloc_5714_, 14, v_c_5685_);
lean_ctor_set(v_reuseFailAlloc_5714_, 15, v_F_5686_);
lean_ctor_set(v_reuseFailAlloc_5714_, 16, v_a_5687_);
lean_ctor_set(v_reuseFailAlloc_5714_, 17, v_b_5688_);
lean_ctor_set(v_reuseFailAlloc_5714_, 18, v_B_5689_);
lean_ctor_set(v_reuseFailAlloc_5714_, 19, v_h_5690_);
lean_ctor_set(v_reuseFailAlloc_5714_, 20, v_K_5691_);
lean_ctor_set(v_reuseFailAlloc_5714_, 21, v_k_5692_);
lean_ctor_set(v_reuseFailAlloc_5714_, 22, v___x_5711_);
lean_ctor_set(v_reuseFailAlloc_5714_, 23, v_m_5693_);
lean_ctor_set(v_reuseFailAlloc_5714_, 24, v_s_5694_);
lean_ctor_set(v_reuseFailAlloc_5714_, 25, v_S_5695_);
lean_ctor_set(v_reuseFailAlloc_5714_, 26, v_A_5696_);
lean_ctor_set(v_reuseFailAlloc_5714_, 27, v_n_5697_);
lean_ctor_set(v_reuseFailAlloc_5714_, 28, v_N_5698_);
lean_ctor_set(v_reuseFailAlloc_5714_, 29, v_V_5699_);
lean_ctor_set(v_reuseFailAlloc_5714_, 30, v_z_5700_);
lean_ctor_set(v_reuseFailAlloc_5714_, 31, v_zabbrev_5701_);
lean_ctor_set(v_reuseFailAlloc_5714_, 32, v_v_5702_);
lean_ctor_set(v_reuseFailAlloc_5714_, 33, v_O_5703_);
lean_ctor_set(v_reuseFailAlloc_5714_, 34, v_X_5704_);
lean_ctor_set(v_reuseFailAlloc_5714_, 35, v_x_5705_);
lean_ctor_set(v_reuseFailAlloc_5714_, 36, v_Z_5706_);
v___x_5713_ = v_reuseFailAlloc_5714_;
goto v_reusejp_5712_;
}
v_reusejp_5712_:
{
return v___x_5713_;
}
}
}
}
}
case 23:
{
lean_object* v___x_5721_; uint8_t v_isShared_5722_; uint8_t v_isSharedCheck_5770_; 
v_isSharedCheck_5770_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_5770_ == 0)
{
lean_object* v_unused_5771_; 
v_unused_5771_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_5771_);
v___x_5721_ = v_modifier_4557_;
v_isShared_5722_ = v_isSharedCheck_5770_;
goto v_resetjp_5720_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_5721_ = lean_box(0);
v_isShared_5722_ = v_isSharedCheck_5770_;
goto v_resetjp_5720_;
}
v_resetjp_5720_:
{
lean_object* v_G_5723_; lean_object* v_y_5724_; lean_object* v_u_5725_; lean_object* v_Y_5726_; lean_object* v_D_5727_; lean_object* v_M_5728_; lean_object* v_L_5729_; lean_object* v_d_5730_; lean_object* v_Q_5731_; lean_object* v_q_5732_; lean_object* v_w_5733_; lean_object* v_W_5734_; lean_object* v_E_5735_; lean_object* v_e_5736_; lean_object* v_c_5737_; lean_object* v_F_5738_; lean_object* v_a_5739_; lean_object* v_b_5740_; lean_object* v_B_5741_; lean_object* v_h_5742_; lean_object* v_K_5743_; lean_object* v_k_5744_; lean_object* v_H_5745_; lean_object* v_s_5746_; lean_object* v_S_5747_; lean_object* v_A_5748_; lean_object* v_n_5749_; lean_object* v_N_5750_; lean_object* v_V_5751_; lean_object* v_z_5752_; lean_object* v_zabbrev_5753_; lean_object* v_v_5754_; lean_object* v_O_5755_; lean_object* v_X_5756_; lean_object* v_x_5757_; lean_object* v_Z_5758_; lean_object* v___x_5760_; uint8_t v_isShared_5761_; uint8_t v_isSharedCheck_5768_; 
v_G_5723_ = lean_ctor_get(v_date_4556_, 0);
v_y_5724_ = lean_ctor_get(v_date_4556_, 1);
v_u_5725_ = lean_ctor_get(v_date_4556_, 2);
v_Y_5726_ = lean_ctor_get(v_date_4556_, 3);
v_D_5727_ = lean_ctor_get(v_date_4556_, 4);
v_M_5728_ = lean_ctor_get(v_date_4556_, 5);
v_L_5729_ = lean_ctor_get(v_date_4556_, 6);
v_d_5730_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5731_ = lean_ctor_get(v_date_4556_, 8);
v_q_5732_ = lean_ctor_get(v_date_4556_, 9);
v_w_5733_ = lean_ctor_get(v_date_4556_, 10);
v_W_5734_ = lean_ctor_get(v_date_4556_, 11);
v_E_5735_ = lean_ctor_get(v_date_4556_, 12);
v_e_5736_ = lean_ctor_get(v_date_4556_, 13);
v_c_5737_ = lean_ctor_get(v_date_4556_, 14);
v_F_5738_ = lean_ctor_get(v_date_4556_, 15);
v_a_5739_ = lean_ctor_get(v_date_4556_, 16);
v_b_5740_ = lean_ctor_get(v_date_4556_, 17);
v_B_5741_ = lean_ctor_get(v_date_4556_, 18);
v_h_5742_ = lean_ctor_get(v_date_4556_, 19);
v_K_5743_ = lean_ctor_get(v_date_4556_, 20);
v_k_5744_ = lean_ctor_get(v_date_4556_, 21);
v_H_5745_ = lean_ctor_get(v_date_4556_, 22);
v_s_5746_ = lean_ctor_get(v_date_4556_, 24);
v_S_5747_ = lean_ctor_get(v_date_4556_, 25);
v_A_5748_ = lean_ctor_get(v_date_4556_, 26);
v_n_5749_ = lean_ctor_get(v_date_4556_, 27);
v_N_5750_ = lean_ctor_get(v_date_4556_, 28);
v_V_5751_ = lean_ctor_get(v_date_4556_, 29);
v_z_5752_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5753_ = lean_ctor_get(v_date_4556_, 31);
v_v_5754_ = lean_ctor_get(v_date_4556_, 32);
v_O_5755_ = lean_ctor_get(v_date_4556_, 33);
v_X_5756_ = lean_ctor_get(v_date_4556_, 34);
v_x_5757_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5758_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5768_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5768_ == 0)
{
lean_object* v_unused_5769_; 
v_unused_5769_ = lean_ctor_get(v_date_4556_, 23);
lean_dec(v_unused_5769_);
v___x_5760_ = v_date_4556_;
v_isShared_5761_ = v_isSharedCheck_5768_;
goto v_resetjp_5759_;
}
else
{
lean_inc(v_Z_5758_);
lean_inc(v_x_5757_);
lean_inc(v_X_5756_);
lean_inc(v_O_5755_);
lean_inc(v_v_5754_);
lean_inc(v_zabbrev_5753_);
lean_inc(v_z_5752_);
lean_inc(v_V_5751_);
lean_inc(v_N_5750_);
lean_inc(v_n_5749_);
lean_inc(v_A_5748_);
lean_inc(v_S_5747_);
lean_inc(v_s_5746_);
lean_inc(v_H_5745_);
lean_inc(v_k_5744_);
lean_inc(v_K_5743_);
lean_inc(v_h_5742_);
lean_inc(v_B_5741_);
lean_inc(v_b_5740_);
lean_inc(v_a_5739_);
lean_inc(v_F_5738_);
lean_inc(v_c_5737_);
lean_inc(v_e_5736_);
lean_inc(v_E_5735_);
lean_inc(v_W_5734_);
lean_inc(v_w_5733_);
lean_inc(v_q_5732_);
lean_inc(v_Q_5731_);
lean_inc(v_d_5730_);
lean_inc(v_L_5729_);
lean_inc(v_M_5728_);
lean_inc(v_D_5727_);
lean_inc(v_Y_5726_);
lean_inc(v_u_5725_);
lean_inc(v_y_5724_);
lean_inc(v_G_5723_);
lean_dec(v_date_4556_);
v___x_5760_ = lean_box(0);
v_isShared_5761_ = v_isSharedCheck_5768_;
goto v_resetjp_5759_;
}
v_resetjp_5759_:
{
lean_object* v___x_5763_; 
if (v_isShared_5722_ == 0)
{
lean_ctor_set_tag(v___x_5721_, 1);
lean_ctor_set(v___x_5721_, 0, v_data_4558_);
v___x_5763_ = v___x_5721_;
goto v_reusejp_5762_;
}
else
{
lean_object* v_reuseFailAlloc_5767_; 
v_reuseFailAlloc_5767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5767_, 0, v_data_4558_);
v___x_5763_ = v_reuseFailAlloc_5767_;
goto v_reusejp_5762_;
}
v_reusejp_5762_:
{
lean_object* v___x_5765_; 
if (v_isShared_5761_ == 0)
{
lean_ctor_set(v___x_5760_, 23, v___x_5763_);
v___x_5765_ = v___x_5760_;
goto v_reusejp_5764_;
}
else
{
lean_object* v_reuseFailAlloc_5766_; 
v_reuseFailAlloc_5766_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5766_, 0, v_G_5723_);
lean_ctor_set(v_reuseFailAlloc_5766_, 1, v_y_5724_);
lean_ctor_set(v_reuseFailAlloc_5766_, 2, v_u_5725_);
lean_ctor_set(v_reuseFailAlloc_5766_, 3, v_Y_5726_);
lean_ctor_set(v_reuseFailAlloc_5766_, 4, v_D_5727_);
lean_ctor_set(v_reuseFailAlloc_5766_, 5, v_M_5728_);
lean_ctor_set(v_reuseFailAlloc_5766_, 6, v_L_5729_);
lean_ctor_set(v_reuseFailAlloc_5766_, 7, v_d_5730_);
lean_ctor_set(v_reuseFailAlloc_5766_, 8, v_Q_5731_);
lean_ctor_set(v_reuseFailAlloc_5766_, 9, v_q_5732_);
lean_ctor_set(v_reuseFailAlloc_5766_, 10, v_w_5733_);
lean_ctor_set(v_reuseFailAlloc_5766_, 11, v_W_5734_);
lean_ctor_set(v_reuseFailAlloc_5766_, 12, v_E_5735_);
lean_ctor_set(v_reuseFailAlloc_5766_, 13, v_e_5736_);
lean_ctor_set(v_reuseFailAlloc_5766_, 14, v_c_5737_);
lean_ctor_set(v_reuseFailAlloc_5766_, 15, v_F_5738_);
lean_ctor_set(v_reuseFailAlloc_5766_, 16, v_a_5739_);
lean_ctor_set(v_reuseFailAlloc_5766_, 17, v_b_5740_);
lean_ctor_set(v_reuseFailAlloc_5766_, 18, v_B_5741_);
lean_ctor_set(v_reuseFailAlloc_5766_, 19, v_h_5742_);
lean_ctor_set(v_reuseFailAlloc_5766_, 20, v_K_5743_);
lean_ctor_set(v_reuseFailAlloc_5766_, 21, v_k_5744_);
lean_ctor_set(v_reuseFailAlloc_5766_, 22, v_H_5745_);
lean_ctor_set(v_reuseFailAlloc_5766_, 23, v___x_5763_);
lean_ctor_set(v_reuseFailAlloc_5766_, 24, v_s_5746_);
lean_ctor_set(v_reuseFailAlloc_5766_, 25, v_S_5747_);
lean_ctor_set(v_reuseFailAlloc_5766_, 26, v_A_5748_);
lean_ctor_set(v_reuseFailAlloc_5766_, 27, v_n_5749_);
lean_ctor_set(v_reuseFailAlloc_5766_, 28, v_N_5750_);
lean_ctor_set(v_reuseFailAlloc_5766_, 29, v_V_5751_);
lean_ctor_set(v_reuseFailAlloc_5766_, 30, v_z_5752_);
lean_ctor_set(v_reuseFailAlloc_5766_, 31, v_zabbrev_5753_);
lean_ctor_set(v_reuseFailAlloc_5766_, 32, v_v_5754_);
lean_ctor_set(v_reuseFailAlloc_5766_, 33, v_O_5755_);
lean_ctor_set(v_reuseFailAlloc_5766_, 34, v_X_5756_);
lean_ctor_set(v_reuseFailAlloc_5766_, 35, v_x_5757_);
lean_ctor_set(v_reuseFailAlloc_5766_, 36, v_Z_5758_);
v___x_5765_ = v_reuseFailAlloc_5766_;
goto v_reusejp_5764_;
}
v_reusejp_5764_:
{
return v___x_5765_;
}
}
}
}
}
case 24:
{
lean_object* v___x_5773_; uint8_t v_isShared_5774_; uint8_t v_isSharedCheck_5822_; 
v_isSharedCheck_5822_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_5822_ == 0)
{
lean_object* v_unused_5823_; 
v_unused_5823_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_5823_);
v___x_5773_ = v_modifier_4557_;
v_isShared_5774_ = v_isSharedCheck_5822_;
goto v_resetjp_5772_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_5773_ = lean_box(0);
v_isShared_5774_ = v_isSharedCheck_5822_;
goto v_resetjp_5772_;
}
v_resetjp_5772_:
{
lean_object* v_G_5775_; lean_object* v_y_5776_; lean_object* v_u_5777_; lean_object* v_Y_5778_; lean_object* v_D_5779_; lean_object* v_M_5780_; lean_object* v_L_5781_; lean_object* v_d_5782_; lean_object* v_Q_5783_; lean_object* v_q_5784_; lean_object* v_w_5785_; lean_object* v_W_5786_; lean_object* v_E_5787_; lean_object* v_e_5788_; lean_object* v_c_5789_; lean_object* v_F_5790_; lean_object* v_a_5791_; lean_object* v_b_5792_; lean_object* v_B_5793_; lean_object* v_h_5794_; lean_object* v_K_5795_; lean_object* v_k_5796_; lean_object* v_H_5797_; lean_object* v_m_5798_; lean_object* v_S_5799_; lean_object* v_A_5800_; lean_object* v_n_5801_; lean_object* v_N_5802_; lean_object* v_V_5803_; lean_object* v_z_5804_; lean_object* v_zabbrev_5805_; lean_object* v_v_5806_; lean_object* v_O_5807_; lean_object* v_X_5808_; lean_object* v_x_5809_; lean_object* v_Z_5810_; lean_object* v___x_5812_; uint8_t v_isShared_5813_; uint8_t v_isSharedCheck_5820_; 
v_G_5775_ = lean_ctor_get(v_date_4556_, 0);
v_y_5776_ = lean_ctor_get(v_date_4556_, 1);
v_u_5777_ = lean_ctor_get(v_date_4556_, 2);
v_Y_5778_ = lean_ctor_get(v_date_4556_, 3);
v_D_5779_ = lean_ctor_get(v_date_4556_, 4);
v_M_5780_ = lean_ctor_get(v_date_4556_, 5);
v_L_5781_ = lean_ctor_get(v_date_4556_, 6);
v_d_5782_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5783_ = lean_ctor_get(v_date_4556_, 8);
v_q_5784_ = lean_ctor_get(v_date_4556_, 9);
v_w_5785_ = lean_ctor_get(v_date_4556_, 10);
v_W_5786_ = lean_ctor_get(v_date_4556_, 11);
v_E_5787_ = lean_ctor_get(v_date_4556_, 12);
v_e_5788_ = lean_ctor_get(v_date_4556_, 13);
v_c_5789_ = lean_ctor_get(v_date_4556_, 14);
v_F_5790_ = lean_ctor_get(v_date_4556_, 15);
v_a_5791_ = lean_ctor_get(v_date_4556_, 16);
v_b_5792_ = lean_ctor_get(v_date_4556_, 17);
v_B_5793_ = lean_ctor_get(v_date_4556_, 18);
v_h_5794_ = lean_ctor_get(v_date_4556_, 19);
v_K_5795_ = lean_ctor_get(v_date_4556_, 20);
v_k_5796_ = lean_ctor_get(v_date_4556_, 21);
v_H_5797_ = lean_ctor_get(v_date_4556_, 22);
v_m_5798_ = lean_ctor_get(v_date_4556_, 23);
v_S_5799_ = lean_ctor_get(v_date_4556_, 25);
v_A_5800_ = lean_ctor_get(v_date_4556_, 26);
v_n_5801_ = lean_ctor_get(v_date_4556_, 27);
v_N_5802_ = lean_ctor_get(v_date_4556_, 28);
v_V_5803_ = lean_ctor_get(v_date_4556_, 29);
v_z_5804_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5805_ = lean_ctor_get(v_date_4556_, 31);
v_v_5806_ = lean_ctor_get(v_date_4556_, 32);
v_O_5807_ = lean_ctor_get(v_date_4556_, 33);
v_X_5808_ = lean_ctor_get(v_date_4556_, 34);
v_x_5809_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5810_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5820_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5820_ == 0)
{
lean_object* v_unused_5821_; 
v_unused_5821_ = lean_ctor_get(v_date_4556_, 24);
lean_dec(v_unused_5821_);
v___x_5812_ = v_date_4556_;
v_isShared_5813_ = v_isSharedCheck_5820_;
goto v_resetjp_5811_;
}
else
{
lean_inc(v_Z_5810_);
lean_inc(v_x_5809_);
lean_inc(v_X_5808_);
lean_inc(v_O_5807_);
lean_inc(v_v_5806_);
lean_inc(v_zabbrev_5805_);
lean_inc(v_z_5804_);
lean_inc(v_V_5803_);
lean_inc(v_N_5802_);
lean_inc(v_n_5801_);
lean_inc(v_A_5800_);
lean_inc(v_S_5799_);
lean_inc(v_m_5798_);
lean_inc(v_H_5797_);
lean_inc(v_k_5796_);
lean_inc(v_K_5795_);
lean_inc(v_h_5794_);
lean_inc(v_B_5793_);
lean_inc(v_b_5792_);
lean_inc(v_a_5791_);
lean_inc(v_F_5790_);
lean_inc(v_c_5789_);
lean_inc(v_e_5788_);
lean_inc(v_E_5787_);
lean_inc(v_W_5786_);
lean_inc(v_w_5785_);
lean_inc(v_q_5784_);
lean_inc(v_Q_5783_);
lean_inc(v_d_5782_);
lean_inc(v_L_5781_);
lean_inc(v_M_5780_);
lean_inc(v_D_5779_);
lean_inc(v_Y_5778_);
lean_inc(v_u_5777_);
lean_inc(v_y_5776_);
lean_inc(v_G_5775_);
lean_dec(v_date_4556_);
v___x_5812_ = lean_box(0);
v_isShared_5813_ = v_isSharedCheck_5820_;
goto v_resetjp_5811_;
}
v_resetjp_5811_:
{
lean_object* v___x_5815_; 
if (v_isShared_5774_ == 0)
{
lean_ctor_set_tag(v___x_5773_, 1);
lean_ctor_set(v___x_5773_, 0, v_data_4558_);
v___x_5815_ = v___x_5773_;
goto v_reusejp_5814_;
}
else
{
lean_object* v_reuseFailAlloc_5819_; 
v_reuseFailAlloc_5819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5819_, 0, v_data_4558_);
v___x_5815_ = v_reuseFailAlloc_5819_;
goto v_reusejp_5814_;
}
v_reusejp_5814_:
{
lean_object* v___x_5817_; 
if (v_isShared_5813_ == 0)
{
lean_ctor_set(v___x_5812_, 24, v___x_5815_);
v___x_5817_ = v___x_5812_;
goto v_reusejp_5816_;
}
else
{
lean_object* v_reuseFailAlloc_5818_; 
v_reuseFailAlloc_5818_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5818_, 0, v_G_5775_);
lean_ctor_set(v_reuseFailAlloc_5818_, 1, v_y_5776_);
lean_ctor_set(v_reuseFailAlloc_5818_, 2, v_u_5777_);
lean_ctor_set(v_reuseFailAlloc_5818_, 3, v_Y_5778_);
lean_ctor_set(v_reuseFailAlloc_5818_, 4, v_D_5779_);
lean_ctor_set(v_reuseFailAlloc_5818_, 5, v_M_5780_);
lean_ctor_set(v_reuseFailAlloc_5818_, 6, v_L_5781_);
lean_ctor_set(v_reuseFailAlloc_5818_, 7, v_d_5782_);
lean_ctor_set(v_reuseFailAlloc_5818_, 8, v_Q_5783_);
lean_ctor_set(v_reuseFailAlloc_5818_, 9, v_q_5784_);
lean_ctor_set(v_reuseFailAlloc_5818_, 10, v_w_5785_);
lean_ctor_set(v_reuseFailAlloc_5818_, 11, v_W_5786_);
lean_ctor_set(v_reuseFailAlloc_5818_, 12, v_E_5787_);
lean_ctor_set(v_reuseFailAlloc_5818_, 13, v_e_5788_);
lean_ctor_set(v_reuseFailAlloc_5818_, 14, v_c_5789_);
lean_ctor_set(v_reuseFailAlloc_5818_, 15, v_F_5790_);
lean_ctor_set(v_reuseFailAlloc_5818_, 16, v_a_5791_);
lean_ctor_set(v_reuseFailAlloc_5818_, 17, v_b_5792_);
lean_ctor_set(v_reuseFailAlloc_5818_, 18, v_B_5793_);
lean_ctor_set(v_reuseFailAlloc_5818_, 19, v_h_5794_);
lean_ctor_set(v_reuseFailAlloc_5818_, 20, v_K_5795_);
lean_ctor_set(v_reuseFailAlloc_5818_, 21, v_k_5796_);
lean_ctor_set(v_reuseFailAlloc_5818_, 22, v_H_5797_);
lean_ctor_set(v_reuseFailAlloc_5818_, 23, v_m_5798_);
lean_ctor_set(v_reuseFailAlloc_5818_, 24, v___x_5815_);
lean_ctor_set(v_reuseFailAlloc_5818_, 25, v_S_5799_);
lean_ctor_set(v_reuseFailAlloc_5818_, 26, v_A_5800_);
lean_ctor_set(v_reuseFailAlloc_5818_, 27, v_n_5801_);
lean_ctor_set(v_reuseFailAlloc_5818_, 28, v_N_5802_);
lean_ctor_set(v_reuseFailAlloc_5818_, 29, v_V_5803_);
lean_ctor_set(v_reuseFailAlloc_5818_, 30, v_z_5804_);
lean_ctor_set(v_reuseFailAlloc_5818_, 31, v_zabbrev_5805_);
lean_ctor_set(v_reuseFailAlloc_5818_, 32, v_v_5806_);
lean_ctor_set(v_reuseFailAlloc_5818_, 33, v_O_5807_);
lean_ctor_set(v_reuseFailAlloc_5818_, 34, v_X_5808_);
lean_ctor_set(v_reuseFailAlloc_5818_, 35, v_x_5809_);
lean_ctor_set(v_reuseFailAlloc_5818_, 36, v_Z_5810_);
v___x_5817_ = v_reuseFailAlloc_5818_;
goto v_reusejp_5816_;
}
v_reusejp_5816_:
{
return v___x_5817_;
}
}
}
}
}
case 25:
{
lean_object* v___x_5825_; uint8_t v_isShared_5826_; uint8_t v_isSharedCheck_5874_; 
v_isSharedCheck_5874_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_5874_ == 0)
{
lean_object* v_unused_5875_; 
v_unused_5875_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_5875_);
v___x_5825_ = v_modifier_4557_;
v_isShared_5826_ = v_isSharedCheck_5874_;
goto v_resetjp_5824_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_5825_ = lean_box(0);
v_isShared_5826_ = v_isSharedCheck_5874_;
goto v_resetjp_5824_;
}
v_resetjp_5824_:
{
lean_object* v_G_5827_; lean_object* v_y_5828_; lean_object* v_u_5829_; lean_object* v_Y_5830_; lean_object* v_D_5831_; lean_object* v_M_5832_; lean_object* v_L_5833_; lean_object* v_d_5834_; lean_object* v_Q_5835_; lean_object* v_q_5836_; lean_object* v_w_5837_; lean_object* v_W_5838_; lean_object* v_E_5839_; lean_object* v_e_5840_; lean_object* v_c_5841_; lean_object* v_F_5842_; lean_object* v_a_5843_; lean_object* v_b_5844_; lean_object* v_B_5845_; lean_object* v_h_5846_; lean_object* v_K_5847_; lean_object* v_k_5848_; lean_object* v_H_5849_; lean_object* v_m_5850_; lean_object* v_s_5851_; lean_object* v_A_5852_; lean_object* v_n_5853_; lean_object* v_N_5854_; lean_object* v_V_5855_; lean_object* v_z_5856_; lean_object* v_zabbrev_5857_; lean_object* v_v_5858_; lean_object* v_O_5859_; lean_object* v_X_5860_; lean_object* v_x_5861_; lean_object* v_Z_5862_; lean_object* v___x_5864_; uint8_t v_isShared_5865_; uint8_t v_isSharedCheck_5872_; 
v_G_5827_ = lean_ctor_get(v_date_4556_, 0);
v_y_5828_ = lean_ctor_get(v_date_4556_, 1);
v_u_5829_ = lean_ctor_get(v_date_4556_, 2);
v_Y_5830_ = lean_ctor_get(v_date_4556_, 3);
v_D_5831_ = lean_ctor_get(v_date_4556_, 4);
v_M_5832_ = lean_ctor_get(v_date_4556_, 5);
v_L_5833_ = lean_ctor_get(v_date_4556_, 6);
v_d_5834_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5835_ = lean_ctor_get(v_date_4556_, 8);
v_q_5836_ = lean_ctor_get(v_date_4556_, 9);
v_w_5837_ = lean_ctor_get(v_date_4556_, 10);
v_W_5838_ = lean_ctor_get(v_date_4556_, 11);
v_E_5839_ = lean_ctor_get(v_date_4556_, 12);
v_e_5840_ = lean_ctor_get(v_date_4556_, 13);
v_c_5841_ = lean_ctor_get(v_date_4556_, 14);
v_F_5842_ = lean_ctor_get(v_date_4556_, 15);
v_a_5843_ = lean_ctor_get(v_date_4556_, 16);
v_b_5844_ = lean_ctor_get(v_date_4556_, 17);
v_B_5845_ = lean_ctor_get(v_date_4556_, 18);
v_h_5846_ = lean_ctor_get(v_date_4556_, 19);
v_K_5847_ = lean_ctor_get(v_date_4556_, 20);
v_k_5848_ = lean_ctor_get(v_date_4556_, 21);
v_H_5849_ = lean_ctor_get(v_date_4556_, 22);
v_m_5850_ = lean_ctor_get(v_date_4556_, 23);
v_s_5851_ = lean_ctor_get(v_date_4556_, 24);
v_A_5852_ = lean_ctor_get(v_date_4556_, 26);
v_n_5853_ = lean_ctor_get(v_date_4556_, 27);
v_N_5854_ = lean_ctor_get(v_date_4556_, 28);
v_V_5855_ = lean_ctor_get(v_date_4556_, 29);
v_z_5856_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5857_ = lean_ctor_get(v_date_4556_, 31);
v_v_5858_ = lean_ctor_get(v_date_4556_, 32);
v_O_5859_ = lean_ctor_get(v_date_4556_, 33);
v_X_5860_ = lean_ctor_get(v_date_4556_, 34);
v_x_5861_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5862_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5872_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5872_ == 0)
{
lean_object* v_unused_5873_; 
v_unused_5873_ = lean_ctor_get(v_date_4556_, 25);
lean_dec(v_unused_5873_);
v___x_5864_ = v_date_4556_;
v_isShared_5865_ = v_isSharedCheck_5872_;
goto v_resetjp_5863_;
}
else
{
lean_inc(v_Z_5862_);
lean_inc(v_x_5861_);
lean_inc(v_X_5860_);
lean_inc(v_O_5859_);
lean_inc(v_v_5858_);
lean_inc(v_zabbrev_5857_);
lean_inc(v_z_5856_);
lean_inc(v_V_5855_);
lean_inc(v_N_5854_);
lean_inc(v_n_5853_);
lean_inc(v_A_5852_);
lean_inc(v_s_5851_);
lean_inc(v_m_5850_);
lean_inc(v_H_5849_);
lean_inc(v_k_5848_);
lean_inc(v_K_5847_);
lean_inc(v_h_5846_);
lean_inc(v_B_5845_);
lean_inc(v_b_5844_);
lean_inc(v_a_5843_);
lean_inc(v_F_5842_);
lean_inc(v_c_5841_);
lean_inc(v_e_5840_);
lean_inc(v_E_5839_);
lean_inc(v_W_5838_);
lean_inc(v_w_5837_);
lean_inc(v_q_5836_);
lean_inc(v_Q_5835_);
lean_inc(v_d_5834_);
lean_inc(v_L_5833_);
lean_inc(v_M_5832_);
lean_inc(v_D_5831_);
lean_inc(v_Y_5830_);
lean_inc(v_u_5829_);
lean_inc(v_y_5828_);
lean_inc(v_G_5827_);
lean_dec(v_date_4556_);
v___x_5864_ = lean_box(0);
v_isShared_5865_ = v_isSharedCheck_5872_;
goto v_resetjp_5863_;
}
v_resetjp_5863_:
{
lean_object* v___x_5867_; 
if (v_isShared_5826_ == 0)
{
lean_ctor_set_tag(v___x_5825_, 1);
lean_ctor_set(v___x_5825_, 0, v_data_4558_);
v___x_5867_ = v___x_5825_;
goto v_reusejp_5866_;
}
else
{
lean_object* v_reuseFailAlloc_5871_; 
v_reuseFailAlloc_5871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5871_, 0, v_data_4558_);
v___x_5867_ = v_reuseFailAlloc_5871_;
goto v_reusejp_5866_;
}
v_reusejp_5866_:
{
lean_object* v___x_5869_; 
if (v_isShared_5865_ == 0)
{
lean_ctor_set(v___x_5864_, 25, v___x_5867_);
v___x_5869_ = v___x_5864_;
goto v_reusejp_5868_;
}
else
{
lean_object* v_reuseFailAlloc_5870_; 
v_reuseFailAlloc_5870_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5870_, 0, v_G_5827_);
lean_ctor_set(v_reuseFailAlloc_5870_, 1, v_y_5828_);
lean_ctor_set(v_reuseFailAlloc_5870_, 2, v_u_5829_);
lean_ctor_set(v_reuseFailAlloc_5870_, 3, v_Y_5830_);
lean_ctor_set(v_reuseFailAlloc_5870_, 4, v_D_5831_);
lean_ctor_set(v_reuseFailAlloc_5870_, 5, v_M_5832_);
lean_ctor_set(v_reuseFailAlloc_5870_, 6, v_L_5833_);
lean_ctor_set(v_reuseFailAlloc_5870_, 7, v_d_5834_);
lean_ctor_set(v_reuseFailAlloc_5870_, 8, v_Q_5835_);
lean_ctor_set(v_reuseFailAlloc_5870_, 9, v_q_5836_);
lean_ctor_set(v_reuseFailAlloc_5870_, 10, v_w_5837_);
lean_ctor_set(v_reuseFailAlloc_5870_, 11, v_W_5838_);
lean_ctor_set(v_reuseFailAlloc_5870_, 12, v_E_5839_);
lean_ctor_set(v_reuseFailAlloc_5870_, 13, v_e_5840_);
lean_ctor_set(v_reuseFailAlloc_5870_, 14, v_c_5841_);
lean_ctor_set(v_reuseFailAlloc_5870_, 15, v_F_5842_);
lean_ctor_set(v_reuseFailAlloc_5870_, 16, v_a_5843_);
lean_ctor_set(v_reuseFailAlloc_5870_, 17, v_b_5844_);
lean_ctor_set(v_reuseFailAlloc_5870_, 18, v_B_5845_);
lean_ctor_set(v_reuseFailAlloc_5870_, 19, v_h_5846_);
lean_ctor_set(v_reuseFailAlloc_5870_, 20, v_K_5847_);
lean_ctor_set(v_reuseFailAlloc_5870_, 21, v_k_5848_);
lean_ctor_set(v_reuseFailAlloc_5870_, 22, v_H_5849_);
lean_ctor_set(v_reuseFailAlloc_5870_, 23, v_m_5850_);
lean_ctor_set(v_reuseFailAlloc_5870_, 24, v_s_5851_);
lean_ctor_set(v_reuseFailAlloc_5870_, 25, v___x_5867_);
lean_ctor_set(v_reuseFailAlloc_5870_, 26, v_A_5852_);
lean_ctor_set(v_reuseFailAlloc_5870_, 27, v_n_5853_);
lean_ctor_set(v_reuseFailAlloc_5870_, 28, v_N_5854_);
lean_ctor_set(v_reuseFailAlloc_5870_, 29, v_V_5855_);
lean_ctor_set(v_reuseFailAlloc_5870_, 30, v_z_5856_);
lean_ctor_set(v_reuseFailAlloc_5870_, 31, v_zabbrev_5857_);
lean_ctor_set(v_reuseFailAlloc_5870_, 32, v_v_5858_);
lean_ctor_set(v_reuseFailAlloc_5870_, 33, v_O_5859_);
lean_ctor_set(v_reuseFailAlloc_5870_, 34, v_X_5860_);
lean_ctor_set(v_reuseFailAlloc_5870_, 35, v_x_5861_);
lean_ctor_set(v_reuseFailAlloc_5870_, 36, v_Z_5862_);
v___x_5869_ = v_reuseFailAlloc_5870_;
goto v_reusejp_5868_;
}
v_reusejp_5868_:
{
return v___x_5869_;
}
}
}
}
}
case 26:
{
lean_object* v___x_5877_; uint8_t v_isShared_5878_; uint8_t v_isSharedCheck_5926_; 
v_isSharedCheck_5926_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_5926_ == 0)
{
lean_object* v_unused_5927_; 
v_unused_5927_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_5927_);
v___x_5877_ = v_modifier_4557_;
v_isShared_5878_ = v_isSharedCheck_5926_;
goto v_resetjp_5876_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_5877_ = lean_box(0);
v_isShared_5878_ = v_isSharedCheck_5926_;
goto v_resetjp_5876_;
}
v_resetjp_5876_:
{
lean_object* v_G_5879_; lean_object* v_y_5880_; lean_object* v_u_5881_; lean_object* v_Y_5882_; lean_object* v_D_5883_; lean_object* v_M_5884_; lean_object* v_L_5885_; lean_object* v_d_5886_; lean_object* v_Q_5887_; lean_object* v_q_5888_; lean_object* v_w_5889_; lean_object* v_W_5890_; lean_object* v_E_5891_; lean_object* v_e_5892_; lean_object* v_c_5893_; lean_object* v_F_5894_; lean_object* v_a_5895_; lean_object* v_b_5896_; lean_object* v_B_5897_; lean_object* v_h_5898_; lean_object* v_K_5899_; lean_object* v_k_5900_; lean_object* v_H_5901_; lean_object* v_m_5902_; lean_object* v_s_5903_; lean_object* v_S_5904_; lean_object* v_n_5905_; lean_object* v_N_5906_; lean_object* v_V_5907_; lean_object* v_z_5908_; lean_object* v_zabbrev_5909_; lean_object* v_v_5910_; lean_object* v_O_5911_; lean_object* v_X_5912_; lean_object* v_x_5913_; lean_object* v_Z_5914_; lean_object* v___x_5916_; uint8_t v_isShared_5917_; uint8_t v_isSharedCheck_5924_; 
v_G_5879_ = lean_ctor_get(v_date_4556_, 0);
v_y_5880_ = lean_ctor_get(v_date_4556_, 1);
v_u_5881_ = lean_ctor_get(v_date_4556_, 2);
v_Y_5882_ = lean_ctor_get(v_date_4556_, 3);
v_D_5883_ = lean_ctor_get(v_date_4556_, 4);
v_M_5884_ = lean_ctor_get(v_date_4556_, 5);
v_L_5885_ = lean_ctor_get(v_date_4556_, 6);
v_d_5886_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5887_ = lean_ctor_get(v_date_4556_, 8);
v_q_5888_ = lean_ctor_get(v_date_4556_, 9);
v_w_5889_ = lean_ctor_get(v_date_4556_, 10);
v_W_5890_ = lean_ctor_get(v_date_4556_, 11);
v_E_5891_ = lean_ctor_get(v_date_4556_, 12);
v_e_5892_ = lean_ctor_get(v_date_4556_, 13);
v_c_5893_ = lean_ctor_get(v_date_4556_, 14);
v_F_5894_ = lean_ctor_get(v_date_4556_, 15);
v_a_5895_ = lean_ctor_get(v_date_4556_, 16);
v_b_5896_ = lean_ctor_get(v_date_4556_, 17);
v_B_5897_ = lean_ctor_get(v_date_4556_, 18);
v_h_5898_ = lean_ctor_get(v_date_4556_, 19);
v_K_5899_ = lean_ctor_get(v_date_4556_, 20);
v_k_5900_ = lean_ctor_get(v_date_4556_, 21);
v_H_5901_ = lean_ctor_get(v_date_4556_, 22);
v_m_5902_ = lean_ctor_get(v_date_4556_, 23);
v_s_5903_ = lean_ctor_get(v_date_4556_, 24);
v_S_5904_ = lean_ctor_get(v_date_4556_, 25);
v_n_5905_ = lean_ctor_get(v_date_4556_, 27);
v_N_5906_ = lean_ctor_get(v_date_4556_, 28);
v_V_5907_ = lean_ctor_get(v_date_4556_, 29);
v_z_5908_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5909_ = lean_ctor_get(v_date_4556_, 31);
v_v_5910_ = lean_ctor_get(v_date_4556_, 32);
v_O_5911_ = lean_ctor_get(v_date_4556_, 33);
v_X_5912_ = lean_ctor_get(v_date_4556_, 34);
v_x_5913_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5914_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5924_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5924_ == 0)
{
lean_object* v_unused_5925_; 
v_unused_5925_ = lean_ctor_get(v_date_4556_, 26);
lean_dec(v_unused_5925_);
v___x_5916_ = v_date_4556_;
v_isShared_5917_ = v_isSharedCheck_5924_;
goto v_resetjp_5915_;
}
else
{
lean_inc(v_Z_5914_);
lean_inc(v_x_5913_);
lean_inc(v_X_5912_);
lean_inc(v_O_5911_);
lean_inc(v_v_5910_);
lean_inc(v_zabbrev_5909_);
lean_inc(v_z_5908_);
lean_inc(v_V_5907_);
lean_inc(v_N_5906_);
lean_inc(v_n_5905_);
lean_inc(v_S_5904_);
lean_inc(v_s_5903_);
lean_inc(v_m_5902_);
lean_inc(v_H_5901_);
lean_inc(v_k_5900_);
lean_inc(v_K_5899_);
lean_inc(v_h_5898_);
lean_inc(v_B_5897_);
lean_inc(v_b_5896_);
lean_inc(v_a_5895_);
lean_inc(v_F_5894_);
lean_inc(v_c_5893_);
lean_inc(v_e_5892_);
lean_inc(v_E_5891_);
lean_inc(v_W_5890_);
lean_inc(v_w_5889_);
lean_inc(v_q_5888_);
lean_inc(v_Q_5887_);
lean_inc(v_d_5886_);
lean_inc(v_L_5885_);
lean_inc(v_M_5884_);
lean_inc(v_D_5883_);
lean_inc(v_Y_5882_);
lean_inc(v_u_5881_);
lean_inc(v_y_5880_);
lean_inc(v_G_5879_);
lean_dec(v_date_4556_);
v___x_5916_ = lean_box(0);
v_isShared_5917_ = v_isSharedCheck_5924_;
goto v_resetjp_5915_;
}
v_resetjp_5915_:
{
lean_object* v___x_5919_; 
if (v_isShared_5878_ == 0)
{
lean_ctor_set_tag(v___x_5877_, 1);
lean_ctor_set(v___x_5877_, 0, v_data_4558_);
v___x_5919_ = v___x_5877_;
goto v_reusejp_5918_;
}
else
{
lean_object* v_reuseFailAlloc_5923_; 
v_reuseFailAlloc_5923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5923_, 0, v_data_4558_);
v___x_5919_ = v_reuseFailAlloc_5923_;
goto v_reusejp_5918_;
}
v_reusejp_5918_:
{
lean_object* v___x_5921_; 
if (v_isShared_5917_ == 0)
{
lean_ctor_set(v___x_5916_, 26, v___x_5919_);
v___x_5921_ = v___x_5916_;
goto v_reusejp_5920_;
}
else
{
lean_object* v_reuseFailAlloc_5922_; 
v_reuseFailAlloc_5922_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5922_, 0, v_G_5879_);
lean_ctor_set(v_reuseFailAlloc_5922_, 1, v_y_5880_);
lean_ctor_set(v_reuseFailAlloc_5922_, 2, v_u_5881_);
lean_ctor_set(v_reuseFailAlloc_5922_, 3, v_Y_5882_);
lean_ctor_set(v_reuseFailAlloc_5922_, 4, v_D_5883_);
lean_ctor_set(v_reuseFailAlloc_5922_, 5, v_M_5884_);
lean_ctor_set(v_reuseFailAlloc_5922_, 6, v_L_5885_);
lean_ctor_set(v_reuseFailAlloc_5922_, 7, v_d_5886_);
lean_ctor_set(v_reuseFailAlloc_5922_, 8, v_Q_5887_);
lean_ctor_set(v_reuseFailAlloc_5922_, 9, v_q_5888_);
lean_ctor_set(v_reuseFailAlloc_5922_, 10, v_w_5889_);
lean_ctor_set(v_reuseFailAlloc_5922_, 11, v_W_5890_);
lean_ctor_set(v_reuseFailAlloc_5922_, 12, v_E_5891_);
lean_ctor_set(v_reuseFailAlloc_5922_, 13, v_e_5892_);
lean_ctor_set(v_reuseFailAlloc_5922_, 14, v_c_5893_);
lean_ctor_set(v_reuseFailAlloc_5922_, 15, v_F_5894_);
lean_ctor_set(v_reuseFailAlloc_5922_, 16, v_a_5895_);
lean_ctor_set(v_reuseFailAlloc_5922_, 17, v_b_5896_);
lean_ctor_set(v_reuseFailAlloc_5922_, 18, v_B_5897_);
lean_ctor_set(v_reuseFailAlloc_5922_, 19, v_h_5898_);
lean_ctor_set(v_reuseFailAlloc_5922_, 20, v_K_5899_);
lean_ctor_set(v_reuseFailAlloc_5922_, 21, v_k_5900_);
lean_ctor_set(v_reuseFailAlloc_5922_, 22, v_H_5901_);
lean_ctor_set(v_reuseFailAlloc_5922_, 23, v_m_5902_);
lean_ctor_set(v_reuseFailAlloc_5922_, 24, v_s_5903_);
lean_ctor_set(v_reuseFailAlloc_5922_, 25, v_S_5904_);
lean_ctor_set(v_reuseFailAlloc_5922_, 26, v___x_5919_);
lean_ctor_set(v_reuseFailAlloc_5922_, 27, v_n_5905_);
lean_ctor_set(v_reuseFailAlloc_5922_, 28, v_N_5906_);
lean_ctor_set(v_reuseFailAlloc_5922_, 29, v_V_5907_);
lean_ctor_set(v_reuseFailAlloc_5922_, 30, v_z_5908_);
lean_ctor_set(v_reuseFailAlloc_5922_, 31, v_zabbrev_5909_);
lean_ctor_set(v_reuseFailAlloc_5922_, 32, v_v_5910_);
lean_ctor_set(v_reuseFailAlloc_5922_, 33, v_O_5911_);
lean_ctor_set(v_reuseFailAlloc_5922_, 34, v_X_5912_);
lean_ctor_set(v_reuseFailAlloc_5922_, 35, v_x_5913_);
lean_ctor_set(v_reuseFailAlloc_5922_, 36, v_Z_5914_);
v___x_5921_ = v_reuseFailAlloc_5922_;
goto v_reusejp_5920_;
}
v_reusejp_5920_:
{
return v___x_5921_;
}
}
}
}
}
case 27:
{
lean_object* v___x_5929_; uint8_t v_isShared_5930_; uint8_t v_isSharedCheck_5978_; 
v_isSharedCheck_5978_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_5978_ == 0)
{
lean_object* v_unused_5979_; 
v_unused_5979_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_5979_);
v___x_5929_ = v_modifier_4557_;
v_isShared_5930_ = v_isSharedCheck_5978_;
goto v_resetjp_5928_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_5929_ = lean_box(0);
v_isShared_5930_ = v_isSharedCheck_5978_;
goto v_resetjp_5928_;
}
v_resetjp_5928_:
{
lean_object* v_G_5931_; lean_object* v_y_5932_; lean_object* v_u_5933_; lean_object* v_Y_5934_; lean_object* v_D_5935_; lean_object* v_M_5936_; lean_object* v_L_5937_; lean_object* v_d_5938_; lean_object* v_Q_5939_; lean_object* v_q_5940_; lean_object* v_w_5941_; lean_object* v_W_5942_; lean_object* v_E_5943_; lean_object* v_e_5944_; lean_object* v_c_5945_; lean_object* v_F_5946_; lean_object* v_a_5947_; lean_object* v_b_5948_; lean_object* v_B_5949_; lean_object* v_h_5950_; lean_object* v_K_5951_; lean_object* v_k_5952_; lean_object* v_H_5953_; lean_object* v_m_5954_; lean_object* v_s_5955_; lean_object* v_S_5956_; lean_object* v_A_5957_; lean_object* v_N_5958_; lean_object* v_V_5959_; lean_object* v_z_5960_; lean_object* v_zabbrev_5961_; lean_object* v_v_5962_; lean_object* v_O_5963_; lean_object* v_X_5964_; lean_object* v_x_5965_; lean_object* v_Z_5966_; lean_object* v___x_5968_; uint8_t v_isShared_5969_; uint8_t v_isSharedCheck_5976_; 
v_G_5931_ = lean_ctor_get(v_date_4556_, 0);
v_y_5932_ = lean_ctor_get(v_date_4556_, 1);
v_u_5933_ = lean_ctor_get(v_date_4556_, 2);
v_Y_5934_ = lean_ctor_get(v_date_4556_, 3);
v_D_5935_ = lean_ctor_get(v_date_4556_, 4);
v_M_5936_ = lean_ctor_get(v_date_4556_, 5);
v_L_5937_ = lean_ctor_get(v_date_4556_, 6);
v_d_5938_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5939_ = lean_ctor_get(v_date_4556_, 8);
v_q_5940_ = lean_ctor_get(v_date_4556_, 9);
v_w_5941_ = lean_ctor_get(v_date_4556_, 10);
v_W_5942_ = lean_ctor_get(v_date_4556_, 11);
v_E_5943_ = lean_ctor_get(v_date_4556_, 12);
v_e_5944_ = lean_ctor_get(v_date_4556_, 13);
v_c_5945_ = lean_ctor_get(v_date_4556_, 14);
v_F_5946_ = lean_ctor_get(v_date_4556_, 15);
v_a_5947_ = lean_ctor_get(v_date_4556_, 16);
v_b_5948_ = lean_ctor_get(v_date_4556_, 17);
v_B_5949_ = lean_ctor_get(v_date_4556_, 18);
v_h_5950_ = lean_ctor_get(v_date_4556_, 19);
v_K_5951_ = lean_ctor_get(v_date_4556_, 20);
v_k_5952_ = lean_ctor_get(v_date_4556_, 21);
v_H_5953_ = lean_ctor_get(v_date_4556_, 22);
v_m_5954_ = lean_ctor_get(v_date_4556_, 23);
v_s_5955_ = lean_ctor_get(v_date_4556_, 24);
v_S_5956_ = lean_ctor_get(v_date_4556_, 25);
v_A_5957_ = lean_ctor_get(v_date_4556_, 26);
v_N_5958_ = lean_ctor_get(v_date_4556_, 28);
v_V_5959_ = lean_ctor_get(v_date_4556_, 29);
v_z_5960_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_5961_ = lean_ctor_get(v_date_4556_, 31);
v_v_5962_ = lean_ctor_get(v_date_4556_, 32);
v_O_5963_ = lean_ctor_get(v_date_4556_, 33);
v_X_5964_ = lean_ctor_get(v_date_4556_, 34);
v_x_5965_ = lean_ctor_get(v_date_4556_, 35);
v_Z_5966_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_5976_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_5976_ == 0)
{
lean_object* v_unused_5977_; 
v_unused_5977_ = lean_ctor_get(v_date_4556_, 27);
lean_dec(v_unused_5977_);
v___x_5968_ = v_date_4556_;
v_isShared_5969_ = v_isSharedCheck_5976_;
goto v_resetjp_5967_;
}
else
{
lean_inc(v_Z_5966_);
lean_inc(v_x_5965_);
lean_inc(v_X_5964_);
lean_inc(v_O_5963_);
lean_inc(v_v_5962_);
lean_inc(v_zabbrev_5961_);
lean_inc(v_z_5960_);
lean_inc(v_V_5959_);
lean_inc(v_N_5958_);
lean_inc(v_A_5957_);
lean_inc(v_S_5956_);
lean_inc(v_s_5955_);
lean_inc(v_m_5954_);
lean_inc(v_H_5953_);
lean_inc(v_k_5952_);
lean_inc(v_K_5951_);
lean_inc(v_h_5950_);
lean_inc(v_B_5949_);
lean_inc(v_b_5948_);
lean_inc(v_a_5947_);
lean_inc(v_F_5946_);
lean_inc(v_c_5945_);
lean_inc(v_e_5944_);
lean_inc(v_E_5943_);
lean_inc(v_W_5942_);
lean_inc(v_w_5941_);
lean_inc(v_q_5940_);
lean_inc(v_Q_5939_);
lean_inc(v_d_5938_);
lean_inc(v_L_5937_);
lean_inc(v_M_5936_);
lean_inc(v_D_5935_);
lean_inc(v_Y_5934_);
lean_inc(v_u_5933_);
lean_inc(v_y_5932_);
lean_inc(v_G_5931_);
lean_dec(v_date_4556_);
v___x_5968_ = lean_box(0);
v_isShared_5969_ = v_isSharedCheck_5976_;
goto v_resetjp_5967_;
}
v_resetjp_5967_:
{
lean_object* v___x_5971_; 
if (v_isShared_5930_ == 0)
{
lean_ctor_set_tag(v___x_5929_, 1);
lean_ctor_set(v___x_5929_, 0, v_data_4558_);
v___x_5971_ = v___x_5929_;
goto v_reusejp_5970_;
}
else
{
lean_object* v_reuseFailAlloc_5975_; 
v_reuseFailAlloc_5975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5975_, 0, v_data_4558_);
v___x_5971_ = v_reuseFailAlloc_5975_;
goto v_reusejp_5970_;
}
v_reusejp_5970_:
{
lean_object* v___x_5973_; 
if (v_isShared_5969_ == 0)
{
lean_ctor_set(v___x_5968_, 27, v___x_5971_);
v___x_5973_ = v___x_5968_;
goto v_reusejp_5972_;
}
else
{
lean_object* v_reuseFailAlloc_5974_; 
v_reuseFailAlloc_5974_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5974_, 0, v_G_5931_);
lean_ctor_set(v_reuseFailAlloc_5974_, 1, v_y_5932_);
lean_ctor_set(v_reuseFailAlloc_5974_, 2, v_u_5933_);
lean_ctor_set(v_reuseFailAlloc_5974_, 3, v_Y_5934_);
lean_ctor_set(v_reuseFailAlloc_5974_, 4, v_D_5935_);
lean_ctor_set(v_reuseFailAlloc_5974_, 5, v_M_5936_);
lean_ctor_set(v_reuseFailAlloc_5974_, 6, v_L_5937_);
lean_ctor_set(v_reuseFailAlloc_5974_, 7, v_d_5938_);
lean_ctor_set(v_reuseFailAlloc_5974_, 8, v_Q_5939_);
lean_ctor_set(v_reuseFailAlloc_5974_, 9, v_q_5940_);
lean_ctor_set(v_reuseFailAlloc_5974_, 10, v_w_5941_);
lean_ctor_set(v_reuseFailAlloc_5974_, 11, v_W_5942_);
lean_ctor_set(v_reuseFailAlloc_5974_, 12, v_E_5943_);
lean_ctor_set(v_reuseFailAlloc_5974_, 13, v_e_5944_);
lean_ctor_set(v_reuseFailAlloc_5974_, 14, v_c_5945_);
lean_ctor_set(v_reuseFailAlloc_5974_, 15, v_F_5946_);
lean_ctor_set(v_reuseFailAlloc_5974_, 16, v_a_5947_);
lean_ctor_set(v_reuseFailAlloc_5974_, 17, v_b_5948_);
lean_ctor_set(v_reuseFailAlloc_5974_, 18, v_B_5949_);
lean_ctor_set(v_reuseFailAlloc_5974_, 19, v_h_5950_);
lean_ctor_set(v_reuseFailAlloc_5974_, 20, v_K_5951_);
lean_ctor_set(v_reuseFailAlloc_5974_, 21, v_k_5952_);
lean_ctor_set(v_reuseFailAlloc_5974_, 22, v_H_5953_);
lean_ctor_set(v_reuseFailAlloc_5974_, 23, v_m_5954_);
lean_ctor_set(v_reuseFailAlloc_5974_, 24, v_s_5955_);
lean_ctor_set(v_reuseFailAlloc_5974_, 25, v_S_5956_);
lean_ctor_set(v_reuseFailAlloc_5974_, 26, v_A_5957_);
lean_ctor_set(v_reuseFailAlloc_5974_, 27, v___x_5971_);
lean_ctor_set(v_reuseFailAlloc_5974_, 28, v_N_5958_);
lean_ctor_set(v_reuseFailAlloc_5974_, 29, v_V_5959_);
lean_ctor_set(v_reuseFailAlloc_5974_, 30, v_z_5960_);
lean_ctor_set(v_reuseFailAlloc_5974_, 31, v_zabbrev_5961_);
lean_ctor_set(v_reuseFailAlloc_5974_, 32, v_v_5962_);
lean_ctor_set(v_reuseFailAlloc_5974_, 33, v_O_5963_);
lean_ctor_set(v_reuseFailAlloc_5974_, 34, v_X_5964_);
lean_ctor_set(v_reuseFailAlloc_5974_, 35, v_x_5965_);
lean_ctor_set(v_reuseFailAlloc_5974_, 36, v_Z_5966_);
v___x_5973_ = v_reuseFailAlloc_5974_;
goto v_reusejp_5972_;
}
v_reusejp_5972_:
{
return v___x_5973_;
}
}
}
}
}
case 28:
{
lean_object* v___x_5981_; uint8_t v_isShared_5982_; uint8_t v_isSharedCheck_6030_; 
v_isSharedCheck_6030_ = !lean_is_exclusive(v_modifier_4557_);
if (v_isSharedCheck_6030_ == 0)
{
lean_object* v_unused_6031_; 
v_unused_6031_ = lean_ctor_get(v_modifier_4557_, 0);
lean_dec(v_unused_6031_);
v___x_5981_ = v_modifier_4557_;
v_isShared_5982_ = v_isSharedCheck_6030_;
goto v_resetjp_5980_;
}
else
{
lean_dec(v_modifier_4557_);
v___x_5981_ = lean_box(0);
v_isShared_5982_ = v_isSharedCheck_6030_;
goto v_resetjp_5980_;
}
v_resetjp_5980_:
{
lean_object* v_G_5983_; lean_object* v_y_5984_; lean_object* v_u_5985_; lean_object* v_Y_5986_; lean_object* v_D_5987_; lean_object* v_M_5988_; lean_object* v_L_5989_; lean_object* v_d_5990_; lean_object* v_Q_5991_; lean_object* v_q_5992_; lean_object* v_w_5993_; lean_object* v_W_5994_; lean_object* v_E_5995_; lean_object* v_e_5996_; lean_object* v_c_5997_; lean_object* v_F_5998_; lean_object* v_a_5999_; lean_object* v_b_6000_; lean_object* v_B_6001_; lean_object* v_h_6002_; lean_object* v_K_6003_; lean_object* v_k_6004_; lean_object* v_H_6005_; lean_object* v_m_6006_; lean_object* v_s_6007_; lean_object* v_S_6008_; lean_object* v_A_6009_; lean_object* v_n_6010_; lean_object* v_V_6011_; lean_object* v_z_6012_; lean_object* v_zabbrev_6013_; lean_object* v_v_6014_; lean_object* v_O_6015_; lean_object* v_X_6016_; lean_object* v_x_6017_; lean_object* v_Z_6018_; lean_object* v___x_6020_; uint8_t v_isShared_6021_; uint8_t v_isSharedCheck_6028_; 
v_G_5983_ = lean_ctor_get(v_date_4556_, 0);
v_y_5984_ = lean_ctor_get(v_date_4556_, 1);
v_u_5985_ = lean_ctor_get(v_date_4556_, 2);
v_Y_5986_ = lean_ctor_get(v_date_4556_, 3);
v_D_5987_ = lean_ctor_get(v_date_4556_, 4);
v_M_5988_ = lean_ctor_get(v_date_4556_, 5);
v_L_5989_ = lean_ctor_get(v_date_4556_, 6);
v_d_5990_ = lean_ctor_get(v_date_4556_, 7);
v_Q_5991_ = lean_ctor_get(v_date_4556_, 8);
v_q_5992_ = lean_ctor_get(v_date_4556_, 9);
v_w_5993_ = lean_ctor_get(v_date_4556_, 10);
v_W_5994_ = lean_ctor_get(v_date_4556_, 11);
v_E_5995_ = lean_ctor_get(v_date_4556_, 12);
v_e_5996_ = lean_ctor_get(v_date_4556_, 13);
v_c_5997_ = lean_ctor_get(v_date_4556_, 14);
v_F_5998_ = lean_ctor_get(v_date_4556_, 15);
v_a_5999_ = lean_ctor_get(v_date_4556_, 16);
v_b_6000_ = lean_ctor_get(v_date_4556_, 17);
v_B_6001_ = lean_ctor_get(v_date_4556_, 18);
v_h_6002_ = lean_ctor_get(v_date_4556_, 19);
v_K_6003_ = lean_ctor_get(v_date_4556_, 20);
v_k_6004_ = lean_ctor_get(v_date_4556_, 21);
v_H_6005_ = lean_ctor_get(v_date_4556_, 22);
v_m_6006_ = lean_ctor_get(v_date_4556_, 23);
v_s_6007_ = lean_ctor_get(v_date_4556_, 24);
v_S_6008_ = lean_ctor_get(v_date_4556_, 25);
v_A_6009_ = lean_ctor_get(v_date_4556_, 26);
v_n_6010_ = lean_ctor_get(v_date_4556_, 27);
v_V_6011_ = lean_ctor_get(v_date_4556_, 29);
v_z_6012_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_6013_ = lean_ctor_get(v_date_4556_, 31);
v_v_6014_ = lean_ctor_get(v_date_4556_, 32);
v_O_6015_ = lean_ctor_get(v_date_4556_, 33);
v_X_6016_ = lean_ctor_get(v_date_4556_, 34);
v_x_6017_ = lean_ctor_get(v_date_4556_, 35);
v_Z_6018_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_6028_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_6028_ == 0)
{
lean_object* v_unused_6029_; 
v_unused_6029_ = lean_ctor_get(v_date_4556_, 28);
lean_dec(v_unused_6029_);
v___x_6020_ = v_date_4556_;
v_isShared_6021_ = v_isSharedCheck_6028_;
goto v_resetjp_6019_;
}
else
{
lean_inc(v_Z_6018_);
lean_inc(v_x_6017_);
lean_inc(v_X_6016_);
lean_inc(v_O_6015_);
lean_inc(v_v_6014_);
lean_inc(v_zabbrev_6013_);
lean_inc(v_z_6012_);
lean_inc(v_V_6011_);
lean_inc(v_n_6010_);
lean_inc(v_A_6009_);
lean_inc(v_S_6008_);
lean_inc(v_s_6007_);
lean_inc(v_m_6006_);
lean_inc(v_H_6005_);
lean_inc(v_k_6004_);
lean_inc(v_K_6003_);
lean_inc(v_h_6002_);
lean_inc(v_B_6001_);
lean_inc(v_b_6000_);
lean_inc(v_a_5999_);
lean_inc(v_F_5998_);
lean_inc(v_c_5997_);
lean_inc(v_e_5996_);
lean_inc(v_E_5995_);
lean_inc(v_W_5994_);
lean_inc(v_w_5993_);
lean_inc(v_q_5992_);
lean_inc(v_Q_5991_);
lean_inc(v_d_5990_);
lean_inc(v_L_5989_);
lean_inc(v_M_5988_);
lean_inc(v_D_5987_);
lean_inc(v_Y_5986_);
lean_inc(v_u_5985_);
lean_inc(v_y_5984_);
lean_inc(v_G_5983_);
lean_dec(v_date_4556_);
v___x_6020_ = lean_box(0);
v_isShared_6021_ = v_isSharedCheck_6028_;
goto v_resetjp_6019_;
}
v_resetjp_6019_:
{
lean_object* v___x_6023_; 
if (v_isShared_5982_ == 0)
{
lean_ctor_set_tag(v___x_5981_, 1);
lean_ctor_set(v___x_5981_, 0, v_data_4558_);
v___x_6023_ = v___x_5981_;
goto v_reusejp_6022_;
}
else
{
lean_object* v_reuseFailAlloc_6027_; 
v_reuseFailAlloc_6027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6027_, 0, v_data_4558_);
v___x_6023_ = v_reuseFailAlloc_6027_;
goto v_reusejp_6022_;
}
v_reusejp_6022_:
{
lean_object* v___x_6025_; 
if (v_isShared_6021_ == 0)
{
lean_ctor_set(v___x_6020_, 28, v___x_6023_);
v___x_6025_ = v___x_6020_;
goto v_reusejp_6024_;
}
else
{
lean_object* v_reuseFailAlloc_6026_; 
v_reuseFailAlloc_6026_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6026_, 0, v_G_5983_);
lean_ctor_set(v_reuseFailAlloc_6026_, 1, v_y_5984_);
lean_ctor_set(v_reuseFailAlloc_6026_, 2, v_u_5985_);
lean_ctor_set(v_reuseFailAlloc_6026_, 3, v_Y_5986_);
lean_ctor_set(v_reuseFailAlloc_6026_, 4, v_D_5987_);
lean_ctor_set(v_reuseFailAlloc_6026_, 5, v_M_5988_);
lean_ctor_set(v_reuseFailAlloc_6026_, 6, v_L_5989_);
lean_ctor_set(v_reuseFailAlloc_6026_, 7, v_d_5990_);
lean_ctor_set(v_reuseFailAlloc_6026_, 8, v_Q_5991_);
lean_ctor_set(v_reuseFailAlloc_6026_, 9, v_q_5992_);
lean_ctor_set(v_reuseFailAlloc_6026_, 10, v_w_5993_);
lean_ctor_set(v_reuseFailAlloc_6026_, 11, v_W_5994_);
lean_ctor_set(v_reuseFailAlloc_6026_, 12, v_E_5995_);
lean_ctor_set(v_reuseFailAlloc_6026_, 13, v_e_5996_);
lean_ctor_set(v_reuseFailAlloc_6026_, 14, v_c_5997_);
lean_ctor_set(v_reuseFailAlloc_6026_, 15, v_F_5998_);
lean_ctor_set(v_reuseFailAlloc_6026_, 16, v_a_5999_);
lean_ctor_set(v_reuseFailAlloc_6026_, 17, v_b_6000_);
lean_ctor_set(v_reuseFailAlloc_6026_, 18, v_B_6001_);
lean_ctor_set(v_reuseFailAlloc_6026_, 19, v_h_6002_);
lean_ctor_set(v_reuseFailAlloc_6026_, 20, v_K_6003_);
lean_ctor_set(v_reuseFailAlloc_6026_, 21, v_k_6004_);
lean_ctor_set(v_reuseFailAlloc_6026_, 22, v_H_6005_);
lean_ctor_set(v_reuseFailAlloc_6026_, 23, v_m_6006_);
lean_ctor_set(v_reuseFailAlloc_6026_, 24, v_s_6007_);
lean_ctor_set(v_reuseFailAlloc_6026_, 25, v_S_6008_);
lean_ctor_set(v_reuseFailAlloc_6026_, 26, v_A_6009_);
lean_ctor_set(v_reuseFailAlloc_6026_, 27, v_n_6010_);
lean_ctor_set(v_reuseFailAlloc_6026_, 28, v___x_6023_);
lean_ctor_set(v_reuseFailAlloc_6026_, 29, v_V_6011_);
lean_ctor_set(v_reuseFailAlloc_6026_, 30, v_z_6012_);
lean_ctor_set(v_reuseFailAlloc_6026_, 31, v_zabbrev_6013_);
lean_ctor_set(v_reuseFailAlloc_6026_, 32, v_v_6014_);
lean_ctor_set(v_reuseFailAlloc_6026_, 33, v_O_6015_);
lean_ctor_set(v_reuseFailAlloc_6026_, 34, v_X_6016_);
lean_ctor_set(v_reuseFailAlloc_6026_, 35, v_x_6017_);
lean_ctor_set(v_reuseFailAlloc_6026_, 36, v_Z_6018_);
v___x_6025_ = v_reuseFailAlloc_6026_;
goto v_reusejp_6024_;
}
v_reusejp_6024_:
{
return v___x_6025_;
}
}
}
}
}
case 29:
{
lean_object* v_G_6032_; lean_object* v_y_6033_; lean_object* v_u_6034_; lean_object* v_Y_6035_; lean_object* v_D_6036_; lean_object* v_M_6037_; lean_object* v_L_6038_; lean_object* v_d_6039_; lean_object* v_Q_6040_; lean_object* v_q_6041_; lean_object* v_w_6042_; lean_object* v_W_6043_; lean_object* v_E_6044_; lean_object* v_e_6045_; lean_object* v_c_6046_; lean_object* v_F_6047_; lean_object* v_a_6048_; lean_object* v_b_6049_; lean_object* v_B_6050_; lean_object* v_h_6051_; lean_object* v_K_6052_; lean_object* v_k_6053_; lean_object* v_H_6054_; lean_object* v_m_6055_; lean_object* v_s_6056_; lean_object* v_S_6057_; lean_object* v_A_6058_; lean_object* v_n_6059_; lean_object* v_N_6060_; lean_object* v_z_6061_; lean_object* v_zabbrev_6062_; lean_object* v_v_6063_; lean_object* v_O_6064_; lean_object* v_X_6065_; lean_object* v_x_6066_; lean_object* v_Z_6067_; lean_object* v___x_6069_; uint8_t v_isShared_6070_; uint8_t v_isSharedCheck_6075_; 
lean_dec_ref_known(v_modifier_4557_, 0);
v_G_6032_ = lean_ctor_get(v_date_4556_, 0);
v_y_6033_ = lean_ctor_get(v_date_4556_, 1);
v_u_6034_ = lean_ctor_get(v_date_4556_, 2);
v_Y_6035_ = lean_ctor_get(v_date_4556_, 3);
v_D_6036_ = lean_ctor_get(v_date_4556_, 4);
v_M_6037_ = lean_ctor_get(v_date_4556_, 5);
v_L_6038_ = lean_ctor_get(v_date_4556_, 6);
v_d_6039_ = lean_ctor_get(v_date_4556_, 7);
v_Q_6040_ = lean_ctor_get(v_date_4556_, 8);
v_q_6041_ = lean_ctor_get(v_date_4556_, 9);
v_w_6042_ = lean_ctor_get(v_date_4556_, 10);
v_W_6043_ = lean_ctor_get(v_date_4556_, 11);
v_E_6044_ = lean_ctor_get(v_date_4556_, 12);
v_e_6045_ = lean_ctor_get(v_date_4556_, 13);
v_c_6046_ = lean_ctor_get(v_date_4556_, 14);
v_F_6047_ = lean_ctor_get(v_date_4556_, 15);
v_a_6048_ = lean_ctor_get(v_date_4556_, 16);
v_b_6049_ = lean_ctor_get(v_date_4556_, 17);
v_B_6050_ = lean_ctor_get(v_date_4556_, 18);
v_h_6051_ = lean_ctor_get(v_date_4556_, 19);
v_K_6052_ = lean_ctor_get(v_date_4556_, 20);
v_k_6053_ = lean_ctor_get(v_date_4556_, 21);
v_H_6054_ = lean_ctor_get(v_date_4556_, 22);
v_m_6055_ = lean_ctor_get(v_date_4556_, 23);
v_s_6056_ = lean_ctor_get(v_date_4556_, 24);
v_S_6057_ = lean_ctor_get(v_date_4556_, 25);
v_A_6058_ = lean_ctor_get(v_date_4556_, 26);
v_n_6059_ = lean_ctor_get(v_date_4556_, 27);
v_N_6060_ = lean_ctor_get(v_date_4556_, 28);
v_z_6061_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_6062_ = lean_ctor_get(v_date_4556_, 31);
v_v_6063_ = lean_ctor_get(v_date_4556_, 32);
v_O_6064_ = lean_ctor_get(v_date_4556_, 33);
v_X_6065_ = lean_ctor_get(v_date_4556_, 34);
v_x_6066_ = lean_ctor_get(v_date_4556_, 35);
v_Z_6067_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_6075_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_6075_ == 0)
{
lean_object* v_unused_6076_; 
v_unused_6076_ = lean_ctor_get(v_date_4556_, 29);
lean_dec(v_unused_6076_);
v___x_6069_ = v_date_4556_;
v_isShared_6070_ = v_isSharedCheck_6075_;
goto v_resetjp_6068_;
}
else
{
lean_inc(v_Z_6067_);
lean_inc(v_x_6066_);
lean_inc(v_X_6065_);
lean_inc(v_O_6064_);
lean_inc(v_v_6063_);
lean_inc(v_zabbrev_6062_);
lean_inc(v_z_6061_);
lean_inc(v_N_6060_);
lean_inc(v_n_6059_);
lean_inc(v_A_6058_);
lean_inc(v_S_6057_);
lean_inc(v_s_6056_);
lean_inc(v_m_6055_);
lean_inc(v_H_6054_);
lean_inc(v_k_6053_);
lean_inc(v_K_6052_);
lean_inc(v_h_6051_);
lean_inc(v_B_6050_);
lean_inc(v_b_6049_);
lean_inc(v_a_6048_);
lean_inc(v_F_6047_);
lean_inc(v_c_6046_);
lean_inc(v_e_6045_);
lean_inc(v_E_6044_);
lean_inc(v_W_6043_);
lean_inc(v_w_6042_);
lean_inc(v_q_6041_);
lean_inc(v_Q_6040_);
lean_inc(v_d_6039_);
lean_inc(v_L_6038_);
lean_inc(v_M_6037_);
lean_inc(v_D_6036_);
lean_inc(v_Y_6035_);
lean_inc(v_u_6034_);
lean_inc(v_y_6033_);
lean_inc(v_G_6032_);
lean_dec(v_date_4556_);
v___x_6069_ = lean_box(0);
v_isShared_6070_ = v_isSharedCheck_6075_;
goto v_resetjp_6068_;
}
v_resetjp_6068_:
{
lean_object* v___x_6071_; lean_object* v___x_6073_; 
v___x_6071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6071_, 0, v_data_4558_);
if (v_isShared_6070_ == 0)
{
lean_ctor_set(v___x_6069_, 29, v___x_6071_);
v___x_6073_ = v___x_6069_;
goto v_reusejp_6072_;
}
else
{
lean_object* v_reuseFailAlloc_6074_; 
v_reuseFailAlloc_6074_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6074_, 0, v_G_6032_);
lean_ctor_set(v_reuseFailAlloc_6074_, 1, v_y_6033_);
lean_ctor_set(v_reuseFailAlloc_6074_, 2, v_u_6034_);
lean_ctor_set(v_reuseFailAlloc_6074_, 3, v_Y_6035_);
lean_ctor_set(v_reuseFailAlloc_6074_, 4, v_D_6036_);
lean_ctor_set(v_reuseFailAlloc_6074_, 5, v_M_6037_);
lean_ctor_set(v_reuseFailAlloc_6074_, 6, v_L_6038_);
lean_ctor_set(v_reuseFailAlloc_6074_, 7, v_d_6039_);
lean_ctor_set(v_reuseFailAlloc_6074_, 8, v_Q_6040_);
lean_ctor_set(v_reuseFailAlloc_6074_, 9, v_q_6041_);
lean_ctor_set(v_reuseFailAlloc_6074_, 10, v_w_6042_);
lean_ctor_set(v_reuseFailAlloc_6074_, 11, v_W_6043_);
lean_ctor_set(v_reuseFailAlloc_6074_, 12, v_E_6044_);
lean_ctor_set(v_reuseFailAlloc_6074_, 13, v_e_6045_);
lean_ctor_set(v_reuseFailAlloc_6074_, 14, v_c_6046_);
lean_ctor_set(v_reuseFailAlloc_6074_, 15, v_F_6047_);
lean_ctor_set(v_reuseFailAlloc_6074_, 16, v_a_6048_);
lean_ctor_set(v_reuseFailAlloc_6074_, 17, v_b_6049_);
lean_ctor_set(v_reuseFailAlloc_6074_, 18, v_B_6050_);
lean_ctor_set(v_reuseFailAlloc_6074_, 19, v_h_6051_);
lean_ctor_set(v_reuseFailAlloc_6074_, 20, v_K_6052_);
lean_ctor_set(v_reuseFailAlloc_6074_, 21, v_k_6053_);
lean_ctor_set(v_reuseFailAlloc_6074_, 22, v_H_6054_);
lean_ctor_set(v_reuseFailAlloc_6074_, 23, v_m_6055_);
lean_ctor_set(v_reuseFailAlloc_6074_, 24, v_s_6056_);
lean_ctor_set(v_reuseFailAlloc_6074_, 25, v_S_6057_);
lean_ctor_set(v_reuseFailAlloc_6074_, 26, v_A_6058_);
lean_ctor_set(v_reuseFailAlloc_6074_, 27, v_n_6059_);
lean_ctor_set(v_reuseFailAlloc_6074_, 28, v_N_6060_);
lean_ctor_set(v_reuseFailAlloc_6074_, 29, v___x_6071_);
lean_ctor_set(v_reuseFailAlloc_6074_, 30, v_z_6061_);
lean_ctor_set(v_reuseFailAlloc_6074_, 31, v_zabbrev_6062_);
lean_ctor_set(v_reuseFailAlloc_6074_, 32, v_v_6063_);
lean_ctor_set(v_reuseFailAlloc_6074_, 33, v_O_6064_);
lean_ctor_set(v_reuseFailAlloc_6074_, 34, v_X_6065_);
lean_ctor_set(v_reuseFailAlloc_6074_, 35, v_x_6066_);
lean_ctor_set(v_reuseFailAlloc_6074_, 36, v_Z_6067_);
v___x_6073_ = v_reuseFailAlloc_6074_;
goto v_reusejp_6072_;
}
v_reusejp_6072_:
{
return v___x_6073_;
}
}
}
case 30:
{
uint8_t v_presentation_6077_; 
v_presentation_6077_ = lean_ctor_get_uint8(v_modifier_4557_, 0);
lean_dec_ref_known(v_modifier_4557_, 0);
if (v_presentation_6077_ == 0)
{
lean_object* v_G_6078_; lean_object* v_y_6079_; lean_object* v_u_6080_; lean_object* v_Y_6081_; lean_object* v_D_6082_; lean_object* v_M_6083_; lean_object* v_L_6084_; lean_object* v_d_6085_; lean_object* v_Q_6086_; lean_object* v_q_6087_; lean_object* v_w_6088_; lean_object* v_W_6089_; lean_object* v_E_6090_; lean_object* v_e_6091_; lean_object* v_c_6092_; lean_object* v_F_6093_; lean_object* v_a_6094_; lean_object* v_b_6095_; lean_object* v_B_6096_; lean_object* v_h_6097_; lean_object* v_K_6098_; lean_object* v_k_6099_; lean_object* v_H_6100_; lean_object* v_m_6101_; lean_object* v_s_6102_; lean_object* v_S_6103_; lean_object* v_A_6104_; lean_object* v_n_6105_; lean_object* v_N_6106_; lean_object* v_V_6107_; lean_object* v_z_6108_; lean_object* v_v_6109_; lean_object* v_O_6110_; lean_object* v_X_6111_; lean_object* v_x_6112_; lean_object* v_Z_6113_; lean_object* v___x_6115_; uint8_t v_isShared_6116_; uint8_t v_isSharedCheck_6121_; 
v_G_6078_ = lean_ctor_get(v_date_4556_, 0);
v_y_6079_ = lean_ctor_get(v_date_4556_, 1);
v_u_6080_ = lean_ctor_get(v_date_4556_, 2);
v_Y_6081_ = lean_ctor_get(v_date_4556_, 3);
v_D_6082_ = lean_ctor_get(v_date_4556_, 4);
v_M_6083_ = lean_ctor_get(v_date_4556_, 5);
v_L_6084_ = lean_ctor_get(v_date_4556_, 6);
v_d_6085_ = lean_ctor_get(v_date_4556_, 7);
v_Q_6086_ = lean_ctor_get(v_date_4556_, 8);
v_q_6087_ = lean_ctor_get(v_date_4556_, 9);
v_w_6088_ = lean_ctor_get(v_date_4556_, 10);
v_W_6089_ = lean_ctor_get(v_date_4556_, 11);
v_E_6090_ = lean_ctor_get(v_date_4556_, 12);
v_e_6091_ = lean_ctor_get(v_date_4556_, 13);
v_c_6092_ = lean_ctor_get(v_date_4556_, 14);
v_F_6093_ = lean_ctor_get(v_date_4556_, 15);
v_a_6094_ = lean_ctor_get(v_date_4556_, 16);
v_b_6095_ = lean_ctor_get(v_date_4556_, 17);
v_B_6096_ = lean_ctor_get(v_date_4556_, 18);
v_h_6097_ = lean_ctor_get(v_date_4556_, 19);
v_K_6098_ = lean_ctor_get(v_date_4556_, 20);
v_k_6099_ = lean_ctor_get(v_date_4556_, 21);
v_H_6100_ = lean_ctor_get(v_date_4556_, 22);
v_m_6101_ = lean_ctor_get(v_date_4556_, 23);
v_s_6102_ = lean_ctor_get(v_date_4556_, 24);
v_S_6103_ = lean_ctor_get(v_date_4556_, 25);
v_A_6104_ = lean_ctor_get(v_date_4556_, 26);
v_n_6105_ = lean_ctor_get(v_date_4556_, 27);
v_N_6106_ = lean_ctor_get(v_date_4556_, 28);
v_V_6107_ = lean_ctor_get(v_date_4556_, 29);
v_z_6108_ = lean_ctor_get(v_date_4556_, 30);
v_v_6109_ = lean_ctor_get(v_date_4556_, 32);
v_O_6110_ = lean_ctor_get(v_date_4556_, 33);
v_X_6111_ = lean_ctor_get(v_date_4556_, 34);
v_x_6112_ = lean_ctor_get(v_date_4556_, 35);
v_Z_6113_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_6121_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_6121_ == 0)
{
lean_object* v_unused_6122_; 
v_unused_6122_ = lean_ctor_get(v_date_4556_, 31);
lean_dec(v_unused_6122_);
v___x_6115_ = v_date_4556_;
v_isShared_6116_ = v_isSharedCheck_6121_;
goto v_resetjp_6114_;
}
else
{
lean_inc(v_Z_6113_);
lean_inc(v_x_6112_);
lean_inc(v_X_6111_);
lean_inc(v_O_6110_);
lean_inc(v_v_6109_);
lean_inc(v_z_6108_);
lean_inc(v_V_6107_);
lean_inc(v_N_6106_);
lean_inc(v_n_6105_);
lean_inc(v_A_6104_);
lean_inc(v_S_6103_);
lean_inc(v_s_6102_);
lean_inc(v_m_6101_);
lean_inc(v_H_6100_);
lean_inc(v_k_6099_);
lean_inc(v_K_6098_);
lean_inc(v_h_6097_);
lean_inc(v_B_6096_);
lean_inc(v_b_6095_);
lean_inc(v_a_6094_);
lean_inc(v_F_6093_);
lean_inc(v_c_6092_);
lean_inc(v_e_6091_);
lean_inc(v_E_6090_);
lean_inc(v_W_6089_);
lean_inc(v_w_6088_);
lean_inc(v_q_6087_);
lean_inc(v_Q_6086_);
lean_inc(v_d_6085_);
lean_inc(v_L_6084_);
lean_inc(v_M_6083_);
lean_inc(v_D_6082_);
lean_inc(v_Y_6081_);
lean_inc(v_u_6080_);
lean_inc(v_y_6079_);
lean_inc(v_G_6078_);
lean_dec(v_date_4556_);
v___x_6115_ = lean_box(0);
v_isShared_6116_ = v_isSharedCheck_6121_;
goto v_resetjp_6114_;
}
v_resetjp_6114_:
{
lean_object* v___x_6117_; lean_object* v___x_6119_; 
v___x_6117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6117_, 0, v_data_4558_);
if (v_isShared_6116_ == 0)
{
lean_ctor_set(v___x_6115_, 31, v___x_6117_);
v___x_6119_ = v___x_6115_;
goto v_reusejp_6118_;
}
else
{
lean_object* v_reuseFailAlloc_6120_; 
v_reuseFailAlloc_6120_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6120_, 0, v_G_6078_);
lean_ctor_set(v_reuseFailAlloc_6120_, 1, v_y_6079_);
lean_ctor_set(v_reuseFailAlloc_6120_, 2, v_u_6080_);
lean_ctor_set(v_reuseFailAlloc_6120_, 3, v_Y_6081_);
lean_ctor_set(v_reuseFailAlloc_6120_, 4, v_D_6082_);
lean_ctor_set(v_reuseFailAlloc_6120_, 5, v_M_6083_);
lean_ctor_set(v_reuseFailAlloc_6120_, 6, v_L_6084_);
lean_ctor_set(v_reuseFailAlloc_6120_, 7, v_d_6085_);
lean_ctor_set(v_reuseFailAlloc_6120_, 8, v_Q_6086_);
lean_ctor_set(v_reuseFailAlloc_6120_, 9, v_q_6087_);
lean_ctor_set(v_reuseFailAlloc_6120_, 10, v_w_6088_);
lean_ctor_set(v_reuseFailAlloc_6120_, 11, v_W_6089_);
lean_ctor_set(v_reuseFailAlloc_6120_, 12, v_E_6090_);
lean_ctor_set(v_reuseFailAlloc_6120_, 13, v_e_6091_);
lean_ctor_set(v_reuseFailAlloc_6120_, 14, v_c_6092_);
lean_ctor_set(v_reuseFailAlloc_6120_, 15, v_F_6093_);
lean_ctor_set(v_reuseFailAlloc_6120_, 16, v_a_6094_);
lean_ctor_set(v_reuseFailAlloc_6120_, 17, v_b_6095_);
lean_ctor_set(v_reuseFailAlloc_6120_, 18, v_B_6096_);
lean_ctor_set(v_reuseFailAlloc_6120_, 19, v_h_6097_);
lean_ctor_set(v_reuseFailAlloc_6120_, 20, v_K_6098_);
lean_ctor_set(v_reuseFailAlloc_6120_, 21, v_k_6099_);
lean_ctor_set(v_reuseFailAlloc_6120_, 22, v_H_6100_);
lean_ctor_set(v_reuseFailAlloc_6120_, 23, v_m_6101_);
lean_ctor_set(v_reuseFailAlloc_6120_, 24, v_s_6102_);
lean_ctor_set(v_reuseFailAlloc_6120_, 25, v_S_6103_);
lean_ctor_set(v_reuseFailAlloc_6120_, 26, v_A_6104_);
lean_ctor_set(v_reuseFailAlloc_6120_, 27, v_n_6105_);
lean_ctor_set(v_reuseFailAlloc_6120_, 28, v_N_6106_);
lean_ctor_set(v_reuseFailAlloc_6120_, 29, v_V_6107_);
lean_ctor_set(v_reuseFailAlloc_6120_, 30, v_z_6108_);
lean_ctor_set(v_reuseFailAlloc_6120_, 31, v___x_6117_);
lean_ctor_set(v_reuseFailAlloc_6120_, 32, v_v_6109_);
lean_ctor_set(v_reuseFailAlloc_6120_, 33, v_O_6110_);
lean_ctor_set(v_reuseFailAlloc_6120_, 34, v_X_6111_);
lean_ctor_set(v_reuseFailAlloc_6120_, 35, v_x_6112_);
lean_ctor_set(v_reuseFailAlloc_6120_, 36, v_Z_6113_);
v___x_6119_ = v_reuseFailAlloc_6120_;
goto v_reusejp_6118_;
}
v_reusejp_6118_:
{
return v___x_6119_;
}
}
}
else
{
lean_object* v_G_6123_; lean_object* v_y_6124_; lean_object* v_u_6125_; lean_object* v_Y_6126_; lean_object* v_D_6127_; lean_object* v_M_6128_; lean_object* v_L_6129_; lean_object* v_d_6130_; lean_object* v_Q_6131_; lean_object* v_q_6132_; lean_object* v_w_6133_; lean_object* v_W_6134_; lean_object* v_E_6135_; lean_object* v_e_6136_; lean_object* v_c_6137_; lean_object* v_F_6138_; lean_object* v_a_6139_; lean_object* v_b_6140_; lean_object* v_B_6141_; lean_object* v_h_6142_; lean_object* v_K_6143_; lean_object* v_k_6144_; lean_object* v_H_6145_; lean_object* v_m_6146_; lean_object* v_s_6147_; lean_object* v_S_6148_; lean_object* v_A_6149_; lean_object* v_n_6150_; lean_object* v_N_6151_; lean_object* v_V_6152_; lean_object* v_zabbrev_6153_; lean_object* v_v_6154_; lean_object* v_O_6155_; lean_object* v_X_6156_; lean_object* v_x_6157_; lean_object* v_Z_6158_; lean_object* v___x_6160_; uint8_t v_isShared_6161_; uint8_t v_isSharedCheck_6166_; 
v_G_6123_ = lean_ctor_get(v_date_4556_, 0);
v_y_6124_ = lean_ctor_get(v_date_4556_, 1);
v_u_6125_ = lean_ctor_get(v_date_4556_, 2);
v_Y_6126_ = lean_ctor_get(v_date_4556_, 3);
v_D_6127_ = lean_ctor_get(v_date_4556_, 4);
v_M_6128_ = lean_ctor_get(v_date_4556_, 5);
v_L_6129_ = lean_ctor_get(v_date_4556_, 6);
v_d_6130_ = lean_ctor_get(v_date_4556_, 7);
v_Q_6131_ = lean_ctor_get(v_date_4556_, 8);
v_q_6132_ = lean_ctor_get(v_date_4556_, 9);
v_w_6133_ = lean_ctor_get(v_date_4556_, 10);
v_W_6134_ = lean_ctor_get(v_date_4556_, 11);
v_E_6135_ = lean_ctor_get(v_date_4556_, 12);
v_e_6136_ = lean_ctor_get(v_date_4556_, 13);
v_c_6137_ = lean_ctor_get(v_date_4556_, 14);
v_F_6138_ = lean_ctor_get(v_date_4556_, 15);
v_a_6139_ = lean_ctor_get(v_date_4556_, 16);
v_b_6140_ = lean_ctor_get(v_date_4556_, 17);
v_B_6141_ = lean_ctor_get(v_date_4556_, 18);
v_h_6142_ = lean_ctor_get(v_date_4556_, 19);
v_K_6143_ = lean_ctor_get(v_date_4556_, 20);
v_k_6144_ = lean_ctor_get(v_date_4556_, 21);
v_H_6145_ = lean_ctor_get(v_date_4556_, 22);
v_m_6146_ = lean_ctor_get(v_date_4556_, 23);
v_s_6147_ = lean_ctor_get(v_date_4556_, 24);
v_S_6148_ = lean_ctor_get(v_date_4556_, 25);
v_A_6149_ = lean_ctor_get(v_date_4556_, 26);
v_n_6150_ = lean_ctor_get(v_date_4556_, 27);
v_N_6151_ = lean_ctor_get(v_date_4556_, 28);
v_V_6152_ = lean_ctor_get(v_date_4556_, 29);
v_zabbrev_6153_ = lean_ctor_get(v_date_4556_, 31);
v_v_6154_ = lean_ctor_get(v_date_4556_, 32);
v_O_6155_ = lean_ctor_get(v_date_4556_, 33);
v_X_6156_ = lean_ctor_get(v_date_4556_, 34);
v_x_6157_ = lean_ctor_get(v_date_4556_, 35);
v_Z_6158_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_6166_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_6166_ == 0)
{
lean_object* v_unused_6167_; 
v_unused_6167_ = lean_ctor_get(v_date_4556_, 30);
lean_dec(v_unused_6167_);
v___x_6160_ = v_date_4556_;
v_isShared_6161_ = v_isSharedCheck_6166_;
goto v_resetjp_6159_;
}
else
{
lean_inc(v_Z_6158_);
lean_inc(v_x_6157_);
lean_inc(v_X_6156_);
lean_inc(v_O_6155_);
lean_inc(v_v_6154_);
lean_inc(v_zabbrev_6153_);
lean_inc(v_V_6152_);
lean_inc(v_N_6151_);
lean_inc(v_n_6150_);
lean_inc(v_A_6149_);
lean_inc(v_S_6148_);
lean_inc(v_s_6147_);
lean_inc(v_m_6146_);
lean_inc(v_H_6145_);
lean_inc(v_k_6144_);
lean_inc(v_K_6143_);
lean_inc(v_h_6142_);
lean_inc(v_B_6141_);
lean_inc(v_b_6140_);
lean_inc(v_a_6139_);
lean_inc(v_F_6138_);
lean_inc(v_c_6137_);
lean_inc(v_e_6136_);
lean_inc(v_E_6135_);
lean_inc(v_W_6134_);
lean_inc(v_w_6133_);
lean_inc(v_q_6132_);
lean_inc(v_Q_6131_);
lean_inc(v_d_6130_);
lean_inc(v_L_6129_);
lean_inc(v_M_6128_);
lean_inc(v_D_6127_);
lean_inc(v_Y_6126_);
lean_inc(v_u_6125_);
lean_inc(v_y_6124_);
lean_inc(v_G_6123_);
lean_dec(v_date_4556_);
v___x_6160_ = lean_box(0);
v_isShared_6161_ = v_isSharedCheck_6166_;
goto v_resetjp_6159_;
}
v_resetjp_6159_:
{
lean_object* v___x_6162_; lean_object* v___x_6164_; 
v___x_6162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6162_, 0, v_data_4558_);
if (v_isShared_6161_ == 0)
{
lean_ctor_set(v___x_6160_, 30, v___x_6162_);
v___x_6164_ = v___x_6160_;
goto v_reusejp_6163_;
}
else
{
lean_object* v_reuseFailAlloc_6165_; 
v_reuseFailAlloc_6165_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6165_, 0, v_G_6123_);
lean_ctor_set(v_reuseFailAlloc_6165_, 1, v_y_6124_);
lean_ctor_set(v_reuseFailAlloc_6165_, 2, v_u_6125_);
lean_ctor_set(v_reuseFailAlloc_6165_, 3, v_Y_6126_);
lean_ctor_set(v_reuseFailAlloc_6165_, 4, v_D_6127_);
lean_ctor_set(v_reuseFailAlloc_6165_, 5, v_M_6128_);
lean_ctor_set(v_reuseFailAlloc_6165_, 6, v_L_6129_);
lean_ctor_set(v_reuseFailAlloc_6165_, 7, v_d_6130_);
lean_ctor_set(v_reuseFailAlloc_6165_, 8, v_Q_6131_);
lean_ctor_set(v_reuseFailAlloc_6165_, 9, v_q_6132_);
lean_ctor_set(v_reuseFailAlloc_6165_, 10, v_w_6133_);
lean_ctor_set(v_reuseFailAlloc_6165_, 11, v_W_6134_);
lean_ctor_set(v_reuseFailAlloc_6165_, 12, v_E_6135_);
lean_ctor_set(v_reuseFailAlloc_6165_, 13, v_e_6136_);
lean_ctor_set(v_reuseFailAlloc_6165_, 14, v_c_6137_);
lean_ctor_set(v_reuseFailAlloc_6165_, 15, v_F_6138_);
lean_ctor_set(v_reuseFailAlloc_6165_, 16, v_a_6139_);
lean_ctor_set(v_reuseFailAlloc_6165_, 17, v_b_6140_);
lean_ctor_set(v_reuseFailAlloc_6165_, 18, v_B_6141_);
lean_ctor_set(v_reuseFailAlloc_6165_, 19, v_h_6142_);
lean_ctor_set(v_reuseFailAlloc_6165_, 20, v_K_6143_);
lean_ctor_set(v_reuseFailAlloc_6165_, 21, v_k_6144_);
lean_ctor_set(v_reuseFailAlloc_6165_, 22, v_H_6145_);
lean_ctor_set(v_reuseFailAlloc_6165_, 23, v_m_6146_);
lean_ctor_set(v_reuseFailAlloc_6165_, 24, v_s_6147_);
lean_ctor_set(v_reuseFailAlloc_6165_, 25, v_S_6148_);
lean_ctor_set(v_reuseFailAlloc_6165_, 26, v_A_6149_);
lean_ctor_set(v_reuseFailAlloc_6165_, 27, v_n_6150_);
lean_ctor_set(v_reuseFailAlloc_6165_, 28, v_N_6151_);
lean_ctor_set(v_reuseFailAlloc_6165_, 29, v_V_6152_);
lean_ctor_set(v_reuseFailAlloc_6165_, 30, v___x_6162_);
lean_ctor_set(v_reuseFailAlloc_6165_, 31, v_zabbrev_6153_);
lean_ctor_set(v_reuseFailAlloc_6165_, 32, v_v_6154_);
lean_ctor_set(v_reuseFailAlloc_6165_, 33, v_O_6155_);
lean_ctor_set(v_reuseFailAlloc_6165_, 34, v_X_6156_);
lean_ctor_set(v_reuseFailAlloc_6165_, 35, v_x_6157_);
lean_ctor_set(v_reuseFailAlloc_6165_, 36, v_Z_6158_);
v___x_6164_ = v_reuseFailAlloc_6165_;
goto v_reusejp_6163_;
}
v_reusejp_6163_:
{
return v___x_6164_;
}
}
}
}
case 31:
{
lean_object* v_G_6168_; lean_object* v_y_6169_; lean_object* v_u_6170_; lean_object* v_Y_6171_; lean_object* v_D_6172_; lean_object* v_M_6173_; lean_object* v_L_6174_; lean_object* v_d_6175_; lean_object* v_Q_6176_; lean_object* v_q_6177_; lean_object* v_w_6178_; lean_object* v_W_6179_; lean_object* v_E_6180_; lean_object* v_e_6181_; lean_object* v_c_6182_; lean_object* v_F_6183_; lean_object* v_a_6184_; lean_object* v_b_6185_; lean_object* v_B_6186_; lean_object* v_h_6187_; lean_object* v_K_6188_; lean_object* v_k_6189_; lean_object* v_H_6190_; lean_object* v_m_6191_; lean_object* v_s_6192_; lean_object* v_S_6193_; lean_object* v_A_6194_; lean_object* v_n_6195_; lean_object* v_N_6196_; lean_object* v_V_6197_; lean_object* v_z_6198_; lean_object* v_zabbrev_6199_; lean_object* v_O_6200_; lean_object* v_X_6201_; lean_object* v_x_6202_; lean_object* v_Z_6203_; lean_object* v___x_6205_; uint8_t v_isShared_6206_; uint8_t v_isSharedCheck_6211_; 
lean_dec_ref_known(v_modifier_4557_, 0);
v_G_6168_ = lean_ctor_get(v_date_4556_, 0);
v_y_6169_ = lean_ctor_get(v_date_4556_, 1);
v_u_6170_ = lean_ctor_get(v_date_4556_, 2);
v_Y_6171_ = lean_ctor_get(v_date_4556_, 3);
v_D_6172_ = lean_ctor_get(v_date_4556_, 4);
v_M_6173_ = lean_ctor_get(v_date_4556_, 5);
v_L_6174_ = lean_ctor_get(v_date_4556_, 6);
v_d_6175_ = lean_ctor_get(v_date_4556_, 7);
v_Q_6176_ = lean_ctor_get(v_date_4556_, 8);
v_q_6177_ = lean_ctor_get(v_date_4556_, 9);
v_w_6178_ = lean_ctor_get(v_date_4556_, 10);
v_W_6179_ = lean_ctor_get(v_date_4556_, 11);
v_E_6180_ = lean_ctor_get(v_date_4556_, 12);
v_e_6181_ = lean_ctor_get(v_date_4556_, 13);
v_c_6182_ = lean_ctor_get(v_date_4556_, 14);
v_F_6183_ = lean_ctor_get(v_date_4556_, 15);
v_a_6184_ = lean_ctor_get(v_date_4556_, 16);
v_b_6185_ = lean_ctor_get(v_date_4556_, 17);
v_B_6186_ = lean_ctor_get(v_date_4556_, 18);
v_h_6187_ = lean_ctor_get(v_date_4556_, 19);
v_K_6188_ = lean_ctor_get(v_date_4556_, 20);
v_k_6189_ = lean_ctor_get(v_date_4556_, 21);
v_H_6190_ = lean_ctor_get(v_date_4556_, 22);
v_m_6191_ = lean_ctor_get(v_date_4556_, 23);
v_s_6192_ = lean_ctor_get(v_date_4556_, 24);
v_S_6193_ = lean_ctor_get(v_date_4556_, 25);
v_A_6194_ = lean_ctor_get(v_date_4556_, 26);
v_n_6195_ = lean_ctor_get(v_date_4556_, 27);
v_N_6196_ = lean_ctor_get(v_date_4556_, 28);
v_V_6197_ = lean_ctor_get(v_date_4556_, 29);
v_z_6198_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_6199_ = lean_ctor_get(v_date_4556_, 31);
v_O_6200_ = lean_ctor_get(v_date_4556_, 33);
v_X_6201_ = lean_ctor_get(v_date_4556_, 34);
v_x_6202_ = lean_ctor_get(v_date_4556_, 35);
v_Z_6203_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_6211_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_6211_ == 0)
{
lean_object* v_unused_6212_; 
v_unused_6212_ = lean_ctor_get(v_date_4556_, 32);
lean_dec(v_unused_6212_);
v___x_6205_ = v_date_4556_;
v_isShared_6206_ = v_isSharedCheck_6211_;
goto v_resetjp_6204_;
}
else
{
lean_inc(v_Z_6203_);
lean_inc(v_x_6202_);
lean_inc(v_X_6201_);
lean_inc(v_O_6200_);
lean_inc(v_zabbrev_6199_);
lean_inc(v_z_6198_);
lean_inc(v_V_6197_);
lean_inc(v_N_6196_);
lean_inc(v_n_6195_);
lean_inc(v_A_6194_);
lean_inc(v_S_6193_);
lean_inc(v_s_6192_);
lean_inc(v_m_6191_);
lean_inc(v_H_6190_);
lean_inc(v_k_6189_);
lean_inc(v_K_6188_);
lean_inc(v_h_6187_);
lean_inc(v_B_6186_);
lean_inc(v_b_6185_);
lean_inc(v_a_6184_);
lean_inc(v_F_6183_);
lean_inc(v_c_6182_);
lean_inc(v_e_6181_);
lean_inc(v_E_6180_);
lean_inc(v_W_6179_);
lean_inc(v_w_6178_);
lean_inc(v_q_6177_);
lean_inc(v_Q_6176_);
lean_inc(v_d_6175_);
lean_inc(v_L_6174_);
lean_inc(v_M_6173_);
lean_inc(v_D_6172_);
lean_inc(v_Y_6171_);
lean_inc(v_u_6170_);
lean_inc(v_y_6169_);
lean_inc(v_G_6168_);
lean_dec(v_date_4556_);
v___x_6205_ = lean_box(0);
v_isShared_6206_ = v_isSharedCheck_6211_;
goto v_resetjp_6204_;
}
v_resetjp_6204_:
{
lean_object* v___x_6207_; lean_object* v___x_6209_; 
v___x_6207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6207_, 0, v_data_4558_);
if (v_isShared_6206_ == 0)
{
lean_ctor_set(v___x_6205_, 32, v___x_6207_);
v___x_6209_ = v___x_6205_;
goto v_reusejp_6208_;
}
else
{
lean_object* v_reuseFailAlloc_6210_; 
v_reuseFailAlloc_6210_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6210_, 0, v_G_6168_);
lean_ctor_set(v_reuseFailAlloc_6210_, 1, v_y_6169_);
lean_ctor_set(v_reuseFailAlloc_6210_, 2, v_u_6170_);
lean_ctor_set(v_reuseFailAlloc_6210_, 3, v_Y_6171_);
lean_ctor_set(v_reuseFailAlloc_6210_, 4, v_D_6172_);
lean_ctor_set(v_reuseFailAlloc_6210_, 5, v_M_6173_);
lean_ctor_set(v_reuseFailAlloc_6210_, 6, v_L_6174_);
lean_ctor_set(v_reuseFailAlloc_6210_, 7, v_d_6175_);
lean_ctor_set(v_reuseFailAlloc_6210_, 8, v_Q_6176_);
lean_ctor_set(v_reuseFailAlloc_6210_, 9, v_q_6177_);
lean_ctor_set(v_reuseFailAlloc_6210_, 10, v_w_6178_);
lean_ctor_set(v_reuseFailAlloc_6210_, 11, v_W_6179_);
lean_ctor_set(v_reuseFailAlloc_6210_, 12, v_E_6180_);
lean_ctor_set(v_reuseFailAlloc_6210_, 13, v_e_6181_);
lean_ctor_set(v_reuseFailAlloc_6210_, 14, v_c_6182_);
lean_ctor_set(v_reuseFailAlloc_6210_, 15, v_F_6183_);
lean_ctor_set(v_reuseFailAlloc_6210_, 16, v_a_6184_);
lean_ctor_set(v_reuseFailAlloc_6210_, 17, v_b_6185_);
lean_ctor_set(v_reuseFailAlloc_6210_, 18, v_B_6186_);
lean_ctor_set(v_reuseFailAlloc_6210_, 19, v_h_6187_);
lean_ctor_set(v_reuseFailAlloc_6210_, 20, v_K_6188_);
lean_ctor_set(v_reuseFailAlloc_6210_, 21, v_k_6189_);
lean_ctor_set(v_reuseFailAlloc_6210_, 22, v_H_6190_);
lean_ctor_set(v_reuseFailAlloc_6210_, 23, v_m_6191_);
lean_ctor_set(v_reuseFailAlloc_6210_, 24, v_s_6192_);
lean_ctor_set(v_reuseFailAlloc_6210_, 25, v_S_6193_);
lean_ctor_set(v_reuseFailAlloc_6210_, 26, v_A_6194_);
lean_ctor_set(v_reuseFailAlloc_6210_, 27, v_n_6195_);
lean_ctor_set(v_reuseFailAlloc_6210_, 28, v_N_6196_);
lean_ctor_set(v_reuseFailAlloc_6210_, 29, v_V_6197_);
lean_ctor_set(v_reuseFailAlloc_6210_, 30, v_z_6198_);
lean_ctor_set(v_reuseFailAlloc_6210_, 31, v_zabbrev_6199_);
lean_ctor_set(v_reuseFailAlloc_6210_, 32, v___x_6207_);
lean_ctor_set(v_reuseFailAlloc_6210_, 33, v_O_6200_);
lean_ctor_set(v_reuseFailAlloc_6210_, 34, v_X_6201_);
lean_ctor_set(v_reuseFailAlloc_6210_, 35, v_x_6202_);
lean_ctor_set(v_reuseFailAlloc_6210_, 36, v_Z_6203_);
v___x_6209_ = v_reuseFailAlloc_6210_;
goto v_reusejp_6208_;
}
v_reusejp_6208_:
{
return v___x_6209_;
}
}
}
case 32:
{
lean_object* v_G_6213_; lean_object* v_y_6214_; lean_object* v_u_6215_; lean_object* v_Y_6216_; lean_object* v_D_6217_; lean_object* v_M_6218_; lean_object* v_L_6219_; lean_object* v_d_6220_; lean_object* v_Q_6221_; lean_object* v_q_6222_; lean_object* v_w_6223_; lean_object* v_W_6224_; lean_object* v_E_6225_; lean_object* v_e_6226_; lean_object* v_c_6227_; lean_object* v_F_6228_; lean_object* v_a_6229_; lean_object* v_b_6230_; lean_object* v_B_6231_; lean_object* v_h_6232_; lean_object* v_K_6233_; lean_object* v_k_6234_; lean_object* v_H_6235_; lean_object* v_m_6236_; lean_object* v_s_6237_; lean_object* v_S_6238_; lean_object* v_A_6239_; lean_object* v_n_6240_; lean_object* v_N_6241_; lean_object* v_V_6242_; lean_object* v_z_6243_; lean_object* v_zabbrev_6244_; lean_object* v_v_6245_; lean_object* v_X_6246_; lean_object* v_x_6247_; lean_object* v_Z_6248_; lean_object* v___x_6250_; uint8_t v_isShared_6251_; uint8_t v_isSharedCheck_6256_; 
lean_dec_ref_known(v_modifier_4557_, 0);
v_G_6213_ = lean_ctor_get(v_date_4556_, 0);
v_y_6214_ = lean_ctor_get(v_date_4556_, 1);
v_u_6215_ = lean_ctor_get(v_date_4556_, 2);
v_Y_6216_ = lean_ctor_get(v_date_4556_, 3);
v_D_6217_ = lean_ctor_get(v_date_4556_, 4);
v_M_6218_ = lean_ctor_get(v_date_4556_, 5);
v_L_6219_ = lean_ctor_get(v_date_4556_, 6);
v_d_6220_ = lean_ctor_get(v_date_4556_, 7);
v_Q_6221_ = lean_ctor_get(v_date_4556_, 8);
v_q_6222_ = lean_ctor_get(v_date_4556_, 9);
v_w_6223_ = lean_ctor_get(v_date_4556_, 10);
v_W_6224_ = lean_ctor_get(v_date_4556_, 11);
v_E_6225_ = lean_ctor_get(v_date_4556_, 12);
v_e_6226_ = lean_ctor_get(v_date_4556_, 13);
v_c_6227_ = lean_ctor_get(v_date_4556_, 14);
v_F_6228_ = lean_ctor_get(v_date_4556_, 15);
v_a_6229_ = lean_ctor_get(v_date_4556_, 16);
v_b_6230_ = lean_ctor_get(v_date_4556_, 17);
v_B_6231_ = lean_ctor_get(v_date_4556_, 18);
v_h_6232_ = lean_ctor_get(v_date_4556_, 19);
v_K_6233_ = lean_ctor_get(v_date_4556_, 20);
v_k_6234_ = lean_ctor_get(v_date_4556_, 21);
v_H_6235_ = lean_ctor_get(v_date_4556_, 22);
v_m_6236_ = lean_ctor_get(v_date_4556_, 23);
v_s_6237_ = lean_ctor_get(v_date_4556_, 24);
v_S_6238_ = lean_ctor_get(v_date_4556_, 25);
v_A_6239_ = lean_ctor_get(v_date_4556_, 26);
v_n_6240_ = lean_ctor_get(v_date_4556_, 27);
v_N_6241_ = lean_ctor_get(v_date_4556_, 28);
v_V_6242_ = lean_ctor_get(v_date_4556_, 29);
v_z_6243_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_6244_ = lean_ctor_get(v_date_4556_, 31);
v_v_6245_ = lean_ctor_get(v_date_4556_, 32);
v_X_6246_ = lean_ctor_get(v_date_4556_, 34);
v_x_6247_ = lean_ctor_get(v_date_4556_, 35);
v_Z_6248_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_6256_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_6256_ == 0)
{
lean_object* v_unused_6257_; 
v_unused_6257_ = lean_ctor_get(v_date_4556_, 33);
lean_dec(v_unused_6257_);
v___x_6250_ = v_date_4556_;
v_isShared_6251_ = v_isSharedCheck_6256_;
goto v_resetjp_6249_;
}
else
{
lean_inc(v_Z_6248_);
lean_inc(v_x_6247_);
lean_inc(v_X_6246_);
lean_inc(v_v_6245_);
lean_inc(v_zabbrev_6244_);
lean_inc(v_z_6243_);
lean_inc(v_V_6242_);
lean_inc(v_N_6241_);
lean_inc(v_n_6240_);
lean_inc(v_A_6239_);
lean_inc(v_S_6238_);
lean_inc(v_s_6237_);
lean_inc(v_m_6236_);
lean_inc(v_H_6235_);
lean_inc(v_k_6234_);
lean_inc(v_K_6233_);
lean_inc(v_h_6232_);
lean_inc(v_B_6231_);
lean_inc(v_b_6230_);
lean_inc(v_a_6229_);
lean_inc(v_F_6228_);
lean_inc(v_c_6227_);
lean_inc(v_e_6226_);
lean_inc(v_E_6225_);
lean_inc(v_W_6224_);
lean_inc(v_w_6223_);
lean_inc(v_q_6222_);
lean_inc(v_Q_6221_);
lean_inc(v_d_6220_);
lean_inc(v_L_6219_);
lean_inc(v_M_6218_);
lean_inc(v_D_6217_);
lean_inc(v_Y_6216_);
lean_inc(v_u_6215_);
lean_inc(v_y_6214_);
lean_inc(v_G_6213_);
lean_dec(v_date_4556_);
v___x_6250_ = lean_box(0);
v_isShared_6251_ = v_isSharedCheck_6256_;
goto v_resetjp_6249_;
}
v_resetjp_6249_:
{
lean_object* v___x_6252_; lean_object* v___x_6254_; 
v___x_6252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6252_, 0, v_data_4558_);
if (v_isShared_6251_ == 0)
{
lean_ctor_set(v___x_6250_, 33, v___x_6252_);
v___x_6254_ = v___x_6250_;
goto v_reusejp_6253_;
}
else
{
lean_object* v_reuseFailAlloc_6255_; 
v_reuseFailAlloc_6255_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6255_, 0, v_G_6213_);
lean_ctor_set(v_reuseFailAlloc_6255_, 1, v_y_6214_);
lean_ctor_set(v_reuseFailAlloc_6255_, 2, v_u_6215_);
lean_ctor_set(v_reuseFailAlloc_6255_, 3, v_Y_6216_);
lean_ctor_set(v_reuseFailAlloc_6255_, 4, v_D_6217_);
lean_ctor_set(v_reuseFailAlloc_6255_, 5, v_M_6218_);
lean_ctor_set(v_reuseFailAlloc_6255_, 6, v_L_6219_);
lean_ctor_set(v_reuseFailAlloc_6255_, 7, v_d_6220_);
lean_ctor_set(v_reuseFailAlloc_6255_, 8, v_Q_6221_);
lean_ctor_set(v_reuseFailAlloc_6255_, 9, v_q_6222_);
lean_ctor_set(v_reuseFailAlloc_6255_, 10, v_w_6223_);
lean_ctor_set(v_reuseFailAlloc_6255_, 11, v_W_6224_);
lean_ctor_set(v_reuseFailAlloc_6255_, 12, v_E_6225_);
lean_ctor_set(v_reuseFailAlloc_6255_, 13, v_e_6226_);
lean_ctor_set(v_reuseFailAlloc_6255_, 14, v_c_6227_);
lean_ctor_set(v_reuseFailAlloc_6255_, 15, v_F_6228_);
lean_ctor_set(v_reuseFailAlloc_6255_, 16, v_a_6229_);
lean_ctor_set(v_reuseFailAlloc_6255_, 17, v_b_6230_);
lean_ctor_set(v_reuseFailAlloc_6255_, 18, v_B_6231_);
lean_ctor_set(v_reuseFailAlloc_6255_, 19, v_h_6232_);
lean_ctor_set(v_reuseFailAlloc_6255_, 20, v_K_6233_);
lean_ctor_set(v_reuseFailAlloc_6255_, 21, v_k_6234_);
lean_ctor_set(v_reuseFailAlloc_6255_, 22, v_H_6235_);
lean_ctor_set(v_reuseFailAlloc_6255_, 23, v_m_6236_);
lean_ctor_set(v_reuseFailAlloc_6255_, 24, v_s_6237_);
lean_ctor_set(v_reuseFailAlloc_6255_, 25, v_S_6238_);
lean_ctor_set(v_reuseFailAlloc_6255_, 26, v_A_6239_);
lean_ctor_set(v_reuseFailAlloc_6255_, 27, v_n_6240_);
lean_ctor_set(v_reuseFailAlloc_6255_, 28, v_N_6241_);
lean_ctor_set(v_reuseFailAlloc_6255_, 29, v_V_6242_);
lean_ctor_set(v_reuseFailAlloc_6255_, 30, v_z_6243_);
lean_ctor_set(v_reuseFailAlloc_6255_, 31, v_zabbrev_6244_);
lean_ctor_set(v_reuseFailAlloc_6255_, 32, v_v_6245_);
lean_ctor_set(v_reuseFailAlloc_6255_, 33, v___x_6252_);
lean_ctor_set(v_reuseFailAlloc_6255_, 34, v_X_6246_);
lean_ctor_set(v_reuseFailAlloc_6255_, 35, v_x_6247_);
lean_ctor_set(v_reuseFailAlloc_6255_, 36, v_Z_6248_);
v___x_6254_ = v_reuseFailAlloc_6255_;
goto v_reusejp_6253_;
}
v_reusejp_6253_:
{
return v___x_6254_;
}
}
}
case 33:
{
lean_object* v_G_6258_; lean_object* v_y_6259_; lean_object* v_u_6260_; lean_object* v_Y_6261_; lean_object* v_D_6262_; lean_object* v_M_6263_; lean_object* v_L_6264_; lean_object* v_d_6265_; lean_object* v_Q_6266_; lean_object* v_q_6267_; lean_object* v_w_6268_; lean_object* v_W_6269_; lean_object* v_E_6270_; lean_object* v_e_6271_; lean_object* v_c_6272_; lean_object* v_F_6273_; lean_object* v_a_6274_; lean_object* v_b_6275_; lean_object* v_B_6276_; lean_object* v_h_6277_; lean_object* v_K_6278_; lean_object* v_k_6279_; lean_object* v_H_6280_; lean_object* v_m_6281_; lean_object* v_s_6282_; lean_object* v_S_6283_; lean_object* v_A_6284_; lean_object* v_n_6285_; lean_object* v_N_6286_; lean_object* v_V_6287_; lean_object* v_z_6288_; lean_object* v_zabbrev_6289_; lean_object* v_v_6290_; lean_object* v_O_6291_; lean_object* v_x_6292_; lean_object* v_Z_6293_; lean_object* v___x_6295_; uint8_t v_isShared_6296_; uint8_t v_isSharedCheck_6301_; 
lean_dec_ref_known(v_modifier_4557_, 0);
v_G_6258_ = lean_ctor_get(v_date_4556_, 0);
v_y_6259_ = lean_ctor_get(v_date_4556_, 1);
v_u_6260_ = lean_ctor_get(v_date_4556_, 2);
v_Y_6261_ = lean_ctor_get(v_date_4556_, 3);
v_D_6262_ = lean_ctor_get(v_date_4556_, 4);
v_M_6263_ = lean_ctor_get(v_date_4556_, 5);
v_L_6264_ = lean_ctor_get(v_date_4556_, 6);
v_d_6265_ = lean_ctor_get(v_date_4556_, 7);
v_Q_6266_ = lean_ctor_get(v_date_4556_, 8);
v_q_6267_ = lean_ctor_get(v_date_4556_, 9);
v_w_6268_ = lean_ctor_get(v_date_4556_, 10);
v_W_6269_ = lean_ctor_get(v_date_4556_, 11);
v_E_6270_ = lean_ctor_get(v_date_4556_, 12);
v_e_6271_ = lean_ctor_get(v_date_4556_, 13);
v_c_6272_ = lean_ctor_get(v_date_4556_, 14);
v_F_6273_ = lean_ctor_get(v_date_4556_, 15);
v_a_6274_ = lean_ctor_get(v_date_4556_, 16);
v_b_6275_ = lean_ctor_get(v_date_4556_, 17);
v_B_6276_ = lean_ctor_get(v_date_4556_, 18);
v_h_6277_ = lean_ctor_get(v_date_4556_, 19);
v_K_6278_ = lean_ctor_get(v_date_4556_, 20);
v_k_6279_ = lean_ctor_get(v_date_4556_, 21);
v_H_6280_ = lean_ctor_get(v_date_4556_, 22);
v_m_6281_ = lean_ctor_get(v_date_4556_, 23);
v_s_6282_ = lean_ctor_get(v_date_4556_, 24);
v_S_6283_ = lean_ctor_get(v_date_4556_, 25);
v_A_6284_ = lean_ctor_get(v_date_4556_, 26);
v_n_6285_ = lean_ctor_get(v_date_4556_, 27);
v_N_6286_ = lean_ctor_get(v_date_4556_, 28);
v_V_6287_ = lean_ctor_get(v_date_4556_, 29);
v_z_6288_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_6289_ = lean_ctor_get(v_date_4556_, 31);
v_v_6290_ = lean_ctor_get(v_date_4556_, 32);
v_O_6291_ = lean_ctor_get(v_date_4556_, 33);
v_x_6292_ = lean_ctor_get(v_date_4556_, 35);
v_Z_6293_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_6301_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_6301_ == 0)
{
lean_object* v_unused_6302_; 
v_unused_6302_ = lean_ctor_get(v_date_4556_, 34);
lean_dec(v_unused_6302_);
v___x_6295_ = v_date_4556_;
v_isShared_6296_ = v_isSharedCheck_6301_;
goto v_resetjp_6294_;
}
else
{
lean_inc(v_Z_6293_);
lean_inc(v_x_6292_);
lean_inc(v_O_6291_);
lean_inc(v_v_6290_);
lean_inc(v_zabbrev_6289_);
lean_inc(v_z_6288_);
lean_inc(v_V_6287_);
lean_inc(v_N_6286_);
lean_inc(v_n_6285_);
lean_inc(v_A_6284_);
lean_inc(v_S_6283_);
lean_inc(v_s_6282_);
lean_inc(v_m_6281_);
lean_inc(v_H_6280_);
lean_inc(v_k_6279_);
lean_inc(v_K_6278_);
lean_inc(v_h_6277_);
lean_inc(v_B_6276_);
lean_inc(v_b_6275_);
lean_inc(v_a_6274_);
lean_inc(v_F_6273_);
lean_inc(v_c_6272_);
lean_inc(v_e_6271_);
lean_inc(v_E_6270_);
lean_inc(v_W_6269_);
lean_inc(v_w_6268_);
lean_inc(v_q_6267_);
lean_inc(v_Q_6266_);
lean_inc(v_d_6265_);
lean_inc(v_L_6264_);
lean_inc(v_M_6263_);
lean_inc(v_D_6262_);
lean_inc(v_Y_6261_);
lean_inc(v_u_6260_);
lean_inc(v_y_6259_);
lean_inc(v_G_6258_);
lean_dec(v_date_4556_);
v___x_6295_ = lean_box(0);
v_isShared_6296_ = v_isSharedCheck_6301_;
goto v_resetjp_6294_;
}
v_resetjp_6294_:
{
lean_object* v___x_6297_; lean_object* v___x_6299_; 
v___x_6297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6297_, 0, v_data_4558_);
if (v_isShared_6296_ == 0)
{
lean_ctor_set(v___x_6295_, 34, v___x_6297_);
v___x_6299_ = v___x_6295_;
goto v_reusejp_6298_;
}
else
{
lean_object* v_reuseFailAlloc_6300_; 
v_reuseFailAlloc_6300_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6300_, 0, v_G_6258_);
lean_ctor_set(v_reuseFailAlloc_6300_, 1, v_y_6259_);
lean_ctor_set(v_reuseFailAlloc_6300_, 2, v_u_6260_);
lean_ctor_set(v_reuseFailAlloc_6300_, 3, v_Y_6261_);
lean_ctor_set(v_reuseFailAlloc_6300_, 4, v_D_6262_);
lean_ctor_set(v_reuseFailAlloc_6300_, 5, v_M_6263_);
lean_ctor_set(v_reuseFailAlloc_6300_, 6, v_L_6264_);
lean_ctor_set(v_reuseFailAlloc_6300_, 7, v_d_6265_);
lean_ctor_set(v_reuseFailAlloc_6300_, 8, v_Q_6266_);
lean_ctor_set(v_reuseFailAlloc_6300_, 9, v_q_6267_);
lean_ctor_set(v_reuseFailAlloc_6300_, 10, v_w_6268_);
lean_ctor_set(v_reuseFailAlloc_6300_, 11, v_W_6269_);
lean_ctor_set(v_reuseFailAlloc_6300_, 12, v_E_6270_);
lean_ctor_set(v_reuseFailAlloc_6300_, 13, v_e_6271_);
lean_ctor_set(v_reuseFailAlloc_6300_, 14, v_c_6272_);
lean_ctor_set(v_reuseFailAlloc_6300_, 15, v_F_6273_);
lean_ctor_set(v_reuseFailAlloc_6300_, 16, v_a_6274_);
lean_ctor_set(v_reuseFailAlloc_6300_, 17, v_b_6275_);
lean_ctor_set(v_reuseFailAlloc_6300_, 18, v_B_6276_);
lean_ctor_set(v_reuseFailAlloc_6300_, 19, v_h_6277_);
lean_ctor_set(v_reuseFailAlloc_6300_, 20, v_K_6278_);
lean_ctor_set(v_reuseFailAlloc_6300_, 21, v_k_6279_);
lean_ctor_set(v_reuseFailAlloc_6300_, 22, v_H_6280_);
lean_ctor_set(v_reuseFailAlloc_6300_, 23, v_m_6281_);
lean_ctor_set(v_reuseFailAlloc_6300_, 24, v_s_6282_);
lean_ctor_set(v_reuseFailAlloc_6300_, 25, v_S_6283_);
lean_ctor_set(v_reuseFailAlloc_6300_, 26, v_A_6284_);
lean_ctor_set(v_reuseFailAlloc_6300_, 27, v_n_6285_);
lean_ctor_set(v_reuseFailAlloc_6300_, 28, v_N_6286_);
lean_ctor_set(v_reuseFailAlloc_6300_, 29, v_V_6287_);
lean_ctor_set(v_reuseFailAlloc_6300_, 30, v_z_6288_);
lean_ctor_set(v_reuseFailAlloc_6300_, 31, v_zabbrev_6289_);
lean_ctor_set(v_reuseFailAlloc_6300_, 32, v_v_6290_);
lean_ctor_set(v_reuseFailAlloc_6300_, 33, v_O_6291_);
lean_ctor_set(v_reuseFailAlloc_6300_, 34, v___x_6297_);
lean_ctor_set(v_reuseFailAlloc_6300_, 35, v_x_6292_);
lean_ctor_set(v_reuseFailAlloc_6300_, 36, v_Z_6293_);
v___x_6299_ = v_reuseFailAlloc_6300_;
goto v_reusejp_6298_;
}
v_reusejp_6298_:
{
return v___x_6299_;
}
}
}
case 34:
{
lean_object* v_G_6303_; lean_object* v_y_6304_; lean_object* v_u_6305_; lean_object* v_Y_6306_; lean_object* v_D_6307_; lean_object* v_M_6308_; lean_object* v_L_6309_; lean_object* v_d_6310_; lean_object* v_Q_6311_; lean_object* v_q_6312_; lean_object* v_w_6313_; lean_object* v_W_6314_; lean_object* v_E_6315_; lean_object* v_e_6316_; lean_object* v_c_6317_; lean_object* v_F_6318_; lean_object* v_a_6319_; lean_object* v_b_6320_; lean_object* v_B_6321_; lean_object* v_h_6322_; lean_object* v_K_6323_; lean_object* v_k_6324_; lean_object* v_H_6325_; lean_object* v_m_6326_; lean_object* v_s_6327_; lean_object* v_S_6328_; lean_object* v_A_6329_; lean_object* v_n_6330_; lean_object* v_N_6331_; lean_object* v_V_6332_; lean_object* v_z_6333_; lean_object* v_zabbrev_6334_; lean_object* v_v_6335_; lean_object* v_O_6336_; lean_object* v_X_6337_; lean_object* v_Z_6338_; lean_object* v___x_6340_; uint8_t v_isShared_6341_; uint8_t v_isSharedCheck_6346_; 
lean_dec_ref_known(v_modifier_4557_, 0);
v_G_6303_ = lean_ctor_get(v_date_4556_, 0);
v_y_6304_ = lean_ctor_get(v_date_4556_, 1);
v_u_6305_ = lean_ctor_get(v_date_4556_, 2);
v_Y_6306_ = lean_ctor_get(v_date_4556_, 3);
v_D_6307_ = lean_ctor_get(v_date_4556_, 4);
v_M_6308_ = lean_ctor_get(v_date_4556_, 5);
v_L_6309_ = lean_ctor_get(v_date_4556_, 6);
v_d_6310_ = lean_ctor_get(v_date_4556_, 7);
v_Q_6311_ = lean_ctor_get(v_date_4556_, 8);
v_q_6312_ = lean_ctor_get(v_date_4556_, 9);
v_w_6313_ = lean_ctor_get(v_date_4556_, 10);
v_W_6314_ = lean_ctor_get(v_date_4556_, 11);
v_E_6315_ = lean_ctor_get(v_date_4556_, 12);
v_e_6316_ = lean_ctor_get(v_date_4556_, 13);
v_c_6317_ = lean_ctor_get(v_date_4556_, 14);
v_F_6318_ = lean_ctor_get(v_date_4556_, 15);
v_a_6319_ = lean_ctor_get(v_date_4556_, 16);
v_b_6320_ = lean_ctor_get(v_date_4556_, 17);
v_B_6321_ = lean_ctor_get(v_date_4556_, 18);
v_h_6322_ = lean_ctor_get(v_date_4556_, 19);
v_K_6323_ = lean_ctor_get(v_date_4556_, 20);
v_k_6324_ = lean_ctor_get(v_date_4556_, 21);
v_H_6325_ = lean_ctor_get(v_date_4556_, 22);
v_m_6326_ = lean_ctor_get(v_date_4556_, 23);
v_s_6327_ = lean_ctor_get(v_date_4556_, 24);
v_S_6328_ = lean_ctor_get(v_date_4556_, 25);
v_A_6329_ = lean_ctor_get(v_date_4556_, 26);
v_n_6330_ = lean_ctor_get(v_date_4556_, 27);
v_N_6331_ = lean_ctor_get(v_date_4556_, 28);
v_V_6332_ = lean_ctor_get(v_date_4556_, 29);
v_z_6333_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_6334_ = lean_ctor_get(v_date_4556_, 31);
v_v_6335_ = lean_ctor_get(v_date_4556_, 32);
v_O_6336_ = lean_ctor_get(v_date_4556_, 33);
v_X_6337_ = lean_ctor_get(v_date_4556_, 34);
v_Z_6338_ = lean_ctor_get(v_date_4556_, 36);
v_isSharedCheck_6346_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_6346_ == 0)
{
lean_object* v_unused_6347_; 
v_unused_6347_ = lean_ctor_get(v_date_4556_, 35);
lean_dec(v_unused_6347_);
v___x_6340_ = v_date_4556_;
v_isShared_6341_ = v_isSharedCheck_6346_;
goto v_resetjp_6339_;
}
else
{
lean_inc(v_Z_6338_);
lean_inc(v_X_6337_);
lean_inc(v_O_6336_);
lean_inc(v_v_6335_);
lean_inc(v_zabbrev_6334_);
lean_inc(v_z_6333_);
lean_inc(v_V_6332_);
lean_inc(v_N_6331_);
lean_inc(v_n_6330_);
lean_inc(v_A_6329_);
lean_inc(v_S_6328_);
lean_inc(v_s_6327_);
lean_inc(v_m_6326_);
lean_inc(v_H_6325_);
lean_inc(v_k_6324_);
lean_inc(v_K_6323_);
lean_inc(v_h_6322_);
lean_inc(v_B_6321_);
lean_inc(v_b_6320_);
lean_inc(v_a_6319_);
lean_inc(v_F_6318_);
lean_inc(v_c_6317_);
lean_inc(v_e_6316_);
lean_inc(v_E_6315_);
lean_inc(v_W_6314_);
lean_inc(v_w_6313_);
lean_inc(v_q_6312_);
lean_inc(v_Q_6311_);
lean_inc(v_d_6310_);
lean_inc(v_L_6309_);
lean_inc(v_M_6308_);
lean_inc(v_D_6307_);
lean_inc(v_Y_6306_);
lean_inc(v_u_6305_);
lean_inc(v_y_6304_);
lean_inc(v_G_6303_);
lean_dec(v_date_4556_);
v___x_6340_ = lean_box(0);
v_isShared_6341_ = v_isSharedCheck_6346_;
goto v_resetjp_6339_;
}
v_resetjp_6339_:
{
lean_object* v___x_6342_; lean_object* v___x_6344_; 
v___x_6342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6342_, 0, v_data_4558_);
if (v_isShared_6341_ == 0)
{
lean_ctor_set(v___x_6340_, 35, v___x_6342_);
v___x_6344_ = v___x_6340_;
goto v_reusejp_6343_;
}
else
{
lean_object* v_reuseFailAlloc_6345_; 
v_reuseFailAlloc_6345_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6345_, 0, v_G_6303_);
lean_ctor_set(v_reuseFailAlloc_6345_, 1, v_y_6304_);
lean_ctor_set(v_reuseFailAlloc_6345_, 2, v_u_6305_);
lean_ctor_set(v_reuseFailAlloc_6345_, 3, v_Y_6306_);
lean_ctor_set(v_reuseFailAlloc_6345_, 4, v_D_6307_);
lean_ctor_set(v_reuseFailAlloc_6345_, 5, v_M_6308_);
lean_ctor_set(v_reuseFailAlloc_6345_, 6, v_L_6309_);
lean_ctor_set(v_reuseFailAlloc_6345_, 7, v_d_6310_);
lean_ctor_set(v_reuseFailAlloc_6345_, 8, v_Q_6311_);
lean_ctor_set(v_reuseFailAlloc_6345_, 9, v_q_6312_);
lean_ctor_set(v_reuseFailAlloc_6345_, 10, v_w_6313_);
lean_ctor_set(v_reuseFailAlloc_6345_, 11, v_W_6314_);
lean_ctor_set(v_reuseFailAlloc_6345_, 12, v_E_6315_);
lean_ctor_set(v_reuseFailAlloc_6345_, 13, v_e_6316_);
lean_ctor_set(v_reuseFailAlloc_6345_, 14, v_c_6317_);
lean_ctor_set(v_reuseFailAlloc_6345_, 15, v_F_6318_);
lean_ctor_set(v_reuseFailAlloc_6345_, 16, v_a_6319_);
lean_ctor_set(v_reuseFailAlloc_6345_, 17, v_b_6320_);
lean_ctor_set(v_reuseFailAlloc_6345_, 18, v_B_6321_);
lean_ctor_set(v_reuseFailAlloc_6345_, 19, v_h_6322_);
lean_ctor_set(v_reuseFailAlloc_6345_, 20, v_K_6323_);
lean_ctor_set(v_reuseFailAlloc_6345_, 21, v_k_6324_);
lean_ctor_set(v_reuseFailAlloc_6345_, 22, v_H_6325_);
lean_ctor_set(v_reuseFailAlloc_6345_, 23, v_m_6326_);
lean_ctor_set(v_reuseFailAlloc_6345_, 24, v_s_6327_);
lean_ctor_set(v_reuseFailAlloc_6345_, 25, v_S_6328_);
lean_ctor_set(v_reuseFailAlloc_6345_, 26, v_A_6329_);
lean_ctor_set(v_reuseFailAlloc_6345_, 27, v_n_6330_);
lean_ctor_set(v_reuseFailAlloc_6345_, 28, v_N_6331_);
lean_ctor_set(v_reuseFailAlloc_6345_, 29, v_V_6332_);
lean_ctor_set(v_reuseFailAlloc_6345_, 30, v_z_6333_);
lean_ctor_set(v_reuseFailAlloc_6345_, 31, v_zabbrev_6334_);
lean_ctor_set(v_reuseFailAlloc_6345_, 32, v_v_6335_);
lean_ctor_set(v_reuseFailAlloc_6345_, 33, v_O_6336_);
lean_ctor_set(v_reuseFailAlloc_6345_, 34, v_X_6337_);
lean_ctor_set(v_reuseFailAlloc_6345_, 35, v___x_6342_);
lean_ctor_set(v_reuseFailAlloc_6345_, 36, v_Z_6338_);
v___x_6344_ = v_reuseFailAlloc_6345_;
goto v_reusejp_6343_;
}
v_reusejp_6343_:
{
return v___x_6344_;
}
}
}
default: 
{
lean_object* v_G_6348_; lean_object* v_y_6349_; lean_object* v_u_6350_; lean_object* v_Y_6351_; lean_object* v_D_6352_; lean_object* v_M_6353_; lean_object* v_L_6354_; lean_object* v_d_6355_; lean_object* v_Q_6356_; lean_object* v_q_6357_; lean_object* v_w_6358_; lean_object* v_W_6359_; lean_object* v_E_6360_; lean_object* v_e_6361_; lean_object* v_c_6362_; lean_object* v_F_6363_; lean_object* v_a_6364_; lean_object* v_b_6365_; lean_object* v_B_6366_; lean_object* v_h_6367_; lean_object* v_K_6368_; lean_object* v_k_6369_; lean_object* v_H_6370_; lean_object* v_m_6371_; lean_object* v_s_6372_; lean_object* v_S_6373_; lean_object* v_A_6374_; lean_object* v_n_6375_; lean_object* v_N_6376_; lean_object* v_V_6377_; lean_object* v_z_6378_; lean_object* v_zabbrev_6379_; lean_object* v_v_6380_; lean_object* v_O_6381_; lean_object* v_X_6382_; lean_object* v_x_6383_; lean_object* v___x_6385_; uint8_t v_isShared_6386_; uint8_t v_isSharedCheck_6391_; 
lean_dec_ref_known(v_modifier_4557_, 0);
v_G_6348_ = lean_ctor_get(v_date_4556_, 0);
v_y_6349_ = lean_ctor_get(v_date_4556_, 1);
v_u_6350_ = lean_ctor_get(v_date_4556_, 2);
v_Y_6351_ = lean_ctor_get(v_date_4556_, 3);
v_D_6352_ = lean_ctor_get(v_date_4556_, 4);
v_M_6353_ = lean_ctor_get(v_date_4556_, 5);
v_L_6354_ = lean_ctor_get(v_date_4556_, 6);
v_d_6355_ = lean_ctor_get(v_date_4556_, 7);
v_Q_6356_ = lean_ctor_get(v_date_4556_, 8);
v_q_6357_ = lean_ctor_get(v_date_4556_, 9);
v_w_6358_ = lean_ctor_get(v_date_4556_, 10);
v_W_6359_ = lean_ctor_get(v_date_4556_, 11);
v_E_6360_ = lean_ctor_get(v_date_4556_, 12);
v_e_6361_ = lean_ctor_get(v_date_4556_, 13);
v_c_6362_ = lean_ctor_get(v_date_4556_, 14);
v_F_6363_ = lean_ctor_get(v_date_4556_, 15);
v_a_6364_ = lean_ctor_get(v_date_4556_, 16);
v_b_6365_ = lean_ctor_get(v_date_4556_, 17);
v_B_6366_ = lean_ctor_get(v_date_4556_, 18);
v_h_6367_ = lean_ctor_get(v_date_4556_, 19);
v_K_6368_ = lean_ctor_get(v_date_4556_, 20);
v_k_6369_ = lean_ctor_get(v_date_4556_, 21);
v_H_6370_ = lean_ctor_get(v_date_4556_, 22);
v_m_6371_ = lean_ctor_get(v_date_4556_, 23);
v_s_6372_ = lean_ctor_get(v_date_4556_, 24);
v_S_6373_ = lean_ctor_get(v_date_4556_, 25);
v_A_6374_ = lean_ctor_get(v_date_4556_, 26);
v_n_6375_ = lean_ctor_get(v_date_4556_, 27);
v_N_6376_ = lean_ctor_get(v_date_4556_, 28);
v_V_6377_ = lean_ctor_get(v_date_4556_, 29);
v_z_6378_ = lean_ctor_get(v_date_4556_, 30);
v_zabbrev_6379_ = lean_ctor_get(v_date_4556_, 31);
v_v_6380_ = lean_ctor_get(v_date_4556_, 32);
v_O_6381_ = lean_ctor_get(v_date_4556_, 33);
v_X_6382_ = lean_ctor_get(v_date_4556_, 34);
v_x_6383_ = lean_ctor_get(v_date_4556_, 35);
v_isSharedCheck_6391_ = !lean_is_exclusive(v_date_4556_);
if (v_isSharedCheck_6391_ == 0)
{
lean_object* v_unused_6392_; 
v_unused_6392_ = lean_ctor_get(v_date_4556_, 36);
lean_dec(v_unused_6392_);
v___x_6385_ = v_date_4556_;
v_isShared_6386_ = v_isSharedCheck_6391_;
goto v_resetjp_6384_;
}
else
{
lean_inc(v_x_6383_);
lean_inc(v_X_6382_);
lean_inc(v_O_6381_);
lean_inc(v_v_6380_);
lean_inc(v_zabbrev_6379_);
lean_inc(v_z_6378_);
lean_inc(v_V_6377_);
lean_inc(v_N_6376_);
lean_inc(v_n_6375_);
lean_inc(v_A_6374_);
lean_inc(v_S_6373_);
lean_inc(v_s_6372_);
lean_inc(v_m_6371_);
lean_inc(v_H_6370_);
lean_inc(v_k_6369_);
lean_inc(v_K_6368_);
lean_inc(v_h_6367_);
lean_inc(v_B_6366_);
lean_inc(v_b_6365_);
lean_inc(v_a_6364_);
lean_inc(v_F_6363_);
lean_inc(v_c_6362_);
lean_inc(v_e_6361_);
lean_inc(v_E_6360_);
lean_inc(v_W_6359_);
lean_inc(v_w_6358_);
lean_inc(v_q_6357_);
lean_inc(v_Q_6356_);
lean_inc(v_d_6355_);
lean_inc(v_L_6354_);
lean_inc(v_M_6353_);
lean_inc(v_D_6352_);
lean_inc(v_Y_6351_);
lean_inc(v_u_6350_);
lean_inc(v_y_6349_);
lean_inc(v_G_6348_);
lean_dec(v_date_4556_);
v___x_6385_ = lean_box(0);
v_isShared_6386_ = v_isSharedCheck_6391_;
goto v_resetjp_6384_;
}
v_resetjp_6384_:
{
lean_object* v___x_6387_; lean_object* v___x_6389_; 
v___x_6387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6387_, 0, v_data_4558_);
if (v_isShared_6386_ == 0)
{
lean_ctor_set(v___x_6385_, 36, v___x_6387_);
v___x_6389_ = v___x_6385_;
goto v_reusejp_6388_;
}
else
{
lean_object* v_reuseFailAlloc_6390_; 
v_reuseFailAlloc_6390_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6390_, 0, v_G_6348_);
lean_ctor_set(v_reuseFailAlloc_6390_, 1, v_y_6349_);
lean_ctor_set(v_reuseFailAlloc_6390_, 2, v_u_6350_);
lean_ctor_set(v_reuseFailAlloc_6390_, 3, v_Y_6351_);
lean_ctor_set(v_reuseFailAlloc_6390_, 4, v_D_6352_);
lean_ctor_set(v_reuseFailAlloc_6390_, 5, v_M_6353_);
lean_ctor_set(v_reuseFailAlloc_6390_, 6, v_L_6354_);
lean_ctor_set(v_reuseFailAlloc_6390_, 7, v_d_6355_);
lean_ctor_set(v_reuseFailAlloc_6390_, 8, v_Q_6356_);
lean_ctor_set(v_reuseFailAlloc_6390_, 9, v_q_6357_);
lean_ctor_set(v_reuseFailAlloc_6390_, 10, v_w_6358_);
lean_ctor_set(v_reuseFailAlloc_6390_, 11, v_W_6359_);
lean_ctor_set(v_reuseFailAlloc_6390_, 12, v_E_6360_);
lean_ctor_set(v_reuseFailAlloc_6390_, 13, v_e_6361_);
lean_ctor_set(v_reuseFailAlloc_6390_, 14, v_c_6362_);
lean_ctor_set(v_reuseFailAlloc_6390_, 15, v_F_6363_);
lean_ctor_set(v_reuseFailAlloc_6390_, 16, v_a_6364_);
lean_ctor_set(v_reuseFailAlloc_6390_, 17, v_b_6365_);
lean_ctor_set(v_reuseFailAlloc_6390_, 18, v_B_6366_);
lean_ctor_set(v_reuseFailAlloc_6390_, 19, v_h_6367_);
lean_ctor_set(v_reuseFailAlloc_6390_, 20, v_K_6368_);
lean_ctor_set(v_reuseFailAlloc_6390_, 21, v_k_6369_);
lean_ctor_set(v_reuseFailAlloc_6390_, 22, v_H_6370_);
lean_ctor_set(v_reuseFailAlloc_6390_, 23, v_m_6371_);
lean_ctor_set(v_reuseFailAlloc_6390_, 24, v_s_6372_);
lean_ctor_set(v_reuseFailAlloc_6390_, 25, v_S_6373_);
lean_ctor_set(v_reuseFailAlloc_6390_, 26, v_A_6374_);
lean_ctor_set(v_reuseFailAlloc_6390_, 27, v_n_6375_);
lean_ctor_set(v_reuseFailAlloc_6390_, 28, v_N_6376_);
lean_ctor_set(v_reuseFailAlloc_6390_, 29, v_V_6377_);
lean_ctor_set(v_reuseFailAlloc_6390_, 30, v_z_6378_);
lean_ctor_set(v_reuseFailAlloc_6390_, 31, v_zabbrev_6379_);
lean_ctor_set(v_reuseFailAlloc_6390_, 32, v_v_6380_);
lean_ctor_set(v_reuseFailAlloc_6390_, 33, v_O_6381_);
lean_ctor_set(v_reuseFailAlloc_6390_, 34, v_X_6382_);
lean_ctor_set(v_reuseFailAlloc_6390_, 35, v_x_6383_);
lean_ctor_set(v_reuseFailAlloc_6390_, 36, v___x_6387_);
v___x_6389_ = v_reuseFailAlloc_6390_;
goto v_reusejp_6388_;
}
v_reusejp_6388_:
{
return v___x_6389_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(lean_object* v_year_6393_, uint8_t v_x_6394_){
_start:
{
if (v_x_6394_ == 0)
{
lean_object* v___x_6395_; lean_object* v___x_6396_; lean_object* v___x_6397_; 
v___x_6395_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6396_ = lean_int_add(v_year_6393_, v___x_6395_);
v___x_6397_ = lean_int_neg(v___x_6396_);
lean_dec(v___x_6396_);
return v___x_6397_;
}
else
{
lean_inc(v_year_6393_);
return v_year_6393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra___boxed(lean_object* v_year_6398_, lean_object* v_x_6399_){
_start:
{
uint8_t v_x_42__boxed_6400_; lean_object* v_res_6401_; 
v_x_42__boxed_6400_ = lean_unbox(v_x_6399_);
v_res_6401_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_year_6398_, v_x_42__boxed_6400_);
lean_dec(v_year_6398_);
return v_res_6401_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(uint8_t v_x_6402_){
_start:
{
switch(v_x_6402_)
{
case 1:
{
uint8_t v___x_6403_; 
v___x_6403_ = 1;
return v___x_6403_;
}
case 2:
{
uint8_t v___x_6404_; 
v___x_6404_ = 1;
return v___x_6404_;
}
default: 
{
uint8_t v___x_6405_; 
v___x_6405_ = 0;
return v___x_6405_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod___boxed(lean_object* v_x_6406_){
_start:
{
uint8_t v_x_28__boxed_6407_; uint8_t v_res_6408_; lean_object* v_r_6409_; 
v_x_28__boxed_6407_ = lean_unbox(v_x_6406_);
v_res_6408_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v_x_28__boxed_6407_);
v_r_6409_ = lean_box(v_res_6408_);
return v_r_6409_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(uint8_t v_x_6410_){
_start:
{
switch(v_x_6410_)
{
case 3:
{
uint8_t v___x_6411_; 
v___x_6411_ = 1;
return v___x_6411_;
}
case 4:
{
uint8_t v___x_6412_; 
v___x_6412_ = 1;
return v___x_6412_;
}
case 5:
{
uint8_t v___x_6413_; 
v___x_6413_ = 1;
return v___x_6413_;
}
default: 
{
uint8_t v___x_6414_; 
v___x_6414_ = 0;
return v___x_6414_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod___boxed(lean_object* v_x_6415_){
_start:
{
uint8_t v_x_38__boxed_6416_; uint8_t v_res_6417_; lean_object* v_r_6418_; 
v_x_38__boxed_6416_ = lean_unbox(v_x_6415_);
v_res_6417_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v_x_38__boxed_6416_);
v_r_6418_ = lean_box(v_res_6417_);
return v_r_6418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(lean_object* v_val_6419_, lean_object* v_x_6420_){
_start:
{
lean_inc_ref(v_val_6419_);
return v_val_6419_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed(lean_object* v_val_6421_, lean_object* v_x_6422_){
_start:
{
lean_object* v_res_6423_; 
v_res_6423_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(v_val_6421_, v_x_6422_);
lean_dec_ref(v_val_6421_);
return v_res_6423_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(lean_object* v___y_6424_, lean_object* v_00___6425_){
_start:
{
uint8_t v___x_6426_; lean_object* v___x_6427_; 
v___x_6426_ = 1;
v___x_6427_ = l_Std_Time_TimeZone_Offset_toIsoString(v___y_6424_, v___x_6426_);
return v___x_6427_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1(void){
_start:
{
lean_object* v___x_6430_; lean_object* v___x_6431_; 
v___x_6430_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6431_ = lean_int_neg(v___x_6430_);
return v___x_6431_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2(void){
_start:
{
lean_object* v___x_6432_; lean_object* v___x_6433_; 
v___x_6432_ = lean_unsigned_to_nat(1000000u);
v___x_6433_ = lean_nat_to_int(v___x_6432_);
return v___x_6433_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3(void){
_start:
{
lean_object* v___x_6434_; lean_object* v___x_6435_; lean_object* v___x_6436_; 
v___x_6434_ = lean_unsigned_to_nat(1000000000u);
v___x_6435_ = lean_unsigned_to_nat(0u);
v___x_6436_ = lean_nat_mod(v___x_6435_, v___x_6434_);
return v___x_6436_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4(void){
_start:
{
lean_object* v___x_6437_; lean_object* v___x_6438_; 
v___x_6437_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3);
v___x_6438_ = lean_nat_to_int(v___x_6437_);
return v___x_6438_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5(void){
_start:
{
lean_object* v___x_6439_; uint8_t v___x_6440_; lean_object* v___x_6441_; 
v___x_6439_ = lean_unsigned_to_nat(0u);
v___x_6440_ = 1;
v___x_6441_ = l_Std_Time_Second_instOfNatOrdinal(v___x_6440_, v___x_6439_);
return v___x_6441_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6(void){
_start:
{
lean_object* v___x_6442_; lean_object* v___x_6443_; lean_object* v___x_6444_; 
v___x_6442_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5);
v___x_6443_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6444_ = lean_int_add(v___x_6443_, v___x_6442_);
return v___x_6444_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7(void){
_start:
{
lean_object* v___x_6445_; lean_object* v___x_6446_; lean_object* v___x_6447_; 
v___x_6445_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6446_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6);
v___x_6447_ = lean_int_sub(v___x_6446_, v___x_6445_);
return v___x_6447_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8(void){
_start:
{
lean_object* v___x_6448_; lean_object* v___x_6449_; lean_object* v_range_6450_; 
v___x_6448_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6449_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7);
v_range_6450_ = lean_int_add(v___x_6449_, v___x_6448_);
return v_range_6450_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9(void){
_start:
{
lean_object* v___x_6451_; lean_object* v___x_6452_; 
v___x_6451_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6452_ = lean_int_sub(v___x_6451_, v___x_6451_);
return v___x_6452_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10(void){
_start:
{
lean_object* v_range_6453_; lean_object* v___x_6454_; lean_object* v___x_6455_; 
v_range_6453_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8);
v___x_6454_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9);
v___x_6455_ = lean_int_emod(v___x_6454_, v_range_6453_);
return v___x_6455_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11(void){
_start:
{
lean_object* v_range_6456_; lean_object* v___x_6457_; lean_object* v___x_6458_; 
v_range_6456_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8);
v___x_6457_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10);
v___x_6458_ = lean_int_add(v___x_6457_, v_range_6456_);
return v___x_6458_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12(void){
_start:
{
lean_object* v_range_6459_; lean_object* v___x_6460_; lean_object* v___x_6461_; 
v_range_6459_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8);
v___x_6460_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11);
v___x_6461_ = lean_int_emod(v___x_6460_, v_range_6459_);
return v___x_6461_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13(void){
_start:
{
lean_object* v___x_6462_; lean_object* v___x_6463_; lean_object* v___x_6464_; 
v___x_6462_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6463_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12);
v___x_6464_ = lean_int_add(v___x_6463_, v___x_6462_);
return v___x_6464_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14(void){
_start:
{
lean_object* v___x_6465_; lean_object* v___x_6466_; 
v___x_6465_ = lean_unsigned_to_nat(30u);
v___x_6466_ = lean_nat_to_int(v___x_6465_);
return v___x_6466_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15(void){
_start:
{
lean_object* v___x_6467_; lean_object* v___x_6468_; lean_object* v___x_6469_; 
v___x_6467_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14);
v___x_6468_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6469_ = lean_int_add(v___x_6468_, v___x_6467_);
return v___x_6469_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16(void){
_start:
{
lean_object* v___x_6470_; lean_object* v___x_6471_; lean_object* v___x_6472_; 
v___x_6470_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6471_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v___x_6472_ = lean_int_sub(v___x_6471_, v___x_6470_);
return v___x_6472_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17(void){
_start:
{
lean_object* v___x_6473_; lean_object* v___x_6474_; lean_object* v_range_6475_; 
v___x_6473_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6474_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16);
v_range_6475_ = lean_int_add(v___x_6474_, v___x_6473_);
return v_range_6475_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18(void){
_start:
{
lean_object* v___x_6476_; lean_object* v___x_6477_; lean_object* v___x_6478_; 
v___x_6476_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6477_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6478_ = lean_int_sub(v___x_6477_, v___x_6476_);
return v___x_6478_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19(void){
_start:
{
lean_object* v_range_6479_; lean_object* v___x_6480_; lean_object* v___x_6481_; 
v_range_6479_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17);
v___x_6480_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18);
v___x_6481_ = lean_int_emod(v___x_6480_, v_range_6479_);
return v___x_6481_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20(void){
_start:
{
lean_object* v_range_6482_; lean_object* v___x_6483_; lean_object* v___x_6484_; 
v_range_6482_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17);
v___x_6483_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19);
v___x_6484_ = lean_int_add(v___x_6483_, v_range_6482_);
return v___x_6484_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21(void){
_start:
{
lean_object* v_range_6485_; lean_object* v___x_6486_; lean_object* v___x_6487_; 
v_range_6485_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17);
v___x_6486_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20);
v___x_6487_ = lean_int_emod(v___x_6486_, v_range_6485_);
return v___x_6487_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22(void){
_start:
{
lean_object* v___x_6488_; lean_object* v___x_6489_; lean_object* v___x_6490_; 
v___x_6488_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6489_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21);
v___x_6490_ = lean_int_add(v___x_6489_, v___x_6488_);
return v___x_6490_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23(void){
_start:
{
lean_object* v___x_6491_; lean_object* v___x_6492_; 
v___x_6491_ = lean_unsigned_to_nat(11u);
v___x_6492_ = lean_nat_to_int(v___x_6491_);
return v___x_6492_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24(void){
_start:
{
lean_object* v___x_6493_; lean_object* v___x_6494_; lean_object* v___x_6495_; 
v___x_6493_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23);
v___x_6494_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6495_ = lean_int_add(v___x_6494_, v___x_6493_);
return v___x_6495_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25(void){
_start:
{
lean_object* v___x_6496_; lean_object* v___x_6497_; lean_object* v___x_6498_; 
v___x_6496_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6497_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24);
v___x_6498_ = lean_int_sub(v___x_6497_, v___x_6496_);
return v___x_6498_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26(void){
_start:
{
lean_object* v___x_6499_; lean_object* v___x_6500_; lean_object* v_range_6501_; 
v___x_6499_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6500_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25);
v_range_6501_ = lean_int_add(v___x_6500_, v___x_6499_);
return v_range_6501_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27(void){
_start:
{
lean_object* v_range_6502_; lean_object* v___x_6503_; lean_object* v___x_6504_; 
v_range_6502_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26);
v___x_6503_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18);
v___x_6504_ = lean_int_emod(v___x_6503_, v_range_6502_);
return v___x_6504_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28(void){
_start:
{
lean_object* v_range_6505_; lean_object* v___x_6506_; lean_object* v___x_6507_; 
v_range_6505_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26);
v___x_6506_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27);
v___x_6507_ = lean_int_add(v___x_6506_, v_range_6505_);
return v___x_6507_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29(void){
_start:
{
lean_object* v_range_6508_; lean_object* v___x_6509_; lean_object* v___x_6510_; 
v_range_6508_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26);
v___x_6509_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28);
v___x_6510_ = lean_int_emod(v___x_6509_, v_range_6508_);
return v___x_6510_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__30(void){
_start:
{
lean_object* v___x_6511_; lean_object* v___x_6512_; lean_object* v___x_6513_; 
v___x_6511_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6512_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29);
v___x_6513_ = lean_int_add(v___x_6512_, v___x_6511_);
return v___x_6513_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(lean_object* v_builder_6514_, lean_object* v_aw_6515_){
_start:
{
lean_object* v___y_6517_; lean_object* v___y_6518_; lean_object* v___y_6557_; lean_object* v___y_6558_; lean_object* v___y_6561_; lean_object* v___y_6562_; lean_object* v___y_6563_; lean_object* v___y_6564_; lean_object* v___y_6565_; uint8_t v___y_6566_; lean_object* v___y_6574_; lean_object* v___y_6575_; lean_object* v___y_6576_; lean_object* v___y_6577_; lean_object* v___y_6578_; lean_object* v___y_6579_; uint8_t v___y_6580_; lean_object* v___y_6585_; lean_object* v___y_6586_; lean_object* v___y_6587_; lean_object* v___y_6588_; uint8_t v___y_6589_; lean_object* v___y_6590_; lean_object* v_G_6598_; lean_object* v_y_6599_; lean_object* v_u_6600_; lean_object* v_Y_6601_; lean_object* v_M_6602_; lean_object* v_L_6603_; lean_object* v_d_6604_; lean_object* v_a_6605_; lean_object* v_b_6606_; lean_object* v_B_6607_; lean_object* v_h_6608_; lean_object* v_K_6609_; lean_object* v_k_6610_; lean_object* v_H_6611_; lean_object* v_m_6612_; lean_object* v_s_6613_; lean_object* v_S_6614_; lean_object* v_A_6615_; lean_object* v_n_6616_; lean_object* v_N_6617_; lean_object* v_V_6618_; lean_object* v_z_6619_; lean_object* v_zabbrev_6620_; lean_object* v_v_6621_; lean_object* v_O_6622_; lean_object* v_X_6623_; lean_object* v_x_6624_; lean_object* v_Z_6625_; lean_object* v___y_6627_; lean_object* v___y_6628_; lean_object* v___y_6629_; lean_object* v___y_6630_; lean_object* v___y_6631_; lean_object* v___y_6632_; lean_object* v___y_6633_; uint8_t v___y_6634_; lean_object* v___y_6635_; lean_object* v___y_6644_; lean_object* v___y_6645_; lean_object* v___y_6646_; lean_object* v___y_6647_; lean_object* v___y_6648_; lean_object* v___y_6649_; uint8_t v___y_6650_; lean_object* v___y_6651_; lean_object* v___y_6656_; lean_object* v___y_6657_; lean_object* v___y_6658_; lean_object* v___y_6659_; lean_object* v___y_6660_; uint8_t v___y_6661_; lean_object* v___y_6662_; lean_object* v___y_6666_; lean_object* v___y_6667_; lean_object* v___y_6668_; lean_object* v___y_6669_; uint8_t v___y_6670_; lean_object* v___y_6671_; lean_object* v___y_6675_; lean_object* v___y_6676_; lean_object* v___y_6677_; lean_object* v___y_6678_; uint8_t v___y_6679_; lean_object* v___y_6687_; lean_object* v___y_6688_; lean_object* v___y_6689_; lean_object* v___y_6690_; uint8_t v___y_6691_; uint8_t v_val_6692_; lean_object* v___y_6700_; lean_object* v___y_6701_; lean_object* v___y_6702_; uint8_t v___y_6703_; lean_object* v___y_6704_; lean_object* v___y_6714_; lean_object* v___y_6715_; lean_object* v___y_6716_; uint8_t v___y_6717_; uint8_t v___y_6718_; lean_object* v___y_6725_; lean_object* v___y_6726_; uint8_t v___y_6727_; lean_object* v___y_6728_; lean_object* v___y_6733_; uint8_t v___y_6734_; lean_object* v___y_6735_; lean_object* v___y_6739_; lean_object* v___y_6740_; lean_object* v___y_6741_; lean_object* v___y_6748_; lean_object* v___y_6749_; lean_object* v___y_6750_; lean_object* v___y_6755_; 
v_G_6598_ = lean_ctor_get(v_builder_6514_, 0);
lean_inc(v_G_6598_);
v_y_6599_ = lean_ctor_get(v_builder_6514_, 1);
lean_inc(v_y_6599_);
v_u_6600_ = lean_ctor_get(v_builder_6514_, 2);
lean_inc(v_u_6600_);
v_Y_6601_ = lean_ctor_get(v_builder_6514_, 3);
lean_inc(v_Y_6601_);
v_M_6602_ = lean_ctor_get(v_builder_6514_, 5);
lean_inc(v_M_6602_);
v_L_6603_ = lean_ctor_get(v_builder_6514_, 6);
lean_inc(v_L_6603_);
v_d_6604_ = lean_ctor_get(v_builder_6514_, 7);
lean_inc(v_d_6604_);
v_a_6605_ = lean_ctor_get(v_builder_6514_, 16);
lean_inc(v_a_6605_);
v_b_6606_ = lean_ctor_get(v_builder_6514_, 17);
lean_inc(v_b_6606_);
v_B_6607_ = lean_ctor_get(v_builder_6514_, 18);
lean_inc(v_B_6607_);
v_h_6608_ = lean_ctor_get(v_builder_6514_, 19);
lean_inc(v_h_6608_);
v_K_6609_ = lean_ctor_get(v_builder_6514_, 20);
lean_inc(v_K_6609_);
v_k_6610_ = lean_ctor_get(v_builder_6514_, 21);
lean_inc(v_k_6610_);
v_H_6611_ = lean_ctor_get(v_builder_6514_, 22);
lean_inc(v_H_6611_);
v_m_6612_ = lean_ctor_get(v_builder_6514_, 23);
lean_inc(v_m_6612_);
v_s_6613_ = lean_ctor_get(v_builder_6514_, 24);
lean_inc(v_s_6613_);
v_S_6614_ = lean_ctor_get(v_builder_6514_, 25);
lean_inc(v_S_6614_);
v_A_6615_ = lean_ctor_get(v_builder_6514_, 26);
lean_inc(v_A_6615_);
v_n_6616_ = lean_ctor_get(v_builder_6514_, 27);
lean_inc(v_n_6616_);
v_N_6617_ = lean_ctor_get(v_builder_6514_, 28);
lean_inc(v_N_6617_);
v_V_6618_ = lean_ctor_get(v_builder_6514_, 29);
lean_inc(v_V_6618_);
v_z_6619_ = lean_ctor_get(v_builder_6514_, 30);
lean_inc(v_z_6619_);
v_zabbrev_6620_ = lean_ctor_get(v_builder_6514_, 31);
lean_inc(v_zabbrev_6620_);
v_v_6621_ = lean_ctor_get(v_builder_6514_, 32);
lean_inc(v_v_6621_);
v_O_6622_ = lean_ctor_get(v_builder_6514_, 33);
lean_inc(v_O_6622_);
v_X_6623_ = lean_ctor_get(v_builder_6514_, 34);
lean_inc(v_X_6623_);
v_x_6624_ = lean_ctor_get(v_builder_6514_, 35);
lean_inc(v_x_6624_);
v_Z_6625_ = lean_ctor_get(v_builder_6514_, 36);
lean_inc(v_Z_6625_);
lean_dec_ref(v_builder_6514_);
if (lean_obj_tag(v_O_6622_) == 0)
{
if (lean_obj_tag(v_X_6623_) == 0)
{
if (lean_obj_tag(v_x_6624_) == 0)
{
if (lean_obj_tag(v_Z_6625_) == 0)
{
lean_object* v___x_6762_; 
v___x_6762_ = l_Std_Time_TimeZone_Offset_zero;
v___y_6755_ = v___x_6762_;
goto v___jp_6754_;
}
else
{
lean_object* v_val_6763_; 
v_val_6763_ = lean_ctor_get(v_Z_6625_, 0);
lean_inc(v_val_6763_);
lean_dec_ref_known(v_Z_6625_, 1);
v___y_6755_ = v_val_6763_;
goto v___jp_6754_;
}
}
else
{
lean_object* v_val_6764_; 
lean_dec(v_Z_6625_);
v_val_6764_ = lean_ctor_get(v_x_6624_, 0);
lean_inc(v_val_6764_);
lean_dec_ref_known(v_x_6624_, 1);
v___y_6755_ = v_val_6764_;
goto v___jp_6754_;
}
}
else
{
lean_object* v_val_6765_; 
lean_dec(v_Z_6625_);
lean_dec(v_x_6624_);
v_val_6765_ = lean_ctor_get(v_X_6623_, 0);
lean_inc(v_val_6765_);
lean_dec_ref_known(v_X_6623_, 1);
v___y_6755_ = v_val_6765_;
goto v___jp_6754_;
}
}
else
{
lean_object* v_val_6766_; 
lean_dec(v_Z_6625_);
lean_dec(v_x_6624_);
lean_dec(v_X_6623_);
v_val_6766_ = lean_ctor_get(v_O_6622_, 0);
lean_inc(v_val_6766_);
lean_dec_ref_known(v_O_6622_, 1);
v___y_6755_ = v_val_6766_;
goto v___jp_6754_;
}
v___jp_6516_:
{
if (lean_obj_tag(v___y_6517_) == 0)
{
lean_object* v___x_6519_; 
lean_dec_ref(v___y_6518_);
v___x_6519_ = lean_box(0);
return v___x_6519_;
}
else
{
lean_object* v_val_6520_; lean_object* v___x_6522_; uint8_t v_isShared_6523_; uint8_t v_isSharedCheck_6555_; 
v_val_6520_ = lean_ctor_get(v___y_6517_, 0);
v_isSharedCheck_6555_ = !lean_is_exclusive(v___y_6517_);
if (v_isSharedCheck_6555_ == 0)
{
v___x_6522_ = v___y_6517_;
v_isShared_6523_ = v_isSharedCheck_6555_;
goto v_resetjp_6521_;
}
else
{
lean_inc(v_val_6520_);
lean_dec(v___y_6517_);
v___x_6522_ = lean_box(0);
v_isShared_6523_ = v_isSharedCheck_6555_;
goto v_resetjp_6521_;
}
v_resetjp_6521_:
{
lean_object* v_offset_6524_; lean_object* v_name_6525_; lean_object* v_abbreviation_6526_; uint8_t v_isDST_6527_; uint8_t v___x_6528_; uint8_t v___x_6529_; lean_object* v_ltt_6530_; lean_object* v___x_6531_; lean_object* v___x_6532_; lean_object* v___x_6533_; lean_object* v_wt_6534_; lean_object* v_ltt_6535_; lean_object* v_tz_6536_; lean_object* v_offset_6537_; lean_object* v_second_6538_; lean_object* v_nano_6539_; lean_object* v___f_6540_; lean_object* v___x_6541_; lean_object* v___x_6542_; lean_object* v___x_6543_; lean_object* v___x_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; lean_object* v___x_6549_; lean_object* v___x_6550_; lean_object* v___x_6551_; lean_object* v___x_6553_; 
v_offset_6524_ = lean_ctor_get(v___y_6518_, 0);
lean_inc(v_offset_6524_);
v_name_6525_ = lean_ctor_get(v___y_6518_, 1);
lean_inc_ref(v_name_6525_);
v_abbreviation_6526_ = lean_ctor_get(v___y_6518_, 2);
lean_inc_ref(v_abbreviation_6526_);
v_isDST_6527_ = lean_ctor_get_uint8(v___y_6518_, sizeof(void*)*3);
lean_dec_ref(v___y_6518_);
v___x_6528_ = 0;
v___x_6529_ = 1;
v_ltt_6530_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6530_, 0, v_offset_6524_);
lean_ctor_set(v_ltt_6530_, 1, v_abbreviation_6526_);
lean_ctor_set(v_ltt_6530_, 2, v_name_6525_);
lean_ctor_set_uint8(v_ltt_6530_, sizeof(void*)*3, v_isDST_6527_);
lean_ctor_set_uint8(v_ltt_6530_, sizeof(void*)*3 + 1, v___x_6528_);
lean_ctor_set_uint8(v_ltt_6530_, sizeof(void*)*3 + 2, v___x_6529_);
v___x_6531_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6532_ = lean_box(0);
v___x_6533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6533_, 0, v_ltt_6530_);
lean_ctor_set(v___x_6533_, 1, v___x_6531_);
lean_ctor_set(v___x_6533_, 2, v___x_6532_);
lean_inc(v_val_6520_);
v_wt_6534_ = l_Std_Time_PlainDateTime_toWallTime(v_val_6520_);
lean_inc_ref(v___x_6533_);
v_ltt_6535_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_6533_, v_wt_6534_);
v_tz_6536_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_6535_);
lean_dec_ref(v_ltt_6535_);
v_offset_6537_ = lean_ctor_get(v_tz_6536_, 0);
lean_inc(v_offset_6537_);
v_second_6538_ = lean_ctor_get(v_wt_6534_, 0);
lean_inc(v_second_6538_);
v_nano_6539_ = lean_ctor_get(v_wt_6534_, 1);
lean_inc(v_nano_6539_);
lean_dec_ref(v_wt_6534_);
v___f_6540_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed), 2, 1);
lean_closure_set(v___f_6540_, 0, v_val_6520_);
v___x_6541_ = lean_mk_thunk(v___f_6540_);
v___x_6542_ = lean_int_neg(v_offset_6537_);
lean_dec(v_offset_6537_);
v___x_6543_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1);
v___x_6544_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_6545_ = lean_int_mul(v_second_6538_, v___x_6544_);
lean_dec(v_second_6538_);
v___x_6546_ = lean_int_add(v___x_6545_, v_nano_6539_);
lean_dec(v_nano_6539_);
lean_dec(v___x_6545_);
v___x_6547_ = lean_int_mul(v___x_6542_, v___x_6544_);
lean_dec(v___x_6542_);
v___x_6548_ = lean_int_add(v___x_6547_, v___x_6543_);
lean_dec(v___x_6547_);
v___x_6549_ = lean_int_add(v___x_6546_, v___x_6548_);
lean_dec(v___x_6548_);
lean_dec(v___x_6546_);
v___x_6550_ = l_Std_Time_Duration_ofNanoseconds(v___x_6549_);
lean_dec(v___x_6549_);
v___x_6551_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6551_, 0, v___x_6541_);
lean_ctor_set(v___x_6551_, 1, v___x_6550_);
lean_ctor_set(v___x_6551_, 2, v___x_6533_);
lean_ctor_set(v___x_6551_, 3, v_tz_6536_);
if (v_isShared_6523_ == 0)
{
lean_ctor_set(v___x_6522_, 0, v___x_6551_);
v___x_6553_ = v___x_6522_;
goto v_reusejp_6552_;
}
else
{
lean_object* v_reuseFailAlloc_6554_; 
v_reuseFailAlloc_6554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6554_, 0, v___x_6551_);
v___x_6553_ = v_reuseFailAlloc_6554_;
goto v_reusejp_6552_;
}
v_reusejp_6552_:
{
return v___x_6553_;
}
}
}
}
v___jp_6556_:
{
if (lean_obj_tag(v_aw_6515_) == 0)
{
lean_object* v_a_6559_; 
lean_dec_ref(v___y_6557_);
v_a_6559_ = lean_ctor_get(v_aw_6515_, 0);
lean_inc_ref(v_a_6559_);
lean_dec_ref_known(v_aw_6515_, 1);
v___y_6517_ = v___y_6558_;
v___y_6518_ = v_a_6559_;
goto v___jp_6516_;
}
else
{
v___y_6517_ = v___y_6558_;
v___y_6518_ = v___y_6557_;
goto v___jp_6516_;
}
}
v___jp_6560_:
{
lean_object* v___x_6567_; uint8_t v___x_6568_; 
v___x_6567_ = l_Std_Time_Month_Ordinal_days(v___y_6566_, v___y_6565_);
v___x_6568_ = lean_int_dec_le(v___y_6563_, v___x_6567_);
lean_dec(v___x_6567_);
if (v___x_6568_ == 0)
{
lean_object* v___x_6569_; 
lean_dec(v___y_6565_);
lean_dec(v___y_6563_);
lean_dec(v___y_6562_);
lean_dec_ref(v___y_6561_);
v___x_6569_ = lean_box(0);
v___y_6557_ = v___y_6564_;
v___y_6558_ = v___x_6569_;
goto v___jp_6556_;
}
else
{
lean_object* v_date_6570_; lean_object* v___x_6571_; lean_object* v___x_6572_; 
v_date_6570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_date_6570_, 0, v___y_6562_);
lean_ctor_set(v_date_6570_, 1, v___y_6565_);
lean_ctor_set(v_date_6570_, 2, v___y_6563_);
v___x_6571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6571_, 0, v_date_6570_);
lean_ctor_set(v___x_6571_, 1, v___y_6561_);
v___x_6572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6572_, 0, v___x_6571_);
v___y_6557_ = v___y_6564_;
v___y_6558_ = v___x_6572_;
goto v___jp_6556_;
}
}
v___jp_6573_:
{
lean_object* v___x_6581_; lean_object* v___x_6582_; uint8_t v___x_6583_; 
v___x_6581_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_6582_ = lean_int_mod(v___y_6576_, v___x_6581_);
v___x_6583_ = lean_int_dec_eq(v___x_6582_, v___y_6574_);
lean_dec(v___x_6582_);
if (v___x_6583_ == 0)
{
v___y_6561_ = v___y_6575_;
v___y_6562_ = v___y_6576_;
v___y_6563_ = v___y_6577_;
v___y_6564_ = v___y_6578_;
v___y_6565_ = v___y_6579_;
v___y_6566_ = v___y_6580_;
goto v___jp_6560_;
}
else
{
v___y_6561_ = v___y_6575_;
v___y_6562_ = v___y_6576_;
v___y_6563_ = v___y_6577_;
v___y_6564_ = v___y_6578_;
v___y_6565_ = v___y_6579_;
v___y_6566_ = v___x_6583_;
goto v___jp_6560_;
}
}
v___jp_6584_:
{
lean_object* v___x_6591_; lean_object* v___x_6592_; lean_object* v___x_6593_; uint8_t v___x_6594_; 
v___x_6591_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_6592_ = lean_int_mod(v___y_6585_, v___x_6591_);
v___x_6593_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6594_ = lean_int_dec_eq(v___x_6592_, v___x_6593_);
lean_dec(v___x_6592_);
if (v___x_6594_ == 0)
{
v___y_6561_ = v___y_6590_;
v___y_6562_ = v___y_6585_;
v___y_6563_ = v___y_6586_;
v___y_6564_ = v___y_6587_;
v___y_6565_ = v___y_6588_;
v___y_6566_ = v___y_6589_;
goto v___jp_6560_;
}
else
{
lean_object* v___x_6595_; lean_object* v___x_6596_; uint8_t v___x_6597_; 
v___x_6595_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_6596_ = lean_int_mod(v___y_6585_, v___x_6595_);
v___x_6597_ = lean_int_dec_eq(v___x_6596_, v___x_6593_);
lean_dec(v___x_6596_);
if (v___x_6597_ == 0)
{
if (v___x_6594_ == 0)
{
v___y_6574_ = v___x_6593_;
v___y_6575_ = v___y_6590_;
v___y_6576_ = v___y_6585_;
v___y_6577_ = v___y_6586_;
v___y_6578_ = v___y_6587_;
v___y_6579_ = v___y_6588_;
v___y_6580_ = v___y_6589_;
goto v___jp_6573_;
}
else
{
v___y_6561_ = v___y_6590_;
v___y_6562_ = v___y_6585_;
v___y_6563_ = v___y_6586_;
v___y_6564_ = v___y_6587_;
v___y_6565_ = v___y_6588_;
v___y_6566_ = v___x_6594_;
goto v___jp_6560_;
}
}
else
{
v___y_6574_ = v___x_6593_;
v___y_6575_ = v___y_6590_;
v___y_6576_ = v___y_6585_;
v___y_6577_ = v___y_6586_;
v___y_6578_ = v___y_6587_;
v___y_6579_ = v___y_6588_;
v___y_6580_ = v___y_6589_;
goto v___jp_6573_;
}
}
}
v___jp_6626_:
{
if (lean_obj_tag(v_N_6617_) == 0)
{
if (lean_obj_tag(v_A_6615_) == 0)
{
lean_object* v___x_6636_; 
v___x_6636_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6636_, 0, v___y_6632_);
lean_ctor_set(v___x_6636_, 1, v___y_6631_);
lean_ctor_set(v___x_6636_, 2, v___y_6627_);
lean_ctor_set(v___x_6636_, 3, v___y_6635_);
v___y_6585_ = v___y_6628_;
v___y_6586_ = v___y_6629_;
v___y_6587_ = v___y_6630_;
v___y_6588_ = v___y_6633_;
v___y_6589_ = v___y_6634_;
v___y_6590_ = v___x_6636_;
goto v___jp_6584_;
}
else
{
lean_object* v_val_6637_; lean_object* v___x_6638_; lean_object* v___x_6639_; lean_object* v___x_6640_; 
lean_dec(v___y_6635_);
lean_dec(v___y_6632_);
lean_dec(v___y_6631_);
lean_dec(v___y_6627_);
v_val_6637_ = lean_ctor_get(v_A_6615_, 0);
lean_inc(v_val_6637_);
lean_dec_ref_known(v_A_6615_, 1);
v___x_6638_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2);
v___x_6639_ = lean_int_mul(v_val_6637_, v___x_6638_);
lean_dec(v_val_6637_);
v___x_6640_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_6639_);
lean_dec(v___x_6639_);
v___y_6585_ = v___y_6628_;
v___y_6586_ = v___y_6629_;
v___y_6587_ = v___y_6630_;
v___y_6588_ = v___y_6633_;
v___y_6589_ = v___y_6634_;
v___y_6590_ = v___x_6640_;
goto v___jp_6584_;
}
}
else
{
lean_object* v_val_6641_; lean_object* v___x_6642_; 
lean_dec(v___y_6635_);
lean_dec(v___y_6632_);
lean_dec(v___y_6631_);
lean_dec(v___y_6627_);
lean_dec(v_A_6615_);
v_val_6641_ = lean_ctor_get(v_N_6617_, 0);
lean_inc(v_val_6641_);
lean_dec_ref_known(v_N_6617_, 1);
v___x_6642_ = l_Std_Time_PlainTime_ofNanoseconds(v_val_6641_);
lean_dec(v_val_6641_);
v___y_6585_ = v___y_6628_;
v___y_6586_ = v___y_6629_;
v___y_6587_ = v___y_6630_;
v___y_6588_ = v___y_6633_;
v___y_6589_ = v___y_6634_;
v___y_6590_ = v___x_6642_;
goto v___jp_6584_;
}
}
v___jp_6643_:
{
if (lean_obj_tag(v_n_6616_) == 0)
{
if (lean_obj_tag(v_S_6614_) == 0)
{
lean_object* v___x_6652_; 
v___x_6652_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4);
v___y_6627_ = v___y_6651_;
v___y_6628_ = v___y_6644_;
v___y_6629_ = v___y_6645_;
v___y_6630_ = v___y_6648_;
v___y_6631_ = v___y_6647_;
v___y_6632_ = v___y_6646_;
v___y_6633_ = v___y_6649_;
v___y_6634_ = v___y_6650_;
v___y_6635_ = v___x_6652_;
goto v___jp_6626_;
}
else
{
lean_object* v_val_6653_; 
v_val_6653_ = lean_ctor_get(v_S_6614_, 0);
lean_inc(v_val_6653_);
lean_dec_ref_known(v_S_6614_, 1);
v___y_6627_ = v___y_6651_;
v___y_6628_ = v___y_6644_;
v___y_6629_ = v___y_6645_;
v___y_6630_ = v___y_6648_;
v___y_6631_ = v___y_6647_;
v___y_6632_ = v___y_6646_;
v___y_6633_ = v___y_6649_;
v___y_6634_ = v___y_6650_;
v___y_6635_ = v_val_6653_;
goto v___jp_6626_;
}
}
else
{
lean_object* v_val_6654_; 
lean_dec(v_S_6614_);
v_val_6654_ = lean_ctor_get(v_n_6616_, 0);
lean_inc(v_val_6654_);
lean_dec_ref_known(v_n_6616_, 1);
v___y_6627_ = v___y_6651_;
v___y_6628_ = v___y_6644_;
v___y_6629_ = v___y_6645_;
v___y_6630_ = v___y_6648_;
v___y_6631_ = v___y_6647_;
v___y_6632_ = v___y_6646_;
v___y_6633_ = v___y_6649_;
v___y_6634_ = v___y_6650_;
v___y_6635_ = v_val_6654_;
goto v___jp_6626_;
}
}
v___jp_6655_:
{
if (lean_obj_tag(v_s_6613_) == 0)
{
lean_object* v___x_6663_; 
v___x_6663_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5);
v___y_6644_ = v___y_6656_;
v___y_6645_ = v___y_6657_;
v___y_6646_ = v___y_6659_;
v___y_6647_ = v___y_6662_;
v___y_6648_ = v___y_6658_;
v___y_6649_ = v___y_6660_;
v___y_6650_ = v___y_6661_;
v___y_6651_ = v___x_6663_;
goto v___jp_6643_;
}
else
{
lean_object* v_val_6664_; 
v_val_6664_ = lean_ctor_get(v_s_6613_, 0);
lean_inc(v_val_6664_);
lean_dec_ref_known(v_s_6613_, 1);
v___y_6644_ = v___y_6656_;
v___y_6645_ = v___y_6657_;
v___y_6646_ = v___y_6659_;
v___y_6647_ = v___y_6662_;
v___y_6648_ = v___y_6658_;
v___y_6649_ = v___y_6660_;
v___y_6650_ = v___y_6661_;
v___y_6651_ = v_val_6664_;
goto v___jp_6643_;
}
}
v___jp_6665_:
{
if (lean_obj_tag(v_m_6612_) == 0)
{
lean_object* v___x_6672_; 
v___x_6672_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13);
v___y_6656_ = v___y_6666_;
v___y_6657_ = v___y_6667_;
v___y_6658_ = v___y_6668_;
v___y_6659_ = v___y_6671_;
v___y_6660_ = v___y_6669_;
v___y_6661_ = v___y_6670_;
v___y_6662_ = v___x_6672_;
goto v___jp_6655_;
}
else
{
lean_object* v_val_6673_; 
v_val_6673_ = lean_ctor_get(v_m_6612_, 0);
lean_inc(v_val_6673_);
lean_dec_ref_known(v_m_6612_, 1);
v___y_6656_ = v___y_6666_;
v___y_6657_ = v___y_6667_;
v___y_6658_ = v___y_6668_;
v___y_6659_ = v___y_6671_;
v___y_6660_ = v___y_6669_;
v___y_6661_ = v___y_6670_;
v___y_6662_ = v_val_6673_;
goto v___jp_6655_;
}
}
v___jp_6674_:
{
if (lean_obj_tag(v_k_6610_) == 0)
{
if (lean_obj_tag(v_H_6611_) == 0)
{
lean_object* v___x_6680_; 
v___x_6680_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6666_ = v___y_6675_;
v___y_6667_ = v___y_6676_;
v___y_6668_ = v___y_6677_;
v___y_6669_ = v___y_6678_;
v___y_6670_ = v___y_6679_;
v___y_6671_ = v___x_6680_;
goto v___jp_6665_;
}
else
{
lean_object* v_val_6681_; 
v_val_6681_ = lean_ctor_get(v_H_6611_, 0);
lean_inc(v_val_6681_);
lean_dec_ref_known(v_H_6611_, 1);
v___y_6666_ = v___y_6675_;
v___y_6667_ = v___y_6676_;
v___y_6668_ = v___y_6677_;
v___y_6669_ = v___y_6678_;
v___y_6670_ = v___y_6679_;
v___y_6671_ = v_val_6681_;
goto v___jp_6665_;
}
}
else
{
if (lean_obj_tag(v_H_6611_) == 0)
{
lean_object* v_val_6682_; lean_object* v___x_6683_; lean_object* v___x_6684_; 
v_val_6682_ = lean_ctor_get(v_k_6610_, 0);
lean_inc(v_val_6682_);
lean_dec_ref_known(v_k_6610_, 1);
v___x_6683_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_6684_ = lean_int_add(v_val_6682_, v___x_6683_);
lean_dec(v_val_6682_);
v___y_6666_ = v___y_6675_;
v___y_6667_ = v___y_6676_;
v___y_6668_ = v___y_6677_;
v___y_6669_ = v___y_6678_;
v___y_6670_ = v___y_6679_;
v___y_6671_ = v___x_6684_;
goto v___jp_6665_;
}
else
{
lean_object* v_val_6685_; 
lean_dec_ref_known(v_k_6610_, 1);
v_val_6685_ = lean_ctor_get(v_H_6611_, 0);
lean_inc(v_val_6685_);
lean_dec_ref_known(v_H_6611_, 1);
v___y_6666_ = v___y_6675_;
v___y_6667_ = v___y_6676_;
v___y_6668_ = v___y_6677_;
v___y_6669_ = v___y_6678_;
v___y_6670_ = v___y_6679_;
v___y_6671_ = v_val_6685_;
goto v___jp_6665_;
}
}
}
v___jp_6686_:
{
if (lean_obj_tag(v_h_6608_) == 0)
{
if (lean_obj_tag(v_K_6609_) == 0)
{
v___y_6675_ = v___y_6687_;
v___y_6676_ = v___y_6688_;
v___y_6677_ = v___y_6689_;
v___y_6678_ = v___y_6690_;
v___y_6679_ = v___y_6691_;
goto v___jp_6674_;
}
else
{
lean_object* v_val_6693_; lean_object* v___x_6694_; lean_object* v___x_6695_; lean_object* v___x_6696_; 
lean_dec(v_H_6611_);
lean_dec(v_k_6610_);
v_val_6693_ = lean_ctor_get(v_K_6609_, 0);
lean_inc(v_val_6693_);
lean_dec_ref_known(v_K_6609_, 1);
v___x_6694_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6695_ = lean_int_add(v_val_6693_, v___x_6694_);
lean_dec(v_val_6693_);
v___x_6696_ = l_Std_Time_HourMarker_toAbsolute(v_val_6692_, v___x_6695_);
lean_dec(v___x_6695_);
v___y_6666_ = v___y_6687_;
v___y_6667_ = v___y_6688_;
v___y_6668_ = v___y_6689_;
v___y_6669_ = v___y_6690_;
v___y_6670_ = v___y_6691_;
v___y_6671_ = v___x_6696_;
goto v___jp_6665_;
}
}
else
{
lean_object* v_val_6697_; lean_object* v___x_6698_; 
lean_dec(v_H_6611_);
lean_dec(v_k_6610_);
lean_dec(v_K_6609_);
v_val_6697_ = lean_ctor_get(v_h_6608_, 0);
lean_inc(v_val_6697_);
lean_dec_ref_known(v_h_6608_, 1);
v___x_6698_ = l_Std_Time_HourMarker_toAbsolute(v_val_6692_, v_val_6697_);
lean_dec(v_val_6697_);
v___y_6666_ = v___y_6687_;
v___y_6667_ = v___y_6688_;
v___y_6668_ = v___y_6689_;
v___y_6669_ = v___y_6690_;
v___y_6670_ = v___y_6691_;
v___y_6671_ = v___x_6698_;
goto v___jp_6665_;
}
}
v___jp_6699_:
{
if (lean_obj_tag(v_a_6605_) == 0)
{
if (lean_obj_tag(v_b_6606_) == 0)
{
if (lean_obj_tag(v_B_6607_) == 0)
{
lean_dec(v_K_6609_);
lean_dec(v_h_6608_);
v___y_6675_ = v___y_6704_;
v___y_6676_ = v___y_6700_;
v___y_6677_ = v___y_6701_;
v___y_6678_ = v___y_6702_;
v___y_6679_ = v___y_6703_;
goto v___jp_6674_;
}
else
{
lean_object* v_val_6705_; uint8_t v___x_6706_; uint8_t v___x_6707_; 
v_val_6705_ = lean_ctor_get(v_B_6607_, 0);
lean_inc(v_val_6705_);
lean_dec_ref_known(v_B_6607_, 1);
v___x_6706_ = lean_unbox(v_val_6705_);
lean_dec(v_val_6705_);
v___x_6707_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v___x_6706_);
v___y_6687_ = v___y_6704_;
v___y_6688_ = v___y_6700_;
v___y_6689_ = v___y_6701_;
v___y_6690_ = v___y_6702_;
v___y_6691_ = v___y_6703_;
v_val_6692_ = v___x_6707_;
goto v___jp_6686_;
}
}
else
{
lean_object* v_val_6708_; uint8_t v___x_6709_; uint8_t v___x_6710_; 
lean_dec(v_B_6607_);
v_val_6708_ = lean_ctor_get(v_b_6606_, 0);
lean_inc(v_val_6708_);
lean_dec_ref_known(v_b_6606_, 1);
v___x_6709_ = lean_unbox(v_val_6708_);
lean_dec(v_val_6708_);
v___x_6710_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v___x_6709_);
v___y_6687_ = v___y_6704_;
v___y_6688_ = v___y_6700_;
v___y_6689_ = v___y_6701_;
v___y_6690_ = v___y_6702_;
v___y_6691_ = v___y_6703_;
v_val_6692_ = v___x_6710_;
goto v___jp_6686_;
}
}
else
{
lean_object* v_val_6711_; uint8_t v___x_6712_; 
lean_dec(v_B_6607_);
lean_dec(v_b_6606_);
v_val_6711_ = lean_ctor_get(v_a_6605_, 0);
lean_inc(v_val_6711_);
lean_dec_ref_known(v_a_6605_, 1);
v___x_6712_ = lean_unbox(v_val_6711_);
lean_dec(v_val_6711_);
v___y_6687_ = v___y_6704_;
v___y_6688_ = v___y_6700_;
v___y_6689_ = v___y_6701_;
v___y_6690_ = v___y_6702_;
v___y_6691_ = v___y_6703_;
v_val_6692_ = v___x_6712_;
goto v___jp_6686_;
}
}
v___jp_6713_:
{
if (lean_obj_tag(v_u_6600_) == 0)
{
if (lean_obj_tag(v_y_6599_) == 0)
{
if (lean_obj_tag(v_Y_6601_) == 0)
{
lean_object* v___x_6719_; 
v___x_6719_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6700_ = v___y_6714_;
v___y_6701_ = v___y_6715_;
v___y_6702_ = v___y_6716_;
v___y_6703_ = v___y_6717_;
v___y_6704_ = v___x_6719_;
goto v___jp_6699_;
}
else
{
lean_object* v_val_6720_; 
v_val_6720_ = lean_ctor_get(v_Y_6601_, 0);
lean_inc(v_val_6720_);
lean_dec_ref_known(v_Y_6601_, 1);
v___y_6700_ = v___y_6714_;
v___y_6701_ = v___y_6715_;
v___y_6702_ = v___y_6716_;
v___y_6703_ = v___y_6717_;
v___y_6704_ = v_val_6720_;
goto v___jp_6699_;
}
}
else
{
lean_object* v_val_6721_; lean_object* v___x_6722_; 
lean_dec(v_Y_6601_);
v_val_6721_ = lean_ctor_get(v_y_6599_, 0);
lean_inc(v_val_6721_);
lean_dec_ref_known(v_y_6599_, 1);
v___x_6722_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_val_6721_, v___y_6718_);
lean_dec(v_val_6721_);
v___y_6700_ = v___y_6714_;
v___y_6701_ = v___y_6715_;
v___y_6702_ = v___y_6716_;
v___y_6703_ = v___y_6717_;
v___y_6704_ = v___x_6722_;
goto v___jp_6699_;
}
}
else
{
lean_object* v_val_6723_; 
lean_dec(v_Y_6601_);
lean_dec(v_y_6599_);
v_val_6723_ = lean_ctor_get(v_u_6600_, 0);
lean_inc(v_val_6723_);
lean_dec_ref_known(v_u_6600_, 1);
v___y_6700_ = v___y_6714_;
v___y_6701_ = v___y_6715_;
v___y_6702_ = v___y_6716_;
v___y_6703_ = v___y_6717_;
v___y_6704_ = v_val_6723_;
goto v___jp_6699_;
}
}
v___jp_6724_:
{
if (lean_obj_tag(v_G_6598_) == 0)
{
uint8_t v___x_6729_; 
v___x_6729_ = 1;
v___y_6714_ = v___y_6728_;
v___y_6715_ = v___y_6725_;
v___y_6716_ = v___y_6726_;
v___y_6717_ = v___y_6727_;
v___y_6718_ = v___x_6729_;
goto v___jp_6713_;
}
else
{
lean_object* v_val_6730_; uint8_t v___x_6731_; 
v_val_6730_ = lean_ctor_get(v_G_6598_, 0);
lean_inc(v_val_6730_);
lean_dec_ref_known(v_G_6598_, 1);
v___x_6731_ = lean_unbox(v_val_6730_);
lean_dec(v_val_6730_);
v___y_6714_ = v___y_6728_;
v___y_6715_ = v___y_6725_;
v___y_6716_ = v___y_6726_;
v___y_6717_ = v___y_6727_;
v___y_6718_ = v___x_6731_;
goto v___jp_6713_;
}
}
v___jp_6732_:
{
if (lean_obj_tag(v_d_6604_) == 0)
{
lean_object* v___x_6736_; 
v___x_6736_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22);
v___y_6725_ = v___y_6733_;
v___y_6726_ = v___y_6735_;
v___y_6727_ = v___y_6734_;
v___y_6728_ = v___x_6736_;
goto v___jp_6724_;
}
else
{
lean_object* v_val_6737_; 
v_val_6737_ = lean_ctor_get(v_d_6604_, 0);
lean_inc(v_val_6737_);
lean_dec_ref_known(v_d_6604_, 1);
v___y_6725_ = v___y_6733_;
v___y_6726_ = v___y_6735_;
v___y_6727_ = v___y_6734_;
v___y_6728_ = v_val_6737_;
goto v___jp_6724_;
}
}
v___jp_6738_:
{
uint8_t v___x_6742_; lean_object* v_tz_6743_; 
v___x_6742_ = 0;
v_tz_6743_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_tz_6743_, 0, v___y_6739_);
lean_ctor_set(v_tz_6743_, 1, v___y_6740_);
lean_ctor_set(v_tz_6743_, 2, v___y_6741_);
lean_ctor_set_uint8(v_tz_6743_, sizeof(void*)*3, v___x_6742_);
if (lean_obj_tag(v_M_6602_) == 0)
{
if (lean_obj_tag(v_L_6603_) == 0)
{
lean_object* v___x_6744_; 
v___x_6744_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__30, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__30_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__30);
v___y_6733_ = v_tz_6743_;
v___y_6734_ = v___x_6742_;
v___y_6735_ = v___x_6744_;
goto v___jp_6732_;
}
else
{
lean_object* v_val_6745_; 
v_val_6745_ = lean_ctor_get(v_L_6603_, 0);
lean_inc(v_val_6745_);
lean_dec_ref_known(v_L_6603_, 1);
v___y_6733_ = v_tz_6743_;
v___y_6734_ = v___x_6742_;
v___y_6735_ = v_val_6745_;
goto v___jp_6732_;
}
}
else
{
lean_object* v_val_6746_; 
lean_dec(v_L_6603_);
v_val_6746_ = lean_ctor_get(v_M_6602_, 0);
lean_inc(v_val_6746_);
lean_dec_ref_known(v_M_6602_, 1);
v___y_6733_ = v_tz_6743_;
v___y_6734_ = v___x_6742_;
v___y_6735_ = v_val_6746_;
goto v___jp_6732_;
}
}
v___jp_6747_:
{
if (lean_obj_tag(v_zabbrev_6620_) == 0)
{
lean_object* v___x_6751_; lean_object* v___x_6752_; 
v___x_6751_ = lean_box(0);
v___x_6752_ = lean_apply_1(v___y_6748_, v___x_6751_);
v___y_6739_ = v___y_6749_;
v___y_6740_ = v___y_6750_;
v___y_6741_ = v___x_6752_;
goto v___jp_6738_;
}
else
{
lean_object* v_val_6753_; 
lean_dec_ref(v___y_6748_);
v_val_6753_ = lean_ctor_get(v_zabbrev_6620_, 0);
lean_inc(v_val_6753_);
lean_dec_ref_known(v_zabbrev_6620_, 1);
v___y_6739_ = v___y_6749_;
v___y_6740_ = v___y_6750_;
v___y_6741_ = v_val_6753_;
goto v___jp_6738_;
}
}
v___jp_6754_:
{
lean_object* v___f_6756_; 
lean_inc(v___y_6755_);
v___f_6756_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1), 2, 1);
lean_closure_set(v___f_6756_, 0, v___y_6755_);
if (lean_obj_tag(v_V_6618_) == 0)
{
if (lean_obj_tag(v_v_6621_) == 0)
{
if (lean_obj_tag(v_z_6619_) == 0)
{
lean_object* v___x_6757_; lean_object* v___x_6758_; 
v___x_6757_ = lean_box(0);
lean_inc(v___y_6755_);
v___x_6758_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(v___y_6755_, v___x_6757_);
v___y_6748_ = v___f_6756_;
v___y_6749_ = v___y_6755_;
v___y_6750_ = v___x_6758_;
goto v___jp_6747_;
}
else
{
lean_object* v_val_6759_; 
v_val_6759_ = lean_ctor_get(v_z_6619_, 0);
lean_inc(v_val_6759_);
lean_dec_ref_known(v_z_6619_, 1);
v___y_6748_ = v___f_6756_;
v___y_6749_ = v___y_6755_;
v___y_6750_ = v_val_6759_;
goto v___jp_6747_;
}
}
else
{
lean_object* v_val_6760_; 
lean_dec(v_z_6619_);
v_val_6760_ = lean_ctor_get(v_v_6621_, 0);
lean_inc(v_val_6760_);
lean_dec_ref_known(v_v_6621_, 1);
v___y_6748_ = v___f_6756_;
v___y_6749_ = v___y_6755_;
v___y_6750_ = v_val_6760_;
goto v___jp_6747_;
}
}
else
{
lean_object* v_val_6761_; 
lean_dec(v_v_6621_);
lean_dec(v_z_6619_);
v_val_6761_ = lean_ctor_get(v_V_6618_, 0);
lean_inc(v_val_6761_);
lean_dec_ref_known(v_V_6618_, 1);
v___y_6748_ = v___f_6756_;
v___y_6749_ = v___y_6755_;
v___y_6750_ = v_val_6761_;
goto v___jp_6747_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(lean_object* v_date_6767_, lean_object* v_config_6768_, lean_object* v_mod_6769_, lean_object* v_a_6770_){
_start:
{
if (lean_obj_tag(v_mod_6769_) == 0)
{
lean_object* v_val_6771_; lean_object* v___x_6772_; 
lean_dec_ref(v_config_6768_);
v_val_6771_ = lean_ctor_get(v_mod_6769_, 0);
lean_inc_ref(v_val_6771_);
lean_dec_ref_known(v_mod_6769_, 1);
v___x_6772_ = l_Std_Internal_Parsec_String_pstring(v_val_6771_, v_a_6770_);
if (lean_obj_tag(v___x_6772_) == 0)
{
lean_object* v_pos_6773_; lean_object* v___x_6775_; uint8_t v_isShared_6776_; uint8_t v_isSharedCheck_6780_; 
v_pos_6773_ = lean_ctor_get(v___x_6772_, 0);
v_isSharedCheck_6780_ = !lean_is_exclusive(v___x_6772_);
if (v_isSharedCheck_6780_ == 0)
{
lean_object* v_unused_6781_; 
v_unused_6781_ = lean_ctor_get(v___x_6772_, 1);
lean_dec(v_unused_6781_);
v___x_6775_ = v___x_6772_;
v_isShared_6776_ = v_isSharedCheck_6780_;
goto v_resetjp_6774_;
}
else
{
lean_inc(v_pos_6773_);
lean_dec(v___x_6772_);
v___x_6775_ = lean_box(0);
v_isShared_6776_ = v_isSharedCheck_6780_;
goto v_resetjp_6774_;
}
v_resetjp_6774_:
{
lean_object* v___x_6778_; 
if (v_isShared_6776_ == 0)
{
lean_ctor_set(v___x_6775_, 1, v_date_6767_);
v___x_6778_ = v___x_6775_;
goto v_reusejp_6777_;
}
else
{
lean_object* v_reuseFailAlloc_6779_; 
v_reuseFailAlloc_6779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6779_, 0, v_pos_6773_);
lean_ctor_set(v_reuseFailAlloc_6779_, 1, v_date_6767_);
v___x_6778_ = v_reuseFailAlloc_6779_;
goto v_reusejp_6777_;
}
v_reusejp_6777_:
{
return v___x_6778_;
}
}
}
else
{
lean_object* v_pos_6782_; lean_object* v_err_6783_; lean_object* v___x_6785_; uint8_t v_isShared_6786_; uint8_t v_isSharedCheck_6790_; 
lean_dec_ref(v_date_6767_);
v_pos_6782_ = lean_ctor_get(v___x_6772_, 0);
v_err_6783_ = lean_ctor_get(v___x_6772_, 1);
v_isSharedCheck_6790_ = !lean_is_exclusive(v___x_6772_);
if (v_isSharedCheck_6790_ == 0)
{
v___x_6785_ = v___x_6772_;
v_isShared_6786_ = v_isSharedCheck_6790_;
goto v_resetjp_6784_;
}
else
{
lean_inc(v_err_6783_);
lean_inc(v_pos_6782_);
lean_dec(v___x_6772_);
v___x_6785_ = lean_box(0);
v_isShared_6786_ = v_isSharedCheck_6790_;
goto v_resetjp_6784_;
}
v_resetjp_6784_:
{
lean_object* v___x_6788_; 
if (v_isShared_6786_ == 0)
{
v___x_6788_ = v___x_6785_;
goto v_reusejp_6787_;
}
else
{
lean_object* v_reuseFailAlloc_6789_; 
v_reuseFailAlloc_6789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6789_, 0, v_pos_6782_);
lean_ctor_set(v_reuseFailAlloc_6789_, 1, v_err_6783_);
v___x_6788_ = v_reuseFailAlloc_6789_;
goto v_reusejp_6787_;
}
v_reusejp_6787_:
{
return v___x_6788_;
}
}
}
}
else
{
lean_object* v_modifier_6791_; lean_object* v___x_6792_; 
v_modifier_6791_ = lean_ctor_get(v_mod_6769_, 0);
lean_inc_ref_n(v_modifier_6791_, 2);
lean_dec_ref_known(v_mod_6769_, 1);
v___x_6792_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_6768_, v_modifier_6791_, v_a_6770_);
if (lean_obj_tag(v___x_6792_) == 0)
{
lean_object* v_pos_6793_; lean_object* v_res_6794_; lean_object* v___x_6796_; uint8_t v_isShared_6797_; uint8_t v_isSharedCheck_6802_; 
v_pos_6793_ = lean_ctor_get(v___x_6792_, 0);
v_res_6794_ = lean_ctor_get(v___x_6792_, 1);
v_isSharedCheck_6802_ = !lean_is_exclusive(v___x_6792_);
if (v_isSharedCheck_6802_ == 0)
{
v___x_6796_ = v___x_6792_;
v_isShared_6797_ = v_isSharedCheck_6802_;
goto v_resetjp_6795_;
}
else
{
lean_inc(v_res_6794_);
lean_inc(v_pos_6793_);
lean_dec(v___x_6792_);
v___x_6796_ = lean_box(0);
v_isShared_6797_ = v_isSharedCheck_6802_;
goto v_resetjp_6795_;
}
v_resetjp_6795_:
{
lean_object* v___x_6798_; lean_object* v___x_6800_; 
v___x_6798_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(v_date_6767_, v_modifier_6791_, v_res_6794_);
if (v_isShared_6797_ == 0)
{
lean_ctor_set(v___x_6796_, 1, v___x_6798_);
v___x_6800_ = v___x_6796_;
goto v_reusejp_6799_;
}
else
{
lean_object* v_reuseFailAlloc_6801_; 
v_reuseFailAlloc_6801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6801_, 0, v_pos_6793_);
lean_ctor_set(v_reuseFailAlloc_6801_, 1, v___x_6798_);
v___x_6800_ = v_reuseFailAlloc_6801_;
goto v_reusejp_6799_;
}
v_reusejp_6799_:
{
return v___x_6800_;
}
}
}
else
{
lean_object* v_pos_6803_; lean_object* v_err_6804_; lean_object* v___x_6806_; uint8_t v_isShared_6807_; uint8_t v_isSharedCheck_6811_; 
lean_dec_ref(v_modifier_6791_);
lean_dec_ref(v_date_6767_);
v_pos_6803_ = lean_ctor_get(v___x_6792_, 0);
v_err_6804_ = lean_ctor_get(v___x_6792_, 1);
v_isSharedCheck_6811_ = !lean_is_exclusive(v___x_6792_);
if (v_isSharedCheck_6811_ == 0)
{
v___x_6806_ = v___x_6792_;
v_isShared_6807_ = v_isSharedCheck_6811_;
goto v_resetjp_6805_;
}
else
{
lean_inc(v_err_6804_);
lean_inc(v_pos_6803_);
lean_dec(v___x_6792_);
v___x_6806_ = lean_box(0);
v_isShared_6807_ = v_isSharedCheck_6811_;
goto v_resetjp_6805_;
}
v_resetjp_6805_:
{
lean_object* v___x_6809_; 
if (v_isShared_6807_ == 0)
{
v___x_6809_ = v___x_6806_;
goto v_reusejp_6808_;
}
else
{
lean_object* v_reuseFailAlloc_6810_; 
v_reuseFailAlloc_6810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6810_, 0, v_pos_6803_);
lean_ctor_set(v_reuseFailAlloc_6810_, 1, v_err_6804_);
v___x_6809_ = v_reuseFailAlloc_6810_;
goto v_reusejp_6808_;
}
v_reusejp_6808_:
{
return v___x_6809_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___redArg(lean_object* v_input_6812_, lean_object* v_config_6813_){
_start:
{
lean_object* v___x_6814_; lean_object* v___x_6815_; 
v___x_6814_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6815_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6814_, v_input_6812_);
if (lean_obj_tag(v___x_6815_) == 0)
{
lean_object* v_a_6816_; lean_object* v___x_6818_; uint8_t v_isShared_6819_; uint8_t v_isSharedCheck_6823_; 
lean_dec_ref(v_config_6813_);
v_a_6816_ = lean_ctor_get(v___x_6815_, 0);
v_isSharedCheck_6823_ = !lean_is_exclusive(v___x_6815_);
if (v_isSharedCheck_6823_ == 0)
{
v___x_6818_ = v___x_6815_;
v_isShared_6819_ = v_isSharedCheck_6823_;
goto v_resetjp_6817_;
}
else
{
lean_inc(v_a_6816_);
lean_dec(v___x_6815_);
v___x_6818_ = lean_box(0);
v_isShared_6819_ = v_isSharedCheck_6823_;
goto v_resetjp_6817_;
}
v_resetjp_6817_:
{
lean_object* v___x_6821_; 
if (v_isShared_6819_ == 0)
{
v___x_6821_ = v___x_6818_;
goto v_reusejp_6820_;
}
else
{
lean_object* v_reuseFailAlloc_6822_; 
v_reuseFailAlloc_6822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6822_, 0, v_a_6816_);
v___x_6821_ = v_reuseFailAlloc_6822_;
goto v_reusejp_6820_;
}
v_reusejp_6820_:
{
return v___x_6821_;
}
}
}
else
{
lean_object* v_a_6824_; lean_object* v___x_6826_; uint8_t v_isShared_6827_; uint8_t v_isSharedCheck_6832_; 
v_a_6824_ = lean_ctor_get(v___x_6815_, 0);
v_isSharedCheck_6832_ = !lean_is_exclusive(v___x_6815_);
if (v_isSharedCheck_6832_ == 0)
{
v___x_6826_ = v___x_6815_;
v_isShared_6827_ = v_isSharedCheck_6832_;
goto v_resetjp_6825_;
}
else
{
lean_inc(v_a_6824_);
lean_dec(v___x_6815_);
v___x_6826_ = lean_box(0);
v_isShared_6827_ = v_isSharedCheck_6832_;
goto v_resetjp_6825_;
}
v_resetjp_6825_:
{
lean_object* v___x_6828_; lean_object* v___x_6830_; 
v___x_6828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6828_, 0, v_config_6813_);
lean_ctor_set(v___x_6828_, 1, v_a_6824_);
if (v_isShared_6827_ == 0)
{
lean_ctor_set(v___x_6826_, 0, v___x_6828_);
v___x_6830_ = v___x_6826_;
goto v_reusejp_6829_;
}
else
{
lean_object* v_reuseFailAlloc_6831_; 
v_reuseFailAlloc_6831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6831_, 0, v___x_6828_);
v___x_6830_ = v_reuseFailAlloc_6831_;
goto v_reusejp_6829_;
}
v_reusejp_6829_:
{
return v___x_6830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec(lean_object* v_tz_6833_, lean_object* v_input_6834_, lean_object* v_config_6835_){
_start:
{
lean_object* v___x_6836_; 
v___x_6836_ = l_Std_Time_GenericFormat_spec___redArg(v_input_6834_, v_config_6835_);
return v___x_6836_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___boxed(lean_object* v_tz_6837_, lean_object* v_input_6838_, lean_object* v_config_6839_){
_start:
{
lean_object* v_res_6840_; 
v_res_6840_ = l_Std_Time_GenericFormat_spec(v_tz_6837_, v_input_6838_, v_config_6839_);
lean_dec(v_tz_6837_);
return v_res_6840_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(lean_object* v_tz_6841_, lean_object* v_msg_6842_){
_start:
{
lean_object* v___x_6843_; lean_object* v___x_6844_; 
v___x_6843_ = l_Std_Time_instInhabitedGenericFormat_default(v_tz_6841_);
v___x_6844_ = lean_panic_fn_borrowed(v___x_6843_, v_msg_6842_);
lean_dec_ref(v___x_6843_);
return v___x_6844_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___boxed(lean_object* v_tz_6845_, lean_object* v_msg_6846_){
_start:
{
lean_object* v_res_6847_; 
v_res_6847_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(v_tz_6845_, v_msg_6846_);
lean_dec(v_tz_6845_);
return v_res_6847_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21(lean_object* v_tz_6850_, lean_object* v_input_6851_, lean_object* v_config_6852_){
_start:
{
lean_object* v___x_6853_; lean_object* v___x_6854_; 
v___x_6853_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6854_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6853_, v_input_6851_);
if (lean_obj_tag(v___x_6854_) == 0)
{
lean_object* v_a_6855_; lean_object* v___x_6856_; lean_object* v___x_6857_; lean_object* v___x_6858_; lean_object* v___x_6859_; lean_object* v___x_6860_; lean_object* v___x_6861_; 
lean_dec_ref(v_config_6852_);
v_a_6855_ = lean_ctor_get(v___x_6854_, 0);
lean_inc(v_a_6855_);
lean_dec_ref_known(v___x_6854_, 1);
v___x_6856_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_6857_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__1));
v___x_6858_ = lean_unsigned_to_nat(1071u);
v___x_6859_ = lean_unsigned_to_nat(18u);
v___x_6860_ = l_mkPanicMessageWithDecl(v___x_6856_, v___x_6857_, v___x_6858_, v___x_6859_, v_a_6855_);
lean_dec(v_a_6855_);
v___x_6861_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(v_tz_6850_, v___x_6860_);
return v___x_6861_;
}
else
{
lean_object* v_a_6862_; lean_object* v___x_6863_; 
v_a_6862_ = lean_ctor_get(v___x_6854_, 0);
lean_inc(v_a_6862_);
lean_dec_ref_known(v___x_6854_, 1);
v___x_6863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6863_, 0, v_config_6852_);
lean_ctor_set(v___x_6863_, 1, v_a_6862_);
return v___x_6863_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21___boxed(lean_object* v_tz_6864_, lean_object* v_input_6865_, lean_object* v_config_6866_){
_start:
{
lean_object* v_res_6867_; 
v_res_6867_ = l_Std_Time_GenericFormat_spec_x21(v_tz_6864_, v_input_6865_, v_config_6866_);
lean_dec(v_tz_6864_);
return v_res_6867_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(lean_object* v_x_6868_, lean_object* v_x_6869_){
_start:
{
if (lean_obj_tag(v_x_6869_) == 0)
{
return v_x_6868_;
}
else
{
lean_object* v_head_6870_; lean_object* v_tail_6871_; lean_object* v___x_6872_; 
v_head_6870_ = lean_ctor_get(v_x_6869_, 0);
v_tail_6871_ = lean_ctor_get(v_x_6869_, 1);
v___x_6872_ = lean_string_append(v_x_6868_, v_head_6870_);
v_x_6868_ = v___x_6872_;
v_x_6869_ = v_tail_6871_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1___boxed(lean_object* v_x_6874_, lean_object* v_x_6875_){
_start:
{
lean_object* v_res_6876_; 
v_res_6876_ = l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(v_x_6874_, v_x_6875_);
lean_dec(v_x_6875_);
return v_res_6876_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0(lean_object* v_tz_6877_, lean_object* v_timestamp_6878_, lean_object* v___x_6879_, lean_object* v_x_6880_){
_start:
{
lean_object* v_offset_6881_; lean_object* v_second_6882_; lean_object* v_nano_6883_; lean_object* v___x_6884_; lean_object* v___x_6885_; lean_object* v___x_6886_; lean_object* v___x_6887_; lean_object* v___x_6888_; lean_object* v___x_6889_; lean_object* v___x_6890_; lean_object* v___x_6891_; lean_object* v___x_6892_; 
v_offset_6881_ = lean_ctor_get(v_tz_6877_, 0);
v_second_6882_ = lean_ctor_get(v_timestamp_6878_, 0);
v_nano_6883_ = lean_ctor_get(v_timestamp_6878_, 1);
v___x_6884_ = lean_nat_to_int(v___x_6879_);
v___x_6885_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_6886_ = lean_int_mul(v_second_6882_, v___x_6885_);
v___x_6887_ = lean_int_add(v___x_6886_, v_nano_6883_);
lean_dec(v___x_6886_);
v___x_6888_ = lean_int_mul(v_offset_6881_, v___x_6885_);
v___x_6889_ = lean_int_add(v___x_6888_, v___x_6884_);
lean_dec(v___x_6884_);
lean_dec(v___x_6888_);
v___x_6890_ = lean_int_add(v___x_6887_, v___x_6889_);
lean_dec(v___x_6889_);
lean_dec(v___x_6887_);
v___x_6891_ = l_Std_Time_Duration_ofNanoseconds(v___x_6890_);
lean_dec(v___x_6890_);
v___x_6892_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_6891_);
return v___x_6892_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed(lean_object* v_tz_6893_, lean_object* v_timestamp_6894_, lean_object* v___x_6895_, lean_object* v_x_6896_){
_start:
{
lean_object* v_res_6897_; 
v_res_6897_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0(v_tz_6893_, v_timestamp_6894_, v___x_6895_, v_x_6896_);
lean_dec_ref(v_timestamp_6894_);
lean_dec_ref(v_tz_6893_);
return v_res_6897_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(lean_object* v_aw_6898_, lean_object* v_date_6899_, lean_object* v_dateformat_6900_, lean_object* v_a_6901_, lean_object* v_a_6902_){
_start:
{
if (lean_obj_tag(v_a_6901_) == 0)
{
lean_object* v___x_6903_; 
lean_dec_ref(v_date_6899_);
v___x_6903_ = l_List_reverse___redArg(v_a_6902_);
return v___x_6903_;
}
else
{
lean_object* v_head_6904_; lean_object* v_tail_6905_; lean_object* v___x_6907_; uint8_t v_isShared_6908_; uint8_t v_isSharedCheck_6934_; 
v_head_6904_ = lean_ctor_get(v_a_6901_, 0);
v_tail_6905_ = lean_ctor_get(v_a_6901_, 1);
v_isSharedCheck_6934_ = !lean_is_exclusive(v_a_6901_);
if (v_isSharedCheck_6934_ == 0)
{
v___x_6907_ = v_a_6901_;
v_isShared_6908_ = v_isSharedCheck_6934_;
goto v_resetjp_6906_;
}
else
{
lean_inc(v_tail_6905_);
lean_inc(v_head_6904_);
lean_dec(v_a_6901_);
v___x_6907_ = lean_box(0);
v_isShared_6908_ = v_isSharedCheck_6934_;
goto v_resetjp_6906_;
}
v_resetjp_6906_:
{
lean_object* v___y_6910_; 
if (lean_obj_tag(v_aw_6898_) == 0)
{
lean_object* v_a_6915_; lean_object* v_offset_6916_; lean_object* v_name_6917_; lean_object* v_abbreviation_6918_; uint8_t v_isDST_6919_; lean_object* v_timestamp_6920_; uint8_t v___x_6921_; uint8_t v___x_6922_; lean_object* v_ltt_6923_; lean_object* v___x_6924_; lean_object* v___x_6925_; lean_object* v___x_6926_; lean_object* v___x_6927_; lean_object* v_tz_6928_; lean_object* v___f_6929_; lean_object* v___x_6930_; lean_object* v___x_6931_; lean_object* v___x_6932_; 
v_a_6915_ = lean_ctor_get(v_aw_6898_, 0);
v_offset_6916_ = lean_ctor_get(v_a_6915_, 0);
v_name_6917_ = lean_ctor_get(v_a_6915_, 1);
v_abbreviation_6918_ = lean_ctor_get(v_a_6915_, 2);
v_isDST_6919_ = lean_ctor_get_uint8(v_a_6915_, sizeof(void*)*3);
v_timestamp_6920_ = lean_ctor_get(v_date_6899_, 1);
v___x_6921_ = 0;
v___x_6922_ = 1;
lean_inc_ref(v_name_6917_);
lean_inc_ref(v_abbreviation_6918_);
lean_inc(v_offset_6916_);
v_ltt_6923_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6923_, 0, v_offset_6916_);
lean_ctor_set(v_ltt_6923_, 1, v_abbreviation_6918_);
lean_ctor_set(v_ltt_6923_, 2, v_name_6917_);
lean_ctor_set_uint8(v_ltt_6923_, sizeof(void*)*3, v_isDST_6919_);
lean_ctor_set_uint8(v_ltt_6923_, sizeof(void*)*3 + 1, v___x_6921_);
lean_ctor_set_uint8(v_ltt_6923_, sizeof(void*)*3 + 2, v___x_6922_);
v___x_6924_ = lean_unsigned_to_nat(0u);
v___x_6925_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6926_ = lean_box(0);
v___x_6927_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6927_, 0, v_ltt_6923_);
lean_ctor_set(v___x_6927_, 1, v___x_6925_);
lean_ctor_set(v___x_6927_, 2, v___x_6926_);
lean_inc_ref(v___x_6927_);
v_tz_6928_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_6927_, v_timestamp_6920_);
lean_inc_ref_n(v_timestamp_6920_, 2);
lean_inc_ref(v_tz_6928_);
v___f_6929_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_6929_, 0, v_tz_6928_);
lean_closure_set(v___f_6929_, 1, v_timestamp_6920_);
lean_closure_set(v___f_6929_, 2, v___x_6924_);
v___x_6930_ = lean_mk_thunk(v___f_6929_);
v___x_6931_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6931_, 0, v___x_6930_);
lean_ctor_set(v___x_6931_, 1, v_timestamp_6920_);
lean_ctor_set(v___x_6931_, 2, v___x_6927_);
lean_ctor_set(v___x_6931_, 3, v_tz_6928_);
v___x_6932_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6900_, v___x_6931_, v_head_6904_);
v___y_6910_ = v___x_6932_;
goto v___jp_6909_;
}
else
{
lean_object* v___x_6933_; 
lean_inc_ref(v_date_6899_);
v___x_6933_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6900_, v_date_6899_, v_head_6904_);
v___y_6910_ = v___x_6933_;
goto v___jp_6909_;
}
v___jp_6909_:
{
lean_object* v___x_6912_; 
if (v_isShared_6908_ == 0)
{
lean_ctor_set(v___x_6907_, 1, v_a_6902_);
lean_ctor_set(v___x_6907_, 0, v___y_6910_);
v___x_6912_ = v___x_6907_;
goto v_reusejp_6911_;
}
else
{
lean_object* v_reuseFailAlloc_6914_; 
v_reuseFailAlloc_6914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6914_, 0, v___y_6910_);
lean_ctor_set(v_reuseFailAlloc_6914_, 1, v_a_6902_);
v___x_6912_ = v_reuseFailAlloc_6914_;
goto v_reusejp_6911_;
}
v_reusejp_6911_:
{
v_a_6901_ = v_tail_6905_;
v_a_6902_ = v___x_6912_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___boxed(lean_object* v_aw_6935_, lean_object* v_date_6936_, lean_object* v_dateformat_6937_, lean_object* v_a_6938_, lean_object* v_a_6939_){
_start:
{
lean_object* v_res_6940_; 
v_res_6940_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(v_aw_6935_, v_date_6936_, v_dateformat_6937_, v_a_6938_, v_a_6939_);
lean_dec_ref(v_dateformat_6937_);
lean_dec(v_aw_6935_);
return v_res_6940_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format(lean_object* v_aw_6941_, lean_object* v_format_6942_, lean_object* v_date_6943_){
_start:
{
lean_object* v_config_6944_; lean_object* v_string_6945_; lean_object* v_dateformat_6946_; lean_object* v___x_6947_; lean_object* v___x_6948_; lean_object* v___x_6949_; lean_object* v___x_6950_; 
v_config_6944_ = lean_ctor_get(v_format_6942_, 0);
lean_inc_ref(v_config_6944_);
v_string_6945_ = lean_ctor_get(v_format_6942_, 1);
lean_inc(v_string_6945_);
lean_dec_ref(v_format_6942_);
v_dateformat_6946_ = lean_ctor_get(v_config_6944_, 0);
lean_inc_ref(v_dateformat_6946_);
lean_dec_ref(v_config_6944_);
v___x_6947_ = lean_box(0);
v___x_6948_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(v_aw_6941_, v_date_6943_, v_dateformat_6946_, v_string_6945_, v___x_6947_);
lean_dec_ref(v_dateformat_6946_);
v___x_6949_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_6950_ = l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(v___x_6949_, v___x_6948_);
lean_dec(v___x_6948_);
return v___x_6950_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format___boxed(lean_object* v_aw_6951_, lean_object* v_format_6952_, lean_object* v_date_6953_){
_start:
{
lean_object* v_res_6954_; 
v_res_6954_ = l_Std_Time_GenericFormat_format(v_aw_6951_, v_format_6952_, v_date_6953_);
lean_dec(v_aw_6951_);
return v_res_6954_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(lean_object* v_config_6958_, lean_object* v_aw_6959_, lean_object* v_builder_6960_, lean_object* v_x_6961_, lean_object* v_a_6962_){
_start:
{
if (lean_obj_tag(v_x_6961_) == 0)
{
lean_object* v___x_6963_; 
lean_dec_ref(v_config_6958_);
v___x_6963_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(v_builder_6960_, v_aw_6959_);
if (lean_obj_tag(v___x_6963_) == 0)
{
lean_object* v___x_6964_; lean_object* v___x_6965_; 
v___x_6964_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go___closed__1));
v___x_6965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6965_, 0, v_a_6962_);
lean_ctor_set(v___x_6965_, 1, v___x_6964_);
return v___x_6965_;
}
else
{
lean_object* v_val_6966_; lean_object* v___x_6967_; 
v_val_6966_ = lean_ctor_get(v___x_6963_, 0);
lean_inc(v_val_6966_);
lean_dec_ref_known(v___x_6963_, 1);
v___x_6967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6967_, 0, v_a_6962_);
lean_ctor_set(v___x_6967_, 1, v_val_6966_);
return v___x_6967_;
}
}
else
{
lean_object* v_head_6968_; lean_object* v_tail_6969_; lean_object* v___x_6970_; 
v_head_6968_ = lean_ctor_get(v_x_6961_, 0);
lean_inc(v_head_6968_);
v_tail_6969_ = lean_ctor_get(v_x_6961_, 1);
lean_inc(v_tail_6969_);
lean_dec_ref_known(v_x_6961_, 2);
lean_inc_ref(v_config_6958_);
v___x_6970_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(v_builder_6960_, v_config_6958_, v_head_6968_, v_a_6962_);
if (lean_obj_tag(v___x_6970_) == 0)
{
lean_object* v_pos_6971_; lean_object* v_res_6972_; 
v_pos_6971_ = lean_ctor_get(v___x_6970_, 0);
lean_inc(v_pos_6971_);
v_res_6972_ = lean_ctor_get(v___x_6970_, 1);
lean_inc(v_res_6972_);
lean_dec_ref_known(v___x_6970_, 2);
v_builder_6960_ = v_res_6972_;
v_x_6961_ = v_tail_6969_;
v_a_6962_ = v_pos_6971_;
goto _start;
}
else
{
lean_object* v_pos_6974_; lean_object* v_err_6975_; lean_object* v___x_6977_; uint8_t v_isShared_6978_; uint8_t v_isSharedCheck_6982_; 
lean_dec(v_tail_6969_);
lean_dec(v_aw_6959_);
lean_dec_ref(v_config_6958_);
v_pos_6974_ = lean_ctor_get(v___x_6970_, 0);
v_err_6975_ = lean_ctor_get(v___x_6970_, 1);
v_isSharedCheck_6982_ = !lean_is_exclusive(v___x_6970_);
if (v_isSharedCheck_6982_ == 0)
{
v___x_6977_ = v___x_6970_;
v_isShared_6978_ = v_isSharedCheck_6982_;
goto v_resetjp_6976_;
}
else
{
lean_inc(v_err_6975_);
lean_inc(v_pos_6974_);
lean_dec(v___x_6970_);
v___x_6977_ = lean_box(0);
v_isShared_6978_ = v_isSharedCheck_6982_;
goto v_resetjp_6976_;
}
v_resetjp_6976_:
{
lean_object* v___x_6980_; 
if (v_isShared_6978_ == 0)
{
v___x_6980_ = v___x_6977_;
goto v_reusejp_6979_;
}
else
{
lean_object* v_reuseFailAlloc_6981_; 
v_reuseFailAlloc_6981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6981_, 0, v_pos_6974_);
lean_ctor_set(v_reuseFailAlloc_6981_, 1, v_err_6975_);
v___x_6980_ = v_reuseFailAlloc_6981_;
goto v_reusejp_6979_;
}
v_reusejp_6979_:
{
return v___x_6980_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(lean_object* v_format_6985_, lean_object* v_config_6986_, lean_object* v_aw_6987_, lean_object* v_a_6988_){
_start:
{
lean_object* v___x_6989_; lean_object* v___x_6990_; 
v___x_6989_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser___closed__0));
v___x_6990_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(v_config_6986_, v_aw_6987_, v___x_6989_, v_format_6985_, v_a_6988_);
return v___x_6990_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(lean_object* v_config_6994_, lean_object* v_format_6995_, lean_object* v_func_6996_, lean_object* v_a_6997_){
_start:
{
if (lean_obj_tag(v_format_6995_) == 0)
{
lean_dec_ref(v_config_6994_);
if (lean_obj_tag(v_func_6996_) == 0)
{
lean_object* v___x_6998_; lean_object* v___x_6999_; 
v___x_6998_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg___closed__1));
v___x_6999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6999_, 0, v_a_6997_);
lean_ctor_set(v___x_6999_, 1, v___x_6998_);
return v___x_6999_;
}
else
{
lean_object* v_val_7000_; lean_object* v_fst_7001_; lean_object* v_snd_7002_; lean_object* v___x_7003_; uint8_t v___x_7004_; 
v_val_7000_ = lean_ctor_get(v_func_6996_, 0);
lean_inc(v_val_7000_);
lean_dec_ref_known(v_func_6996_, 1);
v_fst_7001_ = lean_ctor_get(v_a_6997_, 0);
v_snd_7002_ = lean_ctor_get(v_a_6997_, 1);
v___x_7003_ = lean_string_utf8_byte_size(v_fst_7001_);
v___x_7004_ = lean_nat_dec_eq(v_snd_7002_, v___x_7003_);
if (v___x_7004_ == 0)
{
lean_object* v___x_7005_; lean_object* v___x_7006_; 
lean_dec(v_val_7000_);
v___x_7005_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
v___x_7006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7006_, 0, v_a_6997_);
lean_ctor_set(v___x_7006_, 1, v___x_7005_);
return v___x_7006_;
}
else
{
lean_object* v___x_7007_; 
v___x_7007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7007_, 0, v_a_6997_);
lean_ctor_set(v___x_7007_, 1, v_val_7000_);
return v___x_7007_;
}
}
}
else
{
lean_object* v_head_7008_; 
v_head_7008_ = lean_ctor_get(v_format_6995_, 0);
lean_inc(v_head_7008_);
if (lean_obj_tag(v_head_7008_) == 0)
{
lean_object* v_tail_7009_; lean_object* v_val_7010_; lean_object* v___x_7011_; 
v_tail_7009_ = lean_ctor_get(v_format_6995_, 1);
lean_inc(v_tail_7009_);
lean_dec_ref_known(v_format_6995_, 2);
v_val_7010_ = lean_ctor_get(v_head_7008_, 0);
lean_inc_ref(v_val_7010_);
lean_dec_ref_known(v_head_7008_, 1);
v___x_7011_ = l_Std_Internal_Parsec_String_pstring(v_val_7010_, v_a_6997_);
if (lean_obj_tag(v___x_7011_) == 0)
{
lean_object* v_pos_7012_; 
v_pos_7012_ = lean_ctor_get(v___x_7011_, 0);
lean_inc(v_pos_7012_);
lean_dec_ref_known(v___x_7011_, 2);
v_format_6995_ = v_tail_7009_;
v_a_6997_ = v_pos_7012_;
goto _start;
}
else
{
lean_object* v_pos_7014_; lean_object* v_err_7015_; lean_object* v___x_7017_; uint8_t v_isShared_7018_; uint8_t v_isSharedCheck_7022_; 
lean_dec(v_tail_7009_);
lean_dec(v_func_6996_);
lean_dec_ref(v_config_6994_);
v_pos_7014_ = lean_ctor_get(v___x_7011_, 0);
v_err_7015_ = lean_ctor_get(v___x_7011_, 1);
v_isSharedCheck_7022_ = !lean_is_exclusive(v___x_7011_);
if (v_isSharedCheck_7022_ == 0)
{
v___x_7017_ = v___x_7011_;
v_isShared_7018_ = v_isSharedCheck_7022_;
goto v_resetjp_7016_;
}
else
{
lean_inc(v_err_7015_);
lean_inc(v_pos_7014_);
lean_dec(v___x_7011_);
v___x_7017_ = lean_box(0);
v_isShared_7018_ = v_isSharedCheck_7022_;
goto v_resetjp_7016_;
}
v_resetjp_7016_:
{
lean_object* v___x_7020_; 
if (v_isShared_7018_ == 0)
{
v___x_7020_ = v___x_7017_;
goto v_reusejp_7019_;
}
else
{
lean_object* v_reuseFailAlloc_7021_; 
v_reuseFailAlloc_7021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7021_, 0, v_pos_7014_);
lean_ctor_set(v_reuseFailAlloc_7021_, 1, v_err_7015_);
v___x_7020_ = v_reuseFailAlloc_7021_;
goto v_reusejp_7019_;
}
v_reusejp_7019_:
{
return v___x_7020_;
}
}
}
}
else
{
lean_object* v_tail_7023_; lean_object* v_modifier_7024_; lean_object* v___x_7025_; 
v_tail_7023_ = lean_ctor_get(v_format_6995_, 1);
lean_inc(v_tail_7023_);
lean_dec_ref_known(v_format_6995_, 2);
v_modifier_7024_ = lean_ctor_get(v_head_7008_, 0);
lean_inc_ref(v_modifier_7024_);
lean_dec_ref_known(v_head_7008_, 1);
lean_inc_ref(v_config_6994_);
v___x_7025_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_6994_, v_modifier_7024_, v_a_6997_);
if (lean_obj_tag(v___x_7025_) == 0)
{
lean_object* v_pos_7026_; lean_object* v_res_7027_; lean_object* v___x_7028_; 
v_pos_7026_ = lean_ctor_get(v___x_7025_, 0);
lean_inc(v_pos_7026_);
v_res_7027_ = lean_ctor_get(v___x_7025_, 1);
lean_inc(v_res_7027_);
lean_dec_ref_known(v___x_7025_, 2);
v___x_7028_ = lean_apply_1(v_func_6996_, v_res_7027_);
v_format_6995_ = v_tail_7023_;
v_func_6996_ = v___x_7028_;
v_a_6997_ = v_pos_7026_;
goto _start;
}
else
{
lean_object* v_pos_7030_; lean_object* v_err_7031_; lean_object* v___x_7033_; uint8_t v_isShared_7034_; uint8_t v_isSharedCheck_7038_; 
lean_dec(v_tail_7023_);
lean_dec(v_func_6996_);
lean_dec_ref(v_config_6994_);
v_pos_7030_ = lean_ctor_get(v___x_7025_, 0);
v_err_7031_ = lean_ctor_get(v___x_7025_, 1);
v_isSharedCheck_7038_ = !lean_is_exclusive(v___x_7025_);
if (v_isSharedCheck_7038_ == 0)
{
v___x_7033_ = v___x_7025_;
v_isShared_7034_ = v_isSharedCheck_7038_;
goto v_resetjp_7032_;
}
else
{
lean_inc(v_err_7031_);
lean_inc(v_pos_7030_);
lean_dec(v___x_7025_);
v___x_7033_ = lean_box(0);
v_isShared_7034_ = v_isSharedCheck_7038_;
goto v_resetjp_7032_;
}
v_resetjp_7032_:
{
lean_object* v___x_7036_; 
if (v_isShared_7034_ == 0)
{
v___x_7036_ = v___x_7033_;
goto v_reusejp_7035_;
}
else
{
lean_object* v_reuseFailAlloc_7037_; 
v_reuseFailAlloc_7037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7037_, 0, v_pos_7030_);
lean_ctor_set(v_reuseFailAlloc_7037_, 1, v_err_7031_);
v___x_7036_ = v_reuseFailAlloc_7037_;
goto v_reusejp_7035_;
}
v_reusejp_7035_:
{
return v___x_7036_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go(lean_object* v_00_u03b1_7039_, lean_object* v_config_7040_, lean_object* v_format_7041_, lean_object* v_func_7042_, lean_object* v_a_7043_){
_start:
{
lean_object* v___x_7044_; 
v___x_7044_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7040_, v_format_7041_, v_func_7042_, v_a_7043_);
return v___x_7044_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser___redArg(lean_object* v_format_7045_, lean_object* v_config_7046_, lean_object* v_func_7047_, lean_object* v_a_7048_){
_start:
{
lean_object* v___x_7049_; 
v___x_7049_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7046_, v_format_7045_, v_func_7047_, v_a_7048_);
return v___x_7049_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser(lean_object* v_00_u03b1_7050_, lean_object* v_format_7051_, lean_object* v_config_7052_, lean_object* v_func_7053_, lean_object* v_a_7054_){
_start:
{
lean_object* v___x_7055_; 
v___x_7055_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7052_, v_format_7051_, v_func_7053_, v_a_7054_);
return v___x_7055_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse___lam__0(lean_object* v_string_7056_, lean_object* v_config_7057_, lean_object* v_aw_7058_, lean_object* v___y_7059_){
_start:
{
lean_object* v___x_7060_; 
v___x_7060_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(v_string_7056_, v_config_7057_, v_aw_7058_, v___y_7059_);
if (lean_obj_tag(v___x_7060_) == 0)
{
lean_object* v_pos_7061_; lean_object* v_fst_7062_; lean_object* v_snd_7063_; lean_object* v___x_7064_; uint8_t v___x_7065_; 
v_pos_7061_ = lean_ctor_get(v___x_7060_, 0);
lean_inc(v_pos_7061_);
v_fst_7062_ = lean_ctor_get(v_pos_7061_, 0);
v_snd_7063_ = lean_ctor_get(v_pos_7061_, 1);
v___x_7064_ = lean_string_utf8_byte_size(v_fst_7062_);
v___x_7065_ = lean_nat_dec_eq(v_snd_7063_, v___x_7064_);
if (v___x_7065_ == 0)
{
lean_object* v___x_7067_; uint8_t v_isShared_7068_; uint8_t v_isSharedCheck_7073_; 
v_isSharedCheck_7073_ = !lean_is_exclusive(v___x_7060_);
if (v_isSharedCheck_7073_ == 0)
{
lean_object* v_unused_7074_; lean_object* v_unused_7075_; 
v_unused_7074_ = lean_ctor_get(v___x_7060_, 1);
lean_dec(v_unused_7074_);
v_unused_7075_ = lean_ctor_get(v___x_7060_, 0);
lean_dec(v_unused_7075_);
v___x_7067_ = v___x_7060_;
v_isShared_7068_ = v_isSharedCheck_7073_;
goto v_resetjp_7066_;
}
else
{
lean_dec(v___x_7060_);
v___x_7067_ = lean_box(0);
v_isShared_7068_ = v_isSharedCheck_7073_;
goto v_resetjp_7066_;
}
v_resetjp_7066_:
{
lean_object* v___x_7069_; lean_object* v___x_7071_; 
v___x_7069_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_7068_ == 0)
{
lean_ctor_set_tag(v___x_7067_, 1);
lean_ctor_set(v___x_7067_, 1, v___x_7069_);
v___x_7071_ = v___x_7067_;
goto v_reusejp_7070_;
}
else
{
lean_object* v_reuseFailAlloc_7072_; 
v_reuseFailAlloc_7072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7072_, 0, v_pos_7061_);
lean_ctor_set(v_reuseFailAlloc_7072_, 1, v___x_7069_);
v___x_7071_ = v_reuseFailAlloc_7072_;
goto v_reusejp_7070_;
}
v_reusejp_7070_:
{
return v___x_7071_;
}
}
}
else
{
lean_dec(v_pos_7061_);
return v___x_7060_;
}
}
else
{
return v___x_7060_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse(lean_object* v_aw_7076_, lean_object* v_format_7077_, lean_object* v_input_7078_){
_start:
{
lean_object* v_config_7079_; lean_object* v_string_7080_; lean_object* v___f_7081_; lean_object* v___x_7082_; 
v_config_7079_ = lean_ctor_get(v_format_7077_, 0);
lean_inc_ref(v_config_7079_);
v_string_7080_ = lean_ctor_get(v_format_7077_, 1);
lean_inc(v_string_7080_);
lean_dec_ref(v_format_7077_);
v___f_7081_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parse___lam__0), 4, 3);
lean_closure_set(v___f_7081_, 0, v_string_7080_);
lean_closure_set(v___f_7081_, 1, v_config_7079_);
lean_closure_set(v___f_7081_, 2, v_aw_7076_);
v___x_7082_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_7081_, v_input_7078_);
return v___x_7082_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(lean_object* v_msg_7083_){
_start:
{
lean_object* v___x_7084_; lean_object* v___x_7085_; 
v___x_7084_ = l_Std_Time_instInhabitedDateTime;
v___x_7085_ = lean_panic_fn_borrowed(v___x_7084_, v_msg_7083_);
return v___x_7085_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse_x21(lean_object* v_aw_7087_, lean_object* v_format_7088_, lean_object* v_input_7089_){
_start:
{
lean_object* v___x_7090_; 
v___x_7090_ = l_Std_Time_GenericFormat_parse(v_aw_7087_, v_format_7088_, v_input_7089_);
if (lean_obj_tag(v___x_7090_) == 0)
{
lean_object* v_a_7091_; lean_object* v___x_7092_; lean_object* v___x_7093_; lean_object* v___x_7094_; lean_object* v___x_7095_; lean_object* v___x_7096_; lean_object* v___x_7097_; 
v_a_7091_ = lean_ctor_get(v___x_7090_, 0);
lean_inc(v_a_7091_);
lean_dec_ref_known(v___x_7090_, 1);
v___x_7092_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_7093_ = ((lean_object*)(l_Std_Time_GenericFormat_parse_x21___closed__0));
v___x_7094_ = lean_unsigned_to_nat(1124u);
v___x_7095_ = lean_unsigned_to_nat(18u);
v___x_7096_ = l_mkPanicMessageWithDecl(v___x_7092_, v___x_7093_, v___x_7094_, v___x_7095_, v_a_7091_);
lean_dec(v_a_7091_);
v___x_7097_ = l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(v___x_7096_);
return v___x_7097_;
}
else
{
lean_object* v_a_7098_; 
v_a_7098_ = lean_ctor_get(v___x_7090_, 0);
lean_inc(v_a_7098_);
lean_dec_ref_known(v___x_7090_, 1);
return v_a_7098_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0(lean_object* v_config_7099_, lean_object* v_string_7100_, lean_object* v_builder_7101_, lean_object* v___y_7102_){
_start:
{
lean_object* v___x_7103_; 
v___x_7103_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7099_, v_string_7100_, v_builder_7101_, v___y_7102_);
return v___x_7103_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg(lean_object* v_format_7104_, lean_object* v_builder_7105_, lean_object* v_input_7106_){
_start:
{
lean_object* v_config_7107_; lean_object* v_string_7108_; lean_object* v___f_7109_; lean_object* v___x_7110_; 
v_config_7107_ = lean_ctor_get(v_format_7104_, 0);
lean_inc_ref(v_config_7107_);
v_string_7108_ = lean_ctor_get(v_format_7104_, 1);
lean_inc(v_string_7108_);
lean_dec_ref(v_format_7104_);
v___f_7109_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0), 4, 3);
lean_closure_set(v___f_7109_, 0, v_config_7107_);
lean_closure_set(v___f_7109_, 1, v_string_7108_);
lean_closure_set(v___f_7109_, 2, v_builder_7105_);
v___x_7110_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_7109_, v_input_7106_);
return v___x_7110_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder(lean_object* v_aw_7111_, lean_object* v_00_u03b1_7112_, lean_object* v_format_7113_, lean_object* v_builder_7114_, lean_object* v_input_7115_){
_start:
{
lean_object* v___x_7116_; 
v___x_7116_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_7113_, v_builder_7114_, v_input_7115_);
return v___x_7116_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___boxed(lean_object* v_aw_7117_, lean_object* v_00_u03b1_7118_, lean_object* v_format_7119_, lean_object* v_builder_7120_, lean_object* v_input_7121_){
_start:
{
lean_object* v_res_7122_; 
v_res_7122_ = l_Std_Time_GenericFormat_parseBuilder(v_aw_7117_, v_00_u03b1_7118_, v_format_7119_, v_builder_7120_, v_input_7121_);
lean_dec(v_aw_7117_);
return v_res_7122_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg(lean_object* v_inst_7124_, lean_object* v_format_7125_, lean_object* v_builder_7126_, lean_object* v_input_7127_){
_start:
{
lean_object* v___x_7128_; 
v___x_7128_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_7125_, v_builder_7126_, v_input_7127_);
if (lean_obj_tag(v___x_7128_) == 0)
{
lean_object* v_a_7129_; lean_object* v___x_7130_; lean_object* v___x_7131_; lean_object* v___x_7132_; lean_object* v___x_7133_; lean_object* v___x_7134_; lean_object* v___x_7135_; 
v_a_7129_ = lean_ctor_get(v___x_7128_, 0);
lean_inc(v_a_7129_);
lean_dec_ref_known(v___x_7128_, 1);
v___x_7130_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_7131_ = ((lean_object*)(l_Std_Time_GenericFormat_parseBuilder_x21___redArg___closed__0));
v___x_7132_ = lean_unsigned_to_nat(1138u);
v___x_7133_ = lean_unsigned_to_nat(18u);
v___x_7134_ = l_mkPanicMessageWithDecl(v___x_7130_, v___x_7131_, v___x_7132_, v___x_7133_, v_a_7129_);
lean_dec(v_a_7129_);
v___x_7135_ = l_panic___redArg(v_inst_7124_, v___x_7134_);
return v___x_7135_;
}
else
{
lean_object* v_a_7136_; 
v_a_7136_ = lean_ctor_get(v___x_7128_, 0);
lean_inc(v_a_7136_);
lean_dec_ref_known(v___x_7128_, 1);
return v_a_7136_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg___boxed(lean_object* v_inst_7137_, lean_object* v_format_7138_, lean_object* v_builder_7139_, lean_object* v_input_7140_){
_start:
{
lean_object* v_res_7141_; 
v_res_7141_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7137_, v_format_7138_, v_builder_7139_, v_input_7140_);
lean_dec(v_inst_7137_);
return v_res_7141_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21(lean_object* v_00_u03b1_7142_, lean_object* v_aw_7143_, lean_object* v_inst_7144_, lean_object* v_format_7145_, lean_object* v_builder_7146_, lean_object* v_input_7147_){
_start:
{
lean_object* v___x_7148_; 
v___x_7148_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7144_, v_format_7145_, v_builder_7146_, v_input_7147_);
return v___x_7148_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___boxed(lean_object* v_00_u03b1_7149_, lean_object* v_aw_7150_, lean_object* v_inst_7151_, lean_object* v_format_7152_, lean_object* v_builder_7153_, lean_object* v_input_7154_){
_start:
{
lean_object* v_res_7155_; 
v_res_7155_ = l_Std_Time_GenericFormat_parseBuilder_x21(v_00_u03b1_7149_, v_aw_7150_, v_inst_7151_, v_format_7152_, v_builder_7153_, v_input_7154_);
lean_dec(v_inst_7151_);
lean_dec(v_aw_7150_);
return v_res_7155_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(lean_object* v_getInfo_7156_, lean_object* v_dateformat_7157_, lean_object* v_data_7158_, lean_object* v_format_7159_){
_start:
{
if (lean_obj_tag(v_format_7159_) == 0)
{
lean_object* v___x_7160_; 
lean_dec_ref(v_getInfo_7156_);
v___x_7160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7160_, 0, v_data_7158_);
return v___x_7160_;
}
else
{
lean_object* v_head_7161_; 
v_head_7161_ = lean_ctor_get(v_format_7159_, 0);
lean_inc(v_head_7161_);
if (lean_obj_tag(v_head_7161_) == 0)
{
lean_object* v_tail_7162_; lean_object* v_val_7163_; lean_object* v___x_7164_; 
v_tail_7162_ = lean_ctor_get(v_format_7159_, 1);
lean_inc(v_tail_7162_);
lean_dec_ref_known(v_format_7159_, 2);
v_val_7163_ = lean_ctor_get(v_head_7161_, 0);
lean_inc_ref(v_val_7163_);
lean_dec_ref_known(v_head_7161_, 1);
v___x_7164_ = lean_string_append(v_data_7158_, v_val_7163_);
lean_dec_ref(v_val_7163_);
v_data_7158_ = v___x_7164_;
v_format_7159_ = v_tail_7162_;
goto _start;
}
else
{
lean_object* v_tail_7166_; lean_object* v_modifier_7167_; lean_object* v___x_7168_; 
v_tail_7166_ = lean_ctor_get(v_format_7159_, 1);
lean_inc(v_tail_7166_);
lean_dec_ref_known(v_format_7159_, 2);
v_modifier_7167_ = lean_ctor_get(v_head_7161_, 0);
lean_inc_ref_n(v_modifier_7167_, 2);
lean_dec_ref_known(v_head_7161_, 1);
lean_inc_ref(v_getInfo_7156_);
v___x_7168_ = lean_apply_1(v_getInfo_7156_, v_modifier_7167_);
if (lean_obj_tag(v___x_7168_) == 0)
{
lean_object* v___x_7169_; 
lean_dec_ref(v_modifier_7167_);
lean_dec(v_tail_7166_);
lean_dec_ref(v_data_7158_);
lean_dec_ref(v_getInfo_7156_);
v___x_7169_ = lean_box(0);
return v___x_7169_;
}
else
{
lean_object* v_val_7170_; lean_object* v___x_7171_; lean_object* v___x_7172_; 
v_val_7170_ = lean_ctor_get(v___x_7168_, 0);
lean_inc(v_val_7170_);
lean_dec_ref_known(v___x_7168_, 1);
v___x_7171_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7157_, v_modifier_7167_, v_val_7170_);
v___x_7172_ = lean_string_append(v_data_7158_, v___x_7171_);
lean_dec_ref(v___x_7171_);
v_data_7158_ = v___x_7172_;
v_format_7159_ = v_tail_7166_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go___boxed(lean_object* v_getInfo_7174_, lean_object* v_dateformat_7175_, lean_object* v_data_7176_, lean_object* v_format_7177_){
_start:
{
lean_object* v_res_7178_; 
v_res_7178_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(v_getInfo_7174_, v_dateformat_7175_, v_data_7176_, v_format_7177_);
lean_dec_ref(v_dateformat_7175_);
return v_res_7178_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___redArg(lean_object* v_format_7179_, lean_object* v_getInfo_7180_){
_start:
{
lean_object* v_config_7181_; lean_object* v_string_7182_; lean_object* v_dateformat_7183_; lean_object* v___x_7184_; lean_object* v___x_7185_; 
v_config_7181_ = lean_ctor_get(v_format_7179_, 0);
lean_inc_ref(v_config_7181_);
v_string_7182_ = lean_ctor_get(v_format_7179_, 1);
lean_inc(v_string_7182_);
lean_dec_ref(v_format_7179_);
v_dateformat_7183_ = lean_ctor_get(v_config_7181_, 0);
lean_inc_ref(v_dateformat_7183_);
lean_dec_ref(v_config_7181_);
v___x_7184_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_7185_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(v_getInfo_7180_, v_dateformat_7183_, v___x_7184_, v_string_7182_);
lean_dec_ref(v_dateformat_7183_);
return v___x_7185_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric(lean_object* v_aw_7186_, lean_object* v_format_7187_, lean_object* v_getInfo_7188_){
_start:
{
lean_object* v___x_7189_; 
v___x_7189_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_format_7187_, v_getInfo_7188_);
return v___x_7189_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___boxed(lean_object* v_aw_7190_, lean_object* v_format_7191_, lean_object* v_getInfo_7192_){
_start:
{
lean_object* v_res_7193_; 
v_res_7193_ = l_Std_Time_GenericFormat_formatGeneric(v_aw_7190_, v_format_7191_, v_getInfo_7192_);
lean_dec(v_aw_7190_);
return v_res_7193_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(lean_object* v_dateformat_7194_, lean_object* v_data_7195_, lean_object* v_format_7196_){
_start:
{
if (lean_obj_tag(v_format_7196_) == 0)
{
lean_dec_ref(v_dateformat_7194_);
return v_data_7195_;
}
else
{
lean_object* v_head_7197_; 
v_head_7197_ = lean_ctor_get(v_format_7196_, 0);
lean_inc(v_head_7197_);
if (lean_obj_tag(v_head_7197_) == 0)
{
lean_object* v_tail_7198_; lean_object* v_val_7199_; lean_object* v___x_7200_; 
v_tail_7198_ = lean_ctor_get(v_format_7196_, 1);
lean_inc(v_tail_7198_);
lean_dec_ref_known(v_format_7196_, 2);
v_val_7199_ = lean_ctor_get(v_head_7197_, 0);
lean_inc_ref(v_val_7199_);
lean_dec_ref_known(v_head_7197_, 1);
v___x_7200_ = lean_string_append(v_data_7195_, v_val_7199_);
lean_dec_ref(v_val_7199_);
v_data_7195_ = v___x_7200_;
v_format_7196_ = v_tail_7198_;
goto _start;
}
else
{
lean_object* v_tail_7202_; lean_object* v_modifier_7203_; lean_object* v___f_7204_; 
v_tail_7202_ = lean_ctor_get(v_format_7196_, 1);
lean_inc(v_tail_7202_);
lean_dec_ref_known(v_format_7196_, 2);
v_modifier_7203_ = lean_ctor_get(v_head_7197_, 0);
lean_inc_ref(v_modifier_7203_);
lean_dec_ref_known(v_head_7197_, 1);
v___f_7204_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0), 5, 4);
lean_closure_set(v___f_7204_, 0, v_dateformat_7194_);
lean_closure_set(v___f_7204_, 1, v_modifier_7203_);
lean_closure_set(v___f_7204_, 2, v_data_7195_);
lean_closure_set(v___f_7204_, 3, v_tail_7202_);
return v___f_7204_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0(lean_object* v_dateformat_7205_, lean_object* v_modifier_7206_, lean_object* v_data_7207_, lean_object* v_tail_7208_, lean_object* v___y_7209_){
_start:
{
lean_object* v___x_7210_; lean_object* v___x_7211_; lean_object* v___x_7212_; 
v___x_7210_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7205_, v_modifier_7206_, v___y_7209_);
v___x_7211_ = lean_string_append(v_data_7207_, v___x_7210_);
lean_dec_ref(v___x_7210_);
v___x_7212_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7205_, v___x_7211_, v_tail_7208_);
return v___x_7212_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___redArg(lean_object* v_format_7213_){
_start:
{
lean_object* v_config_7214_; lean_object* v_string_7215_; lean_object* v_dateformat_7216_; lean_object* v___x_7217_; lean_object* v___x_7218_; 
v_config_7214_ = lean_ctor_get(v_format_7213_, 0);
lean_inc_ref(v_config_7214_);
v_string_7215_ = lean_ctor_get(v_format_7213_, 1);
lean_inc(v_string_7215_);
lean_dec_ref(v_format_7213_);
v_dateformat_7216_ = lean_ctor_get(v_config_7214_, 0);
lean_inc_ref(v_dateformat_7216_);
lean_dec_ref(v_config_7214_);
v___x_7217_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_7218_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7216_, v___x_7217_, v_string_7215_);
return v___x_7218_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder(lean_object* v_aw_7219_, lean_object* v_format_7220_){
_start:
{
lean_object* v___x_7221_; 
v___x_7221_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v_format_7220_);
return v___x_7221_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___boxed(lean_object* v_aw_7222_, lean_object* v_format_7223_){
_start:
{
lean_object* v_res_7224_; 
v_res_7224_ = l_Std_Time_GenericFormat_formatBuilder(v_aw_7222_, v_format_7223_);
lean_dec(v_aw_7222_);
return v_res_7224_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instFormatGenericFormatFormatTypeString(lean_object* v_aw_7225_){
_start:
{
lean_object* v___x_7226_; lean_object* v___x_7227_; lean_object* v___x_7228_; 
lean_inc(v_aw_7225_);
v___x_7226_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_formatBuilder___boxed), 2, 1);
lean_closure_set(v___x_7226_, 0, v_aw_7225_);
v___x_7227_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parseBuilder___boxed), 5, 1);
lean_closure_set(v___x_7227_, 0, v_aw_7225_);
v___x_7228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7228_, 0, v___x_7226_);
lean_ctor_set(v___x_7228_, 1, v___x_7227_);
return v___x_7228_;
}
}
lean_object* runtime_initialize_Std_Time_Zoned(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Format_Modifier(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Format_DateFormat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Format_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time_Zoned(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Format_Modifier(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Format_DateFormat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_instInhabitedFormatConfig_default = _init_l_Std_Time_instInhabitedFormatConfig_default();
lean_mark_persistent(l_Std_Time_instInhabitedFormatConfig_default);
l_Std_Time_instInhabitedFormatConfig = _init_l_Std_Time_instInhabitedFormatConfig();
lean_mark_persistent(l_Std_Time_instInhabitedFormatConfig);
l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1 = _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1();
lean_mark_persistent(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1);
l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2 = _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2();
lean_mark_persistent(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2);
l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___boxed__const__1 = _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___boxed__const__1();
lean_mark_persistent(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Format_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Zoned(uint8_t builtin);
lean_object* initialize_Std_Time_Format_Modifier(uint8_t builtin);
lean_object* initialize_Std_Time_Format_DateFormat(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Format_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Format_Modifier(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Format_DateFormat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Format_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
