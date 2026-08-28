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
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
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
lean_object* lean_thunk_get_own(lean_object*);
lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__0;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__1;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__2;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0;
static const lean_closure_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__1_value;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "invalid second offset: "};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = ". Must be between 0 and 59."};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_value;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "invalid minute offset: "};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__7 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__7_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid hour offset: "};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = ". Must be between 0 and 23."};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9_value;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10;
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
lean_object* v_fst_202_; lean_object* v_snd_203_; lean_object* v_pos_205_; lean_object* v_snd_206_; lean_object* v_err_207_; lean_object* v___x_211_; uint8_t v_decide_212_; 
v_fst_202_ = lean_ctor_get(v_a_201_, 0);
v_snd_203_ = lean_ctor_get(v_a_201_, 1);
lean_inc(v_snd_203_);
v___x_211_ = lean_string_utf8_byte_size(v_fst_202_);
v_decide_212_ = lean_nat_dec_eq(v_snd_203_, v___x_211_);
if (v_decide_212_ == 0)
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
uint8_t v_decide_208_; 
v_decide_208_ = lean_nat_dec_eq(v_snd_203_, v_snd_206_);
lean_dec(v_snd_206_);
lean_dec(v_snd_203_);
if (v_decide_208_ == 0)
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
lean_object* v_fst_232_; lean_object* v_snd_233_; lean_object* v_pos_235_; lean_object* v_snd_236_; lean_object* v_err_237_; lean_object* v___x_241_; uint8_t v_decide_242_; 
v_fst_232_ = lean_ctor_get(v_a_231_, 0);
v_snd_233_ = lean_ctor_get(v_a_231_, 1);
lean_inc(v_snd_233_);
v___x_241_ = lean_string_utf8_byte_size(v_fst_232_);
v_decide_242_ = lean_nat_dec_eq(v_snd_233_, v___x_241_);
if (v_decide_242_ == 0)
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
uint8_t v_decide_238_; 
v_decide_238_ = lean_nat_dec_eq(v_snd_233_, v_snd_236_);
lean_dec(v_snd_236_);
lean_dec(v_snd_233_);
if (v_decide_238_ == 0)
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(uint8_t v_decide_263_, uint32_t v___x_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_fst_269_; lean_object* v_snd_270_; lean_object* v___x_271_; uint8_t v_decide_272_; 
v_fst_269_ = lean_ctor_get(v___y_265_, 0);
v_snd_270_ = lean_ctor_get(v___y_265_, 1);
v___x_271_ = lean_string_utf8_byte_size(v_fst_269_);
v_decide_272_ = lean_nat_dec_eq(v_snd_270_, v___x_271_);
if (v_decide_272_ == 0)
{
if (v_decide_263_ == 0)
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
uint8_t v_decide_292_; 
v_decide_292_ = lean_nat_dec_eq(v___x_286_, v___x_271_);
if (v_decide_292_ == 0)
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
lean_object* v_fst_305_; lean_object* v_snd_306_; lean_object* v___x_307_; uint8_t v_decide_308_; 
v_fst_305_ = lean_ctor_get(v_pos_300_, 0);
v_snd_306_ = lean_ctor_get(v_pos_300_, 1);
v___x_307_ = lean_string_utf8_byte_size(v_fst_305_);
v_decide_308_ = lean_nat_dec_eq(v_snd_306_, v___x_307_);
if (v_decide_308_ == 0)
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___boxed(lean_object* v_decide_344_, lean_object* v___x_345_, lean_object* v___y_346_){
_start:
{
uint8_t v_decide_11288__boxed_347_; uint32_t v___x_11289__boxed_348_; lean_object* v_res_349_; 
v_decide_11288__boxed_347_ = lean_unbox(v_decide_344_);
v___x_11289__boxed_348_ = lean_unbox_uint32(v___x_345_);
lean_dec(v___x_345_);
v_res_349_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(v_decide_11288__boxed_347_, v___x_11289__boxed_348_, v___y_346_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2_spec__3(lean_object* v_acc_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_fst_352_; lean_object* v_snd_353_; lean_object* v_pos_355_; lean_object* v_snd_356_; lean_object* v_err_357_; lean_object* v___x_361_; uint8_t v_decide_362_; 
v_fst_352_ = lean_ctor_get(v_a_351_, 0);
v_snd_353_ = lean_ctor_get(v_a_351_, 1);
lean_inc(v_snd_353_);
v___x_361_ = lean_string_utf8_byte_size(v_fst_352_);
v_decide_362_ = lean_nat_dec_eq(v_snd_353_, v___x_361_);
if (v_decide_362_ == 0)
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
uint8_t v_decide_358_; 
v_decide_358_ = lean_nat_dec_eq(v_snd_353_, v_snd_356_);
lean_dec(v_snd_356_);
lean_dec(v_snd_353_);
if (v_decide_358_ == 0)
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
lean_object* v_fst_382_; lean_object* v_snd_383_; lean_object* v_pos_385_; lean_object* v_snd_386_; lean_object* v_err_387_; lean_object* v___x_391_; uint8_t v_decide_392_; 
v_fst_382_ = lean_ctor_get(v_a_381_, 0);
v_snd_383_ = lean_ctor_get(v_a_381_, 1);
lean_inc(v_snd_383_);
v___x_391_ = lean_string_utf8_byte_size(v_fst_382_);
v_decide_392_ = lean_nat_dec_eq(v_snd_383_, v___x_391_);
if (v_decide_392_ == 0)
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
uint8_t v_decide_388_; 
v_decide_388_ = lean_nat_dec_eq(v_snd_383_, v_snd_386_);
lean_dec(v_snd_386_);
lean_dec(v_snd_383_);
if (v_decide_388_ == 0)
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0(uint8_t v_decide_410_, uint32_t v___x_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_fst_416_; lean_object* v_snd_417_; lean_object* v___x_418_; uint8_t v_decide_419_; 
v_fst_416_ = lean_ctor_get(v___y_412_, 0);
v_snd_417_ = lean_ctor_get(v___y_412_, 1);
v___x_418_ = lean_string_utf8_byte_size(v_fst_416_);
v_decide_419_ = lean_nat_dec_eq(v_snd_417_, v___x_418_);
if (v_decide_419_ == 0)
{
if (v_decide_410_ == 0)
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
uint8_t v_decide_439_; 
v_decide_439_ = lean_nat_dec_eq(v___x_433_, v___x_418_);
if (v_decide_439_ == 0)
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
lean_object* v_fst_452_; lean_object* v_snd_453_; lean_object* v___x_454_; uint8_t v_decide_455_; 
v_fst_452_ = lean_ctor_get(v_pos_447_, 0);
v_snd_453_ = lean_ctor_get(v_pos_447_, 1);
v___x_454_ = lean_string_utf8_byte_size(v_fst_452_);
v_decide_455_ = lean_nat_dec_eq(v_snd_453_, v___x_454_);
if (v_decide_455_ == 0)
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___boxed(lean_object* v_decide_491_, lean_object* v___x_492_, lean_object* v___y_493_){
_start:
{
uint8_t v_decide_11555__boxed_494_; uint32_t v___x_11556__boxed_495_; lean_object* v_res_496_; 
v_decide_11555__boxed_494_ = lean_unbox(v_decide_491_);
v___x_11556__boxed_495_ = lean_unbox_uint32(v___x_492_);
lean_dec(v___x_492_);
v_res_496_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0(v_decide_11555__boxed_494_, v___x_11556__boxed_495_, v___y_493_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__3(lean_object* v_acc_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_fst_499_; lean_object* v_snd_500_; lean_object* v_pos_502_; lean_object* v_snd_503_; lean_object* v_err_504_; lean_object* v___x_510_; uint8_t v_decide_511_; 
v_fst_499_ = lean_ctor_get(v_a_498_, 0);
v_snd_500_ = lean_ctor_get(v_a_498_, 1);
lean_inc(v_snd_500_);
v___x_510_ = lean_string_utf8_byte_size(v_fst_499_);
v_decide_511_ = lean_nat_dec_eq(v_snd_500_, v___x_510_);
if (v_decide_511_ == 0)
{
uint32_t v___x_512_; uint32_t v___x_513_; uint8_t v___x_514_; uint32_t v_c_515_; lean_object* v___x_516_; lean_object* v_it_x27_517_; uint8_t v___y_519_; uint8_t v___y_520_; uint8_t v___y_524_; uint8_t v___y_525_; uint8_t v___y_526_; uint8_t v___y_528_; uint8_t v___y_529_; uint8_t v___y_532_; uint8_t v___y_535_; uint8_t v___y_537_; uint32_t v___x_542_; uint8_t v___x_543_; 
v___x_512_ = 39;
v___x_513_ = 34;
v___x_514_ = 1;
v_c_515_ = lean_string_utf8_get_fast(v_fst_499_, v_snd_500_);
v___x_516_ = lean_string_utf8_next_fast(v_fst_499_, v_snd_500_);
lean_inc(v_fst_499_);
v_it_x27_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_517_, 0, v_fst_499_);
lean_ctor_set(v_it_x27_517_, 1, v___x_516_);
v___x_542_ = 65;
v___x_543_ = lean_uint32_dec_le(v___x_542_, v_c_515_);
if (v___x_543_ == 0)
{
v___y_537_ = v___x_543_;
goto v___jp_536_;
}
else
{
uint32_t v___x_544_; uint8_t v___x_545_; 
v___x_544_ = 90;
v___x_545_ = lean_uint32_dec_le(v_c_515_, v___x_544_);
v___y_537_ = v___x_545_;
goto v___jp_536_;
}
v___jp_518_:
{
if (v___y_519_ == 0)
{
lean_dec_ref_known(v_it_x27_517_, 2);
goto v___jp_508_;
}
else
{
if (v___y_520_ == 0)
{
lean_dec_ref_known(v_it_x27_517_, 2);
goto v___jp_508_;
}
else
{
lean_object* v___x_521_; 
lean_dec(v_snd_500_);
lean_dec_ref(v_a_498_);
v___x_521_ = lean_string_push(v_acc_497_, v_c_515_);
v_acc_497_ = v___x_521_;
v_a_498_ = v_it_x27_517_;
goto _start;
}
}
}
v___jp_523_:
{
if (v___y_525_ == 0)
{
v___y_519_ = v___y_524_;
v___y_520_ = v___y_525_;
goto v___jp_518_;
}
else
{
v___y_519_ = v___y_524_;
v___y_520_ = v___y_526_;
goto v___jp_518_;
}
}
v___jp_527_:
{
uint8_t v___x_530_; 
v___x_530_ = lean_uint32_dec_eq(v_c_515_, v___x_513_);
if (v___x_530_ == 0)
{
v___y_524_ = v___y_528_;
v___y_525_ = v___y_529_;
v___y_526_ = v___x_514_;
goto v___jp_523_;
}
else
{
v___y_524_ = v___y_528_;
v___y_525_ = v___y_529_;
v___y_526_ = v_decide_511_;
goto v___jp_523_;
}
}
v___jp_531_:
{
uint8_t v___x_533_; 
v___x_533_ = lean_uint32_dec_eq(v_c_515_, v___x_512_);
if (v___x_533_ == 0)
{
v___y_528_ = v___y_532_;
v___y_529_ = v___x_514_;
goto v___jp_527_;
}
else
{
v___y_528_ = v___y_532_;
v___y_529_ = v_decide_511_;
goto v___jp_527_;
}
}
v___jp_534_:
{
if (v___y_535_ == 0)
{
v___y_532_ = v___x_514_;
goto v___jp_531_;
}
else
{
v___y_532_ = v_decide_511_;
goto v___jp_531_;
}
}
v___jp_536_:
{
if (v___y_537_ == 0)
{
uint32_t v___x_538_; uint8_t v___x_539_; 
v___x_538_ = 97;
v___x_539_ = lean_uint32_dec_le(v___x_538_, v_c_515_);
if (v___x_539_ == 0)
{
v___y_535_ = v___x_539_;
goto v___jp_534_;
}
else
{
uint32_t v___x_540_; uint8_t v___x_541_; 
v___x_540_ = 122;
v___x_541_ = lean_uint32_dec_le(v_c_515_, v___x_540_);
v___y_535_ = v___x_541_;
goto v___jp_534_;
}
}
else
{
v___y_532_ = v_decide_511_;
goto v___jp_531_;
}
}
}
else
{
lean_object* v___x_546_; 
v___x_546_ = lean_box(0);
lean_inc(v_snd_500_);
v_pos_502_ = v_a_498_;
v_snd_503_ = v_snd_500_;
v_err_504_ = v___x_546_;
goto v___jp_501_;
}
v___jp_501_:
{
uint8_t v_decide_505_; 
v_decide_505_ = lean_nat_dec_eq(v_snd_500_, v_snd_503_);
lean_dec(v_snd_503_);
lean_dec(v_snd_500_);
if (v_decide_505_ == 0)
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(uint8_t v_decide_547_, uint32_t v___x_548_, uint32_t v___x_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_fst_557_; lean_object* v_snd_558_; lean_object* v___x_559_; uint8_t v_decide_560_; 
v_fst_557_ = lean_ctor_get(v___y_550_, 0);
v_snd_558_ = lean_ctor_get(v___y_550_, 1);
v___x_559_ = lean_string_utf8_byte_size(v_fst_557_);
v_decide_560_ = lean_nat_dec_eq(v_snd_558_, v___x_559_);
if (v_decide_560_ == 0)
{
if (v_decide_547_ == 0)
{
goto v___jp_554_;
}
else
{
uint32_t v_c_561_; lean_object* v___x_562_; lean_object* v_it_x27_563_; uint8_t v___y_565_; uint8_t v___y_566_; uint8_t v___y_571_; uint8_t v___y_572_; uint8_t v___y_573_; uint8_t v___y_575_; uint8_t v___y_576_; uint8_t v___y_579_; uint8_t v___y_582_; uint8_t v___y_584_; uint32_t v___x_589_; uint8_t v___x_590_; 
v_c_561_ = lean_string_utf8_get_fast(v_fst_557_, v_snd_558_);
v___x_562_ = lean_string_utf8_next_fast(v_fst_557_, v_snd_558_);
lean_inc(v_fst_557_);
v_it_x27_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_563_, 0, v_fst_557_);
lean_ctor_set(v_it_x27_563_, 1, v___x_562_);
v___x_589_ = 65;
v___x_590_ = lean_uint32_dec_le(v___x_589_, v_c_561_);
if (v___x_590_ == 0)
{
v___y_584_ = v___x_590_;
goto v___jp_583_;
}
else
{
uint32_t v___x_591_; uint8_t v___x_592_; 
v___x_591_ = 90;
v___x_592_ = lean_uint32_dec_le(v_c_561_, v___x_591_);
v___y_584_ = v___x_592_;
goto v___jp_583_;
}
v___jp_564_:
{
if (v___y_565_ == 0)
{
lean_dec_ref_known(v_it_x27_563_, 2);
goto v___jp_551_;
}
else
{
if (v___y_566_ == 0)
{
lean_dec_ref_known(v_it_x27_563_, 2);
goto v___jp_551_;
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec_ref(v___y_550_);
v___x_567_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_568_ = lean_string_push(v___x_567_, v_c_561_);
v___x_569_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__3(v___x_568_, v_it_x27_563_);
return v___x_569_;
}
}
}
v___jp_570_:
{
if (v___y_571_ == 0)
{
v___y_565_ = v___y_572_;
v___y_566_ = v___y_571_;
goto v___jp_564_;
}
else
{
v___y_565_ = v___y_572_;
v___y_566_ = v___y_573_;
goto v___jp_564_;
}
}
v___jp_574_:
{
uint8_t v___x_577_; 
v___x_577_ = lean_uint32_dec_eq(v_c_561_, v___x_548_);
if (v___x_577_ == 0)
{
v___y_571_ = v___y_576_;
v___y_572_ = v___y_575_;
v___y_573_ = v_decide_547_;
goto v___jp_570_;
}
else
{
v___y_571_ = v___y_576_;
v___y_572_ = v___y_575_;
v___y_573_ = v_decide_560_;
goto v___jp_570_;
}
}
v___jp_578_:
{
uint8_t v___x_580_; 
v___x_580_ = lean_uint32_dec_eq(v_c_561_, v___x_549_);
if (v___x_580_ == 0)
{
v___y_575_ = v___y_579_;
v___y_576_ = v_decide_547_;
goto v___jp_574_;
}
else
{
v___y_575_ = v___y_579_;
v___y_576_ = v_decide_560_;
goto v___jp_574_;
}
}
v___jp_581_:
{
if (v___y_582_ == 0)
{
v___y_579_ = v_decide_547_;
goto v___jp_578_;
}
else
{
v___y_579_ = v_decide_560_;
goto v___jp_578_;
}
}
v___jp_583_:
{
if (v___y_584_ == 0)
{
uint32_t v___x_585_; uint8_t v___x_586_; 
v___x_585_ = 97;
v___x_586_ = lean_uint32_dec_le(v___x_585_, v_c_561_);
if (v___x_586_ == 0)
{
v___y_582_ = v___x_586_;
goto v___jp_581_;
}
else
{
uint32_t v___x_587_; uint8_t v___x_588_; 
v___x_587_ = 122;
v___x_588_ = lean_uint32_dec_le(v_c_561_, v___x_587_);
v___y_582_ = v___x_588_;
goto v___jp_581_;
}
}
else
{
v___y_579_ = v_decide_560_;
goto v___jp_578_;
}
}
}
}
else
{
goto v___jp_554_;
}
v___jp_551_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_553_, 0, v___y_550_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
return v___x_553_;
}
v___jp_554_:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_box(0);
v___x_556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_556_, 0, v___y_550_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2___boxed(lean_object* v_decide_593_, lean_object* v___x_594_, lean_object* v___x_595_, lean_object* v___y_596_){
_start:
{
uint8_t v_decide_11803__boxed_597_; uint32_t v___x_11804__boxed_598_; uint32_t v___x_11805__boxed_599_; lean_object* v_res_600_; 
v_decide_11803__boxed_597_ = lean_unbox(v_decide_593_);
v___x_11804__boxed_598_ = lean_unbox_uint32(v___x_594_);
lean_dec(v___x_594_);
v___x_11805__boxed_599_ = lean_unbox_uint32(v___x_595_);
lean_dec(v___x_595_);
v_res_600_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(v_decide_11803__boxed_597_, v___x_11804__boxed_598_, v___x_11805__boxed_599_, v___y_596_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(uint32_t v___y_601_){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_603_ = lean_string_push(v___x_602_, v___y_601_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3___boxed(lean_object* v___y_605_){
_start:
{
uint32_t v___y_11893__boxed_606_; lean_object* v_res_607_; 
v___y_11893__boxed_606_ = lean_unbox_uint32(v___y_605_);
lean_dec(v___y_605_);
v_res_607_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(v___y_11893__boxed_606_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4(uint8_t v___x_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_fst_613_; lean_object* v_snd_614_; lean_object* v___x_615_; uint8_t v_decide_616_; 
v_fst_613_ = lean_ctor_get(v___y_609_, 0);
v_snd_614_ = lean_ctor_get(v___y_609_, 1);
v___x_615_ = lean_string_utf8_byte_size(v_fst_613_);
v_decide_616_ = lean_nat_dec_eq(v_snd_614_, v___x_615_);
if (v_decide_616_ == 0)
{
if (v___x_608_ == 0)
{
goto v___jp_610_;
}
else
{
lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_627_; 
lean_inc(v_snd_614_);
lean_inc(v_fst_613_);
v_isSharedCheck_627_ = !lean_is_exclusive(v___y_609_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; lean_object* v_unused_629_; 
v_unused_628_ = lean_ctor_get(v___y_609_, 1);
lean_dec(v_unused_628_);
v_unused_629_ = lean_ctor_get(v___y_609_, 0);
lean_dec(v_unused_629_);
v___x_618_ = v___y_609_;
v_isShared_619_ = v_isSharedCheck_627_;
goto v_resetjp_617_;
}
else
{
lean_dec(v___y_609_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_627_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
uint32_t v_c_620_; lean_object* v___x_621_; lean_object* v_it_x27_623_; 
v_c_620_ = lean_string_utf8_get_fast(v_fst_613_, v_snd_614_);
v___x_621_ = lean_string_utf8_next_fast(v_fst_613_, v_snd_614_);
lean_dec(v_snd_614_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 1, v___x_621_);
v_it_x27_623_ = v___x_618_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_fst_613_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v___x_621_);
v_it_x27_623_ = v_reuseFailAlloc_626_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_box_uint32(v_c_620_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v_it_x27_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
return v___x_625_;
}
}
}
}
else
{
goto v___jp_610_;
}
v___jp_610_:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_box(0);
v___x_612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_612_, 0, v___y_609_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4___boxed(lean_object* v___x_630_, lean_object* v___y_631_){
_start:
{
uint8_t v___x_11902__boxed_632_; lean_object* v_res_633_; 
v___x_11902__boxed_632_ = lean_unbox(v___x_630_);
v_res_633_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4(v___x_11902__boxed_632_, v___y_631_);
return v_res_633_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0(void){
_start:
{
uint32_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = 92;
v___x_635_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_636_ = lean_string_push(v___x_635_, v___x_634_);
return v___x_636_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0);
v___x_638_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_639_ = lean_string_append(v___x_638_, v___x_637_);
return v___x_639_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_641_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1);
v___x_642_ = lean_string_append(v___x_641_, v___x_640_);
return v___x_642_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__3(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2);
v___x_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1(void){
_start:
{
uint32_t v___x_646_; lean_object* v___x_647_; 
v___x_646_ = 34;
v___x_647_ = lean_box_uint32(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2(void){
_start:
{
uint32_t v___x_648_; lean_object* v___x_649_; 
v___x_648_ = 39;
v___x_649_ = lean_box_uint32(v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart(lean_object* v_a_650_){
_start:
{
lean_object* v___x_651_; 
lean_inc_ref(v_a_650_);
v___x_651_ = l_Std_Time_parseModifier(v_a_650_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_pos_652_; lean_object* v_res_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_661_; 
lean_dec_ref(v_a_650_);
v_pos_652_ = lean_ctor_get(v___x_651_, 0);
v_res_653_ = lean_ctor_get(v___x_651_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_661_ == 0)
{
v___x_655_ = v___x_651_;
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_res_653_);
lean_inc(v_pos_652_);
lean_dec(v___x_651_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_657_, 0, v_res_653_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 1, v___x_657_);
v___x_659_ = v___x_655_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_pos_652_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
else
{
lean_object* v_pos_662_; lean_object* v_err_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_734_; 
v_pos_662_ = lean_ctor_get(v___x_651_, 0);
v_err_663_ = lean_ctor_get(v___x_651_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_734_ == 0)
{
v___x_665_ = v___x_651_;
v_isShared_666_ = v_isSharedCheck_734_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_err_663_);
lean_inc(v_pos_662_);
lean_dec(v___x_651_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_734_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v_snd_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_732_; 
v_snd_667_ = lean_ctor_get(v_a_650_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v_a_650_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v_a_650_, 0);
lean_dec(v_unused_733_);
v___x_669_ = v_a_650_;
v_isShared_670_ = v_isSharedCheck_732_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_snd_667_);
lean_dec(v_a_650_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_732_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v_fst_671_; lean_object* v_snd_672_; uint8_t v_decide_673_; 
v_fst_671_ = lean_ctor_get(v_pos_662_, 0);
v_snd_672_ = lean_ctor_get(v_pos_662_, 1);
v_decide_673_ = lean_nat_dec_eq(v_snd_667_, v_snd_672_);
lean_dec(v_snd_667_);
if (v_decide_673_ == 0)
{
lean_object* v___x_675_; 
lean_del_object(v___x_669_);
if (v_isShared_666_ == 0)
{
v___x_675_ = v___x_665_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_pos_662_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_err_663_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
else
{
lean_object* v___f_677_; lean_object* v___y_679_; lean_object* v_pos_680_; lean_object* v_snd_681_; lean_object* v___x_707_; uint8_t v_decide_708_; 
lean_inc(v_snd_672_);
lean_dec(v_err_663_);
v___f_677_ = ((lean_object*)(l_Std_Time_instCoeStringFormatPart___closed__0));
v___x_707_ = lean_string_utf8_byte_size(v_fst_671_);
v_decide_708_ = lean_nat_dec_eq(v_snd_672_, v___x_707_);
if (v_decide_708_ == 0)
{
if (v_decide_673_ == 0)
{
lean_del_object(v___x_669_);
goto v___jp_702_;
}
else
{
uint32_t v___x_709_; uint32_t v_c_710_; uint8_t v___x_711_; 
lean_del_object(v___x_665_);
v___x_709_ = 92;
v_c_710_ = lean_string_utf8_get_fast(v_fst_671_, v_snd_672_);
v___x_711_ = lean_uint32_dec_eq(v_c_710_, v___x_709_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__3);
lean_inc(v_pos_662_);
if (v_isShared_670_ == 0)
{
lean_ctor_set_tag(v___x_669_, 1);
lean_ctor_set(v___x_669_, 1, v___x_712_);
lean_ctor_set(v___x_669_, 0, v_pos_662_);
v___x_714_ = v___x_669_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_pos_662_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_inc(v_snd_672_);
v___y_679_ = v___x_714_;
v_pos_680_ = v_pos_662_;
v_snd_681_ = v_snd_672_;
goto v___jp_678_;
}
}
else
{
lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_729_; 
lean_inc(v_fst_671_);
lean_del_object(v___x_669_);
v_isSharedCheck_729_ = !lean_is_exclusive(v_pos_662_);
if (v_isSharedCheck_729_ == 0)
{
lean_object* v_unused_730_; lean_object* v_unused_731_; 
v_unused_730_ = lean_ctor_get(v_pos_662_, 1);
lean_dec(v_unused_730_);
v_unused_731_ = lean_ctor_get(v_pos_662_, 0);
lean_dec(v_unused_731_);
v___x_717_ = v_pos_662_;
v_isShared_718_ = v_isSharedCheck_729_;
goto v_resetjp_716_;
}
else
{
lean_dec(v_pos_662_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_729_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___f_719_; lean_object* v___x_720_; lean_object* v___f_721_; lean_object* v___x_722_; lean_object* v_it_x27_724_; 
v___f_719_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__4));
v___x_720_ = lean_box(v___x_711_);
v___f_721_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4___boxed), 2, 1);
lean_closure_set(v___f_721_, 0, v___x_720_);
v___x_722_ = lean_string_utf8_next_fast(v_fst_671_, v_snd_672_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 1, v___x_722_);
v_it_x27_724_ = v___x_717_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_fst_671_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v___x_722_);
v_it_x27_724_ = v_reuseFailAlloc_728_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_725_; 
v___x_725_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_721_, v___f_719_, v_it_x27_724_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_dec(v_snd_672_);
return v___x_725_;
}
else
{
lean_object* v_pos_726_; lean_object* v_snd_727_; 
v_pos_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_pos_726_);
v_snd_727_ = lean_ctor_get(v_pos_726_, 1);
lean_inc(v_snd_727_);
v___y_679_ = v___x_725_;
v_pos_680_ = v_pos_726_;
v_snd_681_ = v_snd_727_;
goto v___jp_678_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_669_);
goto v___jp_702_;
}
v___jp_678_:
{
uint8_t v_decide_682_; 
v_decide_682_ = lean_nat_dec_eq(v_snd_672_, v_snd_681_);
lean_dec(v_snd_672_);
if (v_decide_682_ == 0)
{
lean_dec(v_snd_681_);
lean_dec_ref(v_pos_680_);
return v___y_679_;
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___f_685_; lean_object* v___x_686_; 
lean_dec_ref(v___y_679_);
v___x_683_ = lean_box(v_decide_682_);
v___x_684_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1;
v___f_685_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___boxed), 3, 2);
lean_closure_set(v___f_685_, 0, v___x_683_);
lean_closure_set(v___f_685_, 1, v___x_684_);
v___x_686_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_685_, v___f_677_, v_pos_680_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_dec(v_snd_681_);
return v___x_686_;
}
else
{
lean_object* v_pos_687_; lean_object* v_snd_688_; uint8_t v_decide_689_; 
v_pos_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_pos_687_);
v_snd_688_ = lean_ctor_get(v_pos_687_, 1);
lean_inc(v_snd_688_);
v_decide_689_ = lean_nat_dec_eq(v_snd_681_, v_snd_688_);
lean_dec(v_snd_681_);
if (v_decide_689_ == 0)
{
lean_dec(v_snd_688_);
lean_dec(v_pos_687_);
return v___x_686_;
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___f_692_; lean_object* v___x_693_; 
lean_dec_ref_known(v___x_686_, 2);
v___x_690_ = lean_box(v_decide_689_);
v___x_691_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2;
v___f_692_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___boxed), 3, 2);
lean_closure_set(v___f_692_, 0, v___x_690_);
lean_closure_set(v___f_692_, 1, v___x_691_);
v___x_693_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_692_, v___f_677_, v_pos_687_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_dec(v_snd_688_);
return v___x_693_;
}
else
{
lean_object* v_pos_694_; lean_object* v_snd_695_; uint8_t v_decide_696_; 
v_pos_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_pos_694_);
v_snd_695_ = lean_ctor_get(v_pos_694_, 1);
v_decide_696_ = lean_nat_dec_eq(v_snd_688_, v_snd_695_);
lean_dec(v_snd_688_);
if (v_decide_696_ == 0)
{
lean_dec(v_pos_694_);
return v___x_693_;
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___f_700_; lean_object* v___x_701_; 
lean_dec_ref_known(v___x_693_, 2);
v___x_697_ = lean_box(v_decide_696_);
v___x_698_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1;
v___x_699_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2;
v___f_700_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2___boxed), 4, 3);
lean_closure_set(v___f_700_, 0, v___x_697_);
lean_closure_set(v___f_700_, 1, v___x_698_);
lean_closure_set(v___f_700_, 2, v___x_699_);
v___x_701_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_700_, v___f_677_, v_pos_694_);
return v___x_701_;
}
}
}
}
}
}
v___jp_702_:
{
lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_703_ = lean_box(0);
lean_inc(v_pos_662_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___x_703_);
v___x_705_ = v___x_665_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_pos_662_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_inc(v_snd_672_);
v___y_679_ = v___x_705_;
v_pos_680_ = v_pos_662_;
v_snd_681_ = v_snd_672_;
goto v___jp_678_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_specParser_spec__0(lean_object* v_acc_735_, lean_object* v_a_736_){
_start:
{
lean_object* v___x_737_; 
lean_inc_ref(v_a_736_);
v___x_737_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart(v_a_736_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_pos_738_; lean_object* v_res_739_; lean_object* v___x_740_; 
lean_dec_ref(v_a_736_);
v_pos_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_pos_738_);
v_res_739_ = lean_ctor_get(v___x_737_, 1);
lean_inc(v_res_739_);
lean_dec_ref_known(v___x_737_, 2);
v___x_740_ = lean_array_push(v_acc_735_, v_res_739_);
v_acc_735_ = v___x_740_;
v_a_736_ = v_pos_738_;
goto _start;
}
else
{
lean_object* v_pos_742_; lean_object* v_err_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_756_; 
v_pos_742_ = lean_ctor_get(v___x_737_, 0);
v_err_743_ = lean_ctor_get(v___x_737_, 1);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_756_ == 0)
{
v___x_745_ = v___x_737_;
v_isShared_746_ = v_isSharedCheck_756_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_err_743_);
lean_inc(v_pos_742_);
lean_dec(v___x_737_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_756_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v_snd_747_; lean_object* v_snd_748_; uint8_t v_decide_749_; 
v_snd_747_ = lean_ctor_get(v_a_736_, 1);
lean_inc(v_snd_747_);
lean_dec_ref(v_a_736_);
v_snd_748_ = lean_ctor_get(v_pos_742_, 1);
v_decide_749_ = lean_nat_dec_eq(v_snd_747_, v_snd_748_);
lean_dec(v_snd_747_);
if (v_decide_749_ == 0)
{
lean_object* v___x_751_; 
lean_dec_ref(v_acc_735_);
if (v_isShared_746_ == 0)
{
v___x_751_ = v___x_745_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_pos_742_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_err_743_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
else
{
lean_object* v___x_754_; 
lean_dec(v_err_743_);
if (v_isShared_746_ == 0)
{
lean_ctor_set_tag(v___x_745_, 0);
lean_ctor_set(v___x_745_, 1, v_acc_735_);
v___x_754_ = v___x_745_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_pos_742_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_acc_735_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParser(lean_object* v_a_762_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__0));
v___x_764_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_specParser_spec__0(v___x_763_, v_a_762_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_pos_765_; lean_object* v_res_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_782_; 
v_pos_765_ = lean_ctor_get(v___x_764_, 0);
v_res_766_ = lean_ctor_get(v___x_764_, 1);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_782_ == 0)
{
v___x_768_ = v___x_764_;
v_isShared_769_ = v_isSharedCheck_782_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_res_766_);
lean_inc(v_pos_765_);
lean_dec(v___x_764_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_782_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v_fst_770_; lean_object* v_snd_771_; lean_object* v___x_772_; uint8_t v_decide_773_; 
v_fst_770_ = lean_ctor_get(v_pos_765_, 0);
v_snd_771_ = lean_ctor_get(v_pos_765_, 1);
v___x_772_ = lean_string_utf8_byte_size(v_fst_770_);
v_decide_773_ = lean_nat_dec_eq(v_snd_771_, v___x_772_);
if (v_decide_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_776_; 
lean_dec(v_res_766_);
v___x_774_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_769_ == 0)
{
lean_ctor_set_tag(v___x_768_, 1);
lean_ctor_set(v___x_768_, 1, v___x_774_);
v___x_776_ = v___x_768_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_pos_765_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
else
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lean_array_to_list(v_res_766_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v___x_778_);
v___x_780_ = v___x_768_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_pos_765_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_778_);
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
else
{
lean_object* v_pos_783_; lean_object* v_err_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
v_pos_783_ = lean_ctor_get(v___x_764_, 0);
v_err_784_ = lean_ctor_get(v___x_764_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_764_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_err_784_);
lean_inc(v_pos_783_);
lean_dec(v___x_764_);
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParse(lean_object* v_s_792_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_794_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_793_, v_s_792_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(uint32_t v_a_795_, lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
lean_object* v_zero_798_; uint8_t v_isZero_799_; 
v_zero_798_ = lean_unsigned_to_nat(0u);
v_isZero_799_ = lean_nat_dec_eq(v_x_796_, v_zero_798_);
if (v_isZero_799_ == 1)
{
lean_dec(v_x_796_);
return v_x_797_;
}
else
{
lean_object* v_one_800_; lean_object* v_n_801_; lean_object* v___x_802_; 
v_one_800_ = lean_unsigned_to_nat(1u);
v_n_801_ = lean_nat_sub(v_x_796_, v_one_800_);
lean_dec(v_x_796_);
v___x_802_ = lean_string_push(v_x_797_, v_a_795_);
v_x_796_ = v_n_801_;
v_x_797_ = v___x_802_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1___boxed(lean_object* v_a_804_, lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
uint32_t v_a_boxed_807_; lean_object* v_res_808_; 
v_a_boxed_807_ = lean_unbox_uint32(v_a_804_);
lean_dec(v_a_804_);
v_res_808_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_boxed_807_, v_x_805_, v_x_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(lean_object* v___x_809_, lean_object* v_s_810_, lean_object* v_a_811_, lean_object* v_b_812_){
_start:
{
uint8_t v_decide_813_; 
v_decide_813_ = lean_nat_dec_eq(v_a_811_, v___x_809_);
if (v_decide_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_814_ = lean_string_utf8_next_fast(v_s_810_, v_a_811_);
lean_dec(v_a_811_);
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = lean_nat_add(v_b_812_, v___x_815_);
lean_dec(v_b_812_);
v_a_811_ = v___x_814_;
v_b_812_ = v___x_816_;
goto _start;
}
else
{
lean_dec(v_a_811_);
return v_b_812_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg___boxed(lean_object* v___x_818_, lean_object* v_s_819_, lean_object* v_a_820_, lean_object* v_b_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_818_, v_s_819_, v_a_820_, v_b_821_);
lean_dec_ref(v_s_819_);
lean_dec(v___x_818_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(lean_object* v_n_823_, uint32_t v_a_824_, lean_object* v_s_825_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_826_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = lean_string_utf8_byte_size(v_s_825_);
v___x_829_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_828_, v_s_825_, v___x_827_, v___x_827_);
v___x_830_ = lean_nat_sub(v_n_823_, v___x_829_);
lean_dec(v___x_829_);
v___x_831_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_824_, v___x_830_, v___x_826_);
v___x_832_ = lean_string_append(v___x_831_, v_s_825_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii___boxed(lean_object* v_n_833_, lean_object* v_a_834_, lean_object* v_s_835_){
_start:
{
uint32_t v_a_boxed_836_; lean_object* v_res_837_; 
v_a_boxed_836_ = lean_unbox_uint32(v_a_834_);
lean_dec(v_a_834_);
v_res_837_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v_n_833_, v_a_boxed_836_, v_s_835_);
lean_dec_ref(v_s_835_);
lean_dec(v_n_833_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0(lean_object* v___x_838_, lean_object* v___x_839_, lean_object* v_s_840_, lean_object* v_inst_841_, lean_object* v_R_842_, lean_object* v_a_843_, lean_object* v_b_844_, lean_object* v_c_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_838_, v_s_840_, v_a_843_, v_b_844_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___boxed(lean_object* v___x_847_, lean_object* v___x_848_, lean_object* v_s_849_, lean_object* v_inst_850_, lean_object* v_R_851_, lean_object* v_a_852_, lean_object* v_b_853_, lean_object* v_c_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0(v___x_847_, v___x_848_, v_s_849_, v_inst_850_, v_R_851_, v_a_852_, v_b_853_, v_c_854_);
lean_dec_ref(v_s_849_);
lean_dec_ref(v___x_848_);
lean_dec(v___x_847_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(lean_object* v_n_856_, uint32_t v_a_857_, lean_object* v_s_858_){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_859_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_860_ = lean_unsigned_to_nat(0u);
v___x_861_ = lean_string_utf8_byte_size(v_s_858_);
v___x_862_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_861_, v_s_858_, v___x_860_, v___x_860_);
v___x_863_ = lean_nat_sub(v_n_856_, v___x_862_);
lean_dec(v___x_862_);
v___x_864_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_857_, v___x_863_, v___x_859_);
v___x_865_ = lean_string_append(v_s_858_, v___x_864_);
lean_dec_ref(v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii___boxed(lean_object* v_n_866_, lean_object* v_a_867_, lean_object* v_s_868_){
_start:
{
uint32_t v_a_boxed_869_; lean_object* v_res_870_; 
v_a_boxed_869_ = lean_unbox_uint32(v_a_867_);
lean_dec(v_a_867_);
v_res_870_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_n_866_, v_a_boxed_869_, v_s_868_);
lean_dec(v_n_866_);
return v_res_870_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = lean_nat_to_int(v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad(lean_object* v_size_874_, lean_object* v_n_875_, uint8_t v_cut_876_){
_start:
{
lean_object* v_fst_878_; lean_object* v_snd_879_; lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_893_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_894_ = lean_int_dec_lt(v_n_875_, v___x_893_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; 
v___x_895_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v_fst_878_ = v___x_895_;
v_snd_879_ = v_n_875_;
goto v___jp_877_;
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_897_ = lean_int_neg(v_n_875_);
lean_dec(v_n_875_);
v_fst_878_ = v___x_896_;
v_snd_879_ = v___x_897_;
goto v___jp_877_;
}
v___jp_877_:
{
lean_object* v_numStr_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v_numStr_880_ = l_Int_repr(v_snd_879_);
lean_dec(v_snd_879_);
v___x_881_ = lean_string_utf8_byte_size(v_numStr_880_);
v___x_882_ = lean_nat_dec_lt(v_size_874_, v___x_881_);
if (v___x_882_ == 0)
{
uint32_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_883_ = 48;
v___x_884_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v_size_874_, v___x_883_, v_numStr_880_);
lean_dec_ref(v_numStr_880_);
lean_inc_ref(v_fst_878_);
v___x_885_ = lean_string_append(v_fst_878_, v___x_884_);
lean_dec_ref(v___x_884_);
return v___x_885_;
}
else
{
if (v_cut_876_ == 0)
{
lean_object* v___x_886_; 
lean_inc_ref(v_fst_878_);
v___x_886_ = lean_string_append(v_fst_878_, v_numStr_880_);
lean_dec_ref(v_numStr_880_);
return v___x_886_;
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_887_ = lean_nat_sub(v___x_881_, v_size_874_);
v___x_888_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_numStr_880_);
v___x_889_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_889_, 0, v_numStr_880_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
lean_ctor_set(v___x_889_, 2, v___x_881_);
v___x_890_ = l_String_Slice_Pos_nextn(v___x_889_, v___x_888_, v___x_887_);
lean_dec_ref_known(v___x_889_, 3);
v___x_891_ = lean_string_utf8_extract_fast(v_numStr_880_, v___x_890_, v___x_881_);
lean_dec(v___x_890_);
lean_dec_ref(v_numStr_880_);
lean_inc_ref(v_fst_878_);
v___x_892_ = lean_string_append(v_fst_878_, v___x_891_);
lean_dec_ref(v___x_891_);
return v___x_892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad___boxed(lean_object* v_size_898_, lean_object* v_n_899_, lean_object* v_cut_900_){
_start:
{
uint8_t v_cut_boxed_901_; lean_object* v_res_902_; 
v_cut_boxed_901_ = lean_unbox(v_cut_900_);
v_res_902_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_size_898_, v_n_899_, v_cut_boxed_901_);
lean_dec(v_size_898_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate(lean_object* v_size_903_, lean_object* v_n_904_, uint8_t v_cut_905_){
_start:
{
lean_object* v_fst_907_; lean_object* v_snd_908_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_922_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_923_ = lean_int_dec_lt(v_n_904_, v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; 
v___x_924_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v_fst_907_ = v___x_924_;
v_snd_908_ = v_n_904_;
goto v___jp_906_;
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_926_ = lean_int_neg(v_n_904_);
lean_dec(v_n_904_);
v_fst_907_ = v___x_925_;
v_snd_908_ = v___x_926_;
goto v___jp_906_;
}
v___jp_906_:
{
lean_object* v_numStr_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v_numStr_909_ = l_Int_repr(v_snd_908_);
lean_dec(v_snd_908_);
v___x_910_ = lean_string_length(v_numStr_909_);
v___x_911_ = lean_nat_dec_lt(v_size_903_, v___x_910_);
if (v___x_911_ == 0)
{
uint32_t v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_912_ = 48;
v___x_913_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_size_903_, v___x_912_, v_numStr_909_);
lean_dec(v_size_903_);
lean_inc_ref(v_fst_907_);
v___x_914_ = lean_string_append(v_fst_907_, v___x_913_);
lean_dec_ref(v___x_913_);
return v___x_914_;
}
else
{
if (v_cut_905_ == 0)
{
lean_object* v___x_915_; 
lean_dec(v_size_903_);
lean_inc_ref(v_fst_907_);
v___x_915_ = lean_string_append(v_fst_907_, v_numStr_909_);
lean_dec_ref(v_numStr_909_);
return v___x_915_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_916_ = lean_unsigned_to_nat(0u);
v___x_917_ = lean_string_utf8_byte_size(v_numStr_909_);
lean_inc_ref(v_numStr_909_);
v___x_918_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_918_, 0, v_numStr_909_);
lean_ctor_set(v___x_918_, 1, v___x_916_);
lean_ctor_set(v___x_918_, 2, v___x_917_);
v___x_919_ = l_String_Slice_Pos_nextn(v___x_918_, v___x_916_, v_size_903_);
lean_dec_ref_known(v___x_918_, 3);
v___x_920_ = lean_string_utf8_extract_fast(v_numStr_909_, v___x_916_, v___x_919_);
lean_dec(v___x_919_);
lean_dec_ref(v_numStr_909_);
lean_inc_ref(v_fst_907_);
v___x_921_ = lean_string_append(v_fst_907_, v___x_920_);
lean_dec_ref(v___x_920_);
return v___x_921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate___boxed(lean_object* v_size_927_, lean_object* v_n_928_, lean_object* v_cut_929_){
_start:
{
uint8_t v_cut_boxed_930_; lean_object* v_res_931_; 
v_cut_boxed_930_ = lean_unbox(v_cut_929_);
v_res_931_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate(v_size_927_, v_n_928_, v_cut_boxed_930_);
return v_res_931_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__0(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_932_ = lean_unsigned_to_nat(2u);
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_nat_mod(v___x_933_, v___x_932_);
return v___x_934_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__1(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_935_ = lean_unsigned_to_nat(2u);
v___x_936_ = lean_unsigned_to_nat(1u);
v___x_937_ = lean_nat_mod(v___x_936_, v___x_935_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(uint8_t v_x_938_){
_start:
{
if (v_x_938_ == 0)
{
lean_object* v___x_939_; 
v___x_939_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__0);
return v___x_939_;
}
else
{
lean_object* v___x_940_; 
v___x_940_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___closed__1);
return v___x_940_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___boxed(lean_object* v_x_941_){
_start:
{
uint8_t v_x_52__boxed_942_; lean_object* v_res_943_; 
v_x_52__boxed_942_ = lean_unbox(v_x_941_);
v_res_943_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_x_52__boxed_942_);
return v_res_943_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_945_ = lean_int_neg(v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(lean_object* v_symbols_946_, lean_object* v_month_947_){
_start:
{
lean_object* v_monthLong_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v_monthLong_948_ = lean_ctor_get(v_symbols_946_, 0);
v___x_949_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_950_ = lean_int_add(v_month_947_, v___x_949_);
v___x_951_ = l_Int_toNat(v___x_950_);
lean_dec(v___x_950_);
v___x_952_ = lean_array_fget_borrowed(v_monthLong_948_, v___x_951_);
lean_dec(v___x_951_);
lean_inc(v___x_952_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___boxed(lean_object* v_symbols_953_, lean_object* v_month_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_953_, v_month_954_);
lean_dec(v_month_954_);
lean_dec_ref(v_symbols_953_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(lean_object* v_symbols_956_, lean_object* v_month_957_){
_start:
{
lean_object* v_monthShort_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_monthShort_958_ = lean_ctor_get(v_symbols_956_, 1);
v___x_959_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_960_ = lean_int_add(v_month_957_, v___x_959_);
v___x_961_ = l_Int_toNat(v___x_960_);
lean_dec(v___x_960_);
v___x_962_ = lean_array_fget_borrowed(v_monthShort_958_, v___x_961_);
lean_dec(v___x_961_);
lean_inc(v___x_962_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort___boxed(lean_object* v_symbols_963_, lean_object* v_month_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_963_, v_month_964_);
lean_dec(v_month_964_);
lean_dec_ref(v_symbols_963_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(lean_object* v_symbols_966_, lean_object* v_month_967_){
_start:
{
lean_object* v_monthNarrow_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_monthNarrow_968_ = lean_ctor_get(v_symbols_966_, 2);
v___x_969_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_970_ = lean_int_add(v_month_967_, v___x_969_);
v___x_971_ = l_Int_toNat(v___x_970_);
lean_dec(v___x_970_);
v___x_972_ = lean_array_fget_borrowed(v_monthNarrow_968_, v___x_971_);
lean_dec(v___x_971_);
lean_inc(v___x_972_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow___boxed(lean_object* v_symbols_973_, lean_object* v_month_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_973_, v_month_974_);
lean_dec(v_month_974_);
lean_dec_ref(v_symbols_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(lean_object* v_symbols_976_, uint8_t v_wd_977_){
_start:
{
lean_object* v_weekdayLong_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_weekdayLong_978_ = lean_ctor_get(v_symbols_976_, 3);
v___x_979_ = l_Std_Time_Weekday_toOrdinal(v_wd_977_);
v___x_980_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_981_ = lean_int_add(v___x_979_, v___x_980_);
lean_dec(v___x_979_);
v___x_982_ = l_Int_toNat(v___x_981_);
lean_dec(v___x_981_);
v___x_983_ = lean_array_fget_borrowed(v_weekdayLong_978_, v___x_982_);
lean_dec(v___x_982_);
lean_inc(v___x_983_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong___boxed(lean_object* v_symbols_984_, lean_object* v_wd_985_){
_start:
{
uint8_t v_wd_boxed_986_; lean_object* v_res_987_; 
v_wd_boxed_986_ = lean_unbox(v_wd_985_);
v_res_987_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_984_, v_wd_boxed_986_);
lean_dec_ref(v_symbols_984_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(lean_object* v_symbols_988_, uint8_t v_wd_989_){
_start:
{
lean_object* v_weekdayShort_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_weekdayShort_990_ = lean_ctor_get(v_symbols_988_, 4);
v___x_991_ = l_Std_Time_Weekday_toOrdinal(v_wd_989_);
v___x_992_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_993_ = lean_int_add(v___x_991_, v___x_992_);
lean_dec(v___x_991_);
v___x_994_ = l_Int_toNat(v___x_993_);
lean_dec(v___x_993_);
v___x_995_ = lean_array_fget_borrowed(v_weekdayShort_990_, v___x_994_);
lean_dec(v___x_994_);
lean_inc(v___x_995_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort___boxed(lean_object* v_symbols_996_, lean_object* v_wd_997_){
_start:
{
uint8_t v_wd_boxed_998_; lean_object* v_res_999_; 
v_wd_boxed_998_ = lean_unbox(v_wd_997_);
v_res_999_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_996_, v_wd_boxed_998_);
lean_dec_ref(v_symbols_996_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(lean_object* v_symbols_1000_, uint8_t v_wd_1001_){
_start:
{
lean_object* v_weekdayNarrow_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_weekdayNarrow_1002_ = lean_ctor_get(v_symbols_1000_, 5);
v___x_1003_ = l_Std_Time_Weekday_toOrdinal(v_wd_1001_);
v___x_1004_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1005_ = lean_int_add(v___x_1003_, v___x_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = l_Int_toNat(v___x_1005_);
lean_dec(v___x_1005_);
v___x_1007_ = lean_array_fget_borrowed(v_weekdayNarrow_1002_, v___x_1006_);
lean_dec(v___x_1006_);
lean_inc(v___x_1007_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow___boxed(lean_object* v_symbols_1008_, lean_object* v_wd_1009_){
_start:
{
uint8_t v_wd_boxed_1010_; lean_object* v_res_1011_; 
v_wd_boxed_1010_ = lean_unbox(v_wd_1009_);
v_res_1011_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1008_, v_wd_boxed_1010_);
lean_dec_ref(v_symbols_1008_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(lean_object* v_symbols_1012_, uint8_t v_wd_1013_){
_start:
{
lean_object* v_weekdayTwoLetter_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v_weekdayTwoLetter_1014_ = lean_ctor_get(v_symbols_1012_, 6);
v___x_1015_ = l_Std_Time_Weekday_toOrdinal(v_wd_1013_);
v___x_1016_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1017_ = lean_int_add(v___x_1015_, v___x_1016_);
lean_dec(v___x_1015_);
v___x_1018_ = l_Int_toNat(v___x_1017_);
lean_dec(v___x_1017_);
v___x_1019_ = lean_array_fget_borrowed(v_weekdayTwoLetter_1014_, v___x_1018_);
lean_dec(v___x_1018_);
lean_inc(v___x_1019_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter___boxed(lean_object* v_symbols_1020_, lean_object* v_wd_1021_){
_start:
{
uint8_t v_wd_boxed_1022_; lean_object* v_res_1023_; 
v_wd_boxed_1022_ = lean_unbox(v_wd_1021_);
v_res_1023_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1020_, v_wd_boxed_1022_);
lean_dec_ref(v_symbols_1020_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(lean_object* v_symbols_1024_, uint8_t v_era_1025_){
_start:
{
lean_object* v_eraShort_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_eraShort_1026_ = lean_ctor_get(v_symbols_1024_, 7);
v___x_1027_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_1025_);
v___x_1028_ = lean_array_fget_borrowed(v_eraShort_1026_, v___x_1027_);
lean_dec(v___x_1027_);
lean_inc(v___x_1028_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort___boxed(lean_object* v_symbols_1029_, lean_object* v_era_1030_){
_start:
{
uint8_t v_era_boxed_1031_; lean_object* v_res_1032_; 
v_era_boxed_1031_ = lean_unbox(v_era_1030_);
v_res_1032_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(v_symbols_1029_, v_era_boxed_1031_);
lean_dec_ref(v_symbols_1029_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(lean_object* v_symbols_1033_, uint8_t v_era_1034_){
_start:
{
lean_object* v_eraLong_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_eraLong_1035_ = lean_ctor_get(v_symbols_1033_, 8);
v___x_1036_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_1034_);
v___x_1037_ = lean_array_fget_borrowed(v_eraLong_1035_, v___x_1036_);
lean_dec(v___x_1036_);
lean_inc(v___x_1037_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong___boxed(lean_object* v_symbols_1038_, lean_object* v_era_1039_){
_start:
{
uint8_t v_era_boxed_1040_; lean_object* v_res_1041_; 
v_era_boxed_1040_ = lean_unbox(v_era_1039_);
v_res_1041_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(v_symbols_1038_, v_era_boxed_1040_);
lean_dec_ref(v_symbols_1038_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(lean_object* v_symbols_1042_, uint8_t v_era_1043_){
_start:
{
lean_object* v_eraNarrow_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v_eraNarrow_1044_ = lean_ctor_get(v_symbols_1042_, 9);
v___x_1045_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_1043_);
v___x_1046_ = lean_array_fget_borrowed(v_eraNarrow_1044_, v___x_1045_);
lean_dec(v___x_1045_);
lean_inc(v___x_1046_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow___boxed(lean_object* v_symbols_1047_, lean_object* v_era_1048_){
_start:
{
uint8_t v_era_boxed_1049_; lean_object* v_res_1050_; 
v_era_boxed_1049_ = lean_unbox(v_era_1048_);
v_res_1050_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(v_symbols_1047_, v_era_boxed_1049_);
lean_dec_ref(v_symbols_1047_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(lean_object* v_x_1055_){
_start:
{
lean_object* v_natZero_1056_; lean_object* v_intZero_1057_; uint8_t v_isNeg_1058_; lean_object* v_a_1059_; uint8_t v_isZero_1060_; lean_object* v_one_1061_; lean_object* v_n_1062_; uint8_t v_isZero_1063_; 
v_natZero_1056_ = lean_unsigned_to_nat(0u);
v_intZero_1057_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v_isNeg_1058_ = lean_int_dec_lt(v_x_1055_, v_intZero_1057_);
v_a_1059_ = lean_nat_abs(v_x_1055_);
v_isZero_1060_ = lean_nat_dec_eq(v_a_1059_, v_natZero_1056_);
v_one_1061_ = lean_unsigned_to_nat(1u);
v_n_1062_ = lean_nat_sub(v_a_1059_, v_one_1061_);
lean_dec(v_a_1059_);
v_isZero_1063_ = lean_nat_dec_eq(v_n_1062_, v_natZero_1056_);
if (v_isZero_1063_ == 1)
{
lean_object* v___x_1064_; 
lean_dec(v_n_1062_);
v___x_1064_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__0));
return v___x_1064_;
}
else
{
lean_object* v_n_1065_; uint8_t v_isZero_1066_; 
v_n_1065_ = lean_nat_sub(v_n_1062_, v_one_1061_);
lean_dec(v_n_1062_);
v_isZero_1066_ = lean_nat_dec_eq(v_n_1065_, v_natZero_1056_);
if (v_isZero_1066_ == 1)
{
lean_object* v___x_1067_; 
lean_dec(v_n_1065_);
v___x_1067_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__1));
return v___x_1067_;
}
else
{
lean_object* v_n_1068_; uint8_t v_isZero_1069_; 
v_n_1068_ = lean_nat_sub(v_n_1065_, v_one_1061_);
lean_dec(v_n_1065_);
v_isZero_1069_ = lean_nat_dec_eq(v_n_1068_, v_natZero_1056_);
if (v_isZero_1069_ == 1)
{
lean_object* v___x_1070_; 
lean_dec(v_n_1068_);
v___x_1070_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__2));
return v___x_1070_;
}
else
{
lean_object* v_n_1071_; uint8_t v_isZero_1072_; lean_object* v___x_1073_; 
v_n_1071_ = lean_nat_sub(v_n_1068_, v_one_1061_);
lean_dec(v_n_1068_);
v_isZero_1072_ = lean_nat_dec_eq(v_n_1071_, v_natZero_1056_);
lean_dec(v_n_1071_);
v___x_1073_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__3));
return v___x_1073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___boxed(lean_object* v_x_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_x_1074_);
lean_dec(v_x_1074_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(lean_object* v_symbols_1076_, lean_object* v_q_1077_){
_start:
{
lean_object* v_quarterShort_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v_quarterShort_1078_ = lean_ctor_get(v_symbols_1076_, 10);
v___x_1079_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1080_ = lean_int_add(v_q_1077_, v___x_1079_);
v___x_1081_ = l_Int_toNat(v___x_1080_);
lean_dec(v___x_1080_);
v___x_1082_ = lean_array_fget_borrowed(v_quarterShort_1078_, v___x_1081_);
lean_dec(v___x_1081_);
lean_inc(v___x_1082_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort___boxed(lean_object* v_symbols_1083_, lean_object* v_q_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1083_, v_q_1084_);
lean_dec(v_q_1084_);
lean_dec_ref(v_symbols_1083_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(lean_object* v_symbols_1086_, lean_object* v_q_1087_){
_start:
{
lean_object* v_quarterLong_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v_quarterLong_1088_ = lean_ctor_get(v_symbols_1086_, 11);
v___x_1089_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1090_ = lean_int_add(v_q_1087_, v___x_1089_);
v___x_1091_ = l_Int_toNat(v___x_1090_);
lean_dec(v___x_1090_);
v___x_1092_ = lean_array_fget_borrowed(v_quarterLong_1088_, v___x_1091_);
lean_dec(v___x_1091_);
lean_inc(v___x_1092_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong___boxed(lean_object* v_symbols_1093_, lean_object* v_q_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1093_, v_q_1094_);
lean_dec(v_q_1094_);
lean_dec_ref(v_symbols_1093_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(lean_object* v_symbols_1096_, lean_object* v_q_1097_){
_start:
{
lean_object* v_quarterNarrow_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_quarterNarrow_1098_ = lean_ctor_get(v_symbols_1096_, 12);
v___x_1099_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1100_ = lean_int_add(v_q_1097_, v___x_1099_);
v___x_1101_ = l_Int_toNat(v___x_1100_);
lean_dec(v___x_1100_);
v___x_1102_ = lean_array_fget_borrowed(v_quarterNarrow_1098_, v___x_1101_);
lean_dec(v___x_1101_);
lean_inc(v___x_1102_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow___boxed(lean_object* v_symbols_1103_, lean_object* v_q_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1103_, v_q_1104_);
lean_dec(v_q_1104_);
lean_dec_ref(v_symbols_1103_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(lean_object* v_symbols_1106_, uint8_t v_marker_1107_){
_start:
{
if (v_marker_1107_ == 0)
{
lean_object* v_amShort_1108_; 
v_amShort_1108_ = lean_ctor_get(v_symbols_1106_, 13);
lean_inc_ref(v_amShort_1108_);
return v_amShort_1108_;
}
else
{
lean_object* v_pmShort_1109_; 
v_pmShort_1109_ = lean_ctor_get(v_symbols_1106_, 14);
lean_inc_ref(v_pmShort_1109_);
return v_pmShort_1109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort___boxed(lean_object* v_symbols_1110_, lean_object* v_marker_1111_){
_start:
{
uint8_t v_marker_boxed_1112_; lean_object* v_res_1113_; 
v_marker_boxed_1112_ = lean_unbox(v_marker_1111_);
v_res_1113_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(v_symbols_1110_, v_marker_boxed_1112_);
lean_dec_ref(v_symbols_1110_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong(lean_object* v_symbols_1114_, uint8_t v_marker_1115_){
_start:
{
if (v_marker_1115_ == 0)
{
lean_object* v_amLong_1116_; 
v_amLong_1116_ = lean_ctor_get(v_symbols_1114_, 15);
lean_inc_ref(v_amLong_1116_);
return v_amLong_1116_;
}
else
{
lean_object* v_pmLong_1117_; 
v_pmLong_1117_ = lean_ctor_get(v_symbols_1114_, 16);
lean_inc_ref(v_pmLong_1117_);
return v_pmLong_1117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong___boxed(lean_object* v_symbols_1118_, lean_object* v_marker_1119_){
_start:
{
uint8_t v_marker_boxed_1120_; lean_object* v_res_1121_; 
v_marker_boxed_1120_ = lean_unbox(v_marker_1119_);
v_res_1121_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong(v_symbols_1118_, v_marker_boxed_1120_);
lean_dec_ref(v_symbols_1118_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(lean_object* v_symbols_1122_, uint8_t v_marker_1123_){
_start:
{
if (v_marker_1123_ == 0)
{
lean_object* v_amNarrow_1124_; 
v_amNarrow_1124_ = lean_ctor_get(v_symbols_1122_, 17);
lean_inc_ref(v_amNarrow_1124_);
return v_amNarrow_1124_;
}
else
{
lean_object* v_pmNarrow_1125_; 
v_pmNarrow_1125_ = lean_ctor_get(v_symbols_1122_, 18);
lean_inc_ref(v_pmNarrow_1125_);
return v_pmNarrow_1125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow___boxed(lean_object* v_symbols_1126_, lean_object* v_marker_1127_){
_start:
{
uint8_t v_marker_boxed_1128_; lean_object* v_res_1129_; 
v_marker_boxed_1128_ = lean_unbox(v_marker_1127_);
v_res_1129_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(v_symbols_1126_, v_marker_boxed_1128_);
lean_dec_ref(v_symbols_1126_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(lean_object* v_dp_1130_, uint8_t v_period_1131_){
_start:
{
switch(v_period_1131_)
{
case 0:
{
lean_object* v_am_1132_; 
v_am_1132_ = lean_ctor_get(v_dp_1130_, 0);
lean_inc_ref(v_am_1132_);
return v_am_1132_;
}
case 1:
{
lean_object* v_pm_1133_; 
v_pm_1133_ = lean_ctor_get(v_dp_1130_, 1);
lean_inc_ref(v_pm_1133_);
return v_pm_1133_;
}
case 2:
{
lean_object* v_noon_1134_; 
v_noon_1134_ = lean_ctor_get(v_dp_1130_, 2);
lean_inc_ref(v_noon_1134_);
return v_noon_1134_;
}
default: 
{
lean_object* v_midnight_1135_; 
v_midnight_1135_ = lean_ctor_get(v_dp_1130_, 3);
lean_inc_ref(v_midnight_1135_);
return v_midnight_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod___boxed(lean_object* v_dp_1136_, lean_object* v_period_1137_){
_start:
{
uint8_t v_period_boxed_1138_; lean_object* v_res_1139_; 
v_period_boxed_1138_ = lean_unbox(v_period_1137_);
v_res_1139_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dp_1136_, v_period_boxed_1138_);
lean_dec_ref(v_dp_1136_);
return v_res_1139_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = lean_unsigned_to_nat(6u);
v___x_1141_ = lean_unsigned_to_nat(0u);
v___x_1142_ = lean_nat_mod(v___x_1141_, v___x_1140_);
return v___x_1142_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = lean_unsigned_to_nat(6u);
v___x_1144_ = lean_unsigned_to_nat(1u);
v___x_1145_ = lean_nat_mod(v___x_1144_, v___x_1143_);
return v___x_1145_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = lean_unsigned_to_nat(6u);
v___x_1147_ = lean_unsigned_to_nat(2u);
v___x_1148_ = lean_nat_mod(v___x_1147_, v___x_1146_);
return v___x_1148_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = lean_unsigned_to_nat(6u);
v___x_1150_ = lean_unsigned_to_nat(3u);
v___x_1151_ = lean_nat_mod(v___x_1150_, v___x_1149_);
return v___x_1151_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = lean_unsigned_to_nat(6u);
v___x_1153_ = lean_unsigned_to_nat(4u);
v___x_1154_ = lean_nat_mod(v___x_1153_, v___x_1152_);
return v___x_1154_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = lean_unsigned_to_nat(6u);
v___x_1156_ = lean_unsigned_to_nat(5u);
v___x_1157_ = lean_nat_mod(v___x_1156_, v___x_1155_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(uint8_t v_x_1158_){
_start:
{
switch(v_x_1158_)
{
case 0:
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0);
return v___x_1159_;
}
case 1:
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1);
return v___x_1160_;
}
case 2:
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2);
return v___x_1161_;
}
case 3:
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3);
return v___x_1162_;
}
case 4:
{
lean_object* v___x_1163_; 
v___x_1163_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4);
return v___x_1163_;
}
default: 
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5);
return v___x_1164_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___boxed(lean_object* v_x_1165_){
_start:
{
uint8_t v_x_148__boxed_1166_; lean_object* v_res_1167_; 
v_x_148__boxed_1166_ = lean_unbox(v_x_1165_);
v_res_1167_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(v_x_148__boxed_1166_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(lean_object* v_arr_1168_, uint8_t v_period_1169_){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(v_period_1169_);
v___x_1171_ = lean_array_fget_borrowed(v_arr_1168_, v___x_1170_);
lean_dec(v___x_1170_);
lean_inc(v___x_1171_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod___boxed(lean_object* v_arr_1172_, lean_object* v_period_1173_){
_start:
{
uint8_t v_period_boxed_1174_; lean_object* v_res_1175_; 
v_period_boxed_1174_ = lean_unbox(v_period_1173_);
v_res_1175_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_arr_1172_, v_period_boxed_1174_);
lean_dec_ref(v_arr_1172_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned(lean_object* v_data_1177_){
_start:
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1179_ = lean_int_dec_lt(v_data_1177_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1180_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_1181_ = l_Int_repr(v_data_1177_);
v___x_1182_ = lean_string_append(v___x_1180_, v___x_1181_);
lean_dec_ref(v___x_1181_);
return v___x_1182_;
}
else
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Int_repr(v_data_1177_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___boxed(lean_object* v_data_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l___private_Std_Time_Format_Basic_0__Std_Time_toSigned(v_data_1184_);
lean_dec(v_data_1184_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(uint8_t v_x_1186_){
_start:
{
switch(v_x_1186_)
{
case 0:
{
lean_object* v___x_1187_; 
v___x_1187_ = lean_unsigned_to_nat(0u);
return v___x_1187_;
}
case 1:
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_unsigned_to_nat(1u);
return v___x_1188_;
}
default: 
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_unsigned_to_nat(2u);
return v___x_1189_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___boxed(lean_object* v_x_1190_){
_start:
{
uint8_t v_x_boxed_1191_; lean_object* v_res_1192_; 
v_x_boxed_1191_ = lean_unbox(v_x_1190_);
v_res_1192_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(v_x_boxed_1191_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg(lean_object* v_k_1193_){
_start:
{
lean_inc(v_k_1193_);
return v_k_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg___boxed(lean_object* v_k_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg(v_k_1194_);
lean_dec(v_k_1194_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(lean_object* v_motive_1196_, lean_object* v_ctorIdx_1197_, uint8_t v_t_1198_, lean_object* v_h_1199_, lean_object* v_k_1200_){
_start:
{
lean_inc(v_k_1200_);
return v_k_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___boxed(lean_object* v_motive_1201_, lean_object* v_ctorIdx_1202_, lean_object* v_t_1203_, lean_object* v_h_1204_, lean_object* v_k_1205_){
_start:
{
uint8_t v_t_boxed_1206_; lean_object* v_res_1207_; 
v_t_boxed_1206_ = lean_unbox(v_t_1203_);
v_res_1207_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(v_motive_1201_, v_ctorIdx_1202_, v_t_boxed_1206_, v_h_1204_, v_k_1205_);
lean_dec(v_k_1205_);
lean_dec(v_ctorIdx_1202_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg(lean_object* v_yes_1208_){
_start:
{
lean_inc(v_yes_1208_);
return v_yes_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg___boxed(lean_object* v_yes_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg(v_yes_1209_);
lean_dec(v_yes_1209_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(lean_object* v_motive_1211_, uint8_t v_t_1212_, lean_object* v_h_1213_, lean_object* v_yes_1214_){
_start:
{
lean_inc(v_yes_1214_);
return v_yes_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___boxed(lean_object* v_motive_1215_, lean_object* v_t_1216_, lean_object* v_h_1217_, lean_object* v_yes_1218_){
_start:
{
uint8_t v_t_boxed_1219_; lean_object* v_res_1220_; 
v_t_boxed_1219_ = lean_unbox(v_t_1216_);
v_res_1220_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(v_motive_1215_, v_t_boxed_1219_, v_h_1217_, v_yes_1218_);
lean_dec(v_yes_1218_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg(lean_object* v_no_1221_){
_start:
{
lean_inc(v_no_1221_);
return v_no_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg___boxed(lean_object* v_no_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg(v_no_1222_);
lean_dec(v_no_1222_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim(lean_object* v_motive_1224_, uint8_t v_t_1225_, lean_object* v_h_1226_, lean_object* v_no_1227_){
_start:
{
lean_inc(v_no_1227_);
return v_no_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___boxed(lean_object* v_motive_1228_, lean_object* v_t_1229_, lean_object* v_h_1230_, lean_object* v_no_1231_){
_start:
{
uint8_t v_t_boxed_1232_; lean_object* v_res_1233_; 
v_t_boxed_1232_ = lean_unbox(v_t_1229_);
v_res_1233_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim(v_motive_1228_, v_t_boxed_1232_, v_h_1230_, v_no_1231_);
lean_dec(v_no_1231_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg(lean_object* v_optional_1234_){
_start:
{
lean_inc(v_optional_1234_);
return v_optional_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg___boxed(lean_object* v_optional_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg(v_optional_1235_);
lean_dec(v_optional_1235_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(lean_object* v_motive_1237_, uint8_t v_t_1238_, lean_object* v_h_1239_, lean_object* v_optional_1240_){
_start:
{
lean_inc(v_optional_1240_);
return v_optional_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___boxed(lean_object* v_motive_1241_, lean_object* v_t_1242_, lean_object* v_h_1243_, lean_object* v_optional_1244_){
_start:
{
uint8_t v_t_boxed_1245_; lean_object* v_res_1246_; 
v_t_boxed_1245_ = lean_unbox(v_t_1242_);
v_res_1246_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(v_motive_1241_, v_t_boxed_1245_, v_h_1243_, v_optional_1244_);
lean_dec(v_optional_1244_);
return v_res_1246_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(uint8_t v_x_1247_, uint8_t v_y_1248_){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1249_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(v_x_1247_);
v___x_1250_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx(v_y_1248_);
v___x_1251_ = lean_nat_dec_eq(v___x_1249_, v___x_1250_);
lean_dec(v___x_1250_);
lean_dec(v___x_1249_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq___boxed(lean_object* v_x_1252_, lean_object* v_y_1253_){
_start:
{
uint8_t v_x_21__boxed_1254_; uint8_t v_y_22__boxed_1255_; uint8_t v_res_1256_; lean_object* v_r_1257_; 
v_x_21__boxed_1254_ = lean_unbox(v_x_1252_);
v_y_22__boxed_1255_ = lean_unbox(v_y_1253_);
v_res_1256_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_x_21__boxed_1254_, v_y_22__boxed_1255_);
v_r_1257_ = lean_box(v_res_1256_);
return v_r_1257_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__1(lean_object* v_a_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Rat_ofInt(v_a_1260_);
return v___x_1261_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_unsigned_to_nat(1000000000u);
v___x_1264_ = lean_nat_to_int(v___x_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(lean_object* v_offset_1265_, uint8_t v_withMinutes_1266_, uint8_t v_withSeconds_1267_, uint8_t v_colon_1268_, uint8_t v_padHour_1269_){
_start:
{
lean_object* v___y_1271_; uint32_t v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1281_; uint32_t v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1288_; uint8_t v___y_1289_; uint32_t v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; uint8_t v___y_1293_; uint8_t v___y_1295_; lean_object* v___y_1296_; uint8_t v___y_1297_; uint32_t v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; uint8_t v___y_1301_; uint8_t v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; uint32_t v___y_1306_; lean_object* v___y_1307_; uint8_t v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1316_; uint8_t v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; uint32_t v___y_1321_; lean_object* v___y_1322_; uint8_t v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1330_; uint8_t v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; uint32_t v___y_1335_; lean_object* v___y_1336_; uint8_t v___y_1337_; lean_object* v___y_1341_; uint8_t v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; uint8_t v___y_1346_; uint32_t v___y_1347_; lean_object* v___y_1348_; uint8_t v___y_1349_; uint8_t v___y_1350_; lean_object* v___y_1352_; uint8_t v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; uint8_t v___y_1356_; lean_object* v___y_1357_; uint8_t v___y_1358_; uint32_t v___y_1359_; lean_object* v___y_1360_; uint8_t v___y_1361_; uint8_t v___y_1362_; lean_object* v___y_1364_; lean_object* v___y_1365_; uint32_t v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v_fst_1381_; lean_object* v_snd_1382_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1393_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1394_ = lean_int_dec_le(v___x_1393_, v_offset_1265_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1396_ = lean_int_neg(v_offset_1265_);
lean_dec(v_offset_1265_);
v_fst_1381_ = v___x_1395_;
v_snd_1382_ = v___x_1396_;
goto v___jp_1380_;
}
else
{
lean_object* v___x_1397_; 
v___x_1397_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v_fst_1381_ = v___x_1397_;
v_snd_1382_ = v_offset_1265_;
goto v___jp_1380_;
}
v___jp_1270_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1276_ = lean_string_append(v___y_1274_, v___y_1275_);
v___x_1277_ = l_Int_repr(v___y_1271_);
lean_dec(v___y_1271_);
v___x_1278_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___y_1273_, v___y_1272_, v___x_1277_);
lean_dec_ref(v___x_1277_);
v___x_1279_ = lean_string_append(v___x_1276_, v___x_1278_);
lean_dec_ref(v___x_1278_);
return v___x_1279_;
}
v___jp_1280_:
{
if (v_colon_1268_ == 0)
{
lean_object* v___x_1285_; 
v___x_1285_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___y_1271_ = v___y_1281_;
v___y_1272_ = v___y_1282_;
v___y_1273_ = v___y_1283_;
v___y_1274_ = v___y_1284_;
v___y_1275_ = v___x_1285_;
goto v___jp_1270_;
}
else
{
lean_object* v___x_1286_; 
v___x_1286_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___y_1271_ = v___y_1281_;
v___y_1272_ = v___y_1282_;
v___y_1273_ = v___y_1283_;
v___y_1274_ = v___y_1284_;
v___y_1275_ = v___x_1286_;
goto v___jp_1270_;
}
}
v___jp_1287_:
{
if (v___y_1289_ == 0)
{
if (v___y_1293_ == 0)
{
lean_dec(v___y_1288_);
return v___y_1292_;
}
else
{
v___y_1281_ = v___y_1288_;
v___y_1282_ = v___y_1290_;
v___y_1283_ = v___y_1291_;
v___y_1284_ = v___y_1292_;
goto v___jp_1280_;
}
}
else
{
v___y_1281_ = v___y_1288_;
v___y_1282_ = v___y_1290_;
v___y_1283_ = v___y_1291_;
v___y_1284_ = v___y_1292_;
goto v___jp_1280_;
}
}
v___jp_1294_:
{
if (v___y_1295_ == 0)
{
v___y_1288_ = v___y_1296_;
v___y_1289_ = v___y_1297_;
v___y_1290_ = v___y_1298_;
v___y_1291_ = v___y_1299_;
v___y_1292_ = v___y_1300_;
v___y_1293_ = v___y_1295_;
goto v___jp_1287_;
}
else
{
v___y_1288_ = v___y_1296_;
v___y_1289_ = v___y_1297_;
v___y_1290_ = v___y_1298_;
v___y_1291_ = v___y_1299_;
v___y_1292_ = v___y_1300_;
v___y_1293_ = v___y_1301_;
goto v___jp_1287_;
}
}
v___jp_1302_:
{
uint8_t v___x_1310_; uint8_t v___x_1311_; uint8_t v___x_1312_; 
v___x_1310_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withSeconds_1267_, v___y_1308_);
v___x_1311_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withSeconds_1267_, v___y_1303_);
v___x_1312_ = lean_int_dec_eq(v___y_1305_, v___y_1304_);
if (v___x_1312_ == 0)
{
uint8_t v___x_1313_; 
v___x_1313_ = 1;
v___y_1295_ = v___x_1311_;
v___y_1296_ = v___y_1305_;
v___y_1297_ = v___x_1310_;
v___y_1298_ = v___y_1306_;
v___y_1299_ = v___y_1307_;
v___y_1300_ = v___y_1309_;
v___y_1301_ = v___x_1313_;
goto v___jp_1294_;
}
else
{
uint8_t v___x_1314_; 
v___x_1314_ = 0;
v___y_1295_ = v___x_1311_;
v___y_1296_ = v___y_1305_;
v___y_1297_ = v___x_1310_;
v___y_1298_ = v___y_1306_;
v___y_1299_ = v___y_1307_;
v___y_1300_ = v___y_1309_;
v___y_1301_ = v___x_1314_;
goto v___jp_1294_;
}
}
v___jp_1315_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1325_ = lean_string_append(v___y_1318_, v___y_1324_);
v___x_1326_ = l_Int_repr(v___y_1316_);
lean_dec(v___y_1316_);
v___x_1327_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___y_1322_, v___y_1321_, v___x_1326_);
lean_dec_ref(v___x_1326_);
v___x_1328_ = lean_string_append(v___x_1325_, v___x_1327_);
lean_dec_ref(v___x_1327_);
v___y_1303_ = v___y_1317_;
v___y_1304_ = v___y_1319_;
v___y_1305_ = v___y_1320_;
v___y_1306_ = v___y_1321_;
v___y_1307_ = v___y_1322_;
v___y_1308_ = v___y_1323_;
v___y_1309_ = v___x_1328_;
goto v___jp_1302_;
}
v___jp_1329_:
{
if (v_colon_1268_ == 0)
{
lean_object* v___x_1338_; 
v___x_1338_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___y_1316_ = v___y_1330_;
v___y_1317_ = v___y_1331_;
v___y_1318_ = v___y_1332_;
v___y_1319_ = v___y_1333_;
v___y_1320_ = v___y_1334_;
v___y_1321_ = v___y_1335_;
v___y_1322_ = v___y_1336_;
v___y_1323_ = v___y_1337_;
v___y_1324_ = v___x_1338_;
goto v___jp_1315_;
}
else
{
lean_object* v___x_1339_; 
v___x_1339_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___y_1316_ = v___y_1330_;
v___y_1317_ = v___y_1331_;
v___y_1318_ = v___y_1332_;
v___y_1319_ = v___y_1333_;
v___y_1320_ = v___y_1334_;
v___y_1321_ = v___y_1335_;
v___y_1322_ = v___y_1336_;
v___y_1323_ = v___y_1337_;
v___y_1324_ = v___x_1339_;
goto v___jp_1315_;
}
}
v___jp_1340_:
{
if (v___y_1346_ == 0)
{
if (v___y_1350_ == 0)
{
lean_dec(v___y_1341_);
v___y_1303_ = v___y_1342_;
v___y_1304_ = v___y_1344_;
v___y_1305_ = v___y_1345_;
v___y_1306_ = v___y_1347_;
v___y_1307_ = v___y_1348_;
v___y_1308_ = v___y_1349_;
v___y_1309_ = v___y_1343_;
goto v___jp_1302_;
}
else
{
v___y_1330_ = v___y_1341_;
v___y_1331_ = v___y_1342_;
v___y_1332_ = v___y_1343_;
v___y_1333_ = v___y_1344_;
v___y_1334_ = v___y_1345_;
v___y_1335_ = v___y_1347_;
v___y_1336_ = v___y_1348_;
v___y_1337_ = v___y_1349_;
goto v___jp_1329_;
}
}
else
{
v___y_1330_ = v___y_1341_;
v___y_1331_ = v___y_1342_;
v___y_1332_ = v___y_1343_;
v___y_1333_ = v___y_1344_;
v___y_1334_ = v___y_1345_;
v___y_1335_ = v___y_1347_;
v___y_1336_ = v___y_1348_;
v___y_1337_ = v___y_1349_;
goto v___jp_1329_;
}
}
v___jp_1351_:
{
if (v___y_1356_ == 0)
{
v___y_1341_ = v___y_1352_;
v___y_1342_ = v___y_1353_;
v___y_1343_ = v___y_1354_;
v___y_1344_ = v___y_1355_;
v___y_1345_ = v___y_1357_;
v___y_1346_ = v___y_1358_;
v___y_1347_ = v___y_1359_;
v___y_1348_ = v___y_1360_;
v___y_1349_ = v___y_1361_;
v___y_1350_ = v___y_1356_;
goto v___jp_1340_;
}
else
{
v___y_1341_ = v___y_1352_;
v___y_1342_ = v___y_1353_;
v___y_1343_ = v___y_1354_;
v___y_1344_ = v___y_1355_;
v___y_1345_ = v___y_1357_;
v___y_1346_ = v___y_1358_;
v___y_1347_ = v___y_1359_;
v___y_1348_ = v___y_1360_;
v___y_1349_ = v___y_1361_;
v___y_1350_ = v___y_1362_;
goto v___jp_1340_;
}
}
v___jp_1363_:
{
lean_object* v_minute_1369_; lean_object* v_second_1370_; uint8_t v___x_1371_; uint8_t v___x_1372_; lean_object* v_data_1373_; uint8_t v___x_1374_; uint8_t v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v_minute_1369_ = lean_ctor_get(v___y_1364_, 1);
lean_inc(v_minute_1369_);
v_second_1370_ = lean_ctor_get(v___y_1364_, 2);
lean_inc(v_second_1370_);
lean_dec_ref(v___y_1364_);
v___x_1371_ = 0;
v___x_1372_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withMinutes_1266_, v___x_1371_);
lean_inc_ref(v___y_1365_);
v_data_1373_ = lean_string_append(v___y_1365_, v___y_1368_);
lean_dec_ref(v___y_1368_);
v___x_1374_ = 2;
v___x_1375_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withMinutes_1266_, v___x_1374_);
v___x_1376_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1377_ = lean_int_dec_eq(v_minute_1369_, v___x_1376_);
if (v___x_1377_ == 0)
{
uint8_t v___x_1378_; 
v___x_1378_ = 1;
v___y_1352_ = v_minute_1369_;
v___y_1353_ = v___x_1374_;
v___y_1354_ = v_data_1373_;
v___y_1355_ = v___x_1376_;
v___y_1356_ = v___x_1375_;
v___y_1357_ = v_second_1370_;
v___y_1358_ = v___x_1372_;
v___y_1359_ = v___y_1366_;
v___y_1360_ = v___y_1367_;
v___y_1361_ = v___x_1371_;
v___y_1362_ = v___x_1378_;
goto v___jp_1351_;
}
else
{
uint8_t v___x_1379_; 
v___x_1379_ = 0;
v___y_1352_ = v_minute_1369_;
v___y_1353_ = v___x_1374_;
v___y_1354_ = v_data_1373_;
v___y_1355_ = v___x_1376_;
v___y_1356_ = v___x_1375_;
v___y_1357_ = v_second_1370_;
v___y_1358_ = v___x_1372_;
v___y_1359_ = v___y_1366_;
v___y_1360_ = v___y_1367_;
v___y_1361_ = v___x_1371_;
v___y_1362_ = v___x_1379_;
goto v___jp_1351_;
}
}
v___jp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v_time_1385_; lean_object* v___x_1386_; uint32_t v___x_1387_; 
v___x_1383_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_1384_ = lean_int_mul(v_snd_1382_, v___x_1383_);
lean_dec(v_snd_1382_);
v_time_1385_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1384_);
lean_dec(v___x_1384_);
v___x_1386_ = lean_unsigned_to_nat(2u);
v___x_1387_ = 48;
if (v_padHour_1269_ == 0)
{
lean_object* v_hour_1388_; lean_object* v___x_1389_; 
v_hour_1388_ = lean_ctor_get(v_time_1385_, 0);
lean_inc(v_hour_1388_);
v___x_1389_ = l_Int_repr(v_hour_1388_);
lean_dec(v_hour_1388_);
v___y_1364_ = v_time_1385_;
v___y_1365_ = v_fst_1381_;
v___y_1366_ = v___x_1387_;
v___y_1367_ = v___x_1386_;
v___y_1368_ = v___x_1389_;
goto v___jp_1363_;
}
else
{
lean_object* v_hour_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v_hour_1390_ = lean_ctor_get(v_time_1385_, 0);
lean_inc(v_hour_1390_);
v___x_1391_ = l_Int_repr(v_hour_1390_);
lean_dec(v_hour_1390_);
v___x_1392_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1386_, v___x_1387_, v___x_1391_);
lean_dec_ref(v___x_1391_);
v___y_1364_ = v_time_1385_;
v___y_1365_ = v_fst_1381_;
v___y_1366_ = v___x_1387_;
v___y_1367_ = v___x_1386_;
v___y_1368_ = v___x_1392_;
goto v___jp_1363_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___boxed(lean_object* v_offset_1398_, lean_object* v_withMinutes_1399_, lean_object* v_withSeconds_1400_, lean_object* v_colon_1401_, lean_object* v_padHour_1402_){
_start:
{
uint8_t v_withMinutes_boxed_1403_; uint8_t v_withSeconds_boxed_1404_; uint8_t v_colon_boxed_1405_; uint8_t v_padHour_boxed_1406_; lean_object* v_res_1407_; 
v_withMinutes_boxed_1403_ = lean_unbox(v_withMinutes_1399_);
v_withSeconds_boxed_1404_ = lean_unbox(v_withSeconds_1400_);
v_colon_boxed_1405_ = lean_unbox(v_colon_1401_);
v_padHour_boxed_1406_ = lean_unbox(v_padHour_1402_);
v_res_1407_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1398_, v_withMinutes_boxed_1403_, v_withSeconds_boxed_1404_, v_colon_boxed_1405_, v_padHour_boxed_1406_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0_spec__0(lean_object* v_a_1408_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = lean_nat_to_int(v_a_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(lean_object* v_a_1410_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = lean_nat_to_int(v_a_1410_);
v___x_1412_ = l_Rat_ofInt(v___x_1411_);
return v___x_1412_;
}
}
static lean_object* _init_l_Std_Time_classifyDayPeriod___closed__0(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_unsigned_to_nat(12u);
v___x_1414_ = lean_nat_to_int(v___x_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_classifyDayPeriod(lean_object* v_hour_1415_, lean_object* v_minute_1416_, lean_object* v_second_1417_){
_start:
{
lean_object* v___y_1419_; uint8_t v___y_1420_; uint8_t v___y_1426_; uint8_t v___y_1427_; lean_object* v___x_1431_; uint8_t v___x_1432_; uint8_t v___y_1434_; uint8_t v___x_1435_; 
v___x_1431_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1432_ = lean_int_dec_eq(v_hour_1415_, v___x_1431_);
v___x_1435_ = lean_int_dec_eq(v_minute_1416_, v___x_1431_);
if (v___x_1435_ == 0)
{
v___y_1434_ = v___x_1435_;
goto v___jp_1433_;
}
else
{
uint8_t v___x_1436_; 
v___x_1436_ = lean_int_dec_eq(v_second_1417_, v___x_1431_);
v___y_1434_ = v___x_1436_;
goto v___jp_1433_;
}
v___jp_1418_:
{
if (v___y_1420_ == 0)
{
uint8_t v___x_1421_; 
v___x_1421_ = lean_int_dec_lt(v_hour_1415_, v___y_1419_);
if (v___x_1421_ == 0)
{
uint8_t v___x_1422_; 
v___x_1422_ = 1;
return v___x_1422_;
}
else
{
uint8_t v___x_1423_; 
v___x_1423_ = 0;
return v___x_1423_;
}
}
else
{
uint8_t v___x_1424_; 
v___x_1424_ = 2;
return v___x_1424_;
}
}
v___jp_1425_:
{
if (v___y_1427_ == 0)
{
lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1428_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1429_ = lean_int_dec_eq(v_hour_1415_, v___x_1428_);
if (v___x_1429_ == 0)
{
v___y_1419_ = v___x_1428_;
v___y_1420_ = v___x_1429_;
goto v___jp_1418_;
}
else
{
v___y_1419_ = v___x_1428_;
v___y_1420_ = v___y_1426_;
goto v___jp_1418_;
}
}
else
{
uint8_t v___x_1430_; 
v___x_1430_ = 3;
return v___x_1430_;
}
}
v___jp_1433_:
{
if (v___x_1432_ == 0)
{
v___y_1426_ = v___y_1434_;
v___y_1427_ = v___x_1432_;
goto v___jp_1425_;
}
else
{
v___y_1426_ = v___y_1434_;
v___y_1427_ = v___y_1434_;
goto v___jp_1425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyDayPeriod___boxed(lean_object* v_hour_1437_, lean_object* v_minute_1438_, lean_object* v_second_1439_){
_start:
{
uint8_t v_res_1440_; lean_object* v_r_1441_; 
v_res_1440_ = l_Std_Time_classifyDayPeriod(v_hour_1437_, v_minute_1438_, v_second_1439_);
lean_dec(v_second_1439_);
lean_dec(v_minute_1438_);
lean_dec(v_hour_1437_);
v_r_1441_ = lean_box(v_res_1440_);
return v_r_1441_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__0(void){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = lean_unsigned_to_nat(6u);
v___x_1443_ = lean_nat_to_int(v___x_1442_);
return v___x_1443_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__1(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = lean_unsigned_to_nat(18u);
v___x_1445_ = lean_nat_to_int(v___x_1444_);
return v___x_1445_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__2(void){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_unsigned_to_nat(21u);
v___x_1447_ = lean_nat_to_int(v___x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_classifyExtendedDayPeriod(lean_object* v_hour_1448_, lean_object* v_minute_1449_, lean_object* v_second_1450_){
_start:
{
lean_object* v___y_1452_; uint8_t v___y_1453_; uint8_t v___y_1468_; uint8_t v___y_1469_; lean_object* v___x_1473_; uint8_t v___x_1474_; uint8_t v___y_1476_; uint8_t v___x_1477_; 
v___x_1473_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1474_ = lean_int_dec_eq(v_hour_1448_, v___x_1473_);
v___x_1477_ = lean_int_dec_eq(v_minute_1449_, v___x_1473_);
if (v___x_1477_ == 0)
{
v___y_1476_ = v___x_1477_;
goto v___jp_1475_;
}
else
{
uint8_t v___x_1478_; 
v___x_1478_ = lean_int_dec_eq(v_second_1450_, v___x_1473_);
v___y_1476_ = v___x_1478_;
goto v___jp_1475_;
}
v___jp_1451_:
{
if (v___y_1453_ == 0)
{
lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1454_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__0, &l_Std_Time_classifyExtendedDayPeriod___closed__0_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__0);
v___x_1455_ = lean_int_dec_lt(v_hour_1448_, v___x_1454_);
if (v___x_1455_ == 0)
{
uint8_t v___x_1456_; 
v___x_1456_ = lean_int_dec_lt(v_hour_1448_, v___y_1452_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1457_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__1, &l_Std_Time_classifyExtendedDayPeriod___closed__1_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__1);
v___x_1458_ = lean_int_dec_lt(v_hour_1448_, v___x_1457_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1459_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__2, &l_Std_Time_classifyExtendedDayPeriod___closed__2_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__2);
v___x_1460_ = lean_int_dec_lt(v_hour_1448_, v___x_1459_);
if (v___x_1460_ == 0)
{
uint8_t v___x_1461_; 
v___x_1461_ = 1;
return v___x_1461_;
}
else
{
uint8_t v___x_1462_; 
v___x_1462_ = 5;
return v___x_1462_;
}
}
else
{
uint8_t v___x_1463_; 
v___x_1463_ = 4;
return v___x_1463_;
}
}
else
{
uint8_t v___x_1464_; 
v___x_1464_ = 2;
return v___x_1464_;
}
}
else
{
uint8_t v___x_1465_; 
v___x_1465_ = 1;
return v___x_1465_;
}
}
else
{
uint8_t v___x_1466_; 
v___x_1466_ = 3;
return v___x_1466_;
}
}
v___jp_1467_:
{
if (v___y_1469_ == 0)
{
lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1470_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1471_ = lean_int_dec_eq(v_hour_1448_, v___x_1470_);
if (v___x_1471_ == 0)
{
v___y_1452_ = v___x_1470_;
v___y_1453_ = v___x_1471_;
goto v___jp_1451_;
}
else
{
v___y_1452_ = v___x_1470_;
v___y_1453_ = v___y_1468_;
goto v___jp_1451_;
}
}
else
{
uint8_t v___x_1472_; 
v___x_1472_ = 0;
return v___x_1472_;
}
}
v___jp_1475_:
{
if (v___x_1474_ == 0)
{
v___y_1468_ = v___y_1476_;
v___y_1469_ = v___x_1474_;
goto v___jp_1467_;
}
else
{
v___y_1468_ = v___y_1476_;
v___y_1469_ = v___y_1476_;
goto v___jp_1467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyExtendedDayPeriod___boxed(lean_object* v_hour_1479_, lean_object* v_minute_1480_, lean_object* v_second_1481_){
_start:
{
uint8_t v_res_1482_; lean_object* v_r_1483_; 
v_res_1482_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1479_, v_minute_1480_, v_second_1481_);
lean_dec(v_second_1481_);
lean_dec(v_minute_1480_);
lean_dec(v_hour_1479_);
v_r_1483_ = lean_box(v_res_1482_);
return v_r_1483_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = lean_unsigned_to_nat(100u);
v___x_1485_ = lean_nat_to_int(v___x_1484_);
return v___x_1485_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = lean_unsigned_to_nat(7u);
v___x_1487_ = lean_nat_to_int(v___x_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(lean_object* v_dateformat_1491_, lean_object* v_modifier_1492_, lean_object* v_data_1493_){
_start:
{
switch(lean_obj_tag(v_modifier_1492_))
{
case 0:
{
uint8_t v_presentation_1494_; 
v_presentation_1494_ = lean_ctor_get_uint8(v_modifier_1492_, 0);
lean_dec_ref_known(v_modifier_1492_, 0);
switch(v_presentation_1494_)
{
case 1:
{
lean_object* v_symbols_1495_; uint8_t v___x_1496_; lean_object* v___x_1497_; 
v_symbols_1495_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1496_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1497_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(v_symbols_1495_, v___x_1496_);
return v___x_1497_;
}
case 2:
{
lean_object* v_symbols_1498_; uint8_t v___x_1499_; lean_object* v___x_1500_; 
v_symbols_1498_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1499_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1500_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(v_symbols_1498_, v___x_1499_);
return v___x_1500_;
}
default: 
{
lean_object* v_symbols_1501_; uint8_t v___x_1502_; lean_object* v___x_1503_; 
v_symbols_1501_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1502_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1503_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(v_symbols_1501_, v___x_1502_);
return v___x_1503_;
}
}
}
case 1:
{
lean_object* v_presentation_1504_; 
v_presentation_1504_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc(v_presentation_1504_);
lean_dec_ref_known(v_modifier_1492_, 1);
switch(lean_obj_tag(v_presentation_1504_))
{
case 0:
{
lean_object* v___x_1505_; uint8_t v___x_1506_; lean_object* v___x_1507_; 
v___x_1505_ = lean_unsigned_to_nat(0u);
v___x_1506_ = 0;
v___x_1507_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1505_, v_data_1493_, v___x_1506_);
return v___x_1507_;
}
case 1:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; lean_object* v___x_1512_; 
v___x_1508_ = lean_unsigned_to_nat(2u);
v___x_1509_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1510_ = lean_int_emod(v_data_1493_, v___x_1509_);
lean_dec(v_data_1493_);
v___x_1511_ = 0;
v___x_1512_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1508_, v___x_1510_, v___x_1511_);
return v___x_1512_;
}
case 2:
{
lean_object* v___x_1513_; uint8_t v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = lean_unsigned_to_nat(4u);
v___x_1514_ = 0;
v___x_1515_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1513_, v_data_1493_, v___x_1514_);
return v___x_1515_;
}
default: 
{
lean_object* v_num_1516_; uint8_t v___x_1517_; lean_object* v___x_1518_; 
v_num_1516_ = lean_ctor_get(v_presentation_1504_, 0);
lean_inc(v_num_1516_);
lean_dec_ref_known(v_presentation_1504_, 1);
v___x_1517_ = 0;
v___x_1518_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1516_, v_data_1493_, v___x_1517_);
lean_dec(v_num_1516_);
return v___x_1518_;
}
}
}
case 2:
{
lean_object* v_presentation_1519_; lean_object* v___x_1520_; lean_object* v___y_1522_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v_presentation_1519_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc(v_presentation_1519_);
lean_dec_ref_known(v_modifier_1492_, 1);
v___x_1520_ = lean_unsigned_to_nat(0u);
v___x_1536_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1537_ = lean_int_dec_le(v_data_1493_, v___x_1536_);
if (v___x_1537_ == 0)
{
v___y_1522_ = v_data_1493_;
goto v___jp_1521_;
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1538_ = lean_int_neg(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1539_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1540_ = lean_int_add(v___x_1538_, v___x_1539_);
lean_dec(v___x_1538_);
v___y_1522_ = v___x_1540_;
goto v___jp_1521_;
}
v___jp_1521_:
{
switch(lean_obj_tag(v_presentation_1519_))
{
case 0:
{
uint8_t v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = 0;
v___x_1524_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1520_, v___y_1522_, v___x_1523_);
return v___x_1524_;
}
case 1:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; 
v___x_1525_ = lean_unsigned_to_nat(2u);
v___x_1526_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1527_ = lean_int_emod(v___y_1522_, v___x_1526_);
lean_dec(v___y_1522_);
v___x_1528_ = 0;
v___x_1529_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1525_, v___x_1527_, v___x_1528_);
return v___x_1529_;
}
case 2:
{
lean_object* v___x_1530_; uint8_t v___x_1531_; lean_object* v___x_1532_; 
v___x_1530_ = lean_unsigned_to_nat(4u);
v___x_1531_ = 0;
v___x_1532_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1530_, v___y_1522_, v___x_1531_);
return v___x_1532_;
}
default: 
{
lean_object* v_num_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; 
v_num_1533_ = lean_ctor_get(v_presentation_1519_, 0);
lean_inc(v_num_1533_);
lean_dec_ref_known(v_presentation_1519_, 1);
v___x_1534_ = 0;
v___x_1535_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1533_, v___y_1522_, v___x_1534_);
lean_dec(v_num_1533_);
return v___x_1535_;
}
}
}
}
case 3:
{
lean_object* v_presentation_1541_; lean_object* v_snd_1542_; uint8_t v___x_1543_; lean_object* v___x_1544_; 
v_presentation_1541_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc(v_presentation_1541_);
lean_dec_ref_known(v_modifier_1492_, 1);
v_snd_1542_ = lean_ctor_get(v_data_1493_, 1);
lean_inc(v_snd_1542_);
lean_dec(v_data_1493_);
v___x_1543_ = 0;
v___x_1544_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1541_, v_snd_1542_, v___x_1543_);
lean_dec(v_presentation_1541_);
return v___x_1544_;
}
case 4:
{
lean_object* v_presentation_1545_; 
v_presentation_1545_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc_ref(v_presentation_1545_);
lean_dec_ref_known(v_modifier_1492_, 1);
if (lean_obj_tag(v_presentation_1545_) == 0)
{
lean_object* v_val_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; 
v_val_1546_ = lean_ctor_get(v_presentation_1545_, 0);
lean_inc(v_val_1546_);
lean_dec_ref_known(v_presentation_1545_, 1);
v___x_1547_ = 0;
v___x_1548_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1546_, v_data_1493_, v___x_1547_);
lean_dec(v_val_1546_);
return v___x_1548_;
}
else
{
lean_object* v_val_1549_; uint8_t v___x_1550_; 
v_val_1549_ = lean_ctor_get(v_presentation_1545_, 0);
lean_inc(v_val_1549_);
lean_dec_ref_known(v_presentation_1545_, 1);
v___x_1550_ = lean_unbox(v_val_1549_);
lean_dec(v_val_1549_);
switch(v___x_1550_)
{
case 1:
{
lean_object* v_symbols_1551_; lean_object* v___x_1552_; 
v_symbols_1551_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1552_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_1551_, v_data_1493_);
lean_dec(v_data_1493_);
return v___x_1552_;
}
case 2:
{
lean_object* v_symbols_1553_; lean_object* v___x_1554_; 
v_symbols_1553_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1554_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_1553_, v_data_1493_);
lean_dec(v_data_1493_);
return v___x_1554_;
}
default: 
{
lean_object* v_symbols_1555_; lean_object* v___x_1556_; 
v_symbols_1555_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1556_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_1555_, v_data_1493_);
lean_dec(v_data_1493_);
return v___x_1556_;
}
}
}
}
case 5:
{
lean_object* v_presentation_1557_; 
v_presentation_1557_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc_ref(v_presentation_1557_);
lean_dec_ref_known(v_modifier_1492_, 1);
if (lean_obj_tag(v_presentation_1557_) == 0)
{
lean_object* v_val_1558_; uint8_t v___x_1559_; lean_object* v___x_1560_; 
v_val_1558_ = lean_ctor_get(v_presentation_1557_, 0);
lean_inc(v_val_1558_);
lean_dec_ref_known(v_presentation_1557_, 1);
v___x_1559_ = 0;
v___x_1560_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1558_, v_data_1493_, v___x_1559_);
lean_dec(v_val_1558_);
return v___x_1560_;
}
else
{
lean_object* v_val_1561_; uint8_t v___x_1562_; 
v_val_1561_ = lean_ctor_get(v_presentation_1557_, 0);
lean_inc(v_val_1561_);
lean_dec_ref_known(v_presentation_1557_, 1);
v___x_1562_ = lean_unbox(v_val_1561_);
lean_dec(v_val_1561_);
switch(v___x_1562_)
{
case 1:
{
lean_object* v_symbols_1563_; lean_object* v___x_1564_; 
v_symbols_1563_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1564_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_1563_, v_data_1493_);
lean_dec(v_data_1493_);
return v___x_1564_;
}
case 2:
{
lean_object* v_symbols_1565_; lean_object* v___x_1566_; 
v_symbols_1565_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1566_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_1565_, v_data_1493_);
lean_dec(v_data_1493_);
return v___x_1566_;
}
default: 
{
lean_object* v_symbols_1567_; lean_object* v___x_1568_; 
v_symbols_1567_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1568_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_1567_, v_data_1493_);
lean_dec(v_data_1493_);
return v___x_1568_;
}
}
}
}
case 6:
{
lean_object* v_presentation_1569_; uint8_t v___x_1570_; lean_object* v___x_1571_; 
v_presentation_1569_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc(v_presentation_1569_);
lean_dec_ref_known(v_modifier_1492_, 1);
v___x_1570_ = 0;
v___x_1571_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1569_, v_data_1493_, v___x_1570_);
lean_dec(v_presentation_1569_);
return v___x_1571_;
}
case 7:
{
lean_object* v_presentation_1572_; 
v_presentation_1572_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc_ref(v_presentation_1572_);
lean_dec_ref_known(v_modifier_1492_, 1);
if (lean_obj_tag(v_presentation_1572_) == 0)
{
lean_object* v_val_1573_; uint8_t v___x_1574_; lean_object* v___x_1575_; 
v_val_1573_ = lean_ctor_get(v_presentation_1572_, 0);
lean_inc(v_val_1573_);
lean_dec_ref_known(v_presentation_1572_, 1);
v___x_1574_ = 0;
v___x_1575_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1573_, v_data_1493_, v___x_1574_);
lean_dec(v_val_1573_);
return v___x_1575_;
}
else
{
lean_object* v_val_1576_; uint8_t v___x_1577_; 
v_val_1576_ = lean_ctor_get(v_presentation_1572_, 0);
lean_inc(v_val_1576_);
lean_dec_ref_known(v_presentation_1572_, 1);
v___x_1577_ = lean_unbox(v_val_1576_);
lean_dec(v_val_1576_);
switch(v___x_1577_)
{
case 0:
{
lean_object* v_symbols_1578_; lean_object* v___x_1579_; 
v_symbols_1578_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1579_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1578_, v_data_1493_);
lean_dec(v_data_1493_);
return v___x_1579_;
}
case 1:
{
lean_object* v_symbols_1580_; lean_object* v___x_1581_; 
v_symbols_1580_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1581_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1580_, v_data_1493_);
lean_dec(v_data_1493_);
return v___x_1581_;
}
case 2:
{
lean_object* v_symbols_1582_; lean_object* v___x_1583_; 
v_symbols_1582_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1583_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1582_, v_data_1493_);
lean_dec(v_data_1493_);
return v___x_1583_;
}
default: 
{
lean_object* v___x_1584_; 
v___x_1584_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_data_1493_);
lean_dec(v_data_1493_);
return v___x_1584_;
}
}
}
}
case 8:
{
lean_object* v_presentation_1585_; 
v_presentation_1585_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc_ref(v_presentation_1585_);
lean_dec_ref_known(v_modifier_1492_, 1);
if (lean_obj_tag(v_presentation_1585_) == 0)
{
lean_object* v_val_1586_; uint8_t v___x_1587_; lean_object* v___x_1588_; 
v_val_1586_ = lean_ctor_get(v_presentation_1585_, 0);
lean_inc(v_val_1586_);
lean_dec_ref_known(v_presentation_1585_, 1);
v___x_1587_ = 0;
v___x_1588_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1586_, v_data_1493_, v___x_1587_);
lean_dec(v_val_1586_);
return v___x_1588_;
}
else
{
lean_object* v_val_1589_; uint8_t v___x_1590_; 
v_val_1589_ = lean_ctor_get(v_presentation_1585_, 0);
lean_inc(v_val_1589_);
lean_dec_ref_known(v_presentation_1585_, 1);
v___x_1590_ = lean_unbox(v_val_1589_);
lean_dec(v_val_1589_);
switch(v___x_1590_)
{
case 0:
{
lean_object* v_symbols_1591_; lean_object* v___x_1592_; 
v_symbols_1591_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1592_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1591_, v_data_1493_);
lean_dec(v_data_1493_);
return v___x_1592_;
}
case 1:
{
lean_object* v_symbols_1593_; lean_object* v___x_1594_; 
v_symbols_1593_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1594_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1593_, v_data_1493_);
lean_dec(v_data_1493_);
return v___x_1594_;
}
case 2:
{
lean_object* v_symbols_1595_; lean_object* v___x_1596_; 
v_symbols_1595_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1596_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1595_, v_data_1493_);
lean_dec(v_data_1493_);
return v___x_1596_;
}
default: 
{
lean_object* v___x_1597_; 
v___x_1597_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_data_1493_);
lean_dec(v_data_1493_);
return v___x_1597_;
}
}
}
}
case 9:
{
lean_object* v_presentation_1598_; lean_object* v___x_1599_; lean_object* v___y_1601_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
v_presentation_1598_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc(v_presentation_1598_);
lean_dec_ref_known(v_modifier_1492_, 1);
v___x_1599_ = lean_unsigned_to_nat(0u);
v___x_1615_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1616_ = lean_int_dec_le(v_data_1493_, v___x_1615_);
if (v___x_1616_ == 0)
{
v___y_1601_ = v_data_1493_;
goto v___jp_1600_;
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1617_ = lean_int_neg(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1618_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1619_ = lean_int_add(v___x_1617_, v___x_1618_);
lean_dec(v___x_1617_);
v___y_1601_ = v___x_1619_;
goto v___jp_1600_;
}
v___jp_1600_:
{
switch(lean_obj_tag(v_presentation_1598_))
{
case 0:
{
uint8_t v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = 0;
v___x_1603_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1599_, v___y_1601_, v___x_1602_);
return v___x_1603_;
}
case 1:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; lean_object* v___x_1608_; 
v___x_1604_ = lean_unsigned_to_nat(2u);
v___x_1605_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1606_ = lean_int_emod(v___y_1601_, v___x_1605_);
lean_dec(v___y_1601_);
v___x_1607_ = 0;
v___x_1608_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1604_, v___x_1606_, v___x_1607_);
return v___x_1608_;
}
case 2:
{
lean_object* v___x_1609_; uint8_t v___x_1610_; lean_object* v___x_1611_; 
v___x_1609_ = lean_unsigned_to_nat(4u);
v___x_1610_ = 0;
v___x_1611_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1609_, v___y_1601_, v___x_1610_);
return v___x_1611_;
}
default: 
{
lean_object* v_num_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; 
v_num_1612_ = lean_ctor_get(v_presentation_1598_, 0);
lean_inc(v_num_1612_);
lean_dec_ref_known(v_presentation_1598_, 1);
v___x_1613_ = 0;
v___x_1614_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1612_, v___y_1601_, v___x_1613_);
lean_dec(v_num_1612_);
return v___x_1614_;
}
}
}
}
case 10:
{
lean_object* v_presentation_1620_; uint8_t v___x_1621_; lean_object* v___x_1622_; 
v_presentation_1620_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc(v_presentation_1620_);
lean_dec_ref_known(v_modifier_1492_, 1);
v___x_1621_ = 0;
v___x_1622_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1620_, v_data_1493_, v___x_1621_);
lean_dec(v_presentation_1620_);
return v___x_1622_;
}
case 11:
{
lean_object* v_presentation_1623_; uint8_t v___x_1624_; lean_object* v___x_1625_; 
v_presentation_1623_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc(v_presentation_1623_);
lean_dec_ref_known(v_modifier_1492_, 1);
v___x_1624_ = 0;
v___x_1625_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1623_, v_data_1493_, v___x_1624_);
lean_dec(v_presentation_1623_);
return v___x_1625_;
}
case 12:
{
uint8_t v_presentation_1626_; 
v_presentation_1626_ = lean_ctor_get_uint8(v_modifier_1492_, 0);
lean_dec_ref_known(v_modifier_1492_, 0);
switch(v_presentation_1626_)
{
case 0:
{
lean_object* v_symbols_1627_; uint8_t v___x_1628_; lean_object* v___x_1629_; 
v_symbols_1627_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1628_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1629_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1627_, v___x_1628_);
return v___x_1629_;
}
case 1:
{
lean_object* v_symbols_1630_; uint8_t v___x_1631_; lean_object* v___x_1632_; 
v_symbols_1630_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1631_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1632_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1630_, v___x_1631_);
return v___x_1632_;
}
case 2:
{
lean_object* v_symbols_1633_; uint8_t v___x_1634_; lean_object* v___x_1635_; 
v_symbols_1633_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1634_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1635_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1633_, v___x_1634_);
return v___x_1635_;
}
default: 
{
lean_object* v_symbols_1636_; uint8_t v___x_1637_; lean_object* v___x_1638_; 
v_symbols_1636_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1637_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1638_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1636_, v___x_1637_);
return v___x_1638_;
}
}
}
case 13:
{
lean_object* v_presentation_1639_; 
v_presentation_1639_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc_ref(v_presentation_1639_);
lean_dec_ref_known(v_modifier_1492_, 1);
if (lean_obj_tag(v_presentation_1639_) == 0)
{
lean_object* v_val_1640_; uint8_t v_firstDayOfWeek_1641_; lean_object* v_firstOrd_1642_; uint8_t v___x_1643_; lean_object* v_dayOrd_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; lean_object* v___x_1652_; 
v_val_1640_ = lean_ctor_get(v_presentation_1639_, 0);
lean_inc(v_val_1640_);
lean_dec_ref_known(v_presentation_1639_, 1);
v_firstDayOfWeek_1641_ = lean_ctor_get_uint8(v_dateformat_1491_, sizeof(void*)*2);
v_firstOrd_1642_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_1641_);
v___x_1643_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v_dayOrd_1644_ = l_Std_Time_Weekday_toOrdinal(v___x_1643_);
v___x_1645_ = lean_int_sub(v_dayOrd_1644_, v_firstOrd_1642_);
lean_dec(v_firstOrd_1642_);
lean_dec(v_dayOrd_1644_);
v___x_1646_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_1647_ = lean_int_add(v___x_1645_, v___x_1646_);
lean_dec(v___x_1645_);
v___x_1648_ = lean_int_emod(v___x_1647_, v___x_1646_);
lean_dec(v___x_1647_);
v___x_1649_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1650_ = lean_int_add(v___x_1648_, v___x_1649_);
lean_dec(v___x_1648_);
v___x_1651_ = 0;
v___x_1652_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1640_, v___x_1650_, v___x_1651_);
lean_dec(v_val_1640_);
return v___x_1652_;
}
else
{
lean_object* v_val_1653_; uint8_t v___x_1654_; 
v_val_1653_ = lean_ctor_get(v_presentation_1639_, 0);
lean_inc(v_val_1653_);
lean_dec_ref_known(v_presentation_1639_, 1);
v___x_1654_ = lean_unbox(v_val_1653_);
lean_dec(v_val_1653_);
switch(v___x_1654_)
{
case 0:
{
lean_object* v_symbols_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; 
v_symbols_1655_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1656_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1657_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1655_, v___x_1656_);
return v___x_1657_;
}
case 1:
{
lean_object* v_symbols_1658_; uint8_t v___x_1659_; lean_object* v___x_1660_; 
v_symbols_1658_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1659_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1660_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1658_, v___x_1659_);
return v___x_1660_;
}
case 2:
{
lean_object* v_symbols_1661_; uint8_t v___x_1662_; lean_object* v___x_1663_; 
v_symbols_1661_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1662_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1663_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1661_, v___x_1662_);
return v___x_1663_;
}
default: 
{
lean_object* v_symbols_1664_; uint8_t v___x_1665_; lean_object* v___x_1666_; 
v_symbols_1664_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1665_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1666_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1664_, v___x_1665_);
return v___x_1666_;
}
}
}
}
case 14:
{
lean_object* v_presentation_1667_; 
v_presentation_1667_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc_ref(v_presentation_1667_);
lean_dec_ref_known(v_modifier_1492_, 1);
if (lean_obj_tag(v_presentation_1667_) == 0)
{
lean_object* v_val_1668_; uint8_t v_firstDayOfWeek_1669_; lean_object* v_firstOrd_1670_; uint8_t v___x_1671_; lean_object* v_dayOrd_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; lean_object* v___x_1680_; 
v_val_1668_ = lean_ctor_get(v_presentation_1667_, 0);
lean_inc(v_val_1668_);
lean_dec_ref_known(v_presentation_1667_, 1);
v_firstDayOfWeek_1669_ = lean_ctor_get_uint8(v_dateformat_1491_, sizeof(void*)*2);
v_firstOrd_1670_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_1669_);
v___x_1671_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v_dayOrd_1672_ = l_Std_Time_Weekday_toOrdinal(v___x_1671_);
v___x_1673_ = lean_int_sub(v_dayOrd_1672_, v_firstOrd_1670_);
lean_dec(v_firstOrd_1670_);
lean_dec(v_dayOrd_1672_);
v___x_1674_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_1675_ = lean_int_add(v___x_1673_, v___x_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_int_emod(v___x_1675_, v___x_1674_);
lean_dec(v___x_1675_);
v___x_1677_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1678_ = lean_int_add(v___x_1676_, v___x_1677_);
lean_dec(v___x_1676_);
v___x_1679_ = 0;
v___x_1680_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1668_, v___x_1678_, v___x_1679_);
lean_dec(v_val_1668_);
return v___x_1680_;
}
else
{
lean_object* v_val_1681_; uint8_t v___x_1682_; 
v_val_1681_ = lean_ctor_get(v_presentation_1667_, 0);
lean_inc(v_val_1681_);
lean_dec_ref_known(v_presentation_1667_, 1);
v___x_1682_ = lean_unbox(v_val_1681_);
lean_dec(v_val_1681_);
switch(v___x_1682_)
{
case 0:
{
lean_object* v_symbols_1683_; uint8_t v___x_1684_; lean_object* v___x_1685_; 
v_symbols_1683_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1684_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1685_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1683_, v___x_1684_);
return v___x_1685_;
}
case 1:
{
lean_object* v_symbols_1686_; uint8_t v___x_1687_; lean_object* v___x_1688_; 
v_symbols_1686_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1687_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1688_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1686_, v___x_1687_);
return v___x_1688_;
}
case 2:
{
lean_object* v_symbols_1689_; uint8_t v___x_1690_; lean_object* v___x_1691_; 
v_symbols_1689_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1690_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1691_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1689_, v___x_1690_);
return v___x_1691_;
}
default: 
{
lean_object* v_symbols_1692_; uint8_t v___x_1693_; lean_object* v___x_1694_; 
v_symbols_1692_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1693_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1694_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1692_, v___x_1693_);
return v___x_1694_;
}
}
}
}
case 15:
{
lean_object* v_presentation_1695_; uint8_t v___x_1696_; lean_object* v___x_1697_; 
v_presentation_1695_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc(v_presentation_1695_);
lean_dec_ref_known(v_modifier_1492_, 1);
v___x_1696_ = 0;
v___x_1697_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1695_, v_data_1493_, v___x_1696_);
lean_dec(v_presentation_1695_);
return v___x_1697_;
}
case 16:
{
uint8_t v_presentation_1698_; 
v_presentation_1698_ = lean_ctor_get_uint8(v_modifier_1492_, 0);
lean_dec_ref_known(v_modifier_1492_, 0);
if (v_presentation_1698_ == 2)
{
lean_object* v_symbols_1699_; uint8_t v___x_1700_; lean_object* v___x_1701_; 
v_symbols_1699_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1700_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1701_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(v_symbols_1699_, v___x_1700_);
return v___x_1701_;
}
else
{
lean_object* v_symbols_1702_; uint8_t v___x_1703_; lean_object* v___x_1704_; 
v_symbols_1702_ = lean_ctor_get(v_dateformat_1491_, 1);
v___x_1703_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1704_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(v_symbols_1702_, v___x_1703_);
return v___x_1704_;
}
}
case 17:
{
uint8_t v_presentation_1705_; 
v_presentation_1705_ = lean_ctor_get_uint8(v_modifier_1492_, 0);
lean_dec_ref_known(v_modifier_1492_, 0);
switch(v_presentation_1705_)
{
case 1:
{
lean_object* v_symbols_1706_; lean_object* v_dayPeriodLong_1707_; uint8_t v___x_1708_; lean_object* v___x_1709_; 
v_symbols_1706_ = lean_ctor_get(v_dateformat_1491_, 1);
v_dayPeriodLong_1707_ = lean_ctor_get(v_symbols_1706_, 20);
v___x_1708_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1709_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodLong_1707_, v___x_1708_);
return v___x_1709_;
}
case 2:
{
lean_object* v_symbols_1710_; lean_object* v_dayPeriodNarrow_1711_; uint8_t v___x_1712_; lean_object* v___x_1713_; 
v_symbols_1710_ = lean_ctor_get(v_dateformat_1491_, 1);
v_dayPeriodNarrow_1711_ = lean_ctor_get(v_symbols_1710_, 21);
v___x_1712_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1713_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodNarrow_1711_, v___x_1712_);
return v___x_1713_;
}
default: 
{
lean_object* v_symbols_1714_; lean_object* v_dayPeriodShort_1715_; uint8_t v___x_1716_; lean_object* v___x_1717_; 
v_symbols_1714_ = lean_ctor_get(v_dateformat_1491_, 1);
v_dayPeriodShort_1715_ = lean_ctor_get(v_symbols_1714_, 19);
v___x_1716_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1717_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodShort_1715_, v___x_1716_);
return v___x_1717_;
}
}
}
case 18:
{
uint8_t v_presentation_1718_; 
v_presentation_1718_ = lean_ctor_get_uint8(v_modifier_1492_, 0);
lean_dec_ref_known(v_modifier_1492_, 0);
switch(v_presentation_1718_)
{
case 1:
{
lean_object* v_symbols_1719_; lean_object* v_extendedDayPeriodLong_1720_; uint8_t v___x_1721_; lean_object* v___x_1722_; 
v_symbols_1719_ = lean_ctor_get(v_dateformat_1491_, 1);
v_extendedDayPeriodLong_1720_ = lean_ctor_get(v_symbols_1719_, 23);
v___x_1721_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1722_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodLong_1720_, v___x_1721_);
return v___x_1722_;
}
case 2:
{
lean_object* v_symbols_1723_; lean_object* v_extendedDayPeriodNarrow_1724_; uint8_t v___x_1725_; lean_object* v___x_1726_; 
v_symbols_1723_ = lean_ctor_get(v_dateformat_1491_, 1);
v_extendedDayPeriodNarrow_1724_ = lean_ctor_get(v_symbols_1723_, 24);
v___x_1725_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1726_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodNarrow_1724_, v___x_1725_);
return v___x_1726_;
}
default: 
{
lean_object* v_symbols_1727_; lean_object* v_extendedDayPeriodShort_1728_; uint8_t v___x_1729_; lean_object* v___x_1730_; 
v_symbols_1727_ = lean_ctor_get(v_dateformat_1491_, 1);
v_extendedDayPeriodShort_1728_ = lean_ctor_get(v_symbols_1727_, 22);
v___x_1729_ = lean_unbox(v_data_1493_);
lean_dec(v_data_1493_);
v___x_1730_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodShort_1728_, v___x_1729_);
return v___x_1730_;
}
}
}
case 19:
{
lean_object* v_presentation_1731_; uint8_t v___x_1732_; lean_object* v___x_1733_; 
v_presentation_1731_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc(v_presentation_1731_);
lean_dec_ref_known(v_modifier_1492_, 1);
v___x_1732_ = 0;
v___x_1733_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1731_, v_data_1493_, v___x_1732_);
lean_dec(v_presentation_1731_);
return v___x_1733_;
}
case 20:
{
lean_object* v_presentation_1734_; uint8_t v___x_1735_; lean_object* v___x_1736_; 
v_presentation_1734_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc(v_presentation_1734_);
lean_dec_ref_known(v_modifier_1492_, 1);
v___x_1735_ = 0;
v___x_1736_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1734_, v_data_1493_, v___x_1735_);
lean_dec(v_presentation_1734_);
return v___x_1736_;
}
case 21:
{
lean_object* v_presentation_1737_; uint8_t v___x_1738_; lean_object* v___x_1739_; 
v_presentation_1737_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc(v_presentation_1737_);
lean_dec_ref_known(v_modifier_1492_, 1);
v___x_1738_ = 0;
v___x_1739_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1737_, v_data_1493_, v___x_1738_);
lean_dec(v_presentation_1737_);
return v___x_1739_;
}
case 22:
{
lean_object* v_presentation_1740_; uint8_t v___x_1741_; lean_object* v___x_1742_; 
v_presentation_1740_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc(v_presentation_1740_);
lean_dec_ref_known(v_modifier_1492_, 1);
v___x_1741_ = 0;
v___x_1742_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1740_, v_data_1493_, v___x_1741_);
lean_dec(v_presentation_1740_);
return v___x_1742_;
}
case 23:
{
lean_object* v_presentation_1743_; uint8_t v___x_1744_; lean_object* v___x_1745_; 
v_presentation_1743_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc(v_presentation_1743_);
lean_dec_ref_known(v_modifier_1492_, 1);
v___x_1744_ = 0;
v___x_1745_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1743_, v_data_1493_, v___x_1744_);
lean_dec(v_presentation_1743_);
return v___x_1745_;
}
case 24:
{
lean_object* v_presentation_1746_; uint8_t v___x_1747_; lean_object* v___x_1748_; 
v_presentation_1746_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc(v_presentation_1746_);
lean_dec_ref_known(v_modifier_1492_, 1);
v___x_1747_ = 0;
v___x_1748_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1746_, v_data_1493_, v___x_1747_);
lean_dec(v_presentation_1746_);
return v___x_1748_;
}
case 25:
{
lean_object* v_presentation_1749_; 
v_presentation_1749_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc(v_presentation_1749_);
lean_dec_ref_known(v_modifier_1492_, 1);
if (lean_obj_tag(v_presentation_1749_) == 0)
{
lean_object* v___x_1750_; uint8_t v___x_1751_; lean_object* v___x_1752_; 
v___x_1750_ = lean_unsigned_to_nat(9u);
v___x_1751_ = 0;
v___x_1752_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1750_, v_data_1493_, v___x_1751_);
return v___x_1752_;
}
else
{
lean_object* v_digits_1753_; lean_object* v___x_1754_; uint32_t v___x_1755_; lean_object* v___x_1756_; lean_object* v_s_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v_digits_1753_ = lean_ctor_get(v_presentation_1749_, 0);
lean_inc(v_digits_1753_);
lean_dec_ref_known(v_presentation_1749_, 1);
v___x_1754_ = lean_unsigned_to_nat(9u);
v___x_1755_ = 48;
v___x_1756_ = l_Int_repr(v_data_1493_);
lean_dec(v_data_1493_);
v_s_1757_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1754_, v___x_1755_, v___x_1756_);
lean_dec_ref(v___x_1756_);
v___x_1758_ = lean_unsigned_to_nat(0u);
v___x_1759_ = lean_string_utf8_byte_size(v_s_1757_);
lean_inc_ref(v_s_1757_);
v___x_1760_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1760_, 0, v_s_1757_);
lean_ctor_set(v___x_1760_, 1, v___x_1758_);
lean_ctor_set(v___x_1760_, 2, v___x_1759_);
v___x_1761_ = l_String_Slice_Pos_nextn(v___x_1760_, v___x_1758_, v_digits_1753_);
lean_dec_ref_known(v___x_1760_, 3);
v___x_1762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1762_, 0, v_s_1757_);
lean_ctor_set(v___x_1762_, 1, v___x_1758_);
lean_ctor_set(v___x_1762_, 2, v___x_1761_);
v___x_1763_ = l_String_Slice_toString(v___x_1762_);
lean_dec_ref_known(v___x_1762_, 3);
return v___x_1763_;
}
}
case 26:
{
lean_object* v_presentation_1764_; uint8_t v___x_1765_; lean_object* v___x_1766_; 
v_presentation_1764_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc(v_presentation_1764_);
lean_dec_ref_known(v_modifier_1492_, 1);
v___x_1765_ = 0;
v___x_1766_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1764_, v_data_1493_, v___x_1765_);
lean_dec(v_presentation_1764_);
return v___x_1766_;
}
case 27:
{
lean_object* v_presentation_1767_; uint8_t v___x_1768_; lean_object* v___x_1769_; 
v_presentation_1767_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc(v_presentation_1767_);
lean_dec_ref_known(v_modifier_1492_, 1);
v___x_1768_ = 0;
v___x_1769_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1767_, v_data_1493_, v___x_1768_);
lean_dec(v_presentation_1767_);
return v___x_1769_;
}
case 28:
{
lean_object* v_presentation_1770_; uint8_t v___x_1771_; lean_object* v___x_1772_; 
v_presentation_1770_ = lean_ctor_get(v_modifier_1492_, 0);
lean_inc(v_presentation_1770_);
lean_dec_ref_known(v_modifier_1492_, 1);
v___x_1771_ = 0;
v___x_1772_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1770_, v_data_1493_, v___x_1771_);
lean_dec(v_presentation_1770_);
return v___x_1772_;
}
case 29:
{
uint8_t v_presentation_1773_; 
v_presentation_1773_ = lean_ctor_get_uint8(v_modifier_1492_, 0);
lean_dec_ref_known(v_modifier_1492_, 0);
if (v_presentation_1773_ == 0)
{
lean_object* v___x_1774_; 
lean_dec(v_data_1493_);
v___x_1774_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
return v___x_1774_;
}
else
{
return v_data_1493_;
}
}
case 32:
{
uint8_t v_presentation_1775_; 
v_presentation_1775_ = lean_ctor_get_uint8(v_modifier_1492_, 0);
lean_dec_ref_known(v_modifier_1492_, 0);
if (v_presentation_1775_ == 0)
{
lean_object* v_fst_1777_; lean_object* v_snd_1778_; lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___x_1801_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1802_ = lean_int_dec_eq(v_data_1493_, v___x_1801_);
if (v___x_1802_ == 0)
{
uint8_t v___x_1803_; 
v___x_1803_ = lean_int_dec_le(v___x_1801_, v_data_1493_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1805_ = lean_int_neg(v_data_1493_);
lean_dec(v_data_1493_);
v_fst_1777_ = v___x_1804_;
v_snd_1778_ = v___x_1805_;
goto v___jp_1776_;
}
else
{
lean_object* v___x_1806_; 
v___x_1806_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v_fst_1777_ = v___x_1806_;
v_snd_1778_ = v_data_1493_;
goto v___jp_1776_;
}
}
else
{
lean_object* v___x_1807_; 
lean_dec(v_data_1493_);
v___x_1807_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1807_;
}
v___jp_1776_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v_t_1781_; lean_object* v_hour_1782_; lean_object* v_minute_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1779_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_1780_ = lean_int_mul(v_snd_1778_, v___x_1779_);
lean_dec(v_snd_1778_);
v_t_1781_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1780_);
lean_dec(v___x_1780_);
v_hour_1782_ = lean_ctor_get(v_t_1781_, 0);
lean_inc(v_hour_1782_);
v_minute_1783_ = lean_ctor_get(v_t_1781_, 1);
lean_inc(v_minute_1783_);
lean_dec_ref(v_t_1781_);
v___x_1784_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1785_ = lean_int_dec_eq(v_minute_1783_, v___x_1784_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; uint32_t v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1786_ = lean_unsigned_to_nat(2u);
v___x_1787_ = 48;
v___x_1788_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1789_ = lean_string_append(v___x_1788_, v_fst_1777_);
v___x_1790_ = l_Int_repr(v_hour_1782_);
lean_dec(v_hour_1782_);
v___x_1791_ = lean_string_append(v___x_1789_, v___x_1790_);
lean_dec_ref(v___x_1790_);
v___x_1792_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___x_1793_ = lean_string_append(v___x_1791_, v___x_1792_);
v___x_1794_ = l_Int_repr(v_minute_1783_);
lean_dec(v_minute_1783_);
v___x_1795_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1786_, v___x_1787_, v___x_1794_);
lean_dec_ref(v___x_1794_);
v___x_1796_ = lean_string_append(v___x_1793_, v___x_1795_);
lean_dec_ref(v___x_1795_);
return v___x_1796_;
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
lean_dec(v_minute_1783_);
v___x_1797_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1798_ = lean_string_append(v___x_1797_, v_fst_1777_);
v___x_1799_ = l_Int_repr(v_hour_1782_);
lean_dec(v_hour_1782_);
v___x_1800_ = lean_string_append(v___x_1798_, v___x_1799_);
lean_dec_ref(v___x_1799_);
return v___x_1800_;
}
}
}
else
{
lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1808_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1809_ = lean_int_dec_eq(v_data_1493_, v___x_1808_);
if (v___x_1809_ == 0)
{
uint8_t v___x_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; uint8_t v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1810_ = 1;
v___x_1811_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1812_ = 0;
v___x_1813_ = 1;
v___x_1814_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1493_, v___x_1812_, v___x_1813_, v___x_1810_, v___x_1810_);
v___x_1815_ = lean_string_append(v___x_1811_, v___x_1814_);
lean_dec_ref(v___x_1814_);
return v___x_1815_;
}
else
{
lean_object* v___x_1816_; 
lean_dec(v_data_1493_);
v___x_1816_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1816_;
}
}
}
case 33:
{
uint8_t v_presentation_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; 
v_presentation_1817_ = lean_ctor_get_uint8(v_modifier_1492_, 0);
lean_dec_ref_known(v_modifier_1492_, 0);
v___x_1818_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1819_ = lean_int_dec_eq(v_data_1493_, v___x_1818_);
if (v___x_1819_ == 0)
{
uint8_t v___x_1820_; 
v___x_1820_ = 1;
switch(v_presentation_1817_)
{
case 0:
{
uint8_t v___x_1821_; uint8_t v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = 2;
v___x_1822_ = 1;
v___x_1823_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1493_, v___x_1821_, v___x_1822_, v___x_1819_, v___x_1820_);
return v___x_1823_;
}
case 1:
{
uint8_t v___x_1824_; uint8_t v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = 0;
v___x_1825_ = 1;
v___x_1826_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1493_, v___x_1824_, v___x_1825_, v___x_1819_, v___x_1820_);
return v___x_1826_;
}
case 2:
{
uint8_t v___x_1827_; uint8_t v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = 0;
v___x_1828_ = 1;
v___x_1829_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1493_, v___x_1827_, v___x_1828_, v___x_1820_, v___x_1820_);
return v___x_1829_;
}
case 3:
{
uint8_t v___x_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; 
v___x_1830_ = 0;
v___x_1831_ = 2;
v___x_1832_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1493_, v___x_1830_, v___x_1831_, v___x_1819_, v___x_1820_);
return v___x_1832_;
}
default: 
{
uint8_t v___x_1833_; uint8_t v___x_1834_; lean_object* v___x_1835_; 
v___x_1833_ = 0;
v___x_1834_ = 2;
v___x_1835_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1493_, v___x_1833_, v___x_1834_, v___x_1820_, v___x_1820_);
return v___x_1835_;
}
}
}
else
{
lean_object* v___x_1836_; 
lean_dec(v_data_1493_);
v___x_1836_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
return v___x_1836_;
}
}
case 34:
{
uint8_t v_presentation_1837_; 
v_presentation_1837_ = lean_ctor_get_uint8(v_modifier_1492_, 0);
lean_dec_ref_known(v_modifier_1492_, 0);
switch(v_presentation_1837_)
{
case 0:
{
uint8_t v___x_1838_; uint8_t v___x_1839_; uint8_t v___x_1840_; uint8_t v___x_1841_; lean_object* v___x_1842_; 
v___x_1838_ = 2;
v___x_1839_ = 1;
v___x_1840_ = 0;
v___x_1841_ = 1;
v___x_1842_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1493_, v___x_1838_, v___x_1839_, v___x_1840_, v___x_1841_);
return v___x_1842_;
}
case 1:
{
uint8_t v___x_1843_; uint8_t v___x_1844_; uint8_t v___x_1845_; uint8_t v___x_1846_; lean_object* v___x_1847_; 
v___x_1843_ = 0;
v___x_1844_ = 1;
v___x_1845_ = 0;
v___x_1846_ = 1;
v___x_1847_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1493_, v___x_1843_, v___x_1844_, v___x_1845_, v___x_1846_);
return v___x_1847_;
}
case 2:
{
uint8_t v___x_1848_; uint8_t v___x_1849_; uint8_t v___x_1850_; lean_object* v___x_1851_; 
v___x_1848_ = 0;
v___x_1849_ = 1;
v___x_1850_ = 1;
v___x_1851_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1493_, v___x_1848_, v___x_1849_, v___x_1850_, v___x_1850_);
return v___x_1851_;
}
case 3:
{
uint8_t v___x_1852_; uint8_t v___x_1853_; uint8_t v___x_1854_; uint8_t v___x_1855_; lean_object* v___x_1856_; 
v___x_1852_ = 0;
v___x_1853_ = 2;
v___x_1854_ = 0;
v___x_1855_ = 1;
v___x_1856_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1493_, v___x_1852_, v___x_1853_, v___x_1854_, v___x_1855_);
return v___x_1856_;
}
default: 
{
uint8_t v___x_1857_; uint8_t v___x_1858_; uint8_t v___x_1859_; lean_object* v___x_1860_; 
v___x_1857_ = 0;
v___x_1858_ = 2;
v___x_1859_ = 1;
v___x_1860_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1493_, v___x_1857_, v___x_1858_, v___x_1859_, v___x_1859_);
return v___x_1860_;
}
}
}
case 35:
{
uint8_t v_presentation_1861_; 
v_presentation_1861_ = lean_ctor_get_uint8(v_modifier_1492_, 0);
lean_dec_ref_known(v_modifier_1492_, 0);
switch(v_presentation_1861_)
{
case 0:
{
uint8_t v___x_1862_; uint8_t v___x_1863_; uint8_t v___x_1864_; uint8_t v___x_1865_; lean_object* v___x_1866_; 
v___x_1862_ = 0;
v___x_1863_ = 2;
v___x_1864_ = 0;
v___x_1865_ = 1;
v___x_1866_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1493_, v___x_1862_, v___x_1863_, v___x_1864_, v___x_1865_);
return v___x_1866_;
}
case 1:
{
lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1867_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1868_ = lean_int_dec_eq(v_data_1493_, v___x_1867_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; uint8_t v___x_1870_; uint8_t v___x_1871_; uint8_t v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1869_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1870_ = 0;
v___x_1871_ = 1;
v___x_1872_ = 1;
v___x_1873_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1493_, v___x_1870_, v___x_1871_, v___x_1872_, v___x_1872_);
v___x_1874_ = lean_string_append(v___x_1869_, v___x_1873_);
lean_dec_ref(v___x_1873_);
return v___x_1874_;
}
else
{
lean_object* v___x_1875_; 
lean_dec(v_data_1493_);
v___x_1875_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1875_;
}
}
default: 
{
lean_object* v___x_1876_; uint8_t v___x_1877_; 
v___x_1876_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1877_ = lean_int_dec_eq(v_data_1493_, v___x_1876_);
if (v___x_1877_ == 0)
{
uint8_t v___x_1878_; uint8_t v___x_1879_; uint8_t v___x_1880_; lean_object* v___x_1881_; 
v___x_1878_ = 1;
v___x_1879_ = 0;
v___x_1880_ = 2;
v___x_1881_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1493_, v___x_1879_, v___x_1880_, v___x_1878_, v___x_1878_);
return v___x_1881_;
}
else
{
lean_object* v___x_1882_; 
lean_dec(v_data_1493_);
v___x_1882_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
return v___x_1882_;
}
}
}
}
default: 
{
lean_dec_ref(v_modifier_1492_);
return v_data_1493_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___boxed(lean_object* v_dateformat_1883_, lean_object* v_modifier_1884_, lean_object* v_data_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_1883_, v_modifier_1884_, v_data_1885_);
lean_dec_ref(v_dateformat_1883_);
return v_res_1886_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0(void){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_unsigned_to_nat(4u);
v___x_1888_ = lean_nat_to_int(v___x_1887_);
return v___x_1888_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = lean_unsigned_to_nat(400u);
v___x_1890_ = lean_nat_to_int(v___x_1889_);
return v___x_1890_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2(void){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1892_ = lean_string_utf8_byte_size(v___x_1891_);
return v___x_1892_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_1894_ = lean_string_utf8_byte_size(v___x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(lean_object* v_modifier_1895_, lean_object* v_dateformat_1896_, lean_object* v_date_1897_){
_start:
{
uint8_t v_firstDayOfWeek_1898_; lean_object* v_minimalDaysInFirstWeek_1899_; lean_object* v_date_1900_; lean_object* v_timezone_1901_; 
v_firstDayOfWeek_1898_ = lean_ctor_get_uint8(v_dateformat_1896_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_1899_ = lean_ctor_get(v_dateformat_1896_, 0);
v_date_1900_ = lean_ctor_get(v_date_1897_, 0);
v_timezone_1901_ = lean_ctor_get(v_date_1897_, 3);
switch(lean_obj_tag(v_modifier_1895_))
{
case 0:
{
lean_object* v___x_1919_; lean_object* v_date_1920_; lean_object* v_year_1921_; uint8_t v___x_1922_; lean_object* v___x_1923_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_1919_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_date_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc_ref(v_date_1920_);
lean_dec(v___x_1919_);
v_year_1921_ = lean_ctor_get(v_date_1920_, 0);
lean_inc(v_year_1921_);
lean_dec_ref(v_date_1920_);
v___x_1922_ = l_Std_Time_Year_Offset_era(v_year_1921_);
lean_dec(v_year_1921_);
v___x_1923_ = lean_box(v___x_1922_);
return v___x_1923_;
}
case 1:
{
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
goto v___jp_1902_;
}
case 2:
{
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
goto v___jp_1902_;
}
case 3:
{
lean_object* v___x_1924_; lean_object* v_date_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1953_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_1924_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_date_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1953_ == 0)
{
lean_object* v_unused_1954_; 
v_unused_1954_ = lean_ctor_get(v___x_1924_, 1);
lean_dec(v_unused_1954_);
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1953_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_date_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1953_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v_year_1929_; lean_object* v_month_1930_; lean_object* v_day_1931_; uint8_t v___y_1933_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; uint8_t v___y_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; 
v_year_1929_ = lean_ctor_get(v_date_1925_, 0);
lean_inc(v_year_1929_);
v_month_1930_ = lean_ctor_get(v_date_1925_, 1);
lean_inc(v_month_1930_);
v_day_1931_ = lean_ctor_get(v_date_1925_, 2);
lean_inc(v_day_1931_);
lean_dec_ref(v_date_1925_);
v___x_1940_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_1941_ = lean_int_mod(v_year_1929_, v___x_1940_);
v___x_1942_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1943_ = lean_int_dec_eq(v___x_1941_, v___x_1942_);
lean_dec(v___x_1941_);
v___x_1946_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1947_ = lean_int_mod(v_year_1929_, v___x_1946_);
v___x_1948_ = lean_int_dec_eq(v___x_1947_, v___x_1942_);
lean_dec(v___x_1947_);
if (v___x_1948_ == 0)
{
uint8_t v___x_1949_; 
lean_dec(v_year_1929_);
v___x_1949_ = 1;
v___y_1945_ = v___x_1949_;
goto v___jp_1944_;
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1950_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_1951_ = lean_int_mod(v_year_1929_, v___x_1950_);
lean_dec(v_year_1929_);
v___x_1952_ = lean_int_dec_eq(v___x_1951_, v___x_1942_);
lean_dec(v___x_1951_);
v___y_1945_ = v___x_1952_;
goto v___jp_1944_;
}
v___jp_1932_:
{
lean_object* v___x_1935_; 
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 1, v_day_1931_);
lean_ctor_set(v___x_1927_, 0, v_month_1930_);
v___x_1935_ = v___x_1927_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_month_1930_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_day_1931_);
v___x_1935_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1936_ = l_Std_Time_ValidDate_dayOfYear(v___y_1933_, v___x_1935_);
lean_dec_ref(v___x_1935_);
v___x_1937_ = lean_box(v___y_1933_);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
lean_ctor_set(v___x_1938_, 1, v___x_1936_);
return v___x_1938_;
}
}
v___jp_1944_:
{
if (v___x_1943_ == 0)
{
v___y_1933_ = v___x_1943_;
goto v___jp_1932_;
}
else
{
v___y_1933_ = v___y_1945_;
goto v___jp_1932_;
}
}
}
}
case 4:
{
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
goto v___jp_1906_;
}
case 5:
{
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
goto v___jp_1906_;
}
case 6:
{
lean_object* v___x_1955_; lean_object* v_date_1956_; lean_object* v_day_1957_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_1955_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_date_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc_ref(v_date_1956_);
lean_dec(v___x_1955_);
v_day_1957_ = lean_ctor_get(v_date_1956_, 2);
lean_inc(v_day_1957_);
lean_dec_ref(v_date_1956_);
return v_day_1957_;
}
case 7:
{
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
goto v___jp_1910_;
}
case 8:
{
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
goto v___jp_1910_;
}
case 9:
{
lean_object* v___x_1958_; lean_object* v_date_1959_; lean_object* v___x_1960_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_1958_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_date_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc_ref(v_date_1959_);
lean_dec(v___x_1958_);
v___x_1960_ = l_Std_Time_PlainDate_weekYear(v_date_1959_, v_firstDayOfWeek_1898_, v_minimalDaysInFirstWeek_1899_);
return v___x_1960_;
}
case 10:
{
lean_object* v___x_1961_; lean_object* v_date_1962_; lean_object* v___x_1963_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_1961_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_date_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc_ref(v_date_1962_);
lean_dec(v___x_1961_);
v___x_1963_ = l_Std_Time_PlainDate_weekOfYear(v_date_1962_, v_firstDayOfWeek_1898_, v_minimalDaysInFirstWeek_1899_);
return v___x_1963_;
}
case 11:
{
lean_object* v___x_1964_; lean_object* v_date_1965_; lean_object* v___x_1966_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_1964_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_date_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc_ref(v_date_1965_);
lean_dec(v___x_1964_);
v___x_1966_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1965_, v_firstDayOfWeek_1898_);
return v___x_1966_;
}
case 12:
{
lean_object* v___x_1967_; lean_object* v_date_1968_; uint8_t v___x_1969_; lean_object* v___x_1970_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_1967_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_date_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc_ref(v_date_1968_);
lean_dec(v___x_1967_);
v___x_1969_ = l_Std_Time_PlainDate_weekday(v_date_1968_);
v___x_1970_ = lean_box(v___x_1969_);
return v___x_1970_;
}
case 13:
{
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
goto v___jp_1914_;
}
case 14:
{
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
goto v___jp_1914_;
}
case 15:
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Std_Time_DateTime_alignedWeekOfMonth(v_date_1897_);
lean_dec_ref(v_date_1897_);
return v___x_1971_;
}
case 16:
{
lean_object* v___x_1972_; lean_object* v_time_1973_; lean_object* v_hour_1974_; uint8_t v___x_1975_; lean_object* v___x_1976_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_1972_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_time_1973_ = lean_ctor_get(v___x_1972_, 1);
lean_inc_ref(v_time_1973_);
lean_dec(v___x_1972_);
v_hour_1974_ = lean_ctor_get(v_time_1973_, 0);
lean_inc(v_hour_1974_);
lean_dec_ref(v_time_1973_);
v___x_1975_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1974_);
lean_dec(v_hour_1974_);
v___x_1976_ = lean_box(v___x_1975_);
return v___x_1976_;
}
case 17:
{
lean_object* v___x_1977_; lean_object* v_time_1978_; lean_object* v_hour_1979_; lean_object* v_minute_1980_; lean_object* v_second_1981_; uint8_t v___x_1982_; lean_object* v___x_1983_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_1977_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_time_1978_ = lean_ctor_get(v___x_1977_, 1);
lean_inc_ref(v_time_1978_);
lean_dec(v___x_1977_);
v_hour_1979_ = lean_ctor_get(v_time_1978_, 0);
lean_inc(v_hour_1979_);
v_minute_1980_ = lean_ctor_get(v_time_1978_, 1);
lean_inc(v_minute_1980_);
v_second_1981_ = lean_ctor_get(v_time_1978_, 2);
lean_inc(v_second_1981_);
lean_dec_ref(v_time_1978_);
v___x_1982_ = l_Std_Time_classifyDayPeriod(v_hour_1979_, v_minute_1980_, v_second_1981_);
lean_dec(v_second_1981_);
lean_dec(v_minute_1980_);
lean_dec(v_hour_1979_);
v___x_1983_ = lean_box(v___x_1982_);
return v___x_1983_;
}
case 18:
{
lean_object* v___x_1984_; lean_object* v_time_1985_; lean_object* v_hour_1986_; lean_object* v_minute_1987_; lean_object* v_second_1988_; uint8_t v___x_1989_; lean_object* v___x_1990_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_1984_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_time_1985_ = lean_ctor_get(v___x_1984_, 1);
lean_inc_ref(v_time_1985_);
lean_dec(v___x_1984_);
v_hour_1986_ = lean_ctor_get(v_time_1985_, 0);
lean_inc(v_hour_1986_);
v_minute_1987_ = lean_ctor_get(v_time_1985_, 1);
lean_inc(v_minute_1987_);
v_second_1988_ = lean_ctor_get(v_time_1985_, 2);
lean_inc(v_second_1988_);
lean_dec_ref(v_time_1985_);
v___x_1989_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1986_, v_minute_1987_, v_second_1988_);
lean_dec(v_second_1988_);
lean_dec(v_minute_1987_);
lean_dec(v_hour_1986_);
v___x_1990_ = lean_box(v___x_1989_);
return v___x_1990_;
}
case 19:
{
lean_object* v___x_1991_; lean_object* v_time_1992_; lean_object* v_hour_1993_; lean_object* v___x_1994_; lean_object* v_fst_1995_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_1991_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_time_1992_ = lean_ctor_get(v___x_1991_, 1);
lean_inc_ref(v_time_1992_);
lean_dec(v___x_1991_);
v_hour_1993_ = lean_ctor_get(v_time_1992_, 0);
lean_inc(v_hour_1993_);
lean_dec_ref(v_time_1992_);
v___x_1994_ = l_Std_Time_HourMarker_toRelative(v_hour_1993_);
v_fst_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_fst_1995_);
lean_dec_ref(v___x_1994_);
return v_fst_1995_;
}
case 20:
{
lean_object* v___x_1996_; lean_object* v_time_1997_; lean_object* v_hour_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_1996_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_time_1997_ = lean_ctor_get(v___x_1996_, 1);
lean_inc_ref(v_time_1997_);
lean_dec(v___x_1996_);
v_hour_1998_ = lean_ctor_get(v_time_1997_, 0);
lean_inc(v_hour_1998_);
lean_dec_ref(v_time_1997_);
v___x_1999_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_2000_ = lean_int_emod(v_hour_1998_, v___x_1999_);
lean_dec(v_hour_1998_);
return v___x_2000_;
}
case 21:
{
lean_object* v___x_2001_; lean_object* v_time_2002_; lean_object* v_hour_2003_; lean_object* v___x_2004_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_2001_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_time_2002_ = lean_ctor_get(v___x_2001_, 1);
lean_inc_ref(v_time_2002_);
lean_dec(v___x_2001_);
v_hour_2003_ = lean_ctor_get(v_time_2002_, 0);
lean_inc(v_hour_2003_);
lean_dec_ref(v_time_2002_);
v___x_2004_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_2003_);
lean_dec(v_hour_2003_);
return v___x_2004_;
}
case 22:
{
lean_object* v___x_2005_; lean_object* v_time_2006_; lean_object* v_hour_2007_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_2005_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_time_2006_ = lean_ctor_get(v___x_2005_, 1);
lean_inc_ref(v_time_2006_);
lean_dec(v___x_2005_);
v_hour_2007_ = lean_ctor_get(v_time_2006_, 0);
lean_inc(v_hour_2007_);
lean_dec_ref(v_time_2006_);
return v_hour_2007_;
}
case 23:
{
lean_object* v___x_2008_; lean_object* v_time_2009_; lean_object* v_minute_2010_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_2008_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_time_2009_ = lean_ctor_get(v___x_2008_, 1);
lean_inc_ref(v_time_2009_);
lean_dec(v___x_2008_);
v_minute_2010_ = lean_ctor_get(v_time_2009_, 1);
lean_inc(v_minute_2010_);
lean_dec_ref(v_time_2009_);
return v_minute_2010_;
}
case 24:
{
lean_object* v___x_2011_; lean_object* v_time_2012_; lean_object* v_second_2013_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_2011_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_time_2012_ = lean_ctor_get(v___x_2011_, 1);
lean_inc_ref(v_time_2012_);
lean_dec(v___x_2011_);
v_second_2013_ = lean_ctor_get(v_time_2012_, 2);
lean_inc(v_second_2013_);
lean_dec_ref(v_time_2012_);
return v_second_2013_;
}
case 25:
{
lean_object* v___x_2014_; lean_object* v_time_2015_; lean_object* v_nanosecond_2016_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_2014_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_time_2015_ = lean_ctor_get(v___x_2014_, 1);
lean_inc_ref(v_time_2015_);
lean_dec(v___x_2014_);
v_nanosecond_2016_ = lean_ctor_get(v_time_2015_, 3);
lean_inc(v_nanosecond_2016_);
lean_dec_ref(v_time_2015_);
return v_nanosecond_2016_;
}
case 26:
{
lean_object* v___x_2017_; lean_object* v_time_2018_; lean_object* v___x_2019_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_2017_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_time_2018_ = lean_ctor_get(v___x_2017_, 1);
lean_inc_ref(v_time_2018_);
lean_dec(v___x_2017_);
v___x_2019_ = l_Std_Time_PlainTime_toMilliseconds(v_time_2018_);
lean_dec_ref(v_time_2018_);
return v___x_2019_;
}
case 27:
{
lean_object* v___x_2020_; lean_object* v_time_2021_; lean_object* v_nanosecond_2022_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_2020_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_time_2021_ = lean_ctor_get(v___x_2020_, 1);
lean_inc_ref(v_time_2021_);
lean_dec(v___x_2020_);
v_nanosecond_2022_ = lean_ctor_get(v_time_2021_, 3);
lean_inc(v_nanosecond_2022_);
lean_dec_ref(v_time_2021_);
return v_nanosecond_2022_;
}
case 28:
{
lean_object* v___x_2023_; lean_object* v_time_2024_; lean_object* v___x_2025_; 
lean_inc_ref(v_date_1900_);
lean_dec_ref(v_date_1897_);
v___x_2023_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_time_2024_ = lean_ctor_get(v___x_2023_, 1);
lean_inc_ref(v_time_2024_);
lean_dec(v___x_2023_);
v___x_2025_ = l_Std_Time_PlainTime_toNanoseconds(v_time_2024_);
lean_dec_ref(v_time_2024_);
return v___x_2025_;
}
case 29:
{
uint8_t v_presentation_2026_; 
lean_inc_ref(v_timezone_1901_);
lean_dec_ref(v_date_1897_);
v_presentation_2026_ = lean_ctor_get_uint8(v_modifier_1895_, 0);
if (v_presentation_2026_ == 0)
{
lean_object* v___x_2027_; 
lean_dec_ref(v_timezone_1901_);
v___x_2027_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
return v___x_2027_;
}
else
{
lean_object* v_offset_2028_; lean_object* v_name_2029_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
v_offset_2028_ = lean_ctor_get(v_timezone_1901_, 0);
lean_inc(v_offset_2028_);
v_name_2029_ = lean_ctor_get(v_timezone_1901_, 1);
lean_inc_ref(v_name_2029_);
lean_dec_ref(v_timezone_1901_);
v___x_2044_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2045_ = lean_string_utf8_byte_size(v_name_2029_);
v___x_2046_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_2047_ = lean_nat_dec_le(v___x_2046_, v___x_2045_);
if (v___x_2047_ == 0)
{
goto v___jp_2037_;
}
else
{
lean_object* v___x_2048_; uint8_t v___x_2049_; 
v___x_2048_ = lean_unsigned_to_nat(0u);
v___x_2049_ = lean_string_memcmp(v_name_2029_, v___x_2044_, v___x_2048_, v___x_2048_, v___x_2046_);
if (v___x_2049_ == 0)
{
goto v___jp_2037_;
}
else
{
lean_dec_ref(v_name_2029_);
goto v___jp_2030_;
}
}
v___jp_2030_:
{
uint8_t v___x_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; uint8_t v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2031_ = 1;
v___x_2032_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2033_ = 0;
v___x_2034_ = 1;
v___x_2035_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2028_, v___x_2033_, v___x_2034_, v___x_2031_, v___x_2031_);
v___x_2036_ = lean_string_append(v___x_2032_, v___x_2035_);
lean_dec_ref(v___x_2035_);
return v___x_2036_;
}
v___jp_2037_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; uint8_t v___x_2041_; 
v___x_2038_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2039_ = lean_string_utf8_byte_size(v_name_2029_);
v___x_2040_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_2041_ = lean_nat_dec_le(v___x_2040_, v___x_2039_);
if (v___x_2041_ == 0)
{
lean_dec(v_offset_2028_);
return v_name_2029_;
}
else
{
lean_object* v___x_2042_; uint8_t v___x_2043_; 
v___x_2042_ = lean_unsigned_to_nat(0u);
v___x_2043_ = lean_string_memcmp(v_name_2029_, v___x_2038_, v___x_2042_, v___x_2042_, v___x_2040_);
if (v___x_2043_ == 0)
{
lean_dec(v_offset_2028_);
return v_name_2029_;
}
else
{
lean_dec_ref(v_name_2029_);
goto v___jp_2030_;
}
}
}
}
}
case 30:
{
uint8_t v_presentation_2050_; 
lean_inc_ref(v_timezone_1901_);
lean_dec_ref(v_date_1897_);
v_presentation_2050_ = lean_ctor_get_uint8(v_modifier_1895_, 0);
if (v_presentation_2050_ == 0)
{
lean_object* v_offset_2051_; lean_object* v_abbreviation_2052_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v_offset_2051_ = lean_ctor_get(v_timezone_1901_, 0);
lean_inc(v_offset_2051_);
v_abbreviation_2052_ = lean_ctor_get(v_timezone_1901_, 2);
lean_inc_ref(v_abbreviation_2052_);
lean_dec_ref(v_timezone_1901_);
v___x_2067_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2068_ = lean_string_utf8_byte_size(v_abbreviation_2052_);
v___x_2069_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_2070_ = lean_nat_dec_le(v___x_2069_, v___x_2068_);
if (v___x_2070_ == 0)
{
goto v___jp_2060_;
}
else
{
lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2071_ = lean_unsigned_to_nat(0u);
v___x_2072_ = lean_string_memcmp(v_abbreviation_2052_, v___x_2067_, v___x_2071_, v___x_2071_, v___x_2069_);
if (v___x_2072_ == 0)
{
goto v___jp_2060_;
}
else
{
lean_dec_ref(v_abbreviation_2052_);
goto v___jp_2053_;
}
}
v___jp_2053_:
{
uint8_t v___x_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; uint8_t v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2054_ = 1;
v___x_2055_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2056_ = 0;
v___x_2057_ = 1;
v___x_2058_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2051_, v___x_2056_, v___x_2057_, v___x_2054_, v___x_2054_);
v___x_2059_ = lean_string_append(v___x_2055_, v___x_2058_);
lean_dec_ref(v___x_2058_);
return v___x_2059_;
}
v___jp_2060_:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2061_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2062_ = lean_string_utf8_byte_size(v_abbreviation_2052_);
v___x_2063_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_2064_ = lean_nat_dec_le(v___x_2063_, v___x_2062_);
if (v___x_2064_ == 0)
{
lean_dec(v_offset_2051_);
return v_abbreviation_2052_;
}
else
{
lean_object* v___x_2065_; uint8_t v___x_2066_; 
v___x_2065_ = lean_unsigned_to_nat(0u);
v___x_2066_ = lean_string_memcmp(v_abbreviation_2052_, v___x_2061_, v___x_2065_, v___x_2065_, v___x_2063_);
if (v___x_2066_ == 0)
{
lean_dec(v_offset_2051_);
return v_abbreviation_2052_;
}
else
{
lean_dec_ref(v_abbreviation_2052_);
goto v___jp_2053_;
}
}
}
}
else
{
lean_object* v_offset_2073_; lean_object* v_name_2074_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v_offset_2073_ = lean_ctor_get(v_timezone_1901_, 0);
lean_inc(v_offset_2073_);
v_name_2074_ = lean_ctor_get(v_timezone_1901_, 1);
lean_inc_ref(v_name_2074_);
lean_dec_ref(v_timezone_1901_);
v___x_2089_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2090_ = lean_string_utf8_byte_size(v_name_2074_);
v___x_2091_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_2092_ = lean_nat_dec_le(v___x_2091_, v___x_2090_);
if (v___x_2092_ == 0)
{
goto v___jp_2082_;
}
else
{
lean_object* v___x_2093_; uint8_t v___x_2094_; 
v___x_2093_ = lean_unsigned_to_nat(0u);
v___x_2094_ = lean_string_memcmp(v_name_2074_, v___x_2089_, v___x_2093_, v___x_2093_, v___x_2091_);
if (v___x_2094_ == 0)
{
goto v___jp_2082_;
}
else
{
lean_dec_ref(v_name_2074_);
goto v___jp_2075_;
}
}
v___jp_2075_:
{
uint8_t v___x_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2076_ = 1;
v___x_2077_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2078_ = 0;
v___x_2079_ = 1;
v___x_2080_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2073_, v___x_2078_, v___x_2079_, v___x_2076_, v___x_2076_);
v___x_2081_ = lean_string_append(v___x_2077_, v___x_2080_);
lean_dec_ref(v___x_2080_);
return v___x_2081_;
}
v___jp_2082_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2083_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2084_ = lean_string_utf8_byte_size(v_name_2074_);
v___x_2085_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_2086_ = lean_nat_dec_le(v___x_2085_, v___x_2084_);
if (v___x_2086_ == 0)
{
lean_dec(v_offset_2073_);
return v_name_2074_;
}
else
{
lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2088_ = lean_string_memcmp(v_name_2074_, v___x_2083_, v___x_2087_, v___x_2087_, v___x_2085_);
if (v___x_2088_ == 0)
{
lean_dec(v_offset_2073_);
return v_name_2074_;
}
else
{
lean_dec_ref(v_name_2074_);
goto v___jp_2075_;
}
}
}
}
}
case 31:
{
uint8_t v_presentation_2095_; 
lean_inc_ref(v_timezone_1901_);
lean_dec_ref(v_date_1897_);
v_presentation_2095_ = lean_ctor_get_uint8(v_modifier_1895_, 0);
if (v_presentation_2095_ == 0)
{
lean_object* v_offset_2096_; lean_object* v_abbreviation_2097_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; 
v_offset_2096_ = lean_ctor_get(v_timezone_1901_, 0);
lean_inc(v_offset_2096_);
v_abbreviation_2097_ = lean_ctor_get(v_timezone_1901_, 2);
lean_inc_ref(v_abbreviation_2097_);
lean_dec_ref(v_timezone_1901_);
v___x_2112_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2113_ = lean_string_utf8_byte_size(v_abbreviation_2097_);
v___x_2114_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_2115_ = lean_nat_dec_le(v___x_2114_, v___x_2113_);
if (v___x_2115_ == 0)
{
goto v___jp_2105_;
}
else
{
lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2116_ = lean_unsigned_to_nat(0u);
v___x_2117_ = lean_string_memcmp(v_abbreviation_2097_, v___x_2112_, v___x_2116_, v___x_2116_, v___x_2114_);
if (v___x_2117_ == 0)
{
goto v___jp_2105_;
}
else
{
lean_dec_ref(v_abbreviation_2097_);
goto v___jp_2098_;
}
}
v___jp_2098_:
{
uint8_t v___x_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; uint8_t v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2099_ = 1;
v___x_2100_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2101_ = 0;
v___x_2102_ = 1;
v___x_2103_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2096_, v___x_2101_, v___x_2102_, v___x_2099_, v___x_2099_);
v___x_2104_ = lean_string_append(v___x_2100_, v___x_2103_);
lean_dec_ref(v___x_2103_);
return v___x_2104_;
}
v___jp_2105_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; 
v___x_2106_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2107_ = lean_string_utf8_byte_size(v_abbreviation_2097_);
v___x_2108_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_2109_ = lean_nat_dec_le(v___x_2108_, v___x_2107_);
if (v___x_2109_ == 0)
{
lean_dec(v_offset_2096_);
return v_abbreviation_2097_;
}
else
{
lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2110_ = lean_unsigned_to_nat(0u);
v___x_2111_ = lean_string_memcmp(v_abbreviation_2097_, v___x_2106_, v___x_2110_, v___x_2110_, v___x_2108_);
if (v___x_2111_ == 0)
{
lean_dec(v_offset_2096_);
return v_abbreviation_2097_;
}
else
{
lean_dec_ref(v_abbreviation_2097_);
goto v___jp_2098_;
}
}
}
}
else
{
lean_object* v_offset_2118_; lean_object* v_name_2119_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; uint8_t v___x_2137_; 
v_offset_2118_ = lean_ctor_get(v_timezone_1901_, 0);
lean_inc(v_offset_2118_);
v_name_2119_ = lean_ctor_get(v_timezone_1901_, 1);
lean_inc_ref(v_name_2119_);
lean_dec_ref(v_timezone_1901_);
v___x_2134_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2135_ = lean_string_utf8_byte_size(v_name_2119_);
v___x_2136_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__3);
v___x_2137_ = lean_nat_dec_le(v___x_2136_, v___x_2135_);
if (v___x_2137_ == 0)
{
goto v___jp_2127_;
}
else
{
lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2138_ = lean_unsigned_to_nat(0u);
v___x_2139_ = lean_string_memcmp(v_name_2119_, v___x_2134_, v___x_2138_, v___x_2138_, v___x_2136_);
if (v___x_2139_ == 0)
{
goto v___jp_2127_;
}
else
{
lean_dec_ref(v_name_2119_);
goto v___jp_2120_;
}
}
v___jp_2120_:
{
uint8_t v___x_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; uint8_t v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2121_ = 1;
v___x_2122_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2123_ = 0;
v___x_2124_ = 1;
v___x_2125_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2118_, v___x_2123_, v___x_2124_, v___x_2121_, v___x_2121_);
v___x_2126_ = lean_string_append(v___x_2122_, v___x_2125_);
lean_dec_ref(v___x_2125_);
return v___x_2126_;
}
v___jp_2127_:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; 
v___x_2128_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2129_ = lean_string_utf8_byte_size(v_name_2119_);
v___x_2130_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__2);
v___x_2131_ = lean_nat_dec_le(v___x_2130_, v___x_2129_);
if (v___x_2131_ == 0)
{
lean_dec(v_offset_2118_);
return v_name_2119_;
}
else
{
lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2132_ = lean_unsigned_to_nat(0u);
v___x_2133_ = lean_string_memcmp(v_name_2119_, v___x_2128_, v___x_2132_, v___x_2132_, v___x_2130_);
if (v___x_2133_ == 0)
{
lean_dec(v_offset_2118_);
return v_name_2119_;
}
else
{
lean_dec_ref(v_name_2119_);
goto v___jp_2120_;
}
}
}
}
}
default: 
{
lean_object* v_offset_2140_; 
lean_inc_ref(v_timezone_1901_);
lean_dec_ref(v_date_1897_);
v_offset_2140_ = lean_ctor_get(v_timezone_1901_, 0);
lean_inc(v_offset_2140_);
lean_dec_ref(v_timezone_1901_);
return v_offset_2140_;
}
}
v___jp_1902_:
{
lean_object* v___x_1903_; lean_object* v_date_1904_; lean_object* v_year_1905_; 
v___x_1903_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_date_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc_ref(v_date_1904_);
lean_dec(v___x_1903_);
v_year_1905_ = lean_ctor_get(v_date_1904_, 0);
lean_inc(v_year_1905_);
lean_dec_ref(v_date_1904_);
return v_year_1905_;
}
v___jp_1906_:
{
lean_object* v___x_1907_; lean_object* v_date_1908_; lean_object* v_month_1909_; 
v___x_1907_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_date_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc_ref(v_date_1908_);
lean_dec(v___x_1907_);
v_month_1909_ = lean_ctor_get(v_date_1908_, 1);
lean_inc(v_month_1909_);
lean_dec_ref(v_date_1908_);
return v_month_1909_;
}
v___jp_1910_:
{
lean_object* v___x_1911_; lean_object* v_date_1912_; lean_object* v___x_1913_; 
v___x_1911_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_date_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc_ref(v_date_1912_);
lean_dec(v___x_1911_);
v___x_1913_ = l_Std_Time_PlainDate_quarter(v_date_1912_);
lean_dec_ref(v_date_1912_);
return v___x_1913_;
}
v___jp_1914_:
{
lean_object* v___x_1915_; lean_object* v_date_1916_; uint8_t v___x_1917_; lean_object* v___x_1918_; 
v___x_1915_ = lean_thunk_get_own(v_date_1900_);
lean_dec_ref(v_date_1900_);
v_date_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc_ref(v_date_1916_);
lean_dec(v___x_1915_);
v___x_1917_ = l_Std_Time_PlainDate_weekday(v_date_1916_);
v___x_1918_ = lean_box(v___x_1917_);
return v___x_1918_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___boxed(lean_object* v_modifier_2141_, lean_object* v_dateformat_2142_, lean_object* v_date_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(v_modifier_2141_, v_dateformat_2142_, v_date_2143_);
lean_dec_ref(v_dateformat_2142_);
lean_dec_ref(v_modifier_2141_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___lam__0(lean_object* v___x_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2145_);
v___x_2148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___y_2146_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___lam__0(lean_object* v___x_2149_, lean_object* v_b_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_fst_2152_; lean_object* v_snd_2153_; lean_object* v___x_2154_; 
v_fst_2152_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_fst_2152_);
v_snd_2153_ = lean_ctor_get(v___x_2149_, 1);
lean_inc(v_snd_2153_);
lean_dec_ref(v___x_2149_);
lean_inc_ref(v___y_2151_);
v___x_2154_ = lean_apply_1(v_b_2150_, v___y_2151_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_dec(v_snd_2153_);
lean_dec(v_fst_2152_);
lean_dec_ref(v___y_2151_);
return v___x_2154_;
}
else
{
lean_object* v_pos_2155_; lean_object* v_snd_2156_; lean_object* v_snd_2157_; uint8_t v_decide_2158_; 
v_pos_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_pos_2155_);
v_snd_2156_ = lean_ctor_get(v___y_2151_, 1);
lean_inc(v_snd_2156_);
lean_dec_ref(v___y_2151_);
v_snd_2157_ = lean_ctor_get(v_pos_2155_, 1);
v_decide_2158_ = lean_nat_dec_eq(v_snd_2156_, v_snd_2157_);
lean_dec(v_snd_2156_);
if (v_decide_2158_ == 0)
{
lean_dec(v_pos_2155_);
lean_dec(v_snd_2153_);
lean_dec(v_fst_2152_);
return v___x_2154_;
}
else
{
lean_object* v___x_2159_; 
lean_dec_ref_known(v___x_2154_, 2);
v___x_2159_ = l_Std_Internal_Parsec_String_pstring(v_fst_2152_, v_pos_2155_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_pos_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
v_pos_2160_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2167_ == 0)
{
lean_object* v_unused_2168_; 
v_unused_2168_ = lean_ctor_get(v___x_2159_, 1);
lean_dec(v_unused_2168_);
v___x_2162_ = v___x_2159_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_pos_2160_);
lean_dec(v___x_2159_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 1, v_snd_2153_);
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_pos_2160_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_snd_2153_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
else
{
lean_object* v_pos_2169_; lean_object* v_err_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec(v_snd_2153_);
v_pos_2169_ = lean_ctor_get(v___x_2159_, 0);
v_err_2170_ = lean_ctor_get(v___x_2159_, 1);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2159_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_err_2170_);
lean_inc(v_pos_2169_);
lean_dec(v___x_2159_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_pos_2169_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_err_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(lean_object* v_as_2178_, size_t v_i_2179_, size_t v_stop_2180_, lean_object* v_b_2181_, lean_object* v___y_2182_){
_start:
{
uint8_t v___x_2183_; 
v___x_2183_ = lean_usize_dec_eq(v_i_2179_, v_stop_2180_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; lean_object* v___f_2185_; size_t v___x_2186_; size_t v___x_2187_; 
v___x_2184_ = lean_array_uget_borrowed(v_as_2178_, v_i_2179_);
lean_inc(v___x_2184_);
v___f_2185_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2185_, 0, v___x_2184_);
lean_closure_set(v___f_2185_, 1, v_b_2181_);
v___x_2186_ = ((size_t)1ULL);
v___x_2187_ = lean_usize_add(v_i_2179_, v___x_2186_);
v_i_2179_ = v___x_2187_;
v_b_2181_ = v___f_2185_;
goto _start;
}
else
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_apply_1(v_b_2181_, v___y_2182_);
return v___x_2189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___boxed(lean_object* v_as_2190_, lean_object* v_i_2191_, lean_object* v_stop_2192_, lean_object* v_b_2193_, lean_object* v___y_2194_){
_start:
{
size_t v_i_boxed_2195_; size_t v_stop_boxed_2196_; lean_object* v_res_2197_; 
v_i_boxed_2195_ = lean_unbox_usize(v_i_2191_);
lean_dec(v_i_2191_);
v_stop_boxed_2196_ = lean_unbox_usize(v_stop_2192_);
lean_dec(v_stop_2192_);
v_res_2197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_as_2190_, v_i_boxed_2195_, v_stop_boxed_2196_, v_b_2193_, v___y_2194_);
lean_dec_ref(v_as_2190_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(lean_object* v_pairs_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; 
v___x_2205_ = lean_unsigned_to_nat(0u);
v___x_2206_ = lean_array_get_size(v_pairs_2203_);
v___x_2207_ = lean_nat_dec_lt(v___x_2205_, v___x_2206_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__1));
v___x_2209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2209_, 0, v_a_2204_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
return v___x_2209_;
}
else
{
lean_object* v___f_2210_; uint8_t v___x_2211_; 
v___f_2210_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__2));
v___x_2211_ = lean_nat_dec_le(v___x_2206_, v___x_2206_);
if (v___x_2211_ == 0)
{
if (v___x_2207_ == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__1));
v___x_2213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2213_, 0, v_a_2204_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
return v___x_2213_;
}
else
{
size_t v___x_2214_; size_t v___x_2215_; lean_object* v___x_2216_; 
v___x_2214_ = ((size_t)0ULL);
v___x_2215_ = lean_usize_of_nat(v___x_2206_);
v___x_2216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_pairs_2203_, v___x_2214_, v___x_2215_, v___f_2210_, v_a_2204_);
return v___x_2216_;
}
}
else
{
size_t v___x_2217_; size_t v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = ((size_t)0ULL);
v___x_2218_ = lean_usize_of_nat(v___x_2206_);
v___x_2219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_pairs_2203_, v___x_2217_, v___x_2218_, v___f_2210_, v_a_2204_);
return v___x_2219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___boxed(lean_object* v_pairs_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2220_, v_a_2221_);
lean_dec_ref(v_pairs_2220_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols(lean_object* v_00_u03b1_2223_, lean_object* v_pairs_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2224_, v_a_2225_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___boxed(lean_object* v_00_u03b1_2227_, lean_object* v_pairs_2228_, lean_object* v_a_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols(v_00_u03b1_2227_, v_pairs_2228_, v_a_2229_);
lean_dec_ref(v_pairs_2228_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0(lean_object* v_00_u03b1_2231_, lean_object* v_as_2232_, size_t v_i_2233_, size_t v_stop_2234_, lean_object* v_b_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_as_2232_, v_i_2233_, v_stop_2234_, v_b_2235_, v___y_2236_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___boxed(lean_object* v_00_u03b1_2238_, lean_object* v_as_2239_, lean_object* v_i_2240_, lean_object* v_stop_2241_, lean_object* v_b_2242_, lean_object* v___y_2243_){
_start:
{
size_t v_i_boxed_2244_; size_t v_stop_boxed_2245_; lean_object* v_res_2246_; 
v_i_boxed_2244_ = lean_unbox_usize(v_i_2240_);
lean_dec(v_i_2240_);
v_stop_boxed_2245_ = lean_unbox_usize(v_stop_2241_);
lean_dec(v_stop_2241_);
v_res_2246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0(v_00_u03b1_2238_, v_as_2239_, v_i_boxed_2244_, v_stop_boxed_2245_, v_b_2242_, v___y_2243_);
lean_dec_ref(v_as_2239_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(size_t v_sz_2247_, size_t v_i_2248_, lean_object* v_bs_2249_){
_start:
{
uint8_t v___x_2250_; 
v___x_2250_ = lean_usize_dec_lt(v_i_2248_, v_sz_2247_);
if (v___x_2250_ == 0)
{
return v_bs_2249_;
}
else
{
lean_object* v_v_2251_; lean_object* v___x_2252_; lean_object* v_bs_x27_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; size_t v___x_2259_; size_t v___x_2260_; lean_object* v___x_2261_; 
v_v_2251_ = lean_array_uget(v_bs_2249_, v_i_2248_);
v___x_2252_ = lean_unsigned_to_nat(0u);
v_bs_x27_2253_ = lean_array_uset(v_bs_2249_, v_i_2248_, v___x_2252_);
v___x_2254_ = lean_usize_to_nat(v_i_2248_);
v___x_2255_ = lean_nat_to_int(v___x_2254_);
v___x_2256_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2257_ = lean_int_add(v___x_2255_, v___x_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2258_, 0, v_v_2251_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = ((size_t)1ULL);
v___x_2260_ = lean_usize_add(v_i_2248_, v___x_2259_);
v___x_2261_ = lean_array_uset(v_bs_x27_2253_, v_i_2248_, v___x_2258_);
v_i_2248_ = v___x_2260_;
v_bs_2249_ = v___x_2261_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg___boxed(lean_object* v_sz_2263_, lean_object* v_i_2264_, lean_object* v_bs_2265_){
_start:
{
size_t v_sz_boxed_2266_; size_t v_i_boxed_2267_; lean_object* v_res_2268_; 
v_sz_boxed_2266_ = lean_unbox_usize(v_sz_2263_);
lean_dec(v_sz_2263_);
v_i_boxed_2267_ = lean_unbox_usize(v_i_2264_);
lean_dec(v_i_2264_);
v_res_2268_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_boxed_2266_, v_i_boxed_2267_, v_bs_2265_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(lean_object* v_as_2269_, size_t v_sz_2270_, size_t v_i_2271_, lean_object* v_bs_2272_){
_start:
{
uint8_t v___x_2273_; 
v___x_2273_ = lean_usize_dec_lt(v_i_2271_, v_sz_2270_);
if (v___x_2273_ == 0)
{
return v_bs_2272_;
}
else
{
lean_object* v_v_2274_; lean_object* v___x_2275_; lean_object* v_bs_x27_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; size_t v___x_2282_; size_t v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v_v_2274_ = lean_array_uget(v_bs_2272_, v_i_2271_);
v___x_2275_ = lean_unsigned_to_nat(0u);
v_bs_x27_2276_ = lean_array_uset(v_bs_2272_, v_i_2271_, v___x_2275_);
v___x_2277_ = lean_usize_to_nat(v_i_2271_);
v___x_2278_ = lean_nat_to_int(v___x_2277_);
v___x_2279_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2280_ = lean_int_add(v___x_2278_, v___x_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2281_, 0, v_v_2274_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = ((size_t)1ULL);
v___x_2283_ = lean_usize_add(v_i_2271_, v___x_2282_);
v___x_2284_ = lean_array_uset(v_bs_x27_2276_, v_i_2271_, v___x_2281_);
v___x_2285_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_2270_, v___x_2283_, v___x_2284_);
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0___boxed(lean_object* v_as_2286_, lean_object* v_sz_2287_, lean_object* v_i_2288_, lean_object* v_bs_2289_){
_start:
{
size_t v_sz_boxed_2290_; size_t v_i_boxed_2291_; lean_object* v_res_2292_; 
v_sz_boxed_2290_ = lean_unbox_usize(v_sz_2287_);
lean_dec(v_sz_2287_);
v_i_boxed_2291_ = lean_unbox_usize(v_i_2288_);
lean_dec(v_i_2288_);
v_res_2292_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_as_2286_, v_sz_boxed_2290_, v_i_boxed_2291_, v_bs_2289_);
lean_dec_ref(v_as_2286_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(lean_object* v_arr_2293_){
_start:
{
size_t v_sz_2294_; size_t v___x_2295_; lean_object* v___x_2296_; 
v_sz_2294_ = lean_array_size(v_arr_2293_);
v___x_2295_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2293_);
v___x_2296_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_arr_2293_, v_sz_2294_, v___x_2295_, v_arr_2293_);
lean_dec_ref(v_arr_2293_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0(lean_object* v_as_2297_, size_t v_sz_2298_, size_t v_i_2299_, lean_object* v_bs_2300_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_2298_, v_i_2299_, v_bs_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___boxed(lean_object* v_as_2302_, lean_object* v_sz_2303_, lean_object* v_i_2304_, lean_object* v_bs_2305_){
_start:
{
size_t v_sz_boxed_2306_; size_t v_i_boxed_2307_; lean_object* v_res_2308_; 
v_sz_boxed_2306_ = lean_unbox_usize(v_sz_2303_);
lean_dec(v_sz_2303_);
v_i_boxed_2307_ = lean_unbox_usize(v_i_2304_);
lean_dec(v_i_2304_);
v_res_2308_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0(v_as_2302_, v_sz_boxed_2306_, v_i_boxed_2307_, v_bs_2305_);
lean_dec_ref(v_as_2302_);
return v_res_2308_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(lean_object* v_x_2309_){
_start:
{
lean_object* v___x_2310_; uint8_t v___x_2311_; 
v___x_2310_ = lean_unsigned_to_nat(0u);
v___x_2311_ = lean_nat_dec_eq(v_x_2309_, v___x_2310_);
if (v___x_2311_ == 0)
{
lean_object* v___x_2312_; uint8_t v___x_2313_; 
v___x_2312_ = lean_unsigned_to_nat(1u);
v___x_2313_ = lean_nat_dec_eq(v_x_2309_, v___x_2312_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; uint8_t v___x_2315_; 
v___x_2314_ = lean_unsigned_to_nat(2u);
v___x_2315_ = lean_nat_dec_eq(v_x_2309_, v___x_2314_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2316_; uint8_t v___x_2317_; 
v___x_2316_ = lean_unsigned_to_nat(3u);
v___x_2317_ = lean_nat_dec_eq(v_x_2309_, v___x_2316_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___x_2318_ = lean_unsigned_to_nat(4u);
v___x_2319_ = lean_nat_dec_eq(v_x_2309_, v___x_2318_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; uint8_t v___x_2321_; 
v___x_2320_ = lean_unsigned_to_nat(5u);
v___x_2321_ = lean_nat_dec_eq(v_x_2309_, v___x_2320_);
if (v___x_2321_ == 0)
{
uint8_t v___x_2322_; 
v___x_2322_ = 5;
return v___x_2322_;
}
else
{
uint8_t v___x_2323_; 
v___x_2323_ = 4;
return v___x_2323_;
}
}
else
{
uint8_t v___x_2324_; 
v___x_2324_ = 3;
return v___x_2324_;
}
}
else
{
uint8_t v___x_2325_; 
v___x_2325_ = 2;
return v___x_2325_;
}
}
else
{
uint8_t v___x_2326_; 
v___x_2326_ = 1;
return v___x_2326_;
}
}
else
{
uint8_t v___x_2327_; 
v___x_2327_ = 0;
return v___x_2327_;
}
}
else
{
uint8_t v___x_2328_; 
v___x_2328_ = 6;
return v___x_2328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex___boxed(lean_object* v_x_2329_){
_start:
{
uint8_t v_res_2330_; lean_object* v_r_2331_; 
v_res_2330_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(v_x_2329_);
lean_dec(v_x_2329_);
v_r_2331_ = lean_box(v_res_2330_);
return v_r_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(size_t v_sz_2332_, size_t v_i_2333_, lean_object* v_bs_2334_){
_start:
{
uint8_t v___x_2335_; 
v___x_2335_ = lean_usize_dec_lt(v_i_2333_, v_sz_2332_);
if (v___x_2335_ == 0)
{
return v_bs_2334_;
}
else
{
lean_object* v_v_2336_; lean_object* v___x_2337_; lean_object* v_bs_x27_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; size_t v___x_2346_; size_t v___x_2347_; lean_object* v___x_2348_; 
v_v_2336_ = lean_array_uget(v_bs_2334_, v_i_2333_);
v___x_2337_ = lean_unsigned_to_nat(0u);
v_bs_x27_2338_ = lean_array_uset(v_bs_2334_, v_i_2333_, v___x_2337_);
v___x_2339_ = lean_usize_to_nat(v_i_2333_);
v___x_2340_ = lean_nat_to_int(v___x_2339_);
v___x_2341_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2342_ = lean_int_add(v___x_2340_, v___x_2341_);
lean_dec(v___x_2340_);
v___x_2343_ = l_Std_Time_Weekday_ofOrdinal(v___x_2342_);
lean_dec(v___x_2342_);
v___x_2344_ = lean_box(v___x_2343_);
v___x_2345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2345_, 0, v_v_2336_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
v___x_2346_ = ((size_t)1ULL);
v___x_2347_ = lean_usize_add(v_i_2333_, v___x_2346_);
v___x_2348_ = lean_array_uset(v_bs_x27_2338_, v_i_2333_, v___x_2345_);
v_i_2333_ = v___x_2347_;
v_bs_2334_ = v___x_2348_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg___boxed(lean_object* v_sz_2350_, lean_object* v_i_2351_, lean_object* v_bs_2352_){
_start:
{
size_t v_sz_boxed_2353_; size_t v_i_boxed_2354_; lean_object* v_res_2355_; 
v_sz_boxed_2353_ = lean_unbox_usize(v_sz_2350_);
lean_dec(v_sz_2350_);
v_i_boxed_2354_ = lean_unbox_usize(v_i_2351_);
lean_dec(v_i_2351_);
v_res_2355_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_boxed_2353_, v_i_boxed_2354_, v_bs_2352_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(lean_object* v_as_2356_, size_t v_sz_2357_, size_t v_i_2358_, lean_object* v_bs_2359_){
_start:
{
uint8_t v___x_2360_; 
v___x_2360_ = lean_usize_dec_lt(v_i_2358_, v_sz_2357_);
if (v___x_2360_ == 0)
{
return v_bs_2359_;
}
else
{
lean_object* v_v_2361_; lean_object* v___x_2362_; lean_object* v_bs_x27_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; uint8_t v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; size_t v___x_2371_; size_t v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v_v_2361_ = lean_array_uget(v_bs_2359_, v_i_2358_);
v___x_2362_ = lean_unsigned_to_nat(0u);
v_bs_x27_2363_ = lean_array_uset(v_bs_2359_, v_i_2358_, v___x_2362_);
v___x_2364_ = lean_usize_to_nat(v_i_2358_);
v___x_2365_ = lean_nat_to_int(v___x_2364_);
v___x_2366_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2367_ = lean_int_add(v___x_2365_, v___x_2366_);
lean_dec(v___x_2365_);
v___x_2368_ = l_Std_Time_Weekday_ofOrdinal(v___x_2367_);
lean_dec(v___x_2367_);
v___x_2369_ = lean_box(v___x_2368_);
v___x_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2370_, 0, v_v_2361_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
v___x_2371_ = ((size_t)1ULL);
v___x_2372_ = lean_usize_add(v_i_2358_, v___x_2371_);
v___x_2373_ = lean_array_uset(v_bs_x27_2363_, v_i_2358_, v___x_2370_);
v___x_2374_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_2357_, v___x_2372_, v___x_2373_);
return v___x_2374_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0___boxed(lean_object* v_as_2375_, lean_object* v_sz_2376_, lean_object* v_i_2377_, lean_object* v_bs_2378_){
_start:
{
size_t v_sz_boxed_2379_; size_t v_i_boxed_2380_; lean_object* v_res_2381_; 
v_sz_boxed_2379_ = lean_unbox_usize(v_sz_2376_);
lean_dec(v_sz_2376_);
v_i_boxed_2380_ = lean_unbox_usize(v_i_2377_);
lean_dec(v_i_2377_);
v_res_2381_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(v_as_2375_, v_sz_boxed_2379_, v_i_boxed_2380_, v_bs_2378_);
lean_dec_ref(v_as_2375_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(lean_object* v_arr_2382_){
_start:
{
size_t v_sz_2383_; size_t v___x_2384_; lean_object* v___x_2385_; 
v_sz_2383_ = lean_array_size(v_arr_2382_);
v___x_2384_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2382_);
v___x_2385_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(v_arr_2382_, v_sz_2383_, v___x_2384_, v_arr_2382_);
lean_dec_ref(v_arr_2382_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0(lean_object* v_as_2386_, size_t v_sz_2387_, size_t v_i_2388_, lean_object* v_bs_2389_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_2387_, v_i_2388_, v_bs_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___boxed(lean_object* v_as_2391_, lean_object* v_sz_2392_, lean_object* v_i_2393_, lean_object* v_bs_2394_){
_start:
{
size_t v_sz_boxed_2395_; size_t v_i_boxed_2396_; lean_object* v_res_2397_; 
v_sz_boxed_2395_ = lean_unbox_usize(v_sz_2392_);
lean_dec(v_sz_2392_);
v_i_boxed_2396_ = lean_unbox_usize(v_i_2393_);
lean_dec(v_i_2393_);
v_res_2397_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0(v_as_2391_, v_sz_boxed_2395_, v_i_boxed_2396_, v_bs_2394_);
lean_dec_ref(v_as_2391_);
return v_res_2397_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(lean_object* v_x_2398_){
_start:
{
lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2399_ = lean_unsigned_to_nat(0u);
v___x_2400_ = lean_nat_dec_eq(v_x_2398_, v___x_2399_);
if (v___x_2400_ == 0)
{
uint8_t v___x_2401_; 
v___x_2401_ = 1;
return v___x_2401_;
}
else
{
uint8_t v___x_2402_; 
v___x_2402_ = 0;
return v___x_2402_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex___boxed(lean_object* v_x_2403_){
_start:
{
uint8_t v_res_2404_; lean_object* v_r_2405_; 
v_res_2404_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(v_x_2403_);
lean_dec(v_x_2403_);
v_r_2405_ = lean_box(v_res_2404_);
return v_r_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(size_t v_sz_2406_, size_t v_i_2407_, lean_object* v_bs_2408_){
_start:
{
uint8_t v___x_2409_; 
v___x_2409_ = lean_usize_dec_lt(v_i_2407_, v_sz_2406_);
if (v___x_2409_ == 0)
{
return v_bs_2408_;
}
else
{
lean_object* v_v_2410_; lean_object* v___x_2411_; lean_object* v_bs_x27_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; size_t v___x_2417_; size_t v___x_2418_; lean_object* v___x_2419_; 
v_v_2410_ = lean_array_uget(v_bs_2408_, v_i_2407_);
v___x_2411_ = lean_unsigned_to_nat(0u);
v_bs_x27_2412_ = lean_array_uset(v_bs_2408_, v_i_2407_, v___x_2411_);
v___x_2413_ = lean_usize_to_nat(v_i_2407_);
v___x_2414_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(v___x_2413_);
lean_dec(v___x_2413_);
v___x_2415_ = lean_box(v___x_2414_);
v___x_2416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2416_, 0, v_v_2410_);
lean_ctor_set(v___x_2416_, 1, v___x_2415_);
v___x_2417_ = ((size_t)1ULL);
v___x_2418_ = lean_usize_add(v_i_2407_, v___x_2417_);
v___x_2419_ = lean_array_uset(v_bs_x27_2412_, v_i_2407_, v___x_2416_);
v_i_2407_ = v___x_2418_;
v_bs_2408_ = v___x_2419_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg___boxed(lean_object* v_sz_2421_, lean_object* v_i_2422_, lean_object* v_bs_2423_){
_start:
{
size_t v_sz_boxed_2424_; size_t v_i_boxed_2425_; lean_object* v_res_2426_; 
v_sz_boxed_2424_ = lean_unbox_usize(v_sz_2421_);
lean_dec(v_sz_2421_);
v_i_boxed_2425_ = lean_unbox_usize(v_i_2422_);
lean_dec(v_i_2422_);
v_res_2426_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_boxed_2424_, v_i_boxed_2425_, v_bs_2423_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(lean_object* v_arr_2427_){
_start:
{
size_t v_sz_2428_; size_t v___x_2429_; lean_object* v___x_2430_; 
v_sz_2428_ = lean_array_size(v_arr_2427_);
v___x_2429_ = ((size_t)0ULL);
v___x_2430_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_2428_, v___x_2429_, v_arr_2427_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0(lean_object* v_as_2431_, size_t v_sz_2432_, size_t v_i_2433_, lean_object* v_bs_2434_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_2432_, v_i_2433_, v_bs_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___boxed(lean_object* v_as_2436_, lean_object* v_sz_2437_, lean_object* v_i_2438_, lean_object* v_bs_2439_){
_start:
{
size_t v_sz_boxed_2440_; size_t v_i_boxed_2441_; lean_object* v_res_2442_; 
v_sz_boxed_2440_ = lean_unbox_usize(v_sz_2437_);
lean_dec(v_sz_2437_);
v_i_boxed_2441_ = lean_unbox_usize(v_i_2438_);
lean_dec(v_i_2438_);
v_res_2442_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0(v_as_2436_, v_sz_boxed_2440_, v_i_boxed_2441_, v_bs_2439_);
lean_dec_ref(v_as_2436_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(lean_object* v_arr_2443_){
_start:
{
size_t v_sz_2444_; size_t v___x_2445_; lean_object* v___x_2446_; 
v_sz_2444_ = lean_array_size(v_arr_2443_);
v___x_2445_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2443_);
v___x_2446_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_arr_2443_, v_sz_2444_, v___x_2445_, v_arr_2443_);
lean_dec_ref(v_arr_2443_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(lean_object* v_symbols_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_monthLong_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v_monthLong_2449_ = lean_ctor_get(v_symbols_2447_, 0);
lean_inc_ref(v_monthLong_2449_);
lean_dec_ref(v_symbols_2447_);
v___x_2450_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthLong_2449_);
v___x_2451_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2450_, v_a_2448_);
lean_dec_ref(v___x_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseMonthShort(lean_object* v_symbols_2452_, lean_object* v_a_2453_){
_start:
{
lean_object* v_monthShort_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v_monthShort_2454_ = lean_ctor_get(v_symbols_2452_, 1);
lean_inc_ref(v_monthShort_2454_);
lean_dec_ref(v_symbols_2452_);
v___x_2455_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthShort_2454_);
v___x_2456_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2455_, v_a_2453_);
lean_dec_ref(v___x_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(lean_object* v_symbols_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v_monthNarrow_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v_monthNarrow_2459_ = lean_ctor_get(v_symbols_2457_, 2);
lean_inc_ref(v_monthNarrow_2459_);
lean_dec_ref(v_symbols_2457_);
v___x_2460_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthNarrow_2459_);
v___x_2461_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2460_, v_a_2458_);
lean_dec_ref(v___x_2460_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(lean_object* v_symbols_2462_, lean_object* v_a_2463_){
_start:
{
lean_object* v_weekdayLong_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v_weekdayLong_2464_ = lean_ctor_get(v_symbols_2462_, 3);
lean_inc_ref(v_weekdayLong_2464_);
lean_dec_ref(v_symbols_2462_);
v___x_2465_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayLong_2464_);
v___x_2466_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2465_, v_a_2463_);
lean_dec_ref(v___x_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(lean_object* v_symbols_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v_weekdayShort_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v_weekdayShort_2469_ = lean_ctor_get(v_symbols_2467_, 4);
lean_inc_ref(v_weekdayShort_2469_);
lean_dec_ref(v_symbols_2467_);
v___x_2470_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayShort_2469_);
v___x_2471_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2470_, v_a_2468_);
lean_dec_ref(v___x_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(lean_object* v_symbols_2472_, lean_object* v_a_2473_){
_start:
{
lean_object* v_weekdayNarrow_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v_weekdayNarrow_2474_ = lean_ctor_get(v_symbols_2472_, 5);
lean_inc_ref(v_weekdayNarrow_2474_);
lean_dec_ref(v_symbols_2472_);
v___x_2475_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayNarrow_2474_);
v___x_2476_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2475_, v_a_2473_);
lean_dec_ref(v___x_2475_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(lean_object* v_symbols_2477_, lean_object* v_a_2478_){
_start:
{
lean_object* v_weekdayTwoLetter_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_weekdayTwoLetter_2479_ = lean_ctor_get(v_symbols_2477_, 6);
lean_inc_ref(v_weekdayTwoLetter_2479_);
lean_dec_ref(v_symbols_2477_);
v___x_2480_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayTwoLetter_2479_);
v___x_2481_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2480_, v_a_2478_);
lean_dec_ref(v___x_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraShort(lean_object* v_symbols_2482_, lean_object* v_a_2483_){
_start:
{
lean_object* v_eraShort_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v_eraShort_2484_ = lean_ctor_get(v_symbols_2482_, 7);
lean_inc_ref(v_eraShort_2484_);
lean_dec_ref(v_symbols_2482_);
v___x_2485_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraShort_2484_);
v___x_2486_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2485_, v_a_2483_);
lean_dec_ref(v___x_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraLong(lean_object* v_symbols_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v_eraLong_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v_eraLong_2489_ = lean_ctor_get(v_symbols_2487_, 8);
lean_inc_ref(v_eraLong_2489_);
lean_dec_ref(v_symbols_2487_);
v___x_2490_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraLong_2489_);
v___x_2491_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2490_, v_a_2488_);
lean_dec_ref(v___x_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraNarrow(lean_object* v_symbols_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v_eraNarrow_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v_eraNarrow_2494_ = lean_ctor_get(v_symbols_2492_, 9);
lean_inc_ref(v_eraNarrow_2494_);
lean_dec_ref(v_symbols_2492_);
v___x_2495_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraNarrow_2494_);
v___x_2496_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2495_, v_a_2493_);
lean_dec_ref(v___x_2495_);
return v___x_2496_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0(void){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = lean_unsigned_to_nat(3u);
v___x_2498_ = lean_nat_to_int(v___x_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber(lean_object* v_a_2499_){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__0));
lean_inc_ref(v_a_2499_);
v___x_2501_ = l_Std_Internal_Parsec_String_pstring(v___x_2500_, v_a_2499_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_pos_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2510_; 
lean_dec_ref(v_a_2499_);
v_pos_2502_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2510_ == 0)
{
lean_object* v_unused_2511_; 
v_unused_2511_ = lean_ctor_get(v___x_2501_, 1);
lean_dec(v_unused_2511_);
v___x_2504_ = v___x_2501_;
v_isShared_2505_ = v_isSharedCheck_2510_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_pos_2502_);
lean_dec(v___x_2501_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2510_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2506_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 1, v___x_2506_);
v___x_2508_ = v___x_2504_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_pos_2502_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v___x_2506_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
else
{
lean_object* v_pos_2512_; lean_object* v_err_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2590_; 
v_pos_2512_ = lean_ctor_get(v___x_2501_, 0);
v_err_2513_ = lean_ctor_get(v___x_2501_, 1);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2515_ = v___x_2501_;
v_isShared_2516_ = v_isSharedCheck_2590_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_err_2513_);
lean_inc(v_pos_2512_);
lean_dec(v___x_2501_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2590_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v_snd_2517_; lean_object* v_snd_2518_; uint8_t v_decide_2519_; 
v_snd_2517_ = lean_ctor_get(v_a_2499_, 1);
lean_inc(v_snd_2517_);
lean_dec_ref(v_a_2499_);
v_snd_2518_ = lean_ctor_get(v_pos_2512_, 1);
v_decide_2519_ = lean_nat_dec_eq(v_snd_2517_, v_snd_2518_);
lean_dec(v_snd_2517_);
if (v_decide_2519_ == 0)
{
lean_object* v___x_2521_; 
if (v_isShared_2516_ == 0)
{
v___x_2521_ = v___x_2515_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_pos_2512_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_err_2513_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
else
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
lean_inc(v_snd_2518_);
lean_del_object(v___x_2515_);
lean_dec(v_err_2513_);
v___x_2523_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__1));
v___x_2524_ = l_Std_Internal_Parsec_String_pstring(v___x_2523_, v_pos_2512_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_pos_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2533_; 
lean_dec(v_snd_2518_);
v_pos_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2533_ == 0)
{
lean_object* v_unused_2534_; 
v_unused_2534_ = lean_ctor_get(v___x_2524_, 1);
lean_dec(v_unused_2534_);
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2533_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_pos_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2533_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; lean_object* v___x_2531_; 
v___x_2529_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__3, &l_Std_Time_instReprFormatPart_repr___closed__3_once, _init_l_Std_Time_instReprFormatPart_repr___closed__3);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 1, v___x_2529_);
v___x_2531_ = v___x_2527_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_pos_2525_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___x_2529_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
else
{
lean_object* v_pos_2535_; lean_object* v_err_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2589_; 
v_pos_2535_ = lean_ctor_get(v___x_2524_, 0);
v_err_2536_ = lean_ctor_get(v___x_2524_, 1);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2538_ = v___x_2524_;
v_isShared_2539_ = v_isSharedCheck_2589_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_err_2536_);
lean_inc(v_pos_2535_);
lean_dec(v___x_2524_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2589_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v_snd_2540_; uint8_t v_decide_2541_; 
v_snd_2540_ = lean_ctor_get(v_pos_2535_, 1);
v_decide_2541_ = lean_nat_dec_eq(v_snd_2518_, v_snd_2540_);
lean_dec(v_snd_2518_);
if (v_decide_2541_ == 0)
{
lean_object* v___x_2543_; 
if (v_isShared_2539_ == 0)
{
v___x_2543_ = v___x_2538_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_pos_2535_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v_err_2536_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
else
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
lean_inc(v_snd_2540_);
lean_del_object(v___x_2538_);
lean_dec(v_err_2536_);
v___x_2545_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__2));
v___x_2546_ = l_Std_Internal_Parsec_String_pstring(v___x_2545_, v_pos_2535_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_pos_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2555_; 
lean_dec(v_snd_2540_);
v_pos_2547_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2555_ == 0)
{
lean_object* v_unused_2556_; 
v_unused_2556_ = lean_ctor_get(v___x_2546_, 1);
lean_dec(v_unused_2556_);
v___x_2549_ = v___x_2546_;
v_isShared_2550_ = v_isSharedCheck_2555_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_pos_2547_);
lean_dec(v___x_2546_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2555_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2551_; lean_object* v___x_2553_; 
v___x_2551_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 1, v___x_2551_);
v___x_2553_ = v___x_2549_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_pos_2547_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
else
{
lean_object* v_pos_2557_; lean_object* v_err_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2588_; 
v_pos_2557_ = lean_ctor_get(v___x_2546_, 0);
v_err_2558_ = lean_ctor_get(v___x_2546_, 1);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2560_ = v___x_2546_;
v_isShared_2561_ = v_isSharedCheck_2588_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_err_2558_);
lean_inc(v_pos_2557_);
lean_dec(v___x_2546_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2588_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v_snd_2562_; uint8_t v_decide_2563_; 
v_snd_2562_ = lean_ctor_get(v_pos_2557_, 1);
v_decide_2563_ = lean_nat_dec_eq(v_snd_2540_, v_snd_2562_);
lean_dec(v_snd_2540_);
if (v_decide_2563_ == 0)
{
lean_object* v___x_2565_; 
if (v_isShared_2561_ == 0)
{
v___x_2565_ = v___x_2560_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_pos_2557_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v_err_2558_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
else
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
lean_del_object(v___x_2560_);
lean_dec(v_err_2558_);
v___x_2567_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__3));
v___x_2568_ = l_Std_Internal_Parsec_String_pstring(v___x_2567_, v_pos_2557_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_pos_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2577_; 
v_pos_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2577_ == 0)
{
lean_object* v_unused_2578_; 
v_unused_2578_ = lean_ctor_get(v___x_2568_, 1);
lean_dec(v_unused_2578_);
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2577_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_pos_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2577_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2573_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 1, v___x_2573_);
v___x_2575_ = v___x_2571_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_pos_2569_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v___x_2573_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
else
{
lean_object* v_pos_2579_; lean_object* v_err_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
v_pos_2579_ = lean_ctor_get(v___x_2568_, 0);
v_err_2580_ = lean_ctor_get(v___x_2568_, 1);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2568_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_err_2580_);
lean_inc(v_pos_2579_);
lean_dec(v___x_2568_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_pos_2579_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_err_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(lean_object* v_symbols_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v_quarterLong_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v_quarterLong_2593_ = lean_ctor_get(v_symbols_2591_, 11);
lean_inc_ref(v_quarterLong_2593_);
lean_dec_ref(v_symbols_2591_);
v___x_2594_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterLong_2593_);
v___x_2595_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2594_, v_a_2592_);
lean_dec_ref(v___x_2594_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(lean_object* v_symbols_2596_, lean_object* v_a_2597_){
_start:
{
lean_object* v_quarterShort_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v_quarterShort_2598_ = lean_ctor_get(v_symbols_2596_, 10);
lean_inc_ref(v_quarterShort_2598_);
lean_dec_ref(v_symbols_2596_);
v___x_2599_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterShort_2598_);
v___x_2600_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2599_, v_a_2597_);
lean_dec_ref(v___x_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(lean_object* v_symbols_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v_quarterNarrow_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v_quarterNarrow_2603_ = lean_ctor_get(v_symbols_2601_, 12);
lean_inc_ref(v_quarterNarrow_2603_);
lean_dec_ref(v_symbols_2601_);
v___x_2604_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterNarrow_2603_);
v___x_2605_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2604_, v_a_2602_);
lean_dec_ref(v___x_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerShort(lean_object* v_symbols_2606_, lean_object* v_a_2607_){
_start:
{
lean_object* v_amShort_2608_; lean_object* v_pmShort_2609_; lean_object* v___x_2610_; 
v_amShort_2608_ = lean_ctor_get(v_symbols_2606_, 13);
lean_inc_ref(v_amShort_2608_);
v_pmShort_2609_ = lean_ctor_get(v_symbols_2606_, 14);
lean_inc_ref(v_pmShort_2609_);
lean_dec_ref(v_symbols_2606_);
lean_inc_ref(v_a_2607_);
v___x_2610_ = l_Std_Internal_Parsec_String_pstring(v_amShort_2608_, v_a_2607_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_pos_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2620_; 
lean_dec_ref(v_pmShort_2609_);
lean_dec_ref(v_a_2607_);
v_pos_2611_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2620_ == 0)
{
lean_object* v_unused_2621_; 
v_unused_2621_ = lean_ctor_get(v___x_2610_, 1);
lean_dec(v_unused_2621_);
v___x_2613_ = v___x_2610_;
v_isShared_2614_ = v_isSharedCheck_2620_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_pos_2611_);
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2620_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
uint8_t v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2618_; 
v___x_2615_ = 0;
v___x_2616_ = lean_box(v___x_2615_);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 1, v___x_2616_);
v___x_2618_ = v___x_2613_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_pos_2611_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
else
{
lean_object* v_pos_2622_; lean_object* v_err_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2654_; 
v_pos_2622_ = lean_ctor_get(v___x_2610_, 0);
v_err_2623_ = lean_ctor_get(v___x_2610_, 1);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2625_ = v___x_2610_;
v_isShared_2626_ = v_isSharedCheck_2654_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_err_2623_);
lean_inc(v_pos_2622_);
lean_dec(v___x_2610_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2654_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v_snd_2627_; lean_object* v_snd_2628_; uint8_t v_decide_2629_; 
v_snd_2627_ = lean_ctor_get(v_a_2607_, 1);
lean_inc(v_snd_2627_);
lean_dec_ref(v_a_2607_);
v_snd_2628_ = lean_ctor_get(v_pos_2622_, 1);
v_decide_2629_ = lean_nat_dec_eq(v_snd_2627_, v_snd_2628_);
lean_dec(v_snd_2627_);
if (v_decide_2629_ == 0)
{
lean_object* v___x_2631_; 
lean_dec_ref(v_pmShort_2609_);
if (v_isShared_2626_ == 0)
{
v___x_2631_ = v___x_2625_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_pos_2622_);
lean_ctor_set(v_reuseFailAlloc_2632_, 1, v_err_2623_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
else
{
lean_object* v___x_2633_; 
lean_del_object(v___x_2625_);
lean_dec(v_err_2623_);
v___x_2633_ = l_Std_Internal_Parsec_String_pstring(v_pmShort_2609_, v_pos_2622_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_pos_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2643_; 
v_pos_2634_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2643_ == 0)
{
lean_object* v_unused_2644_; 
v_unused_2644_ = lean_ctor_get(v___x_2633_, 1);
lean_dec(v_unused_2644_);
v___x_2636_ = v___x_2633_;
v_isShared_2637_ = v_isSharedCheck_2643_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_pos_2634_);
lean_dec(v___x_2633_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2643_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
uint8_t v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2638_ = 1;
v___x_2639_ = lean_box(v___x_2638_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 1, v___x_2639_);
v___x_2641_ = v___x_2636_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_pos_2634_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
else
{
lean_object* v_pos_2645_; lean_object* v_err_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
v_pos_2645_ = lean_ctor_get(v___x_2633_, 0);
v_err_2646_ = lean_ctor_get(v___x_2633_, 1);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2633_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_err_2646_);
lean_inc(v_pos_2645_);
lean_dec(v___x_2633_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_pos_2645_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v_err_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerLong(lean_object* v_symbols_2655_, lean_object* v_a_2656_){
_start:
{
lean_object* v_amLong_2657_; lean_object* v_pmLong_2658_; lean_object* v___x_2659_; 
v_amLong_2657_ = lean_ctor_get(v_symbols_2655_, 15);
lean_inc_ref(v_amLong_2657_);
v_pmLong_2658_ = lean_ctor_get(v_symbols_2655_, 16);
lean_inc_ref(v_pmLong_2658_);
lean_dec_ref(v_symbols_2655_);
lean_inc_ref(v_a_2656_);
v___x_2659_ = l_Std_Internal_Parsec_String_pstring(v_amLong_2657_, v_a_2656_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_pos_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2669_; 
lean_dec_ref(v_pmLong_2658_);
lean_dec_ref(v_a_2656_);
v_pos_2660_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2669_ == 0)
{
lean_object* v_unused_2670_; 
v_unused_2670_ = lean_ctor_get(v___x_2659_, 1);
lean_dec(v_unused_2670_);
v___x_2662_ = v___x_2659_;
v_isShared_2663_ = v_isSharedCheck_2669_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_pos_2660_);
lean_dec(v___x_2659_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2669_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
uint8_t v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2664_ = 0;
v___x_2665_ = lean_box(v___x_2664_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 1, v___x_2665_);
v___x_2667_ = v___x_2662_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_pos_2660_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
else
{
lean_object* v_pos_2671_; lean_object* v_err_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2703_; 
v_pos_2671_ = lean_ctor_get(v___x_2659_, 0);
v_err_2672_ = lean_ctor_get(v___x_2659_, 1);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2674_ = v___x_2659_;
v_isShared_2675_ = v_isSharedCheck_2703_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_err_2672_);
lean_inc(v_pos_2671_);
lean_dec(v___x_2659_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2703_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v_snd_2676_; lean_object* v_snd_2677_; uint8_t v_decide_2678_; 
v_snd_2676_ = lean_ctor_get(v_a_2656_, 1);
lean_inc(v_snd_2676_);
lean_dec_ref(v_a_2656_);
v_snd_2677_ = lean_ctor_get(v_pos_2671_, 1);
v_decide_2678_ = lean_nat_dec_eq(v_snd_2676_, v_snd_2677_);
lean_dec(v_snd_2676_);
if (v_decide_2678_ == 0)
{
lean_object* v___x_2680_; 
lean_dec_ref(v_pmLong_2658_);
if (v_isShared_2675_ == 0)
{
v___x_2680_ = v___x_2674_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_pos_2671_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v_err_2672_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
else
{
lean_object* v___x_2682_; 
lean_del_object(v___x_2674_);
lean_dec(v_err_2672_);
v___x_2682_ = l_Std_Internal_Parsec_String_pstring(v_pmLong_2658_, v_pos_2671_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_pos_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2692_; 
v_pos_2683_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2692_ == 0)
{
lean_object* v_unused_2693_; 
v_unused_2693_ = lean_ctor_get(v___x_2682_, 1);
lean_dec(v_unused_2693_);
v___x_2685_ = v___x_2682_;
v_isShared_2686_ = v_isSharedCheck_2692_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_pos_2683_);
lean_dec(v___x_2682_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2692_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
uint8_t v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2687_ = 1;
v___x_2688_ = lean_box(v___x_2687_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 1, v___x_2688_);
v___x_2690_ = v___x_2685_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_pos_2683_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v___x_2688_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
else
{
lean_object* v_pos_2694_; lean_object* v_err_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
v_pos_2694_ = lean_ctor_get(v___x_2682_, 0);
v_err_2695_ = lean_ctor_get(v___x_2682_, 1);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2682_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_err_2695_);
lean_inc(v_pos_2694_);
lean_dec(v___x_2682_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_pos_2694_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_err_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerNarrow(lean_object* v_symbols_2704_, lean_object* v_a_2705_){
_start:
{
lean_object* v_amNarrow_2706_; lean_object* v_pmNarrow_2707_; lean_object* v___x_2708_; 
v_amNarrow_2706_ = lean_ctor_get(v_symbols_2704_, 17);
lean_inc_ref(v_amNarrow_2706_);
v_pmNarrow_2707_ = lean_ctor_get(v_symbols_2704_, 18);
lean_inc_ref(v_pmNarrow_2707_);
lean_dec_ref(v_symbols_2704_);
lean_inc_ref(v_a_2705_);
v___x_2708_ = l_Std_Internal_Parsec_String_pstring(v_amNarrow_2706_, v_a_2705_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_pos_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2718_; 
lean_dec_ref(v_pmNarrow_2707_);
lean_dec_ref(v_a_2705_);
v_pos_2709_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2718_ == 0)
{
lean_object* v_unused_2719_; 
v_unused_2719_ = lean_ctor_get(v___x_2708_, 1);
lean_dec(v_unused_2719_);
v___x_2711_ = v___x_2708_;
v_isShared_2712_ = v_isSharedCheck_2718_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_pos_2709_);
lean_dec(v___x_2708_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2718_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
uint8_t v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2716_; 
v___x_2713_ = 0;
v___x_2714_ = lean_box(v___x_2713_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 1, v___x_2714_);
v___x_2716_ = v___x_2711_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_pos_2709_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
else
{
lean_object* v_pos_2720_; lean_object* v_err_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2752_; 
v_pos_2720_ = lean_ctor_get(v___x_2708_, 0);
v_err_2721_ = lean_ctor_get(v___x_2708_, 1);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2723_ = v___x_2708_;
v_isShared_2724_ = v_isSharedCheck_2752_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_err_2721_);
lean_inc(v_pos_2720_);
lean_dec(v___x_2708_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2752_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v_snd_2725_; lean_object* v_snd_2726_; uint8_t v_decide_2727_; 
v_snd_2725_ = lean_ctor_get(v_a_2705_, 1);
lean_inc(v_snd_2725_);
lean_dec_ref(v_a_2705_);
v_snd_2726_ = lean_ctor_get(v_pos_2720_, 1);
v_decide_2727_ = lean_nat_dec_eq(v_snd_2725_, v_snd_2726_);
lean_dec(v_snd_2725_);
if (v_decide_2727_ == 0)
{
lean_object* v___x_2729_; 
lean_dec_ref(v_pmNarrow_2707_);
if (v_isShared_2724_ == 0)
{
v___x_2729_ = v___x_2723_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_pos_2720_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_err_2721_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
else
{
lean_object* v___x_2731_; 
lean_del_object(v___x_2723_);
lean_dec(v_err_2721_);
v___x_2731_ = l_Std_Internal_Parsec_String_pstring(v_pmNarrow_2707_, v_pos_2720_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_pos_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2741_; 
v_pos_2732_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2741_ == 0)
{
lean_object* v_unused_2742_; 
v_unused_2742_ = lean_ctor_get(v___x_2731_, 1);
lean_dec(v_unused_2742_);
v___x_2734_ = v___x_2731_;
v_isShared_2735_ = v_isSharedCheck_2741_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_pos_2732_);
lean_dec(v___x_2731_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2741_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
uint8_t v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2739_; 
v___x_2736_ = 1;
v___x_2737_ = lean_box(v___x_2736_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 1, v___x_2737_);
v___x_2739_ = v___x_2734_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_pos_2732_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v___x_2737_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
else
{
lean_object* v_pos_2743_; lean_object* v_err_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
v_pos_2743_ = lean_ctor_get(v___x_2731_, 0);
v_err_2744_ = lean_ctor_get(v___x_2731_, 1);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2731_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_err_2744_);
lean_inc(v_pos_2743_);
lean_dec(v___x_2731_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_pos_2743_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v_err_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(lean_object* v_dp_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v_am_2755_; lean_object* v_pm_2756_; lean_object* v_noon_2757_; lean_object* v_midnight_2758_; lean_object* v___x_2759_; 
v_am_2755_ = lean_ctor_get(v_dp_2753_, 0);
lean_inc_ref(v_am_2755_);
v_pm_2756_ = lean_ctor_get(v_dp_2753_, 1);
lean_inc_ref(v_pm_2756_);
v_noon_2757_ = lean_ctor_get(v_dp_2753_, 2);
lean_inc_ref(v_noon_2757_);
v_midnight_2758_ = lean_ctor_get(v_dp_2753_, 3);
lean_inc_ref(v_midnight_2758_);
lean_dec_ref(v_dp_2753_);
lean_inc_ref(v_a_2754_);
v___x_2759_ = l_Std_Internal_Parsec_String_pstring(v_midnight_2758_, v_a_2754_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_pos_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2769_; 
lean_dec_ref(v_noon_2757_);
lean_dec_ref(v_pm_2756_);
lean_dec_ref(v_am_2755_);
lean_dec_ref(v_a_2754_);
v_pos_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2769_ == 0)
{
lean_object* v_unused_2770_; 
v_unused_2770_ = lean_ctor_get(v___x_2759_, 1);
lean_dec(v_unused_2770_);
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2769_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_pos_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2769_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
uint8_t v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
v___x_2764_ = 3;
v___x_2765_ = lean_box(v___x_2764_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 1, v___x_2765_);
v___x_2767_ = v___x_2762_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_pos_2760_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v___x_2765_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
else
{
lean_object* v_pos_2771_; lean_object* v_err_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2849_; 
v_pos_2771_ = lean_ctor_get(v___x_2759_, 0);
v_err_2772_ = lean_ctor_get(v___x_2759_, 1);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2774_ = v___x_2759_;
v_isShared_2775_ = v_isSharedCheck_2849_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_err_2772_);
lean_inc(v_pos_2771_);
lean_dec(v___x_2759_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2849_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v_snd_2776_; lean_object* v_snd_2777_; uint8_t v_decide_2778_; 
v_snd_2776_ = lean_ctor_get(v_a_2754_, 1);
lean_inc(v_snd_2776_);
lean_dec_ref(v_a_2754_);
v_snd_2777_ = lean_ctor_get(v_pos_2771_, 1);
v_decide_2778_ = lean_nat_dec_eq(v_snd_2776_, v_snd_2777_);
lean_dec(v_snd_2776_);
if (v_decide_2778_ == 0)
{
lean_object* v___x_2780_; 
lean_dec_ref(v_noon_2757_);
lean_dec_ref(v_pm_2756_);
lean_dec_ref(v_am_2755_);
if (v_isShared_2775_ == 0)
{
v___x_2780_ = v___x_2774_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_pos_2771_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v_err_2772_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
else
{
lean_object* v___x_2782_; 
lean_inc(v_snd_2777_);
lean_del_object(v___x_2774_);
lean_dec(v_err_2772_);
v___x_2782_ = l_Std_Internal_Parsec_String_pstring(v_noon_2757_, v_pos_2771_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_pos_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2792_; 
lean_dec(v_snd_2777_);
lean_dec_ref(v_pm_2756_);
lean_dec_ref(v_am_2755_);
v_pos_2783_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2792_ == 0)
{
lean_object* v_unused_2793_; 
v_unused_2793_ = lean_ctor_get(v___x_2782_, 1);
lean_dec(v_unused_2793_);
v___x_2785_ = v___x_2782_;
v_isShared_2786_ = v_isSharedCheck_2792_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_pos_2783_);
lean_dec(v___x_2782_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2792_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
uint8_t v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2790_; 
v___x_2787_ = 2;
v___x_2788_ = lean_box(v___x_2787_);
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 1, v___x_2788_);
v___x_2790_ = v___x_2785_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_pos_2783_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v___x_2788_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
else
{
lean_object* v_pos_2794_; lean_object* v_err_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2848_; 
v_pos_2794_ = lean_ctor_get(v___x_2782_, 0);
v_err_2795_ = lean_ctor_get(v___x_2782_, 1);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2797_ = v___x_2782_;
v_isShared_2798_ = v_isSharedCheck_2848_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_err_2795_);
lean_inc(v_pos_2794_);
lean_dec(v___x_2782_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2848_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v_snd_2799_; uint8_t v_decide_2800_; 
v_snd_2799_ = lean_ctor_get(v_pos_2794_, 1);
v_decide_2800_ = lean_nat_dec_eq(v_snd_2777_, v_snd_2799_);
lean_dec(v_snd_2777_);
if (v_decide_2800_ == 0)
{
lean_object* v___x_2802_; 
lean_dec_ref(v_pm_2756_);
lean_dec_ref(v_am_2755_);
if (v_isShared_2798_ == 0)
{
v___x_2802_ = v___x_2797_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_pos_2794_);
lean_ctor_set(v_reuseFailAlloc_2803_, 1, v_err_2795_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
else
{
lean_object* v___x_2804_; 
lean_inc(v_snd_2799_);
lean_del_object(v___x_2797_);
lean_dec(v_err_2795_);
v___x_2804_ = l_Std_Internal_Parsec_String_pstring(v_am_2755_, v_pos_2794_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_pos_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2814_; 
lean_dec(v_snd_2799_);
lean_dec_ref(v_pm_2756_);
v_pos_2805_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2814_ == 0)
{
lean_object* v_unused_2815_; 
v_unused_2815_ = lean_ctor_get(v___x_2804_, 1);
lean_dec(v_unused_2815_);
v___x_2807_ = v___x_2804_;
v_isShared_2808_ = v_isSharedCheck_2814_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_pos_2805_);
lean_dec(v___x_2804_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2814_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
uint8_t v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2809_ = 0;
v___x_2810_ = lean_box(v___x_2809_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 1, v___x_2810_);
v___x_2812_ = v___x_2807_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_pos_2805_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v___x_2810_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
else
{
lean_object* v_pos_2816_; lean_object* v_err_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2847_; 
v_pos_2816_ = lean_ctor_get(v___x_2804_, 0);
v_err_2817_ = lean_ctor_get(v___x_2804_, 1);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2819_ = v___x_2804_;
v_isShared_2820_ = v_isSharedCheck_2847_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_err_2817_);
lean_inc(v_pos_2816_);
lean_dec(v___x_2804_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2847_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v_snd_2821_; uint8_t v_decide_2822_; 
v_snd_2821_ = lean_ctor_get(v_pos_2816_, 1);
v_decide_2822_ = lean_nat_dec_eq(v_snd_2799_, v_snd_2821_);
lean_dec(v_snd_2799_);
if (v_decide_2822_ == 0)
{
lean_object* v___x_2824_; 
lean_dec_ref(v_pm_2756_);
if (v_isShared_2820_ == 0)
{
v___x_2824_ = v___x_2819_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_pos_2816_);
lean_ctor_set(v_reuseFailAlloc_2825_, 1, v_err_2817_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
else
{
lean_object* v___x_2826_; 
lean_del_object(v___x_2819_);
lean_dec(v_err_2817_);
v___x_2826_ = l_Std_Internal_Parsec_String_pstring(v_pm_2756_, v_pos_2816_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_pos_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2836_; 
v_pos_2827_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2836_ == 0)
{
lean_object* v_unused_2837_; 
v_unused_2837_ = lean_ctor_get(v___x_2826_, 1);
lean_dec(v_unused_2837_);
v___x_2829_ = v___x_2826_;
v_isShared_2830_ = v_isSharedCheck_2836_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_pos_2827_);
lean_dec(v___x_2826_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2836_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
uint8_t v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2834_; 
v___x_2831_ = 1;
v___x_2832_ = lean_box(v___x_2831_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 1, v___x_2832_);
v___x_2834_ = v___x_2829_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_pos_2827_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v___x_2832_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
else
{
lean_object* v_pos_2838_; lean_object* v_err_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
v_pos_2838_ = lean_ctor_get(v___x_2826_, 0);
v_err_2839_ = lean_ctor_get(v___x_2826_, 1);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2826_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_err_2839_);
lean_inc(v_pos_2838_);
lean_dec(v___x_2826_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_pos_2838_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v_err_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(lean_object* v_arr_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; uint8_t v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; uint8_t v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v_pairs_2889_; lean_object* v___x_2890_; 
v___x_2852_ = lean_unsigned_to_nat(6u);
v___x_2853_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__0);
v___x_2854_ = lean_array_fget_borrowed(v_arr_2850_, v___x_2853_);
v___x_2855_ = 0;
v___x_2856_ = lean_box(v___x_2855_);
lean_inc(v___x_2854_);
v___x_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2854_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
v___x_2858_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__1);
v___x_2859_ = lean_array_fget_borrowed(v_arr_2850_, v___x_2858_);
v___x_2860_ = 1;
v___x_2861_ = lean_box(v___x_2860_);
lean_inc(v___x_2859_);
v___x_2862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2859_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
v___x_2863_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__2);
v___x_2864_ = lean_array_fget_borrowed(v_arr_2850_, v___x_2863_);
v___x_2865_ = 2;
v___x_2866_ = lean_box(v___x_2865_);
lean_inc(v___x_2864_);
v___x_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2864_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
v___x_2868_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__3);
v___x_2869_ = lean_array_fget_borrowed(v_arr_2850_, v___x_2868_);
v___x_2870_ = 3;
v___x_2871_ = lean_box(v___x_2870_);
lean_inc(v___x_2869_);
v___x_2872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2869_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__4);
v___x_2874_ = lean_array_fget_borrowed(v_arr_2850_, v___x_2873_);
v___x_2875_ = 4;
v___x_2876_ = lean_box(v___x_2875_);
lean_inc(v___x_2874_);
v___x_2877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2874_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
v___x_2878_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___closed__5);
v___x_2879_ = lean_array_fget_borrowed(v_arr_2850_, v___x_2878_);
v___x_2880_ = 5;
v___x_2881_ = lean_box(v___x_2880_);
lean_inc(v___x_2879_);
v___x_2882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2879_);
lean_ctor_set(v___x_2882_, 1, v___x_2881_);
v___x_2883_ = lean_mk_empty_array_with_capacity(v___x_2852_);
v___x_2884_ = lean_array_push(v___x_2883_, v___x_2857_);
v___x_2885_ = lean_array_push(v___x_2884_, v___x_2862_);
v___x_2886_ = lean_array_push(v___x_2885_, v___x_2867_);
v___x_2887_ = lean_array_push(v___x_2886_, v___x_2872_);
v___x_2888_ = lean_array_push(v___x_2887_, v___x_2877_);
v_pairs_2889_ = lean_array_push(v___x_2888_, v___x_2882_);
v___x_2890_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2889_, v_a_2851_);
lean_dec_ref(v_pairs_2889_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom___boxed(lean_object* v_arr_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_arr_2891_, v_a_2892_);
lean_dec_ref(v_arr_2891_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(lean_object* v_parse_2894_, lean_object* v_size_2895_, lean_object* v_acc_2896_, lean_object* v_count_2897_, lean_object* v_a_2898_){
_start:
{
uint8_t v___x_2899_; 
v___x_2899_ = lean_nat_dec_le(v_size_2895_, v_count_2897_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; 
lean_inc_ref(v_parse_2894_);
v___x_2900_ = lean_apply_1(v_parse_2894_, v_a_2898_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_pos_2901_; lean_object* v_res_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v_pos_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_pos_2901_);
v_res_2902_ = lean_ctor_get(v___x_2900_, 1);
lean_inc(v_res_2902_);
lean_dec_ref_known(v___x_2900_, 2);
v___x_2903_ = lean_array_push(v_acc_2896_, v_res_2902_);
v___x_2904_ = lean_unsigned_to_nat(1u);
v___x_2905_ = lean_nat_add(v_count_2897_, v___x_2904_);
lean_dec(v_count_2897_);
v_acc_2896_ = v___x_2903_;
v_count_2897_ = v___x_2905_;
v_a_2898_ = v_pos_2901_;
goto _start;
}
else
{
lean_object* v_pos_2907_; lean_object* v_err_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec(v_count_2897_);
lean_dec_ref(v_acc_2896_);
lean_dec_ref(v_parse_2894_);
v_pos_2907_ = lean_ctor_get(v___x_2900_, 0);
v_err_2908_ = lean_ctor_get(v___x_2900_, 1);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2900_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_err_2908_);
lean_inc(v_pos_2907_);
lean_dec(v___x_2900_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_pos_2907_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v_err_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
else
{
lean_object* v___x_2916_; 
lean_dec(v_count_2897_);
lean_dec_ref(v_parse_2894_);
v___x_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2916_, 0, v_a_2898_);
lean_ctor_set(v___x_2916_, 1, v_acc_2896_);
return v___x_2916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg___boxed(lean_object* v_parse_2917_, lean_object* v_size_2918_, lean_object* v_acc_2919_, lean_object* v_count_2920_, lean_object* v_a_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2917_, v_size_2918_, v_acc_2919_, v_count_2920_, v_a_2921_);
lean_dec(v_size_2918_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go(lean_object* v_00_u03b1_2923_, lean_object* v_parse_2924_, lean_object* v_size_2925_, lean_object* v_acc_2926_, lean_object* v_count_2927_, lean_object* v_a_2928_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2924_, v_size_2925_, v_acc_2926_, v_count_2927_, v_a_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___boxed(lean_object* v_00_u03b1_2930_, lean_object* v_parse_2931_, lean_object* v_size_2932_, lean_object* v_acc_2933_, lean_object* v_count_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go(v_00_u03b1_2930_, v_parse_2931_, v_size_2932_, v_acc_2933_, v_count_2934_, v_a_2935_);
lean_dec(v_size_2932_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(lean_object* v_parse_2939_, lean_object* v_size_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2942_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___closed__0));
v___x_2943_ = lean_unsigned_to_nat(12u);
v___x_2944_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2939_, v_size_2940_, v___x_2942_, v___x_2943_, v_a_2941_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___boxed(lean_object* v_parse_2945_, lean_object* v_size_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(v_parse_2945_, v_size_2946_, v_a_2947_);
lean_dec(v_size_2946_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly(lean_object* v_00_u03b1_2949_, lean_object* v_parse_2950_, lean_object* v_size_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(v_parse_2950_, v_size_2951_, v_a_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___boxed(lean_object* v_00_u03b1_2954_, lean_object* v_parse_2955_, lean_object* v_size_2956_, lean_object* v_a_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly(v_00_u03b1_2954_, v_parse_2955_, v_size_2956_, v_a_2957_);
lean_dec(v_size_2956_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(lean_object* v_parse_2959_, lean_object* v_size_2960_, lean_object* v_acc_2961_, lean_object* v_count_2962_, lean_object* v_a_2963_){
_start:
{
uint8_t v___x_2964_; 
v___x_2964_ = lean_nat_dec_le(v_size_2960_, v_count_2962_);
if (v___x_2964_ == 0)
{
lean_object* v___x_2965_; 
lean_inc_ref(v_parse_2959_);
v___x_2965_ = lean_apply_1(v_parse_2959_, v_a_2963_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_pos_2966_; lean_object* v_res_2967_; uint32_t v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v_pos_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_pos_2966_);
v_res_2967_ = lean_ctor_get(v___x_2965_, 1);
lean_inc(v_res_2967_);
lean_dec_ref_known(v___x_2965_, 2);
v___x_2968_ = lean_unbox_uint32(v_res_2967_);
lean_dec(v_res_2967_);
v___x_2969_ = lean_string_push(v_acc_2961_, v___x_2968_);
v___x_2970_ = lean_unsigned_to_nat(1u);
v___x_2971_ = lean_nat_add(v_count_2962_, v___x_2970_);
lean_dec(v_count_2962_);
v_acc_2961_ = v___x_2969_;
v_count_2962_ = v___x_2971_;
v_a_2963_ = v_pos_2966_;
goto _start;
}
else
{
lean_object* v_pos_2973_; lean_object* v_err_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_dec(v_count_2962_);
lean_dec_ref(v_acc_2961_);
lean_dec_ref(v_parse_2959_);
v_pos_2973_ = lean_ctor_get(v___x_2965_, 0);
v_err_2974_ = lean_ctor_get(v___x_2965_, 1);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2965_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_err_2974_);
lean_inc(v_pos_2973_);
lean_dec(v___x_2965_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_pos_2973_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_err_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
else
{
lean_object* v___x_2982_; 
lean_dec(v_count_2962_);
lean_dec_ref(v_parse_2959_);
v___x_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2982_, 0, v_a_2963_);
lean_ctor_set(v___x_2982_, 1, v_acc_2961_);
return v___x_2982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go___boxed(lean_object* v_parse_2983_, lean_object* v_size_2984_, lean_object* v_acc_2985_, lean_object* v_count_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(v_parse_2983_, v_size_2984_, v_acc_2985_, v_count_2986_, v_a_2987_);
lean_dec(v_size_2984_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(lean_object* v_parse_2989_, lean_object* v_size_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_2993_ = lean_unsigned_to_nat(0u);
v___x_2994_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(v_parse_2989_, v_size_2990_, v___x_2992_, v___x_2993_, v_a_2991_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars___boxed(lean_object* v_parse_2995_, lean_object* v_size_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v_parse_2995_, v_size_2996_, v_a_2997_);
lean_dec(v_size_2996_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(lean_object* v_parser_2999_, lean_object* v_a_3000_){
_start:
{
lean_object* v_pos_3002_; lean_object* v_res_3003_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3035_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
lean_inc_ref(v_a_3000_);
v___x_3036_ = l_Std_Internal_Parsec_String_pstring(v___x_3035_, v_a_3000_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v_pos_3037_; lean_object* v_res_3038_; lean_object* v___x_3039_; 
lean_dec_ref(v_a_3000_);
v_pos_3037_ = lean_ctor_get(v___x_3036_, 0);
lean_inc(v_pos_3037_);
v_res_3038_ = lean_ctor_get(v___x_3036_, 1);
lean_inc(v_res_3038_);
lean_dec_ref_known(v___x_3036_, 2);
v___x_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3039_, 0, v_res_3038_);
v_pos_3002_ = v_pos_3037_;
v_res_3003_ = v___x_3039_;
goto v___jp_3001_;
}
else
{
lean_object* v_pos_3040_; lean_object* v_err_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3052_; 
v_pos_3040_ = lean_ctor_get(v___x_3036_, 0);
v_err_3041_ = lean_ctor_get(v___x_3036_, 1);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3043_ = v___x_3036_;
v_isShared_3044_ = v_isSharedCheck_3052_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_err_3041_);
lean_inc(v_pos_3040_);
lean_dec(v___x_3036_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3052_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v_snd_3045_; lean_object* v_snd_3046_; uint8_t v_decide_3047_; 
v_snd_3045_ = lean_ctor_get(v_a_3000_, 1);
lean_inc(v_snd_3045_);
lean_dec_ref(v_a_3000_);
v_snd_3046_ = lean_ctor_get(v_pos_3040_, 1);
v_decide_3047_ = lean_nat_dec_eq(v_snd_3045_, v_snd_3046_);
lean_dec(v_snd_3045_);
if (v_decide_3047_ == 0)
{
lean_object* v___x_3049_; 
lean_dec_ref(v_parser_2999_);
if (v_isShared_3044_ == 0)
{
v___x_3049_ = v___x_3043_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_pos_3040_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_err_3041_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
else
{
lean_object* v___x_3051_; 
lean_del_object(v___x_3043_);
lean_dec(v_err_3041_);
v___x_3051_ = lean_box(0);
v_pos_3002_ = v_pos_3040_;
v_res_3003_ = v___x_3051_;
goto v___jp_3001_;
}
}
}
v___jp_3001_:
{
lean_object* v___x_3004_; 
v___x_3004_ = lean_apply_1(v_parser_2999_, v_pos_3002_);
if (lean_obj_tag(v___x_3004_) == 0)
{
if (lean_obj_tag(v_res_3003_) == 0)
{
lean_object* v_pos_3005_; lean_object* v_res_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3014_; 
v_pos_3005_ = lean_ctor_get(v___x_3004_, 0);
v_res_3006_ = lean_ctor_get(v___x_3004_, 1);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3008_ = v___x_3004_;
v_isShared_3009_ = v_isSharedCheck_3014_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_res_3006_);
lean_inc(v_pos_3005_);
lean_dec(v___x_3004_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3014_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3010_; lean_object* v___x_3012_; 
v___x_3010_ = lean_nat_to_int(v_res_3006_);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 1, v___x_3010_);
v___x_3012_ = v___x_3008_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_pos_3005_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v___x_3010_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
else
{
lean_object* v_pos_3015_; lean_object* v_res_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3025_; 
lean_dec_ref_known(v_res_3003_, 1);
v_pos_3015_ = lean_ctor_get(v___x_3004_, 0);
v_res_3016_ = lean_ctor_get(v___x_3004_, 1);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3018_ = v___x_3004_;
v_isShared_3019_ = v_isSharedCheck_3025_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_res_3016_);
lean_inc(v_pos_3015_);
lean_dec(v___x_3004_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3025_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3023_; 
v___x_3020_ = lean_nat_to_int(v_res_3016_);
v___x_3021_ = lean_int_neg(v___x_3020_);
lean_dec(v___x_3020_);
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 1, v___x_3021_);
v___x_3023_ = v___x_3018_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_pos_3015_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
else
{
lean_object* v_pos_3026_; lean_object* v_err_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec(v_res_3003_);
v_pos_3026_ = lean_ctor_get(v___x_3004_, 0);
v_err_3027_ = lean_ctor_get(v___x_3004_, 1);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3004_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_err_3027_);
lean_inc(v_pos_3026_);
lean_dec(v___x_3004_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_pos_3026_);
lean_ctor_set(v_reuseFailAlloc_3033_, 1, v_err_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___lam__0(lean_object* v___y_3053_){
_start:
{
lean_object* v_fst_3057_; lean_object* v_snd_3058_; lean_object* v___x_3059_; uint8_t v_decide_3060_; 
v_fst_3057_ = lean_ctor_get(v___y_3053_, 0);
v_snd_3058_ = lean_ctor_get(v___y_3053_, 1);
v___x_3059_ = lean_string_utf8_byte_size(v_fst_3057_);
v_decide_3060_ = lean_nat_dec_eq(v_snd_3058_, v___x_3059_);
if (v_decide_3060_ == 0)
{
uint32_t v_c_3061_; lean_object* v___x_3062_; lean_object* v_it_x27_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; uint32_t v___x_3066_; uint8_t v___x_3067_; 
v_c_3061_ = lean_string_utf8_get_fast(v_fst_3057_, v_snd_3058_);
v___x_3062_ = lean_string_utf8_next_fast(v_fst_3057_, v_snd_3058_);
lean_inc(v_fst_3057_);
v_it_x27_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3063_, 0, v_fst_3057_);
lean_ctor_set(v_it_x27_3063_, 1, v___x_3062_);
v___x_3064_ = lean_box_uint32(v_c_3061_);
v___x_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3065_, 0, v_it_x27_3063_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
v___x_3066_ = 48;
v___x_3067_ = lean_uint32_dec_le(v___x_3066_, v_c_3061_);
if (v___x_3067_ == 0)
{
lean_dec_ref_known(v___x_3065_, 2);
goto v___jp_3054_;
}
else
{
uint32_t v___x_3068_; uint8_t v___x_3069_; 
v___x_3068_ = 57;
v___x_3069_ = lean_uint32_dec_le(v_c_3061_, v___x_3068_);
if (v___x_3069_ == 0)
{
lean_dec_ref_known(v___x_3065_, 2);
goto v___jp_3054_;
}
else
{
lean_dec_ref(v___y_3053_);
return v___x_3065_;
}
}
}
else
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = lean_box(0);
v___x_3071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___y_3053_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
return v___x_3071_;
}
v___jp_3054_:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___y_3053_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
return v___x_3056_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(lean_object* v_size_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v___f_3075_; lean_object* v___x_3076_; 
v___f_3075_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3076_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3075_, v_size_3073_, v_a_3074_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_pos_3077_; lean_object* v_res_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3089_; 
v_pos_3077_ = lean_ctor_get(v___x_3076_, 0);
v_res_3078_ = lean_ctor_get(v___x_3076_, 1);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3080_ = v___x_3076_;
v_isShared_3081_ = v_isSharedCheck_3089_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_res_3078_);
lean_inc(v_pos_3077_);
lean_dec(v___x_3076_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3089_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3087_; 
v___x_3082_ = lean_unsigned_to_nat(0u);
v___x_3083_ = lean_string_utf8_byte_size(v_res_3078_);
v___x_3084_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3084_, 0, v_res_3078_);
lean_ctor_set(v___x_3084_, 1, v___x_3082_);
lean_ctor_set(v___x_3084_, 2, v___x_3083_);
v___x_3085_ = l_String_Slice_toNat_x21(v___x_3084_);
lean_dec_ref_known(v___x_3084_, 3);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 1, v___x_3085_);
v___x_3087_ = v___x_3080_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_pos_3077_);
lean_ctor_set(v_reuseFailAlloc_3088_, 1, v___x_3085_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
else
{
lean_object* v_pos_3090_; lean_object* v_err_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
v_pos_3090_ = lean_ctor_get(v___x_3076_, 0);
v_err_3091_ = lean_ctor_get(v___x_3076_, 1);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3076_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_err_3091_);
lean_inc(v_pos_3090_);
lean_dec(v___x_3076_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_pos_3090_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v_err_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed(lean_object* v_size_3099_, lean_object* v_a_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_size_3099_, v_a_3100_);
lean_dec(v_size_3099_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(lean_object* v_acc_3102_, lean_object* v_a_3103_){
_start:
{
lean_object* v_fst_3104_; lean_object* v_snd_3105_; lean_object* v_pos_3107_; lean_object* v_snd_3108_; lean_object* v_err_3109_; lean_object* v___x_3115_; uint8_t v_decide_3116_; 
v_fst_3104_ = lean_ctor_get(v_a_3103_, 0);
v_snd_3105_ = lean_ctor_get(v_a_3103_, 1);
lean_inc(v_snd_3105_);
v___x_3115_ = lean_string_utf8_byte_size(v_fst_3104_);
v_decide_3116_ = lean_nat_dec_eq(v_snd_3105_, v___x_3115_);
if (v_decide_3116_ == 0)
{
uint32_t v_c_3117_; uint32_t v___x_3118_; uint8_t v___x_3119_; 
v_c_3117_ = lean_string_utf8_get_fast(v_fst_3104_, v_snd_3105_);
v___x_3118_ = 48;
v___x_3119_ = lean_uint32_dec_le(v___x_3118_, v_c_3117_);
if (v___x_3119_ == 0)
{
goto v___jp_3113_;
}
else
{
uint32_t v___x_3120_; uint8_t v___x_3121_; 
v___x_3120_ = 57;
v___x_3121_ = lean_uint32_dec_le(v_c_3117_, v___x_3120_);
if (v___x_3121_ == 0)
{
goto v___jp_3113_;
}
else
{
lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3131_; 
lean_inc(v_fst_3104_);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_a_3103_);
if (v_isSharedCheck_3131_ == 0)
{
lean_object* v_unused_3132_; lean_object* v_unused_3133_; 
v_unused_3132_ = lean_ctor_get(v_a_3103_, 1);
lean_dec(v_unused_3132_);
v_unused_3133_ = lean_ctor_get(v_a_3103_, 0);
lean_dec(v_unused_3133_);
v___x_3123_ = v_a_3103_;
v_isShared_3124_ = v_isSharedCheck_3131_;
goto v_resetjp_3122_;
}
else
{
lean_dec(v_a_3103_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3131_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3125_; lean_object* v_it_x27_3127_; 
v___x_3125_ = lean_string_utf8_next_fast(v_fst_3104_, v_snd_3105_);
lean_dec(v_snd_3105_);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 1, v___x_3125_);
v_it_x27_3127_ = v___x_3123_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_fst_3104_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v___x_3125_);
v_it_x27_3127_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
lean_object* v___x_3128_; 
v___x_3128_ = lean_string_push(v_acc_3102_, v_c_3117_);
v_acc_3102_ = v___x_3128_;
v_a_3103_ = v_it_x27_3127_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_3134_; 
v___x_3134_ = lean_box(0);
lean_inc(v_snd_3105_);
v_pos_3107_ = v_a_3103_;
v_snd_3108_ = v_snd_3105_;
v_err_3109_ = v___x_3134_;
goto v___jp_3106_;
}
v___jp_3106_:
{
uint8_t v_decide_3110_; 
v_decide_3110_ = lean_nat_dec_eq(v_snd_3105_, v_snd_3108_);
lean_dec(v_snd_3108_);
lean_dec(v_snd_3105_);
if (v_decide_3110_ == 0)
{
lean_object* v___x_3111_; 
lean_dec_ref(v_acc_3102_);
lean_inc(v_err_3109_);
v___x_3111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3111_, 0, v_pos_3107_);
lean_ctor_set(v___x_3111_, 1, v_err_3109_);
return v___x_3111_;
}
else
{
lean_object* v___x_3112_; 
v___x_3112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3112_, 0, v_pos_3107_);
lean_ctor_set(v___x_3112_, 1, v_acc_3102_);
return v___x_3112_;
}
}
v___jp_3113_:
{
lean_object* v___x_3114_; 
v___x_3114_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3105_);
v_pos_3107_ = v_a_3103_;
v_snd_3108_ = v_snd_3105_;
v_err_3109_ = v___x_3114_;
goto v___jp_3106_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(lean_object* v_size_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v_pos_3138_; lean_object* v_res_3139_; lean_object* v___y_3146_; lean_object* v___f_3158_; lean_object* v___x_3159_; 
v___f_3158_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3159_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3158_, v_size_3135_, v_a_3136_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_pos_3160_; lean_object* v_res_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v_pos_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_pos_3160_);
v_res_3161_ = lean_ctor_get(v___x_3159_, 1);
lean_inc(v_res_3161_);
lean_dec_ref_known(v___x_3159_, 2);
v___x_3162_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3163_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(v___x_3162_, v_pos_3160_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_pos_3164_; lean_object* v_res_3165_; lean_object* v___x_3166_; 
v_pos_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_pos_3164_);
v_res_3165_ = lean_ctor_get(v___x_3163_, 1);
lean_inc(v_res_3165_);
lean_dec_ref_known(v___x_3163_, 2);
v___x_3166_ = lean_string_append(v_res_3161_, v_res_3165_);
lean_dec(v_res_3165_);
v_pos_3138_ = v_pos_3164_;
v_res_3139_ = v___x_3166_;
goto v___jp_3137_;
}
else
{
lean_dec(v_res_3161_);
v___y_3146_ = v___x_3163_;
goto v___jp_3145_;
}
}
else
{
v___y_3146_ = v___x_3159_;
goto v___jp_3145_;
}
v___jp_3137_:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3140_ = lean_unsigned_to_nat(0u);
v___x_3141_ = lean_string_utf8_byte_size(v_res_3139_);
v___x_3142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3142_, 0, v_res_3139_);
lean_ctor_set(v___x_3142_, 1, v___x_3140_);
lean_ctor_set(v___x_3142_, 2, v___x_3141_);
v___x_3143_ = l_String_Slice_toNat_x21(v___x_3142_);
lean_dec_ref_known(v___x_3142_, 3);
v___x_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3144_, 0, v_pos_3138_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
return v___x_3144_;
}
v___jp_3145_:
{
if (lean_obj_tag(v___y_3146_) == 0)
{
lean_object* v_pos_3147_; lean_object* v_res_3148_; 
v_pos_3147_ = lean_ctor_get(v___y_3146_, 0);
lean_inc(v_pos_3147_);
v_res_3148_ = lean_ctor_get(v___y_3146_, 1);
lean_inc(v_res_3148_);
lean_dec_ref_known(v___y_3146_, 2);
v_pos_3138_ = v_pos_3147_;
v_res_3139_ = v_res_3148_;
goto v___jp_3137_;
}
else
{
lean_object* v_pos_3149_; lean_object* v_err_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
v_pos_3149_ = lean_ctor_get(v___y_3146_, 0);
v_err_3150_ = lean_ctor_get(v___y_3146_, 1);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___y_3146_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___y_3146_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_err_3150_);
lean_inc(v_pos_3149_);
lean_dec(v___y_3146_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_pos_3149_);
lean_ctor_set(v_reuseFailAlloc_3156_, 1, v_err_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___boxed(lean_object* v_size_3167_, lean_object* v_a_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v_size_3167_, v_a_3168_);
lean_dec(v_size_3167_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(lean_object* v_size_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v___x_3172_; uint8_t v___x_3173_; 
v___x_3172_ = lean_unsigned_to_nat(1u);
v___x_3173_ = lean_nat_dec_eq(v_size_3170_, v___x_3172_);
if (v___x_3173_ == 0)
{
lean_object* v___x_3174_; 
v___x_3174_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_size_3170_, v_a_3171_);
return v___x_3174_;
}
else
{
lean_object* v___x_3175_; 
v___x_3175_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v___x_3172_, v_a_3171_);
return v___x_3175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed(lean_object* v_size_3176_, lean_object* v_a_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_size_3176_, v_a_3177_);
lean_dec(v_size_3176_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(lean_object* v_size_3179_, lean_object* v_pad_3180_, lean_object* v_a_3181_){
_start:
{
lean_object* v_pos_3183_; lean_object* v_res_3184_; lean_object* v___f_3190_; lean_object* v___x_3191_; 
v___f_3190_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3191_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3190_, v_size_3179_, v_a_3181_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v_pos_3192_; lean_object* v_res_3193_; uint32_t v___x_3194_; lean_object* v___x_3195_; 
v_pos_3192_ = lean_ctor_get(v___x_3191_, 0);
lean_inc(v_pos_3192_);
v_res_3193_ = lean_ctor_get(v___x_3191_, 1);
lean_inc(v_res_3193_);
lean_dec_ref_known(v___x_3191_, 2);
v___x_3194_ = 48;
v___x_3195_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_pad_3180_, v___x_3194_, v_res_3193_);
v_pos_3183_ = v_pos_3192_;
v_res_3184_ = v___x_3195_;
goto v___jp_3182_;
}
else
{
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v_pos_3196_; lean_object* v_res_3197_; 
v_pos_3196_ = lean_ctor_get(v___x_3191_, 0);
lean_inc(v_pos_3196_);
v_res_3197_ = lean_ctor_get(v___x_3191_, 1);
lean_inc(v_res_3197_);
lean_dec_ref_known(v___x_3191_, 2);
v_pos_3183_ = v_pos_3196_;
v_res_3184_ = v_res_3197_;
goto v___jp_3182_;
}
else
{
lean_object* v_pos_3198_; lean_object* v_err_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
v_pos_3198_ = lean_ctor_get(v___x_3191_, 0);
v_err_3199_ = lean_ctor_get(v___x_3191_, 1);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3191_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_err_3199_);
lean_inc(v_pos_3198_);
lean_dec(v___x_3191_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_pos_3198_);
lean_ctor_set(v_reuseFailAlloc_3205_, 1, v_err_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
v___jp_3182_:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3185_ = lean_unsigned_to_nat(0u);
v___x_3186_ = lean_string_utf8_byte_size(v_res_3184_);
v___x_3187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3187_, 0, v_res_3184_);
lean_ctor_set(v___x_3187_, 1, v___x_3185_);
lean_ctor_set(v___x_3187_, 2, v___x_3186_);
v___x_3188_ = l_String_Slice_toNat_x21(v___x_3187_);
lean_dec_ref_known(v___x_3187_, 3);
v___x_3189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3189_, 0, v_pos_3183_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
return v___x_3189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed(lean_object* v_size_3207_, lean_object* v_pad_3208_, lean_object* v_a_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(v_size_3207_, v_pad_3208_, v_a_3209_);
lean_dec(v_pad_3208_);
lean_dec(v_size_3207_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(lean_object* v_acc_3211_, lean_object* v_a_3212_){
_start:
{
lean_object* v_fst_3213_; lean_object* v_snd_3214_; lean_object* v_pos_3216_; lean_object* v_snd_3217_; lean_object* v_err_3218_; lean_object* v___x_3222_; uint8_t v_decide_3223_; 
v_fst_3213_ = lean_ctor_get(v_a_3212_, 0);
v_snd_3214_ = lean_ctor_get(v_a_3212_, 1);
lean_inc(v_snd_3214_);
v___x_3222_ = lean_string_utf8_byte_size(v_fst_3213_);
v_decide_3223_ = lean_nat_dec_eq(v_snd_3214_, v___x_3222_);
if (v_decide_3223_ == 0)
{
uint32_t v_c_3224_; lean_object* v___x_3225_; lean_object* v_it_x27_3226_; uint8_t v___y_3231_; uint8_t v___y_3232_; uint8_t v___y_3235_; uint8_t v___y_3236_; uint8_t v___y_3237_; uint8_t v___y_3239_; uint8_t v___y_3240_; uint8_t v___y_3241_; uint8_t v___y_3242_; uint8_t v___y_3244_; uint8_t v___y_3245_; uint8_t v___y_3253_; uint8_t v___y_3259_; uint32_t v___x_3264_; uint8_t v___x_3265_; 
v_c_3224_ = lean_string_utf8_get_fast(v_fst_3213_, v_snd_3214_);
v___x_3225_ = lean_string_utf8_next_fast(v_fst_3213_, v_snd_3214_);
lean_inc(v_fst_3213_);
v_it_x27_3226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3226_, 0, v_fst_3213_);
lean_ctor_set(v_it_x27_3226_, 1, v___x_3225_);
v___x_3264_ = 65;
v___x_3265_ = lean_uint32_dec_le(v___x_3264_, v_c_3224_);
if (v___x_3265_ == 0)
{
v___y_3259_ = v___x_3265_;
goto v___jp_3258_;
}
else
{
uint32_t v___x_3266_; uint8_t v___x_3267_; 
v___x_3266_ = 90;
v___x_3267_ = lean_uint32_dec_le(v_c_3224_, v___x_3266_);
v___y_3259_ = v___x_3267_;
goto v___jp_3258_;
}
v___jp_3227_:
{
lean_object* v___x_3228_; 
v___x_3228_ = lean_string_push(v_acc_3211_, v_c_3224_);
v_acc_3211_ = v___x_3228_;
v_a_3212_ = v_it_x27_3226_;
goto _start;
}
v___jp_3230_:
{
if (v___y_3231_ == 0)
{
if (v___y_3232_ == 0)
{
lean_object* v___x_3233_; 
lean_dec_ref_known(v_it_x27_3226_, 2);
v___x_3233_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3214_);
v_pos_3216_ = v_a_3212_;
v_snd_3217_ = v_snd_3214_;
v_err_3218_ = v___x_3233_;
goto v___jp_3215_;
}
else
{
lean_dec(v_snd_3214_);
lean_dec_ref(v_a_3212_);
goto v___jp_3227_;
}
}
else
{
lean_dec(v_snd_3214_);
lean_dec_ref(v_a_3212_);
goto v___jp_3227_;
}
}
v___jp_3234_:
{
if (v___y_3236_ == 0)
{
v___y_3231_ = v___y_3235_;
v___y_3232_ = v___y_3237_;
goto v___jp_3230_;
}
else
{
v___y_3231_ = v___y_3235_;
v___y_3232_ = v___y_3236_;
goto v___jp_3230_;
}
}
v___jp_3238_:
{
if (v___y_3240_ == 0)
{
v___y_3235_ = v___y_3239_;
v___y_3236_ = v___y_3241_;
v___y_3237_ = v___y_3242_;
goto v___jp_3234_;
}
else
{
v___y_3235_ = v___y_3239_;
v___y_3236_ = v___y_3241_;
v___y_3237_ = v___y_3240_;
goto v___jp_3234_;
}
}
v___jp_3243_:
{
uint32_t v___x_3246_; uint8_t v___x_3247_; uint32_t v___x_3248_; uint8_t v___x_3249_; 
v___x_3246_ = 95;
v___x_3247_ = lean_uint32_dec_eq(v_c_3224_, v___x_3246_);
v___x_3248_ = 45;
v___x_3249_ = lean_uint32_dec_eq(v_c_3224_, v___x_3248_);
if (v___x_3249_ == 0)
{
uint32_t v___x_3250_; uint8_t v___x_3251_; 
v___x_3250_ = 47;
v___x_3251_ = lean_uint32_dec_eq(v_c_3224_, v___x_3250_);
v___y_3239_ = v___y_3244_;
v___y_3240_ = v___x_3247_;
v___y_3241_ = v___y_3245_;
v___y_3242_ = v___x_3251_;
goto v___jp_3238_;
}
else
{
v___y_3239_ = v___y_3244_;
v___y_3240_ = v___x_3247_;
v___y_3241_ = v___y_3245_;
v___y_3242_ = v___x_3249_;
goto v___jp_3238_;
}
}
v___jp_3252_:
{
uint32_t v___x_3254_; uint8_t v___x_3255_; 
v___x_3254_ = 48;
v___x_3255_ = lean_uint32_dec_le(v___x_3254_, v_c_3224_);
if (v___x_3255_ == 0)
{
v___y_3244_ = v___y_3253_;
v___y_3245_ = v___x_3255_;
goto v___jp_3243_;
}
else
{
uint32_t v___x_3256_; uint8_t v___x_3257_; 
v___x_3256_ = 57;
v___x_3257_ = lean_uint32_dec_le(v_c_3224_, v___x_3256_);
v___y_3244_ = v___y_3253_;
v___y_3245_ = v___x_3257_;
goto v___jp_3243_;
}
}
v___jp_3258_:
{
if (v___y_3259_ == 0)
{
uint32_t v___x_3260_; uint8_t v___x_3261_; 
v___x_3260_ = 97;
v___x_3261_ = lean_uint32_dec_le(v___x_3260_, v_c_3224_);
if (v___x_3261_ == 0)
{
v___y_3253_ = v___x_3261_;
goto v___jp_3252_;
}
else
{
uint32_t v___x_3262_; uint8_t v___x_3263_; 
v___x_3262_ = 122;
v___x_3263_ = lean_uint32_dec_le(v_c_3224_, v___x_3262_);
v___y_3253_ = v___x_3263_;
goto v___jp_3252_;
}
}
else
{
v___y_3253_ = v___y_3259_;
goto v___jp_3252_;
}
}
}
else
{
lean_object* v___x_3268_; 
v___x_3268_ = lean_box(0);
lean_inc(v_snd_3214_);
v_pos_3216_ = v_a_3212_;
v_snd_3217_ = v_snd_3214_;
v_err_3218_ = v___x_3268_;
goto v___jp_3215_;
}
v___jp_3215_:
{
uint8_t v_decide_3219_; 
v_decide_3219_ = lean_nat_dec_eq(v_snd_3214_, v_snd_3217_);
lean_dec(v_snd_3217_);
lean_dec(v_snd_3214_);
if (v_decide_3219_ == 0)
{
lean_object* v___x_3220_; 
lean_dec_ref(v_acc_3211_);
lean_inc(v_err_3218_);
v___x_3220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3220_, 0, v_pos_3216_);
lean_ctor_set(v___x_3220_, 1, v_err_3218_);
return v___x_3220_;
}
else
{
lean_object* v___x_3221_; 
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v_pos_3216_);
lean_ctor_set(v___x_3221_, 1, v_acc_3211_);
return v___x_3221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(lean_object* v_acc_3269_, lean_object* v_a_3270_){
_start:
{
lean_object* v_fst_3271_; lean_object* v_snd_3272_; lean_object* v_pos_3274_; lean_object* v_snd_3275_; lean_object* v_err_3276_; lean_object* v___x_3280_; uint8_t v_decide_3281_; 
v_fst_3271_ = lean_ctor_get(v_a_3270_, 0);
v_snd_3272_ = lean_ctor_get(v_a_3270_, 1);
lean_inc(v_snd_3272_);
v___x_3280_ = lean_string_utf8_byte_size(v_fst_3271_);
v_decide_3281_ = lean_nat_dec_eq(v_snd_3272_, v___x_3280_);
if (v_decide_3281_ == 0)
{
uint32_t v_c_3282_; lean_object* v___x_3283_; lean_object* v_it_x27_3284_; uint8_t v___y_3289_; uint8_t v___y_3290_; uint8_t v___y_3293_; uint8_t v___y_3294_; uint8_t v___y_3295_; uint8_t v___y_3297_; uint8_t v___y_3298_; uint8_t v___y_3299_; uint8_t v___y_3300_; uint8_t v___y_3302_; uint8_t v___y_3303_; uint8_t v___y_3311_; uint8_t v___y_3317_; uint32_t v___x_3322_; uint8_t v___x_3323_; 
v_c_3282_ = lean_string_utf8_get_fast(v_fst_3271_, v_snd_3272_);
v___x_3283_ = lean_string_utf8_next_fast(v_fst_3271_, v_snd_3272_);
lean_inc(v_fst_3271_);
v_it_x27_3284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3284_, 0, v_fst_3271_);
lean_ctor_set(v_it_x27_3284_, 1, v___x_3283_);
v___x_3322_ = 65;
v___x_3323_ = lean_uint32_dec_le(v___x_3322_, v_c_3282_);
if (v___x_3323_ == 0)
{
v___y_3317_ = v___x_3323_;
goto v___jp_3316_;
}
else
{
uint32_t v___x_3324_; uint8_t v___x_3325_; 
v___x_3324_ = 90;
v___x_3325_ = lean_uint32_dec_le(v_c_3282_, v___x_3324_);
v___y_3317_ = v___x_3325_;
goto v___jp_3316_;
}
v___jp_3285_:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3286_ = lean_string_push(v_acc_3269_, v_c_3282_);
v___x_3287_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(v___x_3286_, v_it_x27_3284_);
return v___x_3287_;
}
v___jp_3288_:
{
if (v___y_3289_ == 0)
{
if (v___y_3290_ == 0)
{
lean_object* v___x_3291_; 
lean_dec_ref_known(v_it_x27_3284_, 2);
v___x_3291_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3272_);
v_pos_3274_ = v_a_3270_;
v_snd_3275_ = v_snd_3272_;
v_err_3276_ = v___x_3291_;
goto v___jp_3273_;
}
else
{
lean_dec(v_snd_3272_);
lean_dec_ref(v_a_3270_);
goto v___jp_3285_;
}
}
else
{
lean_dec(v_snd_3272_);
lean_dec_ref(v_a_3270_);
goto v___jp_3285_;
}
}
v___jp_3292_:
{
if (v___y_3293_ == 0)
{
v___y_3289_ = v___y_3294_;
v___y_3290_ = v___y_3295_;
goto v___jp_3288_;
}
else
{
v___y_3289_ = v___y_3294_;
v___y_3290_ = v___y_3293_;
goto v___jp_3288_;
}
}
v___jp_3296_:
{
if (v___y_3298_ == 0)
{
v___y_3293_ = v___y_3297_;
v___y_3294_ = v___y_3299_;
v___y_3295_ = v___y_3300_;
goto v___jp_3292_;
}
else
{
v___y_3293_ = v___y_3297_;
v___y_3294_ = v___y_3299_;
v___y_3295_ = v___y_3298_;
goto v___jp_3292_;
}
}
v___jp_3301_:
{
uint32_t v___x_3304_; uint8_t v___x_3305_; uint32_t v___x_3306_; uint8_t v___x_3307_; 
v___x_3304_ = 95;
v___x_3305_ = lean_uint32_dec_eq(v_c_3282_, v___x_3304_);
v___x_3306_ = 45;
v___x_3307_ = lean_uint32_dec_eq(v_c_3282_, v___x_3306_);
if (v___x_3307_ == 0)
{
uint32_t v___x_3308_; uint8_t v___x_3309_; 
v___x_3308_ = 47;
v___x_3309_ = lean_uint32_dec_eq(v_c_3282_, v___x_3308_);
v___y_3297_ = v___y_3303_;
v___y_3298_ = v___x_3305_;
v___y_3299_ = v___y_3302_;
v___y_3300_ = v___x_3309_;
goto v___jp_3296_;
}
else
{
v___y_3297_ = v___y_3303_;
v___y_3298_ = v___x_3305_;
v___y_3299_ = v___y_3302_;
v___y_3300_ = v___x_3307_;
goto v___jp_3296_;
}
}
v___jp_3310_:
{
uint32_t v___x_3312_; uint8_t v___x_3313_; 
v___x_3312_ = 48;
v___x_3313_ = lean_uint32_dec_le(v___x_3312_, v_c_3282_);
if (v___x_3313_ == 0)
{
v___y_3302_ = v___y_3311_;
v___y_3303_ = v___x_3313_;
goto v___jp_3301_;
}
else
{
uint32_t v___x_3314_; uint8_t v___x_3315_; 
v___x_3314_ = 57;
v___x_3315_ = lean_uint32_dec_le(v_c_3282_, v___x_3314_);
v___y_3302_ = v___y_3311_;
v___y_3303_ = v___x_3315_;
goto v___jp_3301_;
}
}
v___jp_3316_:
{
if (v___y_3317_ == 0)
{
uint32_t v___x_3318_; uint8_t v___x_3319_; 
v___x_3318_ = 97;
v___x_3319_ = lean_uint32_dec_le(v___x_3318_, v_c_3282_);
if (v___x_3319_ == 0)
{
v___y_3311_ = v___x_3319_;
goto v___jp_3310_;
}
else
{
uint32_t v___x_3320_; uint8_t v___x_3321_; 
v___x_3320_ = 122;
v___x_3321_ = lean_uint32_dec_le(v_c_3282_, v___x_3320_);
v___y_3311_ = v___x_3321_;
goto v___jp_3310_;
}
}
else
{
v___y_3311_ = v___y_3317_;
goto v___jp_3310_;
}
}
}
else
{
lean_object* v___x_3326_; 
v___x_3326_ = lean_box(0);
lean_inc(v_snd_3272_);
v_pos_3274_ = v_a_3270_;
v_snd_3275_ = v_snd_3272_;
v_err_3276_ = v___x_3326_;
goto v___jp_3273_;
}
v___jp_3273_:
{
uint8_t v_decide_3277_; 
v_decide_3277_ = lean_nat_dec_eq(v_snd_3272_, v_snd_3275_);
lean_dec(v_snd_3275_);
lean_dec(v_snd_3272_);
if (v_decide_3277_ == 0)
{
lean_object* v___x_3278_; 
lean_dec_ref(v_acc_3269_);
lean_inc(v_err_3276_);
v___x_3278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3278_, 0, v_pos_3274_);
lean_ctor_set(v___x_3278_, 1, v_err_3276_);
return v___x_3278_;
}
else
{
lean_object* v___x_3279_; 
v___x_3279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3279_, 0, v_pos_3274_);
lean_ctor_set(v___x_3279_, 1, v_acc_3269_);
return v___x_3279_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(lean_object* v_a_3327_){
_start:
{
lean_object* v_fst_3328_; lean_object* v_snd_3329_; lean_object* v___x_3330_; uint8_t v_decide_3331_; 
v_fst_3328_ = lean_ctor_get(v_a_3327_, 0);
v_snd_3329_ = lean_ctor_get(v_a_3327_, 1);
v___x_3330_ = lean_string_utf8_byte_size(v_fst_3328_);
v_decide_3331_ = lean_nat_dec_eq(v_snd_3329_, v___x_3330_);
if (v_decide_3331_ == 0)
{
uint32_t v_c_3332_; lean_object* v___x_3333_; uint8_t v___y_3340_; uint8_t v___y_3341_; uint8_t v___y_3345_; uint8_t v___y_3346_; uint8_t v___y_3347_; uint8_t v___y_3349_; uint8_t v___y_3350_; uint8_t v___y_3351_; uint8_t v___y_3352_; uint8_t v___y_3354_; uint8_t v___y_3355_; uint8_t v___y_3363_; uint8_t v___y_3369_; uint32_t v___x_3374_; uint8_t v___x_3375_; 
v_c_3332_ = lean_string_utf8_get_fast(v_fst_3328_, v_snd_3329_);
v___x_3333_ = lean_string_utf8_next_fast(v_fst_3328_, v_snd_3329_);
v___x_3374_ = 65;
v___x_3375_ = lean_uint32_dec_le(v___x_3374_, v_c_3332_);
if (v___x_3375_ == 0)
{
v___y_3369_ = v___x_3375_;
goto v___jp_3368_;
}
else
{
uint32_t v___x_3376_; uint8_t v___x_3377_; 
v___x_3376_ = 90;
v___x_3377_ = lean_uint32_dec_le(v_c_3332_, v___x_3376_);
v___y_3369_ = v___x_3377_;
goto v___jp_3368_;
}
v___jp_3334_:
{
lean_object* v_it_x27_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v_it_x27_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3335_, 0, v_fst_3328_);
lean_ctor_set(v_it_x27_3335_, 1, v___x_3333_);
v___x_3336_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3337_ = lean_string_push(v___x_3336_, v_c_3332_);
v___x_3338_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(v___x_3337_, v_it_x27_3335_);
return v___x_3338_;
}
v___jp_3339_:
{
if (v___y_3340_ == 0)
{
if (v___y_3341_ == 0)
{
lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3342_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3343_, 0, v_a_3327_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
return v___x_3343_;
}
else
{
lean_inc(v_fst_3328_);
lean_dec_ref(v_a_3327_);
goto v___jp_3334_;
}
}
else
{
lean_inc(v_fst_3328_);
lean_dec_ref(v_a_3327_);
goto v___jp_3334_;
}
}
v___jp_3344_:
{
if (v___y_3345_ == 0)
{
v___y_3340_ = v___y_3346_;
v___y_3341_ = v___y_3347_;
goto v___jp_3339_;
}
else
{
v___y_3340_ = v___y_3346_;
v___y_3341_ = v___y_3345_;
goto v___jp_3339_;
}
}
v___jp_3348_:
{
if (v___y_3349_ == 0)
{
v___y_3345_ = v___y_3350_;
v___y_3346_ = v___y_3351_;
v___y_3347_ = v___y_3352_;
goto v___jp_3344_;
}
else
{
v___y_3345_ = v___y_3350_;
v___y_3346_ = v___y_3351_;
v___y_3347_ = v___y_3349_;
goto v___jp_3344_;
}
}
v___jp_3353_:
{
uint32_t v___x_3356_; uint8_t v___x_3357_; uint32_t v___x_3358_; uint8_t v___x_3359_; 
v___x_3356_ = 95;
v___x_3357_ = lean_uint32_dec_eq(v_c_3332_, v___x_3356_);
v___x_3358_ = 45;
v___x_3359_ = lean_uint32_dec_eq(v_c_3332_, v___x_3358_);
if (v___x_3359_ == 0)
{
uint32_t v___x_3360_; uint8_t v___x_3361_; 
v___x_3360_ = 47;
v___x_3361_ = lean_uint32_dec_eq(v_c_3332_, v___x_3360_);
v___y_3349_ = v___x_3357_;
v___y_3350_ = v___y_3355_;
v___y_3351_ = v___y_3354_;
v___y_3352_ = v___x_3361_;
goto v___jp_3348_;
}
else
{
v___y_3349_ = v___x_3357_;
v___y_3350_ = v___y_3355_;
v___y_3351_ = v___y_3354_;
v___y_3352_ = v___x_3359_;
goto v___jp_3348_;
}
}
v___jp_3362_:
{
uint32_t v___x_3364_; uint8_t v___x_3365_; 
v___x_3364_ = 48;
v___x_3365_ = lean_uint32_dec_le(v___x_3364_, v_c_3332_);
if (v___x_3365_ == 0)
{
v___y_3354_ = v___y_3363_;
v___y_3355_ = v___x_3365_;
goto v___jp_3353_;
}
else
{
uint32_t v___x_3366_; uint8_t v___x_3367_; 
v___x_3366_ = 57;
v___x_3367_ = lean_uint32_dec_le(v_c_3332_, v___x_3366_);
v___y_3354_ = v___y_3363_;
v___y_3355_ = v___x_3367_;
goto v___jp_3353_;
}
}
v___jp_3368_:
{
if (v___y_3369_ == 0)
{
uint32_t v___x_3370_; uint8_t v___x_3371_; 
v___x_3370_ = 97;
v___x_3371_ = lean_uint32_dec_le(v___x_3370_, v_c_3332_);
if (v___x_3371_ == 0)
{
v___y_3363_ = v___x_3371_;
goto v___jp_3362_;
}
else
{
uint32_t v___x_3372_; uint8_t v___x_3373_; 
v___x_3372_ = 122;
v___x_3373_ = lean_uint32_dec_le(v_c_3332_, v___x_3372_);
v___y_3363_ = v___x_3373_;
goto v___jp_3362_;
}
}
else
{
v___y_3363_ = v___y_3369_;
goto v___jp_3362_;
}
}
}
else
{
lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3378_ = lean_box(0);
v___x_3379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3379_, 0, v_a_3327_);
lean_ctor_set(v___x_3379_, 1, v___x_3378_);
return v___x_3379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(lean_object* v_n_3382_, lean_object* v_m_3383_, lean_object* v_parser_3384_, lean_object* v_a_3385_){
_start:
{
lean_object* v___x_3386_; 
v___x_3386_ = lean_apply_1(v_parser_3384_, v_a_3385_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_pos_3387_; lean_object* v_res_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3411_; 
v_pos_3387_ = lean_ctor_get(v___x_3386_, 0);
v_res_3388_ = lean_ctor_get(v___x_3386_, 1);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3390_ = v___x_3386_;
v_isShared_3391_ = v_isSharedCheck_3411_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_res_3388_);
lean_inc(v_pos_3387_);
lean_dec(v___x_3386_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3411_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
uint8_t v___y_3393_; uint8_t v___x_3409_; 
v___x_3409_ = lean_nat_dec_le(v_n_3382_, v_res_3388_);
if (v___x_3409_ == 0)
{
v___y_3393_ = v___x_3409_;
goto v___jp_3392_;
}
else
{
uint8_t v___x_3410_; 
v___x_3410_ = lean_nat_dec_le(v_res_3388_, v_m_3383_);
v___y_3393_ = v___x_3410_;
goto v___jp_3392_;
}
v___jp_3392_:
{
if (v___y_3393_ == 0)
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3403_; 
lean_dec(v_res_3388_);
v___x_3394_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__0));
v___x_3395_ = l_Nat_reprFast(v_n_3382_);
v___x_3396_ = lean_string_append(v___x_3394_, v___x_3395_);
lean_dec_ref(v___x_3395_);
v___x_3397_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__1));
v___x_3398_ = lean_string_append(v___x_3396_, v___x_3397_);
v___x_3399_ = l_Nat_reprFast(v_m_3383_);
v___x_3400_ = lean_string_append(v___x_3398_, v___x_3399_);
lean_dec_ref(v___x_3399_);
v___x_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set_tag(v___x_3390_, 1);
lean_ctor_set(v___x_3390_, 1, v___x_3401_);
v___x_3403_ = v___x_3390_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_pos_3387_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v___x_3401_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
else
{
lean_object* v___x_3405_; lean_object* v___x_3407_; 
lean_dec(v_m_3383_);
lean_dec(v_n_3382_);
v___x_3405_ = lean_nat_to_int(v_res_3388_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 1, v___x_3405_);
v___x_3407_ = v___x_3390_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_pos_3387_);
lean_ctor_set(v_reuseFailAlloc_3408_, 1, v___x_3405_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
}
else
{
lean_object* v_pos_3412_; lean_object* v_err_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec(v_m_3383_);
lean_dec(v_n_3382_);
v_pos_3412_ = lean_ctor_get(v___x_3386_, 0);
v_err_3413_ = lean_ctor_get(v___x_3386_, 1);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3386_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_err_3413_);
lean_inc(v_pos_3412_);
lean_dec(v___x_3386_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_pos_3412_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v_err_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(lean_object* v_a_3421_){
_start:
{
lean_object* v_fst_3425_; lean_object* v_snd_3426_; lean_object* v___x_3427_; uint8_t v_decide_3428_; 
v_fst_3425_ = lean_ctor_get(v_a_3421_, 0);
v_snd_3426_ = lean_ctor_get(v_a_3421_, 1);
v___x_3427_ = lean_string_utf8_byte_size(v_fst_3425_);
v_decide_3428_ = lean_nat_dec_eq(v_snd_3426_, v___x_3427_);
if (v_decide_3428_ == 0)
{
uint32_t v_c_3429_; uint32_t v___x_3430_; uint8_t v___x_3431_; 
v_c_3429_ = lean_string_utf8_get_fast(v_fst_3425_, v_snd_3426_);
v___x_3430_ = 48;
v___x_3431_ = lean_uint32_dec_le(v___x_3430_, v_c_3429_);
if (v___x_3431_ == 0)
{
goto v___jp_3422_;
}
else
{
uint32_t v___x_3432_; uint8_t v___x_3433_; 
v___x_3432_ = 57;
v___x_3433_ = lean_uint32_dec_le(v_c_3429_, v___x_3432_);
if (v___x_3433_ == 0)
{
goto v___jp_3422_;
}
else
{
lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3470_; 
lean_inc(v_snd_3426_);
lean_inc(v_fst_3425_);
v_isSharedCheck_3470_ = !lean_is_exclusive(v_a_3421_);
if (v_isSharedCheck_3470_ == 0)
{
lean_object* v_unused_3471_; lean_object* v_unused_3472_; 
v_unused_3471_ = lean_ctor_get(v_a_3421_, 1);
lean_dec(v_unused_3471_);
v_unused_3472_ = lean_ctor_get(v_a_3421_, 0);
lean_dec(v_unused_3472_);
v___x_3435_ = v_a_3421_;
v_isShared_3436_ = v_isSharedCheck_3470_;
goto v_resetjp_3434_;
}
else
{
lean_dec(v_a_3421_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3470_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3437_; lean_object* v_pos_3439_; lean_object* v_snd_3440_; lean_object* v_err_3441_; lean_object* v_it_x27_3449_; 
v___x_3437_ = lean_string_utf8_next_fast(v_fst_3425_, v_snd_3426_);
lean_dec(v_snd_3426_);
lean_inc(v_fst_3425_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 1, v___x_3437_);
v_it_x27_3449_ = v___x_3435_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_fst_3425_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v___x_3437_);
v_it_x27_3449_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3448_;
}
v___jp_3438_:
{
uint8_t v_decide_3442_; 
v_decide_3442_ = lean_nat_dec_eq(v___x_3437_, v_snd_3440_);
lean_dec(v_snd_3440_);
if (v_decide_3442_ == 0)
{
lean_object* v___x_3443_; 
lean_inc(v_err_3441_);
v___x_3443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3443_, 0, v_pos_3439_);
lean_ctor_set(v___x_3443_, 1, v_err_3441_);
return v___x_3443_;
}
else
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3444_ = lean_uint32_to_nat(v_c_3429_);
v___x_3445_ = lean_unsigned_to_nat(48u);
v___x_3446_ = lean_nat_sub(v___x_3444_, v___x_3445_);
lean_dec(v___x_3444_);
v___x_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3447_, 0, v_pos_3439_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
return v___x_3447_;
}
}
v_reusejp_3448_:
{
uint8_t v_decide_3454_; 
v_decide_3454_ = lean_nat_dec_eq(v___x_3437_, v___x_3427_);
if (v_decide_3454_ == 0)
{
if (v___x_3433_ == 0)
{
lean_dec(v_fst_3425_);
goto v___jp_3452_;
}
else
{
uint32_t v___x_3455_; uint8_t v___x_3456_; 
v___x_3455_ = lean_string_utf8_get_fast(v_fst_3425_, v___x_3437_);
v___x_3456_ = lean_uint32_dec_le(v___x_3430_, v___x_3455_);
if (v___x_3456_ == 0)
{
lean_dec(v_fst_3425_);
goto v___jp_3450_;
}
else
{
uint8_t v___x_3457_; 
v___x_3457_ = lean_uint32_dec_le(v___x_3455_, v___x_3432_);
if (v___x_3457_ == 0)
{
lean_dec(v_fst_3425_);
goto v___jp_3450_;
}
else
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
lean_dec_ref(v_it_x27_3449_);
v___x_3458_ = lean_string_utf8_next_fast(v_fst_3425_, v___x_3437_);
v___x_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3459_, 0, v_fst_3425_);
lean_ctor_set(v___x_3459_, 1, v___x_3458_);
v___x_3460_ = lean_uint32_to_nat(v_c_3429_);
v___x_3461_ = lean_unsigned_to_nat(48u);
v___x_3462_ = lean_nat_sub(v___x_3460_, v___x_3461_);
lean_dec(v___x_3460_);
v___x_3463_ = lean_unsigned_to_nat(10u);
v___x_3464_ = lean_nat_mul(v___x_3462_, v___x_3463_);
lean_dec(v___x_3462_);
v___x_3465_ = lean_uint32_to_nat(v___x_3455_);
v___x_3466_ = lean_nat_sub(v___x_3465_, v___x_3461_);
lean_dec(v___x_3465_);
v___x_3467_ = lean_nat_add(v___x_3464_, v___x_3466_);
lean_dec(v___x_3466_);
lean_dec(v___x_3464_);
v___x_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3459_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
return v___x_3468_;
}
}
}
}
else
{
lean_dec(v_fst_3425_);
goto v___jp_3452_;
}
v___jp_3450_:
{
lean_object* v___x_3451_; 
v___x_3451_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v_pos_3439_ = v_it_x27_3449_;
v_snd_3440_ = v___x_3437_;
v_err_3441_ = v___x_3451_;
goto v___jp_3438_;
}
v___jp_3452_:
{
lean_object* v___x_3453_; 
v___x_3453_ = lean_box(0);
v_pos_3439_ = v_it_x27_3449_;
v_snd_3440_ = v___x_3437_;
v_err_3441_ = v___x_3453_;
goto v___jp_3438_;
}
}
}
}
}
}
else
{
lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3473_ = lean_box(0);
v___x_3474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3474_, 0, v_a_3421_);
lean_ctor_set(v___x_3474_, 1, v___x_3473_);
return v___x_3474_;
}
v___jp_3422_:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3424_, 0, v_a_3421_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
return v___x_3424_;
}
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__0(void){
_start:
{
uint32_t v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3475_ = 58;
v___x_3476_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3477_ = lean_string_push(v___x_3476_, v___x_3475_);
return v___x_3477_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3478_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__0);
v___x_3479_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_3480_ = lean_string_append(v___x_3479_, v___x_3478_);
return v___x_3480_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3481_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3482_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__1);
v___x_3483_ = lean_string_append(v___x_3482_, v___x_3481_);
return v___x_3483_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__2);
v___x_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
return v___x_3485_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1(void){
_start:
{
uint32_t v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = 58;
v___x_3487_ = lean_box_uint32(v___x_3486_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(uint8_t v_withColon_3488_, lean_object* v___y_3489_){
_start:
{
if (v_withColon_3488_ == 0)
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3490_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1;
v___x_3491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___y_3489_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
return v___x_3491_;
}
else
{
lean_object* v_fst_3492_; lean_object* v_snd_3493_; lean_object* v___x_3494_; uint8_t v_decide_3495_; 
v_fst_3492_ = lean_ctor_get(v___y_3489_, 0);
v_snd_3493_ = lean_ctor_get(v___y_3489_, 1);
v___x_3494_ = lean_string_utf8_byte_size(v_fst_3492_);
v_decide_3495_ = lean_nat_dec_eq(v_snd_3493_, v___x_3494_);
if (v_decide_3495_ == 0)
{
uint32_t v___x_3496_; uint32_t v_c_3497_; uint8_t v___x_3498_; 
v___x_3496_ = 58;
v_c_3497_ = lean_string_utf8_get_fast(v_fst_3492_, v_snd_3493_);
v___x_3498_ = lean_uint32_dec_eq(v_c_3497_, v___x_3496_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3499_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__3);
v___x_3500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___y_3489_);
lean_ctor_set(v___x_3500_, 1, v___x_3499_);
return v___x_3500_;
}
else
{
lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3510_; 
lean_inc(v_snd_3493_);
lean_inc(v_fst_3492_);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___y_3489_);
if (v_isSharedCheck_3510_ == 0)
{
lean_object* v_unused_3511_; lean_object* v_unused_3512_; 
v_unused_3511_ = lean_ctor_get(v___y_3489_, 1);
lean_dec(v_unused_3511_);
v_unused_3512_ = lean_ctor_get(v___y_3489_, 0);
lean_dec(v_unused_3512_);
v___x_3502_ = v___y_3489_;
v_isShared_3503_ = v_isSharedCheck_3510_;
goto v_resetjp_3501_;
}
else
{
lean_dec(v___y_3489_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3510_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3504_; lean_object* v_it_x27_3506_; 
v___x_3504_ = lean_string_utf8_next_fast(v_fst_3492_, v_snd_3493_);
lean_dec(v_snd_3493_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 1, v___x_3504_);
v_it_x27_3506_ = v___x_3502_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_fst_3492_);
lean_ctor_set(v_reuseFailAlloc_3509_, 1, v___x_3504_);
v_it_x27_3506_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1;
v___x_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3508_, 0, v_it_x27_3506_);
lean_ctor_set(v___x_3508_, 1, v___x_3507_);
return v___x_3508_;
}
}
}
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = lean_box(0);
v___x_3514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3514_, 0, v___y_3489_);
lean_ctor_set(v___x_3514_, 1, v___x_3513_);
return v___x_3514_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed(lean_object* v_withColon_3515_, lean_object* v___y_3516_){
_start:
{
uint8_t v_withColon_boxed_3517_; lean_object* v_res_3518_; 
v_withColon_boxed_3517_ = lean_unbox(v_withColon_3515_);
v_res_3518_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(v_withColon_boxed_3517_, v___y_3516_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1(lean_object* v_a_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = lean_nat_to_int(v_a_3519_);
v___x_3522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___y_3520_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(lean_object* v___y_3523_, lean_object* v___f_3524_, lean_object* v_n_3525_, uint8_t v_reason_3526_, lean_object* v___y_3527_){
_start:
{
lean_object* v_pos_3529_; lean_object* v_err_3530_; 
switch(v_reason_3526_)
{
case 0:
{
lean_object* v___x_3546_; 
v___x_3546_ = lean_apply_1(v___y_3523_, v___y_3527_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_pos_3547_; lean_object* v___x_3548_; 
v_pos_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_pos_3547_);
lean_dec_ref_known(v___x_3546_, 2);
v___x_3548_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3547_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_pos_3549_; lean_object* v_res_3550_; lean_object* v___x_3551_; 
v_pos_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_pos_3549_);
v_res_3550_ = lean_ctor_get(v___x_3548_, 1);
lean_inc(v_res_3550_);
lean_dec_ref_known(v___x_3548_, 2);
v___x_3551_ = lean_apply_2(v___f_3524_, v_res_3550_, v_pos_3549_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_pos_3552_; lean_object* v_res_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3561_; 
v_pos_3552_ = lean_ctor_get(v___x_3551_, 0);
v_res_3553_ = lean_ctor_get(v___x_3551_, 1);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3555_ = v___x_3551_;
v_isShared_3556_ = v_isSharedCheck_3561_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_res_3553_);
lean_inc(v_pos_3552_);
lean_dec(v___x_3551_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3561_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3557_; lean_object* v___x_3559_; 
v___x_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3557_, 0, v_res_3553_);
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 1, v___x_3557_);
v___x_3559_ = v___x_3555_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_pos_3552_);
lean_ctor_set(v_reuseFailAlloc_3560_, 1, v___x_3557_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
else
{
lean_object* v_pos_3562_; lean_object* v_err_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
v_pos_3562_ = lean_ctor_get(v___x_3551_, 0);
v_err_3563_ = lean_ctor_get(v___x_3551_, 1);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3551_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_err_3563_);
lean_inc(v_pos_3562_);
lean_dec(v___x_3551_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_pos_3562_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_err_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
else
{
lean_object* v_pos_3571_; lean_object* v_err_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
lean_dec_ref(v___f_3524_);
v_pos_3571_ = lean_ctor_get(v___x_3548_, 0);
v_err_3572_ = lean_ctor_get(v___x_3548_, 1);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3548_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_err_3572_);
lean_inc(v_pos_3571_);
lean_dec(v___x_3548_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_pos_3571_);
lean_ctor_set(v_reuseFailAlloc_3578_, 1, v_err_3572_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
else
{
lean_object* v_pos_3580_; lean_object* v_err_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec_ref(v___f_3524_);
v_pos_3580_ = lean_ctor_get(v___x_3546_, 0);
v_err_3581_ = lean_ctor_get(v___x_3546_, 1);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3546_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_err_3581_);
lean_inc(v_pos_3580_);
lean_dec(v___x_3546_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_pos_3580_);
lean_ctor_set(v_reuseFailAlloc_3587_, 1, v_err_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
case 1:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; 
lean_dec_ref(v___f_3524_);
lean_dec_ref(v___y_3523_);
v___x_3589_ = lean_box(0);
v___x_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___y_3527_);
lean_ctor_set(v___x_3590_, 1, v___x_3589_);
return v___x_3590_;
}
default: 
{
lean_object* v___x_3591_; 
lean_inc_ref(v___y_3527_);
v___x_3591_ = lean_apply_1(v___y_3523_, v___y_3527_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_pos_3592_; lean_object* v___x_3593_; 
v_pos_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_pos_3592_);
lean_dec_ref_known(v___x_3591_, 2);
v___x_3593_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3592_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_pos_3594_; lean_object* v_res_3595_; lean_object* v___x_3596_; 
v_pos_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_pos_3594_);
v_res_3595_ = lean_ctor_get(v___x_3593_, 1);
lean_inc(v_res_3595_);
lean_dec_ref_known(v___x_3593_, 2);
v___x_3596_ = lean_apply_2(v___f_3524_, v_res_3595_, v_pos_3594_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_pos_3597_; lean_object* v_res_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3606_; 
lean_dec_ref(v___y_3527_);
v_pos_3597_ = lean_ctor_get(v___x_3596_, 0);
v_res_3598_ = lean_ctor_get(v___x_3596_, 1);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3600_ = v___x_3596_;
v_isShared_3601_ = v_isSharedCheck_3606_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_res_3598_);
lean_inc(v_pos_3597_);
lean_dec(v___x_3596_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3606_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; lean_object* v___x_3604_; 
v___x_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3602_, 0, v_res_3598_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 1, v___x_3602_);
v___x_3604_ = v___x_3600_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_pos_3597_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v___x_3602_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
else
{
lean_object* v_pos_3607_; lean_object* v_err_3608_; 
v_pos_3607_ = lean_ctor_get(v___x_3596_, 0);
lean_inc(v_pos_3607_);
v_err_3608_ = lean_ctor_get(v___x_3596_, 1);
lean_inc(v_err_3608_);
lean_dec_ref_known(v___x_3596_, 2);
v_pos_3529_ = v_pos_3607_;
v_err_3530_ = v_err_3608_;
goto v___jp_3528_;
}
}
else
{
lean_object* v_pos_3609_; lean_object* v_err_3610_; 
lean_dec_ref(v___f_3524_);
v_pos_3609_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_pos_3609_);
v_err_3610_ = lean_ctor_get(v___x_3593_, 1);
lean_inc(v_err_3610_);
lean_dec_ref_known(v___x_3593_, 2);
v_pos_3529_ = v_pos_3609_;
v_err_3530_ = v_err_3610_;
goto v___jp_3528_;
}
}
else
{
lean_object* v_pos_3611_; lean_object* v_err_3612_; 
lean_dec_ref(v___f_3524_);
v_pos_3611_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_pos_3611_);
v_err_3612_ = lean_ctor_get(v___x_3591_, 1);
lean_inc(v_err_3612_);
lean_dec_ref_known(v___x_3591_, 2);
v_pos_3529_ = v_pos_3611_;
v_err_3530_ = v_err_3612_;
goto v___jp_3528_;
}
}
}
v___jp_3528_:
{
lean_object* v_snd_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3544_; 
v_snd_3531_ = lean_ctor_get(v___y_3527_, 1);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___y_3527_);
if (v_isSharedCheck_3544_ == 0)
{
lean_object* v_unused_3545_; 
v_unused_3545_ = lean_ctor_get(v___y_3527_, 0);
lean_dec(v_unused_3545_);
v___x_3533_ = v___y_3527_;
v_isShared_3534_ = v_isSharedCheck_3544_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_snd_3531_);
lean_dec(v___y_3527_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3544_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v_snd_3535_; uint8_t v_decide_3536_; 
v_snd_3535_ = lean_ctor_get(v_pos_3529_, 1);
v_decide_3536_ = lean_nat_dec_eq(v_snd_3531_, v_snd_3535_);
lean_dec(v_snd_3531_);
if (v_decide_3536_ == 0)
{
lean_object* v___x_3538_; 
if (v_isShared_3534_ == 0)
{
lean_ctor_set_tag(v___x_3533_, 1);
lean_ctor_set(v___x_3533_, 1, v_err_3530_);
lean_ctor_set(v___x_3533_, 0, v_pos_3529_);
v___x_3538_ = v___x_3533_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_pos_3529_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_err_3530_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
else
{
lean_object* v___x_3540_; lean_object* v___x_3542_; 
lean_dec(v_err_3530_);
v___x_3540_ = lean_box(0);
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 1, v___x_3540_);
lean_ctor_set(v___x_3533_, 0, v_pos_3529_);
v___x_3542_ = v___x_3533_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_pos_3529_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v___x_3540_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2___boxed(lean_object* v___y_3613_, lean_object* v___f_3614_, lean_object* v_n_3615_, lean_object* v_reason_3616_, lean_object* v___y_3617_){
_start:
{
uint8_t v_reason_boxed_3618_; lean_object* v_res_3619_; 
v_reason_boxed_3618_ = lean_unbox(v_reason_3616_);
v_res_3619_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3613_, v___f_3614_, v_n_3615_, v_reason_boxed_3618_, v___y_3617_);
lean_dec_ref(v_n_3615_);
return v_res_3619_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0(void){
_start:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3620_ = lean_unsigned_to_nat(3600u);
v___x_3621_ = lean_nat_to_int(v___x_3620_);
return v___x_3621_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2(void){
_start:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; 
v___x_3623_ = lean_unsigned_to_nat(1u);
v___x_3624_ = l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(v___x_3623_);
return v___x_3624_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3(void){
_start:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3625_ = lean_unsigned_to_nat(59u);
v___x_3626_ = lean_nat_to_int(v___x_3625_);
return v___x_3626_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6(void){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3629_ = lean_unsigned_to_nat(60u);
v___x_3630_ = l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(v___x_3629_);
return v___x_3630_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10(void){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3634_ = lean_unsigned_to_nat(23u);
v___x_3635_ = lean_nat_to_int(v___x_3634_);
return v___x_3635_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11(void){
_start:
{
uint32_t v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3636_ = 45;
v___x_3637_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3638_ = lean_string_push(v___x_3637_, v___x_3636_);
return v___x_3638_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12(void){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3639_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11);
v___x_3640_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_3641_ = lean_string_append(v___x_3640_, v___x_3639_);
return v___x_3641_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13(void){
_start:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3642_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3643_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12);
v___x_3644_ = lean_string_append(v___x_3643_, v___x_3642_);
return v___x_3644_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14(void){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3645_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13);
v___x_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3645_);
return v___x_3646_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__15(void){
_start:
{
uint32_t v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3647_ = 43;
v___x_3648_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_3649_ = lean_string_push(v___x_3648_, v___x_3647_);
return v___x_3649_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__16(void){
_start:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3650_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__15);
v___x_3651_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0));
v___x_3652_ = lean_string_append(v___x_3651_, v___x_3650_);
return v___x_3652_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__17(void){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3653_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3654_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__16);
v___x_3655_ = lean_string_append(v___x_3654_, v___x_3653_);
return v___x_3655_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__18(void){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3656_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__17);
v___x_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(uint8_t v_withMinutes_3658_, uint8_t v_withSeconds_3659_, uint8_t v_withColon_3660_, lean_object* v_a_3661_){
_start:
{
lean_object* v___y_3663_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v_fst_3697_; lean_object* v_snd_3698_; lean_object* v___x_3699_; lean_object* v___y_3700_; lean_object* v___f_3701_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; uint8_t v___y_3752_; lean_object* v_pos_3800_; lean_object* v_res_3801_; lean_object* v_pos_3820_; lean_object* v_fst_3821_; lean_object* v_snd_3822_; lean_object* v_err_3823_; lean_object* v___x_3836_; uint8_t v_decide_3837_; 
v_fst_3697_ = lean_ctor_get(v_a_3661_, 0);
lean_inc(v_fst_3697_);
v_snd_3698_ = lean_ctor_get(v_a_3661_, 1);
lean_inc(v_snd_3698_);
v___x_3699_ = lean_box(v_withColon_3660_);
v___y_3700_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed), 2, 1);
lean_closure_set(v___y_3700_, 0, v___x_3699_);
v___f_3701_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__1));
v___x_3836_ = lean_string_utf8_byte_size(v_fst_3697_);
v_decide_3837_ = lean_nat_dec_eq(v_snd_3698_, v___x_3836_);
if (v_decide_3837_ == 0)
{
uint32_t v___x_3838_; uint32_t v_c_3839_; uint8_t v___x_3840_; 
v___x_3838_ = 43;
v_c_3839_ = lean_string_utf8_get_fast(v_fst_3697_, v_snd_3698_);
v___x_3840_ = lean_uint32_dec_eq(v_c_3839_, v___x_3838_);
if (v___x_3840_ == 0)
{
lean_object* v___x_3841_; 
v___x_3841_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__18, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__18_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__18);
lean_inc(v_snd_3698_);
v_pos_3820_ = v_a_3661_;
v_fst_3821_ = v_fst_3697_;
v_snd_3822_ = v_snd_3698_;
v_err_3823_ = v___x_3841_;
goto v___jp_3819_;
}
else
{
lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3850_; 
v_isSharedCheck_3850_ = !lean_is_exclusive(v_a_3661_);
if (v_isSharedCheck_3850_ == 0)
{
lean_object* v_unused_3851_; lean_object* v_unused_3852_; 
v_unused_3851_ = lean_ctor_get(v_a_3661_, 1);
lean_dec(v_unused_3851_);
v_unused_3852_ = lean_ctor_get(v_a_3661_, 0);
lean_dec(v_unused_3852_);
v___x_3843_ = v_a_3661_;
v_isShared_3844_ = v_isSharedCheck_3850_;
goto v_resetjp_3842_;
}
else
{
lean_dec(v_a_3661_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3850_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3845_; lean_object* v_it_x27_3847_; 
v___x_3845_ = lean_string_utf8_next_fast(v_fst_3697_, v_snd_3698_);
lean_dec(v_snd_3698_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 1, v___x_3845_);
v_it_x27_3847_ = v___x_3843_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_fst_3697_);
lean_ctor_set(v_reuseFailAlloc_3849_, 1, v___x_3845_);
v_it_x27_3847_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
lean_object* v___x_3848_; 
v___x_3848_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v_pos_3800_ = v_it_x27_3847_;
v_res_3801_ = v___x_3848_;
goto v___jp_3799_;
}
}
}
}
else
{
lean_object* v___x_3853_; 
v___x_3853_ = lean_box(0);
lean_inc(v_snd_3698_);
v_pos_3820_ = v_a_3661_;
v_fst_3821_ = v_fst_3697_;
v_snd_3822_ = v_snd_3698_;
v_err_3823_ = v___x_3853_;
goto v___jp_3819_;
}
v___jp_3662_:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3664_ = lean_box(0);
v___x_3665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3665_, 0, v___y_3663_);
lean_ctor_set(v___x_3665_, 1, v___x_3664_);
return v___x_3665_;
}
v___jp_3666_:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3671_ = lean_int_add(v___y_3667_, v___y_3670_);
lean_dec(v___y_3670_);
lean_dec(v___y_3667_);
v___x_3672_ = lean_int_mul(v___x_3671_, v___y_3669_);
lean_dec(v___x_3671_);
v___x_3673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___y_3668_);
lean_ctor_set(v___x_3673_, 1, v___x_3672_);
return v___x_3673_;
}
v___jp_3674_:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3682_ = lean_nat_to_int(v___y_3679_);
v___x_3683_ = lean_int_mul(v___y_3681_, v___x_3682_);
lean_dec(v___x_3682_);
lean_dec(v___y_3681_);
v___x_3684_ = lean_int_add(v___y_3677_, v___x_3683_);
lean_dec(v___x_3683_);
lean_dec(v___y_3677_);
if (lean_obj_tag(v___y_3676_) == 0)
{
lean_inc(v___y_3675_);
v___y_3667_ = v___x_3684_;
v___y_3668_ = v___y_3678_;
v___y_3669_ = v___y_3680_;
v___y_3670_ = v___y_3675_;
goto v___jp_3666_;
}
else
{
lean_object* v_val_3685_; 
v_val_3685_ = lean_ctor_get(v___y_3676_, 0);
lean_inc(v_val_3685_);
lean_dec_ref_known(v___y_3676_, 1);
v___y_3667_ = v___x_3684_;
v___y_3668_ = v___y_3678_;
v___y_3669_ = v___y_3680_;
v___y_3670_ = v_val_3685_;
goto v___jp_3666_;
}
}
v___jp_3686_:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3694_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0);
v___x_3695_ = lean_int_mul(v___y_3688_, v___x_3694_);
lean_dec(v___y_3688_);
if (lean_obj_tag(v___y_3689_) == 0)
{
lean_inc(v___y_3687_);
v___y_3675_ = v___y_3687_;
v___y_3676_ = v___y_3690_;
v___y_3677_ = v___x_3695_;
v___y_3678_ = v___y_3693_;
v___y_3679_ = v___y_3691_;
v___y_3680_ = v___y_3692_;
v___y_3681_ = v___y_3687_;
goto v___jp_3674_;
}
else
{
lean_object* v_val_3696_; 
v_val_3696_ = lean_ctor_get(v___y_3689_, 0);
lean_inc(v_val_3696_);
lean_dec_ref_known(v___y_3689_, 1);
v___y_3675_ = v___y_3687_;
v___y_3676_ = v___y_3690_;
v___y_3677_ = v___x_3695_;
v___y_3678_ = v___y_3693_;
v___y_3679_ = v___y_3691_;
v___y_3680_ = v___y_3692_;
v___y_3681_ = v_val_3696_;
goto v___jp_3674_;
}
}
v___jp_3702_:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3709_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2);
v___x_3710_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3700_, v___f_3701_, v___x_3709_, v_withSeconds_3659_, v___y_3708_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_res_3711_; 
v_res_3711_ = lean_ctor_get(v___x_3710_, 1);
lean_inc(v_res_3711_);
if (lean_obj_tag(v_res_3711_) == 1)
{
lean_object* v_pos_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3735_; 
v_pos_3712_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3735_ == 0)
{
lean_object* v_unused_3736_; 
v_unused_3736_ = lean_ctor_get(v___x_3710_, 1);
lean_dec(v_unused_3736_);
v___x_3714_ = v___x_3710_;
v_isShared_3715_ = v_isSharedCheck_3735_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_pos_3712_);
lean_dec(v___x_3710_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3735_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v_val_3716_; lean_object* v___x_3717_; uint8_t v___x_3718_; 
v_val_3716_ = lean_ctor_get(v_res_3711_, 0);
v___x_3717_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3);
v___x_3718_ = lean_int_dec_lt(v___x_3717_, v_val_3716_);
if (v___x_3718_ == 0)
{
lean_del_object(v___x_3714_);
v___y_3687_ = v___y_3703_;
v___y_3688_ = v___y_3704_;
v___y_3689_ = v___y_3705_;
v___y_3690_ = v_res_3711_;
v___y_3691_ = v___y_3706_;
v___y_3692_ = v___y_3707_;
v___y_3693_ = v_pos_3712_;
goto v___jp_3686_;
}
else
{
lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3733_; 
lean_inc(v_val_3716_);
lean_dec(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec(v___y_3704_);
v_isSharedCheck_3733_ = !lean_is_exclusive(v_res_3711_);
if (v_isSharedCheck_3733_ == 0)
{
lean_object* v_unused_3734_; 
v_unused_3734_ = lean_ctor_get(v_res_3711_, 0);
lean_dec(v_unused_3734_);
v___x_3720_ = v_res_3711_;
v_isShared_3721_ = v_isSharedCheck_3733_;
goto v_resetjp_3719_;
}
else
{
lean_dec(v_res_3711_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3733_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3728_; 
v___x_3722_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4));
v___x_3723_ = l_Int_repr(v_val_3716_);
lean_dec(v_val_3716_);
v___x_3724_ = lean_string_append(v___x_3722_, v___x_3723_);
lean_dec_ref(v___x_3723_);
v___x_3725_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5));
v___x_3726_ = lean_string_append(v___x_3724_, v___x_3725_);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v___x_3726_);
v___x_3728_ = v___x_3720_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3726_);
v___x_3728_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
lean_object* v___x_3730_; 
if (v_isShared_3715_ == 0)
{
lean_ctor_set_tag(v___x_3714_, 1);
lean_ctor_set(v___x_3714_, 1, v___x_3728_);
v___x_3730_ = v___x_3714_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_pos_3712_);
lean_ctor_set(v_reuseFailAlloc_3731_, 1, v___x_3728_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3737_; 
v_pos_3737_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_pos_3737_);
lean_dec_ref_known(v___x_3710_, 2);
v___y_3687_ = v___y_3703_;
v___y_3688_ = v___y_3704_;
v___y_3689_ = v___y_3705_;
v___y_3690_ = v_res_3711_;
v___y_3691_ = v___y_3706_;
v___y_3692_ = v___y_3707_;
v___y_3693_ = v_pos_3737_;
goto v___jp_3686_;
}
}
else
{
lean_object* v_pos_3738_; lean_object* v_err_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
lean_dec(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec(v___y_3704_);
v_pos_3738_ = lean_ctor_get(v___x_3710_, 0);
v_err_3739_ = lean_ctor_get(v___x_3710_, 1);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3710_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_err_3739_);
lean_inc(v_pos_3738_);
lean_dec(v___x_3710_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_pos_3738_);
lean_ctor_set(v_reuseFailAlloc_3745_, 1, v_err_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
v___jp_3747_:
{
if (v___y_3752_ == 0)
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3753_ = lean_unsigned_to_nat(60u);
v___x_3754_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6);
lean_inc_ref(v___y_3700_);
v___x_3755_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3700_, v___f_3701_, v___x_3754_, v_withMinutes_3658_, v___y_3750_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_res_3756_; 
v_res_3756_ = lean_ctor_get(v___x_3755_, 1);
lean_inc(v_res_3756_);
if (lean_obj_tag(v_res_3756_) == 1)
{
lean_object* v_pos_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3780_; 
v_pos_3757_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3780_ == 0)
{
lean_object* v_unused_3781_; 
v_unused_3781_ = lean_ctor_get(v___x_3755_, 1);
lean_dec(v_unused_3781_);
v___x_3759_ = v___x_3755_;
v_isShared_3760_ = v_isSharedCheck_3780_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_pos_3757_);
lean_dec(v___x_3755_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3780_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v_val_3761_; lean_object* v___x_3762_; uint8_t v___x_3763_; 
v_val_3761_ = lean_ctor_get(v_res_3756_, 0);
v___x_3762_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3);
v___x_3763_ = lean_int_dec_lt(v___x_3762_, v_val_3761_);
if (v___x_3763_ == 0)
{
lean_del_object(v___x_3759_);
v___y_3703_ = v___y_3748_;
v___y_3704_ = v___y_3749_;
v___y_3705_ = v_res_3756_;
v___y_3706_ = v___x_3753_;
v___y_3707_ = v___y_3751_;
v___y_3708_ = v_pos_3757_;
goto v___jp_3702_;
}
else
{
lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3778_; 
lean_inc(v_val_3761_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3700_);
v_isSharedCheck_3778_ = !lean_is_exclusive(v_res_3756_);
if (v_isSharedCheck_3778_ == 0)
{
lean_object* v_unused_3779_; 
v_unused_3779_ = lean_ctor_get(v_res_3756_, 0);
lean_dec(v_unused_3779_);
v___x_3765_ = v_res_3756_;
v_isShared_3766_ = v_isSharedCheck_3778_;
goto v_resetjp_3764_;
}
else
{
lean_dec(v_res_3756_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3778_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3773_; 
v___x_3767_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__7));
v___x_3768_ = l_Int_repr(v_val_3761_);
lean_dec(v_val_3761_);
v___x_3769_ = lean_string_append(v___x_3767_, v___x_3768_);
lean_dec_ref(v___x_3768_);
v___x_3770_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5));
v___x_3771_ = lean_string_append(v___x_3769_, v___x_3770_);
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 0, v___x_3771_);
v___x_3773_ = v___x_3765_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3771_);
v___x_3773_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
lean_object* v___x_3775_; 
if (v_isShared_3760_ == 0)
{
lean_ctor_set_tag(v___x_3759_, 1);
lean_ctor_set(v___x_3759_, 1, v___x_3773_);
v___x_3775_ = v___x_3759_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_pos_3757_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v___x_3773_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3782_; 
v_pos_3782_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_pos_3782_);
lean_dec_ref_known(v___x_3755_, 2);
v___y_3703_ = v___y_3748_;
v___y_3704_ = v___y_3749_;
v___y_3705_ = v_res_3756_;
v___y_3706_ = v___x_3753_;
v___y_3707_ = v___y_3751_;
v___y_3708_ = v_pos_3782_;
goto v___jp_3702_;
}
}
else
{
lean_object* v_pos_3783_; lean_object* v_err_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3700_);
v_pos_3783_ = lean_ctor_get(v___x_3755_, 0);
v_err_3784_ = lean_ctor_get(v___x_3755_, 1);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3755_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_err_3784_);
lean_inc(v_pos_3783_);
lean_dec(v___x_3755_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_pos_3783_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v_err_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
else
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
lean_dec_ref(v___y_3700_);
v___x_3792_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8));
v___x_3793_ = l_Int_repr(v___y_3749_);
lean_dec(v___y_3749_);
v___x_3794_ = lean_string_append(v___x_3792_, v___x_3793_);
lean_dec_ref(v___x_3793_);
v___x_3795_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9));
v___x_3796_ = lean_string_append(v___x_3794_, v___x_3795_);
v___x_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3796_);
v___x_3798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___y_3750_);
lean_ctor_set(v___x_3798_, 1, v___x_3797_);
return v___x_3798_;
}
}
v___jp_3799_:
{
lean_object* v___x_3802_; 
v___x_3802_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3800_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_pos_3803_; lean_object* v_res_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; uint8_t v___x_3807_; 
v_pos_3803_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_pos_3803_);
v_res_3804_ = lean_ctor_get(v___x_3802_, 1);
lean_inc(v_res_3804_);
lean_dec_ref_known(v___x_3802_, 2);
v___x_3805_ = lean_nat_to_int(v_res_3804_);
v___x_3806_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_3807_ = lean_int_dec_lt(v___x_3805_, v___x_3806_);
if (v___x_3807_ == 0)
{
lean_object* v___x_3808_; uint8_t v___x_3809_; 
v___x_3808_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10);
v___x_3809_ = lean_int_dec_lt(v___x_3808_, v___x_3805_);
v___y_3748_ = v___x_3806_;
v___y_3749_ = v___x_3805_;
v___y_3750_ = v_pos_3803_;
v___y_3751_ = v_res_3801_;
v___y_3752_ = v___x_3809_;
goto v___jp_3747_;
}
else
{
v___y_3748_ = v___x_3806_;
v___y_3749_ = v___x_3805_;
v___y_3750_ = v_pos_3803_;
v___y_3751_ = v_res_3801_;
v___y_3752_ = v___x_3807_;
goto v___jp_3747_;
}
}
else
{
lean_object* v_pos_3810_; lean_object* v_err_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_dec_ref(v___y_3700_);
v_pos_3810_ = lean_ctor_get(v___x_3802_, 0);
v_err_3811_ = lean_ctor_get(v___x_3802_, 1);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3802_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_err_3811_);
lean_inc(v_pos_3810_);
lean_dec(v___x_3802_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_pos_3810_);
lean_ctor_set(v_reuseFailAlloc_3817_, 1, v_err_3811_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
v___jp_3819_:
{
uint8_t v_decide_3824_; 
v_decide_3824_ = lean_nat_dec_eq(v_snd_3698_, v_snd_3822_);
lean_dec(v_snd_3698_);
if (v_decide_3824_ == 0)
{
lean_object* v___x_3825_; 
lean_dec(v_snd_3822_);
lean_dec(v_fst_3821_);
lean_dec_ref(v___y_3700_);
lean_inc(v_err_3823_);
v___x_3825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3825_, 0, v_pos_3820_);
lean_ctor_set(v___x_3825_, 1, v_err_3823_);
return v___x_3825_;
}
else
{
lean_object* v___x_3826_; uint8_t v_decide_3827_; 
v___x_3826_ = lean_string_utf8_byte_size(v_fst_3821_);
v_decide_3827_ = lean_nat_dec_eq(v_snd_3822_, v___x_3826_);
if (v_decide_3827_ == 0)
{
if (v_decide_3824_ == 0)
{
lean_dec(v_snd_3822_);
lean_dec(v_fst_3821_);
lean_dec_ref(v___y_3700_);
v___y_3663_ = v_pos_3820_;
goto v___jp_3662_;
}
else
{
uint32_t v___x_3828_; uint32_t v_c_3829_; uint8_t v___x_3830_; 
v___x_3828_ = 45;
v_c_3829_ = lean_string_utf8_get_fast(v_fst_3821_, v_snd_3822_);
v___x_3830_ = lean_uint32_dec_eq(v_c_3829_, v___x_3828_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
lean_dec(v_snd_3822_);
lean_dec(v_fst_3821_);
lean_dec_ref(v___y_3700_);
v___x_3831_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14);
v___x_3832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3832_, 0, v_pos_3820_);
lean_ctor_set(v___x_3832_, 1, v___x_3831_);
return v___x_3832_;
}
else
{
lean_object* v___x_3833_; lean_object* v_it_x27_3834_; lean_object* v___x_3835_; 
lean_dec_ref(v_pos_3820_);
v___x_3833_ = lean_string_utf8_next_fast(v_fst_3821_, v_snd_3822_);
lean_dec(v_snd_3822_);
v_it_x27_3834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3834_, 0, v_fst_3821_);
lean_ctor_set(v_it_x27_3834_, 1, v___x_3833_);
v___x_3835_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v_pos_3800_ = v_it_x27_3834_;
v_res_3801_ = v___x_3835_;
goto v___jp_3799_;
}
}
}
else
{
lean_dec(v_snd_3822_);
lean_dec(v_fst_3821_);
lean_dec_ref(v___y_3700_);
v___y_3663_ = v_pos_3820_;
goto v___jp_3662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___boxed(lean_object* v_withMinutes_3854_, lean_object* v_withSeconds_3855_, lean_object* v_withColon_3856_, lean_object* v_a_3857_){
_start:
{
uint8_t v_withMinutes_boxed_3858_; uint8_t v_withSeconds_boxed_3859_; uint8_t v_withColon_boxed_3860_; lean_object* v_res_3861_; 
v_withMinutes_boxed_3858_ = lean_unbox(v_withMinutes_3854_);
v_withSeconds_boxed_3859_ = lean_unbox(v_withSeconds_3855_);
v_withColon_boxed_3860_ = lean_unbox(v_withColon_3856_);
v_res_3861_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v_withMinutes_boxed_3858_, v_withSeconds_boxed_3859_, v_withColon_boxed_3860_, v_a_3857_);
return v_res_3861_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1(void){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = lean_unsigned_to_nat(2000u);
v___x_3865_ = lean_nat_to_int(v___x_3864_);
return v___x_3865_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5(void){
_start:
{
lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3871_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3872_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_3873_ = lean_int_sub(v___x_3872_, v___x_3871_);
return v___x_3873_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6(void){
_start:
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v_range_3876_; 
v___x_3874_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3875_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5);
v_range_3876_ = lean_int_add(v___x_3875_, v___x_3874_);
return v_range_3876_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(lean_object* v_config_3879_, lean_object* v_x_3880_, lean_object* v_a_3881_){
_start:
{
lean_object* v___y_3883_; 
switch(lean_obj_tag(v_x_3880_))
{
case 0:
{
uint8_t v_presentation_3909_; 
v_presentation_3909_ = lean_ctor_get_uint8(v_x_3880_, 0);
lean_dec_ref_known(v_x_3880_, 0);
switch(v_presentation_3909_)
{
case 1:
{
lean_object* v_dateformat_3910_; lean_object* v_symbols_3911_; lean_object* v___x_3912_; 
v_dateformat_3910_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_3910_);
lean_dec_ref(v_config_3879_);
v_symbols_3911_ = lean_ctor_get(v_dateformat_3910_, 1);
lean_inc_ref(v_symbols_3911_);
lean_dec_ref(v_dateformat_3910_);
v___x_3912_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraLong(v_symbols_3911_, v_a_3881_);
return v___x_3912_;
}
case 2:
{
lean_object* v_dateformat_3913_; lean_object* v_symbols_3914_; lean_object* v___x_3915_; 
v_dateformat_3913_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_3913_);
lean_dec_ref(v_config_3879_);
v_symbols_3914_ = lean_ctor_get(v_dateformat_3913_, 1);
lean_inc_ref(v_symbols_3914_);
lean_dec_ref(v_dateformat_3913_);
v___x_3915_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraNarrow(v_symbols_3914_, v_a_3881_);
return v___x_3915_;
}
default: 
{
lean_object* v_dateformat_3916_; lean_object* v_symbols_3917_; lean_object* v___x_3918_; 
v_dateformat_3916_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_3916_);
lean_dec_ref(v_config_3879_);
v_symbols_3917_ = lean_ctor_get(v_dateformat_3916_, 1);
lean_inc_ref(v_symbols_3917_);
lean_dec_ref(v_dateformat_3916_);
v___x_3918_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraShort(v_symbols_3917_, v_a_3881_);
return v___x_3918_;
}
}
}
case 1:
{
lean_object* v_presentation_3919_; 
lean_dec_ref(v_config_3879_);
v_presentation_3919_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_presentation_3919_);
lean_dec_ref_known(v_x_3880_, 1);
switch(lean_obj_tag(v_presentation_3919_))
{
case 0:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3920_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0));
v___x_3921_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3920_, v_a_3881_);
return v___x_3921_;
}
case 1:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3922_ = lean_unsigned_to_nat(2u);
v___x_3923_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3922_, v_a_3881_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_pos_3924_; lean_object* v_res_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3935_; 
v_pos_3924_ = lean_ctor_get(v___x_3923_, 0);
v_res_3925_ = lean_ctor_get(v___x_3923_, 1);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3927_ = v___x_3923_;
v_isShared_3928_ = v_isSharedCheck_3935_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_res_3925_);
lean_inc(v_pos_3924_);
lean_dec(v___x_3923_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3935_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3933_; 
v___x_3929_ = lean_nat_to_int(v_res_3925_);
v___x_3930_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_3931_ = lean_int_add(v___x_3930_, v___x_3929_);
lean_dec(v___x_3929_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 1, v___x_3931_);
v___x_3933_ = v___x_3927_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_pos_3924_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v___x_3931_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
else
{
lean_object* v_pos_3936_; lean_object* v_err_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
v_pos_3936_ = lean_ctor_get(v___x_3923_, 0);
v_err_3937_ = lean_ctor_get(v___x_3923_, 1);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3923_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_err_3937_);
lean_inc(v_pos_3936_);
lean_dec(v___x_3923_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_pos_3936_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v_err_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
case 2:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3945_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2));
v___x_3946_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3945_, v_a_3881_);
return v___x_3946_;
}
default: 
{
lean_object* v_num_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
v_num_3947_ = lean_ctor_get(v_presentation_3919_, 0);
lean_inc(v_num_3947_);
lean_dec_ref_known(v_presentation_3919_, 1);
v___x_3948_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed), 2, 1);
lean_closure_set(v___x_3948_, 0, v_num_3947_);
v___x_3949_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3948_, v_a_3881_);
return v___x_3949_;
}
}
}
case 2:
{
lean_object* v_presentation_3950_; 
lean_dec_ref(v_config_3879_);
v_presentation_3950_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_presentation_3950_);
lean_dec_ref_known(v_x_3880_, 1);
switch(lean_obj_tag(v_presentation_3950_))
{
case 0:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3951_ = lean_unsigned_to_nat(1u);
v___x_3952_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v___x_3951_, v_a_3881_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v_pos_3953_; lean_object* v_res_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3962_; 
v_pos_3953_ = lean_ctor_get(v___x_3952_, 0);
v_res_3954_ = lean_ctor_get(v___x_3952_, 1);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3956_ = v___x_3952_;
v_isShared_3957_ = v_isSharedCheck_3962_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_res_3954_);
lean_inc(v_pos_3953_);
lean_dec(v___x_3952_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3962_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3958_; lean_object* v___x_3960_; 
v___x_3958_ = lean_nat_to_int(v_res_3954_);
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 1, v___x_3958_);
v___x_3960_ = v___x_3956_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_pos_3953_);
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
v_pos_3963_ = lean_ctor_get(v___x_3952_, 0);
v_err_3964_ = lean_ctor_get(v___x_3952_, 1);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3952_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_err_3964_);
lean_inc(v_pos_3963_);
lean_dec(v___x_3952_);
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
case 1:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3972_ = lean_unsigned_to_nat(2u);
v___x_3973_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3972_, v_a_3881_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v_pos_3974_; lean_object* v_res_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3985_; 
v_pos_3974_ = lean_ctor_get(v___x_3973_, 0);
v_res_3975_ = lean_ctor_get(v___x_3973_, 1);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3977_ = v___x_3973_;
v_isShared_3978_ = v_isSharedCheck_3985_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_res_3975_);
lean_inc(v_pos_3974_);
lean_dec(v___x_3973_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3985_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3983_; 
v___x_3979_ = lean_nat_to_int(v_res_3975_);
v___x_3980_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_3981_ = lean_int_add(v___x_3980_, v___x_3979_);
lean_dec(v___x_3979_);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 1, v___x_3981_);
v___x_3983_ = v___x_3977_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_pos_3974_);
lean_ctor_set(v_reuseFailAlloc_3984_, 1, v___x_3981_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
else
{
lean_object* v_pos_3986_; lean_object* v_err_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3994_; 
v_pos_3986_ = lean_ctor_get(v___x_3973_, 0);
v_err_3987_ = lean_ctor_get(v___x_3973_, 1);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3989_ = v___x_3973_;
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_err_3987_);
lean_inc(v_pos_3986_);
lean_dec(v___x_3973_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_pos_3986_);
lean_ctor_set(v_reuseFailAlloc_3993_, 1, v_err_3987_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
}
case 2:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3995_ = lean_unsigned_to_nat(4u);
v___x_3996_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3995_, v_a_3881_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_pos_3997_; lean_object* v_res_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4006_; 
v_pos_3997_ = lean_ctor_get(v___x_3996_, 0);
v_res_3998_ = lean_ctor_get(v___x_3996_, 1);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_4000_ = v___x_3996_;
v_isShared_4001_ = v_isSharedCheck_4006_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_res_3998_);
lean_inc(v_pos_3997_);
lean_dec(v___x_3996_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4006_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4002_; lean_object* v___x_4004_; 
v___x_4002_ = lean_nat_to_int(v_res_3998_);
if (v_isShared_4001_ == 0)
{
lean_ctor_set(v___x_4000_, 1, v___x_4002_);
v___x_4004_ = v___x_4000_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_pos_3997_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v___x_4002_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
else
{
lean_object* v_pos_4007_; lean_object* v_err_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
v_pos_4007_ = lean_ctor_get(v___x_3996_, 0);
v_err_4008_ = lean_ctor_get(v___x_3996_, 1);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_3996_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_err_4008_);
lean_inc(v_pos_4007_);
lean_dec(v___x_3996_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_pos_4007_);
lean_ctor_set(v_reuseFailAlloc_4014_, 1, v_err_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
default: 
{
lean_object* v_num_4016_; lean_object* v___x_4017_; 
v_num_4016_ = lean_ctor_get(v_presentation_3950_, 0);
lean_inc(v_num_4016_);
lean_dec_ref_known(v_presentation_3950_, 1);
v___x_4017_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_num_4016_, v_a_3881_);
lean_dec(v_num_4016_);
if (lean_obj_tag(v___x_4017_) == 0)
{
lean_object* v_pos_4018_; lean_object* v_res_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4027_; 
v_pos_4018_ = lean_ctor_get(v___x_4017_, 0);
v_res_4019_ = lean_ctor_get(v___x_4017_, 1);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4017_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4021_ = v___x_4017_;
v_isShared_4022_ = v_isSharedCheck_4027_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_res_4019_);
lean_inc(v_pos_4018_);
lean_dec(v___x_4017_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4027_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4023_; lean_object* v___x_4025_; 
v___x_4023_ = lean_nat_to_int(v_res_4019_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 1, v___x_4023_);
v___x_4025_ = v___x_4021_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_pos_4018_);
lean_ctor_set(v_reuseFailAlloc_4026_, 1, v___x_4023_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
else
{
lean_object* v_pos_4028_; lean_object* v_err_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
v_pos_4028_ = lean_ctor_get(v___x_4017_, 0);
v_err_4029_ = lean_ctor_get(v___x_4017_, 1);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4017_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_4017_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_err_4029_);
lean_inc(v_pos_4028_);
lean_dec(v___x_4017_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_pos_4028_);
lean_ctor_set(v_reuseFailAlloc_4035_, 1, v_err_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
}
}
case 3:
{
lean_object* v_presentation_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
lean_dec_ref(v_config_3879_);
v_presentation_4037_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_presentation_4037_);
lean_dec_ref_known(v_x_3880_, 1);
v___x_4038_ = lean_unsigned_to_nat(1u);
v___x_4039_ = lean_unsigned_to_nat(366u);
v___x_4040_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4040_, 0, v_presentation_4037_);
v___x_4041_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4038_, v___x_4039_, v___x_4040_, v_a_3881_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_pos_4042_; lean_object* v_res_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4053_; 
v_pos_4042_ = lean_ctor_get(v___x_4041_, 0);
v_res_4043_ = lean_ctor_get(v___x_4041_, 1);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4045_ = v___x_4041_;
v_isShared_4046_ = v_isSharedCheck_4053_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_res_4043_);
lean_inc(v_pos_4042_);
lean_dec(v___x_4041_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4053_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
uint8_t v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4051_; 
v___x_4047_ = 1;
v___x_4048_ = lean_box(v___x_4047_);
v___x_4049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
lean_ctor_set(v___x_4049_, 1, v_res_4043_);
if (v_isShared_4046_ == 0)
{
lean_ctor_set(v___x_4045_, 1, v___x_4049_);
v___x_4051_ = v___x_4045_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_pos_4042_);
lean_ctor_set(v_reuseFailAlloc_4052_, 1, v___x_4049_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
else
{
lean_object* v_pos_4054_; lean_object* v_err_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
v_pos_4054_ = lean_ctor_get(v___x_4041_, 0);
v_err_4055_ = lean_ctor_get(v___x_4041_, 1);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_4041_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_err_4055_);
lean_inc(v_pos_4054_);
lean_dec(v___x_4041_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_pos_4054_);
lean_ctor_set(v_reuseFailAlloc_4061_, 1, v_err_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
case 4:
{
lean_object* v_presentation_4063_; 
v_presentation_4063_ = lean_ctor_get(v_x_3880_, 0);
lean_inc_ref(v_presentation_4063_);
lean_dec_ref_known(v_x_3880_, 1);
if (lean_obj_tag(v_presentation_4063_) == 0)
{
lean_object* v_val_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
lean_dec_ref(v_config_3879_);
v_val_4064_ = lean_ctor_get(v_presentation_4063_, 0);
lean_inc(v_val_4064_);
lean_dec_ref_known(v_presentation_4063_, 1);
v___x_4065_ = lean_unsigned_to_nat(1u);
v___x_4066_ = lean_unsigned_to_nat(12u);
v___x_4067_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4067_, 0, v_val_4064_);
v___x_4068_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4065_, v___x_4066_, v___x_4067_, v_a_3881_);
return v___x_4068_;
}
else
{
lean_object* v_val_4069_; uint8_t v___x_4070_; 
v_val_4069_ = lean_ctor_get(v_presentation_4063_, 0);
lean_inc(v_val_4069_);
lean_dec_ref_known(v_presentation_4063_, 1);
v___x_4070_ = lean_unbox(v_val_4069_);
lean_dec(v_val_4069_);
switch(v___x_4070_)
{
case 1:
{
lean_object* v_dateformat_4071_; lean_object* v_symbols_4072_; lean_object* v___x_4073_; 
v_dateformat_4071_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4071_);
lean_dec_ref(v_config_3879_);
v_symbols_4072_ = lean_ctor_get(v_dateformat_4071_, 1);
lean_inc_ref(v_symbols_4072_);
lean_dec_ref(v_dateformat_4071_);
v___x_4073_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(v_symbols_4072_, v_a_3881_);
return v___x_4073_;
}
case 2:
{
lean_object* v_dateformat_4074_; lean_object* v_symbols_4075_; lean_object* v___x_4076_; 
v_dateformat_4074_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4074_);
lean_dec_ref(v_config_3879_);
v_symbols_4075_ = lean_ctor_get(v_dateformat_4074_, 1);
lean_inc_ref(v_symbols_4075_);
lean_dec_ref(v_dateformat_4074_);
v___x_4076_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(v_symbols_4075_, v_a_3881_);
return v___x_4076_;
}
default: 
{
lean_object* v_dateformat_4077_; lean_object* v_symbols_4078_; lean_object* v___x_4079_; 
v_dateformat_4077_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4077_);
lean_dec_ref(v_config_3879_);
v_symbols_4078_ = lean_ctor_get(v_dateformat_4077_, 1);
lean_inc_ref(v_symbols_4078_);
lean_dec_ref(v_dateformat_4077_);
v___x_4079_ = l_Std_Time_parseMonthShort(v_symbols_4078_, v_a_3881_);
return v___x_4079_;
}
}
}
}
case 5:
{
lean_object* v_presentation_4080_; 
v_presentation_4080_ = lean_ctor_get(v_x_3880_, 0);
lean_inc_ref(v_presentation_4080_);
lean_dec_ref_known(v_x_3880_, 1);
if (lean_obj_tag(v_presentation_4080_) == 0)
{
lean_object* v_val_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; 
lean_dec_ref(v_config_3879_);
v_val_4081_ = lean_ctor_get(v_presentation_4080_, 0);
lean_inc(v_val_4081_);
lean_dec_ref_known(v_presentation_4080_, 1);
v___x_4082_ = lean_unsigned_to_nat(1u);
v___x_4083_ = lean_unsigned_to_nat(12u);
v___x_4084_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4084_, 0, v_val_4081_);
v___x_4085_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4082_, v___x_4083_, v___x_4084_, v_a_3881_);
return v___x_4085_;
}
else
{
lean_object* v_val_4086_; uint8_t v___x_4087_; 
v_val_4086_ = lean_ctor_get(v_presentation_4080_, 0);
lean_inc(v_val_4086_);
lean_dec_ref_known(v_presentation_4080_, 1);
v___x_4087_ = lean_unbox(v_val_4086_);
lean_dec(v_val_4086_);
switch(v___x_4087_)
{
case 1:
{
lean_object* v_dateformat_4088_; lean_object* v_symbols_4089_; lean_object* v___x_4090_; 
v_dateformat_4088_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4088_);
lean_dec_ref(v_config_3879_);
v_symbols_4089_ = lean_ctor_get(v_dateformat_4088_, 1);
lean_inc_ref(v_symbols_4089_);
lean_dec_ref(v_dateformat_4088_);
v___x_4090_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(v_symbols_4089_, v_a_3881_);
return v___x_4090_;
}
case 2:
{
lean_object* v_dateformat_4091_; lean_object* v_symbols_4092_; lean_object* v___x_4093_; 
v_dateformat_4091_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4091_);
lean_dec_ref(v_config_3879_);
v_symbols_4092_ = lean_ctor_get(v_dateformat_4091_, 1);
lean_inc_ref(v_symbols_4092_);
lean_dec_ref(v_dateformat_4091_);
v___x_4093_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(v_symbols_4092_, v_a_3881_);
return v___x_4093_;
}
default: 
{
lean_object* v_dateformat_4094_; lean_object* v_symbols_4095_; lean_object* v___x_4096_; 
v_dateformat_4094_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4094_);
lean_dec_ref(v_config_3879_);
v_symbols_4095_ = lean_ctor_get(v_dateformat_4094_, 1);
lean_inc_ref(v_symbols_4095_);
lean_dec_ref(v_dateformat_4094_);
v___x_4096_ = l_Std_Time_parseMonthShort(v_symbols_4095_, v_a_3881_);
return v___x_4096_;
}
}
}
}
case 6:
{
lean_object* v_presentation_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
lean_dec_ref(v_config_3879_);
v_presentation_4097_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_presentation_4097_);
lean_dec_ref_known(v_x_3880_, 1);
v___x_4098_ = lean_unsigned_to_nat(1u);
v___x_4099_ = lean_unsigned_to_nat(31u);
v___x_4100_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4100_, 0, v_presentation_4097_);
v___x_4101_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4098_, v___x_4099_, v___x_4100_, v_a_3881_);
return v___x_4101_;
}
case 7:
{
lean_object* v_presentation_4102_; 
v_presentation_4102_ = lean_ctor_get(v_x_3880_, 0);
lean_inc_ref(v_presentation_4102_);
lean_dec_ref_known(v_x_3880_, 1);
if (lean_obj_tag(v_presentation_4102_) == 0)
{
lean_object* v_val_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; 
lean_dec_ref(v_config_3879_);
v_val_4103_ = lean_ctor_get(v_presentation_4102_, 0);
lean_inc(v_val_4103_);
lean_dec_ref_known(v_presentation_4102_, 1);
v___x_4104_ = lean_unsigned_to_nat(1u);
v___x_4105_ = lean_unsigned_to_nat(4u);
v___x_4106_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4106_, 0, v_val_4103_);
v___x_4107_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4104_, v___x_4105_, v___x_4106_, v_a_3881_);
return v___x_4107_;
}
else
{
lean_object* v_val_4108_; uint8_t v___x_4109_; 
v_val_4108_ = lean_ctor_get(v_presentation_4102_, 0);
lean_inc(v_val_4108_);
lean_dec_ref_known(v_presentation_4102_, 1);
v___x_4109_ = lean_unbox(v_val_4108_);
lean_dec(v_val_4108_);
switch(v___x_4109_)
{
case 0:
{
lean_object* v_dateformat_4110_; lean_object* v_symbols_4111_; lean_object* v___x_4112_; 
v_dateformat_4110_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4110_);
lean_dec_ref(v_config_3879_);
v_symbols_4111_ = lean_ctor_get(v_dateformat_4110_, 1);
lean_inc_ref(v_symbols_4111_);
lean_dec_ref(v_dateformat_4110_);
v___x_4112_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(v_symbols_4111_, v_a_3881_);
return v___x_4112_;
}
case 1:
{
lean_object* v_dateformat_4113_; lean_object* v_symbols_4114_; lean_object* v___x_4115_; 
v_dateformat_4113_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4113_);
lean_dec_ref(v_config_3879_);
v_symbols_4114_ = lean_ctor_get(v_dateformat_4113_, 1);
lean_inc_ref(v_symbols_4114_);
lean_dec_ref(v_dateformat_4113_);
v___x_4115_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(v_symbols_4114_, v_a_3881_);
return v___x_4115_;
}
default: 
{
lean_object* v_dateformat_4116_; lean_object* v_symbols_4117_; lean_object* v___x_4118_; 
v_dateformat_4116_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4116_);
lean_dec_ref(v_config_3879_);
v_symbols_4117_ = lean_ctor_get(v_dateformat_4116_, 1);
lean_inc_ref(v_symbols_4117_);
lean_dec_ref(v_dateformat_4116_);
v___x_4118_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(v_symbols_4117_, v_a_3881_);
return v___x_4118_;
}
}
}
}
case 8:
{
lean_object* v_presentation_4119_; 
v_presentation_4119_ = lean_ctor_get(v_x_3880_, 0);
lean_inc_ref(v_presentation_4119_);
lean_dec_ref_known(v_x_3880_, 1);
if (lean_obj_tag(v_presentation_4119_) == 0)
{
lean_object* v_val_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
lean_dec_ref(v_config_3879_);
v_val_4120_ = lean_ctor_get(v_presentation_4119_, 0);
lean_inc(v_val_4120_);
lean_dec_ref_known(v_presentation_4119_, 1);
v___x_4121_ = lean_unsigned_to_nat(1u);
v___x_4122_ = lean_unsigned_to_nat(4u);
v___x_4123_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4123_, 0, v_val_4120_);
v___x_4124_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4121_, v___x_4122_, v___x_4123_, v_a_3881_);
return v___x_4124_;
}
else
{
lean_object* v_val_4125_; uint8_t v___x_4126_; 
v_val_4125_ = lean_ctor_get(v_presentation_4119_, 0);
lean_inc(v_val_4125_);
lean_dec_ref_known(v_presentation_4119_, 1);
v___x_4126_ = lean_unbox(v_val_4125_);
lean_dec(v_val_4125_);
switch(v___x_4126_)
{
case 0:
{
lean_object* v_dateformat_4127_; lean_object* v_symbols_4128_; lean_object* v___x_4129_; 
v_dateformat_4127_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4127_);
lean_dec_ref(v_config_3879_);
v_symbols_4128_ = lean_ctor_get(v_dateformat_4127_, 1);
lean_inc_ref(v_symbols_4128_);
lean_dec_ref(v_dateformat_4127_);
v___x_4129_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(v_symbols_4128_, v_a_3881_);
return v___x_4129_;
}
case 1:
{
lean_object* v_dateformat_4130_; lean_object* v_symbols_4131_; lean_object* v___x_4132_; 
v_dateformat_4130_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4130_);
lean_dec_ref(v_config_3879_);
v_symbols_4131_ = lean_ctor_get(v_dateformat_4130_, 1);
lean_inc_ref(v_symbols_4131_);
lean_dec_ref(v_dateformat_4130_);
v___x_4132_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(v_symbols_4131_, v_a_3881_);
return v___x_4132_;
}
default: 
{
lean_object* v_dateformat_4133_; lean_object* v_symbols_4134_; lean_object* v___x_4135_; 
v_dateformat_4133_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4133_);
lean_dec_ref(v_config_3879_);
v_symbols_4134_ = lean_ctor_get(v_dateformat_4133_, 1);
lean_inc_ref(v_symbols_4134_);
lean_dec_ref(v_dateformat_4133_);
v___x_4135_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(v_symbols_4134_, v_a_3881_);
return v___x_4135_;
}
}
}
}
case 9:
{
lean_object* v_presentation_4136_; 
lean_dec_ref(v_config_3879_);
v_presentation_4136_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_presentation_4136_);
lean_dec_ref_known(v_x_3880_, 1);
switch(lean_obj_tag(v_presentation_4136_))
{
case 0:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4137_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0));
v___x_4138_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4137_, v_a_3881_);
return v___x_4138_;
}
case 1:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4139_ = lean_unsigned_to_nat(2u);
v___x_4140_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_4139_, v_a_3881_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_pos_4141_; lean_object* v_res_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4152_; 
v_pos_4141_ = lean_ctor_get(v___x_4140_, 0);
v_res_4142_ = lean_ctor_get(v___x_4140_, 1);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4144_ = v___x_4140_;
v_isShared_4145_ = v_isSharedCheck_4152_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_res_4142_);
lean_inc(v_pos_4141_);
lean_dec(v___x_4140_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4152_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4150_; 
v___x_4146_ = lean_nat_to_int(v_res_4142_);
v___x_4147_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_4148_ = lean_int_add(v___x_4147_, v___x_4146_);
lean_dec(v___x_4146_);
if (v_isShared_4145_ == 0)
{
lean_ctor_set(v___x_4144_, 1, v___x_4148_);
v___x_4150_ = v___x_4144_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_pos_4141_);
lean_ctor_set(v_reuseFailAlloc_4151_, 1, v___x_4148_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
else
{
lean_object* v_pos_4153_; lean_object* v_err_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4161_; 
v_pos_4153_ = lean_ctor_get(v___x_4140_, 0);
v_err_4154_ = lean_ctor_get(v___x_4140_, 1);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4156_ = v___x_4140_;
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_err_4154_);
lean_inc(v_pos_4153_);
lean_dec(v___x_4140_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4159_; 
if (v_isShared_4157_ == 0)
{
v___x_4159_ = v___x_4156_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_pos_4153_);
lean_ctor_set(v_reuseFailAlloc_4160_, 1, v_err_4154_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
case 2:
{
lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4162_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2));
v___x_4163_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4162_, v_a_3881_);
return v___x_4163_;
}
default: 
{
lean_object* v_num_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
v_num_4164_ = lean_ctor_get(v_presentation_4136_, 0);
lean_inc(v_num_4164_);
lean_dec_ref_known(v_presentation_4136_, 1);
v___x_4165_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed), 2, 1);
lean_closure_set(v___x_4165_, 0, v_num_4164_);
v___x_4166_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4165_, v_a_3881_);
return v___x_4166_;
}
}
}
case 10:
{
lean_object* v_presentation_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
lean_dec_ref(v_config_3879_);
v_presentation_4167_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_presentation_4167_);
lean_dec_ref_known(v_x_3880_, 1);
v___x_4168_ = lean_unsigned_to_nat(1u);
v___x_4169_ = lean_unsigned_to_nat(53u);
v___x_4170_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4170_, 0, v_presentation_4167_);
v___x_4171_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4168_, v___x_4169_, v___x_4170_, v_a_3881_);
return v___x_4171_;
}
case 11:
{
lean_object* v_presentation_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
lean_dec_ref(v_config_3879_);
v_presentation_4172_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_presentation_4172_);
lean_dec_ref_known(v_x_3880_, 1);
v___x_4173_ = lean_unsigned_to_nat(1u);
v___x_4174_ = lean_unsigned_to_nat(6u);
v___x_4175_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4175_, 0, v_presentation_4172_);
v___x_4176_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4173_, v___x_4174_, v___x_4175_, v_a_3881_);
return v___x_4176_;
}
case 12:
{
uint8_t v_presentation_4177_; 
v_presentation_4177_ = lean_ctor_get_uint8(v_x_3880_, 0);
lean_dec_ref_known(v_x_3880_, 0);
switch(v_presentation_4177_)
{
case 1:
{
lean_object* v_dateformat_4178_; lean_object* v_symbols_4179_; lean_object* v___x_4180_; 
v_dateformat_4178_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4178_);
lean_dec_ref(v_config_3879_);
v_symbols_4179_ = lean_ctor_get(v_dateformat_4178_, 1);
lean_inc_ref(v_symbols_4179_);
lean_dec_ref(v_dateformat_4178_);
v___x_4180_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4179_, v_a_3881_);
return v___x_4180_;
}
case 2:
{
lean_object* v_dateformat_4181_; lean_object* v_symbols_4182_; lean_object* v___x_4183_; 
v_dateformat_4181_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4181_);
lean_dec_ref(v_config_3879_);
v_symbols_4182_ = lean_ctor_get(v_dateformat_4181_, 1);
lean_inc_ref(v_symbols_4182_);
lean_dec_ref(v_dateformat_4181_);
v___x_4183_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4182_, v_a_3881_);
return v___x_4183_;
}
default: 
{
lean_object* v_dateformat_4184_; lean_object* v_symbols_4185_; lean_object* v___x_4186_; 
v_dateformat_4184_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4184_);
lean_dec_ref(v_config_3879_);
v_symbols_4185_ = lean_ctor_get(v_dateformat_4184_, 1);
lean_inc_ref(v_symbols_4185_);
lean_dec_ref(v_dateformat_4184_);
v___x_4186_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4185_, v_a_3881_);
return v___x_4186_;
}
}
}
case 13:
{
lean_object* v_presentation_4187_; 
v_presentation_4187_ = lean_ctor_get(v_x_3880_, 0);
lean_inc_ref(v_presentation_4187_);
lean_dec_ref_known(v_x_3880_, 1);
if (lean_obj_tag(v_presentation_4187_) == 0)
{
lean_object* v_val_4188_; lean_object* v___x_4189_; 
v_val_4188_ = lean_ctor_get(v_presentation_4187_, 0);
lean_inc(v_val_4188_);
lean_dec_ref_known(v_presentation_4187_, 1);
v___x_4189_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_val_4188_, v_a_3881_);
lean_dec(v_val_4188_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_pos_4190_; lean_object* v_res_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4227_; 
v_pos_4190_ = lean_ctor_get(v___x_4189_, 0);
v_res_4191_ = lean_ctor_get(v___x_4189_, 1);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4193_ = v___x_4189_;
v_isShared_4194_ = v_isSharedCheck_4227_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_res_4191_);
lean_inc(v_pos_4190_);
lean_dec(v___x_4189_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4227_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4195_; uint8_t v___x_4196_; lean_object* v___x_4197_; uint8_t v___y_4199_; 
v___x_4195_ = lean_unsigned_to_nat(1u);
v___x_4196_ = lean_nat_dec_le(v___x_4195_, v_res_4191_);
v___x_4197_ = lean_unsigned_to_nat(7u);
if (v___x_4196_ == 0)
{
v___y_4199_ = v___x_4196_;
goto v___jp_4198_;
}
else
{
uint8_t v___x_4226_; 
v___x_4226_ = lean_nat_dec_le(v_res_4191_, v___x_4197_);
v___y_4199_ = v___x_4226_;
goto v___jp_4198_;
}
v___jp_4198_:
{
if (v___y_4199_ == 0)
{
lean_object* v___x_4200_; lean_object* v___x_4202_; 
lean_dec(v_res_4191_);
lean_dec_ref(v_config_3879_);
v___x_4200_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4));
if (v_isShared_4194_ == 0)
{
lean_ctor_set_tag(v___x_4193_, 1);
lean_ctor_set(v___x_4193_, 1, v___x_4200_);
v___x_4202_ = v___x_4193_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_pos_4190_);
lean_ctor_set(v_reuseFailAlloc_4203_, 1, v___x_4200_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
else
{
lean_object* v_dateformat_4204_; uint8_t v_firstDayOfWeek_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v_range_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; uint8_t v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4224_; 
v_dateformat_4204_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4204_);
lean_dec_ref(v_config_3879_);
v_firstDayOfWeek_4205_ = lean_ctor_get_uint8(v_dateformat_4204_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_4204_);
v___x_4206_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_4205_);
v___x_4207_ = lean_nat_to_int(v_res_4191_);
v___x_4208_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_4209_ = lean_int_sub(v___x_4207_, v___x_4208_);
lean_dec(v___x_4207_);
v___x_4210_ = lean_int_add(v___x_4209_, v___x_4206_);
lean_dec(v___x_4206_);
lean_dec(v___x_4209_);
v___x_4211_ = lean_int_sub(v___x_4210_, v___x_4208_);
lean_dec(v___x_4210_);
v___x_4212_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_4213_ = lean_int_emod(v___x_4211_, v___x_4212_);
lean_dec(v___x_4211_);
v___x_4214_ = lean_int_add(v___x_4213_, v___x_4208_);
lean_dec(v___x_4213_);
v_range_4215_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6);
v___x_4216_ = lean_int_sub(v___x_4214_, v___x_4208_);
lean_dec(v___x_4214_);
v___x_4217_ = lean_int_emod(v___x_4216_, v_range_4215_);
lean_dec(v___x_4216_);
v___x_4218_ = lean_int_add(v___x_4217_, v_range_4215_);
lean_dec(v___x_4217_);
v___x_4219_ = lean_int_emod(v___x_4218_, v_range_4215_);
lean_dec(v___x_4218_);
v___x_4220_ = lean_int_add(v___x_4219_, v___x_4208_);
lean_dec(v___x_4219_);
v___x_4221_ = l_Std_Time_Weekday_ofOrdinal(v___x_4220_);
lean_dec(v___x_4220_);
v___x_4222_ = lean_box(v___x_4221_);
if (v_isShared_4194_ == 0)
{
lean_ctor_set(v___x_4193_, 1, v___x_4222_);
v___x_4224_ = v___x_4193_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_pos_4190_);
lean_ctor_set(v_reuseFailAlloc_4225_, 1, v___x_4222_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
}
else
{
lean_object* v_pos_4228_; lean_object* v_err_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
lean_dec_ref(v_config_3879_);
v_pos_4228_ = lean_ctor_get(v___x_4189_, 0);
v_err_4229_ = lean_ctor_get(v___x_4189_, 1);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4189_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_err_4229_);
lean_inc(v_pos_4228_);
lean_dec(v___x_4189_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_pos_4228_);
lean_ctor_set(v_reuseFailAlloc_4235_, 1, v_err_4229_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
else
{
lean_object* v_val_4237_; uint8_t v___x_4238_; 
v_val_4237_ = lean_ctor_get(v_presentation_4187_, 0);
lean_inc(v_val_4237_);
lean_dec_ref_known(v_presentation_4187_, 1);
v___x_4238_ = lean_unbox(v_val_4237_);
lean_dec(v_val_4237_);
switch(v___x_4238_)
{
case 0:
{
lean_object* v_dateformat_4239_; lean_object* v_symbols_4240_; lean_object* v___x_4241_; 
v_dateformat_4239_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4239_);
lean_dec_ref(v_config_3879_);
v_symbols_4240_ = lean_ctor_get(v_dateformat_4239_, 1);
lean_inc_ref(v_symbols_4240_);
lean_dec_ref(v_dateformat_4239_);
v___x_4241_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4240_, v_a_3881_);
return v___x_4241_;
}
case 1:
{
lean_object* v_dateformat_4242_; lean_object* v_symbols_4243_; lean_object* v___x_4244_; 
v_dateformat_4242_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4242_);
lean_dec_ref(v_config_3879_);
v_symbols_4243_ = lean_ctor_get(v_dateformat_4242_, 1);
lean_inc_ref(v_symbols_4243_);
lean_dec_ref(v_dateformat_4242_);
v___x_4244_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4243_, v_a_3881_);
return v___x_4244_;
}
case 2:
{
lean_object* v_dateformat_4245_; lean_object* v_symbols_4246_; lean_object* v___x_4247_; 
v_dateformat_4245_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4245_);
lean_dec_ref(v_config_3879_);
v_symbols_4246_ = lean_ctor_get(v_dateformat_4245_, 1);
lean_inc_ref(v_symbols_4246_);
lean_dec_ref(v_dateformat_4245_);
v___x_4247_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4246_, v_a_3881_);
return v___x_4247_;
}
default: 
{
lean_object* v_dateformat_4248_; lean_object* v_symbols_4249_; lean_object* v___x_4250_; 
v_dateformat_4248_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4248_);
lean_dec_ref(v_config_3879_);
v_symbols_4249_ = lean_ctor_get(v_dateformat_4248_, 1);
lean_inc_ref(v_symbols_4249_);
lean_dec_ref(v_dateformat_4248_);
v___x_4250_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(v_symbols_4249_, v_a_3881_);
return v___x_4250_;
}
}
}
}
case 14:
{
lean_object* v_presentation_4251_; 
v_presentation_4251_ = lean_ctor_get(v_x_3880_, 0);
lean_inc_ref(v_presentation_4251_);
lean_dec_ref_known(v_x_3880_, 1);
if (lean_obj_tag(v_presentation_4251_) == 0)
{
lean_object* v_val_4252_; lean_object* v___x_4253_; 
v_val_4252_ = lean_ctor_get(v_presentation_4251_, 0);
lean_inc(v_val_4252_);
lean_dec_ref_known(v_presentation_4251_, 1);
v___x_4253_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_val_4252_, v_a_3881_);
lean_dec(v_val_4252_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_pos_4254_; lean_object* v_res_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4291_; 
v_pos_4254_ = lean_ctor_get(v___x_4253_, 0);
v_res_4255_ = lean_ctor_get(v___x_4253_, 1);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4257_ = v___x_4253_;
v_isShared_4258_ = v_isSharedCheck_4291_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_res_4255_);
lean_inc(v_pos_4254_);
lean_dec(v___x_4253_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4291_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v___x_4259_; uint8_t v___x_4260_; lean_object* v___x_4261_; uint8_t v___y_4263_; 
v___x_4259_ = lean_unsigned_to_nat(1u);
v___x_4260_ = lean_nat_dec_le(v___x_4259_, v_res_4255_);
v___x_4261_ = lean_unsigned_to_nat(7u);
if (v___x_4260_ == 0)
{
v___y_4263_ = v___x_4260_;
goto v___jp_4262_;
}
else
{
uint8_t v___x_4290_; 
v___x_4290_ = lean_nat_dec_le(v_res_4255_, v___x_4261_);
v___y_4263_ = v___x_4290_;
goto v___jp_4262_;
}
v___jp_4262_:
{
if (v___y_4263_ == 0)
{
lean_object* v___x_4264_; lean_object* v___x_4266_; 
lean_dec(v_res_4255_);
lean_dec_ref(v_config_3879_);
v___x_4264_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4));
if (v_isShared_4258_ == 0)
{
lean_ctor_set_tag(v___x_4257_, 1);
lean_ctor_set(v___x_4257_, 1, v___x_4264_);
v___x_4266_ = v___x_4257_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_pos_4254_);
lean_ctor_set(v_reuseFailAlloc_4267_, 1, v___x_4264_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
else
{
lean_object* v_dateformat_4268_; uint8_t v_firstDayOfWeek_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v_range_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; uint8_t v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4288_; 
v_dateformat_4268_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4268_);
lean_dec_ref(v_config_3879_);
v_firstDayOfWeek_4269_ = lean_ctor_get_uint8(v_dateformat_4268_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_4268_);
v___x_4270_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_4269_);
v___x_4271_ = lean_nat_to_int(v_res_4255_);
v___x_4272_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_4273_ = lean_int_sub(v___x_4271_, v___x_4272_);
lean_dec(v___x_4271_);
v___x_4274_ = lean_int_add(v___x_4273_, v___x_4270_);
lean_dec(v___x_4270_);
lean_dec(v___x_4273_);
v___x_4275_ = lean_int_sub(v___x_4274_, v___x_4272_);
lean_dec(v___x_4274_);
v___x_4276_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_4277_ = lean_int_emod(v___x_4275_, v___x_4276_);
lean_dec(v___x_4275_);
v___x_4278_ = lean_int_add(v___x_4277_, v___x_4272_);
lean_dec(v___x_4277_);
v_range_4279_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6);
v___x_4280_ = lean_int_sub(v___x_4278_, v___x_4272_);
lean_dec(v___x_4278_);
v___x_4281_ = lean_int_emod(v___x_4280_, v_range_4279_);
lean_dec(v___x_4280_);
v___x_4282_ = lean_int_add(v___x_4281_, v_range_4279_);
lean_dec(v___x_4281_);
v___x_4283_ = lean_int_emod(v___x_4282_, v_range_4279_);
lean_dec(v___x_4282_);
v___x_4284_ = lean_int_add(v___x_4283_, v___x_4272_);
lean_dec(v___x_4283_);
v___x_4285_ = l_Std_Time_Weekday_ofOrdinal(v___x_4284_);
lean_dec(v___x_4284_);
v___x_4286_ = lean_box(v___x_4285_);
if (v_isShared_4258_ == 0)
{
lean_ctor_set(v___x_4257_, 1, v___x_4286_);
v___x_4288_ = v___x_4257_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_pos_4254_);
lean_ctor_set(v_reuseFailAlloc_4289_, 1, v___x_4286_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
}
}
else
{
lean_object* v_pos_4292_; lean_object* v_err_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
lean_dec_ref(v_config_3879_);
v_pos_4292_ = lean_ctor_get(v___x_4253_, 0);
v_err_4293_ = lean_ctor_get(v___x_4253_, 1);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v___x_4253_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_err_4293_);
lean_inc(v_pos_4292_);
lean_dec(v___x_4253_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4298_; 
if (v_isShared_4296_ == 0)
{
v___x_4298_ = v___x_4295_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_pos_4292_);
lean_ctor_set(v_reuseFailAlloc_4299_, 1, v_err_4293_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
}
else
{
lean_object* v_val_4301_; uint8_t v___x_4302_; 
v_val_4301_ = lean_ctor_get(v_presentation_4251_, 0);
lean_inc(v_val_4301_);
lean_dec_ref_known(v_presentation_4251_, 1);
v___x_4302_ = lean_unbox(v_val_4301_);
lean_dec(v_val_4301_);
switch(v___x_4302_)
{
case 0:
{
lean_object* v_dateformat_4303_; lean_object* v_symbols_4304_; lean_object* v___x_4305_; 
v_dateformat_4303_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4303_);
lean_dec_ref(v_config_3879_);
v_symbols_4304_ = lean_ctor_get(v_dateformat_4303_, 1);
lean_inc_ref(v_symbols_4304_);
lean_dec_ref(v_dateformat_4303_);
v___x_4305_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4304_, v_a_3881_);
return v___x_4305_;
}
case 1:
{
lean_object* v_dateformat_4306_; lean_object* v_symbols_4307_; lean_object* v___x_4308_; 
v_dateformat_4306_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4306_);
lean_dec_ref(v_config_3879_);
v_symbols_4307_ = lean_ctor_get(v_dateformat_4306_, 1);
lean_inc_ref(v_symbols_4307_);
lean_dec_ref(v_dateformat_4306_);
v___x_4308_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4307_, v_a_3881_);
return v___x_4308_;
}
case 2:
{
lean_object* v_dateformat_4309_; lean_object* v_symbols_4310_; lean_object* v___x_4311_; 
v_dateformat_4309_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4309_);
lean_dec_ref(v_config_3879_);
v_symbols_4310_ = lean_ctor_get(v_dateformat_4309_, 1);
lean_inc_ref(v_symbols_4310_);
lean_dec_ref(v_dateformat_4309_);
v___x_4311_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4310_, v_a_3881_);
return v___x_4311_;
}
default: 
{
lean_object* v_dateformat_4312_; lean_object* v_symbols_4313_; lean_object* v___x_4314_; 
v_dateformat_4312_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4312_);
lean_dec_ref(v_config_3879_);
v_symbols_4313_ = lean_ctor_get(v_dateformat_4312_, 1);
lean_inc_ref(v_symbols_4313_);
lean_dec_ref(v_dateformat_4312_);
v___x_4314_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(v_symbols_4313_, v_a_3881_);
return v___x_4314_;
}
}
}
}
case 15:
{
lean_object* v_presentation_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
lean_dec_ref(v_config_3879_);
v_presentation_4315_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_presentation_4315_);
lean_dec_ref_known(v_x_3880_, 1);
v___x_4316_ = lean_unsigned_to_nat(1u);
v___x_4317_ = lean_unsigned_to_nat(5u);
v___x_4318_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4318_, 0, v_presentation_4315_);
v___x_4319_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4316_, v___x_4317_, v___x_4318_, v_a_3881_);
return v___x_4319_;
}
case 16:
{
uint8_t v_presentation_4320_; 
v_presentation_4320_ = lean_ctor_get_uint8(v_x_3880_, 0);
lean_dec_ref_known(v_x_3880_, 0);
switch(v_presentation_4320_)
{
case 1:
{
lean_object* v_dateformat_4321_; lean_object* v_symbols_4322_; lean_object* v___x_4323_; 
v_dateformat_4321_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4321_);
lean_dec_ref(v_config_3879_);
v_symbols_4322_ = lean_ctor_get(v_dateformat_4321_, 1);
lean_inc_ref(v_symbols_4322_);
lean_dec_ref(v_dateformat_4321_);
v___x_4323_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerLong(v_symbols_4322_, v_a_3881_);
return v___x_4323_;
}
case 2:
{
lean_object* v_dateformat_4324_; lean_object* v_symbols_4325_; lean_object* v___x_4326_; 
v_dateformat_4324_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4324_);
lean_dec_ref(v_config_3879_);
v_symbols_4325_ = lean_ctor_get(v_dateformat_4324_, 1);
lean_inc_ref(v_symbols_4325_);
lean_dec_ref(v_dateformat_4324_);
v___x_4326_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerNarrow(v_symbols_4325_, v_a_3881_);
return v___x_4326_;
}
default: 
{
lean_object* v_dateformat_4327_; lean_object* v_symbols_4328_; lean_object* v___x_4329_; 
v_dateformat_4327_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4327_);
lean_dec_ref(v_config_3879_);
v_symbols_4328_ = lean_ctor_get(v_dateformat_4327_, 1);
lean_inc_ref(v_symbols_4328_);
lean_dec_ref(v_dateformat_4327_);
v___x_4329_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerShort(v_symbols_4328_, v_a_3881_);
return v___x_4329_;
}
}
}
case 17:
{
uint8_t v_presentation_4330_; 
v_presentation_4330_ = lean_ctor_get_uint8(v_x_3880_, 0);
lean_dec_ref_known(v_x_3880_, 0);
switch(v_presentation_4330_)
{
case 1:
{
lean_object* v_dateformat_4331_; lean_object* v_symbols_4332_; lean_object* v_dayPeriodLong_4333_; lean_object* v___x_4334_; 
v_dateformat_4331_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4331_);
lean_dec_ref(v_config_3879_);
v_symbols_4332_ = lean_ctor_get(v_dateformat_4331_, 1);
lean_inc_ref(v_symbols_4332_);
lean_dec_ref(v_dateformat_4331_);
v_dayPeriodLong_4333_ = lean_ctor_get(v_symbols_4332_, 20);
lean_inc_ref(v_dayPeriodLong_4333_);
lean_dec_ref(v_symbols_4332_);
v___x_4334_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodLong_4333_, v_a_3881_);
return v___x_4334_;
}
case 2:
{
lean_object* v_dateformat_4335_; lean_object* v_symbols_4336_; lean_object* v_dayPeriodNarrow_4337_; lean_object* v___x_4338_; 
v_dateformat_4335_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4335_);
lean_dec_ref(v_config_3879_);
v_symbols_4336_ = lean_ctor_get(v_dateformat_4335_, 1);
lean_inc_ref(v_symbols_4336_);
lean_dec_ref(v_dateformat_4335_);
v_dayPeriodNarrow_4337_ = lean_ctor_get(v_symbols_4336_, 21);
lean_inc_ref(v_dayPeriodNarrow_4337_);
lean_dec_ref(v_symbols_4336_);
v___x_4338_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodNarrow_4337_, v_a_3881_);
return v___x_4338_;
}
default: 
{
lean_object* v_dateformat_4339_; lean_object* v_symbols_4340_; lean_object* v_dayPeriodShort_4341_; lean_object* v___x_4342_; 
v_dateformat_4339_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4339_);
lean_dec_ref(v_config_3879_);
v_symbols_4340_ = lean_ctor_get(v_dateformat_4339_, 1);
lean_inc_ref(v_symbols_4340_);
lean_dec_ref(v_dateformat_4339_);
v_dayPeriodShort_4341_ = lean_ctor_get(v_symbols_4340_, 19);
lean_inc_ref(v_dayPeriodShort_4341_);
lean_dec_ref(v_symbols_4340_);
v___x_4342_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodShort_4341_, v_a_3881_);
return v___x_4342_;
}
}
}
case 18:
{
uint8_t v_presentation_4343_; 
v_presentation_4343_ = lean_ctor_get_uint8(v_x_3880_, 0);
lean_dec_ref_known(v_x_3880_, 0);
switch(v_presentation_4343_)
{
case 1:
{
lean_object* v_dateformat_4344_; lean_object* v_symbols_4345_; lean_object* v_extendedDayPeriodLong_4346_; lean_object* v___x_4347_; 
v_dateformat_4344_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4344_);
lean_dec_ref(v_config_3879_);
v_symbols_4345_ = lean_ctor_get(v_dateformat_4344_, 1);
lean_inc_ref(v_symbols_4345_);
lean_dec_ref(v_dateformat_4344_);
v_extendedDayPeriodLong_4346_ = lean_ctor_get(v_symbols_4345_, 23);
lean_inc_ref(v_extendedDayPeriodLong_4346_);
lean_dec_ref(v_symbols_4345_);
v___x_4347_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodLong_4346_, v_a_3881_);
lean_dec_ref(v_extendedDayPeriodLong_4346_);
return v___x_4347_;
}
case 2:
{
lean_object* v_dateformat_4348_; lean_object* v_symbols_4349_; lean_object* v_extendedDayPeriodNarrow_4350_; lean_object* v___x_4351_; 
v_dateformat_4348_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4348_);
lean_dec_ref(v_config_3879_);
v_symbols_4349_ = lean_ctor_get(v_dateformat_4348_, 1);
lean_inc_ref(v_symbols_4349_);
lean_dec_ref(v_dateformat_4348_);
v_extendedDayPeriodNarrow_4350_ = lean_ctor_get(v_symbols_4349_, 24);
lean_inc_ref(v_extendedDayPeriodNarrow_4350_);
lean_dec_ref(v_symbols_4349_);
v___x_4351_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodNarrow_4350_, v_a_3881_);
lean_dec_ref(v_extendedDayPeriodNarrow_4350_);
return v___x_4351_;
}
default: 
{
lean_object* v_dateformat_4352_; lean_object* v_symbols_4353_; lean_object* v_extendedDayPeriodShort_4354_; lean_object* v___x_4355_; 
v_dateformat_4352_ = lean_ctor_get(v_config_3879_, 0);
lean_inc_ref(v_dateformat_4352_);
lean_dec_ref(v_config_3879_);
v_symbols_4353_ = lean_ctor_get(v_dateformat_4352_, 1);
lean_inc_ref(v_symbols_4353_);
lean_dec_ref(v_dateformat_4352_);
v_extendedDayPeriodShort_4354_ = lean_ctor_get(v_symbols_4353_, 22);
lean_inc_ref(v_extendedDayPeriodShort_4354_);
lean_dec_ref(v_symbols_4353_);
v___x_4355_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodShort_4354_, v_a_3881_);
lean_dec_ref(v_extendedDayPeriodShort_4354_);
return v___x_4355_;
}
}
}
case 19:
{
lean_object* v_presentation_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
lean_dec_ref(v_config_3879_);
v_presentation_4356_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_presentation_4356_);
lean_dec_ref_known(v_x_3880_, 1);
v___x_4357_ = lean_unsigned_to_nat(1u);
v___x_4358_ = lean_unsigned_to_nat(12u);
v___x_4359_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4359_, 0, v_presentation_4356_);
v___x_4360_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4357_, v___x_4358_, v___x_4359_, v_a_3881_);
return v___x_4360_;
}
case 20:
{
lean_object* v_presentation_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
lean_dec_ref(v_config_3879_);
v_presentation_4361_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_presentation_4361_);
lean_dec_ref_known(v_x_3880_, 1);
v___x_4362_ = lean_unsigned_to_nat(0u);
v___x_4363_ = lean_unsigned_to_nat(11u);
v___x_4364_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4364_, 0, v_presentation_4361_);
v___x_4365_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4362_, v___x_4363_, v___x_4364_, v_a_3881_);
return v___x_4365_;
}
case 21:
{
lean_object* v_presentation_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
lean_dec_ref(v_config_3879_);
v_presentation_4366_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_presentation_4366_);
lean_dec_ref_known(v_x_3880_, 1);
v___x_4367_ = lean_unsigned_to_nat(1u);
v___x_4368_ = lean_unsigned_to_nat(24u);
v___x_4369_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4369_, 0, v_presentation_4366_);
v___x_4370_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4367_, v___x_4368_, v___x_4369_, v_a_3881_);
return v___x_4370_;
}
case 22:
{
lean_object* v_presentation_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
lean_dec_ref(v_config_3879_);
v_presentation_4371_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_presentation_4371_);
lean_dec_ref_known(v_x_3880_, 1);
v___x_4372_ = lean_unsigned_to_nat(0u);
v___x_4373_ = lean_unsigned_to_nat(23u);
v___x_4374_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4374_, 0, v_presentation_4371_);
v___x_4375_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4372_, v___x_4373_, v___x_4374_, v_a_3881_);
return v___x_4375_;
}
case 23:
{
lean_object* v_presentation_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
lean_dec_ref(v_config_3879_);
v_presentation_4376_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_presentation_4376_);
lean_dec_ref_known(v_x_3880_, 1);
v___x_4377_ = lean_unsigned_to_nat(0u);
v___x_4378_ = lean_unsigned_to_nat(59u);
v___x_4379_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4379_, 0, v_presentation_4376_);
v___x_4380_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4377_, v___x_4378_, v___x_4379_, v_a_3881_);
return v___x_4380_;
}
case 24:
{
uint8_t v_allowLeapSeconds_4381_; 
v_allowLeapSeconds_4381_ = lean_ctor_get_uint8(v_config_3879_, sizeof(void*)*1);
lean_dec_ref(v_config_3879_);
if (v_allowLeapSeconds_4381_ == 0)
{
lean_object* v_presentation_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
v_presentation_4382_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_presentation_4382_);
lean_dec_ref_known(v_x_3880_, 1);
v___x_4383_ = lean_unsigned_to_nat(0u);
v___x_4384_ = lean_unsigned_to_nat(59u);
v___x_4385_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4385_, 0, v_presentation_4382_);
v___x_4386_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4383_, v___x_4384_, v___x_4385_, v_a_3881_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_object* v_pos_4387_; lean_object* v_res_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4395_; 
v_pos_4387_ = lean_ctor_get(v___x_4386_, 0);
v_res_4388_ = lean_ctor_get(v___x_4386_, 1);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4390_ = v___x_4386_;
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_res_4388_);
lean_inc(v_pos_4387_);
lean_dec(v___x_4386_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4393_; 
if (v_isShared_4391_ == 0)
{
v___x_4393_ = v___x_4390_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_pos_4387_);
lean_ctor_set(v_reuseFailAlloc_4394_, 1, v_res_4388_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
else
{
return v___x_4386_;
}
}
else
{
lean_object* v_presentation_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v_presentation_4396_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_presentation_4396_);
lean_dec_ref_known(v_x_3880_, 1);
v___x_4397_ = lean_unsigned_to_nat(0u);
v___x_4398_ = lean_unsigned_to_nat(60u);
v___x_4399_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4399_, 0, v_presentation_4396_);
v___x_4400_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4397_, v___x_4398_, v___x_4399_, v_a_3881_);
return v___x_4400_;
}
}
case 25:
{
lean_object* v_presentation_4401_; 
lean_dec_ref(v_config_3879_);
v_presentation_4401_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_presentation_4401_);
lean_dec_ref_known(v_x_3880_, 1);
if (lean_obj_tag(v_presentation_4401_) == 0)
{
lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4402_ = lean_unsigned_to_nat(0u);
v___x_4403_ = lean_unsigned_to_nat(999999999u);
v___x_4404_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__7));
v___x_4405_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4402_, v___x_4403_, v___x_4404_, v_a_3881_);
return v___x_4405_;
}
else
{
lean_object* v_digits_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v_digits_4406_ = lean_ctor_get(v_presentation_4401_, 0);
lean_inc(v_digits_4406_);
lean_dec_ref_known(v_presentation_4401_, 1);
v___x_4407_ = lean_unsigned_to_nat(0u);
v___x_4408_ = lean_unsigned_to_nat(999999999u);
v___x_4409_ = lean_unsigned_to_nat(9u);
v___x_4410_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed), 3, 2);
lean_closure_set(v___x_4410_, 0, v_digits_4406_);
lean_closure_set(v___x_4410_, 1, v___x_4409_);
v___x_4411_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4407_, v___x_4408_, v___x_4410_, v_a_3881_);
return v___x_4411_;
}
}
case 26:
{
lean_object* v_presentation_4412_; lean_object* v___x_4413_; 
lean_dec_ref(v_config_3879_);
v_presentation_4412_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_presentation_4412_);
lean_dec_ref_known(v_x_3880_, 1);
v___x_4413_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_presentation_4412_, v_a_3881_);
lean_dec(v_presentation_4412_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v_pos_4414_; lean_object* v_res_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4423_; 
v_pos_4414_ = lean_ctor_get(v___x_4413_, 0);
v_res_4415_ = lean_ctor_get(v___x_4413_, 1);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4417_ = v___x_4413_;
v_isShared_4418_ = v_isSharedCheck_4423_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_res_4415_);
lean_inc(v_pos_4414_);
lean_dec(v___x_4413_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4423_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4419_; lean_object* v___x_4421_; 
v___x_4419_ = lean_nat_to_int(v_res_4415_);
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 1, v___x_4419_);
v___x_4421_ = v___x_4417_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_pos_4414_);
lean_ctor_set(v_reuseFailAlloc_4422_, 1, v___x_4419_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
}
else
{
lean_object* v_pos_4424_; lean_object* v_err_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4432_; 
v_pos_4424_ = lean_ctor_get(v___x_4413_, 0);
v_err_4425_ = lean_ctor_get(v___x_4413_, 1);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4427_ = v___x_4413_;
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_err_4425_);
lean_inc(v_pos_4424_);
lean_dec(v___x_4413_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_pos_4424_);
lean_ctor_set(v_reuseFailAlloc_4431_, 1, v_err_4425_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
}
case 27:
{
lean_object* v_presentation_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; 
lean_dec_ref(v_config_3879_);
v_presentation_4433_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_presentation_4433_);
lean_dec_ref_known(v_x_3880_, 1);
v___x_4434_ = lean_unsigned_to_nat(0u);
v___x_4435_ = lean_unsigned_to_nat(999999999u);
v___x_4436_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4436_, 0, v_presentation_4433_);
v___x_4437_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4434_, v___x_4435_, v___x_4436_, v_a_3881_);
return v___x_4437_;
}
case 28:
{
lean_object* v_presentation_4438_; lean_object* v___x_4439_; 
lean_dec_ref(v_config_3879_);
v_presentation_4438_ = lean_ctor_get(v_x_3880_, 0);
lean_inc(v_presentation_4438_);
lean_dec_ref_known(v_x_3880_, 1);
v___x_4439_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_presentation_4438_, v_a_3881_);
lean_dec(v_presentation_4438_);
if (lean_obj_tag(v___x_4439_) == 0)
{
lean_object* v_pos_4440_; lean_object* v_res_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4449_; 
v_pos_4440_ = lean_ctor_get(v___x_4439_, 0);
v_res_4441_ = lean_ctor_get(v___x_4439_, 1);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_4439_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4443_ = v___x_4439_;
v_isShared_4444_ = v_isSharedCheck_4449_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_res_4441_);
lean_inc(v_pos_4440_);
lean_dec(v___x_4439_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4449_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4445_; lean_object* v___x_4447_; 
v___x_4445_ = lean_nat_to_int(v_res_4441_);
if (v_isShared_4444_ == 0)
{
lean_ctor_set(v___x_4443_, 1, v___x_4445_);
v___x_4447_ = v___x_4443_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_pos_4440_);
lean_ctor_set(v_reuseFailAlloc_4448_, 1, v___x_4445_);
v___x_4447_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
return v___x_4447_;
}
}
}
else
{
lean_object* v_pos_4450_; lean_object* v_err_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
v_pos_4450_ = lean_ctor_get(v___x_4439_, 0);
v_err_4451_ = lean_ctor_get(v___x_4439_, 1);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4439_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4439_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_err_4451_);
lean_inc(v_pos_4450_);
lean_dec(v___x_4439_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_pos_4450_);
lean_ctor_set(v_reuseFailAlloc_4457_, 1, v_err_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
case 29:
{
uint8_t v_presentation_4459_; 
lean_dec_ref(v_config_3879_);
v_presentation_4459_ = lean_ctor_get_uint8(v_x_3880_, 0);
lean_dec_ref_known(v_x_3880_, 0);
if (v_presentation_4459_ == 0)
{
lean_object* v___x_4460_; lean_object* v___x_4461_; 
v___x_4460_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
v___x_4461_ = l_Std_Internal_Parsec_String_pstring(v___x_4460_, v_a_3881_);
if (lean_obj_tag(v___x_4461_) == 0)
{
lean_object* v_pos_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4469_; 
v_pos_4462_ = lean_ctor_get(v___x_4461_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4461_);
if (v_isSharedCheck_4469_ == 0)
{
lean_object* v_unused_4470_; 
v_unused_4470_ = lean_ctor_get(v___x_4461_, 1);
lean_dec(v_unused_4470_);
v___x_4464_ = v___x_4461_;
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_pos_4462_);
lean_dec(v___x_4461_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v___x_4467_; 
if (v_isShared_4465_ == 0)
{
lean_ctor_set(v___x_4464_, 1, v___x_4460_);
v___x_4467_ = v___x_4464_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v_pos_4462_);
lean_ctor_set(v_reuseFailAlloc_4468_, 1, v___x_4460_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
return v___x_4467_;
}
}
}
else
{
return v___x_4461_;
}
}
else
{
lean_object* v___x_4471_; 
v___x_4471_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(v_a_3881_);
return v___x_4471_;
}
}
case 32:
{
uint8_t v_presentation_4472_; 
lean_dec_ref(v_config_3879_);
v_presentation_4472_ = lean_ctor_get_uint8(v_x_3880_, 0);
lean_dec_ref_known(v_x_3880_, 0);
if (v_presentation_4472_ == 0)
{
lean_object* v___x_4473_; lean_object* v___x_4474_; 
v___x_4473_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4474_ = l_Std_Internal_Parsec_String_pstring(v___x_4473_, v_a_3881_);
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_object* v_pos_4475_; uint8_t v___x_4476_; uint8_t v___x_4477_; uint8_t v___x_4478_; lean_object* v___x_4479_; 
v_pos_4475_ = lean_ctor_get(v___x_4474_, 0);
lean_inc(v_pos_4475_);
lean_dec_ref_known(v___x_4474_, 2);
v___x_4476_ = 2;
v___x_4477_ = 1;
v___x_4478_ = 1;
v___x_4479_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4476_, v___x_4477_, v___x_4478_, v_pos_4475_);
return v___x_4479_;
}
else
{
lean_object* v_pos_4480_; lean_object* v_err_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
v_pos_4480_ = lean_ctor_get(v___x_4474_, 0);
v_err_4481_ = lean_ctor_get(v___x_4474_, 1);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4474_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4483_ = v___x_4474_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_err_4481_);
lean_inc(v_pos_4480_);
lean_dec(v___x_4474_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
if (v_isShared_4484_ == 0)
{
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_pos_4480_);
lean_ctor_set(v_reuseFailAlloc_4487_, 1, v_err_4481_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
}
else
{
lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4489_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4490_ = l_Std_Internal_Parsec_String_pstring(v___x_4489_, v_a_3881_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_object* v_pos_4491_; uint8_t v___x_4492_; uint8_t v___x_4493_; uint8_t v___x_4494_; lean_object* v___x_4495_; 
v_pos_4491_ = lean_ctor_get(v___x_4490_, 0);
lean_inc(v_pos_4491_);
lean_dec_ref_known(v___x_4490_, 2);
v___x_4492_ = 0;
v___x_4493_ = 2;
v___x_4494_ = 1;
v___x_4495_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4492_, v___x_4493_, v___x_4494_, v_pos_4491_);
return v___x_4495_;
}
else
{
lean_object* v_pos_4496_; lean_object* v_err_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4504_; 
v_pos_4496_ = lean_ctor_get(v___x_4490_, 0);
v_err_4497_ = lean_ctor_get(v___x_4490_, 1);
v_isSharedCheck_4504_ = !lean_is_exclusive(v___x_4490_);
if (v_isSharedCheck_4504_ == 0)
{
v___x_4499_ = v___x_4490_;
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_err_4497_);
lean_inc(v_pos_4496_);
lean_dec(v___x_4490_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4502_; 
if (v_isShared_4500_ == 0)
{
v___x_4502_ = v___x_4499_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_pos_4496_);
lean_ctor_set(v_reuseFailAlloc_4503_, 1, v_err_4497_);
v___x_4502_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
return v___x_4502_;
}
}
}
}
}
case 33:
{
uint8_t v_presentation_4505_; 
lean_dec_ref(v_config_3879_);
v_presentation_4505_ = lean_ctor_get_uint8(v_x_3880_, 0);
lean_dec_ref_known(v_x_3880_, 0);
switch(v_presentation_4505_)
{
case 0:
{
uint8_t v___x_4506_; uint8_t v___x_4507_; uint8_t v___x_4508_; lean_object* v___x_4509_; 
v___x_4506_ = 2;
v___x_4507_ = 1;
v___x_4508_ = 0;
lean_inc_ref(v_a_3881_);
v___x_4509_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4506_, v___x_4507_, v___x_4508_, v_a_3881_);
v___y_3883_ = v___x_4509_;
goto v___jp_3882_;
}
case 1:
{
uint8_t v___x_4510_; uint8_t v___x_4511_; uint8_t v___x_4512_; lean_object* v___x_4513_; 
v___x_4510_ = 0;
v___x_4511_ = 1;
v___x_4512_ = 0;
lean_inc_ref(v_a_3881_);
v___x_4513_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4510_, v___x_4511_, v___x_4512_, v_a_3881_);
v___y_3883_ = v___x_4513_;
goto v___jp_3882_;
}
case 2:
{
uint8_t v___x_4514_; uint8_t v___x_4515_; uint8_t v___x_4516_; lean_object* v___x_4517_; 
v___x_4514_ = 0;
v___x_4515_ = 1;
v___x_4516_ = 1;
lean_inc_ref(v_a_3881_);
v___x_4517_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4514_, v___x_4515_, v___x_4516_, v_a_3881_);
v___y_3883_ = v___x_4517_;
goto v___jp_3882_;
}
case 3:
{
uint8_t v___x_4518_; uint8_t v___x_4519_; uint8_t v___x_4520_; lean_object* v___x_4521_; 
v___x_4518_ = 0;
v___x_4519_ = 2;
v___x_4520_ = 0;
lean_inc_ref(v_a_3881_);
v___x_4521_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4518_, v___x_4519_, v___x_4520_, v_a_3881_);
v___y_3883_ = v___x_4521_;
goto v___jp_3882_;
}
default: 
{
uint8_t v___x_4522_; uint8_t v___x_4523_; uint8_t v___x_4524_; lean_object* v___x_4525_; 
v___x_4522_ = 0;
v___x_4523_ = 2;
v___x_4524_ = 1;
lean_inc_ref(v_a_3881_);
v___x_4525_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4522_, v___x_4523_, v___x_4524_, v_a_3881_);
v___y_3883_ = v___x_4525_;
goto v___jp_3882_;
}
}
}
case 34:
{
uint8_t v_presentation_4526_; 
lean_dec_ref(v_config_3879_);
v_presentation_4526_ = lean_ctor_get_uint8(v_x_3880_, 0);
lean_dec_ref_known(v_x_3880_, 0);
switch(v_presentation_4526_)
{
case 0:
{
uint8_t v___x_4527_; uint8_t v___x_4528_; uint8_t v___x_4529_; lean_object* v___x_4530_; 
v___x_4527_ = 2;
v___x_4528_ = 1;
v___x_4529_ = 0;
v___x_4530_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4527_, v___x_4528_, v___x_4529_, v_a_3881_);
return v___x_4530_;
}
case 1:
{
uint8_t v___x_4531_; uint8_t v___x_4532_; uint8_t v___x_4533_; lean_object* v___x_4534_; 
v___x_4531_ = 0;
v___x_4532_ = 1;
v___x_4533_ = 0;
v___x_4534_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4531_, v___x_4532_, v___x_4533_, v_a_3881_);
return v___x_4534_;
}
case 2:
{
uint8_t v___x_4535_; uint8_t v___x_4536_; uint8_t v___x_4537_; lean_object* v___x_4538_; 
v___x_4535_ = 0;
v___x_4536_ = 2;
v___x_4537_ = 1;
v___x_4538_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4535_, v___x_4536_, v___x_4537_, v_a_3881_);
return v___x_4538_;
}
case 3:
{
uint8_t v___x_4539_; uint8_t v___x_4540_; uint8_t v___x_4541_; lean_object* v___x_4542_; 
v___x_4539_ = 0;
v___x_4540_ = 2;
v___x_4541_ = 0;
v___x_4542_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4539_, v___x_4540_, v___x_4541_, v_a_3881_);
return v___x_4542_;
}
default: 
{
uint8_t v___x_4543_; uint8_t v___x_4544_; lean_object* v___x_4545_; 
v___x_4543_ = 0;
v___x_4544_ = 1;
v___x_4545_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4543_, v___x_4543_, v___x_4544_, v_a_3881_);
return v___x_4545_;
}
}
}
case 35:
{
uint8_t v_presentation_4546_; 
lean_dec_ref(v_config_3879_);
v_presentation_4546_ = lean_ctor_get_uint8(v_x_3880_, 0);
lean_dec_ref_known(v_x_3880_, 0);
switch(v_presentation_4546_)
{
case 0:
{
uint8_t v___x_4547_; uint8_t v___x_4548_; uint8_t v___x_4549_; lean_object* v___x_4550_; 
v___x_4547_ = 0;
v___x_4548_ = 1;
v___x_4549_ = 0;
v___x_4550_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4547_, v___x_4548_, v___x_4549_, v_a_3881_);
return v___x_4550_;
}
case 1:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; 
v___x_4551_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4552_ = l_Std_Internal_Parsec_String_pstring(v___x_4551_, v_a_3881_);
if (lean_obj_tag(v___x_4552_) == 0)
{
lean_object* v_pos_4553_; uint8_t v___x_4554_; uint8_t v___x_4555_; uint8_t v___x_4556_; lean_object* v___x_4557_; 
v_pos_4553_ = lean_ctor_get(v___x_4552_, 0);
lean_inc_n(v_pos_4553_, 2);
lean_dec_ref_known(v___x_4552_, 2);
v___x_4554_ = 0;
v___x_4555_ = 1;
v___x_4556_ = 1;
v___x_4557_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4554_, v___x_4555_, v___x_4556_, v_pos_4553_);
if (lean_obj_tag(v___x_4557_) == 0)
{
lean_dec(v_pos_4553_);
return v___x_4557_;
}
else
{
lean_object* v_pos_4558_; lean_object* v_snd_4559_; lean_object* v_snd_4560_; uint8_t v_decide_4561_; 
v_pos_4558_ = lean_ctor_get(v___x_4557_, 0);
lean_inc(v_pos_4558_);
v_snd_4559_ = lean_ctor_get(v_pos_4553_, 1);
lean_inc(v_snd_4559_);
lean_dec(v_pos_4553_);
v_snd_4560_ = lean_ctor_get(v_pos_4558_, 1);
v_decide_4561_ = lean_nat_dec_eq(v_snd_4559_, v_snd_4560_);
lean_dec(v_snd_4559_);
if (v_decide_4561_ == 0)
{
lean_dec(v_pos_4558_);
return v___x_4557_;
}
else
{
lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4569_; 
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4557_);
if (v_isSharedCheck_4569_ == 0)
{
lean_object* v_unused_4570_; lean_object* v_unused_4571_; 
v_unused_4570_ = lean_ctor_get(v___x_4557_, 1);
lean_dec(v_unused_4570_);
v_unused_4571_ = lean_ctor_get(v___x_4557_, 0);
lean_dec(v_unused_4571_);
v___x_4563_ = v___x_4557_;
v_isShared_4564_ = v_isSharedCheck_4569_;
goto v_resetjp_4562_;
}
else
{
lean_dec(v___x_4557_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4569_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4565_; lean_object* v___x_4567_; 
v___x_4565_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_4564_ == 0)
{
lean_ctor_set_tag(v___x_4563_, 0);
lean_ctor_set(v___x_4563_, 1, v___x_4565_);
v___x_4567_ = v___x_4563_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_pos_4558_);
lean_ctor_set(v_reuseFailAlloc_4568_, 1, v___x_4565_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
}
}
}
else
{
lean_object* v_pos_4572_; lean_object* v_err_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4580_; 
v_pos_4572_ = lean_ctor_get(v___x_4552_, 0);
v_err_4573_ = lean_ctor_get(v___x_4552_, 1);
v_isSharedCheck_4580_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4580_ == 0)
{
v___x_4575_ = v___x_4552_;
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_err_4573_);
lean_inc(v_pos_4572_);
lean_dec(v___x_4552_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
lean_object* v___x_4578_; 
if (v_isShared_4576_ == 0)
{
v___x_4578_ = v___x_4575_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v_pos_4572_);
lean_ctor_set(v_reuseFailAlloc_4579_, 1, v_err_4573_);
v___x_4578_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
return v___x_4578_;
}
}
}
}
default: 
{
lean_object* v___x_4581_; lean_object* v___x_4582_; 
v___x_4581_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
lean_inc_ref(v_a_3881_);
v___x_4582_ = l_Std_Internal_Parsec_String_pstring(v___x_4581_, v_a_3881_);
if (lean_obj_tag(v___x_4582_) == 0)
{
lean_object* v_pos_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4591_; 
lean_dec_ref(v_a_3881_);
v_pos_4583_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4591_ == 0)
{
lean_object* v_unused_4592_; 
v_unused_4592_ = lean_ctor_get(v___x_4582_, 1);
lean_dec(v_unused_4592_);
v___x_4585_ = v___x_4582_;
v_isShared_4586_ = v_isSharedCheck_4591_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_pos_4583_);
lean_dec(v___x_4582_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4591_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4587_; lean_object* v___x_4589_; 
v___x_4587_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_4586_ == 0)
{
lean_ctor_set(v___x_4585_, 1, v___x_4587_);
v___x_4589_ = v___x_4585_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_pos_4583_);
lean_ctor_set(v_reuseFailAlloc_4590_, 1, v___x_4587_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
}
else
{
lean_object* v_pos_4593_; lean_object* v_err_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4607_; 
v_pos_4593_ = lean_ctor_get(v___x_4582_, 0);
v_err_4594_ = lean_ctor_get(v___x_4582_, 1);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4596_ = v___x_4582_;
v_isShared_4597_ = v_isSharedCheck_4607_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_err_4594_);
lean_inc(v_pos_4593_);
lean_dec(v___x_4582_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4607_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v_snd_4598_; lean_object* v_snd_4599_; uint8_t v_decide_4600_; 
v_snd_4598_ = lean_ctor_get(v_a_3881_, 1);
lean_inc(v_snd_4598_);
lean_dec_ref(v_a_3881_);
v_snd_4599_ = lean_ctor_get(v_pos_4593_, 1);
v_decide_4600_ = lean_nat_dec_eq(v_snd_4598_, v_snd_4599_);
lean_dec(v_snd_4598_);
if (v_decide_4600_ == 0)
{
lean_object* v___x_4602_; 
if (v_isShared_4597_ == 0)
{
v___x_4602_ = v___x_4596_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_pos_4593_);
lean_ctor_set(v_reuseFailAlloc_4603_, 1, v_err_4594_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
return v___x_4602_;
}
}
else
{
uint8_t v___x_4604_; uint8_t v___x_4605_; lean_object* v___x_4606_; 
lean_del_object(v___x_4596_);
lean_dec(v_err_4594_);
v___x_4604_ = 0;
v___x_4605_ = 2;
v___x_4606_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4604_, v___x_4605_, v_decide_4600_, v_pos_4593_);
return v___x_4606_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_4608_; 
lean_dec_ref(v_x_3880_);
lean_dec_ref(v_config_3879_);
v___x_4608_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(v_a_3881_);
return v___x_4608_;
}
}
v___jp_3882_:
{
if (lean_obj_tag(v___y_3883_) == 0)
{
lean_dec_ref(v_a_3881_);
return v___y_3883_;
}
else
{
lean_object* v_pos_3884_; lean_object* v_snd_3885_; lean_object* v_snd_3886_; uint8_t v_decide_3887_; 
v_pos_3884_ = lean_ctor_get(v___y_3883_, 0);
v_snd_3885_ = lean_ctor_get(v_a_3881_, 1);
lean_inc(v_snd_3885_);
lean_dec_ref(v_a_3881_);
v_snd_3886_ = lean_ctor_get(v_pos_3884_, 1);
v_decide_3887_ = lean_nat_dec_eq(v_snd_3885_, v_snd_3886_);
lean_dec(v_snd_3885_);
if (v_decide_3887_ == 0)
{
return v___y_3883_;
}
else
{
lean_object* v___x_3888_; lean_object* v___x_3889_; 
lean_inc(v_pos_3884_);
lean_dec_ref_known(v___y_3883_, 2);
v___x_3888_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
v___x_3889_ = l_Std_Internal_Parsec_String_pstring(v___x_3888_, v_pos_3884_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_pos_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3898_; 
v_pos_3890_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3898_ == 0)
{
lean_object* v_unused_3899_; 
v_unused_3899_ = lean_ctor_get(v___x_3889_, 1);
lean_dec(v_unused_3899_);
v___x_3892_ = v___x_3889_;
v_isShared_3893_ = v_isSharedCheck_3898_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_pos_3890_);
lean_dec(v___x_3889_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3898_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3894_; lean_object* v___x_3896_; 
v___x_3894_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 1, v___x_3894_);
v___x_3896_ = v___x_3892_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_pos_3890_);
lean_ctor_set(v_reuseFailAlloc_3897_, 1, v___x_3894_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
else
{
lean_object* v_pos_3900_; lean_object* v_err_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
v_pos_3900_ = lean_ctor_get(v___x_3889_, 0);
v_err_3901_ = lean_ctor_get(v___x_3889_, 1);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3889_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_err_3901_);
lean_inc(v_pos_3900_);
lean_dec(v___x_3889_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_pos_3900_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v_err_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(lean_object* v_dateformat_4609_, lean_object* v_date_4610_, lean_object* v_part_4611_){
_start:
{
if (lean_obj_tag(v_part_4611_) == 0)
{
lean_object* v_val_4612_; 
lean_dec_ref(v_date_4610_);
v_val_4612_ = lean_ctor_get(v_part_4611_, 0);
lean_inc_ref(v_val_4612_);
lean_dec_ref_known(v_part_4611_, 1);
return v_val_4612_;
}
else
{
lean_object* v_modifier_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
v_modifier_4613_ = lean_ctor_get(v_part_4611_, 0);
lean_inc_ref(v_modifier_4613_);
lean_dec_ref_known(v_part_4611_, 1);
v___x_4614_ = l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(v_modifier_4613_, v_dateformat_4609_, v_date_4610_);
v___x_4615_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_4609_, v_modifier_4613_, v___x_4614_);
return v___x_4615_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate___boxed(lean_object* v_dateformat_4616_, lean_object* v_date_4617_, lean_object* v_part_4618_){
_start:
{
lean_object* v_res_4619_; 
v_res_4619_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_4616_, v_date_4617_, v_part_4618_);
lean_dec_ref(v_dateformat_4616_);
return v_res_4619_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_FormatType_match__1_splitter___redArg(lean_object* v_x_4620_, lean_object* v_h__1_4621_, lean_object* v_h__2_4622_, lean_object* v_h__3_4623_){
_start:
{
if (lean_obj_tag(v_x_4620_) == 0)
{
lean_object* v___x_4624_; lean_object* v___x_4625_; 
lean_dec(v_h__2_4622_);
lean_dec(v_h__1_4621_);
v___x_4624_ = lean_box(0);
v___x_4625_ = lean_apply_1(v_h__3_4623_, v___x_4624_);
return v___x_4625_;
}
else
{
lean_object* v_head_4626_; 
lean_dec(v_h__3_4623_);
v_head_4626_ = lean_ctor_get(v_x_4620_, 0);
lean_inc(v_head_4626_);
if (lean_obj_tag(v_head_4626_) == 0)
{
lean_object* v_tail_4627_; lean_object* v_val_4628_; lean_object* v___x_4629_; 
lean_dec(v_h__1_4621_);
v_tail_4627_ = lean_ctor_get(v_x_4620_, 1);
lean_inc(v_tail_4627_);
lean_dec_ref_known(v_x_4620_, 2);
v_val_4628_ = lean_ctor_get(v_head_4626_, 0);
lean_inc_ref(v_val_4628_);
lean_dec_ref_known(v_head_4626_, 1);
v___x_4629_ = lean_apply_2(v_h__2_4622_, v_val_4628_, v_tail_4627_);
return v___x_4629_;
}
else
{
lean_object* v_tail_4630_; lean_object* v_modifier_4631_; lean_object* v___x_4632_; 
lean_dec(v_h__2_4622_);
v_tail_4630_ = lean_ctor_get(v_x_4620_, 1);
lean_inc(v_tail_4630_);
lean_dec_ref_known(v_x_4620_, 2);
v_modifier_4631_ = lean_ctor_get(v_head_4626_, 0);
lean_inc_ref(v_modifier_4631_);
lean_dec_ref_known(v_head_4626_, 1);
v___x_4632_ = lean_apply_2(v_h__1_4621_, v_modifier_4631_, v_tail_4630_);
return v___x_4632_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_FormatType_match__1_splitter(lean_object* v_motive_4633_, lean_object* v_x_4634_, lean_object* v_h__1_4635_, lean_object* v_h__2_4636_, lean_object* v_h__3_4637_){
_start:
{
if (lean_obj_tag(v_x_4634_) == 0)
{
lean_object* v___x_4638_; lean_object* v___x_4639_; 
lean_dec(v_h__2_4636_);
lean_dec(v_h__1_4635_);
v___x_4638_ = lean_box(0);
v___x_4639_ = lean_apply_1(v_h__3_4637_, v___x_4638_);
return v___x_4639_;
}
else
{
lean_object* v_head_4640_; 
lean_dec(v_h__3_4637_);
v_head_4640_ = lean_ctor_get(v_x_4634_, 0);
lean_inc(v_head_4640_);
if (lean_obj_tag(v_head_4640_) == 0)
{
lean_object* v_tail_4641_; lean_object* v_val_4642_; lean_object* v___x_4643_; 
lean_dec(v_h__1_4635_);
v_tail_4641_ = lean_ctor_get(v_x_4634_, 1);
lean_inc(v_tail_4641_);
lean_dec_ref_known(v_x_4634_, 2);
v_val_4642_ = lean_ctor_get(v_head_4640_, 0);
lean_inc_ref(v_val_4642_);
lean_dec_ref_known(v_head_4640_, 1);
v___x_4643_ = lean_apply_2(v_h__2_4636_, v_val_4642_, v_tail_4641_);
return v___x_4643_;
}
else
{
lean_object* v_tail_4644_; lean_object* v_modifier_4645_; lean_object* v___x_4646_; 
lean_dec(v_h__2_4636_);
v_tail_4644_ = lean_ctor_get(v_x_4634_, 1);
lean_inc(v_tail_4644_);
lean_dec_ref_known(v_x_4634_, 2);
v_modifier_4645_ = lean_ctor_get(v_head_4640_, 0);
lean_inc_ref(v_modifier_4645_);
lean_dec_ref_known(v_head_4640_, 1);
v___x_4646_ = lean_apply_2(v_h__1_4635_, v_modifier_4645_, v_tail_4644_);
return v___x_4646_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(lean_object* v_date_4647_, lean_object* v_modifier_4648_, lean_object* v_data_4649_){
_start:
{
switch(lean_obj_tag(v_modifier_4648_))
{
case 0:
{
lean_object* v_y_4650_; lean_object* v_u_4651_; lean_object* v_Y_4652_; lean_object* v_D_4653_; lean_object* v_M_4654_; lean_object* v_L_4655_; lean_object* v_d_4656_; lean_object* v_Q_4657_; lean_object* v_q_4658_; lean_object* v_w_4659_; lean_object* v_W_4660_; lean_object* v_E_4661_; lean_object* v_e_4662_; lean_object* v_c_4663_; lean_object* v_F_4664_; lean_object* v_a_4665_; lean_object* v_b_4666_; lean_object* v_B_4667_; lean_object* v_h_4668_; lean_object* v_K_4669_; lean_object* v_k_4670_; lean_object* v_H_4671_; lean_object* v_m_4672_; lean_object* v_s_4673_; lean_object* v_S_4674_; lean_object* v_A_4675_; lean_object* v_n_4676_; lean_object* v_N_4677_; lean_object* v_V_4678_; lean_object* v_z_4679_; lean_object* v_zabbrev_4680_; lean_object* v_v_4681_; lean_object* v_O_4682_; lean_object* v_X_4683_; lean_object* v_x_4684_; lean_object* v_Z_4685_; lean_object* v___x_4687_; uint8_t v_isShared_4688_; uint8_t v_isSharedCheck_4693_; 
lean_dec_ref_known(v_modifier_4648_, 0);
v_y_4650_ = lean_ctor_get(v_date_4647_, 1);
v_u_4651_ = lean_ctor_get(v_date_4647_, 2);
v_Y_4652_ = lean_ctor_get(v_date_4647_, 3);
v_D_4653_ = lean_ctor_get(v_date_4647_, 4);
v_M_4654_ = lean_ctor_get(v_date_4647_, 5);
v_L_4655_ = lean_ctor_get(v_date_4647_, 6);
v_d_4656_ = lean_ctor_get(v_date_4647_, 7);
v_Q_4657_ = lean_ctor_get(v_date_4647_, 8);
v_q_4658_ = lean_ctor_get(v_date_4647_, 9);
v_w_4659_ = lean_ctor_get(v_date_4647_, 10);
v_W_4660_ = lean_ctor_get(v_date_4647_, 11);
v_E_4661_ = lean_ctor_get(v_date_4647_, 12);
v_e_4662_ = lean_ctor_get(v_date_4647_, 13);
v_c_4663_ = lean_ctor_get(v_date_4647_, 14);
v_F_4664_ = lean_ctor_get(v_date_4647_, 15);
v_a_4665_ = lean_ctor_get(v_date_4647_, 16);
v_b_4666_ = lean_ctor_get(v_date_4647_, 17);
v_B_4667_ = lean_ctor_get(v_date_4647_, 18);
v_h_4668_ = lean_ctor_get(v_date_4647_, 19);
v_K_4669_ = lean_ctor_get(v_date_4647_, 20);
v_k_4670_ = lean_ctor_get(v_date_4647_, 21);
v_H_4671_ = lean_ctor_get(v_date_4647_, 22);
v_m_4672_ = lean_ctor_get(v_date_4647_, 23);
v_s_4673_ = lean_ctor_get(v_date_4647_, 24);
v_S_4674_ = lean_ctor_get(v_date_4647_, 25);
v_A_4675_ = lean_ctor_get(v_date_4647_, 26);
v_n_4676_ = lean_ctor_get(v_date_4647_, 27);
v_N_4677_ = lean_ctor_get(v_date_4647_, 28);
v_V_4678_ = lean_ctor_get(v_date_4647_, 29);
v_z_4679_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_4680_ = lean_ctor_get(v_date_4647_, 31);
v_v_4681_ = lean_ctor_get(v_date_4647_, 32);
v_O_4682_ = lean_ctor_get(v_date_4647_, 33);
v_X_4683_ = lean_ctor_get(v_date_4647_, 34);
v_x_4684_ = lean_ctor_get(v_date_4647_, 35);
v_Z_4685_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_4693_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_4693_ == 0)
{
lean_object* v_unused_4694_; 
v_unused_4694_ = lean_ctor_get(v_date_4647_, 0);
lean_dec(v_unused_4694_);
v___x_4687_ = v_date_4647_;
v_isShared_4688_ = v_isSharedCheck_4693_;
goto v_resetjp_4686_;
}
else
{
lean_inc(v_Z_4685_);
lean_inc(v_x_4684_);
lean_inc(v_X_4683_);
lean_inc(v_O_4682_);
lean_inc(v_v_4681_);
lean_inc(v_zabbrev_4680_);
lean_inc(v_z_4679_);
lean_inc(v_V_4678_);
lean_inc(v_N_4677_);
lean_inc(v_n_4676_);
lean_inc(v_A_4675_);
lean_inc(v_S_4674_);
lean_inc(v_s_4673_);
lean_inc(v_m_4672_);
lean_inc(v_H_4671_);
lean_inc(v_k_4670_);
lean_inc(v_K_4669_);
lean_inc(v_h_4668_);
lean_inc(v_B_4667_);
lean_inc(v_b_4666_);
lean_inc(v_a_4665_);
lean_inc(v_F_4664_);
lean_inc(v_c_4663_);
lean_inc(v_e_4662_);
lean_inc(v_E_4661_);
lean_inc(v_W_4660_);
lean_inc(v_w_4659_);
lean_inc(v_q_4658_);
lean_inc(v_Q_4657_);
lean_inc(v_d_4656_);
lean_inc(v_L_4655_);
lean_inc(v_M_4654_);
lean_inc(v_D_4653_);
lean_inc(v_Y_4652_);
lean_inc(v_u_4651_);
lean_inc(v_y_4650_);
lean_dec(v_date_4647_);
v___x_4687_ = lean_box(0);
v_isShared_4688_ = v_isSharedCheck_4693_;
goto v_resetjp_4686_;
}
v_resetjp_4686_:
{
lean_object* v___x_4689_; lean_object* v___x_4691_; 
v___x_4689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4689_, 0, v_data_4649_);
if (v_isShared_4688_ == 0)
{
lean_ctor_set(v___x_4687_, 0, v___x_4689_);
v___x_4691_ = v___x_4687_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v___x_4689_);
lean_ctor_set(v_reuseFailAlloc_4692_, 1, v_y_4650_);
lean_ctor_set(v_reuseFailAlloc_4692_, 2, v_u_4651_);
lean_ctor_set(v_reuseFailAlloc_4692_, 3, v_Y_4652_);
lean_ctor_set(v_reuseFailAlloc_4692_, 4, v_D_4653_);
lean_ctor_set(v_reuseFailAlloc_4692_, 5, v_M_4654_);
lean_ctor_set(v_reuseFailAlloc_4692_, 6, v_L_4655_);
lean_ctor_set(v_reuseFailAlloc_4692_, 7, v_d_4656_);
lean_ctor_set(v_reuseFailAlloc_4692_, 8, v_Q_4657_);
lean_ctor_set(v_reuseFailAlloc_4692_, 9, v_q_4658_);
lean_ctor_set(v_reuseFailAlloc_4692_, 10, v_w_4659_);
lean_ctor_set(v_reuseFailAlloc_4692_, 11, v_W_4660_);
lean_ctor_set(v_reuseFailAlloc_4692_, 12, v_E_4661_);
lean_ctor_set(v_reuseFailAlloc_4692_, 13, v_e_4662_);
lean_ctor_set(v_reuseFailAlloc_4692_, 14, v_c_4663_);
lean_ctor_set(v_reuseFailAlloc_4692_, 15, v_F_4664_);
lean_ctor_set(v_reuseFailAlloc_4692_, 16, v_a_4665_);
lean_ctor_set(v_reuseFailAlloc_4692_, 17, v_b_4666_);
lean_ctor_set(v_reuseFailAlloc_4692_, 18, v_B_4667_);
lean_ctor_set(v_reuseFailAlloc_4692_, 19, v_h_4668_);
lean_ctor_set(v_reuseFailAlloc_4692_, 20, v_K_4669_);
lean_ctor_set(v_reuseFailAlloc_4692_, 21, v_k_4670_);
lean_ctor_set(v_reuseFailAlloc_4692_, 22, v_H_4671_);
lean_ctor_set(v_reuseFailAlloc_4692_, 23, v_m_4672_);
lean_ctor_set(v_reuseFailAlloc_4692_, 24, v_s_4673_);
lean_ctor_set(v_reuseFailAlloc_4692_, 25, v_S_4674_);
lean_ctor_set(v_reuseFailAlloc_4692_, 26, v_A_4675_);
lean_ctor_set(v_reuseFailAlloc_4692_, 27, v_n_4676_);
lean_ctor_set(v_reuseFailAlloc_4692_, 28, v_N_4677_);
lean_ctor_set(v_reuseFailAlloc_4692_, 29, v_V_4678_);
lean_ctor_set(v_reuseFailAlloc_4692_, 30, v_z_4679_);
lean_ctor_set(v_reuseFailAlloc_4692_, 31, v_zabbrev_4680_);
lean_ctor_set(v_reuseFailAlloc_4692_, 32, v_v_4681_);
lean_ctor_set(v_reuseFailAlloc_4692_, 33, v_O_4682_);
lean_ctor_set(v_reuseFailAlloc_4692_, 34, v_X_4683_);
lean_ctor_set(v_reuseFailAlloc_4692_, 35, v_x_4684_);
lean_ctor_set(v_reuseFailAlloc_4692_, 36, v_Z_4685_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
return v___x_4691_;
}
}
}
case 1:
{
lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4745_; 
v_isSharedCheck_4745_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_4745_ == 0)
{
lean_object* v_unused_4746_; 
v_unused_4746_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_4746_);
v___x_4696_ = v_modifier_4648_;
v_isShared_4697_ = v_isSharedCheck_4745_;
goto v_resetjp_4695_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4745_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v_G_4698_; lean_object* v_y_4699_; lean_object* v_Y_4700_; lean_object* v_D_4701_; lean_object* v_M_4702_; lean_object* v_L_4703_; lean_object* v_d_4704_; lean_object* v_Q_4705_; lean_object* v_q_4706_; lean_object* v_w_4707_; lean_object* v_W_4708_; lean_object* v_E_4709_; lean_object* v_e_4710_; lean_object* v_c_4711_; lean_object* v_F_4712_; lean_object* v_a_4713_; lean_object* v_b_4714_; lean_object* v_B_4715_; lean_object* v_h_4716_; lean_object* v_K_4717_; lean_object* v_k_4718_; lean_object* v_H_4719_; lean_object* v_m_4720_; lean_object* v_s_4721_; lean_object* v_S_4722_; lean_object* v_A_4723_; lean_object* v_n_4724_; lean_object* v_N_4725_; lean_object* v_V_4726_; lean_object* v_z_4727_; lean_object* v_zabbrev_4728_; lean_object* v_v_4729_; lean_object* v_O_4730_; lean_object* v_X_4731_; lean_object* v_x_4732_; lean_object* v_Z_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4743_; 
v_G_4698_ = lean_ctor_get(v_date_4647_, 0);
v_y_4699_ = lean_ctor_get(v_date_4647_, 1);
v_Y_4700_ = lean_ctor_get(v_date_4647_, 3);
v_D_4701_ = lean_ctor_get(v_date_4647_, 4);
v_M_4702_ = lean_ctor_get(v_date_4647_, 5);
v_L_4703_ = lean_ctor_get(v_date_4647_, 6);
v_d_4704_ = lean_ctor_get(v_date_4647_, 7);
v_Q_4705_ = lean_ctor_get(v_date_4647_, 8);
v_q_4706_ = lean_ctor_get(v_date_4647_, 9);
v_w_4707_ = lean_ctor_get(v_date_4647_, 10);
v_W_4708_ = lean_ctor_get(v_date_4647_, 11);
v_E_4709_ = lean_ctor_get(v_date_4647_, 12);
v_e_4710_ = lean_ctor_get(v_date_4647_, 13);
v_c_4711_ = lean_ctor_get(v_date_4647_, 14);
v_F_4712_ = lean_ctor_get(v_date_4647_, 15);
v_a_4713_ = lean_ctor_get(v_date_4647_, 16);
v_b_4714_ = lean_ctor_get(v_date_4647_, 17);
v_B_4715_ = lean_ctor_get(v_date_4647_, 18);
v_h_4716_ = lean_ctor_get(v_date_4647_, 19);
v_K_4717_ = lean_ctor_get(v_date_4647_, 20);
v_k_4718_ = lean_ctor_get(v_date_4647_, 21);
v_H_4719_ = lean_ctor_get(v_date_4647_, 22);
v_m_4720_ = lean_ctor_get(v_date_4647_, 23);
v_s_4721_ = lean_ctor_get(v_date_4647_, 24);
v_S_4722_ = lean_ctor_get(v_date_4647_, 25);
v_A_4723_ = lean_ctor_get(v_date_4647_, 26);
v_n_4724_ = lean_ctor_get(v_date_4647_, 27);
v_N_4725_ = lean_ctor_get(v_date_4647_, 28);
v_V_4726_ = lean_ctor_get(v_date_4647_, 29);
v_z_4727_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_4728_ = lean_ctor_get(v_date_4647_, 31);
v_v_4729_ = lean_ctor_get(v_date_4647_, 32);
v_O_4730_ = lean_ctor_get(v_date_4647_, 33);
v_X_4731_ = lean_ctor_get(v_date_4647_, 34);
v_x_4732_ = lean_ctor_get(v_date_4647_, 35);
v_Z_4733_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_4743_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_4743_ == 0)
{
lean_object* v_unused_4744_; 
v_unused_4744_ = lean_ctor_get(v_date_4647_, 2);
lean_dec(v_unused_4744_);
v___x_4735_ = v_date_4647_;
v_isShared_4736_ = v_isSharedCheck_4743_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_Z_4733_);
lean_inc(v_x_4732_);
lean_inc(v_X_4731_);
lean_inc(v_O_4730_);
lean_inc(v_v_4729_);
lean_inc(v_zabbrev_4728_);
lean_inc(v_z_4727_);
lean_inc(v_V_4726_);
lean_inc(v_N_4725_);
lean_inc(v_n_4724_);
lean_inc(v_A_4723_);
lean_inc(v_S_4722_);
lean_inc(v_s_4721_);
lean_inc(v_m_4720_);
lean_inc(v_H_4719_);
lean_inc(v_k_4718_);
lean_inc(v_K_4717_);
lean_inc(v_h_4716_);
lean_inc(v_B_4715_);
lean_inc(v_b_4714_);
lean_inc(v_a_4713_);
lean_inc(v_F_4712_);
lean_inc(v_c_4711_);
lean_inc(v_e_4710_);
lean_inc(v_E_4709_);
lean_inc(v_W_4708_);
lean_inc(v_w_4707_);
lean_inc(v_q_4706_);
lean_inc(v_Q_4705_);
lean_inc(v_d_4704_);
lean_inc(v_L_4703_);
lean_inc(v_M_4702_);
lean_inc(v_D_4701_);
lean_inc(v_Y_4700_);
lean_inc(v_y_4699_);
lean_inc(v_G_4698_);
lean_dec(v_date_4647_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4743_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v___x_4738_; 
if (v_isShared_4697_ == 0)
{
lean_ctor_set(v___x_4696_, 0, v_data_4649_);
v___x_4738_ = v___x_4696_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v_data_4649_);
v___x_4738_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
lean_object* v___x_4740_; 
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 2, v___x_4738_);
v___x_4740_ = v___x_4735_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_G_4698_);
lean_ctor_set(v_reuseFailAlloc_4741_, 1, v_y_4699_);
lean_ctor_set(v_reuseFailAlloc_4741_, 2, v___x_4738_);
lean_ctor_set(v_reuseFailAlloc_4741_, 3, v_Y_4700_);
lean_ctor_set(v_reuseFailAlloc_4741_, 4, v_D_4701_);
lean_ctor_set(v_reuseFailAlloc_4741_, 5, v_M_4702_);
lean_ctor_set(v_reuseFailAlloc_4741_, 6, v_L_4703_);
lean_ctor_set(v_reuseFailAlloc_4741_, 7, v_d_4704_);
lean_ctor_set(v_reuseFailAlloc_4741_, 8, v_Q_4705_);
lean_ctor_set(v_reuseFailAlloc_4741_, 9, v_q_4706_);
lean_ctor_set(v_reuseFailAlloc_4741_, 10, v_w_4707_);
lean_ctor_set(v_reuseFailAlloc_4741_, 11, v_W_4708_);
lean_ctor_set(v_reuseFailAlloc_4741_, 12, v_E_4709_);
lean_ctor_set(v_reuseFailAlloc_4741_, 13, v_e_4710_);
lean_ctor_set(v_reuseFailAlloc_4741_, 14, v_c_4711_);
lean_ctor_set(v_reuseFailAlloc_4741_, 15, v_F_4712_);
lean_ctor_set(v_reuseFailAlloc_4741_, 16, v_a_4713_);
lean_ctor_set(v_reuseFailAlloc_4741_, 17, v_b_4714_);
lean_ctor_set(v_reuseFailAlloc_4741_, 18, v_B_4715_);
lean_ctor_set(v_reuseFailAlloc_4741_, 19, v_h_4716_);
lean_ctor_set(v_reuseFailAlloc_4741_, 20, v_K_4717_);
lean_ctor_set(v_reuseFailAlloc_4741_, 21, v_k_4718_);
lean_ctor_set(v_reuseFailAlloc_4741_, 22, v_H_4719_);
lean_ctor_set(v_reuseFailAlloc_4741_, 23, v_m_4720_);
lean_ctor_set(v_reuseFailAlloc_4741_, 24, v_s_4721_);
lean_ctor_set(v_reuseFailAlloc_4741_, 25, v_S_4722_);
lean_ctor_set(v_reuseFailAlloc_4741_, 26, v_A_4723_);
lean_ctor_set(v_reuseFailAlloc_4741_, 27, v_n_4724_);
lean_ctor_set(v_reuseFailAlloc_4741_, 28, v_N_4725_);
lean_ctor_set(v_reuseFailAlloc_4741_, 29, v_V_4726_);
lean_ctor_set(v_reuseFailAlloc_4741_, 30, v_z_4727_);
lean_ctor_set(v_reuseFailAlloc_4741_, 31, v_zabbrev_4728_);
lean_ctor_set(v_reuseFailAlloc_4741_, 32, v_v_4729_);
lean_ctor_set(v_reuseFailAlloc_4741_, 33, v_O_4730_);
lean_ctor_set(v_reuseFailAlloc_4741_, 34, v_X_4731_);
lean_ctor_set(v_reuseFailAlloc_4741_, 35, v_x_4732_);
lean_ctor_set(v_reuseFailAlloc_4741_, 36, v_Z_4733_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
}
}
}
case 2:
{
lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4797_; 
v_isSharedCheck_4797_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_4797_ == 0)
{
lean_object* v_unused_4798_; 
v_unused_4798_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_4798_);
v___x_4748_ = v_modifier_4648_;
v_isShared_4749_ = v_isSharedCheck_4797_;
goto v_resetjp_4747_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4797_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v_G_4750_; lean_object* v_u_4751_; lean_object* v_Y_4752_; lean_object* v_D_4753_; lean_object* v_M_4754_; lean_object* v_L_4755_; lean_object* v_d_4756_; lean_object* v_Q_4757_; lean_object* v_q_4758_; lean_object* v_w_4759_; lean_object* v_W_4760_; lean_object* v_E_4761_; lean_object* v_e_4762_; lean_object* v_c_4763_; lean_object* v_F_4764_; lean_object* v_a_4765_; lean_object* v_b_4766_; lean_object* v_B_4767_; lean_object* v_h_4768_; lean_object* v_K_4769_; lean_object* v_k_4770_; lean_object* v_H_4771_; lean_object* v_m_4772_; lean_object* v_s_4773_; lean_object* v_S_4774_; lean_object* v_A_4775_; lean_object* v_n_4776_; lean_object* v_N_4777_; lean_object* v_V_4778_; lean_object* v_z_4779_; lean_object* v_zabbrev_4780_; lean_object* v_v_4781_; lean_object* v_O_4782_; lean_object* v_X_4783_; lean_object* v_x_4784_; lean_object* v_Z_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4795_; 
v_G_4750_ = lean_ctor_get(v_date_4647_, 0);
v_u_4751_ = lean_ctor_get(v_date_4647_, 2);
v_Y_4752_ = lean_ctor_get(v_date_4647_, 3);
v_D_4753_ = lean_ctor_get(v_date_4647_, 4);
v_M_4754_ = lean_ctor_get(v_date_4647_, 5);
v_L_4755_ = lean_ctor_get(v_date_4647_, 6);
v_d_4756_ = lean_ctor_get(v_date_4647_, 7);
v_Q_4757_ = lean_ctor_get(v_date_4647_, 8);
v_q_4758_ = lean_ctor_get(v_date_4647_, 9);
v_w_4759_ = lean_ctor_get(v_date_4647_, 10);
v_W_4760_ = lean_ctor_get(v_date_4647_, 11);
v_E_4761_ = lean_ctor_get(v_date_4647_, 12);
v_e_4762_ = lean_ctor_get(v_date_4647_, 13);
v_c_4763_ = lean_ctor_get(v_date_4647_, 14);
v_F_4764_ = lean_ctor_get(v_date_4647_, 15);
v_a_4765_ = lean_ctor_get(v_date_4647_, 16);
v_b_4766_ = lean_ctor_get(v_date_4647_, 17);
v_B_4767_ = lean_ctor_get(v_date_4647_, 18);
v_h_4768_ = lean_ctor_get(v_date_4647_, 19);
v_K_4769_ = lean_ctor_get(v_date_4647_, 20);
v_k_4770_ = lean_ctor_get(v_date_4647_, 21);
v_H_4771_ = lean_ctor_get(v_date_4647_, 22);
v_m_4772_ = lean_ctor_get(v_date_4647_, 23);
v_s_4773_ = lean_ctor_get(v_date_4647_, 24);
v_S_4774_ = lean_ctor_get(v_date_4647_, 25);
v_A_4775_ = lean_ctor_get(v_date_4647_, 26);
v_n_4776_ = lean_ctor_get(v_date_4647_, 27);
v_N_4777_ = lean_ctor_get(v_date_4647_, 28);
v_V_4778_ = lean_ctor_get(v_date_4647_, 29);
v_z_4779_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_4780_ = lean_ctor_get(v_date_4647_, 31);
v_v_4781_ = lean_ctor_get(v_date_4647_, 32);
v_O_4782_ = lean_ctor_get(v_date_4647_, 33);
v_X_4783_ = lean_ctor_get(v_date_4647_, 34);
v_x_4784_ = lean_ctor_get(v_date_4647_, 35);
v_Z_4785_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_4795_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_4795_ == 0)
{
lean_object* v_unused_4796_; 
v_unused_4796_ = lean_ctor_get(v_date_4647_, 1);
lean_dec(v_unused_4796_);
v___x_4787_ = v_date_4647_;
v_isShared_4788_ = v_isSharedCheck_4795_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_Z_4785_);
lean_inc(v_x_4784_);
lean_inc(v_X_4783_);
lean_inc(v_O_4782_);
lean_inc(v_v_4781_);
lean_inc(v_zabbrev_4780_);
lean_inc(v_z_4779_);
lean_inc(v_V_4778_);
lean_inc(v_N_4777_);
lean_inc(v_n_4776_);
lean_inc(v_A_4775_);
lean_inc(v_S_4774_);
lean_inc(v_s_4773_);
lean_inc(v_m_4772_);
lean_inc(v_H_4771_);
lean_inc(v_k_4770_);
lean_inc(v_K_4769_);
lean_inc(v_h_4768_);
lean_inc(v_B_4767_);
lean_inc(v_b_4766_);
lean_inc(v_a_4765_);
lean_inc(v_F_4764_);
lean_inc(v_c_4763_);
lean_inc(v_e_4762_);
lean_inc(v_E_4761_);
lean_inc(v_W_4760_);
lean_inc(v_w_4759_);
lean_inc(v_q_4758_);
lean_inc(v_Q_4757_);
lean_inc(v_d_4756_);
lean_inc(v_L_4755_);
lean_inc(v_M_4754_);
lean_inc(v_D_4753_);
lean_inc(v_Y_4752_);
lean_inc(v_u_4751_);
lean_inc(v_G_4750_);
lean_dec(v_date_4647_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4795_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
lean_object* v___x_4790_; 
if (v_isShared_4749_ == 0)
{
lean_ctor_set_tag(v___x_4748_, 1);
lean_ctor_set(v___x_4748_, 0, v_data_4649_);
v___x_4790_ = v___x_4748_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v_data_4649_);
v___x_4790_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
lean_object* v___x_4792_; 
if (v_isShared_4788_ == 0)
{
lean_ctor_set(v___x_4787_, 1, v___x_4790_);
v___x_4792_ = v___x_4787_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_G_4750_);
lean_ctor_set(v_reuseFailAlloc_4793_, 1, v___x_4790_);
lean_ctor_set(v_reuseFailAlloc_4793_, 2, v_u_4751_);
lean_ctor_set(v_reuseFailAlloc_4793_, 3, v_Y_4752_);
lean_ctor_set(v_reuseFailAlloc_4793_, 4, v_D_4753_);
lean_ctor_set(v_reuseFailAlloc_4793_, 5, v_M_4754_);
lean_ctor_set(v_reuseFailAlloc_4793_, 6, v_L_4755_);
lean_ctor_set(v_reuseFailAlloc_4793_, 7, v_d_4756_);
lean_ctor_set(v_reuseFailAlloc_4793_, 8, v_Q_4757_);
lean_ctor_set(v_reuseFailAlloc_4793_, 9, v_q_4758_);
lean_ctor_set(v_reuseFailAlloc_4793_, 10, v_w_4759_);
lean_ctor_set(v_reuseFailAlloc_4793_, 11, v_W_4760_);
lean_ctor_set(v_reuseFailAlloc_4793_, 12, v_E_4761_);
lean_ctor_set(v_reuseFailAlloc_4793_, 13, v_e_4762_);
lean_ctor_set(v_reuseFailAlloc_4793_, 14, v_c_4763_);
lean_ctor_set(v_reuseFailAlloc_4793_, 15, v_F_4764_);
lean_ctor_set(v_reuseFailAlloc_4793_, 16, v_a_4765_);
lean_ctor_set(v_reuseFailAlloc_4793_, 17, v_b_4766_);
lean_ctor_set(v_reuseFailAlloc_4793_, 18, v_B_4767_);
lean_ctor_set(v_reuseFailAlloc_4793_, 19, v_h_4768_);
lean_ctor_set(v_reuseFailAlloc_4793_, 20, v_K_4769_);
lean_ctor_set(v_reuseFailAlloc_4793_, 21, v_k_4770_);
lean_ctor_set(v_reuseFailAlloc_4793_, 22, v_H_4771_);
lean_ctor_set(v_reuseFailAlloc_4793_, 23, v_m_4772_);
lean_ctor_set(v_reuseFailAlloc_4793_, 24, v_s_4773_);
lean_ctor_set(v_reuseFailAlloc_4793_, 25, v_S_4774_);
lean_ctor_set(v_reuseFailAlloc_4793_, 26, v_A_4775_);
lean_ctor_set(v_reuseFailAlloc_4793_, 27, v_n_4776_);
lean_ctor_set(v_reuseFailAlloc_4793_, 28, v_N_4777_);
lean_ctor_set(v_reuseFailAlloc_4793_, 29, v_V_4778_);
lean_ctor_set(v_reuseFailAlloc_4793_, 30, v_z_4779_);
lean_ctor_set(v_reuseFailAlloc_4793_, 31, v_zabbrev_4780_);
lean_ctor_set(v_reuseFailAlloc_4793_, 32, v_v_4781_);
lean_ctor_set(v_reuseFailAlloc_4793_, 33, v_O_4782_);
lean_ctor_set(v_reuseFailAlloc_4793_, 34, v_X_4783_);
lean_ctor_set(v_reuseFailAlloc_4793_, 35, v_x_4784_);
lean_ctor_set(v_reuseFailAlloc_4793_, 36, v_Z_4785_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
}
}
case 3:
{
lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4849_; 
v_isSharedCheck_4849_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_4849_ == 0)
{
lean_object* v_unused_4850_; 
v_unused_4850_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_4850_);
v___x_4800_ = v_modifier_4648_;
v_isShared_4801_ = v_isSharedCheck_4849_;
goto v_resetjp_4799_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4849_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v_G_4802_; lean_object* v_y_4803_; lean_object* v_u_4804_; lean_object* v_Y_4805_; lean_object* v_M_4806_; lean_object* v_L_4807_; lean_object* v_d_4808_; lean_object* v_Q_4809_; lean_object* v_q_4810_; lean_object* v_w_4811_; lean_object* v_W_4812_; lean_object* v_E_4813_; lean_object* v_e_4814_; lean_object* v_c_4815_; lean_object* v_F_4816_; lean_object* v_a_4817_; lean_object* v_b_4818_; lean_object* v_B_4819_; lean_object* v_h_4820_; lean_object* v_K_4821_; lean_object* v_k_4822_; lean_object* v_H_4823_; lean_object* v_m_4824_; lean_object* v_s_4825_; lean_object* v_S_4826_; lean_object* v_A_4827_; lean_object* v_n_4828_; lean_object* v_N_4829_; lean_object* v_V_4830_; lean_object* v_z_4831_; lean_object* v_zabbrev_4832_; lean_object* v_v_4833_; lean_object* v_O_4834_; lean_object* v_X_4835_; lean_object* v_x_4836_; lean_object* v_Z_4837_; lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4847_; 
v_G_4802_ = lean_ctor_get(v_date_4647_, 0);
v_y_4803_ = lean_ctor_get(v_date_4647_, 1);
v_u_4804_ = lean_ctor_get(v_date_4647_, 2);
v_Y_4805_ = lean_ctor_get(v_date_4647_, 3);
v_M_4806_ = lean_ctor_get(v_date_4647_, 5);
v_L_4807_ = lean_ctor_get(v_date_4647_, 6);
v_d_4808_ = lean_ctor_get(v_date_4647_, 7);
v_Q_4809_ = lean_ctor_get(v_date_4647_, 8);
v_q_4810_ = lean_ctor_get(v_date_4647_, 9);
v_w_4811_ = lean_ctor_get(v_date_4647_, 10);
v_W_4812_ = lean_ctor_get(v_date_4647_, 11);
v_E_4813_ = lean_ctor_get(v_date_4647_, 12);
v_e_4814_ = lean_ctor_get(v_date_4647_, 13);
v_c_4815_ = lean_ctor_get(v_date_4647_, 14);
v_F_4816_ = lean_ctor_get(v_date_4647_, 15);
v_a_4817_ = lean_ctor_get(v_date_4647_, 16);
v_b_4818_ = lean_ctor_get(v_date_4647_, 17);
v_B_4819_ = lean_ctor_get(v_date_4647_, 18);
v_h_4820_ = lean_ctor_get(v_date_4647_, 19);
v_K_4821_ = lean_ctor_get(v_date_4647_, 20);
v_k_4822_ = lean_ctor_get(v_date_4647_, 21);
v_H_4823_ = lean_ctor_get(v_date_4647_, 22);
v_m_4824_ = lean_ctor_get(v_date_4647_, 23);
v_s_4825_ = lean_ctor_get(v_date_4647_, 24);
v_S_4826_ = lean_ctor_get(v_date_4647_, 25);
v_A_4827_ = lean_ctor_get(v_date_4647_, 26);
v_n_4828_ = lean_ctor_get(v_date_4647_, 27);
v_N_4829_ = lean_ctor_get(v_date_4647_, 28);
v_V_4830_ = lean_ctor_get(v_date_4647_, 29);
v_z_4831_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_4832_ = lean_ctor_get(v_date_4647_, 31);
v_v_4833_ = lean_ctor_get(v_date_4647_, 32);
v_O_4834_ = lean_ctor_get(v_date_4647_, 33);
v_X_4835_ = lean_ctor_get(v_date_4647_, 34);
v_x_4836_ = lean_ctor_get(v_date_4647_, 35);
v_Z_4837_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_4847_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_4847_ == 0)
{
lean_object* v_unused_4848_; 
v_unused_4848_ = lean_ctor_get(v_date_4647_, 4);
lean_dec(v_unused_4848_);
v___x_4839_ = v_date_4647_;
v_isShared_4840_ = v_isSharedCheck_4847_;
goto v_resetjp_4838_;
}
else
{
lean_inc(v_Z_4837_);
lean_inc(v_x_4836_);
lean_inc(v_X_4835_);
lean_inc(v_O_4834_);
lean_inc(v_v_4833_);
lean_inc(v_zabbrev_4832_);
lean_inc(v_z_4831_);
lean_inc(v_V_4830_);
lean_inc(v_N_4829_);
lean_inc(v_n_4828_);
lean_inc(v_A_4827_);
lean_inc(v_S_4826_);
lean_inc(v_s_4825_);
lean_inc(v_m_4824_);
lean_inc(v_H_4823_);
lean_inc(v_k_4822_);
lean_inc(v_K_4821_);
lean_inc(v_h_4820_);
lean_inc(v_B_4819_);
lean_inc(v_b_4818_);
lean_inc(v_a_4817_);
lean_inc(v_F_4816_);
lean_inc(v_c_4815_);
lean_inc(v_e_4814_);
lean_inc(v_E_4813_);
lean_inc(v_W_4812_);
lean_inc(v_w_4811_);
lean_inc(v_q_4810_);
lean_inc(v_Q_4809_);
lean_inc(v_d_4808_);
lean_inc(v_L_4807_);
lean_inc(v_M_4806_);
lean_inc(v_Y_4805_);
lean_inc(v_u_4804_);
lean_inc(v_y_4803_);
lean_inc(v_G_4802_);
lean_dec(v_date_4647_);
v___x_4839_ = lean_box(0);
v_isShared_4840_ = v_isSharedCheck_4847_;
goto v_resetjp_4838_;
}
v_resetjp_4838_:
{
lean_object* v___x_4842_; 
if (v_isShared_4801_ == 0)
{
lean_ctor_set_tag(v___x_4800_, 1);
lean_ctor_set(v___x_4800_, 0, v_data_4649_);
v___x_4842_ = v___x_4800_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v_data_4649_);
v___x_4842_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
lean_object* v___x_4844_; 
if (v_isShared_4840_ == 0)
{
lean_ctor_set(v___x_4839_, 4, v___x_4842_);
v___x_4844_ = v___x_4839_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_G_4802_);
lean_ctor_set(v_reuseFailAlloc_4845_, 1, v_y_4803_);
lean_ctor_set(v_reuseFailAlloc_4845_, 2, v_u_4804_);
lean_ctor_set(v_reuseFailAlloc_4845_, 3, v_Y_4805_);
lean_ctor_set(v_reuseFailAlloc_4845_, 4, v___x_4842_);
lean_ctor_set(v_reuseFailAlloc_4845_, 5, v_M_4806_);
lean_ctor_set(v_reuseFailAlloc_4845_, 6, v_L_4807_);
lean_ctor_set(v_reuseFailAlloc_4845_, 7, v_d_4808_);
lean_ctor_set(v_reuseFailAlloc_4845_, 8, v_Q_4809_);
lean_ctor_set(v_reuseFailAlloc_4845_, 9, v_q_4810_);
lean_ctor_set(v_reuseFailAlloc_4845_, 10, v_w_4811_);
lean_ctor_set(v_reuseFailAlloc_4845_, 11, v_W_4812_);
lean_ctor_set(v_reuseFailAlloc_4845_, 12, v_E_4813_);
lean_ctor_set(v_reuseFailAlloc_4845_, 13, v_e_4814_);
lean_ctor_set(v_reuseFailAlloc_4845_, 14, v_c_4815_);
lean_ctor_set(v_reuseFailAlloc_4845_, 15, v_F_4816_);
lean_ctor_set(v_reuseFailAlloc_4845_, 16, v_a_4817_);
lean_ctor_set(v_reuseFailAlloc_4845_, 17, v_b_4818_);
lean_ctor_set(v_reuseFailAlloc_4845_, 18, v_B_4819_);
lean_ctor_set(v_reuseFailAlloc_4845_, 19, v_h_4820_);
lean_ctor_set(v_reuseFailAlloc_4845_, 20, v_K_4821_);
lean_ctor_set(v_reuseFailAlloc_4845_, 21, v_k_4822_);
lean_ctor_set(v_reuseFailAlloc_4845_, 22, v_H_4823_);
lean_ctor_set(v_reuseFailAlloc_4845_, 23, v_m_4824_);
lean_ctor_set(v_reuseFailAlloc_4845_, 24, v_s_4825_);
lean_ctor_set(v_reuseFailAlloc_4845_, 25, v_S_4826_);
lean_ctor_set(v_reuseFailAlloc_4845_, 26, v_A_4827_);
lean_ctor_set(v_reuseFailAlloc_4845_, 27, v_n_4828_);
lean_ctor_set(v_reuseFailAlloc_4845_, 28, v_N_4829_);
lean_ctor_set(v_reuseFailAlloc_4845_, 29, v_V_4830_);
lean_ctor_set(v_reuseFailAlloc_4845_, 30, v_z_4831_);
lean_ctor_set(v_reuseFailAlloc_4845_, 31, v_zabbrev_4832_);
lean_ctor_set(v_reuseFailAlloc_4845_, 32, v_v_4833_);
lean_ctor_set(v_reuseFailAlloc_4845_, 33, v_O_4834_);
lean_ctor_set(v_reuseFailAlloc_4845_, 34, v_X_4835_);
lean_ctor_set(v_reuseFailAlloc_4845_, 35, v_x_4836_);
lean_ctor_set(v_reuseFailAlloc_4845_, 36, v_Z_4837_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
return v___x_4844_;
}
}
}
}
}
case 4:
{
lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4901_; 
v_isSharedCheck_4901_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_4901_ == 0)
{
lean_object* v_unused_4902_; 
v_unused_4902_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_4902_);
v___x_4852_ = v_modifier_4648_;
v_isShared_4853_ = v_isSharedCheck_4901_;
goto v_resetjp_4851_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4901_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v_G_4854_; lean_object* v_y_4855_; lean_object* v_u_4856_; lean_object* v_Y_4857_; lean_object* v_D_4858_; lean_object* v_L_4859_; lean_object* v_d_4860_; lean_object* v_Q_4861_; lean_object* v_q_4862_; lean_object* v_w_4863_; lean_object* v_W_4864_; lean_object* v_E_4865_; lean_object* v_e_4866_; lean_object* v_c_4867_; lean_object* v_F_4868_; lean_object* v_a_4869_; lean_object* v_b_4870_; lean_object* v_B_4871_; lean_object* v_h_4872_; lean_object* v_K_4873_; lean_object* v_k_4874_; lean_object* v_H_4875_; lean_object* v_m_4876_; lean_object* v_s_4877_; lean_object* v_S_4878_; lean_object* v_A_4879_; lean_object* v_n_4880_; lean_object* v_N_4881_; lean_object* v_V_4882_; lean_object* v_z_4883_; lean_object* v_zabbrev_4884_; lean_object* v_v_4885_; lean_object* v_O_4886_; lean_object* v_X_4887_; lean_object* v_x_4888_; lean_object* v_Z_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4899_; 
v_G_4854_ = lean_ctor_get(v_date_4647_, 0);
v_y_4855_ = lean_ctor_get(v_date_4647_, 1);
v_u_4856_ = lean_ctor_get(v_date_4647_, 2);
v_Y_4857_ = lean_ctor_get(v_date_4647_, 3);
v_D_4858_ = lean_ctor_get(v_date_4647_, 4);
v_L_4859_ = lean_ctor_get(v_date_4647_, 6);
v_d_4860_ = lean_ctor_get(v_date_4647_, 7);
v_Q_4861_ = lean_ctor_get(v_date_4647_, 8);
v_q_4862_ = lean_ctor_get(v_date_4647_, 9);
v_w_4863_ = lean_ctor_get(v_date_4647_, 10);
v_W_4864_ = lean_ctor_get(v_date_4647_, 11);
v_E_4865_ = lean_ctor_get(v_date_4647_, 12);
v_e_4866_ = lean_ctor_get(v_date_4647_, 13);
v_c_4867_ = lean_ctor_get(v_date_4647_, 14);
v_F_4868_ = lean_ctor_get(v_date_4647_, 15);
v_a_4869_ = lean_ctor_get(v_date_4647_, 16);
v_b_4870_ = lean_ctor_get(v_date_4647_, 17);
v_B_4871_ = lean_ctor_get(v_date_4647_, 18);
v_h_4872_ = lean_ctor_get(v_date_4647_, 19);
v_K_4873_ = lean_ctor_get(v_date_4647_, 20);
v_k_4874_ = lean_ctor_get(v_date_4647_, 21);
v_H_4875_ = lean_ctor_get(v_date_4647_, 22);
v_m_4876_ = lean_ctor_get(v_date_4647_, 23);
v_s_4877_ = lean_ctor_get(v_date_4647_, 24);
v_S_4878_ = lean_ctor_get(v_date_4647_, 25);
v_A_4879_ = lean_ctor_get(v_date_4647_, 26);
v_n_4880_ = lean_ctor_get(v_date_4647_, 27);
v_N_4881_ = lean_ctor_get(v_date_4647_, 28);
v_V_4882_ = lean_ctor_get(v_date_4647_, 29);
v_z_4883_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_4884_ = lean_ctor_get(v_date_4647_, 31);
v_v_4885_ = lean_ctor_get(v_date_4647_, 32);
v_O_4886_ = lean_ctor_get(v_date_4647_, 33);
v_X_4887_ = lean_ctor_get(v_date_4647_, 34);
v_x_4888_ = lean_ctor_get(v_date_4647_, 35);
v_Z_4889_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_4899_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_4899_ == 0)
{
lean_object* v_unused_4900_; 
v_unused_4900_ = lean_ctor_get(v_date_4647_, 5);
lean_dec(v_unused_4900_);
v___x_4891_ = v_date_4647_;
v_isShared_4892_ = v_isSharedCheck_4899_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_Z_4889_);
lean_inc(v_x_4888_);
lean_inc(v_X_4887_);
lean_inc(v_O_4886_);
lean_inc(v_v_4885_);
lean_inc(v_zabbrev_4884_);
lean_inc(v_z_4883_);
lean_inc(v_V_4882_);
lean_inc(v_N_4881_);
lean_inc(v_n_4880_);
lean_inc(v_A_4879_);
lean_inc(v_S_4878_);
lean_inc(v_s_4877_);
lean_inc(v_m_4876_);
lean_inc(v_H_4875_);
lean_inc(v_k_4874_);
lean_inc(v_K_4873_);
lean_inc(v_h_4872_);
lean_inc(v_B_4871_);
lean_inc(v_b_4870_);
lean_inc(v_a_4869_);
lean_inc(v_F_4868_);
lean_inc(v_c_4867_);
lean_inc(v_e_4866_);
lean_inc(v_E_4865_);
lean_inc(v_W_4864_);
lean_inc(v_w_4863_);
lean_inc(v_q_4862_);
lean_inc(v_Q_4861_);
lean_inc(v_d_4860_);
lean_inc(v_L_4859_);
lean_inc(v_D_4858_);
lean_inc(v_Y_4857_);
lean_inc(v_u_4856_);
lean_inc(v_y_4855_);
lean_inc(v_G_4854_);
lean_dec(v_date_4647_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4899_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v___x_4894_; 
if (v_isShared_4853_ == 0)
{
lean_ctor_set_tag(v___x_4852_, 1);
lean_ctor_set(v___x_4852_, 0, v_data_4649_);
v___x_4894_ = v___x_4852_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_data_4649_);
v___x_4894_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
lean_object* v___x_4896_; 
if (v_isShared_4892_ == 0)
{
lean_ctor_set(v___x_4891_, 5, v___x_4894_);
v___x_4896_ = v___x_4891_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_G_4854_);
lean_ctor_set(v_reuseFailAlloc_4897_, 1, v_y_4855_);
lean_ctor_set(v_reuseFailAlloc_4897_, 2, v_u_4856_);
lean_ctor_set(v_reuseFailAlloc_4897_, 3, v_Y_4857_);
lean_ctor_set(v_reuseFailAlloc_4897_, 4, v_D_4858_);
lean_ctor_set(v_reuseFailAlloc_4897_, 5, v___x_4894_);
lean_ctor_set(v_reuseFailAlloc_4897_, 6, v_L_4859_);
lean_ctor_set(v_reuseFailAlloc_4897_, 7, v_d_4860_);
lean_ctor_set(v_reuseFailAlloc_4897_, 8, v_Q_4861_);
lean_ctor_set(v_reuseFailAlloc_4897_, 9, v_q_4862_);
lean_ctor_set(v_reuseFailAlloc_4897_, 10, v_w_4863_);
lean_ctor_set(v_reuseFailAlloc_4897_, 11, v_W_4864_);
lean_ctor_set(v_reuseFailAlloc_4897_, 12, v_E_4865_);
lean_ctor_set(v_reuseFailAlloc_4897_, 13, v_e_4866_);
lean_ctor_set(v_reuseFailAlloc_4897_, 14, v_c_4867_);
lean_ctor_set(v_reuseFailAlloc_4897_, 15, v_F_4868_);
lean_ctor_set(v_reuseFailAlloc_4897_, 16, v_a_4869_);
lean_ctor_set(v_reuseFailAlloc_4897_, 17, v_b_4870_);
lean_ctor_set(v_reuseFailAlloc_4897_, 18, v_B_4871_);
lean_ctor_set(v_reuseFailAlloc_4897_, 19, v_h_4872_);
lean_ctor_set(v_reuseFailAlloc_4897_, 20, v_K_4873_);
lean_ctor_set(v_reuseFailAlloc_4897_, 21, v_k_4874_);
lean_ctor_set(v_reuseFailAlloc_4897_, 22, v_H_4875_);
lean_ctor_set(v_reuseFailAlloc_4897_, 23, v_m_4876_);
lean_ctor_set(v_reuseFailAlloc_4897_, 24, v_s_4877_);
lean_ctor_set(v_reuseFailAlloc_4897_, 25, v_S_4878_);
lean_ctor_set(v_reuseFailAlloc_4897_, 26, v_A_4879_);
lean_ctor_set(v_reuseFailAlloc_4897_, 27, v_n_4880_);
lean_ctor_set(v_reuseFailAlloc_4897_, 28, v_N_4881_);
lean_ctor_set(v_reuseFailAlloc_4897_, 29, v_V_4882_);
lean_ctor_set(v_reuseFailAlloc_4897_, 30, v_z_4883_);
lean_ctor_set(v_reuseFailAlloc_4897_, 31, v_zabbrev_4884_);
lean_ctor_set(v_reuseFailAlloc_4897_, 32, v_v_4885_);
lean_ctor_set(v_reuseFailAlloc_4897_, 33, v_O_4886_);
lean_ctor_set(v_reuseFailAlloc_4897_, 34, v_X_4887_);
lean_ctor_set(v_reuseFailAlloc_4897_, 35, v_x_4888_);
lean_ctor_set(v_reuseFailAlloc_4897_, 36, v_Z_4889_);
v___x_4896_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
return v___x_4896_;
}
}
}
}
}
case 5:
{
lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4953_; 
v_isSharedCheck_4953_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_4953_ == 0)
{
lean_object* v_unused_4954_; 
v_unused_4954_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_4954_);
v___x_4904_ = v_modifier_4648_;
v_isShared_4905_ = v_isSharedCheck_4953_;
goto v_resetjp_4903_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4953_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v_G_4906_; lean_object* v_y_4907_; lean_object* v_u_4908_; lean_object* v_Y_4909_; lean_object* v_D_4910_; lean_object* v_M_4911_; lean_object* v_d_4912_; lean_object* v_Q_4913_; lean_object* v_q_4914_; lean_object* v_w_4915_; lean_object* v_W_4916_; lean_object* v_E_4917_; lean_object* v_e_4918_; lean_object* v_c_4919_; lean_object* v_F_4920_; lean_object* v_a_4921_; lean_object* v_b_4922_; lean_object* v_B_4923_; lean_object* v_h_4924_; lean_object* v_K_4925_; lean_object* v_k_4926_; lean_object* v_H_4927_; lean_object* v_m_4928_; lean_object* v_s_4929_; lean_object* v_S_4930_; lean_object* v_A_4931_; lean_object* v_n_4932_; lean_object* v_N_4933_; lean_object* v_V_4934_; lean_object* v_z_4935_; lean_object* v_zabbrev_4936_; lean_object* v_v_4937_; lean_object* v_O_4938_; lean_object* v_X_4939_; lean_object* v_x_4940_; lean_object* v_Z_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4951_; 
v_G_4906_ = lean_ctor_get(v_date_4647_, 0);
v_y_4907_ = lean_ctor_get(v_date_4647_, 1);
v_u_4908_ = lean_ctor_get(v_date_4647_, 2);
v_Y_4909_ = lean_ctor_get(v_date_4647_, 3);
v_D_4910_ = lean_ctor_get(v_date_4647_, 4);
v_M_4911_ = lean_ctor_get(v_date_4647_, 5);
v_d_4912_ = lean_ctor_get(v_date_4647_, 7);
v_Q_4913_ = lean_ctor_get(v_date_4647_, 8);
v_q_4914_ = lean_ctor_get(v_date_4647_, 9);
v_w_4915_ = lean_ctor_get(v_date_4647_, 10);
v_W_4916_ = lean_ctor_get(v_date_4647_, 11);
v_E_4917_ = lean_ctor_get(v_date_4647_, 12);
v_e_4918_ = lean_ctor_get(v_date_4647_, 13);
v_c_4919_ = lean_ctor_get(v_date_4647_, 14);
v_F_4920_ = lean_ctor_get(v_date_4647_, 15);
v_a_4921_ = lean_ctor_get(v_date_4647_, 16);
v_b_4922_ = lean_ctor_get(v_date_4647_, 17);
v_B_4923_ = lean_ctor_get(v_date_4647_, 18);
v_h_4924_ = lean_ctor_get(v_date_4647_, 19);
v_K_4925_ = lean_ctor_get(v_date_4647_, 20);
v_k_4926_ = lean_ctor_get(v_date_4647_, 21);
v_H_4927_ = lean_ctor_get(v_date_4647_, 22);
v_m_4928_ = lean_ctor_get(v_date_4647_, 23);
v_s_4929_ = lean_ctor_get(v_date_4647_, 24);
v_S_4930_ = lean_ctor_get(v_date_4647_, 25);
v_A_4931_ = lean_ctor_get(v_date_4647_, 26);
v_n_4932_ = lean_ctor_get(v_date_4647_, 27);
v_N_4933_ = lean_ctor_get(v_date_4647_, 28);
v_V_4934_ = lean_ctor_get(v_date_4647_, 29);
v_z_4935_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_4936_ = lean_ctor_get(v_date_4647_, 31);
v_v_4937_ = lean_ctor_get(v_date_4647_, 32);
v_O_4938_ = lean_ctor_get(v_date_4647_, 33);
v_X_4939_ = lean_ctor_get(v_date_4647_, 34);
v_x_4940_ = lean_ctor_get(v_date_4647_, 35);
v_Z_4941_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_4951_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_4951_ == 0)
{
lean_object* v_unused_4952_; 
v_unused_4952_ = lean_ctor_get(v_date_4647_, 6);
lean_dec(v_unused_4952_);
v___x_4943_ = v_date_4647_;
v_isShared_4944_ = v_isSharedCheck_4951_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_Z_4941_);
lean_inc(v_x_4940_);
lean_inc(v_X_4939_);
lean_inc(v_O_4938_);
lean_inc(v_v_4937_);
lean_inc(v_zabbrev_4936_);
lean_inc(v_z_4935_);
lean_inc(v_V_4934_);
lean_inc(v_N_4933_);
lean_inc(v_n_4932_);
lean_inc(v_A_4931_);
lean_inc(v_S_4930_);
lean_inc(v_s_4929_);
lean_inc(v_m_4928_);
lean_inc(v_H_4927_);
lean_inc(v_k_4926_);
lean_inc(v_K_4925_);
lean_inc(v_h_4924_);
lean_inc(v_B_4923_);
lean_inc(v_b_4922_);
lean_inc(v_a_4921_);
lean_inc(v_F_4920_);
lean_inc(v_c_4919_);
lean_inc(v_e_4918_);
lean_inc(v_E_4917_);
lean_inc(v_W_4916_);
lean_inc(v_w_4915_);
lean_inc(v_q_4914_);
lean_inc(v_Q_4913_);
lean_inc(v_d_4912_);
lean_inc(v_M_4911_);
lean_inc(v_D_4910_);
lean_inc(v_Y_4909_);
lean_inc(v_u_4908_);
lean_inc(v_y_4907_);
lean_inc(v_G_4906_);
lean_dec(v_date_4647_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4951_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4946_; 
if (v_isShared_4905_ == 0)
{
lean_ctor_set_tag(v___x_4904_, 1);
lean_ctor_set(v___x_4904_, 0, v_data_4649_);
v___x_4946_ = v___x_4904_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v_data_4649_);
v___x_4946_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
lean_object* v___x_4948_; 
if (v_isShared_4944_ == 0)
{
lean_ctor_set(v___x_4943_, 6, v___x_4946_);
v___x_4948_ = v___x_4943_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v_G_4906_);
lean_ctor_set(v_reuseFailAlloc_4949_, 1, v_y_4907_);
lean_ctor_set(v_reuseFailAlloc_4949_, 2, v_u_4908_);
lean_ctor_set(v_reuseFailAlloc_4949_, 3, v_Y_4909_);
lean_ctor_set(v_reuseFailAlloc_4949_, 4, v_D_4910_);
lean_ctor_set(v_reuseFailAlloc_4949_, 5, v_M_4911_);
lean_ctor_set(v_reuseFailAlloc_4949_, 6, v___x_4946_);
lean_ctor_set(v_reuseFailAlloc_4949_, 7, v_d_4912_);
lean_ctor_set(v_reuseFailAlloc_4949_, 8, v_Q_4913_);
lean_ctor_set(v_reuseFailAlloc_4949_, 9, v_q_4914_);
lean_ctor_set(v_reuseFailAlloc_4949_, 10, v_w_4915_);
lean_ctor_set(v_reuseFailAlloc_4949_, 11, v_W_4916_);
lean_ctor_set(v_reuseFailAlloc_4949_, 12, v_E_4917_);
lean_ctor_set(v_reuseFailAlloc_4949_, 13, v_e_4918_);
lean_ctor_set(v_reuseFailAlloc_4949_, 14, v_c_4919_);
lean_ctor_set(v_reuseFailAlloc_4949_, 15, v_F_4920_);
lean_ctor_set(v_reuseFailAlloc_4949_, 16, v_a_4921_);
lean_ctor_set(v_reuseFailAlloc_4949_, 17, v_b_4922_);
lean_ctor_set(v_reuseFailAlloc_4949_, 18, v_B_4923_);
lean_ctor_set(v_reuseFailAlloc_4949_, 19, v_h_4924_);
lean_ctor_set(v_reuseFailAlloc_4949_, 20, v_K_4925_);
lean_ctor_set(v_reuseFailAlloc_4949_, 21, v_k_4926_);
lean_ctor_set(v_reuseFailAlloc_4949_, 22, v_H_4927_);
lean_ctor_set(v_reuseFailAlloc_4949_, 23, v_m_4928_);
lean_ctor_set(v_reuseFailAlloc_4949_, 24, v_s_4929_);
lean_ctor_set(v_reuseFailAlloc_4949_, 25, v_S_4930_);
lean_ctor_set(v_reuseFailAlloc_4949_, 26, v_A_4931_);
lean_ctor_set(v_reuseFailAlloc_4949_, 27, v_n_4932_);
lean_ctor_set(v_reuseFailAlloc_4949_, 28, v_N_4933_);
lean_ctor_set(v_reuseFailAlloc_4949_, 29, v_V_4934_);
lean_ctor_set(v_reuseFailAlloc_4949_, 30, v_z_4935_);
lean_ctor_set(v_reuseFailAlloc_4949_, 31, v_zabbrev_4936_);
lean_ctor_set(v_reuseFailAlloc_4949_, 32, v_v_4937_);
lean_ctor_set(v_reuseFailAlloc_4949_, 33, v_O_4938_);
lean_ctor_set(v_reuseFailAlloc_4949_, 34, v_X_4939_);
lean_ctor_set(v_reuseFailAlloc_4949_, 35, v_x_4940_);
lean_ctor_set(v_reuseFailAlloc_4949_, 36, v_Z_4941_);
v___x_4948_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
return v___x_4948_;
}
}
}
}
}
case 6:
{
lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_5005_; 
v_isSharedCheck_5005_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_5005_ == 0)
{
lean_object* v_unused_5006_; 
v_unused_5006_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_5006_);
v___x_4956_ = v_modifier_4648_;
v_isShared_4957_ = v_isSharedCheck_5005_;
goto v_resetjp_4955_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_5005_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v_G_4958_; lean_object* v_y_4959_; lean_object* v_u_4960_; lean_object* v_Y_4961_; lean_object* v_D_4962_; lean_object* v_M_4963_; lean_object* v_L_4964_; lean_object* v_Q_4965_; lean_object* v_q_4966_; lean_object* v_w_4967_; lean_object* v_W_4968_; lean_object* v_E_4969_; lean_object* v_e_4970_; lean_object* v_c_4971_; lean_object* v_F_4972_; lean_object* v_a_4973_; lean_object* v_b_4974_; lean_object* v_B_4975_; lean_object* v_h_4976_; lean_object* v_K_4977_; lean_object* v_k_4978_; lean_object* v_H_4979_; lean_object* v_m_4980_; lean_object* v_s_4981_; lean_object* v_S_4982_; lean_object* v_A_4983_; lean_object* v_n_4984_; lean_object* v_N_4985_; lean_object* v_V_4986_; lean_object* v_z_4987_; lean_object* v_zabbrev_4988_; lean_object* v_v_4989_; lean_object* v_O_4990_; lean_object* v_X_4991_; lean_object* v_x_4992_; lean_object* v_Z_4993_; lean_object* v___x_4995_; uint8_t v_isShared_4996_; uint8_t v_isSharedCheck_5003_; 
v_G_4958_ = lean_ctor_get(v_date_4647_, 0);
v_y_4959_ = lean_ctor_get(v_date_4647_, 1);
v_u_4960_ = lean_ctor_get(v_date_4647_, 2);
v_Y_4961_ = lean_ctor_get(v_date_4647_, 3);
v_D_4962_ = lean_ctor_get(v_date_4647_, 4);
v_M_4963_ = lean_ctor_get(v_date_4647_, 5);
v_L_4964_ = lean_ctor_get(v_date_4647_, 6);
v_Q_4965_ = lean_ctor_get(v_date_4647_, 8);
v_q_4966_ = lean_ctor_get(v_date_4647_, 9);
v_w_4967_ = lean_ctor_get(v_date_4647_, 10);
v_W_4968_ = lean_ctor_get(v_date_4647_, 11);
v_E_4969_ = lean_ctor_get(v_date_4647_, 12);
v_e_4970_ = lean_ctor_get(v_date_4647_, 13);
v_c_4971_ = lean_ctor_get(v_date_4647_, 14);
v_F_4972_ = lean_ctor_get(v_date_4647_, 15);
v_a_4973_ = lean_ctor_get(v_date_4647_, 16);
v_b_4974_ = lean_ctor_get(v_date_4647_, 17);
v_B_4975_ = lean_ctor_get(v_date_4647_, 18);
v_h_4976_ = lean_ctor_get(v_date_4647_, 19);
v_K_4977_ = lean_ctor_get(v_date_4647_, 20);
v_k_4978_ = lean_ctor_get(v_date_4647_, 21);
v_H_4979_ = lean_ctor_get(v_date_4647_, 22);
v_m_4980_ = lean_ctor_get(v_date_4647_, 23);
v_s_4981_ = lean_ctor_get(v_date_4647_, 24);
v_S_4982_ = lean_ctor_get(v_date_4647_, 25);
v_A_4983_ = lean_ctor_get(v_date_4647_, 26);
v_n_4984_ = lean_ctor_get(v_date_4647_, 27);
v_N_4985_ = lean_ctor_get(v_date_4647_, 28);
v_V_4986_ = lean_ctor_get(v_date_4647_, 29);
v_z_4987_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_4988_ = lean_ctor_get(v_date_4647_, 31);
v_v_4989_ = lean_ctor_get(v_date_4647_, 32);
v_O_4990_ = lean_ctor_get(v_date_4647_, 33);
v_X_4991_ = lean_ctor_get(v_date_4647_, 34);
v_x_4992_ = lean_ctor_get(v_date_4647_, 35);
v_Z_4993_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5003_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5003_ == 0)
{
lean_object* v_unused_5004_; 
v_unused_5004_ = lean_ctor_get(v_date_4647_, 7);
lean_dec(v_unused_5004_);
v___x_4995_ = v_date_4647_;
v_isShared_4996_ = v_isSharedCheck_5003_;
goto v_resetjp_4994_;
}
else
{
lean_inc(v_Z_4993_);
lean_inc(v_x_4992_);
lean_inc(v_X_4991_);
lean_inc(v_O_4990_);
lean_inc(v_v_4989_);
lean_inc(v_zabbrev_4988_);
lean_inc(v_z_4987_);
lean_inc(v_V_4986_);
lean_inc(v_N_4985_);
lean_inc(v_n_4984_);
lean_inc(v_A_4983_);
lean_inc(v_S_4982_);
lean_inc(v_s_4981_);
lean_inc(v_m_4980_);
lean_inc(v_H_4979_);
lean_inc(v_k_4978_);
lean_inc(v_K_4977_);
lean_inc(v_h_4976_);
lean_inc(v_B_4975_);
lean_inc(v_b_4974_);
lean_inc(v_a_4973_);
lean_inc(v_F_4972_);
lean_inc(v_c_4971_);
lean_inc(v_e_4970_);
lean_inc(v_E_4969_);
lean_inc(v_W_4968_);
lean_inc(v_w_4967_);
lean_inc(v_q_4966_);
lean_inc(v_Q_4965_);
lean_inc(v_L_4964_);
lean_inc(v_M_4963_);
lean_inc(v_D_4962_);
lean_inc(v_Y_4961_);
lean_inc(v_u_4960_);
lean_inc(v_y_4959_);
lean_inc(v_G_4958_);
lean_dec(v_date_4647_);
v___x_4995_ = lean_box(0);
v_isShared_4996_ = v_isSharedCheck_5003_;
goto v_resetjp_4994_;
}
v_resetjp_4994_:
{
lean_object* v___x_4998_; 
if (v_isShared_4957_ == 0)
{
lean_ctor_set_tag(v___x_4956_, 1);
lean_ctor_set(v___x_4956_, 0, v_data_4649_);
v___x_4998_ = v___x_4956_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_5002_; 
v_reuseFailAlloc_5002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5002_, 0, v_data_4649_);
v___x_4998_ = v_reuseFailAlloc_5002_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
lean_object* v___x_5000_; 
if (v_isShared_4996_ == 0)
{
lean_ctor_set(v___x_4995_, 7, v___x_4998_);
v___x_5000_ = v___x_4995_;
goto v_reusejp_4999_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_G_4958_);
lean_ctor_set(v_reuseFailAlloc_5001_, 1, v_y_4959_);
lean_ctor_set(v_reuseFailAlloc_5001_, 2, v_u_4960_);
lean_ctor_set(v_reuseFailAlloc_5001_, 3, v_Y_4961_);
lean_ctor_set(v_reuseFailAlloc_5001_, 4, v_D_4962_);
lean_ctor_set(v_reuseFailAlloc_5001_, 5, v_M_4963_);
lean_ctor_set(v_reuseFailAlloc_5001_, 6, v_L_4964_);
lean_ctor_set(v_reuseFailAlloc_5001_, 7, v___x_4998_);
lean_ctor_set(v_reuseFailAlloc_5001_, 8, v_Q_4965_);
lean_ctor_set(v_reuseFailAlloc_5001_, 9, v_q_4966_);
lean_ctor_set(v_reuseFailAlloc_5001_, 10, v_w_4967_);
lean_ctor_set(v_reuseFailAlloc_5001_, 11, v_W_4968_);
lean_ctor_set(v_reuseFailAlloc_5001_, 12, v_E_4969_);
lean_ctor_set(v_reuseFailAlloc_5001_, 13, v_e_4970_);
lean_ctor_set(v_reuseFailAlloc_5001_, 14, v_c_4971_);
lean_ctor_set(v_reuseFailAlloc_5001_, 15, v_F_4972_);
lean_ctor_set(v_reuseFailAlloc_5001_, 16, v_a_4973_);
lean_ctor_set(v_reuseFailAlloc_5001_, 17, v_b_4974_);
lean_ctor_set(v_reuseFailAlloc_5001_, 18, v_B_4975_);
lean_ctor_set(v_reuseFailAlloc_5001_, 19, v_h_4976_);
lean_ctor_set(v_reuseFailAlloc_5001_, 20, v_K_4977_);
lean_ctor_set(v_reuseFailAlloc_5001_, 21, v_k_4978_);
lean_ctor_set(v_reuseFailAlloc_5001_, 22, v_H_4979_);
lean_ctor_set(v_reuseFailAlloc_5001_, 23, v_m_4980_);
lean_ctor_set(v_reuseFailAlloc_5001_, 24, v_s_4981_);
lean_ctor_set(v_reuseFailAlloc_5001_, 25, v_S_4982_);
lean_ctor_set(v_reuseFailAlloc_5001_, 26, v_A_4983_);
lean_ctor_set(v_reuseFailAlloc_5001_, 27, v_n_4984_);
lean_ctor_set(v_reuseFailAlloc_5001_, 28, v_N_4985_);
lean_ctor_set(v_reuseFailAlloc_5001_, 29, v_V_4986_);
lean_ctor_set(v_reuseFailAlloc_5001_, 30, v_z_4987_);
lean_ctor_set(v_reuseFailAlloc_5001_, 31, v_zabbrev_4988_);
lean_ctor_set(v_reuseFailAlloc_5001_, 32, v_v_4989_);
lean_ctor_set(v_reuseFailAlloc_5001_, 33, v_O_4990_);
lean_ctor_set(v_reuseFailAlloc_5001_, 34, v_X_4991_);
lean_ctor_set(v_reuseFailAlloc_5001_, 35, v_x_4992_);
lean_ctor_set(v_reuseFailAlloc_5001_, 36, v_Z_4993_);
v___x_5000_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4999_;
}
v_reusejp_4999_:
{
return v___x_5000_;
}
}
}
}
}
case 7:
{
lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5057_; 
v_isSharedCheck_5057_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_5057_ == 0)
{
lean_object* v_unused_5058_; 
v_unused_5058_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_5058_);
v___x_5008_ = v_modifier_4648_;
v_isShared_5009_ = v_isSharedCheck_5057_;
goto v_resetjp_5007_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5057_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v_G_5010_; lean_object* v_y_5011_; lean_object* v_u_5012_; lean_object* v_Y_5013_; lean_object* v_D_5014_; lean_object* v_M_5015_; lean_object* v_L_5016_; lean_object* v_d_5017_; lean_object* v_q_5018_; lean_object* v_w_5019_; lean_object* v_W_5020_; lean_object* v_E_5021_; lean_object* v_e_5022_; lean_object* v_c_5023_; lean_object* v_F_5024_; lean_object* v_a_5025_; lean_object* v_b_5026_; lean_object* v_B_5027_; lean_object* v_h_5028_; lean_object* v_K_5029_; lean_object* v_k_5030_; lean_object* v_H_5031_; lean_object* v_m_5032_; lean_object* v_s_5033_; lean_object* v_S_5034_; lean_object* v_A_5035_; lean_object* v_n_5036_; lean_object* v_N_5037_; lean_object* v_V_5038_; lean_object* v_z_5039_; lean_object* v_zabbrev_5040_; lean_object* v_v_5041_; lean_object* v_O_5042_; lean_object* v_X_5043_; lean_object* v_x_5044_; lean_object* v_Z_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5055_; 
v_G_5010_ = lean_ctor_get(v_date_4647_, 0);
v_y_5011_ = lean_ctor_get(v_date_4647_, 1);
v_u_5012_ = lean_ctor_get(v_date_4647_, 2);
v_Y_5013_ = lean_ctor_get(v_date_4647_, 3);
v_D_5014_ = lean_ctor_get(v_date_4647_, 4);
v_M_5015_ = lean_ctor_get(v_date_4647_, 5);
v_L_5016_ = lean_ctor_get(v_date_4647_, 6);
v_d_5017_ = lean_ctor_get(v_date_4647_, 7);
v_q_5018_ = lean_ctor_get(v_date_4647_, 9);
v_w_5019_ = lean_ctor_get(v_date_4647_, 10);
v_W_5020_ = lean_ctor_get(v_date_4647_, 11);
v_E_5021_ = lean_ctor_get(v_date_4647_, 12);
v_e_5022_ = lean_ctor_get(v_date_4647_, 13);
v_c_5023_ = lean_ctor_get(v_date_4647_, 14);
v_F_5024_ = lean_ctor_get(v_date_4647_, 15);
v_a_5025_ = lean_ctor_get(v_date_4647_, 16);
v_b_5026_ = lean_ctor_get(v_date_4647_, 17);
v_B_5027_ = lean_ctor_get(v_date_4647_, 18);
v_h_5028_ = lean_ctor_get(v_date_4647_, 19);
v_K_5029_ = lean_ctor_get(v_date_4647_, 20);
v_k_5030_ = lean_ctor_get(v_date_4647_, 21);
v_H_5031_ = lean_ctor_get(v_date_4647_, 22);
v_m_5032_ = lean_ctor_get(v_date_4647_, 23);
v_s_5033_ = lean_ctor_get(v_date_4647_, 24);
v_S_5034_ = lean_ctor_get(v_date_4647_, 25);
v_A_5035_ = lean_ctor_get(v_date_4647_, 26);
v_n_5036_ = lean_ctor_get(v_date_4647_, 27);
v_N_5037_ = lean_ctor_get(v_date_4647_, 28);
v_V_5038_ = lean_ctor_get(v_date_4647_, 29);
v_z_5039_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_5040_ = lean_ctor_get(v_date_4647_, 31);
v_v_5041_ = lean_ctor_get(v_date_4647_, 32);
v_O_5042_ = lean_ctor_get(v_date_4647_, 33);
v_X_5043_ = lean_ctor_get(v_date_4647_, 34);
v_x_5044_ = lean_ctor_get(v_date_4647_, 35);
v_Z_5045_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5055_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5055_ == 0)
{
lean_object* v_unused_5056_; 
v_unused_5056_ = lean_ctor_get(v_date_4647_, 8);
lean_dec(v_unused_5056_);
v___x_5047_ = v_date_4647_;
v_isShared_5048_ = v_isSharedCheck_5055_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_Z_5045_);
lean_inc(v_x_5044_);
lean_inc(v_X_5043_);
lean_inc(v_O_5042_);
lean_inc(v_v_5041_);
lean_inc(v_zabbrev_5040_);
lean_inc(v_z_5039_);
lean_inc(v_V_5038_);
lean_inc(v_N_5037_);
lean_inc(v_n_5036_);
lean_inc(v_A_5035_);
lean_inc(v_S_5034_);
lean_inc(v_s_5033_);
lean_inc(v_m_5032_);
lean_inc(v_H_5031_);
lean_inc(v_k_5030_);
lean_inc(v_K_5029_);
lean_inc(v_h_5028_);
lean_inc(v_B_5027_);
lean_inc(v_b_5026_);
lean_inc(v_a_5025_);
lean_inc(v_F_5024_);
lean_inc(v_c_5023_);
lean_inc(v_e_5022_);
lean_inc(v_E_5021_);
lean_inc(v_W_5020_);
lean_inc(v_w_5019_);
lean_inc(v_q_5018_);
lean_inc(v_d_5017_);
lean_inc(v_L_5016_);
lean_inc(v_M_5015_);
lean_inc(v_D_5014_);
lean_inc(v_Y_5013_);
lean_inc(v_u_5012_);
lean_inc(v_y_5011_);
lean_inc(v_G_5010_);
lean_dec(v_date_4647_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5055_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5050_; 
if (v_isShared_5009_ == 0)
{
lean_ctor_set_tag(v___x_5008_, 1);
lean_ctor_set(v___x_5008_, 0, v_data_4649_);
v___x_5050_ = v___x_5008_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_data_4649_);
v___x_5050_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
lean_object* v___x_5052_; 
if (v_isShared_5048_ == 0)
{
lean_ctor_set(v___x_5047_, 8, v___x_5050_);
v___x_5052_ = v___x_5047_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_G_5010_);
lean_ctor_set(v_reuseFailAlloc_5053_, 1, v_y_5011_);
lean_ctor_set(v_reuseFailAlloc_5053_, 2, v_u_5012_);
lean_ctor_set(v_reuseFailAlloc_5053_, 3, v_Y_5013_);
lean_ctor_set(v_reuseFailAlloc_5053_, 4, v_D_5014_);
lean_ctor_set(v_reuseFailAlloc_5053_, 5, v_M_5015_);
lean_ctor_set(v_reuseFailAlloc_5053_, 6, v_L_5016_);
lean_ctor_set(v_reuseFailAlloc_5053_, 7, v_d_5017_);
lean_ctor_set(v_reuseFailAlloc_5053_, 8, v___x_5050_);
lean_ctor_set(v_reuseFailAlloc_5053_, 9, v_q_5018_);
lean_ctor_set(v_reuseFailAlloc_5053_, 10, v_w_5019_);
lean_ctor_set(v_reuseFailAlloc_5053_, 11, v_W_5020_);
lean_ctor_set(v_reuseFailAlloc_5053_, 12, v_E_5021_);
lean_ctor_set(v_reuseFailAlloc_5053_, 13, v_e_5022_);
lean_ctor_set(v_reuseFailAlloc_5053_, 14, v_c_5023_);
lean_ctor_set(v_reuseFailAlloc_5053_, 15, v_F_5024_);
lean_ctor_set(v_reuseFailAlloc_5053_, 16, v_a_5025_);
lean_ctor_set(v_reuseFailAlloc_5053_, 17, v_b_5026_);
lean_ctor_set(v_reuseFailAlloc_5053_, 18, v_B_5027_);
lean_ctor_set(v_reuseFailAlloc_5053_, 19, v_h_5028_);
lean_ctor_set(v_reuseFailAlloc_5053_, 20, v_K_5029_);
lean_ctor_set(v_reuseFailAlloc_5053_, 21, v_k_5030_);
lean_ctor_set(v_reuseFailAlloc_5053_, 22, v_H_5031_);
lean_ctor_set(v_reuseFailAlloc_5053_, 23, v_m_5032_);
lean_ctor_set(v_reuseFailAlloc_5053_, 24, v_s_5033_);
lean_ctor_set(v_reuseFailAlloc_5053_, 25, v_S_5034_);
lean_ctor_set(v_reuseFailAlloc_5053_, 26, v_A_5035_);
lean_ctor_set(v_reuseFailAlloc_5053_, 27, v_n_5036_);
lean_ctor_set(v_reuseFailAlloc_5053_, 28, v_N_5037_);
lean_ctor_set(v_reuseFailAlloc_5053_, 29, v_V_5038_);
lean_ctor_set(v_reuseFailAlloc_5053_, 30, v_z_5039_);
lean_ctor_set(v_reuseFailAlloc_5053_, 31, v_zabbrev_5040_);
lean_ctor_set(v_reuseFailAlloc_5053_, 32, v_v_5041_);
lean_ctor_set(v_reuseFailAlloc_5053_, 33, v_O_5042_);
lean_ctor_set(v_reuseFailAlloc_5053_, 34, v_X_5043_);
lean_ctor_set(v_reuseFailAlloc_5053_, 35, v_x_5044_);
lean_ctor_set(v_reuseFailAlloc_5053_, 36, v_Z_5045_);
v___x_5052_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
return v___x_5052_;
}
}
}
}
}
case 8:
{
lean_object* v___x_5060_; uint8_t v_isShared_5061_; uint8_t v_isSharedCheck_5109_; 
v_isSharedCheck_5109_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_5109_ == 0)
{
lean_object* v_unused_5110_; 
v_unused_5110_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_5110_);
v___x_5060_ = v_modifier_4648_;
v_isShared_5061_ = v_isSharedCheck_5109_;
goto v_resetjp_5059_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_5060_ = lean_box(0);
v_isShared_5061_ = v_isSharedCheck_5109_;
goto v_resetjp_5059_;
}
v_resetjp_5059_:
{
lean_object* v_G_5062_; lean_object* v_y_5063_; lean_object* v_u_5064_; lean_object* v_Y_5065_; lean_object* v_D_5066_; lean_object* v_M_5067_; lean_object* v_L_5068_; lean_object* v_d_5069_; lean_object* v_Q_5070_; lean_object* v_w_5071_; lean_object* v_W_5072_; lean_object* v_E_5073_; lean_object* v_e_5074_; lean_object* v_c_5075_; lean_object* v_F_5076_; lean_object* v_a_5077_; lean_object* v_b_5078_; lean_object* v_B_5079_; lean_object* v_h_5080_; lean_object* v_K_5081_; lean_object* v_k_5082_; lean_object* v_H_5083_; lean_object* v_m_5084_; lean_object* v_s_5085_; lean_object* v_S_5086_; lean_object* v_A_5087_; lean_object* v_n_5088_; lean_object* v_N_5089_; lean_object* v_V_5090_; lean_object* v_z_5091_; lean_object* v_zabbrev_5092_; lean_object* v_v_5093_; lean_object* v_O_5094_; lean_object* v_X_5095_; lean_object* v_x_5096_; lean_object* v_Z_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5107_; 
v_G_5062_ = lean_ctor_get(v_date_4647_, 0);
v_y_5063_ = lean_ctor_get(v_date_4647_, 1);
v_u_5064_ = lean_ctor_get(v_date_4647_, 2);
v_Y_5065_ = lean_ctor_get(v_date_4647_, 3);
v_D_5066_ = lean_ctor_get(v_date_4647_, 4);
v_M_5067_ = lean_ctor_get(v_date_4647_, 5);
v_L_5068_ = lean_ctor_get(v_date_4647_, 6);
v_d_5069_ = lean_ctor_get(v_date_4647_, 7);
v_Q_5070_ = lean_ctor_get(v_date_4647_, 8);
v_w_5071_ = lean_ctor_get(v_date_4647_, 10);
v_W_5072_ = lean_ctor_get(v_date_4647_, 11);
v_E_5073_ = lean_ctor_get(v_date_4647_, 12);
v_e_5074_ = lean_ctor_get(v_date_4647_, 13);
v_c_5075_ = lean_ctor_get(v_date_4647_, 14);
v_F_5076_ = lean_ctor_get(v_date_4647_, 15);
v_a_5077_ = lean_ctor_get(v_date_4647_, 16);
v_b_5078_ = lean_ctor_get(v_date_4647_, 17);
v_B_5079_ = lean_ctor_get(v_date_4647_, 18);
v_h_5080_ = lean_ctor_get(v_date_4647_, 19);
v_K_5081_ = lean_ctor_get(v_date_4647_, 20);
v_k_5082_ = lean_ctor_get(v_date_4647_, 21);
v_H_5083_ = lean_ctor_get(v_date_4647_, 22);
v_m_5084_ = lean_ctor_get(v_date_4647_, 23);
v_s_5085_ = lean_ctor_get(v_date_4647_, 24);
v_S_5086_ = lean_ctor_get(v_date_4647_, 25);
v_A_5087_ = lean_ctor_get(v_date_4647_, 26);
v_n_5088_ = lean_ctor_get(v_date_4647_, 27);
v_N_5089_ = lean_ctor_get(v_date_4647_, 28);
v_V_5090_ = lean_ctor_get(v_date_4647_, 29);
v_z_5091_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_5092_ = lean_ctor_get(v_date_4647_, 31);
v_v_5093_ = lean_ctor_get(v_date_4647_, 32);
v_O_5094_ = lean_ctor_get(v_date_4647_, 33);
v_X_5095_ = lean_ctor_get(v_date_4647_, 34);
v_x_5096_ = lean_ctor_get(v_date_4647_, 35);
v_Z_5097_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5107_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5107_ == 0)
{
lean_object* v_unused_5108_; 
v_unused_5108_ = lean_ctor_get(v_date_4647_, 9);
lean_dec(v_unused_5108_);
v___x_5099_ = v_date_4647_;
v_isShared_5100_ = v_isSharedCheck_5107_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_Z_5097_);
lean_inc(v_x_5096_);
lean_inc(v_X_5095_);
lean_inc(v_O_5094_);
lean_inc(v_v_5093_);
lean_inc(v_zabbrev_5092_);
lean_inc(v_z_5091_);
lean_inc(v_V_5090_);
lean_inc(v_N_5089_);
lean_inc(v_n_5088_);
lean_inc(v_A_5087_);
lean_inc(v_S_5086_);
lean_inc(v_s_5085_);
lean_inc(v_m_5084_);
lean_inc(v_H_5083_);
lean_inc(v_k_5082_);
lean_inc(v_K_5081_);
lean_inc(v_h_5080_);
lean_inc(v_B_5079_);
lean_inc(v_b_5078_);
lean_inc(v_a_5077_);
lean_inc(v_F_5076_);
lean_inc(v_c_5075_);
lean_inc(v_e_5074_);
lean_inc(v_E_5073_);
lean_inc(v_W_5072_);
lean_inc(v_w_5071_);
lean_inc(v_Q_5070_);
lean_inc(v_d_5069_);
lean_inc(v_L_5068_);
lean_inc(v_M_5067_);
lean_inc(v_D_5066_);
lean_inc(v_Y_5065_);
lean_inc(v_u_5064_);
lean_inc(v_y_5063_);
lean_inc(v_G_5062_);
lean_dec(v_date_4647_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5107_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v___x_5102_; 
if (v_isShared_5061_ == 0)
{
lean_ctor_set_tag(v___x_5060_, 1);
lean_ctor_set(v___x_5060_, 0, v_data_4649_);
v___x_5102_ = v___x_5060_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_data_4649_);
v___x_5102_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5101_;
}
v_reusejp_5101_:
{
lean_object* v___x_5104_; 
if (v_isShared_5100_ == 0)
{
lean_ctor_set(v___x_5099_, 9, v___x_5102_);
v___x_5104_ = v___x_5099_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_G_5062_);
lean_ctor_set(v_reuseFailAlloc_5105_, 1, v_y_5063_);
lean_ctor_set(v_reuseFailAlloc_5105_, 2, v_u_5064_);
lean_ctor_set(v_reuseFailAlloc_5105_, 3, v_Y_5065_);
lean_ctor_set(v_reuseFailAlloc_5105_, 4, v_D_5066_);
lean_ctor_set(v_reuseFailAlloc_5105_, 5, v_M_5067_);
lean_ctor_set(v_reuseFailAlloc_5105_, 6, v_L_5068_);
lean_ctor_set(v_reuseFailAlloc_5105_, 7, v_d_5069_);
lean_ctor_set(v_reuseFailAlloc_5105_, 8, v_Q_5070_);
lean_ctor_set(v_reuseFailAlloc_5105_, 9, v___x_5102_);
lean_ctor_set(v_reuseFailAlloc_5105_, 10, v_w_5071_);
lean_ctor_set(v_reuseFailAlloc_5105_, 11, v_W_5072_);
lean_ctor_set(v_reuseFailAlloc_5105_, 12, v_E_5073_);
lean_ctor_set(v_reuseFailAlloc_5105_, 13, v_e_5074_);
lean_ctor_set(v_reuseFailAlloc_5105_, 14, v_c_5075_);
lean_ctor_set(v_reuseFailAlloc_5105_, 15, v_F_5076_);
lean_ctor_set(v_reuseFailAlloc_5105_, 16, v_a_5077_);
lean_ctor_set(v_reuseFailAlloc_5105_, 17, v_b_5078_);
lean_ctor_set(v_reuseFailAlloc_5105_, 18, v_B_5079_);
lean_ctor_set(v_reuseFailAlloc_5105_, 19, v_h_5080_);
lean_ctor_set(v_reuseFailAlloc_5105_, 20, v_K_5081_);
lean_ctor_set(v_reuseFailAlloc_5105_, 21, v_k_5082_);
lean_ctor_set(v_reuseFailAlloc_5105_, 22, v_H_5083_);
lean_ctor_set(v_reuseFailAlloc_5105_, 23, v_m_5084_);
lean_ctor_set(v_reuseFailAlloc_5105_, 24, v_s_5085_);
lean_ctor_set(v_reuseFailAlloc_5105_, 25, v_S_5086_);
lean_ctor_set(v_reuseFailAlloc_5105_, 26, v_A_5087_);
lean_ctor_set(v_reuseFailAlloc_5105_, 27, v_n_5088_);
lean_ctor_set(v_reuseFailAlloc_5105_, 28, v_N_5089_);
lean_ctor_set(v_reuseFailAlloc_5105_, 29, v_V_5090_);
lean_ctor_set(v_reuseFailAlloc_5105_, 30, v_z_5091_);
lean_ctor_set(v_reuseFailAlloc_5105_, 31, v_zabbrev_5092_);
lean_ctor_set(v_reuseFailAlloc_5105_, 32, v_v_5093_);
lean_ctor_set(v_reuseFailAlloc_5105_, 33, v_O_5094_);
lean_ctor_set(v_reuseFailAlloc_5105_, 34, v_X_5095_);
lean_ctor_set(v_reuseFailAlloc_5105_, 35, v_x_5096_);
lean_ctor_set(v_reuseFailAlloc_5105_, 36, v_Z_5097_);
v___x_5104_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
return v___x_5104_;
}
}
}
}
}
case 9:
{
lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5161_; 
v_isSharedCheck_5161_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_5161_ == 0)
{
lean_object* v_unused_5162_; 
v_unused_5162_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_5162_);
v___x_5112_ = v_modifier_4648_;
v_isShared_5113_ = v_isSharedCheck_5161_;
goto v_resetjp_5111_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_5112_ = lean_box(0);
v_isShared_5113_ = v_isSharedCheck_5161_;
goto v_resetjp_5111_;
}
v_resetjp_5111_:
{
lean_object* v_G_5114_; lean_object* v_y_5115_; lean_object* v_u_5116_; lean_object* v_D_5117_; lean_object* v_M_5118_; lean_object* v_L_5119_; lean_object* v_d_5120_; lean_object* v_Q_5121_; lean_object* v_q_5122_; lean_object* v_w_5123_; lean_object* v_W_5124_; lean_object* v_E_5125_; lean_object* v_e_5126_; lean_object* v_c_5127_; lean_object* v_F_5128_; lean_object* v_a_5129_; lean_object* v_b_5130_; lean_object* v_B_5131_; lean_object* v_h_5132_; lean_object* v_K_5133_; lean_object* v_k_5134_; lean_object* v_H_5135_; lean_object* v_m_5136_; lean_object* v_s_5137_; lean_object* v_S_5138_; lean_object* v_A_5139_; lean_object* v_n_5140_; lean_object* v_N_5141_; lean_object* v_V_5142_; lean_object* v_z_5143_; lean_object* v_zabbrev_5144_; lean_object* v_v_5145_; lean_object* v_O_5146_; lean_object* v_X_5147_; lean_object* v_x_5148_; lean_object* v_Z_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5159_; 
v_G_5114_ = lean_ctor_get(v_date_4647_, 0);
v_y_5115_ = lean_ctor_get(v_date_4647_, 1);
v_u_5116_ = lean_ctor_get(v_date_4647_, 2);
v_D_5117_ = lean_ctor_get(v_date_4647_, 4);
v_M_5118_ = lean_ctor_get(v_date_4647_, 5);
v_L_5119_ = lean_ctor_get(v_date_4647_, 6);
v_d_5120_ = lean_ctor_get(v_date_4647_, 7);
v_Q_5121_ = lean_ctor_get(v_date_4647_, 8);
v_q_5122_ = lean_ctor_get(v_date_4647_, 9);
v_w_5123_ = lean_ctor_get(v_date_4647_, 10);
v_W_5124_ = lean_ctor_get(v_date_4647_, 11);
v_E_5125_ = lean_ctor_get(v_date_4647_, 12);
v_e_5126_ = lean_ctor_get(v_date_4647_, 13);
v_c_5127_ = lean_ctor_get(v_date_4647_, 14);
v_F_5128_ = lean_ctor_get(v_date_4647_, 15);
v_a_5129_ = lean_ctor_get(v_date_4647_, 16);
v_b_5130_ = lean_ctor_get(v_date_4647_, 17);
v_B_5131_ = lean_ctor_get(v_date_4647_, 18);
v_h_5132_ = lean_ctor_get(v_date_4647_, 19);
v_K_5133_ = lean_ctor_get(v_date_4647_, 20);
v_k_5134_ = lean_ctor_get(v_date_4647_, 21);
v_H_5135_ = lean_ctor_get(v_date_4647_, 22);
v_m_5136_ = lean_ctor_get(v_date_4647_, 23);
v_s_5137_ = lean_ctor_get(v_date_4647_, 24);
v_S_5138_ = lean_ctor_get(v_date_4647_, 25);
v_A_5139_ = lean_ctor_get(v_date_4647_, 26);
v_n_5140_ = lean_ctor_get(v_date_4647_, 27);
v_N_5141_ = lean_ctor_get(v_date_4647_, 28);
v_V_5142_ = lean_ctor_get(v_date_4647_, 29);
v_z_5143_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_5144_ = lean_ctor_get(v_date_4647_, 31);
v_v_5145_ = lean_ctor_get(v_date_4647_, 32);
v_O_5146_ = lean_ctor_get(v_date_4647_, 33);
v_X_5147_ = lean_ctor_get(v_date_4647_, 34);
v_x_5148_ = lean_ctor_get(v_date_4647_, 35);
v_Z_5149_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5159_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5159_ == 0)
{
lean_object* v_unused_5160_; 
v_unused_5160_ = lean_ctor_get(v_date_4647_, 3);
lean_dec(v_unused_5160_);
v___x_5151_ = v_date_4647_;
v_isShared_5152_ = v_isSharedCheck_5159_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_Z_5149_);
lean_inc(v_x_5148_);
lean_inc(v_X_5147_);
lean_inc(v_O_5146_);
lean_inc(v_v_5145_);
lean_inc(v_zabbrev_5144_);
lean_inc(v_z_5143_);
lean_inc(v_V_5142_);
lean_inc(v_N_5141_);
lean_inc(v_n_5140_);
lean_inc(v_A_5139_);
lean_inc(v_S_5138_);
lean_inc(v_s_5137_);
lean_inc(v_m_5136_);
lean_inc(v_H_5135_);
lean_inc(v_k_5134_);
lean_inc(v_K_5133_);
lean_inc(v_h_5132_);
lean_inc(v_B_5131_);
lean_inc(v_b_5130_);
lean_inc(v_a_5129_);
lean_inc(v_F_5128_);
lean_inc(v_c_5127_);
lean_inc(v_e_5126_);
lean_inc(v_E_5125_);
lean_inc(v_W_5124_);
lean_inc(v_w_5123_);
lean_inc(v_q_5122_);
lean_inc(v_Q_5121_);
lean_inc(v_d_5120_);
lean_inc(v_L_5119_);
lean_inc(v_M_5118_);
lean_inc(v_D_5117_);
lean_inc(v_u_5116_);
lean_inc(v_y_5115_);
lean_inc(v_G_5114_);
lean_dec(v_date_4647_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5159_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5154_; 
if (v_isShared_5113_ == 0)
{
lean_ctor_set_tag(v___x_5112_, 1);
lean_ctor_set(v___x_5112_, 0, v_data_4649_);
v___x_5154_ = v___x_5112_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5158_; 
v_reuseFailAlloc_5158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5158_, 0, v_data_4649_);
v___x_5154_ = v_reuseFailAlloc_5158_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
lean_object* v___x_5156_; 
if (v_isShared_5152_ == 0)
{
lean_ctor_set(v___x_5151_, 3, v___x_5154_);
v___x_5156_ = v___x_5151_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v_G_5114_);
lean_ctor_set(v_reuseFailAlloc_5157_, 1, v_y_5115_);
lean_ctor_set(v_reuseFailAlloc_5157_, 2, v_u_5116_);
lean_ctor_set(v_reuseFailAlloc_5157_, 3, v___x_5154_);
lean_ctor_set(v_reuseFailAlloc_5157_, 4, v_D_5117_);
lean_ctor_set(v_reuseFailAlloc_5157_, 5, v_M_5118_);
lean_ctor_set(v_reuseFailAlloc_5157_, 6, v_L_5119_);
lean_ctor_set(v_reuseFailAlloc_5157_, 7, v_d_5120_);
lean_ctor_set(v_reuseFailAlloc_5157_, 8, v_Q_5121_);
lean_ctor_set(v_reuseFailAlloc_5157_, 9, v_q_5122_);
lean_ctor_set(v_reuseFailAlloc_5157_, 10, v_w_5123_);
lean_ctor_set(v_reuseFailAlloc_5157_, 11, v_W_5124_);
lean_ctor_set(v_reuseFailAlloc_5157_, 12, v_E_5125_);
lean_ctor_set(v_reuseFailAlloc_5157_, 13, v_e_5126_);
lean_ctor_set(v_reuseFailAlloc_5157_, 14, v_c_5127_);
lean_ctor_set(v_reuseFailAlloc_5157_, 15, v_F_5128_);
lean_ctor_set(v_reuseFailAlloc_5157_, 16, v_a_5129_);
lean_ctor_set(v_reuseFailAlloc_5157_, 17, v_b_5130_);
lean_ctor_set(v_reuseFailAlloc_5157_, 18, v_B_5131_);
lean_ctor_set(v_reuseFailAlloc_5157_, 19, v_h_5132_);
lean_ctor_set(v_reuseFailAlloc_5157_, 20, v_K_5133_);
lean_ctor_set(v_reuseFailAlloc_5157_, 21, v_k_5134_);
lean_ctor_set(v_reuseFailAlloc_5157_, 22, v_H_5135_);
lean_ctor_set(v_reuseFailAlloc_5157_, 23, v_m_5136_);
lean_ctor_set(v_reuseFailAlloc_5157_, 24, v_s_5137_);
lean_ctor_set(v_reuseFailAlloc_5157_, 25, v_S_5138_);
lean_ctor_set(v_reuseFailAlloc_5157_, 26, v_A_5139_);
lean_ctor_set(v_reuseFailAlloc_5157_, 27, v_n_5140_);
lean_ctor_set(v_reuseFailAlloc_5157_, 28, v_N_5141_);
lean_ctor_set(v_reuseFailAlloc_5157_, 29, v_V_5142_);
lean_ctor_set(v_reuseFailAlloc_5157_, 30, v_z_5143_);
lean_ctor_set(v_reuseFailAlloc_5157_, 31, v_zabbrev_5144_);
lean_ctor_set(v_reuseFailAlloc_5157_, 32, v_v_5145_);
lean_ctor_set(v_reuseFailAlloc_5157_, 33, v_O_5146_);
lean_ctor_set(v_reuseFailAlloc_5157_, 34, v_X_5147_);
lean_ctor_set(v_reuseFailAlloc_5157_, 35, v_x_5148_);
lean_ctor_set(v_reuseFailAlloc_5157_, 36, v_Z_5149_);
v___x_5156_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
return v___x_5156_;
}
}
}
}
}
case 10:
{
lean_object* v___x_5164_; uint8_t v_isShared_5165_; uint8_t v_isSharedCheck_5213_; 
v_isSharedCheck_5213_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_5213_ == 0)
{
lean_object* v_unused_5214_; 
v_unused_5214_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_5214_);
v___x_5164_ = v_modifier_4648_;
v_isShared_5165_ = v_isSharedCheck_5213_;
goto v_resetjp_5163_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_5164_ = lean_box(0);
v_isShared_5165_ = v_isSharedCheck_5213_;
goto v_resetjp_5163_;
}
v_resetjp_5163_:
{
lean_object* v_G_5166_; lean_object* v_y_5167_; lean_object* v_u_5168_; lean_object* v_Y_5169_; lean_object* v_D_5170_; lean_object* v_M_5171_; lean_object* v_L_5172_; lean_object* v_d_5173_; lean_object* v_Q_5174_; lean_object* v_q_5175_; lean_object* v_W_5176_; lean_object* v_E_5177_; lean_object* v_e_5178_; lean_object* v_c_5179_; lean_object* v_F_5180_; lean_object* v_a_5181_; lean_object* v_b_5182_; lean_object* v_B_5183_; lean_object* v_h_5184_; lean_object* v_K_5185_; lean_object* v_k_5186_; lean_object* v_H_5187_; lean_object* v_m_5188_; lean_object* v_s_5189_; lean_object* v_S_5190_; lean_object* v_A_5191_; lean_object* v_n_5192_; lean_object* v_N_5193_; lean_object* v_V_5194_; lean_object* v_z_5195_; lean_object* v_zabbrev_5196_; lean_object* v_v_5197_; lean_object* v_O_5198_; lean_object* v_X_5199_; lean_object* v_x_5200_; lean_object* v_Z_5201_; lean_object* v___x_5203_; uint8_t v_isShared_5204_; uint8_t v_isSharedCheck_5211_; 
v_G_5166_ = lean_ctor_get(v_date_4647_, 0);
v_y_5167_ = lean_ctor_get(v_date_4647_, 1);
v_u_5168_ = lean_ctor_get(v_date_4647_, 2);
v_Y_5169_ = lean_ctor_get(v_date_4647_, 3);
v_D_5170_ = lean_ctor_get(v_date_4647_, 4);
v_M_5171_ = lean_ctor_get(v_date_4647_, 5);
v_L_5172_ = lean_ctor_get(v_date_4647_, 6);
v_d_5173_ = lean_ctor_get(v_date_4647_, 7);
v_Q_5174_ = lean_ctor_get(v_date_4647_, 8);
v_q_5175_ = lean_ctor_get(v_date_4647_, 9);
v_W_5176_ = lean_ctor_get(v_date_4647_, 11);
v_E_5177_ = lean_ctor_get(v_date_4647_, 12);
v_e_5178_ = lean_ctor_get(v_date_4647_, 13);
v_c_5179_ = lean_ctor_get(v_date_4647_, 14);
v_F_5180_ = lean_ctor_get(v_date_4647_, 15);
v_a_5181_ = lean_ctor_get(v_date_4647_, 16);
v_b_5182_ = lean_ctor_get(v_date_4647_, 17);
v_B_5183_ = lean_ctor_get(v_date_4647_, 18);
v_h_5184_ = lean_ctor_get(v_date_4647_, 19);
v_K_5185_ = lean_ctor_get(v_date_4647_, 20);
v_k_5186_ = lean_ctor_get(v_date_4647_, 21);
v_H_5187_ = lean_ctor_get(v_date_4647_, 22);
v_m_5188_ = lean_ctor_get(v_date_4647_, 23);
v_s_5189_ = lean_ctor_get(v_date_4647_, 24);
v_S_5190_ = lean_ctor_get(v_date_4647_, 25);
v_A_5191_ = lean_ctor_get(v_date_4647_, 26);
v_n_5192_ = lean_ctor_get(v_date_4647_, 27);
v_N_5193_ = lean_ctor_get(v_date_4647_, 28);
v_V_5194_ = lean_ctor_get(v_date_4647_, 29);
v_z_5195_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_5196_ = lean_ctor_get(v_date_4647_, 31);
v_v_5197_ = lean_ctor_get(v_date_4647_, 32);
v_O_5198_ = lean_ctor_get(v_date_4647_, 33);
v_X_5199_ = lean_ctor_get(v_date_4647_, 34);
v_x_5200_ = lean_ctor_get(v_date_4647_, 35);
v_Z_5201_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5211_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5211_ == 0)
{
lean_object* v_unused_5212_; 
v_unused_5212_ = lean_ctor_get(v_date_4647_, 10);
lean_dec(v_unused_5212_);
v___x_5203_ = v_date_4647_;
v_isShared_5204_ = v_isSharedCheck_5211_;
goto v_resetjp_5202_;
}
else
{
lean_inc(v_Z_5201_);
lean_inc(v_x_5200_);
lean_inc(v_X_5199_);
lean_inc(v_O_5198_);
lean_inc(v_v_5197_);
lean_inc(v_zabbrev_5196_);
lean_inc(v_z_5195_);
lean_inc(v_V_5194_);
lean_inc(v_N_5193_);
lean_inc(v_n_5192_);
lean_inc(v_A_5191_);
lean_inc(v_S_5190_);
lean_inc(v_s_5189_);
lean_inc(v_m_5188_);
lean_inc(v_H_5187_);
lean_inc(v_k_5186_);
lean_inc(v_K_5185_);
lean_inc(v_h_5184_);
lean_inc(v_B_5183_);
lean_inc(v_b_5182_);
lean_inc(v_a_5181_);
lean_inc(v_F_5180_);
lean_inc(v_c_5179_);
lean_inc(v_e_5178_);
lean_inc(v_E_5177_);
lean_inc(v_W_5176_);
lean_inc(v_q_5175_);
lean_inc(v_Q_5174_);
lean_inc(v_d_5173_);
lean_inc(v_L_5172_);
lean_inc(v_M_5171_);
lean_inc(v_D_5170_);
lean_inc(v_Y_5169_);
lean_inc(v_u_5168_);
lean_inc(v_y_5167_);
lean_inc(v_G_5166_);
lean_dec(v_date_4647_);
v___x_5203_ = lean_box(0);
v_isShared_5204_ = v_isSharedCheck_5211_;
goto v_resetjp_5202_;
}
v_resetjp_5202_:
{
lean_object* v___x_5206_; 
if (v_isShared_5165_ == 0)
{
lean_ctor_set_tag(v___x_5164_, 1);
lean_ctor_set(v___x_5164_, 0, v_data_4649_);
v___x_5206_ = v___x_5164_;
goto v_reusejp_5205_;
}
else
{
lean_object* v_reuseFailAlloc_5210_; 
v_reuseFailAlloc_5210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5210_, 0, v_data_4649_);
v___x_5206_ = v_reuseFailAlloc_5210_;
goto v_reusejp_5205_;
}
v_reusejp_5205_:
{
lean_object* v___x_5208_; 
if (v_isShared_5204_ == 0)
{
lean_ctor_set(v___x_5203_, 10, v___x_5206_);
v___x_5208_ = v___x_5203_;
goto v_reusejp_5207_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v_G_5166_);
lean_ctor_set(v_reuseFailAlloc_5209_, 1, v_y_5167_);
lean_ctor_set(v_reuseFailAlloc_5209_, 2, v_u_5168_);
lean_ctor_set(v_reuseFailAlloc_5209_, 3, v_Y_5169_);
lean_ctor_set(v_reuseFailAlloc_5209_, 4, v_D_5170_);
lean_ctor_set(v_reuseFailAlloc_5209_, 5, v_M_5171_);
lean_ctor_set(v_reuseFailAlloc_5209_, 6, v_L_5172_);
lean_ctor_set(v_reuseFailAlloc_5209_, 7, v_d_5173_);
lean_ctor_set(v_reuseFailAlloc_5209_, 8, v_Q_5174_);
lean_ctor_set(v_reuseFailAlloc_5209_, 9, v_q_5175_);
lean_ctor_set(v_reuseFailAlloc_5209_, 10, v___x_5206_);
lean_ctor_set(v_reuseFailAlloc_5209_, 11, v_W_5176_);
lean_ctor_set(v_reuseFailAlloc_5209_, 12, v_E_5177_);
lean_ctor_set(v_reuseFailAlloc_5209_, 13, v_e_5178_);
lean_ctor_set(v_reuseFailAlloc_5209_, 14, v_c_5179_);
lean_ctor_set(v_reuseFailAlloc_5209_, 15, v_F_5180_);
lean_ctor_set(v_reuseFailAlloc_5209_, 16, v_a_5181_);
lean_ctor_set(v_reuseFailAlloc_5209_, 17, v_b_5182_);
lean_ctor_set(v_reuseFailAlloc_5209_, 18, v_B_5183_);
lean_ctor_set(v_reuseFailAlloc_5209_, 19, v_h_5184_);
lean_ctor_set(v_reuseFailAlloc_5209_, 20, v_K_5185_);
lean_ctor_set(v_reuseFailAlloc_5209_, 21, v_k_5186_);
lean_ctor_set(v_reuseFailAlloc_5209_, 22, v_H_5187_);
lean_ctor_set(v_reuseFailAlloc_5209_, 23, v_m_5188_);
lean_ctor_set(v_reuseFailAlloc_5209_, 24, v_s_5189_);
lean_ctor_set(v_reuseFailAlloc_5209_, 25, v_S_5190_);
lean_ctor_set(v_reuseFailAlloc_5209_, 26, v_A_5191_);
lean_ctor_set(v_reuseFailAlloc_5209_, 27, v_n_5192_);
lean_ctor_set(v_reuseFailAlloc_5209_, 28, v_N_5193_);
lean_ctor_set(v_reuseFailAlloc_5209_, 29, v_V_5194_);
lean_ctor_set(v_reuseFailAlloc_5209_, 30, v_z_5195_);
lean_ctor_set(v_reuseFailAlloc_5209_, 31, v_zabbrev_5196_);
lean_ctor_set(v_reuseFailAlloc_5209_, 32, v_v_5197_);
lean_ctor_set(v_reuseFailAlloc_5209_, 33, v_O_5198_);
lean_ctor_set(v_reuseFailAlloc_5209_, 34, v_X_5199_);
lean_ctor_set(v_reuseFailAlloc_5209_, 35, v_x_5200_);
lean_ctor_set(v_reuseFailAlloc_5209_, 36, v_Z_5201_);
v___x_5208_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5207_;
}
v_reusejp_5207_:
{
return v___x_5208_;
}
}
}
}
}
case 11:
{
lean_object* v___x_5216_; uint8_t v_isShared_5217_; uint8_t v_isSharedCheck_5265_; 
v_isSharedCheck_5265_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_5265_ == 0)
{
lean_object* v_unused_5266_; 
v_unused_5266_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_5266_);
v___x_5216_ = v_modifier_4648_;
v_isShared_5217_ = v_isSharedCheck_5265_;
goto v_resetjp_5215_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_5216_ = lean_box(0);
v_isShared_5217_ = v_isSharedCheck_5265_;
goto v_resetjp_5215_;
}
v_resetjp_5215_:
{
lean_object* v_G_5218_; lean_object* v_y_5219_; lean_object* v_u_5220_; lean_object* v_Y_5221_; lean_object* v_D_5222_; lean_object* v_M_5223_; lean_object* v_L_5224_; lean_object* v_d_5225_; lean_object* v_Q_5226_; lean_object* v_q_5227_; lean_object* v_w_5228_; lean_object* v_E_5229_; lean_object* v_e_5230_; lean_object* v_c_5231_; lean_object* v_F_5232_; lean_object* v_a_5233_; lean_object* v_b_5234_; lean_object* v_B_5235_; lean_object* v_h_5236_; lean_object* v_K_5237_; lean_object* v_k_5238_; lean_object* v_H_5239_; lean_object* v_m_5240_; lean_object* v_s_5241_; lean_object* v_S_5242_; lean_object* v_A_5243_; lean_object* v_n_5244_; lean_object* v_N_5245_; lean_object* v_V_5246_; lean_object* v_z_5247_; lean_object* v_zabbrev_5248_; lean_object* v_v_5249_; lean_object* v_O_5250_; lean_object* v_X_5251_; lean_object* v_x_5252_; lean_object* v_Z_5253_; lean_object* v___x_5255_; uint8_t v_isShared_5256_; uint8_t v_isSharedCheck_5263_; 
v_G_5218_ = lean_ctor_get(v_date_4647_, 0);
v_y_5219_ = lean_ctor_get(v_date_4647_, 1);
v_u_5220_ = lean_ctor_get(v_date_4647_, 2);
v_Y_5221_ = lean_ctor_get(v_date_4647_, 3);
v_D_5222_ = lean_ctor_get(v_date_4647_, 4);
v_M_5223_ = lean_ctor_get(v_date_4647_, 5);
v_L_5224_ = lean_ctor_get(v_date_4647_, 6);
v_d_5225_ = lean_ctor_get(v_date_4647_, 7);
v_Q_5226_ = lean_ctor_get(v_date_4647_, 8);
v_q_5227_ = lean_ctor_get(v_date_4647_, 9);
v_w_5228_ = lean_ctor_get(v_date_4647_, 10);
v_E_5229_ = lean_ctor_get(v_date_4647_, 12);
v_e_5230_ = lean_ctor_get(v_date_4647_, 13);
v_c_5231_ = lean_ctor_get(v_date_4647_, 14);
v_F_5232_ = lean_ctor_get(v_date_4647_, 15);
v_a_5233_ = lean_ctor_get(v_date_4647_, 16);
v_b_5234_ = lean_ctor_get(v_date_4647_, 17);
v_B_5235_ = lean_ctor_get(v_date_4647_, 18);
v_h_5236_ = lean_ctor_get(v_date_4647_, 19);
v_K_5237_ = lean_ctor_get(v_date_4647_, 20);
v_k_5238_ = lean_ctor_get(v_date_4647_, 21);
v_H_5239_ = lean_ctor_get(v_date_4647_, 22);
v_m_5240_ = lean_ctor_get(v_date_4647_, 23);
v_s_5241_ = lean_ctor_get(v_date_4647_, 24);
v_S_5242_ = lean_ctor_get(v_date_4647_, 25);
v_A_5243_ = lean_ctor_get(v_date_4647_, 26);
v_n_5244_ = lean_ctor_get(v_date_4647_, 27);
v_N_5245_ = lean_ctor_get(v_date_4647_, 28);
v_V_5246_ = lean_ctor_get(v_date_4647_, 29);
v_z_5247_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_5248_ = lean_ctor_get(v_date_4647_, 31);
v_v_5249_ = lean_ctor_get(v_date_4647_, 32);
v_O_5250_ = lean_ctor_get(v_date_4647_, 33);
v_X_5251_ = lean_ctor_get(v_date_4647_, 34);
v_x_5252_ = lean_ctor_get(v_date_4647_, 35);
v_Z_5253_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5263_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5263_ == 0)
{
lean_object* v_unused_5264_; 
v_unused_5264_ = lean_ctor_get(v_date_4647_, 11);
lean_dec(v_unused_5264_);
v___x_5255_ = v_date_4647_;
v_isShared_5256_ = v_isSharedCheck_5263_;
goto v_resetjp_5254_;
}
else
{
lean_inc(v_Z_5253_);
lean_inc(v_x_5252_);
lean_inc(v_X_5251_);
lean_inc(v_O_5250_);
lean_inc(v_v_5249_);
lean_inc(v_zabbrev_5248_);
lean_inc(v_z_5247_);
lean_inc(v_V_5246_);
lean_inc(v_N_5245_);
lean_inc(v_n_5244_);
lean_inc(v_A_5243_);
lean_inc(v_S_5242_);
lean_inc(v_s_5241_);
lean_inc(v_m_5240_);
lean_inc(v_H_5239_);
lean_inc(v_k_5238_);
lean_inc(v_K_5237_);
lean_inc(v_h_5236_);
lean_inc(v_B_5235_);
lean_inc(v_b_5234_);
lean_inc(v_a_5233_);
lean_inc(v_F_5232_);
lean_inc(v_c_5231_);
lean_inc(v_e_5230_);
lean_inc(v_E_5229_);
lean_inc(v_w_5228_);
lean_inc(v_q_5227_);
lean_inc(v_Q_5226_);
lean_inc(v_d_5225_);
lean_inc(v_L_5224_);
lean_inc(v_M_5223_);
lean_inc(v_D_5222_);
lean_inc(v_Y_5221_);
lean_inc(v_u_5220_);
lean_inc(v_y_5219_);
lean_inc(v_G_5218_);
lean_dec(v_date_4647_);
v___x_5255_ = lean_box(0);
v_isShared_5256_ = v_isSharedCheck_5263_;
goto v_resetjp_5254_;
}
v_resetjp_5254_:
{
lean_object* v___x_5258_; 
if (v_isShared_5217_ == 0)
{
lean_ctor_set_tag(v___x_5216_, 1);
lean_ctor_set(v___x_5216_, 0, v_data_4649_);
v___x_5258_ = v___x_5216_;
goto v_reusejp_5257_;
}
else
{
lean_object* v_reuseFailAlloc_5262_; 
v_reuseFailAlloc_5262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_data_4649_);
v___x_5258_ = v_reuseFailAlloc_5262_;
goto v_reusejp_5257_;
}
v_reusejp_5257_:
{
lean_object* v___x_5260_; 
if (v_isShared_5256_ == 0)
{
lean_ctor_set(v___x_5255_, 11, v___x_5258_);
v___x_5260_ = v___x_5255_;
goto v_reusejp_5259_;
}
else
{
lean_object* v_reuseFailAlloc_5261_; 
v_reuseFailAlloc_5261_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_G_5218_);
lean_ctor_set(v_reuseFailAlloc_5261_, 1, v_y_5219_);
lean_ctor_set(v_reuseFailAlloc_5261_, 2, v_u_5220_);
lean_ctor_set(v_reuseFailAlloc_5261_, 3, v_Y_5221_);
lean_ctor_set(v_reuseFailAlloc_5261_, 4, v_D_5222_);
lean_ctor_set(v_reuseFailAlloc_5261_, 5, v_M_5223_);
lean_ctor_set(v_reuseFailAlloc_5261_, 6, v_L_5224_);
lean_ctor_set(v_reuseFailAlloc_5261_, 7, v_d_5225_);
lean_ctor_set(v_reuseFailAlloc_5261_, 8, v_Q_5226_);
lean_ctor_set(v_reuseFailAlloc_5261_, 9, v_q_5227_);
lean_ctor_set(v_reuseFailAlloc_5261_, 10, v_w_5228_);
lean_ctor_set(v_reuseFailAlloc_5261_, 11, v___x_5258_);
lean_ctor_set(v_reuseFailAlloc_5261_, 12, v_E_5229_);
lean_ctor_set(v_reuseFailAlloc_5261_, 13, v_e_5230_);
lean_ctor_set(v_reuseFailAlloc_5261_, 14, v_c_5231_);
lean_ctor_set(v_reuseFailAlloc_5261_, 15, v_F_5232_);
lean_ctor_set(v_reuseFailAlloc_5261_, 16, v_a_5233_);
lean_ctor_set(v_reuseFailAlloc_5261_, 17, v_b_5234_);
lean_ctor_set(v_reuseFailAlloc_5261_, 18, v_B_5235_);
lean_ctor_set(v_reuseFailAlloc_5261_, 19, v_h_5236_);
lean_ctor_set(v_reuseFailAlloc_5261_, 20, v_K_5237_);
lean_ctor_set(v_reuseFailAlloc_5261_, 21, v_k_5238_);
lean_ctor_set(v_reuseFailAlloc_5261_, 22, v_H_5239_);
lean_ctor_set(v_reuseFailAlloc_5261_, 23, v_m_5240_);
lean_ctor_set(v_reuseFailAlloc_5261_, 24, v_s_5241_);
lean_ctor_set(v_reuseFailAlloc_5261_, 25, v_S_5242_);
lean_ctor_set(v_reuseFailAlloc_5261_, 26, v_A_5243_);
lean_ctor_set(v_reuseFailAlloc_5261_, 27, v_n_5244_);
lean_ctor_set(v_reuseFailAlloc_5261_, 28, v_N_5245_);
lean_ctor_set(v_reuseFailAlloc_5261_, 29, v_V_5246_);
lean_ctor_set(v_reuseFailAlloc_5261_, 30, v_z_5247_);
lean_ctor_set(v_reuseFailAlloc_5261_, 31, v_zabbrev_5248_);
lean_ctor_set(v_reuseFailAlloc_5261_, 32, v_v_5249_);
lean_ctor_set(v_reuseFailAlloc_5261_, 33, v_O_5250_);
lean_ctor_set(v_reuseFailAlloc_5261_, 34, v_X_5251_);
lean_ctor_set(v_reuseFailAlloc_5261_, 35, v_x_5252_);
lean_ctor_set(v_reuseFailAlloc_5261_, 36, v_Z_5253_);
v___x_5260_ = v_reuseFailAlloc_5261_;
goto v_reusejp_5259_;
}
v_reusejp_5259_:
{
return v___x_5260_;
}
}
}
}
}
case 12:
{
lean_object* v_G_5267_; lean_object* v_y_5268_; lean_object* v_u_5269_; lean_object* v_Y_5270_; lean_object* v_D_5271_; lean_object* v_M_5272_; lean_object* v_L_5273_; lean_object* v_d_5274_; lean_object* v_Q_5275_; lean_object* v_q_5276_; lean_object* v_w_5277_; lean_object* v_W_5278_; lean_object* v_e_5279_; lean_object* v_c_5280_; lean_object* v_F_5281_; lean_object* v_a_5282_; lean_object* v_b_5283_; lean_object* v_B_5284_; lean_object* v_h_5285_; lean_object* v_K_5286_; lean_object* v_k_5287_; lean_object* v_H_5288_; lean_object* v_m_5289_; lean_object* v_s_5290_; lean_object* v_S_5291_; lean_object* v_A_5292_; lean_object* v_n_5293_; lean_object* v_N_5294_; lean_object* v_V_5295_; lean_object* v_z_5296_; lean_object* v_zabbrev_5297_; lean_object* v_v_5298_; lean_object* v_O_5299_; lean_object* v_X_5300_; lean_object* v_x_5301_; lean_object* v_Z_5302_; lean_object* v___x_5304_; uint8_t v_isShared_5305_; uint8_t v_isSharedCheck_5310_; 
lean_dec_ref_known(v_modifier_4648_, 0);
v_G_5267_ = lean_ctor_get(v_date_4647_, 0);
v_y_5268_ = lean_ctor_get(v_date_4647_, 1);
v_u_5269_ = lean_ctor_get(v_date_4647_, 2);
v_Y_5270_ = lean_ctor_get(v_date_4647_, 3);
v_D_5271_ = lean_ctor_get(v_date_4647_, 4);
v_M_5272_ = lean_ctor_get(v_date_4647_, 5);
v_L_5273_ = lean_ctor_get(v_date_4647_, 6);
v_d_5274_ = lean_ctor_get(v_date_4647_, 7);
v_Q_5275_ = lean_ctor_get(v_date_4647_, 8);
v_q_5276_ = lean_ctor_get(v_date_4647_, 9);
v_w_5277_ = lean_ctor_get(v_date_4647_, 10);
v_W_5278_ = lean_ctor_get(v_date_4647_, 11);
v_e_5279_ = lean_ctor_get(v_date_4647_, 13);
v_c_5280_ = lean_ctor_get(v_date_4647_, 14);
v_F_5281_ = lean_ctor_get(v_date_4647_, 15);
v_a_5282_ = lean_ctor_get(v_date_4647_, 16);
v_b_5283_ = lean_ctor_get(v_date_4647_, 17);
v_B_5284_ = lean_ctor_get(v_date_4647_, 18);
v_h_5285_ = lean_ctor_get(v_date_4647_, 19);
v_K_5286_ = lean_ctor_get(v_date_4647_, 20);
v_k_5287_ = lean_ctor_get(v_date_4647_, 21);
v_H_5288_ = lean_ctor_get(v_date_4647_, 22);
v_m_5289_ = lean_ctor_get(v_date_4647_, 23);
v_s_5290_ = lean_ctor_get(v_date_4647_, 24);
v_S_5291_ = lean_ctor_get(v_date_4647_, 25);
v_A_5292_ = lean_ctor_get(v_date_4647_, 26);
v_n_5293_ = lean_ctor_get(v_date_4647_, 27);
v_N_5294_ = lean_ctor_get(v_date_4647_, 28);
v_V_5295_ = lean_ctor_get(v_date_4647_, 29);
v_z_5296_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_5297_ = lean_ctor_get(v_date_4647_, 31);
v_v_5298_ = lean_ctor_get(v_date_4647_, 32);
v_O_5299_ = lean_ctor_get(v_date_4647_, 33);
v_X_5300_ = lean_ctor_get(v_date_4647_, 34);
v_x_5301_ = lean_ctor_get(v_date_4647_, 35);
v_Z_5302_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5310_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5310_ == 0)
{
lean_object* v_unused_5311_; 
v_unused_5311_ = lean_ctor_get(v_date_4647_, 12);
lean_dec(v_unused_5311_);
v___x_5304_ = v_date_4647_;
v_isShared_5305_ = v_isSharedCheck_5310_;
goto v_resetjp_5303_;
}
else
{
lean_inc(v_Z_5302_);
lean_inc(v_x_5301_);
lean_inc(v_X_5300_);
lean_inc(v_O_5299_);
lean_inc(v_v_5298_);
lean_inc(v_zabbrev_5297_);
lean_inc(v_z_5296_);
lean_inc(v_V_5295_);
lean_inc(v_N_5294_);
lean_inc(v_n_5293_);
lean_inc(v_A_5292_);
lean_inc(v_S_5291_);
lean_inc(v_s_5290_);
lean_inc(v_m_5289_);
lean_inc(v_H_5288_);
lean_inc(v_k_5287_);
lean_inc(v_K_5286_);
lean_inc(v_h_5285_);
lean_inc(v_B_5284_);
lean_inc(v_b_5283_);
lean_inc(v_a_5282_);
lean_inc(v_F_5281_);
lean_inc(v_c_5280_);
lean_inc(v_e_5279_);
lean_inc(v_W_5278_);
lean_inc(v_w_5277_);
lean_inc(v_q_5276_);
lean_inc(v_Q_5275_);
lean_inc(v_d_5274_);
lean_inc(v_L_5273_);
lean_inc(v_M_5272_);
lean_inc(v_D_5271_);
lean_inc(v_Y_5270_);
lean_inc(v_u_5269_);
lean_inc(v_y_5268_);
lean_inc(v_G_5267_);
lean_dec(v_date_4647_);
v___x_5304_ = lean_box(0);
v_isShared_5305_ = v_isSharedCheck_5310_;
goto v_resetjp_5303_;
}
v_resetjp_5303_:
{
lean_object* v___x_5306_; lean_object* v___x_5308_; 
v___x_5306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5306_, 0, v_data_4649_);
if (v_isShared_5305_ == 0)
{
lean_ctor_set(v___x_5304_, 12, v___x_5306_);
v___x_5308_ = v___x_5304_;
goto v_reusejp_5307_;
}
else
{
lean_object* v_reuseFailAlloc_5309_; 
v_reuseFailAlloc_5309_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5309_, 0, v_G_5267_);
lean_ctor_set(v_reuseFailAlloc_5309_, 1, v_y_5268_);
lean_ctor_set(v_reuseFailAlloc_5309_, 2, v_u_5269_);
lean_ctor_set(v_reuseFailAlloc_5309_, 3, v_Y_5270_);
lean_ctor_set(v_reuseFailAlloc_5309_, 4, v_D_5271_);
lean_ctor_set(v_reuseFailAlloc_5309_, 5, v_M_5272_);
lean_ctor_set(v_reuseFailAlloc_5309_, 6, v_L_5273_);
lean_ctor_set(v_reuseFailAlloc_5309_, 7, v_d_5274_);
lean_ctor_set(v_reuseFailAlloc_5309_, 8, v_Q_5275_);
lean_ctor_set(v_reuseFailAlloc_5309_, 9, v_q_5276_);
lean_ctor_set(v_reuseFailAlloc_5309_, 10, v_w_5277_);
lean_ctor_set(v_reuseFailAlloc_5309_, 11, v_W_5278_);
lean_ctor_set(v_reuseFailAlloc_5309_, 12, v___x_5306_);
lean_ctor_set(v_reuseFailAlloc_5309_, 13, v_e_5279_);
lean_ctor_set(v_reuseFailAlloc_5309_, 14, v_c_5280_);
lean_ctor_set(v_reuseFailAlloc_5309_, 15, v_F_5281_);
lean_ctor_set(v_reuseFailAlloc_5309_, 16, v_a_5282_);
lean_ctor_set(v_reuseFailAlloc_5309_, 17, v_b_5283_);
lean_ctor_set(v_reuseFailAlloc_5309_, 18, v_B_5284_);
lean_ctor_set(v_reuseFailAlloc_5309_, 19, v_h_5285_);
lean_ctor_set(v_reuseFailAlloc_5309_, 20, v_K_5286_);
lean_ctor_set(v_reuseFailAlloc_5309_, 21, v_k_5287_);
lean_ctor_set(v_reuseFailAlloc_5309_, 22, v_H_5288_);
lean_ctor_set(v_reuseFailAlloc_5309_, 23, v_m_5289_);
lean_ctor_set(v_reuseFailAlloc_5309_, 24, v_s_5290_);
lean_ctor_set(v_reuseFailAlloc_5309_, 25, v_S_5291_);
lean_ctor_set(v_reuseFailAlloc_5309_, 26, v_A_5292_);
lean_ctor_set(v_reuseFailAlloc_5309_, 27, v_n_5293_);
lean_ctor_set(v_reuseFailAlloc_5309_, 28, v_N_5294_);
lean_ctor_set(v_reuseFailAlloc_5309_, 29, v_V_5295_);
lean_ctor_set(v_reuseFailAlloc_5309_, 30, v_z_5296_);
lean_ctor_set(v_reuseFailAlloc_5309_, 31, v_zabbrev_5297_);
lean_ctor_set(v_reuseFailAlloc_5309_, 32, v_v_5298_);
lean_ctor_set(v_reuseFailAlloc_5309_, 33, v_O_5299_);
lean_ctor_set(v_reuseFailAlloc_5309_, 34, v_X_5300_);
lean_ctor_set(v_reuseFailAlloc_5309_, 35, v_x_5301_);
lean_ctor_set(v_reuseFailAlloc_5309_, 36, v_Z_5302_);
v___x_5308_ = v_reuseFailAlloc_5309_;
goto v_reusejp_5307_;
}
v_reusejp_5307_:
{
return v___x_5308_;
}
}
}
case 13:
{
lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5362_; 
v_isSharedCheck_5362_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_5362_ == 0)
{
lean_object* v_unused_5363_; 
v_unused_5363_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_5363_);
v___x_5313_ = v_modifier_4648_;
v_isShared_5314_ = v_isSharedCheck_5362_;
goto v_resetjp_5312_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5362_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
lean_object* v_G_5315_; lean_object* v_y_5316_; lean_object* v_u_5317_; lean_object* v_Y_5318_; lean_object* v_D_5319_; lean_object* v_M_5320_; lean_object* v_L_5321_; lean_object* v_d_5322_; lean_object* v_Q_5323_; lean_object* v_q_5324_; lean_object* v_w_5325_; lean_object* v_W_5326_; lean_object* v_E_5327_; lean_object* v_c_5328_; lean_object* v_F_5329_; lean_object* v_a_5330_; lean_object* v_b_5331_; lean_object* v_B_5332_; lean_object* v_h_5333_; lean_object* v_K_5334_; lean_object* v_k_5335_; lean_object* v_H_5336_; lean_object* v_m_5337_; lean_object* v_s_5338_; lean_object* v_S_5339_; lean_object* v_A_5340_; lean_object* v_n_5341_; lean_object* v_N_5342_; lean_object* v_V_5343_; lean_object* v_z_5344_; lean_object* v_zabbrev_5345_; lean_object* v_v_5346_; lean_object* v_O_5347_; lean_object* v_X_5348_; lean_object* v_x_5349_; lean_object* v_Z_5350_; lean_object* v___x_5352_; uint8_t v_isShared_5353_; uint8_t v_isSharedCheck_5360_; 
v_G_5315_ = lean_ctor_get(v_date_4647_, 0);
v_y_5316_ = lean_ctor_get(v_date_4647_, 1);
v_u_5317_ = lean_ctor_get(v_date_4647_, 2);
v_Y_5318_ = lean_ctor_get(v_date_4647_, 3);
v_D_5319_ = lean_ctor_get(v_date_4647_, 4);
v_M_5320_ = lean_ctor_get(v_date_4647_, 5);
v_L_5321_ = lean_ctor_get(v_date_4647_, 6);
v_d_5322_ = lean_ctor_get(v_date_4647_, 7);
v_Q_5323_ = lean_ctor_get(v_date_4647_, 8);
v_q_5324_ = lean_ctor_get(v_date_4647_, 9);
v_w_5325_ = lean_ctor_get(v_date_4647_, 10);
v_W_5326_ = lean_ctor_get(v_date_4647_, 11);
v_E_5327_ = lean_ctor_get(v_date_4647_, 12);
v_c_5328_ = lean_ctor_get(v_date_4647_, 14);
v_F_5329_ = lean_ctor_get(v_date_4647_, 15);
v_a_5330_ = lean_ctor_get(v_date_4647_, 16);
v_b_5331_ = lean_ctor_get(v_date_4647_, 17);
v_B_5332_ = lean_ctor_get(v_date_4647_, 18);
v_h_5333_ = lean_ctor_get(v_date_4647_, 19);
v_K_5334_ = lean_ctor_get(v_date_4647_, 20);
v_k_5335_ = lean_ctor_get(v_date_4647_, 21);
v_H_5336_ = lean_ctor_get(v_date_4647_, 22);
v_m_5337_ = lean_ctor_get(v_date_4647_, 23);
v_s_5338_ = lean_ctor_get(v_date_4647_, 24);
v_S_5339_ = lean_ctor_get(v_date_4647_, 25);
v_A_5340_ = lean_ctor_get(v_date_4647_, 26);
v_n_5341_ = lean_ctor_get(v_date_4647_, 27);
v_N_5342_ = lean_ctor_get(v_date_4647_, 28);
v_V_5343_ = lean_ctor_get(v_date_4647_, 29);
v_z_5344_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_5345_ = lean_ctor_get(v_date_4647_, 31);
v_v_5346_ = lean_ctor_get(v_date_4647_, 32);
v_O_5347_ = lean_ctor_get(v_date_4647_, 33);
v_X_5348_ = lean_ctor_get(v_date_4647_, 34);
v_x_5349_ = lean_ctor_get(v_date_4647_, 35);
v_Z_5350_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5360_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5360_ == 0)
{
lean_object* v_unused_5361_; 
v_unused_5361_ = lean_ctor_get(v_date_4647_, 13);
lean_dec(v_unused_5361_);
v___x_5352_ = v_date_4647_;
v_isShared_5353_ = v_isSharedCheck_5360_;
goto v_resetjp_5351_;
}
else
{
lean_inc(v_Z_5350_);
lean_inc(v_x_5349_);
lean_inc(v_X_5348_);
lean_inc(v_O_5347_);
lean_inc(v_v_5346_);
lean_inc(v_zabbrev_5345_);
lean_inc(v_z_5344_);
lean_inc(v_V_5343_);
lean_inc(v_N_5342_);
lean_inc(v_n_5341_);
lean_inc(v_A_5340_);
lean_inc(v_S_5339_);
lean_inc(v_s_5338_);
lean_inc(v_m_5337_);
lean_inc(v_H_5336_);
lean_inc(v_k_5335_);
lean_inc(v_K_5334_);
lean_inc(v_h_5333_);
lean_inc(v_B_5332_);
lean_inc(v_b_5331_);
lean_inc(v_a_5330_);
lean_inc(v_F_5329_);
lean_inc(v_c_5328_);
lean_inc(v_E_5327_);
lean_inc(v_W_5326_);
lean_inc(v_w_5325_);
lean_inc(v_q_5324_);
lean_inc(v_Q_5323_);
lean_inc(v_d_5322_);
lean_inc(v_L_5321_);
lean_inc(v_M_5320_);
lean_inc(v_D_5319_);
lean_inc(v_Y_5318_);
lean_inc(v_u_5317_);
lean_inc(v_y_5316_);
lean_inc(v_G_5315_);
lean_dec(v_date_4647_);
v___x_5352_ = lean_box(0);
v_isShared_5353_ = v_isSharedCheck_5360_;
goto v_resetjp_5351_;
}
v_resetjp_5351_:
{
lean_object* v___x_5355_; 
if (v_isShared_5314_ == 0)
{
lean_ctor_set_tag(v___x_5313_, 1);
lean_ctor_set(v___x_5313_, 0, v_data_4649_);
v___x_5355_ = v___x_5313_;
goto v_reusejp_5354_;
}
else
{
lean_object* v_reuseFailAlloc_5359_; 
v_reuseFailAlloc_5359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5359_, 0, v_data_4649_);
v___x_5355_ = v_reuseFailAlloc_5359_;
goto v_reusejp_5354_;
}
v_reusejp_5354_:
{
lean_object* v___x_5357_; 
if (v_isShared_5353_ == 0)
{
lean_ctor_set(v___x_5352_, 13, v___x_5355_);
v___x_5357_ = v___x_5352_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5358_; 
v_reuseFailAlloc_5358_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5358_, 0, v_G_5315_);
lean_ctor_set(v_reuseFailAlloc_5358_, 1, v_y_5316_);
lean_ctor_set(v_reuseFailAlloc_5358_, 2, v_u_5317_);
lean_ctor_set(v_reuseFailAlloc_5358_, 3, v_Y_5318_);
lean_ctor_set(v_reuseFailAlloc_5358_, 4, v_D_5319_);
lean_ctor_set(v_reuseFailAlloc_5358_, 5, v_M_5320_);
lean_ctor_set(v_reuseFailAlloc_5358_, 6, v_L_5321_);
lean_ctor_set(v_reuseFailAlloc_5358_, 7, v_d_5322_);
lean_ctor_set(v_reuseFailAlloc_5358_, 8, v_Q_5323_);
lean_ctor_set(v_reuseFailAlloc_5358_, 9, v_q_5324_);
lean_ctor_set(v_reuseFailAlloc_5358_, 10, v_w_5325_);
lean_ctor_set(v_reuseFailAlloc_5358_, 11, v_W_5326_);
lean_ctor_set(v_reuseFailAlloc_5358_, 12, v_E_5327_);
lean_ctor_set(v_reuseFailAlloc_5358_, 13, v___x_5355_);
lean_ctor_set(v_reuseFailAlloc_5358_, 14, v_c_5328_);
lean_ctor_set(v_reuseFailAlloc_5358_, 15, v_F_5329_);
lean_ctor_set(v_reuseFailAlloc_5358_, 16, v_a_5330_);
lean_ctor_set(v_reuseFailAlloc_5358_, 17, v_b_5331_);
lean_ctor_set(v_reuseFailAlloc_5358_, 18, v_B_5332_);
lean_ctor_set(v_reuseFailAlloc_5358_, 19, v_h_5333_);
lean_ctor_set(v_reuseFailAlloc_5358_, 20, v_K_5334_);
lean_ctor_set(v_reuseFailAlloc_5358_, 21, v_k_5335_);
lean_ctor_set(v_reuseFailAlloc_5358_, 22, v_H_5336_);
lean_ctor_set(v_reuseFailAlloc_5358_, 23, v_m_5337_);
lean_ctor_set(v_reuseFailAlloc_5358_, 24, v_s_5338_);
lean_ctor_set(v_reuseFailAlloc_5358_, 25, v_S_5339_);
lean_ctor_set(v_reuseFailAlloc_5358_, 26, v_A_5340_);
lean_ctor_set(v_reuseFailAlloc_5358_, 27, v_n_5341_);
lean_ctor_set(v_reuseFailAlloc_5358_, 28, v_N_5342_);
lean_ctor_set(v_reuseFailAlloc_5358_, 29, v_V_5343_);
lean_ctor_set(v_reuseFailAlloc_5358_, 30, v_z_5344_);
lean_ctor_set(v_reuseFailAlloc_5358_, 31, v_zabbrev_5345_);
lean_ctor_set(v_reuseFailAlloc_5358_, 32, v_v_5346_);
lean_ctor_set(v_reuseFailAlloc_5358_, 33, v_O_5347_);
lean_ctor_set(v_reuseFailAlloc_5358_, 34, v_X_5348_);
lean_ctor_set(v_reuseFailAlloc_5358_, 35, v_x_5349_);
lean_ctor_set(v_reuseFailAlloc_5358_, 36, v_Z_5350_);
v___x_5357_ = v_reuseFailAlloc_5358_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
return v___x_5357_;
}
}
}
}
}
case 14:
{
lean_object* v___x_5365_; uint8_t v_isShared_5366_; uint8_t v_isSharedCheck_5414_; 
v_isSharedCheck_5414_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_5414_ == 0)
{
lean_object* v_unused_5415_; 
v_unused_5415_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_5415_);
v___x_5365_ = v_modifier_4648_;
v_isShared_5366_ = v_isSharedCheck_5414_;
goto v_resetjp_5364_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_5365_ = lean_box(0);
v_isShared_5366_ = v_isSharedCheck_5414_;
goto v_resetjp_5364_;
}
v_resetjp_5364_:
{
lean_object* v_G_5367_; lean_object* v_y_5368_; lean_object* v_u_5369_; lean_object* v_Y_5370_; lean_object* v_D_5371_; lean_object* v_M_5372_; lean_object* v_L_5373_; lean_object* v_d_5374_; lean_object* v_Q_5375_; lean_object* v_q_5376_; lean_object* v_w_5377_; lean_object* v_W_5378_; lean_object* v_E_5379_; lean_object* v_e_5380_; lean_object* v_F_5381_; lean_object* v_a_5382_; lean_object* v_b_5383_; lean_object* v_B_5384_; lean_object* v_h_5385_; lean_object* v_K_5386_; lean_object* v_k_5387_; lean_object* v_H_5388_; lean_object* v_m_5389_; lean_object* v_s_5390_; lean_object* v_S_5391_; lean_object* v_A_5392_; lean_object* v_n_5393_; lean_object* v_N_5394_; lean_object* v_V_5395_; lean_object* v_z_5396_; lean_object* v_zabbrev_5397_; lean_object* v_v_5398_; lean_object* v_O_5399_; lean_object* v_X_5400_; lean_object* v_x_5401_; lean_object* v_Z_5402_; lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5412_; 
v_G_5367_ = lean_ctor_get(v_date_4647_, 0);
v_y_5368_ = lean_ctor_get(v_date_4647_, 1);
v_u_5369_ = lean_ctor_get(v_date_4647_, 2);
v_Y_5370_ = lean_ctor_get(v_date_4647_, 3);
v_D_5371_ = lean_ctor_get(v_date_4647_, 4);
v_M_5372_ = lean_ctor_get(v_date_4647_, 5);
v_L_5373_ = lean_ctor_get(v_date_4647_, 6);
v_d_5374_ = lean_ctor_get(v_date_4647_, 7);
v_Q_5375_ = lean_ctor_get(v_date_4647_, 8);
v_q_5376_ = lean_ctor_get(v_date_4647_, 9);
v_w_5377_ = lean_ctor_get(v_date_4647_, 10);
v_W_5378_ = lean_ctor_get(v_date_4647_, 11);
v_E_5379_ = lean_ctor_get(v_date_4647_, 12);
v_e_5380_ = lean_ctor_get(v_date_4647_, 13);
v_F_5381_ = lean_ctor_get(v_date_4647_, 15);
v_a_5382_ = lean_ctor_get(v_date_4647_, 16);
v_b_5383_ = lean_ctor_get(v_date_4647_, 17);
v_B_5384_ = lean_ctor_get(v_date_4647_, 18);
v_h_5385_ = lean_ctor_get(v_date_4647_, 19);
v_K_5386_ = lean_ctor_get(v_date_4647_, 20);
v_k_5387_ = lean_ctor_get(v_date_4647_, 21);
v_H_5388_ = lean_ctor_get(v_date_4647_, 22);
v_m_5389_ = lean_ctor_get(v_date_4647_, 23);
v_s_5390_ = lean_ctor_get(v_date_4647_, 24);
v_S_5391_ = lean_ctor_get(v_date_4647_, 25);
v_A_5392_ = lean_ctor_get(v_date_4647_, 26);
v_n_5393_ = lean_ctor_get(v_date_4647_, 27);
v_N_5394_ = lean_ctor_get(v_date_4647_, 28);
v_V_5395_ = lean_ctor_get(v_date_4647_, 29);
v_z_5396_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_5397_ = lean_ctor_get(v_date_4647_, 31);
v_v_5398_ = lean_ctor_get(v_date_4647_, 32);
v_O_5399_ = lean_ctor_get(v_date_4647_, 33);
v_X_5400_ = lean_ctor_get(v_date_4647_, 34);
v_x_5401_ = lean_ctor_get(v_date_4647_, 35);
v_Z_5402_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5412_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5412_ == 0)
{
lean_object* v_unused_5413_; 
v_unused_5413_ = lean_ctor_get(v_date_4647_, 14);
lean_dec(v_unused_5413_);
v___x_5404_ = v_date_4647_;
v_isShared_5405_ = v_isSharedCheck_5412_;
goto v_resetjp_5403_;
}
else
{
lean_inc(v_Z_5402_);
lean_inc(v_x_5401_);
lean_inc(v_X_5400_);
lean_inc(v_O_5399_);
lean_inc(v_v_5398_);
lean_inc(v_zabbrev_5397_);
lean_inc(v_z_5396_);
lean_inc(v_V_5395_);
lean_inc(v_N_5394_);
lean_inc(v_n_5393_);
lean_inc(v_A_5392_);
lean_inc(v_S_5391_);
lean_inc(v_s_5390_);
lean_inc(v_m_5389_);
lean_inc(v_H_5388_);
lean_inc(v_k_5387_);
lean_inc(v_K_5386_);
lean_inc(v_h_5385_);
lean_inc(v_B_5384_);
lean_inc(v_b_5383_);
lean_inc(v_a_5382_);
lean_inc(v_F_5381_);
lean_inc(v_e_5380_);
lean_inc(v_E_5379_);
lean_inc(v_W_5378_);
lean_inc(v_w_5377_);
lean_inc(v_q_5376_);
lean_inc(v_Q_5375_);
lean_inc(v_d_5374_);
lean_inc(v_L_5373_);
lean_inc(v_M_5372_);
lean_inc(v_D_5371_);
lean_inc(v_Y_5370_);
lean_inc(v_u_5369_);
lean_inc(v_y_5368_);
lean_inc(v_G_5367_);
lean_dec(v_date_4647_);
v___x_5404_ = lean_box(0);
v_isShared_5405_ = v_isSharedCheck_5412_;
goto v_resetjp_5403_;
}
v_resetjp_5403_:
{
lean_object* v___x_5407_; 
if (v_isShared_5366_ == 0)
{
lean_ctor_set_tag(v___x_5365_, 1);
lean_ctor_set(v___x_5365_, 0, v_data_4649_);
v___x_5407_ = v___x_5365_;
goto v_reusejp_5406_;
}
else
{
lean_object* v_reuseFailAlloc_5411_; 
v_reuseFailAlloc_5411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5411_, 0, v_data_4649_);
v___x_5407_ = v_reuseFailAlloc_5411_;
goto v_reusejp_5406_;
}
v_reusejp_5406_:
{
lean_object* v___x_5409_; 
if (v_isShared_5405_ == 0)
{
lean_ctor_set(v___x_5404_, 14, v___x_5407_);
v___x_5409_ = v___x_5404_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5410_; 
v_reuseFailAlloc_5410_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5410_, 0, v_G_5367_);
lean_ctor_set(v_reuseFailAlloc_5410_, 1, v_y_5368_);
lean_ctor_set(v_reuseFailAlloc_5410_, 2, v_u_5369_);
lean_ctor_set(v_reuseFailAlloc_5410_, 3, v_Y_5370_);
lean_ctor_set(v_reuseFailAlloc_5410_, 4, v_D_5371_);
lean_ctor_set(v_reuseFailAlloc_5410_, 5, v_M_5372_);
lean_ctor_set(v_reuseFailAlloc_5410_, 6, v_L_5373_);
lean_ctor_set(v_reuseFailAlloc_5410_, 7, v_d_5374_);
lean_ctor_set(v_reuseFailAlloc_5410_, 8, v_Q_5375_);
lean_ctor_set(v_reuseFailAlloc_5410_, 9, v_q_5376_);
lean_ctor_set(v_reuseFailAlloc_5410_, 10, v_w_5377_);
lean_ctor_set(v_reuseFailAlloc_5410_, 11, v_W_5378_);
lean_ctor_set(v_reuseFailAlloc_5410_, 12, v_E_5379_);
lean_ctor_set(v_reuseFailAlloc_5410_, 13, v_e_5380_);
lean_ctor_set(v_reuseFailAlloc_5410_, 14, v___x_5407_);
lean_ctor_set(v_reuseFailAlloc_5410_, 15, v_F_5381_);
lean_ctor_set(v_reuseFailAlloc_5410_, 16, v_a_5382_);
lean_ctor_set(v_reuseFailAlloc_5410_, 17, v_b_5383_);
lean_ctor_set(v_reuseFailAlloc_5410_, 18, v_B_5384_);
lean_ctor_set(v_reuseFailAlloc_5410_, 19, v_h_5385_);
lean_ctor_set(v_reuseFailAlloc_5410_, 20, v_K_5386_);
lean_ctor_set(v_reuseFailAlloc_5410_, 21, v_k_5387_);
lean_ctor_set(v_reuseFailAlloc_5410_, 22, v_H_5388_);
lean_ctor_set(v_reuseFailAlloc_5410_, 23, v_m_5389_);
lean_ctor_set(v_reuseFailAlloc_5410_, 24, v_s_5390_);
lean_ctor_set(v_reuseFailAlloc_5410_, 25, v_S_5391_);
lean_ctor_set(v_reuseFailAlloc_5410_, 26, v_A_5392_);
lean_ctor_set(v_reuseFailAlloc_5410_, 27, v_n_5393_);
lean_ctor_set(v_reuseFailAlloc_5410_, 28, v_N_5394_);
lean_ctor_set(v_reuseFailAlloc_5410_, 29, v_V_5395_);
lean_ctor_set(v_reuseFailAlloc_5410_, 30, v_z_5396_);
lean_ctor_set(v_reuseFailAlloc_5410_, 31, v_zabbrev_5397_);
lean_ctor_set(v_reuseFailAlloc_5410_, 32, v_v_5398_);
lean_ctor_set(v_reuseFailAlloc_5410_, 33, v_O_5399_);
lean_ctor_set(v_reuseFailAlloc_5410_, 34, v_X_5400_);
lean_ctor_set(v_reuseFailAlloc_5410_, 35, v_x_5401_);
lean_ctor_set(v_reuseFailAlloc_5410_, 36, v_Z_5402_);
v___x_5409_ = v_reuseFailAlloc_5410_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
return v___x_5409_;
}
}
}
}
}
case 15:
{
lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5466_; 
v_isSharedCheck_5466_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_5466_ == 0)
{
lean_object* v_unused_5467_; 
v_unused_5467_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_5467_);
v___x_5417_ = v_modifier_4648_;
v_isShared_5418_ = v_isSharedCheck_5466_;
goto v_resetjp_5416_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5466_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
lean_object* v_G_5419_; lean_object* v_y_5420_; lean_object* v_u_5421_; lean_object* v_Y_5422_; lean_object* v_D_5423_; lean_object* v_M_5424_; lean_object* v_L_5425_; lean_object* v_d_5426_; lean_object* v_Q_5427_; lean_object* v_q_5428_; lean_object* v_w_5429_; lean_object* v_W_5430_; lean_object* v_E_5431_; lean_object* v_e_5432_; lean_object* v_c_5433_; lean_object* v_a_5434_; lean_object* v_b_5435_; lean_object* v_B_5436_; lean_object* v_h_5437_; lean_object* v_K_5438_; lean_object* v_k_5439_; lean_object* v_H_5440_; lean_object* v_m_5441_; lean_object* v_s_5442_; lean_object* v_S_5443_; lean_object* v_A_5444_; lean_object* v_n_5445_; lean_object* v_N_5446_; lean_object* v_V_5447_; lean_object* v_z_5448_; lean_object* v_zabbrev_5449_; lean_object* v_v_5450_; lean_object* v_O_5451_; lean_object* v_X_5452_; lean_object* v_x_5453_; lean_object* v_Z_5454_; lean_object* v___x_5456_; uint8_t v_isShared_5457_; uint8_t v_isSharedCheck_5464_; 
v_G_5419_ = lean_ctor_get(v_date_4647_, 0);
v_y_5420_ = lean_ctor_get(v_date_4647_, 1);
v_u_5421_ = lean_ctor_get(v_date_4647_, 2);
v_Y_5422_ = lean_ctor_get(v_date_4647_, 3);
v_D_5423_ = lean_ctor_get(v_date_4647_, 4);
v_M_5424_ = lean_ctor_get(v_date_4647_, 5);
v_L_5425_ = lean_ctor_get(v_date_4647_, 6);
v_d_5426_ = lean_ctor_get(v_date_4647_, 7);
v_Q_5427_ = lean_ctor_get(v_date_4647_, 8);
v_q_5428_ = lean_ctor_get(v_date_4647_, 9);
v_w_5429_ = lean_ctor_get(v_date_4647_, 10);
v_W_5430_ = lean_ctor_get(v_date_4647_, 11);
v_E_5431_ = lean_ctor_get(v_date_4647_, 12);
v_e_5432_ = lean_ctor_get(v_date_4647_, 13);
v_c_5433_ = lean_ctor_get(v_date_4647_, 14);
v_a_5434_ = lean_ctor_get(v_date_4647_, 16);
v_b_5435_ = lean_ctor_get(v_date_4647_, 17);
v_B_5436_ = lean_ctor_get(v_date_4647_, 18);
v_h_5437_ = lean_ctor_get(v_date_4647_, 19);
v_K_5438_ = lean_ctor_get(v_date_4647_, 20);
v_k_5439_ = lean_ctor_get(v_date_4647_, 21);
v_H_5440_ = lean_ctor_get(v_date_4647_, 22);
v_m_5441_ = lean_ctor_get(v_date_4647_, 23);
v_s_5442_ = lean_ctor_get(v_date_4647_, 24);
v_S_5443_ = lean_ctor_get(v_date_4647_, 25);
v_A_5444_ = lean_ctor_get(v_date_4647_, 26);
v_n_5445_ = lean_ctor_get(v_date_4647_, 27);
v_N_5446_ = lean_ctor_get(v_date_4647_, 28);
v_V_5447_ = lean_ctor_get(v_date_4647_, 29);
v_z_5448_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_5449_ = lean_ctor_get(v_date_4647_, 31);
v_v_5450_ = lean_ctor_get(v_date_4647_, 32);
v_O_5451_ = lean_ctor_get(v_date_4647_, 33);
v_X_5452_ = lean_ctor_get(v_date_4647_, 34);
v_x_5453_ = lean_ctor_get(v_date_4647_, 35);
v_Z_5454_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5464_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5464_ == 0)
{
lean_object* v_unused_5465_; 
v_unused_5465_ = lean_ctor_get(v_date_4647_, 15);
lean_dec(v_unused_5465_);
v___x_5456_ = v_date_4647_;
v_isShared_5457_ = v_isSharedCheck_5464_;
goto v_resetjp_5455_;
}
else
{
lean_inc(v_Z_5454_);
lean_inc(v_x_5453_);
lean_inc(v_X_5452_);
lean_inc(v_O_5451_);
lean_inc(v_v_5450_);
lean_inc(v_zabbrev_5449_);
lean_inc(v_z_5448_);
lean_inc(v_V_5447_);
lean_inc(v_N_5446_);
lean_inc(v_n_5445_);
lean_inc(v_A_5444_);
lean_inc(v_S_5443_);
lean_inc(v_s_5442_);
lean_inc(v_m_5441_);
lean_inc(v_H_5440_);
lean_inc(v_k_5439_);
lean_inc(v_K_5438_);
lean_inc(v_h_5437_);
lean_inc(v_B_5436_);
lean_inc(v_b_5435_);
lean_inc(v_a_5434_);
lean_inc(v_c_5433_);
lean_inc(v_e_5432_);
lean_inc(v_E_5431_);
lean_inc(v_W_5430_);
lean_inc(v_w_5429_);
lean_inc(v_q_5428_);
lean_inc(v_Q_5427_);
lean_inc(v_d_5426_);
lean_inc(v_L_5425_);
lean_inc(v_M_5424_);
lean_inc(v_D_5423_);
lean_inc(v_Y_5422_);
lean_inc(v_u_5421_);
lean_inc(v_y_5420_);
lean_inc(v_G_5419_);
lean_dec(v_date_4647_);
v___x_5456_ = lean_box(0);
v_isShared_5457_ = v_isSharedCheck_5464_;
goto v_resetjp_5455_;
}
v_resetjp_5455_:
{
lean_object* v___x_5459_; 
if (v_isShared_5418_ == 0)
{
lean_ctor_set_tag(v___x_5417_, 1);
lean_ctor_set(v___x_5417_, 0, v_data_4649_);
v___x_5459_ = v___x_5417_;
goto v_reusejp_5458_;
}
else
{
lean_object* v_reuseFailAlloc_5463_; 
v_reuseFailAlloc_5463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5463_, 0, v_data_4649_);
v___x_5459_ = v_reuseFailAlloc_5463_;
goto v_reusejp_5458_;
}
v_reusejp_5458_:
{
lean_object* v___x_5461_; 
if (v_isShared_5457_ == 0)
{
lean_ctor_set(v___x_5456_, 15, v___x_5459_);
v___x_5461_ = v___x_5456_;
goto v_reusejp_5460_;
}
else
{
lean_object* v_reuseFailAlloc_5462_; 
v_reuseFailAlloc_5462_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5462_, 0, v_G_5419_);
lean_ctor_set(v_reuseFailAlloc_5462_, 1, v_y_5420_);
lean_ctor_set(v_reuseFailAlloc_5462_, 2, v_u_5421_);
lean_ctor_set(v_reuseFailAlloc_5462_, 3, v_Y_5422_);
lean_ctor_set(v_reuseFailAlloc_5462_, 4, v_D_5423_);
lean_ctor_set(v_reuseFailAlloc_5462_, 5, v_M_5424_);
lean_ctor_set(v_reuseFailAlloc_5462_, 6, v_L_5425_);
lean_ctor_set(v_reuseFailAlloc_5462_, 7, v_d_5426_);
lean_ctor_set(v_reuseFailAlloc_5462_, 8, v_Q_5427_);
lean_ctor_set(v_reuseFailAlloc_5462_, 9, v_q_5428_);
lean_ctor_set(v_reuseFailAlloc_5462_, 10, v_w_5429_);
lean_ctor_set(v_reuseFailAlloc_5462_, 11, v_W_5430_);
lean_ctor_set(v_reuseFailAlloc_5462_, 12, v_E_5431_);
lean_ctor_set(v_reuseFailAlloc_5462_, 13, v_e_5432_);
lean_ctor_set(v_reuseFailAlloc_5462_, 14, v_c_5433_);
lean_ctor_set(v_reuseFailAlloc_5462_, 15, v___x_5459_);
lean_ctor_set(v_reuseFailAlloc_5462_, 16, v_a_5434_);
lean_ctor_set(v_reuseFailAlloc_5462_, 17, v_b_5435_);
lean_ctor_set(v_reuseFailAlloc_5462_, 18, v_B_5436_);
lean_ctor_set(v_reuseFailAlloc_5462_, 19, v_h_5437_);
lean_ctor_set(v_reuseFailAlloc_5462_, 20, v_K_5438_);
lean_ctor_set(v_reuseFailAlloc_5462_, 21, v_k_5439_);
lean_ctor_set(v_reuseFailAlloc_5462_, 22, v_H_5440_);
lean_ctor_set(v_reuseFailAlloc_5462_, 23, v_m_5441_);
lean_ctor_set(v_reuseFailAlloc_5462_, 24, v_s_5442_);
lean_ctor_set(v_reuseFailAlloc_5462_, 25, v_S_5443_);
lean_ctor_set(v_reuseFailAlloc_5462_, 26, v_A_5444_);
lean_ctor_set(v_reuseFailAlloc_5462_, 27, v_n_5445_);
lean_ctor_set(v_reuseFailAlloc_5462_, 28, v_N_5446_);
lean_ctor_set(v_reuseFailAlloc_5462_, 29, v_V_5447_);
lean_ctor_set(v_reuseFailAlloc_5462_, 30, v_z_5448_);
lean_ctor_set(v_reuseFailAlloc_5462_, 31, v_zabbrev_5449_);
lean_ctor_set(v_reuseFailAlloc_5462_, 32, v_v_5450_);
lean_ctor_set(v_reuseFailAlloc_5462_, 33, v_O_5451_);
lean_ctor_set(v_reuseFailAlloc_5462_, 34, v_X_5452_);
lean_ctor_set(v_reuseFailAlloc_5462_, 35, v_x_5453_);
lean_ctor_set(v_reuseFailAlloc_5462_, 36, v_Z_5454_);
v___x_5461_ = v_reuseFailAlloc_5462_;
goto v_reusejp_5460_;
}
v_reusejp_5460_:
{
return v___x_5461_;
}
}
}
}
}
case 16:
{
lean_object* v_G_5468_; lean_object* v_y_5469_; lean_object* v_u_5470_; lean_object* v_Y_5471_; lean_object* v_D_5472_; lean_object* v_M_5473_; lean_object* v_L_5474_; lean_object* v_d_5475_; lean_object* v_Q_5476_; lean_object* v_q_5477_; lean_object* v_w_5478_; lean_object* v_W_5479_; lean_object* v_E_5480_; lean_object* v_e_5481_; lean_object* v_c_5482_; lean_object* v_F_5483_; lean_object* v_b_5484_; lean_object* v_B_5485_; lean_object* v_h_5486_; lean_object* v_K_5487_; lean_object* v_k_5488_; lean_object* v_H_5489_; lean_object* v_m_5490_; lean_object* v_s_5491_; lean_object* v_S_5492_; lean_object* v_A_5493_; lean_object* v_n_5494_; lean_object* v_N_5495_; lean_object* v_V_5496_; lean_object* v_z_5497_; lean_object* v_zabbrev_5498_; lean_object* v_v_5499_; lean_object* v_O_5500_; lean_object* v_X_5501_; lean_object* v_x_5502_; lean_object* v_Z_5503_; lean_object* v___x_5505_; uint8_t v_isShared_5506_; uint8_t v_isSharedCheck_5511_; 
lean_dec_ref_known(v_modifier_4648_, 0);
v_G_5468_ = lean_ctor_get(v_date_4647_, 0);
v_y_5469_ = lean_ctor_get(v_date_4647_, 1);
v_u_5470_ = lean_ctor_get(v_date_4647_, 2);
v_Y_5471_ = lean_ctor_get(v_date_4647_, 3);
v_D_5472_ = lean_ctor_get(v_date_4647_, 4);
v_M_5473_ = lean_ctor_get(v_date_4647_, 5);
v_L_5474_ = lean_ctor_get(v_date_4647_, 6);
v_d_5475_ = lean_ctor_get(v_date_4647_, 7);
v_Q_5476_ = lean_ctor_get(v_date_4647_, 8);
v_q_5477_ = lean_ctor_get(v_date_4647_, 9);
v_w_5478_ = lean_ctor_get(v_date_4647_, 10);
v_W_5479_ = lean_ctor_get(v_date_4647_, 11);
v_E_5480_ = lean_ctor_get(v_date_4647_, 12);
v_e_5481_ = lean_ctor_get(v_date_4647_, 13);
v_c_5482_ = lean_ctor_get(v_date_4647_, 14);
v_F_5483_ = lean_ctor_get(v_date_4647_, 15);
v_b_5484_ = lean_ctor_get(v_date_4647_, 17);
v_B_5485_ = lean_ctor_get(v_date_4647_, 18);
v_h_5486_ = lean_ctor_get(v_date_4647_, 19);
v_K_5487_ = lean_ctor_get(v_date_4647_, 20);
v_k_5488_ = lean_ctor_get(v_date_4647_, 21);
v_H_5489_ = lean_ctor_get(v_date_4647_, 22);
v_m_5490_ = lean_ctor_get(v_date_4647_, 23);
v_s_5491_ = lean_ctor_get(v_date_4647_, 24);
v_S_5492_ = lean_ctor_get(v_date_4647_, 25);
v_A_5493_ = lean_ctor_get(v_date_4647_, 26);
v_n_5494_ = lean_ctor_get(v_date_4647_, 27);
v_N_5495_ = lean_ctor_get(v_date_4647_, 28);
v_V_5496_ = lean_ctor_get(v_date_4647_, 29);
v_z_5497_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_5498_ = lean_ctor_get(v_date_4647_, 31);
v_v_5499_ = lean_ctor_get(v_date_4647_, 32);
v_O_5500_ = lean_ctor_get(v_date_4647_, 33);
v_X_5501_ = lean_ctor_get(v_date_4647_, 34);
v_x_5502_ = lean_ctor_get(v_date_4647_, 35);
v_Z_5503_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5511_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5511_ == 0)
{
lean_object* v_unused_5512_; 
v_unused_5512_ = lean_ctor_get(v_date_4647_, 16);
lean_dec(v_unused_5512_);
v___x_5505_ = v_date_4647_;
v_isShared_5506_ = v_isSharedCheck_5511_;
goto v_resetjp_5504_;
}
else
{
lean_inc(v_Z_5503_);
lean_inc(v_x_5502_);
lean_inc(v_X_5501_);
lean_inc(v_O_5500_);
lean_inc(v_v_5499_);
lean_inc(v_zabbrev_5498_);
lean_inc(v_z_5497_);
lean_inc(v_V_5496_);
lean_inc(v_N_5495_);
lean_inc(v_n_5494_);
lean_inc(v_A_5493_);
lean_inc(v_S_5492_);
lean_inc(v_s_5491_);
lean_inc(v_m_5490_);
lean_inc(v_H_5489_);
lean_inc(v_k_5488_);
lean_inc(v_K_5487_);
lean_inc(v_h_5486_);
lean_inc(v_B_5485_);
lean_inc(v_b_5484_);
lean_inc(v_F_5483_);
lean_inc(v_c_5482_);
lean_inc(v_e_5481_);
lean_inc(v_E_5480_);
lean_inc(v_W_5479_);
lean_inc(v_w_5478_);
lean_inc(v_q_5477_);
lean_inc(v_Q_5476_);
lean_inc(v_d_5475_);
lean_inc(v_L_5474_);
lean_inc(v_M_5473_);
lean_inc(v_D_5472_);
lean_inc(v_Y_5471_);
lean_inc(v_u_5470_);
lean_inc(v_y_5469_);
lean_inc(v_G_5468_);
lean_dec(v_date_4647_);
v___x_5505_ = lean_box(0);
v_isShared_5506_ = v_isSharedCheck_5511_;
goto v_resetjp_5504_;
}
v_resetjp_5504_:
{
lean_object* v___x_5507_; lean_object* v___x_5509_; 
v___x_5507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5507_, 0, v_data_4649_);
if (v_isShared_5506_ == 0)
{
lean_ctor_set(v___x_5505_, 16, v___x_5507_);
v___x_5509_ = v___x_5505_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_G_5468_);
lean_ctor_set(v_reuseFailAlloc_5510_, 1, v_y_5469_);
lean_ctor_set(v_reuseFailAlloc_5510_, 2, v_u_5470_);
lean_ctor_set(v_reuseFailAlloc_5510_, 3, v_Y_5471_);
lean_ctor_set(v_reuseFailAlloc_5510_, 4, v_D_5472_);
lean_ctor_set(v_reuseFailAlloc_5510_, 5, v_M_5473_);
lean_ctor_set(v_reuseFailAlloc_5510_, 6, v_L_5474_);
lean_ctor_set(v_reuseFailAlloc_5510_, 7, v_d_5475_);
lean_ctor_set(v_reuseFailAlloc_5510_, 8, v_Q_5476_);
lean_ctor_set(v_reuseFailAlloc_5510_, 9, v_q_5477_);
lean_ctor_set(v_reuseFailAlloc_5510_, 10, v_w_5478_);
lean_ctor_set(v_reuseFailAlloc_5510_, 11, v_W_5479_);
lean_ctor_set(v_reuseFailAlloc_5510_, 12, v_E_5480_);
lean_ctor_set(v_reuseFailAlloc_5510_, 13, v_e_5481_);
lean_ctor_set(v_reuseFailAlloc_5510_, 14, v_c_5482_);
lean_ctor_set(v_reuseFailAlloc_5510_, 15, v_F_5483_);
lean_ctor_set(v_reuseFailAlloc_5510_, 16, v___x_5507_);
lean_ctor_set(v_reuseFailAlloc_5510_, 17, v_b_5484_);
lean_ctor_set(v_reuseFailAlloc_5510_, 18, v_B_5485_);
lean_ctor_set(v_reuseFailAlloc_5510_, 19, v_h_5486_);
lean_ctor_set(v_reuseFailAlloc_5510_, 20, v_K_5487_);
lean_ctor_set(v_reuseFailAlloc_5510_, 21, v_k_5488_);
lean_ctor_set(v_reuseFailAlloc_5510_, 22, v_H_5489_);
lean_ctor_set(v_reuseFailAlloc_5510_, 23, v_m_5490_);
lean_ctor_set(v_reuseFailAlloc_5510_, 24, v_s_5491_);
lean_ctor_set(v_reuseFailAlloc_5510_, 25, v_S_5492_);
lean_ctor_set(v_reuseFailAlloc_5510_, 26, v_A_5493_);
lean_ctor_set(v_reuseFailAlloc_5510_, 27, v_n_5494_);
lean_ctor_set(v_reuseFailAlloc_5510_, 28, v_N_5495_);
lean_ctor_set(v_reuseFailAlloc_5510_, 29, v_V_5496_);
lean_ctor_set(v_reuseFailAlloc_5510_, 30, v_z_5497_);
lean_ctor_set(v_reuseFailAlloc_5510_, 31, v_zabbrev_5498_);
lean_ctor_set(v_reuseFailAlloc_5510_, 32, v_v_5499_);
lean_ctor_set(v_reuseFailAlloc_5510_, 33, v_O_5500_);
lean_ctor_set(v_reuseFailAlloc_5510_, 34, v_X_5501_);
lean_ctor_set(v_reuseFailAlloc_5510_, 35, v_x_5502_);
lean_ctor_set(v_reuseFailAlloc_5510_, 36, v_Z_5503_);
v___x_5509_ = v_reuseFailAlloc_5510_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
return v___x_5509_;
}
}
}
case 17:
{
lean_object* v_G_5513_; lean_object* v_y_5514_; lean_object* v_u_5515_; lean_object* v_Y_5516_; lean_object* v_D_5517_; lean_object* v_M_5518_; lean_object* v_L_5519_; lean_object* v_d_5520_; lean_object* v_Q_5521_; lean_object* v_q_5522_; lean_object* v_w_5523_; lean_object* v_W_5524_; lean_object* v_E_5525_; lean_object* v_e_5526_; lean_object* v_c_5527_; lean_object* v_F_5528_; lean_object* v_a_5529_; lean_object* v_B_5530_; lean_object* v_h_5531_; lean_object* v_K_5532_; lean_object* v_k_5533_; lean_object* v_H_5534_; lean_object* v_m_5535_; lean_object* v_s_5536_; lean_object* v_S_5537_; lean_object* v_A_5538_; lean_object* v_n_5539_; lean_object* v_N_5540_; lean_object* v_V_5541_; lean_object* v_z_5542_; lean_object* v_zabbrev_5543_; lean_object* v_v_5544_; lean_object* v_O_5545_; lean_object* v_X_5546_; lean_object* v_x_5547_; lean_object* v_Z_5548_; lean_object* v___x_5550_; uint8_t v_isShared_5551_; uint8_t v_isSharedCheck_5556_; 
lean_dec_ref_known(v_modifier_4648_, 0);
v_G_5513_ = lean_ctor_get(v_date_4647_, 0);
v_y_5514_ = lean_ctor_get(v_date_4647_, 1);
v_u_5515_ = lean_ctor_get(v_date_4647_, 2);
v_Y_5516_ = lean_ctor_get(v_date_4647_, 3);
v_D_5517_ = lean_ctor_get(v_date_4647_, 4);
v_M_5518_ = lean_ctor_get(v_date_4647_, 5);
v_L_5519_ = lean_ctor_get(v_date_4647_, 6);
v_d_5520_ = lean_ctor_get(v_date_4647_, 7);
v_Q_5521_ = lean_ctor_get(v_date_4647_, 8);
v_q_5522_ = lean_ctor_get(v_date_4647_, 9);
v_w_5523_ = lean_ctor_get(v_date_4647_, 10);
v_W_5524_ = lean_ctor_get(v_date_4647_, 11);
v_E_5525_ = lean_ctor_get(v_date_4647_, 12);
v_e_5526_ = lean_ctor_get(v_date_4647_, 13);
v_c_5527_ = lean_ctor_get(v_date_4647_, 14);
v_F_5528_ = lean_ctor_get(v_date_4647_, 15);
v_a_5529_ = lean_ctor_get(v_date_4647_, 16);
v_B_5530_ = lean_ctor_get(v_date_4647_, 18);
v_h_5531_ = lean_ctor_get(v_date_4647_, 19);
v_K_5532_ = lean_ctor_get(v_date_4647_, 20);
v_k_5533_ = lean_ctor_get(v_date_4647_, 21);
v_H_5534_ = lean_ctor_get(v_date_4647_, 22);
v_m_5535_ = lean_ctor_get(v_date_4647_, 23);
v_s_5536_ = lean_ctor_get(v_date_4647_, 24);
v_S_5537_ = lean_ctor_get(v_date_4647_, 25);
v_A_5538_ = lean_ctor_get(v_date_4647_, 26);
v_n_5539_ = lean_ctor_get(v_date_4647_, 27);
v_N_5540_ = lean_ctor_get(v_date_4647_, 28);
v_V_5541_ = lean_ctor_get(v_date_4647_, 29);
v_z_5542_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_5543_ = lean_ctor_get(v_date_4647_, 31);
v_v_5544_ = lean_ctor_get(v_date_4647_, 32);
v_O_5545_ = lean_ctor_get(v_date_4647_, 33);
v_X_5546_ = lean_ctor_get(v_date_4647_, 34);
v_x_5547_ = lean_ctor_get(v_date_4647_, 35);
v_Z_5548_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5556_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5556_ == 0)
{
lean_object* v_unused_5557_; 
v_unused_5557_ = lean_ctor_get(v_date_4647_, 17);
lean_dec(v_unused_5557_);
v___x_5550_ = v_date_4647_;
v_isShared_5551_ = v_isSharedCheck_5556_;
goto v_resetjp_5549_;
}
else
{
lean_inc(v_Z_5548_);
lean_inc(v_x_5547_);
lean_inc(v_X_5546_);
lean_inc(v_O_5545_);
lean_inc(v_v_5544_);
lean_inc(v_zabbrev_5543_);
lean_inc(v_z_5542_);
lean_inc(v_V_5541_);
lean_inc(v_N_5540_);
lean_inc(v_n_5539_);
lean_inc(v_A_5538_);
lean_inc(v_S_5537_);
lean_inc(v_s_5536_);
lean_inc(v_m_5535_);
lean_inc(v_H_5534_);
lean_inc(v_k_5533_);
lean_inc(v_K_5532_);
lean_inc(v_h_5531_);
lean_inc(v_B_5530_);
lean_inc(v_a_5529_);
lean_inc(v_F_5528_);
lean_inc(v_c_5527_);
lean_inc(v_e_5526_);
lean_inc(v_E_5525_);
lean_inc(v_W_5524_);
lean_inc(v_w_5523_);
lean_inc(v_q_5522_);
lean_inc(v_Q_5521_);
lean_inc(v_d_5520_);
lean_inc(v_L_5519_);
lean_inc(v_M_5518_);
lean_inc(v_D_5517_);
lean_inc(v_Y_5516_);
lean_inc(v_u_5515_);
lean_inc(v_y_5514_);
lean_inc(v_G_5513_);
lean_dec(v_date_4647_);
v___x_5550_ = lean_box(0);
v_isShared_5551_ = v_isSharedCheck_5556_;
goto v_resetjp_5549_;
}
v_resetjp_5549_:
{
lean_object* v___x_5552_; lean_object* v___x_5554_; 
v___x_5552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5552_, 0, v_data_4649_);
if (v_isShared_5551_ == 0)
{
lean_ctor_set(v___x_5550_, 17, v___x_5552_);
v___x_5554_ = v___x_5550_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5555_; 
v_reuseFailAlloc_5555_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5555_, 0, v_G_5513_);
lean_ctor_set(v_reuseFailAlloc_5555_, 1, v_y_5514_);
lean_ctor_set(v_reuseFailAlloc_5555_, 2, v_u_5515_);
lean_ctor_set(v_reuseFailAlloc_5555_, 3, v_Y_5516_);
lean_ctor_set(v_reuseFailAlloc_5555_, 4, v_D_5517_);
lean_ctor_set(v_reuseFailAlloc_5555_, 5, v_M_5518_);
lean_ctor_set(v_reuseFailAlloc_5555_, 6, v_L_5519_);
lean_ctor_set(v_reuseFailAlloc_5555_, 7, v_d_5520_);
lean_ctor_set(v_reuseFailAlloc_5555_, 8, v_Q_5521_);
lean_ctor_set(v_reuseFailAlloc_5555_, 9, v_q_5522_);
lean_ctor_set(v_reuseFailAlloc_5555_, 10, v_w_5523_);
lean_ctor_set(v_reuseFailAlloc_5555_, 11, v_W_5524_);
lean_ctor_set(v_reuseFailAlloc_5555_, 12, v_E_5525_);
lean_ctor_set(v_reuseFailAlloc_5555_, 13, v_e_5526_);
lean_ctor_set(v_reuseFailAlloc_5555_, 14, v_c_5527_);
lean_ctor_set(v_reuseFailAlloc_5555_, 15, v_F_5528_);
lean_ctor_set(v_reuseFailAlloc_5555_, 16, v_a_5529_);
lean_ctor_set(v_reuseFailAlloc_5555_, 17, v___x_5552_);
lean_ctor_set(v_reuseFailAlloc_5555_, 18, v_B_5530_);
lean_ctor_set(v_reuseFailAlloc_5555_, 19, v_h_5531_);
lean_ctor_set(v_reuseFailAlloc_5555_, 20, v_K_5532_);
lean_ctor_set(v_reuseFailAlloc_5555_, 21, v_k_5533_);
lean_ctor_set(v_reuseFailAlloc_5555_, 22, v_H_5534_);
lean_ctor_set(v_reuseFailAlloc_5555_, 23, v_m_5535_);
lean_ctor_set(v_reuseFailAlloc_5555_, 24, v_s_5536_);
lean_ctor_set(v_reuseFailAlloc_5555_, 25, v_S_5537_);
lean_ctor_set(v_reuseFailAlloc_5555_, 26, v_A_5538_);
lean_ctor_set(v_reuseFailAlloc_5555_, 27, v_n_5539_);
lean_ctor_set(v_reuseFailAlloc_5555_, 28, v_N_5540_);
lean_ctor_set(v_reuseFailAlloc_5555_, 29, v_V_5541_);
lean_ctor_set(v_reuseFailAlloc_5555_, 30, v_z_5542_);
lean_ctor_set(v_reuseFailAlloc_5555_, 31, v_zabbrev_5543_);
lean_ctor_set(v_reuseFailAlloc_5555_, 32, v_v_5544_);
lean_ctor_set(v_reuseFailAlloc_5555_, 33, v_O_5545_);
lean_ctor_set(v_reuseFailAlloc_5555_, 34, v_X_5546_);
lean_ctor_set(v_reuseFailAlloc_5555_, 35, v_x_5547_);
lean_ctor_set(v_reuseFailAlloc_5555_, 36, v_Z_5548_);
v___x_5554_ = v_reuseFailAlloc_5555_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
return v___x_5554_;
}
}
}
case 18:
{
lean_object* v_G_5558_; lean_object* v_y_5559_; lean_object* v_u_5560_; lean_object* v_Y_5561_; lean_object* v_D_5562_; lean_object* v_M_5563_; lean_object* v_L_5564_; lean_object* v_d_5565_; lean_object* v_Q_5566_; lean_object* v_q_5567_; lean_object* v_w_5568_; lean_object* v_W_5569_; lean_object* v_E_5570_; lean_object* v_e_5571_; lean_object* v_c_5572_; lean_object* v_F_5573_; lean_object* v_a_5574_; lean_object* v_b_5575_; lean_object* v_h_5576_; lean_object* v_K_5577_; lean_object* v_k_5578_; lean_object* v_H_5579_; lean_object* v_m_5580_; lean_object* v_s_5581_; lean_object* v_S_5582_; lean_object* v_A_5583_; lean_object* v_n_5584_; lean_object* v_N_5585_; lean_object* v_V_5586_; lean_object* v_z_5587_; lean_object* v_zabbrev_5588_; lean_object* v_v_5589_; lean_object* v_O_5590_; lean_object* v_X_5591_; lean_object* v_x_5592_; lean_object* v_Z_5593_; lean_object* v___x_5595_; uint8_t v_isShared_5596_; uint8_t v_isSharedCheck_5601_; 
lean_dec_ref_known(v_modifier_4648_, 0);
v_G_5558_ = lean_ctor_get(v_date_4647_, 0);
v_y_5559_ = lean_ctor_get(v_date_4647_, 1);
v_u_5560_ = lean_ctor_get(v_date_4647_, 2);
v_Y_5561_ = lean_ctor_get(v_date_4647_, 3);
v_D_5562_ = lean_ctor_get(v_date_4647_, 4);
v_M_5563_ = lean_ctor_get(v_date_4647_, 5);
v_L_5564_ = lean_ctor_get(v_date_4647_, 6);
v_d_5565_ = lean_ctor_get(v_date_4647_, 7);
v_Q_5566_ = lean_ctor_get(v_date_4647_, 8);
v_q_5567_ = lean_ctor_get(v_date_4647_, 9);
v_w_5568_ = lean_ctor_get(v_date_4647_, 10);
v_W_5569_ = lean_ctor_get(v_date_4647_, 11);
v_E_5570_ = lean_ctor_get(v_date_4647_, 12);
v_e_5571_ = lean_ctor_get(v_date_4647_, 13);
v_c_5572_ = lean_ctor_get(v_date_4647_, 14);
v_F_5573_ = lean_ctor_get(v_date_4647_, 15);
v_a_5574_ = lean_ctor_get(v_date_4647_, 16);
v_b_5575_ = lean_ctor_get(v_date_4647_, 17);
v_h_5576_ = lean_ctor_get(v_date_4647_, 19);
v_K_5577_ = lean_ctor_get(v_date_4647_, 20);
v_k_5578_ = lean_ctor_get(v_date_4647_, 21);
v_H_5579_ = lean_ctor_get(v_date_4647_, 22);
v_m_5580_ = lean_ctor_get(v_date_4647_, 23);
v_s_5581_ = lean_ctor_get(v_date_4647_, 24);
v_S_5582_ = lean_ctor_get(v_date_4647_, 25);
v_A_5583_ = lean_ctor_get(v_date_4647_, 26);
v_n_5584_ = lean_ctor_get(v_date_4647_, 27);
v_N_5585_ = lean_ctor_get(v_date_4647_, 28);
v_V_5586_ = lean_ctor_get(v_date_4647_, 29);
v_z_5587_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_5588_ = lean_ctor_get(v_date_4647_, 31);
v_v_5589_ = lean_ctor_get(v_date_4647_, 32);
v_O_5590_ = lean_ctor_get(v_date_4647_, 33);
v_X_5591_ = lean_ctor_get(v_date_4647_, 34);
v_x_5592_ = lean_ctor_get(v_date_4647_, 35);
v_Z_5593_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5601_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5601_ == 0)
{
lean_object* v_unused_5602_; 
v_unused_5602_ = lean_ctor_get(v_date_4647_, 18);
lean_dec(v_unused_5602_);
v___x_5595_ = v_date_4647_;
v_isShared_5596_ = v_isSharedCheck_5601_;
goto v_resetjp_5594_;
}
else
{
lean_inc(v_Z_5593_);
lean_inc(v_x_5592_);
lean_inc(v_X_5591_);
lean_inc(v_O_5590_);
lean_inc(v_v_5589_);
lean_inc(v_zabbrev_5588_);
lean_inc(v_z_5587_);
lean_inc(v_V_5586_);
lean_inc(v_N_5585_);
lean_inc(v_n_5584_);
lean_inc(v_A_5583_);
lean_inc(v_S_5582_);
lean_inc(v_s_5581_);
lean_inc(v_m_5580_);
lean_inc(v_H_5579_);
lean_inc(v_k_5578_);
lean_inc(v_K_5577_);
lean_inc(v_h_5576_);
lean_inc(v_b_5575_);
lean_inc(v_a_5574_);
lean_inc(v_F_5573_);
lean_inc(v_c_5572_);
lean_inc(v_e_5571_);
lean_inc(v_E_5570_);
lean_inc(v_W_5569_);
lean_inc(v_w_5568_);
lean_inc(v_q_5567_);
lean_inc(v_Q_5566_);
lean_inc(v_d_5565_);
lean_inc(v_L_5564_);
lean_inc(v_M_5563_);
lean_inc(v_D_5562_);
lean_inc(v_Y_5561_);
lean_inc(v_u_5560_);
lean_inc(v_y_5559_);
lean_inc(v_G_5558_);
lean_dec(v_date_4647_);
v___x_5595_ = lean_box(0);
v_isShared_5596_ = v_isSharedCheck_5601_;
goto v_resetjp_5594_;
}
v_resetjp_5594_:
{
lean_object* v___x_5597_; lean_object* v___x_5599_; 
v___x_5597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5597_, 0, v_data_4649_);
if (v_isShared_5596_ == 0)
{
lean_ctor_set(v___x_5595_, 18, v___x_5597_);
v___x_5599_ = v___x_5595_;
goto v_reusejp_5598_;
}
else
{
lean_object* v_reuseFailAlloc_5600_; 
v_reuseFailAlloc_5600_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5600_, 0, v_G_5558_);
lean_ctor_set(v_reuseFailAlloc_5600_, 1, v_y_5559_);
lean_ctor_set(v_reuseFailAlloc_5600_, 2, v_u_5560_);
lean_ctor_set(v_reuseFailAlloc_5600_, 3, v_Y_5561_);
lean_ctor_set(v_reuseFailAlloc_5600_, 4, v_D_5562_);
lean_ctor_set(v_reuseFailAlloc_5600_, 5, v_M_5563_);
lean_ctor_set(v_reuseFailAlloc_5600_, 6, v_L_5564_);
lean_ctor_set(v_reuseFailAlloc_5600_, 7, v_d_5565_);
lean_ctor_set(v_reuseFailAlloc_5600_, 8, v_Q_5566_);
lean_ctor_set(v_reuseFailAlloc_5600_, 9, v_q_5567_);
lean_ctor_set(v_reuseFailAlloc_5600_, 10, v_w_5568_);
lean_ctor_set(v_reuseFailAlloc_5600_, 11, v_W_5569_);
lean_ctor_set(v_reuseFailAlloc_5600_, 12, v_E_5570_);
lean_ctor_set(v_reuseFailAlloc_5600_, 13, v_e_5571_);
lean_ctor_set(v_reuseFailAlloc_5600_, 14, v_c_5572_);
lean_ctor_set(v_reuseFailAlloc_5600_, 15, v_F_5573_);
lean_ctor_set(v_reuseFailAlloc_5600_, 16, v_a_5574_);
lean_ctor_set(v_reuseFailAlloc_5600_, 17, v_b_5575_);
lean_ctor_set(v_reuseFailAlloc_5600_, 18, v___x_5597_);
lean_ctor_set(v_reuseFailAlloc_5600_, 19, v_h_5576_);
lean_ctor_set(v_reuseFailAlloc_5600_, 20, v_K_5577_);
lean_ctor_set(v_reuseFailAlloc_5600_, 21, v_k_5578_);
lean_ctor_set(v_reuseFailAlloc_5600_, 22, v_H_5579_);
lean_ctor_set(v_reuseFailAlloc_5600_, 23, v_m_5580_);
lean_ctor_set(v_reuseFailAlloc_5600_, 24, v_s_5581_);
lean_ctor_set(v_reuseFailAlloc_5600_, 25, v_S_5582_);
lean_ctor_set(v_reuseFailAlloc_5600_, 26, v_A_5583_);
lean_ctor_set(v_reuseFailAlloc_5600_, 27, v_n_5584_);
lean_ctor_set(v_reuseFailAlloc_5600_, 28, v_N_5585_);
lean_ctor_set(v_reuseFailAlloc_5600_, 29, v_V_5586_);
lean_ctor_set(v_reuseFailAlloc_5600_, 30, v_z_5587_);
lean_ctor_set(v_reuseFailAlloc_5600_, 31, v_zabbrev_5588_);
lean_ctor_set(v_reuseFailAlloc_5600_, 32, v_v_5589_);
lean_ctor_set(v_reuseFailAlloc_5600_, 33, v_O_5590_);
lean_ctor_set(v_reuseFailAlloc_5600_, 34, v_X_5591_);
lean_ctor_set(v_reuseFailAlloc_5600_, 35, v_x_5592_);
lean_ctor_set(v_reuseFailAlloc_5600_, 36, v_Z_5593_);
v___x_5599_ = v_reuseFailAlloc_5600_;
goto v_reusejp_5598_;
}
v_reusejp_5598_:
{
return v___x_5599_;
}
}
}
case 19:
{
lean_object* v___x_5604_; uint8_t v_isShared_5605_; uint8_t v_isSharedCheck_5653_; 
v_isSharedCheck_5653_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_5653_ == 0)
{
lean_object* v_unused_5654_; 
v_unused_5654_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_5654_);
v___x_5604_ = v_modifier_4648_;
v_isShared_5605_ = v_isSharedCheck_5653_;
goto v_resetjp_5603_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_5604_ = lean_box(0);
v_isShared_5605_ = v_isSharedCheck_5653_;
goto v_resetjp_5603_;
}
v_resetjp_5603_:
{
lean_object* v_G_5606_; lean_object* v_y_5607_; lean_object* v_u_5608_; lean_object* v_Y_5609_; lean_object* v_D_5610_; lean_object* v_M_5611_; lean_object* v_L_5612_; lean_object* v_d_5613_; lean_object* v_Q_5614_; lean_object* v_q_5615_; lean_object* v_w_5616_; lean_object* v_W_5617_; lean_object* v_E_5618_; lean_object* v_e_5619_; lean_object* v_c_5620_; lean_object* v_F_5621_; lean_object* v_a_5622_; lean_object* v_b_5623_; lean_object* v_B_5624_; lean_object* v_K_5625_; lean_object* v_k_5626_; lean_object* v_H_5627_; lean_object* v_m_5628_; lean_object* v_s_5629_; lean_object* v_S_5630_; lean_object* v_A_5631_; lean_object* v_n_5632_; lean_object* v_N_5633_; lean_object* v_V_5634_; lean_object* v_z_5635_; lean_object* v_zabbrev_5636_; lean_object* v_v_5637_; lean_object* v_O_5638_; lean_object* v_X_5639_; lean_object* v_x_5640_; lean_object* v_Z_5641_; lean_object* v___x_5643_; uint8_t v_isShared_5644_; uint8_t v_isSharedCheck_5651_; 
v_G_5606_ = lean_ctor_get(v_date_4647_, 0);
v_y_5607_ = lean_ctor_get(v_date_4647_, 1);
v_u_5608_ = lean_ctor_get(v_date_4647_, 2);
v_Y_5609_ = lean_ctor_get(v_date_4647_, 3);
v_D_5610_ = lean_ctor_get(v_date_4647_, 4);
v_M_5611_ = lean_ctor_get(v_date_4647_, 5);
v_L_5612_ = lean_ctor_get(v_date_4647_, 6);
v_d_5613_ = lean_ctor_get(v_date_4647_, 7);
v_Q_5614_ = lean_ctor_get(v_date_4647_, 8);
v_q_5615_ = lean_ctor_get(v_date_4647_, 9);
v_w_5616_ = lean_ctor_get(v_date_4647_, 10);
v_W_5617_ = lean_ctor_get(v_date_4647_, 11);
v_E_5618_ = lean_ctor_get(v_date_4647_, 12);
v_e_5619_ = lean_ctor_get(v_date_4647_, 13);
v_c_5620_ = lean_ctor_get(v_date_4647_, 14);
v_F_5621_ = lean_ctor_get(v_date_4647_, 15);
v_a_5622_ = lean_ctor_get(v_date_4647_, 16);
v_b_5623_ = lean_ctor_get(v_date_4647_, 17);
v_B_5624_ = lean_ctor_get(v_date_4647_, 18);
v_K_5625_ = lean_ctor_get(v_date_4647_, 20);
v_k_5626_ = lean_ctor_get(v_date_4647_, 21);
v_H_5627_ = lean_ctor_get(v_date_4647_, 22);
v_m_5628_ = lean_ctor_get(v_date_4647_, 23);
v_s_5629_ = lean_ctor_get(v_date_4647_, 24);
v_S_5630_ = lean_ctor_get(v_date_4647_, 25);
v_A_5631_ = lean_ctor_get(v_date_4647_, 26);
v_n_5632_ = lean_ctor_get(v_date_4647_, 27);
v_N_5633_ = lean_ctor_get(v_date_4647_, 28);
v_V_5634_ = lean_ctor_get(v_date_4647_, 29);
v_z_5635_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_5636_ = lean_ctor_get(v_date_4647_, 31);
v_v_5637_ = lean_ctor_get(v_date_4647_, 32);
v_O_5638_ = lean_ctor_get(v_date_4647_, 33);
v_X_5639_ = lean_ctor_get(v_date_4647_, 34);
v_x_5640_ = lean_ctor_get(v_date_4647_, 35);
v_Z_5641_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5651_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5651_ == 0)
{
lean_object* v_unused_5652_; 
v_unused_5652_ = lean_ctor_get(v_date_4647_, 19);
lean_dec(v_unused_5652_);
v___x_5643_ = v_date_4647_;
v_isShared_5644_ = v_isSharedCheck_5651_;
goto v_resetjp_5642_;
}
else
{
lean_inc(v_Z_5641_);
lean_inc(v_x_5640_);
lean_inc(v_X_5639_);
lean_inc(v_O_5638_);
lean_inc(v_v_5637_);
lean_inc(v_zabbrev_5636_);
lean_inc(v_z_5635_);
lean_inc(v_V_5634_);
lean_inc(v_N_5633_);
lean_inc(v_n_5632_);
lean_inc(v_A_5631_);
lean_inc(v_S_5630_);
lean_inc(v_s_5629_);
lean_inc(v_m_5628_);
lean_inc(v_H_5627_);
lean_inc(v_k_5626_);
lean_inc(v_K_5625_);
lean_inc(v_B_5624_);
lean_inc(v_b_5623_);
lean_inc(v_a_5622_);
lean_inc(v_F_5621_);
lean_inc(v_c_5620_);
lean_inc(v_e_5619_);
lean_inc(v_E_5618_);
lean_inc(v_W_5617_);
lean_inc(v_w_5616_);
lean_inc(v_q_5615_);
lean_inc(v_Q_5614_);
lean_inc(v_d_5613_);
lean_inc(v_L_5612_);
lean_inc(v_M_5611_);
lean_inc(v_D_5610_);
lean_inc(v_Y_5609_);
lean_inc(v_u_5608_);
lean_inc(v_y_5607_);
lean_inc(v_G_5606_);
lean_dec(v_date_4647_);
v___x_5643_ = lean_box(0);
v_isShared_5644_ = v_isSharedCheck_5651_;
goto v_resetjp_5642_;
}
v_resetjp_5642_:
{
lean_object* v___x_5646_; 
if (v_isShared_5605_ == 0)
{
lean_ctor_set_tag(v___x_5604_, 1);
lean_ctor_set(v___x_5604_, 0, v_data_4649_);
v___x_5646_ = v___x_5604_;
goto v_reusejp_5645_;
}
else
{
lean_object* v_reuseFailAlloc_5650_; 
v_reuseFailAlloc_5650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5650_, 0, v_data_4649_);
v___x_5646_ = v_reuseFailAlloc_5650_;
goto v_reusejp_5645_;
}
v_reusejp_5645_:
{
lean_object* v___x_5648_; 
if (v_isShared_5644_ == 0)
{
lean_ctor_set(v___x_5643_, 19, v___x_5646_);
v___x_5648_ = v___x_5643_;
goto v_reusejp_5647_;
}
else
{
lean_object* v_reuseFailAlloc_5649_; 
v_reuseFailAlloc_5649_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5649_, 0, v_G_5606_);
lean_ctor_set(v_reuseFailAlloc_5649_, 1, v_y_5607_);
lean_ctor_set(v_reuseFailAlloc_5649_, 2, v_u_5608_);
lean_ctor_set(v_reuseFailAlloc_5649_, 3, v_Y_5609_);
lean_ctor_set(v_reuseFailAlloc_5649_, 4, v_D_5610_);
lean_ctor_set(v_reuseFailAlloc_5649_, 5, v_M_5611_);
lean_ctor_set(v_reuseFailAlloc_5649_, 6, v_L_5612_);
lean_ctor_set(v_reuseFailAlloc_5649_, 7, v_d_5613_);
lean_ctor_set(v_reuseFailAlloc_5649_, 8, v_Q_5614_);
lean_ctor_set(v_reuseFailAlloc_5649_, 9, v_q_5615_);
lean_ctor_set(v_reuseFailAlloc_5649_, 10, v_w_5616_);
lean_ctor_set(v_reuseFailAlloc_5649_, 11, v_W_5617_);
lean_ctor_set(v_reuseFailAlloc_5649_, 12, v_E_5618_);
lean_ctor_set(v_reuseFailAlloc_5649_, 13, v_e_5619_);
lean_ctor_set(v_reuseFailAlloc_5649_, 14, v_c_5620_);
lean_ctor_set(v_reuseFailAlloc_5649_, 15, v_F_5621_);
lean_ctor_set(v_reuseFailAlloc_5649_, 16, v_a_5622_);
lean_ctor_set(v_reuseFailAlloc_5649_, 17, v_b_5623_);
lean_ctor_set(v_reuseFailAlloc_5649_, 18, v_B_5624_);
lean_ctor_set(v_reuseFailAlloc_5649_, 19, v___x_5646_);
lean_ctor_set(v_reuseFailAlloc_5649_, 20, v_K_5625_);
lean_ctor_set(v_reuseFailAlloc_5649_, 21, v_k_5626_);
lean_ctor_set(v_reuseFailAlloc_5649_, 22, v_H_5627_);
lean_ctor_set(v_reuseFailAlloc_5649_, 23, v_m_5628_);
lean_ctor_set(v_reuseFailAlloc_5649_, 24, v_s_5629_);
lean_ctor_set(v_reuseFailAlloc_5649_, 25, v_S_5630_);
lean_ctor_set(v_reuseFailAlloc_5649_, 26, v_A_5631_);
lean_ctor_set(v_reuseFailAlloc_5649_, 27, v_n_5632_);
lean_ctor_set(v_reuseFailAlloc_5649_, 28, v_N_5633_);
lean_ctor_set(v_reuseFailAlloc_5649_, 29, v_V_5634_);
lean_ctor_set(v_reuseFailAlloc_5649_, 30, v_z_5635_);
lean_ctor_set(v_reuseFailAlloc_5649_, 31, v_zabbrev_5636_);
lean_ctor_set(v_reuseFailAlloc_5649_, 32, v_v_5637_);
lean_ctor_set(v_reuseFailAlloc_5649_, 33, v_O_5638_);
lean_ctor_set(v_reuseFailAlloc_5649_, 34, v_X_5639_);
lean_ctor_set(v_reuseFailAlloc_5649_, 35, v_x_5640_);
lean_ctor_set(v_reuseFailAlloc_5649_, 36, v_Z_5641_);
v___x_5648_ = v_reuseFailAlloc_5649_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
return v___x_5648_;
}
}
}
}
}
case 20:
{
lean_object* v___x_5656_; uint8_t v_isShared_5657_; uint8_t v_isSharedCheck_5705_; 
v_isSharedCheck_5705_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_5705_ == 0)
{
lean_object* v_unused_5706_; 
v_unused_5706_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_5706_);
v___x_5656_ = v_modifier_4648_;
v_isShared_5657_ = v_isSharedCheck_5705_;
goto v_resetjp_5655_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_5656_ = lean_box(0);
v_isShared_5657_ = v_isSharedCheck_5705_;
goto v_resetjp_5655_;
}
v_resetjp_5655_:
{
lean_object* v_G_5658_; lean_object* v_y_5659_; lean_object* v_u_5660_; lean_object* v_Y_5661_; lean_object* v_D_5662_; lean_object* v_M_5663_; lean_object* v_L_5664_; lean_object* v_d_5665_; lean_object* v_Q_5666_; lean_object* v_q_5667_; lean_object* v_w_5668_; lean_object* v_W_5669_; lean_object* v_E_5670_; lean_object* v_e_5671_; lean_object* v_c_5672_; lean_object* v_F_5673_; lean_object* v_a_5674_; lean_object* v_b_5675_; lean_object* v_B_5676_; lean_object* v_h_5677_; lean_object* v_k_5678_; lean_object* v_H_5679_; lean_object* v_m_5680_; lean_object* v_s_5681_; lean_object* v_S_5682_; lean_object* v_A_5683_; lean_object* v_n_5684_; lean_object* v_N_5685_; lean_object* v_V_5686_; lean_object* v_z_5687_; lean_object* v_zabbrev_5688_; lean_object* v_v_5689_; lean_object* v_O_5690_; lean_object* v_X_5691_; lean_object* v_x_5692_; lean_object* v_Z_5693_; lean_object* v___x_5695_; uint8_t v_isShared_5696_; uint8_t v_isSharedCheck_5703_; 
v_G_5658_ = lean_ctor_get(v_date_4647_, 0);
v_y_5659_ = lean_ctor_get(v_date_4647_, 1);
v_u_5660_ = lean_ctor_get(v_date_4647_, 2);
v_Y_5661_ = lean_ctor_get(v_date_4647_, 3);
v_D_5662_ = lean_ctor_get(v_date_4647_, 4);
v_M_5663_ = lean_ctor_get(v_date_4647_, 5);
v_L_5664_ = lean_ctor_get(v_date_4647_, 6);
v_d_5665_ = lean_ctor_get(v_date_4647_, 7);
v_Q_5666_ = lean_ctor_get(v_date_4647_, 8);
v_q_5667_ = lean_ctor_get(v_date_4647_, 9);
v_w_5668_ = lean_ctor_get(v_date_4647_, 10);
v_W_5669_ = lean_ctor_get(v_date_4647_, 11);
v_E_5670_ = lean_ctor_get(v_date_4647_, 12);
v_e_5671_ = lean_ctor_get(v_date_4647_, 13);
v_c_5672_ = lean_ctor_get(v_date_4647_, 14);
v_F_5673_ = lean_ctor_get(v_date_4647_, 15);
v_a_5674_ = lean_ctor_get(v_date_4647_, 16);
v_b_5675_ = lean_ctor_get(v_date_4647_, 17);
v_B_5676_ = lean_ctor_get(v_date_4647_, 18);
v_h_5677_ = lean_ctor_get(v_date_4647_, 19);
v_k_5678_ = lean_ctor_get(v_date_4647_, 21);
v_H_5679_ = lean_ctor_get(v_date_4647_, 22);
v_m_5680_ = lean_ctor_get(v_date_4647_, 23);
v_s_5681_ = lean_ctor_get(v_date_4647_, 24);
v_S_5682_ = lean_ctor_get(v_date_4647_, 25);
v_A_5683_ = lean_ctor_get(v_date_4647_, 26);
v_n_5684_ = lean_ctor_get(v_date_4647_, 27);
v_N_5685_ = lean_ctor_get(v_date_4647_, 28);
v_V_5686_ = lean_ctor_get(v_date_4647_, 29);
v_z_5687_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_5688_ = lean_ctor_get(v_date_4647_, 31);
v_v_5689_ = lean_ctor_get(v_date_4647_, 32);
v_O_5690_ = lean_ctor_get(v_date_4647_, 33);
v_X_5691_ = lean_ctor_get(v_date_4647_, 34);
v_x_5692_ = lean_ctor_get(v_date_4647_, 35);
v_Z_5693_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5703_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5703_ == 0)
{
lean_object* v_unused_5704_; 
v_unused_5704_ = lean_ctor_get(v_date_4647_, 20);
lean_dec(v_unused_5704_);
v___x_5695_ = v_date_4647_;
v_isShared_5696_ = v_isSharedCheck_5703_;
goto v_resetjp_5694_;
}
else
{
lean_inc(v_Z_5693_);
lean_inc(v_x_5692_);
lean_inc(v_X_5691_);
lean_inc(v_O_5690_);
lean_inc(v_v_5689_);
lean_inc(v_zabbrev_5688_);
lean_inc(v_z_5687_);
lean_inc(v_V_5686_);
lean_inc(v_N_5685_);
lean_inc(v_n_5684_);
lean_inc(v_A_5683_);
lean_inc(v_S_5682_);
lean_inc(v_s_5681_);
lean_inc(v_m_5680_);
lean_inc(v_H_5679_);
lean_inc(v_k_5678_);
lean_inc(v_h_5677_);
lean_inc(v_B_5676_);
lean_inc(v_b_5675_);
lean_inc(v_a_5674_);
lean_inc(v_F_5673_);
lean_inc(v_c_5672_);
lean_inc(v_e_5671_);
lean_inc(v_E_5670_);
lean_inc(v_W_5669_);
lean_inc(v_w_5668_);
lean_inc(v_q_5667_);
lean_inc(v_Q_5666_);
lean_inc(v_d_5665_);
lean_inc(v_L_5664_);
lean_inc(v_M_5663_);
lean_inc(v_D_5662_);
lean_inc(v_Y_5661_);
lean_inc(v_u_5660_);
lean_inc(v_y_5659_);
lean_inc(v_G_5658_);
lean_dec(v_date_4647_);
v___x_5695_ = lean_box(0);
v_isShared_5696_ = v_isSharedCheck_5703_;
goto v_resetjp_5694_;
}
v_resetjp_5694_:
{
lean_object* v___x_5698_; 
if (v_isShared_5657_ == 0)
{
lean_ctor_set_tag(v___x_5656_, 1);
lean_ctor_set(v___x_5656_, 0, v_data_4649_);
v___x_5698_ = v___x_5656_;
goto v_reusejp_5697_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v_data_4649_);
v___x_5698_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5697_;
}
v_reusejp_5697_:
{
lean_object* v___x_5700_; 
if (v_isShared_5696_ == 0)
{
lean_ctor_set(v___x_5695_, 20, v___x_5698_);
v___x_5700_ = v___x_5695_;
goto v_reusejp_5699_;
}
else
{
lean_object* v_reuseFailAlloc_5701_; 
v_reuseFailAlloc_5701_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5701_, 0, v_G_5658_);
lean_ctor_set(v_reuseFailAlloc_5701_, 1, v_y_5659_);
lean_ctor_set(v_reuseFailAlloc_5701_, 2, v_u_5660_);
lean_ctor_set(v_reuseFailAlloc_5701_, 3, v_Y_5661_);
lean_ctor_set(v_reuseFailAlloc_5701_, 4, v_D_5662_);
lean_ctor_set(v_reuseFailAlloc_5701_, 5, v_M_5663_);
lean_ctor_set(v_reuseFailAlloc_5701_, 6, v_L_5664_);
lean_ctor_set(v_reuseFailAlloc_5701_, 7, v_d_5665_);
lean_ctor_set(v_reuseFailAlloc_5701_, 8, v_Q_5666_);
lean_ctor_set(v_reuseFailAlloc_5701_, 9, v_q_5667_);
lean_ctor_set(v_reuseFailAlloc_5701_, 10, v_w_5668_);
lean_ctor_set(v_reuseFailAlloc_5701_, 11, v_W_5669_);
lean_ctor_set(v_reuseFailAlloc_5701_, 12, v_E_5670_);
lean_ctor_set(v_reuseFailAlloc_5701_, 13, v_e_5671_);
lean_ctor_set(v_reuseFailAlloc_5701_, 14, v_c_5672_);
lean_ctor_set(v_reuseFailAlloc_5701_, 15, v_F_5673_);
lean_ctor_set(v_reuseFailAlloc_5701_, 16, v_a_5674_);
lean_ctor_set(v_reuseFailAlloc_5701_, 17, v_b_5675_);
lean_ctor_set(v_reuseFailAlloc_5701_, 18, v_B_5676_);
lean_ctor_set(v_reuseFailAlloc_5701_, 19, v_h_5677_);
lean_ctor_set(v_reuseFailAlloc_5701_, 20, v___x_5698_);
lean_ctor_set(v_reuseFailAlloc_5701_, 21, v_k_5678_);
lean_ctor_set(v_reuseFailAlloc_5701_, 22, v_H_5679_);
lean_ctor_set(v_reuseFailAlloc_5701_, 23, v_m_5680_);
lean_ctor_set(v_reuseFailAlloc_5701_, 24, v_s_5681_);
lean_ctor_set(v_reuseFailAlloc_5701_, 25, v_S_5682_);
lean_ctor_set(v_reuseFailAlloc_5701_, 26, v_A_5683_);
lean_ctor_set(v_reuseFailAlloc_5701_, 27, v_n_5684_);
lean_ctor_set(v_reuseFailAlloc_5701_, 28, v_N_5685_);
lean_ctor_set(v_reuseFailAlloc_5701_, 29, v_V_5686_);
lean_ctor_set(v_reuseFailAlloc_5701_, 30, v_z_5687_);
lean_ctor_set(v_reuseFailAlloc_5701_, 31, v_zabbrev_5688_);
lean_ctor_set(v_reuseFailAlloc_5701_, 32, v_v_5689_);
lean_ctor_set(v_reuseFailAlloc_5701_, 33, v_O_5690_);
lean_ctor_set(v_reuseFailAlloc_5701_, 34, v_X_5691_);
lean_ctor_set(v_reuseFailAlloc_5701_, 35, v_x_5692_);
lean_ctor_set(v_reuseFailAlloc_5701_, 36, v_Z_5693_);
v___x_5700_ = v_reuseFailAlloc_5701_;
goto v_reusejp_5699_;
}
v_reusejp_5699_:
{
return v___x_5700_;
}
}
}
}
}
case 21:
{
lean_object* v___x_5708_; uint8_t v_isShared_5709_; uint8_t v_isSharedCheck_5757_; 
v_isSharedCheck_5757_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_5757_ == 0)
{
lean_object* v_unused_5758_; 
v_unused_5758_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_5758_);
v___x_5708_ = v_modifier_4648_;
v_isShared_5709_ = v_isSharedCheck_5757_;
goto v_resetjp_5707_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_5708_ = lean_box(0);
v_isShared_5709_ = v_isSharedCheck_5757_;
goto v_resetjp_5707_;
}
v_resetjp_5707_:
{
lean_object* v_G_5710_; lean_object* v_y_5711_; lean_object* v_u_5712_; lean_object* v_Y_5713_; lean_object* v_D_5714_; lean_object* v_M_5715_; lean_object* v_L_5716_; lean_object* v_d_5717_; lean_object* v_Q_5718_; lean_object* v_q_5719_; lean_object* v_w_5720_; lean_object* v_W_5721_; lean_object* v_E_5722_; lean_object* v_e_5723_; lean_object* v_c_5724_; lean_object* v_F_5725_; lean_object* v_a_5726_; lean_object* v_b_5727_; lean_object* v_B_5728_; lean_object* v_h_5729_; lean_object* v_K_5730_; lean_object* v_H_5731_; lean_object* v_m_5732_; lean_object* v_s_5733_; lean_object* v_S_5734_; lean_object* v_A_5735_; lean_object* v_n_5736_; lean_object* v_N_5737_; lean_object* v_V_5738_; lean_object* v_z_5739_; lean_object* v_zabbrev_5740_; lean_object* v_v_5741_; lean_object* v_O_5742_; lean_object* v_X_5743_; lean_object* v_x_5744_; lean_object* v_Z_5745_; lean_object* v___x_5747_; uint8_t v_isShared_5748_; uint8_t v_isSharedCheck_5755_; 
v_G_5710_ = lean_ctor_get(v_date_4647_, 0);
v_y_5711_ = lean_ctor_get(v_date_4647_, 1);
v_u_5712_ = lean_ctor_get(v_date_4647_, 2);
v_Y_5713_ = lean_ctor_get(v_date_4647_, 3);
v_D_5714_ = lean_ctor_get(v_date_4647_, 4);
v_M_5715_ = lean_ctor_get(v_date_4647_, 5);
v_L_5716_ = lean_ctor_get(v_date_4647_, 6);
v_d_5717_ = lean_ctor_get(v_date_4647_, 7);
v_Q_5718_ = lean_ctor_get(v_date_4647_, 8);
v_q_5719_ = lean_ctor_get(v_date_4647_, 9);
v_w_5720_ = lean_ctor_get(v_date_4647_, 10);
v_W_5721_ = lean_ctor_get(v_date_4647_, 11);
v_E_5722_ = lean_ctor_get(v_date_4647_, 12);
v_e_5723_ = lean_ctor_get(v_date_4647_, 13);
v_c_5724_ = lean_ctor_get(v_date_4647_, 14);
v_F_5725_ = lean_ctor_get(v_date_4647_, 15);
v_a_5726_ = lean_ctor_get(v_date_4647_, 16);
v_b_5727_ = lean_ctor_get(v_date_4647_, 17);
v_B_5728_ = lean_ctor_get(v_date_4647_, 18);
v_h_5729_ = lean_ctor_get(v_date_4647_, 19);
v_K_5730_ = lean_ctor_get(v_date_4647_, 20);
v_H_5731_ = lean_ctor_get(v_date_4647_, 22);
v_m_5732_ = lean_ctor_get(v_date_4647_, 23);
v_s_5733_ = lean_ctor_get(v_date_4647_, 24);
v_S_5734_ = lean_ctor_get(v_date_4647_, 25);
v_A_5735_ = lean_ctor_get(v_date_4647_, 26);
v_n_5736_ = lean_ctor_get(v_date_4647_, 27);
v_N_5737_ = lean_ctor_get(v_date_4647_, 28);
v_V_5738_ = lean_ctor_get(v_date_4647_, 29);
v_z_5739_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_5740_ = lean_ctor_get(v_date_4647_, 31);
v_v_5741_ = lean_ctor_get(v_date_4647_, 32);
v_O_5742_ = lean_ctor_get(v_date_4647_, 33);
v_X_5743_ = lean_ctor_get(v_date_4647_, 34);
v_x_5744_ = lean_ctor_get(v_date_4647_, 35);
v_Z_5745_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5755_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5755_ == 0)
{
lean_object* v_unused_5756_; 
v_unused_5756_ = lean_ctor_get(v_date_4647_, 21);
lean_dec(v_unused_5756_);
v___x_5747_ = v_date_4647_;
v_isShared_5748_ = v_isSharedCheck_5755_;
goto v_resetjp_5746_;
}
else
{
lean_inc(v_Z_5745_);
lean_inc(v_x_5744_);
lean_inc(v_X_5743_);
lean_inc(v_O_5742_);
lean_inc(v_v_5741_);
lean_inc(v_zabbrev_5740_);
lean_inc(v_z_5739_);
lean_inc(v_V_5738_);
lean_inc(v_N_5737_);
lean_inc(v_n_5736_);
lean_inc(v_A_5735_);
lean_inc(v_S_5734_);
lean_inc(v_s_5733_);
lean_inc(v_m_5732_);
lean_inc(v_H_5731_);
lean_inc(v_K_5730_);
lean_inc(v_h_5729_);
lean_inc(v_B_5728_);
lean_inc(v_b_5727_);
lean_inc(v_a_5726_);
lean_inc(v_F_5725_);
lean_inc(v_c_5724_);
lean_inc(v_e_5723_);
lean_inc(v_E_5722_);
lean_inc(v_W_5721_);
lean_inc(v_w_5720_);
lean_inc(v_q_5719_);
lean_inc(v_Q_5718_);
lean_inc(v_d_5717_);
lean_inc(v_L_5716_);
lean_inc(v_M_5715_);
lean_inc(v_D_5714_);
lean_inc(v_Y_5713_);
lean_inc(v_u_5712_);
lean_inc(v_y_5711_);
lean_inc(v_G_5710_);
lean_dec(v_date_4647_);
v___x_5747_ = lean_box(0);
v_isShared_5748_ = v_isSharedCheck_5755_;
goto v_resetjp_5746_;
}
v_resetjp_5746_:
{
lean_object* v___x_5750_; 
if (v_isShared_5709_ == 0)
{
lean_ctor_set_tag(v___x_5708_, 1);
lean_ctor_set(v___x_5708_, 0, v_data_4649_);
v___x_5750_ = v___x_5708_;
goto v_reusejp_5749_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v_data_4649_);
v___x_5750_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5749_;
}
v_reusejp_5749_:
{
lean_object* v___x_5752_; 
if (v_isShared_5748_ == 0)
{
lean_ctor_set(v___x_5747_, 21, v___x_5750_);
v___x_5752_ = v___x_5747_;
goto v_reusejp_5751_;
}
else
{
lean_object* v_reuseFailAlloc_5753_; 
v_reuseFailAlloc_5753_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5753_, 0, v_G_5710_);
lean_ctor_set(v_reuseFailAlloc_5753_, 1, v_y_5711_);
lean_ctor_set(v_reuseFailAlloc_5753_, 2, v_u_5712_);
lean_ctor_set(v_reuseFailAlloc_5753_, 3, v_Y_5713_);
lean_ctor_set(v_reuseFailAlloc_5753_, 4, v_D_5714_);
lean_ctor_set(v_reuseFailAlloc_5753_, 5, v_M_5715_);
lean_ctor_set(v_reuseFailAlloc_5753_, 6, v_L_5716_);
lean_ctor_set(v_reuseFailAlloc_5753_, 7, v_d_5717_);
lean_ctor_set(v_reuseFailAlloc_5753_, 8, v_Q_5718_);
lean_ctor_set(v_reuseFailAlloc_5753_, 9, v_q_5719_);
lean_ctor_set(v_reuseFailAlloc_5753_, 10, v_w_5720_);
lean_ctor_set(v_reuseFailAlloc_5753_, 11, v_W_5721_);
lean_ctor_set(v_reuseFailAlloc_5753_, 12, v_E_5722_);
lean_ctor_set(v_reuseFailAlloc_5753_, 13, v_e_5723_);
lean_ctor_set(v_reuseFailAlloc_5753_, 14, v_c_5724_);
lean_ctor_set(v_reuseFailAlloc_5753_, 15, v_F_5725_);
lean_ctor_set(v_reuseFailAlloc_5753_, 16, v_a_5726_);
lean_ctor_set(v_reuseFailAlloc_5753_, 17, v_b_5727_);
lean_ctor_set(v_reuseFailAlloc_5753_, 18, v_B_5728_);
lean_ctor_set(v_reuseFailAlloc_5753_, 19, v_h_5729_);
lean_ctor_set(v_reuseFailAlloc_5753_, 20, v_K_5730_);
lean_ctor_set(v_reuseFailAlloc_5753_, 21, v___x_5750_);
lean_ctor_set(v_reuseFailAlloc_5753_, 22, v_H_5731_);
lean_ctor_set(v_reuseFailAlloc_5753_, 23, v_m_5732_);
lean_ctor_set(v_reuseFailAlloc_5753_, 24, v_s_5733_);
lean_ctor_set(v_reuseFailAlloc_5753_, 25, v_S_5734_);
lean_ctor_set(v_reuseFailAlloc_5753_, 26, v_A_5735_);
lean_ctor_set(v_reuseFailAlloc_5753_, 27, v_n_5736_);
lean_ctor_set(v_reuseFailAlloc_5753_, 28, v_N_5737_);
lean_ctor_set(v_reuseFailAlloc_5753_, 29, v_V_5738_);
lean_ctor_set(v_reuseFailAlloc_5753_, 30, v_z_5739_);
lean_ctor_set(v_reuseFailAlloc_5753_, 31, v_zabbrev_5740_);
lean_ctor_set(v_reuseFailAlloc_5753_, 32, v_v_5741_);
lean_ctor_set(v_reuseFailAlloc_5753_, 33, v_O_5742_);
lean_ctor_set(v_reuseFailAlloc_5753_, 34, v_X_5743_);
lean_ctor_set(v_reuseFailAlloc_5753_, 35, v_x_5744_);
lean_ctor_set(v_reuseFailAlloc_5753_, 36, v_Z_5745_);
v___x_5752_ = v_reuseFailAlloc_5753_;
goto v_reusejp_5751_;
}
v_reusejp_5751_:
{
return v___x_5752_;
}
}
}
}
}
case 22:
{
lean_object* v___x_5760_; uint8_t v_isShared_5761_; uint8_t v_isSharedCheck_5809_; 
v_isSharedCheck_5809_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_5809_ == 0)
{
lean_object* v_unused_5810_; 
v_unused_5810_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_5810_);
v___x_5760_ = v_modifier_4648_;
v_isShared_5761_ = v_isSharedCheck_5809_;
goto v_resetjp_5759_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_5760_ = lean_box(0);
v_isShared_5761_ = v_isSharedCheck_5809_;
goto v_resetjp_5759_;
}
v_resetjp_5759_:
{
lean_object* v_G_5762_; lean_object* v_y_5763_; lean_object* v_u_5764_; lean_object* v_Y_5765_; lean_object* v_D_5766_; lean_object* v_M_5767_; lean_object* v_L_5768_; lean_object* v_d_5769_; lean_object* v_Q_5770_; lean_object* v_q_5771_; lean_object* v_w_5772_; lean_object* v_W_5773_; lean_object* v_E_5774_; lean_object* v_e_5775_; lean_object* v_c_5776_; lean_object* v_F_5777_; lean_object* v_a_5778_; lean_object* v_b_5779_; lean_object* v_B_5780_; lean_object* v_h_5781_; lean_object* v_K_5782_; lean_object* v_k_5783_; lean_object* v_m_5784_; lean_object* v_s_5785_; lean_object* v_S_5786_; lean_object* v_A_5787_; lean_object* v_n_5788_; lean_object* v_N_5789_; lean_object* v_V_5790_; lean_object* v_z_5791_; lean_object* v_zabbrev_5792_; lean_object* v_v_5793_; lean_object* v_O_5794_; lean_object* v_X_5795_; lean_object* v_x_5796_; lean_object* v_Z_5797_; lean_object* v___x_5799_; uint8_t v_isShared_5800_; uint8_t v_isSharedCheck_5807_; 
v_G_5762_ = lean_ctor_get(v_date_4647_, 0);
v_y_5763_ = lean_ctor_get(v_date_4647_, 1);
v_u_5764_ = lean_ctor_get(v_date_4647_, 2);
v_Y_5765_ = lean_ctor_get(v_date_4647_, 3);
v_D_5766_ = lean_ctor_get(v_date_4647_, 4);
v_M_5767_ = lean_ctor_get(v_date_4647_, 5);
v_L_5768_ = lean_ctor_get(v_date_4647_, 6);
v_d_5769_ = lean_ctor_get(v_date_4647_, 7);
v_Q_5770_ = lean_ctor_get(v_date_4647_, 8);
v_q_5771_ = lean_ctor_get(v_date_4647_, 9);
v_w_5772_ = lean_ctor_get(v_date_4647_, 10);
v_W_5773_ = lean_ctor_get(v_date_4647_, 11);
v_E_5774_ = lean_ctor_get(v_date_4647_, 12);
v_e_5775_ = lean_ctor_get(v_date_4647_, 13);
v_c_5776_ = lean_ctor_get(v_date_4647_, 14);
v_F_5777_ = lean_ctor_get(v_date_4647_, 15);
v_a_5778_ = lean_ctor_get(v_date_4647_, 16);
v_b_5779_ = lean_ctor_get(v_date_4647_, 17);
v_B_5780_ = lean_ctor_get(v_date_4647_, 18);
v_h_5781_ = lean_ctor_get(v_date_4647_, 19);
v_K_5782_ = lean_ctor_get(v_date_4647_, 20);
v_k_5783_ = lean_ctor_get(v_date_4647_, 21);
v_m_5784_ = lean_ctor_get(v_date_4647_, 23);
v_s_5785_ = lean_ctor_get(v_date_4647_, 24);
v_S_5786_ = lean_ctor_get(v_date_4647_, 25);
v_A_5787_ = lean_ctor_get(v_date_4647_, 26);
v_n_5788_ = lean_ctor_get(v_date_4647_, 27);
v_N_5789_ = lean_ctor_get(v_date_4647_, 28);
v_V_5790_ = lean_ctor_get(v_date_4647_, 29);
v_z_5791_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_5792_ = lean_ctor_get(v_date_4647_, 31);
v_v_5793_ = lean_ctor_get(v_date_4647_, 32);
v_O_5794_ = lean_ctor_get(v_date_4647_, 33);
v_X_5795_ = lean_ctor_get(v_date_4647_, 34);
v_x_5796_ = lean_ctor_get(v_date_4647_, 35);
v_Z_5797_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5807_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5807_ == 0)
{
lean_object* v_unused_5808_; 
v_unused_5808_ = lean_ctor_get(v_date_4647_, 22);
lean_dec(v_unused_5808_);
v___x_5799_ = v_date_4647_;
v_isShared_5800_ = v_isSharedCheck_5807_;
goto v_resetjp_5798_;
}
else
{
lean_inc(v_Z_5797_);
lean_inc(v_x_5796_);
lean_inc(v_X_5795_);
lean_inc(v_O_5794_);
lean_inc(v_v_5793_);
lean_inc(v_zabbrev_5792_);
lean_inc(v_z_5791_);
lean_inc(v_V_5790_);
lean_inc(v_N_5789_);
lean_inc(v_n_5788_);
lean_inc(v_A_5787_);
lean_inc(v_S_5786_);
lean_inc(v_s_5785_);
lean_inc(v_m_5784_);
lean_inc(v_k_5783_);
lean_inc(v_K_5782_);
lean_inc(v_h_5781_);
lean_inc(v_B_5780_);
lean_inc(v_b_5779_);
lean_inc(v_a_5778_);
lean_inc(v_F_5777_);
lean_inc(v_c_5776_);
lean_inc(v_e_5775_);
lean_inc(v_E_5774_);
lean_inc(v_W_5773_);
lean_inc(v_w_5772_);
lean_inc(v_q_5771_);
lean_inc(v_Q_5770_);
lean_inc(v_d_5769_);
lean_inc(v_L_5768_);
lean_inc(v_M_5767_);
lean_inc(v_D_5766_);
lean_inc(v_Y_5765_);
lean_inc(v_u_5764_);
lean_inc(v_y_5763_);
lean_inc(v_G_5762_);
lean_dec(v_date_4647_);
v___x_5799_ = lean_box(0);
v_isShared_5800_ = v_isSharedCheck_5807_;
goto v_resetjp_5798_;
}
v_resetjp_5798_:
{
lean_object* v___x_5802_; 
if (v_isShared_5761_ == 0)
{
lean_ctor_set_tag(v___x_5760_, 1);
lean_ctor_set(v___x_5760_, 0, v_data_4649_);
v___x_5802_ = v___x_5760_;
goto v_reusejp_5801_;
}
else
{
lean_object* v_reuseFailAlloc_5806_; 
v_reuseFailAlloc_5806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5806_, 0, v_data_4649_);
v___x_5802_ = v_reuseFailAlloc_5806_;
goto v_reusejp_5801_;
}
v_reusejp_5801_:
{
lean_object* v___x_5804_; 
if (v_isShared_5800_ == 0)
{
lean_ctor_set(v___x_5799_, 22, v___x_5802_);
v___x_5804_ = v___x_5799_;
goto v_reusejp_5803_;
}
else
{
lean_object* v_reuseFailAlloc_5805_; 
v_reuseFailAlloc_5805_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5805_, 0, v_G_5762_);
lean_ctor_set(v_reuseFailAlloc_5805_, 1, v_y_5763_);
lean_ctor_set(v_reuseFailAlloc_5805_, 2, v_u_5764_);
lean_ctor_set(v_reuseFailAlloc_5805_, 3, v_Y_5765_);
lean_ctor_set(v_reuseFailAlloc_5805_, 4, v_D_5766_);
lean_ctor_set(v_reuseFailAlloc_5805_, 5, v_M_5767_);
lean_ctor_set(v_reuseFailAlloc_5805_, 6, v_L_5768_);
lean_ctor_set(v_reuseFailAlloc_5805_, 7, v_d_5769_);
lean_ctor_set(v_reuseFailAlloc_5805_, 8, v_Q_5770_);
lean_ctor_set(v_reuseFailAlloc_5805_, 9, v_q_5771_);
lean_ctor_set(v_reuseFailAlloc_5805_, 10, v_w_5772_);
lean_ctor_set(v_reuseFailAlloc_5805_, 11, v_W_5773_);
lean_ctor_set(v_reuseFailAlloc_5805_, 12, v_E_5774_);
lean_ctor_set(v_reuseFailAlloc_5805_, 13, v_e_5775_);
lean_ctor_set(v_reuseFailAlloc_5805_, 14, v_c_5776_);
lean_ctor_set(v_reuseFailAlloc_5805_, 15, v_F_5777_);
lean_ctor_set(v_reuseFailAlloc_5805_, 16, v_a_5778_);
lean_ctor_set(v_reuseFailAlloc_5805_, 17, v_b_5779_);
lean_ctor_set(v_reuseFailAlloc_5805_, 18, v_B_5780_);
lean_ctor_set(v_reuseFailAlloc_5805_, 19, v_h_5781_);
lean_ctor_set(v_reuseFailAlloc_5805_, 20, v_K_5782_);
lean_ctor_set(v_reuseFailAlloc_5805_, 21, v_k_5783_);
lean_ctor_set(v_reuseFailAlloc_5805_, 22, v___x_5802_);
lean_ctor_set(v_reuseFailAlloc_5805_, 23, v_m_5784_);
lean_ctor_set(v_reuseFailAlloc_5805_, 24, v_s_5785_);
lean_ctor_set(v_reuseFailAlloc_5805_, 25, v_S_5786_);
lean_ctor_set(v_reuseFailAlloc_5805_, 26, v_A_5787_);
lean_ctor_set(v_reuseFailAlloc_5805_, 27, v_n_5788_);
lean_ctor_set(v_reuseFailAlloc_5805_, 28, v_N_5789_);
lean_ctor_set(v_reuseFailAlloc_5805_, 29, v_V_5790_);
lean_ctor_set(v_reuseFailAlloc_5805_, 30, v_z_5791_);
lean_ctor_set(v_reuseFailAlloc_5805_, 31, v_zabbrev_5792_);
lean_ctor_set(v_reuseFailAlloc_5805_, 32, v_v_5793_);
lean_ctor_set(v_reuseFailAlloc_5805_, 33, v_O_5794_);
lean_ctor_set(v_reuseFailAlloc_5805_, 34, v_X_5795_);
lean_ctor_set(v_reuseFailAlloc_5805_, 35, v_x_5796_);
lean_ctor_set(v_reuseFailAlloc_5805_, 36, v_Z_5797_);
v___x_5804_ = v_reuseFailAlloc_5805_;
goto v_reusejp_5803_;
}
v_reusejp_5803_:
{
return v___x_5804_;
}
}
}
}
}
case 23:
{
lean_object* v___x_5812_; uint8_t v_isShared_5813_; uint8_t v_isSharedCheck_5861_; 
v_isSharedCheck_5861_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_5861_ == 0)
{
lean_object* v_unused_5862_; 
v_unused_5862_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_5862_);
v___x_5812_ = v_modifier_4648_;
v_isShared_5813_ = v_isSharedCheck_5861_;
goto v_resetjp_5811_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_5812_ = lean_box(0);
v_isShared_5813_ = v_isSharedCheck_5861_;
goto v_resetjp_5811_;
}
v_resetjp_5811_:
{
lean_object* v_G_5814_; lean_object* v_y_5815_; lean_object* v_u_5816_; lean_object* v_Y_5817_; lean_object* v_D_5818_; lean_object* v_M_5819_; lean_object* v_L_5820_; lean_object* v_d_5821_; lean_object* v_Q_5822_; lean_object* v_q_5823_; lean_object* v_w_5824_; lean_object* v_W_5825_; lean_object* v_E_5826_; lean_object* v_e_5827_; lean_object* v_c_5828_; lean_object* v_F_5829_; lean_object* v_a_5830_; lean_object* v_b_5831_; lean_object* v_B_5832_; lean_object* v_h_5833_; lean_object* v_K_5834_; lean_object* v_k_5835_; lean_object* v_H_5836_; lean_object* v_s_5837_; lean_object* v_S_5838_; lean_object* v_A_5839_; lean_object* v_n_5840_; lean_object* v_N_5841_; lean_object* v_V_5842_; lean_object* v_z_5843_; lean_object* v_zabbrev_5844_; lean_object* v_v_5845_; lean_object* v_O_5846_; lean_object* v_X_5847_; lean_object* v_x_5848_; lean_object* v_Z_5849_; lean_object* v___x_5851_; uint8_t v_isShared_5852_; uint8_t v_isSharedCheck_5859_; 
v_G_5814_ = lean_ctor_get(v_date_4647_, 0);
v_y_5815_ = lean_ctor_get(v_date_4647_, 1);
v_u_5816_ = lean_ctor_get(v_date_4647_, 2);
v_Y_5817_ = lean_ctor_get(v_date_4647_, 3);
v_D_5818_ = lean_ctor_get(v_date_4647_, 4);
v_M_5819_ = lean_ctor_get(v_date_4647_, 5);
v_L_5820_ = lean_ctor_get(v_date_4647_, 6);
v_d_5821_ = lean_ctor_get(v_date_4647_, 7);
v_Q_5822_ = lean_ctor_get(v_date_4647_, 8);
v_q_5823_ = lean_ctor_get(v_date_4647_, 9);
v_w_5824_ = lean_ctor_get(v_date_4647_, 10);
v_W_5825_ = lean_ctor_get(v_date_4647_, 11);
v_E_5826_ = lean_ctor_get(v_date_4647_, 12);
v_e_5827_ = lean_ctor_get(v_date_4647_, 13);
v_c_5828_ = lean_ctor_get(v_date_4647_, 14);
v_F_5829_ = lean_ctor_get(v_date_4647_, 15);
v_a_5830_ = lean_ctor_get(v_date_4647_, 16);
v_b_5831_ = lean_ctor_get(v_date_4647_, 17);
v_B_5832_ = lean_ctor_get(v_date_4647_, 18);
v_h_5833_ = lean_ctor_get(v_date_4647_, 19);
v_K_5834_ = lean_ctor_get(v_date_4647_, 20);
v_k_5835_ = lean_ctor_get(v_date_4647_, 21);
v_H_5836_ = lean_ctor_get(v_date_4647_, 22);
v_s_5837_ = lean_ctor_get(v_date_4647_, 24);
v_S_5838_ = lean_ctor_get(v_date_4647_, 25);
v_A_5839_ = lean_ctor_get(v_date_4647_, 26);
v_n_5840_ = lean_ctor_get(v_date_4647_, 27);
v_N_5841_ = lean_ctor_get(v_date_4647_, 28);
v_V_5842_ = lean_ctor_get(v_date_4647_, 29);
v_z_5843_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_5844_ = lean_ctor_get(v_date_4647_, 31);
v_v_5845_ = lean_ctor_get(v_date_4647_, 32);
v_O_5846_ = lean_ctor_get(v_date_4647_, 33);
v_X_5847_ = lean_ctor_get(v_date_4647_, 34);
v_x_5848_ = lean_ctor_get(v_date_4647_, 35);
v_Z_5849_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5859_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5859_ == 0)
{
lean_object* v_unused_5860_; 
v_unused_5860_ = lean_ctor_get(v_date_4647_, 23);
lean_dec(v_unused_5860_);
v___x_5851_ = v_date_4647_;
v_isShared_5852_ = v_isSharedCheck_5859_;
goto v_resetjp_5850_;
}
else
{
lean_inc(v_Z_5849_);
lean_inc(v_x_5848_);
lean_inc(v_X_5847_);
lean_inc(v_O_5846_);
lean_inc(v_v_5845_);
lean_inc(v_zabbrev_5844_);
lean_inc(v_z_5843_);
lean_inc(v_V_5842_);
lean_inc(v_N_5841_);
lean_inc(v_n_5840_);
lean_inc(v_A_5839_);
lean_inc(v_S_5838_);
lean_inc(v_s_5837_);
lean_inc(v_H_5836_);
lean_inc(v_k_5835_);
lean_inc(v_K_5834_);
lean_inc(v_h_5833_);
lean_inc(v_B_5832_);
lean_inc(v_b_5831_);
lean_inc(v_a_5830_);
lean_inc(v_F_5829_);
lean_inc(v_c_5828_);
lean_inc(v_e_5827_);
lean_inc(v_E_5826_);
lean_inc(v_W_5825_);
lean_inc(v_w_5824_);
lean_inc(v_q_5823_);
lean_inc(v_Q_5822_);
lean_inc(v_d_5821_);
lean_inc(v_L_5820_);
lean_inc(v_M_5819_);
lean_inc(v_D_5818_);
lean_inc(v_Y_5817_);
lean_inc(v_u_5816_);
lean_inc(v_y_5815_);
lean_inc(v_G_5814_);
lean_dec(v_date_4647_);
v___x_5851_ = lean_box(0);
v_isShared_5852_ = v_isSharedCheck_5859_;
goto v_resetjp_5850_;
}
v_resetjp_5850_:
{
lean_object* v___x_5854_; 
if (v_isShared_5813_ == 0)
{
lean_ctor_set_tag(v___x_5812_, 1);
lean_ctor_set(v___x_5812_, 0, v_data_4649_);
v___x_5854_ = v___x_5812_;
goto v_reusejp_5853_;
}
else
{
lean_object* v_reuseFailAlloc_5858_; 
v_reuseFailAlloc_5858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5858_, 0, v_data_4649_);
v___x_5854_ = v_reuseFailAlloc_5858_;
goto v_reusejp_5853_;
}
v_reusejp_5853_:
{
lean_object* v___x_5856_; 
if (v_isShared_5852_ == 0)
{
lean_ctor_set(v___x_5851_, 23, v___x_5854_);
v___x_5856_ = v___x_5851_;
goto v_reusejp_5855_;
}
else
{
lean_object* v_reuseFailAlloc_5857_; 
v_reuseFailAlloc_5857_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5857_, 0, v_G_5814_);
lean_ctor_set(v_reuseFailAlloc_5857_, 1, v_y_5815_);
lean_ctor_set(v_reuseFailAlloc_5857_, 2, v_u_5816_);
lean_ctor_set(v_reuseFailAlloc_5857_, 3, v_Y_5817_);
lean_ctor_set(v_reuseFailAlloc_5857_, 4, v_D_5818_);
lean_ctor_set(v_reuseFailAlloc_5857_, 5, v_M_5819_);
lean_ctor_set(v_reuseFailAlloc_5857_, 6, v_L_5820_);
lean_ctor_set(v_reuseFailAlloc_5857_, 7, v_d_5821_);
lean_ctor_set(v_reuseFailAlloc_5857_, 8, v_Q_5822_);
lean_ctor_set(v_reuseFailAlloc_5857_, 9, v_q_5823_);
lean_ctor_set(v_reuseFailAlloc_5857_, 10, v_w_5824_);
lean_ctor_set(v_reuseFailAlloc_5857_, 11, v_W_5825_);
lean_ctor_set(v_reuseFailAlloc_5857_, 12, v_E_5826_);
lean_ctor_set(v_reuseFailAlloc_5857_, 13, v_e_5827_);
lean_ctor_set(v_reuseFailAlloc_5857_, 14, v_c_5828_);
lean_ctor_set(v_reuseFailAlloc_5857_, 15, v_F_5829_);
lean_ctor_set(v_reuseFailAlloc_5857_, 16, v_a_5830_);
lean_ctor_set(v_reuseFailAlloc_5857_, 17, v_b_5831_);
lean_ctor_set(v_reuseFailAlloc_5857_, 18, v_B_5832_);
lean_ctor_set(v_reuseFailAlloc_5857_, 19, v_h_5833_);
lean_ctor_set(v_reuseFailAlloc_5857_, 20, v_K_5834_);
lean_ctor_set(v_reuseFailAlloc_5857_, 21, v_k_5835_);
lean_ctor_set(v_reuseFailAlloc_5857_, 22, v_H_5836_);
lean_ctor_set(v_reuseFailAlloc_5857_, 23, v___x_5854_);
lean_ctor_set(v_reuseFailAlloc_5857_, 24, v_s_5837_);
lean_ctor_set(v_reuseFailAlloc_5857_, 25, v_S_5838_);
lean_ctor_set(v_reuseFailAlloc_5857_, 26, v_A_5839_);
lean_ctor_set(v_reuseFailAlloc_5857_, 27, v_n_5840_);
lean_ctor_set(v_reuseFailAlloc_5857_, 28, v_N_5841_);
lean_ctor_set(v_reuseFailAlloc_5857_, 29, v_V_5842_);
lean_ctor_set(v_reuseFailAlloc_5857_, 30, v_z_5843_);
lean_ctor_set(v_reuseFailAlloc_5857_, 31, v_zabbrev_5844_);
lean_ctor_set(v_reuseFailAlloc_5857_, 32, v_v_5845_);
lean_ctor_set(v_reuseFailAlloc_5857_, 33, v_O_5846_);
lean_ctor_set(v_reuseFailAlloc_5857_, 34, v_X_5847_);
lean_ctor_set(v_reuseFailAlloc_5857_, 35, v_x_5848_);
lean_ctor_set(v_reuseFailAlloc_5857_, 36, v_Z_5849_);
v___x_5856_ = v_reuseFailAlloc_5857_;
goto v_reusejp_5855_;
}
v_reusejp_5855_:
{
return v___x_5856_;
}
}
}
}
}
case 24:
{
lean_object* v___x_5864_; uint8_t v_isShared_5865_; uint8_t v_isSharedCheck_5913_; 
v_isSharedCheck_5913_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_5913_ == 0)
{
lean_object* v_unused_5914_; 
v_unused_5914_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_5914_);
v___x_5864_ = v_modifier_4648_;
v_isShared_5865_ = v_isSharedCheck_5913_;
goto v_resetjp_5863_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_5864_ = lean_box(0);
v_isShared_5865_ = v_isSharedCheck_5913_;
goto v_resetjp_5863_;
}
v_resetjp_5863_:
{
lean_object* v_G_5866_; lean_object* v_y_5867_; lean_object* v_u_5868_; lean_object* v_Y_5869_; lean_object* v_D_5870_; lean_object* v_M_5871_; lean_object* v_L_5872_; lean_object* v_d_5873_; lean_object* v_Q_5874_; lean_object* v_q_5875_; lean_object* v_w_5876_; lean_object* v_W_5877_; lean_object* v_E_5878_; lean_object* v_e_5879_; lean_object* v_c_5880_; lean_object* v_F_5881_; lean_object* v_a_5882_; lean_object* v_b_5883_; lean_object* v_B_5884_; lean_object* v_h_5885_; lean_object* v_K_5886_; lean_object* v_k_5887_; lean_object* v_H_5888_; lean_object* v_m_5889_; lean_object* v_S_5890_; lean_object* v_A_5891_; lean_object* v_n_5892_; lean_object* v_N_5893_; lean_object* v_V_5894_; lean_object* v_z_5895_; lean_object* v_zabbrev_5896_; lean_object* v_v_5897_; lean_object* v_O_5898_; lean_object* v_X_5899_; lean_object* v_x_5900_; lean_object* v_Z_5901_; lean_object* v___x_5903_; uint8_t v_isShared_5904_; uint8_t v_isSharedCheck_5911_; 
v_G_5866_ = lean_ctor_get(v_date_4647_, 0);
v_y_5867_ = lean_ctor_get(v_date_4647_, 1);
v_u_5868_ = lean_ctor_get(v_date_4647_, 2);
v_Y_5869_ = lean_ctor_get(v_date_4647_, 3);
v_D_5870_ = lean_ctor_get(v_date_4647_, 4);
v_M_5871_ = lean_ctor_get(v_date_4647_, 5);
v_L_5872_ = lean_ctor_get(v_date_4647_, 6);
v_d_5873_ = lean_ctor_get(v_date_4647_, 7);
v_Q_5874_ = lean_ctor_get(v_date_4647_, 8);
v_q_5875_ = lean_ctor_get(v_date_4647_, 9);
v_w_5876_ = lean_ctor_get(v_date_4647_, 10);
v_W_5877_ = lean_ctor_get(v_date_4647_, 11);
v_E_5878_ = lean_ctor_get(v_date_4647_, 12);
v_e_5879_ = lean_ctor_get(v_date_4647_, 13);
v_c_5880_ = lean_ctor_get(v_date_4647_, 14);
v_F_5881_ = lean_ctor_get(v_date_4647_, 15);
v_a_5882_ = lean_ctor_get(v_date_4647_, 16);
v_b_5883_ = lean_ctor_get(v_date_4647_, 17);
v_B_5884_ = lean_ctor_get(v_date_4647_, 18);
v_h_5885_ = lean_ctor_get(v_date_4647_, 19);
v_K_5886_ = lean_ctor_get(v_date_4647_, 20);
v_k_5887_ = lean_ctor_get(v_date_4647_, 21);
v_H_5888_ = lean_ctor_get(v_date_4647_, 22);
v_m_5889_ = lean_ctor_get(v_date_4647_, 23);
v_S_5890_ = lean_ctor_get(v_date_4647_, 25);
v_A_5891_ = lean_ctor_get(v_date_4647_, 26);
v_n_5892_ = lean_ctor_get(v_date_4647_, 27);
v_N_5893_ = lean_ctor_get(v_date_4647_, 28);
v_V_5894_ = lean_ctor_get(v_date_4647_, 29);
v_z_5895_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_5896_ = lean_ctor_get(v_date_4647_, 31);
v_v_5897_ = lean_ctor_get(v_date_4647_, 32);
v_O_5898_ = lean_ctor_get(v_date_4647_, 33);
v_X_5899_ = lean_ctor_get(v_date_4647_, 34);
v_x_5900_ = lean_ctor_get(v_date_4647_, 35);
v_Z_5901_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5911_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5911_ == 0)
{
lean_object* v_unused_5912_; 
v_unused_5912_ = lean_ctor_get(v_date_4647_, 24);
lean_dec(v_unused_5912_);
v___x_5903_ = v_date_4647_;
v_isShared_5904_ = v_isSharedCheck_5911_;
goto v_resetjp_5902_;
}
else
{
lean_inc(v_Z_5901_);
lean_inc(v_x_5900_);
lean_inc(v_X_5899_);
lean_inc(v_O_5898_);
lean_inc(v_v_5897_);
lean_inc(v_zabbrev_5896_);
lean_inc(v_z_5895_);
lean_inc(v_V_5894_);
lean_inc(v_N_5893_);
lean_inc(v_n_5892_);
lean_inc(v_A_5891_);
lean_inc(v_S_5890_);
lean_inc(v_m_5889_);
lean_inc(v_H_5888_);
lean_inc(v_k_5887_);
lean_inc(v_K_5886_);
lean_inc(v_h_5885_);
lean_inc(v_B_5884_);
lean_inc(v_b_5883_);
lean_inc(v_a_5882_);
lean_inc(v_F_5881_);
lean_inc(v_c_5880_);
lean_inc(v_e_5879_);
lean_inc(v_E_5878_);
lean_inc(v_W_5877_);
lean_inc(v_w_5876_);
lean_inc(v_q_5875_);
lean_inc(v_Q_5874_);
lean_inc(v_d_5873_);
lean_inc(v_L_5872_);
lean_inc(v_M_5871_);
lean_inc(v_D_5870_);
lean_inc(v_Y_5869_);
lean_inc(v_u_5868_);
lean_inc(v_y_5867_);
lean_inc(v_G_5866_);
lean_dec(v_date_4647_);
v___x_5903_ = lean_box(0);
v_isShared_5904_ = v_isSharedCheck_5911_;
goto v_resetjp_5902_;
}
v_resetjp_5902_:
{
lean_object* v___x_5906_; 
if (v_isShared_5865_ == 0)
{
lean_ctor_set_tag(v___x_5864_, 1);
lean_ctor_set(v___x_5864_, 0, v_data_4649_);
v___x_5906_ = v___x_5864_;
goto v_reusejp_5905_;
}
else
{
lean_object* v_reuseFailAlloc_5910_; 
v_reuseFailAlloc_5910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5910_, 0, v_data_4649_);
v___x_5906_ = v_reuseFailAlloc_5910_;
goto v_reusejp_5905_;
}
v_reusejp_5905_:
{
lean_object* v___x_5908_; 
if (v_isShared_5904_ == 0)
{
lean_ctor_set(v___x_5903_, 24, v___x_5906_);
v___x_5908_ = v___x_5903_;
goto v_reusejp_5907_;
}
else
{
lean_object* v_reuseFailAlloc_5909_; 
v_reuseFailAlloc_5909_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5909_, 0, v_G_5866_);
lean_ctor_set(v_reuseFailAlloc_5909_, 1, v_y_5867_);
lean_ctor_set(v_reuseFailAlloc_5909_, 2, v_u_5868_);
lean_ctor_set(v_reuseFailAlloc_5909_, 3, v_Y_5869_);
lean_ctor_set(v_reuseFailAlloc_5909_, 4, v_D_5870_);
lean_ctor_set(v_reuseFailAlloc_5909_, 5, v_M_5871_);
lean_ctor_set(v_reuseFailAlloc_5909_, 6, v_L_5872_);
lean_ctor_set(v_reuseFailAlloc_5909_, 7, v_d_5873_);
lean_ctor_set(v_reuseFailAlloc_5909_, 8, v_Q_5874_);
lean_ctor_set(v_reuseFailAlloc_5909_, 9, v_q_5875_);
lean_ctor_set(v_reuseFailAlloc_5909_, 10, v_w_5876_);
lean_ctor_set(v_reuseFailAlloc_5909_, 11, v_W_5877_);
lean_ctor_set(v_reuseFailAlloc_5909_, 12, v_E_5878_);
lean_ctor_set(v_reuseFailAlloc_5909_, 13, v_e_5879_);
lean_ctor_set(v_reuseFailAlloc_5909_, 14, v_c_5880_);
lean_ctor_set(v_reuseFailAlloc_5909_, 15, v_F_5881_);
lean_ctor_set(v_reuseFailAlloc_5909_, 16, v_a_5882_);
lean_ctor_set(v_reuseFailAlloc_5909_, 17, v_b_5883_);
lean_ctor_set(v_reuseFailAlloc_5909_, 18, v_B_5884_);
lean_ctor_set(v_reuseFailAlloc_5909_, 19, v_h_5885_);
lean_ctor_set(v_reuseFailAlloc_5909_, 20, v_K_5886_);
lean_ctor_set(v_reuseFailAlloc_5909_, 21, v_k_5887_);
lean_ctor_set(v_reuseFailAlloc_5909_, 22, v_H_5888_);
lean_ctor_set(v_reuseFailAlloc_5909_, 23, v_m_5889_);
lean_ctor_set(v_reuseFailAlloc_5909_, 24, v___x_5906_);
lean_ctor_set(v_reuseFailAlloc_5909_, 25, v_S_5890_);
lean_ctor_set(v_reuseFailAlloc_5909_, 26, v_A_5891_);
lean_ctor_set(v_reuseFailAlloc_5909_, 27, v_n_5892_);
lean_ctor_set(v_reuseFailAlloc_5909_, 28, v_N_5893_);
lean_ctor_set(v_reuseFailAlloc_5909_, 29, v_V_5894_);
lean_ctor_set(v_reuseFailAlloc_5909_, 30, v_z_5895_);
lean_ctor_set(v_reuseFailAlloc_5909_, 31, v_zabbrev_5896_);
lean_ctor_set(v_reuseFailAlloc_5909_, 32, v_v_5897_);
lean_ctor_set(v_reuseFailAlloc_5909_, 33, v_O_5898_);
lean_ctor_set(v_reuseFailAlloc_5909_, 34, v_X_5899_);
lean_ctor_set(v_reuseFailAlloc_5909_, 35, v_x_5900_);
lean_ctor_set(v_reuseFailAlloc_5909_, 36, v_Z_5901_);
v___x_5908_ = v_reuseFailAlloc_5909_;
goto v_reusejp_5907_;
}
v_reusejp_5907_:
{
return v___x_5908_;
}
}
}
}
}
case 25:
{
lean_object* v___x_5916_; uint8_t v_isShared_5917_; uint8_t v_isSharedCheck_5965_; 
v_isSharedCheck_5965_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_5965_ == 0)
{
lean_object* v_unused_5966_; 
v_unused_5966_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_5966_);
v___x_5916_ = v_modifier_4648_;
v_isShared_5917_ = v_isSharedCheck_5965_;
goto v_resetjp_5915_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_5916_ = lean_box(0);
v_isShared_5917_ = v_isSharedCheck_5965_;
goto v_resetjp_5915_;
}
v_resetjp_5915_:
{
lean_object* v_G_5918_; lean_object* v_y_5919_; lean_object* v_u_5920_; lean_object* v_Y_5921_; lean_object* v_D_5922_; lean_object* v_M_5923_; lean_object* v_L_5924_; lean_object* v_d_5925_; lean_object* v_Q_5926_; lean_object* v_q_5927_; lean_object* v_w_5928_; lean_object* v_W_5929_; lean_object* v_E_5930_; lean_object* v_e_5931_; lean_object* v_c_5932_; lean_object* v_F_5933_; lean_object* v_a_5934_; lean_object* v_b_5935_; lean_object* v_B_5936_; lean_object* v_h_5937_; lean_object* v_K_5938_; lean_object* v_k_5939_; lean_object* v_H_5940_; lean_object* v_m_5941_; lean_object* v_s_5942_; lean_object* v_A_5943_; lean_object* v_n_5944_; lean_object* v_N_5945_; lean_object* v_V_5946_; lean_object* v_z_5947_; lean_object* v_zabbrev_5948_; lean_object* v_v_5949_; lean_object* v_O_5950_; lean_object* v_X_5951_; lean_object* v_x_5952_; lean_object* v_Z_5953_; lean_object* v___x_5955_; uint8_t v_isShared_5956_; uint8_t v_isSharedCheck_5963_; 
v_G_5918_ = lean_ctor_get(v_date_4647_, 0);
v_y_5919_ = lean_ctor_get(v_date_4647_, 1);
v_u_5920_ = lean_ctor_get(v_date_4647_, 2);
v_Y_5921_ = lean_ctor_get(v_date_4647_, 3);
v_D_5922_ = lean_ctor_get(v_date_4647_, 4);
v_M_5923_ = lean_ctor_get(v_date_4647_, 5);
v_L_5924_ = lean_ctor_get(v_date_4647_, 6);
v_d_5925_ = lean_ctor_get(v_date_4647_, 7);
v_Q_5926_ = lean_ctor_get(v_date_4647_, 8);
v_q_5927_ = lean_ctor_get(v_date_4647_, 9);
v_w_5928_ = lean_ctor_get(v_date_4647_, 10);
v_W_5929_ = lean_ctor_get(v_date_4647_, 11);
v_E_5930_ = lean_ctor_get(v_date_4647_, 12);
v_e_5931_ = lean_ctor_get(v_date_4647_, 13);
v_c_5932_ = lean_ctor_get(v_date_4647_, 14);
v_F_5933_ = lean_ctor_get(v_date_4647_, 15);
v_a_5934_ = lean_ctor_get(v_date_4647_, 16);
v_b_5935_ = lean_ctor_get(v_date_4647_, 17);
v_B_5936_ = lean_ctor_get(v_date_4647_, 18);
v_h_5937_ = lean_ctor_get(v_date_4647_, 19);
v_K_5938_ = lean_ctor_get(v_date_4647_, 20);
v_k_5939_ = lean_ctor_get(v_date_4647_, 21);
v_H_5940_ = lean_ctor_get(v_date_4647_, 22);
v_m_5941_ = lean_ctor_get(v_date_4647_, 23);
v_s_5942_ = lean_ctor_get(v_date_4647_, 24);
v_A_5943_ = lean_ctor_get(v_date_4647_, 26);
v_n_5944_ = lean_ctor_get(v_date_4647_, 27);
v_N_5945_ = lean_ctor_get(v_date_4647_, 28);
v_V_5946_ = lean_ctor_get(v_date_4647_, 29);
v_z_5947_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_5948_ = lean_ctor_get(v_date_4647_, 31);
v_v_5949_ = lean_ctor_get(v_date_4647_, 32);
v_O_5950_ = lean_ctor_get(v_date_4647_, 33);
v_X_5951_ = lean_ctor_get(v_date_4647_, 34);
v_x_5952_ = lean_ctor_get(v_date_4647_, 35);
v_Z_5953_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_5963_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_5963_ == 0)
{
lean_object* v_unused_5964_; 
v_unused_5964_ = lean_ctor_get(v_date_4647_, 25);
lean_dec(v_unused_5964_);
v___x_5955_ = v_date_4647_;
v_isShared_5956_ = v_isSharedCheck_5963_;
goto v_resetjp_5954_;
}
else
{
lean_inc(v_Z_5953_);
lean_inc(v_x_5952_);
lean_inc(v_X_5951_);
lean_inc(v_O_5950_);
lean_inc(v_v_5949_);
lean_inc(v_zabbrev_5948_);
lean_inc(v_z_5947_);
lean_inc(v_V_5946_);
lean_inc(v_N_5945_);
lean_inc(v_n_5944_);
lean_inc(v_A_5943_);
lean_inc(v_s_5942_);
lean_inc(v_m_5941_);
lean_inc(v_H_5940_);
lean_inc(v_k_5939_);
lean_inc(v_K_5938_);
lean_inc(v_h_5937_);
lean_inc(v_B_5936_);
lean_inc(v_b_5935_);
lean_inc(v_a_5934_);
lean_inc(v_F_5933_);
lean_inc(v_c_5932_);
lean_inc(v_e_5931_);
lean_inc(v_E_5930_);
lean_inc(v_W_5929_);
lean_inc(v_w_5928_);
lean_inc(v_q_5927_);
lean_inc(v_Q_5926_);
lean_inc(v_d_5925_);
lean_inc(v_L_5924_);
lean_inc(v_M_5923_);
lean_inc(v_D_5922_);
lean_inc(v_Y_5921_);
lean_inc(v_u_5920_);
lean_inc(v_y_5919_);
lean_inc(v_G_5918_);
lean_dec(v_date_4647_);
v___x_5955_ = lean_box(0);
v_isShared_5956_ = v_isSharedCheck_5963_;
goto v_resetjp_5954_;
}
v_resetjp_5954_:
{
lean_object* v___x_5958_; 
if (v_isShared_5917_ == 0)
{
lean_ctor_set_tag(v___x_5916_, 1);
lean_ctor_set(v___x_5916_, 0, v_data_4649_);
v___x_5958_ = v___x_5916_;
goto v_reusejp_5957_;
}
else
{
lean_object* v_reuseFailAlloc_5962_; 
v_reuseFailAlloc_5962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5962_, 0, v_data_4649_);
v___x_5958_ = v_reuseFailAlloc_5962_;
goto v_reusejp_5957_;
}
v_reusejp_5957_:
{
lean_object* v___x_5960_; 
if (v_isShared_5956_ == 0)
{
lean_ctor_set(v___x_5955_, 25, v___x_5958_);
v___x_5960_ = v___x_5955_;
goto v_reusejp_5959_;
}
else
{
lean_object* v_reuseFailAlloc_5961_; 
v_reuseFailAlloc_5961_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5961_, 0, v_G_5918_);
lean_ctor_set(v_reuseFailAlloc_5961_, 1, v_y_5919_);
lean_ctor_set(v_reuseFailAlloc_5961_, 2, v_u_5920_);
lean_ctor_set(v_reuseFailAlloc_5961_, 3, v_Y_5921_);
lean_ctor_set(v_reuseFailAlloc_5961_, 4, v_D_5922_);
lean_ctor_set(v_reuseFailAlloc_5961_, 5, v_M_5923_);
lean_ctor_set(v_reuseFailAlloc_5961_, 6, v_L_5924_);
lean_ctor_set(v_reuseFailAlloc_5961_, 7, v_d_5925_);
lean_ctor_set(v_reuseFailAlloc_5961_, 8, v_Q_5926_);
lean_ctor_set(v_reuseFailAlloc_5961_, 9, v_q_5927_);
lean_ctor_set(v_reuseFailAlloc_5961_, 10, v_w_5928_);
lean_ctor_set(v_reuseFailAlloc_5961_, 11, v_W_5929_);
lean_ctor_set(v_reuseFailAlloc_5961_, 12, v_E_5930_);
lean_ctor_set(v_reuseFailAlloc_5961_, 13, v_e_5931_);
lean_ctor_set(v_reuseFailAlloc_5961_, 14, v_c_5932_);
lean_ctor_set(v_reuseFailAlloc_5961_, 15, v_F_5933_);
lean_ctor_set(v_reuseFailAlloc_5961_, 16, v_a_5934_);
lean_ctor_set(v_reuseFailAlloc_5961_, 17, v_b_5935_);
lean_ctor_set(v_reuseFailAlloc_5961_, 18, v_B_5936_);
lean_ctor_set(v_reuseFailAlloc_5961_, 19, v_h_5937_);
lean_ctor_set(v_reuseFailAlloc_5961_, 20, v_K_5938_);
lean_ctor_set(v_reuseFailAlloc_5961_, 21, v_k_5939_);
lean_ctor_set(v_reuseFailAlloc_5961_, 22, v_H_5940_);
lean_ctor_set(v_reuseFailAlloc_5961_, 23, v_m_5941_);
lean_ctor_set(v_reuseFailAlloc_5961_, 24, v_s_5942_);
lean_ctor_set(v_reuseFailAlloc_5961_, 25, v___x_5958_);
lean_ctor_set(v_reuseFailAlloc_5961_, 26, v_A_5943_);
lean_ctor_set(v_reuseFailAlloc_5961_, 27, v_n_5944_);
lean_ctor_set(v_reuseFailAlloc_5961_, 28, v_N_5945_);
lean_ctor_set(v_reuseFailAlloc_5961_, 29, v_V_5946_);
lean_ctor_set(v_reuseFailAlloc_5961_, 30, v_z_5947_);
lean_ctor_set(v_reuseFailAlloc_5961_, 31, v_zabbrev_5948_);
lean_ctor_set(v_reuseFailAlloc_5961_, 32, v_v_5949_);
lean_ctor_set(v_reuseFailAlloc_5961_, 33, v_O_5950_);
lean_ctor_set(v_reuseFailAlloc_5961_, 34, v_X_5951_);
lean_ctor_set(v_reuseFailAlloc_5961_, 35, v_x_5952_);
lean_ctor_set(v_reuseFailAlloc_5961_, 36, v_Z_5953_);
v___x_5960_ = v_reuseFailAlloc_5961_;
goto v_reusejp_5959_;
}
v_reusejp_5959_:
{
return v___x_5960_;
}
}
}
}
}
case 26:
{
lean_object* v___x_5968_; uint8_t v_isShared_5969_; uint8_t v_isSharedCheck_6017_; 
v_isSharedCheck_6017_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_6017_ == 0)
{
lean_object* v_unused_6018_; 
v_unused_6018_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_6018_);
v___x_5968_ = v_modifier_4648_;
v_isShared_5969_ = v_isSharedCheck_6017_;
goto v_resetjp_5967_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_5968_ = lean_box(0);
v_isShared_5969_ = v_isSharedCheck_6017_;
goto v_resetjp_5967_;
}
v_resetjp_5967_:
{
lean_object* v_G_5970_; lean_object* v_y_5971_; lean_object* v_u_5972_; lean_object* v_Y_5973_; lean_object* v_D_5974_; lean_object* v_M_5975_; lean_object* v_L_5976_; lean_object* v_d_5977_; lean_object* v_Q_5978_; lean_object* v_q_5979_; lean_object* v_w_5980_; lean_object* v_W_5981_; lean_object* v_E_5982_; lean_object* v_e_5983_; lean_object* v_c_5984_; lean_object* v_F_5985_; lean_object* v_a_5986_; lean_object* v_b_5987_; lean_object* v_B_5988_; lean_object* v_h_5989_; lean_object* v_K_5990_; lean_object* v_k_5991_; lean_object* v_H_5992_; lean_object* v_m_5993_; lean_object* v_s_5994_; lean_object* v_S_5995_; lean_object* v_n_5996_; lean_object* v_N_5997_; lean_object* v_V_5998_; lean_object* v_z_5999_; lean_object* v_zabbrev_6000_; lean_object* v_v_6001_; lean_object* v_O_6002_; lean_object* v_X_6003_; lean_object* v_x_6004_; lean_object* v_Z_6005_; lean_object* v___x_6007_; uint8_t v_isShared_6008_; uint8_t v_isSharedCheck_6015_; 
v_G_5970_ = lean_ctor_get(v_date_4647_, 0);
v_y_5971_ = lean_ctor_get(v_date_4647_, 1);
v_u_5972_ = lean_ctor_get(v_date_4647_, 2);
v_Y_5973_ = lean_ctor_get(v_date_4647_, 3);
v_D_5974_ = lean_ctor_get(v_date_4647_, 4);
v_M_5975_ = lean_ctor_get(v_date_4647_, 5);
v_L_5976_ = lean_ctor_get(v_date_4647_, 6);
v_d_5977_ = lean_ctor_get(v_date_4647_, 7);
v_Q_5978_ = lean_ctor_get(v_date_4647_, 8);
v_q_5979_ = lean_ctor_get(v_date_4647_, 9);
v_w_5980_ = lean_ctor_get(v_date_4647_, 10);
v_W_5981_ = lean_ctor_get(v_date_4647_, 11);
v_E_5982_ = lean_ctor_get(v_date_4647_, 12);
v_e_5983_ = lean_ctor_get(v_date_4647_, 13);
v_c_5984_ = lean_ctor_get(v_date_4647_, 14);
v_F_5985_ = lean_ctor_get(v_date_4647_, 15);
v_a_5986_ = lean_ctor_get(v_date_4647_, 16);
v_b_5987_ = lean_ctor_get(v_date_4647_, 17);
v_B_5988_ = lean_ctor_get(v_date_4647_, 18);
v_h_5989_ = lean_ctor_get(v_date_4647_, 19);
v_K_5990_ = lean_ctor_get(v_date_4647_, 20);
v_k_5991_ = lean_ctor_get(v_date_4647_, 21);
v_H_5992_ = lean_ctor_get(v_date_4647_, 22);
v_m_5993_ = lean_ctor_get(v_date_4647_, 23);
v_s_5994_ = lean_ctor_get(v_date_4647_, 24);
v_S_5995_ = lean_ctor_get(v_date_4647_, 25);
v_n_5996_ = lean_ctor_get(v_date_4647_, 27);
v_N_5997_ = lean_ctor_get(v_date_4647_, 28);
v_V_5998_ = lean_ctor_get(v_date_4647_, 29);
v_z_5999_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_6000_ = lean_ctor_get(v_date_4647_, 31);
v_v_6001_ = lean_ctor_get(v_date_4647_, 32);
v_O_6002_ = lean_ctor_get(v_date_4647_, 33);
v_X_6003_ = lean_ctor_get(v_date_4647_, 34);
v_x_6004_ = lean_ctor_get(v_date_4647_, 35);
v_Z_6005_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_6015_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_6015_ == 0)
{
lean_object* v_unused_6016_; 
v_unused_6016_ = lean_ctor_get(v_date_4647_, 26);
lean_dec(v_unused_6016_);
v___x_6007_ = v_date_4647_;
v_isShared_6008_ = v_isSharedCheck_6015_;
goto v_resetjp_6006_;
}
else
{
lean_inc(v_Z_6005_);
lean_inc(v_x_6004_);
lean_inc(v_X_6003_);
lean_inc(v_O_6002_);
lean_inc(v_v_6001_);
lean_inc(v_zabbrev_6000_);
lean_inc(v_z_5999_);
lean_inc(v_V_5998_);
lean_inc(v_N_5997_);
lean_inc(v_n_5996_);
lean_inc(v_S_5995_);
lean_inc(v_s_5994_);
lean_inc(v_m_5993_);
lean_inc(v_H_5992_);
lean_inc(v_k_5991_);
lean_inc(v_K_5990_);
lean_inc(v_h_5989_);
lean_inc(v_B_5988_);
lean_inc(v_b_5987_);
lean_inc(v_a_5986_);
lean_inc(v_F_5985_);
lean_inc(v_c_5984_);
lean_inc(v_e_5983_);
lean_inc(v_E_5982_);
lean_inc(v_W_5981_);
lean_inc(v_w_5980_);
lean_inc(v_q_5979_);
lean_inc(v_Q_5978_);
lean_inc(v_d_5977_);
lean_inc(v_L_5976_);
lean_inc(v_M_5975_);
lean_inc(v_D_5974_);
lean_inc(v_Y_5973_);
lean_inc(v_u_5972_);
lean_inc(v_y_5971_);
lean_inc(v_G_5970_);
lean_dec(v_date_4647_);
v___x_6007_ = lean_box(0);
v_isShared_6008_ = v_isSharedCheck_6015_;
goto v_resetjp_6006_;
}
v_resetjp_6006_:
{
lean_object* v___x_6010_; 
if (v_isShared_5969_ == 0)
{
lean_ctor_set_tag(v___x_5968_, 1);
lean_ctor_set(v___x_5968_, 0, v_data_4649_);
v___x_6010_ = v___x_5968_;
goto v_reusejp_6009_;
}
else
{
lean_object* v_reuseFailAlloc_6014_; 
v_reuseFailAlloc_6014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6014_, 0, v_data_4649_);
v___x_6010_ = v_reuseFailAlloc_6014_;
goto v_reusejp_6009_;
}
v_reusejp_6009_:
{
lean_object* v___x_6012_; 
if (v_isShared_6008_ == 0)
{
lean_ctor_set(v___x_6007_, 26, v___x_6010_);
v___x_6012_ = v___x_6007_;
goto v_reusejp_6011_;
}
else
{
lean_object* v_reuseFailAlloc_6013_; 
v_reuseFailAlloc_6013_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6013_, 0, v_G_5970_);
lean_ctor_set(v_reuseFailAlloc_6013_, 1, v_y_5971_);
lean_ctor_set(v_reuseFailAlloc_6013_, 2, v_u_5972_);
lean_ctor_set(v_reuseFailAlloc_6013_, 3, v_Y_5973_);
lean_ctor_set(v_reuseFailAlloc_6013_, 4, v_D_5974_);
lean_ctor_set(v_reuseFailAlloc_6013_, 5, v_M_5975_);
lean_ctor_set(v_reuseFailAlloc_6013_, 6, v_L_5976_);
lean_ctor_set(v_reuseFailAlloc_6013_, 7, v_d_5977_);
lean_ctor_set(v_reuseFailAlloc_6013_, 8, v_Q_5978_);
lean_ctor_set(v_reuseFailAlloc_6013_, 9, v_q_5979_);
lean_ctor_set(v_reuseFailAlloc_6013_, 10, v_w_5980_);
lean_ctor_set(v_reuseFailAlloc_6013_, 11, v_W_5981_);
lean_ctor_set(v_reuseFailAlloc_6013_, 12, v_E_5982_);
lean_ctor_set(v_reuseFailAlloc_6013_, 13, v_e_5983_);
lean_ctor_set(v_reuseFailAlloc_6013_, 14, v_c_5984_);
lean_ctor_set(v_reuseFailAlloc_6013_, 15, v_F_5985_);
lean_ctor_set(v_reuseFailAlloc_6013_, 16, v_a_5986_);
lean_ctor_set(v_reuseFailAlloc_6013_, 17, v_b_5987_);
lean_ctor_set(v_reuseFailAlloc_6013_, 18, v_B_5988_);
lean_ctor_set(v_reuseFailAlloc_6013_, 19, v_h_5989_);
lean_ctor_set(v_reuseFailAlloc_6013_, 20, v_K_5990_);
lean_ctor_set(v_reuseFailAlloc_6013_, 21, v_k_5991_);
lean_ctor_set(v_reuseFailAlloc_6013_, 22, v_H_5992_);
lean_ctor_set(v_reuseFailAlloc_6013_, 23, v_m_5993_);
lean_ctor_set(v_reuseFailAlloc_6013_, 24, v_s_5994_);
lean_ctor_set(v_reuseFailAlloc_6013_, 25, v_S_5995_);
lean_ctor_set(v_reuseFailAlloc_6013_, 26, v___x_6010_);
lean_ctor_set(v_reuseFailAlloc_6013_, 27, v_n_5996_);
lean_ctor_set(v_reuseFailAlloc_6013_, 28, v_N_5997_);
lean_ctor_set(v_reuseFailAlloc_6013_, 29, v_V_5998_);
lean_ctor_set(v_reuseFailAlloc_6013_, 30, v_z_5999_);
lean_ctor_set(v_reuseFailAlloc_6013_, 31, v_zabbrev_6000_);
lean_ctor_set(v_reuseFailAlloc_6013_, 32, v_v_6001_);
lean_ctor_set(v_reuseFailAlloc_6013_, 33, v_O_6002_);
lean_ctor_set(v_reuseFailAlloc_6013_, 34, v_X_6003_);
lean_ctor_set(v_reuseFailAlloc_6013_, 35, v_x_6004_);
lean_ctor_set(v_reuseFailAlloc_6013_, 36, v_Z_6005_);
v___x_6012_ = v_reuseFailAlloc_6013_;
goto v_reusejp_6011_;
}
v_reusejp_6011_:
{
return v___x_6012_;
}
}
}
}
}
case 27:
{
lean_object* v___x_6020_; uint8_t v_isShared_6021_; uint8_t v_isSharedCheck_6069_; 
v_isSharedCheck_6069_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_6069_ == 0)
{
lean_object* v_unused_6070_; 
v_unused_6070_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_6070_);
v___x_6020_ = v_modifier_4648_;
v_isShared_6021_ = v_isSharedCheck_6069_;
goto v_resetjp_6019_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_6020_ = lean_box(0);
v_isShared_6021_ = v_isSharedCheck_6069_;
goto v_resetjp_6019_;
}
v_resetjp_6019_:
{
lean_object* v_G_6022_; lean_object* v_y_6023_; lean_object* v_u_6024_; lean_object* v_Y_6025_; lean_object* v_D_6026_; lean_object* v_M_6027_; lean_object* v_L_6028_; lean_object* v_d_6029_; lean_object* v_Q_6030_; lean_object* v_q_6031_; lean_object* v_w_6032_; lean_object* v_W_6033_; lean_object* v_E_6034_; lean_object* v_e_6035_; lean_object* v_c_6036_; lean_object* v_F_6037_; lean_object* v_a_6038_; lean_object* v_b_6039_; lean_object* v_B_6040_; lean_object* v_h_6041_; lean_object* v_K_6042_; lean_object* v_k_6043_; lean_object* v_H_6044_; lean_object* v_m_6045_; lean_object* v_s_6046_; lean_object* v_S_6047_; lean_object* v_A_6048_; lean_object* v_N_6049_; lean_object* v_V_6050_; lean_object* v_z_6051_; lean_object* v_zabbrev_6052_; lean_object* v_v_6053_; lean_object* v_O_6054_; lean_object* v_X_6055_; lean_object* v_x_6056_; lean_object* v_Z_6057_; lean_object* v___x_6059_; uint8_t v_isShared_6060_; uint8_t v_isSharedCheck_6067_; 
v_G_6022_ = lean_ctor_get(v_date_4647_, 0);
v_y_6023_ = lean_ctor_get(v_date_4647_, 1);
v_u_6024_ = lean_ctor_get(v_date_4647_, 2);
v_Y_6025_ = lean_ctor_get(v_date_4647_, 3);
v_D_6026_ = lean_ctor_get(v_date_4647_, 4);
v_M_6027_ = lean_ctor_get(v_date_4647_, 5);
v_L_6028_ = lean_ctor_get(v_date_4647_, 6);
v_d_6029_ = lean_ctor_get(v_date_4647_, 7);
v_Q_6030_ = lean_ctor_get(v_date_4647_, 8);
v_q_6031_ = lean_ctor_get(v_date_4647_, 9);
v_w_6032_ = lean_ctor_get(v_date_4647_, 10);
v_W_6033_ = lean_ctor_get(v_date_4647_, 11);
v_E_6034_ = lean_ctor_get(v_date_4647_, 12);
v_e_6035_ = lean_ctor_get(v_date_4647_, 13);
v_c_6036_ = lean_ctor_get(v_date_4647_, 14);
v_F_6037_ = lean_ctor_get(v_date_4647_, 15);
v_a_6038_ = lean_ctor_get(v_date_4647_, 16);
v_b_6039_ = lean_ctor_get(v_date_4647_, 17);
v_B_6040_ = lean_ctor_get(v_date_4647_, 18);
v_h_6041_ = lean_ctor_get(v_date_4647_, 19);
v_K_6042_ = lean_ctor_get(v_date_4647_, 20);
v_k_6043_ = lean_ctor_get(v_date_4647_, 21);
v_H_6044_ = lean_ctor_get(v_date_4647_, 22);
v_m_6045_ = lean_ctor_get(v_date_4647_, 23);
v_s_6046_ = lean_ctor_get(v_date_4647_, 24);
v_S_6047_ = lean_ctor_get(v_date_4647_, 25);
v_A_6048_ = lean_ctor_get(v_date_4647_, 26);
v_N_6049_ = lean_ctor_get(v_date_4647_, 28);
v_V_6050_ = lean_ctor_get(v_date_4647_, 29);
v_z_6051_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_6052_ = lean_ctor_get(v_date_4647_, 31);
v_v_6053_ = lean_ctor_get(v_date_4647_, 32);
v_O_6054_ = lean_ctor_get(v_date_4647_, 33);
v_X_6055_ = lean_ctor_get(v_date_4647_, 34);
v_x_6056_ = lean_ctor_get(v_date_4647_, 35);
v_Z_6057_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_6067_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_6067_ == 0)
{
lean_object* v_unused_6068_; 
v_unused_6068_ = lean_ctor_get(v_date_4647_, 27);
lean_dec(v_unused_6068_);
v___x_6059_ = v_date_4647_;
v_isShared_6060_ = v_isSharedCheck_6067_;
goto v_resetjp_6058_;
}
else
{
lean_inc(v_Z_6057_);
lean_inc(v_x_6056_);
lean_inc(v_X_6055_);
lean_inc(v_O_6054_);
lean_inc(v_v_6053_);
lean_inc(v_zabbrev_6052_);
lean_inc(v_z_6051_);
lean_inc(v_V_6050_);
lean_inc(v_N_6049_);
lean_inc(v_A_6048_);
lean_inc(v_S_6047_);
lean_inc(v_s_6046_);
lean_inc(v_m_6045_);
lean_inc(v_H_6044_);
lean_inc(v_k_6043_);
lean_inc(v_K_6042_);
lean_inc(v_h_6041_);
lean_inc(v_B_6040_);
lean_inc(v_b_6039_);
lean_inc(v_a_6038_);
lean_inc(v_F_6037_);
lean_inc(v_c_6036_);
lean_inc(v_e_6035_);
lean_inc(v_E_6034_);
lean_inc(v_W_6033_);
lean_inc(v_w_6032_);
lean_inc(v_q_6031_);
lean_inc(v_Q_6030_);
lean_inc(v_d_6029_);
lean_inc(v_L_6028_);
lean_inc(v_M_6027_);
lean_inc(v_D_6026_);
lean_inc(v_Y_6025_);
lean_inc(v_u_6024_);
lean_inc(v_y_6023_);
lean_inc(v_G_6022_);
lean_dec(v_date_4647_);
v___x_6059_ = lean_box(0);
v_isShared_6060_ = v_isSharedCheck_6067_;
goto v_resetjp_6058_;
}
v_resetjp_6058_:
{
lean_object* v___x_6062_; 
if (v_isShared_6021_ == 0)
{
lean_ctor_set_tag(v___x_6020_, 1);
lean_ctor_set(v___x_6020_, 0, v_data_4649_);
v___x_6062_ = v___x_6020_;
goto v_reusejp_6061_;
}
else
{
lean_object* v_reuseFailAlloc_6066_; 
v_reuseFailAlloc_6066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6066_, 0, v_data_4649_);
v___x_6062_ = v_reuseFailAlloc_6066_;
goto v_reusejp_6061_;
}
v_reusejp_6061_:
{
lean_object* v___x_6064_; 
if (v_isShared_6060_ == 0)
{
lean_ctor_set(v___x_6059_, 27, v___x_6062_);
v___x_6064_ = v___x_6059_;
goto v_reusejp_6063_;
}
else
{
lean_object* v_reuseFailAlloc_6065_; 
v_reuseFailAlloc_6065_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6065_, 0, v_G_6022_);
lean_ctor_set(v_reuseFailAlloc_6065_, 1, v_y_6023_);
lean_ctor_set(v_reuseFailAlloc_6065_, 2, v_u_6024_);
lean_ctor_set(v_reuseFailAlloc_6065_, 3, v_Y_6025_);
lean_ctor_set(v_reuseFailAlloc_6065_, 4, v_D_6026_);
lean_ctor_set(v_reuseFailAlloc_6065_, 5, v_M_6027_);
lean_ctor_set(v_reuseFailAlloc_6065_, 6, v_L_6028_);
lean_ctor_set(v_reuseFailAlloc_6065_, 7, v_d_6029_);
lean_ctor_set(v_reuseFailAlloc_6065_, 8, v_Q_6030_);
lean_ctor_set(v_reuseFailAlloc_6065_, 9, v_q_6031_);
lean_ctor_set(v_reuseFailAlloc_6065_, 10, v_w_6032_);
lean_ctor_set(v_reuseFailAlloc_6065_, 11, v_W_6033_);
lean_ctor_set(v_reuseFailAlloc_6065_, 12, v_E_6034_);
lean_ctor_set(v_reuseFailAlloc_6065_, 13, v_e_6035_);
lean_ctor_set(v_reuseFailAlloc_6065_, 14, v_c_6036_);
lean_ctor_set(v_reuseFailAlloc_6065_, 15, v_F_6037_);
lean_ctor_set(v_reuseFailAlloc_6065_, 16, v_a_6038_);
lean_ctor_set(v_reuseFailAlloc_6065_, 17, v_b_6039_);
lean_ctor_set(v_reuseFailAlloc_6065_, 18, v_B_6040_);
lean_ctor_set(v_reuseFailAlloc_6065_, 19, v_h_6041_);
lean_ctor_set(v_reuseFailAlloc_6065_, 20, v_K_6042_);
lean_ctor_set(v_reuseFailAlloc_6065_, 21, v_k_6043_);
lean_ctor_set(v_reuseFailAlloc_6065_, 22, v_H_6044_);
lean_ctor_set(v_reuseFailAlloc_6065_, 23, v_m_6045_);
lean_ctor_set(v_reuseFailAlloc_6065_, 24, v_s_6046_);
lean_ctor_set(v_reuseFailAlloc_6065_, 25, v_S_6047_);
lean_ctor_set(v_reuseFailAlloc_6065_, 26, v_A_6048_);
lean_ctor_set(v_reuseFailAlloc_6065_, 27, v___x_6062_);
lean_ctor_set(v_reuseFailAlloc_6065_, 28, v_N_6049_);
lean_ctor_set(v_reuseFailAlloc_6065_, 29, v_V_6050_);
lean_ctor_set(v_reuseFailAlloc_6065_, 30, v_z_6051_);
lean_ctor_set(v_reuseFailAlloc_6065_, 31, v_zabbrev_6052_);
lean_ctor_set(v_reuseFailAlloc_6065_, 32, v_v_6053_);
lean_ctor_set(v_reuseFailAlloc_6065_, 33, v_O_6054_);
lean_ctor_set(v_reuseFailAlloc_6065_, 34, v_X_6055_);
lean_ctor_set(v_reuseFailAlloc_6065_, 35, v_x_6056_);
lean_ctor_set(v_reuseFailAlloc_6065_, 36, v_Z_6057_);
v___x_6064_ = v_reuseFailAlloc_6065_;
goto v_reusejp_6063_;
}
v_reusejp_6063_:
{
return v___x_6064_;
}
}
}
}
}
case 28:
{
lean_object* v___x_6072_; uint8_t v_isShared_6073_; uint8_t v_isSharedCheck_6121_; 
v_isSharedCheck_6121_ = !lean_is_exclusive(v_modifier_4648_);
if (v_isSharedCheck_6121_ == 0)
{
lean_object* v_unused_6122_; 
v_unused_6122_ = lean_ctor_get(v_modifier_4648_, 0);
lean_dec(v_unused_6122_);
v___x_6072_ = v_modifier_4648_;
v_isShared_6073_ = v_isSharedCheck_6121_;
goto v_resetjp_6071_;
}
else
{
lean_dec(v_modifier_4648_);
v___x_6072_ = lean_box(0);
v_isShared_6073_ = v_isSharedCheck_6121_;
goto v_resetjp_6071_;
}
v_resetjp_6071_:
{
lean_object* v_G_6074_; lean_object* v_y_6075_; lean_object* v_u_6076_; lean_object* v_Y_6077_; lean_object* v_D_6078_; lean_object* v_M_6079_; lean_object* v_L_6080_; lean_object* v_d_6081_; lean_object* v_Q_6082_; lean_object* v_q_6083_; lean_object* v_w_6084_; lean_object* v_W_6085_; lean_object* v_E_6086_; lean_object* v_e_6087_; lean_object* v_c_6088_; lean_object* v_F_6089_; lean_object* v_a_6090_; lean_object* v_b_6091_; lean_object* v_B_6092_; lean_object* v_h_6093_; lean_object* v_K_6094_; lean_object* v_k_6095_; lean_object* v_H_6096_; lean_object* v_m_6097_; lean_object* v_s_6098_; lean_object* v_S_6099_; lean_object* v_A_6100_; lean_object* v_n_6101_; lean_object* v_V_6102_; lean_object* v_z_6103_; lean_object* v_zabbrev_6104_; lean_object* v_v_6105_; lean_object* v_O_6106_; lean_object* v_X_6107_; lean_object* v_x_6108_; lean_object* v_Z_6109_; lean_object* v___x_6111_; uint8_t v_isShared_6112_; uint8_t v_isSharedCheck_6119_; 
v_G_6074_ = lean_ctor_get(v_date_4647_, 0);
v_y_6075_ = lean_ctor_get(v_date_4647_, 1);
v_u_6076_ = lean_ctor_get(v_date_4647_, 2);
v_Y_6077_ = lean_ctor_get(v_date_4647_, 3);
v_D_6078_ = lean_ctor_get(v_date_4647_, 4);
v_M_6079_ = lean_ctor_get(v_date_4647_, 5);
v_L_6080_ = lean_ctor_get(v_date_4647_, 6);
v_d_6081_ = lean_ctor_get(v_date_4647_, 7);
v_Q_6082_ = lean_ctor_get(v_date_4647_, 8);
v_q_6083_ = lean_ctor_get(v_date_4647_, 9);
v_w_6084_ = lean_ctor_get(v_date_4647_, 10);
v_W_6085_ = lean_ctor_get(v_date_4647_, 11);
v_E_6086_ = lean_ctor_get(v_date_4647_, 12);
v_e_6087_ = lean_ctor_get(v_date_4647_, 13);
v_c_6088_ = lean_ctor_get(v_date_4647_, 14);
v_F_6089_ = lean_ctor_get(v_date_4647_, 15);
v_a_6090_ = lean_ctor_get(v_date_4647_, 16);
v_b_6091_ = lean_ctor_get(v_date_4647_, 17);
v_B_6092_ = lean_ctor_get(v_date_4647_, 18);
v_h_6093_ = lean_ctor_get(v_date_4647_, 19);
v_K_6094_ = lean_ctor_get(v_date_4647_, 20);
v_k_6095_ = lean_ctor_get(v_date_4647_, 21);
v_H_6096_ = lean_ctor_get(v_date_4647_, 22);
v_m_6097_ = lean_ctor_get(v_date_4647_, 23);
v_s_6098_ = lean_ctor_get(v_date_4647_, 24);
v_S_6099_ = lean_ctor_get(v_date_4647_, 25);
v_A_6100_ = lean_ctor_get(v_date_4647_, 26);
v_n_6101_ = lean_ctor_get(v_date_4647_, 27);
v_V_6102_ = lean_ctor_get(v_date_4647_, 29);
v_z_6103_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_6104_ = lean_ctor_get(v_date_4647_, 31);
v_v_6105_ = lean_ctor_get(v_date_4647_, 32);
v_O_6106_ = lean_ctor_get(v_date_4647_, 33);
v_X_6107_ = lean_ctor_get(v_date_4647_, 34);
v_x_6108_ = lean_ctor_get(v_date_4647_, 35);
v_Z_6109_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_6119_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_6119_ == 0)
{
lean_object* v_unused_6120_; 
v_unused_6120_ = lean_ctor_get(v_date_4647_, 28);
lean_dec(v_unused_6120_);
v___x_6111_ = v_date_4647_;
v_isShared_6112_ = v_isSharedCheck_6119_;
goto v_resetjp_6110_;
}
else
{
lean_inc(v_Z_6109_);
lean_inc(v_x_6108_);
lean_inc(v_X_6107_);
lean_inc(v_O_6106_);
lean_inc(v_v_6105_);
lean_inc(v_zabbrev_6104_);
lean_inc(v_z_6103_);
lean_inc(v_V_6102_);
lean_inc(v_n_6101_);
lean_inc(v_A_6100_);
lean_inc(v_S_6099_);
lean_inc(v_s_6098_);
lean_inc(v_m_6097_);
lean_inc(v_H_6096_);
lean_inc(v_k_6095_);
lean_inc(v_K_6094_);
lean_inc(v_h_6093_);
lean_inc(v_B_6092_);
lean_inc(v_b_6091_);
lean_inc(v_a_6090_);
lean_inc(v_F_6089_);
lean_inc(v_c_6088_);
lean_inc(v_e_6087_);
lean_inc(v_E_6086_);
lean_inc(v_W_6085_);
lean_inc(v_w_6084_);
lean_inc(v_q_6083_);
lean_inc(v_Q_6082_);
lean_inc(v_d_6081_);
lean_inc(v_L_6080_);
lean_inc(v_M_6079_);
lean_inc(v_D_6078_);
lean_inc(v_Y_6077_);
lean_inc(v_u_6076_);
lean_inc(v_y_6075_);
lean_inc(v_G_6074_);
lean_dec(v_date_4647_);
v___x_6111_ = lean_box(0);
v_isShared_6112_ = v_isSharedCheck_6119_;
goto v_resetjp_6110_;
}
v_resetjp_6110_:
{
lean_object* v___x_6114_; 
if (v_isShared_6073_ == 0)
{
lean_ctor_set_tag(v___x_6072_, 1);
lean_ctor_set(v___x_6072_, 0, v_data_4649_);
v___x_6114_ = v___x_6072_;
goto v_reusejp_6113_;
}
else
{
lean_object* v_reuseFailAlloc_6118_; 
v_reuseFailAlloc_6118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6118_, 0, v_data_4649_);
v___x_6114_ = v_reuseFailAlloc_6118_;
goto v_reusejp_6113_;
}
v_reusejp_6113_:
{
lean_object* v___x_6116_; 
if (v_isShared_6112_ == 0)
{
lean_ctor_set(v___x_6111_, 28, v___x_6114_);
v___x_6116_ = v___x_6111_;
goto v_reusejp_6115_;
}
else
{
lean_object* v_reuseFailAlloc_6117_; 
v_reuseFailAlloc_6117_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6117_, 0, v_G_6074_);
lean_ctor_set(v_reuseFailAlloc_6117_, 1, v_y_6075_);
lean_ctor_set(v_reuseFailAlloc_6117_, 2, v_u_6076_);
lean_ctor_set(v_reuseFailAlloc_6117_, 3, v_Y_6077_);
lean_ctor_set(v_reuseFailAlloc_6117_, 4, v_D_6078_);
lean_ctor_set(v_reuseFailAlloc_6117_, 5, v_M_6079_);
lean_ctor_set(v_reuseFailAlloc_6117_, 6, v_L_6080_);
lean_ctor_set(v_reuseFailAlloc_6117_, 7, v_d_6081_);
lean_ctor_set(v_reuseFailAlloc_6117_, 8, v_Q_6082_);
lean_ctor_set(v_reuseFailAlloc_6117_, 9, v_q_6083_);
lean_ctor_set(v_reuseFailAlloc_6117_, 10, v_w_6084_);
lean_ctor_set(v_reuseFailAlloc_6117_, 11, v_W_6085_);
lean_ctor_set(v_reuseFailAlloc_6117_, 12, v_E_6086_);
lean_ctor_set(v_reuseFailAlloc_6117_, 13, v_e_6087_);
lean_ctor_set(v_reuseFailAlloc_6117_, 14, v_c_6088_);
lean_ctor_set(v_reuseFailAlloc_6117_, 15, v_F_6089_);
lean_ctor_set(v_reuseFailAlloc_6117_, 16, v_a_6090_);
lean_ctor_set(v_reuseFailAlloc_6117_, 17, v_b_6091_);
lean_ctor_set(v_reuseFailAlloc_6117_, 18, v_B_6092_);
lean_ctor_set(v_reuseFailAlloc_6117_, 19, v_h_6093_);
lean_ctor_set(v_reuseFailAlloc_6117_, 20, v_K_6094_);
lean_ctor_set(v_reuseFailAlloc_6117_, 21, v_k_6095_);
lean_ctor_set(v_reuseFailAlloc_6117_, 22, v_H_6096_);
lean_ctor_set(v_reuseFailAlloc_6117_, 23, v_m_6097_);
lean_ctor_set(v_reuseFailAlloc_6117_, 24, v_s_6098_);
lean_ctor_set(v_reuseFailAlloc_6117_, 25, v_S_6099_);
lean_ctor_set(v_reuseFailAlloc_6117_, 26, v_A_6100_);
lean_ctor_set(v_reuseFailAlloc_6117_, 27, v_n_6101_);
lean_ctor_set(v_reuseFailAlloc_6117_, 28, v___x_6114_);
lean_ctor_set(v_reuseFailAlloc_6117_, 29, v_V_6102_);
lean_ctor_set(v_reuseFailAlloc_6117_, 30, v_z_6103_);
lean_ctor_set(v_reuseFailAlloc_6117_, 31, v_zabbrev_6104_);
lean_ctor_set(v_reuseFailAlloc_6117_, 32, v_v_6105_);
lean_ctor_set(v_reuseFailAlloc_6117_, 33, v_O_6106_);
lean_ctor_set(v_reuseFailAlloc_6117_, 34, v_X_6107_);
lean_ctor_set(v_reuseFailAlloc_6117_, 35, v_x_6108_);
lean_ctor_set(v_reuseFailAlloc_6117_, 36, v_Z_6109_);
v___x_6116_ = v_reuseFailAlloc_6117_;
goto v_reusejp_6115_;
}
v_reusejp_6115_:
{
return v___x_6116_;
}
}
}
}
}
case 29:
{
lean_object* v_G_6123_; lean_object* v_y_6124_; lean_object* v_u_6125_; lean_object* v_Y_6126_; lean_object* v_D_6127_; lean_object* v_M_6128_; lean_object* v_L_6129_; lean_object* v_d_6130_; lean_object* v_Q_6131_; lean_object* v_q_6132_; lean_object* v_w_6133_; lean_object* v_W_6134_; lean_object* v_E_6135_; lean_object* v_e_6136_; lean_object* v_c_6137_; lean_object* v_F_6138_; lean_object* v_a_6139_; lean_object* v_b_6140_; lean_object* v_B_6141_; lean_object* v_h_6142_; lean_object* v_K_6143_; lean_object* v_k_6144_; lean_object* v_H_6145_; lean_object* v_m_6146_; lean_object* v_s_6147_; lean_object* v_S_6148_; lean_object* v_A_6149_; lean_object* v_n_6150_; lean_object* v_N_6151_; lean_object* v_z_6152_; lean_object* v_zabbrev_6153_; lean_object* v_v_6154_; lean_object* v_O_6155_; lean_object* v_X_6156_; lean_object* v_x_6157_; lean_object* v_Z_6158_; lean_object* v___x_6160_; uint8_t v_isShared_6161_; uint8_t v_isSharedCheck_6166_; 
lean_dec_ref_known(v_modifier_4648_, 0);
v_G_6123_ = lean_ctor_get(v_date_4647_, 0);
v_y_6124_ = lean_ctor_get(v_date_4647_, 1);
v_u_6125_ = lean_ctor_get(v_date_4647_, 2);
v_Y_6126_ = lean_ctor_get(v_date_4647_, 3);
v_D_6127_ = lean_ctor_get(v_date_4647_, 4);
v_M_6128_ = lean_ctor_get(v_date_4647_, 5);
v_L_6129_ = lean_ctor_get(v_date_4647_, 6);
v_d_6130_ = lean_ctor_get(v_date_4647_, 7);
v_Q_6131_ = lean_ctor_get(v_date_4647_, 8);
v_q_6132_ = lean_ctor_get(v_date_4647_, 9);
v_w_6133_ = lean_ctor_get(v_date_4647_, 10);
v_W_6134_ = lean_ctor_get(v_date_4647_, 11);
v_E_6135_ = lean_ctor_get(v_date_4647_, 12);
v_e_6136_ = lean_ctor_get(v_date_4647_, 13);
v_c_6137_ = lean_ctor_get(v_date_4647_, 14);
v_F_6138_ = lean_ctor_get(v_date_4647_, 15);
v_a_6139_ = lean_ctor_get(v_date_4647_, 16);
v_b_6140_ = lean_ctor_get(v_date_4647_, 17);
v_B_6141_ = lean_ctor_get(v_date_4647_, 18);
v_h_6142_ = lean_ctor_get(v_date_4647_, 19);
v_K_6143_ = lean_ctor_get(v_date_4647_, 20);
v_k_6144_ = lean_ctor_get(v_date_4647_, 21);
v_H_6145_ = lean_ctor_get(v_date_4647_, 22);
v_m_6146_ = lean_ctor_get(v_date_4647_, 23);
v_s_6147_ = lean_ctor_get(v_date_4647_, 24);
v_S_6148_ = lean_ctor_get(v_date_4647_, 25);
v_A_6149_ = lean_ctor_get(v_date_4647_, 26);
v_n_6150_ = lean_ctor_get(v_date_4647_, 27);
v_N_6151_ = lean_ctor_get(v_date_4647_, 28);
v_z_6152_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_6153_ = lean_ctor_get(v_date_4647_, 31);
v_v_6154_ = lean_ctor_get(v_date_4647_, 32);
v_O_6155_ = lean_ctor_get(v_date_4647_, 33);
v_X_6156_ = lean_ctor_get(v_date_4647_, 34);
v_x_6157_ = lean_ctor_get(v_date_4647_, 35);
v_Z_6158_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_6166_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_6166_ == 0)
{
lean_object* v_unused_6167_; 
v_unused_6167_ = lean_ctor_get(v_date_4647_, 29);
lean_dec(v_unused_6167_);
v___x_6160_ = v_date_4647_;
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
lean_inc(v_z_6152_);
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
lean_dec(v_date_4647_);
v___x_6160_ = lean_box(0);
v_isShared_6161_ = v_isSharedCheck_6166_;
goto v_resetjp_6159_;
}
v_resetjp_6159_:
{
lean_object* v___x_6162_; lean_object* v___x_6164_; 
v___x_6162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6162_, 0, v_data_4649_);
if (v_isShared_6161_ == 0)
{
lean_ctor_set(v___x_6160_, 29, v___x_6162_);
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
lean_ctor_set(v_reuseFailAlloc_6165_, 29, v___x_6162_);
lean_ctor_set(v_reuseFailAlloc_6165_, 30, v_z_6152_);
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
case 30:
{
uint8_t v_presentation_6168_; 
v_presentation_6168_ = lean_ctor_get_uint8(v_modifier_4648_, 0);
lean_dec_ref_known(v_modifier_4648_, 0);
if (v_presentation_6168_ == 0)
{
lean_object* v_G_6169_; lean_object* v_y_6170_; lean_object* v_u_6171_; lean_object* v_Y_6172_; lean_object* v_D_6173_; lean_object* v_M_6174_; lean_object* v_L_6175_; lean_object* v_d_6176_; lean_object* v_Q_6177_; lean_object* v_q_6178_; lean_object* v_w_6179_; lean_object* v_W_6180_; lean_object* v_E_6181_; lean_object* v_e_6182_; lean_object* v_c_6183_; lean_object* v_F_6184_; lean_object* v_a_6185_; lean_object* v_b_6186_; lean_object* v_B_6187_; lean_object* v_h_6188_; lean_object* v_K_6189_; lean_object* v_k_6190_; lean_object* v_H_6191_; lean_object* v_m_6192_; lean_object* v_s_6193_; lean_object* v_S_6194_; lean_object* v_A_6195_; lean_object* v_n_6196_; lean_object* v_N_6197_; lean_object* v_V_6198_; lean_object* v_z_6199_; lean_object* v_v_6200_; lean_object* v_O_6201_; lean_object* v_X_6202_; lean_object* v_x_6203_; lean_object* v_Z_6204_; lean_object* v___x_6206_; uint8_t v_isShared_6207_; uint8_t v_isSharedCheck_6212_; 
v_G_6169_ = lean_ctor_get(v_date_4647_, 0);
v_y_6170_ = lean_ctor_get(v_date_4647_, 1);
v_u_6171_ = lean_ctor_get(v_date_4647_, 2);
v_Y_6172_ = lean_ctor_get(v_date_4647_, 3);
v_D_6173_ = lean_ctor_get(v_date_4647_, 4);
v_M_6174_ = lean_ctor_get(v_date_4647_, 5);
v_L_6175_ = lean_ctor_get(v_date_4647_, 6);
v_d_6176_ = lean_ctor_get(v_date_4647_, 7);
v_Q_6177_ = lean_ctor_get(v_date_4647_, 8);
v_q_6178_ = lean_ctor_get(v_date_4647_, 9);
v_w_6179_ = lean_ctor_get(v_date_4647_, 10);
v_W_6180_ = lean_ctor_get(v_date_4647_, 11);
v_E_6181_ = lean_ctor_get(v_date_4647_, 12);
v_e_6182_ = lean_ctor_get(v_date_4647_, 13);
v_c_6183_ = lean_ctor_get(v_date_4647_, 14);
v_F_6184_ = lean_ctor_get(v_date_4647_, 15);
v_a_6185_ = lean_ctor_get(v_date_4647_, 16);
v_b_6186_ = lean_ctor_get(v_date_4647_, 17);
v_B_6187_ = lean_ctor_get(v_date_4647_, 18);
v_h_6188_ = lean_ctor_get(v_date_4647_, 19);
v_K_6189_ = lean_ctor_get(v_date_4647_, 20);
v_k_6190_ = lean_ctor_get(v_date_4647_, 21);
v_H_6191_ = lean_ctor_get(v_date_4647_, 22);
v_m_6192_ = lean_ctor_get(v_date_4647_, 23);
v_s_6193_ = lean_ctor_get(v_date_4647_, 24);
v_S_6194_ = lean_ctor_get(v_date_4647_, 25);
v_A_6195_ = lean_ctor_get(v_date_4647_, 26);
v_n_6196_ = lean_ctor_get(v_date_4647_, 27);
v_N_6197_ = lean_ctor_get(v_date_4647_, 28);
v_V_6198_ = lean_ctor_get(v_date_4647_, 29);
v_z_6199_ = lean_ctor_get(v_date_4647_, 30);
v_v_6200_ = lean_ctor_get(v_date_4647_, 32);
v_O_6201_ = lean_ctor_get(v_date_4647_, 33);
v_X_6202_ = lean_ctor_get(v_date_4647_, 34);
v_x_6203_ = lean_ctor_get(v_date_4647_, 35);
v_Z_6204_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_6212_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_6212_ == 0)
{
lean_object* v_unused_6213_; 
v_unused_6213_ = lean_ctor_get(v_date_4647_, 31);
lean_dec(v_unused_6213_);
v___x_6206_ = v_date_4647_;
v_isShared_6207_ = v_isSharedCheck_6212_;
goto v_resetjp_6205_;
}
else
{
lean_inc(v_Z_6204_);
lean_inc(v_x_6203_);
lean_inc(v_X_6202_);
lean_inc(v_O_6201_);
lean_inc(v_v_6200_);
lean_inc(v_z_6199_);
lean_inc(v_V_6198_);
lean_inc(v_N_6197_);
lean_inc(v_n_6196_);
lean_inc(v_A_6195_);
lean_inc(v_S_6194_);
lean_inc(v_s_6193_);
lean_inc(v_m_6192_);
lean_inc(v_H_6191_);
lean_inc(v_k_6190_);
lean_inc(v_K_6189_);
lean_inc(v_h_6188_);
lean_inc(v_B_6187_);
lean_inc(v_b_6186_);
lean_inc(v_a_6185_);
lean_inc(v_F_6184_);
lean_inc(v_c_6183_);
lean_inc(v_e_6182_);
lean_inc(v_E_6181_);
lean_inc(v_W_6180_);
lean_inc(v_w_6179_);
lean_inc(v_q_6178_);
lean_inc(v_Q_6177_);
lean_inc(v_d_6176_);
lean_inc(v_L_6175_);
lean_inc(v_M_6174_);
lean_inc(v_D_6173_);
lean_inc(v_Y_6172_);
lean_inc(v_u_6171_);
lean_inc(v_y_6170_);
lean_inc(v_G_6169_);
lean_dec(v_date_4647_);
v___x_6206_ = lean_box(0);
v_isShared_6207_ = v_isSharedCheck_6212_;
goto v_resetjp_6205_;
}
v_resetjp_6205_:
{
lean_object* v___x_6208_; lean_object* v___x_6210_; 
v___x_6208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6208_, 0, v_data_4649_);
if (v_isShared_6207_ == 0)
{
lean_ctor_set(v___x_6206_, 31, v___x_6208_);
v___x_6210_ = v___x_6206_;
goto v_reusejp_6209_;
}
else
{
lean_object* v_reuseFailAlloc_6211_; 
v_reuseFailAlloc_6211_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6211_, 0, v_G_6169_);
lean_ctor_set(v_reuseFailAlloc_6211_, 1, v_y_6170_);
lean_ctor_set(v_reuseFailAlloc_6211_, 2, v_u_6171_);
lean_ctor_set(v_reuseFailAlloc_6211_, 3, v_Y_6172_);
lean_ctor_set(v_reuseFailAlloc_6211_, 4, v_D_6173_);
lean_ctor_set(v_reuseFailAlloc_6211_, 5, v_M_6174_);
lean_ctor_set(v_reuseFailAlloc_6211_, 6, v_L_6175_);
lean_ctor_set(v_reuseFailAlloc_6211_, 7, v_d_6176_);
lean_ctor_set(v_reuseFailAlloc_6211_, 8, v_Q_6177_);
lean_ctor_set(v_reuseFailAlloc_6211_, 9, v_q_6178_);
lean_ctor_set(v_reuseFailAlloc_6211_, 10, v_w_6179_);
lean_ctor_set(v_reuseFailAlloc_6211_, 11, v_W_6180_);
lean_ctor_set(v_reuseFailAlloc_6211_, 12, v_E_6181_);
lean_ctor_set(v_reuseFailAlloc_6211_, 13, v_e_6182_);
lean_ctor_set(v_reuseFailAlloc_6211_, 14, v_c_6183_);
lean_ctor_set(v_reuseFailAlloc_6211_, 15, v_F_6184_);
lean_ctor_set(v_reuseFailAlloc_6211_, 16, v_a_6185_);
lean_ctor_set(v_reuseFailAlloc_6211_, 17, v_b_6186_);
lean_ctor_set(v_reuseFailAlloc_6211_, 18, v_B_6187_);
lean_ctor_set(v_reuseFailAlloc_6211_, 19, v_h_6188_);
lean_ctor_set(v_reuseFailAlloc_6211_, 20, v_K_6189_);
lean_ctor_set(v_reuseFailAlloc_6211_, 21, v_k_6190_);
lean_ctor_set(v_reuseFailAlloc_6211_, 22, v_H_6191_);
lean_ctor_set(v_reuseFailAlloc_6211_, 23, v_m_6192_);
lean_ctor_set(v_reuseFailAlloc_6211_, 24, v_s_6193_);
lean_ctor_set(v_reuseFailAlloc_6211_, 25, v_S_6194_);
lean_ctor_set(v_reuseFailAlloc_6211_, 26, v_A_6195_);
lean_ctor_set(v_reuseFailAlloc_6211_, 27, v_n_6196_);
lean_ctor_set(v_reuseFailAlloc_6211_, 28, v_N_6197_);
lean_ctor_set(v_reuseFailAlloc_6211_, 29, v_V_6198_);
lean_ctor_set(v_reuseFailAlloc_6211_, 30, v_z_6199_);
lean_ctor_set(v_reuseFailAlloc_6211_, 31, v___x_6208_);
lean_ctor_set(v_reuseFailAlloc_6211_, 32, v_v_6200_);
lean_ctor_set(v_reuseFailAlloc_6211_, 33, v_O_6201_);
lean_ctor_set(v_reuseFailAlloc_6211_, 34, v_X_6202_);
lean_ctor_set(v_reuseFailAlloc_6211_, 35, v_x_6203_);
lean_ctor_set(v_reuseFailAlloc_6211_, 36, v_Z_6204_);
v___x_6210_ = v_reuseFailAlloc_6211_;
goto v_reusejp_6209_;
}
v_reusejp_6209_:
{
return v___x_6210_;
}
}
}
else
{
lean_object* v_G_6214_; lean_object* v_y_6215_; lean_object* v_u_6216_; lean_object* v_Y_6217_; lean_object* v_D_6218_; lean_object* v_M_6219_; lean_object* v_L_6220_; lean_object* v_d_6221_; lean_object* v_Q_6222_; lean_object* v_q_6223_; lean_object* v_w_6224_; lean_object* v_W_6225_; lean_object* v_E_6226_; lean_object* v_e_6227_; lean_object* v_c_6228_; lean_object* v_F_6229_; lean_object* v_a_6230_; lean_object* v_b_6231_; lean_object* v_B_6232_; lean_object* v_h_6233_; lean_object* v_K_6234_; lean_object* v_k_6235_; lean_object* v_H_6236_; lean_object* v_m_6237_; lean_object* v_s_6238_; lean_object* v_S_6239_; lean_object* v_A_6240_; lean_object* v_n_6241_; lean_object* v_N_6242_; lean_object* v_V_6243_; lean_object* v_zabbrev_6244_; lean_object* v_v_6245_; lean_object* v_O_6246_; lean_object* v_X_6247_; lean_object* v_x_6248_; lean_object* v_Z_6249_; lean_object* v___x_6251_; uint8_t v_isShared_6252_; uint8_t v_isSharedCheck_6257_; 
v_G_6214_ = lean_ctor_get(v_date_4647_, 0);
v_y_6215_ = lean_ctor_get(v_date_4647_, 1);
v_u_6216_ = lean_ctor_get(v_date_4647_, 2);
v_Y_6217_ = lean_ctor_get(v_date_4647_, 3);
v_D_6218_ = lean_ctor_get(v_date_4647_, 4);
v_M_6219_ = lean_ctor_get(v_date_4647_, 5);
v_L_6220_ = lean_ctor_get(v_date_4647_, 6);
v_d_6221_ = lean_ctor_get(v_date_4647_, 7);
v_Q_6222_ = lean_ctor_get(v_date_4647_, 8);
v_q_6223_ = lean_ctor_get(v_date_4647_, 9);
v_w_6224_ = lean_ctor_get(v_date_4647_, 10);
v_W_6225_ = lean_ctor_get(v_date_4647_, 11);
v_E_6226_ = lean_ctor_get(v_date_4647_, 12);
v_e_6227_ = lean_ctor_get(v_date_4647_, 13);
v_c_6228_ = lean_ctor_get(v_date_4647_, 14);
v_F_6229_ = lean_ctor_get(v_date_4647_, 15);
v_a_6230_ = lean_ctor_get(v_date_4647_, 16);
v_b_6231_ = lean_ctor_get(v_date_4647_, 17);
v_B_6232_ = lean_ctor_get(v_date_4647_, 18);
v_h_6233_ = lean_ctor_get(v_date_4647_, 19);
v_K_6234_ = lean_ctor_get(v_date_4647_, 20);
v_k_6235_ = lean_ctor_get(v_date_4647_, 21);
v_H_6236_ = lean_ctor_get(v_date_4647_, 22);
v_m_6237_ = lean_ctor_get(v_date_4647_, 23);
v_s_6238_ = lean_ctor_get(v_date_4647_, 24);
v_S_6239_ = lean_ctor_get(v_date_4647_, 25);
v_A_6240_ = lean_ctor_get(v_date_4647_, 26);
v_n_6241_ = lean_ctor_get(v_date_4647_, 27);
v_N_6242_ = lean_ctor_get(v_date_4647_, 28);
v_V_6243_ = lean_ctor_get(v_date_4647_, 29);
v_zabbrev_6244_ = lean_ctor_get(v_date_4647_, 31);
v_v_6245_ = lean_ctor_get(v_date_4647_, 32);
v_O_6246_ = lean_ctor_get(v_date_4647_, 33);
v_X_6247_ = lean_ctor_get(v_date_4647_, 34);
v_x_6248_ = lean_ctor_get(v_date_4647_, 35);
v_Z_6249_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_6257_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_6257_ == 0)
{
lean_object* v_unused_6258_; 
v_unused_6258_ = lean_ctor_get(v_date_4647_, 30);
lean_dec(v_unused_6258_);
v___x_6251_ = v_date_4647_;
v_isShared_6252_ = v_isSharedCheck_6257_;
goto v_resetjp_6250_;
}
else
{
lean_inc(v_Z_6249_);
lean_inc(v_x_6248_);
lean_inc(v_X_6247_);
lean_inc(v_O_6246_);
lean_inc(v_v_6245_);
lean_inc(v_zabbrev_6244_);
lean_inc(v_V_6243_);
lean_inc(v_N_6242_);
lean_inc(v_n_6241_);
lean_inc(v_A_6240_);
lean_inc(v_S_6239_);
lean_inc(v_s_6238_);
lean_inc(v_m_6237_);
lean_inc(v_H_6236_);
lean_inc(v_k_6235_);
lean_inc(v_K_6234_);
lean_inc(v_h_6233_);
lean_inc(v_B_6232_);
lean_inc(v_b_6231_);
lean_inc(v_a_6230_);
lean_inc(v_F_6229_);
lean_inc(v_c_6228_);
lean_inc(v_e_6227_);
lean_inc(v_E_6226_);
lean_inc(v_W_6225_);
lean_inc(v_w_6224_);
lean_inc(v_q_6223_);
lean_inc(v_Q_6222_);
lean_inc(v_d_6221_);
lean_inc(v_L_6220_);
lean_inc(v_M_6219_);
lean_inc(v_D_6218_);
lean_inc(v_Y_6217_);
lean_inc(v_u_6216_);
lean_inc(v_y_6215_);
lean_inc(v_G_6214_);
lean_dec(v_date_4647_);
v___x_6251_ = lean_box(0);
v_isShared_6252_ = v_isSharedCheck_6257_;
goto v_resetjp_6250_;
}
v_resetjp_6250_:
{
lean_object* v___x_6253_; lean_object* v___x_6255_; 
v___x_6253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6253_, 0, v_data_4649_);
if (v_isShared_6252_ == 0)
{
lean_ctor_set(v___x_6251_, 30, v___x_6253_);
v___x_6255_ = v___x_6251_;
goto v_reusejp_6254_;
}
else
{
lean_object* v_reuseFailAlloc_6256_; 
v_reuseFailAlloc_6256_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6256_, 0, v_G_6214_);
lean_ctor_set(v_reuseFailAlloc_6256_, 1, v_y_6215_);
lean_ctor_set(v_reuseFailAlloc_6256_, 2, v_u_6216_);
lean_ctor_set(v_reuseFailAlloc_6256_, 3, v_Y_6217_);
lean_ctor_set(v_reuseFailAlloc_6256_, 4, v_D_6218_);
lean_ctor_set(v_reuseFailAlloc_6256_, 5, v_M_6219_);
lean_ctor_set(v_reuseFailAlloc_6256_, 6, v_L_6220_);
lean_ctor_set(v_reuseFailAlloc_6256_, 7, v_d_6221_);
lean_ctor_set(v_reuseFailAlloc_6256_, 8, v_Q_6222_);
lean_ctor_set(v_reuseFailAlloc_6256_, 9, v_q_6223_);
lean_ctor_set(v_reuseFailAlloc_6256_, 10, v_w_6224_);
lean_ctor_set(v_reuseFailAlloc_6256_, 11, v_W_6225_);
lean_ctor_set(v_reuseFailAlloc_6256_, 12, v_E_6226_);
lean_ctor_set(v_reuseFailAlloc_6256_, 13, v_e_6227_);
lean_ctor_set(v_reuseFailAlloc_6256_, 14, v_c_6228_);
lean_ctor_set(v_reuseFailAlloc_6256_, 15, v_F_6229_);
lean_ctor_set(v_reuseFailAlloc_6256_, 16, v_a_6230_);
lean_ctor_set(v_reuseFailAlloc_6256_, 17, v_b_6231_);
lean_ctor_set(v_reuseFailAlloc_6256_, 18, v_B_6232_);
lean_ctor_set(v_reuseFailAlloc_6256_, 19, v_h_6233_);
lean_ctor_set(v_reuseFailAlloc_6256_, 20, v_K_6234_);
lean_ctor_set(v_reuseFailAlloc_6256_, 21, v_k_6235_);
lean_ctor_set(v_reuseFailAlloc_6256_, 22, v_H_6236_);
lean_ctor_set(v_reuseFailAlloc_6256_, 23, v_m_6237_);
lean_ctor_set(v_reuseFailAlloc_6256_, 24, v_s_6238_);
lean_ctor_set(v_reuseFailAlloc_6256_, 25, v_S_6239_);
lean_ctor_set(v_reuseFailAlloc_6256_, 26, v_A_6240_);
lean_ctor_set(v_reuseFailAlloc_6256_, 27, v_n_6241_);
lean_ctor_set(v_reuseFailAlloc_6256_, 28, v_N_6242_);
lean_ctor_set(v_reuseFailAlloc_6256_, 29, v_V_6243_);
lean_ctor_set(v_reuseFailAlloc_6256_, 30, v___x_6253_);
lean_ctor_set(v_reuseFailAlloc_6256_, 31, v_zabbrev_6244_);
lean_ctor_set(v_reuseFailAlloc_6256_, 32, v_v_6245_);
lean_ctor_set(v_reuseFailAlloc_6256_, 33, v_O_6246_);
lean_ctor_set(v_reuseFailAlloc_6256_, 34, v_X_6247_);
lean_ctor_set(v_reuseFailAlloc_6256_, 35, v_x_6248_);
lean_ctor_set(v_reuseFailAlloc_6256_, 36, v_Z_6249_);
v___x_6255_ = v_reuseFailAlloc_6256_;
goto v_reusejp_6254_;
}
v_reusejp_6254_:
{
return v___x_6255_;
}
}
}
}
case 31:
{
lean_object* v_G_6259_; lean_object* v_y_6260_; lean_object* v_u_6261_; lean_object* v_Y_6262_; lean_object* v_D_6263_; lean_object* v_M_6264_; lean_object* v_L_6265_; lean_object* v_d_6266_; lean_object* v_Q_6267_; lean_object* v_q_6268_; lean_object* v_w_6269_; lean_object* v_W_6270_; lean_object* v_E_6271_; lean_object* v_e_6272_; lean_object* v_c_6273_; lean_object* v_F_6274_; lean_object* v_a_6275_; lean_object* v_b_6276_; lean_object* v_B_6277_; lean_object* v_h_6278_; lean_object* v_K_6279_; lean_object* v_k_6280_; lean_object* v_H_6281_; lean_object* v_m_6282_; lean_object* v_s_6283_; lean_object* v_S_6284_; lean_object* v_A_6285_; lean_object* v_n_6286_; lean_object* v_N_6287_; lean_object* v_V_6288_; lean_object* v_z_6289_; lean_object* v_zabbrev_6290_; lean_object* v_O_6291_; lean_object* v_X_6292_; lean_object* v_x_6293_; lean_object* v_Z_6294_; lean_object* v___x_6296_; uint8_t v_isShared_6297_; uint8_t v_isSharedCheck_6302_; 
lean_dec_ref_known(v_modifier_4648_, 0);
v_G_6259_ = lean_ctor_get(v_date_4647_, 0);
v_y_6260_ = lean_ctor_get(v_date_4647_, 1);
v_u_6261_ = lean_ctor_get(v_date_4647_, 2);
v_Y_6262_ = lean_ctor_get(v_date_4647_, 3);
v_D_6263_ = lean_ctor_get(v_date_4647_, 4);
v_M_6264_ = lean_ctor_get(v_date_4647_, 5);
v_L_6265_ = lean_ctor_get(v_date_4647_, 6);
v_d_6266_ = lean_ctor_get(v_date_4647_, 7);
v_Q_6267_ = lean_ctor_get(v_date_4647_, 8);
v_q_6268_ = lean_ctor_get(v_date_4647_, 9);
v_w_6269_ = lean_ctor_get(v_date_4647_, 10);
v_W_6270_ = lean_ctor_get(v_date_4647_, 11);
v_E_6271_ = lean_ctor_get(v_date_4647_, 12);
v_e_6272_ = lean_ctor_get(v_date_4647_, 13);
v_c_6273_ = lean_ctor_get(v_date_4647_, 14);
v_F_6274_ = lean_ctor_get(v_date_4647_, 15);
v_a_6275_ = lean_ctor_get(v_date_4647_, 16);
v_b_6276_ = lean_ctor_get(v_date_4647_, 17);
v_B_6277_ = lean_ctor_get(v_date_4647_, 18);
v_h_6278_ = lean_ctor_get(v_date_4647_, 19);
v_K_6279_ = lean_ctor_get(v_date_4647_, 20);
v_k_6280_ = lean_ctor_get(v_date_4647_, 21);
v_H_6281_ = lean_ctor_get(v_date_4647_, 22);
v_m_6282_ = lean_ctor_get(v_date_4647_, 23);
v_s_6283_ = lean_ctor_get(v_date_4647_, 24);
v_S_6284_ = lean_ctor_get(v_date_4647_, 25);
v_A_6285_ = lean_ctor_get(v_date_4647_, 26);
v_n_6286_ = lean_ctor_get(v_date_4647_, 27);
v_N_6287_ = lean_ctor_get(v_date_4647_, 28);
v_V_6288_ = lean_ctor_get(v_date_4647_, 29);
v_z_6289_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_6290_ = lean_ctor_get(v_date_4647_, 31);
v_O_6291_ = lean_ctor_get(v_date_4647_, 33);
v_X_6292_ = lean_ctor_get(v_date_4647_, 34);
v_x_6293_ = lean_ctor_get(v_date_4647_, 35);
v_Z_6294_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_6302_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_6302_ == 0)
{
lean_object* v_unused_6303_; 
v_unused_6303_ = lean_ctor_get(v_date_4647_, 32);
lean_dec(v_unused_6303_);
v___x_6296_ = v_date_4647_;
v_isShared_6297_ = v_isSharedCheck_6302_;
goto v_resetjp_6295_;
}
else
{
lean_inc(v_Z_6294_);
lean_inc(v_x_6293_);
lean_inc(v_X_6292_);
lean_inc(v_O_6291_);
lean_inc(v_zabbrev_6290_);
lean_inc(v_z_6289_);
lean_inc(v_V_6288_);
lean_inc(v_N_6287_);
lean_inc(v_n_6286_);
lean_inc(v_A_6285_);
lean_inc(v_S_6284_);
lean_inc(v_s_6283_);
lean_inc(v_m_6282_);
lean_inc(v_H_6281_);
lean_inc(v_k_6280_);
lean_inc(v_K_6279_);
lean_inc(v_h_6278_);
lean_inc(v_B_6277_);
lean_inc(v_b_6276_);
lean_inc(v_a_6275_);
lean_inc(v_F_6274_);
lean_inc(v_c_6273_);
lean_inc(v_e_6272_);
lean_inc(v_E_6271_);
lean_inc(v_W_6270_);
lean_inc(v_w_6269_);
lean_inc(v_q_6268_);
lean_inc(v_Q_6267_);
lean_inc(v_d_6266_);
lean_inc(v_L_6265_);
lean_inc(v_M_6264_);
lean_inc(v_D_6263_);
lean_inc(v_Y_6262_);
lean_inc(v_u_6261_);
lean_inc(v_y_6260_);
lean_inc(v_G_6259_);
lean_dec(v_date_4647_);
v___x_6296_ = lean_box(0);
v_isShared_6297_ = v_isSharedCheck_6302_;
goto v_resetjp_6295_;
}
v_resetjp_6295_:
{
lean_object* v___x_6298_; lean_object* v___x_6300_; 
v___x_6298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6298_, 0, v_data_4649_);
if (v_isShared_6297_ == 0)
{
lean_ctor_set(v___x_6296_, 32, v___x_6298_);
v___x_6300_ = v___x_6296_;
goto v_reusejp_6299_;
}
else
{
lean_object* v_reuseFailAlloc_6301_; 
v_reuseFailAlloc_6301_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6301_, 0, v_G_6259_);
lean_ctor_set(v_reuseFailAlloc_6301_, 1, v_y_6260_);
lean_ctor_set(v_reuseFailAlloc_6301_, 2, v_u_6261_);
lean_ctor_set(v_reuseFailAlloc_6301_, 3, v_Y_6262_);
lean_ctor_set(v_reuseFailAlloc_6301_, 4, v_D_6263_);
lean_ctor_set(v_reuseFailAlloc_6301_, 5, v_M_6264_);
lean_ctor_set(v_reuseFailAlloc_6301_, 6, v_L_6265_);
lean_ctor_set(v_reuseFailAlloc_6301_, 7, v_d_6266_);
lean_ctor_set(v_reuseFailAlloc_6301_, 8, v_Q_6267_);
lean_ctor_set(v_reuseFailAlloc_6301_, 9, v_q_6268_);
lean_ctor_set(v_reuseFailAlloc_6301_, 10, v_w_6269_);
lean_ctor_set(v_reuseFailAlloc_6301_, 11, v_W_6270_);
lean_ctor_set(v_reuseFailAlloc_6301_, 12, v_E_6271_);
lean_ctor_set(v_reuseFailAlloc_6301_, 13, v_e_6272_);
lean_ctor_set(v_reuseFailAlloc_6301_, 14, v_c_6273_);
lean_ctor_set(v_reuseFailAlloc_6301_, 15, v_F_6274_);
lean_ctor_set(v_reuseFailAlloc_6301_, 16, v_a_6275_);
lean_ctor_set(v_reuseFailAlloc_6301_, 17, v_b_6276_);
lean_ctor_set(v_reuseFailAlloc_6301_, 18, v_B_6277_);
lean_ctor_set(v_reuseFailAlloc_6301_, 19, v_h_6278_);
lean_ctor_set(v_reuseFailAlloc_6301_, 20, v_K_6279_);
lean_ctor_set(v_reuseFailAlloc_6301_, 21, v_k_6280_);
lean_ctor_set(v_reuseFailAlloc_6301_, 22, v_H_6281_);
lean_ctor_set(v_reuseFailAlloc_6301_, 23, v_m_6282_);
lean_ctor_set(v_reuseFailAlloc_6301_, 24, v_s_6283_);
lean_ctor_set(v_reuseFailAlloc_6301_, 25, v_S_6284_);
lean_ctor_set(v_reuseFailAlloc_6301_, 26, v_A_6285_);
lean_ctor_set(v_reuseFailAlloc_6301_, 27, v_n_6286_);
lean_ctor_set(v_reuseFailAlloc_6301_, 28, v_N_6287_);
lean_ctor_set(v_reuseFailAlloc_6301_, 29, v_V_6288_);
lean_ctor_set(v_reuseFailAlloc_6301_, 30, v_z_6289_);
lean_ctor_set(v_reuseFailAlloc_6301_, 31, v_zabbrev_6290_);
lean_ctor_set(v_reuseFailAlloc_6301_, 32, v___x_6298_);
lean_ctor_set(v_reuseFailAlloc_6301_, 33, v_O_6291_);
lean_ctor_set(v_reuseFailAlloc_6301_, 34, v_X_6292_);
lean_ctor_set(v_reuseFailAlloc_6301_, 35, v_x_6293_);
lean_ctor_set(v_reuseFailAlloc_6301_, 36, v_Z_6294_);
v___x_6300_ = v_reuseFailAlloc_6301_;
goto v_reusejp_6299_;
}
v_reusejp_6299_:
{
return v___x_6300_;
}
}
}
case 32:
{
lean_object* v_G_6304_; lean_object* v_y_6305_; lean_object* v_u_6306_; lean_object* v_Y_6307_; lean_object* v_D_6308_; lean_object* v_M_6309_; lean_object* v_L_6310_; lean_object* v_d_6311_; lean_object* v_Q_6312_; lean_object* v_q_6313_; lean_object* v_w_6314_; lean_object* v_W_6315_; lean_object* v_E_6316_; lean_object* v_e_6317_; lean_object* v_c_6318_; lean_object* v_F_6319_; lean_object* v_a_6320_; lean_object* v_b_6321_; lean_object* v_B_6322_; lean_object* v_h_6323_; lean_object* v_K_6324_; lean_object* v_k_6325_; lean_object* v_H_6326_; lean_object* v_m_6327_; lean_object* v_s_6328_; lean_object* v_S_6329_; lean_object* v_A_6330_; lean_object* v_n_6331_; lean_object* v_N_6332_; lean_object* v_V_6333_; lean_object* v_z_6334_; lean_object* v_zabbrev_6335_; lean_object* v_v_6336_; lean_object* v_X_6337_; lean_object* v_x_6338_; lean_object* v_Z_6339_; lean_object* v___x_6341_; uint8_t v_isShared_6342_; uint8_t v_isSharedCheck_6347_; 
lean_dec_ref_known(v_modifier_4648_, 0);
v_G_6304_ = lean_ctor_get(v_date_4647_, 0);
v_y_6305_ = lean_ctor_get(v_date_4647_, 1);
v_u_6306_ = lean_ctor_get(v_date_4647_, 2);
v_Y_6307_ = lean_ctor_get(v_date_4647_, 3);
v_D_6308_ = lean_ctor_get(v_date_4647_, 4);
v_M_6309_ = lean_ctor_get(v_date_4647_, 5);
v_L_6310_ = lean_ctor_get(v_date_4647_, 6);
v_d_6311_ = lean_ctor_get(v_date_4647_, 7);
v_Q_6312_ = lean_ctor_get(v_date_4647_, 8);
v_q_6313_ = lean_ctor_get(v_date_4647_, 9);
v_w_6314_ = lean_ctor_get(v_date_4647_, 10);
v_W_6315_ = lean_ctor_get(v_date_4647_, 11);
v_E_6316_ = lean_ctor_get(v_date_4647_, 12);
v_e_6317_ = lean_ctor_get(v_date_4647_, 13);
v_c_6318_ = lean_ctor_get(v_date_4647_, 14);
v_F_6319_ = lean_ctor_get(v_date_4647_, 15);
v_a_6320_ = lean_ctor_get(v_date_4647_, 16);
v_b_6321_ = lean_ctor_get(v_date_4647_, 17);
v_B_6322_ = lean_ctor_get(v_date_4647_, 18);
v_h_6323_ = lean_ctor_get(v_date_4647_, 19);
v_K_6324_ = lean_ctor_get(v_date_4647_, 20);
v_k_6325_ = lean_ctor_get(v_date_4647_, 21);
v_H_6326_ = lean_ctor_get(v_date_4647_, 22);
v_m_6327_ = lean_ctor_get(v_date_4647_, 23);
v_s_6328_ = lean_ctor_get(v_date_4647_, 24);
v_S_6329_ = lean_ctor_get(v_date_4647_, 25);
v_A_6330_ = lean_ctor_get(v_date_4647_, 26);
v_n_6331_ = lean_ctor_get(v_date_4647_, 27);
v_N_6332_ = lean_ctor_get(v_date_4647_, 28);
v_V_6333_ = lean_ctor_get(v_date_4647_, 29);
v_z_6334_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_6335_ = lean_ctor_get(v_date_4647_, 31);
v_v_6336_ = lean_ctor_get(v_date_4647_, 32);
v_X_6337_ = lean_ctor_get(v_date_4647_, 34);
v_x_6338_ = lean_ctor_get(v_date_4647_, 35);
v_Z_6339_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_6347_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_6347_ == 0)
{
lean_object* v_unused_6348_; 
v_unused_6348_ = lean_ctor_get(v_date_4647_, 33);
lean_dec(v_unused_6348_);
v___x_6341_ = v_date_4647_;
v_isShared_6342_ = v_isSharedCheck_6347_;
goto v_resetjp_6340_;
}
else
{
lean_inc(v_Z_6339_);
lean_inc(v_x_6338_);
lean_inc(v_X_6337_);
lean_inc(v_v_6336_);
lean_inc(v_zabbrev_6335_);
lean_inc(v_z_6334_);
lean_inc(v_V_6333_);
lean_inc(v_N_6332_);
lean_inc(v_n_6331_);
lean_inc(v_A_6330_);
lean_inc(v_S_6329_);
lean_inc(v_s_6328_);
lean_inc(v_m_6327_);
lean_inc(v_H_6326_);
lean_inc(v_k_6325_);
lean_inc(v_K_6324_);
lean_inc(v_h_6323_);
lean_inc(v_B_6322_);
lean_inc(v_b_6321_);
lean_inc(v_a_6320_);
lean_inc(v_F_6319_);
lean_inc(v_c_6318_);
lean_inc(v_e_6317_);
lean_inc(v_E_6316_);
lean_inc(v_W_6315_);
lean_inc(v_w_6314_);
lean_inc(v_q_6313_);
lean_inc(v_Q_6312_);
lean_inc(v_d_6311_);
lean_inc(v_L_6310_);
lean_inc(v_M_6309_);
lean_inc(v_D_6308_);
lean_inc(v_Y_6307_);
lean_inc(v_u_6306_);
lean_inc(v_y_6305_);
lean_inc(v_G_6304_);
lean_dec(v_date_4647_);
v___x_6341_ = lean_box(0);
v_isShared_6342_ = v_isSharedCheck_6347_;
goto v_resetjp_6340_;
}
v_resetjp_6340_:
{
lean_object* v___x_6343_; lean_object* v___x_6345_; 
v___x_6343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6343_, 0, v_data_4649_);
if (v_isShared_6342_ == 0)
{
lean_ctor_set(v___x_6341_, 33, v___x_6343_);
v___x_6345_ = v___x_6341_;
goto v_reusejp_6344_;
}
else
{
lean_object* v_reuseFailAlloc_6346_; 
v_reuseFailAlloc_6346_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6346_, 0, v_G_6304_);
lean_ctor_set(v_reuseFailAlloc_6346_, 1, v_y_6305_);
lean_ctor_set(v_reuseFailAlloc_6346_, 2, v_u_6306_);
lean_ctor_set(v_reuseFailAlloc_6346_, 3, v_Y_6307_);
lean_ctor_set(v_reuseFailAlloc_6346_, 4, v_D_6308_);
lean_ctor_set(v_reuseFailAlloc_6346_, 5, v_M_6309_);
lean_ctor_set(v_reuseFailAlloc_6346_, 6, v_L_6310_);
lean_ctor_set(v_reuseFailAlloc_6346_, 7, v_d_6311_);
lean_ctor_set(v_reuseFailAlloc_6346_, 8, v_Q_6312_);
lean_ctor_set(v_reuseFailAlloc_6346_, 9, v_q_6313_);
lean_ctor_set(v_reuseFailAlloc_6346_, 10, v_w_6314_);
lean_ctor_set(v_reuseFailAlloc_6346_, 11, v_W_6315_);
lean_ctor_set(v_reuseFailAlloc_6346_, 12, v_E_6316_);
lean_ctor_set(v_reuseFailAlloc_6346_, 13, v_e_6317_);
lean_ctor_set(v_reuseFailAlloc_6346_, 14, v_c_6318_);
lean_ctor_set(v_reuseFailAlloc_6346_, 15, v_F_6319_);
lean_ctor_set(v_reuseFailAlloc_6346_, 16, v_a_6320_);
lean_ctor_set(v_reuseFailAlloc_6346_, 17, v_b_6321_);
lean_ctor_set(v_reuseFailAlloc_6346_, 18, v_B_6322_);
lean_ctor_set(v_reuseFailAlloc_6346_, 19, v_h_6323_);
lean_ctor_set(v_reuseFailAlloc_6346_, 20, v_K_6324_);
lean_ctor_set(v_reuseFailAlloc_6346_, 21, v_k_6325_);
lean_ctor_set(v_reuseFailAlloc_6346_, 22, v_H_6326_);
lean_ctor_set(v_reuseFailAlloc_6346_, 23, v_m_6327_);
lean_ctor_set(v_reuseFailAlloc_6346_, 24, v_s_6328_);
lean_ctor_set(v_reuseFailAlloc_6346_, 25, v_S_6329_);
lean_ctor_set(v_reuseFailAlloc_6346_, 26, v_A_6330_);
lean_ctor_set(v_reuseFailAlloc_6346_, 27, v_n_6331_);
lean_ctor_set(v_reuseFailAlloc_6346_, 28, v_N_6332_);
lean_ctor_set(v_reuseFailAlloc_6346_, 29, v_V_6333_);
lean_ctor_set(v_reuseFailAlloc_6346_, 30, v_z_6334_);
lean_ctor_set(v_reuseFailAlloc_6346_, 31, v_zabbrev_6335_);
lean_ctor_set(v_reuseFailAlloc_6346_, 32, v_v_6336_);
lean_ctor_set(v_reuseFailAlloc_6346_, 33, v___x_6343_);
lean_ctor_set(v_reuseFailAlloc_6346_, 34, v_X_6337_);
lean_ctor_set(v_reuseFailAlloc_6346_, 35, v_x_6338_);
lean_ctor_set(v_reuseFailAlloc_6346_, 36, v_Z_6339_);
v___x_6345_ = v_reuseFailAlloc_6346_;
goto v_reusejp_6344_;
}
v_reusejp_6344_:
{
return v___x_6345_;
}
}
}
case 33:
{
lean_object* v_G_6349_; lean_object* v_y_6350_; lean_object* v_u_6351_; lean_object* v_Y_6352_; lean_object* v_D_6353_; lean_object* v_M_6354_; lean_object* v_L_6355_; lean_object* v_d_6356_; lean_object* v_Q_6357_; lean_object* v_q_6358_; lean_object* v_w_6359_; lean_object* v_W_6360_; lean_object* v_E_6361_; lean_object* v_e_6362_; lean_object* v_c_6363_; lean_object* v_F_6364_; lean_object* v_a_6365_; lean_object* v_b_6366_; lean_object* v_B_6367_; lean_object* v_h_6368_; lean_object* v_K_6369_; lean_object* v_k_6370_; lean_object* v_H_6371_; lean_object* v_m_6372_; lean_object* v_s_6373_; lean_object* v_S_6374_; lean_object* v_A_6375_; lean_object* v_n_6376_; lean_object* v_N_6377_; lean_object* v_V_6378_; lean_object* v_z_6379_; lean_object* v_zabbrev_6380_; lean_object* v_v_6381_; lean_object* v_O_6382_; lean_object* v_x_6383_; lean_object* v_Z_6384_; lean_object* v___x_6386_; uint8_t v_isShared_6387_; uint8_t v_isSharedCheck_6392_; 
lean_dec_ref_known(v_modifier_4648_, 0);
v_G_6349_ = lean_ctor_get(v_date_4647_, 0);
v_y_6350_ = lean_ctor_get(v_date_4647_, 1);
v_u_6351_ = lean_ctor_get(v_date_4647_, 2);
v_Y_6352_ = lean_ctor_get(v_date_4647_, 3);
v_D_6353_ = lean_ctor_get(v_date_4647_, 4);
v_M_6354_ = lean_ctor_get(v_date_4647_, 5);
v_L_6355_ = lean_ctor_get(v_date_4647_, 6);
v_d_6356_ = lean_ctor_get(v_date_4647_, 7);
v_Q_6357_ = lean_ctor_get(v_date_4647_, 8);
v_q_6358_ = lean_ctor_get(v_date_4647_, 9);
v_w_6359_ = lean_ctor_get(v_date_4647_, 10);
v_W_6360_ = lean_ctor_get(v_date_4647_, 11);
v_E_6361_ = lean_ctor_get(v_date_4647_, 12);
v_e_6362_ = lean_ctor_get(v_date_4647_, 13);
v_c_6363_ = lean_ctor_get(v_date_4647_, 14);
v_F_6364_ = lean_ctor_get(v_date_4647_, 15);
v_a_6365_ = lean_ctor_get(v_date_4647_, 16);
v_b_6366_ = lean_ctor_get(v_date_4647_, 17);
v_B_6367_ = lean_ctor_get(v_date_4647_, 18);
v_h_6368_ = lean_ctor_get(v_date_4647_, 19);
v_K_6369_ = lean_ctor_get(v_date_4647_, 20);
v_k_6370_ = lean_ctor_get(v_date_4647_, 21);
v_H_6371_ = lean_ctor_get(v_date_4647_, 22);
v_m_6372_ = lean_ctor_get(v_date_4647_, 23);
v_s_6373_ = lean_ctor_get(v_date_4647_, 24);
v_S_6374_ = lean_ctor_get(v_date_4647_, 25);
v_A_6375_ = lean_ctor_get(v_date_4647_, 26);
v_n_6376_ = lean_ctor_get(v_date_4647_, 27);
v_N_6377_ = lean_ctor_get(v_date_4647_, 28);
v_V_6378_ = lean_ctor_get(v_date_4647_, 29);
v_z_6379_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_6380_ = lean_ctor_get(v_date_4647_, 31);
v_v_6381_ = lean_ctor_get(v_date_4647_, 32);
v_O_6382_ = lean_ctor_get(v_date_4647_, 33);
v_x_6383_ = lean_ctor_get(v_date_4647_, 35);
v_Z_6384_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_6392_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_6392_ == 0)
{
lean_object* v_unused_6393_; 
v_unused_6393_ = lean_ctor_get(v_date_4647_, 34);
lean_dec(v_unused_6393_);
v___x_6386_ = v_date_4647_;
v_isShared_6387_ = v_isSharedCheck_6392_;
goto v_resetjp_6385_;
}
else
{
lean_inc(v_Z_6384_);
lean_inc(v_x_6383_);
lean_inc(v_O_6382_);
lean_inc(v_v_6381_);
lean_inc(v_zabbrev_6380_);
lean_inc(v_z_6379_);
lean_inc(v_V_6378_);
lean_inc(v_N_6377_);
lean_inc(v_n_6376_);
lean_inc(v_A_6375_);
lean_inc(v_S_6374_);
lean_inc(v_s_6373_);
lean_inc(v_m_6372_);
lean_inc(v_H_6371_);
lean_inc(v_k_6370_);
lean_inc(v_K_6369_);
lean_inc(v_h_6368_);
lean_inc(v_B_6367_);
lean_inc(v_b_6366_);
lean_inc(v_a_6365_);
lean_inc(v_F_6364_);
lean_inc(v_c_6363_);
lean_inc(v_e_6362_);
lean_inc(v_E_6361_);
lean_inc(v_W_6360_);
lean_inc(v_w_6359_);
lean_inc(v_q_6358_);
lean_inc(v_Q_6357_);
lean_inc(v_d_6356_);
lean_inc(v_L_6355_);
lean_inc(v_M_6354_);
lean_inc(v_D_6353_);
lean_inc(v_Y_6352_);
lean_inc(v_u_6351_);
lean_inc(v_y_6350_);
lean_inc(v_G_6349_);
lean_dec(v_date_4647_);
v___x_6386_ = lean_box(0);
v_isShared_6387_ = v_isSharedCheck_6392_;
goto v_resetjp_6385_;
}
v_resetjp_6385_:
{
lean_object* v___x_6388_; lean_object* v___x_6390_; 
v___x_6388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6388_, 0, v_data_4649_);
if (v_isShared_6387_ == 0)
{
lean_ctor_set(v___x_6386_, 34, v___x_6388_);
v___x_6390_ = v___x_6386_;
goto v_reusejp_6389_;
}
else
{
lean_object* v_reuseFailAlloc_6391_; 
v_reuseFailAlloc_6391_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6391_, 0, v_G_6349_);
lean_ctor_set(v_reuseFailAlloc_6391_, 1, v_y_6350_);
lean_ctor_set(v_reuseFailAlloc_6391_, 2, v_u_6351_);
lean_ctor_set(v_reuseFailAlloc_6391_, 3, v_Y_6352_);
lean_ctor_set(v_reuseFailAlloc_6391_, 4, v_D_6353_);
lean_ctor_set(v_reuseFailAlloc_6391_, 5, v_M_6354_);
lean_ctor_set(v_reuseFailAlloc_6391_, 6, v_L_6355_);
lean_ctor_set(v_reuseFailAlloc_6391_, 7, v_d_6356_);
lean_ctor_set(v_reuseFailAlloc_6391_, 8, v_Q_6357_);
lean_ctor_set(v_reuseFailAlloc_6391_, 9, v_q_6358_);
lean_ctor_set(v_reuseFailAlloc_6391_, 10, v_w_6359_);
lean_ctor_set(v_reuseFailAlloc_6391_, 11, v_W_6360_);
lean_ctor_set(v_reuseFailAlloc_6391_, 12, v_E_6361_);
lean_ctor_set(v_reuseFailAlloc_6391_, 13, v_e_6362_);
lean_ctor_set(v_reuseFailAlloc_6391_, 14, v_c_6363_);
lean_ctor_set(v_reuseFailAlloc_6391_, 15, v_F_6364_);
lean_ctor_set(v_reuseFailAlloc_6391_, 16, v_a_6365_);
lean_ctor_set(v_reuseFailAlloc_6391_, 17, v_b_6366_);
lean_ctor_set(v_reuseFailAlloc_6391_, 18, v_B_6367_);
lean_ctor_set(v_reuseFailAlloc_6391_, 19, v_h_6368_);
lean_ctor_set(v_reuseFailAlloc_6391_, 20, v_K_6369_);
lean_ctor_set(v_reuseFailAlloc_6391_, 21, v_k_6370_);
lean_ctor_set(v_reuseFailAlloc_6391_, 22, v_H_6371_);
lean_ctor_set(v_reuseFailAlloc_6391_, 23, v_m_6372_);
lean_ctor_set(v_reuseFailAlloc_6391_, 24, v_s_6373_);
lean_ctor_set(v_reuseFailAlloc_6391_, 25, v_S_6374_);
lean_ctor_set(v_reuseFailAlloc_6391_, 26, v_A_6375_);
lean_ctor_set(v_reuseFailAlloc_6391_, 27, v_n_6376_);
lean_ctor_set(v_reuseFailAlloc_6391_, 28, v_N_6377_);
lean_ctor_set(v_reuseFailAlloc_6391_, 29, v_V_6378_);
lean_ctor_set(v_reuseFailAlloc_6391_, 30, v_z_6379_);
lean_ctor_set(v_reuseFailAlloc_6391_, 31, v_zabbrev_6380_);
lean_ctor_set(v_reuseFailAlloc_6391_, 32, v_v_6381_);
lean_ctor_set(v_reuseFailAlloc_6391_, 33, v_O_6382_);
lean_ctor_set(v_reuseFailAlloc_6391_, 34, v___x_6388_);
lean_ctor_set(v_reuseFailAlloc_6391_, 35, v_x_6383_);
lean_ctor_set(v_reuseFailAlloc_6391_, 36, v_Z_6384_);
v___x_6390_ = v_reuseFailAlloc_6391_;
goto v_reusejp_6389_;
}
v_reusejp_6389_:
{
return v___x_6390_;
}
}
}
case 34:
{
lean_object* v_G_6394_; lean_object* v_y_6395_; lean_object* v_u_6396_; lean_object* v_Y_6397_; lean_object* v_D_6398_; lean_object* v_M_6399_; lean_object* v_L_6400_; lean_object* v_d_6401_; lean_object* v_Q_6402_; lean_object* v_q_6403_; lean_object* v_w_6404_; lean_object* v_W_6405_; lean_object* v_E_6406_; lean_object* v_e_6407_; lean_object* v_c_6408_; lean_object* v_F_6409_; lean_object* v_a_6410_; lean_object* v_b_6411_; lean_object* v_B_6412_; lean_object* v_h_6413_; lean_object* v_K_6414_; lean_object* v_k_6415_; lean_object* v_H_6416_; lean_object* v_m_6417_; lean_object* v_s_6418_; lean_object* v_S_6419_; lean_object* v_A_6420_; lean_object* v_n_6421_; lean_object* v_N_6422_; lean_object* v_V_6423_; lean_object* v_z_6424_; lean_object* v_zabbrev_6425_; lean_object* v_v_6426_; lean_object* v_O_6427_; lean_object* v_X_6428_; lean_object* v_Z_6429_; lean_object* v___x_6431_; uint8_t v_isShared_6432_; uint8_t v_isSharedCheck_6437_; 
lean_dec_ref_known(v_modifier_4648_, 0);
v_G_6394_ = lean_ctor_get(v_date_4647_, 0);
v_y_6395_ = lean_ctor_get(v_date_4647_, 1);
v_u_6396_ = lean_ctor_get(v_date_4647_, 2);
v_Y_6397_ = lean_ctor_get(v_date_4647_, 3);
v_D_6398_ = lean_ctor_get(v_date_4647_, 4);
v_M_6399_ = lean_ctor_get(v_date_4647_, 5);
v_L_6400_ = lean_ctor_get(v_date_4647_, 6);
v_d_6401_ = lean_ctor_get(v_date_4647_, 7);
v_Q_6402_ = lean_ctor_get(v_date_4647_, 8);
v_q_6403_ = lean_ctor_get(v_date_4647_, 9);
v_w_6404_ = lean_ctor_get(v_date_4647_, 10);
v_W_6405_ = lean_ctor_get(v_date_4647_, 11);
v_E_6406_ = lean_ctor_get(v_date_4647_, 12);
v_e_6407_ = lean_ctor_get(v_date_4647_, 13);
v_c_6408_ = lean_ctor_get(v_date_4647_, 14);
v_F_6409_ = lean_ctor_get(v_date_4647_, 15);
v_a_6410_ = lean_ctor_get(v_date_4647_, 16);
v_b_6411_ = lean_ctor_get(v_date_4647_, 17);
v_B_6412_ = lean_ctor_get(v_date_4647_, 18);
v_h_6413_ = lean_ctor_get(v_date_4647_, 19);
v_K_6414_ = lean_ctor_get(v_date_4647_, 20);
v_k_6415_ = lean_ctor_get(v_date_4647_, 21);
v_H_6416_ = lean_ctor_get(v_date_4647_, 22);
v_m_6417_ = lean_ctor_get(v_date_4647_, 23);
v_s_6418_ = lean_ctor_get(v_date_4647_, 24);
v_S_6419_ = lean_ctor_get(v_date_4647_, 25);
v_A_6420_ = lean_ctor_get(v_date_4647_, 26);
v_n_6421_ = lean_ctor_get(v_date_4647_, 27);
v_N_6422_ = lean_ctor_get(v_date_4647_, 28);
v_V_6423_ = lean_ctor_get(v_date_4647_, 29);
v_z_6424_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_6425_ = lean_ctor_get(v_date_4647_, 31);
v_v_6426_ = lean_ctor_get(v_date_4647_, 32);
v_O_6427_ = lean_ctor_get(v_date_4647_, 33);
v_X_6428_ = lean_ctor_get(v_date_4647_, 34);
v_Z_6429_ = lean_ctor_get(v_date_4647_, 36);
v_isSharedCheck_6437_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_6437_ == 0)
{
lean_object* v_unused_6438_; 
v_unused_6438_ = lean_ctor_get(v_date_4647_, 35);
lean_dec(v_unused_6438_);
v___x_6431_ = v_date_4647_;
v_isShared_6432_ = v_isSharedCheck_6437_;
goto v_resetjp_6430_;
}
else
{
lean_inc(v_Z_6429_);
lean_inc(v_X_6428_);
lean_inc(v_O_6427_);
lean_inc(v_v_6426_);
lean_inc(v_zabbrev_6425_);
lean_inc(v_z_6424_);
lean_inc(v_V_6423_);
lean_inc(v_N_6422_);
lean_inc(v_n_6421_);
lean_inc(v_A_6420_);
lean_inc(v_S_6419_);
lean_inc(v_s_6418_);
lean_inc(v_m_6417_);
lean_inc(v_H_6416_);
lean_inc(v_k_6415_);
lean_inc(v_K_6414_);
lean_inc(v_h_6413_);
lean_inc(v_B_6412_);
lean_inc(v_b_6411_);
lean_inc(v_a_6410_);
lean_inc(v_F_6409_);
lean_inc(v_c_6408_);
lean_inc(v_e_6407_);
lean_inc(v_E_6406_);
lean_inc(v_W_6405_);
lean_inc(v_w_6404_);
lean_inc(v_q_6403_);
lean_inc(v_Q_6402_);
lean_inc(v_d_6401_);
lean_inc(v_L_6400_);
lean_inc(v_M_6399_);
lean_inc(v_D_6398_);
lean_inc(v_Y_6397_);
lean_inc(v_u_6396_);
lean_inc(v_y_6395_);
lean_inc(v_G_6394_);
lean_dec(v_date_4647_);
v___x_6431_ = lean_box(0);
v_isShared_6432_ = v_isSharedCheck_6437_;
goto v_resetjp_6430_;
}
v_resetjp_6430_:
{
lean_object* v___x_6433_; lean_object* v___x_6435_; 
v___x_6433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6433_, 0, v_data_4649_);
if (v_isShared_6432_ == 0)
{
lean_ctor_set(v___x_6431_, 35, v___x_6433_);
v___x_6435_ = v___x_6431_;
goto v_reusejp_6434_;
}
else
{
lean_object* v_reuseFailAlloc_6436_; 
v_reuseFailAlloc_6436_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6436_, 0, v_G_6394_);
lean_ctor_set(v_reuseFailAlloc_6436_, 1, v_y_6395_);
lean_ctor_set(v_reuseFailAlloc_6436_, 2, v_u_6396_);
lean_ctor_set(v_reuseFailAlloc_6436_, 3, v_Y_6397_);
lean_ctor_set(v_reuseFailAlloc_6436_, 4, v_D_6398_);
lean_ctor_set(v_reuseFailAlloc_6436_, 5, v_M_6399_);
lean_ctor_set(v_reuseFailAlloc_6436_, 6, v_L_6400_);
lean_ctor_set(v_reuseFailAlloc_6436_, 7, v_d_6401_);
lean_ctor_set(v_reuseFailAlloc_6436_, 8, v_Q_6402_);
lean_ctor_set(v_reuseFailAlloc_6436_, 9, v_q_6403_);
lean_ctor_set(v_reuseFailAlloc_6436_, 10, v_w_6404_);
lean_ctor_set(v_reuseFailAlloc_6436_, 11, v_W_6405_);
lean_ctor_set(v_reuseFailAlloc_6436_, 12, v_E_6406_);
lean_ctor_set(v_reuseFailAlloc_6436_, 13, v_e_6407_);
lean_ctor_set(v_reuseFailAlloc_6436_, 14, v_c_6408_);
lean_ctor_set(v_reuseFailAlloc_6436_, 15, v_F_6409_);
lean_ctor_set(v_reuseFailAlloc_6436_, 16, v_a_6410_);
lean_ctor_set(v_reuseFailAlloc_6436_, 17, v_b_6411_);
lean_ctor_set(v_reuseFailAlloc_6436_, 18, v_B_6412_);
lean_ctor_set(v_reuseFailAlloc_6436_, 19, v_h_6413_);
lean_ctor_set(v_reuseFailAlloc_6436_, 20, v_K_6414_);
lean_ctor_set(v_reuseFailAlloc_6436_, 21, v_k_6415_);
lean_ctor_set(v_reuseFailAlloc_6436_, 22, v_H_6416_);
lean_ctor_set(v_reuseFailAlloc_6436_, 23, v_m_6417_);
lean_ctor_set(v_reuseFailAlloc_6436_, 24, v_s_6418_);
lean_ctor_set(v_reuseFailAlloc_6436_, 25, v_S_6419_);
lean_ctor_set(v_reuseFailAlloc_6436_, 26, v_A_6420_);
lean_ctor_set(v_reuseFailAlloc_6436_, 27, v_n_6421_);
lean_ctor_set(v_reuseFailAlloc_6436_, 28, v_N_6422_);
lean_ctor_set(v_reuseFailAlloc_6436_, 29, v_V_6423_);
lean_ctor_set(v_reuseFailAlloc_6436_, 30, v_z_6424_);
lean_ctor_set(v_reuseFailAlloc_6436_, 31, v_zabbrev_6425_);
lean_ctor_set(v_reuseFailAlloc_6436_, 32, v_v_6426_);
lean_ctor_set(v_reuseFailAlloc_6436_, 33, v_O_6427_);
lean_ctor_set(v_reuseFailAlloc_6436_, 34, v_X_6428_);
lean_ctor_set(v_reuseFailAlloc_6436_, 35, v___x_6433_);
lean_ctor_set(v_reuseFailAlloc_6436_, 36, v_Z_6429_);
v___x_6435_ = v_reuseFailAlloc_6436_;
goto v_reusejp_6434_;
}
v_reusejp_6434_:
{
return v___x_6435_;
}
}
}
default: 
{
lean_object* v_G_6439_; lean_object* v_y_6440_; lean_object* v_u_6441_; lean_object* v_Y_6442_; lean_object* v_D_6443_; lean_object* v_M_6444_; lean_object* v_L_6445_; lean_object* v_d_6446_; lean_object* v_Q_6447_; lean_object* v_q_6448_; lean_object* v_w_6449_; lean_object* v_W_6450_; lean_object* v_E_6451_; lean_object* v_e_6452_; lean_object* v_c_6453_; lean_object* v_F_6454_; lean_object* v_a_6455_; lean_object* v_b_6456_; lean_object* v_B_6457_; lean_object* v_h_6458_; lean_object* v_K_6459_; lean_object* v_k_6460_; lean_object* v_H_6461_; lean_object* v_m_6462_; lean_object* v_s_6463_; lean_object* v_S_6464_; lean_object* v_A_6465_; lean_object* v_n_6466_; lean_object* v_N_6467_; lean_object* v_V_6468_; lean_object* v_z_6469_; lean_object* v_zabbrev_6470_; lean_object* v_v_6471_; lean_object* v_O_6472_; lean_object* v_X_6473_; lean_object* v_x_6474_; lean_object* v___x_6476_; uint8_t v_isShared_6477_; uint8_t v_isSharedCheck_6482_; 
lean_dec_ref_known(v_modifier_4648_, 0);
v_G_6439_ = lean_ctor_get(v_date_4647_, 0);
v_y_6440_ = lean_ctor_get(v_date_4647_, 1);
v_u_6441_ = lean_ctor_get(v_date_4647_, 2);
v_Y_6442_ = lean_ctor_get(v_date_4647_, 3);
v_D_6443_ = lean_ctor_get(v_date_4647_, 4);
v_M_6444_ = lean_ctor_get(v_date_4647_, 5);
v_L_6445_ = lean_ctor_get(v_date_4647_, 6);
v_d_6446_ = lean_ctor_get(v_date_4647_, 7);
v_Q_6447_ = lean_ctor_get(v_date_4647_, 8);
v_q_6448_ = lean_ctor_get(v_date_4647_, 9);
v_w_6449_ = lean_ctor_get(v_date_4647_, 10);
v_W_6450_ = lean_ctor_get(v_date_4647_, 11);
v_E_6451_ = lean_ctor_get(v_date_4647_, 12);
v_e_6452_ = lean_ctor_get(v_date_4647_, 13);
v_c_6453_ = lean_ctor_get(v_date_4647_, 14);
v_F_6454_ = lean_ctor_get(v_date_4647_, 15);
v_a_6455_ = lean_ctor_get(v_date_4647_, 16);
v_b_6456_ = lean_ctor_get(v_date_4647_, 17);
v_B_6457_ = lean_ctor_get(v_date_4647_, 18);
v_h_6458_ = lean_ctor_get(v_date_4647_, 19);
v_K_6459_ = lean_ctor_get(v_date_4647_, 20);
v_k_6460_ = lean_ctor_get(v_date_4647_, 21);
v_H_6461_ = lean_ctor_get(v_date_4647_, 22);
v_m_6462_ = lean_ctor_get(v_date_4647_, 23);
v_s_6463_ = lean_ctor_get(v_date_4647_, 24);
v_S_6464_ = lean_ctor_get(v_date_4647_, 25);
v_A_6465_ = lean_ctor_get(v_date_4647_, 26);
v_n_6466_ = lean_ctor_get(v_date_4647_, 27);
v_N_6467_ = lean_ctor_get(v_date_4647_, 28);
v_V_6468_ = lean_ctor_get(v_date_4647_, 29);
v_z_6469_ = lean_ctor_get(v_date_4647_, 30);
v_zabbrev_6470_ = lean_ctor_get(v_date_4647_, 31);
v_v_6471_ = lean_ctor_get(v_date_4647_, 32);
v_O_6472_ = lean_ctor_get(v_date_4647_, 33);
v_X_6473_ = lean_ctor_get(v_date_4647_, 34);
v_x_6474_ = lean_ctor_get(v_date_4647_, 35);
v_isSharedCheck_6482_ = !lean_is_exclusive(v_date_4647_);
if (v_isSharedCheck_6482_ == 0)
{
lean_object* v_unused_6483_; 
v_unused_6483_ = lean_ctor_get(v_date_4647_, 36);
lean_dec(v_unused_6483_);
v___x_6476_ = v_date_4647_;
v_isShared_6477_ = v_isSharedCheck_6482_;
goto v_resetjp_6475_;
}
else
{
lean_inc(v_x_6474_);
lean_inc(v_X_6473_);
lean_inc(v_O_6472_);
lean_inc(v_v_6471_);
lean_inc(v_zabbrev_6470_);
lean_inc(v_z_6469_);
lean_inc(v_V_6468_);
lean_inc(v_N_6467_);
lean_inc(v_n_6466_);
lean_inc(v_A_6465_);
lean_inc(v_S_6464_);
lean_inc(v_s_6463_);
lean_inc(v_m_6462_);
lean_inc(v_H_6461_);
lean_inc(v_k_6460_);
lean_inc(v_K_6459_);
lean_inc(v_h_6458_);
lean_inc(v_B_6457_);
lean_inc(v_b_6456_);
lean_inc(v_a_6455_);
lean_inc(v_F_6454_);
lean_inc(v_c_6453_);
lean_inc(v_e_6452_);
lean_inc(v_E_6451_);
lean_inc(v_W_6450_);
lean_inc(v_w_6449_);
lean_inc(v_q_6448_);
lean_inc(v_Q_6447_);
lean_inc(v_d_6446_);
lean_inc(v_L_6445_);
lean_inc(v_M_6444_);
lean_inc(v_D_6443_);
lean_inc(v_Y_6442_);
lean_inc(v_u_6441_);
lean_inc(v_y_6440_);
lean_inc(v_G_6439_);
lean_dec(v_date_4647_);
v___x_6476_ = lean_box(0);
v_isShared_6477_ = v_isSharedCheck_6482_;
goto v_resetjp_6475_;
}
v_resetjp_6475_:
{
lean_object* v___x_6478_; lean_object* v___x_6480_; 
v___x_6478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6478_, 0, v_data_4649_);
if (v_isShared_6477_ == 0)
{
lean_ctor_set(v___x_6476_, 36, v___x_6478_);
v___x_6480_ = v___x_6476_;
goto v_reusejp_6479_;
}
else
{
lean_object* v_reuseFailAlloc_6481_; 
v_reuseFailAlloc_6481_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6481_, 0, v_G_6439_);
lean_ctor_set(v_reuseFailAlloc_6481_, 1, v_y_6440_);
lean_ctor_set(v_reuseFailAlloc_6481_, 2, v_u_6441_);
lean_ctor_set(v_reuseFailAlloc_6481_, 3, v_Y_6442_);
lean_ctor_set(v_reuseFailAlloc_6481_, 4, v_D_6443_);
lean_ctor_set(v_reuseFailAlloc_6481_, 5, v_M_6444_);
lean_ctor_set(v_reuseFailAlloc_6481_, 6, v_L_6445_);
lean_ctor_set(v_reuseFailAlloc_6481_, 7, v_d_6446_);
lean_ctor_set(v_reuseFailAlloc_6481_, 8, v_Q_6447_);
lean_ctor_set(v_reuseFailAlloc_6481_, 9, v_q_6448_);
lean_ctor_set(v_reuseFailAlloc_6481_, 10, v_w_6449_);
lean_ctor_set(v_reuseFailAlloc_6481_, 11, v_W_6450_);
lean_ctor_set(v_reuseFailAlloc_6481_, 12, v_E_6451_);
lean_ctor_set(v_reuseFailAlloc_6481_, 13, v_e_6452_);
lean_ctor_set(v_reuseFailAlloc_6481_, 14, v_c_6453_);
lean_ctor_set(v_reuseFailAlloc_6481_, 15, v_F_6454_);
lean_ctor_set(v_reuseFailAlloc_6481_, 16, v_a_6455_);
lean_ctor_set(v_reuseFailAlloc_6481_, 17, v_b_6456_);
lean_ctor_set(v_reuseFailAlloc_6481_, 18, v_B_6457_);
lean_ctor_set(v_reuseFailAlloc_6481_, 19, v_h_6458_);
lean_ctor_set(v_reuseFailAlloc_6481_, 20, v_K_6459_);
lean_ctor_set(v_reuseFailAlloc_6481_, 21, v_k_6460_);
lean_ctor_set(v_reuseFailAlloc_6481_, 22, v_H_6461_);
lean_ctor_set(v_reuseFailAlloc_6481_, 23, v_m_6462_);
lean_ctor_set(v_reuseFailAlloc_6481_, 24, v_s_6463_);
lean_ctor_set(v_reuseFailAlloc_6481_, 25, v_S_6464_);
lean_ctor_set(v_reuseFailAlloc_6481_, 26, v_A_6465_);
lean_ctor_set(v_reuseFailAlloc_6481_, 27, v_n_6466_);
lean_ctor_set(v_reuseFailAlloc_6481_, 28, v_N_6467_);
lean_ctor_set(v_reuseFailAlloc_6481_, 29, v_V_6468_);
lean_ctor_set(v_reuseFailAlloc_6481_, 30, v_z_6469_);
lean_ctor_set(v_reuseFailAlloc_6481_, 31, v_zabbrev_6470_);
lean_ctor_set(v_reuseFailAlloc_6481_, 32, v_v_6471_);
lean_ctor_set(v_reuseFailAlloc_6481_, 33, v_O_6472_);
lean_ctor_set(v_reuseFailAlloc_6481_, 34, v_X_6473_);
lean_ctor_set(v_reuseFailAlloc_6481_, 35, v_x_6474_);
lean_ctor_set(v_reuseFailAlloc_6481_, 36, v___x_6478_);
v___x_6480_ = v_reuseFailAlloc_6481_;
goto v_reusejp_6479_;
}
v_reusejp_6479_:
{
return v___x_6480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(lean_object* v_year_6484_, uint8_t v_x_6485_){
_start:
{
if (v_x_6485_ == 0)
{
lean_object* v___x_6486_; lean_object* v___x_6487_; lean_object* v___x_6488_; 
v___x_6486_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6487_ = lean_int_add(v_year_6484_, v___x_6486_);
v___x_6488_ = lean_int_neg(v___x_6487_);
lean_dec(v___x_6487_);
return v___x_6488_;
}
else
{
lean_inc(v_year_6484_);
return v_year_6484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra___boxed(lean_object* v_year_6489_, lean_object* v_x_6490_){
_start:
{
uint8_t v_x_42__boxed_6491_; lean_object* v_res_6492_; 
v_x_42__boxed_6491_ = lean_unbox(v_x_6490_);
v_res_6492_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_year_6489_, v_x_42__boxed_6491_);
lean_dec(v_year_6489_);
return v_res_6492_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(uint8_t v_x_6493_){
_start:
{
switch(v_x_6493_)
{
case 1:
{
uint8_t v___x_6494_; 
v___x_6494_ = 1;
return v___x_6494_;
}
case 2:
{
uint8_t v___x_6495_; 
v___x_6495_ = 1;
return v___x_6495_;
}
default: 
{
uint8_t v___x_6496_; 
v___x_6496_ = 0;
return v___x_6496_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod___boxed(lean_object* v_x_6497_){
_start:
{
uint8_t v_x_28__boxed_6498_; uint8_t v_res_6499_; lean_object* v_r_6500_; 
v_x_28__boxed_6498_ = lean_unbox(v_x_6497_);
v_res_6499_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v_x_28__boxed_6498_);
v_r_6500_ = lean_box(v_res_6499_);
return v_r_6500_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(uint8_t v_x_6501_){
_start:
{
switch(v_x_6501_)
{
case 3:
{
uint8_t v___x_6502_; 
v___x_6502_ = 1;
return v___x_6502_;
}
case 4:
{
uint8_t v___x_6503_; 
v___x_6503_ = 1;
return v___x_6503_;
}
case 5:
{
uint8_t v___x_6504_; 
v___x_6504_ = 1;
return v___x_6504_;
}
default: 
{
uint8_t v___x_6505_; 
v___x_6505_ = 0;
return v___x_6505_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod___boxed(lean_object* v_x_6506_){
_start:
{
uint8_t v_x_38__boxed_6507_; uint8_t v_res_6508_; lean_object* v_r_6509_; 
v_x_38__boxed_6507_ = lean_unbox(v_x_6506_);
v_res_6508_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v_x_38__boxed_6507_);
v_r_6509_ = lean_box(v_res_6508_);
return v_r_6509_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(lean_object* v_val_6510_, lean_object* v_x_6511_){
_start:
{
lean_inc_ref(v_val_6510_);
return v_val_6510_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed(lean_object* v_val_6512_, lean_object* v_x_6513_){
_start:
{
lean_object* v_res_6514_; 
v_res_6514_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(v_val_6512_, v_x_6513_);
lean_dec_ref(v_val_6512_);
return v_res_6514_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(lean_object* v___y_6515_, lean_object* v_00___6516_){
_start:
{
uint8_t v___x_6517_; lean_object* v___x_6518_; 
v___x_6517_ = 1;
v___x_6518_ = l_Std_Time_TimeZone_Offset_toIsoString(v___y_6515_, v___x_6517_);
return v___x_6518_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1(void){
_start:
{
lean_object* v___x_6521_; lean_object* v___x_6522_; 
v___x_6521_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6522_ = lean_int_neg(v___x_6521_);
return v___x_6522_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2(void){
_start:
{
lean_object* v___x_6523_; lean_object* v___x_6524_; 
v___x_6523_ = lean_unsigned_to_nat(1000000u);
v___x_6524_ = lean_nat_to_int(v___x_6523_);
return v___x_6524_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3(void){
_start:
{
lean_object* v___x_6525_; lean_object* v___x_6526_; lean_object* v___x_6527_; 
v___x_6525_ = lean_unsigned_to_nat(1000000000u);
v___x_6526_ = lean_unsigned_to_nat(0u);
v___x_6527_ = lean_nat_mod(v___x_6526_, v___x_6525_);
return v___x_6527_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4(void){
_start:
{
lean_object* v___x_6528_; lean_object* v___x_6529_; 
v___x_6528_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3);
v___x_6529_ = lean_nat_to_int(v___x_6528_);
return v___x_6529_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5(void){
_start:
{
lean_object* v___x_6530_; uint8_t v___x_6531_; lean_object* v___x_6532_; 
v___x_6530_ = lean_unsigned_to_nat(0u);
v___x_6531_ = 1;
v___x_6532_ = l_Std_Time_Second_instOfNatOrdinal(v___x_6531_, v___x_6530_);
return v___x_6532_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6(void){
_start:
{
lean_object* v___x_6533_; lean_object* v___x_6534_; lean_object* v___x_6535_; 
v___x_6533_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3);
v___x_6534_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6535_ = lean_int_add(v___x_6534_, v___x_6533_);
return v___x_6535_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7(void){
_start:
{
lean_object* v___x_6536_; lean_object* v___x_6537_; lean_object* v___x_6538_; 
v___x_6536_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6537_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6);
v___x_6538_ = lean_int_sub(v___x_6537_, v___x_6536_);
return v___x_6538_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8(void){
_start:
{
lean_object* v___x_6539_; lean_object* v___x_6540_; lean_object* v_range_6541_; 
v___x_6539_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6540_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7);
v_range_6541_ = lean_int_add(v___x_6540_, v___x_6539_);
return v_range_6541_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9(void){
_start:
{
lean_object* v___x_6542_; lean_object* v___x_6543_; 
v___x_6542_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6543_ = lean_int_sub(v___x_6542_, v___x_6542_);
return v___x_6543_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10(void){
_start:
{
lean_object* v_range_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; 
v_range_6544_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8);
v___x_6545_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9);
v___x_6546_ = lean_int_emod(v___x_6545_, v_range_6544_);
return v___x_6546_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11(void){
_start:
{
lean_object* v_range_6547_; lean_object* v___x_6548_; lean_object* v___x_6549_; 
v_range_6547_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8);
v___x_6548_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10);
v___x_6549_ = lean_int_add(v___x_6548_, v_range_6547_);
return v___x_6549_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12(void){
_start:
{
lean_object* v_range_6550_; lean_object* v___x_6551_; lean_object* v___x_6552_; 
v_range_6550_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8);
v___x_6551_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11);
v___x_6552_ = lean_int_emod(v___x_6551_, v_range_6550_);
return v___x_6552_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13(void){
_start:
{
lean_object* v___x_6553_; lean_object* v___x_6554_; lean_object* v___x_6555_; 
v___x_6553_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6554_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12);
v___x_6555_ = lean_int_add(v___x_6554_, v___x_6553_);
return v___x_6555_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14(void){
_start:
{
lean_object* v___x_6556_; lean_object* v___x_6557_; 
v___x_6556_ = lean_unsigned_to_nat(30u);
v___x_6557_ = lean_nat_to_int(v___x_6556_);
return v___x_6557_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15(void){
_start:
{
lean_object* v___x_6558_; lean_object* v___x_6559_; lean_object* v___x_6560_; 
v___x_6558_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14);
v___x_6559_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6560_ = lean_int_add(v___x_6559_, v___x_6558_);
return v___x_6560_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16(void){
_start:
{
lean_object* v___x_6561_; lean_object* v___x_6562_; lean_object* v___x_6563_; 
v___x_6561_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6562_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v___x_6563_ = lean_int_sub(v___x_6562_, v___x_6561_);
return v___x_6563_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17(void){
_start:
{
lean_object* v___x_6564_; lean_object* v___x_6565_; lean_object* v_range_6566_; 
v___x_6564_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6565_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16);
v_range_6566_ = lean_int_add(v___x_6565_, v___x_6564_);
return v_range_6566_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18(void){
_start:
{
lean_object* v___x_6567_; lean_object* v___x_6568_; lean_object* v___x_6569_; 
v___x_6567_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6568_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6569_ = lean_int_sub(v___x_6568_, v___x_6567_);
return v___x_6569_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19(void){
_start:
{
lean_object* v_range_6570_; lean_object* v___x_6571_; lean_object* v___x_6572_; 
v_range_6570_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17);
v___x_6571_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18);
v___x_6572_ = lean_int_emod(v___x_6571_, v_range_6570_);
return v___x_6572_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20(void){
_start:
{
lean_object* v_range_6573_; lean_object* v___x_6574_; lean_object* v___x_6575_; 
v_range_6573_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17);
v___x_6574_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19);
v___x_6575_ = lean_int_add(v___x_6574_, v_range_6573_);
return v___x_6575_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21(void){
_start:
{
lean_object* v_range_6576_; lean_object* v___x_6577_; lean_object* v___x_6578_; 
v_range_6576_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17);
v___x_6577_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20);
v___x_6578_ = lean_int_emod(v___x_6577_, v_range_6576_);
return v___x_6578_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22(void){
_start:
{
lean_object* v___x_6579_; lean_object* v___x_6580_; lean_object* v___x_6581_; 
v___x_6579_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6580_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21);
v___x_6581_ = lean_int_add(v___x_6580_, v___x_6579_);
return v___x_6581_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23(void){
_start:
{
lean_object* v___x_6582_; lean_object* v___x_6583_; 
v___x_6582_ = lean_unsigned_to_nat(11u);
v___x_6583_ = lean_nat_to_int(v___x_6582_);
return v___x_6583_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24(void){
_start:
{
lean_object* v___x_6584_; lean_object* v___x_6585_; lean_object* v___x_6586_; 
v___x_6584_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23);
v___x_6585_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6586_ = lean_int_add(v___x_6585_, v___x_6584_);
return v___x_6586_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25(void){
_start:
{
lean_object* v___x_6587_; lean_object* v___x_6588_; lean_object* v___x_6589_; 
v___x_6587_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6588_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24);
v___x_6589_ = lean_int_sub(v___x_6588_, v___x_6587_);
return v___x_6589_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26(void){
_start:
{
lean_object* v___x_6590_; lean_object* v___x_6591_; lean_object* v_range_6592_; 
v___x_6590_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6591_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25);
v_range_6592_ = lean_int_add(v___x_6591_, v___x_6590_);
return v_range_6592_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27(void){
_start:
{
lean_object* v_range_6593_; lean_object* v___x_6594_; lean_object* v___x_6595_; 
v_range_6593_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26);
v___x_6594_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18);
v___x_6595_ = lean_int_emod(v___x_6594_, v_range_6593_);
return v___x_6595_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28(void){
_start:
{
lean_object* v_range_6596_; lean_object* v___x_6597_; lean_object* v___x_6598_; 
v_range_6596_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26);
v___x_6597_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27);
v___x_6598_ = lean_int_add(v___x_6597_, v_range_6596_);
return v___x_6598_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29(void){
_start:
{
lean_object* v_range_6599_; lean_object* v___x_6600_; lean_object* v___x_6601_; 
v_range_6599_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26);
v___x_6600_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28);
v___x_6601_ = lean_int_emod(v___x_6600_, v_range_6599_);
return v___x_6601_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__30(void){
_start:
{
lean_object* v___x_6602_; lean_object* v___x_6603_; lean_object* v___x_6604_; 
v___x_6602_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6603_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29);
v___x_6604_ = lean_int_add(v___x_6603_, v___x_6602_);
return v___x_6604_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(lean_object* v_builder_6605_, lean_object* v_aw_6606_){
_start:
{
lean_object* v___y_6608_; lean_object* v___y_6609_; lean_object* v___y_6648_; lean_object* v___y_6649_; lean_object* v___y_6652_; lean_object* v___y_6653_; lean_object* v___y_6654_; lean_object* v___y_6655_; lean_object* v___y_6656_; uint8_t v___y_6657_; lean_object* v___y_6665_; lean_object* v___y_6666_; lean_object* v___y_6667_; lean_object* v___y_6668_; uint8_t v___y_6669_; lean_object* v___y_6670_; uint8_t v___y_6671_; lean_object* v___y_6673_; lean_object* v___y_6674_; lean_object* v___y_6675_; lean_object* v___y_6676_; lean_object* v___y_6677_; lean_object* v_G_6689_; lean_object* v_y_6690_; lean_object* v_u_6691_; lean_object* v_Y_6692_; lean_object* v_M_6693_; lean_object* v_L_6694_; lean_object* v_d_6695_; lean_object* v_a_6696_; lean_object* v_b_6697_; lean_object* v_B_6698_; lean_object* v_h_6699_; lean_object* v_K_6700_; lean_object* v_k_6701_; lean_object* v_H_6702_; lean_object* v_m_6703_; lean_object* v_s_6704_; lean_object* v_S_6705_; lean_object* v_A_6706_; lean_object* v_n_6707_; lean_object* v_N_6708_; lean_object* v_V_6709_; lean_object* v_z_6710_; lean_object* v_zabbrev_6711_; lean_object* v_v_6712_; lean_object* v_O_6713_; lean_object* v_X_6714_; lean_object* v_x_6715_; lean_object* v_Z_6716_; lean_object* v___y_6718_; lean_object* v___y_6719_; lean_object* v___y_6720_; lean_object* v___y_6721_; lean_object* v___y_6722_; lean_object* v___y_6723_; lean_object* v___y_6724_; lean_object* v___y_6725_; lean_object* v___y_6734_; lean_object* v___y_6735_; lean_object* v___y_6736_; lean_object* v___y_6737_; lean_object* v___y_6738_; lean_object* v___y_6739_; lean_object* v___y_6740_; lean_object* v___y_6745_; lean_object* v___y_6746_; lean_object* v___y_6747_; lean_object* v___y_6748_; lean_object* v___y_6749_; lean_object* v___y_6750_; lean_object* v___y_6754_; lean_object* v___y_6755_; lean_object* v___y_6756_; lean_object* v___y_6757_; lean_object* v___y_6758_; lean_object* v___y_6762_; lean_object* v___y_6763_; lean_object* v___y_6764_; lean_object* v___y_6765_; lean_object* v___y_6773_; lean_object* v___y_6774_; lean_object* v___y_6775_; lean_object* v___y_6776_; uint8_t v_val_6777_; lean_object* v___y_6785_; lean_object* v___y_6786_; lean_object* v___y_6787_; lean_object* v___y_6788_; lean_object* v___y_6798_; lean_object* v___y_6799_; lean_object* v___y_6800_; uint8_t v___y_6801_; lean_object* v___y_6808_; lean_object* v___y_6809_; lean_object* v___y_6810_; lean_object* v___y_6815_; lean_object* v___y_6816_; lean_object* v___y_6820_; lean_object* v___y_6821_; lean_object* v___y_6822_; lean_object* v___y_6829_; lean_object* v___y_6830_; lean_object* v___y_6831_; lean_object* v___y_6836_; 
v_G_6689_ = lean_ctor_get(v_builder_6605_, 0);
lean_inc(v_G_6689_);
v_y_6690_ = lean_ctor_get(v_builder_6605_, 1);
lean_inc(v_y_6690_);
v_u_6691_ = lean_ctor_get(v_builder_6605_, 2);
lean_inc(v_u_6691_);
v_Y_6692_ = lean_ctor_get(v_builder_6605_, 3);
lean_inc(v_Y_6692_);
v_M_6693_ = lean_ctor_get(v_builder_6605_, 5);
lean_inc(v_M_6693_);
v_L_6694_ = lean_ctor_get(v_builder_6605_, 6);
lean_inc(v_L_6694_);
v_d_6695_ = lean_ctor_get(v_builder_6605_, 7);
lean_inc(v_d_6695_);
v_a_6696_ = lean_ctor_get(v_builder_6605_, 16);
lean_inc(v_a_6696_);
v_b_6697_ = lean_ctor_get(v_builder_6605_, 17);
lean_inc(v_b_6697_);
v_B_6698_ = lean_ctor_get(v_builder_6605_, 18);
lean_inc(v_B_6698_);
v_h_6699_ = lean_ctor_get(v_builder_6605_, 19);
lean_inc(v_h_6699_);
v_K_6700_ = lean_ctor_get(v_builder_6605_, 20);
lean_inc(v_K_6700_);
v_k_6701_ = lean_ctor_get(v_builder_6605_, 21);
lean_inc(v_k_6701_);
v_H_6702_ = lean_ctor_get(v_builder_6605_, 22);
lean_inc(v_H_6702_);
v_m_6703_ = lean_ctor_get(v_builder_6605_, 23);
lean_inc(v_m_6703_);
v_s_6704_ = lean_ctor_get(v_builder_6605_, 24);
lean_inc(v_s_6704_);
v_S_6705_ = lean_ctor_get(v_builder_6605_, 25);
lean_inc(v_S_6705_);
v_A_6706_ = lean_ctor_get(v_builder_6605_, 26);
lean_inc(v_A_6706_);
v_n_6707_ = lean_ctor_get(v_builder_6605_, 27);
lean_inc(v_n_6707_);
v_N_6708_ = lean_ctor_get(v_builder_6605_, 28);
lean_inc(v_N_6708_);
v_V_6709_ = lean_ctor_get(v_builder_6605_, 29);
lean_inc(v_V_6709_);
v_z_6710_ = lean_ctor_get(v_builder_6605_, 30);
lean_inc(v_z_6710_);
v_zabbrev_6711_ = lean_ctor_get(v_builder_6605_, 31);
lean_inc(v_zabbrev_6711_);
v_v_6712_ = lean_ctor_get(v_builder_6605_, 32);
lean_inc(v_v_6712_);
v_O_6713_ = lean_ctor_get(v_builder_6605_, 33);
lean_inc(v_O_6713_);
v_X_6714_ = lean_ctor_get(v_builder_6605_, 34);
lean_inc(v_X_6714_);
v_x_6715_ = lean_ctor_get(v_builder_6605_, 35);
lean_inc(v_x_6715_);
v_Z_6716_ = lean_ctor_get(v_builder_6605_, 36);
lean_inc(v_Z_6716_);
lean_dec_ref(v_builder_6605_);
if (lean_obj_tag(v_O_6713_) == 0)
{
if (lean_obj_tag(v_X_6714_) == 0)
{
if (lean_obj_tag(v_x_6715_) == 0)
{
if (lean_obj_tag(v_Z_6716_) == 0)
{
lean_object* v___x_6843_; 
v___x_6843_ = l_Std_Time_TimeZone_Offset_zero;
v___y_6836_ = v___x_6843_;
goto v___jp_6835_;
}
else
{
lean_object* v_val_6844_; 
v_val_6844_ = lean_ctor_get(v_Z_6716_, 0);
lean_inc(v_val_6844_);
lean_dec_ref_known(v_Z_6716_, 1);
v___y_6836_ = v_val_6844_;
goto v___jp_6835_;
}
}
else
{
lean_object* v_val_6845_; 
lean_dec(v_Z_6716_);
v_val_6845_ = lean_ctor_get(v_x_6715_, 0);
lean_inc(v_val_6845_);
lean_dec_ref_known(v_x_6715_, 1);
v___y_6836_ = v_val_6845_;
goto v___jp_6835_;
}
}
else
{
lean_object* v_val_6846_; 
lean_dec(v_Z_6716_);
lean_dec(v_x_6715_);
v_val_6846_ = lean_ctor_get(v_X_6714_, 0);
lean_inc(v_val_6846_);
lean_dec_ref_known(v_X_6714_, 1);
v___y_6836_ = v_val_6846_;
goto v___jp_6835_;
}
}
else
{
lean_object* v_val_6847_; 
lean_dec(v_Z_6716_);
lean_dec(v_x_6715_);
lean_dec(v_X_6714_);
v_val_6847_ = lean_ctor_get(v_O_6713_, 0);
lean_inc(v_val_6847_);
lean_dec_ref_known(v_O_6713_, 1);
v___y_6836_ = v_val_6847_;
goto v___jp_6835_;
}
v___jp_6607_:
{
if (lean_obj_tag(v___y_6608_) == 0)
{
lean_object* v___x_6610_; 
lean_dec_ref(v___y_6609_);
v___x_6610_ = lean_box(0);
return v___x_6610_;
}
else
{
lean_object* v_val_6611_; lean_object* v___x_6613_; uint8_t v_isShared_6614_; uint8_t v_isSharedCheck_6646_; 
v_val_6611_ = lean_ctor_get(v___y_6608_, 0);
v_isSharedCheck_6646_ = !lean_is_exclusive(v___y_6608_);
if (v_isSharedCheck_6646_ == 0)
{
v___x_6613_ = v___y_6608_;
v_isShared_6614_ = v_isSharedCheck_6646_;
goto v_resetjp_6612_;
}
else
{
lean_inc(v_val_6611_);
lean_dec(v___y_6608_);
v___x_6613_ = lean_box(0);
v_isShared_6614_ = v_isSharedCheck_6646_;
goto v_resetjp_6612_;
}
v_resetjp_6612_:
{
lean_object* v_offset_6615_; lean_object* v_name_6616_; lean_object* v_abbreviation_6617_; uint8_t v_isDST_6618_; uint8_t v___x_6619_; uint8_t v___x_6620_; lean_object* v_ltt_6621_; lean_object* v___x_6622_; lean_object* v___x_6623_; lean_object* v___x_6624_; lean_object* v_wt_6625_; lean_object* v_ltt_6626_; lean_object* v_tz_6627_; lean_object* v_offset_6628_; lean_object* v_second_6629_; lean_object* v_nano_6630_; lean_object* v___f_6631_; lean_object* v___x_6632_; lean_object* v___x_6633_; lean_object* v___x_6634_; lean_object* v___x_6635_; lean_object* v___x_6636_; lean_object* v___x_6637_; lean_object* v___x_6638_; lean_object* v___x_6639_; lean_object* v___x_6640_; lean_object* v___x_6641_; lean_object* v___x_6642_; lean_object* v___x_6644_; 
v_offset_6615_ = lean_ctor_get(v___y_6609_, 0);
lean_inc(v_offset_6615_);
v_name_6616_ = lean_ctor_get(v___y_6609_, 1);
lean_inc_ref(v_name_6616_);
v_abbreviation_6617_ = lean_ctor_get(v___y_6609_, 2);
lean_inc_ref(v_abbreviation_6617_);
v_isDST_6618_ = lean_ctor_get_uint8(v___y_6609_, sizeof(void*)*3);
lean_dec_ref(v___y_6609_);
v___x_6619_ = 0;
v___x_6620_ = 1;
v_ltt_6621_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6621_, 0, v_offset_6615_);
lean_ctor_set(v_ltt_6621_, 1, v_abbreviation_6617_);
lean_ctor_set(v_ltt_6621_, 2, v_name_6616_);
lean_ctor_set_uint8(v_ltt_6621_, sizeof(void*)*3, v_isDST_6618_);
lean_ctor_set_uint8(v_ltt_6621_, sizeof(void*)*3 + 1, v___x_6619_);
lean_ctor_set_uint8(v_ltt_6621_, sizeof(void*)*3 + 2, v___x_6620_);
v___x_6622_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6623_ = lean_box(0);
v___x_6624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6624_, 0, v_ltt_6621_);
lean_ctor_set(v___x_6624_, 1, v___x_6622_);
lean_ctor_set(v___x_6624_, 2, v___x_6623_);
lean_inc(v_val_6611_);
v_wt_6625_ = l_Std_Time_PlainDateTime_toWallTime(v_val_6611_);
lean_inc_ref(v___x_6624_);
v_ltt_6626_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_6624_, v_wt_6625_);
v_tz_6627_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_6626_);
lean_dec_ref(v_ltt_6626_);
v_offset_6628_ = lean_ctor_get(v_tz_6627_, 0);
lean_inc(v_offset_6628_);
v_second_6629_ = lean_ctor_get(v_wt_6625_, 0);
lean_inc(v_second_6629_);
v_nano_6630_ = lean_ctor_get(v_wt_6625_, 1);
lean_inc(v_nano_6630_);
lean_dec_ref(v_wt_6625_);
v___f_6631_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed), 2, 1);
lean_closure_set(v___f_6631_, 0, v_val_6611_);
v___x_6632_ = lean_mk_thunk(v___f_6631_);
v___x_6633_ = lean_int_neg(v_offset_6628_);
lean_dec(v_offset_6628_);
v___x_6634_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1);
v___x_6635_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_6636_ = lean_int_mul(v_second_6629_, v___x_6635_);
lean_dec(v_second_6629_);
v___x_6637_ = lean_int_add(v___x_6636_, v_nano_6630_);
lean_dec(v_nano_6630_);
lean_dec(v___x_6636_);
v___x_6638_ = lean_int_mul(v___x_6633_, v___x_6635_);
lean_dec(v___x_6633_);
v___x_6639_ = lean_int_add(v___x_6638_, v___x_6634_);
lean_dec(v___x_6638_);
v___x_6640_ = lean_int_add(v___x_6637_, v___x_6639_);
lean_dec(v___x_6639_);
lean_dec(v___x_6637_);
v___x_6641_ = l_Std_Time_Duration_ofNanoseconds(v___x_6640_);
lean_dec(v___x_6640_);
v___x_6642_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6642_, 0, v___x_6632_);
lean_ctor_set(v___x_6642_, 1, v___x_6641_);
lean_ctor_set(v___x_6642_, 2, v___x_6624_);
lean_ctor_set(v___x_6642_, 3, v_tz_6627_);
if (v_isShared_6614_ == 0)
{
lean_ctor_set(v___x_6613_, 0, v___x_6642_);
v___x_6644_ = v___x_6613_;
goto v_reusejp_6643_;
}
else
{
lean_object* v_reuseFailAlloc_6645_; 
v_reuseFailAlloc_6645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6645_, 0, v___x_6642_);
v___x_6644_ = v_reuseFailAlloc_6645_;
goto v_reusejp_6643_;
}
v_reusejp_6643_:
{
return v___x_6644_;
}
}
}
}
v___jp_6647_:
{
if (lean_obj_tag(v_aw_6606_) == 0)
{
lean_object* v_a_6650_; 
lean_dec_ref(v___y_6648_);
v_a_6650_ = lean_ctor_get(v_aw_6606_, 0);
lean_inc_ref(v_a_6650_);
lean_dec_ref_known(v_aw_6606_, 1);
v___y_6608_ = v___y_6649_;
v___y_6609_ = v_a_6650_;
goto v___jp_6607_;
}
else
{
v___y_6608_ = v___y_6649_;
v___y_6609_ = v___y_6648_;
goto v___jp_6607_;
}
}
v___jp_6651_:
{
lean_object* v___x_6658_; uint8_t v___x_6659_; 
v___x_6658_ = l_Std_Time_Month_Ordinal_days(v___y_6657_, v___y_6656_);
v___x_6659_ = lean_int_dec_le(v___y_6654_, v___x_6658_);
lean_dec(v___x_6658_);
if (v___x_6659_ == 0)
{
lean_object* v___x_6660_; 
lean_dec(v___y_6656_);
lean_dec_ref(v___y_6655_);
lean_dec(v___y_6654_);
lean_dec(v___y_6652_);
v___x_6660_ = lean_box(0);
v___y_6648_ = v___y_6653_;
v___y_6649_ = v___x_6660_;
goto v___jp_6647_;
}
else
{
lean_object* v_date_6661_; lean_object* v___x_6662_; lean_object* v___x_6663_; 
v_date_6661_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_date_6661_, 0, v___y_6652_);
lean_ctor_set(v_date_6661_, 1, v___y_6656_);
lean_ctor_set(v_date_6661_, 2, v___y_6654_);
v___x_6662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6662_, 0, v_date_6661_);
lean_ctor_set(v___x_6662_, 1, v___y_6655_);
v___x_6663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6663_, 0, v___x_6662_);
v___y_6648_ = v___y_6653_;
v___y_6649_ = v___x_6663_;
goto v___jp_6647_;
}
}
v___jp_6664_:
{
if (v___y_6669_ == 0)
{
v___y_6652_ = v___y_6667_;
v___y_6653_ = v___y_6666_;
v___y_6654_ = v___y_6665_;
v___y_6655_ = v___y_6668_;
v___y_6656_ = v___y_6670_;
v___y_6657_ = v___y_6669_;
goto v___jp_6651_;
}
else
{
v___y_6652_ = v___y_6667_;
v___y_6653_ = v___y_6666_;
v___y_6654_ = v___y_6665_;
v___y_6655_ = v___y_6668_;
v___y_6656_ = v___y_6670_;
v___y_6657_ = v___y_6671_;
goto v___jp_6651_;
}
}
v___jp_6672_:
{
lean_object* v___x_6678_; lean_object* v___x_6679_; lean_object* v___x_6680_; uint8_t v___x_6681_; lean_object* v___x_6682_; lean_object* v___x_6683_; uint8_t v___x_6684_; 
v___x_6678_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_6679_ = lean_int_mod(v___y_6675_, v___x_6678_);
v___x_6680_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6681_ = lean_int_dec_eq(v___x_6679_, v___x_6680_);
lean_dec(v___x_6679_);
v___x_6682_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_6683_ = lean_int_mod(v___y_6675_, v___x_6682_);
v___x_6684_ = lean_int_dec_eq(v___x_6683_, v___x_6680_);
lean_dec(v___x_6683_);
if (v___x_6684_ == 0)
{
uint8_t v___x_6685_; 
v___x_6685_ = 1;
v___y_6665_ = v___y_6673_;
v___y_6666_ = v___y_6674_;
v___y_6667_ = v___y_6675_;
v___y_6668_ = v___y_6677_;
v___y_6669_ = v___x_6681_;
v___y_6670_ = v___y_6676_;
v___y_6671_ = v___x_6685_;
goto v___jp_6664_;
}
else
{
lean_object* v___x_6686_; lean_object* v___x_6687_; uint8_t v___x_6688_; 
v___x_6686_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_6687_ = lean_int_mod(v___y_6675_, v___x_6686_);
v___x_6688_ = lean_int_dec_eq(v___x_6687_, v___x_6680_);
lean_dec(v___x_6687_);
v___y_6665_ = v___y_6673_;
v___y_6666_ = v___y_6674_;
v___y_6667_ = v___y_6675_;
v___y_6668_ = v___y_6677_;
v___y_6669_ = v___x_6681_;
v___y_6670_ = v___y_6676_;
v___y_6671_ = v___x_6688_;
goto v___jp_6664_;
}
}
v___jp_6717_:
{
if (lean_obj_tag(v_N_6708_) == 0)
{
if (lean_obj_tag(v_A_6706_) == 0)
{
lean_object* v___x_6726_; 
v___x_6726_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6726_, 0, v___y_6723_);
lean_ctor_set(v___x_6726_, 1, v___y_6722_);
lean_ctor_set(v___x_6726_, 2, v___y_6721_);
lean_ctor_set(v___x_6726_, 3, v___y_6725_);
v___y_6673_ = v___y_6720_;
v___y_6674_ = v___y_6719_;
v___y_6675_ = v___y_6718_;
v___y_6676_ = v___y_6724_;
v___y_6677_ = v___x_6726_;
goto v___jp_6672_;
}
else
{
lean_object* v_val_6727_; lean_object* v___x_6728_; lean_object* v___x_6729_; lean_object* v___x_6730_; 
lean_dec(v___y_6725_);
lean_dec(v___y_6723_);
lean_dec(v___y_6722_);
lean_dec(v___y_6721_);
v_val_6727_ = lean_ctor_get(v_A_6706_, 0);
lean_inc(v_val_6727_);
lean_dec_ref_known(v_A_6706_, 1);
v___x_6728_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2);
v___x_6729_ = lean_int_mul(v_val_6727_, v___x_6728_);
lean_dec(v_val_6727_);
v___x_6730_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_6729_);
lean_dec(v___x_6729_);
v___y_6673_ = v___y_6720_;
v___y_6674_ = v___y_6719_;
v___y_6675_ = v___y_6718_;
v___y_6676_ = v___y_6724_;
v___y_6677_ = v___x_6730_;
goto v___jp_6672_;
}
}
else
{
lean_object* v_val_6731_; lean_object* v___x_6732_; 
lean_dec(v___y_6725_);
lean_dec(v___y_6723_);
lean_dec(v___y_6722_);
lean_dec(v___y_6721_);
lean_dec(v_A_6706_);
v_val_6731_ = lean_ctor_get(v_N_6708_, 0);
lean_inc(v_val_6731_);
lean_dec_ref_known(v_N_6708_, 1);
v___x_6732_ = l_Std_Time_PlainTime_ofNanoseconds(v_val_6731_);
lean_dec(v_val_6731_);
v___y_6673_ = v___y_6720_;
v___y_6674_ = v___y_6719_;
v___y_6675_ = v___y_6718_;
v___y_6676_ = v___y_6724_;
v___y_6677_ = v___x_6732_;
goto v___jp_6672_;
}
}
v___jp_6733_:
{
if (lean_obj_tag(v_n_6707_) == 0)
{
if (lean_obj_tag(v_S_6705_) == 0)
{
lean_object* v___x_6741_; 
v___x_6741_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4);
v___y_6718_ = v___y_6736_;
v___y_6719_ = v___y_6735_;
v___y_6720_ = v___y_6734_;
v___y_6721_ = v___y_6740_;
v___y_6722_ = v___y_6738_;
v___y_6723_ = v___y_6737_;
v___y_6724_ = v___y_6739_;
v___y_6725_ = v___x_6741_;
goto v___jp_6717_;
}
else
{
lean_object* v_val_6742_; 
v_val_6742_ = lean_ctor_get(v_S_6705_, 0);
lean_inc(v_val_6742_);
lean_dec_ref_known(v_S_6705_, 1);
v___y_6718_ = v___y_6736_;
v___y_6719_ = v___y_6735_;
v___y_6720_ = v___y_6734_;
v___y_6721_ = v___y_6740_;
v___y_6722_ = v___y_6738_;
v___y_6723_ = v___y_6737_;
v___y_6724_ = v___y_6739_;
v___y_6725_ = v_val_6742_;
goto v___jp_6717_;
}
}
else
{
lean_object* v_val_6743_; 
lean_dec(v_S_6705_);
v_val_6743_ = lean_ctor_get(v_n_6707_, 0);
lean_inc(v_val_6743_);
lean_dec_ref_known(v_n_6707_, 1);
v___y_6718_ = v___y_6736_;
v___y_6719_ = v___y_6735_;
v___y_6720_ = v___y_6734_;
v___y_6721_ = v___y_6740_;
v___y_6722_ = v___y_6738_;
v___y_6723_ = v___y_6737_;
v___y_6724_ = v___y_6739_;
v___y_6725_ = v_val_6743_;
goto v___jp_6717_;
}
}
v___jp_6744_:
{
if (lean_obj_tag(v_s_6704_) == 0)
{
lean_object* v___x_6751_; 
v___x_6751_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5);
v___y_6734_ = v___y_6747_;
v___y_6735_ = v___y_6746_;
v___y_6736_ = v___y_6745_;
v___y_6737_ = v___y_6748_;
v___y_6738_ = v___y_6750_;
v___y_6739_ = v___y_6749_;
v___y_6740_ = v___x_6751_;
goto v___jp_6733_;
}
else
{
lean_object* v_val_6752_; 
v_val_6752_ = lean_ctor_get(v_s_6704_, 0);
lean_inc(v_val_6752_);
lean_dec_ref_known(v_s_6704_, 1);
v___y_6734_ = v___y_6747_;
v___y_6735_ = v___y_6746_;
v___y_6736_ = v___y_6745_;
v___y_6737_ = v___y_6748_;
v___y_6738_ = v___y_6750_;
v___y_6739_ = v___y_6749_;
v___y_6740_ = v_val_6752_;
goto v___jp_6733_;
}
}
v___jp_6753_:
{
if (lean_obj_tag(v_m_6703_) == 0)
{
lean_object* v___x_6759_; 
v___x_6759_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13);
v___y_6745_ = v___y_6756_;
v___y_6746_ = v___y_6755_;
v___y_6747_ = v___y_6754_;
v___y_6748_ = v___y_6758_;
v___y_6749_ = v___y_6757_;
v___y_6750_ = v___x_6759_;
goto v___jp_6744_;
}
else
{
lean_object* v_val_6760_; 
v_val_6760_ = lean_ctor_get(v_m_6703_, 0);
lean_inc(v_val_6760_);
lean_dec_ref_known(v_m_6703_, 1);
v___y_6745_ = v___y_6756_;
v___y_6746_ = v___y_6755_;
v___y_6747_ = v___y_6754_;
v___y_6748_ = v___y_6758_;
v___y_6749_ = v___y_6757_;
v___y_6750_ = v_val_6760_;
goto v___jp_6744_;
}
}
v___jp_6761_:
{
if (lean_obj_tag(v_k_6701_) == 0)
{
if (lean_obj_tag(v_H_6702_) == 0)
{
lean_object* v___x_6766_; 
v___x_6766_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6754_ = v___y_6764_;
v___y_6755_ = v___y_6763_;
v___y_6756_ = v___y_6762_;
v___y_6757_ = v___y_6765_;
v___y_6758_ = v___x_6766_;
goto v___jp_6753_;
}
else
{
lean_object* v_val_6767_; 
v_val_6767_ = lean_ctor_get(v_H_6702_, 0);
lean_inc(v_val_6767_);
lean_dec_ref_known(v_H_6702_, 1);
v___y_6754_ = v___y_6764_;
v___y_6755_ = v___y_6763_;
v___y_6756_ = v___y_6762_;
v___y_6757_ = v___y_6765_;
v___y_6758_ = v_val_6767_;
goto v___jp_6753_;
}
}
else
{
if (lean_obj_tag(v_H_6702_) == 0)
{
lean_object* v_val_6768_; lean_object* v___x_6769_; lean_object* v___x_6770_; 
v_val_6768_ = lean_ctor_get(v_k_6701_, 0);
lean_inc(v_val_6768_);
lean_dec_ref_known(v_k_6701_, 1);
v___x_6769_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_6770_ = lean_int_add(v_val_6768_, v___x_6769_);
lean_dec(v_val_6768_);
v___y_6754_ = v___y_6764_;
v___y_6755_ = v___y_6763_;
v___y_6756_ = v___y_6762_;
v___y_6757_ = v___y_6765_;
v___y_6758_ = v___x_6770_;
goto v___jp_6753_;
}
else
{
lean_object* v_val_6771_; 
lean_dec_ref_known(v_k_6701_, 1);
v_val_6771_ = lean_ctor_get(v_H_6702_, 0);
lean_inc(v_val_6771_);
lean_dec_ref_known(v_H_6702_, 1);
v___y_6754_ = v___y_6764_;
v___y_6755_ = v___y_6763_;
v___y_6756_ = v___y_6762_;
v___y_6757_ = v___y_6765_;
v___y_6758_ = v_val_6771_;
goto v___jp_6753_;
}
}
}
v___jp_6772_:
{
if (lean_obj_tag(v_h_6699_) == 0)
{
if (lean_obj_tag(v_K_6700_) == 0)
{
v___y_6762_ = v___y_6775_;
v___y_6763_ = v___y_6774_;
v___y_6764_ = v___y_6773_;
v___y_6765_ = v___y_6776_;
goto v___jp_6761_;
}
else
{
lean_object* v_val_6778_; lean_object* v___x_6779_; lean_object* v___x_6780_; lean_object* v___x_6781_; 
lean_dec(v_H_6702_);
lean_dec(v_k_6701_);
v_val_6778_ = lean_ctor_get(v_K_6700_, 0);
lean_inc(v_val_6778_);
lean_dec_ref_known(v_K_6700_, 1);
v___x_6779_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6780_ = lean_int_add(v_val_6778_, v___x_6779_);
lean_dec(v_val_6778_);
v___x_6781_ = l_Std_Time_HourMarker_toAbsolute(v_val_6777_, v___x_6780_);
lean_dec(v___x_6780_);
v___y_6754_ = v___y_6773_;
v___y_6755_ = v___y_6774_;
v___y_6756_ = v___y_6775_;
v___y_6757_ = v___y_6776_;
v___y_6758_ = v___x_6781_;
goto v___jp_6753_;
}
}
else
{
lean_object* v_val_6782_; lean_object* v___x_6783_; 
lean_dec(v_H_6702_);
lean_dec(v_k_6701_);
lean_dec(v_K_6700_);
v_val_6782_ = lean_ctor_get(v_h_6699_, 0);
lean_inc(v_val_6782_);
lean_dec_ref_known(v_h_6699_, 1);
v___x_6783_ = l_Std_Time_HourMarker_toAbsolute(v_val_6777_, v_val_6782_);
lean_dec(v_val_6782_);
v___y_6754_ = v___y_6773_;
v___y_6755_ = v___y_6774_;
v___y_6756_ = v___y_6775_;
v___y_6757_ = v___y_6776_;
v___y_6758_ = v___x_6783_;
goto v___jp_6753_;
}
}
v___jp_6784_:
{
if (lean_obj_tag(v_a_6696_) == 0)
{
if (lean_obj_tag(v_b_6697_) == 0)
{
if (lean_obj_tag(v_B_6698_) == 0)
{
lean_dec(v_K_6700_);
lean_dec(v_h_6699_);
v___y_6762_ = v___y_6788_;
v___y_6763_ = v___y_6785_;
v___y_6764_ = v___y_6786_;
v___y_6765_ = v___y_6787_;
goto v___jp_6761_;
}
else
{
lean_object* v_val_6789_; uint8_t v___x_6790_; uint8_t v___x_6791_; 
v_val_6789_ = lean_ctor_get(v_B_6698_, 0);
lean_inc(v_val_6789_);
lean_dec_ref_known(v_B_6698_, 1);
v___x_6790_ = lean_unbox(v_val_6789_);
lean_dec(v_val_6789_);
v___x_6791_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v___x_6790_);
v___y_6773_ = v___y_6786_;
v___y_6774_ = v___y_6785_;
v___y_6775_ = v___y_6788_;
v___y_6776_ = v___y_6787_;
v_val_6777_ = v___x_6791_;
goto v___jp_6772_;
}
}
else
{
lean_object* v_val_6792_; uint8_t v___x_6793_; uint8_t v___x_6794_; 
lean_dec(v_B_6698_);
v_val_6792_ = lean_ctor_get(v_b_6697_, 0);
lean_inc(v_val_6792_);
lean_dec_ref_known(v_b_6697_, 1);
v___x_6793_ = lean_unbox(v_val_6792_);
lean_dec(v_val_6792_);
v___x_6794_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v___x_6793_);
v___y_6773_ = v___y_6786_;
v___y_6774_ = v___y_6785_;
v___y_6775_ = v___y_6788_;
v___y_6776_ = v___y_6787_;
v_val_6777_ = v___x_6794_;
goto v___jp_6772_;
}
}
else
{
lean_object* v_val_6795_; uint8_t v___x_6796_; 
lean_dec(v_B_6698_);
lean_dec(v_b_6697_);
v_val_6795_ = lean_ctor_get(v_a_6696_, 0);
lean_inc(v_val_6795_);
lean_dec_ref_known(v_a_6696_, 1);
v___x_6796_ = lean_unbox(v_val_6795_);
lean_dec(v_val_6795_);
v___y_6773_ = v___y_6786_;
v___y_6774_ = v___y_6785_;
v___y_6775_ = v___y_6788_;
v___y_6776_ = v___y_6787_;
v_val_6777_ = v___x_6796_;
goto v___jp_6772_;
}
}
v___jp_6797_:
{
if (lean_obj_tag(v_u_6691_) == 0)
{
if (lean_obj_tag(v_y_6690_) == 0)
{
if (lean_obj_tag(v_Y_6692_) == 0)
{
lean_object* v___x_6802_; 
v___x_6802_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6785_ = v___y_6799_;
v___y_6786_ = v___y_6798_;
v___y_6787_ = v___y_6800_;
v___y_6788_ = v___x_6802_;
goto v___jp_6784_;
}
else
{
lean_object* v_val_6803_; 
v_val_6803_ = lean_ctor_get(v_Y_6692_, 0);
lean_inc(v_val_6803_);
lean_dec_ref_known(v_Y_6692_, 1);
v___y_6785_ = v___y_6799_;
v___y_6786_ = v___y_6798_;
v___y_6787_ = v___y_6800_;
v___y_6788_ = v_val_6803_;
goto v___jp_6784_;
}
}
else
{
lean_object* v_val_6804_; lean_object* v___x_6805_; 
lean_dec(v_Y_6692_);
v_val_6804_ = lean_ctor_get(v_y_6690_, 0);
lean_inc(v_val_6804_);
lean_dec_ref_known(v_y_6690_, 1);
v___x_6805_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_val_6804_, v___y_6801_);
lean_dec(v_val_6804_);
v___y_6785_ = v___y_6799_;
v___y_6786_ = v___y_6798_;
v___y_6787_ = v___y_6800_;
v___y_6788_ = v___x_6805_;
goto v___jp_6784_;
}
}
else
{
lean_object* v_val_6806_; 
lean_dec(v_Y_6692_);
lean_dec(v_y_6690_);
v_val_6806_ = lean_ctor_get(v_u_6691_, 0);
lean_inc(v_val_6806_);
lean_dec_ref_known(v_u_6691_, 1);
v___y_6785_ = v___y_6799_;
v___y_6786_ = v___y_6798_;
v___y_6787_ = v___y_6800_;
v___y_6788_ = v_val_6806_;
goto v___jp_6784_;
}
}
v___jp_6807_:
{
if (lean_obj_tag(v_G_6689_) == 0)
{
uint8_t v___x_6811_; 
v___x_6811_ = 1;
v___y_6798_ = v___y_6810_;
v___y_6799_ = v___y_6808_;
v___y_6800_ = v___y_6809_;
v___y_6801_ = v___x_6811_;
goto v___jp_6797_;
}
else
{
lean_object* v_val_6812_; uint8_t v___x_6813_; 
v_val_6812_ = lean_ctor_get(v_G_6689_, 0);
lean_inc(v_val_6812_);
lean_dec_ref_known(v_G_6689_, 1);
v___x_6813_ = lean_unbox(v_val_6812_);
lean_dec(v_val_6812_);
v___y_6798_ = v___y_6810_;
v___y_6799_ = v___y_6808_;
v___y_6800_ = v___y_6809_;
v___y_6801_ = v___x_6813_;
goto v___jp_6797_;
}
}
v___jp_6814_:
{
if (lean_obj_tag(v_d_6695_) == 0)
{
lean_object* v___x_6817_; 
v___x_6817_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22);
v___y_6808_ = v___y_6815_;
v___y_6809_ = v___y_6816_;
v___y_6810_ = v___x_6817_;
goto v___jp_6807_;
}
else
{
lean_object* v_val_6818_; 
v_val_6818_ = lean_ctor_get(v_d_6695_, 0);
lean_inc(v_val_6818_);
lean_dec_ref_known(v_d_6695_, 1);
v___y_6808_ = v___y_6815_;
v___y_6809_ = v___y_6816_;
v___y_6810_ = v_val_6818_;
goto v___jp_6807_;
}
}
v___jp_6819_:
{
uint8_t v___x_6823_; lean_object* v_tz_6824_; 
v___x_6823_ = 0;
v_tz_6824_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_tz_6824_, 0, v___y_6821_);
lean_ctor_set(v_tz_6824_, 1, v___y_6820_);
lean_ctor_set(v_tz_6824_, 2, v___y_6822_);
lean_ctor_set_uint8(v_tz_6824_, sizeof(void*)*3, v___x_6823_);
if (lean_obj_tag(v_M_6693_) == 0)
{
if (lean_obj_tag(v_L_6694_) == 0)
{
lean_object* v___x_6825_; 
v___x_6825_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__30, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__30_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__30);
v___y_6815_ = v_tz_6824_;
v___y_6816_ = v___x_6825_;
goto v___jp_6814_;
}
else
{
lean_object* v_val_6826_; 
v_val_6826_ = lean_ctor_get(v_L_6694_, 0);
lean_inc(v_val_6826_);
lean_dec_ref_known(v_L_6694_, 1);
v___y_6815_ = v_tz_6824_;
v___y_6816_ = v_val_6826_;
goto v___jp_6814_;
}
}
else
{
lean_object* v_val_6827_; 
lean_dec(v_L_6694_);
v_val_6827_ = lean_ctor_get(v_M_6693_, 0);
lean_inc(v_val_6827_);
lean_dec_ref_known(v_M_6693_, 1);
v___y_6815_ = v_tz_6824_;
v___y_6816_ = v_val_6827_;
goto v___jp_6814_;
}
}
v___jp_6828_:
{
if (lean_obj_tag(v_zabbrev_6711_) == 0)
{
lean_object* v___x_6832_; lean_object* v___x_6833_; 
v___x_6832_ = lean_box(0);
v___x_6833_ = lean_apply_1(v___y_6829_, v___x_6832_);
v___y_6820_ = v___y_6831_;
v___y_6821_ = v___y_6830_;
v___y_6822_ = v___x_6833_;
goto v___jp_6819_;
}
else
{
lean_object* v_val_6834_; 
lean_dec_ref(v___y_6829_);
v_val_6834_ = lean_ctor_get(v_zabbrev_6711_, 0);
lean_inc(v_val_6834_);
lean_dec_ref_known(v_zabbrev_6711_, 1);
v___y_6820_ = v___y_6831_;
v___y_6821_ = v___y_6830_;
v___y_6822_ = v_val_6834_;
goto v___jp_6819_;
}
}
v___jp_6835_:
{
lean_object* v___f_6837_; 
lean_inc(v___y_6836_);
v___f_6837_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1), 2, 1);
lean_closure_set(v___f_6837_, 0, v___y_6836_);
if (lean_obj_tag(v_V_6709_) == 0)
{
if (lean_obj_tag(v_v_6712_) == 0)
{
if (lean_obj_tag(v_z_6710_) == 0)
{
lean_object* v___x_6838_; lean_object* v___x_6839_; 
v___x_6838_ = lean_box(0);
lean_inc(v___y_6836_);
v___x_6839_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(v___y_6836_, v___x_6838_);
v___y_6829_ = v___f_6837_;
v___y_6830_ = v___y_6836_;
v___y_6831_ = v___x_6839_;
goto v___jp_6828_;
}
else
{
lean_object* v_val_6840_; 
v_val_6840_ = lean_ctor_get(v_z_6710_, 0);
lean_inc(v_val_6840_);
lean_dec_ref_known(v_z_6710_, 1);
v___y_6829_ = v___f_6837_;
v___y_6830_ = v___y_6836_;
v___y_6831_ = v_val_6840_;
goto v___jp_6828_;
}
}
else
{
lean_object* v_val_6841_; 
lean_dec(v_z_6710_);
v_val_6841_ = lean_ctor_get(v_v_6712_, 0);
lean_inc(v_val_6841_);
lean_dec_ref_known(v_v_6712_, 1);
v___y_6829_ = v___f_6837_;
v___y_6830_ = v___y_6836_;
v___y_6831_ = v_val_6841_;
goto v___jp_6828_;
}
}
else
{
lean_object* v_val_6842_; 
lean_dec(v_v_6712_);
lean_dec(v_z_6710_);
v_val_6842_ = lean_ctor_get(v_V_6709_, 0);
lean_inc(v_val_6842_);
lean_dec_ref_known(v_V_6709_, 1);
v___y_6829_ = v___f_6837_;
v___y_6830_ = v___y_6836_;
v___y_6831_ = v_val_6842_;
goto v___jp_6828_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(lean_object* v_date_6848_, lean_object* v_config_6849_, lean_object* v_mod_6850_, lean_object* v_a_6851_){
_start:
{
if (lean_obj_tag(v_mod_6850_) == 0)
{
lean_object* v_val_6852_; lean_object* v___x_6853_; 
lean_dec_ref(v_config_6849_);
v_val_6852_ = lean_ctor_get(v_mod_6850_, 0);
lean_inc_ref(v_val_6852_);
lean_dec_ref_known(v_mod_6850_, 1);
v___x_6853_ = l_Std_Internal_Parsec_String_pstring(v_val_6852_, v_a_6851_);
if (lean_obj_tag(v___x_6853_) == 0)
{
lean_object* v_pos_6854_; lean_object* v___x_6856_; uint8_t v_isShared_6857_; uint8_t v_isSharedCheck_6861_; 
v_pos_6854_ = lean_ctor_get(v___x_6853_, 0);
v_isSharedCheck_6861_ = !lean_is_exclusive(v___x_6853_);
if (v_isSharedCheck_6861_ == 0)
{
lean_object* v_unused_6862_; 
v_unused_6862_ = lean_ctor_get(v___x_6853_, 1);
lean_dec(v_unused_6862_);
v___x_6856_ = v___x_6853_;
v_isShared_6857_ = v_isSharedCheck_6861_;
goto v_resetjp_6855_;
}
else
{
lean_inc(v_pos_6854_);
lean_dec(v___x_6853_);
v___x_6856_ = lean_box(0);
v_isShared_6857_ = v_isSharedCheck_6861_;
goto v_resetjp_6855_;
}
v_resetjp_6855_:
{
lean_object* v___x_6859_; 
if (v_isShared_6857_ == 0)
{
lean_ctor_set(v___x_6856_, 1, v_date_6848_);
v___x_6859_ = v___x_6856_;
goto v_reusejp_6858_;
}
else
{
lean_object* v_reuseFailAlloc_6860_; 
v_reuseFailAlloc_6860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6860_, 0, v_pos_6854_);
lean_ctor_set(v_reuseFailAlloc_6860_, 1, v_date_6848_);
v___x_6859_ = v_reuseFailAlloc_6860_;
goto v_reusejp_6858_;
}
v_reusejp_6858_:
{
return v___x_6859_;
}
}
}
else
{
lean_object* v_pos_6863_; lean_object* v_err_6864_; lean_object* v___x_6866_; uint8_t v_isShared_6867_; uint8_t v_isSharedCheck_6871_; 
lean_dec_ref(v_date_6848_);
v_pos_6863_ = lean_ctor_get(v___x_6853_, 0);
v_err_6864_ = lean_ctor_get(v___x_6853_, 1);
v_isSharedCheck_6871_ = !lean_is_exclusive(v___x_6853_);
if (v_isSharedCheck_6871_ == 0)
{
v___x_6866_ = v___x_6853_;
v_isShared_6867_ = v_isSharedCheck_6871_;
goto v_resetjp_6865_;
}
else
{
lean_inc(v_err_6864_);
lean_inc(v_pos_6863_);
lean_dec(v___x_6853_);
v___x_6866_ = lean_box(0);
v_isShared_6867_ = v_isSharedCheck_6871_;
goto v_resetjp_6865_;
}
v_resetjp_6865_:
{
lean_object* v___x_6869_; 
if (v_isShared_6867_ == 0)
{
v___x_6869_ = v___x_6866_;
goto v_reusejp_6868_;
}
else
{
lean_object* v_reuseFailAlloc_6870_; 
v_reuseFailAlloc_6870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6870_, 0, v_pos_6863_);
lean_ctor_set(v_reuseFailAlloc_6870_, 1, v_err_6864_);
v___x_6869_ = v_reuseFailAlloc_6870_;
goto v_reusejp_6868_;
}
v_reusejp_6868_:
{
return v___x_6869_;
}
}
}
}
else
{
lean_object* v_modifier_6872_; lean_object* v___x_6873_; 
v_modifier_6872_ = lean_ctor_get(v_mod_6850_, 0);
lean_inc_ref_n(v_modifier_6872_, 2);
lean_dec_ref_known(v_mod_6850_, 1);
v___x_6873_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_6849_, v_modifier_6872_, v_a_6851_);
if (lean_obj_tag(v___x_6873_) == 0)
{
lean_object* v_pos_6874_; lean_object* v_res_6875_; lean_object* v___x_6877_; uint8_t v_isShared_6878_; uint8_t v_isSharedCheck_6883_; 
v_pos_6874_ = lean_ctor_get(v___x_6873_, 0);
v_res_6875_ = lean_ctor_get(v___x_6873_, 1);
v_isSharedCheck_6883_ = !lean_is_exclusive(v___x_6873_);
if (v_isSharedCheck_6883_ == 0)
{
v___x_6877_ = v___x_6873_;
v_isShared_6878_ = v_isSharedCheck_6883_;
goto v_resetjp_6876_;
}
else
{
lean_inc(v_res_6875_);
lean_inc(v_pos_6874_);
lean_dec(v___x_6873_);
v___x_6877_ = lean_box(0);
v_isShared_6878_ = v_isSharedCheck_6883_;
goto v_resetjp_6876_;
}
v_resetjp_6876_:
{
lean_object* v___x_6879_; lean_object* v___x_6881_; 
v___x_6879_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(v_date_6848_, v_modifier_6872_, v_res_6875_);
if (v_isShared_6878_ == 0)
{
lean_ctor_set(v___x_6877_, 1, v___x_6879_);
v___x_6881_ = v___x_6877_;
goto v_reusejp_6880_;
}
else
{
lean_object* v_reuseFailAlloc_6882_; 
v_reuseFailAlloc_6882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6882_, 0, v_pos_6874_);
lean_ctor_set(v_reuseFailAlloc_6882_, 1, v___x_6879_);
v___x_6881_ = v_reuseFailAlloc_6882_;
goto v_reusejp_6880_;
}
v_reusejp_6880_:
{
return v___x_6881_;
}
}
}
else
{
lean_object* v_pos_6884_; lean_object* v_err_6885_; lean_object* v___x_6887_; uint8_t v_isShared_6888_; uint8_t v_isSharedCheck_6892_; 
lean_dec_ref(v_modifier_6872_);
lean_dec_ref(v_date_6848_);
v_pos_6884_ = lean_ctor_get(v___x_6873_, 0);
v_err_6885_ = lean_ctor_get(v___x_6873_, 1);
v_isSharedCheck_6892_ = !lean_is_exclusive(v___x_6873_);
if (v_isSharedCheck_6892_ == 0)
{
v___x_6887_ = v___x_6873_;
v_isShared_6888_ = v_isSharedCheck_6892_;
goto v_resetjp_6886_;
}
else
{
lean_inc(v_err_6885_);
lean_inc(v_pos_6884_);
lean_dec(v___x_6873_);
v___x_6887_ = lean_box(0);
v_isShared_6888_ = v_isSharedCheck_6892_;
goto v_resetjp_6886_;
}
v_resetjp_6886_:
{
lean_object* v___x_6890_; 
if (v_isShared_6888_ == 0)
{
v___x_6890_ = v___x_6887_;
goto v_reusejp_6889_;
}
else
{
lean_object* v_reuseFailAlloc_6891_; 
v_reuseFailAlloc_6891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6891_, 0, v_pos_6884_);
lean_ctor_set(v_reuseFailAlloc_6891_, 1, v_err_6885_);
v___x_6890_ = v_reuseFailAlloc_6891_;
goto v_reusejp_6889_;
}
v_reusejp_6889_:
{
return v___x_6890_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___redArg(lean_object* v_input_6893_, lean_object* v_config_6894_){
_start:
{
lean_object* v___x_6895_; lean_object* v___x_6896_; 
v___x_6895_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6896_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6895_, v_input_6893_);
if (lean_obj_tag(v___x_6896_) == 0)
{
lean_object* v_a_6897_; lean_object* v___x_6899_; uint8_t v_isShared_6900_; uint8_t v_isSharedCheck_6904_; 
lean_dec_ref(v_config_6894_);
v_a_6897_ = lean_ctor_get(v___x_6896_, 0);
v_isSharedCheck_6904_ = !lean_is_exclusive(v___x_6896_);
if (v_isSharedCheck_6904_ == 0)
{
v___x_6899_ = v___x_6896_;
v_isShared_6900_ = v_isSharedCheck_6904_;
goto v_resetjp_6898_;
}
else
{
lean_inc(v_a_6897_);
lean_dec(v___x_6896_);
v___x_6899_ = lean_box(0);
v_isShared_6900_ = v_isSharedCheck_6904_;
goto v_resetjp_6898_;
}
v_resetjp_6898_:
{
lean_object* v___x_6902_; 
if (v_isShared_6900_ == 0)
{
v___x_6902_ = v___x_6899_;
goto v_reusejp_6901_;
}
else
{
lean_object* v_reuseFailAlloc_6903_; 
v_reuseFailAlloc_6903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6903_, 0, v_a_6897_);
v___x_6902_ = v_reuseFailAlloc_6903_;
goto v_reusejp_6901_;
}
v_reusejp_6901_:
{
return v___x_6902_;
}
}
}
else
{
lean_object* v_a_6905_; lean_object* v___x_6907_; uint8_t v_isShared_6908_; uint8_t v_isSharedCheck_6913_; 
v_a_6905_ = lean_ctor_get(v___x_6896_, 0);
v_isSharedCheck_6913_ = !lean_is_exclusive(v___x_6896_);
if (v_isSharedCheck_6913_ == 0)
{
v___x_6907_ = v___x_6896_;
v_isShared_6908_ = v_isSharedCheck_6913_;
goto v_resetjp_6906_;
}
else
{
lean_inc(v_a_6905_);
lean_dec(v___x_6896_);
v___x_6907_ = lean_box(0);
v_isShared_6908_ = v_isSharedCheck_6913_;
goto v_resetjp_6906_;
}
v_resetjp_6906_:
{
lean_object* v___x_6909_; lean_object* v___x_6911_; 
v___x_6909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6909_, 0, v_config_6894_);
lean_ctor_set(v___x_6909_, 1, v_a_6905_);
if (v_isShared_6908_ == 0)
{
lean_ctor_set(v___x_6907_, 0, v___x_6909_);
v___x_6911_ = v___x_6907_;
goto v_reusejp_6910_;
}
else
{
lean_object* v_reuseFailAlloc_6912_; 
v_reuseFailAlloc_6912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6912_, 0, v___x_6909_);
v___x_6911_ = v_reuseFailAlloc_6912_;
goto v_reusejp_6910_;
}
v_reusejp_6910_:
{
return v___x_6911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec(lean_object* v_tz_6914_, lean_object* v_input_6915_, lean_object* v_config_6916_){
_start:
{
lean_object* v___x_6917_; 
v___x_6917_ = l_Std_Time_GenericFormat_spec___redArg(v_input_6915_, v_config_6916_);
return v___x_6917_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___boxed(lean_object* v_tz_6918_, lean_object* v_input_6919_, lean_object* v_config_6920_){
_start:
{
lean_object* v_res_6921_; 
v_res_6921_ = l_Std_Time_GenericFormat_spec(v_tz_6918_, v_input_6919_, v_config_6920_);
lean_dec(v_tz_6918_);
return v_res_6921_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(lean_object* v_tz_6922_, lean_object* v_msg_6923_){
_start:
{
lean_object* v___x_6924_; lean_object* v___x_6925_; 
v___x_6924_ = l_Std_Time_instInhabitedGenericFormat_default(v_tz_6922_);
v___x_6925_ = lean_panic_fn_borrowed(v___x_6924_, v_msg_6923_);
lean_dec_ref(v___x_6924_);
return v___x_6925_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___boxed(lean_object* v_tz_6926_, lean_object* v_msg_6927_){
_start:
{
lean_object* v_res_6928_; 
v_res_6928_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(v_tz_6926_, v_msg_6927_);
lean_dec(v_tz_6926_);
return v_res_6928_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21(lean_object* v_tz_6931_, lean_object* v_input_6932_, lean_object* v_config_6933_){
_start:
{
lean_object* v___x_6934_; lean_object* v___x_6935_; 
v___x_6934_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6935_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6934_, v_input_6932_);
if (lean_obj_tag(v___x_6935_) == 0)
{
lean_object* v_a_6936_; lean_object* v___x_6937_; lean_object* v___x_6938_; lean_object* v___x_6939_; lean_object* v___x_6940_; lean_object* v___x_6941_; lean_object* v___x_6942_; 
lean_dec_ref(v_config_6933_);
v_a_6936_ = lean_ctor_get(v___x_6935_, 0);
lean_inc(v_a_6936_);
lean_dec_ref_known(v___x_6935_, 1);
v___x_6937_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_6938_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__1));
v___x_6939_ = lean_unsigned_to_nat(1071u);
v___x_6940_ = lean_unsigned_to_nat(18u);
v___x_6941_ = l_mkPanicMessageWithDecl(v___x_6937_, v___x_6938_, v___x_6939_, v___x_6940_, v_a_6936_);
lean_dec(v_a_6936_);
v___x_6942_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(v_tz_6931_, v___x_6941_);
return v___x_6942_;
}
else
{
lean_object* v_a_6943_; lean_object* v___x_6944_; 
v_a_6943_ = lean_ctor_get(v___x_6935_, 0);
lean_inc(v_a_6943_);
lean_dec_ref_known(v___x_6935_, 1);
v___x_6944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6944_, 0, v_config_6933_);
lean_ctor_set(v___x_6944_, 1, v_a_6943_);
return v___x_6944_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21___boxed(lean_object* v_tz_6945_, lean_object* v_input_6946_, lean_object* v_config_6947_){
_start:
{
lean_object* v_res_6948_; 
v_res_6948_ = l_Std_Time_GenericFormat_spec_x21(v_tz_6945_, v_input_6946_, v_config_6947_);
lean_dec(v_tz_6945_);
return v_res_6948_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(lean_object* v_x_6949_, lean_object* v_x_6950_){
_start:
{
if (lean_obj_tag(v_x_6950_) == 0)
{
return v_x_6949_;
}
else
{
lean_object* v_head_6951_; lean_object* v_tail_6952_; lean_object* v___x_6953_; 
v_head_6951_ = lean_ctor_get(v_x_6950_, 0);
v_tail_6952_ = lean_ctor_get(v_x_6950_, 1);
v___x_6953_ = lean_string_append(v_x_6949_, v_head_6951_);
v_x_6949_ = v___x_6953_;
v_x_6950_ = v_tail_6952_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1___boxed(lean_object* v_x_6955_, lean_object* v_x_6956_){
_start:
{
lean_object* v_res_6957_; 
v_res_6957_ = l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(v_x_6955_, v_x_6956_);
lean_dec(v_x_6956_);
return v_res_6957_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0(lean_object* v_tz_6958_, lean_object* v_timestamp_6959_, lean_object* v___x_6960_, lean_object* v_x_6961_){
_start:
{
lean_object* v_offset_6962_; lean_object* v_second_6963_; lean_object* v_nano_6964_; lean_object* v___x_6965_; lean_object* v___x_6966_; lean_object* v___x_6967_; lean_object* v___x_6968_; lean_object* v___x_6969_; lean_object* v___x_6970_; lean_object* v___x_6971_; lean_object* v___x_6972_; lean_object* v___x_6973_; 
v_offset_6962_ = lean_ctor_get(v_tz_6958_, 0);
v_second_6963_ = lean_ctor_get(v_timestamp_6959_, 0);
v_nano_6964_ = lean_ctor_get(v_timestamp_6959_, 1);
v___x_6965_ = lean_nat_to_int(v___x_6960_);
v___x_6966_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_6967_ = lean_int_mul(v_second_6963_, v___x_6966_);
v___x_6968_ = lean_int_add(v___x_6967_, v_nano_6964_);
lean_dec(v___x_6967_);
v___x_6969_ = lean_int_mul(v_offset_6962_, v___x_6966_);
v___x_6970_ = lean_int_add(v___x_6969_, v___x_6965_);
lean_dec(v___x_6965_);
lean_dec(v___x_6969_);
v___x_6971_ = lean_int_add(v___x_6968_, v___x_6970_);
lean_dec(v___x_6970_);
lean_dec(v___x_6968_);
v___x_6972_ = l_Std_Time_Duration_ofNanoseconds(v___x_6971_);
lean_dec(v___x_6971_);
v___x_6973_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_6972_);
return v___x_6973_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed(lean_object* v_tz_6974_, lean_object* v_timestamp_6975_, lean_object* v___x_6976_, lean_object* v_x_6977_){
_start:
{
lean_object* v_res_6978_; 
v_res_6978_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0(v_tz_6974_, v_timestamp_6975_, v___x_6976_, v_x_6977_);
lean_dec_ref(v_timestamp_6975_);
lean_dec_ref(v_tz_6974_);
return v_res_6978_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(lean_object* v_aw_6979_, lean_object* v_date_6980_, lean_object* v_dateformat_6981_, lean_object* v_a_6982_, lean_object* v_a_6983_){
_start:
{
if (lean_obj_tag(v_a_6982_) == 0)
{
lean_object* v___x_6984_; 
lean_dec_ref(v_date_6980_);
v___x_6984_ = l_List_reverse___redArg(v_a_6983_);
return v___x_6984_;
}
else
{
lean_object* v_head_6985_; lean_object* v_tail_6986_; lean_object* v___x_6988_; uint8_t v_isShared_6989_; uint8_t v_isSharedCheck_7015_; 
v_head_6985_ = lean_ctor_get(v_a_6982_, 0);
v_tail_6986_ = lean_ctor_get(v_a_6982_, 1);
v_isSharedCheck_7015_ = !lean_is_exclusive(v_a_6982_);
if (v_isSharedCheck_7015_ == 0)
{
v___x_6988_ = v_a_6982_;
v_isShared_6989_ = v_isSharedCheck_7015_;
goto v_resetjp_6987_;
}
else
{
lean_inc(v_tail_6986_);
lean_inc(v_head_6985_);
lean_dec(v_a_6982_);
v___x_6988_ = lean_box(0);
v_isShared_6989_ = v_isSharedCheck_7015_;
goto v_resetjp_6987_;
}
v_resetjp_6987_:
{
lean_object* v___y_6991_; 
if (lean_obj_tag(v_aw_6979_) == 0)
{
lean_object* v_a_6996_; lean_object* v_offset_6997_; lean_object* v_name_6998_; lean_object* v_abbreviation_6999_; uint8_t v_isDST_7000_; lean_object* v_timestamp_7001_; uint8_t v___x_7002_; uint8_t v___x_7003_; lean_object* v_ltt_7004_; lean_object* v___x_7005_; lean_object* v___x_7006_; lean_object* v___x_7007_; lean_object* v___x_7008_; lean_object* v_tz_7009_; lean_object* v___f_7010_; lean_object* v___x_7011_; lean_object* v___x_7012_; lean_object* v___x_7013_; 
v_a_6996_ = lean_ctor_get(v_aw_6979_, 0);
v_offset_6997_ = lean_ctor_get(v_a_6996_, 0);
v_name_6998_ = lean_ctor_get(v_a_6996_, 1);
v_abbreviation_6999_ = lean_ctor_get(v_a_6996_, 2);
v_isDST_7000_ = lean_ctor_get_uint8(v_a_6996_, sizeof(void*)*3);
v_timestamp_7001_ = lean_ctor_get(v_date_6980_, 1);
v___x_7002_ = 0;
v___x_7003_ = 1;
lean_inc_ref(v_name_6998_);
lean_inc_ref(v_abbreviation_6999_);
lean_inc(v_offset_6997_);
v_ltt_7004_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_7004_, 0, v_offset_6997_);
lean_ctor_set(v_ltt_7004_, 1, v_abbreviation_6999_);
lean_ctor_set(v_ltt_7004_, 2, v_name_6998_);
lean_ctor_set_uint8(v_ltt_7004_, sizeof(void*)*3, v_isDST_7000_);
lean_ctor_set_uint8(v_ltt_7004_, sizeof(void*)*3 + 1, v___x_7002_);
lean_ctor_set_uint8(v_ltt_7004_, sizeof(void*)*3 + 2, v___x_7003_);
v___x_7005_ = lean_unsigned_to_nat(0u);
v___x_7006_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_7007_ = lean_box(0);
v___x_7008_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_7008_, 0, v_ltt_7004_);
lean_ctor_set(v___x_7008_, 1, v___x_7006_);
lean_ctor_set(v___x_7008_, 2, v___x_7007_);
lean_inc_ref(v___x_7008_);
v_tz_7009_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_7008_, v_timestamp_7001_);
lean_inc_ref_n(v_timestamp_7001_, 2);
lean_inc_ref(v_tz_7009_);
v___f_7010_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_7010_, 0, v_tz_7009_);
lean_closure_set(v___f_7010_, 1, v_timestamp_7001_);
lean_closure_set(v___f_7010_, 2, v___x_7005_);
v___x_7011_ = lean_mk_thunk(v___f_7010_);
v___x_7012_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_7012_, 0, v___x_7011_);
lean_ctor_set(v___x_7012_, 1, v_timestamp_7001_);
lean_ctor_set(v___x_7012_, 2, v___x_7008_);
lean_ctor_set(v___x_7012_, 3, v_tz_7009_);
v___x_7013_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6981_, v___x_7012_, v_head_6985_);
v___y_6991_ = v___x_7013_;
goto v___jp_6990_;
}
else
{
lean_object* v___x_7014_; 
lean_inc_ref(v_date_6980_);
v___x_7014_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6981_, v_date_6980_, v_head_6985_);
v___y_6991_ = v___x_7014_;
goto v___jp_6990_;
}
v___jp_6990_:
{
lean_object* v___x_6993_; 
if (v_isShared_6989_ == 0)
{
lean_ctor_set(v___x_6988_, 1, v_a_6983_);
lean_ctor_set(v___x_6988_, 0, v___y_6991_);
v___x_6993_ = v___x_6988_;
goto v_reusejp_6992_;
}
else
{
lean_object* v_reuseFailAlloc_6995_; 
v_reuseFailAlloc_6995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6995_, 0, v___y_6991_);
lean_ctor_set(v_reuseFailAlloc_6995_, 1, v_a_6983_);
v___x_6993_ = v_reuseFailAlloc_6995_;
goto v_reusejp_6992_;
}
v_reusejp_6992_:
{
v_a_6982_ = v_tail_6986_;
v_a_6983_ = v___x_6993_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___boxed(lean_object* v_aw_7016_, lean_object* v_date_7017_, lean_object* v_dateformat_7018_, lean_object* v_a_7019_, lean_object* v_a_7020_){
_start:
{
lean_object* v_res_7021_; 
v_res_7021_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(v_aw_7016_, v_date_7017_, v_dateformat_7018_, v_a_7019_, v_a_7020_);
lean_dec_ref(v_dateformat_7018_);
lean_dec(v_aw_7016_);
return v_res_7021_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format(lean_object* v_aw_7022_, lean_object* v_format_7023_, lean_object* v_date_7024_){
_start:
{
lean_object* v_config_7025_; lean_object* v_string_7026_; lean_object* v_dateformat_7027_; lean_object* v___x_7028_; lean_object* v___x_7029_; lean_object* v___x_7030_; lean_object* v___x_7031_; 
v_config_7025_ = lean_ctor_get(v_format_7023_, 0);
lean_inc_ref(v_config_7025_);
v_string_7026_ = lean_ctor_get(v_format_7023_, 1);
lean_inc(v_string_7026_);
lean_dec_ref(v_format_7023_);
v_dateformat_7027_ = lean_ctor_get(v_config_7025_, 0);
lean_inc_ref(v_dateformat_7027_);
lean_dec_ref(v_config_7025_);
v___x_7028_ = lean_box(0);
v___x_7029_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(v_aw_7022_, v_date_7024_, v_dateformat_7027_, v_string_7026_, v___x_7028_);
lean_dec_ref(v_dateformat_7027_);
v___x_7030_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_7031_ = l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(v___x_7030_, v___x_7029_);
lean_dec(v___x_7029_);
return v___x_7031_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format___boxed(lean_object* v_aw_7032_, lean_object* v_format_7033_, lean_object* v_date_7034_){
_start:
{
lean_object* v_res_7035_; 
v_res_7035_ = l_Std_Time_GenericFormat_format(v_aw_7032_, v_format_7033_, v_date_7034_);
lean_dec(v_aw_7032_);
return v_res_7035_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(lean_object* v_config_7039_, lean_object* v_aw_7040_, lean_object* v_builder_7041_, lean_object* v_x_7042_, lean_object* v_a_7043_){
_start:
{
if (lean_obj_tag(v_x_7042_) == 0)
{
lean_object* v___x_7044_; 
lean_dec_ref(v_config_7039_);
v___x_7044_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(v_builder_7041_, v_aw_7040_);
if (lean_obj_tag(v___x_7044_) == 0)
{
lean_object* v___x_7045_; lean_object* v___x_7046_; 
v___x_7045_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go___closed__1));
v___x_7046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7046_, 0, v_a_7043_);
lean_ctor_set(v___x_7046_, 1, v___x_7045_);
return v___x_7046_;
}
else
{
lean_object* v_val_7047_; lean_object* v___x_7048_; 
v_val_7047_ = lean_ctor_get(v___x_7044_, 0);
lean_inc(v_val_7047_);
lean_dec_ref_known(v___x_7044_, 1);
v___x_7048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7048_, 0, v_a_7043_);
lean_ctor_set(v___x_7048_, 1, v_val_7047_);
return v___x_7048_;
}
}
else
{
lean_object* v_head_7049_; lean_object* v_tail_7050_; lean_object* v___x_7051_; 
v_head_7049_ = lean_ctor_get(v_x_7042_, 0);
lean_inc(v_head_7049_);
v_tail_7050_ = lean_ctor_get(v_x_7042_, 1);
lean_inc(v_tail_7050_);
lean_dec_ref_known(v_x_7042_, 2);
lean_inc_ref(v_config_7039_);
v___x_7051_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(v_builder_7041_, v_config_7039_, v_head_7049_, v_a_7043_);
if (lean_obj_tag(v___x_7051_) == 0)
{
lean_object* v_pos_7052_; lean_object* v_res_7053_; 
v_pos_7052_ = lean_ctor_get(v___x_7051_, 0);
lean_inc(v_pos_7052_);
v_res_7053_ = lean_ctor_get(v___x_7051_, 1);
lean_inc(v_res_7053_);
lean_dec_ref_known(v___x_7051_, 2);
v_builder_7041_ = v_res_7053_;
v_x_7042_ = v_tail_7050_;
v_a_7043_ = v_pos_7052_;
goto _start;
}
else
{
lean_object* v_pos_7055_; lean_object* v_err_7056_; lean_object* v___x_7058_; uint8_t v_isShared_7059_; uint8_t v_isSharedCheck_7063_; 
lean_dec(v_tail_7050_);
lean_dec(v_aw_7040_);
lean_dec_ref(v_config_7039_);
v_pos_7055_ = lean_ctor_get(v___x_7051_, 0);
v_err_7056_ = lean_ctor_get(v___x_7051_, 1);
v_isSharedCheck_7063_ = !lean_is_exclusive(v___x_7051_);
if (v_isSharedCheck_7063_ == 0)
{
v___x_7058_ = v___x_7051_;
v_isShared_7059_ = v_isSharedCheck_7063_;
goto v_resetjp_7057_;
}
else
{
lean_inc(v_err_7056_);
lean_inc(v_pos_7055_);
lean_dec(v___x_7051_);
v___x_7058_ = lean_box(0);
v_isShared_7059_ = v_isSharedCheck_7063_;
goto v_resetjp_7057_;
}
v_resetjp_7057_:
{
lean_object* v___x_7061_; 
if (v_isShared_7059_ == 0)
{
v___x_7061_ = v___x_7058_;
goto v_reusejp_7060_;
}
else
{
lean_object* v_reuseFailAlloc_7062_; 
v_reuseFailAlloc_7062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7062_, 0, v_pos_7055_);
lean_ctor_set(v_reuseFailAlloc_7062_, 1, v_err_7056_);
v___x_7061_ = v_reuseFailAlloc_7062_;
goto v_reusejp_7060_;
}
v_reusejp_7060_:
{
return v___x_7061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(lean_object* v_format_7066_, lean_object* v_config_7067_, lean_object* v_aw_7068_, lean_object* v_a_7069_){
_start:
{
lean_object* v___x_7070_; lean_object* v___x_7071_; 
v___x_7070_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser___closed__0));
v___x_7071_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(v_config_7067_, v_aw_7068_, v___x_7070_, v_format_7066_, v_a_7069_);
return v___x_7071_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(lean_object* v_config_7075_, lean_object* v_format_7076_, lean_object* v_func_7077_, lean_object* v_a_7078_){
_start:
{
if (lean_obj_tag(v_format_7076_) == 0)
{
lean_dec_ref(v_config_7075_);
if (lean_obj_tag(v_func_7077_) == 0)
{
lean_object* v___x_7079_; lean_object* v___x_7080_; 
v___x_7079_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg___closed__1));
v___x_7080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7080_, 0, v_a_7078_);
lean_ctor_set(v___x_7080_, 1, v___x_7079_);
return v___x_7080_;
}
else
{
lean_object* v_val_7081_; lean_object* v_fst_7082_; lean_object* v_snd_7083_; lean_object* v___x_7084_; uint8_t v_decide_7085_; 
v_val_7081_ = lean_ctor_get(v_func_7077_, 0);
lean_inc(v_val_7081_);
lean_dec_ref_known(v_func_7077_, 1);
v_fst_7082_ = lean_ctor_get(v_a_7078_, 0);
v_snd_7083_ = lean_ctor_get(v_a_7078_, 1);
v___x_7084_ = lean_string_utf8_byte_size(v_fst_7082_);
v_decide_7085_ = lean_nat_dec_eq(v_snd_7083_, v___x_7084_);
if (v_decide_7085_ == 0)
{
lean_object* v___x_7086_; lean_object* v___x_7087_; 
lean_dec(v_val_7081_);
v___x_7086_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
v___x_7087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7087_, 0, v_a_7078_);
lean_ctor_set(v___x_7087_, 1, v___x_7086_);
return v___x_7087_;
}
else
{
lean_object* v___x_7088_; 
v___x_7088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7088_, 0, v_a_7078_);
lean_ctor_set(v___x_7088_, 1, v_val_7081_);
return v___x_7088_;
}
}
}
else
{
lean_object* v_head_7089_; 
v_head_7089_ = lean_ctor_get(v_format_7076_, 0);
lean_inc(v_head_7089_);
if (lean_obj_tag(v_head_7089_) == 0)
{
lean_object* v_tail_7090_; lean_object* v_val_7091_; lean_object* v___x_7092_; 
v_tail_7090_ = lean_ctor_get(v_format_7076_, 1);
lean_inc(v_tail_7090_);
lean_dec_ref_known(v_format_7076_, 2);
v_val_7091_ = lean_ctor_get(v_head_7089_, 0);
lean_inc_ref(v_val_7091_);
lean_dec_ref_known(v_head_7089_, 1);
v___x_7092_ = l_Std_Internal_Parsec_String_pstring(v_val_7091_, v_a_7078_);
if (lean_obj_tag(v___x_7092_) == 0)
{
lean_object* v_pos_7093_; 
v_pos_7093_ = lean_ctor_get(v___x_7092_, 0);
lean_inc(v_pos_7093_);
lean_dec_ref_known(v___x_7092_, 2);
v_format_7076_ = v_tail_7090_;
v_a_7078_ = v_pos_7093_;
goto _start;
}
else
{
lean_object* v_pos_7095_; lean_object* v_err_7096_; lean_object* v___x_7098_; uint8_t v_isShared_7099_; uint8_t v_isSharedCheck_7103_; 
lean_dec(v_tail_7090_);
lean_dec(v_func_7077_);
lean_dec_ref(v_config_7075_);
v_pos_7095_ = lean_ctor_get(v___x_7092_, 0);
v_err_7096_ = lean_ctor_get(v___x_7092_, 1);
v_isSharedCheck_7103_ = !lean_is_exclusive(v___x_7092_);
if (v_isSharedCheck_7103_ == 0)
{
v___x_7098_ = v___x_7092_;
v_isShared_7099_ = v_isSharedCheck_7103_;
goto v_resetjp_7097_;
}
else
{
lean_inc(v_err_7096_);
lean_inc(v_pos_7095_);
lean_dec(v___x_7092_);
v___x_7098_ = lean_box(0);
v_isShared_7099_ = v_isSharedCheck_7103_;
goto v_resetjp_7097_;
}
v_resetjp_7097_:
{
lean_object* v___x_7101_; 
if (v_isShared_7099_ == 0)
{
v___x_7101_ = v___x_7098_;
goto v_reusejp_7100_;
}
else
{
lean_object* v_reuseFailAlloc_7102_; 
v_reuseFailAlloc_7102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7102_, 0, v_pos_7095_);
lean_ctor_set(v_reuseFailAlloc_7102_, 1, v_err_7096_);
v___x_7101_ = v_reuseFailAlloc_7102_;
goto v_reusejp_7100_;
}
v_reusejp_7100_:
{
return v___x_7101_;
}
}
}
}
else
{
lean_object* v_tail_7104_; lean_object* v_modifier_7105_; lean_object* v___x_7106_; 
v_tail_7104_ = lean_ctor_get(v_format_7076_, 1);
lean_inc(v_tail_7104_);
lean_dec_ref_known(v_format_7076_, 2);
v_modifier_7105_ = lean_ctor_get(v_head_7089_, 0);
lean_inc_ref(v_modifier_7105_);
lean_dec_ref_known(v_head_7089_, 1);
lean_inc_ref(v_config_7075_);
v___x_7106_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_7075_, v_modifier_7105_, v_a_7078_);
if (lean_obj_tag(v___x_7106_) == 0)
{
lean_object* v_pos_7107_; lean_object* v_res_7108_; lean_object* v___x_7109_; 
v_pos_7107_ = lean_ctor_get(v___x_7106_, 0);
lean_inc(v_pos_7107_);
v_res_7108_ = lean_ctor_get(v___x_7106_, 1);
lean_inc(v_res_7108_);
lean_dec_ref_known(v___x_7106_, 2);
v___x_7109_ = lean_apply_1(v_func_7077_, v_res_7108_);
v_format_7076_ = v_tail_7104_;
v_func_7077_ = v___x_7109_;
v_a_7078_ = v_pos_7107_;
goto _start;
}
else
{
lean_object* v_pos_7111_; lean_object* v_err_7112_; lean_object* v___x_7114_; uint8_t v_isShared_7115_; uint8_t v_isSharedCheck_7119_; 
lean_dec(v_tail_7104_);
lean_dec(v_func_7077_);
lean_dec_ref(v_config_7075_);
v_pos_7111_ = lean_ctor_get(v___x_7106_, 0);
v_err_7112_ = lean_ctor_get(v___x_7106_, 1);
v_isSharedCheck_7119_ = !lean_is_exclusive(v___x_7106_);
if (v_isSharedCheck_7119_ == 0)
{
v___x_7114_ = v___x_7106_;
v_isShared_7115_ = v_isSharedCheck_7119_;
goto v_resetjp_7113_;
}
else
{
lean_inc(v_err_7112_);
lean_inc(v_pos_7111_);
lean_dec(v___x_7106_);
v___x_7114_ = lean_box(0);
v_isShared_7115_ = v_isSharedCheck_7119_;
goto v_resetjp_7113_;
}
v_resetjp_7113_:
{
lean_object* v___x_7117_; 
if (v_isShared_7115_ == 0)
{
v___x_7117_ = v___x_7114_;
goto v_reusejp_7116_;
}
else
{
lean_object* v_reuseFailAlloc_7118_; 
v_reuseFailAlloc_7118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7118_, 0, v_pos_7111_);
lean_ctor_set(v_reuseFailAlloc_7118_, 1, v_err_7112_);
v___x_7117_ = v_reuseFailAlloc_7118_;
goto v_reusejp_7116_;
}
v_reusejp_7116_:
{
return v___x_7117_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go(lean_object* v_00_u03b1_7120_, lean_object* v_config_7121_, lean_object* v_format_7122_, lean_object* v_func_7123_, lean_object* v_a_7124_){
_start:
{
lean_object* v___x_7125_; 
v___x_7125_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7121_, v_format_7122_, v_func_7123_, v_a_7124_);
return v___x_7125_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser___redArg(lean_object* v_format_7126_, lean_object* v_config_7127_, lean_object* v_func_7128_, lean_object* v_a_7129_){
_start:
{
lean_object* v___x_7130_; 
v___x_7130_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7127_, v_format_7126_, v_func_7128_, v_a_7129_);
return v___x_7130_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser(lean_object* v_00_u03b1_7131_, lean_object* v_format_7132_, lean_object* v_config_7133_, lean_object* v_func_7134_, lean_object* v_a_7135_){
_start:
{
lean_object* v___x_7136_; 
v___x_7136_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7133_, v_format_7132_, v_func_7134_, v_a_7135_);
return v___x_7136_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse___lam__0(lean_object* v_string_7137_, lean_object* v_config_7138_, lean_object* v_aw_7139_, lean_object* v___y_7140_){
_start:
{
lean_object* v___x_7141_; 
v___x_7141_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(v_string_7137_, v_config_7138_, v_aw_7139_, v___y_7140_);
if (lean_obj_tag(v___x_7141_) == 0)
{
lean_object* v_pos_7142_; lean_object* v_fst_7143_; lean_object* v_snd_7144_; lean_object* v___x_7145_; uint8_t v_decide_7146_; 
v_pos_7142_ = lean_ctor_get(v___x_7141_, 0);
lean_inc(v_pos_7142_);
v_fst_7143_ = lean_ctor_get(v_pos_7142_, 0);
v_snd_7144_ = lean_ctor_get(v_pos_7142_, 1);
v___x_7145_ = lean_string_utf8_byte_size(v_fst_7143_);
v_decide_7146_ = lean_nat_dec_eq(v_snd_7144_, v___x_7145_);
if (v_decide_7146_ == 0)
{
lean_object* v___x_7148_; uint8_t v_isShared_7149_; uint8_t v_isSharedCheck_7154_; 
v_isSharedCheck_7154_ = !lean_is_exclusive(v___x_7141_);
if (v_isSharedCheck_7154_ == 0)
{
lean_object* v_unused_7155_; lean_object* v_unused_7156_; 
v_unused_7155_ = lean_ctor_get(v___x_7141_, 1);
lean_dec(v_unused_7155_);
v_unused_7156_ = lean_ctor_get(v___x_7141_, 0);
lean_dec(v_unused_7156_);
v___x_7148_ = v___x_7141_;
v_isShared_7149_ = v_isSharedCheck_7154_;
goto v_resetjp_7147_;
}
else
{
lean_dec(v___x_7141_);
v___x_7148_ = lean_box(0);
v_isShared_7149_ = v_isSharedCheck_7154_;
goto v_resetjp_7147_;
}
v_resetjp_7147_:
{
lean_object* v___x_7150_; lean_object* v___x_7152_; 
v___x_7150_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_7149_ == 0)
{
lean_ctor_set_tag(v___x_7148_, 1);
lean_ctor_set(v___x_7148_, 1, v___x_7150_);
v___x_7152_ = v___x_7148_;
goto v_reusejp_7151_;
}
else
{
lean_object* v_reuseFailAlloc_7153_; 
v_reuseFailAlloc_7153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7153_, 0, v_pos_7142_);
lean_ctor_set(v_reuseFailAlloc_7153_, 1, v___x_7150_);
v___x_7152_ = v_reuseFailAlloc_7153_;
goto v_reusejp_7151_;
}
v_reusejp_7151_:
{
return v___x_7152_;
}
}
}
else
{
lean_dec(v_pos_7142_);
return v___x_7141_;
}
}
else
{
return v___x_7141_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse(lean_object* v_aw_7157_, lean_object* v_format_7158_, lean_object* v_input_7159_){
_start:
{
lean_object* v_config_7160_; lean_object* v_string_7161_; lean_object* v___f_7162_; lean_object* v___x_7163_; 
v_config_7160_ = lean_ctor_get(v_format_7158_, 0);
lean_inc_ref(v_config_7160_);
v_string_7161_ = lean_ctor_get(v_format_7158_, 1);
lean_inc(v_string_7161_);
lean_dec_ref(v_format_7158_);
v___f_7162_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parse___lam__0), 4, 3);
lean_closure_set(v___f_7162_, 0, v_string_7161_);
lean_closure_set(v___f_7162_, 1, v_config_7160_);
lean_closure_set(v___f_7162_, 2, v_aw_7157_);
v___x_7163_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_7162_, v_input_7159_);
return v___x_7163_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(lean_object* v_msg_7164_){
_start:
{
lean_object* v___x_7165_; lean_object* v___x_7166_; 
v___x_7165_ = l_Std_Time_instInhabitedDateTime;
v___x_7166_ = lean_panic_fn_borrowed(v___x_7165_, v_msg_7164_);
return v___x_7166_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse_x21(lean_object* v_aw_7168_, lean_object* v_format_7169_, lean_object* v_input_7170_){
_start:
{
lean_object* v___x_7171_; 
v___x_7171_ = l_Std_Time_GenericFormat_parse(v_aw_7168_, v_format_7169_, v_input_7170_);
if (lean_obj_tag(v___x_7171_) == 0)
{
lean_object* v_a_7172_; lean_object* v___x_7173_; lean_object* v___x_7174_; lean_object* v___x_7175_; lean_object* v___x_7176_; lean_object* v___x_7177_; lean_object* v___x_7178_; 
v_a_7172_ = lean_ctor_get(v___x_7171_, 0);
lean_inc(v_a_7172_);
lean_dec_ref_known(v___x_7171_, 1);
v___x_7173_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_7174_ = ((lean_object*)(l_Std_Time_GenericFormat_parse_x21___closed__0));
v___x_7175_ = lean_unsigned_to_nat(1124u);
v___x_7176_ = lean_unsigned_to_nat(18u);
v___x_7177_ = l_mkPanicMessageWithDecl(v___x_7173_, v___x_7174_, v___x_7175_, v___x_7176_, v_a_7172_);
lean_dec(v_a_7172_);
v___x_7178_ = l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(v___x_7177_);
return v___x_7178_;
}
else
{
lean_object* v_a_7179_; 
v_a_7179_ = lean_ctor_get(v___x_7171_, 0);
lean_inc(v_a_7179_);
lean_dec_ref_known(v___x_7171_, 1);
return v_a_7179_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0(lean_object* v_config_7180_, lean_object* v_string_7181_, lean_object* v_builder_7182_, lean_object* v___y_7183_){
_start:
{
lean_object* v___x_7184_; 
v___x_7184_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7180_, v_string_7181_, v_builder_7182_, v___y_7183_);
return v___x_7184_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg(lean_object* v_format_7185_, lean_object* v_builder_7186_, lean_object* v_input_7187_){
_start:
{
lean_object* v_config_7188_; lean_object* v_string_7189_; lean_object* v___f_7190_; lean_object* v___x_7191_; 
v_config_7188_ = lean_ctor_get(v_format_7185_, 0);
lean_inc_ref(v_config_7188_);
v_string_7189_ = lean_ctor_get(v_format_7185_, 1);
lean_inc(v_string_7189_);
lean_dec_ref(v_format_7185_);
v___f_7190_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0), 4, 3);
lean_closure_set(v___f_7190_, 0, v_config_7188_);
lean_closure_set(v___f_7190_, 1, v_string_7189_);
lean_closure_set(v___f_7190_, 2, v_builder_7186_);
v___x_7191_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_7190_, v_input_7187_);
return v___x_7191_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder(lean_object* v_aw_7192_, lean_object* v_00_u03b1_7193_, lean_object* v_format_7194_, lean_object* v_builder_7195_, lean_object* v_input_7196_){
_start:
{
lean_object* v___x_7197_; 
v___x_7197_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_7194_, v_builder_7195_, v_input_7196_);
return v___x_7197_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___boxed(lean_object* v_aw_7198_, lean_object* v_00_u03b1_7199_, lean_object* v_format_7200_, lean_object* v_builder_7201_, lean_object* v_input_7202_){
_start:
{
lean_object* v_res_7203_; 
v_res_7203_ = l_Std_Time_GenericFormat_parseBuilder(v_aw_7198_, v_00_u03b1_7199_, v_format_7200_, v_builder_7201_, v_input_7202_);
lean_dec(v_aw_7198_);
return v_res_7203_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg(lean_object* v_inst_7205_, lean_object* v_format_7206_, lean_object* v_builder_7207_, lean_object* v_input_7208_){
_start:
{
lean_object* v___x_7209_; 
v___x_7209_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_7206_, v_builder_7207_, v_input_7208_);
if (lean_obj_tag(v___x_7209_) == 0)
{
lean_object* v_a_7210_; lean_object* v___x_7211_; lean_object* v___x_7212_; lean_object* v___x_7213_; lean_object* v___x_7214_; lean_object* v___x_7215_; lean_object* v___x_7216_; 
v_a_7210_ = lean_ctor_get(v___x_7209_, 0);
lean_inc(v_a_7210_);
lean_dec_ref_known(v___x_7209_, 1);
v___x_7211_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_7212_ = ((lean_object*)(l_Std_Time_GenericFormat_parseBuilder_x21___redArg___closed__0));
v___x_7213_ = lean_unsigned_to_nat(1138u);
v___x_7214_ = lean_unsigned_to_nat(18u);
v___x_7215_ = l_mkPanicMessageWithDecl(v___x_7211_, v___x_7212_, v___x_7213_, v___x_7214_, v_a_7210_);
lean_dec(v_a_7210_);
v___x_7216_ = l_panic___redArg(v_inst_7205_, v___x_7215_);
return v___x_7216_;
}
else
{
lean_object* v_a_7217_; 
v_a_7217_ = lean_ctor_get(v___x_7209_, 0);
lean_inc(v_a_7217_);
lean_dec_ref_known(v___x_7209_, 1);
return v_a_7217_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg___boxed(lean_object* v_inst_7218_, lean_object* v_format_7219_, lean_object* v_builder_7220_, lean_object* v_input_7221_){
_start:
{
lean_object* v_res_7222_; 
v_res_7222_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7218_, v_format_7219_, v_builder_7220_, v_input_7221_);
lean_dec(v_inst_7218_);
return v_res_7222_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21(lean_object* v_00_u03b1_7223_, lean_object* v_aw_7224_, lean_object* v_inst_7225_, lean_object* v_format_7226_, lean_object* v_builder_7227_, lean_object* v_input_7228_){
_start:
{
lean_object* v___x_7229_; 
v___x_7229_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7225_, v_format_7226_, v_builder_7227_, v_input_7228_);
return v___x_7229_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___boxed(lean_object* v_00_u03b1_7230_, lean_object* v_aw_7231_, lean_object* v_inst_7232_, lean_object* v_format_7233_, lean_object* v_builder_7234_, lean_object* v_input_7235_){
_start:
{
lean_object* v_res_7236_; 
v_res_7236_ = l_Std_Time_GenericFormat_parseBuilder_x21(v_00_u03b1_7230_, v_aw_7231_, v_inst_7232_, v_format_7233_, v_builder_7234_, v_input_7235_);
lean_dec(v_inst_7232_);
lean_dec(v_aw_7231_);
return v_res_7236_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(lean_object* v_getInfo_7237_, lean_object* v_dateformat_7238_, lean_object* v_data_7239_, lean_object* v_format_7240_){
_start:
{
if (lean_obj_tag(v_format_7240_) == 0)
{
lean_object* v___x_7241_; 
lean_dec_ref(v_getInfo_7237_);
v___x_7241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7241_, 0, v_data_7239_);
return v___x_7241_;
}
else
{
lean_object* v_head_7242_; 
v_head_7242_ = lean_ctor_get(v_format_7240_, 0);
lean_inc(v_head_7242_);
if (lean_obj_tag(v_head_7242_) == 0)
{
lean_object* v_tail_7243_; lean_object* v_val_7244_; lean_object* v___x_7245_; 
v_tail_7243_ = lean_ctor_get(v_format_7240_, 1);
lean_inc(v_tail_7243_);
lean_dec_ref_known(v_format_7240_, 2);
v_val_7244_ = lean_ctor_get(v_head_7242_, 0);
lean_inc_ref(v_val_7244_);
lean_dec_ref_known(v_head_7242_, 1);
v___x_7245_ = lean_string_append(v_data_7239_, v_val_7244_);
lean_dec_ref(v_val_7244_);
v_data_7239_ = v___x_7245_;
v_format_7240_ = v_tail_7243_;
goto _start;
}
else
{
lean_object* v_tail_7247_; lean_object* v_modifier_7248_; lean_object* v___x_7249_; 
v_tail_7247_ = lean_ctor_get(v_format_7240_, 1);
lean_inc(v_tail_7247_);
lean_dec_ref_known(v_format_7240_, 2);
v_modifier_7248_ = lean_ctor_get(v_head_7242_, 0);
lean_inc_ref_n(v_modifier_7248_, 2);
lean_dec_ref_known(v_head_7242_, 1);
lean_inc_ref(v_getInfo_7237_);
v___x_7249_ = lean_apply_1(v_getInfo_7237_, v_modifier_7248_);
if (lean_obj_tag(v___x_7249_) == 0)
{
lean_object* v___x_7250_; 
lean_dec_ref(v_modifier_7248_);
lean_dec(v_tail_7247_);
lean_dec_ref(v_data_7239_);
lean_dec_ref(v_getInfo_7237_);
v___x_7250_ = lean_box(0);
return v___x_7250_;
}
else
{
lean_object* v_val_7251_; lean_object* v___x_7252_; lean_object* v___x_7253_; 
v_val_7251_ = lean_ctor_get(v___x_7249_, 0);
lean_inc(v_val_7251_);
lean_dec_ref_known(v___x_7249_, 1);
v___x_7252_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7238_, v_modifier_7248_, v_val_7251_);
v___x_7253_ = lean_string_append(v_data_7239_, v___x_7252_);
lean_dec_ref(v___x_7252_);
v_data_7239_ = v___x_7253_;
v_format_7240_ = v_tail_7247_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go___boxed(lean_object* v_getInfo_7255_, lean_object* v_dateformat_7256_, lean_object* v_data_7257_, lean_object* v_format_7258_){
_start:
{
lean_object* v_res_7259_; 
v_res_7259_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(v_getInfo_7255_, v_dateformat_7256_, v_data_7257_, v_format_7258_);
lean_dec_ref(v_dateformat_7256_);
return v_res_7259_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___redArg(lean_object* v_format_7260_, lean_object* v_getInfo_7261_){
_start:
{
lean_object* v_config_7262_; lean_object* v_string_7263_; lean_object* v_dateformat_7264_; lean_object* v___x_7265_; lean_object* v___x_7266_; 
v_config_7262_ = lean_ctor_get(v_format_7260_, 0);
lean_inc_ref(v_config_7262_);
v_string_7263_ = lean_ctor_get(v_format_7260_, 1);
lean_inc(v_string_7263_);
lean_dec_ref(v_format_7260_);
v_dateformat_7264_ = lean_ctor_get(v_config_7262_, 0);
lean_inc_ref(v_dateformat_7264_);
lean_dec_ref(v_config_7262_);
v___x_7265_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_7266_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(v_getInfo_7261_, v_dateformat_7264_, v___x_7265_, v_string_7263_);
lean_dec_ref(v_dateformat_7264_);
return v___x_7266_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric(lean_object* v_aw_7267_, lean_object* v_format_7268_, lean_object* v_getInfo_7269_){
_start:
{
lean_object* v___x_7270_; 
v___x_7270_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_format_7268_, v_getInfo_7269_);
return v___x_7270_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___boxed(lean_object* v_aw_7271_, lean_object* v_format_7272_, lean_object* v_getInfo_7273_){
_start:
{
lean_object* v_res_7274_; 
v_res_7274_ = l_Std_Time_GenericFormat_formatGeneric(v_aw_7271_, v_format_7272_, v_getInfo_7273_);
lean_dec(v_aw_7271_);
return v_res_7274_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(lean_object* v_dateformat_7275_, lean_object* v_data_7276_, lean_object* v_format_7277_){
_start:
{
if (lean_obj_tag(v_format_7277_) == 0)
{
lean_dec_ref(v_dateformat_7275_);
return v_data_7276_;
}
else
{
lean_object* v_head_7278_; 
v_head_7278_ = lean_ctor_get(v_format_7277_, 0);
lean_inc(v_head_7278_);
if (lean_obj_tag(v_head_7278_) == 0)
{
lean_object* v_tail_7279_; lean_object* v_val_7280_; lean_object* v___x_7281_; 
v_tail_7279_ = lean_ctor_get(v_format_7277_, 1);
lean_inc(v_tail_7279_);
lean_dec_ref_known(v_format_7277_, 2);
v_val_7280_ = lean_ctor_get(v_head_7278_, 0);
lean_inc_ref(v_val_7280_);
lean_dec_ref_known(v_head_7278_, 1);
v___x_7281_ = lean_string_append(v_data_7276_, v_val_7280_);
lean_dec_ref(v_val_7280_);
v_data_7276_ = v___x_7281_;
v_format_7277_ = v_tail_7279_;
goto _start;
}
else
{
lean_object* v_tail_7283_; lean_object* v_modifier_7284_; lean_object* v___f_7285_; 
v_tail_7283_ = lean_ctor_get(v_format_7277_, 1);
lean_inc(v_tail_7283_);
lean_dec_ref_known(v_format_7277_, 2);
v_modifier_7284_ = lean_ctor_get(v_head_7278_, 0);
lean_inc_ref(v_modifier_7284_);
lean_dec_ref_known(v_head_7278_, 1);
v___f_7285_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0), 5, 4);
lean_closure_set(v___f_7285_, 0, v_dateformat_7275_);
lean_closure_set(v___f_7285_, 1, v_modifier_7284_);
lean_closure_set(v___f_7285_, 2, v_data_7276_);
lean_closure_set(v___f_7285_, 3, v_tail_7283_);
return v___f_7285_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0(lean_object* v_dateformat_7286_, lean_object* v_modifier_7287_, lean_object* v_data_7288_, lean_object* v_tail_7289_, lean_object* v___y_7290_){
_start:
{
lean_object* v___x_7291_; lean_object* v___x_7292_; lean_object* v___x_7293_; 
v___x_7291_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7286_, v_modifier_7287_, v___y_7290_);
v___x_7292_ = lean_string_append(v_data_7288_, v___x_7291_);
lean_dec_ref(v___x_7291_);
v___x_7293_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7286_, v___x_7292_, v_tail_7289_);
return v___x_7293_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___redArg(lean_object* v_format_7294_){
_start:
{
lean_object* v_config_7295_; lean_object* v_string_7296_; lean_object* v_dateformat_7297_; lean_object* v___x_7298_; lean_object* v___x_7299_; 
v_config_7295_ = lean_ctor_get(v_format_7294_, 0);
lean_inc_ref(v_config_7295_);
v_string_7296_ = lean_ctor_get(v_format_7294_, 1);
lean_inc(v_string_7296_);
lean_dec_ref(v_format_7294_);
v_dateformat_7297_ = lean_ctor_get(v_config_7295_, 0);
lean_inc_ref(v_dateformat_7297_);
lean_dec_ref(v_config_7295_);
v___x_7298_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_7299_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7297_, v___x_7298_, v_string_7296_);
return v___x_7299_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder(lean_object* v_aw_7300_, lean_object* v_format_7301_){
_start:
{
lean_object* v___x_7302_; 
v___x_7302_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v_format_7301_);
return v___x_7302_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___boxed(lean_object* v_aw_7303_, lean_object* v_format_7304_){
_start:
{
lean_object* v_res_7305_; 
v_res_7305_ = l_Std_Time_GenericFormat_formatBuilder(v_aw_7303_, v_format_7304_);
lean_dec(v_aw_7303_);
return v_res_7305_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instFormatGenericFormatFormatTypeString(lean_object* v_aw_7306_){
_start:
{
lean_object* v___x_7307_; lean_object* v___x_7308_; lean_object* v___x_7309_; 
lean_inc(v_aw_7306_);
v___x_7307_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_formatBuilder___boxed), 2, 1);
lean_closure_set(v___x_7307_, 0, v_aw_7306_);
v___x_7308_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parseBuilder___boxed), 5, 1);
lean_closure_set(v___x_7308_, 0, v_aw_7306_);
v___x_7309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7309_, 0, v___x_7307_);
lean_ctor_set(v___x_7309_, 1, v___x_7308_);
return v___x_7309_;
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
l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1 = _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1();
lean_mark_persistent(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1);
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
