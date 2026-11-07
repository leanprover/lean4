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
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Time_DateFormat_enUS;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Internal_Parsec_String_pstring(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
extern lean_object* l_Std_Time_TimeZone_Offset_zero;
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_String_Slice_toNat_x21(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t l_Std_Time_Weekday_ofOrdinal(lean_object*);
lean_object* l_Std_Time_Weekday_toOrdinal(uint8_t);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
extern lean_object* l_Std_Time_TimeZone_GMT;
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_Std_Time_PlainTime_ofNanoseconds(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_Offset_toIsoString(lean_object*, uint8_t);
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Std_Time_HourMarker_toAbsolute(uint8_t, lean_object*);
lean_object* l_Std_Time_PlainDateTime_toWallTime(lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* l_Std_Time_Second_instOfNatOrdinal(uint8_t, lean_object*);
lean_object* l_Std_Time_PlainDate_startOfWeekBasedYear(lean_object*, uint8_t, lean_object*);
lean_object* l_Std_Time_PlainDate_toEpochDay(lean_object*);
lean_object* l_Std_Time_PlainDate_ofEpochDay(lean_object*);
lean_object* l_Std_Time_PlainDate_weekYear(lean_object*, uint8_t, lean_object*);
lean_object* l_Std_Time_ValidDate_ofOrdinal(uint8_t, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
extern lean_object* l_Std_Time_instInhabitedDateTime;
lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
lean_object* l_Std_Time_PlainDate_dayOfYear(lean_object*);
lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*, uint8_t, lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfMonth(lean_object*, uint8_t);
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object*);
uint8_t l_Std_Time_HourMarker_ofOrdinal(lean_object*);
lean_object* l_Std_Time_Hour_Ordinal_toRelative(lean_object*);
lean_object* l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(lean_object*);
lean_object* l_Std_Time_PlainTime_toMilliseconds(lean_object*);
lean_object* l_Std_Time_PlainTime_toNanoseconds(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_Time_instReprModifier_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_Awareness_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Awareness_ctorIdx___impl___boxed(lean_object*);
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
static lean_once_cell_t l_Std_Time_instInhabitedFormatConfig_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedFormatConfig_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedFormatConfig_default;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedFormatConfig;
static lean_once_cell_t l_Std_Time_instInhabitedGenericFormat_default___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedGenericFormat_default___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default___redArg();
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_instInhabitedGenericFormat_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedGenericFormat_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat___redArg();
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat___redArg___boxed(lean_object*);
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
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: '\"'"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__0_value)}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: '''"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(uint32_t, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(uint32_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1___boxed__const__1;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: '\\'"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__3 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__3_value)}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__4 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__4_value;
static const lean_closure_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__5 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__5_value;
static const lean_closure_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__6 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__6_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_specParser_spec__0(lean_object*, lean_object*);
static const lean_array_object l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__0_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expected end of input"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__1_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__1_value)}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParser(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_pad_spec__0(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear___closed__0;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthNames(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthNames___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayNames(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayNames___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraNames(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraNames___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_quarterNames(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_quarterNames___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_markerNames(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_markerNames___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dayPeriodNames(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dayPeriodNames___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodNames(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodNames___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthOfIndex_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthOfIndex(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayIndex(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayIndex___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_quarterIndex(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_quarterIndex___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_quarterOfIndex(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_markerIndex(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_markerIndex___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_markerOfIndex(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_markerOfIndex___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dayPeriodIndex(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dayPeriodIndex___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_dayPeriodOfIndex(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dayPeriodOfIndex___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodOfIndex(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodOfIndex___boxed(lean_object*);
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_dropSeconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dropSeconds___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dropSeconds(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dropSeconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_dropSeconds_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatOffsetX(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatOffsetX___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_formatGmtOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GMT"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatGmtOffset___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_formatGmtOffset___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatGmtOffset(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_zoneLabel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_zoneLabel___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_classifyDayPeriod___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_classifyDayPeriod___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_formatWith_spec__0(lean_object*);
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "unk"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2_value;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Z"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__5 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__5_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2_value)}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__2 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseName_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseName_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseName___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseName_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_parseMonthShort(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_digitRunLength(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseVarWidthNum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseVarWidthNum___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expected: +"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__0_value)}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__1_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: '-'"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__2 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__2_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__2_value)}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__3 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__3_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: '+'"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__4 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__4_value)}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__5 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__5_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseZoneId(lean_object*);
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "need a natural number in the interval of "};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__0_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " to "};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___impl___boxed(lean_object*);
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
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: ':'"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid hour offset: "};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = ". Must be between 0 and 23."};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__1_value;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2;
static const lean_closure_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(uint8_t, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffsetX(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffsetX___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseGmtOffset(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseGmtOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_isNumericModifier(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_isNumericModifier___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits_covering(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits_covering___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits___closed__1_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits___closed__2 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseField(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseField___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_reservedDigits___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_reservedDigits___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_reservedDigits___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_reservedDigits(lean_object*);
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "need a natural number in the interval of 1 to 7"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_value)}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2_value;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__3;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4;
static const lean_closure_object l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1))} };
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_offsetOfZoneId_x3f___lam__0(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_offsetOfZoneId_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_offsetOfZoneId_x3f___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_formatGmtOffset___closed__0_value)} };
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_offsetOfZoneId_x3f___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_offsetOfZoneId_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_offsetOfZoneId_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekDate(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSome_x3f___at___00__private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSome_x3f___at___00__private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__0;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__1;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__2;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__5;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__6;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__7;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__8;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__9;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__10;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__11;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__13;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__14;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__15;
static lean_once_cell_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__16;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__3(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_GenericFormat_spec_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Std.Time.Format.Basic"};
static const lean_object* l_Std_Time_GenericFormat_spec_x21___closed__0 = (const lean_object*)&l_Std_Time_GenericFormat_spec_x21___closed__0_value;
static const lean_string_object l_Std_Time_GenericFormat_spec_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Std.Time.GenericFormat.spec!"};
static const lean_object* l_Std_Time_GenericFormat_spec_x21___closed__1 = (const lean_object*)&l_Std_Time_GenericFormat_spec_x21___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatParts___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatParts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatParts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_Time_FormatPart_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
lean_object* v_val_7_; lean_object* v___x_8_; 
v_val_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_val_7_);
lean_dec_ref(v_t_5_);
v___x_8_ = lean_apply_1(v_k_6_, v_val_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Std_Time_FormatPart_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_Time_FormatPart_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_string_elim___redArg(lean_object* v_t_21_, lean_object* v_string_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Std_Time_FormatPart_ctorElim___redArg(v_t_21_, v_string_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_string_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_string_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Std_Time_FormatPart_ctorElim___redArg(v_t_25_, v_string_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_modifier_elim___redArg(lean_object* v_t_29_, lean_object* v_modifier_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Std_Time_FormatPart_ctorElim___redArg(v_t_29_, v_modifier_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_FormatPart_modifier_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_modifier_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Std_Time_FormatPart_ctorElim___redArg(v_t_33_, v_modifier_35_);
return v___x_36_;
}
}
static lean_object* _init_l_Std_Time_instReprFormatPart_repr___closed__3(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_unsigned_to_nat(2u);
v___x_44_ = lean_nat_to_int(v___x_43_);
return v___x_44_;
}
}
static lean_object* _init_l_Std_Time_instReprFormatPart_repr___closed__4(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_unsigned_to_nat(1u);
v___x_46_ = lean_nat_to_int(v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprFormatPart_repr(lean_object* v_x_53_, lean_object* v_prec_54_){
_start:
{
if (lean_obj_tag(v_x_53_) == 0)
{
lean_object* v_val_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_75_; 
v_val_55_ = lean_ctor_get(v_x_53_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v_x_53_);
if (v_isSharedCheck_75_ == 0)
{
v___x_57_ = v_x_53_;
v_isShared_58_ = v_isSharedCheck_75_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_val_55_);
lean_dec(v_x_53_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_75_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___y_60_; lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(1024u);
v___x_72_ = lean_nat_dec_le(v___x_71_, v_prec_54_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; 
v___x_73_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__3, &l_Std_Time_instReprFormatPart_repr___closed__3_once, _init_l_Std_Time_instReprFormatPart_repr___closed__3);
v___y_60_ = v___x_73_;
goto v___jp_59_;
}
else
{
lean_object* v___x_74_; 
v___x_74_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___y_60_ = v___x_74_;
goto v___jp_59_;
}
v___jp_59_:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
v___x_61_ = ((lean_object*)(l_Std_Time_instReprFormatPart_repr___closed__2));
v___x_62_ = l_String_quote(v_val_55_);
if (v_isShared_58_ == 0)
{
lean_ctor_set_tag(v___x_57_, 3);
lean_ctor_set(v___x_57_, 0, v___x_62_);
v___x_64_ = v___x_57_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_62_);
v___x_64_ = v_reuseFailAlloc_70_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_65_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_61_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
lean_inc(v___y_60_);
v___x_66_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_66_, 0, v___y_60_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
v___x_67_ = 0;
v___x_68_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_68_, 0, v___x_66_);
lean_ctor_set_uint8(v___x_68_, sizeof(void*)*1, v___x_67_);
v___x_69_ = l_Repr_addAppParen(v___x_68_, v_prec_54_);
return v___x_69_;
}
}
}
}
else
{
lean_object* v_modifier_76_; lean_object* v___y_78_; lean_object* v___x_87_; uint8_t v___x_88_; 
v_modifier_76_ = lean_ctor_get(v_x_53_, 0);
lean_inc_ref(v_modifier_76_);
lean_dec_ref_known(v_x_53_, 1);
v___x_87_ = lean_unsigned_to_nat(1024u);
v___x_88_ = lean_nat_dec_le(v___x_87_, v_prec_54_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; 
v___x_89_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__3, &l_Std_Time_instReprFormatPart_repr___closed__3_once, _init_l_Std_Time_instReprFormatPart_repr___closed__3);
v___y_78_ = v___x_89_;
goto v___jp_77_;
}
else
{
lean_object* v___x_90_; 
v___x_90_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___y_78_ = v___x_90_;
goto v___jp_77_;
}
v___jp_77_:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_79_ = ((lean_object*)(l_Std_Time_instReprFormatPart_repr___closed__7));
v___x_80_ = lean_unsigned_to_nat(1024u);
v___x_81_ = l_Std_Time_instReprModifier_repr(v_modifier_76_, v___x_80_);
v___x_82_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_79_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
lean_inc(v___y_78_);
v___x_83_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_83_, 0, v___y_78_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = 0;
v___x_85_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set_uint8(v___x_85_, sizeof(void*)*1, v___x_84_);
v___x_86_ = l_Repr_addAppParen(v___x_85_, v_prec_54_);
return v___x_86_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprFormatPart_repr___boxed(lean_object* v_x_91_, lean_object* v_prec_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Std_Time_instReprFormatPart_repr(v_x_91_, v_prec_92_);
lean_dec(v_prec_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instCoeStringFormatPart___lam__0(lean_object* v_val_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v_val_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instCoeModifierFormatPart___lam__0(lean_object* v_modifier_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_101_, 0, v_modifier_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_ctorIdx___impl(lean_object* v_x_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_tag_nat(v_x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_ctorIdx___impl___boxed(lean_object* v_x_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Std_Time_Awareness_ctorIdx___impl(v_x_106_);
lean_dec(v_x_106_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_ctorElim___redArg(lean_object* v_t_108_, lean_object* v_k_109_){
_start:
{
if (lean_obj_tag(v_t_108_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_111_; 
v_a_110_ = lean_ctor_get(v_t_108_, 0);
lean_inc_ref(v_a_110_);
lean_dec_ref_known(v_t_108_, 1);
v___x_111_ = lean_apply_1(v_k_109_, v_a_110_);
return v___x_111_;
}
else
{
return v_k_109_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_ctorElim(lean_object* v_motive_112_, lean_object* v_ctorIdx_113_, lean_object* v_t_114_, lean_object* v_h_115_, lean_object* v_k_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Std_Time_Awareness_ctorElim___redArg(v_t_114_, v_k_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_ctorElim___boxed(lean_object* v_motive_118_, lean_object* v_ctorIdx_119_, lean_object* v_t_120_, lean_object* v_h_121_, lean_object* v_k_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Std_Time_Awareness_ctorElim(v_motive_118_, v_ctorIdx_119_, v_t_120_, v_h_121_, v_k_122_);
lean_dec(v_ctorIdx_119_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_only_elim___redArg(lean_object* v_t_124_, lean_object* v_only_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Std_Time_Awareness_ctorElim___redArg(v_t_124_, v_only_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_only_elim(lean_object* v_motive_127_, lean_object* v_t_128_, lean_object* v_h_129_, lean_object* v_only_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Std_Time_Awareness_ctorElim___redArg(v_t_128_, v_only_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_any_elim___redArg(lean_object* v_t_132_, lean_object* v_any_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Std_Time_Awareness_ctorElim___redArg(v_t_132_, v_any_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_any_elim(lean_object* v_motive_135_, lean_object* v_t_136_, lean_object* v_h_137_, lean_object* v_any_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Std_Time_Awareness_ctorElim___redArg(v_t_136_, v_any_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Awareness_instCoeTimeZone___lam__0(lean_object* v_a_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_141_, 0, v_a_140_);
return v___x_141_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedFormatConfig_default___closed__0(void){
_start:
{
lean_object* v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; 
v___x_144_ = l_Std_Time_DateFormat_enUS;
v___x_145_ = 0;
v___x_146_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set_uint8(v___x_146_, sizeof(void*)*1, v___x_145_);
return v___x_146_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedFormatConfig_default(void){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lean_obj_once(&l_Std_Time_instInhabitedFormatConfig_default___closed__0, &l_Std_Time_instInhabitedFormatConfig_default___closed__0_once, _init_l_Std_Time_instInhabitedFormatConfig_default___closed__0);
return v___x_147_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedFormatConfig(void){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Std_Time_instInhabitedFormatConfig_default;
return v___x_148_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedGenericFormat_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_box(0);
v___x_150_ = l_Std_Time_instInhabitedFormatConfig_default;
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v___x_149_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default___redArg(){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___redArg___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___redArg___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___redArg___closed__0);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default___redArg___boxed(lean_object* v___dummy_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Std_Time_instInhabitedGenericFormat_default___redArg();
return v_res_155_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0(void){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_Time_instInhabitedGenericFormat_default___redArg();
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default(lean_object* v_awareness_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default___boxed(lean_object* v_awareness_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Std_Time_instInhabitedGenericFormat_default(v_awareness_159_);
lean_dec(v_awareness_159_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat___redArg(){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat___redArg___boxed(lean_object* v___dummy_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Std_Time_instInhabitedGenericFormat___redArg();
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat(lean_object* v_a_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat___boxed(lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Std_Time_instInhabitedGenericFormat(v_a_167_);
lean_dec(v_a_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(lean_object* v_a_169_, lean_object* v_f_170_, lean_object* v___y_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_apply_1(v_a_169_, v___y_171_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_pos_173_; lean_object* v_res_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_182_; 
v_pos_173_ = lean_ctor_get(v___x_172_, 0);
v_res_174_ = lean_ctor_get(v___x_172_, 1);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_182_ == 0)
{
v___x_176_ = v___x_172_;
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_res_174_);
lean_inc(v_pos_173_);
lean_dec(v___x_172_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_178_ = lean_apply_1(v_f_170_, v_res_174_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 1, v___x_178_);
v___x_180_ = v___x_176_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_pos_173_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
else
{
lean_object* v_pos_183_; lean_object* v_err_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
lean_dec(v_f_170_);
v_pos_183_ = lean_ctor_get(v___x_172_, 0);
v_err_184_ = lean_ctor_get(v___x_172_, 1);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_172_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_err_184_);
lean_inc(v_pos_183_);
lean_dec(v___x_172_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_pos_183_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_err_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1(lean_object* v_00_u03b1_192_, lean_object* v_00_u03b2_193_, lean_object* v_a_194_, lean_object* v_f_195_, lean_object* v___y_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v_a_194_, v_f_195_, v___y_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0(lean_object* v_acc_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_fst_203_; lean_object* v_snd_204_; lean_object* v_pos_206_; lean_object* v_snd_207_; lean_object* v_err_208_; lean_object* v___x_212_; uint8_t v_decide_213_; 
v_fst_203_ = lean_ctor_get(v_a_202_, 0);
v_snd_204_ = lean_ctor_get(v_a_202_, 1);
lean_inc(v_snd_204_);
v___x_212_ = lean_string_utf8_byte_size(v_fst_203_);
v_decide_213_ = lean_nat_dec_eq(v_snd_204_, v___x_212_);
if (v_decide_213_ == 0)
{
uint32_t v___x_214_; uint32_t v_c_215_; uint8_t v___x_216_; 
v___x_214_ = 34;
v_c_215_ = lean_string_utf8_get_fast(v_fst_203_, v_snd_204_);
v___x_216_ = lean_uint32_dec_eq(v_c_215_, v___x_214_);
if (v___x_216_ == 0)
{
lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_226_; 
lean_inc(v_fst_203_);
v_isSharedCheck_226_ = !lean_is_exclusive(v_a_202_);
if (v_isSharedCheck_226_ == 0)
{
lean_object* v_unused_227_; lean_object* v_unused_228_; 
v_unused_227_ = lean_ctor_get(v_a_202_, 1);
lean_dec(v_unused_227_);
v_unused_228_ = lean_ctor_get(v_a_202_, 0);
lean_dec(v_unused_228_);
v___x_218_ = v_a_202_;
v_isShared_219_ = v_isSharedCheck_226_;
goto v_resetjp_217_;
}
else
{
lean_dec(v_a_202_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_226_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; lean_object* v_it_x27_222_; 
v___x_220_ = lean_string_utf8_next_fast(v_fst_203_, v_snd_204_);
lean_dec(v_snd_204_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 1, v___x_220_);
v_it_x27_222_ = v___x_218_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_fst_203_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___x_220_);
v_it_x27_222_ = v_reuseFailAlloc_225_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_223_; 
v___x_223_ = lean_string_push(v_acc_201_, v_c_215_);
v_acc_201_ = v___x_223_;
v_a_202_ = v_it_x27_222_;
goto _start;
}
}
}
else
{
lean_object* v___x_229_; 
v___x_229_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_204_);
v_pos_206_ = v_a_202_;
v_snd_207_ = v_snd_204_;
v_err_208_ = v___x_229_;
goto v___jp_205_;
}
}
else
{
lean_object* v___x_230_; 
v___x_230_ = lean_box(0);
lean_inc(v_snd_204_);
v_pos_206_ = v_a_202_;
v_snd_207_ = v_snd_204_;
v_err_208_ = v___x_230_;
goto v___jp_205_;
}
v___jp_205_:
{
uint8_t v_decide_209_; 
v_decide_209_ = lean_nat_dec_eq(v_snd_204_, v_snd_207_);
lean_dec(v_snd_207_);
lean_dec(v_snd_204_);
if (v_decide_209_ == 0)
{
lean_object* v___x_210_; 
lean_dec_ref(v_acc_201_);
lean_inc(v_err_208_);
v___x_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_210_, 0, v_pos_206_);
lean_ctor_set(v___x_210_, 1, v_err_208_);
return v___x_210_;
}
else
{
lean_object* v___x_211_; 
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v_pos_206_);
lean_ctor_set(v___x_211_, 1, v_acc_201_);
return v___x_211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0(lean_object* v_acc_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_fst_233_; lean_object* v_snd_234_; lean_object* v_pos_236_; lean_object* v_snd_237_; lean_object* v_err_238_; lean_object* v___x_242_; uint8_t v_decide_243_; 
v_fst_233_ = lean_ctor_get(v_a_232_, 0);
v_snd_234_ = lean_ctor_get(v_a_232_, 1);
lean_inc(v_snd_234_);
v___x_242_ = lean_string_utf8_byte_size(v_fst_233_);
v_decide_243_ = lean_nat_dec_eq(v_snd_234_, v___x_242_);
if (v_decide_243_ == 0)
{
uint32_t v___x_244_; uint32_t v_c_245_; uint8_t v___x_246_; 
v___x_244_ = 34;
v_c_245_ = lean_string_utf8_get_fast(v_fst_233_, v_snd_234_);
v___x_246_ = lean_uint32_dec_eq(v_c_245_, v___x_244_);
if (v___x_246_ == 0)
{
lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_256_; 
lean_inc(v_fst_233_);
v_isSharedCheck_256_ = !lean_is_exclusive(v_a_232_);
if (v_isSharedCheck_256_ == 0)
{
lean_object* v_unused_257_; lean_object* v_unused_258_; 
v_unused_257_ = lean_ctor_get(v_a_232_, 1);
lean_dec(v_unused_257_);
v_unused_258_ = lean_ctor_get(v_a_232_, 0);
lean_dec(v_unused_258_);
v___x_248_ = v_a_232_;
v_isShared_249_ = v_isSharedCheck_256_;
goto v_resetjp_247_;
}
else
{
lean_dec(v_a_232_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_256_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v_it_x27_252_; 
v___x_250_ = lean_string_utf8_next_fast(v_fst_233_, v_snd_234_);
lean_dec(v_snd_234_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 1, v___x_250_);
v_it_x27_252_ = v___x_248_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_fst_233_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v___x_250_);
v_it_x27_252_ = v_reuseFailAlloc_255_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_string_push(v_acc_231_, v_c_245_);
v___x_254_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0(v___x_253_, v_it_x27_252_);
return v___x_254_;
}
}
}
else
{
lean_object* v___x_259_; 
v___x_259_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_234_);
v_pos_236_ = v_a_232_;
v_snd_237_ = v_snd_234_;
v_err_238_ = v___x_259_;
goto v___jp_235_;
}
}
else
{
lean_object* v___x_260_; 
v___x_260_ = lean_box(0);
lean_inc(v_snd_234_);
v_pos_236_ = v_a_232_;
v_snd_237_ = v_snd_234_;
v_err_238_ = v___x_260_;
goto v___jp_235_;
}
v___jp_235_:
{
uint8_t v_decide_239_; 
v_decide_239_ = lean_nat_dec_eq(v_snd_234_, v_snd_237_);
lean_dec(v_snd_237_);
lean_dec(v_snd_234_);
if (v_decide_239_ == 0)
{
lean_object* v___x_240_; 
lean_dec_ref(v_acc_231_);
lean_inc(v_err_238_);
v___x_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_240_, 0, v_pos_236_);
lean_ctor_set(v___x_240_, 1, v_err_238_);
return v___x_240_;
}
else
{
lean_object* v___x_241_; 
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v_pos_236_);
lean_ctor_set(v___x_241_, 1, v_acc_231_);
return v___x_241_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(uint32_t v___x_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_fst_267_; lean_object* v_snd_268_; lean_object* v___x_269_; uint8_t v_decide_270_; 
v_fst_267_ = lean_ctor_get(v___y_266_, 0);
v_snd_268_ = lean_ctor_get(v___y_266_, 1);
v___x_269_ = lean_string_utf8_byte_size(v_fst_267_);
v_decide_270_ = lean_nat_dec_eq(v_snd_268_, v___x_269_);
if (v_decide_270_ == 0)
{
uint32_t v_c_271_; uint8_t v___x_272_; 
v_c_271_ = lean_string_utf8_get_fast(v_fst_267_, v_snd_268_);
v___x_272_ = lean_uint32_dec_eq(v_c_271_, v___x_265_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_274_, 0, v___y_266_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
return v___x_274_;
}
else
{
lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_327_; 
lean_inc(v_snd_268_);
lean_inc(v_fst_267_);
v_isSharedCheck_327_ = !lean_is_exclusive(v___y_266_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; lean_object* v_unused_329_; 
v_unused_328_ = lean_ctor_get(v___y_266_, 1);
lean_dec(v_unused_328_);
v_unused_329_ = lean_ctor_get(v___y_266_, 0);
lean_dec(v_unused_329_);
v___x_276_ = v___y_266_;
v_isShared_277_ = v_isSharedCheck_327_;
goto v_resetjp_275_;
}
else
{
lean_dec(v___y_266_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_327_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v_it_x27_280_; 
v___x_278_ = lean_string_utf8_next_fast(v_fst_267_, v_snd_268_);
lean_dec(v_snd_268_);
lean_inc(v_fst_267_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 1, v___x_278_);
v_it_x27_280_ = v___x_276_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_fst_267_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_278_);
v_it_x27_280_ = v_reuseFailAlloc_326_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
uint8_t v_decide_281_; 
v_decide_281_ = lean_nat_dec_eq(v___x_278_, v___x_269_);
if (v_decide_281_ == 0)
{
uint32_t v___x_282_; uint8_t v___x_283_; 
v___x_282_ = lean_string_utf8_get_fast(v_fst_267_, v___x_278_);
v___x_283_ = lean_uint32_dec_eq(v___x_282_, v___x_265_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec_ref(v_it_x27_280_);
v___x_284_ = lean_string_utf8_next_fast(v_fst_267_, v___x_278_);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v_fst_267_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_287_ = lean_string_push(v___x_286_, v___x_282_);
v___x_288_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0(v___x_287_, v___x_285_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_pos_289_; lean_object* v_res_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_321_; 
v_pos_289_ = lean_ctor_get(v___x_288_, 0);
v_res_290_ = lean_ctor_get(v___x_288_, 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_321_ == 0)
{
v___x_292_ = v___x_288_;
v_isShared_293_ = v_isSharedCheck_321_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_res_290_);
lean_inc(v_pos_289_);
lean_dec(v___x_288_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_321_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v_fst_294_; lean_object* v_snd_295_; lean_object* v___x_296_; uint8_t v_decide_297_; 
v_fst_294_ = lean_ctor_get(v_pos_289_, 0);
v_snd_295_ = lean_ctor_get(v_pos_289_, 1);
v___x_296_ = lean_string_utf8_byte_size(v_fst_294_);
v_decide_297_ = lean_nat_dec_eq(v_snd_295_, v___x_296_);
if (v_decide_297_ == 0)
{
uint32_t v_c_298_; uint8_t v___x_299_; 
v_c_298_ = lean_string_utf8_get_fast(v_fst_294_, v_snd_295_);
v___x_299_ = lean_uint32_dec_eq(v_c_298_, v___x_265_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_302_; 
lean_dec(v_res_290_);
v___x_300_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
if (v_isShared_293_ == 0)
{
lean_ctor_set_tag(v___x_292_, 1);
lean_ctor_set(v___x_292_, 1, v___x_300_);
v___x_302_ = v___x_292_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_pos_289_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v___x_300_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
else
{
lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_314_; 
lean_inc(v_snd_295_);
lean_inc(v_fst_294_);
v_isSharedCheck_314_ = !lean_is_exclusive(v_pos_289_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; lean_object* v_unused_316_; 
v_unused_315_ = lean_ctor_get(v_pos_289_, 1);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_pos_289_, 0);
lean_dec(v_unused_316_);
v___x_305_ = v_pos_289_;
v_isShared_306_ = v_isSharedCheck_314_;
goto v_resetjp_304_;
}
else
{
lean_dec(v_pos_289_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_314_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v_it_x27_309_; 
v___x_307_ = lean_string_utf8_next_fast(v_fst_294_, v_snd_295_);
lean_dec(v_snd_295_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v___x_307_);
v_it_x27_309_ = v___x_305_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_fst_294_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v___x_307_);
v_it_x27_309_ = v_reuseFailAlloc_313_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_311_; 
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v_it_x27_309_);
v___x_311_ = v___x_292_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_it_x27_309_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_res_290_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
else
{
lean_object* v___x_317_; lean_object* v___x_319_; 
lean_dec(v_res_290_);
v___x_317_ = lean_box(0);
if (v_isShared_293_ == 0)
{
lean_ctor_set_tag(v___x_292_, 1);
lean_ctor_set(v___x_292_, 1, v___x_317_);
v___x_319_ = v___x_292_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_pos_289_);
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
}
else
{
return v___x_288_;
}
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec(v_fst_267_);
v___x_322_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_323_, 0, v_it_x27_280_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
return v___x_323_;
}
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec(v_fst_267_);
v___x_324_ = lean_box(0);
v___x_325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_325_, 0, v_it_x27_280_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
return v___x_325_;
}
}
}
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_box(0);
v___x_331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_331_, 0, v___y_266_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___boxed(lean_object* v___x_332_, lean_object* v___y_333_){
_start:
{
uint32_t v___x_11507__boxed_334_; lean_object* v_res_335_; 
v___x_11507__boxed_334_ = lean_unbox_uint32(v___x_332_);
lean_dec(v___x_332_);
v_res_335_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(v___x_11507__boxed_334_, v___y_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2_spec__3(lean_object* v_acc_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_fst_338_; lean_object* v_snd_339_; lean_object* v_pos_341_; lean_object* v_snd_342_; lean_object* v_err_343_; lean_object* v___x_347_; uint8_t v_decide_348_; 
v_fst_338_ = lean_ctor_get(v_a_337_, 0);
v_snd_339_ = lean_ctor_get(v_a_337_, 1);
lean_inc(v_snd_339_);
v___x_347_ = lean_string_utf8_byte_size(v_fst_338_);
v_decide_348_ = lean_nat_dec_eq(v_snd_339_, v___x_347_);
if (v_decide_348_ == 0)
{
uint32_t v___x_349_; uint32_t v_c_350_; uint8_t v___x_351_; 
v___x_349_ = 39;
v_c_350_ = lean_string_utf8_get_fast(v_fst_338_, v_snd_339_);
v___x_351_ = lean_uint32_dec_eq(v_c_350_, v___x_349_);
if (v___x_351_ == 0)
{
lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_361_; 
lean_inc(v_fst_338_);
v_isSharedCheck_361_ = !lean_is_exclusive(v_a_337_);
if (v_isSharedCheck_361_ == 0)
{
lean_object* v_unused_362_; lean_object* v_unused_363_; 
v_unused_362_ = lean_ctor_get(v_a_337_, 1);
lean_dec(v_unused_362_);
v_unused_363_ = lean_ctor_get(v_a_337_, 0);
lean_dec(v_unused_363_);
v___x_353_ = v_a_337_;
v_isShared_354_ = v_isSharedCheck_361_;
goto v_resetjp_352_;
}
else
{
lean_dec(v_a_337_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_361_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v_it_x27_357_; 
v___x_355_ = lean_string_utf8_next_fast(v_fst_338_, v_snd_339_);
lean_dec(v_snd_339_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v___x_355_);
v_it_x27_357_ = v___x_353_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_fst_338_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v___x_355_);
v_it_x27_357_ = v_reuseFailAlloc_360_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; 
v___x_358_ = lean_string_push(v_acc_336_, v_c_350_);
v_acc_336_ = v___x_358_;
v_a_337_ = v_it_x27_357_;
goto _start;
}
}
}
else
{
lean_object* v___x_364_; 
v___x_364_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_339_);
v_pos_341_ = v_a_337_;
v_snd_342_ = v_snd_339_;
v_err_343_ = v___x_364_;
goto v___jp_340_;
}
}
else
{
lean_object* v___x_365_; 
v___x_365_ = lean_box(0);
lean_inc(v_snd_339_);
v_pos_341_ = v_a_337_;
v_snd_342_ = v_snd_339_;
v_err_343_ = v___x_365_;
goto v___jp_340_;
}
v___jp_340_:
{
uint8_t v_decide_344_; 
v_decide_344_ = lean_nat_dec_eq(v_snd_339_, v_snd_342_);
lean_dec(v_snd_342_);
lean_dec(v_snd_339_);
if (v_decide_344_ == 0)
{
lean_object* v___x_345_; 
lean_dec_ref(v_acc_336_);
lean_inc(v_err_343_);
v___x_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_345_, 0, v_pos_341_);
lean_ctor_set(v___x_345_, 1, v_err_343_);
return v___x_345_;
}
else
{
lean_object* v___x_346_; 
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v_pos_341_);
lean_ctor_set(v___x_346_, 1, v_acc_336_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2(lean_object* v_acc_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_fst_368_; lean_object* v_snd_369_; lean_object* v_pos_371_; lean_object* v_snd_372_; lean_object* v_err_373_; lean_object* v___x_377_; uint8_t v_decide_378_; 
v_fst_368_ = lean_ctor_get(v_a_367_, 0);
v_snd_369_ = lean_ctor_get(v_a_367_, 1);
lean_inc(v_snd_369_);
v___x_377_ = lean_string_utf8_byte_size(v_fst_368_);
v_decide_378_ = lean_nat_dec_eq(v_snd_369_, v___x_377_);
if (v_decide_378_ == 0)
{
uint32_t v___x_379_; uint32_t v_c_380_; uint8_t v___x_381_; 
v___x_379_ = 39;
v_c_380_ = lean_string_utf8_get_fast(v_fst_368_, v_snd_369_);
v___x_381_ = lean_uint32_dec_eq(v_c_380_, v___x_379_);
if (v___x_381_ == 0)
{
lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_391_; 
lean_inc(v_fst_368_);
v_isSharedCheck_391_ = !lean_is_exclusive(v_a_367_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; lean_object* v_unused_393_; 
v_unused_392_ = lean_ctor_get(v_a_367_, 1);
lean_dec(v_unused_392_);
v_unused_393_ = lean_ctor_get(v_a_367_, 0);
lean_dec(v_unused_393_);
v___x_383_ = v_a_367_;
v_isShared_384_ = v_isSharedCheck_391_;
goto v_resetjp_382_;
}
else
{
lean_dec(v_a_367_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_391_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v_it_x27_387_; 
v___x_385_ = lean_string_utf8_next_fast(v_fst_368_, v_snd_369_);
lean_dec(v_snd_369_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 1, v___x_385_);
v_it_x27_387_ = v___x_383_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_fst_368_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v___x_385_);
v_it_x27_387_ = v_reuseFailAlloc_390_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_string_push(v_acc_366_, v_c_380_);
v___x_389_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2_spec__3(v___x_388_, v_it_x27_387_);
return v___x_389_;
}
}
}
else
{
lean_object* v___x_394_; 
v___x_394_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_369_);
v_pos_371_ = v_a_367_;
v_snd_372_ = v_snd_369_;
v_err_373_ = v___x_394_;
goto v___jp_370_;
}
}
else
{
lean_object* v___x_395_; 
v___x_395_ = lean_box(0);
lean_inc(v_snd_369_);
v_pos_371_ = v_a_367_;
v_snd_372_ = v_snd_369_;
v_err_373_ = v___x_395_;
goto v___jp_370_;
}
v___jp_370_:
{
uint8_t v_decide_374_; 
v_decide_374_ = lean_nat_dec_eq(v_snd_369_, v_snd_372_);
lean_dec(v_snd_372_);
lean_dec(v_snd_369_);
if (v_decide_374_ == 0)
{
lean_object* v___x_375_; 
lean_dec_ref(v_acc_366_);
lean_inc(v_err_373_);
v___x_375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_375_, 0, v_pos_371_);
lean_ctor_set(v___x_375_, 1, v_err_373_);
return v___x_375_;
}
else
{
lean_object* v___x_376_; 
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v_pos_371_);
lean_ctor_set(v___x_376_, 1, v_acc_366_);
return v___x_376_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0(uint32_t v___x_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_fst_401_; lean_object* v_snd_402_; lean_object* v___x_403_; uint8_t v_decide_404_; 
v_fst_401_ = lean_ctor_get(v___y_400_, 0);
v_snd_402_ = lean_ctor_get(v___y_400_, 1);
v___x_403_ = lean_string_utf8_byte_size(v_fst_401_);
v_decide_404_ = lean_nat_dec_eq(v_snd_402_, v___x_403_);
if (v_decide_404_ == 0)
{
uint32_t v_c_405_; uint8_t v___x_406_; 
v_c_405_ = lean_string_utf8_get_fast(v_fst_401_, v_snd_402_);
v___x_406_ = lean_uint32_dec_eq(v_c_405_, v___x_399_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__1));
v___x_408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_408_, 0, v___y_400_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
return v___x_408_;
}
else
{
lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_461_; 
lean_inc(v_snd_402_);
lean_inc(v_fst_401_);
v_isSharedCheck_461_ = !lean_is_exclusive(v___y_400_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; lean_object* v_unused_463_; 
v_unused_462_ = lean_ctor_get(v___y_400_, 1);
lean_dec(v_unused_462_);
v_unused_463_ = lean_ctor_get(v___y_400_, 0);
lean_dec(v_unused_463_);
v___x_410_ = v___y_400_;
v_isShared_411_ = v_isSharedCheck_461_;
goto v_resetjp_409_;
}
else
{
lean_dec(v___y_400_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_461_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; lean_object* v_it_x27_414_; 
v___x_412_ = lean_string_utf8_next_fast(v_fst_401_, v_snd_402_);
lean_dec(v_snd_402_);
lean_inc(v_fst_401_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 1, v___x_412_);
v_it_x27_414_ = v___x_410_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_fst_401_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_412_);
v_it_x27_414_ = v_reuseFailAlloc_460_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
uint8_t v_decide_415_; 
v_decide_415_ = lean_nat_dec_eq(v___x_412_, v___x_403_);
if (v_decide_415_ == 0)
{
uint32_t v___x_416_; uint8_t v___x_417_; 
v___x_416_ = lean_string_utf8_get_fast(v_fst_401_, v___x_412_);
v___x_417_ = lean_uint32_dec_eq(v___x_416_, v___x_399_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec_ref(v_it_x27_414_);
v___x_418_ = lean_string_utf8_next_fast(v_fst_401_, v___x_412_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v_fst_401_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
v___x_420_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_421_ = lean_string_push(v___x_420_, v___x_416_);
v___x_422_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2(v___x_421_, v___x_419_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_pos_423_; lean_object* v_res_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_455_; 
v_pos_423_ = lean_ctor_get(v___x_422_, 0);
v_res_424_ = lean_ctor_get(v___x_422_, 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_455_ == 0)
{
v___x_426_ = v___x_422_;
v_isShared_427_ = v_isSharedCheck_455_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_res_424_);
lean_inc(v_pos_423_);
lean_dec(v___x_422_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_455_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_fst_428_; lean_object* v_snd_429_; lean_object* v___x_430_; uint8_t v_decide_431_; 
v_fst_428_ = lean_ctor_get(v_pos_423_, 0);
v_snd_429_ = lean_ctor_get(v_pos_423_, 1);
v___x_430_ = lean_string_utf8_byte_size(v_fst_428_);
v_decide_431_ = lean_nat_dec_eq(v_snd_429_, v___x_430_);
if (v_decide_431_ == 0)
{
uint32_t v_c_432_; uint8_t v___x_433_; 
v_c_432_ = lean_string_utf8_get_fast(v_fst_428_, v_snd_429_);
v___x_433_ = lean_uint32_dec_eq(v_c_432_, v___x_399_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_436_; 
lean_dec(v_res_424_);
v___x_434_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__1));
if (v_isShared_427_ == 0)
{
lean_ctor_set_tag(v___x_426_, 1);
lean_ctor_set(v___x_426_, 1, v___x_434_);
v___x_436_ = v___x_426_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_pos_423_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
else
{
lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_448_; 
lean_inc(v_snd_429_);
lean_inc(v_fst_428_);
v_isSharedCheck_448_ = !lean_is_exclusive(v_pos_423_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; lean_object* v_unused_450_; 
v_unused_449_ = lean_ctor_get(v_pos_423_, 1);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_pos_423_, 0);
lean_dec(v_unused_450_);
v___x_439_ = v_pos_423_;
v_isShared_440_ = v_isSharedCheck_448_;
goto v_resetjp_438_;
}
else
{
lean_dec(v_pos_423_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_448_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v_it_x27_443_; 
v___x_441_ = lean_string_utf8_next_fast(v_fst_428_, v_snd_429_);
lean_dec(v_snd_429_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___x_441_);
v_it_x27_443_ = v___x_439_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_fst_428_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v___x_441_);
v_it_x27_443_ = v_reuseFailAlloc_447_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_445_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v_it_x27_443_);
v___x_445_ = v___x_426_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_it_x27_443_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_res_424_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
}
else
{
lean_object* v___x_451_; lean_object* v___x_453_; 
lean_dec(v_res_424_);
v___x_451_ = lean_box(0);
if (v_isShared_427_ == 0)
{
lean_ctor_set_tag(v___x_426_, 1);
lean_ctor_set(v___x_426_, 1, v___x_451_);
v___x_453_ = v___x_426_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_pos_423_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
return v___x_422_;
}
}
else
{
lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec(v_fst_401_);
v___x_456_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_457_, 0, v_it_x27_414_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
return v___x_457_;
}
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec(v_fst_401_);
v___x_458_ = lean_box(0);
v___x_459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_459_, 0, v_it_x27_414_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
return v___x_459_;
}
}
}
}
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_box(0);
v___x_465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_465_, 0, v___y_400_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
return v___x_465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___boxed(lean_object* v___x_466_, lean_object* v___y_467_){
_start:
{
uint32_t v___x_11750__boxed_468_; lean_object* v_res_469_; 
v___x_11750__boxed_468_ = lean_unbox_uint32(v___x_466_);
lean_dec(v___x_466_);
v_res_469_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0(v___x_11750__boxed_468_, v___y_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__3(lean_object* v_acc_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_fst_472_; lean_object* v_snd_473_; lean_object* v_pos_475_; lean_object* v_snd_476_; lean_object* v_err_477_; lean_object* v___x_483_; uint8_t v_decide_484_; 
v_fst_472_ = lean_ctor_get(v_a_471_, 0);
v_snd_473_ = lean_ctor_get(v_a_471_, 1);
lean_inc(v_snd_473_);
v___x_483_ = lean_string_utf8_byte_size(v_fst_472_);
v_decide_484_ = lean_nat_dec_eq(v_snd_473_, v___x_483_);
if (v_decide_484_ == 0)
{
uint32_t v___x_485_; uint32_t v___x_486_; uint32_t v_c_487_; lean_object* v___x_488_; lean_object* v_it_x27_489_; uint32_t v___x_500_; uint8_t v___x_501_; 
v___x_485_ = 39;
v___x_486_ = 34;
v_c_487_ = lean_string_utf8_get_fast(v_fst_472_, v_snd_473_);
v___x_488_ = lean_string_utf8_next_fast(v_fst_472_, v_snd_473_);
lean_inc(v_fst_472_);
v_it_x27_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_489_, 0, v_fst_472_);
lean_ctor_set(v_it_x27_489_, 1, v___x_488_);
v___x_500_ = 65;
v___x_501_ = lean_uint32_dec_le(v___x_500_, v_c_487_);
if (v___x_501_ == 0)
{
goto v___jp_495_;
}
else
{
uint32_t v___x_502_; uint8_t v___x_503_; 
v___x_502_ = 90;
v___x_503_ = lean_uint32_dec_le(v_c_487_, v___x_502_);
if (v___x_503_ == 0)
{
goto v___jp_495_;
}
else
{
lean_dec_ref_known(v_it_x27_489_, 2);
goto v___jp_481_;
}
}
v___jp_490_:
{
uint8_t v___x_491_; 
v___x_491_ = lean_uint32_dec_eq(v_c_487_, v___x_485_);
if (v___x_491_ == 0)
{
uint8_t v___x_492_; 
v___x_492_ = lean_uint32_dec_eq(v_c_487_, v___x_486_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; 
lean_dec(v_snd_473_);
lean_dec_ref(v_a_471_);
v___x_493_ = lean_string_push(v_acc_470_, v_c_487_);
v_acc_470_ = v___x_493_;
v_a_471_ = v_it_x27_489_;
goto _start;
}
else
{
lean_dec_ref_known(v_it_x27_489_, 2);
goto v___jp_481_;
}
}
else
{
lean_dec_ref_known(v_it_x27_489_, 2);
goto v___jp_481_;
}
}
v___jp_495_:
{
uint32_t v___x_496_; uint8_t v___x_497_; 
v___x_496_ = 97;
v___x_497_ = lean_uint32_dec_le(v___x_496_, v_c_487_);
if (v___x_497_ == 0)
{
goto v___jp_490_;
}
else
{
uint32_t v___x_498_; uint8_t v___x_499_; 
v___x_498_ = 122;
v___x_499_ = lean_uint32_dec_le(v_c_487_, v___x_498_);
if (v___x_499_ == 0)
{
goto v___jp_490_;
}
else
{
lean_dec_ref_known(v_it_x27_489_, 2);
goto v___jp_481_;
}
}
}
}
else
{
lean_object* v___x_504_; 
v___x_504_ = lean_box(0);
lean_inc(v_snd_473_);
v_pos_475_ = v_a_471_;
v_snd_476_ = v_snd_473_;
v_err_477_ = v___x_504_;
goto v___jp_474_;
}
v___jp_474_:
{
uint8_t v_decide_478_; 
v_decide_478_ = lean_nat_dec_eq(v_snd_473_, v_snd_476_);
lean_dec(v_snd_476_);
lean_dec(v_snd_473_);
if (v_decide_478_ == 0)
{
lean_object* v___x_479_; 
lean_dec_ref(v_acc_470_);
lean_inc(v_err_477_);
v___x_479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_479_, 0, v_pos_475_);
lean_ctor_set(v___x_479_, 1, v_err_477_);
return v___x_479_;
}
else
{
lean_object* v___x_480_; 
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v_pos_475_);
lean_ctor_set(v___x_480_, 1, v_acc_470_);
return v___x_480_;
}
}
v___jp_481_:
{
lean_object* v___x_482_; 
v___x_482_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_473_);
v_pos_475_ = v_a_471_;
v_snd_476_ = v_snd_473_;
v_err_477_ = v___x_482_;
goto v___jp_474_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(uint32_t v___x_505_, uint32_t v___x_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_fst_511_; lean_object* v_snd_512_; lean_object* v___x_513_; uint8_t v_decide_514_; 
v_fst_511_ = lean_ctor_get(v___y_507_, 0);
v_snd_512_ = lean_ctor_get(v___y_507_, 1);
v___x_513_ = lean_string_utf8_byte_size(v_fst_511_);
v_decide_514_ = lean_nat_dec_eq(v_snd_512_, v___x_513_);
if (v_decide_514_ == 0)
{
uint32_t v_c_515_; lean_object* v___x_516_; lean_object* v_it_x27_517_; uint32_t v___x_529_; uint8_t v___x_530_; 
v_c_515_ = lean_string_utf8_get_fast(v_fst_511_, v_snd_512_);
v___x_516_ = lean_string_utf8_next_fast(v_fst_511_, v_snd_512_);
lean_inc(v_fst_511_);
v_it_x27_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_517_, 0, v_fst_511_);
lean_ctor_set(v_it_x27_517_, 1, v___x_516_);
v___x_529_ = 65;
v___x_530_ = lean_uint32_dec_le(v___x_529_, v_c_515_);
if (v___x_530_ == 0)
{
goto v___jp_524_;
}
else
{
uint32_t v___x_531_; uint8_t v___x_532_; 
v___x_531_ = 90;
v___x_532_ = lean_uint32_dec_le(v_c_515_, v___x_531_);
if (v___x_532_ == 0)
{
goto v___jp_524_;
}
else
{
lean_dec_ref_known(v_it_x27_517_, 2);
goto v___jp_508_;
}
}
v___jp_518_:
{
uint8_t v___x_519_; 
v___x_519_ = lean_uint32_dec_eq(v_c_515_, v___x_505_);
if (v___x_519_ == 0)
{
uint8_t v___x_520_; 
v___x_520_ = lean_uint32_dec_eq(v_c_515_, v___x_506_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec_ref(v___y_507_);
v___x_521_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_522_ = lean_string_push(v___x_521_, v_c_515_);
v___x_523_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__3(v___x_522_, v_it_x27_517_);
return v___x_523_;
}
else
{
lean_dec_ref_known(v_it_x27_517_, 2);
goto v___jp_508_;
}
}
else
{
lean_dec_ref_known(v_it_x27_517_, 2);
goto v___jp_508_;
}
}
v___jp_524_:
{
uint32_t v___x_525_; uint8_t v___x_526_; 
v___x_525_ = 97;
v___x_526_ = lean_uint32_dec_le(v___x_525_, v_c_515_);
if (v___x_526_ == 0)
{
goto v___jp_518_;
}
else
{
uint32_t v___x_527_; uint8_t v___x_528_; 
v___x_527_ = 122;
v___x_528_ = lean_uint32_dec_le(v_c_515_, v___x_527_);
if (v___x_528_ == 0)
{
goto v___jp_518_;
}
else
{
lean_dec_ref_known(v_it_x27_517_, 2);
goto v___jp_508_;
}
}
}
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_box(0);
v___x_534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_534_, 0, v___y_507_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
return v___x_534_;
}
v___jp_508_:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_510_, 0, v___y_507_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2___boxed(lean_object* v___x_535_, lean_object* v___x_536_, lean_object* v___y_537_){
_start:
{
uint32_t v___x_11941__boxed_538_; uint32_t v___x_11942__boxed_539_; lean_object* v_res_540_; 
v___x_11941__boxed_538_ = lean_unbox_uint32(v___x_535_);
lean_dec(v___x_535_);
v___x_11942__boxed_539_ = lean_unbox_uint32(v___x_536_);
lean_dec(v___x_536_);
v_res_540_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(v___x_11941__boxed_538_, v___x_11942__boxed_539_, v___y_537_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(uint32_t v___y_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_543_ = lean_string_push(v___x_542_, v___y_541_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3___boxed(lean_object* v___y_545_){
_start:
{
uint32_t v___y_11998__boxed_546_; lean_object* v_res_547_; 
v___y_11998__boxed_546_ = lean_unbox_uint32(v___y_545_);
lean_dec(v___y_545_);
v_res_547_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(v___y_11998__boxed_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4(lean_object* v___y_548_){
_start:
{
lean_object* v_fst_549_; lean_object* v_snd_550_; lean_object* v___x_551_; uint8_t v_decide_552_; 
v_fst_549_ = lean_ctor_get(v___y_548_, 0);
v_snd_550_ = lean_ctor_get(v___y_548_, 1);
v___x_551_ = lean_string_utf8_byte_size(v_fst_549_);
v_decide_552_ = lean_nat_dec_eq(v_snd_550_, v___x_551_);
if (v_decide_552_ == 0)
{
lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_563_; 
lean_inc(v_snd_550_);
lean_inc(v_fst_549_);
v_isSharedCheck_563_ = !lean_is_exclusive(v___y_548_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; lean_object* v_unused_565_; 
v_unused_564_ = lean_ctor_get(v___y_548_, 1);
lean_dec(v_unused_564_);
v_unused_565_ = lean_ctor_get(v___y_548_, 0);
lean_dec(v_unused_565_);
v___x_554_ = v___y_548_;
v_isShared_555_ = v_isSharedCheck_563_;
goto v_resetjp_553_;
}
else
{
lean_dec(v___y_548_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_563_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
uint32_t v_c_556_; lean_object* v___x_557_; lean_object* v_it_x27_559_; 
v_c_556_ = lean_string_utf8_get_fast(v_fst_549_, v_snd_550_);
v___x_557_ = lean_string_utf8_next_fast(v_fst_549_, v_snd_550_);
lean_dec(v_snd_550_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v___x_557_);
v_it_x27_559_ = v___x_554_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_fst_549_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_557_);
v_it_x27_559_ = v_reuseFailAlloc_562_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_box_uint32(v_c_556_);
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v_it_x27_559_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
return v___x_561_;
}
}
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_box(0);
v___x_567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_567_, 0, v___y_548_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
return v___x_567_;
}
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_568_; lean_object* v___x_569_; 
v___x_568_ = 34;
v___x_569_ = lean_box_uint32(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0(void){
_start:
{
lean_object* v___x_570_; lean_object* v___f_571_; 
v___x_570_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0___boxed__const__1;
v___f_571_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___boxed), 2, 1);
lean_closure_set(v___f_571_, 0, v___x_570_);
return v___f_571_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_572_; lean_object* v___x_573_; 
v___x_572_ = 39;
v___x_573_ = lean_box_uint32(v___x_572_);
return v___x_573_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1(void){
_start:
{
lean_object* v___x_574_; lean_object* v___f_575_; 
v___x_574_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1___boxed__const__1;
v___f_575_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___boxed), 2, 1);
lean_closure_set(v___f_575_, 0, v___x_574_);
return v___f_575_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___f_578_; 
v___x_576_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1___boxed__const__1;
v___x_577_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0___boxed__const__1;
v___f_578_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2___boxed), 3, 2);
lean_closure_set(v___f_578_, 0, v___x_576_);
lean_closure_set(v___f_578_, 1, v___x_577_);
return v___f_578_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart(lean_object* v_a_584_){
_start:
{
lean_object* v___x_585_; 
lean_inc_ref(v_a_584_);
v___x_585_ = l_Std_Time_parseModifier(v_a_584_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_pos_586_; lean_object* v_res_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_595_; 
lean_dec_ref(v_a_584_);
v_pos_586_ = lean_ctor_get(v___x_585_, 0);
v_res_587_ = lean_ctor_get(v___x_585_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_595_ == 0)
{
v___x_589_ = v___x_585_;
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_res_587_);
lean_inc(v_pos_586_);
lean_dec(v___x_585_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_591_, 0, v_res_587_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 1, v___x_591_);
v___x_593_ = v___x_589_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_pos_586_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
else
{
lean_object* v_pos_596_; lean_object* v_err_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_654_; 
v_pos_596_ = lean_ctor_get(v___x_585_, 0);
v_err_597_ = lean_ctor_get(v___x_585_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_654_ == 0)
{
v___x_599_ = v___x_585_;
v_isShared_600_ = v_isSharedCheck_654_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_err_597_);
lean_inc(v_pos_596_);
lean_dec(v___x_585_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_654_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v_snd_601_; lean_object* v_fst_602_; lean_object* v_snd_603_; uint8_t v_decide_604_; 
v_snd_601_ = lean_ctor_get(v_a_584_, 1);
lean_inc(v_snd_601_);
lean_dec_ref(v_a_584_);
v_fst_602_ = lean_ctor_get(v_pos_596_, 0);
v_snd_603_ = lean_ctor_get(v_pos_596_, 1);
v_decide_604_ = lean_nat_dec_eq(v_snd_601_, v_snd_603_);
lean_dec(v_snd_601_);
if (v_decide_604_ == 0)
{
lean_object* v___x_606_; 
if (v_isShared_600_ == 0)
{
v___x_606_ = v___x_599_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_pos_596_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_err_597_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
else
{
lean_object* v___f_608_; lean_object* v___y_610_; lean_object* v_pos_611_; lean_object* v_snd_612_; lean_object* v___x_626_; uint8_t v_decide_627_; 
lean_inc(v_snd_603_);
lean_dec(v_err_597_);
v___f_608_ = ((lean_object*)(l_Std_Time_instCoeStringFormatPart___closed__0));
v___x_626_ = lean_string_utf8_byte_size(v_fst_602_);
v_decide_627_ = lean_nat_dec_eq(v_snd_603_, v___x_626_);
if (v_decide_627_ == 0)
{
uint32_t v___x_628_; uint32_t v_c_629_; uint8_t v___x_630_; 
v___x_628_ = 92;
v_c_629_ = lean_string_utf8_get_fast(v_fst_602_, v_snd_603_);
v___x_630_ = lean_uint32_dec_eq(v_c_629_, v___x_628_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_631_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__4));
lean_inc(v_pos_596_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 1, v___x_631_);
v___x_633_ = v___x_599_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_pos_596_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_inc(v_snd_603_);
v___y_610_ = v___x_633_;
v_pos_611_ = v_pos_596_;
v_snd_612_ = v_snd_603_;
goto v___jp_609_;
}
}
else
{
lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_647_; 
lean_inc(v_fst_602_);
lean_del_object(v___x_599_);
v_isSharedCheck_647_ = !lean_is_exclusive(v_pos_596_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; lean_object* v_unused_649_; 
v_unused_648_ = lean_ctor_get(v_pos_596_, 1);
lean_dec(v_unused_648_);
v_unused_649_ = lean_ctor_get(v_pos_596_, 0);
lean_dec(v_unused_649_);
v___x_636_ = v_pos_596_;
v_isShared_637_ = v_isSharedCheck_647_;
goto v_resetjp_635_;
}
else
{
lean_dec(v_pos_596_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_647_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___f_638_; lean_object* v___f_639_; lean_object* v___x_640_; lean_object* v_it_x27_642_; 
v___f_638_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__5));
v___f_639_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__6));
v___x_640_ = lean_string_utf8_next_fast(v_fst_602_, v_snd_603_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_640_);
v_it_x27_642_ = v___x_636_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_fst_602_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v___x_640_);
v_it_x27_642_ = v_reuseFailAlloc_646_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_643_; 
v___x_643_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_639_, v___f_638_, v_it_x27_642_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_dec(v_snd_603_);
return v___x_643_;
}
else
{
lean_object* v_pos_644_; lean_object* v_snd_645_; 
v_pos_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_pos_644_);
v_snd_645_ = lean_ctor_get(v_pos_644_, 1);
lean_inc(v_snd_645_);
v___y_610_ = v___x_643_;
v_pos_611_ = v_pos_644_;
v_snd_612_ = v_snd_645_;
goto v___jp_609_;
}
}
}
}
}
else
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = lean_box(0);
lean_inc(v_pos_596_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 1, v___x_650_);
v___x_652_ = v___x_599_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_pos_596_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_inc(v_snd_603_);
v___y_610_ = v___x_652_;
v_pos_611_ = v_pos_596_;
v_snd_612_ = v_snd_603_;
goto v___jp_609_;
}
}
v___jp_609_:
{
uint8_t v_decide_613_; 
v_decide_613_ = lean_nat_dec_eq(v_snd_603_, v_snd_612_);
lean_dec(v_snd_603_);
if (v_decide_613_ == 0)
{
lean_dec(v_snd_612_);
lean_dec_ref(v_pos_611_);
return v___y_610_;
}
else
{
lean_object* v___f_614_; lean_object* v___x_615_; 
lean_dec_ref(v___y_610_);
v___f_614_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0);
v___x_615_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_614_, v___f_608_, v_pos_611_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_dec(v_snd_612_);
return v___x_615_;
}
else
{
lean_object* v_pos_616_; lean_object* v_snd_617_; uint8_t v_decide_618_; 
v_pos_616_ = lean_ctor_get(v___x_615_, 0);
v_snd_617_ = lean_ctor_get(v_pos_616_, 1);
v_decide_618_ = lean_nat_dec_eq(v_snd_612_, v_snd_617_);
lean_dec(v_snd_612_);
if (v_decide_618_ == 0)
{
return v___x_615_;
}
else
{
lean_object* v___f_619_; lean_object* v___x_620_; 
lean_inc(v_snd_617_);
lean_inc(v_pos_616_);
lean_dec_ref_known(v___x_615_, 2);
v___f_619_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1);
v___x_620_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_619_, v___f_608_, v_pos_616_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_dec(v_snd_617_);
return v___x_620_;
}
else
{
lean_object* v_pos_621_; lean_object* v_snd_622_; uint8_t v_decide_623_; 
v_pos_621_ = lean_ctor_get(v___x_620_, 0);
v_snd_622_ = lean_ctor_get(v_pos_621_, 1);
v_decide_623_ = lean_nat_dec_eq(v_snd_617_, v_snd_622_);
lean_dec(v_snd_617_);
if (v_decide_623_ == 0)
{
return v___x_620_;
}
else
{
lean_object* v___f_624_; lean_object* v___x_625_; 
lean_inc(v_pos_621_);
lean_dec_ref_known(v___x_620_, 2);
v___f_624_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2);
v___x_625_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_624_, v___f_608_, v_pos_621_);
return v___x_625_;
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_specParser_spec__0(lean_object* v_acc_655_, lean_object* v_a_656_){
_start:
{
lean_object* v___x_657_; 
lean_inc_ref(v_a_656_);
v___x_657_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart(v_a_656_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_pos_658_; lean_object* v_res_659_; lean_object* v___x_660_; 
lean_dec_ref(v_a_656_);
v_pos_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_pos_658_);
v_res_659_ = lean_ctor_get(v___x_657_, 1);
lean_inc(v_res_659_);
lean_dec_ref_known(v___x_657_, 2);
v___x_660_ = lean_array_push(v_acc_655_, v_res_659_);
v_acc_655_ = v___x_660_;
v_a_656_ = v_pos_658_;
goto _start;
}
else
{
lean_object* v_pos_662_; lean_object* v_err_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_676_; 
v_pos_662_ = lean_ctor_get(v___x_657_, 0);
v_err_663_ = lean_ctor_get(v___x_657_, 1);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_676_ == 0)
{
v___x_665_ = v___x_657_;
v_isShared_666_ = v_isSharedCheck_676_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_err_663_);
lean_inc(v_pos_662_);
lean_dec(v___x_657_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_676_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v_snd_667_; lean_object* v_snd_668_; uint8_t v_decide_669_; 
v_snd_667_ = lean_ctor_get(v_a_656_, 1);
lean_inc(v_snd_667_);
lean_dec_ref(v_a_656_);
v_snd_668_ = lean_ctor_get(v_pos_662_, 1);
v_decide_669_ = lean_nat_dec_eq(v_snd_667_, v_snd_668_);
lean_dec(v_snd_667_);
if (v_decide_669_ == 0)
{
lean_object* v___x_671_; 
lean_dec_ref(v_acc_655_);
if (v_isShared_666_ == 0)
{
v___x_671_ = v___x_665_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_pos_662_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_err_663_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
else
{
lean_object* v___x_674_; 
lean_dec(v_err_663_);
if (v_isShared_666_ == 0)
{
lean_ctor_set_tag(v___x_665_, 0);
lean_ctor_set(v___x_665_, 1, v_acc_655_);
v___x_674_ = v___x_665_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_pos_662_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_acc_655_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParser(lean_object* v_a_682_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__0));
v___x_684_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_specParser_spec__0(v___x_683_, v_a_682_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_pos_685_; lean_object* v_res_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_702_; 
v_pos_685_ = lean_ctor_get(v___x_684_, 0);
v_res_686_ = lean_ctor_get(v___x_684_, 1);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_702_ == 0)
{
v___x_688_ = v___x_684_;
v_isShared_689_ = v_isSharedCheck_702_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_res_686_);
lean_inc(v_pos_685_);
lean_dec(v___x_684_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_702_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_fst_690_; lean_object* v_snd_691_; lean_object* v___x_692_; uint8_t v_decide_693_; 
v_fst_690_ = lean_ctor_get(v_pos_685_, 0);
v_snd_691_ = lean_ctor_get(v_pos_685_, 1);
v___x_692_ = lean_string_utf8_byte_size(v_fst_690_);
v_decide_693_ = lean_nat_dec_eq(v_snd_691_, v___x_692_);
if (v_decide_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_696_; 
lean_dec(v_res_686_);
v___x_694_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_689_ == 0)
{
lean_ctor_set_tag(v___x_688_, 1);
lean_ctor_set(v___x_688_, 1, v___x_694_);
v___x_696_ = v___x_688_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_pos_685_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
else
{
lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_698_ = lean_array_to_list(v_res_686_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v___x_698_);
v___x_700_ = v___x_688_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_pos_685_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
else
{
lean_object* v_pos_703_; lean_object* v_err_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
v_pos_703_ = lean_ctor_get(v___x_684_, 0);
v_err_704_ = lean_ctor_get(v___x_684_, 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_684_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_err_704_);
lean_inc(v_pos_703_);
lean_dec(v___x_684_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_pos_703_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_err_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(uint32_t v_a_712_, lean_object* v_x_713_, lean_object* v_x_714_){
_start:
{
lean_object* v_zero_715_; uint8_t v_isZero_716_; 
v_zero_715_ = lean_unsigned_to_nat(0u);
v_isZero_716_ = lean_nat_dec_eq(v_x_713_, v_zero_715_);
if (v_isZero_716_ == 1)
{
lean_dec(v_x_713_);
return v_x_714_;
}
else
{
lean_object* v_one_717_; lean_object* v_n_718_; lean_object* v___x_719_; 
v_one_717_ = lean_unsigned_to_nat(1u);
v_n_718_ = lean_nat_sub(v_x_713_, v_one_717_);
lean_dec(v_x_713_);
v___x_719_ = lean_string_push(v_x_714_, v_a_712_);
v_x_713_ = v_n_718_;
v_x_714_ = v___x_719_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1___boxed(lean_object* v_a_721_, lean_object* v_x_722_, lean_object* v_x_723_){
_start:
{
uint32_t v_a_boxed_724_; lean_object* v_res_725_; 
v_a_boxed_724_ = lean_unbox_uint32(v_a_721_);
lean_dec(v_a_721_);
v_res_725_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_boxed_724_, v_x_722_, v_x_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(lean_object* v___x_726_, lean_object* v_s_727_, lean_object* v_a_728_, lean_object* v_b_729_){
_start:
{
uint8_t v_decide_730_; 
v_decide_730_ = lean_nat_dec_eq(v_a_728_, v___x_726_);
if (v_decide_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_731_ = lean_string_utf8_next_fast(v_s_727_, v_a_728_);
lean_dec(v_a_728_);
v___x_732_ = lean_unsigned_to_nat(1u);
v___x_733_ = lean_nat_add(v_b_729_, v___x_732_);
lean_dec(v_b_729_);
v_a_728_ = v___x_731_;
v_b_729_ = v___x_733_;
goto _start;
}
else
{
lean_dec(v_a_728_);
return v_b_729_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg___boxed(lean_object* v___x_735_, lean_object* v_s_736_, lean_object* v_a_737_, lean_object* v_b_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_735_, v_s_736_, v_a_737_, v_b_738_);
lean_dec_ref(v_s_736_);
lean_dec(v___x_735_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(lean_object* v_n_740_, uint32_t v_a_741_, lean_object* v_s_742_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_743_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_string_utf8_byte_size(v_s_742_);
v___x_746_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_745_, v_s_742_, v___x_744_, v___x_744_);
v___x_747_ = lean_nat_sub(v_n_740_, v___x_746_);
lean_dec(v___x_746_);
v___x_748_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_741_, v___x_747_, v___x_743_);
v___x_749_ = lean_string_append(v___x_748_, v_s_742_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii___boxed(lean_object* v_n_750_, lean_object* v_a_751_, lean_object* v_s_752_){
_start:
{
uint32_t v_a_boxed_753_; lean_object* v_res_754_; 
v_a_boxed_753_ = lean_unbox_uint32(v_a_751_);
lean_dec(v_a_751_);
v_res_754_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v_n_750_, v_a_boxed_753_, v_s_752_);
lean_dec_ref(v_s_752_);
lean_dec(v_n_750_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0(lean_object* v___x_755_, lean_object* v___x_756_, lean_object* v_s_757_, lean_object* v_inst_758_, lean_object* v_R_759_, lean_object* v_a_760_, lean_object* v_b_761_, lean_object* v_c_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_755_, v_s_757_, v_a_760_, v_b_761_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___boxed(lean_object* v___x_764_, lean_object* v___x_765_, lean_object* v_s_766_, lean_object* v_inst_767_, lean_object* v_R_768_, lean_object* v_a_769_, lean_object* v_b_770_, lean_object* v_c_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0(v___x_764_, v___x_765_, v_s_766_, v_inst_767_, v_R_768_, v_a_769_, v_b_770_, v_c_771_);
lean_dec_ref(v_s_766_);
lean_dec_ref(v___x_765_);
lean_dec(v___x_764_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(lean_object* v_n_773_, uint32_t v_a_774_, lean_object* v_s_775_){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_776_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = lean_string_utf8_byte_size(v_s_775_);
v___x_779_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_778_, v_s_775_, v___x_777_, v___x_777_);
v___x_780_ = lean_nat_sub(v_n_773_, v___x_779_);
lean_dec(v___x_779_);
v___x_781_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_774_, v___x_780_, v___x_776_);
v___x_782_ = lean_string_append(v_s_775_, v___x_781_);
lean_dec_ref(v___x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii___boxed(lean_object* v_n_783_, lean_object* v_a_784_, lean_object* v_s_785_){
_start:
{
uint32_t v_a_boxed_786_; lean_object* v_res_787_; 
v_a_boxed_786_ = lean_unbox_uint32(v_a_784_);
lean_dec(v_a_784_);
v_res_787_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_n_783_, v_a_boxed_786_, v_s_785_);
lean_dec(v_n_783_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_pad_spec__0(lean_object* v_x_788_, lean_object* v_x_789_){
_start:
{
lean_object* v_zero_790_; uint8_t v_isZero_791_; 
v_zero_790_ = lean_unsigned_to_nat(0u);
v_isZero_791_ = lean_nat_dec_eq(v_x_788_, v_zero_790_);
if (v_isZero_791_ == 1)
{
lean_dec(v_x_788_);
return v_x_789_;
}
else
{
uint32_t v___x_792_; lean_object* v_one_793_; lean_object* v_n_794_; lean_object* v___x_795_; 
v___x_792_ = 48;
v_one_793_ = lean_unsigned_to_nat(1u);
v_n_794_ = lean_nat_sub(v_x_788_, v_one_793_);
lean_dec(v_x_788_);
v___x_795_ = lean_string_push(v_x_789_, v___x_792_);
v_x_788_ = v_n_794_;
v_x_789_ = v___x_795_;
goto _start;
}
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = lean_nat_to_int(v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad(lean_object* v_size_800_, lean_object* v_n_801_){
_start:
{
lean_object* v___x_802_; lean_object* v_digits_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v_padded_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_802_ = lean_nat_abs(v_n_801_);
v_digits_803_ = l_Nat_reprFast(v___x_802_);
v___x_804_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_805_ = lean_string_length(v_digits_803_);
v___x_806_ = lean_nat_sub(v_size_800_, v___x_805_);
v___x_807_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_pad_spec__0(v___x_806_, v___x_804_);
v_padded_808_ = lean_string_append(v___x_807_, v_digits_803_);
lean_dec_ref(v_digits_803_);
v___x_809_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_810_ = lean_int_dec_lt(v_n_801_, v___x_809_);
if (v___x_810_ == 0)
{
return v_padded_808_;
}
else
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_812_ = lean_string_append(v___x_811_, v_padded_808_);
lean_dec_ref(v_padded_808_);
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad___boxed(lean_object* v_size_813_, lean_object* v_n_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_size_813_, v_n_814_);
lean_dec(v_n_814_);
lean_dec(v_size_813_);
return v_res_815_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear___closed__0(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_unsigned_to_nat(9999u);
v___x_817_ = lean_nat_to_int(v___x_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear(lean_object* v_n_819_){
_start:
{
lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_820_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear___closed__0);
v___x_821_ = lean_int_dec_lt(v___x_820_, v_n_819_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_unsigned_to_nat(4u);
v___x_823_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_822_, v_n_819_);
return v___x_823_;
}
else
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_824_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear___closed__1));
v___x_825_ = l_Int_repr(v_n_819_);
v___x_826_ = lean_string_append(v___x_824_, v___x_825_);
lean_dec_ref(v___x_825_);
return v___x_826_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear___boxed(lean_object* v_n_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear(v_n_827_);
lean_dec(v_n_827_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthNames(lean_object* v_symbols_829_, uint8_t v_x_830_){
_start:
{
switch(v_x_830_)
{
case 1:
{
lean_object* v_monthLong_831_; 
v_monthLong_831_ = lean_ctor_get(v_symbols_829_, 0);
lean_inc_ref(v_monthLong_831_);
return v_monthLong_831_;
}
case 2:
{
lean_object* v_monthNarrow_832_; 
v_monthNarrow_832_ = lean_ctor_get(v_symbols_829_, 2);
lean_inc_ref(v_monthNarrow_832_);
return v_monthNarrow_832_;
}
default: 
{
lean_object* v_monthShort_833_; 
v_monthShort_833_ = lean_ctor_get(v_symbols_829_, 1);
lean_inc_ref(v_monthShort_833_);
return v_monthShort_833_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthNames___boxed(lean_object* v_symbols_834_, lean_object* v_x_835_){
_start:
{
uint8_t v_x_30__boxed_836_; lean_object* v_res_837_; 
v_x_30__boxed_836_ = lean_unbox(v_x_835_);
v_res_837_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthNames(v_symbols_834_, v_x_30__boxed_836_);
lean_dec_ref(v_symbols_834_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayNames(lean_object* v_symbols_838_, uint8_t v_x_839_){
_start:
{
switch(v_x_839_)
{
case 0:
{
lean_object* v_weekdayShort_840_; 
v_weekdayShort_840_ = lean_ctor_get(v_symbols_838_, 4);
lean_inc_ref(v_weekdayShort_840_);
return v_weekdayShort_840_;
}
case 1:
{
lean_object* v_weekdayLong_841_; 
v_weekdayLong_841_ = lean_ctor_get(v_symbols_838_, 3);
lean_inc_ref(v_weekdayLong_841_);
return v_weekdayLong_841_;
}
case 2:
{
lean_object* v_weekdayNarrow_842_; 
v_weekdayNarrow_842_ = lean_ctor_get(v_symbols_838_, 5);
lean_inc_ref(v_weekdayNarrow_842_);
return v_weekdayNarrow_842_;
}
default: 
{
lean_object* v_weekdayTwoLetter_843_; 
v_weekdayTwoLetter_843_ = lean_ctor_get(v_symbols_838_, 6);
lean_inc_ref(v_weekdayTwoLetter_843_);
return v_weekdayTwoLetter_843_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayNames___boxed(lean_object* v_symbols_844_, lean_object* v_x_845_){
_start:
{
uint8_t v_x_32__boxed_846_; lean_object* v_res_847_; 
v_x_32__boxed_846_ = lean_unbox(v_x_845_);
v_res_847_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayNames(v_symbols_844_, v_x_32__boxed_846_);
lean_dec_ref(v_symbols_844_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraNames(lean_object* v_symbols_848_, uint8_t v_x_849_){
_start:
{
switch(v_x_849_)
{
case 1:
{
lean_object* v_eraLong_850_; 
v_eraLong_850_ = lean_ctor_get(v_symbols_848_, 8);
lean_inc_ref(v_eraLong_850_);
return v_eraLong_850_;
}
case 2:
{
lean_object* v_eraNarrow_851_; 
v_eraNarrow_851_ = lean_ctor_get(v_symbols_848_, 9);
lean_inc_ref(v_eraNarrow_851_);
return v_eraNarrow_851_;
}
default: 
{
lean_object* v_eraShort_852_; 
v_eraShort_852_ = lean_ctor_get(v_symbols_848_, 7);
lean_inc_ref(v_eraShort_852_);
return v_eraShort_852_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraNames___boxed(lean_object* v_symbols_853_, lean_object* v_x_854_){
_start:
{
uint8_t v_x_30__boxed_855_; lean_object* v_res_856_; 
v_x_30__boxed_855_ = lean_unbox(v_x_854_);
v_res_856_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraNames(v_symbols_853_, v_x_30__boxed_855_);
lean_dec_ref(v_symbols_853_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_quarterNames(lean_object* v_symbols_857_, uint8_t v_x_858_){
_start:
{
switch(v_x_858_)
{
case 0:
{
lean_object* v_quarterShort_859_; 
v_quarterShort_859_ = lean_ctor_get(v_symbols_857_, 10);
lean_inc_ref(v_quarterShort_859_);
return v_quarterShort_859_;
}
case 1:
{
lean_object* v_quarterLong_860_; 
v_quarterLong_860_ = lean_ctor_get(v_symbols_857_, 11);
lean_inc_ref(v_quarterLong_860_);
return v_quarterLong_860_;
}
default: 
{
lean_object* v_quarterNarrow_861_; 
v_quarterNarrow_861_ = lean_ctor_get(v_symbols_857_, 12);
lean_inc_ref(v_quarterNarrow_861_);
return v_quarterNarrow_861_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_quarterNames___boxed(lean_object* v_symbols_862_, lean_object* v_x_863_){
_start:
{
uint8_t v_x_30__boxed_864_; lean_object* v_res_865_; 
v_x_30__boxed_864_ = lean_unbox(v_x_863_);
v_res_865_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterNames(v_symbols_862_, v_x_30__boxed_864_);
lean_dec_ref(v_symbols_862_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_markerNames(lean_object* v_symbols_866_, uint8_t v_x_867_){
_start:
{
switch(v_x_867_)
{
case 1:
{
lean_object* v_amLong_868_; lean_object* v_pmLong_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_amLong_868_ = lean_ctor_get(v_symbols_866_, 15);
lean_inc_ref(v_amLong_868_);
v_pmLong_869_ = lean_ctor_get(v_symbols_866_, 16);
lean_inc_ref(v_pmLong_869_);
lean_dec_ref(v_symbols_866_);
v___x_870_ = lean_unsigned_to_nat(2u);
v___x_871_ = lean_mk_empty_array_with_capacity(v___x_870_);
v___x_872_ = lean_array_push(v___x_871_, v_amLong_868_);
v___x_873_ = lean_array_push(v___x_872_, v_pmLong_869_);
return v___x_873_;
}
case 2:
{
lean_object* v_amNarrow_874_; lean_object* v_pmNarrow_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_amNarrow_874_ = lean_ctor_get(v_symbols_866_, 17);
lean_inc_ref(v_amNarrow_874_);
v_pmNarrow_875_ = lean_ctor_get(v_symbols_866_, 18);
lean_inc_ref(v_pmNarrow_875_);
lean_dec_ref(v_symbols_866_);
v___x_876_ = lean_unsigned_to_nat(2u);
v___x_877_ = lean_mk_empty_array_with_capacity(v___x_876_);
v___x_878_ = lean_array_push(v___x_877_, v_amNarrow_874_);
v___x_879_ = lean_array_push(v___x_878_, v_pmNarrow_875_);
return v___x_879_;
}
default: 
{
lean_object* v_amShort_880_; lean_object* v_pmShort_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_amShort_880_ = lean_ctor_get(v_symbols_866_, 13);
lean_inc_ref(v_amShort_880_);
v_pmShort_881_ = lean_ctor_get(v_symbols_866_, 14);
lean_inc_ref(v_pmShort_881_);
lean_dec_ref(v_symbols_866_);
v___x_882_ = lean_unsigned_to_nat(2u);
v___x_883_ = lean_mk_empty_array_with_capacity(v___x_882_);
v___x_884_ = lean_array_push(v___x_883_, v_amShort_880_);
v___x_885_ = lean_array_push(v___x_884_, v_pmShort_881_);
return v___x_885_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_markerNames___boxed(lean_object* v_symbols_886_, lean_object* v_x_887_){
_start:
{
uint8_t v_x_95__boxed_888_; lean_object* v_res_889_; 
v_x_95__boxed_888_ = lean_unbox(v_x_887_);
v_res_889_ = l___private_Std_Time_Format_Basic_0__Std_Time_markerNames(v_symbols_886_, v_x_95__boxed_888_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dayPeriodNames(lean_object* v_symbols_890_, uint8_t v_text_891_){
_start:
{
lean_object* v___y_893_; 
switch(v_text_891_)
{
case 1:
{
lean_object* v_dayPeriodLong_904_; 
v_dayPeriodLong_904_ = lean_ctor_get(v_symbols_890_, 20);
lean_inc_ref(v_dayPeriodLong_904_);
lean_dec_ref(v_symbols_890_);
v___y_893_ = v_dayPeriodLong_904_;
goto v___jp_892_;
}
case 2:
{
lean_object* v_dayPeriodNarrow_905_; 
v_dayPeriodNarrow_905_ = lean_ctor_get(v_symbols_890_, 21);
lean_inc_ref(v_dayPeriodNarrow_905_);
lean_dec_ref(v_symbols_890_);
v___y_893_ = v_dayPeriodNarrow_905_;
goto v___jp_892_;
}
default: 
{
lean_object* v_dayPeriodShort_906_; 
v_dayPeriodShort_906_ = lean_ctor_get(v_symbols_890_, 19);
lean_inc_ref(v_dayPeriodShort_906_);
lean_dec_ref(v_symbols_890_);
v___y_893_ = v_dayPeriodShort_906_;
goto v___jp_892_;
}
}
v___jp_892_:
{
lean_object* v_am_894_; lean_object* v_pm_895_; lean_object* v_noon_896_; lean_object* v_midnight_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_am_894_ = lean_ctor_get(v___y_893_, 0);
lean_inc_ref(v_am_894_);
v_pm_895_ = lean_ctor_get(v___y_893_, 1);
lean_inc_ref(v_pm_895_);
v_noon_896_ = lean_ctor_get(v___y_893_, 2);
lean_inc_ref(v_noon_896_);
v_midnight_897_ = lean_ctor_get(v___y_893_, 3);
lean_inc_ref(v_midnight_897_);
lean_dec_ref(v___y_893_);
v___x_898_ = lean_unsigned_to_nat(4u);
v___x_899_ = lean_mk_empty_array_with_capacity(v___x_898_);
v___x_900_ = lean_array_push(v___x_899_, v_midnight_897_);
v___x_901_ = lean_array_push(v___x_900_, v_noon_896_);
v___x_902_ = lean_array_push(v___x_901_, v_am_894_);
v___x_903_ = lean_array_push(v___x_902_, v_pm_895_);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dayPeriodNames___boxed(lean_object* v_symbols_907_, lean_object* v_text_908_){
_start:
{
uint8_t v_text_boxed_909_; lean_object* v_res_910_; 
v_text_boxed_909_ = lean_unbox(v_text_908_);
v_res_910_ = l___private_Std_Time_Format_Basic_0__Std_Time_dayPeriodNames(v_symbols_907_, v_text_boxed_909_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodNames(lean_object* v_symbols_911_, uint8_t v_x_912_){
_start:
{
switch(v_x_912_)
{
case 1:
{
lean_object* v_extendedDayPeriodLong_913_; 
v_extendedDayPeriodLong_913_ = lean_ctor_get(v_symbols_911_, 23);
lean_inc_ref(v_extendedDayPeriodLong_913_);
return v_extendedDayPeriodLong_913_;
}
case 2:
{
lean_object* v_extendedDayPeriodNarrow_914_; 
v_extendedDayPeriodNarrow_914_ = lean_ctor_get(v_symbols_911_, 24);
lean_inc_ref(v_extendedDayPeriodNarrow_914_);
return v_extendedDayPeriodNarrow_914_;
}
default: 
{
lean_object* v_extendedDayPeriodShort_915_; 
v_extendedDayPeriodShort_915_ = lean_ctor_get(v_symbols_911_, 22);
lean_inc_ref(v_extendedDayPeriodShort_915_);
return v_extendedDayPeriodShort_915_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodNames___boxed(lean_object* v_symbols_916_, lean_object* v_x_917_){
_start:
{
uint8_t v_x_30__boxed_918_; lean_object* v_res_919_; 
v_x_30__boxed_918_ = lean_unbox(v_x_917_);
v_res_919_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodNames(v_symbols_916_, v_x_30__boxed_918_);
lean_dec_ref(v_symbols_916_);
return v_res_919_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___closed__0(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_921_ = lean_int_neg(v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex(lean_object* v_month_922_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_923_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___closed__0);
v___x_924_ = lean_int_add(v_month_922_, v___x_923_);
v___x_925_ = l_Int_toNat(v___x_924_);
lean_dec(v___x_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___boxed(lean_object* v_month_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex(v_month_926_);
lean_dec(v_month_926_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthOfIndex_spec__0(lean_object* v_a_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = lean_nat_to_int(v_a_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthOfIndex(lean_object* v_i_930_){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = lean_nat_to_int(v_i_930_);
v___x_932_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_933_ = lean_int_add(v___x_931_, v___x_932_);
lean_dec(v___x_931_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayIndex(uint8_t v_weekday_934_){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_935_ = l_Std_Time_Weekday_toOrdinal(v_weekday_934_);
v___x_936_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___closed__0);
v___x_937_ = lean_int_add(v___x_935_, v___x_936_);
lean_dec(v___x_935_);
v___x_938_ = l_Int_toNat(v___x_937_);
lean_dec(v___x_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayIndex___boxed(lean_object* v_weekday_939_){
_start:
{
uint8_t v_weekday_boxed_940_; lean_object* v_res_941_; 
v_weekday_boxed_940_ = lean_unbox(v_weekday_939_);
v_res_941_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayIndex(v_weekday_boxed_940_);
return v_res_941_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(lean_object* v_i_942_){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_943_ = lean_nat_to_int(v_i_942_);
v___x_944_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_945_ = lean_int_add(v___x_943_, v___x_944_);
lean_dec(v___x_943_);
v___x_946_ = l_Std_Time_Weekday_ofOrdinal(v___x_945_);
lean_dec(v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex___boxed(lean_object* v_i_947_){
_start:
{
uint8_t v_res_948_; lean_object* v_r_949_; 
v_res_948_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(v_i_947_);
v_r_949_ = lean_box(v_res_948_);
return v_r_949_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(uint8_t v_x_950_){
_start:
{
if (v_x_950_ == 0)
{
lean_object* v___x_951_; 
v___x_951_ = lean_unsigned_to_nat(0u);
return v___x_951_;
}
else
{
lean_object* v___x_952_; 
v___x_952_ = lean_unsigned_to_nat(1u);
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___boxed(lean_object* v_x_953_){
_start:
{
uint8_t v_x_40__boxed_954_; lean_object* v_res_955_; 
v_x_40__boxed_954_ = lean_unbox(v_x_953_);
v_res_955_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_x_40__boxed_954_);
return v_res_955_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(lean_object* v_i_956_){
_start:
{
lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_957_ = lean_unsigned_to_nat(0u);
v___x_958_ = lean_nat_dec_eq(v_i_956_, v___x_957_);
if (v___x_958_ == 0)
{
uint8_t v___x_959_; 
v___x_959_ = 1;
return v___x_959_;
}
else
{
uint8_t v___x_960_; 
v___x_960_ = 0;
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex___boxed(lean_object* v_i_961_){
_start:
{
uint8_t v_res_962_; lean_object* v_r_963_; 
v_res_962_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(v_i_961_);
lean_dec(v_i_961_);
v_r_963_ = lean_box(v_res_962_);
return v_r_963_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_quarterIndex(lean_object* v_quarter_964_){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_965_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___closed__0);
v___x_966_ = lean_int_add(v_quarter_964_, v___x_965_);
v___x_967_ = l_Int_toNat(v___x_966_);
lean_dec(v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_quarterIndex___boxed(lean_object* v_quarter_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterIndex(v_quarter_968_);
lean_dec(v_quarter_968_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_quarterOfIndex(lean_object* v_i_970_){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_971_ = lean_nat_to_int(v_i_970_);
v___x_972_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_973_ = lean_int_add(v___x_971_, v___x_972_);
lean_dec(v___x_971_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_markerIndex(uint8_t v_x_974_){
_start:
{
if (v_x_974_ == 0)
{
lean_object* v___x_975_; 
v___x_975_ = lean_unsigned_to_nat(0u);
return v___x_975_;
}
else
{
lean_object* v___x_976_; 
v___x_976_ = lean_unsigned_to_nat(1u);
return v___x_976_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_markerIndex___boxed(lean_object* v_x_977_){
_start:
{
uint8_t v_x_40__boxed_978_; lean_object* v_res_979_; 
v_x_40__boxed_978_ = lean_unbox(v_x_977_);
v_res_979_ = l___private_Std_Time_Format_Basic_0__Std_Time_markerIndex(v_x_40__boxed_978_);
return v_res_979_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_markerOfIndex(lean_object* v_i_980_){
_start:
{
lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = lean_nat_dec_eq(v_i_980_, v___x_981_);
if (v___x_982_ == 0)
{
uint8_t v___x_983_; 
v___x_983_ = 1;
return v___x_983_;
}
else
{
uint8_t v___x_984_; 
v___x_984_ = 0;
return v___x_984_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_markerOfIndex___boxed(lean_object* v_i_985_){
_start:
{
uint8_t v_res_986_; lean_object* v_r_987_; 
v_res_986_ = l___private_Std_Time_Format_Basic_0__Std_Time_markerOfIndex(v_i_985_);
lean_dec(v_i_985_);
v_r_987_ = lean_box(v_res_986_);
return v_r_987_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dayPeriodIndex(uint8_t v_x_988_){
_start:
{
switch(v_x_988_)
{
case 0:
{
lean_object* v___x_989_; 
v___x_989_ = lean_unsigned_to_nat(2u);
return v___x_989_;
}
case 1:
{
lean_object* v___x_990_; 
v___x_990_ = lean_unsigned_to_nat(3u);
return v___x_990_;
}
case 2:
{
lean_object* v___x_991_; 
v___x_991_ = lean_unsigned_to_nat(1u);
return v___x_991_;
}
default: 
{
lean_object* v___x_992_; 
v___x_992_ = lean_unsigned_to_nat(0u);
return v___x_992_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dayPeriodIndex___boxed(lean_object* v_x_993_){
_start:
{
uint8_t v_x_76__boxed_994_; lean_object* v_res_995_; 
v_x_76__boxed_994_ = lean_unbox(v_x_993_);
v_res_995_ = l___private_Std_Time_Format_Basic_0__Std_Time_dayPeriodIndex(v_x_76__boxed_994_);
return v_res_995_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_dayPeriodOfIndex(lean_object* v_x_996_){
_start:
{
lean_object* v___x_997_; uint8_t v___x_998_; 
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = lean_nat_dec_eq(v_x_996_, v___x_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_999_ = lean_unsigned_to_nat(1u);
v___x_1000_ = lean_nat_dec_eq(v_x_996_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = lean_unsigned_to_nat(2u);
v___x_1002_ = lean_nat_dec_eq(v_x_996_, v___x_1001_);
if (v___x_1002_ == 0)
{
uint8_t v___x_1003_; 
v___x_1003_ = 1;
return v___x_1003_;
}
else
{
uint8_t v___x_1004_; 
v___x_1004_ = 0;
return v___x_1004_;
}
}
else
{
uint8_t v___x_1005_; 
v___x_1005_ = 2;
return v___x_1005_;
}
}
else
{
uint8_t v___x_1006_; 
v___x_1006_ = 3;
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dayPeriodOfIndex___boxed(lean_object* v_x_1007_){
_start:
{
uint8_t v_res_1008_; lean_object* v_r_1009_; 
v_res_1008_ = l___private_Std_Time_Format_Basic_0__Std_Time_dayPeriodOfIndex(v_x_1007_);
lean_dec(v_x_1007_);
v_r_1009_ = lean_box(v_res_1008_);
return v_r_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(uint8_t v_x_1010_){
_start:
{
switch(v_x_1010_)
{
case 0:
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_unsigned_to_nat(0u);
return v___x_1011_;
}
case 1:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_unsigned_to_nat(1u);
return v___x_1012_;
}
case 2:
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_unsigned_to_nat(2u);
return v___x_1013_;
}
case 3:
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_unsigned_to_nat(3u);
return v___x_1014_;
}
case 4:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_unsigned_to_nat(4u);
return v___x_1015_;
}
default: 
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_unsigned_to_nat(5u);
return v___x_1016_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___boxed(lean_object* v_x_1017_){
_start:
{
uint8_t v_x_112__boxed_1018_; lean_object* v_res_1019_; 
v_x_112__boxed_1018_ = lean_unbox(v_x_1017_);
v_res_1019_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(v_x_112__boxed_1018_);
return v_res_1019_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodOfIndex(lean_object* v_x_1020_){
_start:
{
lean_object* v___x_1021_; uint8_t v___x_1022_; 
v___x_1021_ = lean_unsigned_to_nat(0u);
v___x_1022_ = lean_nat_dec_eq(v_x_1020_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1023_ = lean_unsigned_to_nat(1u);
v___x_1024_ = lean_nat_dec_eq(v_x_1020_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___x_1025_ = lean_unsigned_to_nat(2u);
v___x_1026_ = lean_nat_dec_eq(v_x_1020_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1027_ = lean_unsigned_to_nat(3u);
v___x_1028_ = lean_nat_dec_eq(v_x_1020_, v___x_1027_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1029_ = lean_unsigned_to_nat(4u);
v___x_1030_ = lean_nat_dec_eq(v_x_1020_, v___x_1029_);
if (v___x_1030_ == 0)
{
uint8_t v___x_1031_; 
v___x_1031_ = 5;
return v___x_1031_;
}
else
{
uint8_t v___x_1032_; 
v___x_1032_ = 4;
return v___x_1032_;
}
}
else
{
uint8_t v___x_1033_; 
v___x_1033_ = 3;
return v___x_1033_;
}
}
else
{
uint8_t v___x_1034_; 
v___x_1034_ = 2;
return v___x_1034_;
}
}
else
{
uint8_t v___x_1035_; 
v___x_1035_ = 1;
return v___x_1035_;
}
}
else
{
uint8_t v___x_1036_; 
v___x_1036_ = 0;
return v___x_1036_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodOfIndex___boxed(lean_object* v_x_1037_){
_start:
{
uint8_t v_res_1038_; lean_object* v_r_1039_; 
v_res_1038_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodOfIndex(v_x_1037_);
lean_dec(v_x_1037_);
v_r_1039_ = lean_box(v_res_1038_);
return v_r_1039_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dropSeconds___closed__0(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_unsigned_to_nat(60u);
v___x_1041_ = lean_nat_to_int(v___x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dropSeconds(lean_object* v_offset_1042_){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dropSeconds___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dropSeconds___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dropSeconds___closed__0);
v___x_1044_ = lean_int_div(v_offset_1042_, v___x_1043_);
v___x_1045_ = lean_int_mul(v___x_1044_, v___x_1043_);
lean_dec(v___x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dropSeconds___boxed(lean_object* v_offset_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Std_Time_Format_Basic_0__Std_Time_dropSeconds(v_offset_1046_);
lean_dec(v_offset_1046_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_dropSeconds_spec__0(lean_object* v_a_1048_){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_nat_to_int(v_a_1048_);
v___x_1050_ = l_Rat_ofInt(v___x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatOffsetX(lean_object* v_offset_1051_, uint8_t v_x_1052_){
_start:
{
switch(v_x_1052_)
{
case 0:
{
lean_object* v___x_1053_; uint8_t v___x_1054_; lean_object* v_hourMinute_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1053_ = l___private_Std_Time_Format_Basic_0__Std_Time_dropSeconds(v_offset_1051_);
v___x_1054_ = 0;
v_hourMinute_1055_ = l_Std_Time_TimeZone_Offset_toIsoString(v___x_1053_, v___x_1054_);
v___x_1056_ = lean_nat_abs(v_offset_1051_);
lean_dec(v_offset_1051_);
v___x_1057_ = lean_unsigned_to_nat(60u);
v___x_1058_ = lean_nat_div(v___x_1056_, v___x_1057_);
lean_dec(v___x_1056_);
v___x_1059_ = lean_nat_mod(v___x_1058_, v___x_1057_);
lean_dec(v___x_1058_);
v___x_1060_ = lean_unsigned_to_nat(0u);
v___x_1061_ = lean_nat_dec_eq(v___x_1059_, v___x_1060_);
lean_dec(v___x_1059_);
if (v___x_1061_ == 0)
{
return v_hourMinute_1055_;
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1062_ = lean_unsigned_to_nat(2u);
v___x_1063_ = lean_string_utf8_byte_size(v_hourMinute_1055_);
lean_inc_ref(v_hourMinute_1055_);
v___x_1064_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1064_, 0, v_hourMinute_1055_);
lean_ctor_set(v___x_1064_, 1, v___x_1060_);
lean_ctor_set(v___x_1064_, 2, v___x_1063_);
v___x_1065_ = l_String_Slice_Pos_prevn(v___x_1064_, v___x_1063_, v___x_1062_);
lean_dec_ref_known(v___x_1064_, 3);
v___x_1066_ = lean_string_utf8_extract_fast(v_hourMinute_1055_, v___x_1060_, v___x_1065_);
lean_dec(v___x_1065_);
lean_dec_ref(v_hourMinute_1055_);
return v___x_1066_;
}
}
case 1:
{
lean_object* v___x_1067_; uint8_t v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = l___private_Std_Time_Format_Basic_0__Std_Time_dropSeconds(v_offset_1051_);
lean_dec(v_offset_1051_);
v___x_1068_ = 0;
v___x_1069_ = l_Std_Time_TimeZone_Offset_toIsoString(v___x_1067_, v___x_1068_);
return v___x_1069_;
}
case 2:
{
lean_object* v___x_1070_; uint8_t v___x_1071_; lean_object* v___x_1072_; 
v___x_1070_ = l___private_Std_Time_Format_Basic_0__Std_Time_dropSeconds(v_offset_1051_);
lean_dec(v_offset_1051_);
v___x_1071_ = 1;
v___x_1072_ = l_Std_Time_TimeZone_Offset_toIsoString(v___x_1070_, v___x_1071_);
return v___x_1072_;
}
case 3:
{
uint8_t v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = 0;
v___x_1074_ = l_Std_Time_TimeZone_Offset_toIsoString(v_offset_1051_, v___x_1073_);
return v___x_1074_;
}
default: 
{
uint8_t v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = 1;
v___x_1076_ = l_Std_Time_TimeZone_Offset_toIsoString(v_offset_1051_, v___x_1075_);
return v___x_1076_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatOffsetX___boxed(lean_object* v_offset_1077_, lean_object* v_x_1078_){
_start:
{
uint8_t v_x_147__boxed_1079_; lean_object* v_res_1080_; 
v_x_147__boxed_1079_ = lean_unbox(v_x_1078_);
v_res_1080_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatOffsetX(v_offset_1077_, v_x_147__boxed_1079_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatGmtOffset(lean_object* v_offset_1082_){
_start:
{
lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1083_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1084_ = lean_int_dec_eq(v_offset_1082_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1085_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatGmtOffset___closed__0));
v___x_1086_ = 1;
v___x_1087_ = l_Std_Time_TimeZone_Offset_toIsoString(v_offset_1082_, v___x_1086_);
v___x_1088_ = lean_string_append(v___x_1085_, v___x_1087_);
lean_dec_ref(v___x_1087_);
return v___x_1088_;
}
else
{
lean_object* v___x_1089_; 
lean_dec(v_offset_1082_);
v___x_1089_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatGmtOffset___closed__0));
return v___x_1089_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_zoneLabel(lean_object* v_label_1090_, lean_object* v_offset_1091_){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1104_ = lean_string_utf8_byte_size(v_label_1090_);
v___x_1105_ = lean_unsigned_to_nat(1u);
v___x_1106_ = lean_nat_dec_le(v___x_1105_, v___x_1104_);
if (v___x_1106_ == 0)
{
goto v___jp_1097_;
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1107_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear___closed__1));
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = lean_string_memcmp(v_label_1090_, v___x_1107_, v___x_1108_, v___x_1108_, v___x_1105_);
if (v___x_1109_ == 0)
{
goto v___jp_1097_;
}
else
{
goto v___jp_1092_;
}
}
v___jp_1092_:
{
uint8_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1093_ = 1;
v___x_1094_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatGmtOffset___closed__0));
v___x_1095_ = l_Std_Time_TimeZone_Offset_toIsoString(v_offset_1091_, v___x_1093_);
v___x_1096_ = lean_string_append(v___x_1094_, v___x_1095_);
lean_dec_ref(v___x_1095_);
return v___x_1096_;
}
v___jp_1097_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1098_ = lean_string_utf8_byte_size(v_label_1090_);
v___x_1099_ = lean_unsigned_to_nat(1u);
v___x_1100_ = lean_nat_dec_le(v___x_1099_, v___x_1098_);
if (v___x_1100_ == 0)
{
lean_dec(v_offset_1091_);
lean_inc_ref(v_label_1090_);
return v_label_1090_;
}
else
{
lean_object* v___x_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1101_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = lean_string_memcmp(v_label_1090_, v___x_1101_, v___x_1102_, v___x_1102_, v___x_1099_);
if (v___x_1103_ == 0)
{
lean_dec(v_offset_1091_);
lean_inc_ref(v_label_1090_);
return v_label_1090_;
}
else
{
goto v___jp_1092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_zoneLabel___boxed(lean_object* v_label_1110_, lean_object* v_offset_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l___private_Std_Time_Format_Basic_0__Std_Time_zoneLabel(v_label_1110_, v_offset_1111_);
lean_dec_ref(v_label_1110_);
return v_res_1112_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_classifyDayPeriod___lam__0(lean_object* v_minute_1113_, lean_object* v_second_1114_, lean_object* v_00___1115_){
_start:
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1117_ = lean_int_dec_eq(v_minute_1113_, v___x_1116_);
if (v___x_1117_ == 0)
{
return v___x_1117_;
}
else
{
uint8_t v___x_1118_; 
v___x_1118_ = lean_int_dec_eq(v_second_1114_, v___x_1116_);
return v___x_1118_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyDayPeriod___lam__0___boxed(lean_object* v_minute_1119_, lean_object* v_second_1120_, lean_object* v_00___1121_){
_start:
{
uint8_t v_res_1122_; lean_object* v_r_1123_; 
v_res_1122_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1119_, v_second_1120_, v_00___1121_);
lean_dec(v_second_1120_);
lean_dec(v_minute_1119_);
v_r_1123_ = lean_box(v_res_1122_);
return v_r_1123_;
}
}
static lean_object* _init_l_Std_Time_classifyDayPeriod___closed__0(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_unsigned_to_nat(12u);
v___x_1125_ = lean_nat_to_int(v___x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_classifyDayPeriod(lean_object* v_hour_1126_, lean_object* v_minute_1127_, lean_object* v_second_1128_){
_start:
{
lean_object* v___y_1130_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1140_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1141_ = lean_int_dec_eq(v_hour_1126_, v___x_1140_);
if (v___x_1141_ == 0)
{
goto v___jp_1134_;
}
else
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = lean_box(0);
v___x_1143_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1127_, v_second_1128_, v___x_1142_);
if (v___x_1143_ == 0)
{
goto v___jp_1134_;
}
else
{
uint8_t v___x_1144_; 
v___x_1144_ = 3;
return v___x_1144_;
}
}
v___jp_1129_:
{
uint8_t v___x_1131_; 
v___x_1131_ = lean_int_dec_lt(v_hour_1126_, v___y_1130_);
if (v___x_1131_ == 0)
{
uint8_t v___x_1132_; 
v___x_1132_ = 1;
return v___x_1132_;
}
else
{
uint8_t v___x_1133_; 
v___x_1133_ = 0;
return v___x_1133_;
}
}
v___jp_1134_:
{
lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1136_ = lean_int_dec_eq(v_hour_1126_, v___x_1135_);
if (v___x_1136_ == 0)
{
v___y_1130_ = v___x_1135_;
goto v___jp_1129_;
}
else
{
lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = lean_box(0);
v___x_1138_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1127_, v_second_1128_, v___x_1137_);
if (v___x_1138_ == 0)
{
v___y_1130_ = v___x_1135_;
goto v___jp_1129_;
}
else
{
uint8_t v___x_1139_; 
v___x_1139_ = 2;
return v___x_1139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyDayPeriod___boxed(lean_object* v_hour_1145_, lean_object* v_minute_1146_, lean_object* v_second_1147_){
_start:
{
uint8_t v_res_1148_; lean_object* v_r_1149_; 
v_res_1148_ = l_Std_Time_classifyDayPeriod(v_hour_1145_, v_minute_1146_, v_second_1147_);
lean_dec(v_second_1147_);
lean_dec(v_minute_1146_);
lean_dec(v_hour_1145_);
v_r_1149_ = lean_box(v_res_1148_);
return v_r_1149_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__0(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = lean_unsigned_to_nat(6u);
v___x_1151_ = lean_nat_to_int(v___x_1150_);
return v___x_1151_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__1(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_unsigned_to_nat(18u);
v___x_1153_ = lean_nat_to_int(v___x_1152_);
return v___x_1153_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__2(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_unsigned_to_nat(21u);
v___x_1155_ = lean_nat_to_int(v___x_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_classifyExtendedDayPeriod(lean_object* v_hour_1156_, lean_object* v_minute_1157_, lean_object* v_second_1158_){
_start:
{
lean_object* v___y_1160_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1180_ = lean_int_dec_eq(v_hour_1156_, v___x_1179_);
if (v___x_1180_ == 0)
{
goto v___jp_1173_;
}
else
{
lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = lean_box(0);
v___x_1182_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1157_, v_second_1158_, v___x_1181_);
if (v___x_1182_ == 0)
{
goto v___jp_1173_;
}
else
{
uint8_t v___x_1183_; 
v___x_1183_ = 0;
return v___x_1183_;
}
}
v___jp_1159_:
{
lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__0, &l_Std_Time_classifyExtendedDayPeriod___closed__0_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__0);
v___x_1162_ = lean_int_dec_lt(v_hour_1156_, v___x_1161_);
if (v___x_1162_ == 0)
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_int_dec_lt(v_hour_1156_, v___y_1160_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__1, &l_Std_Time_classifyExtendedDayPeriod___closed__1_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__1);
v___x_1165_ = lean_int_dec_lt(v_hour_1156_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__2, &l_Std_Time_classifyExtendedDayPeriod___closed__2_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__2);
v___x_1167_ = lean_int_dec_lt(v_hour_1156_, v___x_1166_);
if (v___x_1167_ == 0)
{
uint8_t v___x_1168_; 
v___x_1168_ = 1;
return v___x_1168_;
}
else
{
uint8_t v___x_1169_; 
v___x_1169_ = 5;
return v___x_1169_;
}
}
else
{
uint8_t v___x_1170_; 
v___x_1170_ = 4;
return v___x_1170_;
}
}
else
{
uint8_t v___x_1171_; 
v___x_1171_ = 2;
return v___x_1171_;
}
}
else
{
uint8_t v___x_1172_; 
v___x_1172_ = 1;
return v___x_1172_;
}
}
v___jp_1173_:
{
lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1175_ = lean_int_dec_eq(v_hour_1156_, v___x_1174_);
if (v___x_1175_ == 0)
{
v___y_1160_ = v___x_1174_;
goto v___jp_1159_;
}
else
{
lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = lean_box(0);
v___x_1177_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1157_, v_second_1158_, v___x_1176_);
if (v___x_1177_ == 0)
{
v___y_1160_ = v___x_1174_;
goto v___jp_1159_;
}
else
{
uint8_t v___x_1178_; 
v___x_1178_ = 3;
return v___x_1178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyExtendedDayPeriod___boxed(lean_object* v_hour_1184_, lean_object* v_minute_1185_, lean_object* v_second_1186_){
_start:
{
uint8_t v_res_1187_; lean_object* v_r_1188_; 
v_res_1187_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1184_, v_minute_1185_, v_second_1186_);
lean_dec(v_second_1186_);
lean_dec(v_minute_1185_);
lean_dec(v_hour_1184_);
v_r_1188_ = lean_box(v_res_1187_);
return v_r_1188_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_formatWith_spec__0(lean_object* v_a_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Rat_ofInt(v_a_1189_);
return v___x_1190_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_unsigned_to_nat(100u);
v___x_1192_ = lean_nat_to_int(v___x_1191_);
return v___x_1192_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_unsigned_to_nat(7u);
v___x_1194_ = lean_nat_to_int(v___x_1193_);
return v___x_1194_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_unsigned_to_nat(1000000000u);
v___x_1197_ = lean_nat_to_int(v___x_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(lean_object* v_dateformat_1200_, lean_object* v_modifier_1201_, lean_object* v_data_1202_){
_start:
{
switch(lean_obj_tag(v_modifier_1201_))
{
case 0:
{
uint8_t v_presentation_1203_; lean_object* v_symbols_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v_presentation_1203_ = lean_ctor_get_uint8(v_modifier_1201_, 0);
lean_dec_ref_known(v_modifier_1201_, 0);
v_symbols_1204_ = lean_ctor_get(v_dateformat_1200_, 1);
lean_inc_ref(v_symbols_1204_);
lean_dec_ref(v_dateformat_1200_);
v___x_1205_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraNames(v_symbols_1204_, v_presentation_1203_);
lean_dec_ref(v_symbols_1204_);
v___x_1206_ = lean_unbox(v_data_1202_);
lean_dec(v_data_1202_);
v___x_1207_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v___x_1206_);
v___x_1208_ = lean_array_fget(v___x_1205_, v___x_1207_);
lean_dec(v___x_1207_);
lean_dec_ref(v___x_1205_);
return v___x_1208_;
}
case 1:
{
lean_object* v_presentation_1209_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1209_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc(v_presentation_1209_);
lean_dec_ref_known(v_modifier_1201_, 1);
switch(lean_obj_tag(v_presentation_1209_))
{
case 0:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_unsigned_to_nat(0u);
v___x_1211_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1210_, v_data_1202_);
lean_dec(v_data_1202_);
return v___x_1211_;
}
case 1:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1212_ = lean_unsigned_to_nat(2u);
v___x_1213_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1214_ = lean_int_emod(v_data_1202_, v___x_1213_);
lean_dec(v_data_1202_);
v___x_1215_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1212_, v___x_1214_);
lean_dec(v___x_1214_);
return v___x_1215_;
}
case 2:
{
lean_object* v___x_1216_; 
v___x_1216_ = l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear(v_data_1202_);
lean_dec(v_data_1202_);
return v___x_1216_;
}
default: 
{
lean_object* v_num_1217_; lean_object* v___x_1218_; 
v_num_1217_ = lean_ctor_get(v_presentation_1209_, 0);
lean_inc(v_num_1217_);
lean_dec_ref_known(v_presentation_1209_, 1);
v___x_1218_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1217_, v_data_1202_);
lean_dec(v_data_1202_);
lean_dec(v_num_1217_);
return v___x_1218_;
}
}
}
case 2:
{
lean_object* v_presentation_1219_; lean_object* v___x_1220_; lean_object* v___y_1222_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1219_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc(v_presentation_1219_);
lean_dec_ref_known(v_modifier_1201_, 1);
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1231_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1232_ = lean_int_dec_le(v_data_1202_, v___x_1231_);
if (v___x_1232_ == 0)
{
v___y_1222_ = v_data_1202_;
goto v___jp_1221_;
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1233_ = lean_int_neg(v_data_1202_);
lean_dec(v_data_1202_);
v___x_1234_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1235_ = lean_int_add(v___x_1233_, v___x_1234_);
lean_dec(v___x_1233_);
v___y_1222_ = v___x_1235_;
goto v___jp_1221_;
}
v___jp_1221_:
{
switch(lean_obj_tag(v_presentation_1219_))
{
case 0:
{
lean_object* v___x_1223_; 
v___x_1223_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1220_, v___y_1222_);
lean_dec(v___y_1222_);
return v___x_1223_;
}
case 1:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1224_ = lean_unsigned_to_nat(2u);
v___x_1225_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1226_ = lean_int_emod(v___y_1222_, v___x_1225_);
lean_dec(v___y_1222_);
v___x_1227_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1224_, v___x_1226_);
lean_dec(v___x_1226_);
return v___x_1227_;
}
case 2:
{
lean_object* v___x_1228_; 
v___x_1228_ = l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear(v___y_1222_);
lean_dec(v___y_1222_);
return v___x_1228_;
}
default: 
{
lean_object* v_num_1229_; lean_object* v___x_1230_; 
v_num_1229_ = lean_ctor_get(v_presentation_1219_, 0);
lean_inc(v_num_1229_);
lean_dec_ref_known(v_presentation_1219_, 1);
v___x_1230_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1229_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec(v_num_1229_);
return v___x_1230_;
}
}
}
}
case 3:
{
lean_object* v_presentation_1236_; lean_object* v_snd_1237_; lean_object* v___x_1238_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1236_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc(v_presentation_1236_);
lean_dec_ref_known(v_modifier_1201_, 1);
v_snd_1237_ = lean_ctor_get(v_data_1202_, 1);
lean_inc(v_snd_1237_);
lean_dec(v_data_1202_);
v___x_1238_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1236_, v_snd_1237_);
lean_dec(v_snd_1237_);
lean_dec(v_presentation_1236_);
return v___x_1238_;
}
case 4:
{
lean_object* v_presentation_1239_; 
v_presentation_1239_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc_ref(v_presentation_1239_);
lean_dec_ref_known(v_modifier_1201_, 1);
if (lean_obj_tag(v_presentation_1239_) == 0)
{
lean_object* v_val_1240_; lean_object* v___x_1241_; 
lean_dec_ref(v_dateformat_1200_);
v_val_1240_ = lean_ctor_get(v_presentation_1239_, 0);
lean_inc(v_val_1240_);
lean_dec_ref_known(v_presentation_1239_, 1);
v___x_1241_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1240_, v_data_1202_);
lean_dec(v_data_1202_);
lean_dec(v_val_1240_);
return v___x_1241_;
}
else
{
lean_object* v_val_1242_; lean_object* v_symbols_1243_; uint8_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v_val_1242_ = lean_ctor_get(v_presentation_1239_, 0);
lean_inc(v_val_1242_);
lean_dec_ref_known(v_presentation_1239_, 1);
v_symbols_1243_ = lean_ctor_get(v_dateformat_1200_, 1);
lean_inc_ref(v_symbols_1243_);
lean_dec_ref(v_dateformat_1200_);
v___x_1244_ = lean_unbox(v_val_1242_);
lean_dec(v_val_1242_);
v___x_1245_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthNames(v_symbols_1243_, v___x_1244_);
lean_dec_ref(v_symbols_1243_);
v___x_1246_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex(v_data_1202_);
lean_dec(v_data_1202_);
v___x_1247_ = lean_array_fget(v___x_1245_, v___x_1246_);
lean_dec(v___x_1246_);
lean_dec_ref(v___x_1245_);
return v___x_1247_;
}
}
case 5:
{
lean_object* v_presentation_1248_; 
v_presentation_1248_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc_ref(v_presentation_1248_);
lean_dec_ref_known(v_modifier_1201_, 1);
if (lean_obj_tag(v_presentation_1248_) == 0)
{
lean_object* v_val_1249_; lean_object* v___x_1250_; 
lean_dec_ref(v_dateformat_1200_);
v_val_1249_ = lean_ctor_get(v_presentation_1248_, 0);
lean_inc(v_val_1249_);
lean_dec_ref_known(v_presentation_1248_, 1);
v___x_1250_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1249_, v_data_1202_);
lean_dec(v_data_1202_);
lean_dec(v_val_1249_);
return v___x_1250_;
}
else
{
lean_object* v_val_1251_; lean_object* v_symbols_1252_; uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_val_1251_ = lean_ctor_get(v_presentation_1248_, 0);
lean_inc(v_val_1251_);
lean_dec_ref_known(v_presentation_1248_, 1);
v_symbols_1252_ = lean_ctor_get(v_dateformat_1200_, 1);
lean_inc_ref(v_symbols_1252_);
lean_dec_ref(v_dateformat_1200_);
v___x_1253_ = lean_unbox(v_val_1251_);
lean_dec(v_val_1251_);
v___x_1254_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthNames(v_symbols_1252_, v___x_1253_);
lean_dec_ref(v_symbols_1252_);
v___x_1255_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex(v_data_1202_);
lean_dec(v_data_1202_);
v___x_1256_ = lean_array_fget(v___x_1254_, v___x_1255_);
lean_dec(v___x_1255_);
lean_dec_ref(v___x_1254_);
return v___x_1256_;
}
}
case 6:
{
lean_object* v_presentation_1257_; lean_object* v___x_1258_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1257_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc(v_presentation_1257_);
lean_dec_ref_known(v_modifier_1201_, 1);
v___x_1258_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1257_, v_data_1202_);
lean_dec(v_data_1202_);
lean_dec(v_presentation_1257_);
return v___x_1258_;
}
case 7:
{
lean_object* v_presentation_1259_; 
v_presentation_1259_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc_ref(v_presentation_1259_);
lean_dec_ref_known(v_modifier_1201_, 1);
if (lean_obj_tag(v_presentation_1259_) == 0)
{
lean_object* v_val_1260_; lean_object* v___x_1261_; 
lean_dec_ref(v_dateformat_1200_);
v_val_1260_ = lean_ctor_get(v_presentation_1259_, 0);
lean_inc(v_val_1260_);
lean_dec_ref_known(v_presentation_1259_, 1);
v___x_1261_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1260_, v_data_1202_);
lean_dec(v_data_1202_);
lean_dec(v_val_1260_);
return v___x_1261_;
}
else
{
lean_object* v_val_1262_; lean_object* v_symbols_1263_; uint8_t v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v_val_1262_ = lean_ctor_get(v_presentation_1259_, 0);
lean_inc(v_val_1262_);
lean_dec_ref_known(v_presentation_1259_, 1);
v_symbols_1263_ = lean_ctor_get(v_dateformat_1200_, 1);
lean_inc_ref(v_symbols_1263_);
lean_dec_ref(v_dateformat_1200_);
v___x_1264_ = lean_unbox(v_val_1262_);
lean_dec(v_val_1262_);
v___x_1265_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterNames(v_symbols_1263_, v___x_1264_);
lean_dec_ref(v_symbols_1263_);
v___x_1266_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterIndex(v_data_1202_);
lean_dec(v_data_1202_);
v___x_1267_ = lean_array_fget(v___x_1265_, v___x_1266_);
lean_dec(v___x_1266_);
lean_dec_ref(v___x_1265_);
return v___x_1267_;
}
}
case 8:
{
lean_object* v_presentation_1268_; 
v_presentation_1268_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc_ref(v_presentation_1268_);
lean_dec_ref_known(v_modifier_1201_, 1);
if (lean_obj_tag(v_presentation_1268_) == 0)
{
lean_object* v_val_1269_; lean_object* v___x_1270_; 
lean_dec_ref(v_dateformat_1200_);
v_val_1269_ = lean_ctor_get(v_presentation_1268_, 0);
lean_inc(v_val_1269_);
lean_dec_ref_known(v_presentation_1268_, 1);
v___x_1270_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1269_, v_data_1202_);
lean_dec(v_data_1202_);
lean_dec(v_val_1269_);
return v___x_1270_;
}
else
{
lean_object* v_val_1271_; lean_object* v_symbols_1272_; uint8_t v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_val_1271_ = lean_ctor_get(v_presentation_1268_, 0);
lean_inc(v_val_1271_);
lean_dec_ref_known(v_presentation_1268_, 1);
v_symbols_1272_ = lean_ctor_get(v_dateformat_1200_, 1);
lean_inc_ref(v_symbols_1272_);
lean_dec_ref(v_dateformat_1200_);
v___x_1273_ = lean_unbox(v_val_1271_);
lean_dec(v_val_1271_);
v___x_1274_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterNames(v_symbols_1272_, v___x_1273_);
lean_dec_ref(v_symbols_1272_);
v___x_1275_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterIndex(v_data_1202_);
lean_dec(v_data_1202_);
v___x_1276_ = lean_array_fget(v___x_1274_, v___x_1275_);
lean_dec(v___x_1275_);
lean_dec_ref(v___x_1274_);
return v___x_1276_;
}
}
case 9:
{
lean_object* v_presentation_1277_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1277_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc(v_presentation_1277_);
lean_dec_ref_known(v_modifier_1201_, 1);
switch(lean_obj_tag(v_presentation_1277_))
{
case 0:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = lean_unsigned_to_nat(0u);
v___x_1279_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1278_, v_data_1202_);
lean_dec(v_data_1202_);
return v___x_1279_;
}
case 1:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1280_ = lean_unsigned_to_nat(2u);
v___x_1281_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1282_ = lean_int_emod(v_data_1202_, v___x_1281_);
lean_dec(v_data_1202_);
v___x_1283_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1280_, v___x_1282_);
lean_dec(v___x_1282_);
return v___x_1283_;
}
case 2:
{
lean_object* v___x_1284_; 
v___x_1284_ = l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear(v_data_1202_);
lean_dec(v_data_1202_);
return v___x_1284_;
}
default: 
{
lean_object* v_num_1285_; lean_object* v___x_1286_; 
v_num_1285_ = lean_ctor_get(v_presentation_1277_, 0);
lean_inc(v_num_1285_);
lean_dec_ref_known(v_presentation_1277_, 1);
v___x_1286_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1285_, v_data_1202_);
lean_dec(v_data_1202_);
lean_dec(v_num_1285_);
return v___x_1286_;
}
}
}
case 10:
{
lean_object* v_presentation_1287_; lean_object* v___x_1288_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1287_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc(v_presentation_1287_);
lean_dec_ref_known(v_modifier_1201_, 1);
v___x_1288_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1287_, v_data_1202_);
lean_dec(v_data_1202_);
lean_dec(v_presentation_1287_);
return v___x_1288_;
}
case 11:
{
lean_object* v_presentation_1289_; lean_object* v___x_1290_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1289_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc(v_presentation_1289_);
lean_dec_ref_known(v_modifier_1201_, 1);
v___x_1290_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1289_, v_data_1202_);
lean_dec(v_data_1202_);
lean_dec(v_presentation_1289_);
return v___x_1290_;
}
case 12:
{
uint8_t v_presentation_1291_; lean_object* v_symbols_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v_presentation_1291_ = lean_ctor_get_uint8(v_modifier_1201_, 0);
lean_dec_ref_known(v_modifier_1201_, 0);
v_symbols_1292_ = lean_ctor_get(v_dateformat_1200_, 1);
lean_inc_ref(v_symbols_1292_);
lean_dec_ref(v_dateformat_1200_);
v___x_1293_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayNames(v_symbols_1292_, v_presentation_1291_);
lean_dec_ref(v_symbols_1292_);
v___x_1294_ = lean_unbox(v_data_1202_);
lean_dec(v_data_1202_);
v___x_1295_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayIndex(v___x_1294_);
v___x_1296_ = lean_array_fget(v___x_1293_, v___x_1295_);
lean_dec(v___x_1295_);
lean_dec_ref(v___x_1293_);
return v___x_1296_;
}
case 13:
{
lean_object* v_presentation_1297_; 
v_presentation_1297_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc_ref(v_presentation_1297_);
lean_dec_ref_known(v_modifier_1201_, 1);
if (lean_obj_tag(v_presentation_1297_) == 0)
{
lean_object* v_val_1298_; uint8_t v_firstDayOfWeek_1299_; lean_object* v_firstOrd_1300_; uint8_t v___x_1301_; lean_object* v_dayOrd_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_val_1298_ = lean_ctor_get(v_presentation_1297_, 0);
lean_inc(v_val_1298_);
lean_dec_ref_known(v_presentation_1297_, 1);
v_firstDayOfWeek_1299_ = lean_ctor_get_uint8(v_dateformat_1200_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_1200_);
v_firstOrd_1300_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_1299_);
v___x_1301_ = lean_unbox(v_data_1202_);
lean_dec(v_data_1202_);
v_dayOrd_1302_ = l_Std_Time_Weekday_toOrdinal(v___x_1301_);
v___x_1303_ = lean_int_sub(v_dayOrd_1302_, v_firstOrd_1300_);
lean_dec(v_firstOrd_1300_);
lean_dec(v_dayOrd_1302_);
v___x_1304_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_1305_ = lean_int_add(v___x_1303_, v___x_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_int_emod(v___x_1305_, v___x_1304_);
lean_dec(v___x_1305_);
v___x_1307_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1308_ = lean_int_add(v___x_1306_, v___x_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1298_, v___x_1308_);
lean_dec(v___x_1308_);
lean_dec(v_val_1298_);
return v___x_1309_;
}
else
{
lean_object* v_val_1310_; lean_object* v_symbols_1311_; uint8_t v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v_val_1310_ = lean_ctor_get(v_presentation_1297_, 0);
lean_inc(v_val_1310_);
lean_dec_ref_known(v_presentation_1297_, 1);
v_symbols_1311_ = lean_ctor_get(v_dateformat_1200_, 1);
lean_inc_ref(v_symbols_1311_);
lean_dec_ref(v_dateformat_1200_);
v___x_1312_ = lean_unbox(v_val_1310_);
lean_dec(v_val_1310_);
v___x_1313_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayNames(v_symbols_1311_, v___x_1312_);
lean_dec_ref(v_symbols_1311_);
v___x_1314_ = lean_unbox(v_data_1202_);
lean_dec(v_data_1202_);
v___x_1315_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayIndex(v___x_1314_);
v___x_1316_ = lean_array_fget(v___x_1313_, v___x_1315_);
lean_dec(v___x_1315_);
lean_dec_ref(v___x_1313_);
return v___x_1316_;
}
}
case 14:
{
lean_object* v_presentation_1317_; 
v_presentation_1317_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc_ref(v_presentation_1317_);
lean_dec_ref_known(v_modifier_1201_, 1);
if (lean_obj_tag(v_presentation_1317_) == 0)
{
lean_object* v_val_1318_; uint8_t v_firstDayOfWeek_1319_; lean_object* v_firstOrd_1320_; uint8_t v___x_1321_; lean_object* v_dayOrd_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v_val_1318_ = lean_ctor_get(v_presentation_1317_, 0);
lean_inc(v_val_1318_);
lean_dec_ref_known(v_presentation_1317_, 1);
v_firstDayOfWeek_1319_ = lean_ctor_get_uint8(v_dateformat_1200_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_1200_);
v_firstOrd_1320_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_1319_);
v___x_1321_ = lean_unbox(v_data_1202_);
lean_dec(v_data_1202_);
v_dayOrd_1322_ = l_Std_Time_Weekday_toOrdinal(v___x_1321_);
v___x_1323_ = lean_int_sub(v_dayOrd_1322_, v_firstOrd_1320_);
lean_dec(v_firstOrd_1320_);
lean_dec(v_dayOrd_1322_);
v___x_1324_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_1325_ = lean_int_add(v___x_1323_, v___x_1324_);
lean_dec(v___x_1323_);
v___x_1326_ = lean_int_emod(v___x_1325_, v___x_1324_);
lean_dec(v___x_1325_);
v___x_1327_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1328_ = lean_int_add(v___x_1326_, v___x_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1318_, v___x_1328_);
lean_dec(v___x_1328_);
lean_dec(v_val_1318_);
return v___x_1329_;
}
else
{
lean_object* v_val_1330_; lean_object* v_symbols_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v_val_1330_ = lean_ctor_get(v_presentation_1317_, 0);
lean_inc(v_val_1330_);
lean_dec_ref_known(v_presentation_1317_, 1);
v_symbols_1331_ = lean_ctor_get(v_dateformat_1200_, 1);
lean_inc_ref(v_symbols_1331_);
lean_dec_ref(v_dateformat_1200_);
v___x_1332_ = lean_unbox(v_val_1330_);
lean_dec(v_val_1330_);
v___x_1333_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayNames(v_symbols_1331_, v___x_1332_);
lean_dec_ref(v_symbols_1331_);
v___x_1334_ = lean_unbox(v_data_1202_);
lean_dec(v_data_1202_);
v___x_1335_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayIndex(v___x_1334_);
v___x_1336_ = lean_array_fget(v___x_1333_, v___x_1335_);
lean_dec(v___x_1335_);
lean_dec_ref(v___x_1333_);
return v___x_1336_;
}
}
case 15:
{
lean_object* v_presentation_1337_; lean_object* v___x_1338_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1337_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc(v_presentation_1337_);
lean_dec_ref_known(v_modifier_1201_, 1);
v___x_1338_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1337_, v_data_1202_);
lean_dec(v_data_1202_);
lean_dec(v_presentation_1337_);
return v___x_1338_;
}
case 16:
{
uint8_t v_presentation_1339_; lean_object* v_symbols_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_presentation_1339_ = lean_ctor_get_uint8(v_modifier_1201_, 0);
lean_dec_ref_known(v_modifier_1201_, 0);
v_symbols_1340_ = lean_ctor_get(v_dateformat_1200_, 1);
lean_inc_ref(v_symbols_1340_);
lean_dec_ref(v_dateformat_1200_);
v___x_1341_ = l___private_Std_Time_Format_Basic_0__Std_Time_markerNames(v_symbols_1340_, v_presentation_1339_);
v___x_1342_ = lean_unbox(v_data_1202_);
lean_dec(v_data_1202_);
v___x_1343_ = l___private_Std_Time_Format_Basic_0__Std_Time_markerIndex(v___x_1342_);
v___x_1344_ = lean_array_fget(v___x_1341_, v___x_1343_);
lean_dec(v___x_1343_);
lean_dec_ref(v___x_1341_);
return v___x_1344_;
}
case 17:
{
uint8_t v_presentation_1345_; lean_object* v_symbols_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v_presentation_1345_ = lean_ctor_get_uint8(v_modifier_1201_, 0);
lean_dec_ref_known(v_modifier_1201_, 0);
v_symbols_1346_ = lean_ctor_get(v_dateformat_1200_, 1);
lean_inc_ref(v_symbols_1346_);
lean_dec_ref(v_dateformat_1200_);
v___x_1347_ = l___private_Std_Time_Format_Basic_0__Std_Time_dayPeriodNames(v_symbols_1346_, v_presentation_1345_);
v___x_1348_ = lean_unbox(v_data_1202_);
lean_dec(v_data_1202_);
v___x_1349_ = l___private_Std_Time_Format_Basic_0__Std_Time_dayPeriodIndex(v___x_1348_);
v___x_1350_ = lean_array_fget(v___x_1347_, v___x_1349_);
lean_dec(v___x_1349_);
lean_dec_ref(v___x_1347_);
return v___x_1350_;
}
case 18:
{
uint8_t v_presentation_1351_; lean_object* v_symbols_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_presentation_1351_ = lean_ctor_get_uint8(v_modifier_1201_, 0);
lean_dec_ref_known(v_modifier_1201_, 0);
v_symbols_1352_ = lean_ctor_get(v_dateformat_1200_, 1);
lean_inc_ref(v_symbols_1352_);
lean_dec_ref(v_dateformat_1200_);
v___x_1353_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodNames(v_symbols_1352_, v_presentation_1351_);
lean_dec_ref(v_symbols_1352_);
v___x_1354_ = lean_unbox(v_data_1202_);
lean_dec(v_data_1202_);
v___x_1355_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(v___x_1354_);
v___x_1356_ = lean_array_fget(v___x_1353_, v___x_1355_);
lean_dec(v___x_1355_);
lean_dec_ref(v___x_1353_);
return v___x_1356_;
}
case 19:
{
lean_object* v_presentation_1357_; lean_object* v___x_1358_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1357_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc(v_presentation_1357_);
lean_dec_ref_known(v_modifier_1201_, 1);
v___x_1358_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1357_, v_data_1202_);
lean_dec(v_data_1202_);
lean_dec(v_presentation_1357_);
return v___x_1358_;
}
case 20:
{
lean_object* v_presentation_1359_; lean_object* v___x_1360_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1359_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc(v_presentation_1359_);
lean_dec_ref_known(v_modifier_1201_, 1);
v___x_1360_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1359_, v_data_1202_);
lean_dec(v_data_1202_);
lean_dec(v_presentation_1359_);
return v___x_1360_;
}
case 21:
{
lean_object* v_presentation_1361_; lean_object* v___x_1362_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1361_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc(v_presentation_1361_);
lean_dec_ref_known(v_modifier_1201_, 1);
v___x_1362_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1361_, v_data_1202_);
lean_dec(v_data_1202_);
lean_dec(v_presentation_1361_);
return v___x_1362_;
}
case 22:
{
lean_object* v_presentation_1363_; lean_object* v___x_1364_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1363_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc(v_presentation_1363_);
lean_dec_ref_known(v_modifier_1201_, 1);
v___x_1364_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1363_, v_data_1202_);
lean_dec(v_data_1202_);
lean_dec(v_presentation_1363_);
return v___x_1364_;
}
case 23:
{
lean_object* v_presentation_1365_; lean_object* v___x_1366_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1365_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc(v_presentation_1365_);
lean_dec_ref_known(v_modifier_1201_, 1);
v___x_1366_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1365_, v_data_1202_);
lean_dec(v_data_1202_);
lean_dec(v_presentation_1365_);
return v___x_1366_;
}
case 24:
{
lean_object* v_presentation_1367_; lean_object* v___x_1368_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1367_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc(v_presentation_1367_);
lean_dec_ref_known(v_modifier_1201_, 1);
v___x_1368_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1367_, v_data_1202_);
lean_dec(v_data_1202_);
lean_dec(v_presentation_1367_);
return v___x_1368_;
}
case 25:
{
lean_object* v_presentation_1369_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1369_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc(v_presentation_1369_);
lean_dec_ref_known(v_modifier_1201_, 1);
if (lean_obj_tag(v_presentation_1369_) == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_unsigned_to_nat(9u);
v___x_1371_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1370_, v_data_1202_);
lean_dec(v_data_1202_);
return v___x_1371_;
}
else
{
lean_object* v_digits_1372_; lean_object* v___x_1373_; uint32_t v___x_1374_; lean_object* v___x_1375_; lean_object* v_s_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v_digits_1372_ = lean_ctor_get(v_presentation_1369_, 0);
lean_inc(v_digits_1372_);
lean_dec_ref_known(v_presentation_1369_, 1);
v___x_1373_ = lean_unsigned_to_nat(9u);
v___x_1374_ = 48;
v___x_1375_ = l_Int_repr(v_data_1202_);
lean_dec(v_data_1202_);
v_s_1376_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1373_, v___x_1374_, v___x_1375_);
lean_dec_ref(v___x_1375_);
v___x_1377_ = lean_unsigned_to_nat(0u);
v___x_1378_ = lean_string_utf8_byte_size(v_s_1376_);
lean_inc_ref(v_s_1376_);
v___x_1379_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1379_, 0, v_s_1376_);
lean_ctor_set(v___x_1379_, 1, v___x_1377_);
lean_ctor_set(v___x_1379_, 2, v___x_1378_);
v___x_1380_ = l_String_Slice_Pos_nextn(v___x_1379_, v___x_1377_, v_digits_1372_);
lean_dec_ref_known(v___x_1379_, 3);
v___x_1381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1381_, 0, v_s_1376_);
lean_ctor_set(v___x_1381_, 1, v___x_1377_);
lean_ctor_set(v___x_1381_, 2, v___x_1380_);
v___x_1382_ = l_String_Slice_toString(v___x_1381_);
lean_dec_ref_known(v___x_1381_, 3);
return v___x_1382_;
}
}
case 26:
{
lean_object* v_presentation_1383_; lean_object* v___x_1384_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1383_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc(v_presentation_1383_);
lean_dec_ref_known(v_modifier_1201_, 1);
v___x_1384_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1383_, v_data_1202_);
lean_dec(v_data_1202_);
lean_dec(v_presentation_1383_);
return v___x_1384_;
}
case 27:
{
lean_object* v_presentation_1385_; lean_object* v___x_1386_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1385_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc(v_presentation_1385_);
lean_dec_ref_known(v_modifier_1201_, 1);
v___x_1386_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1385_, v_data_1202_);
lean_dec(v_data_1202_);
lean_dec(v_presentation_1385_);
return v___x_1386_;
}
case 28:
{
lean_object* v_presentation_1387_; lean_object* v___x_1388_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1387_ = lean_ctor_get(v_modifier_1201_, 0);
lean_inc(v_presentation_1387_);
lean_dec_ref_known(v_modifier_1201_, 1);
v___x_1388_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1387_, v_data_1202_);
lean_dec(v_data_1202_);
lean_dec(v_presentation_1387_);
return v___x_1388_;
}
case 29:
{
uint8_t v_presentation_1389_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1389_ = lean_ctor_get_uint8(v_modifier_1201_, 0);
lean_dec_ref_known(v_modifier_1201_, 0);
if (v_presentation_1389_ == 0)
{
lean_object* v___x_1390_; 
lean_dec(v_data_1202_);
v___x_1390_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
return v___x_1390_;
}
else
{
return v_data_1202_;
}
}
case 32:
{
uint8_t v_presentation_1391_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1391_ = lean_ctor_get_uint8(v_modifier_1201_, 0);
lean_dec_ref_known(v_modifier_1201_, 0);
if (v_presentation_1391_ == 0)
{
lean_object* v_fst_1393_; lean_object* v_snd_1394_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1432_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1433_ = lean_int_dec_eq(v_data_1202_, v___x_1432_);
if (v___x_1433_ == 0)
{
uint8_t v___x_1434_; 
v___x_1434_ = lean_int_dec_le(v___x_1432_, v_data_1202_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1436_ = lean_int_neg(v_data_1202_);
lean_dec(v_data_1202_);
v_fst_1393_ = v___x_1435_;
v_snd_1394_ = v___x_1436_;
goto v___jp_1392_;
}
else
{
lean_object* v___x_1437_; 
v___x_1437_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_padFourDigitYear___closed__1));
v_fst_1393_ = v___x_1437_;
v_snd_1394_ = v_data_1202_;
goto v___jp_1392_;
}
}
else
{
lean_object* v___x_1438_; 
lean_dec(v_data_1202_);
v___x_1438_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatGmtOffset___closed__0));
return v___x_1438_;
}
v___jp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v_t_1397_; lean_object* v_hour_1398_; lean_object* v_minute_1399_; lean_object* v_second_1400_; lean_object* v___x_1401_; uint32_t v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1395_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3);
v___x_1396_ = lean_int_mul(v_snd_1394_, v___x_1395_);
lean_dec(v_snd_1394_);
v_t_1397_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1396_);
lean_dec(v___x_1396_);
v_hour_1398_ = lean_ctor_get(v_t_1397_, 0);
lean_inc(v_hour_1398_);
v_minute_1399_ = lean_ctor_get(v_t_1397_, 1);
lean_inc(v_minute_1399_);
v_second_1400_ = lean_ctor_get(v_t_1397_, 2);
lean_inc(v_second_1400_);
lean_dec_ref(v_t_1397_);
v___x_1401_ = lean_unsigned_to_nat(2u);
v___x_1402_ = 48;
v___x_1403_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1404_ = lean_int_dec_eq(v_second_1400_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1405_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatGmtOffset___closed__0));
v___x_1406_ = lean_string_append(v___x_1405_, v_fst_1393_);
v___x_1407_ = l_Int_repr(v_hour_1398_);
lean_dec(v_hour_1398_);
v___x_1408_ = lean_string_append(v___x_1406_, v___x_1407_);
lean_dec_ref(v___x_1407_);
v___x_1409_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
v___x_1410_ = lean_string_append(v___x_1408_, v___x_1409_);
v___x_1411_ = l_Int_repr(v_minute_1399_);
lean_dec(v_minute_1399_);
v___x_1412_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1401_, v___x_1402_, v___x_1411_);
lean_dec_ref(v___x_1411_);
v___x_1413_ = lean_string_append(v___x_1410_, v___x_1412_);
lean_dec_ref(v___x_1412_);
v___x_1414_ = lean_string_append(v___x_1413_, v___x_1409_);
v___x_1415_ = l_Int_repr(v_second_1400_);
lean_dec(v_second_1400_);
v___x_1416_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1401_, v___x_1402_, v___x_1415_);
lean_dec_ref(v___x_1415_);
v___x_1417_ = lean_string_append(v___x_1414_, v___x_1416_);
lean_dec_ref(v___x_1416_);
return v___x_1417_;
}
else
{
uint8_t v___x_1418_; 
lean_dec(v_second_1400_);
v___x_1418_ = lean_int_dec_eq(v_minute_1399_, v___x_1403_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1419_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatGmtOffset___closed__0));
v___x_1420_ = lean_string_append(v___x_1419_, v_fst_1393_);
v___x_1421_ = l_Int_repr(v_hour_1398_);
lean_dec(v_hour_1398_);
v___x_1422_ = lean_string_append(v___x_1420_, v___x_1421_);
lean_dec_ref(v___x_1421_);
v___x_1423_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
v___x_1424_ = lean_string_append(v___x_1422_, v___x_1423_);
v___x_1425_ = l_Int_repr(v_minute_1399_);
lean_dec(v_minute_1399_);
v___x_1426_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1401_, v___x_1402_, v___x_1425_);
lean_dec_ref(v___x_1425_);
v___x_1427_ = lean_string_append(v___x_1424_, v___x_1426_);
lean_dec_ref(v___x_1426_);
return v___x_1427_;
}
else
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec(v_minute_1399_);
v___x_1428_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatGmtOffset___closed__0));
v___x_1429_ = lean_string_append(v___x_1428_, v_fst_1393_);
v___x_1430_ = l_Int_repr(v_hour_1398_);
lean_dec(v_hour_1398_);
v___x_1431_ = lean_string_append(v___x_1429_, v___x_1430_);
lean_dec_ref(v___x_1430_);
return v___x_1431_;
}
}
}
}
else
{
lean_object* v___x_1439_; 
v___x_1439_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatGmtOffset(v_data_1202_);
return v___x_1439_;
}
}
case 33:
{
uint8_t v_presentation_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1440_ = lean_ctor_get_uint8(v_modifier_1201_, 0);
lean_dec_ref_known(v_modifier_1201_, 0);
v___x_1441_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1442_ = lean_int_dec_eq(v_data_1202_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
v___x_1443_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatOffsetX(v_data_1202_, v_presentation_1440_);
return v___x_1443_;
}
else
{
lean_object* v___x_1444_; 
lean_dec(v_data_1202_);
v___x_1444_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__5));
return v___x_1444_;
}
}
case 34:
{
uint8_t v_presentation_1445_; lean_object* v___x_1446_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1445_ = lean_ctor_get_uint8(v_modifier_1201_, 0);
lean_dec_ref_known(v_modifier_1201_, 0);
v___x_1446_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatOffsetX(v_data_1202_, v_presentation_1445_);
return v___x_1446_;
}
case 35:
{
uint8_t v_presentation_1447_; 
lean_dec_ref(v_dateformat_1200_);
v_presentation_1447_ = lean_ctor_get_uint8(v_modifier_1201_, 0);
lean_dec_ref_known(v_modifier_1201_, 0);
switch(v_presentation_1447_)
{
case 0:
{
uint8_t v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = 0;
v___x_1449_ = l_Std_Time_TimeZone_Offset_toIsoString(v_data_1202_, v___x_1448_);
return v___x_1449_;
}
case 1:
{
lean_object* v___x_1450_; 
v___x_1450_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatGmtOffset(v_data_1202_);
return v___x_1450_;
}
default: 
{
lean_object* v___x_1451_; uint8_t v___x_1452_; 
v___x_1451_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1452_ = lean_int_dec_eq(v_data_1202_, v___x_1451_);
if (v___x_1452_ == 0)
{
uint8_t v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = 1;
v___x_1454_ = l_Std_Time_TimeZone_Offset_toIsoString(v_data_1202_, v___x_1453_);
return v___x_1454_;
}
else
{
lean_object* v___x_1455_; 
lean_dec(v_data_1202_);
v___x_1455_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__5));
return v___x_1455_;
}
}
}
}
default: 
{
lean_dec_ref(v_modifier_1201_);
lean_dec_ref(v_dateformat_1200_);
return v_data_1202_;
}
}
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_unsigned_to_nat(4u);
v___x_1457_ = lean_nat_to_int(v___x_1456_);
return v___x_1457_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = lean_unsigned_to_nat(400u);
v___x_1459_ = lean_nat_to_int(v___x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f(lean_object* v_dateformat_1462_, lean_object* v_date_x3f_1463_, lean_object* v_time_x3f_1464_, lean_object* v_zone_x3f_1465_, lean_object* v_modifier_1466_){
_start:
{
switch(lean_obj_tag(v_modifier_1466_))
{
case 0:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_time_x3f_1464_);
if (lean_obj_tag(v_date_x3f_1463_) == 0)
{
lean_object* v___x_1467_; 
v___x_1467_ = lean_box(0);
return v___x_1467_;
}
else
{
lean_object* v_val_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1478_; 
v_val_1468_ = lean_ctor_get(v_date_x3f_1463_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_date_x3f_1463_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1470_ = v_date_x3f_1463_;
v_isShared_1471_ = v_isSharedCheck_1478_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_val_1468_);
lean_dec(v_date_x3f_1463_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1478_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v_year_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1476_; 
v_year_1472_ = lean_ctor_get(v_val_1468_, 0);
lean_inc(v_year_1472_);
lean_dec(v_val_1468_);
v___x_1473_ = l_Std_Time_Year_Offset_era(v_year_1472_);
lean_dec(v_year_1472_);
v___x_1474_ = lean_box(v___x_1473_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v___x_1474_);
v___x_1476_ = v___x_1470_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
case 1:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_time_x3f_1464_);
if (lean_obj_tag(v_date_x3f_1463_) == 0)
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_box(0);
return v___x_1479_;
}
else
{
lean_object* v_val_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1488_; 
v_val_1480_ = lean_ctor_get(v_date_x3f_1463_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_date_x3f_1463_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1482_ = v_date_x3f_1463_;
v_isShared_1483_ = v_isSharedCheck_1488_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_val_1480_);
lean_dec(v_date_x3f_1463_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1488_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v_year_1484_; lean_object* v___x_1486_; 
v_year_1484_ = lean_ctor_get(v_val_1480_, 0);
lean_inc(v_year_1484_);
lean_dec(v_val_1480_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v_year_1484_);
v___x_1486_ = v___x_1482_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_year_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
case 2:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_time_x3f_1464_);
if (lean_obj_tag(v_date_x3f_1463_) == 0)
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_box(0);
return v___x_1489_;
}
else
{
lean_object* v_val_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1498_; 
v_val_1490_ = lean_ctor_get(v_date_x3f_1463_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_date_x3f_1463_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1492_ = v_date_x3f_1463_;
v_isShared_1493_ = v_isSharedCheck_1498_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_val_1490_);
lean_dec(v_date_x3f_1463_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1498_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v_year_1494_; lean_object* v___x_1496_; 
v_year_1494_ = lean_ctor_get(v_val_1490_, 0);
lean_inc(v_year_1494_);
lean_dec(v_val_1490_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v_year_1494_);
v___x_1496_ = v___x_1492_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_year_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
case 3:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_time_x3f_1464_);
if (lean_obj_tag(v_date_x3f_1463_) == 0)
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_box(0);
return v___x_1499_;
}
else
{
lean_object* v_val_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1523_; 
v_val_1500_ = lean_ctor_get(v_date_x3f_1463_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_date_x3f_1463_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1502_ = v_date_x3f_1463_;
v_isShared_1503_ = v_isSharedCheck_1523_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_val_1500_);
lean_dec(v_date_x3f_1463_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1523_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
uint8_t v___y_1505_; lean_object* v_year_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; uint8_t v___x_1516_; 
v_year_1512_ = lean_ctor_get(v_val_1500_, 0);
v___x_1513_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0);
v___x_1514_ = lean_int_mod(v_year_1512_, v___x_1513_);
v___x_1515_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1516_ = lean_int_dec_eq(v___x_1514_, v___x_1515_);
lean_dec(v___x_1514_);
if (v___x_1516_ == 0)
{
v___y_1505_ = v___x_1516_;
goto v___jp_1504_;
}
else
{
lean_object* v___x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v___x_1517_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1518_ = lean_int_mod(v_year_1512_, v___x_1517_);
v___x_1519_ = lean_int_dec_eq(v___x_1518_, v___x_1515_);
lean_dec(v___x_1518_);
if (v___x_1519_ == 0)
{
v___y_1505_ = v___x_1516_;
goto v___jp_1504_;
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; 
v___x_1520_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1);
v___x_1521_ = lean_int_mod(v_year_1512_, v___x_1520_);
v___x_1522_ = lean_int_dec_eq(v___x_1521_, v___x_1515_);
lean_dec(v___x_1521_);
v___y_1505_ = v___x_1522_;
goto v___jp_1504_;
}
}
v___jp_1504_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1506_ = l_Std_Time_PlainDate_dayOfYear(v_val_1500_);
lean_dec(v_val_1500_);
v___x_1507_ = lean_box(v___y_1505_);
v___x_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
lean_ctor_set(v___x_1508_, 1, v___x_1506_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1508_);
v___x_1510_ = v___x_1502_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
case 4:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_time_x3f_1464_);
if (lean_obj_tag(v_date_x3f_1463_) == 0)
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_box(0);
return v___x_1524_;
}
else
{
lean_object* v_val_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1533_; 
v_val_1525_ = lean_ctor_get(v_date_x3f_1463_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v_date_x3f_1463_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1527_ = v_date_x3f_1463_;
v_isShared_1528_ = v_isSharedCheck_1533_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_val_1525_);
lean_dec(v_date_x3f_1463_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1533_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v_month_1529_; lean_object* v___x_1531_; 
v_month_1529_ = lean_ctor_get(v_val_1525_, 1);
lean_inc(v_month_1529_);
lean_dec(v_val_1525_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v_month_1529_);
v___x_1531_ = v___x_1527_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_month_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
case 5:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_time_x3f_1464_);
if (lean_obj_tag(v_date_x3f_1463_) == 0)
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_box(0);
return v___x_1534_;
}
else
{
lean_object* v_val_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1543_; 
v_val_1535_ = lean_ctor_get(v_date_x3f_1463_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_date_x3f_1463_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1537_ = v_date_x3f_1463_;
v_isShared_1538_ = v_isSharedCheck_1543_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_val_1535_);
lean_dec(v_date_x3f_1463_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1543_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v_month_1539_; lean_object* v___x_1541_; 
v_month_1539_ = lean_ctor_get(v_val_1535_, 1);
lean_inc(v_month_1539_);
lean_dec(v_val_1535_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v_month_1539_);
v___x_1541_ = v___x_1537_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_month_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
case 6:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_time_x3f_1464_);
if (lean_obj_tag(v_date_x3f_1463_) == 0)
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_box(0);
return v___x_1544_;
}
else
{
lean_object* v_val_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1553_; 
v_val_1545_ = lean_ctor_get(v_date_x3f_1463_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_date_x3f_1463_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1547_ = v_date_x3f_1463_;
v_isShared_1548_ = v_isSharedCheck_1553_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_val_1545_);
lean_dec(v_date_x3f_1463_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1553_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v_day_1549_; lean_object* v___x_1551_; 
v_day_1549_ = lean_ctor_get(v_val_1545_, 2);
lean_inc(v_day_1549_);
lean_dec(v_val_1545_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v_day_1549_);
v___x_1551_ = v___x_1547_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_day_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
case 7:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_time_x3f_1464_);
if (lean_obj_tag(v_date_x3f_1463_) == 0)
{
lean_object* v___x_1554_; 
v___x_1554_ = lean_box(0);
return v___x_1554_;
}
else
{
lean_object* v_val_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1563_; 
v_val_1555_ = lean_ctor_get(v_date_x3f_1463_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_date_x3f_1463_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1557_ = v_date_x3f_1463_;
v_isShared_1558_ = v_isSharedCheck_1563_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_val_1555_);
lean_dec(v_date_x3f_1463_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1563_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1559_; lean_object* v___x_1561_; 
v___x_1559_ = l_Std_Time_PlainDate_quarter(v_val_1555_);
lean_dec(v_val_1555_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 0, v___x_1559_);
v___x_1561_ = v___x_1557_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
case 8:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_time_x3f_1464_);
if (lean_obj_tag(v_date_x3f_1463_) == 0)
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_box(0);
return v___x_1564_;
}
else
{
lean_object* v_val_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1573_; 
v_val_1565_ = lean_ctor_get(v_date_x3f_1463_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_date_x3f_1463_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1567_ = v_date_x3f_1463_;
v_isShared_1568_ = v_isSharedCheck_1573_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_val_1565_);
lean_dec(v_date_x3f_1463_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1573_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1569_; lean_object* v___x_1571_; 
v___x_1569_ = l_Std_Time_PlainDate_quarter(v_val_1565_);
lean_dec(v_val_1565_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v___x_1569_);
v___x_1571_ = v___x_1567_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
case 9:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_time_x3f_1464_);
if (lean_obj_tag(v_date_x3f_1463_) == 0)
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_box(0);
return v___x_1574_;
}
else
{
uint8_t v_firstDayOfWeek_1575_; lean_object* v_minimalDaysInFirstWeek_1576_; lean_object* v_val_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1585_; 
v_firstDayOfWeek_1575_ = lean_ctor_get_uint8(v_dateformat_1462_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_1576_ = lean_ctor_get(v_dateformat_1462_, 0);
v_val_1577_ = lean_ctor_get(v_date_x3f_1463_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_date_x3f_1463_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1579_ = v_date_x3f_1463_;
v_isShared_1580_ = v_isSharedCheck_1585_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_val_1577_);
lean_dec(v_date_x3f_1463_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1585_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1581_ = l_Std_Time_PlainDate_weekYear(v_val_1577_, v_firstDayOfWeek_1575_, v_minimalDaysInFirstWeek_1576_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v___x_1581_);
v___x_1583_ = v___x_1579_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
case 10:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_time_x3f_1464_);
if (lean_obj_tag(v_date_x3f_1463_) == 0)
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_box(0);
return v___x_1586_;
}
else
{
uint8_t v_firstDayOfWeek_1587_; lean_object* v_minimalDaysInFirstWeek_1588_; lean_object* v_val_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1597_; 
v_firstDayOfWeek_1587_ = lean_ctor_get_uint8(v_dateformat_1462_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_1588_ = lean_ctor_get(v_dateformat_1462_, 0);
v_val_1589_ = lean_ctor_get(v_date_x3f_1463_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_date_x3f_1463_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1591_ = v_date_x3f_1463_;
v_isShared_1592_ = v_isSharedCheck_1597_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_val_1589_);
lean_dec(v_date_x3f_1463_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1597_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1593_ = l_Std_Time_PlainDate_weekOfYear(v_val_1589_, v_firstDayOfWeek_1587_, v_minimalDaysInFirstWeek_1588_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1593_);
v___x_1595_ = v___x_1591_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
case 11:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_time_x3f_1464_);
if (lean_obj_tag(v_date_x3f_1463_) == 0)
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_box(0);
return v___x_1598_;
}
else
{
uint8_t v_firstDayOfWeek_1599_; lean_object* v_val_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1608_; 
v_firstDayOfWeek_1599_ = lean_ctor_get_uint8(v_dateformat_1462_, sizeof(void*)*2);
v_val_1600_ = lean_ctor_get(v_date_x3f_1463_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_date_x3f_1463_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1602_ = v_date_x3f_1463_;
v_isShared_1603_ = v_isSharedCheck_1608_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_val_1600_);
lean_dec(v_date_x3f_1463_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1608_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1604_ = l_Std_Time_PlainDate_weekOfMonth(v_val_1600_, v_firstDayOfWeek_1599_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v___x_1604_);
v___x_1606_ = v___x_1602_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
case 12:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_time_x3f_1464_);
if (lean_obj_tag(v_date_x3f_1463_) == 0)
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_box(0);
return v___x_1609_;
}
else
{
lean_object* v_val_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1619_; 
v_val_1610_ = lean_ctor_get(v_date_x3f_1463_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_date_x3f_1463_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1612_ = v_date_x3f_1463_;
v_isShared_1613_ = v_isSharedCheck_1619_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_val_1610_);
lean_dec(v_date_x3f_1463_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1619_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
uint8_t v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1614_ = l_Std_Time_PlainDate_weekday(v_val_1610_);
v___x_1615_ = lean_box(v___x_1614_);
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 0, v___x_1615_);
v___x_1617_ = v___x_1612_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
case 13:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_time_x3f_1464_);
if (lean_obj_tag(v_date_x3f_1463_) == 0)
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_box(0);
return v___x_1620_;
}
else
{
lean_object* v_val_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1630_; 
v_val_1621_ = lean_ctor_get(v_date_x3f_1463_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_date_x3f_1463_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1623_ = v_date_x3f_1463_;
v_isShared_1624_ = v_isSharedCheck_1630_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_val_1621_);
lean_dec(v_date_x3f_1463_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1630_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
uint8_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1625_ = l_Std_Time_PlainDate_weekday(v_val_1621_);
v___x_1626_ = lean_box(v___x_1625_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v___x_1626_);
v___x_1628_ = v___x_1623_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
case 14:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_time_x3f_1464_);
if (lean_obj_tag(v_date_x3f_1463_) == 0)
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_box(0);
return v___x_1631_;
}
else
{
lean_object* v_val_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1641_; 
v_val_1632_ = lean_ctor_get(v_date_x3f_1463_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_date_x3f_1463_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1634_ = v_date_x3f_1463_;
v_isShared_1635_ = v_isSharedCheck_1641_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_val_1632_);
lean_dec(v_date_x3f_1463_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1641_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
uint8_t v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1639_; 
v___x_1636_ = l_Std_Time_PlainDate_weekday(v_val_1632_);
v___x_1637_ = lean_box(v___x_1636_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1637_);
v___x_1639_ = v___x_1634_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
case 15:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_time_x3f_1464_);
if (lean_obj_tag(v_date_x3f_1463_) == 0)
{
lean_object* v___x_1642_; 
v___x_1642_ = lean_box(0);
return v___x_1642_;
}
else
{
lean_object* v_val_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1651_; 
v_val_1643_ = lean_ctor_get(v_date_x3f_1463_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_date_x3f_1463_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1645_ = v_date_x3f_1463_;
v_isShared_1646_ = v_isSharedCheck_1651_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_val_1643_);
lean_dec(v_date_x3f_1463_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1651_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1647_; lean_object* v___x_1649_; 
v___x_1647_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_val_1643_);
lean_dec(v_val_1643_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1647_);
v___x_1649_ = v___x_1645_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
case 16:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_date_x3f_1463_);
if (lean_obj_tag(v_time_x3f_1464_) == 0)
{
lean_object* v___x_1652_; 
v___x_1652_ = lean_box(0);
return v___x_1652_;
}
else
{
lean_object* v_val_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1663_; 
v_val_1653_ = lean_ctor_get(v_time_x3f_1464_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_time_x3f_1464_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1655_ = v_time_x3f_1464_;
v_isShared_1656_ = v_isSharedCheck_1663_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_val_1653_);
lean_dec(v_time_x3f_1464_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1663_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v_hour_1657_; uint8_t v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1661_; 
v_hour_1657_ = lean_ctor_get(v_val_1653_, 0);
lean_inc(v_hour_1657_);
lean_dec(v_val_1653_);
v___x_1658_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1657_);
lean_dec(v_hour_1657_);
v___x_1659_ = lean_box(v___x_1658_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1659_);
v___x_1661_ = v___x_1655_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
case 17:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_date_x3f_1463_);
if (lean_obj_tag(v_time_x3f_1464_) == 0)
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_box(0);
return v___x_1664_;
}
else
{
lean_object* v_val_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1677_; 
v_val_1665_ = lean_ctor_get(v_time_x3f_1464_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_time_x3f_1464_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1667_ = v_time_x3f_1464_;
v_isShared_1668_ = v_isSharedCheck_1677_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_val_1665_);
lean_dec(v_time_x3f_1464_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1677_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v_hour_1669_; lean_object* v_minute_1670_; lean_object* v_second_1671_; uint8_t v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
v_hour_1669_ = lean_ctor_get(v_val_1665_, 0);
lean_inc(v_hour_1669_);
v_minute_1670_ = lean_ctor_get(v_val_1665_, 1);
lean_inc(v_minute_1670_);
v_second_1671_ = lean_ctor_get(v_val_1665_, 2);
lean_inc(v_second_1671_);
lean_dec(v_val_1665_);
v___x_1672_ = l_Std_Time_classifyDayPeriod(v_hour_1669_, v_minute_1670_, v_second_1671_);
lean_dec(v_second_1671_);
lean_dec(v_minute_1670_);
lean_dec(v_hour_1669_);
v___x_1673_ = lean_box(v___x_1672_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v___x_1673_);
v___x_1675_ = v___x_1667_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
case 18:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_date_x3f_1463_);
if (lean_obj_tag(v_time_x3f_1464_) == 0)
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_box(0);
return v___x_1678_;
}
else
{
lean_object* v_val_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1691_; 
v_val_1679_ = lean_ctor_get(v_time_x3f_1464_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_time_x3f_1464_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1681_ = v_time_x3f_1464_;
v_isShared_1682_ = v_isSharedCheck_1691_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_val_1679_);
lean_dec(v_time_x3f_1464_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1691_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v_hour_1683_; lean_object* v_minute_1684_; lean_object* v_second_1685_; uint8_t v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1689_; 
v_hour_1683_ = lean_ctor_get(v_val_1679_, 0);
lean_inc(v_hour_1683_);
v_minute_1684_ = lean_ctor_get(v_val_1679_, 1);
lean_inc(v_minute_1684_);
v_second_1685_ = lean_ctor_get(v_val_1679_, 2);
lean_inc(v_second_1685_);
lean_dec(v_val_1679_);
v___x_1686_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1683_, v_minute_1684_, v_second_1685_);
lean_dec(v_second_1685_);
lean_dec(v_minute_1684_);
lean_dec(v_hour_1683_);
v___x_1687_ = lean_box(v___x_1686_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v___x_1687_);
v___x_1689_ = v___x_1681_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
case 19:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_date_x3f_1463_);
if (lean_obj_tag(v_time_x3f_1464_) == 0)
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_box(0);
return v___x_1692_;
}
else
{
lean_object* v_val_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1702_; 
v_val_1693_ = lean_ctor_get(v_time_x3f_1464_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_time_x3f_1464_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1695_ = v_time_x3f_1464_;
v_isShared_1696_ = v_isSharedCheck_1702_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_val_1693_);
lean_dec(v_time_x3f_1464_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1702_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v_hour_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
v_hour_1697_ = lean_ctor_get(v_val_1693_, 0);
lean_inc(v_hour_1697_);
lean_dec(v_val_1693_);
v___x_1698_ = l_Std_Time_Hour_Ordinal_toRelative(v_hour_1697_);
lean_dec(v_hour_1697_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 0, v___x_1698_);
v___x_1700_ = v___x_1695_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
case 20:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_date_x3f_1463_);
if (lean_obj_tag(v_time_x3f_1464_) == 0)
{
lean_object* v___x_1703_; 
v___x_1703_ = lean_box(0);
return v___x_1703_;
}
else
{
lean_object* v_val_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1714_; 
v_val_1704_ = lean_ctor_get(v_time_x3f_1464_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_time_x3f_1464_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1706_ = v_time_x3f_1464_;
v_isShared_1707_ = v_isSharedCheck_1714_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_val_1704_);
lean_dec(v_time_x3f_1464_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1714_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v_hour_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1712_; 
v_hour_1708_ = lean_ctor_get(v_val_1704_, 0);
lean_inc(v_hour_1708_);
lean_dec(v_val_1704_);
v___x_1709_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1710_ = lean_int_emod(v_hour_1708_, v___x_1709_);
lean_dec(v_hour_1708_);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 0, v___x_1710_);
v___x_1712_ = v___x_1706_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
case 21:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_date_x3f_1463_);
if (lean_obj_tag(v_time_x3f_1464_) == 0)
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_box(0);
return v___x_1715_;
}
else
{
lean_object* v_val_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1725_; 
v_val_1716_ = lean_ctor_get(v_time_x3f_1464_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_time_x3f_1464_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1718_ = v_time_x3f_1464_;
v_isShared_1719_ = v_isSharedCheck_1725_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_val_1716_);
lean_dec(v_time_x3f_1464_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1725_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v_hour_1720_; lean_object* v___x_1721_; lean_object* v___x_1723_; 
v_hour_1720_ = lean_ctor_get(v_val_1716_, 0);
lean_inc(v_hour_1720_);
lean_dec(v_val_1716_);
v___x_1721_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_1720_);
lean_dec(v_hour_1720_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1721_);
v___x_1723_ = v___x_1718_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
case 22:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_date_x3f_1463_);
if (lean_obj_tag(v_time_x3f_1464_) == 0)
{
lean_object* v___x_1726_; 
v___x_1726_ = lean_box(0);
return v___x_1726_;
}
else
{
lean_object* v_val_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1735_; 
v_val_1727_ = lean_ctor_get(v_time_x3f_1464_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_time_x3f_1464_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1729_ = v_time_x3f_1464_;
v_isShared_1730_ = v_isSharedCheck_1735_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_val_1727_);
lean_dec(v_time_x3f_1464_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1735_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v_hour_1731_; lean_object* v___x_1733_; 
v_hour_1731_ = lean_ctor_get(v_val_1727_, 0);
lean_inc(v_hour_1731_);
lean_dec(v_val_1727_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 0, v_hour_1731_);
v___x_1733_ = v___x_1729_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_hour_1731_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
case 23:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_date_x3f_1463_);
if (lean_obj_tag(v_time_x3f_1464_) == 0)
{
lean_object* v___x_1736_; 
v___x_1736_ = lean_box(0);
return v___x_1736_;
}
else
{
lean_object* v_val_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1745_; 
v_val_1737_ = lean_ctor_get(v_time_x3f_1464_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_time_x3f_1464_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1739_ = v_time_x3f_1464_;
v_isShared_1740_ = v_isSharedCheck_1745_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_val_1737_);
lean_dec(v_time_x3f_1464_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1745_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v_minute_1741_; lean_object* v___x_1743_; 
v_minute_1741_ = lean_ctor_get(v_val_1737_, 1);
lean_inc(v_minute_1741_);
lean_dec(v_val_1737_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v_minute_1741_);
v___x_1743_ = v___x_1739_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_minute_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
case 24:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_date_x3f_1463_);
if (lean_obj_tag(v_time_x3f_1464_) == 0)
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_box(0);
return v___x_1746_;
}
else
{
lean_object* v_val_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1755_; 
v_val_1747_ = lean_ctor_get(v_time_x3f_1464_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_time_x3f_1464_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1749_ = v_time_x3f_1464_;
v_isShared_1750_ = v_isSharedCheck_1755_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_val_1747_);
lean_dec(v_time_x3f_1464_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1755_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v_second_1751_; lean_object* v___x_1753_; 
v_second_1751_ = lean_ctor_get(v_val_1747_, 2);
lean_inc(v_second_1751_);
lean_dec(v_val_1747_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v_second_1751_);
v___x_1753_ = v___x_1749_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_second_1751_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
case 25:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_date_x3f_1463_);
if (lean_obj_tag(v_time_x3f_1464_) == 0)
{
lean_object* v___x_1756_; 
v___x_1756_ = lean_box(0);
return v___x_1756_;
}
else
{
lean_object* v_val_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1765_; 
v_val_1757_ = lean_ctor_get(v_time_x3f_1464_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v_time_x3f_1464_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1759_ = v_time_x3f_1464_;
v_isShared_1760_ = v_isSharedCheck_1765_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_val_1757_);
lean_dec(v_time_x3f_1464_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1765_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v_nanosecond_1761_; lean_object* v___x_1763_; 
v_nanosecond_1761_ = lean_ctor_get(v_val_1757_, 3);
lean_inc(v_nanosecond_1761_);
lean_dec(v_val_1757_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v_nanosecond_1761_);
v___x_1763_ = v___x_1759_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_nanosecond_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
case 26:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_date_x3f_1463_);
if (lean_obj_tag(v_time_x3f_1464_) == 0)
{
lean_object* v___x_1766_; 
v___x_1766_ = lean_box(0);
return v___x_1766_;
}
else
{
lean_object* v_val_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1775_; 
v_val_1767_ = lean_ctor_get(v_time_x3f_1464_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_time_x3f_1464_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1769_ = v_time_x3f_1464_;
v_isShared_1770_ = v_isSharedCheck_1775_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_val_1767_);
lean_dec(v_time_x3f_1464_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1775_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1771_ = l_Std_Time_PlainTime_toMilliseconds(v_val_1767_);
lean_dec(v_val_1767_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1771_);
v___x_1773_ = v___x_1769_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
case 27:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_date_x3f_1463_);
if (lean_obj_tag(v_time_x3f_1464_) == 0)
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_box(0);
return v___x_1776_;
}
else
{
lean_object* v_val_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1785_; 
v_val_1777_ = lean_ctor_get(v_time_x3f_1464_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_time_x3f_1464_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1779_ = v_time_x3f_1464_;
v_isShared_1780_ = v_isSharedCheck_1785_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_val_1777_);
lean_dec(v_time_x3f_1464_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1785_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v_nanosecond_1781_; lean_object* v___x_1783_; 
v_nanosecond_1781_ = lean_ctor_get(v_val_1777_, 3);
lean_inc(v_nanosecond_1781_);
lean_dec(v_val_1777_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v_nanosecond_1781_);
v___x_1783_ = v___x_1779_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_nanosecond_1781_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
case 28:
{
lean_dec(v_zone_x3f_1465_);
lean_dec(v_date_x3f_1463_);
if (lean_obj_tag(v_time_x3f_1464_) == 0)
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_box(0);
return v___x_1786_;
}
else
{
lean_object* v_val_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1795_; 
v_val_1787_ = lean_ctor_get(v_time_x3f_1464_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_time_x3f_1464_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1789_ = v_time_x3f_1464_;
v_isShared_1790_ = v_isSharedCheck_1795_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_val_1787_);
lean_dec(v_time_x3f_1464_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1795_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1791_ = l_Std_Time_PlainTime_toNanoseconds(v_val_1787_);
lean_dec(v_val_1787_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1791_);
v___x_1793_ = v___x_1789_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
case 29:
{
uint8_t v_presentation_1796_; 
lean_dec(v_time_x3f_1464_);
lean_dec(v_date_x3f_1463_);
v_presentation_1796_ = lean_ctor_get_uint8(v_modifier_1466_, 0);
if (v_presentation_1796_ == 0)
{
if (lean_obj_tag(v_zone_x3f_1465_) == 0)
{
lean_object* v___x_1797_; 
v___x_1797_ = lean_box(0);
return v___x_1797_;
}
else
{
lean_object* v___x_1798_; 
lean_dec_ref_known(v_zone_x3f_1465_, 1);
v___x_1798_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__2));
return v___x_1798_;
}
}
else
{
if (lean_obj_tag(v_zone_x3f_1465_) == 0)
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_box(0);
return v___x_1799_;
}
else
{
lean_object* v_val_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1810_; 
v_val_1800_ = lean_ctor_get(v_zone_x3f_1465_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_zone_x3f_1465_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1802_ = v_zone_x3f_1465_;
v_isShared_1803_ = v_isSharedCheck_1810_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_val_1800_);
lean_dec(v_zone_x3f_1465_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1810_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v_offset_1804_; lean_object* v_name_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
v_offset_1804_ = lean_ctor_get(v_val_1800_, 0);
lean_inc(v_offset_1804_);
v_name_1805_ = lean_ctor_get(v_val_1800_, 1);
lean_inc_ref(v_name_1805_);
lean_dec(v_val_1800_);
v___x_1806_ = l___private_Std_Time_Format_Basic_0__Std_Time_zoneLabel(v_name_1805_, v_offset_1804_);
lean_dec_ref(v_name_1805_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1806_);
v___x_1808_ = v___x_1802_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
case 30:
{
uint8_t v_presentation_1811_; 
lean_dec(v_time_x3f_1464_);
lean_dec(v_date_x3f_1463_);
v_presentation_1811_ = lean_ctor_get_uint8(v_modifier_1466_, 0);
if (v_presentation_1811_ == 0)
{
if (lean_obj_tag(v_zone_x3f_1465_) == 0)
{
lean_object* v___x_1812_; 
v___x_1812_ = lean_box(0);
return v___x_1812_;
}
else
{
lean_object* v_val_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1823_; 
v_val_1813_ = lean_ctor_get(v_zone_x3f_1465_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_zone_x3f_1465_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1815_ = v_zone_x3f_1465_;
v_isShared_1816_ = v_isSharedCheck_1823_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_val_1813_);
lean_dec(v_zone_x3f_1465_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1823_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v_offset_1817_; lean_object* v_abbreviation_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; 
v_offset_1817_ = lean_ctor_get(v_val_1813_, 0);
lean_inc(v_offset_1817_);
v_abbreviation_1818_ = lean_ctor_get(v_val_1813_, 2);
lean_inc_ref(v_abbreviation_1818_);
lean_dec(v_val_1813_);
v___x_1819_ = l___private_Std_Time_Format_Basic_0__Std_Time_zoneLabel(v_abbreviation_1818_, v_offset_1817_);
lean_dec_ref(v_abbreviation_1818_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1819_);
v___x_1821_ = v___x_1815_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
else
{
if (lean_obj_tag(v_zone_x3f_1465_) == 0)
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_box(0);
return v___x_1824_;
}
else
{
lean_object* v_val_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1835_; 
v_val_1825_ = lean_ctor_get(v_zone_x3f_1465_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_zone_x3f_1465_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1827_ = v_zone_x3f_1465_;
v_isShared_1828_ = v_isSharedCheck_1835_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_val_1825_);
lean_dec(v_zone_x3f_1465_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1835_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_offset_1829_; lean_object* v_name_1830_; lean_object* v___x_1831_; lean_object* v___x_1833_; 
v_offset_1829_ = lean_ctor_get(v_val_1825_, 0);
lean_inc(v_offset_1829_);
v_name_1830_ = lean_ctor_get(v_val_1825_, 1);
lean_inc_ref(v_name_1830_);
lean_dec(v_val_1825_);
v___x_1831_ = l___private_Std_Time_Format_Basic_0__Std_Time_zoneLabel(v_name_1830_, v_offset_1829_);
lean_dec_ref(v_name_1830_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1831_);
v___x_1833_ = v___x_1827_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
}
case 31:
{
uint8_t v_presentation_1836_; 
lean_dec(v_time_x3f_1464_);
lean_dec(v_date_x3f_1463_);
v_presentation_1836_ = lean_ctor_get_uint8(v_modifier_1466_, 0);
if (v_presentation_1836_ == 0)
{
if (lean_obj_tag(v_zone_x3f_1465_) == 0)
{
lean_object* v___x_1837_; 
v___x_1837_ = lean_box(0);
return v___x_1837_;
}
else
{
lean_object* v_val_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1848_; 
v_val_1838_ = lean_ctor_get(v_zone_x3f_1465_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_zone_x3f_1465_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1840_ = v_zone_x3f_1465_;
v_isShared_1841_ = v_isSharedCheck_1848_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_val_1838_);
lean_dec(v_zone_x3f_1465_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1848_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v_offset_1842_; lean_object* v_abbreviation_1843_; lean_object* v___x_1844_; lean_object* v___x_1846_; 
v_offset_1842_ = lean_ctor_get(v_val_1838_, 0);
lean_inc(v_offset_1842_);
v_abbreviation_1843_ = lean_ctor_get(v_val_1838_, 2);
lean_inc_ref(v_abbreviation_1843_);
lean_dec(v_val_1838_);
v___x_1844_ = l___private_Std_Time_Format_Basic_0__Std_Time_zoneLabel(v_abbreviation_1843_, v_offset_1842_);
lean_dec_ref(v_abbreviation_1843_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1844_);
v___x_1846_ = v___x_1840_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
else
{
if (lean_obj_tag(v_zone_x3f_1465_) == 0)
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_box(0);
return v___x_1849_;
}
else
{
lean_object* v_val_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1860_; 
v_val_1850_ = lean_ctor_get(v_zone_x3f_1465_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_zone_x3f_1465_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1852_ = v_zone_x3f_1465_;
v_isShared_1853_ = v_isSharedCheck_1860_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_val_1850_);
lean_dec(v_zone_x3f_1465_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1860_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v_offset_1854_; lean_object* v_name_1855_; lean_object* v___x_1856_; lean_object* v___x_1858_; 
v_offset_1854_ = lean_ctor_get(v_val_1850_, 0);
lean_inc(v_offset_1854_);
v_name_1855_ = lean_ctor_get(v_val_1850_, 1);
lean_inc_ref(v_name_1855_);
lean_dec(v_val_1850_);
v___x_1856_ = l___private_Std_Time_Format_Basic_0__Std_Time_zoneLabel(v_name_1855_, v_offset_1854_);
lean_dec_ref(v_name_1855_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v___x_1856_);
v___x_1858_ = v___x_1852_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
default: 
{
lean_dec(v_time_x3f_1464_);
lean_dec(v_date_x3f_1463_);
if (lean_obj_tag(v_zone_x3f_1465_) == 0)
{
lean_object* v___x_1861_; 
v___x_1861_ = lean_box(0);
return v___x_1861_;
}
else
{
lean_object* v_val_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1870_; 
v_val_1862_ = lean_ctor_get(v_zone_x3f_1465_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v_zone_x3f_1465_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1864_ = v_zone_x3f_1465_;
v_isShared_1865_ = v_isSharedCheck_1870_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_val_1862_);
lean_dec(v_zone_x3f_1465_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1870_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v_offset_1866_; lean_object* v___x_1868_; 
v_offset_1866_ = lean_ctor_get(v_val_1862_, 0);
lean_inc(v_offset_1866_);
lean_dec(v_val_1862_);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v_offset_1866_);
v___x_1868_ = v___x_1864_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_offset_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___boxed(lean_object* v_dateformat_1871_, lean_object* v_date_x3f_1872_, lean_object* v_time_x3f_1873_, lean_object* v_zone_x3f_1874_, lean_object* v_modifier_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f(v_dateformat_1871_, v_date_x3f_1872_, v_time_x3f_1873_, v_zone_x3f_1874_, v_modifier_1875_);
lean_dec_ref(v_modifier_1875_);
lean_dec_ref(v_dateformat_1871_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___lam__0(lean_object* v___x_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1877_);
v___x_1880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___y_1878_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___lam__0(lean_object* v___x_1881_, lean_object* v_b_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_fst_1884_; lean_object* v_snd_1885_; lean_object* v___x_1886_; 
v_fst_1884_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_fst_1884_);
v_snd_1885_ = lean_ctor_get(v___x_1881_, 1);
lean_inc(v_snd_1885_);
lean_dec_ref(v___x_1881_);
lean_inc_ref(v___y_1883_);
v___x_1886_ = lean_apply_1(v_b_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_dec(v_snd_1885_);
lean_dec(v_fst_1884_);
lean_dec_ref(v___y_1883_);
return v___x_1886_;
}
else
{
lean_object* v_pos_1887_; lean_object* v_snd_1888_; lean_object* v_snd_1889_; uint8_t v_decide_1890_; 
v_pos_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_pos_1887_);
v_snd_1888_ = lean_ctor_get(v___y_1883_, 1);
lean_inc(v_snd_1888_);
lean_dec_ref(v___y_1883_);
v_snd_1889_ = lean_ctor_get(v_pos_1887_, 1);
v_decide_1890_ = lean_nat_dec_eq(v_snd_1888_, v_snd_1889_);
lean_dec(v_snd_1888_);
if (v_decide_1890_ == 0)
{
lean_dec(v_pos_1887_);
lean_dec(v_snd_1885_);
lean_dec(v_fst_1884_);
return v___x_1886_;
}
else
{
lean_object* v___x_1891_; 
lean_dec_ref_known(v___x_1886_, 2);
v___x_1891_ = l_Std_Internal_Parsec_String_pstring(v_fst_1884_, v_pos_1887_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_pos_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
v_pos_1892_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; 
v_unused_1900_ = lean_ctor_get(v___x_1891_, 1);
lean_dec(v_unused_1900_);
v___x_1894_ = v___x_1891_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_pos_1892_);
lean_dec(v___x_1891_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 1, v_snd_1885_);
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_pos_1892_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_snd_1885_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
else
{
lean_object* v_pos_1901_; lean_object* v_err_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec(v_snd_1885_);
v_pos_1901_ = lean_ctor_get(v___x_1891_, 0);
v_err_1902_ = lean_ctor_get(v___x_1891_, 1);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1891_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_err_1902_);
lean_inc(v_pos_1901_);
lean_dec(v___x_1891_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_pos_1901_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_err_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(lean_object* v_as_1910_, size_t v_i_1911_, size_t v_stop_1912_, lean_object* v_b_1913_, lean_object* v___y_1914_){
_start:
{
uint8_t v___x_1915_; 
v___x_1915_ = lean_usize_dec_eq(v_i_1911_, v_stop_1912_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; lean_object* v___f_1917_; size_t v___x_1918_; size_t v___x_1919_; 
v___x_1916_ = lean_array_uget_borrowed(v_as_1910_, v_i_1911_);
lean_inc(v___x_1916_);
v___f_1917_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1917_, 0, v___x_1916_);
lean_closure_set(v___f_1917_, 1, v_b_1913_);
v___x_1918_ = ((size_t)1ULL);
v___x_1919_ = lean_usize_add(v_i_1911_, v___x_1918_);
v_i_1911_ = v___x_1919_;
v_b_1913_ = v___f_1917_;
goto _start;
}
else
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_apply_1(v_b_1913_, v___y_1914_);
return v___x_1921_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___boxed(lean_object* v_as_1922_, lean_object* v_i_1923_, lean_object* v_stop_1924_, lean_object* v_b_1925_, lean_object* v___y_1926_){
_start:
{
size_t v_i_boxed_1927_; size_t v_stop_boxed_1928_; lean_object* v_res_1929_; 
v_i_boxed_1927_ = lean_unbox_usize(v_i_1923_);
lean_dec(v_i_1923_);
v_stop_boxed_1928_ = lean_unbox_usize(v_stop_1924_);
lean_dec(v_stop_1924_);
v_res_1929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_as_1922_, v_i_boxed_1927_, v_stop_boxed_1928_, v_b_1925_, v___y_1926_);
lean_dec_ref(v_as_1922_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(lean_object* v_pairs_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1937_ = lean_unsigned_to_nat(0u);
v___x_1938_ = lean_array_get_size(v_pairs_1935_);
v___x_1939_ = lean_nat_dec_lt(v___x_1937_, v___x_1938_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__1));
v___x_1941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1941_, 0, v_a_1936_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
return v___x_1941_;
}
else
{
lean_object* v___f_1942_; size_t v___x_1943_; size_t v___x_1944_; lean_object* v___x_1945_; 
v___f_1942_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__2));
v___x_1943_ = ((size_t)0ULL);
v___x_1944_ = lean_usize_of_nat(v___x_1938_);
v___x_1945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_pairs_1935_, v___x_1943_, v___x_1944_, v___f_1942_, v_a_1936_);
return v___x_1945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___boxed(lean_object* v_pairs_1946_, lean_object* v_a_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_1946_, v_a_1947_);
lean_dec_ref(v_pairs_1946_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols(lean_object* v_00_u03b1_1949_, lean_object* v_pairs_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_1950_, v_a_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___boxed(lean_object* v_00_u03b1_1953_, lean_object* v_pairs_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols(v_00_u03b1_1953_, v_pairs_1954_, v_a_1955_);
lean_dec_ref(v_pairs_1954_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0(lean_object* v_00_u03b1_1957_, lean_object* v_as_1958_, size_t v_i_1959_, size_t v_stop_1960_, lean_object* v_b_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_as_1958_, v_i_1959_, v_stop_1960_, v_b_1961_, v___y_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___boxed(lean_object* v_00_u03b1_1964_, lean_object* v_as_1965_, lean_object* v_i_1966_, lean_object* v_stop_1967_, lean_object* v_b_1968_, lean_object* v___y_1969_){
_start:
{
size_t v_i_boxed_1970_; size_t v_stop_boxed_1971_; lean_object* v_res_1972_; 
v_i_boxed_1970_ = lean_unbox_usize(v_i_1966_);
lean_dec(v_i_1966_);
v_stop_boxed_1971_ = lean_unbox_usize(v_stop_1967_);
lean_dec(v_stop_1967_);
v_res_1972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0(v_00_u03b1_1964_, v_as_1965_, v_i_boxed_1970_, v_stop_boxed_1971_, v_b_1968_, v___y_1969_);
lean_dec_ref(v_as_1965_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseName_spec__0___redArg(size_t v_sz_1973_, size_t v_i_1974_, lean_object* v_bs_1975_){
_start:
{
uint8_t v___x_1976_; 
v___x_1976_ = lean_usize_dec_lt(v_i_1974_, v_sz_1973_);
if (v___x_1976_ == 0)
{
return v_bs_1975_;
}
else
{
lean_object* v_v_1977_; lean_object* v___x_1978_; lean_object* v_bs_x27_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; size_t v___x_1982_; size_t v___x_1983_; lean_object* v___x_1984_; 
v_v_1977_ = lean_array_uget(v_bs_1975_, v_i_1974_);
v___x_1978_ = lean_unsigned_to_nat(0u);
v_bs_x27_1979_ = lean_array_uset(v_bs_1975_, v_i_1974_, v___x_1978_);
v___x_1980_ = lean_usize_to_nat(v_i_1974_);
v___x_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1981_, 0, v_v_1977_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
v___x_1982_ = ((size_t)1ULL);
v___x_1983_ = lean_usize_add(v_i_1974_, v___x_1982_);
v___x_1984_ = lean_array_uset(v_bs_x27_1979_, v_i_1974_, v___x_1981_);
v_i_1974_ = v___x_1983_;
v_bs_1975_ = v___x_1984_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseName_spec__0___redArg___boxed(lean_object* v_sz_1986_, lean_object* v_i_1987_, lean_object* v_bs_1988_){
_start:
{
size_t v_sz_boxed_1989_; size_t v_i_boxed_1990_; lean_object* v_res_1991_; 
v_sz_boxed_1989_ = lean_unbox_usize(v_sz_1986_);
lean_dec(v_sz_1986_);
v_i_boxed_1990_ = lean_unbox_usize(v_i_1987_);
lean_dec(v_i_1987_);
v_res_1991_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseName_spec__0___redArg(v_sz_boxed_1989_, v_i_boxed_1990_, v_bs_1988_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseName(lean_object* v_n_1992_, lean_object* v_names_1993_, lean_object* v_a_1994_){
_start:
{
size_t v_sz_1995_; size_t v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v_sz_1995_ = lean_array_size(v_names_1993_);
v___x_1996_ = ((size_t)0ULL);
v___x_1997_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseName_spec__0___redArg(v_sz_1995_, v___x_1996_, v_names_1993_);
v___x_1998_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_1997_, v_a_1994_);
lean_dec_ref(v___x_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseName___boxed(lean_object* v_n_1999_, lean_object* v_names_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseName(v_n_1999_, v_names_2000_, v_a_2001_);
lean_dec(v_n_1999_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseName_spec__0(lean_object* v_n_2003_, lean_object* v_as_2004_, size_t v_sz_2005_, size_t v_i_2006_, lean_object* v_bs_2007_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseName_spec__0___redArg(v_sz_2005_, v_i_2006_, v_bs_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseName_spec__0___boxed(lean_object* v_n_2009_, lean_object* v_as_2010_, lean_object* v_sz_2011_, lean_object* v_i_2012_, lean_object* v_bs_2013_){
_start:
{
size_t v_sz_boxed_2014_; size_t v_i_boxed_2015_; lean_object* v_res_2016_; 
v_sz_boxed_2014_ = lean_unbox_usize(v_sz_2011_);
lean_dec(v_sz_2011_);
v_i_boxed_2015_ = lean_unbox_usize(v_i_2012_);
lean_dec(v_i_2012_);
v_res_2016_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseName_spec__0(v_n_2009_, v_as_2010_, v_sz_boxed_2014_, v_i_boxed_2015_, v_bs_2013_);
lean_dec_ref(v_as_2010_);
lean_dec(v_n_2009_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseMonthShort(lean_object* v_symbols_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v_monthShort_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v_monthShort_2019_ = lean_ctor_get(v_symbols_2017_, 1);
lean_inc_ref(v_monthShort_2019_);
lean_dec_ref(v_symbols_2017_);
v___x_2020_ = lean_unsigned_to_nat(12u);
v___x_2021_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseName(v___x_2020_, v_monthShort_2019_, v_a_2018_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_pos_2022_; lean_object* v_res_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2031_; 
v_pos_2022_ = lean_ctor_get(v___x_2021_, 0);
v_res_2023_ = lean_ctor_get(v___x_2021_, 1);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2025_ = v___x_2021_;
v_isShared_2026_ = v_isSharedCheck_2031_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_res_2023_);
lean_inc(v_pos_2022_);
lean_dec(v___x_2021_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2031_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2027_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthOfIndex(v_res_2023_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 1, v___x_2027_);
v___x_2029_ = v___x_2025_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_pos_2022_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
else
{
lean_object* v_pos_2032_; lean_object* v_err_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
v_pos_2032_ = lean_ctor_get(v___x_2021_, 0);
v_err_2033_ = lean_ctor_get(v___x_2021_, 1);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_2021_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_err_2033_);
lean_inc(v_pos_2032_);
lean_dec(v___x_2021_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_pos_2032_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_err_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(lean_object* v_parse_2041_, lean_object* v_size_2042_, lean_object* v_acc_2043_, lean_object* v_count_2044_, lean_object* v_a_2045_){
_start:
{
uint8_t v___x_2046_; 
v___x_2046_ = lean_nat_dec_le(v_size_2042_, v_count_2044_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; 
lean_inc_ref(v_parse_2041_);
v___x_2047_ = lean_apply_1(v_parse_2041_, v_a_2045_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_pos_2048_; lean_object* v_res_2049_; uint32_t v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v_pos_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_pos_2048_);
v_res_2049_ = lean_ctor_get(v___x_2047_, 1);
lean_inc(v_res_2049_);
lean_dec_ref_known(v___x_2047_, 2);
v___x_2050_ = lean_unbox_uint32(v_res_2049_);
lean_dec(v_res_2049_);
v___x_2051_ = lean_string_push(v_acc_2043_, v___x_2050_);
v___x_2052_ = lean_unsigned_to_nat(1u);
v___x_2053_ = lean_nat_add(v_count_2044_, v___x_2052_);
lean_dec(v_count_2044_);
v_acc_2043_ = v___x_2051_;
v_count_2044_ = v___x_2053_;
v_a_2045_ = v_pos_2048_;
goto _start;
}
else
{
lean_object* v_pos_2055_; lean_object* v_err_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec(v_count_2044_);
lean_dec_ref(v_acc_2043_);
lean_dec_ref(v_parse_2041_);
v_pos_2055_ = lean_ctor_get(v___x_2047_, 0);
v_err_2056_ = lean_ctor_get(v___x_2047_, 1);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2047_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_err_2056_);
lean_inc(v_pos_2055_);
lean_dec(v___x_2047_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_pos_2055_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_err_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
else
{
lean_object* v___x_2064_; 
lean_dec(v_count_2044_);
lean_dec_ref(v_parse_2041_);
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v_a_2045_);
lean_ctor_set(v___x_2064_, 1, v_acc_2043_);
return v___x_2064_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go___boxed(lean_object* v_parse_2065_, lean_object* v_size_2066_, lean_object* v_acc_2067_, lean_object* v_count_2068_, lean_object* v_a_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(v_parse_2065_, v_size_2066_, v_acc_2067_, v_count_2068_, v_a_2069_);
lean_dec(v_size_2066_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(lean_object* v_parse_2071_, lean_object* v_size_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2074_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_2075_ = lean_unsigned_to_nat(0u);
v___x_2076_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(v_parse_2071_, v_size_2072_, v___x_2074_, v___x_2075_, v_a_2073_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars___boxed(lean_object* v_parse_2077_, lean_object* v_size_2078_, lean_object* v_a_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v_parse_2077_, v_size_2078_, v_a_2079_);
lean_dec(v_size_2078_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(lean_object* v_parser_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v_pos_2084_; lean_object* v_res_2085_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
lean_inc_ref(v_a_2082_);
v___x_2118_ = l_Std_Internal_Parsec_String_pstring(v___x_2117_, v_a_2082_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_pos_2119_; lean_object* v_res_2120_; lean_object* v___x_2121_; 
lean_dec_ref(v_a_2082_);
v_pos_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_pos_2119_);
v_res_2120_ = lean_ctor_get(v___x_2118_, 1);
lean_inc(v_res_2120_);
lean_dec_ref_known(v___x_2118_, 2);
v___x_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2121_, 0, v_res_2120_);
v_pos_2084_ = v_pos_2119_;
v_res_2085_ = v___x_2121_;
goto v___jp_2083_;
}
else
{
lean_object* v_pos_2122_; lean_object* v_err_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2134_; 
v_pos_2122_ = lean_ctor_get(v___x_2118_, 0);
v_err_2123_ = lean_ctor_get(v___x_2118_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2125_ = v___x_2118_;
v_isShared_2126_ = v_isSharedCheck_2134_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_err_2123_);
lean_inc(v_pos_2122_);
lean_dec(v___x_2118_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2134_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v_snd_2127_; lean_object* v_snd_2128_; uint8_t v_decide_2129_; 
v_snd_2127_ = lean_ctor_get(v_a_2082_, 1);
lean_inc(v_snd_2127_);
lean_dec_ref(v_a_2082_);
v_snd_2128_ = lean_ctor_get(v_pos_2122_, 1);
v_decide_2129_ = lean_nat_dec_eq(v_snd_2127_, v_snd_2128_);
lean_dec(v_snd_2127_);
if (v_decide_2129_ == 0)
{
lean_object* v___x_2131_; 
lean_dec_ref(v_parser_2081_);
if (v_isShared_2126_ == 0)
{
v___x_2131_ = v___x_2125_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_pos_2122_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_err_2123_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
else
{
lean_object* v___x_2133_; 
lean_del_object(v___x_2125_);
lean_dec(v_err_2123_);
v___x_2133_ = lean_box(0);
v_pos_2084_ = v_pos_2122_;
v_res_2085_ = v___x_2133_;
goto v___jp_2083_;
}
}
}
v___jp_2083_:
{
lean_object* v___x_2086_; 
v___x_2086_ = lean_apply_1(v_parser_2081_, v_pos_2084_);
if (lean_obj_tag(v___x_2086_) == 0)
{
if (lean_obj_tag(v_res_2085_) == 0)
{
lean_object* v_pos_2087_; lean_object* v_res_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2096_; 
v_pos_2087_ = lean_ctor_get(v___x_2086_, 0);
v_res_2088_ = lean_ctor_get(v___x_2086_, 1);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2090_ = v___x_2086_;
v_isShared_2091_ = v_isSharedCheck_2096_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_res_2088_);
lean_inc(v_pos_2087_);
lean_dec(v___x_2086_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2096_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2092_; lean_object* v___x_2094_; 
v___x_2092_ = lean_nat_to_int(v_res_2088_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 1, v___x_2092_);
v___x_2094_ = v___x_2090_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_pos_2087_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
else
{
lean_object* v_pos_2097_; lean_object* v_res_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2107_; 
lean_dec_ref_known(v_res_2085_, 1);
v_pos_2097_ = lean_ctor_get(v___x_2086_, 0);
v_res_2098_ = lean_ctor_get(v___x_2086_, 1);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2100_ = v___x_2086_;
v_isShared_2101_ = v_isSharedCheck_2107_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_res_2098_);
lean_inc(v_pos_2097_);
lean_dec(v___x_2086_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2107_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2102_ = lean_nat_to_int(v_res_2098_);
v___x_2103_ = lean_int_neg(v___x_2102_);
lean_dec(v___x_2102_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 1, v___x_2103_);
v___x_2105_ = v___x_2100_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_pos_2097_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
else
{
lean_object* v_pos_2108_; lean_object* v_err_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec(v_res_2085_);
v_pos_2108_ = lean_ctor_get(v___x_2086_, 0);
v_err_2109_ = lean_ctor_get(v___x_2086_, 1);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2086_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_err_2109_);
lean_inc(v_pos_2108_);
lean_dec(v___x_2086_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_pos_2108_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_err_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum_go(lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v_zero_2141_; uint8_t v_isZero_2142_; 
v_zero_2141_ = lean_unsigned_to_nat(0u);
v_isZero_2142_ = lean_nat_dec_eq(v_a_2135_, v_zero_2141_);
if (v_isZero_2142_ == 1)
{
lean_object* v___x_2143_; 
lean_dec(v_a_2135_);
v___x_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2143_, 0, v_a_2137_);
lean_ctor_set(v___x_2143_, 1, v_a_2136_);
return v___x_2143_;
}
else
{
lean_object* v_fst_2144_; lean_object* v_snd_2145_; lean_object* v___x_2146_; uint8_t v_decide_2147_; 
v_fst_2144_ = lean_ctor_get(v_a_2137_, 0);
v_snd_2145_ = lean_ctor_get(v_a_2137_, 1);
v___x_2146_ = lean_string_utf8_byte_size(v_fst_2144_);
v_decide_2147_ = lean_nat_dec_eq(v_snd_2145_, v___x_2146_);
if (v_decide_2147_ == 0)
{
uint32_t v_c_2148_; uint32_t v___x_2149_; uint8_t v___x_2150_; 
v_c_2148_ = lean_string_utf8_get_fast(v_fst_2144_, v_snd_2145_);
v___x_2149_ = 48;
v___x_2150_ = lean_uint32_dec_le(v___x_2149_, v_c_2148_);
if (v___x_2150_ == 0)
{
lean_dec(v_a_2136_);
lean_dec(v_a_2135_);
goto v___jp_2138_;
}
else
{
uint32_t v___x_2151_; uint8_t v___x_2152_; 
v___x_2151_ = 57;
v___x_2152_ = lean_uint32_dec_le(v_c_2148_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_dec(v_a_2136_);
lean_dec(v_a_2135_);
goto v___jp_2138_;
}
else
{
lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2169_; 
lean_inc(v_snd_2145_);
lean_inc(v_fst_2144_);
v_isSharedCheck_2169_ = !lean_is_exclusive(v_a_2137_);
if (v_isSharedCheck_2169_ == 0)
{
lean_object* v_unused_2170_; lean_object* v_unused_2171_; 
v_unused_2170_ = lean_ctor_get(v_a_2137_, 1);
lean_dec(v_unused_2170_);
v_unused_2171_ = lean_ctor_get(v_a_2137_, 0);
lean_dec(v_unused_2171_);
v___x_2154_ = v_a_2137_;
v_isShared_2155_ = v_isSharedCheck_2169_;
goto v_resetjp_2153_;
}
else
{
lean_dec(v_a_2137_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2169_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v_one_2156_; lean_object* v_n_2157_; lean_object* v___x_2158_; lean_object* v_it_x27_2160_; 
v_one_2156_ = lean_unsigned_to_nat(1u);
v_n_2157_ = lean_nat_sub(v_a_2135_, v_one_2156_);
lean_dec(v_a_2135_);
v___x_2158_ = lean_string_utf8_next_fast(v_fst_2144_, v_snd_2145_);
lean_dec(v_snd_2145_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 1, v___x_2158_);
v_it_x27_2160_ = v___x_2154_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_fst_2144_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v___x_2158_);
v_it_x27_2160_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2161_ = lean_unsigned_to_nat(10u);
v___x_2162_ = lean_nat_mul(v___x_2161_, v_a_2136_);
lean_dec(v_a_2136_);
v___x_2163_ = lean_uint32_to_nat(v_c_2148_);
v___x_2164_ = lean_unsigned_to_nat(48u);
v___x_2165_ = lean_nat_sub(v___x_2163_, v___x_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_nat_add(v___x_2162_, v___x_2165_);
lean_dec(v___x_2165_);
lean_dec(v___x_2162_);
v_a_2135_ = v_n_2157_;
v_a_2136_ = v___x_2166_;
v_a_2137_ = v_it_x27_2160_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_dec(v_a_2136_);
lean_dec(v_a_2135_);
v___x_2172_ = lean_box(0);
v___x_2173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2173_, 0, v_a_2137_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
return v___x_2173_;
}
}
v___jp_2138_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_2140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2140_, 0, v_a_2137_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
return v___x_2140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(lean_object* v_size_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = lean_unsigned_to_nat(0u);
v___x_2177_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum_go(v_size_2174_, v___x_2176_, v_a_2175_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___lam__0(lean_object* v___y_2178_){
_start:
{
lean_object* v_fst_2182_; lean_object* v_snd_2183_; lean_object* v___x_2184_; uint8_t v_decide_2185_; 
v_fst_2182_ = lean_ctor_get(v___y_2178_, 0);
v_snd_2183_ = lean_ctor_get(v___y_2178_, 1);
v___x_2184_ = lean_string_utf8_byte_size(v_fst_2182_);
v_decide_2185_ = lean_nat_dec_eq(v_snd_2183_, v___x_2184_);
if (v_decide_2185_ == 0)
{
uint32_t v_c_2186_; lean_object* v___x_2187_; lean_object* v_it_x27_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; uint32_t v___x_2191_; uint8_t v___x_2192_; 
v_c_2186_ = lean_string_utf8_get_fast(v_fst_2182_, v_snd_2183_);
v___x_2187_ = lean_string_utf8_next_fast(v_fst_2182_, v_snd_2183_);
lean_inc(v_fst_2182_);
v_it_x27_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_2188_, 0, v_fst_2182_);
lean_ctor_set(v_it_x27_2188_, 1, v___x_2187_);
v___x_2189_ = lean_box_uint32(v_c_2186_);
v___x_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2190_, 0, v_it_x27_2188_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___x_2191_ = 48;
v___x_2192_ = lean_uint32_dec_le(v___x_2191_, v_c_2186_);
if (v___x_2192_ == 0)
{
lean_dec_ref_known(v___x_2190_, 2);
goto v___jp_2179_;
}
else
{
uint32_t v___x_2193_; uint8_t v___x_2194_; 
v___x_2193_ = 57;
v___x_2194_ = lean_uint32_dec_le(v_c_2186_, v___x_2193_);
if (v___x_2194_ == 0)
{
lean_dec_ref_known(v___x_2190_, 2);
goto v___jp_2179_;
}
else
{
lean_dec_ref(v___y_2178_);
return v___x_2190_;
}
}
}
else
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = lean_box(0);
v___x_2196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___y_2178_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
return v___x_2196_;
}
v___jp_2179_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_2181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___y_2178_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
return v___x_2181_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(lean_object* v_acc_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v_fst_2199_; lean_object* v_snd_2200_; lean_object* v_pos_2202_; lean_object* v_snd_2203_; lean_object* v_err_2204_; lean_object* v___x_2210_; uint8_t v_decide_2211_; 
v_fst_2199_ = lean_ctor_get(v_a_2198_, 0);
v_snd_2200_ = lean_ctor_get(v_a_2198_, 1);
lean_inc(v_snd_2200_);
v___x_2210_ = lean_string_utf8_byte_size(v_fst_2199_);
v_decide_2211_ = lean_nat_dec_eq(v_snd_2200_, v___x_2210_);
if (v_decide_2211_ == 0)
{
uint32_t v_c_2212_; uint32_t v___x_2213_; uint8_t v___x_2214_; 
v_c_2212_ = lean_string_utf8_get_fast(v_fst_2199_, v_snd_2200_);
v___x_2213_ = 48;
v___x_2214_ = lean_uint32_dec_le(v___x_2213_, v_c_2212_);
if (v___x_2214_ == 0)
{
goto v___jp_2208_;
}
else
{
uint32_t v___x_2215_; uint8_t v___x_2216_; 
v___x_2215_ = 57;
v___x_2216_ = lean_uint32_dec_le(v_c_2212_, v___x_2215_);
if (v___x_2216_ == 0)
{
goto v___jp_2208_;
}
else
{
lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2226_; 
lean_inc(v_fst_2199_);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_a_2198_);
if (v_isSharedCheck_2226_ == 0)
{
lean_object* v_unused_2227_; lean_object* v_unused_2228_; 
v_unused_2227_ = lean_ctor_get(v_a_2198_, 1);
lean_dec(v_unused_2227_);
v_unused_2228_ = lean_ctor_get(v_a_2198_, 0);
lean_dec(v_unused_2228_);
v___x_2218_ = v_a_2198_;
v_isShared_2219_ = v_isSharedCheck_2226_;
goto v_resetjp_2217_;
}
else
{
lean_dec(v_a_2198_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2226_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v_it_x27_2222_; 
v___x_2220_ = lean_string_utf8_next_fast(v_fst_2199_, v_snd_2200_);
lean_dec(v_snd_2200_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v___x_2220_);
v_it_x27_2222_ = v___x_2218_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_fst_2199_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v___x_2220_);
v_it_x27_2222_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2223_; 
v___x_2223_ = lean_string_push(v_acc_2197_, v_c_2212_);
v_acc_2197_ = v___x_2223_;
v_a_2198_ = v_it_x27_2222_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_box(0);
lean_inc(v_snd_2200_);
v_pos_2202_ = v_a_2198_;
v_snd_2203_ = v_snd_2200_;
v_err_2204_ = v___x_2229_;
goto v___jp_2201_;
}
v___jp_2201_:
{
uint8_t v_decide_2205_; 
v_decide_2205_ = lean_nat_dec_eq(v_snd_2200_, v_snd_2203_);
lean_dec(v_snd_2203_);
lean_dec(v_snd_2200_);
if (v_decide_2205_ == 0)
{
lean_object* v___x_2206_; 
lean_dec_ref(v_acc_2197_);
lean_inc(v_err_2204_);
v___x_2206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2206_, 0, v_pos_2202_);
lean_ctor_set(v___x_2206_, 1, v_err_2204_);
return v___x_2206_;
}
else
{
lean_object* v___x_2207_; 
v___x_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2207_, 0, v_pos_2202_);
lean_ctor_set(v___x_2207_, 1, v_acc_2197_);
return v___x_2207_;
}
}
v___jp_2208_:
{
lean_object* v___x_2209_; 
v___x_2209_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_2200_);
v_pos_2202_ = v_a_2198_;
v_snd_2203_ = v_snd_2200_;
v_err_2204_ = v___x_2209_;
goto v___jp_2201_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(lean_object* v_size_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v___f_2233_; lean_object* v___x_2234_; 
v___f_2233_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___closed__0));
v___x_2234_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_2233_, v_size_2231_, v_a_2232_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_pos_2235_; lean_object* v_res_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v_pos_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_pos_2235_);
v_res_2236_ = lean_ctor_get(v___x_2234_, 1);
lean_inc(v_res_2236_);
lean_dec_ref_known(v___x_2234_, 2);
v___x_2237_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_2238_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(v___x_2237_, v_pos_2235_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_pos_2239_; lean_object* v_res_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2252_; 
v_pos_2239_ = lean_ctor_get(v___x_2238_, 0);
v_res_2240_ = lean_ctor_get(v___x_2238_, 1);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2242_ = v___x_2238_;
v_isShared_2243_ = v_isSharedCheck_2252_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_res_2240_);
lean_inc(v_pos_2239_);
lean_dec(v___x_2238_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2252_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2244_ = lean_string_append(v_res_2236_, v_res_2240_);
lean_dec(v_res_2240_);
v___x_2245_ = lean_unsigned_to_nat(0u);
v___x_2246_ = lean_string_utf8_byte_size(v___x_2244_);
v___x_2247_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2244_);
lean_ctor_set(v___x_2247_, 1, v___x_2245_);
lean_ctor_set(v___x_2247_, 2, v___x_2246_);
v___x_2248_ = l_String_Slice_toNat_x21(v___x_2247_);
lean_dec_ref_known(v___x_2247_, 3);
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 1, v___x_2248_);
v___x_2250_ = v___x_2242_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_pos_2239_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
else
{
lean_object* v_pos_2253_; lean_object* v_err_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec(v_res_2236_);
v_pos_2253_ = lean_ctor_get(v___x_2238_, 0);
v_err_2254_ = lean_ctor_get(v___x_2238_, 1);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2238_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_err_2254_);
lean_inc(v_pos_2253_);
lean_dec(v___x_2238_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_pos_2253_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_err_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
else
{
lean_object* v_pos_2262_; lean_object* v_err_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
v_pos_2262_ = lean_ctor_get(v___x_2234_, 0);
v_err_2263_ = lean_ctor_get(v___x_2234_, 1);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2234_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_err_2263_);
lean_inc(v_pos_2262_);
lean_dec(v___x_2234_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_pos_2262_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_err_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___boxed(lean_object* v_size_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v_size_2271_, v_a_2272_);
lean_dec(v_size_2271_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(lean_object* v_size_2274_, lean_object* v_a_2275_){
_start:
{
lean_object* v___x_2276_; uint8_t v___x_2277_; 
v___x_2276_ = lean_unsigned_to_nat(1u);
v___x_2277_ = lean_nat_dec_eq(v_size_2274_, v___x_2276_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; 
v___x_2278_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_size_2274_, v_a_2275_);
return v___x_2278_;
}
else
{
lean_object* v___x_2279_; 
lean_dec(v_size_2274_);
v___x_2279_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v___x_2276_, v_a_2275_);
return v___x_2279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_digitRunLength(lean_object* v_it_2280_){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
lean_inc_ref(v_it_2280_);
v___x_2282_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(v___x_2281_, v_it_2280_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_res_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2291_; 
v_res_2283_ = lean_ctor_get(v___x_2282_, 1);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2291_ == 0)
{
lean_object* v_unused_2292_; 
v_unused_2292_ = lean_ctor_get(v___x_2282_, 0);
lean_dec(v_unused_2292_);
v___x_2285_ = v___x_2282_;
v_isShared_2286_ = v_isSharedCheck_2291_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_res_2283_);
lean_dec(v___x_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2291_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2287_ = lean_string_length(v_res_2283_);
lean_dec(v_res_2283_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 1, v___x_2287_);
lean_ctor_set(v___x_2285_, 0, v_it_2280_);
v___x_2289_ = v___x_2285_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_it_2280_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
else
{
lean_object* v_err_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
v_err_2293_ = lean_ctor_get(v___x_2282_, 1);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2300_ == 0)
{
lean_object* v_unused_2301_; 
v_unused_2301_ = lean_ctor_get(v___x_2282_, 0);
lean_dec(v_unused_2301_);
v___x_2295_ = v___x_2282_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_err_2293_);
lean_dec(v___x_2282_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v_it_2280_);
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_it_2280_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_err_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseVarWidthNum(lean_object* v_width_2302_, lean_object* v_reserve_2303_, lean_object* v_a_2304_){
_start:
{
if (lean_obj_tag(v_reserve_2303_) == 0)
{
lean_object* v___x_2305_; 
v___x_2305_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_width_2302_, v_a_2304_);
return v___x_2305_;
}
else
{
lean_object* v_val_2306_; lean_object* v___x_2307_; 
v_val_2306_ = lean_ctor_get(v_reserve_2303_, 0);
v___x_2307_ = l___private_Std_Time_Format_Basic_0__Std_Time_digitRunLength(v_a_2304_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_pos_2308_; lean_object* v_res_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; 
v_pos_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_pos_2308_);
v_res_2309_ = lean_ctor_get(v___x_2307_, 1);
lean_inc(v_res_2309_);
lean_dec_ref_known(v___x_2307_, 2);
v___x_2310_ = lean_nat_sub(v_res_2309_, v_val_2306_);
lean_dec(v_res_2309_);
v___x_2311_ = lean_nat_dec_le(v_width_2302_, v___x_2310_);
if (v___x_2311_ == 0)
{
lean_object* v___x_2312_; 
lean_dec(v___x_2310_);
v___x_2312_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_width_2302_, v_pos_2308_);
return v___x_2312_;
}
else
{
lean_object* v___x_2313_; 
lean_dec(v_width_2302_);
v___x_2313_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_2310_, v_pos_2308_);
return v___x_2313_;
}
}
else
{
lean_dec(v_width_2302_);
return v___x_2307_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseVarWidthNum___boxed(lean_object* v_width_2314_, lean_object* v_reserve_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseVarWidthNum(v_width_2314_, v_reserve_2315_, v_a_2316_);
lean_dec(v_reserve_2315_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear(uint8_t v_negative_2327_, lean_object* v_reserve_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v_pos_2338_; lean_object* v_val_2339_; lean_object* v_fst_2353_; lean_object* v_snd_2354_; lean_object* v_pos_2356_; lean_object* v_snd_2357_; lean_object* v_err_2358_; lean_object* v_pos_2376_; lean_object* v_fst_2377_; lean_object* v_snd_2378_; lean_object* v_err_2379_; lean_object* v___x_2392_; uint8_t v_decide_2393_; 
v_fst_2353_ = lean_ctor_get(v_a_2329_, 0);
lean_inc(v_fst_2353_);
v_snd_2354_ = lean_ctor_get(v_a_2329_, 1);
lean_inc(v_snd_2354_);
v___x_2392_ = lean_string_utf8_byte_size(v_fst_2353_);
v_decide_2393_ = lean_nat_dec_eq(v_snd_2354_, v___x_2392_);
if (v_decide_2393_ == 0)
{
uint32_t v___x_2394_; uint32_t v_c_2395_; uint8_t v___x_2396_; 
v___x_2394_ = 43;
v_c_2395_ = lean_string_utf8_get_fast(v_fst_2353_, v_snd_2354_);
v___x_2396_ = lean_uint32_dec_eq(v_c_2395_, v___x_2394_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; 
v___x_2397_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__5));
lean_inc(v_snd_2354_);
v_pos_2376_ = v_a_2329_;
v_fst_2377_ = v_fst_2353_;
v_snd_2378_ = v_snd_2354_;
v_err_2379_ = v___x_2397_;
goto v___jp_2375_;
}
else
{
lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2406_; 
v_isSharedCheck_2406_ = !lean_is_exclusive(v_a_2329_);
if (v_isSharedCheck_2406_ == 0)
{
lean_object* v_unused_2407_; lean_object* v_unused_2408_; 
v_unused_2407_ = lean_ctor_get(v_a_2329_, 1);
lean_dec(v_unused_2407_);
v_unused_2408_ = lean_ctor_get(v_a_2329_, 0);
lean_dec(v_unused_2408_);
v___x_2399_ = v_a_2329_;
v_isShared_2400_ = v_isSharedCheck_2406_;
goto v_resetjp_2398_;
}
else
{
lean_dec(v_a_2329_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2406_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; lean_object* v_it_x27_2403_; 
v___x_2401_ = lean_string_utf8_next_fast(v_fst_2353_, v_snd_2354_);
lean_dec(v_snd_2354_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 1, v___x_2401_);
v_it_x27_2403_ = v___x_2399_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_fst_2353_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v___x_2401_);
v_it_x27_2403_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2404_; 
v___x_2404_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v_pos_2338_ = v_it_x27_2403_;
v_val_2339_ = v___x_2404_;
goto v___jp_2337_;
}
}
}
}
else
{
lean_object* v___x_2409_; 
v___x_2409_ = lean_box(0);
lean_inc(v_snd_2354_);
v_pos_2376_ = v_a_2329_;
v_fst_2377_ = v_fst_2353_;
v_snd_2378_ = v_snd_2354_;
v_err_2379_ = v___x_2409_;
goto v___jp_2375_;
}
v___jp_2330_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2334_ = lean_nat_to_int(v___y_2332_);
v___x_2335_ = lean_int_mul(v___y_2333_, v___x_2334_);
lean_dec(v___x_2334_);
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___y_2331_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
return v___x_2336_;
}
v___jp_2337_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = lean_unsigned_to_nat(4u);
v___x_2341_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseVarWidthNum(v___x_2340_, v_reserve_2328_, v_pos_2338_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_pos_2342_; lean_object* v_res_2343_; 
v_pos_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_pos_2342_);
v_res_2343_ = lean_ctor_get(v___x_2341_, 1);
lean_inc(v_res_2343_);
lean_dec_ref_known(v___x_2341_, 2);
v___y_2331_ = v_pos_2342_;
v___y_2332_ = v_res_2343_;
v___y_2333_ = v_val_2339_;
goto v___jp_2330_;
}
else
{
lean_object* v_pos_2344_; lean_object* v_err_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
v_pos_2344_ = lean_ctor_get(v___x_2341_, 0);
v_err_2345_ = lean_ctor_get(v___x_2341_, 1);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2341_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_err_2345_);
lean_inc(v_pos_2344_);
lean_dec(v___x_2341_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_pos_2344_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_err_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
v___jp_2355_:
{
uint8_t v_decide_2359_; 
v_decide_2359_ = lean_nat_dec_eq(v_snd_2354_, v_snd_2357_);
lean_dec(v_snd_2357_);
lean_dec(v_snd_2354_);
if (v_decide_2359_ == 0)
{
lean_object* v___x_2360_; 
lean_inc(v_err_2358_);
v___x_2360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2360_, 0, v_pos_2356_);
lean_ctor_set(v___x_2360_, 1, v_err_2358_);
return v___x_2360_;
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = lean_unsigned_to_nat(4u);
v___x_2362_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_2361_, v_pos_2356_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_pos_2363_; lean_object* v_res_2364_; lean_object* v___x_2365_; 
v_pos_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_pos_2363_);
v_res_2364_ = lean_ctor_get(v___x_2362_, 1);
lean_inc(v_res_2364_);
lean_dec_ref_known(v___x_2362_, 2);
v___x_2365_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___y_2331_ = v_pos_2363_;
v___y_2332_ = v_res_2364_;
v___y_2333_ = v___x_2365_;
goto v___jp_2330_;
}
else
{
lean_object* v_pos_2366_; lean_object* v_err_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
v_pos_2366_ = lean_ctor_get(v___x_2362_, 0);
v_err_2367_ = lean_ctor_get(v___x_2362_, 1);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2362_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_err_2367_);
lean_inc(v_pos_2366_);
lean_dec(v___x_2362_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_pos_2366_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v_err_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
}
v___jp_2375_:
{
uint8_t v_decide_2380_; 
v_decide_2380_ = lean_nat_dec_eq(v_snd_2354_, v_snd_2378_);
if (v_decide_2380_ == 0)
{
lean_dec(v_fst_2377_);
v_pos_2356_ = v_pos_2376_;
v_snd_2357_ = v_snd_2378_;
v_err_2358_ = v_err_2379_;
goto v___jp_2355_;
}
else
{
if (v_negative_2327_ == 0)
{
lean_object* v___x_2381_; 
lean_dec(v_fst_2377_);
v___x_2381_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__1));
v_pos_2356_ = v_pos_2376_;
v_snd_2357_ = v_snd_2378_;
v_err_2358_ = v___x_2381_;
goto v___jp_2355_;
}
else
{
lean_object* v___x_2382_; uint8_t v_decide_2383_; 
v___x_2382_ = lean_string_utf8_byte_size(v_fst_2377_);
v_decide_2383_ = lean_nat_dec_eq(v_snd_2378_, v___x_2382_);
if (v_decide_2383_ == 0)
{
uint32_t v___x_2384_; uint32_t v_c_2385_; uint8_t v___x_2386_; 
v___x_2384_ = 45;
v_c_2385_ = lean_string_utf8_get_fast(v_fst_2377_, v_snd_2378_);
v___x_2386_ = lean_uint32_dec_eq(v_c_2385_, v___x_2384_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; 
lean_dec(v_fst_2377_);
v___x_2387_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__3));
v_pos_2356_ = v_pos_2376_;
v_snd_2357_ = v_snd_2378_;
v_err_2358_ = v___x_2387_;
goto v___jp_2355_;
}
else
{
lean_object* v___x_2388_; lean_object* v_it_x27_2389_; lean_object* v___x_2390_; 
lean_dec_ref(v_pos_2376_);
lean_dec(v_snd_2354_);
v___x_2388_ = lean_string_utf8_next_fast(v_fst_2377_, v_snd_2378_);
lean_dec(v_snd_2378_);
v_it_x27_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_2389_, 0, v_fst_2377_);
lean_ctor_set(v_it_x27_2389_, 1, v___x_2388_);
v___x_2390_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___closed__0);
v_pos_2338_ = v_it_x27_2389_;
v_val_2339_ = v___x_2390_;
goto v___jp_2337_;
}
}
else
{
lean_object* v___x_2391_; 
lean_dec(v_fst_2377_);
v___x_2391_ = lean_box(0);
v_pos_2356_ = v_pos_2376_;
v_snd_2357_ = v_snd_2378_;
v_err_2358_ = v___x_2391_;
goto v___jp_2355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___boxed(lean_object* v_negative_2410_, lean_object* v_reserve_2411_, lean_object* v_a_2412_){
_start:
{
uint8_t v_negative_boxed_2413_; lean_object* v_res_2414_; 
v_negative_boxed_2413_ = lean_unbox(v_negative_2410_);
v_res_2414_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear(v_negative_boxed_2413_, v_reserve_2411_, v_a_2412_);
lean_dec(v_reserve_2411_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(lean_object* v_size_2415_, lean_object* v_pad_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v___f_2418_; lean_object* v___x_2419_; 
v___f_2418_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___closed__0));
v___x_2419_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_2418_, v_size_2415_, v_a_2417_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_pos_2420_; lean_object* v_res_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2434_; 
v_pos_2420_ = lean_ctor_get(v___x_2419_, 0);
v_res_2421_ = lean_ctor_get(v___x_2419_, 1);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2423_ = v___x_2419_;
v_isShared_2424_ = v_isSharedCheck_2434_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_res_2421_);
lean_inc(v_pos_2420_);
lean_dec(v___x_2419_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2434_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
uint32_t v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2425_ = 48;
v___x_2426_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_pad_2416_, v___x_2425_, v_res_2421_);
v___x_2427_ = lean_unsigned_to_nat(0u);
v___x_2428_ = lean_string_utf8_byte_size(v___x_2426_);
v___x_2429_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2426_);
lean_ctor_set(v___x_2429_, 1, v___x_2427_);
lean_ctor_set(v___x_2429_, 2, v___x_2428_);
v___x_2430_ = l_String_Slice_toNat_x21(v___x_2429_);
lean_dec_ref_known(v___x_2429_, 3);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 1, v___x_2430_);
v___x_2432_ = v___x_2423_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_pos_2420_);
lean_ctor_set(v_reuseFailAlloc_2433_, 1, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
else
{
lean_object* v_pos_2435_; lean_object* v_err_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
v_pos_2435_ = lean_ctor_get(v___x_2419_, 0);
v_err_2436_ = lean_ctor_get(v___x_2419_, 1);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2419_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_err_2436_);
lean_inc(v_pos_2435_);
lean_dec(v___x_2419_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_pos_2435_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v_err_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed(lean_object* v_size_2444_, lean_object* v_pad_2445_, lean_object* v_a_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(v_size_2444_, v_pad_2445_, v_a_2446_);
lean_dec(v_pad_2445_);
lean_dec(v_size_2444_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(lean_object* v_acc_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v_pos_2451_; uint32_t v_res_2452_; lean_object* v_fst_2455_; lean_object* v_snd_2456_; lean_object* v_pos_2458_; lean_object* v_snd_2459_; lean_object* v_err_2460_; lean_object* v___x_2464_; uint8_t v_decide_2465_; 
v_fst_2455_ = lean_ctor_get(v_a_2449_, 0);
v_snd_2456_ = lean_ctor_get(v_a_2449_, 1);
lean_inc(v_snd_2456_);
v___x_2464_ = lean_string_utf8_byte_size(v_fst_2455_);
v_decide_2465_ = lean_nat_dec_eq(v_snd_2456_, v___x_2464_);
if (v_decide_2465_ == 0)
{
uint32_t v_c_2466_; lean_object* v___x_2467_; lean_object* v_it_x27_2468_; uint32_t v___x_2491_; uint8_t v___x_2492_; 
v_c_2466_ = lean_string_utf8_get_fast(v_fst_2455_, v_snd_2456_);
v___x_2467_ = lean_string_utf8_next_fast(v_fst_2455_, v_snd_2456_);
lean_inc(v_fst_2455_);
v_it_x27_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_2468_, 0, v_fst_2455_);
lean_ctor_set(v_it_x27_2468_, 1, v___x_2467_);
v___x_2491_ = 65;
v___x_2492_ = lean_uint32_dec_le(v___x_2491_, v_c_2466_);
if (v___x_2492_ == 0)
{
goto v___jp_2486_;
}
else
{
uint32_t v___x_2493_; uint8_t v___x_2494_; 
v___x_2493_ = 90;
v___x_2494_ = lean_uint32_dec_le(v_c_2466_, v___x_2493_);
if (v___x_2494_ == 0)
{
goto v___jp_2486_;
}
else
{
lean_dec(v_snd_2456_);
lean_dec_ref(v_a_2449_);
v_pos_2451_ = v_it_x27_2468_;
v_res_2452_ = v_c_2466_;
goto v___jp_2450_;
}
}
v___jp_2469_:
{
uint32_t v___x_2470_; uint8_t v___x_2471_; 
v___x_2470_ = 95;
v___x_2471_ = lean_uint32_dec_eq(v_c_2466_, v___x_2470_);
if (v___x_2471_ == 0)
{
uint32_t v___x_2472_; uint8_t v___x_2473_; 
v___x_2472_ = 45;
v___x_2473_ = lean_uint32_dec_eq(v_c_2466_, v___x_2472_);
if (v___x_2473_ == 0)
{
uint32_t v___x_2474_; uint8_t v___x_2475_; 
v___x_2474_ = 43;
v___x_2475_ = lean_uint32_dec_eq(v_c_2466_, v___x_2474_);
if (v___x_2475_ == 0)
{
uint32_t v___x_2476_; uint8_t v___x_2477_; 
v___x_2476_ = 47;
v___x_2477_ = lean_uint32_dec_eq(v_c_2466_, v___x_2476_);
if (v___x_2477_ == 0)
{
uint32_t v___x_2478_; uint8_t v___x_2479_; 
v___x_2478_ = 58;
v___x_2479_ = lean_uint32_dec_eq(v_c_2466_, v___x_2478_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; 
lean_dec_ref_known(v_it_x27_2468_, 2);
v___x_2480_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_2456_);
v_pos_2458_ = v_a_2449_;
v_snd_2459_ = v_snd_2456_;
v_err_2460_ = v___x_2480_;
goto v___jp_2457_;
}
else
{
lean_dec(v_snd_2456_);
lean_dec_ref(v_a_2449_);
v_pos_2451_ = v_it_x27_2468_;
v_res_2452_ = v_c_2466_;
goto v___jp_2450_;
}
}
else
{
lean_dec(v_snd_2456_);
lean_dec_ref(v_a_2449_);
v_pos_2451_ = v_it_x27_2468_;
v_res_2452_ = v_c_2466_;
goto v___jp_2450_;
}
}
else
{
lean_dec(v_snd_2456_);
lean_dec_ref(v_a_2449_);
v_pos_2451_ = v_it_x27_2468_;
v_res_2452_ = v_c_2466_;
goto v___jp_2450_;
}
}
else
{
lean_dec(v_snd_2456_);
lean_dec_ref(v_a_2449_);
v_pos_2451_ = v_it_x27_2468_;
v_res_2452_ = v_c_2466_;
goto v___jp_2450_;
}
}
else
{
lean_dec(v_snd_2456_);
lean_dec_ref(v_a_2449_);
v_pos_2451_ = v_it_x27_2468_;
v_res_2452_ = v_c_2466_;
goto v___jp_2450_;
}
}
v___jp_2481_:
{
uint32_t v___x_2482_; uint8_t v___x_2483_; 
v___x_2482_ = 48;
v___x_2483_ = lean_uint32_dec_le(v___x_2482_, v_c_2466_);
if (v___x_2483_ == 0)
{
goto v___jp_2469_;
}
else
{
uint32_t v___x_2484_; uint8_t v___x_2485_; 
v___x_2484_ = 57;
v___x_2485_ = lean_uint32_dec_le(v_c_2466_, v___x_2484_);
if (v___x_2485_ == 0)
{
goto v___jp_2469_;
}
else
{
lean_dec(v_snd_2456_);
lean_dec_ref(v_a_2449_);
v_pos_2451_ = v_it_x27_2468_;
v_res_2452_ = v_c_2466_;
goto v___jp_2450_;
}
}
}
v___jp_2486_:
{
uint32_t v___x_2487_; uint8_t v___x_2488_; 
v___x_2487_ = 97;
v___x_2488_ = lean_uint32_dec_le(v___x_2487_, v_c_2466_);
if (v___x_2488_ == 0)
{
goto v___jp_2481_;
}
else
{
uint32_t v___x_2489_; uint8_t v___x_2490_; 
v___x_2489_ = 122;
v___x_2490_ = lean_uint32_dec_le(v_c_2466_, v___x_2489_);
if (v___x_2490_ == 0)
{
goto v___jp_2481_;
}
else
{
lean_dec(v_snd_2456_);
lean_dec_ref(v_a_2449_);
v_pos_2451_ = v_it_x27_2468_;
v_res_2452_ = v_c_2466_;
goto v___jp_2450_;
}
}
}
}
else
{
lean_object* v___x_2495_; 
v___x_2495_ = lean_box(0);
lean_inc(v_snd_2456_);
v_pos_2458_ = v_a_2449_;
v_snd_2459_ = v_snd_2456_;
v_err_2460_ = v___x_2495_;
goto v___jp_2457_;
}
v___jp_2450_:
{
lean_object* v___x_2453_; 
v___x_2453_ = lean_string_push(v_acc_2448_, v_res_2452_);
v_acc_2448_ = v___x_2453_;
v_a_2449_ = v_pos_2451_;
goto _start;
}
v___jp_2457_:
{
uint8_t v_decide_2461_; 
v_decide_2461_ = lean_nat_dec_eq(v_snd_2456_, v_snd_2459_);
lean_dec(v_snd_2459_);
lean_dec(v_snd_2456_);
if (v_decide_2461_ == 0)
{
lean_object* v___x_2462_; 
lean_dec_ref(v_acc_2448_);
lean_inc(v_err_2460_);
v___x_2462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2462_, 0, v_pos_2458_);
lean_ctor_set(v___x_2462_, 1, v_err_2460_);
return v___x_2462_;
}
else
{
lean_object* v___x_2463_; 
v___x_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2463_, 0, v_pos_2458_);
lean_ctor_set(v___x_2463_, 1, v_acc_2448_);
return v___x_2463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(lean_object* v_acc_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v_pos_2499_; uint32_t v_res_2500_; lean_object* v_fst_2503_; lean_object* v_snd_2504_; lean_object* v_pos_2506_; lean_object* v_snd_2507_; lean_object* v_err_2508_; lean_object* v___x_2512_; uint8_t v_decide_2513_; 
v_fst_2503_ = lean_ctor_get(v_a_2497_, 0);
v_snd_2504_ = lean_ctor_get(v_a_2497_, 1);
lean_inc(v_snd_2504_);
v___x_2512_ = lean_string_utf8_byte_size(v_fst_2503_);
v_decide_2513_ = lean_nat_dec_eq(v_snd_2504_, v___x_2512_);
if (v_decide_2513_ == 0)
{
uint32_t v_c_2514_; lean_object* v___x_2515_; lean_object* v_it_x27_2516_; uint32_t v___x_2539_; uint8_t v___x_2540_; 
v_c_2514_ = lean_string_utf8_get_fast(v_fst_2503_, v_snd_2504_);
v___x_2515_ = lean_string_utf8_next_fast(v_fst_2503_, v_snd_2504_);
lean_inc(v_fst_2503_);
v_it_x27_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_2516_, 0, v_fst_2503_);
lean_ctor_set(v_it_x27_2516_, 1, v___x_2515_);
v___x_2539_ = 65;
v___x_2540_ = lean_uint32_dec_le(v___x_2539_, v_c_2514_);
if (v___x_2540_ == 0)
{
goto v___jp_2534_;
}
else
{
uint32_t v___x_2541_; uint8_t v___x_2542_; 
v___x_2541_ = 90;
v___x_2542_ = lean_uint32_dec_le(v_c_2514_, v___x_2541_);
if (v___x_2542_ == 0)
{
goto v___jp_2534_;
}
else
{
lean_dec(v_snd_2504_);
lean_dec_ref(v_a_2497_);
v_pos_2499_ = v_it_x27_2516_;
v_res_2500_ = v_c_2514_;
goto v___jp_2498_;
}
}
v___jp_2517_:
{
uint32_t v___x_2518_; uint8_t v___x_2519_; 
v___x_2518_ = 95;
v___x_2519_ = lean_uint32_dec_eq(v_c_2514_, v___x_2518_);
if (v___x_2519_ == 0)
{
uint32_t v___x_2520_; uint8_t v___x_2521_; 
v___x_2520_ = 45;
v___x_2521_ = lean_uint32_dec_eq(v_c_2514_, v___x_2520_);
if (v___x_2521_ == 0)
{
uint32_t v___x_2522_; uint8_t v___x_2523_; 
v___x_2522_ = 43;
v___x_2523_ = lean_uint32_dec_eq(v_c_2514_, v___x_2522_);
if (v___x_2523_ == 0)
{
uint32_t v___x_2524_; uint8_t v___x_2525_; 
v___x_2524_ = 47;
v___x_2525_ = lean_uint32_dec_eq(v_c_2514_, v___x_2524_);
if (v___x_2525_ == 0)
{
uint32_t v___x_2526_; uint8_t v___x_2527_; 
v___x_2526_ = 58;
v___x_2527_ = lean_uint32_dec_eq(v_c_2514_, v___x_2526_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; 
lean_dec_ref_known(v_it_x27_2516_, 2);
v___x_2528_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_2504_);
v_pos_2506_ = v_a_2497_;
v_snd_2507_ = v_snd_2504_;
v_err_2508_ = v___x_2528_;
goto v___jp_2505_;
}
else
{
lean_dec(v_snd_2504_);
lean_dec_ref(v_a_2497_);
v_pos_2499_ = v_it_x27_2516_;
v_res_2500_ = v_c_2514_;
goto v___jp_2498_;
}
}
else
{
lean_dec(v_snd_2504_);
lean_dec_ref(v_a_2497_);
v_pos_2499_ = v_it_x27_2516_;
v_res_2500_ = v_c_2514_;
goto v___jp_2498_;
}
}
else
{
lean_dec(v_snd_2504_);
lean_dec_ref(v_a_2497_);
v_pos_2499_ = v_it_x27_2516_;
v_res_2500_ = v_c_2514_;
goto v___jp_2498_;
}
}
else
{
lean_dec(v_snd_2504_);
lean_dec_ref(v_a_2497_);
v_pos_2499_ = v_it_x27_2516_;
v_res_2500_ = v_c_2514_;
goto v___jp_2498_;
}
}
else
{
lean_dec(v_snd_2504_);
lean_dec_ref(v_a_2497_);
v_pos_2499_ = v_it_x27_2516_;
v_res_2500_ = v_c_2514_;
goto v___jp_2498_;
}
}
v___jp_2529_:
{
uint32_t v___x_2530_; uint8_t v___x_2531_; 
v___x_2530_ = 48;
v___x_2531_ = lean_uint32_dec_le(v___x_2530_, v_c_2514_);
if (v___x_2531_ == 0)
{
goto v___jp_2517_;
}
else
{
uint32_t v___x_2532_; uint8_t v___x_2533_; 
v___x_2532_ = 57;
v___x_2533_ = lean_uint32_dec_le(v_c_2514_, v___x_2532_);
if (v___x_2533_ == 0)
{
goto v___jp_2517_;
}
else
{
lean_dec(v_snd_2504_);
lean_dec_ref(v_a_2497_);
v_pos_2499_ = v_it_x27_2516_;
v_res_2500_ = v_c_2514_;
goto v___jp_2498_;
}
}
}
v___jp_2534_:
{
uint32_t v___x_2535_; uint8_t v___x_2536_; 
v___x_2535_ = 97;
v___x_2536_ = lean_uint32_dec_le(v___x_2535_, v_c_2514_);
if (v___x_2536_ == 0)
{
goto v___jp_2529_;
}
else
{
uint32_t v___x_2537_; uint8_t v___x_2538_; 
v___x_2537_ = 122;
v___x_2538_ = lean_uint32_dec_le(v_c_2514_, v___x_2537_);
if (v___x_2538_ == 0)
{
goto v___jp_2529_;
}
else
{
lean_dec(v_snd_2504_);
lean_dec_ref(v_a_2497_);
v_pos_2499_ = v_it_x27_2516_;
v_res_2500_ = v_c_2514_;
goto v___jp_2498_;
}
}
}
}
else
{
lean_object* v___x_2543_; 
v___x_2543_ = lean_box(0);
lean_inc(v_snd_2504_);
v_pos_2506_ = v_a_2497_;
v_snd_2507_ = v_snd_2504_;
v_err_2508_ = v___x_2543_;
goto v___jp_2505_;
}
v___jp_2498_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = lean_string_push(v_acc_2496_, v_res_2500_);
v___x_2502_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(v___x_2501_, v_pos_2499_);
return v___x_2502_;
}
v___jp_2505_:
{
uint8_t v_decide_2509_; 
v_decide_2509_ = lean_nat_dec_eq(v_snd_2504_, v_snd_2507_);
lean_dec(v_snd_2507_);
lean_dec(v_snd_2504_);
if (v_decide_2509_ == 0)
{
lean_object* v___x_2510_; 
lean_dec_ref(v_acc_2496_);
lean_inc(v_err_2508_);
v___x_2510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2510_, 0, v_pos_2506_);
lean_ctor_set(v___x_2510_, 1, v_err_2508_);
return v___x_2510_;
}
else
{
lean_object* v___x_2511_; 
v___x_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2511_, 0, v_pos_2506_);
lean_ctor_set(v___x_2511_, 1, v_acc_2496_);
return v___x_2511_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(lean_object* v_a_2544_){
_start:
{
lean_object* v_fst_2545_; lean_object* v_snd_2546_; lean_object* v___x_2547_; uint8_t v_decide_2548_; 
v_fst_2545_ = lean_ctor_get(v_a_2544_, 0);
v_snd_2546_ = lean_ctor_get(v_a_2544_, 1);
v___x_2547_ = lean_string_utf8_byte_size(v_fst_2545_);
v_decide_2548_ = lean_nat_dec_eq(v_snd_2546_, v___x_2547_);
if (v_decide_2548_ == 0)
{
uint32_t v_c_2549_; lean_object* v___x_2550_; uint32_t v___x_2579_; uint8_t v___x_2580_; 
v_c_2549_ = lean_string_utf8_get_fast(v_fst_2545_, v_snd_2546_);
v___x_2550_ = lean_string_utf8_next_fast(v_fst_2545_, v_snd_2546_);
v___x_2579_ = 65;
v___x_2580_ = lean_uint32_dec_le(v___x_2579_, v_c_2549_);
if (v___x_2580_ == 0)
{
goto v___jp_2574_;
}
else
{
uint32_t v___x_2581_; uint8_t v___x_2582_; 
v___x_2581_ = 90;
v___x_2582_ = lean_uint32_dec_le(v_c_2549_, v___x_2581_);
if (v___x_2582_ == 0)
{
goto v___jp_2574_;
}
else
{
lean_inc(v_fst_2545_);
lean_dec_ref(v_a_2544_);
goto v___jp_2551_;
}
}
v___jp_2551_:
{
lean_object* v_it_x27_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v_it_x27_2552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_2552_, 0, v_fst_2545_);
lean_ctor_set(v_it_x27_2552_, 1, v___x_2550_);
v___x_2553_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_2554_ = lean_string_push(v___x_2553_, v_c_2549_);
v___x_2555_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(v___x_2554_, v_it_x27_2552_);
return v___x_2555_;
}
v___jp_2556_:
{
uint32_t v___x_2557_; uint8_t v___x_2558_; 
v___x_2557_ = 95;
v___x_2558_ = lean_uint32_dec_eq(v_c_2549_, v___x_2557_);
if (v___x_2558_ == 0)
{
uint32_t v___x_2559_; uint8_t v___x_2560_; 
v___x_2559_ = 45;
v___x_2560_ = lean_uint32_dec_eq(v_c_2549_, v___x_2559_);
if (v___x_2560_ == 0)
{
uint32_t v___x_2561_; uint8_t v___x_2562_; 
v___x_2561_ = 43;
v___x_2562_ = lean_uint32_dec_eq(v_c_2549_, v___x_2561_);
if (v___x_2562_ == 0)
{
uint32_t v___x_2563_; uint8_t v___x_2564_; 
v___x_2563_ = 47;
v___x_2564_ = lean_uint32_dec_eq(v_c_2549_, v___x_2563_);
if (v___x_2564_ == 0)
{
uint32_t v___x_2565_; uint8_t v___x_2566_; 
v___x_2565_ = 58;
v___x_2566_ = lean_uint32_dec_eq(v_c_2549_, v___x_2565_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_2568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2568_, 0, v_a_2544_);
lean_ctor_set(v___x_2568_, 1, v___x_2567_);
return v___x_2568_;
}
else
{
lean_inc(v_fst_2545_);
lean_dec_ref(v_a_2544_);
goto v___jp_2551_;
}
}
else
{
lean_inc(v_fst_2545_);
lean_dec_ref(v_a_2544_);
goto v___jp_2551_;
}
}
else
{
lean_inc(v_fst_2545_);
lean_dec_ref(v_a_2544_);
goto v___jp_2551_;
}
}
else
{
lean_inc(v_fst_2545_);
lean_dec_ref(v_a_2544_);
goto v___jp_2551_;
}
}
else
{
lean_inc(v_fst_2545_);
lean_dec_ref(v_a_2544_);
goto v___jp_2551_;
}
}
v___jp_2569_:
{
uint32_t v___x_2570_; uint8_t v___x_2571_; 
v___x_2570_ = 48;
v___x_2571_ = lean_uint32_dec_le(v___x_2570_, v_c_2549_);
if (v___x_2571_ == 0)
{
goto v___jp_2556_;
}
else
{
uint32_t v___x_2572_; uint8_t v___x_2573_; 
v___x_2572_ = 57;
v___x_2573_ = lean_uint32_dec_le(v_c_2549_, v___x_2572_);
if (v___x_2573_ == 0)
{
goto v___jp_2556_;
}
else
{
lean_inc(v_fst_2545_);
lean_dec_ref(v_a_2544_);
goto v___jp_2551_;
}
}
}
v___jp_2574_:
{
uint32_t v___x_2575_; uint8_t v___x_2576_; 
v___x_2575_ = 97;
v___x_2576_ = lean_uint32_dec_le(v___x_2575_, v_c_2549_);
if (v___x_2576_ == 0)
{
goto v___jp_2569_;
}
else
{
uint32_t v___x_2577_; uint8_t v___x_2578_; 
v___x_2577_ = 122;
v___x_2578_ = lean_uint32_dec_le(v_c_2549_, v___x_2577_);
if (v___x_2578_ == 0)
{
goto v___jp_2569_;
}
else
{
lean_inc(v_fst_2545_);
lean_dec_ref(v_a_2544_);
goto v___jp_2551_;
}
}
}
}
else
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = lean_box(0);
v___x_2584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2584_, 0, v_a_2544_);
lean_ctor_set(v___x_2584_, 1, v___x_2583_);
return v___x_2584_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseZoneId(lean_object* v_a_2585_){
_start:
{
lean_object* v___x_2586_; lean_object* v_name_2587_; lean_object* v___x_2588_; 
v___x_2586_ = l_Std_Time_TimeZone_GMT;
v_name_2587_ = lean_ctor_get(v___x_2586_, 1);
lean_inc_ref(v_a_2585_);
lean_inc_ref(v_name_2587_);
v___x_2588_ = l_Std_Internal_Parsec_String_pstring(v_name_2587_, v_a_2585_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_dec_ref(v_a_2585_);
return v___x_2588_;
}
else
{
lean_object* v_pos_2589_; lean_object* v_snd_2590_; lean_object* v_snd_2591_; uint8_t v_decide_2592_; 
v_pos_2589_ = lean_ctor_get(v___x_2588_, 0);
v_snd_2590_ = lean_ctor_get(v_a_2585_, 1);
lean_inc(v_snd_2590_);
lean_dec_ref(v_a_2585_);
v_snd_2591_ = lean_ctor_get(v_pos_2589_, 1);
v_decide_2592_ = lean_nat_dec_eq(v_snd_2590_, v_snd_2591_);
lean_dec(v_snd_2590_);
if (v_decide_2592_ == 0)
{
return v___x_2588_;
}
else
{
lean_object* v___x_2593_; 
lean_inc(v_pos_2589_);
lean_dec_ref_known(v___x_2588_, 2);
v___x_2593_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(v_pos_2589_);
return v___x_2593_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(lean_object* v_n_2596_, lean_object* v_m_2597_, lean_object* v_parser_2598_, lean_object* v_a_2599_){
_start:
{
lean_object* v___x_2600_; 
v___x_2600_ = lean_apply_1(v_parser_2598_, v_a_2599_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_pos_2601_; lean_object* v_res_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2622_; 
v_pos_2601_ = lean_ctor_get(v___x_2600_, 0);
v_res_2602_ = lean_ctor_get(v___x_2600_, 1);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2604_ = v___x_2600_;
v_isShared_2605_ = v_isSharedCheck_2622_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_res_2602_);
lean_inc(v_pos_2601_);
lean_dec(v___x_2600_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2622_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
uint8_t v___x_2618_; 
v___x_2618_ = lean_nat_dec_le(v_n_2596_, v_res_2602_);
if (v___x_2618_ == 0)
{
lean_dec(v_res_2602_);
goto v___jp_2606_;
}
else
{
uint8_t v___x_2619_; 
v___x_2619_ = lean_nat_dec_le(v_res_2602_, v_m_2597_);
if (v___x_2619_ == 0)
{
lean_dec(v_res_2602_);
goto v___jp_2606_;
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
lean_del_object(v___x_2604_);
lean_dec(v_m_2597_);
lean_dec(v_n_2596_);
v___x_2620_ = lean_nat_to_int(v_res_2602_);
v___x_2621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2621_, 0, v_pos_2601_);
lean_ctor_set(v___x_2621_, 1, v___x_2620_);
return v___x_2621_;
}
}
v___jp_2606_:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2616_; 
v___x_2607_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__0));
v___x_2608_ = l_Nat_reprFast(v_n_2596_);
v___x_2609_ = lean_string_append(v___x_2607_, v___x_2608_);
lean_dec_ref(v___x_2608_);
v___x_2610_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__1));
v___x_2611_ = lean_string_append(v___x_2609_, v___x_2610_);
v___x_2612_ = l_Nat_reprFast(v_m_2597_);
v___x_2613_ = lean_string_append(v___x_2611_, v___x_2612_);
lean_dec_ref(v___x_2612_);
v___x_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set_tag(v___x_2604_, 1);
lean_ctor_set(v___x_2604_, 1, v___x_2614_);
v___x_2616_ = v___x_2604_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_pos_2601_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
else
{
lean_object* v_pos_2623_; lean_object* v_err_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec(v_m_2597_);
lean_dec(v_n_2596_);
v_pos_2623_ = lean_ctor_get(v___x_2600_, 0);
v_err_2624_ = lean_ctor_get(v___x_2600_, 1);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2600_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_err_2624_);
lean_inc(v_pos_2623_);
lean_dec(v___x_2600_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_pos_2623_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_err_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(lean_object* v_a_2632_){
_start:
{
lean_object* v_fst_2636_; lean_object* v_snd_2637_; lean_object* v___x_2638_; uint8_t v_decide_2639_; 
v_fst_2636_ = lean_ctor_get(v_a_2632_, 0);
v_snd_2637_ = lean_ctor_get(v_a_2632_, 1);
v___x_2638_ = lean_string_utf8_byte_size(v_fst_2636_);
v_decide_2639_ = lean_nat_dec_eq(v_snd_2637_, v___x_2638_);
if (v_decide_2639_ == 0)
{
uint32_t v_c_2640_; uint32_t v___x_2641_; uint8_t v___x_2642_; 
v_c_2640_ = lean_string_utf8_get_fast(v_fst_2636_, v_snd_2637_);
v___x_2641_ = 48;
v___x_2642_ = lean_uint32_dec_le(v___x_2641_, v_c_2640_);
if (v___x_2642_ == 0)
{
goto v___jp_2633_;
}
else
{
uint32_t v___x_2643_; uint8_t v___x_2644_; 
v___x_2643_ = 57;
v___x_2644_ = lean_uint32_dec_le(v_c_2640_, v___x_2643_);
if (v___x_2644_ == 0)
{
goto v___jp_2633_;
}
else
{
lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2680_; 
lean_inc(v_snd_2637_);
lean_inc(v_fst_2636_);
v_isSharedCheck_2680_ = !lean_is_exclusive(v_a_2632_);
if (v_isSharedCheck_2680_ == 0)
{
lean_object* v_unused_2681_; lean_object* v_unused_2682_; 
v_unused_2681_ = lean_ctor_get(v_a_2632_, 1);
lean_dec(v_unused_2681_);
v_unused_2682_ = lean_ctor_get(v_a_2632_, 0);
lean_dec(v_unused_2682_);
v___x_2646_ = v_a_2632_;
v_isShared_2647_ = v_isSharedCheck_2680_;
goto v_resetjp_2645_;
}
else
{
lean_dec(v_a_2632_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2680_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2648_; lean_object* v_pos_2650_; lean_object* v_snd_2651_; lean_object* v_err_2652_; lean_object* v_it_x27_2660_; 
v___x_2648_ = lean_string_utf8_next_fast(v_fst_2636_, v_snd_2637_);
lean_dec(v_snd_2637_);
lean_inc(v_fst_2636_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 1, v___x_2648_);
v_it_x27_2660_ = v___x_2646_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_fst_2636_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v___x_2648_);
v_it_x27_2660_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2659_;
}
v___jp_2649_:
{
uint8_t v_decide_2653_; 
v_decide_2653_ = lean_nat_dec_eq(v___x_2648_, v_snd_2651_);
lean_dec(v_snd_2651_);
if (v_decide_2653_ == 0)
{
lean_object* v___x_2654_; 
lean_inc(v_err_2652_);
v___x_2654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2654_, 0, v_pos_2650_);
lean_ctor_set(v___x_2654_, 1, v_err_2652_);
return v___x_2654_;
}
else
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2655_ = lean_uint32_to_nat(v_c_2640_);
v___x_2656_ = lean_unsigned_to_nat(48u);
v___x_2657_ = lean_nat_sub(v___x_2655_, v___x_2656_);
lean_dec(v___x_2655_);
v___x_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2658_, 0, v_pos_2650_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
return v___x_2658_;
}
}
v_reusejp_2659_:
{
uint8_t v_decide_2663_; 
v_decide_2663_ = lean_nat_dec_eq(v___x_2648_, v___x_2638_);
if (v_decide_2663_ == 0)
{
uint32_t v___x_2664_; uint8_t v___x_2665_; 
v___x_2664_ = lean_string_utf8_get_fast(v_fst_2636_, v___x_2648_);
v___x_2665_ = lean_uint32_dec_le(v___x_2641_, v___x_2664_);
if (v___x_2665_ == 0)
{
lean_dec(v_fst_2636_);
goto v___jp_2661_;
}
else
{
uint8_t v___x_2666_; 
v___x_2666_ = lean_uint32_dec_le(v___x_2664_, v___x_2643_);
if (v___x_2666_ == 0)
{
lean_dec(v_fst_2636_);
goto v___jp_2661_;
}
else
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
lean_dec_ref(v_it_x27_2660_);
v___x_2667_ = lean_unsigned_to_nat(48u);
v___x_2668_ = lean_string_utf8_next_fast(v_fst_2636_, v___x_2648_);
v___x_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2669_, 0, v_fst_2636_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = lean_uint32_to_nat(v_c_2640_);
v___x_2671_ = lean_nat_sub(v___x_2670_, v___x_2667_);
lean_dec(v___x_2670_);
v___x_2672_ = lean_unsigned_to_nat(10u);
v___x_2673_ = lean_nat_mul(v___x_2671_, v___x_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_uint32_to_nat(v___x_2664_);
v___x_2675_ = lean_nat_sub(v___x_2674_, v___x_2667_);
lean_dec(v___x_2674_);
v___x_2676_ = lean_nat_add(v___x_2673_, v___x_2675_);
lean_dec(v___x_2675_);
lean_dec(v___x_2673_);
v___x_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2669_);
lean_ctor_set(v___x_2677_, 1, v___x_2676_);
return v___x_2677_;
}
}
}
else
{
lean_object* v___x_2678_; 
lean_dec(v_fst_2636_);
v___x_2678_ = lean_box(0);
v_pos_2650_ = v_it_x27_2660_;
v_snd_2651_ = v___x_2648_;
v_err_2652_ = v___x_2678_;
goto v___jp_2649_;
}
v___jp_2661_:
{
lean_object* v___x_2662_; 
v___x_2662_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v_pos_2650_ = v_it_x27_2660_;
v_snd_2651_ = v___x_2648_;
v_err_2652_ = v___x_2662_;
goto v___jp_2649_;
}
}
}
}
}
}
else
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = lean_box(0);
v___x_2684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2684_, 0, v_a_2632_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
return v___x_2684_;
}
v___jp_2633_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_2635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2635_, 0, v_a_2632_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
return v___x_2635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___impl(uint8_t v_x_2685_){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2686_ = lean_box(v_x_2685_);
v___x_2687_ = lean_obj_tag_nat(v___x_2686_);
lean_dec(v___x_2686_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___impl___boxed(lean_object* v_x_2688_){
_start:
{
uint8_t v_x_4__boxed_2689_; lean_object* v_res_2690_; 
v_x_4__boxed_2689_ = lean_unbox(v_x_2688_);
v_res_2690_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___impl(v_x_4__boxed_2689_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg(lean_object* v_k_2691_){
_start:
{
lean_inc(v_k_2691_);
return v_k_2691_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg___boxed(lean_object* v_k_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg(v_k_2692_);
lean_dec(v_k_2692_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(lean_object* v_motive_2694_, lean_object* v_ctorIdx_2695_, uint8_t v_t_2696_, lean_object* v_h_2697_, lean_object* v_k_2698_){
_start:
{
lean_inc(v_k_2698_);
return v_k_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___boxed(lean_object* v_motive_2699_, lean_object* v_ctorIdx_2700_, lean_object* v_t_2701_, lean_object* v_h_2702_, lean_object* v_k_2703_){
_start:
{
uint8_t v_t_boxed_2704_; lean_object* v_res_2705_; 
v_t_boxed_2704_ = lean_unbox(v_t_2701_);
v_res_2705_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(v_motive_2699_, v_ctorIdx_2700_, v_t_boxed_2704_, v_h_2702_, v_k_2703_);
lean_dec(v_k_2703_);
lean_dec(v_ctorIdx_2700_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg(lean_object* v_yes_2706_){
_start:
{
lean_inc(v_yes_2706_);
return v_yes_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg___boxed(lean_object* v_yes_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg(v_yes_2707_);
lean_dec(v_yes_2707_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(lean_object* v_motive_2709_, uint8_t v_t_2710_, lean_object* v_h_2711_, lean_object* v_yes_2712_){
_start:
{
lean_inc(v_yes_2712_);
return v_yes_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___boxed(lean_object* v_motive_2713_, lean_object* v_t_2714_, lean_object* v_h_2715_, lean_object* v_yes_2716_){
_start:
{
uint8_t v_t_boxed_2717_; lean_object* v_res_2718_; 
v_t_boxed_2717_ = lean_unbox(v_t_2714_);
v_res_2718_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(v_motive_2713_, v_t_boxed_2717_, v_h_2715_, v_yes_2716_);
lean_dec(v_yes_2716_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg(lean_object* v_no_2719_){
_start:
{
lean_inc(v_no_2719_);
return v_no_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg___boxed(lean_object* v_no_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg(v_no_2720_);
lean_dec(v_no_2720_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim(lean_object* v_motive_2722_, uint8_t v_t_2723_, lean_object* v_h_2724_, lean_object* v_no_2725_){
_start:
{
lean_inc(v_no_2725_);
return v_no_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___boxed(lean_object* v_motive_2726_, lean_object* v_t_2727_, lean_object* v_h_2728_, lean_object* v_no_2729_){
_start:
{
uint8_t v_t_boxed_2730_; lean_object* v_res_2731_; 
v_t_boxed_2730_ = lean_unbox(v_t_2727_);
v_res_2731_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim(v_motive_2726_, v_t_boxed_2730_, v_h_2728_, v_no_2729_);
lean_dec(v_no_2729_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg(lean_object* v_optional_2732_){
_start:
{
lean_inc(v_optional_2732_);
return v_optional_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg___boxed(lean_object* v_optional_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg(v_optional_2733_);
lean_dec(v_optional_2733_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(lean_object* v_motive_2735_, uint8_t v_t_2736_, lean_object* v_h_2737_, lean_object* v_optional_2738_){
_start:
{
lean_inc(v_optional_2738_);
return v_optional_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___boxed(lean_object* v_motive_2739_, lean_object* v_t_2740_, lean_object* v_h_2741_, lean_object* v_optional_2742_){
_start:
{
uint8_t v_t_boxed_2743_; lean_object* v_res_2744_; 
v_t_boxed_2743_ = lean_unbox(v_t_2740_);
v_res_2744_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(v_motive_2739_, v_t_boxed_2743_, v_h_2741_, v_optional_2742_);
lean_dec(v_optional_2742_);
return v_res_2744_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1(void){
_start:
{
uint32_t v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = 58;
v___x_2749_ = lean_box_uint32(v___x_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(uint8_t v_withColon_2750_, lean_object* v___y_2751_){
_start:
{
if (v_withColon_2750_ == 0)
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1;
v___x_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___y_2751_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
return v___x_2753_;
}
else
{
lean_object* v_fst_2754_; lean_object* v_snd_2755_; lean_object* v___x_2756_; uint8_t v_decide_2757_; 
v_fst_2754_ = lean_ctor_get(v___y_2751_, 0);
v_snd_2755_ = lean_ctor_get(v___y_2751_, 1);
v___x_2756_ = lean_string_utf8_byte_size(v_fst_2754_);
v_decide_2757_ = lean_nat_dec_eq(v_snd_2755_, v___x_2756_);
if (v_decide_2757_ == 0)
{
uint32_t v___x_2758_; uint32_t v_c_2759_; uint8_t v___x_2760_; 
v___x_2758_ = 58;
v_c_2759_ = lean_string_utf8_get_fast(v_fst_2754_, v_snd_2755_);
v___x_2760_ = lean_uint32_dec_eq(v_c_2759_, v___x_2758_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__1));
v___x_2762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___y_2751_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
return v___x_2762_;
}
else
{
lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2772_; 
lean_inc(v_snd_2755_);
lean_inc(v_fst_2754_);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___y_2751_);
if (v_isSharedCheck_2772_ == 0)
{
lean_object* v_unused_2773_; lean_object* v_unused_2774_; 
v_unused_2773_ = lean_ctor_get(v___y_2751_, 1);
lean_dec(v_unused_2773_);
v_unused_2774_ = lean_ctor_get(v___y_2751_, 0);
lean_dec(v_unused_2774_);
v___x_2764_ = v___y_2751_;
v_isShared_2765_ = v_isSharedCheck_2772_;
goto v_resetjp_2763_;
}
else
{
lean_dec(v___y_2751_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2772_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2766_; lean_object* v_it_x27_2768_; 
v___x_2766_ = lean_string_utf8_next_fast(v_fst_2754_, v_snd_2755_);
lean_dec(v_snd_2755_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 1, v___x_2766_);
v_it_x27_2768_ = v___x_2764_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_fst_2754_);
lean_ctor_set(v_reuseFailAlloc_2771_, 1, v___x_2766_);
v_it_x27_2768_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2769_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1;
v___x_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2770_, 0, v_it_x27_2768_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
return v___x_2770_;
}
}
}
}
else
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2775_ = lean_box(0);
v___x_2776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___y_2751_);
lean_ctor_set(v___x_2776_, 1, v___x_2775_);
return v___x_2776_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed(lean_object* v_withColon_2777_, lean_object* v___y_2778_){
_start:
{
uint8_t v_withColon_boxed_2779_; lean_object* v_res_2780_; 
v_withColon_boxed_2779_ = lean_unbox(v_withColon_2777_);
v_res_2780_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(v_withColon_boxed_2779_, v___y_2778_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1(lean_object* v_a_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = lean_nat_to_int(v_a_2781_);
v___x_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2784_, 0, v___y_2782_);
lean_ctor_set(v___x_2784_, 1, v___x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(lean_object* v___y_2785_, lean_object* v___f_2786_, lean_object* v_n_2787_, uint8_t v_reason_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v_pos_2791_; lean_object* v_err_2792_; 
switch(v_reason_2788_)
{
case 0:
{
lean_object* v___x_2808_; 
v___x_2808_ = lean_apply_1(v___y_2785_, v___y_2789_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_pos_2809_; lean_object* v___x_2810_; 
v_pos_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_pos_2809_);
lean_dec_ref_known(v___x_2808_, 2);
v___x_2810_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_2809_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_pos_2811_; lean_object* v_res_2812_; lean_object* v___x_2813_; 
v_pos_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_pos_2811_);
v_res_2812_ = lean_ctor_get(v___x_2810_, 1);
lean_inc(v_res_2812_);
lean_dec_ref_known(v___x_2810_, 2);
v___x_2813_ = lean_apply_2(v___f_2786_, v_res_2812_, v_pos_2811_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_pos_2814_; lean_object* v_res_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2823_; 
v_pos_2814_ = lean_ctor_get(v___x_2813_, 0);
v_res_2815_ = lean_ctor_get(v___x_2813_, 1);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2817_ = v___x_2813_;
v_isShared_2818_ = v_isSharedCheck_2823_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_res_2815_);
lean_inc(v_pos_2814_);
lean_dec(v___x_2813_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2823_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2819_, 0, v_res_2815_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 1, v___x_2819_);
v___x_2821_ = v___x_2817_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_pos_2814_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v___x_2819_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
else
{
lean_object* v_pos_2824_; lean_object* v_err_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
v_pos_2824_ = lean_ctor_get(v___x_2813_, 0);
v_err_2825_ = lean_ctor_get(v___x_2813_, 1);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2813_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_err_2825_);
lean_inc(v_pos_2824_);
lean_dec(v___x_2813_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_pos_2824_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_err_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
else
{
lean_object* v_pos_2833_; lean_object* v_err_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec_ref(v___f_2786_);
v_pos_2833_ = lean_ctor_get(v___x_2810_, 0);
v_err_2834_ = lean_ctor_get(v___x_2810_, 1);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2810_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_err_2834_);
lean_inc(v_pos_2833_);
lean_dec(v___x_2810_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_pos_2833_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_err_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
else
{
lean_object* v_pos_2842_; lean_object* v_err_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec_ref(v___f_2786_);
v_pos_2842_ = lean_ctor_get(v___x_2808_, 0);
v_err_2843_ = lean_ctor_get(v___x_2808_, 1);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2808_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_err_2843_);
lean_inc(v_pos_2842_);
lean_dec(v___x_2808_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_pos_2842_);
lean_ctor_set(v_reuseFailAlloc_2849_, 1, v_err_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
case 1:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
lean_dec_ref(v___f_2786_);
lean_dec_ref(v___y_2785_);
v___x_2851_ = lean_box(0);
v___x_2852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___y_2789_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
return v___x_2852_;
}
default: 
{
lean_object* v___x_2853_; 
lean_inc_ref(v___y_2789_);
v___x_2853_ = lean_apply_1(v___y_2785_, v___y_2789_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_pos_2854_; lean_object* v___x_2855_; 
v_pos_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_pos_2854_);
lean_dec_ref_known(v___x_2853_, 2);
v___x_2855_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_2854_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_pos_2856_; lean_object* v_res_2857_; lean_object* v___x_2858_; 
v_pos_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_pos_2856_);
v_res_2857_ = lean_ctor_get(v___x_2855_, 1);
lean_inc(v_res_2857_);
lean_dec_ref_known(v___x_2855_, 2);
v___x_2858_ = lean_apply_2(v___f_2786_, v_res_2857_, v_pos_2856_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_pos_2859_; lean_object* v_res_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2868_; 
lean_dec_ref(v___y_2789_);
v_pos_2859_ = lean_ctor_get(v___x_2858_, 0);
v_res_2860_ = lean_ctor_get(v___x_2858_, 1);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2862_ = v___x_2858_;
v_isShared_2863_ = v_isSharedCheck_2868_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_res_2860_);
lean_inc(v_pos_2859_);
lean_dec(v___x_2858_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2868_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2864_; lean_object* v___x_2866_; 
v___x_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2864_, 0, v_res_2860_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 1, v___x_2864_);
v___x_2866_ = v___x_2862_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_pos_2859_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
else
{
lean_object* v_pos_2869_; lean_object* v_err_2870_; 
v_pos_2869_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_pos_2869_);
v_err_2870_ = lean_ctor_get(v___x_2858_, 1);
lean_inc(v_err_2870_);
lean_dec_ref_known(v___x_2858_, 2);
v_pos_2791_ = v_pos_2869_;
v_err_2792_ = v_err_2870_;
goto v___jp_2790_;
}
}
else
{
lean_object* v_pos_2871_; lean_object* v_err_2872_; 
lean_dec_ref(v___f_2786_);
v_pos_2871_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_pos_2871_);
v_err_2872_ = lean_ctor_get(v___x_2855_, 1);
lean_inc(v_err_2872_);
lean_dec_ref_known(v___x_2855_, 2);
v_pos_2791_ = v_pos_2871_;
v_err_2792_ = v_err_2872_;
goto v___jp_2790_;
}
}
else
{
lean_object* v_pos_2873_; lean_object* v_err_2874_; 
lean_dec_ref(v___f_2786_);
v_pos_2873_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_pos_2873_);
v_err_2874_ = lean_ctor_get(v___x_2853_, 1);
lean_inc(v_err_2874_);
lean_dec_ref_known(v___x_2853_, 2);
v_pos_2791_ = v_pos_2873_;
v_err_2792_ = v_err_2874_;
goto v___jp_2790_;
}
}
}
v___jp_2790_:
{
lean_object* v_snd_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2806_; 
v_snd_2793_ = lean_ctor_get(v___y_2789_, 1);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___y_2789_);
if (v_isSharedCheck_2806_ == 0)
{
lean_object* v_unused_2807_; 
v_unused_2807_ = lean_ctor_get(v___y_2789_, 0);
lean_dec(v_unused_2807_);
v___x_2795_ = v___y_2789_;
v_isShared_2796_ = v_isSharedCheck_2806_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_snd_2793_);
lean_dec(v___y_2789_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2806_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v_snd_2797_; uint8_t v_decide_2798_; 
v_snd_2797_ = lean_ctor_get(v_pos_2791_, 1);
v_decide_2798_ = lean_nat_dec_eq(v_snd_2793_, v_snd_2797_);
lean_dec(v_snd_2793_);
if (v_decide_2798_ == 0)
{
lean_object* v___x_2800_; 
if (v_isShared_2796_ == 0)
{
lean_ctor_set_tag(v___x_2795_, 1);
lean_ctor_set(v___x_2795_, 1, v_err_2792_);
lean_ctor_set(v___x_2795_, 0, v_pos_2791_);
v___x_2800_ = v___x_2795_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_pos_2791_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_err_2792_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
else
{
lean_object* v___x_2802_; lean_object* v___x_2804_; 
lean_dec(v_err_2792_);
v___x_2802_ = lean_box(0);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 1, v___x_2802_);
lean_ctor_set(v___x_2795_, 0, v_pos_2791_);
v___x_2804_ = v___x_2795_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_pos_2791_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v___x_2802_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2___boxed(lean_object* v___y_2875_, lean_object* v___f_2876_, lean_object* v_n_2877_, lean_object* v_reason_2878_, lean_object* v___y_2879_){
_start:
{
uint8_t v_reason_boxed_2880_; lean_object* v_res_2881_; 
v_reason_boxed_2880_ = lean_unbox(v_reason_2878_);
v_res_2881_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_2875_, v___f_2876_, v_n_2877_, v_reason_boxed_2880_, v___y_2879_);
lean_dec_ref(v_n_2877_);
return v_res_2881_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2(void){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = lean_unsigned_to_nat(3600u);
v___x_2885_ = lean_nat_to_int(v___x_2884_);
return v___x_2885_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4(void){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2887_ = lean_unsigned_to_nat(1u);
v___x_2888_ = l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_dropSeconds_spec__0(v___x_2887_);
return v___x_2888_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5(void){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_unsigned_to_nat(59u);
v___x_2890_ = lean_nat_to_int(v___x_2889_);
return v___x_2890_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8(void){
_start:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2893_ = lean_unsigned_to_nat(23u);
v___x_2894_ = lean_nat_to_int(v___x_2893_);
return v___x_2894_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = lean_unsigned_to_nat(60u);
v___x_2896_ = l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_dropSeconds_spec__0(v___x_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(uint8_t v_withMinutes_2898_, uint8_t v_withSeconds_2899_, uint8_t v_withColon_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v_fst_2943_; lean_object* v_snd_2944_; lean_object* v___x_2945_; lean_object* v___y_2946_; lean_object* v___f_2947_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v_pos_2994_; lean_object* v_res_2995_; lean_object* v_pos_3053_; lean_object* v_fst_3054_; lean_object* v_snd_3055_; lean_object* v_err_3056_; lean_object* v___x_3071_; uint8_t v_decide_3072_; 
v_fst_2943_ = lean_ctor_get(v_a_2901_, 0);
lean_inc(v_fst_2943_);
v_snd_2944_ = lean_ctor_get(v_a_2901_, 1);
lean_inc(v_snd_2944_);
v___x_2945_ = lean_box(v_withColon_2900_);
v___y_2946_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed), 2, 1);
lean_closure_set(v___y_2946_, 0, v___x_2945_);
v___f_2947_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3));
v___x_3071_ = lean_string_utf8_byte_size(v_fst_2943_);
v_decide_3072_ = lean_nat_dec_eq(v_snd_2944_, v___x_3071_);
if (v_decide_3072_ == 0)
{
uint32_t v___x_3073_; uint32_t v_c_3074_; uint8_t v___x_3075_; 
v___x_3073_ = 43;
v_c_3074_ = lean_string_utf8_get_fast(v_fst_2943_, v_snd_2944_);
v___x_3075_ = lean_uint32_dec_eq(v_c_3074_, v___x_3073_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; 
v___x_3076_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__5));
lean_inc(v_snd_2944_);
v_pos_3053_ = v_a_2901_;
v_fst_3054_ = v_fst_2943_;
v_snd_3055_ = v_snd_2944_;
v_err_3056_ = v___x_3076_;
goto v___jp_3052_;
}
else
{
lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3085_; 
v_isSharedCheck_3085_ = !lean_is_exclusive(v_a_2901_);
if (v_isSharedCheck_3085_ == 0)
{
lean_object* v_unused_3086_; lean_object* v_unused_3087_; 
v_unused_3086_ = lean_ctor_get(v_a_2901_, 1);
lean_dec(v_unused_3086_);
v_unused_3087_ = lean_ctor_get(v_a_2901_, 0);
lean_dec(v_unused_3087_);
v___x_3078_ = v_a_2901_;
v_isShared_3079_ = v_isSharedCheck_3085_;
goto v_resetjp_3077_;
}
else
{
lean_dec(v_a_2901_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3085_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; lean_object* v_it_x27_3082_; 
v___x_3080_ = lean_string_utf8_next_fast(v_fst_2943_, v_snd_2944_);
lean_dec(v_snd_2944_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 1, v___x_3080_);
v_it_x27_3082_ = v___x_3078_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_fst_2943_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v___x_3080_);
v_it_x27_3082_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3083_; 
v___x_3083_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v_pos_2994_ = v_it_x27_3082_;
v_res_2995_ = v___x_3083_;
goto v___jp_2993_;
}
}
}
}
else
{
lean_object* v___x_3088_; 
v___x_3088_ = lean_box(0);
lean_inc(v_snd_2944_);
v_pos_3053_ = v_a_2901_;
v_fst_3054_ = v_fst_2943_;
v_snd_3055_ = v_snd_2944_;
v_err_3056_ = v___x_3088_;
goto v___jp_3052_;
}
v___jp_2902_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2905_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0));
v___x_2906_ = l_Int_repr(v___y_2904_);
lean_dec(v___y_2904_);
v___x_2907_ = lean_string_append(v___x_2905_, v___x_2906_);
lean_dec_ref(v___x_2906_);
v___x_2908_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__1));
v___x_2909_ = lean_string_append(v___x_2907_, v___x_2908_);
v___x_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
v___x_2911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___y_2903_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
return v___x_2911_;
}
v___jp_2912_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2917_ = lean_int_add(v___y_2913_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec(v___y_2913_);
v___x_2918_ = lean_int_mul(v___x_2917_, v___y_2915_);
lean_dec(v___x_2917_);
v___x_2919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___y_2914_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
return v___x_2919_;
}
v___jp_2920_:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2928_ = lean_nat_to_int(v___y_2926_);
v___x_2929_ = lean_int_mul(v___y_2927_, v___x_2928_);
lean_dec(v___x_2928_);
lean_dec(v___y_2927_);
v___x_2930_ = lean_int_add(v___y_2921_, v___x_2929_);
lean_dec(v___x_2929_);
lean_dec(v___y_2921_);
if (lean_obj_tag(v___y_2923_) == 0)
{
lean_inc(v___y_2922_);
v___y_2913_ = v___x_2930_;
v___y_2914_ = v___y_2925_;
v___y_2915_ = v___y_2924_;
v___y_2916_ = v___y_2922_;
goto v___jp_2912_;
}
else
{
lean_object* v_val_2931_; 
v_val_2931_ = lean_ctor_get(v___y_2923_, 0);
lean_inc(v_val_2931_);
lean_dec_ref_known(v___y_2923_, 1);
v___y_2913_ = v___x_2930_;
v___y_2914_ = v___y_2925_;
v___y_2915_ = v___y_2924_;
v___y_2916_ = v_val_2931_;
goto v___jp_2912_;
}
}
v___jp_2932_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2);
v___x_2941_ = lean_int_mul(v___y_2937_, v___x_2940_);
lean_dec(v___y_2937_);
if (lean_obj_tag(v___y_2933_) == 0)
{
lean_inc(v___y_2934_);
v___y_2921_ = v___x_2941_;
v___y_2922_ = v___y_2934_;
v___y_2923_ = v___y_2935_;
v___y_2924_ = v___y_2936_;
v___y_2925_ = v___y_2939_;
v___y_2926_ = v___y_2938_;
v___y_2927_ = v___y_2934_;
goto v___jp_2920_;
}
else
{
lean_object* v_val_2942_; 
v_val_2942_ = lean_ctor_get(v___y_2933_, 0);
lean_inc(v_val_2942_);
lean_dec_ref_known(v___y_2933_, 1);
v___y_2921_ = v___x_2941_;
v___y_2922_ = v___y_2934_;
v___y_2923_ = v___y_2935_;
v___y_2924_ = v___y_2936_;
v___y_2925_ = v___y_2939_;
v___y_2926_ = v___y_2938_;
v___y_2927_ = v_val_2942_;
goto v___jp_2920_;
}
}
v___jp_2948_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4);
v___x_2956_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_2946_, v___f_2947_, v___x_2955_, v_withSeconds_2899_, v___y_2954_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_res_2957_; 
v_res_2957_ = lean_ctor_get(v___x_2956_, 1);
lean_inc(v_res_2957_);
if (lean_obj_tag(v_res_2957_) == 1)
{
lean_object* v_pos_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2981_; 
v_pos_2958_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2981_ == 0)
{
lean_object* v_unused_2982_; 
v_unused_2982_ = lean_ctor_get(v___x_2956_, 1);
lean_dec(v_unused_2982_);
v___x_2960_ = v___x_2956_;
v_isShared_2961_ = v_isSharedCheck_2981_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_pos_2958_);
lean_dec(v___x_2956_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2981_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v_val_2962_; lean_object* v___x_2963_; uint8_t v___x_2964_; 
v_val_2962_ = lean_ctor_get(v_res_2957_, 0);
v___x_2963_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5);
v___x_2964_ = lean_int_dec_lt(v___x_2963_, v_val_2962_);
if (v___x_2964_ == 0)
{
lean_del_object(v___x_2960_);
v___y_2933_ = v___y_2950_;
v___y_2934_ = v___y_2949_;
v___y_2935_ = v_res_2957_;
v___y_2936_ = v___y_2951_;
v___y_2937_ = v___y_2952_;
v___y_2938_ = v___y_2953_;
v___y_2939_ = v_pos_2958_;
goto v___jp_2932_;
}
else
{
lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2979_; 
lean_inc(v_val_2962_);
lean_dec(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec(v___y_2950_);
v_isSharedCheck_2979_ = !lean_is_exclusive(v_res_2957_);
if (v_isSharedCheck_2979_ == 0)
{
lean_object* v_unused_2980_; 
v_unused_2980_ = lean_ctor_get(v_res_2957_, 0);
lean_dec(v_unused_2980_);
v___x_2966_ = v_res_2957_;
v_isShared_2967_ = v_isSharedCheck_2979_;
goto v_resetjp_2965_;
}
else
{
lean_dec(v_res_2957_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2979_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2974_; 
v___x_2968_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6));
v___x_2969_ = l_Int_repr(v_val_2962_);
lean_dec(v_val_2962_);
v___x_2970_ = lean_string_append(v___x_2968_, v___x_2969_);
lean_dec_ref(v___x_2969_);
v___x_2971_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__7));
v___x_2972_ = lean_string_append(v___x_2970_, v___x_2971_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 0, v___x_2972_);
v___x_2974_ = v___x_2966_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2976_; 
if (v_isShared_2961_ == 0)
{
lean_ctor_set_tag(v___x_2960_, 1);
lean_ctor_set(v___x_2960_, 1, v___x_2974_);
v___x_2976_ = v___x_2960_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_pos_2958_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v___x_2974_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
}
}
else
{
lean_object* v_pos_2983_; 
v_pos_2983_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_pos_2983_);
lean_dec_ref_known(v___x_2956_, 2);
v___y_2933_ = v___y_2950_;
v___y_2934_ = v___y_2949_;
v___y_2935_ = v_res_2957_;
v___y_2936_ = v___y_2951_;
v___y_2937_ = v___y_2952_;
v___y_2938_ = v___y_2953_;
v___y_2939_ = v_pos_2983_;
goto v___jp_2932_;
}
}
else
{
lean_object* v_pos_2984_; lean_object* v_err_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
lean_dec(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec(v___y_2950_);
v_pos_2984_ = lean_ctor_get(v___x_2956_, 0);
v_err_2985_ = lean_ctor_get(v___x_2956_, 1);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2987_ = v___x_2956_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_err_2985_);
lean_inc(v_pos_2984_);
lean_dec(v___x_2956_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_pos_2984_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_err_2985_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
v___jp_2993_:
{
lean_object* v___x_2996_; 
v___x_2996_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_2994_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_pos_2997_; lean_object* v_res_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; uint8_t v___x_3001_; 
v_pos_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_pos_2997_);
v_res_2998_ = lean_ctor_get(v___x_2996_, 1);
lean_inc(v_res_2998_);
lean_dec_ref_known(v___x_2996_, 2);
v___x_2999_ = lean_nat_to_int(v_res_2998_);
v___x_3000_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_3001_ = lean_int_dec_lt(v___x_2999_, v___x_3000_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; uint8_t v___x_3003_; 
v___x_3002_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8);
v___x_3003_ = lean_int_dec_lt(v___x_3002_, v___x_2999_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3004_ = lean_unsigned_to_nat(60u);
v___x_3005_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9);
lean_inc_ref(v___y_2946_);
v___x_3006_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_2946_, v___f_2947_, v___x_3005_, v_withMinutes_2898_, v_pos_2997_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_res_3007_; 
v_res_3007_ = lean_ctor_get(v___x_3006_, 1);
lean_inc(v_res_3007_);
if (lean_obj_tag(v_res_3007_) == 1)
{
lean_object* v_pos_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3031_; 
v_pos_3008_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3031_ == 0)
{
lean_object* v_unused_3032_; 
v_unused_3032_ = lean_ctor_get(v___x_3006_, 1);
lean_dec(v_unused_3032_);
v___x_3010_ = v___x_3006_;
v_isShared_3011_ = v_isSharedCheck_3031_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_pos_3008_);
lean_dec(v___x_3006_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3031_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v_val_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v_val_3012_ = lean_ctor_get(v_res_3007_, 0);
v___x_3013_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5);
v___x_3014_ = lean_int_dec_lt(v___x_3013_, v_val_3012_);
if (v___x_3014_ == 0)
{
lean_del_object(v___x_3010_);
v___y_2949_ = v___x_3000_;
v___y_2950_ = v_res_3007_;
v___y_2951_ = v_res_2995_;
v___y_2952_ = v___x_2999_;
v___y_2953_ = v___x_3004_;
v___y_2954_ = v_pos_3008_;
goto v___jp_2948_;
}
else
{
lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3029_; 
lean_inc(v_val_3012_);
lean_dec(v___x_2999_);
lean_dec_ref(v___y_2946_);
v_isSharedCheck_3029_ = !lean_is_exclusive(v_res_3007_);
if (v_isSharedCheck_3029_ == 0)
{
lean_object* v_unused_3030_; 
v_unused_3030_ = lean_ctor_get(v_res_3007_, 0);
lean_dec(v_unused_3030_);
v___x_3016_ = v_res_3007_;
v_isShared_3017_ = v_isSharedCheck_3029_;
goto v_resetjp_3015_;
}
else
{
lean_dec(v_res_3007_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3029_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3024_; 
v___x_3018_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10));
v___x_3019_ = l_Int_repr(v_val_3012_);
lean_dec(v_val_3012_);
v___x_3020_ = lean_string_append(v___x_3018_, v___x_3019_);
lean_dec_ref(v___x_3019_);
v___x_3021_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__7));
v___x_3022_ = lean_string_append(v___x_3020_, v___x_3021_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3022_);
v___x_3024_ = v___x_3016_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3026_; 
if (v_isShared_3011_ == 0)
{
lean_ctor_set_tag(v___x_3010_, 1);
lean_ctor_set(v___x_3010_, 1, v___x_3024_);
v___x_3026_ = v___x_3010_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_pos_3008_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v___x_3024_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3033_; 
v_pos_3033_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_pos_3033_);
lean_dec_ref_known(v___x_3006_, 2);
v___y_2949_ = v___x_3000_;
v___y_2950_ = v_res_3007_;
v___y_2951_ = v_res_2995_;
v___y_2952_ = v___x_2999_;
v___y_2953_ = v___x_3004_;
v___y_2954_ = v_pos_3033_;
goto v___jp_2948_;
}
}
else
{
lean_object* v_pos_3034_; lean_object* v_err_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec(v___x_2999_);
lean_dec_ref(v___y_2946_);
v_pos_3034_ = lean_ctor_get(v___x_3006_, 0);
v_err_3035_ = lean_ctor_get(v___x_3006_, 1);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_3006_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_err_3035_);
lean_inc(v_pos_3034_);
lean_dec(v___x_3006_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_pos_3034_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v_err_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
else
{
lean_dec_ref(v___y_2946_);
v___y_2903_ = v_pos_2997_;
v___y_2904_ = v___x_2999_;
goto v___jp_2902_;
}
}
else
{
lean_dec_ref(v___y_2946_);
v___y_2903_ = v_pos_2997_;
v___y_2904_ = v___x_2999_;
goto v___jp_2902_;
}
}
else
{
lean_object* v_pos_3043_; lean_object* v_err_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec_ref(v___y_2946_);
v_pos_3043_ = lean_ctor_get(v___x_2996_, 0);
v_err_3044_ = lean_ctor_get(v___x_2996_, 1);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_2996_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_err_3044_);
lean_inc(v_pos_3043_);
lean_dec(v___x_2996_);
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
v___jp_3052_:
{
uint8_t v_decide_3057_; 
v_decide_3057_ = lean_nat_dec_eq(v_snd_2944_, v_snd_3055_);
lean_dec(v_snd_2944_);
if (v_decide_3057_ == 0)
{
lean_object* v___x_3058_; 
lean_dec(v_snd_3055_);
lean_dec(v_fst_3054_);
lean_dec_ref(v___y_2946_);
lean_inc(v_err_3056_);
v___x_3058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3058_, 0, v_pos_3053_);
lean_ctor_set(v___x_3058_, 1, v_err_3056_);
return v___x_3058_;
}
else
{
lean_object* v___x_3059_; uint8_t v_decide_3060_; 
v___x_3059_ = lean_string_utf8_byte_size(v_fst_3054_);
v_decide_3060_ = lean_nat_dec_eq(v_snd_3055_, v___x_3059_);
if (v_decide_3060_ == 0)
{
uint32_t v___x_3061_; uint32_t v_c_3062_; uint8_t v___x_3063_; 
v___x_3061_ = 45;
v_c_3062_ = lean_string_utf8_get_fast(v_fst_3054_, v_snd_3055_);
v___x_3063_ = lean_uint32_dec_eq(v_c_3062_, v___x_3061_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_dec(v_snd_3055_);
lean_dec(v_fst_3054_);
lean_dec_ref(v___y_2946_);
v___x_3064_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear___closed__3));
v___x_3065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3065_, 0, v_pos_3053_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
return v___x_3065_;
}
else
{
lean_object* v___x_3066_; lean_object* v_it_x27_3067_; lean_object* v___x_3068_; 
lean_dec_ref(v_pos_3053_);
v___x_3066_ = lean_string_utf8_next_fast(v_fst_3054_, v_snd_3055_);
lean_dec(v_snd_3055_);
v_it_x27_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3067_, 0, v_fst_3054_);
lean_ctor_set(v_it_x27_3067_, 1, v___x_3066_);
v___x_3068_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_monthIndex___closed__0);
v_pos_2994_ = v_it_x27_3067_;
v_res_2995_ = v___x_3068_;
goto v___jp_2993_;
}
}
else
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
lean_dec(v_snd_3055_);
lean_dec(v_fst_3054_);
lean_dec_ref(v___y_2946_);
v___x_3069_ = lean_box(0);
v___x_3070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3070_, 0, v_pos_3053_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
return v___x_3070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___boxed(lean_object* v_withMinutes_3089_, lean_object* v_withSeconds_3090_, lean_object* v_withColon_3091_, lean_object* v_a_3092_){
_start:
{
uint8_t v_withMinutes_boxed_3093_; uint8_t v_withSeconds_boxed_3094_; uint8_t v_withColon_boxed_3095_; lean_object* v_res_3096_; 
v_withMinutes_boxed_3093_ = lean_unbox(v_withMinutes_3089_);
v_withSeconds_boxed_3094_ = lean_unbox(v_withSeconds_3090_);
v_withColon_boxed_3095_ = lean_unbox(v_withColon_3091_);
v_res_3096_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v_withMinutes_boxed_3093_, v_withSeconds_boxed_3094_, v_withColon_boxed_3095_, v_a_3092_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffsetX(uint8_t v_x_3097_, lean_object* v_a_3098_){
_start:
{
lean_object* v___y_3100_; 
switch(v_x_3097_)
{
case 0:
{
uint8_t v___x_3105_; uint8_t v___x_3106_; uint8_t v___x_3107_; lean_object* v___x_3108_; 
v___x_3105_ = 2;
v___x_3106_ = 1;
v___x_3107_ = 0;
v___x_3108_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_3105_, v___x_3106_, v___x_3107_, v_a_3098_);
return v___x_3108_;
}
case 1:
{
uint8_t v___x_3109_; uint8_t v___x_3110_; uint8_t v___x_3111_; lean_object* v___x_3112_; 
v___x_3109_ = 0;
v___x_3110_ = 1;
v___x_3111_ = 0;
v___x_3112_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_3109_, v___x_3110_, v___x_3111_, v_a_3098_);
return v___x_3112_;
}
case 3:
{
uint8_t v___x_3113_; uint8_t v___x_3114_; uint8_t v___x_3115_; lean_object* v___x_3116_; 
v___x_3113_ = 0;
v___x_3114_ = 2;
v___x_3115_ = 0;
v___x_3116_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_3113_, v___x_3114_, v___x_3115_, v_a_3098_);
return v___x_3116_;
}
default: 
{
v___y_3100_ = v_a_3098_;
goto v___jp_3099_;
}
}
v___jp_3099_:
{
uint8_t v___x_3101_; uint8_t v___x_3102_; uint8_t v___x_3103_; lean_object* v___x_3104_; 
v___x_3101_ = 0;
v___x_3102_ = 2;
v___x_3103_ = 1;
v___x_3104_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_3101_, v___x_3102_, v___x_3103_, v___y_3100_);
return v___x_3104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffsetX___boxed(lean_object* v_x_3117_, lean_object* v_a_3118_){
_start:
{
uint8_t v_x_88__boxed_3119_; lean_object* v_res_3120_; 
v_x_88__boxed_3119_ = lean_unbox(v_x_3117_);
v_res_3120_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffsetX(v_x_88__boxed_3119_, v_a_3118_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseGmtOffset(uint8_t v_minutes_3121_, lean_object* v_a_3122_){
_start:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3123_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatGmtOffset___closed__0));
v___x_3124_ = l_Std_Internal_Parsec_String_pstring(v___x_3123_, v_a_3122_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_object* v_pos_3125_; uint8_t v___x_3126_; uint8_t v___x_3127_; lean_object* v___x_3128_; 
v_pos_3125_ = lean_ctor_get(v___x_3124_, 0);
lean_inc_n(v_pos_3125_, 2);
lean_dec_ref_known(v___x_3124_, 2);
v___x_3126_ = 2;
v___x_3127_ = 1;
v___x_3128_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v_minutes_3121_, v___x_3126_, v___x_3127_, v_pos_3125_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_dec(v_pos_3125_);
return v___x_3128_;
}
else
{
lean_object* v_pos_3129_; lean_object* v_snd_3130_; lean_object* v_snd_3131_; uint8_t v_decide_3132_; 
v_pos_3129_ = lean_ctor_get(v___x_3128_, 0);
v_snd_3130_ = lean_ctor_get(v_pos_3125_, 1);
lean_inc(v_snd_3130_);
lean_dec(v_pos_3125_);
v_snd_3131_ = lean_ctor_get(v_pos_3129_, 1);
v_decide_3132_ = lean_nat_dec_eq(v_snd_3130_, v_snd_3131_);
lean_dec(v_snd_3130_);
if (v_decide_3132_ == 0)
{
return v___x_3128_;
}
else
{
lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3140_; 
lean_inc(v_pos_3129_);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; lean_object* v_unused_3142_; 
v_unused_3141_ = lean_ctor_get(v___x_3128_, 1);
lean_dec(v_unused_3141_);
v_unused_3142_ = lean_ctor_get(v___x_3128_, 0);
lean_dec(v_unused_3142_);
v___x_3134_ = v___x_3128_;
v_isShared_3135_ = v_isSharedCheck_3140_;
goto v_resetjp_3133_;
}
else
{
lean_dec(v___x_3128_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3140_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3136_; lean_object* v___x_3138_; 
v___x_3136_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_3135_ == 0)
{
lean_ctor_set_tag(v___x_3134_, 0);
lean_ctor_set(v___x_3134_, 1, v___x_3136_);
v___x_3138_ = v___x_3134_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_pos_3129_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v___x_3136_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
}
else
{
lean_object* v_pos_3143_; lean_object* v_err_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
v_pos_3143_ = lean_ctor_get(v___x_3124_, 0);
v_err_3144_ = lean_ctor_get(v___x_3124_, 1);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3124_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_err_3144_);
lean_inc(v_pos_3143_);
lean_dec(v___x_3124_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_pos_3143_);
lean_ctor_set(v_reuseFailAlloc_3150_, 1, v_err_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseGmtOffset___boxed(lean_object* v_minutes_3152_, lean_object* v_a_3153_){
_start:
{
uint8_t v_minutes_boxed_3154_; lean_object* v_res_3155_; 
v_minutes_boxed_3154_ = lean_unbox(v_minutes_3152_);
v_res_3155_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseGmtOffset(v_minutes_boxed_3154_, v_a_3153_);
return v_res_3155_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_isNumericModifier(lean_object* v_x_3156_){
_start:
{
switch(lean_obj_tag(v_x_3156_))
{
case 2:
{
uint8_t v___x_3157_; 
v___x_3157_ = 1;
return v___x_3157_;
}
case 1:
{
uint8_t v___x_3158_; 
v___x_3158_ = 1;
return v___x_3158_;
}
case 9:
{
uint8_t v___x_3159_; 
v___x_3159_ = 1;
return v___x_3159_;
}
case 3:
{
uint8_t v___x_3160_; 
v___x_3160_ = 1;
return v___x_3160_;
}
case 6:
{
uint8_t v___x_3161_; 
v___x_3161_ = 1;
return v___x_3161_;
}
case 10:
{
uint8_t v___x_3162_; 
v___x_3162_ = 1;
return v___x_3162_;
}
case 11:
{
uint8_t v___x_3163_; 
v___x_3163_ = 1;
return v___x_3163_;
}
case 15:
{
uint8_t v___x_3164_; 
v___x_3164_ = 1;
return v___x_3164_;
}
case 19:
{
uint8_t v___x_3165_; 
v___x_3165_ = 1;
return v___x_3165_;
}
case 20:
{
uint8_t v___x_3166_; 
v___x_3166_ = 1;
return v___x_3166_;
}
case 21:
{
uint8_t v___x_3167_; 
v___x_3167_ = 1;
return v___x_3167_;
}
case 22:
{
uint8_t v___x_3168_; 
v___x_3168_ = 1;
return v___x_3168_;
}
case 23:
{
uint8_t v___x_3169_; 
v___x_3169_ = 1;
return v___x_3169_;
}
case 24:
{
uint8_t v___x_3170_; 
v___x_3170_ = 1;
return v___x_3170_;
}
case 25:
{
uint8_t v___x_3171_; 
v___x_3171_ = 1;
return v___x_3171_;
}
case 26:
{
uint8_t v___x_3172_; 
v___x_3172_ = 1;
return v___x_3172_;
}
case 27:
{
uint8_t v___x_3173_; 
v___x_3173_ = 1;
return v___x_3173_;
}
case 28:
{
uint8_t v___x_3174_; 
v___x_3174_ = 1;
return v___x_3174_;
}
case 4:
{
lean_object* v_presentation_3175_; 
v_presentation_3175_ = lean_ctor_get(v_x_3156_, 0);
if (lean_obj_tag(v_presentation_3175_) == 0)
{
uint8_t v___x_3176_; 
v___x_3176_ = 1;
return v___x_3176_;
}
else
{
uint8_t v___x_3177_; 
v___x_3177_ = 0;
return v___x_3177_;
}
}
case 5:
{
lean_object* v_presentation_3178_; 
v_presentation_3178_ = lean_ctor_get(v_x_3156_, 0);
if (lean_obj_tag(v_presentation_3178_) == 0)
{
uint8_t v___x_3179_; 
v___x_3179_ = 1;
return v___x_3179_;
}
else
{
uint8_t v___x_3180_; 
v___x_3180_ = 0;
return v___x_3180_;
}
}
case 7:
{
lean_object* v_presentation_3181_; 
v_presentation_3181_ = lean_ctor_get(v_x_3156_, 0);
if (lean_obj_tag(v_presentation_3181_) == 0)
{
uint8_t v___x_3182_; 
v___x_3182_ = 1;
return v___x_3182_;
}
else
{
uint8_t v___x_3183_; 
v___x_3183_ = 0;
return v___x_3183_;
}
}
case 8:
{
lean_object* v_presentation_3184_; 
v_presentation_3184_ = lean_ctor_get(v_x_3156_, 0);
if (lean_obj_tag(v_presentation_3184_) == 0)
{
uint8_t v___x_3185_; 
v___x_3185_ = 1;
return v___x_3185_;
}
else
{
uint8_t v___x_3186_; 
v___x_3186_ = 0;
return v___x_3186_;
}
}
case 13:
{
lean_object* v_presentation_3187_; 
v_presentation_3187_ = lean_ctor_get(v_x_3156_, 0);
if (lean_obj_tag(v_presentation_3187_) == 0)
{
uint8_t v___x_3188_; 
v___x_3188_ = 1;
return v___x_3188_;
}
else
{
uint8_t v___x_3189_; 
v___x_3189_ = 0;
return v___x_3189_;
}
}
case 14:
{
lean_object* v_presentation_3190_; 
v_presentation_3190_ = lean_ctor_get(v_x_3156_, 0);
if (lean_obj_tag(v_presentation_3190_) == 0)
{
uint8_t v___x_3191_; 
v___x_3191_ = 1;
return v___x_3191_;
}
else
{
uint8_t v___x_3192_; 
v___x_3192_ = 0;
return v___x_3192_;
}
}
default: 
{
uint8_t v___x_3193_; 
v___x_3193_ = 0;
return v___x_3193_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_isNumericModifier___boxed(lean_object* v_x_3194_){
_start:
{
uint8_t v_res_3195_; lean_object* v_r_3196_; 
v_res_3195_ = l___private_Std_Time_Format_Basic_0__Std_Time_isNumericModifier(v_x_3194_);
lean_dec_ref(v_x_3194_);
v_r_3196_ = lean_box(v_res_3195_);
return v_r_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits_covering(lean_object* v_digits_3197_, lean_object* v_p_3198_){
_start:
{
uint8_t v___x_3199_; 
v___x_3199_ = lean_nat_dec_le(v_digits_3197_, v_p_3198_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; 
lean_dec(v_p_3198_);
v___x_3200_ = lean_box(0);
return v___x_3200_;
}
else
{
lean_object* v___x_3201_; 
v___x_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3201_, 0, v_p_3198_);
return v___x_3201_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits_covering___boxed(lean_object* v_digits_3202_, lean_object* v_p_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits_covering(v_digits_3202_, v_p_3203_);
lean_dec(v_digits_3202_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits(lean_object* v_x_3211_){
_start:
{
lean_object* v_p_3217_; lean_object* v_p_3221_; 
switch(lean_obj_tag(v_x_3211_))
{
case 2:
{
lean_object* v_presentation_3224_; 
v_presentation_3224_ = lean_ctor_get(v_x_3211_, 0);
lean_inc(v_presentation_3224_);
lean_dec_ref_known(v_x_3211_, 1);
switch(lean_obj_tag(v_presentation_3224_))
{
case 1:
{
goto v___jp_3212_;
}
case 2:
{
goto v___jp_3214_;
}
default: 
{
lean_object* v___x_3225_; 
lean_dec(v_presentation_3224_);
v___x_3225_ = lean_box(0);
return v___x_3225_;
}
}
}
case 1:
{
lean_object* v_presentation_3226_; 
v_presentation_3226_ = lean_ctor_get(v_x_3211_, 0);
lean_inc(v_presentation_3226_);
lean_dec_ref_known(v_x_3211_, 1);
switch(lean_obj_tag(v_presentation_3226_))
{
case 1:
{
goto v___jp_3212_;
}
case 2:
{
goto v___jp_3214_;
}
default: 
{
lean_object* v___x_3227_; 
lean_dec(v_presentation_3226_);
v___x_3227_ = lean_box(0);
return v___x_3227_;
}
}
}
case 9:
{
lean_object* v_presentation_3228_; 
v_presentation_3228_ = lean_ctor_get(v_x_3211_, 0);
lean_inc(v_presentation_3228_);
lean_dec_ref_known(v_x_3211_, 1);
switch(lean_obj_tag(v_presentation_3228_))
{
case 1:
{
goto v___jp_3212_;
}
case 2:
{
goto v___jp_3214_;
}
default: 
{
lean_object* v___x_3229_; 
lean_dec(v_presentation_3228_);
v___x_3229_ = lean_box(0);
return v___x_3229_;
}
}
}
case 25:
{
lean_object* v_presentation_3230_; 
v_presentation_3230_ = lean_ctor_get(v_x_3211_, 0);
lean_inc(v_presentation_3230_);
lean_dec_ref_known(v_x_3211_, 1);
if (lean_obj_tag(v_presentation_3230_) == 0)
{
lean_object* v___x_3231_; 
v___x_3231_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits___closed__2));
return v___x_3231_;
}
else
{
lean_object* v_digits_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
v_digits_3232_ = lean_ctor_get(v_presentation_3230_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_presentation_3230_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v_presentation_3230_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_digits_3232_);
lean_dec(v_presentation_3230_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_digits_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
case 7:
{
lean_object* v_presentation_3240_; 
v_presentation_3240_ = lean_ctor_get(v_x_3211_, 0);
lean_inc_ref(v_presentation_3240_);
lean_dec_ref_known(v_x_3211_, 1);
if (lean_obj_tag(v_presentation_3240_) == 0)
{
lean_object* v_val_3241_; 
v_val_3241_ = lean_ctor_get(v_presentation_3240_, 0);
lean_inc(v_val_3241_);
lean_dec_ref_known(v_presentation_3240_, 1);
v_p_3217_ = v_val_3241_;
goto v___jp_3216_;
}
else
{
lean_object* v___x_3242_; 
lean_dec_ref(v_presentation_3240_);
v___x_3242_ = lean_box(0);
return v___x_3242_;
}
}
case 8:
{
lean_object* v_presentation_3243_; 
v_presentation_3243_ = lean_ctor_get(v_x_3211_, 0);
lean_inc_ref(v_presentation_3243_);
lean_dec_ref_known(v_x_3211_, 1);
if (lean_obj_tag(v_presentation_3243_) == 0)
{
lean_object* v_val_3244_; 
v_val_3244_ = lean_ctor_get(v_presentation_3243_, 0);
lean_inc(v_val_3244_);
lean_dec_ref_known(v_presentation_3243_, 1);
v_p_3217_ = v_val_3244_;
goto v___jp_3216_;
}
else
{
lean_object* v___x_3245_; 
lean_dec_ref(v_presentation_3243_);
v___x_3245_ = lean_box(0);
return v___x_3245_;
}
}
case 13:
{
lean_object* v_presentation_3246_; 
v_presentation_3246_ = lean_ctor_get(v_x_3211_, 0);
lean_inc_ref(v_presentation_3246_);
lean_dec_ref_known(v_x_3211_, 1);
if (lean_obj_tag(v_presentation_3246_) == 0)
{
lean_object* v_val_3247_; 
v_val_3247_ = lean_ctor_get(v_presentation_3246_, 0);
lean_inc(v_val_3247_);
lean_dec_ref_known(v_presentation_3246_, 1);
v_p_3217_ = v_val_3247_;
goto v___jp_3216_;
}
else
{
lean_object* v___x_3248_; 
lean_dec_ref(v_presentation_3246_);
v___x_3248_ = lean_box(0);
return v___x_3248_;
}
}
case 14:
{
lean_object* v_presentation_3249_; 
v_presentation_3249_ = lean_ctor_get(v_x_3211_, 0);
lean_inc_ref(v_presentation_3249_);
lean_dec_ref_known(v_x_3211_, 1);
if (lean_obj_tag(v_presentation_3249_) == 0)
{
lean_object* v_val_3250_; 
v_val_3250_ = lean_ctor_get(v_presentation_3249_, 0);
lean_inc(v_val_3250_);
lean_dec_ref_known(v_presentation_3249_, 1);
v_p_3217_ = v_val_3250_;
goto v___jp_3216_;
}
else
{
lean_object* v___x_3251_; 
lean_dec_ref(v_presentation_3249_);
v___x_3251_ = lean_box(0);
return v___x_3251_;
}
}
case 11:
{
lean_object* v_presentation_3252_; 
v_presentation_3252_ = lean_ctor_get(v_x_3211_, 0);
lean_inc(v_presentation_3252_);
lean_dec_ref_known(v_x_3211_, 1);
v_p_3217_ = v_presentation_3252_;
goto v___jp_3216_;
}
case 15:
{
lean_object* v_presentation_3253_; 
v_presentation_3253_ = lean_ctor_get(v_x_3211_, 0);
lean_inc(v_presentation_3253_);
lean_dec_ref_known(v_x_3211_, 1);
v_p_3217_ = v_presentation_3253_;
goto v___jp_3216_;
}
case 6:
{
lean_object* v_presentation_3254_; 
v_presentation_3254_ = lean_ctor_get(v_x_3211_, 0);
lean_inc(v_presentation_3254_);
lean_dec_ref_known(v_x_3211_, 1);
v_p_3221_ = v_presentation_3254_;
goto v___jp_3220_;
}
case 10:
{
lean_object* v_presentation_3255_; 
v_presentation_3255_ = lean_ctor_get(v_x_3211_, 0);
lean_inc(v_presentation_3255_);
lean_dec_ref_known(v_x_3211_, 1);
v_p_3221_ = v_presentation_3255_;
goto v___jp_3220_;
}
case 19:
{
lean_object* v_presentation_3256_; 
v_presentation_3256_ = lean_ctor_get(v_x_3211_, 0);
lean_inc(v_presentation_3256_);
lean_dec_ref_known(v_x_3211_, 1);
v_p_3221_ = v_presentation_3256_;
goto v___jp_3220_;
}
case 20:
{
lean_object* v_presentation_3257_; 
v_presentation_3257_ = lean_ctor_get(v_x_3211_, 0);
lean_inc(v_presentation_3257_);
lean_dec_ref_known(v_x_3211_, 1);
v_p_3221_ = v_presentation_3257_;
goto v___jp_3220_;
}
case 21:
{
lean_object* v_presentation_3258_; 
v_presentation_3258_ = lean_ctor_get(v_x_3211_, 0);
lean_inc(v_presentation_3258_);
lean_dec_ref_known(v_x_3211_, 1);
v_p_3221_ = v_presentation_3258_;
goto v___jp_3220_;
}
case 22:
{
lean_object* v_presentation_3259_; 
v_presentation_3259_ = lean_ctor_get(v_x_3211_, 0);
lean_inc(v_presentation_3259_);
lean_dec_ref_known(v_x_3211_, 1);
v_p_3221_ = v_presentation_3259_;
goto v___jp_3220_;
}
case 23:
{
lean_object* v_presentation_3260_; 
v_presentation_3260_ = lean_ctor_get(v_x_3211_, 0);
lean_inc(v_presentation_3260_);
lean_dec_ref_known(v_x_3211_, 1);
v_p_3221_ = v_presentation_3260_;
goto v___jp_3220_;
}
case 24:
{
lean_object* v_presentation_3261_; 
v_presentation_3261_ = lean_ctor_get(v_x_3211_, 0);
lean_inc(v_presentation_3261_);
lean_dec_ref_known(v_x_3211_, 1);
v_p_3221_ = v_presentation_3261_;
goto v___jp_3220_;
}
case 4:
{
lean_object* v_presentation_3262_; 
v_presentation_3262_ = lean_ctor_get(v_x_3211_, 0);
lean_inc_ref(v_presentation_3262_);
lean_dec_ref_known(v_x_3211_, 1);
if (lean_obj_tag(v_presentation_3262_) == 0)
{
lean_object* v_val_3263_; 
v_val_3263_ = lean_ctor_get(v_presentation_3262_, 0);
lean_inc(v_val_3263_);
lean_dec_ref_known(v_presentation_3262_, 1);
v_p_3221_ = v_val_3263_;
goto v___jp_3220_;
}
else
{
lean_object* v___x_3264_; 
lean_dec_ref(v_presentation_3262_);
v___x_3264_ = lean_box(0);
return v___x_3264_;
}
}
case 5:
{
lean_object* v_presentation_3265_; 
v_presentation_3265_ = lean_ctor_get(v_x_3211_, 0);
lean_inc_ref(v_presentation_3265_);
lean_dec_ref_known(v_x_3211_, 1);
if (lean_obj_tag(v_presentation_3265_) == 0)
{
lean_object* v_val_3266_; 
v_val_3266_ = lean_ctor_get(v_presentation_3265_, 0);
lean_inc(v_val_3266_);
lean_dec_ref_known(v_presentation_3265_, 1);
v_p_3221_ = v_val_3266_;
goto v___jp_3220_;
}
else
{
lean_object* v___x_3267_; 
lean_dec_ref(v_presentation_3265_);
v___x_3267_ = lean_box(0);
return v___x_3267_;
}
}
case 3:
{
lean_object* v_presentation_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v_presentation_3268_ = lean_ctor_get(v_x_3211_, 0);
lean_inc(v_presentation_3268_);
lean_dec_ref_known(v_x_3211_, 1);
v___x_3269_ = lean_unsigned_to_nat(3u);
v___x_3270_ = l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits_covering(v___x_3269_, v_presentation_3268_);
return v___x_3270_;
}
case 26:
{
lean_object* v_presentation_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v_presentation_3271_ = lean_ctor_get(v_x_3211_, 0);
lean_inc(v_presentation_3271_);
lean_dec_ref_known(v_x_3211_, 1);
v___x_3272_ = lean_unsigned_to_nat(8u);
v___x_3273_ = l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits_covering(v___x_3272_, v_presentation_3271_);
return v___x_3273_;
}
case 27:
{
lean_object* v_presentation_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v_presentation_3274_ = lean_ctor_get(v_x_3211_, 0);
lean_inc(v_presentation_3274_);
lean_dec_ref_known(v_x_3211_, 1);
v___x_3275_ = lean_unsigned_to_nat(9u);
v___x_3276_ = l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits_covering(v___x_3275_, v_presentation_3274_);
return v___x_3276_;
}
case 28:
{
lean_object* v_presentation_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
v_presentation_3277_ = lean_ctor_get(v_x_3211_, 0);
lean_inc(v_presentation_3277_);
lean_dec_ref_known(v_x_3211_, 1);
v___x_3278_ = lean_unsigned_to_nat(14u);
v___x_3279_ = l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits_covering(v___x_3278_, v_presentation_3277_);
return v___x_3279_;
}
default: 
{
lean_object* v___x_3280_; 
lean_dec_ref(v_x_3211_);
v___x_3280_ = lean_box(0);
return v___x_3280_;
}
}
v___jp_3212_:
{
lean_object* v___x_3213_; 
v___x_3213_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits___closed__0));
return v___x_3213_;
}
v___jp_3214_:
{
lean_object* v___x_3215_; 
v___x_3215_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits___closed__1));
return v___x_3215_;
}
v___jp_3216_:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = lean_unsigned_to_nat(1u);
v___x_3219_ = l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits_covering(v___x_3218_, v_p_3217_);
return v___x_3219_;
}
v___jp_3220_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = lean_unsigned_to_nat(2u);
v___x_3223_ = l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits_covering(v___x_3222_, v_p_3221_);
return v___x_3223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseField(lean_object* v_m_3281_, lean_object* v_width_3282_, lean_object* v_reserve_3283_, lean_object* v_a_3284_){
_start:
{
lean_object* v___x_3285_; 
v___x_3285_ = l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits(v_m_3281_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v___x_3286_; 
v___x_3286_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseVarWidthNum(v_width_3282_, v_reserve_3283_, v_a_3284_);
return v___x_3286_;
}
else
{
lean_object* v_val_3287_; lean_object* v___x_3288_; 
lean_dec(v_width_3282_);
v_val_3287_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_val_3287_);
lean_dec_ref_known(v___x_3285_, 1);
v___x_3288_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_val_3287_, v_a_3284_);
return v___x_3288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseField___boxed(lean_object* v_m_3289_, lean_object* v_width_3290_, lean_object* v_reserve_3291_, lean_object* v_a_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseField(v_m_3289_, v_width_3290_, v_reserve_3291_, v_a_3292_);
lean_dec(v_reserve_3291_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_reservedDigits(lean_object* v_x_3296_){
_start:
{
if (lean_obj_tag(v_x_3296_) == 1)
{
lean_object* v_head_3299_; 
v_head_3299_ = lean_ctor_get(v_x_3296_, 0);
lean_inc(v_head_3299_);
if (lean_obj_tag(v_head_3299_) == 1)
{
lean_object* v_tail_3300_; lean_object* v_modifier_3301_; uint8_t v___x_3302_; 
v_tail_3300_ = lean_ctor_get(v_x_3296_, 1);
lean_inc(v_tail_3300_);
lean_dec_ref_known(v_x_3296_, 2);
v_modifier_3301_ = lean_ctor_get(v_head_3299_, 0);
lean_inc_ref(v_modifier_3301_);
lean_dec_ref_known(v_head_3299_, 1);
v___x_3302_ = l___private_Std_Time_Format_Basic_0__Std_Time_isNumericModifier(v_modifier_3301_);
if (v___x_3302_ == 0)
{
lean_object* v___x_3303_; 
lean_dec_ref(v_modifier_3301_);
lean_dec(v_tail_3300_);
v___x_3303_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_reservedDigits___closed__0));
return v___x_3303_;
}
else
{
lean_object* v___x_3304_; 
v___x_3304_ = l___private_Std_Time_Format_Basic_0__Std_Time_fixedDigits(v_modifier_3301_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_dec(v_tail_3300_);
return v___x_3304_;
}
else
{
lean_object* v_val_3305_; lean_object* v___x_3306_; 
v_val_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_val_3305_);
lean_dec_ref_known(v___x_3304_, 1);
v___x_3306_ = l___private_Std_Time_Format_Basic_0__Std_Time_reservedDigits(v_tail_3300_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_dec(v_val_3305_);
return v___x_3306_;
}
else
{
lean_object* v_val_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3315_; 
v_val_3307_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3309_ = v___x_3306_;
v_isShared_3310_ = v_isSharedCheck_3315_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_val_3307_);
lean_dec(v___x_3306_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3315_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; lean_object* v___x_3313_; 
v___x_3311_ = lean_nat_add(v_val_3305_, v_val_3307_);
lean_dec(v_val_3307_);
lean_dec(v_val_3305_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v___x_3311_);
v___x_3313_ = v___x_3309_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3311_);
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
}
}
else
{
lean_dec_ref_known(v_x_3296_, 2);
lean_dec(v_head_3299_);
goto v___jp_3297_;
}
}
else
{
lean_dec(v_x_3296_);
goto v___jp_3297_;
}
v___jp_3297_:
{
lean_object* v___x_3298_; 
v___x_3298_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_reservedDigits___closed__0));
return v___x_3298_;
}
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = lean_unsigned_to_nat(2000u);
v___x_3317_ = lean_nat_to_int(v___x_3316_);
return v___x_3317_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__3(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3321_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3322_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_3323_ = lean_int_sub(v___x_3322_, v___x_3321_);
return v___x_3323_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v_range_3326_; 
v___x_3324_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3325_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__3);
v_range_3326_ = lean_int_add(v___x_3325_, v___x_3324_);
return v_range_3326_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(lean_object* v_config_3329_, lean_object* v_reserve_3330_, lean_object* v_x_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v___y_3334_; 
switch(lean_obj_tag(v_x_3331_))
{
case 0:
{
lean_object* v_dateformat_3337_; uint8_t v_presentation_3338_; lean_object* v_symbols_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
lean_dec(v_reserve_3330_);
v_dateformat_3337_ = lean_ctor_get(v_config_3329_, 0);
lean_inc_ref(v_dateformat_3337_);
lean_dec_ref(v_config_3329_);
v_presentation_3338_ = lean_ctor_get_uint8(v_x_3331_, 0);
lean_dec_ref_known(v_x_3331_, 0);
v_symbols_3339_ = lean_ctor_get(v_dateformat_3337_, 1);
lean_inc_ref(v_symbols_3339_);
lean_dec_ref(v_dateformat_3337_);
v___x_3340_ = lean_unsigned_to_nat(2u);
v___x_3341_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraNames(v_symbols_3339_, v_presentation_3338_);
lean_dec_ref(v_symbols_3339_);
v___x_3342_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseName(v___x_3340_, v___x_3341_, v_a_3332_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_pos_3343_; lean_object* v_res_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3353_; 
v_pos_3343_ = lean_ctor_get(v___x_3342_, 0);
v_res_3344_ = lean_ctor_get(v___x_3342_, 1);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3346_ = v___x_3342_;
v_isShared_3347_ = v_isSharedCheck_3353_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_res_3344_);
lean_inc(v_pos_3343_);
lean_dec(v___x_3342_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3353_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
uint8_t v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3351_; 
v___x_3348_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(v_res_3344_);
lean_dec(v_res_3344_);
v___x_3349_ = lean_box(v___x_3348_);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 1, v___x_3349_);
v___x_3351_ = v___x_3346_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_pos_3343_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v___x_3349_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
else
{
lean_object* v_pos_3354_; lean_object* v_err_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
v_pos_3354_ = lean_ctor_get(v___x_3342_, 0);
v_err_3355_ = lean_ctor_get(v___x_3342_, 1);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v___x_3342_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_err_3355_);
lean_inc(v_pos_3354_);
lean_dec(v___x_3342_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_pos_3354_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_err_3355_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
case 1:
{
lean_object* v_presentation_3363_; 
lean_dec_ref(v_config_3329_);
v_presentation_3363_ = lean_ctor_get(v_x_3331_, 0);
lean_inc(v_presentation_3363_);
lean_dec_ref_known(v_x_3331_, 1);
switch(lean_obj_tag(v_presentation_3363_))
{
case 0:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3364_ = lean_unsigned_to_nat(1u);
v___x_3365_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseVarWidthNum___boxed), 3, 2);
lean_closure_set(v___x_3365_, 0, v___x_3364_);
lean_closure_set(v___x_3365_, 1, v_reserve_3330_);
v___x_3366_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3365_, v_a_3332_);
return v___x_3366_;
}
case 1:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
lean_dec(v_reserve_3330_);
v___x_3367_ = lean_unsigned_to_nat(2u);
v___x_3368_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3367_, v_a_3332_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_pos_3369_; lean_object* v_res_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3380_; 
v_pos_3369_ = lean_ctor_get(v___x_3368_, 0);
v_res_3370_ = lean_ctor_get(v___x_3368_, 1);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3372_ = v___x_3368_;
v_isShared_3373_ = v_isSharedCheck_3380_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_res_3370_);
lean_inc(v_pos_3369_);
lean_dec(v___x_3368_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3380_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3378_; 
v___x_3374_ = lean_nat_to_int(v_res_3370_);
v___x_3375_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0);
v___x_3376_ = lean_int_add(v___x_3375_, v___x_3374_);
lean_dec(v___x_3374_);
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 1, v___x_3376_);
v___x_3378_ = v___x_3372_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_pos_3369_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v___x_3376_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
else
{
lean_object* v_pos_3381_; lean_object* v_err_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
v_pos_3381_ = lean_ctor_get(v___x_3368_, 0);
v_err_3382_ = lean_ctor_get(v___x_3368_, 1);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3368_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_err_3382_);
lean_inc(v_pos_3381_);
lean_dec(v___x_3368_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_pos_3381_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v_err_3382_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
case 2:
{
uint8_t v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = 1;
v___x_3391_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear(v___x_3390_, v_reserve_3330_, v_a_3332_);
lean_dec(v_reserve_3330_);
return v___x_3391_;
}
default: 
{
lean_object* v_num_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v_num_3392_ = lean_ctor_get(v_presentation_3363_, 0);
lean_inc(v_num_3392_);
lean_dec_ref_known(v_presentation_3363_, 1);
v___x_3393_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseVarWidthNum___boxed), 3, 2);
lean_closure_set(v___x_3393_, 0, v_num_3392_);
lean_closure_set(v___x_3393_, 1, v_reserve_3330_);
v___x_3394_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3393_, v_a_3332_);
return v___x_3394_;
}
}
}
case 2:
{
lean_object* v_presentation_3395_; 
lean_dec_ref(v_config_3329_);
v_presentation_3395_ = lean_ctor_get(v_x_3331_, 0);
lean_inc(v_presentation_3395_);
lean_dec_ref_known(v_x_3331_, 1);
switch(lean_obj_tag(v_presentation_3395_))
{
case 0:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3396_ = lean_unsigned_to_nat(1u);
v___x_3397_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseVarWidthNum(v___x_3396_, v_reserve_3330_, v_a_3332_);
lean_dec(v_reserve_3330_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_pos_3398_; lean_object* v_res_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3407_; 
v_pos_3398_ = lean_ctor_get(v___x_3397_, 0);
v_res_3399_ = lean_ctor_get(v___x_3397_, 1);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3401_ = v___x_3397_;
v_isShared_3402_ = v_isSharedCheck_3407_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_res_3399_);
lean_inc(v_pos_3398_);
lean_dec(v___x_3397_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3407_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3403_; lean_object* v___x_3405_; 
v___x_3403_ = lean_nat_to_int(v_res_3399_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 1, v___x_3403_);
v___x_3405_ = v___x_3401_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_pos_3398_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
else
{
lean_object* v_pos_3408_; lean_object* v_err_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
v_pos_3408_ = lean_ctor_get(v___x_3397_, 0);
v_err_3409_ = lean_ctor_get(v___x_3397_, 1);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3397_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_err_3409_);
lean_inc(v_pos_3408_);
lean_dec(v___x_3397_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_pos_3408_);
lean_ctor_set(v_reuseFailAlloc_3415_, 1, v_err_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
case 1:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
lean_dec(v_reserve_3330_);
v___x_3417_ = lean_unsigned_to_nat(2u);
v___x_3418_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3417_, v_a_3332_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_pos_3419_; lean_object* v_res_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3430_; 
v_pos_3419_ = lean_ctor_get(v___x_3418_, 0);
v_res_3420_ = lean_ctor_get(v___x_3418_, 1);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3422_ = v___x_3418_;
v_isShared_3423_ = v_isSharedCheck_3430_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_res_3420_);
lean_inc(v_pos_3419_);
lean_dec(v___x_3418_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3430_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3428_; 
v___x_3424_ = lean_nat_to_int(v_res_3420_);
v___x_3425_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0);
v___x_3426_ = lean_int_add(v___x_3425_, v___x_3424_);
lean_dec(v___x_3424_);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 1, v___x_3426_);
v___x_3428_ = v___x_3422_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_pos_3419_);
lean_ctor_set(v_reuseFailAlloc_3429_, 1, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
else
{
lean_object* v_pos_3431_; lean_object* v_err_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
v_pos_3431_ = lean_ctor_get(v___x_3418_, 0);
v_err_3432_ = lean_ctor_get(v___x_3418_, 1);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3434_ = v___x_3418_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_err_3432_);
lean_inc(v_pos_3431_);
lean_dec(v___x_3418_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_pos_3431_);
lean_ctor_set(v_reuseFailAlloc_3438_, 1, v_err_3432_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
case 2:
{
uint8_t v___x_3440_; lean_object* v___x_3441_; 
v___x_3440_ = 0;
v___x_3441_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear(v___x_3440_, v_reserve_3330_, v_a_3332_);
lean_dec(v_reserve_3330_);
return v___x_3441_;
}
default: 
{
lean_object* v_num_3442_; lean_object* v___x_3443_; 
v_num_3442_ = lean_ctor_get(v_presentation_3395_, 0);
lean_inc(v_num_3442_);
lean_dec_ref_known(v_presentation_3395_, 1);
v___x_3443_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseVarWidthNum(v_num_3442_, v_reserve_3330_, v_a_3332_);
lean_dec(v_reserve_3330_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_pos_3444_; lean_object* v_res_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3453_; 
v_pos_3444_ = lean_ctor_get(v___x_3443_, 0);
v_res_3445_ = lean_ctor_get(v___x_3443_, 1);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3447_ = v___x_3443_;
v_isShared_3448_ = v_isSharedCheck_3453_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_res_3445_);
lean_inc(v_pos_3444_);
lean_dec(v___x_3443_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3453_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3449_; lean_object* v___x_3451_; 
v___x_3449_ = lean_nat_to_int(v_res_3445_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 1, v___x_3449_);
v___x_3451_ = v___x_3447_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_pos_3444_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v___x_3449_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
else
{
lean_object* v_pos_3454_; lean_object* v_err_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
v_pos_3454_ = lean_ctor_get(v___x_3443_, 0);
v_err_3455_ = lean_ctor_get(v___x_3443_, 1);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3443_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_err_3455_);
lean_inc(v_pos_3454_);
lean_dec(v___x_3443_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_pos_3454_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_err_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
}
}
case 3:
{
lean_object* v_presentation_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
lean_dec_ref(v_config_3329_);
v_presentation_3463_ = lean_ctor_get(v_x_3331_, 0);
lean_inc(v_presentation_3463_);
v___x_3464_ = lean_unsigned_to_nat(1u);
v___x_3465_ = lean_unsigned_to_nat(366u);
v___x_3466_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseField___boxed), 4, 3);
lean_closure_set(v___x_3466_, 0, v_x_3331_);
lean_closure_set(v___x_3466_, 1, v_presentation_3463_);
lean_closure_set(v___x_3466_, 2, v_reserve_3330_);
v___x_3467_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3464_, v___x_3465_, v___x_3466_, v_a_3332_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_pos_3468_; lean_object* v_res_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3479_; 
v_pos_3468_ = lean_ctor_get(v___x_3467_, 0);
v_res_3469_ = lean_ctor_get(v___x_3467_, 1);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3471_ = v___x_3467_;
v_isShared_3472_ = v_isSharedCheck_3479_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_res_3469_);
lean_inc(v_pos_3468_);
lean_dec(v___x_3467_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3479_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
uint8_t v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3477_; 
v___x_3473_ = 1;
v___x_3474_ = lean_box(v___x_3473_);
v___x_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
lean_ctor_set(v___x_3475_, 1, v_res_3469_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 1, v___x_3475_);
v___x_3477_ = v___x_3471_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_pos_3468_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v___x_3475_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
else
{
lean_object* v_pos_3480_; lean_object* v_err_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
v_pos_3480_ = lean_ctor_get(v___x_3467_, 0);
v_err_3481_ = lean_ctor_get(v___x_3467_, 1);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3467_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_err_3481_);
lean_inc(v_pos_3480_);
lean_dec(v___x_3467_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_pos_3480_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_err_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
case 4:
{
lean_object* v_presentation_3489_; 
v_presentation_3489_ = lean_ctor_get(v_x_3331_, 0);
if (lean_obj_tag(v_presentation_3489_) == 0)
{
lean_object* v_val_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
lean_dec_ref(v_config_3329_);
v_val_3490_ = lean_ctor_get(v_presentation_3489_, 0);
lean_inc(v_val_3490_);
v___x_3491_ = lean_unsigned_to_nat(1u);
v___x_3492_ = lean_unsigned_to_nat(12u);
v___x_3493_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseField___boxed), 4, 3);
lean_closure_set(v___x_3493_, 0, v_x_3331_);
lean_closure_set(v___x_3493_, 1, v_val_3490_);
lean_closure_set(v___x_3493_, 2, v_reserve_3330_);
v___x_3494_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3491_, v___x_3492_, v___x_3493_, v_a_3332_);
return v___x_3494_;
}
else
{
lean_object* v_dateformat_3495_; lean_object* v_val_3496_; lean_object* v_symbols_3497_; lean_object* v___x_3498_; uint8_t v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
lean_inc_ref(v_presentation_3489_);
lean_dec_ref_known(v_x_3331_, 1);
lean_dec(v_reserve_3330_);
v_dateformat_3495_ = lean_ctor_get(v_config_3329_, 0);
lean_inc_ref(v_dateformat_3495_);
lean_dec_ref(v_config_3329_);
v_val_3496_ = lean_ctor_get(v_presentation_3489_, 0);
lean_inc(v_val_3496_);
lean_dec_ref_known(v_presentation_3489_, 1);
v_symbols_3497_ = lean_ctor_get(v_dateformat_3495_, 1);
lean_inc_ref(v_symbols_3497_);
lean_dec_ref(v_dateformat_3495_);
v___x_3498_ = lean_unsigned_to_nat(12u);
v___x_3499_ = lean_unbox(v_val_3496_);
lean_dec(v_val_3496_);
v___x_3500_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthNames(v_symbols_3497_, v___x_3499_);
lean_dec_ref(v_symbols_3497_);
v___x_3501_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseName(v___x_3498_, v___x_3500_, v_a_3332_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_pos_3502_; lean_object* v_res_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3511_; 
v_pos_3502_ = lean_ctor_get(v___x_3501_, 0);
v_res_3503_ = lean_ctor_get(v___x_3501_, 1);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3505_ = v___x_3501_;
v_isShared_3506_ = v_isSharedCheck_3511_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_res_3503_);
lean_inc(v_pos_3502_);
lean_dec(v___x_3501_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3511_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3507_; lean_object* v___x_3509_; 
v___x_3507_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthOfIndex(v_res_3503_);
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 1, v___x_3507_);
v___x_3509_ = v___x_3505_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_pos_3502_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v___x_3507_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
else
{
lean_object* v_pos_3512_; lean_object* v_err_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
v_pos_3512_ = lean_ctor_get(v___x_3501_, 0);
v_err_3513_ = lean_ctor_get(v___x_3501_, 1);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3515_ = v___x_3501_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_err_3513_);
lean_inc(v_pos_3512_);
lean_dec(v___x_3501_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3518_; 
if (v_isShared_3516_ == 0)
{
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_pos_3512_);
lean_ctor_set(v_reuseFailAlloc_3519_, 1, v_err_3513_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
}
}
case 5:
{
lean_object* v_presentation_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3559_; 
v_presentation_3521_ = lean_ctor_get(v_x_3331_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v_x_3331_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3523_ = v_x_3331_;
v_isShared_3524_ = v_isSharedCheck_3559_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_presentation_3521_);
lean_dec(v_x_3331_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3559_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
if (lean_obj_tag(v_presentation_3521_) == 0)
{
lean_object* v_val_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3529_; 
lean_dec_ref(v_config_3329_);
v_val_3525_ = lean_ctor_get(v_presentation_3521_, 0);
lean_inc(v_val_3525_);
v___x_3526_ = lean_unsigned_to_nat(1u);
v___x_3527_ = lean_unsigned_to_nat(12u);
if (v_isShared_3524_ == 0)
{
lean_ctor_set_tag(v___x_3523_, 4);
v___x_3529_ = v___x_3523_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_presentation_3521_);
v___x_3529_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3530_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseField___boxed), 4, 3);
lean_closure_set(v___x_3530_, 0, v___x_3529_);
lean_closure_set(v___x_3530_, 1, v_val_3525_);
lean_closure_set(v___x_3530_, 2, v_reserve_3330_);
v___x_3531_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3526_, v___x_3527_, v___x_3530_, v_a_3332_);
return v___x_3531_;
}
}
else
{
lean_object* v_dateformat_3533_; lean_object* v_val_3534_; lean_object* v_symbols_3535_; lean_object* v___x_3536_; uint8_t v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
lean_del_object(v___x_3523_);
lean_dec(v_reserve_3330_);
v_dateformat_3533_ = lean_ctor_get(v_config_3329_, 0);
lean_inc_ref(v_dateformat_3533_);
lean_dec_ref(v_config_3329_);
v_val_3534_ = lean_ctor_get(v_presentation_3521_, 0);
lean_inc(v_val_3534_);
lean_dec_ref_known(v_presentation_3521_, 1);
v_symbols_3535_ = lean_ctor_get(v_dateformat_3533_, 1);
lean_inc_ref(v_symbols_3535_);
lean_dec_ref(v_dateformat_3533_);
v___x_3536_ = lean_unsigned_to_nat(12u);
v___x_3537_ = lean_unbox(v_val_3534_);
lean_dec(v_val_3534_);
v___x_3538_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthNames(v_symbols_3535_, v___x_3537_);
lean_dec_ref(v_symbols_3535_);
v___x_3539_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseName(v___x_3536_, v___x_3538_, v_a_3332_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_pos_3540_; lean_object* v_res_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3549_; 
v_pos_3540_ = lean_ctor_get(v___x_3539_, 0);
v_res_3541_ = lean_ctor_get(v___x_3539_, 1);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3543_ = v___x_3539_;
v_isShared_3544_ = v_isSharedCheck_3549_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_res_3541_);
lean_inc(v_pos_3540_);
lean_dec(v___x_3539_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3549_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3545_; lean_object* v___x_3547_; 
v___x_3545_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthOfIndex(v_res_3541_);
if (v_isShared_3544_ == 0)
{
lean_ctor_set(v___x_3543_, 1, v___x_3545_);
v___x_3547_ = v___x_3543_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_pos_3540_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v___x_3545_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
else
{
lean_object* v_pos_3550_; lean_object* v_err_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
v_pos_3550_ = lean_ctor_get(v___x_3539_, 0);
v_err_3551_ = lean_ctor_get(v___x_3539_, 1);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3539_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_err_3551_);
lean_inc(v_pos_3550_);
lean_dec(v___x_3539_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_pos_3550_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v_err_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
}
}
case 6:
{
lean_object* v_presentation_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
lean_dec_ref(v_config_3329_);
v_presentation_3560_ = lean_ctor_get(v_x_3331_, 0);
lean_inc(v_presentation_3560_);
v___x_3561_ = lean_unsigned_to_nat(1u);
v___x_3562_ = lean_unsigned_to_nat(31u);
v___x_3563_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseField___boxed), 4, 3);
lean_closure_set(v___x_3563_, 0, v_x_3331_);
lean_closure_set(v___x_3563_, 1, v_presentation_3560_);
lean_closure_set(v___x_3563_, 2, v_reserve_3330_);
v___x_3564_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3561_, v___x_3562_, v___x_3563_, v_a_3332_);
return v___x_3564_;
}
case 7:
{
lean_object* v_presentation_3565_; 
v_presentation_3565_ = lean_ctor_get(v_x_3331_, 0);
if (lean_obj_tag(v_presentation_3565_) == 0)
{
lean_object* v_val_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
lean_dec_ref(v_config_3329_);
v_val_3566_ = lean_ctor_get(v_presentation_3565_, 0);
lean_inc(v_val_3566_);
v___x_3567_ = lean_unsigned_to_nat(1u);
v___x_3568_ = lean_unsigned_to_nat(4u);
v___x_3569_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseField___boxed), 4, 3);
lean_closure_set(v___x_3569_, 0, v_x_3331_);
lean_closure_set(v___x_3569_, 1, v_val_3566_);
lean_closure_set(v___x_3569_, 2, v_reserve_3330_);
v___x_3570_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3567_, v___x_3568_, v___x_3569_, v_a_3332_);
return v___x_3570_;
}
else
{
lean_object* v_dateformat_3571_; lean_object* v_val_3572_; lean_object* v_symbols_3573_; lean_object* v___x_3574_; uint8_t v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
lean_inc_ref(v_presentation_3565_);
lean_dec_ref_known(v_x_3331_, 1);
lean_dec(v_reserve_3330_);
v_dateformat_3571_ = lean_ctor_get(v_config_3329_, 0);
lean_inc_ref(v_dateformat_3571_);
lean_dec_ref(v_config_3329_);
v_val_3572_ = lean_ctor_get(v_presentation_3565_, 0);
lean_inc(v_val_3572_);
lean_dec_ref_known(v_presentation_3565_, 1);
v_symbols_3573_ = lean_ctor_get(v_dateformat_3571_, 1);
lean_inc_ref(v_symbols_3573_);
lean_dec_ref(v_dateformat_3571_);
v___x_3574_ = lean_unsigned_to_nat(4u);
v___x_3575_ = lean_unbox(v_val_3572_);
lean_dec(v_val_3572_);
v___x_3576_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterNames(v_symbols_3573_, v___x_3575_);
lean_dec_ref(v_symbols_3573_);
v___x_3577_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseName(v___x_3574_, v___x_3576_, v_a_3332_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_pos_3578_; lean_object* v_res_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3587_; 
v_pos_3578_ = lean_ctor_get(v___x_3577_, 0);
v_res_3579_ = lean_ctor_get(v___x_3577_, 1);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3581_ = v___x_3577_;
v_isShared_3582_ = v_isSharedCheck_3587_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_res_3579_);
lean_inc(v_pos_3578_);
lean_dec(v___x_3577_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3587_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3583_; lean_object* v___x_3585_; 
v___x_3583_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterOfIndex(v_res_3579_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v___x_3583_);
v___x_3585_ = v___x_3581_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_pos_3578_);
lean_ctor_set(v_reuseFailAlloc_3586_, 1, v___x_3583_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
else
{
lean_object* v_pos_3588_; lean_object* v_err_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3596_; 
v_pos_3588_ = lean_ctor_get(v___x_3577_, 0);
v_err_3589_ = lean_ctor_get(v___x_3577_, 1);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3591_ = v___x_3577_;
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_err_3589_);
lean_inc(v_pos_3588_);
lean_dec(v___x_3577_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_pos_3588_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v_err_3589_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
}
case 8:
{
lean_object* v_presentation_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3635_; 
v_presentation_3597_ = lean_ctor_get(v_x_3331_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v_x_3331_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3599_ = v_x_3331_;
v_isShared_3600_ = v_isSharedCheck_3635_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_presentation_3597_);
lean_dec(v_x_3331_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3635_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
if (lean_obj_tag(v_presentation_3597_) == 0)
{
lean_object* v_val_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
lean_dec_ref(v_config_3329_);
v_val_3601_ = lean_ctor_get(v_presentation_3597_, 0);
lean_inc(v_val_3601_);
v___x_3602_ = lean_unsigned_to_nat(1u);
v___x_3603_ = lean_unsigned_to_nat(4u);
if (v_isShared_3600_ == 0)
{
lean_ctor_set_tag(v___x_3599_, 7);
v___x_3605_ = v___x_3599_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_presentation_3597_);
v___x_3605_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3606_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseField___boxed), 4, 3);
lean_closure_set(v___x_3606_, 0, v___x_3605_);
lean_closure_set(v___x_3606_, 1, v_val_3601_);
lean_closure_set(v___x_3606_, 2, v_reserve_3330_);
v___x_3607_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3602_, v___x_3603_, v___x_3606_, v_a_3332_);
return v___x_3607_;
}
}
else
{
lean_object* v_dateformat_3609_; lean_object* v_val_3610_; lean_object* v_symbols_3611_; lean_object* v___x_3612_; uint8_t v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
lean_del_object(v___x_3599_);
lean_dec(v_reserve_3330_);
v_dateformat_3609_ = lean_ctor_get(v_config_3329_, 0);
lean_inc_ref(v_dateformat_3609_);
lean_dec_ref(v_config_3329_);
v_val_3610_ = lean_ctor_get(v_presentation_3597_, 0);
lean_inc(v_val_3610_);
lean_dec_ref_known(v_presentation_3597_, 1);
v_symbols_3611_ = lean_ctor_get(v_dateformat_3609_, 1);
lean_inc_ref(v_symbols_3611_);
lean_dec_ref(v_dateformat_3609_);
v___x_3612_ = lean_unsigned_to_nat(4u);
v___x_3613_ = lean_unbox(v_val_3610_);
lean_dec(v_val_3610_);
v___x_3614_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterNames(v_symbols_3611_, v___x_3613_);
lean_dec_ref(v_symbols_3611_);
v___x_3615_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseName(v___x_3612_, v___x_3614_, v_a_3332_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_pos_3616_; lean_object* v_res_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3625_; 
v_pos_3616_ = lean_ctor_get(v___x_3615_, 0);
v_res_3617_ = lean_ctor_get(v___x_3615_, 1);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3619_ = v___x_3615_;
v_isShared_3620_ = v_isSharedCheck_3625_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_res_3617_);
lean_inc(v_pos_3616_);
lean_dec(v___x_3615_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3625_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3621_; lean_object* v___x_3623_; 
v___x_3621_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterOfIndex(v_res_3617_);
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 1, v___x_3621_);
v___x_3623_ = v___x_3619_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_pos_3616_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v___x_3621_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
else
{
lean_object* v_pos_3626_; lean_object* v_err_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
v_pos_3626_ = lean_ctor_get(v___x_3615_, 0);
v_err_3627_ = lean_ctor_get(v___x_3615_, 1);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3615_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_err_3627_);
lean_inc(v_pos_3626_);
lean_dec(v___x_3615_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_pos_3626_);
lean_ctor_set(v_reuseFailAlloc_3633_, 1, v_err_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
}
}
case 9:
{
lean_object* v_presentation_3636_; 
lean_dec_ref(v_config_3329_);
v_presentation_3636_ = lean_ctor_get(v_x_3331_, 0);
lean_inc(v_presentation_3636_);
lean_dec_ref_known(v_x_3331_, 1);
switch(lean_obj_tag(v_presentation_3636_))
{
case 0:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3637_ = lean_unsigned_to_nat(1u);
v___x_3638_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseVarWidthNum___boxed), 3, 2);
lean_closure_set(v___x_3638_, 0, v___x_3637_);
lean_closure_set(v___x_3638_, 1, v_reserve_3330_);
v___x_3639_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3638_, v_a_3332_);
return v___x_3639_;
}
case 1:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
lean_dec(v_reserve_3330_);
v___x_3640_ = lean_unsigned_to_nat(2u);
v___x_3641_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3640_, v_a_3332_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_pos_3642_; lean_object* v_res_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3653_; 
v_pos_3642_ = lean_ctor_get(v___x_3641_, 0);
v_res_3643_ = lean_ctor_get(v___x_3641_, 1);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3645_ = v___x_3641_;
v_isShared_3646_ = v_isSharedCheck_3653_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_res_3643_);
lean_inc(v_pos_3642_);
lean_dec(v___x_3641_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3653_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3651_; 
v___x_3647_ = lean_nat_to_int(v_res_3643_);
v___x_3648_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0);
v___x_3649_ = lean_int_add(v___x_3648_, v___x_3647_);
lean_dec(v___x_3647_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 1, v___x_3649_);
v___x_3651_ = v___x_3645_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_pos_3642_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
else
{
lean_object* v_pos_3654_; lean_object* v_err_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
v_pos_3654_ = lean_ctor_get(v___x_3641_, 0);
v_err_3655_ = lean_ctor_get(v___x_3641_, 1);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3641_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_err_3655_);
lean_inc(v_pos_3654_);
lean_dec(v___x_3641_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_pos_3654_);
lean_ctor_set(v_reuseFailAlloc_3661_, 1, v_err_3655_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
case 2:
{
uint8_t v___x_3663_; lean_object* v___x_3664_; 
v___x_3663_ = 1;
v___x_3664_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFourDigitYear(v___x_3663_, v_reserve_3330_, v_a_3332_);
lean_dec(v_reserve_3330_);
return v___x_3664_;
}
default: 
{
lean_object* v_num_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v_num_3665_ = lean_ctor_get(v_presentation_3636_, 0);
lean_inc(v_num_3665_);
lean_dec_ref_known(v_presentation_3636_, 1);
v___x_3666_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseVarWidthNum___boxed), 3, 2);
lean_closure_set(v___x_3666_, 0, v_num_3665_);
lean_closure_set(v___x_3666_, 1, v_reserve_3330_);
v___x_3667_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3666_, v_a_3332_);
return v___x_3667_;
}
}
}
case 10:
{
lean_object* v_presentation_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
lean_dec_ref(v_config_3329_);
v_presentation_3668_ = lean_ctor_get(v_x_3331_, 0);
lean_inc(v_presentation_3668_);
v___x_3669_ = lean_unsigned_to_nat(1u);
v___x_3670_ = lean_unsigned_to_nat(53u);
v___x_3671_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseField___boxed), 4, 3);
lean_closure_set(v___x_3671_, 0, v_x_3331_);
lean_closure_set(v___x_3671_, 1, v_presentation_3668_);
lean_closure_set(v___x_3671_, 2, v_reserve_3330_);
v___x_3672_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3669_, v___x_3670_, v___x_3671_, v_a_3332_);
return v___x_3672_;
}
case 11:
{
lean_object* v_presentation_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
lean_dec_ref(v_config_3329_);
v_presentation_3673_ = lean_ctor_get(v_x_3331_, 0);
lean_inc(v_presentation_3673_);
v___x_3674_ = lean_unsigned_to_nat(1u);
v___x_3675_ = lean_unsigned_to_nat(6u);
v___x_3676_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseField___boxed), 4, 3);
lean_closure_set(v___x_3676_, 0, v_x_3331_);
lean_closure_set(v___x_3676_, 1, v_presentation_3673_);
lean_closure_set(v___x_3676_, 2, v_reserve_3330_);
v___x_3677_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3674_, v___x_3675_, v___x_3676_, v_a_3332_);
return v___x_3677_;
}
case 12:
{
lean_object* v_dateformat_3678_; uint8_t v_presentation_3679_; lean_object* v_symbols_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
lean_dec(v_reserve_3330_);
v_dateformat_3678_ = lean_ctor_get(v_config_3329_, 0);
lean_inc_ref(v_dateformat_3678_);
lean_dec_ref(v_config_3329_);
v_presentation_3679_ = lean_ctor_get_uint8(v_x_3331_, 0);
lean_dec_ref_known(v_x_3331_, 0);
v_symbols_3680_ = lean_ctor_get(v_dateformat_3678_, 1);
lean_inc_ref(v_symbols_3680_);
lean_dec_ref(v_dateformat_3678_);
v___x_3681_ = lean_unsigned_to_nat(7u);
v___x_3682_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayNames(v_symbols_3680_, v_presentation_3679_);
lean_dec_ref(v_symbols_3680_);
v___x_3683_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseName(v___x_3681_, v___x_3682_, v_a_3332_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_pos_3684_; lean_object* v_res_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3694_; 
v_pos_3684_ = lean_ctor_get(v___x_3683_, 0);
v_res_3685_ = lean_ctor_get(v___x_3683_, 1);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3687_ = v___x_3683_;
v_isShared_3688_ = v_isSharedCheck_3694_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_res_3685_);
lean_inc(v_pos_3684_);
lean_dec(v___x_3683_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3694_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
uint8_t v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3692_; 
v___x_3689_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(v_res_3685_);
v___x_3690_ = lean_box(v___x_3689_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 1, v___x_3690_);
v___x_3692_ = v___x_3687_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_pos_3684_);
lean_ctor_set(v_reuseFailAlloc_3693_, 1, v___x_3690_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
else
{
lean_object* v_pos_3695_; lean_object* v_err_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
v_pos_3695_ = lean_ctor_get(v___x_3683_, 0);
v_err_3696_ = lean_ctor_get(v___x_3683_, 1);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3683_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_err_3696_);
lean_inc(v_pos_3695_);
lean_dec(v___x_3683_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_pos_3695_);
lean_ctor_set(v_reuseFailAlloc_3702_, 1, v_err_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
case 13:
{
lean_object* v_presentation_3704_; 
v_presentation_3704_ = lean_ctor_get(v_x_3331_, 0);
if (lean_obj_tag(v_presentation_3704_) == 0)
{
lean_object* v_val_3705_; lean_object* v___x_3706_; 
v_val_3705_ = lean_ctor_get(v_presentation_3704_, 0);
lean_inc(v_val_3705_);
v___x_3706_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseField(v_x_3331_, v_val_3705_, v_reserve_3330_, v_a_3332_);
lean_dec(v_reserve_3330_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_pos_3707_; lean_object* v_res_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3741_; 
v_pos_3707_ = lean_ctor_get(v___x_3706_, 0);
v_res_3708_ = lean_ctor_get(v___x_3706_, 1);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3710_ = v___x_3706_;
v_isShared_3711_ = v_isSharedCheck_3741_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_res_3708_);
lean_inc(v_pos_3707_);
lean_dec(v___x_3706_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3741_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3717_; uint8_t v___x_3718_; 
v___x_3717_ = lean_unsigned_to_nat(1u);
v___x_3718_ = lean_nat_dec_le(v___x_3717_, v_res_3708_);
if (v___x_3718_ == 0)
{
lean_dec(v_res_3708_);
lean_dec_ref(v_config_3329_);
goto v___jp_3712_;
}
else
{
lean_object* v___x_3719_; uint8_t v___x_3720_; 
v___x_3719_ = lean_unsigned_to_nat(7u);
v___x_3720_ = lean_nat_dec_le(v_res_3708_, v___x_3719_);
if (v___x_3720_ == 0)
{
lean_dec(v_res_3708_);
lean_dec_ref(v_config_3329_);
goto v___jp_3712_;
}
else
{
lean_object* v_dateformat_3721_; uint8_t v_firstDayOfWeek_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v_range_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; uint8_t v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
lean_del_object(v___x_3710_);
v_dateformat_3721_ = lean_ctor_get(v_config_3329_, 0);
lean_inc_ref(v_dateformat_3721_);
lean_dec_ref(v_config_3329_);
v_firstDayOfWeek_3722_ = lean_ctor_get_uint8(v_dateformat_3721_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_3721_);
v___x_3723_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_3722_);
v___x_3724_ = lean_nat_to_int(v_res_3708_);
v___x_3725_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3726_ = lean_int_sub(v___x_3724_, v___x_3725_);
lean_dec(v___x_3724_);
v___x_3727_ = lean_int_add(v___x_3726_, v___x_3723_);
lean_dec(v___x_3723_);
lean_dec(v___x_3726_);
v___x_3728_ = lean_int_sub(v___x_3727_, v___x_3725_);
lean_dec(v___x_3727_);
v___x_3729_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_3730_ = lean_int_emod(v___x_3728_, v___x_3729_);
lean_dec(v___x_3728_);
v___x_3731_ = lean_int_add(v___x_3730_, v___x_3725_);
lean_dec(v___x_3730_);
v_range_3732_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4);
v___x_3733_ = lean_int_sub(v___x_3731_, v___x_3725_);
lean_dec(v___x_3731_);
v___x_3734_ = lean_int_emod(v___x_3733_, v_range_3732_);
lean_dec(v___x_3733_);
v___x_3735_ = lean_int_add(v___x_3734_, v_range_3732_);
lean_dec(v___x_3734_);
v___x_3736_ = lean_int_emod(v___x_3735_, v_range_3732_);
lean_dec(v___x_3735_);
v___x_3737_ = lean_int_add(v___x_3736_, v___x_3725_);
lean_dec(v___x_3736_);
v___x_3738_ = l_Std_Time_Weekday_ofOrdinal(v___x_3737_);
lean_dec(v___x_3737_);
v___x_3739_ = lean_box(v___x_3738_);
v___x_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3740_, 0, v_pos_3707_);
lean_ctor_set(v___x_3740_, 1, v___x_3739_);
return v___x_3740_;
}
}
v___jp_3712_:
{
lean_object* v___x_3713_; lean_object* v___x_3715_; 
v___x_3713_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2));
if (v_isShared_3711_ == 0)
{
lean_ctor_set_tag(v___x_3710_, 1);
lean_ctor_set(v___x_3710_, 1, v___x_3713_);
v___x_3715_ = v___x_3710_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_pos_3707_);
lean_ctor_set(v_reuseFailAlloc_3716_, 1, v___x_3713_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
}
else
{
lean_object* v_pos_3742_; lean_object* v_err_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_dec_ref(v_config_3329_);
v_pos_3742_ = lean_ctor_get(v___x_3706_, 0);
v_err_3743_ = lean_ctor_get(v___x_3706_, 1);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3706_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_err_3743_);
lean_inc(v_pos_3742_);
lean_dec(v___x_3706_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_pos_3742_);
lean_ctor_set(v_reuseFailAlloc_3749_, 1, v_err_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
else
{
lean_object* v_dateformat_3751_; lean_object* v_val_3752_; lean_object* v_symbols_3753_; lean_object* v___x_3754_; uint8_t v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
lean_inc_ref(v_presentation_3704_);
lean_dec_ref_known(v_x_3331_, 1);
lean_dec(v_reserve_3330_);
v_dateformat_3751_ = lean_ctor_get(v_config_3329_, 0);
lean_inc_ref(v_dateformat_3751_);
lean_dec_ref(v_config_3329_);
v_val_3752_ = lean_ctor_get(v_presentation_3704_, 0);
lean_inc(v_val_3752_);
lean_dec_ref_known(v_presentation_3704_, 1);
v_symbols_3753_ = lean_ctor_get(v_dateformat_3751_, 1);
lean_inc_ref(v_symbols_3753_);
lean_dec_ref(v_dateformat_3751_);
v___x_3754_ = lean_unsigned_to_nat(7u);
v___x_3755_ = lean_unbox(v_val_3752_);
lean_dec(v_val_3752_);
v___x_3756_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayNames(v_symbols_3753_, v___x_3755_);
lean_dec_ref(v_symbols_3753_);
v___x_3757_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseName(v___x_3754_, v___x_3756_, v_a_3332_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_object* v_pos_3758_; lean_object* v_res_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3768_; 
v_pos_3758_ = lean_ctor_get(v___x_3757_, 0);
v_res_3759_ = lean_ctor_get(v___x_3757_, 1);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3761_ = v___x_3757_;
v_isShared_3762_ = v_isSharedCheck_3768_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_res_3759_);
lean_inc(v_pos_3758_);
lean_dec(v___x_3757_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3768_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
uint8_t v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3766_; 
v___x_3763_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(v_res_3759_);
v___x_3764_ = lean_box(v___x_3763_);
if (v_isShared_3762_ == 0)
{
lean_ctor_set(v___x_3761_, 1, v___x_3764_);
v___x_3766_ = v___x_3761_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_pos_3758_);
lean_ctor_set(v_reuseFailAlloc_3767_, 1, v___x_3764_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
else
{
lean_object* v_pos_3769_; lean_object* v_err_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
v_pos_3769_ = lean_ctor_get(v___x_3757_, 0);
v_err_3770_ = lean_ctor_get(v___x_3757_, 1);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3757_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_err_3770_);
lean_inc(v_pos_3769_);
lean_dec(v___x_3757_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_pos_3769_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v_err_3770_);
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
case 14:
{
lean_object* v_presentation_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3858_; 
v_presentation_3778_ = lean_ctor_get(v_x_3331_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v_x_3331_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3780_ = v_x_3331_;
v_isShared_3781_ = v_isSharedCheck_3858_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_presentation_3778_);
lean_dec(v_x_3331_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3858_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
if (lean_obj_tag(v_presentation_3778_) == 0)
{
lean_object* v_val_3782_; lean_object* v___x_3784_; 
v_val_3782_ = lean_ctor_get(v_presentation_3778_, 0);
lean_inc(v_val_3782_);
if (v_isShared_3781_ == 0)
{
lean_ctor_set_tag(v___x_3780_, 13);
v___x_3784_ = v___x_3780_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_presentation_3778_);
v___x_3784_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
lean_object* v___x_3785_; 
v___x_3785_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseField(v___x_3784_, v_val_3782_, v_reserve_3330_, v_a_3332_);
lean_dec(v_reserve_3330_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_pos_3786_; lean_object* v_res_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3820_; 
v_pos_3786_ = lean_ctor_get(v___x_3785_, 0);
v_res_3787_ = lean_ctor_get(v___x_3785_, 1);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3789_ = v___x_3785_;
v_isShared_3790_ = v_isSharedCheck_3820_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_res_3787_);
lean_inc(v_pos_3786_);
lean_dec(v___x_3785_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3820_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3796_; uint8_t v___x_3797_; 
v___x_3796_ = lean_unsigned_to_nat(1u);
v___x_3797_ = lean_nat_dec_le(v___x_3796_, v_res_3787_);
if (v___x_3797_ == 0)
{
lean_dec(v_res_3787_);
lean_dec_ref(v_config_3329_);
goto v___jp_3791_;
}
else
{
lean_object* v___x_3798_; uint8_t v___x_3799_; 
v___x_3798_ = lean_unsigned_to_nat(7u);
v___x_3799_ = lean_nat_dec_le(v_res_3787_, v___x_3798_);
if (v___x_3799_ == 0)
{
lean_dec(v_res_3787_);
lean_dec_ref(v_config_3329_);
goto v___jp_3791_;
}
else
{
lean_object* v_dateformat_3800_; uint8_t v_firstDayOfWeek_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v_range_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
lean_del_object(v___x_3789_);
v_dateformat_3800_ = lean_ctor_get(v_config_3329_, 0);
lean_inc_ref(v_dateformat_3800_);
lean_dec_ref(v_config_3329_);
v_firstDayOfWeek_3801_ = lean_ctor_get_uint8(v_dateformat_3800_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_3800_);
v___x_3802_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_3801_);
v___x_3803_ = lean_nat_to_int(v_res_3787_);
v___x_3804_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3805_ = lean_int_sub(v___x_3803_, v___x_3804_);
lean_dec(v___x_3803_);
v___x_3806_ = lean_int_add(v___x_3805_, v___x_3802_);
lean_dec(v___x_3802_);
lean_dec(v___x_3805_);
v___x_3807_ = lean_int_sub(v___x_3806_, v___x_3804_);
lean_dec(v___x_3806_);
v___x_3808_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_3809_ = lean_int_emod(v___x_3807_, v___x_3808_);
lean_dec(v___x_3807_);
v___x_3810_ = lean_int_add(v___x_3809_, v___x_3804_);
lean_dec(v___x_3809_);
v_range_3811_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4);
v___x_3812_ = lean_int_sub(v___x_3810_, v___x_3804_);
lean_dec(v___x_3810_);
v___x_3813_ = lean_int_emod(v___x_3812_, v_range_3811_);
lean_dec(v___x_3812_);
v___x_3814_ = lean_int_add(v___x_3813_, v_range_3811_);
lean_dec(v___x_3813_);
v___x_3815_ = lean_int_emod(v___x_3814_, v_range_3811_);
lean_dec(v___x_3814_);
v___x_3816_ = lean_int_add(v___x_3815_, v___x_3804_);
lean_dec(v___x_3815_);
v___x_3817_ = l_Std_Time_Weekday_ofOrdinal(v___x_3816_);
lean_dec(v___x_3816_);
v___x_3818_ = lean_box(v___x_3817_);
v___x_3819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3819_, 0, v_pos_3786_);
lean_ctor_set(v___x_3819_, 1, v___x_3818_);
return v___x_3819_;
}
}
v___jp_3791_:
{
lean_object* v___x_3792_; lean_object* v___x_3794_; 
v___x_3792_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2));
if (v_isShared_3790_ == 0)
{
lean_ctor_set_tag(v___x_3789_, 1);
lean_ctor_set(v___x_3789_, 1, v___x_3792_);
v___x_3794_ = v___x_3789_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_pos_3786_);
lean_ctor_set(v_reuseFailAlloc_3795_, 1, v___x_3792_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
else
{
lean_object* v_pos_3821_; lean_object* v_err_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
lean_dec_ref(v_config_3329_);
v_pos_3821_ = lean_ctor_get(v___x_3785_, 0);
v_err_3822_ = lean_ctor_get(v___x_3785_, 1);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3785_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_err_3822_);
lean_inc(v_pos_3821_);
lean_dec(v___x_3785_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_pos_3821_);
lean_ctor_set(v_reuseFailAlloc_3828_, 1, v_err_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
}
else
{
lean_object* v_dateformat_3831_; lean_object* v_val_3832_; lean_object* v_symbols_3833_; lean_object* v___x_3834_; uint8_t v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
lean_del_object(v___x_3780_);
lean_dec(v_reserve_3330_);
v_dateformat_3831_ = lean_ctor_get(v_config_3329_, 0);
lean_inc_ref(v_dateformat_3831_);
lean_dec_ref(v_config_3329_);
v_val_3832_ = lean_ctor_get(v_presentation_3778_, 0);
lean_inc(v_val_3832_);
lean_dec_ref_known(v_presentation_3778_, 1);
v_symbols_3833_ = lean_ctor_get(v_dateformat_3831_, 1);
lean_inc_ref(v_symbols_3833_);
lean_dec_ref(v_dateformat_3831_);
v___x_3834_ = lean_unsigned_to_nat(7u);
v___x_3835_ = lean_unbox(v_val_3832_);
lean_dec(v_val_3832_);
v___x_3836_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayNames(v_symbols_3833_, v___x_3835_);
lean_dec_ref(v_symbols_3833_);
v___x_3837_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseName(v___x_3834_, v___x_3836_, v_a_3332_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_pos_3838_; lean_object* v_res_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3848_; 
v_pos_3838_ = lean_ctor_get(v___x_3837_, 0);
v_res_3839_ = lean_ctor_get(v___x_3837_, 1);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3841_ = v___x_3837_;
v_isShared_3842_ = v_isSharedCheck_3848_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_res_3839_);
lean_inc(v_pos_3838_);
lean_dec(v___x_3837_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3848_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
uint8_t v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3846_; 
v___x_3843_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(v_res_3839_);
v___x_3844_ = lean_box(v___x_3843_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 1, v___x_3844_);
v___x_3846_ = v___x_3841_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_pos_3838_);
lean_ctor_set(v_reuseFailAlloc_3847_, 1, v___x_3844_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
else
{
lean_object* v_pos_3849_; lean_object* v_err_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
v_pos_3849_ = lean_ctor_get(v___x_3837_, 0);
v_err_3850_ = lean_ctor_get(v___x_3837_, 1);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3837_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_err_3850_);
lean_inc(v_pos_3849_);
lean_dec(v___x_3837_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_pos_3849_);
lean_ctor_set(v_reuseFailAlloc_3856_, 1, v_err_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
}
}
case 15:
{
lean_object* v_presentation_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
lean_dec_ref(v_config_3329_);
v_presentation_3859_ = lean_ctor_get(v_x_3331_, 0);
lean_inc(v_presentation_3859_);
v___x_3860_ = lean_unsigned_to_nat(1u);
v___x_3861_ = lean_unsigned_to_nat(5u);
v___x_3862_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseField___boxed), 4, 3);
lean_closure_set(v___x_3862_, 0, v_x_3331_);
lean_closure_set(v___x_3862_, 1, v_presentation_3859_);
lean_closure_set(v___x_3862_, 2, v_reserve_3330_);
v___x_3863_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3860_, v___x_3861_, v___x_3862_, v_a_3332_);
return v___x_3863_;
}
case 16:
{
lean_object* v_dateformat_3864_; uint8_t v_presentation_3865_; lean_object* v_symbols_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
lean_dec(v_reserve_3330_);
v_dateformat_3864_ = lean_ctor_get(v_config_3329_, 0);
lean_inc_ref(v_dateformat_3864_);
lean_dec_ref(v_config_3329_);
v_presentation_3865_ = lean_ctor_get_uint8(v_x_3331_, 0);
lean_dec_ref_known(v_x_3331_, 0);
v_symbols_3866_ = lean_ctor_get(v_dateformat_3864_, 1);
lean_inc_ref(v_symbols_3866_);
lean_dec_ref(v_dateformat_3864_);
v___x_3867_ = lean_unsigned_to_nat(2u);
v___x_3868_ = l___private_Std_Time_Format_Basic_0__Std_Time_markerNames(v_symbols_3866_, v_presentation_3865_);
v___x_3869_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseName(v___x_3867_, v___x_3868_, v_a_3332_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_pos_3870_; lean_object* v_res_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3880_; 
v_pos_3870_ = lean_ctor_get(v___x_3869_, 0);
v_res_3871_ = lean_ctor_get(v___x_3869_, 1);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3873_ = v___x_3869_;
v_isShared_3874_ = v_isSharedCheck_3880_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_res_3871_);
lean_inc(v_pos_3870_);
lean_dec(v___x_3869_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3880_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
uint8_t v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3878_; 
v___x_3875_ = l___private_Std_Time_Format_Basic_0__Std_Time_markerOfIndex(v_res_3871_);
lean_dec(v_res_3871_);
v___x_3876_ = lean_box(v___x_3875_);
if (v_isShared_3874_ == 0)
{
lean_ctor_set(v___x_3873_, 1, v___x_3876_);
v___x_3878_ = v___x_3873_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_pos_3870_);
lean_ctor_set(v_reuseFailAlloc_3879_, 1, v___x_3876_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
else
{
lean_object* v_pos_3881_; lean_object* v_err_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
v_pos_3881_ = lean_ctor_get(v___x_3869_, 0);
v_err_3882_ = lean_ctor_get(v___x_3869_, 1);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___x_3869_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_err_3882_);
lean_inc(v_pos_3881_);
lean_dec(v___x_3869_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_pos_3881_);
lean_ctor_set(v_reuseFailAlloc_3888_, 1, v_err_3882_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
}
case 17:
{
lean_object* v_dateformat_3890_; uint8_t v_presentation_3891_; lean_object* v_symbols_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
lean_dec(v_reserve_3330_);
v_dateformat_3890_ = lean_ctor_get(v_config_3329_, 0);
lean_inc_ref(v_dateformat_3890_);
lean_dec_ref(v_config_3329_);
v_presentation_3891_ = lean_ctor_get_uint8(v_x_3331_, 0);
lean_dec_ref_known(v_x_3331_, 0);
v_symbols_3892_ = lean_ctor_get(v_dateformat_3890_, 1);
lean_inc_ref(v_symbols_3892_);
lean_dec_ref(v_dateformat_3890_);
v___x_3893_ = lean_unsigned_to_nat(4u);
v___x_3894_ = l___private_Std_Time_Format_Basic_0__Std_Time_dayPeriodNames(v_symbols_3892_, v_presentation_3891_);
v___x_3895_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseName(v___x_3893_, v___x_3894_, v_a_3332_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_pos_3896_; lean_object* v_res_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3906_; 
v_pos_3896_ = lean_ctor_get(v___x_3895_, 0);
v_res_3897_ = lean_ctor_get(v___x_3895_, 1);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3899_ = v___x_3895_;
v_isShared_3900_ = v_isSharedCheck_3906_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_res_3897_);
lean_inc(v_pos_3896_);
lean_dec(v___x_3895_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3906_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
uint8_t v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3904_; 
v___x_3901_ = l___private_Std_Time_Format_Basic_0__Std_Time_dayPeriodOfIndex(v_res_3897_);
lean_dec(v_res_3897_);
v___x_3902_ = lean_box(v___x_3901_);
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 1, v___x_3902_);
v___x_3904_ = v___x_3899_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_pos_3896_);
lean_ctor_set(v_reuseFailAlloc_3905_, 1, v___x_3902_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
else
{
lean_object* v_pos_3907_; lean_object* v_err_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3915_; 
v_pos_3907_ = lean_ctor_get(v___x_3895_, 0);
v_err_3908_ = lean_ctor_get(v___x_3895_, 1);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3910_ = v___x_3895_;
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_err_3908_);
lean_inc(v_pos_3907_);
lean_dec(v___x_3895_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_pos_3907_);
lean_ctor_set(v_reuseFailAlloc_3914_, 1, v_err_3908_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
case 18:
{
lean_object* v_dateformat_3916_; uint8_t v_presentation_3917_; lean_object* v_symbols_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
lean_dec(v_reserve_3330_);
v_dateformat_3916_ = lean_ctor_get(v_config_3329_, 0);
lean_inc_ref(v_dateformat_3916_);
lean_dec_ref(v_config_3329_);
v_presentation_3917_ = lean_ctor_get_uint8(v_x_3331_, 0);
lean_dec_ref_known(v_x_3331_, 0);
v_symbols_3918_ = lean_ctor_get(v_dateformat_3916_, 1);
lean_inc_ref(v_symbols_3918_);
lean_dec_ref(v_dateformat_3916_);
v___x_3919_ = lean_unsigned_to_nat(6u);
v___x_3920_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodNames(v_symbols_3918_, v_presentation_3917_);
lean_dec_ref(v_symbols_3918_);
v___x_3921_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseName(v___x_3919_, v___x_3920_, v_a_3332_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_pos_3922_; lean_object* v_res_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3932_; 
v_pos_3922_ = lean_ctor_get(v___x_3921_, 0);
v_res_3923_ = lean_ctor_get(v___x_3921_, 1);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3925_ = v___x_3921_;
v_isShared_3926_ = v_isSharedCheck_3932_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_res_3923_);
lean_inc(v_pos_3922_);
lean_dec(v___x_3921_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3932_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
uint8_t v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3930_; 
v___x_3927_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodOfIndex(v_res_3923_);
lean_dec(v_res_3923_);
v___x_3928_ = lean_box(v___x_3927_);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 1, v___x_3928_);
v___x_3930_ = v___x_3925_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_pos_3922_);
lean_ctor_set(v_reuseFailAlloc_3931_, 1, v___x_3928_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
else
{
lean_object* v_pos_3933_; lean_object* v_err_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3941_; 
v_pos_3933_ = lean_ctor_get(v___x_3921_, 0);
v_err_3934_ = lean_ctor_get(v___x_3921_, 1);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3936_ = v___x_3921_;
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_err_3934_);
lean_inc(v_pos_3933_);
lean_dec(v___x_3921_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_pos_3933_);
lean_ctor_set(v_reuseFailAlloc_3940_, 1, v_err_3934_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
case 19:
{
lean_object* v_presentation_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
lean_dec_ref(v_config_3329_);
v_presentation_3942_ = lean_ctor_get(v_x_3331_, 0);
lean_inc(v_presentation_3942_);
v___x_3943_ = lean_unsigned_to_nat(1u);
v___x_3944_ = lean_unsigned_to_nat(12u);
v___x_3945_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseField___boxed), 4, 3);
lean_closure_set(v___x_3945_, 0, v_x_3331_);
lean_closure_set(v___x_3945_, 1, v_presentation_3942_);
lean_closure_set(v___x_3945_, 2, v_reserve_3330_);
v___x_3946_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3943_, v___x_3944_, v___x_3945_, v_a_3332_);
return v___x_3946_;
}
case 20:
{
lean_object* v_presentation_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
lean_dec_ref(v_config_3329_);
v_presentation_3947_ = lean_ctor_get(v_x_3331_, 0);
lean_inc(v_presentation_3947_);
v___x_3948_ = lean_unsigned_to_nat(0u);
v___x_3949_ = lean_unsigned_to_nat(11u);
v___x_3950_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseField___boxed), 4, 3);
lean_closure_set(v___x_3950_, 0, v_x_3331_);
lean_closure_set(v___x_3950_, 1, v_presentation_3947_);
lean_closure_set(v___x_3950_, 2, v_reserve_3330_);
v___x_3951_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3948_, v___x_3949_, v___x_3950_, v_a_3332_);
return v___x_3951_;
}
case 21:
{
lean_object* v_presentation_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
lean_dec_ref(v_config_3329_);
v_presentation_3952_ = lean_ctor_get(v_x_3331_, 0);
lean_inc(v_presentation_3952_);
v___x_3953_ = lean_unsigned_to_nat(1u);
v___x_3954_ = lean_unsigned_to_nat(24u);
v___x_3955_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseField___boxed), 4, 3);
lean_closure_set(v___x_3955_, 0, v_x_3331_);
lean_closure_set(v___x_3955_, 1, v_presentation_3952_);
lean_closure_set(v___x_3955_, 2, v_reserve_3330_);
v___x_3956_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3953_, v___x_3954_, v___x_3955_, v_a_3332_);
return v___x_3956_;
}
case 22:
{
lean_object* v_presentation_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
lean_dec_ref(v_config_3329_);
v_presentation_3957_ = lean_ctor_get(v_x_3331_, 0);
lean_inc(v_presentation_3957_);
v___x_3958_ = lean_unsigned_to_nat(0u);
v___x_3959_ = lean_unsigned_to_nat(23u);
v___x_3960_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseField___boxed), 4, 3);
lean_closure_set(v___x_3960_, 0, v_x_3331_);
lean_closure_set(v___x_3960_, 1, v_presentation_3957_);
lean_closure_set(v___x_3960_, 2, v_reserve_3330_);
v___x_3961_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3958_, v___x_3959_, v___x_3960_, v_a_3332_);
return v___x_3961_;
}
case 23:
{
lean_object* v_presentation_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
lean_dec_ref(v_config_3329_);
v_presentation_3962_ = lean_ctor_get(v_x_3331_, 0);
lean_inc(v_presentation_3962_);
v___x_3963_ = lean_unsigned_to_nat(0u);
v___x_3964_ = lean_unsigned_to_nat(59u);
v___x_3965_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseField___boxed), 4, 3);
lean_closure_set(v___x_3965_, 0, v_x_3331_);
lean_closure_set(v___x_3965_, 1, v_presentation_3962_);
lean_closure_set(v___x_3965_, 2, v_reserve_3330_);
v___x_3966_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3963_, v___x_3964_, v___x_3965_, v_a_3332_);
return v___x_3966_;
}
case 24:
{
uint8_t v_allowLeapSeconds_3967_; 
v_allowLeapSeconds_3967_ = lean_ctor_get_uint8(v_config_3329_, sizeof(void*)*1);
lean_dec_ref(v_config_3329_);
if (v_allowLeapSeconds_3967_ == 0)
{
lean_object* v_presentation_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v_presentation_3968_ = lean_ctor_get(v_x_3331_, 0);
lean_inc(v_presentation_3968_);
v___x_3969_ = lean_unsigned_to_nat(0u);
v___x_3970_ = lean_unsigned_to_nat(59u);
v___x_3971_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseField___boxed), 4, 3);
lean_closure_set(v___x_3971_, 0, v_x_3331_);
lean_closure_set(v___x_3971_, 1, v_presentation_3968_);
lean_closure_set(v___x_3971_, 2, v_reserve_3330_);
v___x_3972_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3969_, v___x_3970_, v___x_3971_, v_a_3332_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_pos_3973_; lean_object* v_res_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3981_; 
v_pos_3973_ = lean_ctor_get(v___x_3972_, 0);
v_res_3974_ = lean_ctor_get(v___x_3972_, 1);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3976_ = v___x_3972_;
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_res_3974_);
lean_inc(v_pos_3973_);
lean_dec(v___x_3972_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3979_; 
if (v_isShared_3977_ == 0)
{
v___x_3979_ = v___x_3976_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_pos_3973_);
lean_ctor_set(v_reuseFailAlloc_3980_, 1, v_res_3974_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
else
{
return v___x_3972_;
}
}
else
{
lean_object* v_presentation_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v_presentation_3982_ = lean_ctor_get(v_x_3331_, 0);
lean_inc(v_presentation_3982_);
v___x_3983_ = lean_unsigned_to_nat(0u);
v___x_3984_ = lean_unsigned_to_nat(60u);
v___x_3985_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseField___boxed), 4, 3);
lean_closure_set(v___x_3985_, 0, v_x_3331_);
lean_closure_set(v___x_3985_, 1, v_presentation_3982_);
lean_closure_set(v___x_3985_, 2, v_reserve_3330_);
v___x_3986_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3983_, v___x_3984_, v___x_3985_, v_a_3332_);
return v___x_3986_;
}
}
case 25:
{
lean_object* v_presentation_3987_; 
lean_dec(v_reserve_3330_);
lean_dec_ref(v_config_3329_);
v_presentation_3987_ = lean_ctor_get(v_x_3331_, 0);
lean_inc(v_presentation_3987_);
lean_dec_ref_known(v_x_3331_, 1);
if (lean_obj_tag(v_presentation_3987_) == 0)
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3988_ = lean_unsigned_to_nat(0u);
v___x_3989_ = lean_unsigned_to_nat(999999999u);
v___x_3990_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5));
v___x_3991_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3988_, v___x_3989_, v___x_3990_, v_a_3332_);
return v___x_3991_;
}
else
{
lean_object* v_digits_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v_digits_3992_ = lean_ctor_get(v_presentation_3987_, 0);
lean_inc(v_digits_3992_);
lean_dec_ref_known(v_presentation_3987_, 1);
v___x_3993_ = lean_unsigned_to_nat(0u);
v___x_3994_ = lean_unsigned_to_nat(999999999u);
v___x_3995_ = lean_unsigned_to_nat(9u);
v___x_3996_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed), 3, 2);
lean_closure_set(v___x_3996_, 0, v_digits_3992_);
lean_closure_set(v___x_3996_, 1, v___x_3995_);
v___x_3997_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3993_, v___x_3994_, v___x_3996_, v_a_3332_);
return v___x_3997_;
}
}
case 26:
{
lean_object* v_presentation_3998_; lean_object* v___x_3999_; 
lean_dec_ref(v_config_3329_);
v_presentation_3998_ = lean_ctor_get(v_x_3331_, 0);
lean_inc(v_presentation_3998_);
v___x_3999_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseField(v_x_3331_, v_presentation_3998_, v_reserve_3330_, v_a_3332_);
lean_dec(v_reserve_3330_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_pos_4000_; lean_object* v_res_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4009_; 
v_pos_4000_ = lean_ctor_get(v___x_3999_, 0);
v_res_4001_ = lean_ctor_get(v___x_3999_, 1);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4003_ = v___x_3999_;
v_isShared_4004_ = v_isSharedCheck_4009_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_res_4001_);
lean_inc(v_pos_4000_);
lean_dec(v___x_3999_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4009_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4005_; lean_object* v___x_4007_; 
v___x_4005_ = lean_nat_to_int(v_res_4001_);
if (v_isShared_4004_ == 0)
{
lean_ctor_set(v___x_4003_, 1, v___x_4005_);
v___x_4007_ = v___x_4003_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_pos_4000_);
lean_ctor_set(v_reuseFailAlloc_4008_, 1, v___x_4005_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
else
{
lean_object* v_pos_4010_; lean_object* v_err_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
v_pos_4010_ = lean_ctor_get(v___x_3999_, 0);
v_err_4011_ = lean_ctor_get(v___x_3999_, 1);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___x_3999_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_err_4011_);
lean_inc(v_pos_4010_);
lean_dec(v___x_3999_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_pos_4010_);
lean_ctor_set(v_reuseFailAlloc_4017_, 1, v_err_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
}
case 27:
{
lean_object* v_presentation_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; 
lean_dec_ref(v_config_3329_);
v_presentation_4019_ = lean_ctor_get(v_x_3331_, 0);
lean_inc(v_presentation_4019_);
v___x_4020_ = lean_unsigned_to_nat(0u);
v___x_4021_ = lean_unsigned_to_nat(999999999u);
v___x_4022_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseField___boxed), 4, 3);
lean_closure_set(v___x_4022_, 0, v_x_3331_);
lean_closure_set(v___x_4022_, 1, v_presentation_4019_);
lean_closure_set(v___x_4022_, 2, v_reserve_3330_);
v___x_4023_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4020_, v___x_4021_, v___x_4022_, v_a_3332_);
return v___x_4023_;
}
case 28:
{
lean_object* v_presentation_4024_; lean_object* v___x_4025_; 
lean_dec_ref(v_config_3329_);
v_presentation_4024_ = lean_ctor_get(v_x_3331_, 0);
lean_inc(v_presentation_4024_);
v___x_4025_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseField(v_x_3331_, v_presentation_4024_, v_reserve_3330_, v_a_3332_);
lean_dec(v_reserve_3330_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_object* v_pos_4026_; lean_object* v_res_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4035_; 
v_pos_4026_ = lean_ctor_get(v___x_4025_, 0);
v_res_4027_ = lean_ctor_get(v___x_4025_, 1);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4029_ = v___x_4025_;
v_isShared_4030_ = v_isSharedCheck_4035_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_res_4027_);
lean_inc(v_pos_4026_);
lean_dec(v___x_4025_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4035_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4031_; lean_object* v___x_4033_; 
v___x_4031_ = lean_nat_to_int(v_res_4027_);
if (v_isShared_4030_ == 0)
{
lean_ctor_set(v___x_4029_, 1, v___x_4031_);
v___x_4033_ = v___x_4029_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_pos_4026_);
lean_ctor_set(v_reuseFailAlloc_4034_, 1, v___x_4031_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
else
{
lean_object* v_pos_4036_; lean_object* v_err_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
v_pos_4036_ = lean_ctor_get(v___x_4025_, 0);
v_err_4037_ = lean_ctor_get(v___x_4025_, 1);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_4025_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_err_4037_);
lean_inc(v_pos_4036_);
lean_dec(v___x_4025_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_pos_4036_);
lean_ctor_set(v_reuseFailAlloc_4043_, 1, v_err_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
case 29:
{
uint8_t v_presentation_4045_; 
lean_dec(v_reserve_3330_);
lean_dec_ref(v_config_3329_);
v_presentation_4045_ = lean_ctor_get_uint8(v_x_3331_, 0);
lean_dec_ref_known(v_x_3331_, 0);
if (v_presentation_4045_ == 0)
{
lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4046_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
v___x_4047_ = l_Std_Internal_Parsec_String_pstring(v___x_4046_, v_a_3332_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_pos_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
v_pos_4048_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4055_ == 0)
{
lean_object* v_unused_4056_; 
v_unused_4056_ = lean_ctor_get(v___x_4047_, 1);
lean_dec(v_unused_4056_);
v___x_4050_ = v___x_4047_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_pos_4048_);
lean_dec(v___x_4047_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 1, v___x_4046_);
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_pos_4048_);
lean_ctor_set(v_reuseFailAlloc_4054_, 1, v___x_4046_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
else
{
return v___x_4047_;
}
}
else
{
lean_object* v___x_4057_; 
v___x_4057_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseZoneId(v_a_3332_);
return v___x_4057_;
}
}
case 32:
{
uint8_t v_presentation_4058_; 
lean_dec(v_reserve_3330_);
lean_dec_ref(v_config_3329_);
v_presentation_4058_ = lean_ctor_get_uint8(v_x_3331_, 0);
lean_dec_ref_known(v_x_3331_, 0);
if (v_presentation_4058_ == 0)
{
uint8_t v___x_4059_; lean_object* v___x_4060_; 
v___x_4059_ = 2;
v___x_4060_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseGmtOffset(v___x_4059_, v_a_3332_);
return v___x_4060_;
}
else
{
v___y_3334_ = v_a_3332_;
goto v___jp_3333_;
}
}
case 33:
{
uint8_t v_presentation_4061_; lean_object* v___x_4062_; 
lean_dec(v_reserve_3330_);
lean_dec_ref(v_config_3329_);
v_presentation_4061_ = lean_ctor_get_uint8(v_x_3331_, 0);
lean_dec_ref_known(v_x_3331_, 0);
lean_inc_ref(v_a_3332_);
v___x_4062_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffsetX(v_presentation_4061_, v_a_3332_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_dec_ref(v_a_3332_);
return v___x_4062_;
}
else
{
lean_object* v_pos_4063_; lean_object* v_snd_4064_; lean_object* v_snd_4065_; uint8_t v_decide_4066_; 
v_pos_4063_ = lean_ctor_get(v___x_4062_, 0);
v_snd_4064_ = lean_ctor_get(v_a_3332_, 1);
lean_inc(v_snd_4064_);
lean_dec_ref(v_a_3332_);
v_snd_4065_ = lean_ctor_get(v_pos_4063_, 1);
v_decide_4066_ = lean_nat_dec_eq(v_snd_4064_, v_snd_4065_);
lean_dec(v_snd_4064_);
if (v_decide_4066_ == 0)
{
return v___x_4062_;
}
else
{
lean_object* v___x_4067_; lean_object* v___x_4068_; 
lean_inc(v_pos_4063_);
lean_dec_ref_known(v___x_4062_, 2);
v___x_4067_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__5));
v___x_4068_ = l_Std_Internal_Parsec_String_pstring(v___x_4067_, v_pos_4063_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_object* v_pos_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4077_; 
v_pos_4069_ = lean_ctor_get(v___x_4068_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4077_ == 0)
{
lean_object* v_unused_4078_; 
v_unused_4078_ = lean_ctor_get(v___x_4068_, 1);
lean_dec(v_unused_4078_);
v___x_4071_ = v___x_4068_;
v_isShared_4072_ = v_isSharedCheck_4077_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_pos_4069_);
lean_dec(v___x_4068_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4077_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4073_; lean_object* v___x_4075_; 
v___x_4073_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_4072_ == 0)
{
lean_ctor_set(v___x_4071_, 1, v___x_4073_);
v___x_4075_ = v___x_4071_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_pos_4069_);
lean_ctor_set(v_reuseFailAlloc_4076_, 1, v___x_4073_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
else
{
lean_object* v_pos_4079_; lean_object* v_err_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4087_; 
v_pos_4079_ = lean_ctor_get(v___x_4068_, 0);
v_err_4080_ = lean_ctor_get(v___x_4068_, 1);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4082_ = v___x_4068_;
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_err_4080_);
lean_inc(v_pos_4079_);
lean_dec(v___x_4068_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4085_; 
if (v_isShared_4083_ == 0)
{
v___x_4085_ = v___x_4082_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_pos_4079_);
lean_ctor_set(v_reuseFailAlloc_4086_, 1, v_err_4080_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
}
}
}
}
}
}
case 34:
{
uint8_t v_presentation_4088_; lean_object* v___x_4089_; 
lean_dec(v_reserve_3330_);
lean_dec_ref(v_config_3329_);
v_presentation_4088_ = lean_ctor_get_uint8(v_x_3331_, 0);
lean_dec_ref_known(v_x_3331_, 0);
v___x_4089_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffsetX(v_presentation_4088_, v_a_3332_);
return v___x_4089_;
}
case 35:
{
uint8_t v_presentation_4090_; 
lean_dec(v_reserve_3330_);
lean_dec_ref(v_config_3329_);
v_presentation_4090_ = lean_ctor_get_uint8(v_x_3331_, 0);
lean_dec_ref_known(v_x_3331_, 0);
switch(v_presentation_4090_)
{
case 0:
{
uint8_t v___x_4091_; uint8_t v___x_4092_; uint8_t v___x_4093_; lean_object* v___x_4094_; 
v___x_4091_ = 0;
v___x_4092_ = 2;
v___x_4093_ = 0;
v___x_4094_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4091_, v___x_4092_, v___x_4093_, v_a_3332_);
return v___x_4094_;
}
case 1:
{
v___y_3334_ = v_a_3332_;
goto v___jp_3333_;
}
default: 
{
lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4095_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__5));
lean_inc_ref(v_a_3332_);
v___x_4096_ = l_Std_Internal_Parsec_String_pstring(v___x_4095_, v_a_3332_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v_pos_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4105_; 
lean_dec_ref(v_a_3332_);
v_pos_4097_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4105_ == 0)
{
lean_object* v_unused_4106_; 
v_unused_4106_ = lean_ctor_get(v___x_4096_, 1);
lean_dec(v_unused_4106_);
v___x_4099_ = v___x_4096_;
v_isShared_4100_ = v_isSharedCheck_4105_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_pos_4097_);
lean_dec(v___x_4096_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4105_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4101_; lean_object* v___x_4103_; 
v___x_4101_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_4100_ == 0)
{
lean_ctor_set(v___x_4099_, 1, v___x_4101_);
v___x_4103_ = v___x_4099_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_pos_4097_);
lean_ctor_set(v_reuseFailAlloc_4104_, 1, v___x_4101_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
else
{
lean_object* v_pos_4107_; lean_object* v_err_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4121_; 
v_pos_4107_ = lean_ctor_get(v___x_4096_, 0);
v_err_4108_ = lean_ctor_get(v___x_4096_, 1);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4110_ = v___x_4096_;
v_isShared_4111_ = v_isSharedCheck_4121_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_err_4108_);
lean_inc(v_pos_4107_);
lean_dec(v___x_4096_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4121_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v_snd_4112_; lean_object* v_snd_4113_; uint8_t v_decide_4114_; 
v_snd_4112_ = lean_ctor_get(v_a_3332_, 1);
lean_inc(v_snd_4112_);
lean_dec_ref(v_a_3332_);
v_snd_4113_ = lean_ctor_get(v_pos_4107_, 1);
v_decide_4114_ = lean_nat_dec_eq(v_snd_4112_, v_snd_4113_);
lean_dec(v_snd_4112_);
if (v_decide_4114_ == 0)
{
lean_object* v___x_4116_; 
if (v_isShared_4111_ == 0)
{
v___x_4116_ = v___x_4110_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_pos_4107_);
lean_ctor_set(v_reuseFailAlloc_4117_, 1, v_err_4108_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
else
{
uint8_t v___x_4118_; uint8_t v___x_4119_; lean_object* v___x_4120_; 
lean_del_object(v___x_4110_);
lean_dec(v_err_4108_);
v___x_4118_ = 0;
v___x_4119_ = 2;
v___x_4120_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4118_, v___x_4119_, v_decide_4114_, v_pos_4107_);
return v___x_4120_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_4122_; 
lean_dec_ref(v_x_3331_);
lean_dec(v_reserve_3330_);
lean_dec_ref(v_config_3329_);
v___x_4122_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseZoneId(v_a_3332_);
return v___x_4122_;
}
}
v___jp_3333_:
{
uint8_t v___x_3335_; lean_object* v___x_3336_; 
v___x_3335_ = 0;
v___x_3336_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseGmtOffset(v___x_3335_, v___y_3334_);
return v___x_3336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(lean_object* v_date_4123_, lean_object* v_modifier_4124_, lean_object* v_data_4125_){
_start:
{
switch(lean_obj_tag(v_modifier_4124_))
{
case 0:
{
lean_object* v_y_4126_; lean_object* v_u_4127_; lean_object* v_Y_4128_; lean_object* v_D_4129_; lean_object* v_M_4130_; lean_object* v_L_4131_; lean_object* v_d_4132_; lean_object* v_Q_4133_; lean_object* v_q_4134_; lean_object* v_w_4135_; lean_object* v_W_4136_; lean_object* v_E_4137_; lean_object* v_e_4138_; lean_object* v_c_4139_; lean_object* v_F_4140_; lean_object* v_a_4141_; lean_object* v_b_4142_; lean_object* v_B_4143_; lean_object* v_h_4144_; lean_object* v_K_4145_; lean_object* v_k_4146_; lean_object* v_H_4147_; lean_object* v_m_4148_; lean_object* v_s_4149_; lean_object* v_S_4150_; lean_object* v_A_4151_; lean_object* v_n_4152_; lean_object* v_N_4153_; lean_object* v_V_4154_; lean_object* v_z_4155_; lean_object* v_zabbrev_4156_; lean_object* v_v_4157_; lean_object* v_O_4158_; lean_object* v_X_4159_; lean_object* v_x_4160_; lean_object* v_Z_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4169_; 
lean_dec_ref_known(v_modifier_4124_, 0);
v_y_4126_ = lean_ctor_get(v_date_4123_, 1);
v_u_4127_ = lean_ctor_get(v_date_4123_, 2);
v_Y_4128_ = lean_ctor_get(v_date_4123_, 3);
v_D_4129_ = lean_ctor_get(v_date_4123_, 4);
v_M_4130_ = lean_ctor_get(v_date_4123_, 5);
v_L_4131_ = lean_ctor_get(v_date_4123_, 6);
v_d_4132_ = lean_ctor_get(v_date_4123_, 7);
v_Q_4133_ = lean_ctor_get(v_date_4123_, 8);
v_q_4134_ = lean_ctor_get(v_date_4123_, 9);
v_w_4135_ = lean_ctor_get(v_date_4123_, 10);
v_W_4136_ = lean_ctor_get(v_date_4123_, 11);
v_E_4137_ = lean_ctor_get(v_date_4123_, 12);
v_e_4138_ = lean_ctor_get(v_date_4123_, 13);
v_c_4139_ = lean_ctor_get(v_date_4123_, 14);
v_F_4140_ = lean_ctor_get(v_date_4123_, 15);
v_a_4141_ = lean_ctor_get(v_date_4123_, 16);
v_b_4142_ = lean_ctor_get(v_date_4123_, 17);
v_B_4143_ = lean_ctor_get(v_date_4123_, 18);
v_h_4144_ = lean_ctor_get(v_date_4123_, 19);
v_K_4145_ = lean_ctor_get(v_date_4123_, 20);
v_k_4146_ = lean_ctor_get(v_date_4123_, 21);
v_H_4147_ = lean_ctor_get(v_date_4123_, 22);
v_m_4148_ = lean_ctor_get(v_date_4123_, 23);
v_s_4149_ = lean_ctor_get(v_date_4123_, 24);
v_S_4150_ = lean_ctor_get(v_date_4123_, 25);
v_A_4151_ = lean_ctor_get(v_date_4123_, 26);
v_n_4152_ = lean_ctor_get(v_date_4123_, 27);
v_N_4153_ = lean_ctor_get(v_date_4123_, 28);
v_V_4154_ = lean_ctor_get(v_date_4123_, 29);
v_z_4155_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_4156_ = lean_ctor_get(v_date_4123_, 31);
v_v_4157_ = lean_ctor_get(v_date_4123_, 32);
v_O_4158_ = lean_ctor_get(v_date_4123_, 33);
v_X_4159_ = lean_ctor_get(v_date_4123_, 34);
v_x_4160_ = lean_ctor_get(v_date_4123_, 35);
v_Z_4161_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_4169_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_4169_ == 0)
{
lean_object* v_unused_4170_; 
v_unused_4170_ = lean_ctor_get(v_date_4123_, 0);
lean_dec(v_unused_4170_);
v___x_4163_ = v_date_4123_;
v_isShared_4164_ = v_isSharedCheck_4169_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_Z_4161_);
lean_inc(v_x_4160_);
lean_inc(v_X_4159_);
lean_inc(v_O_4158_);
lean_inc(v_v_4157_);
lean_inc(v_zabbrev_4156_);
lean_inc(v_z_4155_);
lean_inc(v_V_4154_);
lean_inc(v_N_4153_);
lean_inc(v_n_4152_);
lean_inc(v_A_4151_);
lean_inc(v_S_4150_);
lean_inc(v_s_4149_);
lean_inc(v_m_4148_);
lean_inc(v_H_4147_);
lean_inc(v_k_4146_);
lean_inc(v_K_4145_);
lean_inc(v_h_4144_);
lean_inc(v_B_4143_);
lean_inc(v_b_4142_);
lean_inc(v_a_4141_);
lean_inc(v_F_4140_);
lean_inc(v_c_4139_);
lean_inc(v_e_4138_);
lean_inc(v_E_4137_);
lean_inc(v_W_4136_);
lean_inc(v_w_4135_);
lean_inc(v_q_4134_);
lean_inc(v_Q_4133_);
lean_inc(v_d_4132_);
lean_inc(v_L_4131_);
lean_inc(v_M_4130_);
lean_inc(v_D_4129_);
lean_inc(v_Y_4128_);
lean_inc(v_u_4127_);
lean_inc(v_y_4126_);
lean_dec(v_date_4123_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4169_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4165_; lean_object* v___x_4167_; 
v___x_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4165_, 0, v_data_4125_);
if (v_isShared_4164_ == 0)
{
lean_ctor_set(v___x_4163_, 0, v___x_4165_);
v___x_4167_ = v___x_4163_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4165_);
lean_ctor_set(v_reuseFailAlloc_4168_, 1, v_y_4126_);
lean_ctor_set(v_reuseFailAlloc_4168_, 2, v_u_4127_);
lean_ctor_set(v_reuseFailAlloc_4168_, 3, v_Y_4128_);
lean_ctor_set(v_reuseFailAlloc_4168_, 4, v_D_4129_);
lean_ctor_set(v_reuseFailAlloc_4168_, 5, v_M_4130_);
lean_ctor_set(v_reuseFailAlloc_4168_, 6, v_L_4131_);
lean_ctor_set(v_reuseFailAlloc_4168_, 7, v_d_4132_);
lean_ctor_set(v_reuseFailAlloc_4168_, 8, v_Q_4133_);
lean_ctor_set(v_reuseFailAlloc_4168_, 9, v_q_4134_);
lean_ctor_set(v_reuseFailAlloc_4168_, 10, v_w_4135_);
lean_ctor_set(v_reuseFailAlloc_4168_, 11, v_W_4136_);
lean_ctor_set(v_reuseFailAlloc_4168_, 12, v_E_4137_);
lean_ctor_set(v_reuseFailAlloc_4168_, 13, v_e_4138_);
lean_ctor_set(v_reuseFailAlloc_4168_, 14, v_c_4139_);
lean_ctor_set(v_reuseFailAlloc_4168_, 15, v_F_4140_);
lean_ctor_set(v_reuseFailAlloc_4168_, 16, v_a_4141_);
lean_ctor_set(v_reuseFailAlloc_4168_, 17, v_b_4142_);
lean_ctor_set(v_reuseFailAlloc_4168_, 18, v_B_4143_);
lean_ctor_set(v_reuseFailAlloc_4168_, 19, v_h_4144_);
lean_ctor_set(v_reuseFailAlloc_4168_, 20, v_K_4145_);
lean_ctor_set(v_reuseFailAlloc_4168_, 21, v_k_4146_);
lean_ctor_set(v_reuseFailAlloc_4168_, 22, v_H_4147_);
lean_ctor_set(v_reuseFailAlloc_4168_, 23, v_m_4148_);
lean_ctor_set(v_reuseFailAlloc_4168_, 24, v_s_4149_);
lean_ctor_set(v_reuseFailAlloc_4168_, 25, v_S_4150_);
lean_ctor_set(v_reuseFailAlloc_4168_, 26, v_A_4151_);
lean_ctor_set(v_reuseFailAlloc_4168_, 27, v_n_4152_);
lean_ctor_set(v_reuseFailAlloc_4168_, 28, v_N_4153_);
lean_ctor_set(v_reuseFailAlloc_4168_, 29, v_V_4154_);
lean_ctor_set(v_reuseFailAlloc_4168_, 30, v_z_4155_);
lean_ctor_set(v_reuseFailAlloc_4168_, 31, v_zabbrev_4156_);
lean_ctor_set(v_reuseFailAlloc_4168_, 32, v_v_4157_);
lean_ctor_set(v_reuseFailAlloc_4168_, 33, v_O_4158_);
lean_ctor_set(v_reuseFailAlloc_4168_, 34, v_X_4159_);
lean_ctor_set(v_reuseFailAlloc_4168_, 35, v_x_4160_);
lean_ctor_set(v_reuseFailAlloc_4168_, 36, v_Z_4161_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
}
case 1:
{
lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4221_; 
v_isSharedCheck_4221_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_4221_ == 0)
{
lean_object* v_unused_4222_; 
v_unused_4222_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_4222_);
v___x_4172_ = v_modifier_4124_;
v_isShared_4173_ = v_isSharedCheck_4221_;
goto v_resetjp_4171_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4221_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v_G_4174_; lean_object* v_y_4175_; lean_object* v_Y_4176_; lean_object* v_D_4177_; lean_object* v_M_4178_; lean_object* v_L_4179_; lean_object* v_d_4180_; lean_object* v_Q_4181_; lean_object* v_q_4182_; lean_object* v_w_4183_; lean_object* v_W_4184_; lean_object* v_E_4185_; lean_object* v_e_4186_; lean_object* v_c_4187_; lean_object* v_F_4188_; lean_object* v_a_4189_; lean_object* v_b_4190_; lean_object* v_B_4191_; lean_object* v_h_4192_; lean_object* v_K_4193_; lean_object* v_k_4194_; lean_object* v_H_4195_; lean_object* v_m_4196_; lean_object* v_s_4197_; lean_object* v_S_4198_; lean_object* v_A_4199_; lean_object* v_n_4200_; lean_object* v_N_4201_; lean_object* v_V_4202_; lean_object* v_z_4203_; lean_object* v_zabbrev_4204_; lean_object* v_v_4205_; lean_object* v_O_4206_; lean_object* v_X_4207_; lean_object* v_x_4208_; lean_object* v_Z_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4219_; 
v_G_4174_ = lean_ctor_get(v_date_4123_, 0);
v_y_4175_ = lean_ctor_get(v_date_4123_, 1);
v_Y_4176_ = lean_ctor_get(v_date_4123_, 3);
v_D_4177_ = lean_ctor_get(v_date_4123_, 4);
v_M_4178_ = lean_ctor_get(v_date_4123_, 5);
v_L_4179_ = lean_ctor_get(v_date_4123_, 6);
v_d_4180_ = lean_ctor_get(v_date_4123_, 7);
v_Q_4181_ = lean_ctor_get(v_date_4123_, 8);
v_q_4182_ = lean_ctor_get(v_date_4123_, 9);
v_w_4183_ = lean_ctor_get(v_date_4123_, 10);
v_W_4184_ = lean_ctor_get(v_date_4123_, 11);
v_E_4185_ = lean_ctor_get(v_date_4123_, 12);
v_e_4186_ = lean_ctor_get(v_date_4123_, 13);
v_c_4187_ = lean_ctor_get(v_date_4123_, 14);
v_F_4188_ = lean_ctor_get(v_date_4123_, 15);
v_a_4189_ = lean_ctor_get(v_date_4123_, 16);
v_b_4190_ = lean_ctor_get(v_date_4123_, 17);
v_B_4191_ = lean_ctor_get(v_date_4123_, 18);
v_h_4192_ = lean_ctor_get(v_date_4123_, 19);
v_K_4193_ = lean_ctor_get(v_date_4123_, 20);
v_k_4194_ = lean_ctor_get(v_date_4123_, 21);
v_H_4195_ = lean_ctor_get(v_date_4123_, 22);
v_m_4196_ = lean_ctor_get(v_date_4123_, 23);
v_s_4197_ = lean_ctor_get(v_date_4123_, 24);
v_S_4198_ = lean_ctor_get(v_date_4123_, 25);
v_A_4199_ = lean_ctor_get(v_date_4123_, 26);
v_n_4200_ = lean_ctor_get(v_date_4123_, 27);
v_N_4201_ = lean_ctor_get(v_date_4123_, 28);
v_V_4202_ = lean_ctor_get(v_date_4123_, 29);
v_z_4203_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_4204_ = lean_ctor_get(v_date_4123_, 31);
v_v_4205_ = lean_ctor_get(v_date_4123_, 32);
v_O_4206_ = lean_ctor_get(v_date_4123_, 33);
v_X_4207_ = lean_ctor_get(v_date_4123_, 34);
v_x_4208_ = lean_ctor_get(v_date_4123_, 35);
v_Z_4209_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_4219_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_4219_ == 0)
{
lean_object* v_unused_4220_; 
v_unused_4220_ = lean_ctor_get(v_date_4123_, 2);
lean_dec(v_unused_4220_);
v___x_4211_ = v_date_4123_;
v_isShared_4212_ = v_isSharedCheck_4219_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_Z_4209_);
lean_inc(v_x_4208_);
lean_inc(v_X_4207_);
lean_inc(v_O_4206_);
lean_inc(v_v_4205_);
lean_inc(v_zabbrev_4204_);
lean_inc(v_z_4203_);
lean_inc(v_V_4202_);
lean_inc(v_N_4201_);
lean_inc(v_n_4200_);
lean_inc(v_A_4199_);
lean_inc(v_S_4198_);
lean_inc(v_s_4197_);
lean_inc(v_m_4196_);
lean_inc(v_H_4195_);
lean_inc(v_k_4194_);
lean_inc(v_K_4193_);
lean_inc(v_h_4192_);
lean_inc(v_B_4191_);
lean_inc(v_b_4190_);
lean_inc(v_a_4189_);
lean_inc(v_F_4188_);
lean_inc(v_c_4187_);
lean_inc(v_e_4186_);
lean_inc(v_E_4185_);
lean_inc(v_W_4184_);
lean_inc(v_w_4183_);
lean_inc(v_q_4182_);
lean_inc(v_Q_4181_);
lean_inc(v_d_4180_);
lean_inc(v_L_4179_);
lean_inc(v_M_4178_);
lean_inc(v_D_4177_);
lean_inc(v_Y_4176_);
lean_inc(v_y_4175_);
lean_inc(v_G_4174_);
lean_dec(v_date_4123_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4219_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4214_; 
if (v_isShared_4173_ == 0)
{
lean_ctor_set(v___x_4172_, 0, v_data_4125_);
v___x_4214_ = v___x_4172_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_data_4125_);
v___x_4214_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
lean_object* v___x_4216_; 
if (v_isShared_4212_ == 0)
{
lean_ctor_set(v___x_4211_, 2, v___x_4214_);
v___x_4216_ = v___x_4211_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_G_4174_);
lean_ctor_set(v_reuseFailAlloc_4217_, 1, v_y_4175_);
lean_ctor_set(v_reuseFailAlloc_4217_, 2, v___x_4214_);
lean_ctor_set(v_reuseFailAlloc_4217_, 3, v_Y_4176_);
lean_ctor_set(v_reuseFailAlloc_4217_, 4, v_D_4177_);
lean_ctor_set(v_reuseFailAlloc_4217_, 5, v_M_4178_);
lean_ctor_set(v_reuseFailAlloc_4217_, 6, v_L_4179_);
lean_ctor_set(v_reuseFailAlloc_4217_, 7, v_d_4180_);
lean_ctor_set(v_reuseFailAlloc_4217_, 8, v_Q_4181_);
lean_ctor_set(v_reuseFailAlloc_4217_, 9, v_q_4182_);
lean_ctor_set(v_reuseFailAlloc_4217_, 10, v_w_4183_);
lean_ctor_set(v_reuseFailAlloc_4217_, 11, v_W_4184_);
lean_ctor_set(v_reuseFailAlloc_4217_, 12, v_E_4185_);
lean_ctor_set(v_reuseFailAlloc_4217_, 13, v_e_4186_);
lean_ctor_set(v_reuseFailAlloc_4217_, 14, v_c_4187_);
lean_ctor_set(v_reuseFailAlloc_4217_, 15, v_F_4188_);
lean_ctor_set(v_reuseFailAlloc_4217_, 16, v_a_4189_);
lean_ctor_set(v_reuseFailAlloc_4217_, 17, v_b_4190_);
lean_ctor_set(v_reuseFailAlloc_4217_, 18, v_B_4191_);
lean_ctor_set(v_reuseFailAlloc_4217_, 19, v_h_4192_);
lean_ctor_set(v_reuseFailAlloc_4217_, 20, v_K_4193_);
lean_ctor_set(v_reuseFailAlloc_4217_, 21, v_k_4194_);
lean_ctor_set(v_reuseFailAlloc_4217_, 22, v_H_4195_);
lean_ctor_set(v_reuseFailAlloc_4217_, 23, v_m_4196_);
lean_ctor_set(v_reuseFailAlloc_4217_, 24, v_s_4197_);
lean_ctor_set(v_reuseFailAlloc_4217_, 25, v_S_4198_);
lean_ctor_set(v_reuseFailAlloc_4217_, 26, v_A_4199_);
lean_ctor_set(v_reuseFailAlloc_4217_, 27, v_n_4200_);
lean_ctor_set(v_reuseFailAlloc_4217_, 28, v_N_4201_);
lean_ctor_set(v_reuseFailAlloc_4217_, 29, v_V_4202_);
lean_ctor_set(v_reuseFailAlloc_4217_, 30, v_z_4203_);
lean_ctor_set(v_reuseFailAlloc_4217_, 31, v_zabbrev_4204_);
lean_ctor_set(v_reuseFailAlloc_4217_, 32, v_v_4205_);
lean_ctor_set(v_reuseFailAlloc_4217_, 33, v_O_4206_);
lean_ctor_set(v_reuseFailAlloc_4217_, 34, v_X_4207_);
lean_ctor_set(v_reuseFailAlloc_4217_, 35, v_x_4208_);
lean_ctor_set(v_reuseFailAlloc_4217_, 36, v_Z_4209_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
}
case 2:
{
lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4273_; 
v_isSharedCheck_4273_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_4273_ == 0)
{
lean_object* v_unused_4274_; 
v_unused_4274_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_4274_);
v___x_4224_ = v_modifier_4124_;
v_isShared_4225_ = v_isSharedCheck_4273_;
goto v_resetjp_4223_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4273_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v_G_4226_; lean_object* v_u_4227_; lean_object* v_Y_4228_; lean_object* v_D_4229_; lean_object* v_M_4230_; lean_object* v_L_4231_; lean_object* v_d_4232_; lean_object* v_Q_4233_; lean_object* v_q_4234_; lean_object* v_w_4235_; lean_object* v_W_4236_; lean_object* v_E_4237_; lean_object* v_e_4238_; lean_object* v_c_4239_; lean_object* v_F_4240_; lean_object* v_a_4241_; lean_object* v_b_4242_; lean_object* v_B_4243_; lean_object* v_h_4244_; lean_object* v_K_4245_; lean_object* v_k_4246_; lean_object* v_H_4247_; lean_object* v_m_4248_; lean_object* v_s_4249_; lean_object* v_S_4250_; lean_object* v_A_4251_; lean_object* v_n_4252_; lean_object* v_N_4253_; lean_object* v_V_4254_; lean_object* v_z_4255_; lean_object* v_zabbrev_4256_; lean_object* v_v_4257_; lean_object* v_O_4258_; lean_object* v_X_4259_; lean_object* v_x_4260_; lean_object* v_Z_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4271_; 
v_G_4226_ = lean_ctor_get(v_date_4123_, 0);
v_u_4227_ = lean_ctor_get(v_date_4123_, 2);
v_Y_4228_ = lean_ctor_get(v_date_4123_, 3);
v_D_4229_ = lean_ctor_get(v_date_4123_, 4);
v_M_4230_ = lean_ctor_get(v_date_4123_, 5);
v_L_4231_ = lean_ctor_get(v_date_4123_, 6);
v_d_4232_ = lean_ctor_get(v_date_4123_, 7);
v_Q_4233_ = lean_ctor_get(v_date_4123_, 8);
v_q_4234_ = lean_ctor_get(v_date_4123_, 9);
v_w_4235_ = lean_ctor_get(v_date_4123_, 10);
v_W_4236_ = lean_ctor_get(v_date_4123_, 11);
v_E_4237_ = lean_ctor_get(v_date_4123_, 12);
v_e_4238_ = lean_ctor_get(v_date_4123_, 13);
v_c_4239_ = lean_ctor_get(v_date_4123_, 14);
v_F_4240_ = lean_ctor_get(v_date_4123_, 15);
v_a_4241_ = lean_ctor_get(v_date_4123_, 16);
v_b_4242_ = lean_ctor_get(v_date_4123_, 17);
v_B_4243_ = lean_ctor_get(v_date_4123_, 18);
v_h_4244_ = lean_ctor_get(v_date_4123_, 19);
v_K_4245_ = lean_ctor_get(v_date_4123_, 20);
v_k_4246_ = lean_ctor_get(v_date_4123_, 21);
v_H_4247_ = lean_ctor_get(v_date_4123_, 22);
v_m_4248_ = lean_ctor_get(v_date_4123_, 23);
v_s_4249_ = lean_ctor_get(v_date_4123_, 24);
v_S_4250_ = lean_ctor_get(v_date_4123_, 25);
v_A_4251_ = lean_ctor_get(v_date_4123_, 26);
v_n_4252_ = lean_ctor_get(v_date_4123_, 27);
v_N_4253_ = lean_ctor_get(v_date_4123_, 28);
v_V_4254_ = lean_ctor_get(v_date_4123_, 29);
v_z_4255_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_4256_ = lean_ctor_get(v_date_4123_, 31);
v_v_4257_ = lean_ctor_get(v_date_4123_, 32);
v_O_4258_ = lean_ctor_get(v_date_4123_, 33);
v_X_4259_ = lean_ctor_get(v_date_4123_, 34);
v_x_4260_ = lean_ctor_get(v_date_4123_, 35);
v_Z_4261_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_4271_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_4271_ == 0)
{
lean_object* v_unused_4272_; 
v_unused_4272_ = lean_ctor_get(v_date_4123_, 1);
lean_dec(v_unused_4272_);
v___x_4263_ = v_date_4123_;
v_isShared_4264_ = v_isSharedCheck_4271_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_Z_4261_);
lean_inc(v_x_4260_);
lean_inc(v_X_4259_);
lean_inc(v_O_4258_);
lean_inc(v_v_4257_);
lean_inc(v_zabbrev_4256_);
lean_inc(v_z_4255_);
lean_inc(v_V_4254_);
lean_inc(v_N_4253_);
lean_inc(v_n_4252_);
lean_inc(v_A_4251_);
lean_inc(v_S_4250_);
lean_inc(v_s_4249_);
lean_inc(v_m_4248_);
lean_inc(v_H_4247_);
lean_inc(v_k_4246_);
lean_inc(v_K_4245_);
lean_inc(v_h_4244_);
lean_inc(v_B_4243_);
lean_inc(v_b_4242_);
lean_inc(v_a_4241_);
lean_inc(v_F_4240_);
lean_inc(v_c_4239_);
lean_inc(v_e_4238_);
lean_inc(v_E_4237_);
lean_inc(v_W_4236_);
lean_inc(v_w_4235_);
lean_inc(v_q_4234_);
lean_inc(v_Q_4233_);
lean_inc(v_d_4232_);
lean_inc(v_L_4231_);
lean_inc(v_M_4230_);
lean_inc(v_D_4229_);
lean_inc(v_Y_4228_);
lean_inc(v_u_4227_);
lean_inc(v_G_4226_);
lean_dec(v_date_4123_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4271_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4266_; 
if (v_isShared_4225_ == 0)
{
lean_ctor_set_tag(v___x_4224_, 1);
lean_ctor_set(v___x_4224_, 0, v_data_4125_);
v___x_4266_ = v___x_4224_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_data_4125_);
v___x_4266_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
lean_object* v___x_4268_; 
if (v_isShared_4264_ == 0)
{
lean_ctor_set(v___x_4263_, 1, v___x_4266_);
v___x_4268_ = v___x_4263_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_G_4226_);
lean_ctor_set(v_reuseFailAlloc_4269_, 1, v___x_4266_);
lean_ctor_set(v_reuseFailAlloc_4269_, 2, v_u_4227_);
lean_ctor_set(v_reuseFailAlloc_4269_, 3, v_Y_4228_);
lean_ctor_set(v_reuseFailAlloc_4269_, 4, v_D_4229_);
lean_ctor_set(v_reuseFailAlloc_4269_, 5, v_M_4230_);
lean_ctor_set(v_reuseFailAlloc_4269_, 6, v_L_4231_);
lean_ctor_set(v_reuseFailAlloc_4269_, 7, v_d_4232_);
lean_ctor_set(v_reuseFailAlloc_4269_, 8, v_Q_4233_);
lean_ctor_set(v_reuseFailAlloc_4269_, 9, v_q_4234_);
lean_ctor_set(v_reuseFailAlloc_4269_, 10, v_w_4235_);
lean_ctor_set(v_reuseFailAlloc_4269_, 11, v_W_4236_);
lean_ctor_set(v_reuseFailAlloc_4269_, 12, v_E_4237_);
lean_ctor_set(v_reuseFailAlloc_4269_, 13, v_e_4238_);
lean_ctor_set(v_reuseFailAlloc_4269_, 14, v_c_4239_);
lean_ctor_set(v_reuseFailAlloc_4269_, 15, v_F_4240_);
lean_ctor_set(v_reuseFailAlloc_4269_, 16, v_a_4241_);
lean_ctor_set(v_reuseFailAlloc_4269_, 17, v_b_4242_);
lean_ctor_set(v_reuseFailAlloc_4269_, 18, v_B_4243_);
lean_ctor_set(v_reuseFailAlloc_4269_, 19, v_h_4244_);
lean_ctor_set(v_reuseFailAlloc_4269_, 20, v_K_4245_);
lean_ctor_set(v_reuseFailAlloc_4269_, 21, v_k_4246_);
lean_ctor_set(v_reuseFailAlloc_4269_, 22, v_H_4247_);
lean_ctor_set(v_reuseFailAlloc_4269_, 23, v_m_4248_);
lean_ctor_set(v_reuseFailAlloc_4269_, 24, v_s_4249_);
lean_ctor_set(v_reuseFailAlloc_4269_, 25, v_S_4250_);
lean_ctor_set(v_reuseFailAlloc_4269_, 26, v_A_4251_);
lean_ctor_set(v_reuseFailAlloc_4269_, 27, v_n_4252_);
lean_ctor_set(v_reuseFailAlloc_4269_, 28, v_N_4253_);
lean_ctor_set(v_reuseFailAlloc_4269_, 29, v_V_4254_);
lean_ctor_set(v_reuseFailAlloc_4269_, 30, v_z_4255_);
lean_ctor_set(v_reuseFailAlloc_4269_, 31, v_zabbrev_4256_);
lean_ctor_set(v_reuseFailAlloc_4269_, 32, v_v_4257_);
lean_ctor_set(v_reuseFailAlloc_4269_, 33, v_O_4258_);
lean_ctor_set(v_reuseFailAlloc_4269_, 34, v_X_4259_);
lean_ctor_set(v_reuseFailAlloc_4269_, 35, v_x_4260_);
lean_ctor_set(v_reuseFailAlloc_4269_, 36, v_Z_4261_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
}
case 3:
{
lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4325_; 
v_isSharedCheck_4325_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_4325_ == 0)
{
lean_object* v_unused_4326_; 
v_unused_4326_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_4326_);
v___x_4276_ = v_modifier_4124_;
v_isShared_4277_ = v_isSharedCheck_4325_;
goto v_resetjp_4275_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4325_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v_G_4278_; lean_object* v_y_4279_; lean_object* v_u_4280_; lean_object* v_Y_4281_; lean_object* v_M_4282_; lean_object* v_L_4283_; lean_object* v_d_4284_; lean_object* v_Q_4285_; lean_object* v_q_4286_; lean_object* v_w_4287_; lean_object* v_W_4288_; lean_object* v_E_4289_; lean_object* v_e_4290_; lean_object* v_c_4291_; lean_object* v_F_4292_; lean_object* v_a_4293_; lean_object* v_b_4294_; lean_object* v_B_4295_; lean_object* v_h_4296_; lean_object* v_K_4297_; lean_object* v_k_4298_; lean_object* v_H_4299_; lean_object* v_m_4300_; lean_object* v_s_4301_; lean_object* v_S_4302_; lean_object* v_A_4303_; lean_object* v_n_4304_; lean_object* v_N_4305_; lean_object* v_V_4306_; lean_object* v_z_4307_; lean_object* v_zabbrev_4308_; lean_object* v_v_4309_; lean_object* v_O_4310_; lean_object* v_X_4311_; lean_object* v_x_4312_; lean_object* v_Z_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4323_; 
v_G_4278_ = lean_ctor_get(v_date_4123_, 0);
v_y_4279_ = lean_ctor_get(v_date_4123_, 1);
v_u_4280_ = lean_ctor_get(v_date_4123_, 2);
v_Y_4281_ = lean_ctor_get(v_date_4123_, 3);
v_M_4282_ = lean_ctor_get(v_date_4123_, 5);
v_L_4283_ = lean_ctor_get(v_date_4123_, 6);
v_d_4284_ = lean_ctor_get(v_date_4123_, 7);
v_Q_4285_ = lean_ctor_get(v_date_4123_, 8);
v_q_4286_ = lean_ctor_get(v_date_4123_, 9);
v_w_4287_ = lean_ctor_get(v_date_4123_, 10);
v_W_4288_ = lean_ctor_get(v_date_4123_, 11);
v_E_4289_ = lean_ctor_get(v_date_4123_, 12);
v_e_4290_ = lean_ctor_get(v_date_4123_, 13);
v_c_4291_ = lean_ctor_get(v_date_4123_, 14);
v_F_4292_ = lean_ctor_get(v_date_4123_, 15);
v_a_4293_ = lean_ctor_get(v_date_4123_, 16);
v_b_4294_ = lean_ctor_get(v_date_4123_, 17);
v_B_4295_ = lean_ctor_get(v_date_4123_, 18);
v_h_4296_ = lean_ctor_get(v_date_4123_, 19);
v_K_4297_ = lean_ctor_get(v_date_4123_, 20);
v_k_4298_ = lean_ctor_get(v_date_4123_, 21);
v_H_4299_ = lean_ctor_get(v_date_4123_, 22);
v_m_4300_ = lean_ctor_get(v_date_4123_, 23);
v_s_4301_ = lean_ctor_get(v_date_4123_, 24);
v_S_4302_ = lean_ctor_get(v_date_4123_, 25);
v_A_4303_ = lean_ctor_get(v_date_4123_, 26);
v_n_4304_ = lean_ctor_get(v_date_4123_, 27);
v_N_4305_ = lean_ctor_get(v_date_4123_, 28);
v_V_4306_ = lean_ctor_get(v_date_4123_, 29);
v_z_4307_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_4308_ = lean_ctor_get(v_date_4123_, 31);
v_v_4309_ = lean_ctor_get(v_date_4123_, 32);
v_O_4310_ = lean_ctor_get(v_date_4123_, 33);
v_X_4311_ = lean_ctor_get(v_date_4123_, 34);
v_x_4312_ = lean_ctor_get(v_date_4123_, 35);
v_Z_4313_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_4323_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_4323_ == 0)
{
lean_object* v_unused_4324_; 
v_unused_4324_ = lean_ctor_get(v_date_4123_, 4);
lean_dec(v_unused_4324_);
v___x_4315_ = v_date_4123_;
v_isShared_4316_ = v_isSharedCheck_4323_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_Z_4313_);
lean_inc(v_x_4312_);
lean_inc(v_X_4311_);
lean_inc(v_O_4310_);
lean_inc(v_v_4309_);
lean_inc(v_zabbrev_4308_);
lean_inc(v_z_4307_);
lean_inc(v_V_4306_);
lean_inc(v_N_4305_);
lean_inc(v_n_4304_);
lean_inc(v_A_4303_);
lean_inc(v_S_4302_);
lean_inc(v_s_4301_);
lean_inc(v_m_4300_);
lean_inc(v_H_4299_);
lean_inc(v_k_4298_);
lean_inc(v_K_4297_);
lean_inc(v_h_4296_);
lean_inc(v_B_4295_);
lean_inc(v_b_4294_);
lean_inc(v_a_4293_);
lean_inc(v_F_4292_);
lean_inc(v_c_4291_);
lean_inc(v_e_4290_);
lean_inc(v_E_4289_);
lean_inc(v_W_4288_);
lean_inc(v_w_4287_);
lean_inc(v_q_4286_);
lean_inc(v_Q_4285_);
lean_inc(v_d_4284_);
lean_inc(v_L_4283_);
lean_inc(v_M_4282_);
lean_inc(v_Y_4281_);
lean_inc(v_u_4280_);
lean_inc(v_y_4279_);
lean_inc(v_G_4278_);
lean_dec(v_date_4123_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4323_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v___x_4318_; 
if (v_isShared_4277_ == 0)
{
lean_ctor_set_tag(v___x_4276_, 1);
lean_ctor_set(v___x_4276_, 0, v_data_4125_);
v___x_4318_ = v___x_4276_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_data_4125_);
v___x_4318_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
lean_object* v___x_4320_; 
if (v_isShared_4316_ == 0)
{
lean_ctor_set(v___x_4315_, 4, v___x_4318_);
v___x_4320_ = v___x_4315_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_G_4278_);
lean_ctor_set(v_reuseFailAlloc_4321_, 1, v_y_4279_);
lean_ctor_set(v_reuseFailAlloc_4321_, 2, v_u_4280_);
lean_ctor_set(v_reuseFailAlloc_4321_, 3, v_Y_4281_);
lean_ctor_set(v_reuseFailAlloc_4321_, 4, v___x_4318_);
lean_ctor_set(v_reuseFailAlloc_4321_, 5, v_M_4282_);
lean_ctor_set(v_reuseFailAlloc_4321_, 6, v_L_4283_);
lean_ctor_set(v_reuseFailAlloc_4321_, 7, v_d_4284_);
lean_ctor_set(v_reuseFailAlloc_4321_, 8, v_Q_4285_);
lean_ctor_set(v_reuseFailAlloc_4321_, 9, v_q_4286_);
lean_ctor_set(v_reuseFailAlloc_4321_, 10, v_w_4287_);
lean_ctor_set(v_reuseFailAlloc_4321_, 11, v_W_4288_);
lean_ctor_set(v_reuseFailAlloc_4321_, 12, v_E_4289_);
lean_ctor_set(v_reuseFailAlloc_4321_, 13, v_e_4290_);
lean_ctor_set(v_reuseFailAlloc_4321_, 14, v_c_4291_);
lean_ctor_set(v_reuseFailAlloc_4321_, 15, v_F_4292_);
lean_ctor_set(v_reuseFailAlloc_4321_, 16, v_a_4293_);
lean_ctor_set(v_reuseFailAlloc_4321_, 17, v_b_4294_);
lean_ctor_set(v_reuseFailAlloc_4321_, 18, v_B_4295_);
lean_ctor_set(v_reuseFailAlloc_4321_, 19, v_h_4296_);
lean_ctor_set(v_reuseFailAlloc_4321_, 20, v_K_4297_);
lean_ctor_set(v_reuseFailAlloc_4321_, 21, v_k_4298_);
lean_ctor_set(v_reuseFailAlloc_4321_, 22, v_H_4299_);
lean_ctor_set(v_reuseFailAlloc_4321_, 23, v_m_4300_);
lean_ctor_set(v_reuseFailAlloc_4321_, 24, v_s_4301_);
lean_ctor_set(v_reuseFailAlloc_4321_, 25, v_S_4302_);
lean_ctor_set(v_reuseFailAlloc_4321_, 26, v_A_4303_);
lean_ctor_set(v_reuseFailAlloc_4321_, 27, v_n_4304_);
lean_ctor_set(v_reuseFailAlloc_4321_, 28, v_N_4305_);
lean_ctor_set(v_reuseFailAlloc_4321_, 29, v_V_4306_);
lean_ctor_set(v_reuseFailAlloc_4321_, 30, v_z_4307_);
lean_ctor_set(v_reuseFailAlloc_4321_, 31, v_zabbrev_4308_);
lean_ctor_set(v_reuseFailAlloc_4321_, 32, v_v_4309_);
lean_ctor_set(v_reuseFailAlloc_4321_, 33, v_O_4310_);
lean_ctor_set(v_reuseFailAlloc_4321_, 34, v_X_4311_);
lean_ctor_set(v_reuseFailAlloc_4321_, 35, v_x_4312_);
lean_ctor_set(v_reuseFailAlloc_4321_, 36, v_Z_4313_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
return v___x_4320_;
}
}
}
}
}
case 4:
{
lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4377_; 
v_isSharedCheck_4377_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_4377_ == 0)
{
lean_object* v_unused_4378_; 
v_unused_4378_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_4378_);
v___x_4328_ = v_modifier_4124_;
v_isShared_4329_ = v_isSharedCheck_4377_;
goto v_resetjp_4327_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4377_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v_G_4330_; lean_object* v_y_4331_; lean_object* v_u_4332_; lean_object* v_Y_4333_; lean_object* v_D_4334_; lean_object* v_L_4335_; lean_object* v_d_4336_; lean_object* v_Q_4337_; lean_object* v_q_4338_; lean_object* v_w_4339_; lean_object* v_W_4340_; lean_object* v_E_4341_; lean_object* v_e_4342_; lean_object* v_c_4343_; lean_object* v_F_4344_; lean_object* v_a_4345_; lean_object* v_b_4346_; lean_object* v_B_4347_; lean_object* v_h_4348_; lean_object* v_K_4349_; lean_object* v_k_4350_; lean_object* v_H_4351_; lean_object* v_m_4352_; lean_object* v_s_4353_; lean_object* v_S_4354_; lean_object* v_A_4355_; lean_object* v_n_4356_; lean_object* v_N_4357_; lean_object* v_V_4358_; lean_object* v_z_4359_; lean_object* v_zabbrev_4360_; lean_object* v_v_4361_; lean_object* v_O_4362_; lean_object* v_X_4363_; lean_object* v_x_4364_; lean_object* v_Z_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4375_; 
v_G_4330_ = lean_ctor_get(v_date_4123_, 0);
v_y_4331_ = lean_ctor_get(v_date_4123_, 1);
v_u_4332_ = lean_ctor_get(v_date_4123_, 2);
v_Y_4333_ = lean_ctor_get(v_date_4123_, 3);
v_D_4334_ = lean_ctor_get(v_date_4123_, 4);
v_L_4335_ = lean_ctor_get(v_date_4123_, 6);
v_d_4336_ = lean_ctor_get(v_date_4123_, 7);
v_Q_4337_ = lean_ctor_get(v_date_4123_, 8);
v_q_4338_ = lean_ctor_get(v_date_4123_, 9);
v_w_4339_ = lean_ctor_get(v_date_4123_, 10);
v_W_4340_ = lean_ctor_get(v_date_4123_, 11);
v_E_4341_ = lean_ctor_get(v_date_4123_, 12);
v_e_4342_ = lean_ctor_get(v_date_4123_, 13);
v_c_4343_ = lean_ctor_get(v_date_4123_, 14);
v_F_4344_ = lean_ctor_get(v_date_4123_, 15);
v_a_4345_ = lean_ctor_get(v_date_4123_, 16);
v_b_4346_ = lean_ctor_get(v_date_4123_, 17);
v_B_4347_ = lean_ctor_get(v_date_4123_, 18);
v_h_4348_ = lean_ctor_get(v_date_4123_, 19);
v_K_4349_ = lean_ctor_get(v_date_4123_, 20);
v_k_4350_ = lean_ctor_get(v_date_4123_, 21);
v_H_4351_ = lean_ctor_get(v_date_4123_, 22);
v_m_4352_ = lean_ctor_get(v_date_4123_, 23);
v_s_4353_ = lean_ctor_get(v_date_4123_, 24);
v_S_4354_ = lean_ctor_get(v_date_4123_, 25);
v_A_4355_ = lean_ctor_get(v_date_4123_, 26);
v_n_4356_ = lean_ctor_get(v_date_4123_, 27);
v_N_4357_ = lean_ctor_get(v_date_4123_, 28);
v_V_4358_ = lean_ctor_get(v_date_4123_, 29);
v_z_4359_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_4360_ = lean_ctor_get(v_date_4123_, 31);
v_v_4361_ = lean_ctor_get(v_date_4123_, 32);
v_O_4362_ = lean_ctor_get(v_date_4123_, 33);
v_X_4363_ = lean_ctor_get(v_date_4123_, 34);
v_x_4364_ = lean_ctor_get(v_date_4123_, 35);
v_Z_4365_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_4375_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_4375_ == 0)
{
lean_object* v_unused_4376_; 
v_unused_4376_ = lean_ctor_get(v_date_4123_, 5);
lean_dec(v_unused_4376_);
v___x_4367_ = v_date_4123_;
v_isShared_4368_ = v_isSharedCheck_4375_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_Z_4365_);
lean_inc(v_x_4364_);
lean_inc(v_X_4363_);
lean_inc(v_O_4362_);
lean_inc(v_v_4361_);
lean_inc(v_zabbrev_4360_);
lean_inc(v_z_4359_);
lean_inc(v_V_4358_);
lean_inc(v_N_4357_);
lean_inc(v_n_4356_);
lean_inc(v_A_4355_);
lean_inc(v_S_4354_);
lean_inc(v_s_4353_);
lean_inc(v_m_4352_);
lean_inc(v_H_4351_);
lean_inc(v_k_4350_);
lean_inc(v_K_4349_);
lean_inc(v_h_4348_);
lean_inc(v_B_4347_);
lean_inc(v_b_4346_);
lean_inc(v_a_4345_);
lean_inc(v_F_4344_);
lean_inc(v_c_4343_);
lean_inc(v_e_4342_);
lean_inc(v_E_4341_);
lean_inc(v_W_4340_);
lean_inc(v_w_4339_);
lean_inc(v_q_4338_);
lean_inc(v_Q_4337_);
lean_inc(v_d_4336_);
lean_inc(v_L_4335_);
lean_inc(v_D_4334_);
lean_inc(v_Y_4333_);
lean_inc(v_u_4332_);
lean_inc(v_y_4331_);
lean_inc(v_G_4330_);
lean_dec(v_date_4123_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4375_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4370_; 
if (v_isShared_4329_ == 0)
{
lean_ctor_set_tag(v___x_4328_, 1);
lean_ctor_set(v___x_4328_, 0, v_data_4125_);
v___x_4370_ = v___x_4328_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_data_4125_);
v___x_4370_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
lean_object* v___x_4372_; 
if (v_isShared_4368_ == 0)
{
lean_ctor_set(v___x_4367_, 5, v___x_4370_);
v___x_4372_ = v___x_4367_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v_G_4330_);
lean_ctor_set(v_reuseFailAlloc_4373_, 1, v_y_4331_);
lean_ctor_set(v_reuseFailAlloc_4373_, 2, v_u_4332_);
lean_ctor_set(v_reuseFailAlloc_4373_, 3, v_Y_4333_);
lean_ctor_set(v_reuseFailAlloc_4373_, 4, v_D_4334_);
lean_ctor_set(v_reuseFailAlloc_4373_, 5, v___x_4370_);
lean_ctor_set(v_reuseFailAlloc_4373_, 6, v_L_4335_);
lean_ctor_set(v_reuseFailAlloc_4373_, 7, v_d_4336_);
lean_ctor_set(v_reuseFailAlloc_4373_, 8, v_Q_4337_);
lean_ctor_set(v_reuseFailAlloc_4373_, 9, v_q_4338_);
lean_ctor_set(v_reuseFailAlloc_4373_, 10, v_w_4339_);
lean_ctor_set(v_reuseFailAlloc_4373_, 11, v_W_4340_);
lean_ctor_set(v_reuseFailAlloc_4373_, 12, v_E_4341_);
lean_ctor_set(v_reuseFailAlloc_4373_, 13, v_e_4342_);
lean_ctor_set(v_reuseFailAlloc_4373_, 14, v_c_4343_);
lean_ctor_set(v_reuseFailAlloc_4373_, 15, v_F_4344_);
lean_ctor_set(v_reuseFailAlloc_4373_, 16, v_a_4345_);
lean_ctor_set(v_reuseFailAlloc_4373_, 17, v_b_4346_);
lean_ctor_set(v_reuseFailAlloc_4373_, 18, v_B_4347_);
lean_ctor_set(v_reuseFailAlloc_4373_, 19, v_h_4348_);
lean_ctor_set(v_reuseFailAlloc_4373_, 20, v_K_4349_);
lean_ctor_set(v_reuseFailAlloc_4373_, 21, v_k_4350_);
lean_ctor_set(v_reuseFailAlloc_4373_, 22, v_H_4351_);
lean_ctor_set(v_reuseFailAlloc_4373_, 23, v_m_4352_);
lean_ctor_set(v_reuseFailAlloc_4373_, 24, v_s_4353_);
lean_ctor_set(v_reuseFailAlloc_4373_, 25, v_S_4354_);
lean_ctor_set(v_reuseFailAlloc_4373_, 26, v_A_4355_);
lean_ctor_set(v_reuseFailAlloc_4373_, 27, v_n_4356_);
lean_ctor_set(v_reuseFailAlloc_4373_, 28, v_N_4357_);
lean_ctor_set(v_reuseFailAlloc_4373_, 29, v_V_4358_);
lean_ctor_set(v_reuseFailAlloc_4373_, 30, v_z_4359_);
lean_ctor_set(v_reuseFailAlloc_4373_, 31, v_zabbrev_4360_);
lean_ctor_set(v_reuseFailAlloc_4373_, 32, v_v_4361_);
lean_ctor_set(v_reuseFailAlloc_4373_, 33, v_O_4362_);
lean_ctor_set(v_reuseFailAlloc_4373_, 34, v_X_4363_);
lean_ctor_set(v_reuseFailAlloc_4373_, 35, v_x_4364_);
lean_ctor_set(v_reuseFailAlloc_4373_, 36, v_Z_4365_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
return v___x_4372_;
}
}
}
}
}
case 5:
{
lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4429_; 
v_isSharedCheck_4429_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_4429_ == 0)
{
lean_object* v_unused_4430_; 
v_unused_4430_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_4430_);
v___x_4380_ = v_modifier_4124_;
v_isShared_4381_ = v_isSharedCheck_4429_;
goto v_resetjp_4379_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4429_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v_G_4382_; lean_object* v_y_4383_; lean_object* v_u_4384_; lean_object* v_Y_4385_; lean_object* v_D_4386_; lean_object* v_M_4387_; lean_object* v_d_4388_; lean_object* v_Q_4389_; lean_object* v_q_4390_; lean_object* v_w_4391_; lean_object* v_W_4392_; lean_object* v_E_4393_; lean_object* v_e_4394_; lean_object* v_c_4395_; lean_object* v_F_4396_; lean_object* v_a_4397_; lean_object* v_b_4398_; lean_object* v_B_4399_; lean_object* v_h_4400_; lean_object* v_K_4401_; lean_object* v_k_4402_; lean_object* v_H_4403_; lean_object* v_m_4404_; lean_object* v_s_4405_; lean_object* v_S_4406_; lean_object* v_A_4407_; lean_object* v_n_4408_; lean_object* v_N_4409_; lean_object* v_V_4410_; lean_object* v_z_4411_; lean_object* v_zabbrev_4412_; lean_object* v_v_4413_; lean_object* v_O_4414_; lean_object* v_X_4415_; lean_object* v_x_4416_; lean_object* v_Z_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4427_; 
v_G_4382_ = lean_ctor_get(v_date_4123_, 0);
v_y_4383_ = lean_ctor_get(v_date_4123_, 1);
v_u_4384_ = lean_ctor_get(v_date_4123_, 2);
v_Y_4385_ = lean_ctor_get(v_date_4123_, 3);
v_D_4386_ = lean_ctor_get(v_date_4123_, 4);
v_M_4387_ = lean_ctor_get(v_date_4123_, 5);
v_d_4388_ = lean_ctor_get(v_date_4123_, 7);
v_Q_4389_ = lean_ctor_get(v_date_4123_, 8);
v_q_4390_ = lean_ctor_get(v_date_4123_, 9);
v_w_4391_ = lean_ctor_get(v_date_4123_, 10);
v_W_4392_ = lean_ctor_get(v_date_4123_, 11);
v_E_4393_ = lean_ctor_get(v_date_4123_, 12);
v_e_4394_ = lean_ctor_get(v_date_4123_, 13);
v_c_4395_ = lean_ctor_get(v_date_4123_, 14);
v_F_4396_ = lean_ctor_get(v_date_4123_, 15);
v_a_4397_ = lean_ctor_get(v_date_4123_, 16);
v_b_4398_ = lean_ctor_get(v_date_4123_, 17);
v_B_4399_ = lean_ctor_get(v_date_4123_, 18);
v_h_4400_ = lean_ctor_get(v_date_4123_, 19);
v_K_4401_ = lean_ctor_get(v_date_4123_, 20);
v_k_4402_ = lean_ctor_get(v_date_4123_, 21);
v_H_4403_ = lean_ctor_get(v_date_4123_, 22);
v_m_4404_ = lean_ctor_get(v_date_4123_, 23);
v_s_4405_ = lean_ctor_get(v_date_4123_, 24);
v_S_4406_ = lean_ctor_get(v_date_4123_, 25);
v_A_4407_ = lean_ctor_get(v_date_4123_, 26);
v_n_4408_ = lean_ctor_get(v_date_4123_, 27);
v_N_4409_ = lean_ctor_get(v_date_4123_, 28);
v_V_4410_ = lean_ctor_get(v_date_4123_, 29);
v_z_4411_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_4412_ = lean_ctor_get(v_date_4123_, 31);
v_v_4413_ = lean_ctor_get(v_date_4123_, 32);
v_O_4414_ = lean_ctor_get(v_date_4123_, 33);
v_X_4415_ = lean_ctor_get(v_date_4123_, 34);
v_x_4416_ = lean_ctor_get(v_date_4123_, 35);
v_Z_4417_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_4427_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_4427_ == 0)
{
lean_object* v_unused_4428_; 
v_unused_4428_ = lean_ctor_get(v_date_4123_, 6);
lean_dec(v_unused_4428_);
v___x_4419_ = v_date_4123_;
v_isShared_4420_ = v_isSharedCheck_4427_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_Z_4417_);
lean_inc(v_x_4416_);
lean_inc(v_X_4415_);
lean_inc(v_O_4414_);
lean_inc(v_v_4413_);
lean_inc(v_zabbrev_4412_);
lean_inc(v_z_4411_);
lean_inc(v_V_4410_);
lean_inc(v_N_4409_);
lean_inc(v_n_4408_);
lean_inc(v_A_4407_);
lean_inc(v_S_4406_);
lean_inc(v_s_4405_);
lean_inc(v_m_4404_);
lean_inc(v_H_4403_);
lean_inc(v_k_4402_);
lean_inc(v_K_4401_);
lean_inc(v_h_4400_);
lean_inc(v_B_4399_);
lean_inc(v_b_4398_);
lean_inc(v_a_4397_);
lean_inc(v_F_4396_);
lean_inc(v_c_4395_);
lean_inc(v_e_4394_);
lean_inc(v_E_4393_);
lean_inc(v_W_4392_);
lean_inc(v_w_4391_);
lean_inc(v_q_4390_);
lean_inc(v_Q_4389_);
lean_inc(v_d_4388_);
lean_inc(v_M_4387_);
lean_inc(v_D_4386_);
lean_inc(v_Y_4385_);
lean_inc(v_u_4384_);
lean_inc(v_y_4383_);
lean_inc(v_G_4382_);
lean_dec(v_date_4123_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4427_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4422_; 
if (v_isShared_4381_ == 0)
{
lean_ctor_set_tag(v___x_4380_, 1);
lean_ctor_set(v___x_4380_, 0, v_data_4125_);
v___x_4422_ = v___x_4380_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_data_4125_);
v___x_4422_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
lean_object* v___x_4424_; 
if (v_isShared_4420_ == 0)
{
lean_ctor_set(v___x_4419_, 6, v___x_4422_);
v___x_4424_ = v___x_4419_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_G_4382_);
lean_ctor_set(v_reuseFailAlloc_4425_, 1, v_y_4383_);
lean_ctor_set(v_reuseFailAlloc_4425_, 2, v_u_4384_);
lean_ctor_set(v_reuseFailAlloc_4425_, 3, v_Y_4385_);
lean_ctor_set(v_reuseFailAlloc_4425_, 4, v_D_4386_);
lean_ctor_set(v_reuseFailAlloc_4425_, 5, v_M_4387_);
lean_ctor_set(v_reuseFailAlloc_4425_, 6, v___x_4422_);
lean_ctor_set(v_reuseFailAlloc_4425_, 7, v_d_4388_);
lean_ctor_set(v_reuseFailAlloc_4425_, 8, v_Q_4389_);
lean_ctor_set(v_reuseFailAlloc_4425_, 9, v_q_4390_);
lean_ctor_set(v_reuseFailAlloc_4425_, 10, v_w_4391_);
lean_ctor_set(v_reuseFailAlloc_4425_, 11, v_W_4392_);
lean_ctor_set(v_reuseFailAlloc_4425_, 12, v_E_4393_);
lean_ctor_set(v_reuseFailAlloc_4425_, 13, v_e_4394_);
lean_ctor_set(v_reuseFailAlloc_4425_, 14, v_c_4395_);
lean_ctor_set(v_reuseFailAlloc_4425_, 15, v_F_4396_);
lean_ctor_set(v_reuseFailAlloc_4425_, 16, v_a_4397_);
lean_ctor_set(v_reuseFailAlloc_4425_, 17, v_b_4398_);
lean_ctor_set(v_reuseFailAlloc_4425_, 18, v_B_4399_);
lean_ctor_set(v_reuseFailAlloc_4425_, 19, v_h_4400_);
lean_ctor_set(v_reuseFailAlloc_4425_, 20, v_K_4401_);
lean_ctor_set(v_reuseFailAlloc_4425_, 21, v_k_4402_);
lean_ctor_set(v_reuseFailAlloc_4425_, 22, v_H_4403_);
lean_ctor_set(v_reuseFailAlloc_4425_, 23, v_m_4404_);
lean_ctor_set(v_reuseFailAlloc_4425_, 24, v_s_4405_);
lean_ctor_set(v_reuseFailAlloc_4425_, 25, v_S_4406_);
lean_ctor_set(v_reuseFailAlloc_4425_, 26, v_A_4407_);
lean_ctor_set(v_reuseFailAlloc_4425_, 27, v_n_4408_);
lean_ctor_set(v_reuseFailAlloc_4425_, 28, v_N_4409_);
lean_ctor_set(v_reuseFailAlloc_4425_, 29, v_V_4410_);
lean_ctor_set(v_reuseFailAlloc_4425_, 30, v_z_4411_);
lean_ctor_set(v_reuseFailAlloc_4425_, 31, v_zabbrev_4412_);
lean_ctor_set(v_reuseFailAlloc_4425_, 32, v_v_4413_);
lean_ctor_set(v_reuseFailAlloc_4425_, 33, v_O_4414_);
lean_ctor_set(v_reuseFailAlloc_4425_, 34, v_X_4415_);
lean_ctor_set(v_reuseFailAlloc_4425_, 35, v_x_4416_);
lean_ctor_set(v_reuseFailAlloc_4425_, 36, v_Z_4417_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
}
}
case 6:
{
lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4481_; 
v_isSharedCheck_4481_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_4481_ == 0)
{
lean_object* v_unused_4482_; 
v_unused_4482_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_4482_);
v___x_4432_ = v_modifier_4124_;
v_isShared_4433_ = v_isSharedCheck_4481_;
goto v_resetjp_4431_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4481_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v_G_4434_; lean_object* v_y_4435_; lean_object* v_u_4436_; lean_object* v_Y_4437_; lean_object* v_D_4438_; lean_object* v_M_4439_; lean_object* v_L_4440_; lean_object* v_Q_4441_; lean_object* v_q_4442_; lean_object* v_w_4443_; lean_object* v_W_4444_; lean_object* v_E_4445_; lean_object* v_e_4446_; lean_object* v_c_4447_; lean_object* v_F_4448_; lean_object* v_a_4449_; lean_object* v_b_4450_; lean_object* v_B_4451_; lean_object* v_h_4452_; lean_object* v_K_4453_; lean_object* v_k_4454_; lean_object* v_H_4455_; lean_object* v_m_4456_; lean_object* v_s_4457_; lean_object* v_S_4458_; lean_object* v_A_4459_; lean_object* v_n_4460_; lean_object* v_N_4461_; lean_object* v_V_4462_; lean_object* v_z_4463_; lean_object* v_zabbrev_4464_; lean_object* v_v_4465_; lean_object* v_O_4466_; lean_object* v_X_4467_; lean_object* v_x_4468_; lean_object* v_Z_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4479_; 
v_G_4434_ = lean_ctor_get(v_date_4123_, 0);
v_y_4435_ = lean_ctor_get(v_date_4123_, 1);
v_u_4436_ = lean_ctor_get(v_date_4123_, 2);
v_Y_4437_ = lean_ctor_get(v_date_4123_, 3);
v_D_4438_ = lean_ctor_get(v_date_4123_, 4);
v_M_4439_ = lean_ctor_get(v_date_4123_, 5);
v_L_4440_ = lean_ctor_get(v_date_4123_, 6);
v_Q_4441_ = lean_ctor_get(v_date_4123_, 8);
v_q_4442_ = lean_ctor_get(v_date_4123_, 9);
v_w_4443_ = lean_ctor_get(v_date_4123_, 10);
v_W_4444_ = lean_ctor_get(v_date_4123_, 11);
v_E_4445_ = lean_ctor_get(v_date_4123_, 12);
v_e_4446_ = lean_ctor_get(v_date_4123_, 13);
v_c_4447_ = lean_ctor_get(v_date_4123_, 14);
v_F_4448_ = lean_ctor_get(v_date_4123_, 15);
v_a_4449_ = lean_ctor_get(v_date_4123_, 16);
v_b_4450_ = lean_ctor_get(v_date_4123_, 17);
v_B_4451_ = lean_ctor_get(v_date_4123_, 18);
v_h_4452_ = lean_ctor_get(v_date_4123_, 19);
v_K_4453_ = lean_ctor_get(v_date_4123_, 20);
v_k_4454_ = lean_ctor_get(v_date_4123_, 21);
v_H_4455_ = lean_ctor_get(v_date_4123_, 22);
v_m_4456_ = lean_ctor_get(v_date_4123_, 23);
v_s_4457_ = lean_ctor_get(v_date_4123_, 24);
v_S_4458_ = lean_ctor_get(v_date_4123_, 25);
v_A_4459_ = lean_ctor_get(v_date_4123_, 26);
v_n_4460_ = lean_ctor_get(v_date_4123_, 27);
v_N_4461_ = lean_ctor_get(v_date_4123_, 28);
v_V_4462_ = lean_ctor_get(v_date_4123_, 29);
v_z_4463_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_4464_ = lean_ctor_get(v_date_4123_, 31);
v_v_4465_ = lean_ctor_get(v_date_4123_, 32);
v_O_4466_ = lean_ctor_get(v_date_4123_, 33);
v_X_4467_ = lean_ctor_get(v_date_4123_, 34);
v_x_4468_ = lean_ctor_get(v_date_4123_, 35);
v_Z_4469_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_4479_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_4479_ == 0)
{
lean_object* v_unused_4480_; 
v_unused_4480_ = lean_ctor_get(v_date_4123_, 7);
lean_dec(v_unused_4480_);
v___x_4471_ = v_date_4123_;
v_isShared_4472_ = v_isSharedCheck_4479_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_Z_4469_);
lean_inc(v_x_4468_);
lean_inc(v_X_4467_);
lean_inc(v_O_4466_);
lean_inc(v_v_4465_);
lean_inc(v_zabbrev_4464_);
lean_inc(v_z_4463_);
lean_inc(v_V_4462_);
lean_inc(v_N_4461_);
lean_inc(v_n_4460_);
lean_inc(v_A_4459_);
lean_inc(v_S_4458_);
lean_inc(v_s_4457_);
lean_inc(v_m_4456_);
lean_inc(v_H_4455_);
lean_inc(v_k_4454_);
lean_inc(v_K_4453_);
lean_inc(v_h_4452_);
lean_inc(v_B_4451_);
lean_inc(v_b_4450_);
lean_inc(v_a_4449_);
lean_inc(v_F_4448_);
lean_inc(v_c_4447_);
lean_inc(v_e_4446_);
lean_inc(v_E_4445_);
lean_inc(v_W_4444_);
lean_inc(v_w_4443_);
lean_inc(v_q_4442_);
lean_inc(v_Q_4441_);
lean_inc(v_L_4440_);
lean_inc(v_M_4439_);
lean_inc(v_D_4438_);
lean_inc(v_Y_4437_);
lean_inc(v_u_4436_);
lean_inc(v_y_4435_);
lean_inc(v_G_4434_);
lean_dec(v_date_4123_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4479_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4474_; 
if (v_isShared_4433_ == 0)
{
lean_ctor_set_tag(v___x_4432_, 1);
lean_ctor_set(v___x_4432_, 0, v_data_4125_);
v___x_4474_ = v___x_4432_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_data_4125_);
v___x_4474_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
lean_object* v___x_4476_; 
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 7, v___x_4474_);
v___x_4476_ = v___x_4471_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_G_4434_);
lean_ctor_set(v_reuseFailAlloc_4477_, 1, v_y_4435_);
lean_ctor_set(v_reuseFailAlloc_4477_, 2, v_u_4436_);
lean_ctor_set(v_reuseFailAlloc_4477_, 3, v_Y_4437_);
lean_ctor_set(v_reuseFailAlloc_4477_, 4, v_D_4438_);
lean_ctor_set(v_reuseFailAlloc_4477_, 5, v_M_4439_);
lean_ctor_set(v_reuseFailAlloc_4477_, 6, v_L_4440_);
lean_ctor_set(v_reuseFailAlloc_4477_, 7, v___x_4474_);
lean_ctor_set(v_reuseFailAlloc_4477_, 8, v_Q_4441_);
lean_ctor_set(v_reuseFailAlloc_4477_, 9, v_q_4442_);
lean_ctor_set(v_reuseFailAlloc_4477_, 10, v_w_4443_);
lean_ctor_set(v_reuseFailAlloc_4477_, 11, v_W_4444_);
lean_ctor_set(v_reuseFailAlloc_4477_, 12, v_E_4445_);
lean_ctor_set(v_reuseFailAlloc_4477_, 13, v_e_4446_);
lean_ctor_set(v_reuseFailAlloc_4477_, 14, v_c_4447_);
lean_ctor_set(v_reuseFailAlloc_4477_, 15, v_F_4448_);
lean_ctor_set(v_reuseFailAlloc_4477_, 16, v_a_4449_);
lean_ctor_set(v_reuseFailAlloc_4477_, 17, v_b_4450_);
lean_ctor_set(v_reuseFailAlloc_4477_, 18, v_B_4451_);
lean_ctor_set(v_reuseFailAlloc_4477_, 19, v_h_4452_);
lean_ctor_set(v_reuseFailAlloc_4477_, 20, v_K_4453_);
lean_ctor_set(v_reuseFailAlloc_4477_, 21, v_k_4454_);
lean_ctor_set(v_reuseFailAlloc_4477_, 22, v_H_4455_);
lean_ctor_set(v_reuseFailAlloc_4477_, 23, v_m_4456_);
lean_ctor_set(v_reuseFailAlloc_4477_, 24, v_s_4457_);
lean_ctor_set(v_reuseFailAlloc_4477_, 25, v_S_4458_);
lean_ctor_set(v_reuseFailAlloc_4477_, 26, v_A_4459_);
lean_ctor_set(v_reuseFailAlloc_4477_, 27, v_n_4460_);
lean_ctor_set(v_reuseFailAlloc_4477_, 28, v_N_4461_);
lean_ctor_set(v_reuseFailAlloc_4477_, 29, v_V_4462_);
lean_ctor_set(v_reuseFailAlloc_4477_, 30, v_z_4463_);
lean_ctor_set(v_reuseFailAlloc_4477_, 31, v_zabbrev_4464_);
lean_ctor_set(v_reuseFailAlloc_4477_, 32, v_v_4465_);
lean_ctor_set(v_reuseFailAlloc_4477_, 33, v_O_4466_);
lean_ctor_set(v_reuseFailAlloc_4477_, 34, v_X_4467_);
lean_ctor_set(v_reuseFailAlloc_4477_, 35, v_x_4468_);
lean_ctor_set(v_reuseFailAlloc_4477_, 36, v_Z_4469_);
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
case 7:
{
lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4533_; 
v_isSharedCheck_4533_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_4533_ == 0)
{
lean_object* v_unused_4534_; 
v_unused_4534_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_4534_);
v___x_4484_ = v_modifier_4124_;
v_isShared_4485_ = v_isSharedCheck_4533_;
goto v_resetjp_4483_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4533_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v_G_4486_; lean_object* v_y_4487_; lean_object* v_u_4488_; lean_object* v_Y_4489_; lean_object* v_D_4490_; lean_object* v_M_4491_; lean_object* v_L_4492_; lean_object* v_d_4493_; lean_object* v_q_4494_; lean_object* v_w_4495_; lean_object* v_W_4496_; lean_object* v_E_4497_; lean_object* v_e_4498_; lean_object* v_c_4499_; lean_object* v_F_4500_; lean_object* v_a_4501_; lean_object* v_b_4502_; lean_object* v_B_4503_; lean_object* v_h_4504_; lean_object* v_K_4505_; lean_object* v_k_4506_; lean_object* v_H_4507_; lean_object* v_m_4508_; lean_object* v_s_4509_; lean_object* v_S_4510_; lean_object* v_A_4511_; lean_object* v_n_4512_; lean_object* v_N_4513_; lean_object* v_V_4514_; lean_object* v_z_4515_; lean_object* v_zabbrev_4516_; lean_object* v_v_4517_; lean_object* v_O_4518_; lean_object* v_X_4519_; lean_object* v_x_4520_; lean_object* v_Z_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4531_; 
v_G_4486_ = lean_ctor_get(v_date_4123_, 0);
v_y_4487_ = lean_ctor_get(v_date_4123_, 1);
v_u_4488_ = lean_ctor_get(v_date_4123_, 2);
v_Y_4489_ = lean_ctor_get(v_date_4123_, 3);
v_D_4490_ = lean_ctor_get(v_date_4123_, 4);
v_M_4491_ = lean_ctor_get(v_date_4123_, 5);
v_L_4492_ = lean_ctor_get(v_date_4123_, 6);
v_d_4493_ = lean_ctor_get(v_date_4123_, 7);
v_q_4494_ = lean_ctor_get(v_date_4123_, 9);
v_w_4495_ = lean_ctor_get(v_date_4123_, 10);
v_W_4496_ = lean_ctor_get(v_date_4123_, 11);
v_E_4497_ = lean_ctor_get(v_date_4123_, 12);
v_e_4498_ = lean_ctor_get(v_date_4123_, 13);
v_c_4499_ = lean_ctor_get(v_date_4123_, 14);
v_F_4500_ = lean_ctor_get(v_date_4123_, 15);
v_a_4501_ = lean_ctor_get(v_date_4123_, 16);
v_b_4502_ = lean_ctor_get(v_date_4123_, 17);
v_B_4503_ = lean_ctor_get(v_date_4123_, 18);
v_h_4504_ = lean_ctor_get(v_date_4123_, 19);
v_K_4505_ = lean_ctor_get(v_date_4123_, 20);
v_k_4506_ = lean_ctor_get(v_date_4123_, 21);
v_H_4507_ = lean_ctor_get(v_date_4123_, 22);
v_m_4508_ = lean_ctor_get(v_date_4123_, 23);
v_s_4509_ = lean_ctor_get(v_date_4123_, 24);
v_S_4510_ = lean_ctor_get(v_date_4123_, 25);
v_A_4511_ = lean_ctor_get(v_date_4123_, 26);
v_n_4512_ = lean_ctor_get(v_date_4123_, 27);
v_N_4513_ = lean_ctor_get(v_date_4123_, 28);
v_V_4514_ = lean_ctor_get(v_date_4123_, 29);
v_z_4515_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_4516_ = lean_ctor_get(v_date_4123_, 31);
v_v_4517_ = lean_ctor_get(v_date_4123_, 32);
v_O_4518_ = lean_ctor_get(v_date_4123_, 33);
v_X_4519_ = lean_ctor_get(v_date_4123_, 34);
v_x_4520_ = lean_ctor_get(v_date_4123_, 35);
v_Z_4521_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_4531_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_4531_ == 0)
{
lean_object* v_unused_4532_; 
v_unused_4532_ = lean_ctor_get(v_date_4123_, 8);
lean_dec(v_unused_4532_);
v___x_4523_ = v_date_4123_;
v_isShared_4524_ = v_isSharedCheck_4531_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_Z_4521_);
lean_inc(v_x_4520_);
lean_inc(v_X_4519_);
lean_inc(v_O_4518_);
lean_inc(v_v_4517_);
lean_inc(v_zabbrev_4516_);
lean_inc(v_z_4515_);
lean_inc(v_V_4514_);
lean_inc(v_N_4513_);
lean_inc(v_n_4512_);
lean_inc(v_A_4511_);
lean_inc(v_S_4510_);
lean_inc(v_s_4509_);
lean_inc(v_m_4508_);
lean_inc(v_H_4507_);
lean_inc(v_k_4506_);
lean_inc(v_K_4505_);
lean_inc(v_h_4504_);
lean_inc(v_B_4503_);
lean_inc(v_b_4502_);
lean_inc(v_a_4501_);
lean_inc(v_F_4500_);
lean_inc(v_c_4499_);
lean_inc(v_e_4498_);
lean_inc(v_E_4497_);
lean_inc(v_W_4496_);
lean_inc(v_w_4495_);
lean_inc(v_q_4494_);
lean_inc(v_d_4493_);
lean_inc(v_L_4492_);
lean_inc(v_M_4491_);
lean_inc(v_D_4490_);
lean_inc(v_Y_4489_);
lean_inc(v_u_4488_);
lean_inc(v_y_4487_);
lean_inc(v_G_4486_);
lean_dec(v_date_4123_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4531_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4526_; 
if (v_isShared_4485_ == 0)
{
lean_ctor_set_tag(v___x_4484_, 1);
lean_ctor_set(v___x_4484_, 0, v_data_4125_);
v___x_4526_ = v___x_4484_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_data_4125_);
v___x_4526_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
lean_object* v___x_4528_; 
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 8, v___x_4526_);
v___x_4528_ = v___x_4523_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_G_4486_);
lean_ctor_set(v_reuseFailAlloc_4529_, 1, v_y_4487_);
lean_ctor_set(v_reuseFailAlloc_4529_, 2, v_u_4488_);
lean_ctor_set(v_reuseFailAlloc_4529_, 3, v_Y_4489_);
lean_ctor_set(v_reuseFailAlloc_4529_, 4, v_D_4490_);
lean_ctor_set(v_reuseFailAlloc_4529_, 5, v_M_4491_);
lean_ctor_set(v_reuseFailAlloc_4529_, 6, v_L_4492_);
lean_ctor_set(v_reuseFailAlloc_4529_, 7, v_d_4493_);
lean_ctor_set(v_reuseFailAlloc_4529_, 8, v___x_4526_);
lean_ctor_set(v_reuseFailAlloc_4529_, 9, v_q_4494_);
lean_ctor_set(v_reuseFailAlloc_4529_, 10, v_w_4495_);
lean_ctor_set(v_reuseFailAlloc_4529_, 11, v_W_4496_);
lean_ctor_set(v_reuseFailAlloc_4529_, 12, v_E_4497_);
lean_ctor_set(v_reuseFailAlloc_4529_, 13, v_e_4498_);
lean_ctor_set(v_reuseFailAlloc_4529_, 14, v_c_4499_);
lean_ctor_set(v_reuseFailAlloc_4529_, 15, v_F_4500_);
lean_ctor_set(v_reuseFailAlloc_4529_, 16, v_a_4501_);
lean_ctor_set(v_reuseFailAlloc_4529_, 17, v_b_4502_);
lean_ctor_set(v_reuseFailAlloc_4529_, 18, v_B_4503_);
lean_ctor_set(v_reuseFailAlloc_4529_, 19, v_h_4504_);
lean_ctor_set(v_reuseFailAlloc_4529_, 20, v_K_4505_);
lean_ctor_set(v_reuseFailAlloc_4529_, 21, v_k_4506_);
lean_ctor_set(v_reuseFailAlloc_4529_, 22, v_H_4507_);
lean_ctor_set(v_reuseFailAlloc_4529_, 23, v_m_4508_);
lean_ctor_set(v_reuseFailAlloc_4529_, 24, v_s_4509_);
lean_ctor_set(v_reuseFailAlloc_4529_, 25, v_S_4510_);
lean_ctor_set(v_reuseFailAlloc_4529_, 26, v_A_4511_);
lean_ctor_set(v_reuseFailAlloc_4529_, 27, v_n_4512_);
lean_ctor_set(v_reuseFailAlloc_4529_, 28, v_N_4513_);
lean_ctor_set(v_reuseFailAlloc_4529_, 29, v_V_4514_);
lean_ctor_set(v_reuseFailAlloc_4529_, 30, v_z_4515_);
lean_ctor_set(v_reuseFailAlloc_4529_, 31, v_zabbrev_4516_);
lean_ctor_set(v_reuseFailAlloc_4529_, 32, v_v_4517_);
lean_ctor_set(v_reuseFailAlloc_4529_, 33, v_O_4518_);
lean_ctor_set(v_reuseFailAlloc_4529_, 34, v_X_4519_);
lean_ctor_set(v_reuseFailAlloc_4529_, 35, v_x_4520_);
lean_ctor_set(v_reuseFailAlloc_4529_, 36, v_Z_4521_);
v___x_4528_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
return v___x_4528_;
}
}
}
}
}
case 8:
{
lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4585_; 
v_isSharedCheck_4585_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_4585_ == 0)
{
lean_object* v_unused_4586_; 
v_unused_4586_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_4586_);
v___x_4536_ = v_modifier_4124_;
v_isShared_4537_ = v_isSharedCheck_4585_;
goto v_resetjp_4535_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4585_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v_G_4538_; lean_object* v_y_4539_; lean_object* v_u_4540_; lean_object* v_Y_4541_; lean_object* v_D_4542_; lean_object* v_M_4543_; lean_object* v_L_4544_; lean_object* v_d_4545_; lean_object* v_Q_4546_; lean_object* v_w_4547_; lean_object* v_W_4548_; lean_object* v_E_4549_; lean_object* v_e_4550_; lean_object* v_c_4551_; lean_object* v_F_4552_; lean_object* v_a_4553_; lean_object* v_b_4554_; lean_object* v_B_4555_; lean_object* v_h_4556_; lean_object* v_K_4557_; lean_object* v_k_4558_; lean_object* v_H_4559_; lean_object* v_m_4560_; lean_object* v_s_4561_; lean_object* v_S_4562_; lean_object* v_A_4563_; lean_object* v_n_4564_; lean_object* v_N_4565_; lean_object* v_V_4566_; lean_object* v_z_4567_; lean_object* v_zabbrev_4568_; lean_object* v_v_4569_; lean_object* v_O_4570_; lean_object* v_X_4571_; lean_object* v_x_4572_; lean_object* v_Z_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4583_; 
v_G_4538_ = lean_ctor_get(v_date_4123_, 0);
v_y_4539_ = lean_ctor_get(v_date_4123_, 1);
v_u_4540_ = lean_ctor_get(v_date_4123_, 2);
v_Y_4541_ = lean_ctor_get(v_date_4123_, 3);
v_D_4542_ = lean_ctor_get(v_date_4123_, 4);
v_M_4543_ = lean_ctor_get(v_date_4123_, 5);
v_L_4544_ = lean_ctor_get(v_date_4123_, 6);
v_d_4545_ = lean_ctor_get(v_date_4123_, 7);
v_Q_4546_ = lean_ctor_get(v_date_4123_, 8);
v_w_4547_ = lean_ctor_get(v_date_4123_, 10);
v_W_4548_ = lean_ctor_get(v_date_4123_, 11);
v_E_4549_ = lean_ctor_get(v_date_4123_, 12);
v_e_4550_ = lean_ctor_get(v_date_4123_, 13);
v_c_4551_ = lean_ctor_get(v_date_4123_, 14);
v_F_4552_ = lean_ctor_get(v_date_4123_, 15);
v_a_4553_ = lean_ctor_get(v_date_4123_, 16);
v_b_4554_ = lean_ctor_get(v_date_4123_, 17);
v_B_4555_ = lean_ctor_get(v_date_4123_, 18);
v_h_4556_ = lean_ctor_get(v_date_4123_, 19);
v_K_4557_ = lean_ctor_get(v_date_4123_, 20);
v_k_4558_ = lean_ctor_get(v_date_4123_, 21);
v_H_4559_ = lean_ctor_get(v_date_4123_, 22);
v_m_4560_ = lean_ctor_get(v_date_4123_, 23);
v_s_4561_ = lean_ctor_get(v_date_4123_, 24);
v_S_4562_ = lean_ctor_get(v_date_4123_, 25);
v_A_4563_ = lean_ctor_get(v_date_4123_, 26);
v_n_4564_ = lean_ctor_get(v_date_4123_, 27);
v_N_4565_ = lean_ctor_get(v_date_4123_, 28);
v_V_4566_ = lean_ctor_get(v_date_4123_, 29);
v_z_4567_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_4568_ = lean_ctor_get(v_date_4123_, 31);
v_v_4569_ = lean_ctor_get(v_date_4123_, 32);
v_O_4570_ = lean_ctor_get(v_date_4123_, 33);
v_X_4571_ = lean_ctor_get(v_date_4123_, 34);
v_x_4572_ = lean_ctor_get(v_date_4123_, 35);
v_Z_4573_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_4583_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_4583_ == 0)
{
lean_object* v_unused_4584_; 
v_unused_4584_ = lean_ctor_get(v_date_4123_, 9);
lean_dec(v_unused_4584_);
v___x_4575_ = v_date_4123_;
v_isShared_4576_ = v_isSharedCheck_4583_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_Z_4573_);
lean_inc(v_x_4572_);
lean_inc(v_X_4571_);
lean_inc(v_O_4570_);
lean_inc(v_v_4569_);
lean_inc(v_zabbrev_4568_);
lean_inc(v_z_4567_);
lean_inc(v_V_4566_);
lean_inc(v_N_4565_);
lean_inc(v_n_4564_);
lean_inc(v_A_4563_);
lean_inc(v_S_4562_);
lean_inc(v_s_4561_);
lean_inc(v_m_4560_);
lean_inc(v_H_4559_);
lean_inc(v_k_4558_);
lean_inc(v_K_4557_);
lean_inc(v_h_4556_);
lean_inc(v_B_4555_);
lean_inc(v_b_4554_);
lean_inc(v_a_4553_);
lean_inc(v_F_4552_);
lean_inc(v_c_4551_);
lean_inc(v_e_4550_);
lean_inc(v_E_4549_);
lean_inc(v_W_4548_);
lean_inc(v_w_4547_);
lean_inc(v_Q_4546_);
lean_inc(v_d_4545_);
lean_inc(v_L_4544_);
lean_inc(v_M_4543_);
lean_inc(v_D_4542_);
lean_inc(v_Y_4541_);
lean_inc(v_u_4540_);
lean_inc(v_y_4539_);
lean_inc(v_G_4538_);
lean_dec(v_date_4123_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4583_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
lean_object* v___x_4578_; 
if (v_isShared_4537_ == 0)
{
lean_ctor_set_tag(v___x_4536_, 1);
lean_ctor_set(v___x_4536_, 0, v_data_4125_);
v___x_4578_ = v___x_4536_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v_data_4125_);
v___x_4578_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
lean_object* v___x_4580_; 
if (v_isShared_4576_ == 0)
{
lean_ctor_set(v___x_4575_, 9, v___x_4578_);
v___x_4580_ = v___x_4575_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_G_4538_);
lean_ctor_set(v_reuseFailAlloc_4581_, 1, v_y_4539_);
lean_ctor_set(v_reuseFailAlloc_4581_, 2, v_u_4540_);
lean_ctor_set(v_reuseFailAlloc_4581_, 3, v_Y_4541_);
lean_ctor_set(v_reuseFailAlloc_4581_, 4, v_D_4542_);
lean_ctor_set(v_reuseFailAlloc_4581_, 5, v_M_4543_);
lean_ctor_set(v_reuseFailAlloc_4581_, 6, v_L_4544_);
lean_ctor_set(v_reuseFailAlloc_4581_, 7, v_d_4545_);
lean_ctor_set(v_reuseFailAlloc_4581_, 8, v_Q_4546_);
lean_ctor_set(v_reuseFailAlloc_4581_, 9, v___x_4578_);
lean_ctor_set(v_reuseFailAlloc_4581_, 10, v_w_4547_);
lean_ctor_set(v_reuseFailAlloc_4581_, 11, v_W_4548_);
lean_ctor_set(v_reuseFailAlloc_4581_, 12, v_E_4549_);
lean_ctor_set(v_reuseFailAlloc_4581_, 13, v_e_4550_);
lean_ctor_set(v_reuseFailAlloc_4581_, 14, v_c_4551_);
lean_ctor_set(v_reuseFailAlloc_4581_, 15, v_F_4552_);
lean_ctor_set(v_reuseFailAlloc_4581_, 16, v_a_4553_);
lean_ctor_set(v_reuseFailAlloc_4581_, 17, v_b_4554_);
lean_ctor_set(v_reuseFailAlloc_4581_, 18, v_B_4555_);
lean_ctor_set(v_reuseFailAlloc_4581_, 19, v_h_4556_);
lean_ctor_set(v_reuseFailAlloc_4581_, 20, v_K_4557_);
lean_ctor_set(v_reuseFailAlloc_4581_, 21, v_k_4558_);
lean_ctor_set(v_reuseFailAlloc_4581_, 22, v_H_4559_);
lean_ctor_set(v_reuseFailAlloc_4581_, 23, v_m_4560_);
lean_ctor_set(v_reuseFailAlloc_4581_, 24, v_s_4561_);
lean_ctor_set(v_reuseFailAlloc_4581_, 25, v_S_4562_);
lean_ctor_set(v_reuseFailAlloc_4581_, 26, v_A_4563_);
lean_ctor_set(v_reuseFailAlloc_4581_, 27, v_n_4564_);
lean_ctor_set(v_reuseFailAlloc_4581_, 28, v_N_4565_);
lean_ctor_set(v_reuseFailAlloc_4581_, 29, v_V_4566_);
lean_ctor_set(v_reuseFailAlloc_4581_, 30, v_z_4567_);
lean_ctor_set(v_reuseFailAlloc_4581_, 31, v_zabbrev_4568_);
lean_ctor_set(v_reuseFailAlloc_4581_, 32, v_v_4569_);
lean_ctor_set(v_reuseFailAlloc_4581_, 33, v_O_4570_);
lean_ctor_set(v_reuseFailAlloc_4581_, 34, v_X_4571_);
lean_ctor_set(v_reuseFailAlloc_4581_, 35, v_x_4572_);
lean_ctor_set(v_reuseFailAlloc_4581_, 36, v_Z_4573_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
}
}
}
}
}
case 9:
{
lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4637_; 
v_isSharedCheck_4637_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_4637_ == 0)
{
lean_object* v_unused_4638_; 
v_unused_4638_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_4638_);
v___x_4588_ = v_modifier_4124_;
v_isShared_4589_ = v_isSharedCheck_4637_;
goto v_resetjp_4587_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4637_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v_G_4590_; lean_object* v_y_4591_; lean_object* v_u_4592_; lean_object* v_D_4593_; lean_object* v_M_4594_; lean_object* v_L_4595_; lean_object* v_d_4596_; lean_object* v_Q_4597_; lean_object* v_q_4598_; lean_object* v_w_4599_; lean_object* v_W_4600_; lean_object* v_E_4601_; lean_object* v_e_4602_; lean_object* v_c_4603_; lean_object* v_F_4604_; lean_object* v_a_4605_; lean_object* v_b_4606_; lean_object* v_B_4607_; lean_object* v_h_4608_; lean_object* v_K_4609_; lean_object* v_k_4610_; lean_object* v_H_4611_; lean_object* v_m_4612_; lean_object* v_s_4613_; lean_object* v_S_4614_; lean_object* v_A_4615_; lean_object* v_n_4616_; lean_object* v_N_4617_; lean_object* v_V_4618_; lean_object* v_z_4619_; lean_object* v_zabbrev_4620_; lean_object* v_v_4621_; lean_object* v_O_4622_; lean_object* v_X_4623_; lean_object* v_x_4624_; lean_object* v_Z_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4635_; 
v_G_4590_ = lean_ctor_get(v_date_4123_, 0);
v_y_4591_ = lean_ctor_get(v_date_4123_, 1);
v_u_4592_ = lean_ctor_get(v_date_4123_, 2);
v_D_4593_ = lean_ctor_get(v_date_4123_, 4);
v_M_4594_ = lean_ctor_get(v_date_4123_, 5);
v_L_4595_ = lean_ctor_get(v_date_4123_, 6);
v_d_4596_ = lean_ctor_get(v_date_4123_, 7);
v_Q_4597_ = lean_ctor_get(v_date_4123_, 8);
v_q_4598_ = lean_ctor_get(v_date_4123_, 9);
v_w_4599_ = lean_ctor_get(v_date_4123_, 10);
v_W_4600_ = lean_ctor_get(v_date_4123_, 11);
v_E_4601_ = lean_ctor_get(v_date_4123_, 12);
v_e_4602_ = lean_ctor_get(v_date_4123_, 13);
v_c_4603_ = lean_ctor_get(v_date_4123_, 14);
v_F_4604_ = lean_ctor_get(v_date_4123_, 15);
v_a_4605_ = lean_ctor_get(v_date_4123_, 16);
v_b_4606_ = lean_ctor_get(v_date_4123_, 17);
v_B_4607_ = lean_ctor_get(v_date_4123_, 18);
v_h_4608_ = lean_ctor_get(v_date_4123_, 19);
v_K_4609_ = lean_ctor_get(v_date_4123_, 20);
v_k_4610_ = lean_ctor_get(v_date_4123_, 21);
v_H_4611_ = lean_ctor_get(v_date_4123_, 22);
v_m_4612_ = lean_ctor_get(v_date_4123_, 23);
v_s_4613_ = lean_ctor_get(v_date_4123_, 24);
v_S_4614_ = lean_ctor_get(v_date_4123_, 25);
v_A_4615_ = lean_ctor_get(v_date_4123_, 26);
v_n_4616_ = lean_ctor_get(v_date_4123_, 27);
v_N_4617_ = lean_ctor_get(v_date_4123_, 28);
v_V_4618_ = lean_ctor_get(v_date_4123_, 29);
v_z_4619_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_4620_ = lean_ctor_get(v_date_4123_, 31);
v_v_4621_ = lean_ctor_get(v_date_4123_, 32);
v_O_4622_ = lean_ctor_get(v_date_4123_, 33);
v_X_4623_ = lean_ctor_get(v_date_4123_, 34);
v_x_4624_ = lean_ctor_get(v_date_4123_, 35);
v_Z_4625_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_4635_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_4635_ == 0)
{
lean_object* v_unused_4636_; 
v_unused_4636_ = lean_ctor_get(v_date_4123_, 3);
lean_dec(v_unused_4636_);
v___x_4627_ = v_date_4123_;
v_isShared_4628_ = v_isSharedCheck_4635_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_Z_4625_);
lean_inc(v_x_4624_);
lean_inc(v_X_4623_);
lean_inc(v_O_4622_);
lean_inc(v_v_4621_);
lean_inc(v_zabbrev_4620_);
lean_inc(v_z_4619_);
lean_inc(v_V_4618_);
lean_inc(v_N_4617_);
lean_inc(v_n_4616_);
lean_inc(v_A_4615_);
lean_inc(v_S_4614_);
lean_inc(v_s_4613_);
lean_inc(v_m_4612_);
lean_inc(v_H_4611_);
lean_inc(v_k_4610_);
lean_inc(v_K_4609_);
lean_inc(v_h_4608_);
lean_inc(v_B_4607_);
lean_inc(v_b_4606_);
lean_inc(v_a_4605_);
lean_inc(v_F_4604_);
lean_inc(v_c_4603_);
lean_inc(v_e_4602_);
lean_inc(v_E_4601_);
lean_inc(v_W_4600_);
lean_inc(v_w_4599_);
lean_inc(v_q_4598_);
lean_inc(v_Q_4597_);
lean_inc(v_d_4596_);
lean_inc(v_L_4595_);
lean_inc(v_M_4594_);
lean_inc(v_D_4593_);
lean_inc(v_u_4592_);
lean_inc(v_y_4591_);
lean_inc(v_G_4590_);
lean_dec(v_date_4123_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4635_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4630_; 
if (v_isShared_4589_ == 0)
{
lean_ctor_set_tag(v___x_4588_, 1);
lean_ctor_set(v___x_4588_, 0, v_data_4125_);
v___x_4630_ = v___x_4588_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_data_4125_);
v___x_4630_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
lean_object* v___x_4632_; 
if (v_isShared_4628_ == 0)
{
lean_ctor_set(v___x_4627_, 3, v___x_4630_);
v___x_4632_ = v___x_4627_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_G_4590_);
lean_ctor_set(v_reuseFailAlloc_4633_, 1, v_y_4591_);
lean_ctor_set(v_reuseFailAlloc_4633_, 2, v_u_4592_);
lean_ctor_set(v_reuseFailAlloc_4633_, 3, v___x_4630_);
lean_ctor_set(v_reuseFailAlloc_4633_, 4, v_D_4593_);
lean_ctor_set(v_reuseFailAlloc_4633_, 5, v_M_4594_);
lean_ctor_set(v_reuseFailAlloc_4633_, 6, v_L_4595_);
lean_ctor_set(v_reuseFailAlloc_4633_, 7, v_d_4596_);
lean_ctor_set(v_reuseFailAlloc_4633_, 8, v_Q_4597_);
lean_ctor_set(v_reuseFailAlloc_4633_, 9, v_q_4598_);
lean_ctor_set(v_reuseFailAlloc_4633_, 10, v_w_4599_);
lean_ctor_set(v_reuseFailAlloc_4633_, 11, v_W_4600_);
lean_ctor_set(v_reuseFailAlloc_4633_, 12, v_E_4601_);
lean_ctor_set(v_reuseFailAlloc_4633_, 13, v_e_4602_);
lean_ctor_set(v_reuseFailAlloc_4633_, 14, v_c_4603_);
lean_ctor_set(v_reuseFailAlloc_4633_, 15, v_F_4604_);
lean_ctor_set(v_reuseFailAlloc_4633_, 16, v_a_4605_);
lean_ctor_set(v_reuseFailAlloc_4633_, 17, v_b_4606_);
lean_ctor_set(v_reuseFailAlloc_4633_, 18, v_B_4607_);
lean_ctor_set(v_reuseFailAlloc_4633_, 19, v_h_4608_);
lean_ctor_set(v_reuseFailAlloc_4633_, 20, v_K_4609_);
lean_ctor_set(v_reuseFailAlloc_4633_, 21, v_k_4610_);
lean_ctor_set(v_reuseFailAlloc_4633_, 22, v_H_4611_);
lean_ctor_set(v_reuseFailAlloc_4633_, 23, v_m_4612_);
lean_ctor_set(v_reuseFailAlloc_4633_, 24, v_s_4613_);
lean_ctor_set(v_reuseFailAlloc_4633_, 25, v_S_4614_);
lean_ctor_set(v_reuseFailAlloc_4633_, 26, v_A_4615_);
lean_ctor_set(v_reuseFailAlloc_4633_, 27, v_n_4616_);
lean_ctor_set(v_reuseFailAlloc_4633_, 28, v_N_4617_);
lean_ctor_set(v_reuseFailAlloc_4633_, 29, v_V_4618_);
lean_ctor_set(v_reuseFailAlloc_4633_, 30, v_z_4619_);
lean_ctor_set(v_reuseFailAlloc_4633_, 31, v_zabbrev_4620_);
lean_ctor_set(v_reuseFailAlloc_4633_, 32, v_v_4621_);
lean_ctor_set(v_reuseFailAlloc_4633_, 33, v_O_4622_);
lean_ctor_set(v_reuseFailAlloc_4633_, 34, v_X_4623_);
lean_ctor_set(v_reuseFailAlloc_4633_, 35, v_x_4624_);
lean_ctor_set(v_reuseFailAlloc_4633_, 36, v_Z_4625_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
}
}
}
case 10:
{
lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4689_; 
v_isSharedCheck_4689_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_4689_ == 0)
{
lean_object* v_unused_4690_; 
v_unused_4690_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_4690_);
v___x_4640_ = v_modifier_4124_;
v_isShared_4641_ = v_isSharedCheck_4689_;
goto v_resetjp_4639_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4689_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v_G_4642_; lean_object* v_y_4643_; lean_object* v_u_4644_; lean_object* v_Y_4645_; lean_object* v_D_4646_; lean_object* v_M_4647_; lean_object* v_L_4648_; lean_object* v_d_4649_; lean_object* v_Q_4650_; lean_object* v_q_4651_; lean_object* v_W_4652_; lean_object* v_E_4653_; lean_object* v_e_4654_; lean_object* v_c_4655_; lean_object* v_F_4656_; lean_object* v_a_4657_; lean_object* v_b_4658_; lean_object* v_B_4659_; lean_object* v_h_4660_; lean_object* v_K_4661_; lean_object* v_k_4662_; lean_object* v_H_4663_; lean_object* v_m_4664_; lean_object* v_s_4665_; lean_object* v_S_4666_; lean_object* v_A_4667_; lean_object* v_n_4668_; lean_object* v_N_4669_; lean_object* v_V_4670_; lean_object* v_z_4671_; lean_object* v_zabbrev_4672_; lean_object* v_v_4673_; lean_object* v_O_4674_; lean_object* v_X_4675_; lean_object* v_x_4676_; lean_object* v_Z_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4687_; 
v_G_4642_ = lean_ctor_get(v_date_4123_, 0);
v_y_4643_ = lean_ctor_get(v_date_4123_, 1);
v_u_4644_ = lean_ctor_get(v_date_4123_, 2);
v_Y_4645_ = lean_ctor_get(v_date_4123_, 3);
v_D_4646_ = lean_ctor_get(v_date_4123_, 4);
v_M_4647_ = lean_ctor_get(v_date_4123_, 5);
v_L_4648_ = lean_ctor_get(v_date_4123_, 6);
v_d_4649_ = lean_ctor_get(v_date_4123_, 7);
v_Q_4650_ = lean_ctor_get(v_date_4123_, 8);
v_q_4651_ = lean_ctor_get(v_date_4123_, 9);
v_W_4652_ = lean_ctor_get(v_date_4123_, 11);
v_E_4653_ = lean_ctor_get(v_date_4123_, 12);
v_e_4654_ = lean_ctor_get(v_date_4123_, 13);
v_c_4655_ = lean_ctor_get(v_date_4123_, 14);
v_F_4656_ = lean_ctor_get(v_date_4123_, 15);
v_a_4657_ = lean_ctor_get(v_date_4123_, 16);
v_b_4658_ = lean_ctor_get(v_date_4123_, 17);
v_B_4659_ = lean_ctor_get(v_date_4123_, 18);
v_h_4660_ = lean_ctor_get(v_date_4123_, 19);
v_K_4661_ = lean_ctor_get(v_date_4123_, 20);
v_k_4662_ = lean_ctor_get(v_date_4123_, 21);
v_H_4663_ = lean_ctor_get(v_date_4123_, 22);
v_m_4664_ = lean_ctor_get(v_date_4123_, 23);
v_s_4665_ = lean_ctor_get(v_date_4123_, 24);
v_S_4666_ = lean_ctor_get(v_date_4123_, 25);
v_A_4667_ = lean_ctor_get(v_date_4123_, 26);
v_n_4668_ = lean_ctor_get(v_date_4123_, 27);
v_N_4669_ = lean_ctor_get(v_date_4123_, 28);
v_V_4670_ = lean_ctor_get(v_date_4123_, 29);
v_z_4671_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_4672_ = lean_ctor_get(v_date_4123_, 31);
v_v_4673_ = lean_ctor_get(v_date_4123_, 32);
v_O_4674_ = lean_ctor_get(v_date_4123_, 33);
v_X_4675_ = lean_ctor_get(v_date_4123_, 34);
v_x_4676_ = lean_ctor_get(v_date_4123_, 35);
v_Z_4677_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_4687_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_4687_ == 0)
{
lean_object* v_unused_4688_; 
v_unused_4688_ = lean_ctor_get(v_date_4123_, 10);
lean_dec(v_unused_4688_);
v___x_4679_ = v_date_4123_;
v_isShared_4680_ = v_isSharedCheck_4687_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_Z_4677_);
lean_inc(v_x_4676_);
lean_inc(v_X_4675_);
lean_inc(v_O_4674_);
lean_inc(v_v_4673_);
lean_inc(v_zabbrev_4672_);
lean_inc(v_z_4671_);
lean_inc(v_V_4670_);
lean_inc(v_N_4669_);
lean_inc(v_n_4668_);
lean_inc(v_A_4667_);
lean_inc(v_S_4666_);
lean_inc(v_s_4665_);
lean_inc(v_m_4664_);
lean_inc(v_H_4663_);
lean_inc(v_k_4662_);
lean_inc(v_K_4661_);
lean_inc(v_h_4660_);
lean_inc(v_B_4659_);
lean_inc(v_b_4658_);
lean_inc(v_a_4657_);
lean_inc(v_F_4656_);
lean_inc(v_c_4655_);
lean_inc(v_e_4654_);
lean_inc(v_E_4653_);
lean_inc(v_W_4652_);
lean_inc(v_q_4651_);
lean_inc(v_Q_4650_);
lean_inc(v_d_4649_);
lean_inc(v_L_4648_);
lean_inc(v_M_4647_);
lean_inc(v_D_4646_);
lean_inc(v_Y_4645_);
lean_inc(v_u_4644_);
lean_inc(v_y_4643_);
lean_inc(v_G_4642_);
lean_dec(v_date_4123_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4687_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4682_; 
if (v_isShared_4641_ == 0)
{
lean_ctor_set_tag(v___x_4640_, 1);
lean_ctor_set(v___x_4640_, 0, v_data_4125_);
v___x_4682_ = v___x_4640_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v_data_4125_);
v___x_4682_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
lean_object* v___x_4684_; 
if (v_isShared_4680_ == 0)
{
lean_ctor_set(v___x_4679_, 10, v___x_4682_);
v___x_4684_ = v___x_4679_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_G_4642_);
lean_ctor_set(v_reuseFailAlloc_4685_, 1, v_y_4643_);
lean_ctor_set(v_reuseFailAlloc_4685_, 2, v_u_4644_);
lean_ctor_set(v_reuseFailAlloc_4685_, 3, v_Y_4645_);
lean_ctor_set(v_reuseFailAlloc_4685_, 4, v_D_4646_);
lean_ctor_set(v_reuseFailAlloc_4685_, 5, v_M_4647_);
lean_ctor_set(v_reuseFailAlloc_4685_, 6, v_L_4648_);
lean_ctor_set(v_reuseFailAlloc_4685_, 7, v_d_4649_);
lean_ctor_set(v_reuseFailAlloc_4685_, 8, v_Q_4650_);
lean_ctor_set(v_reuseFailAlloc_4685_, 9, v_q_4651_);
lean_ctor_set(v_reuseFailAlloc_4685_, 10, v___x_4682_);
lean_ctor_set(v_reuseFailAlloc_4685_, 11, v_W_4652_);
lean_ctor_set(v_reuseFailAlloc_4685_, 12, v_E_4653_);
lean_ctor_set(v_reuseFailAlloc_4685_, 13, v_e_4654_);
lean_ctor_set(v_reuseFailAlloc_4685_, 14, v_c_4655_);
lean_ctor_set(v_reuseFailAlloc_4685_, 15, v_F_4656_);
lean_ctor_set(v_reuseFailAlloc_4685_, 16, v_a_4657_);
lean_ctor_set(v_reuseFailAlloc_4685_, 17, v_b_4658_);
lean_ctor_set(v_reuseFailAlloc_4685_, 18, v_B_4659_);
lean_ctor_set(v_reuseFailAlloc_4685_, 19, v_h_4660_);
lean_ctor_set(v_reuseFailAlloc_4685_, 20, v_K_4661_);
lean_ctor_set(v_reuseFailAlloc_4685_, 21, v_k_4662_);
lean_ctor_set(v_reuseFailAlloc_4685_, 22, v_H_4663_);
lean_ctor_set(v_reuseFailAlloc_4685_, 23, v_m_4664_);
lean_ctor_set(v_reuseFailAlloc_4685_, 24, v_s_4665_);
lean_ctor_set(v_reuseFailAlloc_4685_, 25, v_S_4666_);
lean_ctor_set(v_reuseFailAlloc_4685_, 26, v_A_4667_);
lean_ctor_set(v_reuseFailAlloc_4685_, 27, v_n_4668_);
lean_ctor_set(v_reuseFailAlloc_4685_, 28, v_N_4669_);
lean_ctor_set(v_reuseFailAlloc_4685_, 29, v_V_4670_);
lean_ctor_set(v_reuseFailAlloc_4685_, 30, v_z_4671_);
lean_ctor_set(v_reuseFailAlloc_4685_, 31, v_zabbrev_4672_);
lean_ctor_set(v_reuseFailAlloc_4685_, 32, v_v_4673_);
lean_ctor_set(v_reuseFailAlloc_4685_, 33, v_O_4674_);
lean_ctor_set(v_reuseFailAlloc_4685_, 34, v_X_4675_);
lean_ctor_set(v_reuseFailAlloc_4685_, 35, v_x_4676_);
lean_ctor_set(v_reuseFailAlloc_4685_, 36, v_Z_4677_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
}
}
case 11:
{
lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4741_; 
v_isSharedCheck_4741_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_4741_ == 0)
{
lean_object* v_unused_4742_; 
v_unused_4742_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_4742_);
v___x_4692_ = v_modifier_4124_;
v_isShared_4693_ = v_isSharedCheck_4741_;
goto v_resetjp_4691_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4741_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v_G_4694_; lean_object* v_y_4695_; lean_object* v_u_4696_; lean_object* v_Y_4697_; lean_object* v_D_4698_; lean_object* v_M_4699_; lean_object* v_L_4700_; lean_object* v_d_4701_; lean_object* v_Q_4702_; lean_object* v_q_4703_; lean_object* v_w_4704_; lean_object* v_E_4705_; lean_object* v_e_4706_; lean_object* v_c_4707_; lean_object* v_F_4708_; lean_object* v_a_4709_; lean_object* v_b_4710_; lean_object* v_B_4711_; lean_object* v_h_4712_; lean_object* v_K_4713_; lean_object* v_k_4714_; lean_object* v_H_4715_; lean_object* v_m_4716_; lean_object* v_s_4717_; lean_object* v_S_4718_; lean_object* v_A_4719_; lean_object* v_n_4720_; lean_object* v_N_4721_; lean_object* v_V_4722_; lean_object* v_z_4723_; lean_object* v_zabbrev_4724_; lean_object* v_v_4725_; lean_object* v_O_4726_; lean_object* v_X_4727_; lean_object* v_x_4728_; lean_object* v_Z_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4739_; 
v_G_4694_ = lean_ctor_get(v_date_4123_, 0);
v_y_4695_ = lean_ctor_get(v_date_4123_, 1);
v_u_4696_ = lean_ctor_get(v_date_4123_, 2);
v_Y_4697_ = lean_ctor_get(v_date_4123_, 3);
v_D_4698_ = lean_ctor_get(v_date_4123_, 4);
v_M_4699_ = lean_ctor_get(v_date_4123_, 5);
v_L_4700_ = lean_ctor_get(v_date_4123_, 6);
v_d_4701_ = lean_ctor_get(v_date_4123_, 7);
v_Q_4702_ = lean_ctor_get(v_date_4123_, 8);
v_q_4703_ = lean_ctor_get(v_date_4123_, 9);
v_w_4704_ = lean_ctor_get(v_date_4123_, 10);
v_E_4705_ = lean_ctor_get(v_date_4123_, 12);
v_e_4706_ = lean_ctor_get(v_date_4123_, 13);
v_c_4707_ = lean_ctor_get(v_date_4123_, 14);
v_F_4708_ = lean_ctor_get(v_date_4123_, 15);
v_a_4709_ = lean_ctor_get(v_date_4123_, 16);
v_b_4710_ = lean_ctor_get(v_date_4123_, 17);
v_B_4711_ = lean_ctor_get(v_date_4123_, 18);
v_h_4712_ = lean_ctor_get(v_date_4123_, 19);
v_K_4713_ = lean_ctor_get(v_date_4123_, 20);
v_k_4714_ = lean_ctor_get(v_date_4123_, 21);
v_H_4715_ = lean_ctor_get(v_date_4123_, 22);
v_m_4716_ = lean_ctor_get(v_date_4123_, 23);
v_s_4717_ = lean_ctor_get(v_date_4123_, 24);
v_S_4718_ = lean_ctor_get(v_date_4123_, 25);
v_A_4719_ = lean_ctor_get(v_date_4123_, 26);
v_n_4720_ = lean_ctor_get(v_date_4123_, 27);
v_N_4721_ = lean_ctor_get(v_date_4123_, 28);
v_V_4722_ = lean_ctor_get(v_date_4123_, 29);
v_z_4723_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_4724_ = lean_ctor_get(v_date_4123_, 31);
v_v_4725_ = lean_ctor_get(v_date_4123_, 32);
v_O_4726_ = lean_ctor_get(v_date_4123_, 33);
v_X_4727_ = lean_ctor_get(v_date_4123_, 34);
v_x_4728_ = lean_ctor_get(v_date_4123_, 35);
v_Z_4729_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_4739_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_4739_ == 0)
{
lean_object* v_unused_4740_; 
v_unused_4740_ = lean_ctor_get(v_date_4123_, 11);
lean_dec(v_unused_4740_);
v___x_4731_ = v_date_4123_;
v_isShared_4732_ = v_isSharedCheck_4739_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_Z_4729_);
lean_inc(v_x_4728_);
lean_inc(v_X_4727_);
lean_inc(v_O_4726_);
lean_inc(v_v_4725_);
lean_inc(v_zabbrev_4724_);
lean_inc(v_z_4723_);
lean_inc(v_V_4722_);
lean_inc(v_N_4721_);
lean_inc(v_n_4720_);
lean_inc(v_A_4719_);
lean_inc(v_S_4718_);
lean_inc(v_s_4717_);
lean_inc(v_m_4716_);
lean_inc(v_H_4715_);
lean_inc(v_k_4714_);
lean_inc(v_K_4713_);
lean_inc(v_h_4712_);
lean_inc(v_B_4711_);
lean_inc(v_b_4710_);
lean_inc(v_a_4709_);
lean_inc(v_F_4708_);
lean_inc(v_c_4707_);
lean_inc(v_e_4706_);
lean_inc(v_E_4705_);
lean_inc(v_w_4704_);
lean_inc(v_q_4703_);
lean_inc(v_Q_4702_);
lean_inc(v_d_4701_);
lean_inc(v_L_4700_);
lean_inc(v_M_4699_);
lean_inc(v_D_4698_);
lean_inc(v_Y_4697_);
lean_inc(v_u_4696_);
lean_inc(v_y_4695_);
lean_inc(v_G_4694_);
lean_dec(v_date_4123_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4739_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4734_; 
if (v_isShared_4693_ == 0)
{
lean_ctor_set_tag(v___x_4692_, 1);
lean_ctor_set(v___x_4692_, 0, v_data_4125_);
v___x_4734_ = v___x_4692_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v_data_4125_);
v___x_4734_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
lean_object* v___x_4736_; 
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 11, v___x_4734_);
v___x_4736_ = v___x_4731_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_G_4694_);
lean_ctor_set(v_reuseFailAlloc_4737_, 1, v_y_4695_);
lean_ctor_set(v_reuseFailAlloc_4737_, 2, v_u_4696_);
lean_ctor_set(v_reuseFailAlloc_4737_, 3, v_Y_4697_);
lean_ctor_set(v_reuseFailAlloc_4737_, 4, v_D_4698_);
lean_ctor_set(v_reuseFailAlloc_4737_, 5, v_M_4699_);
lean_ctor_set(v_reuseFailAlloc_4737_, 6, v_L_4700_);
lean_ctor_set(v_reuseFailAlloc_4737_, 7, v_d_4701_);
lean_ctor_set(v_reuseFailAlloc_4737_, 8, v_Q_4702_);
lean_ctor_set(v_reuseFailAlloc_4737_, 9, v_q_4703_);
lean_ctor_set(v_reuseFailAlloc_4737_, 10, v_w_4704_);
lean_ctor_set(v_reuseFailAlloc_4737_, 11, v___x_4734_);
lean_ctor_set(v_reuseFailAlloc_4737_, 12, v_E_4705_);
lean_ctor_set(v_reuseFailAlloc_4737_, 13, v_e_4706_);
lean_ctor_set(v_reuseFailAlloc_4737_, 14, v_c_4707_);
lean_ctor_set(v_reuseFailAlloc_4737_, 15, v_F_4708_);
lean_ctor_set(v_reuseFailAlloc_4737_, 16, v_a_4709_);
lean_ctor_set(v_reuseFailAlloc_4737_, 17, v_b_4710_);
lean_ctor_set(v_reuseFailAlloc_4737_, 18, v_B_4711_);
lean_ctor_set(v_reuseFailAlloc_4737_, 19, v_h_4712_);
lean_ctor_set(v_reuseFailAlloc_4737_, 20, v_K_4713_);
lean_ctor_set(v_reuseFailAlloc_4737_, 21, v_k_4714_);
lean_ctor_set(v_reuseFailAlloc_4737_, 22, v_H_4715_);
lean_ctor_set(v_reuseFailAlloc_4737_, 23, v_m_4716_);
lean_ctor_set(v_reuseFailAlloc_4737_, 24, v_s_4717_);
lean_ctor_set(v_reuseFailAlloc_4737_, 25, v_S_4718_);
lean_ctor_set(v_reuseFailAlloc_4737_, 26, v_A_4719_);
lean_ctor_set(v_reuseFailAlloc_4737_, 27, v_n_4720_);
lean_ctor_set(v_reuseFailAlloc_4737_, 28, v_N_4721_);
lean_ctor_set(v_reuseFailAlloc_4737_, 29, v_V_4722_);
lean_ctor_set(v_reuseFailAlloc_4737_, 30, v_z_4723_);
lean_ctor_set(v_reuseFailAlloc_4737_, 31, v_zabbrev_4724_);
lean_ctor_set(v_reuseFailAlloc_4737_, 32, v_v_4725_);
lean_ctor_set(v_reuseFailAlloc_4737_, 33, v_O_4726_);
lean_ctor_set(v_reuseFailAlloc_4737_, 34, v_X_4727_);
lean_ctor_set(v_reuseFailAlloc_4737_, 35, v_x_4728_);
lean_ctor_set(v_reuseFailAlloc_4737_, 36, v_Z_4729_);
v___x_4736_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
return v___x_4736_;
}
}
}
}
}
case 12:
{
lean_object* v_G_4743_; lean_object* v_y_4744_; lean_object* v_u_4745_; lean_object* v_Y_4746_; lean_object* v_D_4747_; lean_object* v_M_4748_; lean_object* v_L_4749_; lean_object* v_d_4750_; lean_object* v_Q_4751_; lean_object* v_q_4752_; lean_object* v_w_4753_; lean_object* v_W_4754_; lean_object* v_e_4755_; lean_object* v_c_4756_; lean_object* v_F_4757_; lean_object* v_a_4758_; lean_object* v_b_4759_; lean_object* v_B_4760_; lean_object* v_h_4761_; lean_object* v_K_4762_; lean_object* v_k_4763_; lean_object* v_H_4764_; lean_object* v_m_4765_; lean_object* v_s_4766_; lean_object* v_S_4767_; lean_object* v_A_4768_; lean_object* v_n_4769_; lean_object* v_N_4770_; lean_object* v_V_4771_; lean_object* v_z_4772_; lean_object* v_zabbrev_4773_; lean_object* v_v_4774_; lean_object* v_O_4775_; lean_object* v_X_4776_; lean_object* v_x_4777_; lean_object* v_Z_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4786_; 
lean_dec_ref_known(v_modifier_4124_, 0);
v_G_4743_ = lean_ctor_get(v_date_4123_, 0);
v_y_4744_ = lean_ctor_get(v_date_4123_, 1);
v_u_4745_ = lean_ctor_get(v_date_4123_, 2);
v_Y_4746_ = lean_ctor_get(v_date_4123_, 3);
v_D_4747_ = lean_ctor_get(v_date_4123_, 4);
v_M_4748_ = lean_ctor_get(v_date_4123_, 5);
v_L_4749_ = lean_ctor_get(v_date_4123_, 6);
v_d_4750_ = lean_ctor_get(v_date_4123_, 7);
v_Q_4751_ = lean_ctor_get(v_date_4123_, 8);
v_q_4752_ = lean_ctor_get(v_date_4123_, 9);
v_w_4753_ = lean_ctor_get(v_date_4123_, 10);
v_W_4754_ = lean_ctor_get(v_date_4123_, 11);
v_e_4755_ = lean_ctor_get(v_date_4123_, 13);
v_c_4756_ = lean_ctor_get(v_date_4123_, 14);
v_F_4757_ = lean_ctor_get(v_date_4123_, 15);
v_a_4758_ = lean_ctor_get(v_date_4123_, 16);
v_b_4759_ = lean_ctor_get(v_date_4123_, 17);
v_B_4760_ = lean_ctor_get(v_date_4123_, 18);
v_h_4761_ = lean_ctor_get(v_date_4123_, 19);
v_K_4762_ = lean_ctor_get(v_date_4123_, 20);
v_k_4763_ = lean_ctor_get(v_date_4123_, 21);
v_H_4764_ = lean_ctor_get(v_date_4123_, 22);
v_m_4765_ = lean_ctor_get(v_date_4123_, 23);
v_s_4766_ = lean_ctor_get(v_date_4123_, 24);
v_S_4767_ = lean_ctor_get(v_date_4123_, 25);
v_A_4768_ = lean_ctor_get(v_date_4123_, 26);
v_n_4769_ = lean_ctor_get(v_date_4123_, 27);
v_N_4770_ = lean_ctor_get(v_date_4123_, 28);
v_V_4771_ = lean_ctor_get(v_date_4123_, 29);
v_z_4772_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_4773_ = lean_ctor_get(v_date_4123_, 31);
v_v_4774_ = lean_ctor_get(v_date_4123_, 32);
v_O_4775_ = lean_ctor_get(v_date_4123_, 33);
v_X_4776_ = lean_ctor_get(v_date_4123_, 34);
v_x_4777_ = lean_ctor_get(v_date_4123_, 35);
v_Z_4778_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_4786_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_4786_ == 0)
{
lean_object* v_unused_4787_; 
v_unused_4787_ = lean_ctor_get(v_date_4123_, 12);
lean_dec(v_unused_4787_);
v___x_4780_ = v_date_4123_;
v_isShared_4781_ = v_isSharedCheck_4786_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_Z_4778_);
lean_inc(v_x_4777_);
lean_inc(v_X_4776_);
lean_inc(v_O_4775_);
lean_inc(v_v_4774_);
lean_inc(v_zabbrev_4773_);
lean_inc(v_z_4772_);
lean_inc(v_V_4771_);
lean_inc(v_N_4770_);
lean_inc(v_n_4769_);
lean_inc(v_A_4768_);
lean_inc(v_S_4767_);
lean_inc(v_s_4766_);
lean_inc(v_m_4765_);
lean_inc(v_H_4764_);
lean_inc(v_k_4763_);
lean_inc(v_K_4762_);
lean_inc(v_h_4761_);
lean_inc(v_B_4760_);
lean_inc(v_b_4759_);
lean_inc(v_a_4758_);
lean_inc(v_F_4757_);
lean_inc(v_c_4756_);
lean_inc(v_e_4755_);
lean_inc(v_W_4754_);
lean_inc(v_w_4753_);
lean_inc(v_q_4752_);
lean_inc(v_Q_4751_);
lean_inc(v_d_4750_);
lean_inc(v_L_4749_);
lean_inc(v_M_4748_);
lean_inc(v_D_4747_);
lean_inc(v_Y_4746_);
lean_inc(v_u_4745_);
lean_inc(v_y_4744_);
lean_inc(v_G_4743_);
lean_dec(v_date_4123_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4786_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v___x_4782_; lean_object* v___x_4784_; 
v___x_4782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4782_, 0, v_data_4125_);
if (v_isShared_4781_ == 0)
{
lean_ctor_set(v___x_4780_, 12, v___x_4782_);
v___x_4784_ = v___x_4780_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_G_4743_);
lean_ctor_set(v_reuseFailAlloc_4785_, 1, v_y_4744_);
lean_ctor_set(v_reuseFailAlloc_4785_, 2, v_u_4745_);
lean_ctor_set(v_reuseFailAlloc_4785_, 3, v_Y_4746_);
lean_ctor_set(v_reuseFailAlloc_4785_, 4, v_D_4747_);
lean_ctor_set(v_reuseFailAlloc_4785_, 5, v_M_4748_);
lean_ctor_set(v_reuseFailAlloc_4785_, 6, v_L_4749_);
lean_ctor_set(v_reuseFailAlloc_4785_, 7, v_d_4750_);
lean_ctor_set(v_reuseFailAlloc_4785_, 8, v_Q_4751_);
lean_ctor_set(v_reuseFailAlloc_4785_, 9, v_q_4752_);
lean_ctor_set(v_reuseFailAlloc_4785_, 10, v_w_4753_);
lean_ctor_set(v_reuseFailAlloc_4785_, 11, v_W_4754_);
lean_ctor_set(v_reuseFailAlloc_4785_, 12, v___x_4782_);
lean_ctor_set(v_reuseFailAlloc_4785_, 13, v_e_4755_);
lean_ctor_set(v_reuseFailAlloc_4785_, 14, v_c_4756_);
lean_ctor_set(v_reuseFailAlloc_4785_, 15, v_F_4757_);
lean_ctor_set(v_reuseFailAlloc_4785_, 16, v_a_4758_);
lean_ctor_set(v_reuseFailAlloc_4785_, 17, v_b_4759_);
lean_ctor_set(v_reuseFailAlloc_4785_, 18, v_B_4760_);
lean_ctor_set(v_reuseFailAlloc_4785_, 19, v_h_4761_);
lean_ctor_set(v_reuseFailAlloc_4785_, 20, v_K_4762_);
lean_ctor_set(v_reuseFailAlloc_4785_, 21, v_k_4763_);
lean_ctor_set(v_reuseFailAlloc_4785_, 22, v_H_4764_);
lean_ctor_set(v_reuseFailAlloc_4785_, 23, v_m_4765_);
lean_ctor_set(v_reuseFailAlloc_4785_, 24, v_s_4766_);
lean_ctor_set(v_reuseFailAlloc_4785_, 25, v_S_4767_);
lean_ctor_set(v_reuseFailAlloc_4785_, 26, v_A_4768_);
lean_ctor_set(v_reuseFailAlloc_4785_, 27, v_n_4769_);
lean_ctor_set(v_reuseFailAlloc_4785_, 28, v_N_4770_);
lean_ctor_set(v_reuseFailAlloc_4785_, 29, v_V_4771_);
lean_ctor_set(v_reuseFailAlloc_4785_, 30, v_z_4772_);
lean_ctor_set(v_reuseFailAlloc_4785_, 31, v_zabbrev_4773_);
lean_ctor_set(v_reuseFailAlloc_4785_, 32, v_v_4774_);
lean_ctor_set(v_reuseFailAlloc_4785_, 33, v_O_4775_);
lean_ctor_set(v_reuseFailAlloc_4785_, 34, v_X_4776_);
lean_ctor_set(v_reuseFailAlloc_4785_, 35, v_x_4777_);
lean_ctor_set(v_reuseFailAlloc_4785_, 36, v_Z_4778_);
v___x_4784_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
return v___x_4784_;
}
}
}
case 13:
{
lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4838_; 
v_isSharedCheck_4838_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_4838_ == 0)
{
lean_object* v_unused_4839_; 
v_unused_4839_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_4839_);
v___x_4789_ = v_modifier_4124_;
v_isShared_4790_ = v_isSharedCheck_4838_;
goto v_resetjp_4788_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4838_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
lean_object* v_G_4791_; lean_object* v_y_4792_; lean_object* v_u_4793_; lean_object* v_Y_4794_; lean_object* v_D_4795_; lean_object* v_M_4796_; lean_object* v_L_4797_; lean_object* v_d_4798_; lean_object* v_Q_4799_; lean_object* v_q_4800_; lean_object* v_w_4801_; lean_object* v_W_4802_; lean_object* v_E_4803_; lean_object* v_c_4804_; lean_object* v_F_4805_; lean_object* v_a_4806_; lean_object* v_b_4807_; lean_object* v_B_4808_; lean_object* v_h_4809_; lean_object* v_K_4810_; lean_object* v_k_4811_; lean_object* v_H_4812_; lean_object* v_m_4813_; lean_object* v_s_4814_; lean_object* v_S_4815_; lean_object* v_A_4816_; lean_object* v_n_4817_; lean_object* v_N_4818_; lean_object* v_V_4819_; lean_object* v_z_4820_; lean_object* v_zabbrev_4821_; lean_object* v_v_4822_; lean_object* v_O_4823_; lean_object* v_X_4824_; lean_object* v_x_4825_; lean_object* v_Z_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4836_; 
v_G_4791_ = lean_ctor_get(v_date_4123_, 0);
v_y_4792_ = lean_ctor_get(v_date_4123_, 1);
v_u_4793_ = lean_ctor_get(v_date_4123_, 2);
v_Y_4794_ = lean_ctor_get(v_date_4123_, 3);
v_D_4795_ = lean_ctor_get(v_date_4123_, 4);
v_M_4796_ = lean_ctor_get(v_date_4123_, 5);
v_L_4797_ = lean_ctor_get(v_date_4123_, 6);
v_d_4798_ = lean_ctor_get(v_date_4123_, 7);
v_Q_4799_ = lean_ctor_get(v_date_4123_, 8);
v_q_4800_ = lean_ctor_get(v_date_4123_, 9);
v_w_4801_ = lean_ctor_get(v_date_4123_, 10);
v_W_4802_ = lean_ctor_get(v_date_4123_, 11);
v_E_4803_ = lean_ctor_get(v_date_4123_, 12);
v_c_4804_ = lean_ctor_get(v_date_4123_, 14);
v_F_4805_ = lean_ctor_get(v_date_4123_, 15);
v_a_4806_ = lean_ctor_get(v_date_4123_, 16);
v_b_4807_ = lean_ctor_get(v_date_4123_, 17);
v_B_4808_ = lean_ctor_get(v_date_4123_, 18);
v_h_4809_ = lean_ctor_get(v_date_4123_, 19);
v_K_4810_ = lean_ctor_get(v_date_4123_, 20);
v_k_4811_ = lean_ctor_get(v_date_4123_, 21);
v_H_4812_ = lean_ctor_get(v_date_4123_, 22);
v_m_4813_ = lean_ctor_get(v_date_4123_, 23);
v_s_4814_ = lean_ctor_get(v_date_4123_, 24);
v_S_4815_ = lean_ctor_get(v_date_4123_, 25);
v_A_4816_ = lean_ctor_get(v_date_4123_, 26);
v_n_4817_ = lean_ctor_get(v_date_4123_, 27);
v_N_4818_ = lean_ctor_get(v_date_4123_, 28);
v_V_4819_ = lean_ctor_get(v_date_4123_, 29);
v_z_4820_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_4821_ = lean_ctor_get(v_date_4123_, 31);
v_v_4822_ = lean_ctor_get(v_date_4123_, 32);
v_O_4823_ = lean_ctor_get(v_date_4123_, 33);
v_X_4824_ = lean_ctor_get(v_date_4123_, 34);
v_x_4825_ = lean_ctor_get(v_date_4123_, 35);
v_Z_4826_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_4836_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_4836_ == 0)
{
lean_object* v_unused_4837_; 
v_unused_4837_ = lean_ctor_get(v_date_4123_, 13);
lean_dec(v_unused_4837_);
v___x_4828_ = v_date_4123_;
v_isShared_4829_ = v_isSharedCheck_4836_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_Z_4826_);
lean_inc(v_x_4825_);
lean_inc(v_X_4824_);
lean_inc(v_O_4823_);
lean_inc(v_v_4822_);
lean_inc(v_zabbrev_4821_);
lean_inc(v_z_4820_);
lean_inc(v_V_4819_);
lean_inc(v_N_4818_);
lean_inc(v_n_4817_);
lean_inc(v_A_4816_);
lean_inc(v_S_4815_);
lean_inc(v_s_4814_);
lean_inc(v_m_4813_);
lean_inc(v_H_4812_);
lean_inc(v_k_4811_);
lean_inc(v_K_4810_);
lean_inc(v_h_4809_);
lean_inc(v_B_4808_);
lean_inc(v_b_4807_);
lean_inc(v_a_4806_);
lean_inc(v_F_4805_);
lean_inc(v_c_4804_);
lean_inc(v_E_4803_);
lean_inc(v_W_4802_);
lean_inc(v_w_4801_);
lean_inc(v_q_4800_);
lean_inc(v_Q_4799_);
lean_inc(v_d_4798_);
lean_inc(v_L_4797_);
lean_inc(v_M_4796_);
lean_inc(v_D_4795_);
lean_inc(v_Y_4794_);
lean_inc(v_u_4793_);
lean_inc(v_y_4792_);
lean_inc(v_G_4791_);
lean_dec(v_date_4123_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4836_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4831_; 
if (v_isShared_4790_ == 0)
{
lean_ctor_set_tag(v___x_4789_, 1);
lean_ctor_set(v___x_4789_, 0, v_data_4125_);
v___x_4831_ = v___x_4789_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_data_4125_);
v___x_4831_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
lean_object* v___x_4833_; 
if (v_isShared_4829_ == 0)
{
lean_ctor_set(v___x_4828_, 13, v___x_4831_);
v___x_4833_ = v___x_4828_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v_G_4791_);
lean_ctor_set(v_reuseFailAlloc_4834_, 1, v_y_4792_);
lean_ctor_set(v_reuseFailAlloc_4834_, 2, v_u_4793_);
lean_ctor_set(v_reuseFailAlloc_4834_, 3, v_Y_4794_);
lean_ctor_set(v_reuseFailAlloc_4834_, 4, v_D_4795_);
lean_ctor_set(v_reuseFailAlloc_4834_, 5, v_M_4796_);
lean_ctor_set(v_reuseFailAlloc_4834_, 6, v_L_4797_);
lean_ctor_set(v_reuseFailAlloc_4834_, 7, v_d_4798_);
lean_ctor_set(v_reuseFailAlloc_4834_, 8, v_Q_4799_);
lean_ctor_set(v_reuseFailAlloc_4834_, 9, v_q_4800_);
lean_ctor_set(v_reuseFailAlloc_4834_, 10, v_w_4801_);
lean_ctor_set(v_reuseFailAlloc_4834_, 11, v_W_4802_);
lean_ctor_set(v_reuseFailAlloc_4834_, 12, v_E_4803_);
lean_ctor_set(v_reuseFailAlloc_4834_, 13, v___x_4831_);
lean_ctor_set(v_reuseFailAlloc_4834_, 14, v_c_4804_);
lean_ctor_set(v_reuseFailAlloc_4834_, 15, v_F_4805_);
lean_ctor_set(v_reuseFailAlloc_4834_, 16, v_a_4806_);
lean_ctor_set(v_reuseFailAlloc_4834_, 17, v_b_4807_);
lean_ctor_set(v_reuseFailAlloc_4834_, 18, v_B_4808_);
lean_ctor_set(v_reuseFailAlloc_4834_, 19, v_h_4809_);
lean_ctor_set(v_reuseFailAlloc_4834_, 20, v_K_4810_);
lean_ctor_set(v_reuseFailAlloc_4834_, 21, v_k_4811_);
lean_ctor_set(v_reuseFailAlloc_4834_, 22, v_H_4812_);
lean_ctor_set(v_reuseFailAlloc_4834_, 23, v_m_4813_);
lean_ctor_set(v_reuseFailAlloc_4834_, 24, v_s_4814_);
lean_ctor_set(v_reuseFailAlloc_4834_, 25, v_S_4815_);
lean_ctor_set(v_reuseFailAlloc_4834_, 26, v_A_4816_);
lean_ctor_set(v_reuseFailAlloc_4834_, 27, v_n_4817_);
lean_ctor_set(v_reuseFailAlloc_4834_, 28, v_N_4818_);
lean_ctor_set(v_reuseFailAlloc_4834_, 29, v_V_4819_);
lean_ctor_set(v_reuseFailAlloc_4834_, 30, v_z_4820_);
lean_ctor_set(v_reuseFailAlloc_4834_, 31, v_zabbrev_4821_);
lean_ctor_set(v_reuseFailAlloc_4834_, 32, v_v_4822_);
lean_ctor_set(v_reuseFailAlloc_4834_, 33, v_O_4823_);
lean_ctor_set(v_reuseFailAlloc_4834_, 34, v_X_4824_);
lean_ctor_set(v_reuseFailAlloc_4834_, 35, v_x_4825_);
lean_ctor_set(v_reuseFailAlloc_4834_, 36, v_Z_4826_);
v___x_4833_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
return v___x_4833_;
}
}
}
}
}
case 14:
{
lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4890_; 
v_isSharedCheck_4890_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_4890_ == 0)
{
lean_object* v_unused_4891_; 
v_unused_4891_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_4891_);
v___x_4841_ = v_modifier_4124_;
v_isShared_4842_ = v_isSharedCheck_4890_;
goto v_resetjp_4840_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4890_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v_G_4843_; lean_object* v_y_4844_; lean_object* v_u_4845_; lean_object* v_Y_4846_; lean_object* v_D_4847_; lean_object* v_M_4848_; lean_object* v_L_4849_; lean_object* v_d_4850_; lean_object* v_Q_4851_; lean_object* v_q_4852_; lean_object* v_w_4853_; lean_object* v_W_4854_; lean_object* v_E_4855_; lean_object* v_e_4856_; lean_object* v_F_4857_; lean_object* v_a_4858_; lean_object* v_b_4859_; lean_object* v_B_4860_; lean_object* v_h_4861_; lean_object* v_K_4862_; lean_object* v_k_4863_; lean_object* v_H_4864_; lean_object* v_m_4865_; lean_object* v_s_4866_; lean_object* v_S_4867_; lean_object* v_A_4868_; lean_object* v_n_4869_; lean_object* v_N_4870_; lean_object* v_V_4871_; lean_object* v_z_4872_; lean_object* v_zabbrev_4873_; lean_object* v_v_4874_; lean_object* v_O_4875_; lean_object* v_X_4876_; lean_object* v_x_4877_; lean_object* v_Z_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4888_; 
v_G_4843_ = lean_ctor_get(v_date_4123_, 0);
v_y_4844_ = lean_ctor_get(v_date_4123_, 1);
v_u_4845_ = lean_ctor_get(v_date_4123_, 2);
v_Y_4846_ = lean_ctor_get(v_date_4123_, 3);
v_D_4847_ = lean_ctor_get(v_date_4123_, 4);
v_M_4848_ = lean_ctor_get(v_date_4123_, 5);
v_L_4849_ = lean_ctor_get(v_date_4123_, 6);
v_d_4850_ = lean_ctor_get(v_date_4123_, 7);
v_Q_4851_ = lean_ctor_get(v_date_4123_, 8);
v_q_4852_ = lean_ctor_get(v_date_4123_, 9);
v_w_4853_ = lean_ctor_get(v_date_4123_, 10);
v_W_4854_ = lean_ctor_get(v_date_4123_, 11);
v_E_4855_ = lean_ctor_get(v_date_4123_, 12);
v_e_4856_ = lean_ctor_get(v_date_4123_, 13);
v_F_4857_ = lean_ctor_get(v_date_4123_, 15);
v_a_4858_ = lean_ctor_get(v_date_4123_, 16);
v_b_4859_ = lean_ctor_get(v_date_4123_, 17);
v_B_4860_ = lean_ctor_get(v_date_4123_, 18);
v_h_4861_ = lean_ctor_get(v_date_4123_, 19);
v_K_4862_ = lean_ctor_get(v_date_4123_, 20);
v_k_4863_ = lean_ctor_get(v_date_4123_, 21);
v_H_4864_ = lean_ctor_get(v_date_4123_, 22);
v_m_4865_ = lean_ctor_get(v_date_4123_, 23);
v_s_4866_ = lean_ctor_get(v_date_4123_, 24);
v_S_4867_ = lean_ctor_get(v_date_4123_, 25);
v_A_4868_ = lean_ctor_get(v_date_4123_, 26);
v_n_4869_ = lean_ctor_get(v_date_4123_, 27);
v_N_4870_ = lean_ctor_get(v_date_4123_, 28);
v_V_4871_ = lean_ctor_get(v_date_4123_, 29);
v_z_4872_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_4873_ = lean_ctor_get(v_date_4123_, 31);
v_v_4874_ = lean_ctor_get(v_date_4123_, 32);
v_O_4875_ = lean_ctor_get(v_date_4123_, 33);
v_X_4876_ = lean_ctor_get(v_date_4123_, 34);
v_x_4877_ = lean_ctor_get(v_date_4123_, 35);
v_Z_4878_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_4888_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_4888_ == 0)
{
lean_object* v_unused_4889_; 
v_unused_4889_ = lean_ctor_get(v_date_4123_, 14);
lean_dec(v_unused_4889_);
v___x_4880_ = v_date_4123_;
v_isShared_4881_ = v_isSharedCheck_4888_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_Z_4878_);
lean_inc(v_x_4877_);
lean_inc(v_X_4876_);
lean_inc(v_O_4875_);
lean_inc(v_v_4874_);
lean_inc(v_zabbrev_4873_);
lean_inc(v_z_4872_);
lean_inc(v_V_4871_);
lean_inc(v_N_4870_);
lean_inc(v_n_4869_);
lean_inc(v_A_4868_);
lean_inc(v_S_4867_);
lean_inc(v_s_4866_);
lean_inc(v_m_4865_);
lean_inc(v_H_4864_);
lean_inc(v_k_4863_);
lean_inc(v_K_4862_);
lean_inc(v_h_4861_);
lean_inc(v_B_4860_);
lean_inc(v_b_4859_);
lean_inc(v_a_4858_);
lean_inc(v_F_4857_);
lean_inc(v_e_4856_);
lean_inc(v_E_4855_);
lean_inc(v_W_4854_);
lean_inc(v_w_4853_);
lean_inc(v_q_4852_);
lean_inc(v_Q_4851_);
lean_inc(v_d_4850_);
lean_inc(v_L_4849_);
lean_inc(v_M_4848_);
lean_inc(v_D_4847_);
lean_inc(v_Y_4846_);
lean_inc(v_u_4845_);
lean_inc(v_y_4844_);
lean_inc(v_G_4843_);
lean_dec(v_date_4123_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4888_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
lean_object* v___x_4883_; 
if (v_isShared_4842_ == 0)
{
lean_ctor_set_tag(v___x_4841_, 1);
lean_ctor_set(v___x_4841_, 0, v_data_4125_);
v___x_4883_ = v___x_4841_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v_data_4125_);
v___x_4883_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
lean_object* v___x_4885_; 
if (v_isShared_4881_ == 0)
{
lean_ctor_set(v___x_4880_, 14, v___x_4883_);
v___x_4885_ = v___x_4880_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v_G_4843_);
lean_ctor_set(v_reuseFailAlloc_4886_, 1, v_y_4844_);
lean_ctor_set(v_reuseFailAlloc_4886_, 2, v_u_4845_);
lean_ctor_set(v_reuseFailAlloc_4886_, 3, v_Y_4846_);
lean_ctor_set(v_reuseFailAlloc_4886_, 4, v_D_4847_);
lean_ctor_set(v_reuseFailAlloc_4886_, 5, v_M_4848_);
lean_ctor_set(v_reuseFailAlloc_4886_, 6, v_L_4849_);
lean_ctor_set(v_reuseFailAlloc_4886_, 7, v_d_4850_);
lean_ctor_set(v_reuseFailAlloc_4886_, 8, v_Q_4851_);
lean_ctor_set(v_reuseFailAlloc_4886_, 9, v_q_4852_);
lean_ctor_set(v_reuseFailAlloc_4886_, 10, v_w_4853_);
lean_ctor_set(v_reuseFailAlloc_4886_, 11, v_W_4854_);
lean_ctor_set(v_reuseFailAlloc_4886_, 12, v_E_4855_);
lean_ctor_set(v_reuseFailAlloc_4886_, 13, v_e_4856_);
lean_ctor_set(v_reuseFailAlloc_4886_, 14, v___x_4883_);
lean_ctor_set(v_reuseFailAlloc_4886_, 15, v_F_4857_);
lean_ctor_set(v_reuseFailAlloc_4886_, 16, v_a_4858_);
lean_ctor_set(v_reuseFailAlloc_4886_, 17, v_b_4859_);
lean_ctor_set(v_reuseFailAlloc_4886_, 18, v_B_4860_);
lean_ctor_set(v_reuseFailAlloc_4886_, 19, v_h_4861_);
lean_ctor_set(v_reuseFailAlloc_4886_, 20, v_K_4862_);
lean_ctor_set(v_reuseFailAlloc_4886_, 21, v_k_4863_);
lean_ctor_set(v_reuseFailAlloc_4886_, 22, v_H_4864_);
lean_ctor_set(v_reuseFailAlloc_4886_, 23, v_m_4865_);
lean_ctor_set(v_reuseFailAlloc_4886_, 24, v_s_4866_);
lean_ctor_set(v_reuseFailAlloc_4886_, 25, v_S_4867_);
lean_ctor_set(v_reuseFailAlloc_4886_, 26, v_A_4868_);
lean_ctor_set(v_reuseFailAlloc_4886_, 27, v_n_4869_);
lean_ctor_set(v_reuseFailAlloc_4886_, 28, v_N_4870_);
lean_ctor_set(v_reuseFailAlloc_4886_, 29, v_V_4871_);
lean_ctor_set(v_reuseFailAlloc_4886_, 30, v_z_4872_);
lean_ctor_set(v_reuseFailAlloc_4886_, 31, v_zabbrev_4873_);
lean_ctor_set(v_reuseFailAlloc_4886_, 32, v_v_4874_);
lean_ctor_set(v_reuseFailAlloc_4886_, 33, v_O_4875_);
lean_ctor_set(v_reuseFailAlloc_4886_, 34, v_X_4876_);
lean_ctor_set(v_reuseFailAlloc_4886_, 35, v_x_4877_);
lean_ctor_set(v_reuseFailAlloc_4886_, 36, v_Z_4878_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
}
}
case 15:
{
lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4942_; 
v_isSharedCheck_4942_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_4942_ == 0)
{
lean_object* v_unused_4943_; 
v_unused_4943_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_4943_);
v___x_4893_ = v_modifier_4124_;
v_isShared_4894_ = v_isSharedCheck_4942_;
goto v_resetjp_4892_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4942_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v_G_4895_; lean_object* v_y_4896_; lean_object* v_u_4897_; lean_object* v_Y_4898_; lean_object* v_D_4899_; lean_object* v_M_4900_; lean_object* v_L_4901_; lean_object* v_d_4902_; lean_object* v_Q_4903_; lean_object* v_q_4904_; lean_object* v_w_4905_; lean_object* v_W_4906_; lean_object* v_E_4907_; lean_object* v_e_4908_; lean_object* v_c_4909_; lean_object* v_a_4910_; lean_object* v_b_4911_; lean_object* v_B_4912_; lean_object* v_h_4913_; lean_object* v_K_4914_; lean_object* v_k_4915_; lean_object* v_H_4916_; lean_object* v_m_4917_; lean_object* v_s_4918_; lean_object* v_S_4919_; lean_object* v_A_4920_; lean_object* v_n_4921_; lean_object* v_N_4922_; lean_object* v_V_4923_; lean_object* v_z_4924_; lean_object* v_zabbrev_4925_; lean_object* v_v_4926_; lean_object* v_O_4927_; lean_object* v_X_4928_; lean_object* v_x_4929_; lean_object* v_Z_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4940_; 
v_G_4895_ = lean_ctor_get(v_date_4123_, 0);
v_y_4896_ = lean_ctor_get(v_date_4123_, 1);
v_u_4897_ = lean_ctor_get(v_date_4123_, 2);
v_Y_4898_ = lean_ctor_get(v_date_4123_, 3);
v_D_4899_ = lean_ctor_get(v_date_4123_, 4);
v_M_4900_ = lean_ctor_get(v_date_4123_, 5);
v_L_4901_ = lean_ctor_get(v_date_4123_, 6);
v_d_4902_ = lean_ctor_get(v_date_4123_, 7);
v_Q_4903_ = lean_ctor_get(v_date_4123_, 8);
v_q_4904_ = lean_ctor_get(v_date_4123_, 9);
v_w_4905_ = lean_ctor_get(v_date_4123_, 10);
v_W_4906_ = lean_ctor_get(v_date_4123_, 11);
v_E_4907_ = lean_ctor_get(v_date_4123_, 12);
v_e_4908_ = lean_ctor_get(v_date_4123_, 13);
v_c_4909_ = lean_ctor_get(v_date_4123_, 14);
v_a_4910_ = lean_ctor_get(v_date_4123_, 16);
v_b_4911_ = lean_ctor_get(v_date_4123_, 17);
v_B_4912_ = lean_ctor_get(v_date_4123_, 18);
v_h_4913_ = lean_ctor_get(v_date_4123_, 19);
v_K_4914_ = lean_ctor_get(v_date_4123_, 20);
v_k_4915_ = lean_ctor_get(v_date_4123_, 21);
v_H_4916_ = lean_ctor_get(v_date_4123_, 22);
v_m_4917_ = lean_ctor_get(v_date_4123_, 23);
v_s_4918_ = lean_ctor_get(v_date_4123_, 24);
v_S_4919_ = lean_ctor_get(v_date_4123_, 25);
v_A_4920_ = lean_ctor_get(v_date_4123_, 26);
v_n_4921_ = lean_ctor_get(v_date_4123_, 27);
v_N_4922_ = lean_ctor_get(v_date_4123_, 28);
v_V_4923_ = lean_ctor_get(v_date_4123_, 29);
v_z_4924_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_4925_ = lean_ctor_get(v_date_4123_, 31);
v_v_4926_ = lean_ctor_get(v_date_4123_, 32);
v_O_4927_ = lean_ctor_get(v_date_4123_, 33);
v_X_4928_ = lean_ctor_get(v_date_4123_, 34);
v_x_4929_ = lean_ctor_get(v_date_4123_, 35);
v_Z_4930_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_4940_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_4940_ == 0)
{
lean_object* v_unused_4941_; 
v_unused_4941_ = lean_ctor_get(v_date_4123_, 15);
lean_dec(v_unused_4941_);
v___x_4932_ = v_date_4123_;
v_isShared_4933_ = v_isSharedCheck_4940_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_Z_4930_);
lean_inc(v_x_4929_);
lean_inc(v_X_4928_);
lean_inc(v_O_4927_);
lean_inc(v_v_4926_);
lean_inc(v_zabbrev_4925_);
lean_inc(v_z_4924_);
lean_inc(v_V_4923_);
lean_inc(v_N_4922_);
lean_inc(v_n_4921_);
lean_inc(v_A_4920_);
lean_inc(v_S_4919_);
lean_inc(v_s_4918_);
lean_inc(v_m_4917_);
lean_inc(v_H_4916_);
lean_inc(v_k_4915_);
lean_inc(v_K_4914_);
lean_inc(v_h_4913_);
lean_inc(v_B_4912_);
lean_inc(v_b_4911_);
lean_inc(v_a_4910_);
lean_inc(v_c_4909_);
lean_inc(v_e_4908_);
lean_inc(v_E_4907_);
lean_inc(v_W_4906_);
lean_inc(v_w_4905_);
lean_inc(v_q_4904_);
lean_inc(v_Q_4903_);
lean_inc(v_d_4902_);
lean_inc(v_L_4901_);
lean_inc(v_M_4900_);
lean_inc(v_D_4899_);
lean_inc(v_Y_4898_);
lean_inc(v_u_4897_);
lean_inc(v_y_4896_);
lean_inc(v_G_4895_);
lean_dec(v_date_4123_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4940_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4935_; 
if (v_isShared_4894_ == 0)
{
lean_ctor_set_tag(v___x_4893_, 1);
lean_ctor_set(v___x_4893_, 0, v_data_4125_);
v___x_4935_ = v___x_4893_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v_data_4125_);
v___x_4935_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
lean_object* v___x_4937_; 
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 15, v___x_4935_);
v___x_4937_ = v___x_4932_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_G_4895_);
lean_ctor_set(v_reuseFailAlloc_4938_, 1, v_y_4896_);
lean_ctor_set(v_reuseFailAlloc_4938_, 2, v_u_4897_);
lean_ctor_set(v_reuseFailAlloc_4938_, 3, v_Y_4898_);
lean_ctor_set(v_reuseFailAlloc_4938_, 4, v_D_4899_);
lean_ctor_set(v_reuseFailAlloc_4938_, 5, v_M_4900_);
lean_ctor_set(v_reuseFailAlloc_4938_, 6, v_L_4901_);
lean_ctor_set(v_reuseFailAlloc_4938_, 7, v_d_4902_);
lean_ctor_set(v_reuseFailAlloc_4938_, 8, v_Q_4903_);
lean_ctor_set(v_reuseFailAlloc_4938_, 9, v_q_4904_);
lean_ctor_set(v_reuseFailAlloc_4938_, 10, v_w_4905_);
lean_ctor_set(v_reuseFailAlloc_4938_, 11, v_W_4906_);
lean_ctor_set(v_reuseFailAlloc_4938_, 12, v_E_4907_);
lean_ctor_set(v_reuseFailAlloc_4938_, 13, v_e_4908_);
lean_ctor_set(v_reuseFailAlloc_4938_, 14, v_c_4909_);
lean_ctor_set(v_reuseFailAlloc_4938_, 15, v___x_4935_);
lean_ctor_set(v_reuseFailAlloc_4938_, 16, v_a_4910_);
lean_ctor_set(v_reuseFailAlloc_4938_, 17, v_b_4911_);
lean_ctor_set(v_reuseFailAlloc_4938_, 18, v_B_4912_);
lean_ctor_set(v_reuseFailAlloc_4938_, 19, v_h_4913_);
lean_ctor_set(v_reuseFailAlloc_4938_, 20, v_K_4914_);
lean_ctor_set(v_reuseFailAlloc_4938_, 21, v_k_4915_);
lean_ctor_set(v_reuseFailAlloc_4938_, 22, v_H_4916_);
lean_ctor_set(v_reuseFailAlloc_4938_, 23, v_m_4917_);
lean_ctor_set(v_reuseFailAlloc_4938_, 24, v_s_4918_);
lean_ctor_set(v_reuseFailAlloc_4938_, 25, v_S_4919_);
lean_ctor_set(v_reuseFailAlloc_4938_, 26, v_A_4920_);
lean_ctor_set(v_reuseFailAlloc_4938_, 27, v_n_4921_);
lean_ctor_set(v_reuseFailAlloc_4938_, 28, v_N_4922_);
lean_ctor_set(v_reuseFailAlloc_4938_, 29, v_V_4923_);
lean_ctor_set(v_reuseFailAlloc_4938_, 30, v_z_4924_);
lean_ctor_set(v_reuseFailAlloc_4938_, 31, v_zabbrev_4925_);
lean_ctor_set(v_reuseFailAlloc_4938_, 32, v_v_4926_);
lean_ctor_set(v_reuseFailAlloc_4938_, 33, v_O_4927_);
lean_ctor_set(v_reuseFailAlloc_4938_, 34, v_X_4928_);
lean_ctor_set(v_reuseFailAlloc_4938_, 35, v_x_4929_);
lean_ctor_set(v_reuseFailAlloc_4938_, 36, v_Z_4930_);
v___x_4937_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
return v___x_4937_;
}
}
}
}
}
case 16:
{
lean_object* v_G_4944_; lean_object* v_y_4945_; lean_object* v_u_4946_; lean_object* v_Y_4947_; lean_object* v_D_4948_; lean_object* v_M_4949_; lean_object* v_L_4950_; lean_object* v_d_4951_; lean_object* v_Q_4952_; lean_object* v_q_4953_; lean_object* v_w_4954_; lean_object* v_W_4955_; lean_object* v_E_4956_; lean_object* v_e_4957_; lean_object* v_c_4958_; lean_object* v_F_4959_; lean_object* v_b_4960_; lean_object* v_B_4961_; lean_object* v_h_4962_; lean_object* v_K_4963_; lean_object* v_k_4964_; lean_object* v_H_4965_; lean_object* v_m_4966_; lean_object* v_s_4967_; lean_object* v_S_4968_; lean_object* v_A_4969_; lean_object* v_n_4970_; lean_object* v_N_4971_; lean_object* v_V_4972_; lean_object* v_z_4973_; lean_object* v_zabbrev_4974_; lean_object* v_v_4975_; lean_object* v_O_4976_; lean_object* v_X_4977_; lean_object* v_x_4978_; lean_object* v_Z_4979_; lean_object* v___x_4981_; uint8_t v_isShared_4982_; uint8_t v_isSharedCheck_4987_; 
lean_dec_ref_known(v_modifier_4124_, 0);
v_G_4944_ = lean_ctor_get(v_date_4123_, 0);
v_y_4945_ = lean_ctor_get(v_date_4123_, 1);
v_u_4946_ = lean_ctor_get(v_date_4123_, 2);
v_Y_4947_ = lean_ctor_get(v_date_4123_, 3);
v_D_4948_ = lean_ctor_get(v_date_4123_, 4);
v_M_4949_ = lean_ctor_get(v_date_4123_, 5);
v_L_4950_ = lean_ctor_get(v_date_4123_, 6);
v_d_4951_ = lean_ctor_get(v_date_4123_, 7);
v_Q_4952_ = lean_ctor_get(v_date_4123_, 8);
v_q_4953_ = lean_ctor_get(v_date_4123_, 9);
v_w_4954_ = lean_ctor_get(v_date_4123_, 10);
v_W_4955_ = lean_ctor_get(v_date_4123_, 11);
v_E_4956_ = lean_ctor_get(v_date_4123_, 12);
v_e_4957_ = lean_ctor_get(v_date_4123_, 13);
v_c_4958_ = lean_ctor_get(v_date_4123_, 14);
v_F_4959_ = lean_ctor_get(v_date_4123_, 15);
v_b_4960_ = lean_ctor_get(v_date_4123_, 17);
v_B_4961_ = lean_ctor_get(v_date_4123_, 18);
v_h_4962_ = lean_ctor_get(v_date_4123_, 19);
v_K_4963_ = lean_ctor_get(v_date_4123_, 20);
v_k_4964_ = lean_ctor_get(v_date_4123_, 21);
v_H_4965_ = lean_ctor_get(v_date_4123_, 22);
v_m_4966_ = lean_ctor_get(v_date_4123_, 23);
v_s_4967_ = lean_ctor_get(v_date_4123_, 24);
v_S_4968_ = lean_ctor_get(v_date_4123_, 25);
v_A_4969_ = lean_ctor_get(v_date_4123_, 26);
v_n_4970_ = lean_ctor_get(v_date_4123_, 27);
v_N_4971_ = lean_ctor_get(v_date_4123_, 28);
v_V_4972_ = lean_ctor_get(v_date_4123_, 29);
v_z_4973_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_4974_ = lean_ctor_get(v_date_4123_, 31);
v_v_4975_ = lean_ctor_get(v_date_4123_, 32);
v_O_4976_ = lean_ctor_get(v_date_4123_, 33);
v_X_4977_ = lean_ctor_get(v_date_4123_, 34);
v_x_4978_ = lean_ctor_get(v_date_4123_, 35);
v_Z_4979_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_4987_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_4987_ == 0)
{
lean_object* v_unused_4988_; 
v_unused_4988_ = lean_ctor_get(v_date_4123_, 16);
lean_dec(v_unused_4988_);
v___x_4981_ = v_date_4123_;
v_isShared_4982_ = v_isSharedCheck_4987_;
goto v_resetjp_4980_;
}
else
{
lean_inc(v_Z_4979_);
lean_inc(v_x_4978_);
lean_inc(v_X_4977_);
lean_inc(v_O_4976_);
lean_inc(v_v_4975_);
lean_inc(v_zabbrev_4974_);
lean_inc(v_z_4973_);
lean_inc(v_V_4972_);
lean_inc(v_N_4971_);
lean_inc(v_n_4970_);
lean_inc(v_A_4969_);
lean_inc(v_S_4968_);
lean_inc(v_s_4967_);
lean_inc(v_m_4966_);
lean_inc(v_H_4965_);
lean_inc(v_k_4964_);
lean_inc(v_K_4963_);
lean_inc(v_h_4962_);
lean_inc(v_B_4961_);
lean_inc(v_b_4960_);
lean_inc(v_F_4959_);
lean_inc(v_c_4958_);
lean_inc(v_e_4957_);
lean_inc(v_E_4956_);
lean_inc(v_W_4955_);
lean_inc(v_w_4954_);
lean_inc(v_q_4953_);
lean_inc(v_Q_4952_);
lean_inc(v_d_4951_);
lean_inc(v_L_4950_);
lean_inc(v_M_4949_);
lean_inc(v_D_4948_);
lean_inc(v_Y_4947_);
lean_inc(v_u_4946_);
lean_inc(v_y_4945_);
lean_inc(v_G_4944_);
lean_dec(v_date_4123_);
v___x_4981_ = lean_box(0);
v_isShared_4982_ = v_isSharedCheck_4987_;
goto v_resetjp_4980_;
}
v_resetjp_4980_:
{
lean_object* v___x_4983_; lean_object* v___x_4985_; 
v___x_4983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4983_, 0, v_data_4125_);
if (v_isShared_4982_ == 0)
{
lean_ctor_set(v___x_4981_, 16, v___x_4983_);
v___x_4985_ = v___x_4981_;
goto v_reusejp_4984_;
}
else
{
lean_object* v_reuseFailAlloc_4986_; 
v_reuseFailAlloc_4986_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4986_, 0, v_G_4944_);
lean_ctor_set(v_reuseFailAlloc_4986_, 1, v_y_4945_);
lean_ctor_set(v_reuseFailAlloc_4986_, 2, v_u_4946_);
lean_ctor_set(v_reuseFailAlloc_4986_, 3, v_Y_4947_);
lean_ctor_set(v_reuseFailAlloc_4986_, 4, v_D_4948_);
lean_ctor_set(v_reuseFailAlloc_4986_, 5, v_M_4949_);
lean_ctor_set(v_reuseFailAlloc_4986_, 6, v_L_4950_);
lean_ctor_set(v_reuseFailAlloc_4986_, 7, v_d_4951_);
lean_ctor_set(v_reuseFailAlloc_4986_, 8, v_Q_4952_);
lean_ctor_set(v_reuseFailAlloc_4986_, 9, v_q_4953_);
lean_ctor_set(v_reuseFailAlloc_4986_, 10, v_w_4954_);
lean_ctor_set(v_reuseFailAlloc_4986_, 11, v_W_4955_);
lean_ctor_set(v_reuseFailAlloc_4986_, 12, v_E_4956_);
lean_ctor_set(v_reuseFailAlloc_4986_, 13, v_e_4957_);
lean_ctor_set(v_reuseFailAlloc_4986_, 14, v_c_4958_);
lean_ctor_set(v_reuseFailAlloc_4986_, 15, v_F_4959_);
lean_ctor_set(v_reuseFailAlloc_4986_, 16, v___x_4983_);
lean_ctor_set(v_reuseFailAlloc_4986_, 17, v_b_4960_);
lean_ctor_set(v_reuseFailAlloc_4986_, 18, v_B_4961_);
lean_ctor_set(v_reuseFailAlloc_4986_, 19, v_h_4962_);
lean_ctor_set(v_reuseFailAlloc_4986_, 20, v_K_4963_);
lean_ctor_set(v_reuseFailAlloc_4986_, 21, v_k_4964_);
lean_ctor_set(v_reuseFailAlloc_4986_, 22, v_H_4965_);
lean_ctor_set(v_reuseFailAlloc_4986_, 23, v_m_4966_);
lean_ctor_set(v_reuseFailAlloc_4986_, 24, v_s_4967_);
lean_ctor_set(v_reuseFailAlloc_4986_, 25, v_S_4968_);
lean_ctor_set(v_reuseFailAlloc_4986_, 26, v_A_4969_);
lean_ctor_set(v_reuseFailAlloc_4986_, 27, v_n_4970_);
lean_ctor_set(v_reuseFailAlloc_4986_, 28, v_N_4971_);
lean_ctor_set(v_reuseFailAlloc_4986_, 29, v_V_4972_);
lean_ctor_set(v_reuseFailAlloc_4986_, 30, v_z_4973_);
lean_ctor_set(v_reuseFailAlloc_4986_, 31, v_zabbrev_4974_);
lean_ctor_set(v_reuseFailAlloc_4986_, 32, v_v_4975_);
lean_ctor_set(v_reuseFailAlloc_4986_, 33, v_O_4976_);
lean_ctor_set(v_reuseFailAlloc_4986_, 34, v_X_4977_);
lean_ctor_set(v_reuseFailAlloc_4986_, 35, v_x_4978_);
lean_ctor_set(v_reuseFailAlloc_4986_, 36, v_Z_4979_);
v___x_4985_ = v_reuseFailAlloc_4986_;
goto v_reusejp_4984_;
}
v_reusejp_4984_:
{
return v___x_4985_;
}
}
}
case 17:
{
lean_object* v_G_4989_; lean_object* v_y_4990_; lean_object* v_u_4991_; lean_object* v_Y_4992_; lean_object* v_D_4993_; lean_object* v_M_4994_; lean_object* v_L_4995_; lean_object* v_d_4996_; lean_object* v_Q_4997_; lean_object* v_q_4998_; lean_object* v_w_4999_; lean_object* v_W_5000_; lean_object* v_E_5001_; lean_object* v_e_5002_; lean_object* v_c_5003_; lean_object* v_F_5004_; lean_object* v_a_5005_; lean_object* v_B_5006_; lean_object* v_h_5007_; lean_object* v_K_5008_; lean_object* v_k_5009_; lean_object* v_H_5010_; lean_object* v_m_5011_; lean_object* v_s_5012_; lean_object* v_S_5013_; lean_object* v_A_5014_; lean_object* v_n_5015_; lean_object* v_N_5016_; lean_object* v_V_5017_; lean_object* v_z_5018_; lean_object* v_zabbrev_5019_; lean_object* v_v_5020_; lean_object* v_O_5021_; lean_object* v_X_5022_; lean_object* v_x_5023_; lean_object* v_Z_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5032_; 
lean_dec_ref_known(v_modifier_4124_, 0);
v_G_4989_ = lean_ctor_get(v_date_4123_, 0);
v_y_4990_ = lean_ctor_get(v_date_4123_, 1);
v_u_4991_ = lean_ctor_get(v_date_4123_, 2);
v_Y_4992_ = lean_ctor_get(v_date_4123_, 3);
v_D_4993_ = lean_ctor_get(v_date_4123_, 4);
v_M_4994_ = lean_ctor_get(v_date_4123_, 5);
v_L_4995_ = lean_ctor_get(v_date_4123_, 6);
v_d_4996_ = lean_ctor_get(v_date_4123_, 7);
v_Q_4997_ = lean_ctor_get(v_date_4123_, 8);
v_q_4998_ = lean_ctor_get(v_date_4123_, 9);
v_w_4999_ = lean_ctor_get(v_date_4123_, 10);
v_W_5000_ = lean_ctor_get(v_date_4123_, 11);
v_E_5001_ = lean_ctor_get(v_date_4123_, 12);
v_e_5002_ = lean_ctor_get(v_date_4123_, 13);
v_c_5003_ = lean_ctor_get(v_date_4123_, 14);
v_F_5004_ = lean_ctor_get(v_date_4123_, 15);
v_a_5005_ = lean_ctor_get(v_date_4123_, 16);
v_B_5006_ = lean_ctor_get(v_date_4123_, 18);
v_h_5007_ = lean_ctor_get(v_date_4123_, 19);
v_K_5008_ = lean_ctor_get(v_date_4123_, 20);
v_k_5009_ = lean_ctor_get(v_date_4123_, 21);
v_H_5010_ = lean_ctor_get(v_date_4123_, 22);
v_m_5011_ = lean_ctor_get(v_date_4123_, 23);
v_s_5012_ = lean_ctor_get(v_date_4123_, 24);
v_S_5013_ = lean_ctor_get(v_date_4123_, 25);
v_A_5014_ = lean_ctor_get(v_date_4123_, 26);
v_n_5015_ = lean_ctor_get(v_date_4123_, 27);
v_N_5016_ = lean_ctor_get(v_date_4123_, 28);
v_V_5017_ = lean_ctor_get(v_date_4123_, 29);
v_z_5018_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_5019_ = lean_ctor_get(v_date_4123_, 31);
v_v_5020_ = lean_ctor_get(v_date_4123_, 32);
v_O_5021_ = lean_ctor_get(v_date_4123_, 33);
v_X_5022_ = lean_ctor_get(v_date_4123_, 34);
v_x_5023_ = lean_ctor_get(v_date_4123_, 35);
v_Z_5024_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5032_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5032_ == 0)
{
lean_object* v_unused_5033_; 
v_unused_5033_ = lean_ctor_get(v_date_4123_, 17);
lean_dec(v_unused_5033_);
v___x_5026_ = v_date_4123_;
v_isShared_5027_ = v_isSharedCheck_5032_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_Z_5024_);
lean_inc(v_x_5023_);
lean_inc(v_X_5022_);
lean_inc(v_O_5021_);
lean_inc(v_v_5020_);
lean_inc(v_zabbrev_5019_);
lean_inc(v_z_5018_);
lean_inc(v_V_5017_);
lean_inc(v_N_5016_);
lean_inc(v_n_5015_);
lean_inc(v_A_5014_);
lean_inc(v_S_5013_);
lean_inc(v_s_5012_);
lean_inc(v_m_5011_);
lean_inc(v_H_5010_);
lean_inc(v_k_5009_);
lean_inc(v_K_5008_);
lean_inc(v_h_5007_);
lean_inc(v_B_5006_);
lean_inc(v_a_5005_);
lean_inc(v_F_5004_);
lean_inc(v_c_5003_);
lean_inc(v_e_5002_);
lean_inc(v_E_5001_);
lean_inc(v_W_5000_);
lean_inc(v_w_4999_);
lean_inc(v_q_4998_);
lean_inc(v_Q_4997_);
lean_inc(v_d_4996_);
lean_inc(v_L_4995_);
lean_inc(v_M_4994_);
lean_inc(v_D_4993_);
lean_inc(v_Y_4992_);
lean_inc(v_u_4991_);
lean_inc(v_y_4990_);
lean_inc(v_G_4989_);
lean_dec(v_date_4123_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5032_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v___x_5028_; lean_object* v___x_5030_; 
v___x_5028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5028_, 0, v_data_4125_);
if (v_isShared_5027_ == 0)
{
lean_ctor_set(v___x_5026_, 17, v___x_5028_);
v___x_5030_ = v___x_5026_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v_G_4989_);
lean_ctor_set(v_reuseFailAlloc_5031_, 1, v_y_4990_);
lean_ctor_set(v_reuseFailAlloc_5031_, 2, v_u_4991_);
lean_ctor_set(v_reuseFailAlloc_5031_, 3, v_Y_4992_);
lean_ctor_set(v_reuseFailAlloc_5031_, 4, v_D_4993_);
lean_ctor_set(v_reuseFailAlloc_5031_, 5, v_M_4994_);
lean_ctor_set(v_reuseFailAlloc_5031_, 6, v_L_4995_);
lean_ctor_set(v_reuseFailAlloc_5031_, 7, v_d_4996_);
lean_ctor_set(v_reuseFailAlloc_5031_, 8, v_Q_4997_);
lean_ctor_set(v_reuseFailAlloc_5031_, 9, v_q_4998_);
lean_ctor_set(v_reuseFailAlloc_5031_, 10, v_w_4999_);
lean_ctor_set(v_reuseFailAlloc_5031_, 11, v_W_5000_);
lean_ctor_set(v_reuseFailAlloc_5031_, 12, v_E_5001_);
lean_ctor_set(v_reuseFailAlloc_5031_, 13, v_e_5002_);
lean_ctor_set(v_reuseFailAlloc_5031_, 14, v_c_5003_);
lean_ctor_set(v_reuseFailAlloc_5031_, 15, v_F_5004_);
lean_ctor_set(v_reuseFailAlloc_5031_, 16, v_a_5005_);
lean_ctor_set(v_reuseFailAlloc_5031_, 17, v___x_5028_);
lean_ctor_set(v_reuseFailAlloc_5031_, 18, v_B_5006_);
lean_ctor_set(v_reuseFailAlloc_5031_, 19, v_h_5007_);
lean_ctor_set(v_reuseFailAlloc_5031_, 20, v_K_5008_);
lean_ctor_set(v_reuseFailAlloc_5031_, 21, v_k_5009_);
lean_ctor_set(v_reuseFailAlloc_5031_, 22, v_H_5010_);
lean_ctor_set(v_reuseFailAlloc_5031_, 23, v_m_5011_);
lean_ctor_set(v_reuseFailAlloc_5031_, 24, v_s_5012_);
lean_ctor_set(v_reuseFailAlloc_5031_, 25, v_S_5013_);
lean_ctor_set(v_reuseFailAlloc_5031_, 26, v_A_5014_);
lean_ctor_set(v_reuseFailAlloc_5031_, 27, v_n_5015_);
lean_ctor_set(v_reuseFailAlloc_5031_, 28, v_N_5016_);
lean_ctor_set(v_reuseFailAlloc_5031_, 29, v_V_5017_);
lean_ctor_set(v_reuseFailAlloc_5031_, 30, v_z_5018_);
lean_ctor_set(v_reuseFailAlloc_5031_, 31, v_zabbrev_5019_);
lean_ctor_set(v_reuseFailAlloc_5031_, 32, v_v_5020_);
lean_ctor_set(v_reuseFailAlloc_5031_, 33, v_O_5021_);
lean_ctor_set(v_reuseFailAlloc_5031_, 34, v_X_5022_);
lean_ctor_set(v_reuseFailAlloc_5031_, 35, v_x_5023_);
lean_ctor_set(v_reuseFailAlloc_5031_, 36, v_Z_5024_);
v___x_5030_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
return v___x_5030_;
}
}
}
case 18:
{
lean_object* v_G_5034_; lean_object* v_y_5035_; lean_object* v_u_5036_; lean_object* v_Y_5037_; lean_object* v_D_5038_; lean_object* v_M_5039_; lean_object* v_L_5040_; lean_object* v_d_5041_; lean_object* v_Q_5042_; lean_object* v_q_5043_; lean_object* v_w_5044_; lean_object* v_W_5045_; lean_object* v_E_5046_; lean_object* v_e_5047_; lean_object* v_c_5048_; lean_object* v_F_5049_; lean_object* v_a_5050_; lean_object* v_b_5051_; lean_object* v_h_5052_; lean_object* v_K_5053_; lean_object* v_k_5054_; lean_object* v_H_5055_; lean_object* v_m_5056_; lean_object* v_s_5057_; lean_object* v_S_5058_; lean_object* v_A_5059_; lean_object* v_n_5060_; lean_object* v_N_5061_; lean_object* v_V_5062_; lean_object* v_z_5063_; lean_object* v_zabbrev_5064_; lean_object* v_v_5065_; lean_object* v_O_5066_; lean_object* v_X_5067_; lean_object* v_x_5068_; lean_object* v_Z_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5077_; 
lean_dec_ref_known(v_modifier_4124_, 0);
v_G_5034_ = lean_ctor_get(v_date_4123_, 0);
v_y_5035_ = lean_ctor_get(v_date_4123_, 1);
v_u_5036_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5037_ = lean_ctor_get(v_date_4123_, 3);
v_D_5038_ = lean_ctor_get(v_date_4123_, 4);
v_M_5039_ = lean_ctor_get(v_date_4123_, 5);
v_L_5040_ = lean_ctor_get(v_date_4123_, 6);
v_d_5041_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5042_ = lean_ctor_get(v_date_4123_, 8);
v_q_5043_ = lean_ctor_get(v_date_4123_, 9);
v_w_5044_ = lean_ctor_get(v_date_4123_, 10);
v_W_5045_ = lean_ctor_get(v_date_4123_, 11);
v_E_5046_ = lean_ctor_get(v_date_4123_, 12);
v_e_5047_ = lean_ctor_get(v_date_4123_, 13);
v_c_5048_ = lean_ctor_get(v_date_4123_, 14);
v_F_5049_ = lean_ctor_get(v_date_4123_, 15);
v_a_5050_ = lean_ctor_get(v_date_4123_, 16);
v_b_5051_ = lean_ctor_get(v_date_4123_, 17);
v_h_5052_ = lean_ctor_get(v_date_4123_, 19);
v_K_5053_ = lean_ctor_get(v_date_4123_, 20);
v_k_5054_ = lean_ctor_get(v_date_4123_, 21);
v_H_5055_ = lean_ctor_get(v_date_4123_, 22);
v_m_5056_ = lean_ctor_get(v_date_4123_, 23);
v_s_5057_ = lean_ctor_get(v_date_4123_, 24);
v_S_5058_ = lean_ctor_get(v_date_4123_, 25);
v_A_5059_ = lean_ctor_get(v_date_4123_, 26);
v_n_5060_ = lean_ctor_get(v_date_4123_, 27);
v_N_5061_ = lean_ctor_get(v_date_4123_, 28);
v_V_5062_ = lean_ctor_get(v_date_4123_, 29);
v_z_5063_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_5064_ = lean_ctor_get(v_date_4123_, 31);
v_v_5065_ = lean_ctor_get(v_date_4123_, 32);
v_O_5066_ = lean_ctor_get(v_date_4123_, 33);
v_X_5067_ = lean_ctor_get(v_date_4123_, 34);
v_x_5068_ = lean_ctor_get(v_date_4123_, 35);
v_Z_5069_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5077_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5077_ == 0)
{
lean_object* v_unused_5078_; 
v_unused_5078_ = lean_ctor_get(v_date_4123_, 18);
lean_dec(v_unused_5078_);
v___x_5071_ = v_date_4123_;
v_isShared_5072_ = v_isSharedCheck_5077_;
goto v_resetjp_5070_;
}
else
{
lean_inc(v_Z_5069_);
lean_inc(v_x_5068_);
lean_inc(v_X_5067_);
lean_inc(v_O_5066_);
lean_inc(v_v_5065_);
lean_inc(v_zabbrev_5064_);
lean_inc(v_z_5063_);
lean_inc(v_V_5062_);
lean_inc(v_N_5061_);
lean_inc(v_n_5060_);
lean_inc(v_A_5059_);
lean_inc(v_S_5058_);
lean_inc(v_s_5057_);
lean_inc(v_m_5056_);
lean_inc(v_H_5055_);
lean_inc(v_k_5054_);
lean_inc(v_K_5053_);
lean_inc(v_h_5052_);
lean_inc(v_b_5051_);
lean_inc(v_a_5050_);
lean_inc(v_F_5049_);
lean_inc(v_c_5048_);
lean_inc(v_e_5047_);
lean_inc(v_E_5046_);
lean_inc(v_W_5045_);
lean_inc(v_w_5044_);
lean_inc(v_q_5043_);
lean_inc(v_Q_5042_);
lean_inc(v_d_5041_);
lean_inc(v_L_5040_);
lean_inc(v_M_5039_);
lean_inc(v_D_5038_);
lean_inc(v_Y_5037_);
lean_inc(v_u_5036_);
lean_inc(v_y_5035_);
lean_inc(v_G_5034_);
lean_dec(v_date_4123_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5077_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5073_; lean_object* v___x_5075_; 
v___x_5073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5073_, 0, v_data_4125_);
if (v_isShared_5072_ == 0)
{
lean_ctor_set(v___x_5071_, 18, v___x_5073_);
v___x_5075_ = v___x_5071_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v_G_5034_);
lean_ctor_set(v_reuseFailAlloc_5076_, 1, v_y_5035_);
lean_ctor_set(v_reuseFailAlloc_5076_, 2, v_u_5036_);
lean_ctor_set(v_reuseFailAlloc_5076_, 3, v_Y_5037_);
lean_ctor_set(v_reuseFailAlloc_5076_, 4, v_D_5038_);
lean_ctor_set(v_reuseFailAlloc_5076_, 5, v_M_5039_);
lean_ctor_set(v_reuseFailAlloc_5076_, 6, v_L_5040_);
lean_ctor_set(v_reuseFailAlloc_5076_, 7, v_d_5041_);
lean_ctor_set(v_reuseFailAlloc_5076_, 8, v_Q_5042_);
lean_ctor_set(v_reuseFailAlloc_5076_, 9, v_q_5043_);
lean_ctor_set(v_reuseFailAlloc_5076_, 10, v_w_5044_);
lean_ctor_set(v_reuseFailAlloc_5076_, 11, v_W_5045_);
lean_ctor_set(v_reuseFailAlloc_5076_, 12, v_E_5046_);
lean_ctor_set(v_reuseFailAlloc_5076_, 13, v_e_5047_);
lean_ctor_set(v_reuseFailAlloc_5076_, 14, v_c_5048_);
lean_ctor_set(v_reuseFailAlloc_5076_, 15, v_F_5049_);
lean_ctor_set(v_reuseFailAlloc_5076_, 16, v_a_5050_);
lean_ctor_set(v_reuseFailAlloc_5076_, 17, v_b_5051_);
lean_ctor_set(v_reuseFailAlloc_5076_, 18, v___x_5073_);
lean_ctor_set(v_reuseFailAlloc_5076_, 19, v_h_5052_);
lean_ctor_set(v_reuseFailAlloc_5076_, 20, v_K_5053_);
lean_ctor_set(v_reuseFailAlloc_5076_, 21, v_k_5054_);
lean_ctor_set(v_reuseFailAlloc_5076_, 22, v_H_5055_);
lean_ctor_set(v_reuseFailAlloc_5076_, 23, v_m_5056_);
lean_ctor_set(v_reuseFailAlloc_5076_, 24, v_s_5057_);
lean_ctor_set(v_reuseFailAlloc_5076_, 25, v_S_5058_);
lean_ctor_set(v_reuseFailAlloc_5076_, 26, v_A_5059_);
lean_ctor_set(v_reuseFailAlloc_5076_, 27, v_n_5060_);
lean_ctor_set(v_reuseFailAlloc_5076_, 28, v_N_5061_);
lean_ctor_set(v_reuseFailAlloc_5076_, 29, v_V_5062_);
lean_ctor_set(v_reuseFailAlloc_5076_, 30, v_z_5063_);
lean_ctor_set(v_reuseFailAlloc_5076_, 31, v_zabbrev_5064_);
lean_ctor_set(v_reuseFailAlloc_5076_, 32, v_v_5065_);
lean_ctor_set(v_reuseFailAlloc_5076_, 33, v_O_5066_);
lean_ctor_set(v_reuseFailAlloc_5076_, 34, v_X_5067_);
lean_ctor_set(v_reuseFailAlloc_5076_, 35, v_x_5068_);
lean_ctor_set(v_reuseFailAlloc_5076_, 36, v_Z_5069_);
v___x_5075_ = v_reuseFailAlloc_5076_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
return v___x_5075_;
}
}
}
case 19:
{
lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5129_; 
v_isSharedCheck_5129_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_5129_ == 0)
{
lean_object* v_unused_5130_; 
v_unused_5130_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_5130_);
v___x_5080_ = v_modifier_4124_;
v_isShared_5081_ = v_isSharedCheck_5129_;
goto v_resetjp_5079_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5129_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
lean_object* v_G_5082_; lean_object* v_y_5083_; lean_object* v_u_5084_; lean_object* v_Y_5085_; lean_object* v_D_5086_; lean_object* v_M_5087_; lean_object* v_L_5088_; lean_object* v_d_5089_; lean_object* v_Q_5090_; lean_object* v_q_5091_; lean_object* v_w_5092_; lean_object* v_W_5093_; lean_object* v_E_5094_; lean_object* v_e_5095_; lean_object* v_c_5096_; lean_object* v_F_5097_; lean_object* v_a_5098_; lean_object* v_b_5099_; lean_object* v_B_5100_; lean_object* v_K_5101_; lean_object* v_k_5102_; lean_object* v_H_5103_; lean_object* v_m_5104_; lean_object* v_s_5105_; lean_object* v_S_5106_; lean_object* v_A_5107_; lean_object* v_n_5108_; lean_object* v_N_5109_; lean_object* v_V_5110_; lean_object* v_z_5111_; lean_object* v_zabbrev_5112_; lean_object* v_v_5113_; lean_object* v_O_5114_; lean_object* v_X_5115_; lean_object* v_x_5116_; lean_object* v_Z_5117_; lean_object* v___x_5119_; uint8_t v_isShared_5120_; uint8_t v_isSharedCheck_5127_; 
v_G_5082_ = lean_ctor_get(v_date_4123_, 0);
v_y_5083_ = lean_ctor_get(v_date_4123_, 1);
v_u_5084_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5085_ = lean_ctor_get(v_date_4123_, 3);
v_D_5086_ = lean_ctor_get(v_date_4123_, 4);
v_M_5087_ = lean_ctor_get(v_date_4123_, 5);
v_L_5088_ = lean_ctor_get(v_date_4123_, 6);
v_d_5089_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5090_ = lean_ctor_get(v_date_4123_, 8);
v_q_5091_ = lean_ctor_get(v_date_4123_, 9);
v_w_5092_ = lean_ctor_get(v_date_4123_, 10);
v_W_5093_ = lean_ctor_get(v_date_4123_, 11);
v_E_5094_ = lean_ctor_get(v_date_4123_, 12);
v_e_5095_ = lean_ctor_get(v_date_4123_, 13);
v_c_5096_ = lean_ctor_get(v_date_4123_, 14);
v_F_5097_ = lean_ctor_get(v_date_4123_, 15);
v_a_5098_ = lean_ctor_get(v_date_4123_, 16);
v_b_5099_ = lean_ctor_get(v_date_4123_, 17);
v_B_5100_ = lean_ctor_get(v_date_4123_, 18);
v_K_5101_ = lean_ctor_get(v_date_4123_, 20);
v_k_5102_ = lean_ctor_get(v_date_4123_, 21);
v_H_5103_ = lean_ctor_get(v_date_4123_, 22);
v_m_5104_ = lean_ctor_get(v_date_4123_, 23);
v_s_5105_ = lean_ctor_get(v_date_4123_, 24);
v_S_5106_ = lean_ctor_get(v_date_4123_, 25);
v_A_5107_ = lean_ctor_get(v_date_4123_, 26);
v_n_5108_ = lean_ctor_get(v_date_4123_, 27);
v_N_5109_ = lean_ctor_get(v_date_4123_, 28);
v_V_5110_ = lean_ctor_get(v_date_4123_, 29);
v_z_5111_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_5112_ = lean_ctor_get(v_date_4123_, 31);
v_v_5113_ = lean_ctor_get(v_date_4123_, 32);
v_O_5114_ = lean_ctor_get(v_date_4123_, 33);
v_X_5115_ = lean_ctor_get(v_date_4123_, 34);
v_x_5116_ = lean_ctor_get(v_date_4123_, 35);
v_Z_5117_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5127_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5127_ == 0)
{
lean_object* v_unused_5128_; 
v_unused_5128_ = lean_ctor_get(v_date_4123_, 19);
lean_dec(v_unused_5128_);
v___x_5119_ = v_date_4123_;
v_isShared_5120_ = v_isSharedCheck_5127_;
goto v_resetjp_5118_;
}
else
{
lean_inc(v_Z_5117_);
lean_inc(v_x_5116_);
lean_inc(v_X_5115_);
lean_inc(v_O_5114_);
lean_inc(v_v_5113_);
lean_inc(v_zabbrev_5112_);
lean_inc(v_z_5111_);
lean_inc(v_V_5110_);
lean_inc(v_N_5109_);
lean_inc(v_n_5108_);
lean_inc(v_A_5107_);
lean_inc(v_S_5106_);
lean_inc(v_s_5105_);
lean_inc(v_m_5104_);
lean_inc(v_H_5103_);
lean_inc(v_k_5102_);
lean_inc(v_K_5101_);
lean_inc(v_B_5100_);
lean_inc(v_b_5099_);
lean_inc(v_a_5098_);
lean_inc(v_F_5097_);
lean_inc(v_c_5096_);
lean_inc(v_e_5095_);
lean_inc(v_E_5094_);
lean_inc(v_W_5093_);
lean_inc(v_w_5092_);
lean_inc(v_q_5091_);
lean_inc(v_Q_5090_);
lean_inc(v_d_5089_);
lean_inc(v_L_5088_);
lean_inc(v_M_5087_);
lean_inc(v_D_5086_);
lean_inc(v_Y_5085_);
lean_inc(v_u_5084_);
lean_inc(v_y_5083_);
lean_inc(v_G_5082_);
lean_dec(v_date_4123_);
v___x_5119_ = lean_box(0);
v_isShared_5120_ = v_isSharedCheck_5127_;
goto v_resetjp_5118_;
}
v_resetjp_5118_:
{
lean_object* v___x_5122_; 
if (v_isShared_5081_ == 0)
{
lean_ctor_set_tag(v___x_5080_, 1);
lean_ctor_set(v___x_5080_, 0, v_data_4125_);
v___x_5122_ = v___x_5080_;
goto v_reusejp_5121_;
}
else
{
lean_object* v_reuseFailAlloc_5126_; 
v_reuseFailAlloc_5126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5126_, 0, v_data_4125_);
v___x_5122_ = v_reuseFailAlloc_5126_;
goto v_reusejp_5121_;
}
v_reusejp_5121_:
{
lean_object* v___x_5124_; 
if (v_isShared_5120_ == 0)
{
lean_ctor_set(v___x_5119_, 19, v___x_5122_);
v___x_5124_ = v___x_5119_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5125_; 
v_reuseFailAlloc_5125_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5125_, 0, v_G_5082_);
lean_ctor_set(v_reuseFailAlloc_5125_, 1, v_y_5083_);
lean_ctor_set(v_reuseFailAlloc_5125_, 2, v_u_5084_);
lean_ctor_set(v_reuseFailAlloc_5125_, 3, v_Y_5085_);
lean_ctor_set(v_reuseFailAlloc_5125_, 4, v_D_5086_);
lean_ctor_set(v_reuseFailAlloc_5125_, 5, v_M_5087_);
lean_ctor_set(v_reuseFailAlloc_5125_, 6, v_L_5088_);
lean_ctor_set(v_reuseFailAlloc_5125_, 7, v_d_5089_);
lean_ctor_set(v_reuseFailAlloc_5125_, 8, v_Q_5090_);
lean_ctor_set(v_reuseFailAlloc_5125_, 9, v_q_5091_);
lean_ctor_set(v_reuseFailAlloc_5125_, 10, v_w_5092_);
lean_ctor_set(v_reuseFailAlloc_5125_, 11, v_W_5093_);
lean_ctor_set(v_reuseFailAlloc_5125_, 12, v_E_5094_);
lean_ctor_set(v_reuseFailAlloc_5125_, 13, v_e_5095_);
lean_ctor_set(v_reuseFailAlloc_5125_, 14, v_c_5096_);
lean_ctor_set(v_reuseFailAlloc_5125_, 15, v_F_5097_);
lean_ctor_set(v_reuseFailAlloc_5125_, 16, v_a_5098_);
lean_ctor_set(v_reuseFailAlloc_5125_, 17, v_b_5099_);
lean_ctor_set(v_reuseFailAlloc_5125_, 18, v_B_5100_);
lean_ctor_set(v_reuseFailAlloc_5125_, 19, v___x_5122_);
lean_ctor_set(v_reuseFailAlloc_5125_, 20, v_K_5101_);
lean_ctor_set(v_reuseFailAlloc_5125_, 21, v_k_5102_);
lean_ctor_set(v_reuseFailAlloc_5125_, 22, v_H_5103_);
lean_ctor_set(v_reuseFailAlloc_5125_, 23, v_m_5104_);
lean_ctor_set(v_reuseFailAlloc_5125_, 24, v_s_5105_);
lean_ctor_set(v_reuseFailAlloc_5125_, 25, v_S_5106_);
lean_ctor_set(v_reuseFailAlloc_5125_, 26, v_A_5107_);
lean_ctor_set(v_reuseFailAlloc_5125_, 27, v_n_5108_);
lean_ctor_set(v_reuseFailAlloc_5125_, 28, v_N_5109_);
lean_ctor_set(v_reuseFailAlloc_5125_, 29, v_V_5110_);
lean_ctor_set(v_reuseFailAlloc_5125_, 30, v_z_5111_);
lean_ctor_set(v_reuseFailAlloc_5125_, 31, v_zabbrev_5112_);
lean_ctor_set(v_reuseFailAlloc_5125_, 32, v_v_5113_);
lean_ctor_set(v_reuseFailAlloc_5125_, 33, v_O_5114_);
lean_ctor_set(v_reuseFailAlloc_5125_, 34, v_X_5115_);
lean_ctor_set(v_reuseFailAlloc_5125_, 35, v_x_5116_);
lean_ctor_set(v_reuseFailAlloc_5125_, 36, v_Z_5117_);
v___x_5124_ = v_reuseFailAlloc_5125_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
return v___x_5124_;
}
}
}
}
}
case 20:
{
lean_object* v___x_5132_; uint8_t v_isShared_5133_; uint8_t v_isSharedCheck_5181_; 
v_isSharedCheck_5181_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_5181_ == 0)
{
lean_object* v_unused_5182_; 
v_unused_5182_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_5182_);
v___x_5132_ = v_modifier_4124_;
v_isShared_5133_ = v_isSharedCheck_5181_;
goto v_resetjp_5131_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_5132_ = lean_box(0);
v_isShared_5133_ = v_isSharedCheck_5181_;
goto v_resetjp_5131_;
}
v_resetjp_5131_:
{
lean_object* v_G_5134_; lean_object* v_y_5135_; lean_object* v_u_5136_; lean_object* v_Y_5137_; lean_object* v_D_5138_; lean_object* v_M_5139_; lean_object* v_L_5140_; lean_object* v_d_5141_; lean_object* v_Q_5142_; lean_object* v_q_5143_; lean_object* v_w_5144_; lean_object* v_W_5145_; lean_object* v_E_5146_; lean_object* v_e_5147_; lean_object* v_c_5148_; lean_object* v_F_5149_; lean_object* v_a_5150_; lean_object* v_b_5151_; lean_object* v_B_5152_; lean_object* v_h_5153_; lean_object* v_k_5154_; lean_object* v_H_5155_; lean_object* v_m_5156_; lean_object* v_s_5157_; lean_object* v_S_5158_; lean_object* v_A_5159_; lean_object* v_n_5160_; lean_object* v_N_5161_; lean_object* v_V_5162_; lean_object* v_z_5163_; lean_object* v_zabbrev_5164_; lean_object* v_v_5165_; lean_object* v_O_5166_; lean_object* v_X_5167_; lean_object* v_x_5168_; lean_object* v_Z_5169_; lean_object* v___x_5171_; uint8_t v_isShared_5172_; uint8_t v_isSharedCheck_5179_; 
v_G_5134_ = lean_ctor_get(v_date_4123_, 0);
v_y_5135_ = lean_ctor_get(v_date_4123_, 1);
v_u_5136_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5137_ = lean_ctor_get(v_date_4123_, 3);
v_D_5138_ = lean_ctor_get(v_date_4123_, 4);
v_M_5139_ = lean_ctor_get(v_date_4123_, 5);
v_L_5140_ = lean_ctor_get(v_date_4123_, 6);
v_d_5141_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5142_ = lean_ctor_get(v_date_4123_, 8);
v_q_5143_ = lean_ctor_get(v_date_4123_, 9);
v_w_5144_ = lean_ctor_get(v_date_4123_, 10);
v_W_5145_ = lean_ctor_get(v_date_4123_, 11);
v_E_5146_ = lean_ctor_get(v_date_4123_, 12);
v_e_5147_ = lean_ctor_get(v_date_4123_, 13);
v_c_5148_ = lean_ctor_get(v_date_4123_, 14);
v_F_5149_ = lean_ctor_get(v_date_4123_, 15);
v_a_5150_ = lean_ctor_get(v_date_4123_, 16);
v_b_5151_ = lean_ctor_get(v_date_4123_, 17);
v_B_5152_ = lean_ctor_get(v_date_4123_, 18);
v_h_5153_ = lean_ctor_get(v_date_4123_, 19);
v_k_5154_ = lean_ctor_get(v_date_4123_, 21);
v_H_5155_ = lean_ctor_get(v_date_4123_, 22);
v_m_5156_ = lean_ctor_get(v_date_4123_, 23);
v_s_5157_ = lean_ctor_get(v_date_4123_, 24);
v_S_5158_ = lean_ctor_get(v_date_4123_, 25);
v_A_5159_ = lean_ctor_get(v_date_4123_, 26);
v_n_5160_ = lean_ctor_get(v_date_4123_, 27);
v_N_5161_ = lean_ctor_get(v_date_4123_, 28);
v_V_5162_ = lean_ctor_get(v_date_4123_, 29);
v_z_5163_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_5164_ = lean_ctor_get(v_date_4123_, 31);
v_v_5165_ = lean_ctor_get(v_date_4123_, 32);
v_O_5166_ = lean_ctor_get(v_date_4123_, 33);
v_X_5167_ = lean_ctor_get(v_date_4123_, 34);
v_x_5168_ = lean_ctor_get(v_date_4123_, 35);
v_Z_5169_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5179_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5179_ == 0)
{
lean_object* v_unused_5180_; 
v_unused_5180_ = lean_ctor_get(v_date_4123_, 20);
lean_dec(v_unused_5180_);
v___x_5171_ = v_date_4123_;
v_isShared_5172_ = v_isSharedCheck_5179_;
goto v_resetjp_5170_;
}
else
{
lean_inc(v_Z_5169_);
lean_inc(v_x_5168_);
lean_inc(v_X_5167_);
lean_inc(v_O_5166_);
lean_inc(v_v_5165_);
lean_inc(v_zabbrev_5164_);
lean_inc(v_z_5163_);
lean_inc(v_V_5162_);
lean_inc(v_N_5161_);
lean_inc(v_n_5160_);
lean_inc(v_A_5159_);
lean_inc(v_S_5158_);
lean_inc(v_s_5157_);
lean_inc(v_m_5156_);
lean_inc(v_H_5155_);
lean_inc(v_k_5154_);
lean_inc(v_h_5153_);
lean_inc(v_B_5152_);
lean_inc(v_b_5151_);
lean_inc(v_a_5150_);
lean_inc(v_F_5149_);
lean_inc(v_c_5148_);
lean_inc(v_e_5147_);
lean_inc(v_E_5146_);
lean_inc(v_W_5145_);
lean_inc(v_w_5144_);
lean_inc(v_q_5143_);
lean_inc(v_Q_5142_);
lean_inc(v_d_5141_);
lean_inc(v_L_5140_);
lean_inc(v_M_5139_);
lean_inc(v_D_5138_);
lean_inc(v_Y_5137_);
lean_inc(v_u_5136_);
lean_inc(v_y_5135_);
lean_inc(v_G_5134_);
lean_dec(v_date_4123_);
v___x_5171_ = lean_box(0);
v_isShared_5172_ = v_isSharedCheck_5179_;
goto v_resetjp_5170_;
}
v_resetjp_5170_:
{
lean_object* v___x_5174_; 
if (v_isShared_5133_ == 0)
{
lean_ctor_set_tag(v___x_5132_, 1);
lean_ctor_set(v___x_5132_, 0, v_data_4125_);
v___x_5174_ = v___x_5132_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v_data_4125_);
v___x_5174_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
lean_object* v___x_5176_; 
if (v_isShared_5172_ == 0)
{
lean_ctor_set(v___x_5171_, 20, v___x_5174_);
v___x_5176_ = v___x_5171_;
goto v_reusejp_5175_;
}
else
{
lean_object* v_reuseFailAlloc_5177_; 
v_reuseFailAlloc_5177_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5177_, 0, v_G_5134_);
lean_ctor_set(v_reuseFailAlloc_5177_, 1, v_y_5135_);
lean_ctor_set(v_reuseFailAlloc_5177_, 2, v_u_5136_);
lean_ctor_set(v_reuseFailAlloc_5177_, 3, v_Y_5137_);
lean_ctor_set(v_reuseFailAlloc_5177_, 4, v_D_5138_);
lean_ctor_set(v_reuseFailAlloc_5177_, 5, v_M_5139_);
lean_ctor_set(v_reuseFailAlloc_5177_, 6, v_L_5140_);
lean_ctor_set(v_reuseFailAlloc_5177_, 7, v_d_5141_);
lean_ctor_set(v_reuseFailAlloc_5177_, 8, v_Q_5142_);
lean_ctor_set(v_reuseFailAlloc_5177_, 9, v_q_5143_);
lean_ctor_set(v_reuseFailAlloc_5177_, 10, v_w_5144_);
lean_ctor_set(v_reuseFailAlloc_5177_, 11, v_W_5145_);
lean_ctor_set(v_reuseFailAlloc_5177_, 12, v_E_5146_);
lean_ctor_set(v_reuseFailAlloc_5177_, 13, v_e_5147_);
lean_ctor_set(v_reuseFailAlloc_5177_, 14, v_c_5148_);
lean_ctor_set(v_reuseFailAlloc_5177_, 15, v_F_5149_);
lean_ctor_set(v_reuseFailAlloc_5177_, 16, v_a_5150_);
lean_ctor_set(v_reuseFailAlloc_5177_, 17, v_b_5151_);
lean_ctor_set(v_reuseFailAlloc_5177_, 18, v_B_5152_);
lean_ctor_set(v_reuseFailAlloc_5177_, 19, v_h_5153_);
lean_ctor_set(v_reuseFailAlloc_5177_, 20, v___x_5174_);
lean_ctor_set(v_reuseFailAlloc_5177_, 21, v_k_5154_);
lean_ctor_set(v_reuseFailAlloc_5177_, 22, v_H_5155_);
lean_ctor_set(v_reuseFailAlloc_5177_, 23, v_m_5156_);
lean_ctor_set(v_reuseFailAlloc_5177_, 24, v_s_5157_);
lean_ctor_set(v_reuseFailAlloc_5177_, 25, v_S_5158_);
lean_ctor_set(v_reuseFailAlloc_5177_, 26, v_A_5159_);
lean_ctor_set(v_reuseFailAlloc_5177_, 27, v_n_5160_);
lean_ctor_set(v_reuseFailAlloc_5177_, 28, v_N_5161_);
lean_ctor_set(v_reuseFailAlloc_5177_, 29, v_V_5162_);
lean_ctor_set(v_reuseFailAlloc_5177_, 30, v_z_5163_);
lean_ctor_set(v_reuseFailAlloc_5177_, 31, v_zabbrev_5164_);
lean_ctor_set(v_reuseFailAlloc_5177_, 32, v_v_5165_);
lean_ctor_set(v_reuseFailAlloc_5177_, 33, v_O_5166_);
lean_ctor_set(v_reuseFailAlloc_5177_, 34, v_X_5167_);
lean_ctor_set(v_reuseFailAlloc_5177_, 35, v_x_5168_);
lean_ctor_set(v_reuseFailAlloc_5177_, 36, v_Z_5169_);
v___x_5176_ = v_reuseFailAlloc_5177_;
goto v_reusejp_5175_;
}
v_reusejp_5175_:
{
return v___x_5176_;
}
}
}
}
}
case 21:
{
lean_object* v___x_5184_; uint8_t v_isShared_5185_; uint8_t v_isSharedCheck_5233_; 
v_isSharedCheck_5233_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_5233_ == 0)
{
lean_object* v_unused_5234_; 
v_unused_5234_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_5234_);
v___x_5184_ = v_modifier_4124_;
v_isShared_5185_ = v_isSharedCheck_5233_;
goto v_resetjp_5183_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_5184_ = lean_box(0);
v_isShared_5185_ = v_isSharedCheck_5233_;
goto v_resetjp_5183_;
}
v_resetjp_5183_:
{
lean_object* v_G_5186_; lean_object* v_y_5187_; lean_object* v_u_5188_; lean_object* v_Y_5189_; lean_object* v_D_5190_; lean_object* v_M_5191_; lean_object* v_L_5192_; lean_object* v_d_5193_; lean_object* v_Q_5194_; lean_object* v_q_5195_; lean_object* v_w_5196_; lean_object* v_W_5197_; lean_object* v_E_5198_; lean_object* v_e_5199_; lean_object* v_c_5200_; lean_object* v_F_5201_; lean_object* v_a_5202_; lean_object* v_b_5203_; lean_object* v_B_5204_; lean_object* v_h_5205_; lean_object* v_K_5206_; lean_object* v_H_5207_; lean_object* v_m_5208_; lean_object* v_s_5209_; lean_object* v_S_5210_; lean_object* v_A_5211_; lean_object* v_n_5212_; lean_object* v_N_5213_; lean_object* v_V_5214_; lean_object* v_z_5215_; lean_object* v_zabbrev_5216_; lean_object* v_v_5217_; lean_object* v_O_5218_; lean_object* v_X_5219_; lean_object* v_x_5220_; lean_object* v_Z_5221_; lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5231_; 
v_G_5186_ = lean_ctor_get(v_date_4123_, 0);
v_y_5187_ = lean_ctor_get(v_date_4123_, 1);
v_u_5188_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5189_ = lean_ctor_get(v_date_4123_, 3);
v_D_5190_ = lean_ctor_get(v_date_4123_, 4);
v_M_5191_ = lean_ctor_get(v_date_4123_, 5);
v_L_5192_ = lean_ctor_get(v_date_4123_, 6);
v_d_5193_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5194_ = lean_ctor_get(v_date_4123_, 8);
v_q_5195_ = lean_ctor_get(v_date_4123_, 9);
v_w_5196_ = lean_ctor_get(v_date_4123_, 10);
v_W_5197_ = lean_ctor_get(v_date_4123_, 11);
v_E_5198_ = lean_ctor_get(v_date_4123_, 12);
v_e_5199_ = lean_ctor_get(v_date_4123_, 13);
v_c_5200_ = lean_ctor_get(v_date_4123_, 14);
v_F_5201_ = lean_ctor_get(v_date_4123_, 15);
v_a_5202_ = lean_ctor_get(v_date_4123_, 16);
v_b_5203_ = lean_ctor_get(v_date_4123_, 17);
v_B_5204_ = lean_ctor_get(v_date_4123_, 18);
v_h_5205_ = lean_ctor_get(v_date_4123_, 19);
v_K_5206_ = lean_ctor_get(v_date_4123_, 20);
v_H_5207_ = lean_ctor_get(v_date_4123_, 22);
v_m_5208_ = lean_ctor_get(v_date_4123_, 23);
v_s_5209_ = lean_ctor_get(v_date_4123_, 24);
v_S_5210_ = lean_ctor_get(v_date_4123_, 25);
v_A_5211_ = lean_ctor_get(v_date_4123_, 26);
v_n_5212_ = lean_ctor_get(v_date_4123_, 27);
v_N_5213_ = lean_ctor_get(v_date_4123_, 28);
v_V_5214_ = lean_ctor_get(v_date_4123_, 29);
v_z_5215_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_5216_ = lean_ctor_get(v_date_4123_, 31);
v_v_5217_ = lean_ctor_get(v_date_4123_, 32);
v_O_5218_ = lean_ctor_get(v_date_4123_, 33);
v_X_5219_ = lean_ctor_get(v_date_4123_, 34);
v_x_5220_ = lean_ctor_get(v_date_4123_, 35);
v_Z_5221_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5231_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5231_ == 0)
{
lean_object* v_unused_5232_; 
v_unused_5232_ = lean_ctor_get(v_date_4123_, 21);
lean_dec(v_unused_5232_);
v___x_5223_ = v_date_4123_;
v_isShared_5224_ = v_isSharedCheck_5231_;
goto v_resetjp_5222_;
}
else
{
lean_inc(v_Z_5221_);
lean_inc(v_x_5220_);
lean_inc(v_X_5219_);
lean_inc(v_O_5218_);
lean_inc(v_v_5217_);
lean_inc(v_zabbrev_5216_);
lean_inc(v_z_5215_);
lean_inc(v_V_5214_);
lean_inc(v_N_5213_);
lean_inc(v_n_5212_);
lean_inc(v_A_5211_);
lean_inc(v_S_5210_);
lean_inc(v_s_5209_);
lean_inc(v_m_5208_);
lean_inc(v_H_5207_);
lean_inc(v_K_5206_);
lean_inc(v_h_5205_);
lean_inc(v_B_5204_);
lean_inc(v_b_5203_);
lean_inc(v_a_5202_);
lean_inc(v_F_5201_);
lean_inc(v_c_5200_);
lean_inc(v_e_5199_);
lean_inc(v_E_5198_);
lean_inc(v_W_5197_);
lean_inc(v_w_5196_);
lean_inc(v_q_5195_);
lean_inc(v_Q_5194_);
lean_inc(v_d_5193_);
lean_inc(v_L_5192_);
lean_inc(v_M_5191_);
lean_inc(v_D_5190_);
lean_inc(v_Y_5189_);
lean_inc(v_u_5188_);
lean_inc(v_y_5187_);
lean_inc(v_G_5186_);
lean_dec(v_date_4123_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5231_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
lean_object* v___x_5226_; 
if (v_isShared_5185_ == 0)
{
lean_ctor_set_tag(v___x_5184_, 1);
lean_ctor_set(v___x_5184_, 0, v_data_4125_);
v___x_5226_ = v___x_5184_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v_data_4125_);
v___x_5226_ = v_reuseFailAlloc_5230_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
lean_object* v___x_5228_; 
if (v_isShared_5224_ == 0)
{
lean_ctor_set(v___x_5223_, 21, v___x_5226_);
v___x_5228_ = v___x_5223_;
goto v_reusejp_5227_;
}
else
{
lean_object* v_reuseFailAlloc_5229_; 
v_reuseFailAlloc_5229_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5229_, 0, v_G_5186_);
lean_ctor_set(v_reuseFailAlloc_5229_, 1, v_y_5187_);
lean_ctor_set(v_reuseFailAlloc_5229_, 2, v_u_5188_);
lean_ctor_set(v_reuseFailAlloc_5229_, 3, v_Y_5189_);
lean_ctor_set(v_reuseFailAlloc_5229_, 4, v_D_5190_);
lean_ctor_set(v_reuseFailAlloc_5229_, 5, v_M_5191_);
lean_ctor_set(v_reuseFailAlloc_5229_, 6, v_L_5192_);
lean_ctor_set(v_reuseFailAlloc_5229_, 7, v_d_5193_);
lean_ctor_set(v_reuseFailAlloc_5229_, 8, v_Q_5194_);
lean_ctor_set(v_reuseFailAlloc_5229_, 9, v_q_5195_);
lean_ctor_set(v_reuseFailAlloc_5229_, 10, v_w_5196_);
lean_ctor_set(v_reuseFailAlloc_5229_, 11, v_W_5197_);
lean_ctor_set(v_reuseFailAlloc_5229_, 12, v_E_5198_);
lean_ctor_set(v_reuseFailAlloc_5229_, 13, v_e_5199_);
lean_ctor_set(v_reuseFailAlloc_5229_, 14, v_c_5200_);
lean_ctor_set(v_reuseFailAlloc_5229_, 15, v_F_5201_);
lean_ctor_set(v_reuseFailAlloc_5229_, 16, v_a_5202_);
lean_ctor_set(v_reuseFailAlloc_5229_, 17, v_b_5203_);
lean_ctor_set(v_reuseFailAlloc_5229_, 18, v_B_5204_);
lean_ctor_set(v_reuseFailAlloc_5229_, 19, v_h_5205_);
lean_ctor_set(v_reuseFailAlloc_5229_, 20, v_K_5206_);
lean_ctor_set(v_reuseFailAlloc_5229_, 21, v___x_5226_);
lean_ctor_set(v_reuseFailAlloc_5229_, 22, v_H_5207_);
lean_ctor_set(v_reuseFailAlloc_5229_, 23, v_m_5208_);
lean_ctor_set(v_reuseFailAlloc_5229_, 24, v_s_5209_);
lean_ctor_set(v_reuseFailAlloc_5229_, 25, v_S_5210_);
lean_ctor_set(v_reuseFailAlloc_5229_, 26, v_A_5211_);
lean_ctor_set(v_reuseFailAlloc_5229_, 27, v_n_5212_);
lean_ctor_set(v_reuseFailAlloc_5229_, 28, v_N_5213_);
lean_ctor_set(v_reuseFailAlloc_5229_, 29, v_V_5214_);
lean_ctor_set(v_reuseFailAlloc_5229_, 30, v_z_5215_);
lean_ctor_set(v_reuseFailAlloc_5229_, 31, v_zabbrev_5216_);
lean_ctor_set(v_reuseFailAlloc_5229_, 32, v_v_5217_);
lean_ctor_set(v_reuseFailAlloc_5229_, 33, v_O_5218_);
lean_ctor_set(v_reuseFailAlloc_5229_, 34, v_X_5219_);
lean_ctor_set(v_reuseFailAlloc_5229_, 35, v_x_5220_);
lean_ctor_set(v_reuseFailAlloc_5229_, 36, v_Z_5221_);
v___x_5228_ = v_reuseFailAlloc_5229_;
goto v_reusejp_5227_;
}
v_reusejp_5227_:
{
return v___x_5228_;
}
}
}
}
}
case 22:
{
lean_object* v___x_5236_; uint8_t v_isShared_5237_; uint8_t v_isSharedCheck_5285_; 
v_isSharedCheck_5285_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_5285_ == 0)
{
lean_object* v_unused_5286_; 
v_unused_5286_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_5286_);
v___x_5236_ = v_modifier_4124_;
v_isShared_5237_ = v_isSharedCheck_5285_;
goto v_resetjp_5235_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_5236_ = lean_box(0);
v_isShared_5237_ = v_isSharedCheck_5285_;
goto v_resetjp_5235_;
}
v_resetjp_5235_:
{
lean_object* v_G_5238_; lean_object* v_y_5239_; lean_object* v_u_5240_; lean_object* v_Y_5241_; lean_object* v_D_5242_; lean_object* v_M_5243_; lean_object* v_L_5244_; lean_object* v_d_5245_; lean_object* v_Q_5246_; lean_object* v_q_5247_; lean_object* v_w_5248_; lean_object* v_W_5249_; lean_object* v_E_5250_; lean_object* v_e_5251_; lean_object* v_c_5252_; lean_object* v_F_5253_; lean_object* v_a_5254_; lean_object* v_b_5255_; lean_object* v_B_5256_; lean_object* v_h_5257_; lean_object* v_K_5258_; lean_object* v_k_5259_; lean_object* v_m_5260_; lean_object* v_s_5261_; lean_object* v_S_5262_; lean_object* v_A_5263_; lean_object* v_n_5264_; lean_object* v_N_5265_; lean_object* v_V_5266_; lean_object* v_z_5267_; lean_object* v_zabbrev_5268_; lean_object* v_v_5269_; lean_object* v_O_5270_; lean_object* v_X_5271_; lean_object* v_x_5272_; lean_object* v_Z_5273_; lean_object* v___x_5275_; uint8_t v_isShared_5276_; uint8_t v_isSharedCheck_5283_; 
v_G_5238_ = lean_ctor_get(v_date_4123_, 0);
v_y_5239_ = lean_ctor_get(v_date_4123_, 1);
v_u_5240_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5241_ = lean_ctor_get(v_date_4123_, 3);
v_D_5242_ = lean_ctor_get(v_date_4123_, 4);
v_M_5243_ = lean_ctor_get(v_date_4123_, 5);
v_L_5244_ = lean_ctor_get(v_date_4123_, 6);
v_d_5245_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5246_ = lean_ctor_get(v_date_4123_, 8);
v_q_5247_ = lean_ctor_get(v_date_4123_, 9);
v_w_5248_ = lean_ctor_get(v_date_4123_, 10);
v_W_5249_ = lean_ctor_get(v_date_4123_, 11);
v_E_5250_ = lean_ctor_get(v_date_4123_, 12);
v_e_5251_ = lean_ctor_get(v_date_4123_, 13);
v_c_5252_ = lean_ctor_get(v_date_4123_, 14);
v_F_5253_ = lean_ctor_get(v_date_4123_, 15);
v_a_5254_ = lean_ctor_get(v_date_4123_, 16);
v_b_5255_ = lean_ctor_get(v_date_4123_, 17);
v_B_5256_ = lean_ctor_get(v_date_4123_, 18);
v_h_5257_ = lean_ctor_get(v_date_4123_, 19);
v_K_5258_ = lean_ctor_get(v_date_4123_, 20);
v_k_5259_ = lean_ctor_get(v_date_4123_, 21);
v_m_5260_ = lean_ctor_get(v_date_4123_, 23);
v_s_5261_ = lean_ctor_get(v_date_4123_, 24);
v_S_5262_ = lean_ctor_get(v_date_4123_, 25);
v_A_5263_ = lean_ctor_get(v_date_4123_, 26);
v_n_5264_ = lean_ctor_get(v_date_4123_, 27);
v_N_5265_ = lean_ctor_get(v_date_4123_, 28);
v_V_5266_ = lean_ctor_get(v_date_4123_, 29);
v_z_5267_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_5268_ = lean_ctor_get(v_date_4123_, 31);
v_v_5269_ = lean_ctor_get(v_date_4123_, 32);
v_O_5270_ = lean_ctor_get(v_date_4123_, 33);
v_X_5271_ = lean_ctor_get(v_date_4123_, 34);
v_x_5272_ = lean_ctor_get(v_date_4123_, 35);
v_Z_5273_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5283_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5283_ == 0)
{
lean_object* v_unused_5284_; 
v_unused_5284_ = lean_ctor_get(v_date_4123_, 22);
lean_dec(v_unused_5284_);
v___x_5275_ = v_date_4123_;
v_isShared_5276_ = v_isSharedCheck_5283_;
goto v_resetjp_5274_;
}
else
{
lean_inc(v_Z_5273_);
lean_inc(v_x_5272_);
lean_inc(v_X_5271_);
lean_inc(v_O_5270_);
lean_inc(v_v_5269_);
lean_inc(v_zabbrev_5268_);
lean_inc(v_z_5267_);
lean_inc(v_V_5266_);
lean_inc(v_N_5265_);
lean_inc(v_n_5264_);
lean_inc(v_A_5263_);
lean_inc(v_S_5262_);
lean_inc(v_s_5261_);
lean_inc(v_m_5260_);
lean_inc(v_k_5259_);
lean_inc(v_K_5258_);
lean_inc(v_h_5257_);
lean_inc(v_B_5256_);
lean_inc(v_b_5255_);
lean_inc(v_a_5254_);
lean_inc(v_F_5253_);
lean_inc(v_c_5252_);
lean_inc(v_e_5251_);
lean_inc(v_E_5250_);
lean_inc(v_W_5249_);
lean_inc(v_w_5248_);
lean_inc(v_q_5247_);
lean_inc(v_Q_5246_);
lean_inc(v_d_5245_);
lean_inc(v_L_5244_);
lean_inc(v_M_5243_);
lean_inc(v_D_5242_);
lean_inc(v_Y_5241_);
lean_inc(v_u_5240_);
lean_inc(v_y_5239_);
lean_inc(v_G_5238_);
lean_dec(v_date_4123_);
v___x_5275_ = lean_box(0);
v_isShared_5276_ = v_isSharedCheck_5283_;
goto v_resetjp_5274_;
}
v_resetjp_5274_:
{
lean_object* v___x_5278_; 
if (v_isShared_5237_ == 0)
{
lean_ctor_set_tag(v___x_5236_, 1);
lean_ctor_set(v___x_5236_, 0, v_data_4125_);
v___x_5278_ = v___x_5236_;
goto v_reusejp_5277_;
}
else
{
lean_object* v_reuseFailAlloc_5282_; 
v_reuseFailAlloc_5282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5282_, 0, v_data_4125_);
v___x_5278_ = v_reuseFailAlloc_5282_;
goto v_reusejp_5277_;
}
v_reusejp_5277_:
{
lean_object* v___x_5280_; 
if (v_isShared_5276_ == 0)
{
lean_ctor_set(v___x_5275_, 22, v___x_5278_);
v___x_5280_ = v___x_5275_;
goto v_reusejp_5279_;
}
else
{
lean_object* v_reuseFailAlloc_5281_; 
v_reuseFailAlloc_5281_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5281_, 0, v_G_5238_);
lean_ctor_set(v_reuseFailAlloc_5281_, 1, v_y_5239_);
lean_ctor_set(v_reuseFailAlloc_5281_, 2, v_u_5240_);
lean_ctor_set(v_reuseFailAlloc_5281_, 3, v_Y_5241_);
lean_ctor_set(v_reuseFailAlloc_5281_, 4, v_D_5242_);
lean_ctor_set(v_reuseFailAlloc_5281_, 5, v_M_5243_);
lean_ctor_set(v_reuseFailAlloc_5281_, 6, v_L_5244_);
lean_ctor_set(v_reuseFailAlloc_5281_, 7, v_d_5245_);
lean_ctor_set(v_reuseFailAlloc_5281_, 8, v_Q_5246_);
lean_ctor_set(v_reuseFailAlloc_5281_, 9, v_q_5247_);
lean_ctor_set(v_reuseFailAlloc_5281_, 10, v_w_5248_);
lean_ctor_set(v_reuseFailAlloc_5281_, 11, v_W_5249_);
lean_ctor_set(v_reuseFailAlloc_5281_, 12, v_E_5250_);
lean_ctor_set(v_reuseFailAlloc_5281_, 13, v_e_5251_);
lean_ctor_set(v_reuseFailAlloc_5281_, 14, v_c_5252_);
lean_ctor_set(v_reuseFailAlloc_5281_, 15, v_F_5253_);
lean_ctor_set(v_reuseFailAlloc_5281_, 16, v_a_5254_);
lean_ctor_set(v_reuseFailAlloc_5281_, 17, v_b_5255_);
lean_ctor_set(v_reuseFailAlloc_5281_, 18, v_B_5256_);
lean_ctor_set(v_reuseFailAlloc_5281_, 19, v_h_5257_);
lean_ctor_set(v_reuseFailAlloc_5281_, 20, v_K_5258_);
lean_ctor_set(v_reuseFailAlloc_5281_, 21, v_k_5259_);
lean_ctor_set(v_reuseFailAlloc_5281_, 22, v___x_5278_);
lean_ctor_set(v_reuseFailAlloc_5281_, 23, v_m_5260_);
lean_ctor_set(v_reuseFailAlloc_5281_, 24, v_s_5261_);
lean_ctor_set(v_reuseFailAlloc_5281_, 25, v_S_5262_);
lean_ctor_set(v_reuseFailAlloc_5281_, 26, v_A_5263_);
lean_ctor_set(v_reuseFailAlloc_5281_, 27, v_n_5264_);
lean_ctor_set(v_reuseFailAlloc_5281_, 28, v_N_5265_);
lean_ctor_set(v_reuseFailAlloc_5281_, 29, v_V_5266_);
lean_ctor_set(v_reuseFailAlloc_5281_, 30, v_z_5267_);
lean_ctor_set(v_reuseFailAlloc_5281_, 31, v_zabbrev_5268_);
lean_ctor_set(v_reuseFailAlloc_5281_, 32, v_v_5269_);
lean_ctor_set(v_reuseFailAlloc_5281_, 33, v_O_5270_);
lean_ctor_set(v_reuseFailAlloc_5281_, 34, v_X_5271_);
lean_ctor_set(v_reuseFailAlloc_5281_, 35, v_x_5272_);
lean_ctor_set(v_reuseFailAlloc_5281_, 36, v_Z_5273_);
v___x_5280_ = v_reuseFailAlloc_5281_;
goto v_reusejp_5279_;
}
v_reusejp_5279_:
{
return v___x_5280_;
}
}
}
}
}
case 23:
{
lean_object* v___x_5288_; uint8_t v_isShared_5289_; uint8_t v_isSharedCheck_5337_; 
v_isSharedCheck_5337_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_5337_ == 0)
{
lean_object* v_unused_5338_; 
v_unused_5338_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_5338_);
v___x_5288_ = v_modifier_4124_;
v_isShared_5289_ = v_isSharedCheck_5337_;
goto v_resetjp_5287_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_5288_ = lean_box(0);
v_isShared_5289_ = v_isSharedCheck_5337_;
goto v_resetjp_5287_;
}
v_resetjp_5287_:
{
lean_object* v_G_5290_; lean_object* v_y_5291_; lean_object* v_u_5292_; lean_object* v_Y_5293_; lean_object* v_D_5294_; lean_object* v_M_5295_; lean_object* v_L_5296_; lean_object* v_d_5297_; lean_object* v_Q_5298_; lean_object* v_q_5299_; lean_object* v_w_5300_; lean_object* v_W_5301_; lean_object* v_E_5302_; lean_object* v_e_5303_; lean_object* v_c_5304_; lean_object* v_F_5305_; lean_object* v_a_5306_; lean_object* v_b_5307_; lean_object* v_B_5308_; lean_object* v_h_5309_; lean_object* v_K_5310_; lean_object* v_k_5311_; lean_object* v_H_5312_; lean_object* v_s_5313_; lean_object* v_S_5314_; lean_object* v_A_5315_; lean_object* v_n_5316_; lean_object* v_N_5317_; lean_object* v_V_5318_; lean_object* v_z_5319_; lean_object* v_zabbrev_5320_; lean_object* v_v_5321_; lean_object* v_O_5322_; lean_object* v_X_5323_; lean_object* v_x_5324_; lean_object* v_Z_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5335_; 
v_G_5290_ = lean_ctor_get(v_date_4123_, 0);
v_y_5291_ = lean_ctor_get(v_date_4123_, 1);
v_u_5292_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5293_ = lean_ctor_get(v_date_4123_, 3);
v_D_5294_ = lean_ctor_get(v_date_4123_, 4);
v_M_5295_ = lean_ctor_get(v_date_4123_, 5);
v_L_5296_ = lean_ctor_get(v_date_4123_, 6);
v_d_5297_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5298_ = lean_ctor_get(v_date_4123_, 8);
v_q_5299_ = lean_ctor_get(v_date_4123_, 9);
v_w_5300_ = lean_ctor_get(v_date_4123_, 10);
v_W_5301_ = lean_ctor_get(v_date_4123_, 11);
v_E_5302_ = lean_ctor_get(v_date_4123_, 12);
v_e_5303_ = lean_ctor_get(v_date_4123_, 13);
v_c_5304_ = lean_ctor_get(v_date_4123_, 14);
v_F_5305_ = lean_ctor_get(v_date_4123_, 15);
v_a_5306_ = lean_ctor_get(v_date_4123_, 16);
v_b_5307_ = lean_ctor_get(v_date_4123_, 17);
v_B_5308_ = lean_ctor_get(v_date_4123_, 18);
v_h_5309_ = lean_ctor_get(v_date_4123_, 19);
v_K_5310_ = lean_ctor_get(v_date_4123_, 20);
v_k_5311_ = lean_ctor_get(v_date_4123_, 21);
v_H_5312_ = lean_ctor_get(v_date_4123_, 22);
v_s_5313_ = lean_ctor_get(v_date_4123_, 24);
v_S_5314_ = lean_ctor_get(v_date_4123_, 25);
v_A_5315_ = lean_ctor_get(v_date_4123_, 26);
v_n_5316_ = lean_ctor_get(v_date_4123_, 27);
v_N_5317_ = lean_ctor_get(v_date_4123_, 28);
v_V_5318_ = lean_ctor_get(v_date_4123_, 29);
v_z_5319_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_5320_ = lean_ctor_get(v_date_4123_, 31);
v_v_5321_ = lean_ctor_get(v_date_4123_, 32);
v_O_5322_ = lean_ctor_get(v_date_4123_, 33);
v_X_5323_ = lean_ctor_get(v_date_4123_, 34);
v_x_5324_ = lean_ctor_get(v_date_4123_, 35);
v_Z_5325_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5335_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5335_ == 0)
{
lean_object* v_unused_5336_; 
v_unused_5336_ = lean_ctor_get(v_date_4123_, 23);
lean_dec(v_unused_5336_);
v___x_5327_ = v_date_4123_;
v_isShared_5328_ = v_isSharedCheck_5335_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_Z_5325_);
lean_inc(v_x_5324_);
lean_inc(v_X_5323_);
lean_inc(v_O_5322_);
lean_inc(v_v_5321_);
lean_inc(v_zabbrev_5320_);
lean_inc(v_z_5319_);
lean_inc(v_V_5318_);
lean_inc(v_N_5317_);
lean_inc(v_n_5316_);
lean_inc(v_A_5315_);
lean_inc(v_S_5314_);
lean_inc(v_s_5313_);
lean_inc(v_H_5312_);
lean_inc(v_k_5311_);
lean_inc(v_K_5310_);
lean_inc(v_h_5309_);
lean_inc(v_B_5308_);
lean_inc(v_b_5307_);
lean_inc(v_a_5306_);
lean_inc(v_F_5305_);
lean_inc(v_c_5304_);
lean_inc(v_e_5303_);
lean_inc(v_E_5302_);
lean_inc(v_W_5301_);
lean_inc(v_w_5300_);
lean_inc(v_q_5299_);
lean_inc(v_Q_5298_);
lean_inc(v_d_5297_);
lean_inc(v_L_5296_);
lean_inc(v_M_5295_);
lean_inc(v_D_5294_);
lean_inc(v_Y_5293_);
lean_inc(v_u_5292_);
lean_inc(v_y_5291_);
lean_inc(v_G_5290_);
lean_dec(v_date_4123_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5335_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v___x_5330_; 
if (v_isShared_5289_ == 0)
{
lean_ctor_set_tag(v___x_5288_, 1);
lean_ctor_set(v___x_5288_, 0, v_data_4125_);
v___x_5330_ = v___x_5288_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v_data_4125_);
v___x_5330_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
lean_object* v___x_5332_; 
if (v_isShared_5328_ == 0)
{
lean_ctor_set(v___x_5327_, 23, v___x_5330_);
v___x_5332_ = v___x_5327_;
goto v_reusejp_5331_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v_G_5290_);
lean_ctor_set(v_reuseFailAlloc_5333_, 1, v_y_5291_);
lean_ctor_set(v_reuseFailAlloc_5333_, 2, v_u_5292_);
lean_ctor_set(v_reuseFailAlloc_5333_, 3, v_Y_5293_);
lean_ctor_set(v_reuseFailAlloc_5333_, 4, v_D_5294_);
lean_ctor_set(v_reuseFailAlloc_5333_, 5, v_M_5295_);
lean_ctor_set(v_reuseFailAlloc_5333_, 6, v_L_5296_);
lean_ctor_set(v_reuseFailAlloc_5333_, 7, v_d_5297_);
lean_ctor_set(v_reuseFailAlloc_5333_, 8, v_Q_5298_);
lean_ctor_set(v_reuseFailAlloc_5333_, 9, v_q_5299_);
lean_ctor_set(v_reuseFailAlloc_5333_, 10, v_w_5300_);
lean_ctor_set(v_reuseFailAlloc_5333_, 11, v_W_5301_);
lean_ctor_set(v_reuseFailAlloc_5333_, 12, v_E_5302_);
lean_ctor_set(v_reuseFailAlloc_5333_, 13, v_e_5303_);
lean_ctor_set(v_reuseFailAlloc_5333_, 14, v_c_5304_);
lean_ctor_set(v_reuseFailAlloc_5333_, 15, v_F_5305_);
lean_ctor_set(v_reuseFailAlloc_5333_, 16, v_a_5306_);
lean_ctor_set(v_reuseFailAlloc_5333_, 17, v_b_5307_);
lean_ctor_set(v_reuseFailAlloc_5333_, 18, v_B_5308_);
lean_ctor_set(v_reuseFailAlloc_5333_, 19, v_h_5309_);
lean_ctor_set(v_reuseFailAlloc_5333_, 20, v_K_5310_);
lean_ctor_set(v_reuseFailAlloc_5333_, 21, v_k_5311_);
lean_ctor_set(v_reuseFailAlloc_5333_, 22, v_H_5312_);
lean_ctor_set(v_reuseFailAlloc_5333_, 23, v___x_5330_);
lean_ctor_set(v_reuseFailAlloc_5333_, 24, v_s_5313_);
lean_ctor_set(v_reuseFailAlloc_5333_, 25, v_S_5314_);
lean_ctor_set(v_reuseFailAlloc_5333_, 26, v_A_5315_);
lean_ctor_set(v_reuseFailAlloc_5333_, 27, v_n_5316_);
lean_ctor_set(v_reuseFailAlloc_5333_, 28, v_N_5317_);
lean_ctor_set(v_reuseFailAlloc_5333_, 29, v_V_5318_);
lean_ctor_set(v_reuseFailAlloc_5333_, 30, v_z_5319_);
lean_ctor_set(v_reuseFailAlloc_5333_, 31, v_zabbrev_5320_);
lean_ctor_set(v_reuseFailAlloc_5333_, 32, v_v_5321_);
lean_ctor_set(v_reuseFailAlloc_5333_, 33, v_O_5322_);
lean_ctor_set(v_reuseFailAlloc_5333_, 34, v_X_5323_);
lean_ctor_set(v_reuseFailAlloc_5333_, 35, v_x_5324_);
lean_ctor_set(v_reuseFailAlloc_5333_, 36, v_Z_5325_);
v___x_5332_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5331_;
}
v_reusejp_5331_:
{
return v___x_5332_;
}
}
}
}
}
case 24:
{
lean_object* v___x_5340_; uint8_t v_isShared_5341_; uint8_t v_isSharedCheck_5389_; 
v_isSharedCheck_5389_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_5389_ == 0)
{
lean_object* v_unused_5390_; 
v_unused_5390_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_5390_);
v___x_5340_ = v_modifier_4124_;
v_isShared_5341_ = v_isSharedCheck_5389_;
goto v_resetjp_5339_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_5340_ = lean_box(0);
v_isShared_5341_ = v_isSharedCheck_5389_;
goto v_resetjp_5339_;
}
v_resetjp_5339_:
{
lean_object* v_G_5342_; lean_object* v_y_5343_; lean_object* v_u_5344_; lean_object* v_Y_5345_; lean_object* v_D_5346_; lean_object* v_M_5347_; lean_object* v_L_5348_; lean_object* v_d_5349_; lean_object* v_Q_5350_; lean_object* v_q_5351_; lean_object* v_w_5352_; lean_object* v_W_5353_; lean_object* v_E_5354_; lean_object* v_e_5355_; lean_object* v_c_5356_; lean_object* v_F_5357_; lean_object* v_a_5358_; lean_object* v_b_5359_; lean_object* v_B_5360_; lean_object* v_h_5361_; lean_object* v_K_5362_; lean_object* v_k_5363_; lean_object* v_H_5364_; lean_object* v_m_5365_; lean_object* v_S_5366_; lean_object* v_A_5367_; lean_object* v_n_5368_; lean_object* v_N_5369_; lean_object* v_V_5370_; lean_object* v_z_5371_; lean_object* v_zabbrev_5372_; lean_object* v_v_5373_; lean_object* v_O_5374_; lean_object* v_X_5375_; lean_object* v_x_5376_; lean_object* v_Z_5377_; lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5387_; 
v_G_5342_ = lean_ctor_get(v_date_4123_, 0);
v_y_5343_ = lean_ctor_get(v_date_4123_, 1);
v_u_5344_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5345_ = lean_ctor_get(v_date_4123_, 3);
v_D_5346_ = lean_ctor_get(v_date_4123_, 4);
v_M_5347_ = lean_ctor_get(v_date_4123_, 5);
v_L_5348_ = lean_ctor_get(v_date_4123_, 6);
v_d_5349_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5350_ = lean_ctor_get(v_date_4123_, 8);
v_q_5351_ = lean_ctor_get(v_date_4123_, 9);
v_w_5352_ = lean_ctor_get(v_date_4123_, 10);
v_W_5353_ = lean_ctor_get(v_date_4123_, 11);
v_E_5354_ = lean_ctor_get(v_date_4123_, 12);
v_e_5355_ = lean_ctor_get(v_date_4123_, 13);
v_c_5356_ = lean_ctor_get(v_date_4123_, 14);
v_F_5357_ = lean_ctor_get(v_date_4123_, 15);
v_a_5358_ = lean_ctor_get(v_date_4123_, 16);
v_b_5359_ = lean_ctor_get(v_date_4123_, 17);
v_B_5360_ = lean_ctor_get(v_date_4123_, 18);
v_h_5361_ = lean_ctor_get(v_date_4123_, 19);
v_K_5362_ = lean_ctor_get(v_date_4123_, 20);
v_k_5363_ = lean_ctor_get(v_date_4123_, 21);
v_H_5364_ = lean_ctor_get(v_date_4123_, 22);
v_m_5365_ = lean_ctor_get(v_date_4123_, 23);
v_S_5366_ = lean_ctor_get(v_date_4123_, 25);
v_A_5367_ = lean_ctor_get(v_date_4123_, 26);
v_n_5368_ = lean_ctor_get(v_date_4123_, 27);
v_N_5369_ = lean_ctor_get(v_date_4123_, 28);
v_V_5370_ = lean_ctor_get(v_date_4123_, 29);
v_z_5371_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_5372_ = lean_ctor_get(v_date_4123_, 31);
v_v_5373_ = lean_ctor_get(v_date_4123_, 32);
v_O_5374_ = lean_ctor_get(v_date_4123_, 33);
v_X_5375_ = lean_ctor_get(v_date_4123_, 34);
v_x_5376_ = lean_ctor_get(v_date_4123_, 35);
v_Z_5377_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5387_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5387_ == 0)
{
lean_object* v_unused_5388_; 
v_unused_5388_ = lean_ctor_get(v_date_4123_, 24);
lean_dec(v_unused_5388_);
v___x_5379_ = v_date_4123_;
v_isShared_5380_ = v_isSharedCheck_5387_;
goto v_resetjp_5378_;
}
else
{
lean_inc(v_Z_5377_);
lean_inc(v_x_5376_);
lean_inc(v_X_5375_);
lean_inc(v_O_5374_);
lean_inc(v_v_5373_);
lean_inc(v_zabbrev_5372_);
lean_inc(v_z_5371_);
lean_inc(v_V_5370_);
lean_inc(v_N_5369_);
lean_inc(v_n_5368_);
lean_inc(v_A_5367_);
lean_inc(v_S_5366_);
lean_inc(v_m_5365_);
lean_inc(v_H_5364_);
lean_inc(v_k_5363_);
lean_inc(v_K_5362_);
lean_inc(v_h_5361_);
lean_inc(v_B_5360_);
lean_inc(v_b_5359_);
lean_inc(v_a_5358_);
lean_inc(v_F_5357_);
lean_inc(v_c_5356_);
lean_inc(v_e_5355_);
lean_inc(v_E_5354_);
lean_inc(v_W_5353_);
lean_inc(v_w_5352_);
lean_inc(v_q_5351_);
lean_inc(v_Q_5350_);
lean_inc(v_d_5349_);
lean_inc(v_L_5348_);
lean_inc(v_M_5347_);
lean_inc(v_D_5346_);
lean_inc(v_Y_5345_);
lean_inc(v_u_5344_);
lean_inc(v_y_5343_);
lean_inc(v_G_5342_);
lean_dec(v_date_4123_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5387_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
lean_object* v___x_5382_; 
if (v_isShared_5341_ == 0)
{
lean_ctor_set_tag(v___x_5340_, 1);
lean_ctor_set(v___x_5340_, 0, v_data_4125_);
v___x_5382_ = v___x_5340_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5386_; 
v_reuseFailAlloc_5386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5386_, 0, v_data_4125_);
v___x_5382_ = v_reuseFailAlloc_5386_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
lean_object* v___x_5384_; 
if (v_isShared_5380_ == 0)
{
lean_ctor_set(v___x_5379_, 24, v___x_5382_);
v___x_5384_ = v___x_5379_;
goto v_reusejp_5383_;
}
else
{
lean_object* v_reuseFailAlloc_5385_; 
v_reuseFailAlloc_5385_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5385_, 0, v_G_5342_);
lean_ctor_set(v_reuseFailAlloc_5385_, 1, v_y_5343_);
lean_ctor_set(v_reuseFailAlloc_5385_, 2, v_u_5344_);
lean_ctor_set(v_reuseFailAlloc_5385_, 3, v_Y_5345_);
lean_ctor_set(v_reuseFailAlloc_5385_, 4, v_D_5346_);
lean_ctor_set(v_reuseFailAlloc_5385_, 5, v_M_5347_);
lean_ctor_set(v_reuseFailAlloc_5385_, 6, v_L_5348_);
lean_ctor_set(v_reuseFailAlloc_5385_, 7, v_d_5349_);
lean_ctor_set(v_reuseFailAlloc_5385_, 8, v_Q_5350_);
lean_ctor_set(v_reuseFailAlloc_5385_, 9, v_q_5351_);
lean_ctor_set(v_reuseFailAlloc_5385_, 10, v_w_5352_);
lean_ctor_set(v_reuseFailAlloc_5385_, 11, v_W_5353_);
lean_ctor_set(v_reuseFailAlloc_5385_, 12, v_E_5354_);
lean_ctor_set(v_reuseFailAlloc_5385_, 13, v_e_5355_);
lean_ctor_set(v_reuseFailAlloc_5385_, 14, v_c_5356_);
lean_ctor_set(v_reuseFailAlloc_5385_, 15, v_F_5357_);
lean_ctor_set(v_reuseFailAlloc_5385_, 16, v_a_5358_);
lean_ctor_set(v_reuseFailAlloc_5385_, 17, v_b_5359_);
lean_ctor_set(v_reuseFailAlloc_5385_, 18, v_B_5360_);
lean_ctor_set(v_reuseFailAlloc_5385_, 19, v_h_5361_);
lean_ctor_set(v_reuseFailAlloc_5385_, 20, v_K_5362_);
lean_ctor_set(v_reuseFailAlloc_5385_, 21, v_k_5363_);
lean_ctor_set(v_reuseFailAlloc_5385_, 22, v_H_5364_);
lean_ctor_set(v_reuseFailAlloc_5385_, 23, v_m_5365_);
lean_ctor_set(v_reuseFailAlloc_5385_, 24, v___x_5382_);
lean_ctor_set(v_reuseFailAlloc_5385_, 25, v_S_5366_);
lean_ctor_set(v_reuseFailAlloc_5385_, 26, v_A_5367_);
lean_ctor_set(v_reuseFailAlloc_5385_, 27, v_n_5368_);
lean_ctor_set(v_reuseFailAlloc_5385_, 28, v_N_5369_);
lean_ctor_set(v_reuseFailAlloc_5385_, 29, v_V_5370_);
lean_ctor_set(v_reuseFailAlloc_5385_, 30, v_z_5371_);
lean_ctor_set(v_reuseFailAlloc_5385_, 31, v_zabbrev_5372_);
lean_ctor_set(v_reuseFailAlloc_5385_, 32, v_v_5373_);
lean_ctor_set(v_reuseFailAlloc_5385_, 33, v_O_5374_);
lean_ctor_set(v_reuseFailAlloc_5385_, 34, v_X_5375_);
lean_ctor_set(v_reuseFailAlloc_5385_, 35, v_x_5376_);
lean_ctor_set(v_reuseFailAlloc_5385_, 36, v_Z_5377_);
v___x_5384_ = v_reuseFailAlloc_5385_;
goto v_reusejp_5383_;
}
v_reusejp_5383_:
{
return v___x_5384_;
}
}
}
}
}
case 25:
{
lean_object* v___x_5392_; uint8_t v_isShared_5393_; uint8_t v_isSharedCheck_5441_; 
v_isSharedCheck_5441_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_5441_ == 0)
{
lean_object* v_unused_5442_; 
v_unused_5442_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_5442_);
v___x_5392_ = v_modifier_4124_;
v_isShared_5393_ = v_isSharedCheck_5441_;
goto v_resetjp_5391_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_5392_ = lean_box(0);
v_isShared_5393_ = v_isSharedCheck_5441_;
goto v_resetjp_5391_;
}
v_resetjp_5391_:
{
lean_object* v_G_5394_; lean_object* v_y_5395_; lean_object* v_u_5396_; lean_object* v_Y_5397_; lean_object* v_D_5398_; lean_object* v_M_5399_; lean_object* v_L_5400_; lean_object* v_d_5401_; lean_object* v_Q_5402_; lean_object* v_q_5403_; lean_object* v_w_5404_; lean_object* v_W_5405_; lean_object* v_E_5406_; lean_object* v_e_5407_; lean_object* v_c_5408_; lean_object* v_F_5409_; lean_object* v_a_5410_; lean_object* v_b_5411_; lean_object* v_B_5412_; lean_object* v_h_5413_; lean_object* v_K_5414_; lean_object* v_k_5415_; lean_object* v_H_5416_; lean_object* v_m_5417_; lean_object* v_s_5418_; lean_object* v_A_5419_; lean_object* v_n_5420_; lean_object* v_N_5421_; lean_object* v_V_5422_; lean_object* v_z_5423_; lean_object* v_zabbrev_5424_; lean_object* v_v_5425_; lean_object* v_O_5426_; lean_object* v_X_5427_; lean_object* v_x_5428_; lean_object* v_Z_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5439_; 
v_G_5394_ = lean_ctor_get(v_date_4123_, 0);
v_y_5395_ = lean_ctor_get(v_date_4123_, 1);
v_u_5396_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5397_ = lean_ctor_get(v_date_4123_, 3);
v_D_5398_ = lean_ctor_get(v_date_4123_, 4);
v_M_5399_ = lean_ctor_get(v_date_4123_, 5);
v_L_5400_ = lean_ctor_get(v_date_4123_, 6);
v_d_5401_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5402_ = lean_ctor_get(v_date_4123_, 8);
v_q_5403_ = lean_ctor_get(v_date_4123_, 9);
v_w_5404_ = lean_ctor_get(v_date_4123_, 10);
v_W_5405_ = lean_ctor_get(v_date_4123_, 11);
v_E_5406_ = lean_ctor_get(v_date_4123_, 12);
v_e_5407_ = lean_ctor_get(v_date_4123_, 13);
v_c_5408_ = lean_ctor_get(v_date_4123_, 14);
v_F_5409_ = lean_ctor_get(v_date_4123_, 15);
v_a_5410_ = lean_ctor_get(v_date_4123_, 16);
v_b_5411_ = lean_ctor_get(v_date_4123_, 17);
v_B_5412_ = lean_ctor_get(v_date_4123_, 18);
v_h_5413_ = lean_ctor_get(v_date_4123_, 19);
v_K_5414_ = lean_ctor_get(v_date_4123_, 20);
v_k_5415_ = lean_ctor_get(v_date_4123_, 21);
v_H_5416_ = lean_ctor_get(v_date_4123_, 22);
v_m_5417_ = lean_ctor_get(v_date_4123_, 23);
v_s_5418_ = lean_ctor_get(v_date_4123_, 24);
v_A_5419_ = lean_ctor_get(v_date_4123_, 26);
v_n_5420_ = lean_ctor_get(v_date_4123_, 27);
v_N_5421_ = lean_ctor_get(v_date_4123_, 28);
v_V_5422_ = lean_ctor_get(v_date_4123_, 29);
v_z_5423_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_5424_ = lean_ctor_get(v_date_4123_, 31);
v_v_5425_ = lean_ctor_get(v_date_4123_, 32);
v_O_5426_ = lean_ctor_get(v_date_4123_, 33);
v_X_5427_ = lean_ctor_get(v_date_4123_, 34);
v_x_5428_ = lean_ctor_get(v_date_4123_, 35);
v_Z_5429_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5439_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5439_ == 0)
{
lean_object* v_unused_5440_; 
v_unused_5440_ = lean_ctor_get(v_date_4123_, 25);
lean_dec(v_unused_5440_);
v___x_5431_ = v_date_4123_;
v_isShared_5432_ = v_isSharedCheck_5439_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_Z_5429_);
lean_inc(v_x_5428_);
lean_inc(v_X_5427_);
lean_inc(v_O_5426_);
lean_inc(v_v_5425_);
lean_inc(v_zabbrev_5424_);
lean_inc(v_z_5423_);
lean_inc(v_V_5422_);
lean_inc(v_N_5421_);
lean_inc(v_n_5420_);
lean_inc(v_A_5419_);
lean_inc(v_s_5418_);
lean_inc(v_m_5417_);
lean_inc(v_H_5416_);
lean_inc(v_k_5415_);
lean_inc(v_K_5414_);
lean_inc(v_h_5413_);
lean_inc(v_B_5412_);
lean_inc(v_b_5411_);
lean_inc(v_a_5410_);
lean_inc(v_F_5409_);
lean_inc(v_c_5408_);
lean_inc(v_e_5407_);
lean_inc(v_E_5406_);
lean_inc(v_W_5405_);
lean_inc(v_w_5404_);
lean_inc(v_q_5403_);
lean_inc(v_Q_5402_);
lean_inc(v_d_5401_);
lean_inc(v_L_5400_);
lean_inc(v_M_5399_);
lean_inc(v_D_5398_);
lean_inc(v_Y_5397_);
lean_inc(v_u_5396_);
lean_inc(v_y_5395_);
lean_inc(v_G_5394_);
lean_dec(v_date_4123_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5439_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
lean_object* v___x_5434_; 
if (v_isShared_5393_ == 0)
{
lean_ctor_set_tag(v___x_5392_, 1);
lean_ctor_set(v___x_5392_, 0, v_data_4125_);
v___x_5434_ = v___x_5392_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5438_; 
v_reuseFailAlloc_5438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5438_, 0, v_data_4125_);
v___x_5434_ = v_reuseFailAlloc_5438_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
lean_object* v___x_5436_; 
if (v_isShared_5432_ == 0)
{
lean_ctor_set(v___x_5431_, 25, v___x_5434_);
v___x_5436_ = v___x_5431_;
goto v_reusejp_5435_;
}
else
{
lean_object* v_reuseFailAlloc_5437_; 
v_reuseFailAlloc_5437_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5437_, 0, v_G_5394_);
lean_ctor_set(v_reuseFailAlloc_5437_, 1, v_y_5395_);
lean_ctor_set(v_reuseFailAlloc_5437_, 2, v_u_5396_);
lean_ctor_set(v_reuseFailAlloc_5437_, 3, v_Y_5397_);
lean_ctor_set(v_reuseFailAlloc_5437_, 4, v_D_5398_);
lean_ctor_set(v_reuseFailAlloc_5437_, 5, v_M_5399_);
lean_ctor_set(v_reuseFailAlloc_5437_, 6, v_L_5400_);
lean_ctor_set(v_reuseFailAlloc_5437_, 7, v_d_5401_);
lean_ctor_set(v_reuseFailAlloc_5437_, 8, v_Q_5402_);
lean_ctor_set(v_reuseFailAlloc_5437_, 9, v_q_5403_);
lean_ctor_set(v_reuseFailAlloc_5437_, 10, v_w_5404_);
lean_ctor_set(v_reuseFailAlloc_5437_, 11, v_W_5405_);
lean_ctor_set(v_reuseFailAlloc_5437_, 12, v_E_5406_);
lean_ctor_set(v_reuseFailAlloc_5437_, 13, v_e_5407_);
lean_ctor_set(v_reuseFailAlloc_5437_, 14, v_c_5408_);
lean_ctor_set(v_reuseFailAlloc_5437_, 15, v_F_5409_);
lean_ctor_set(v_reuseFailAlloc_5437_, 16, v_a_5410_);
lean_ctor_set(v_reuseFailAlloc_5437_, 17, v_b_5411_);
lean_ctor_set(v_reuseFailAlloc_5437_, 18, v_B_5412_);
lean_ctor_set(v_reuseFailAlloc_5437_, 19, v_h_5413_);
lean_ctor_set(v_reuseFailAlloc_5437_, 20, v_K_5414_);
lean_ctor_set(v_reuseFailAlloc_5437_, 21, v_k_5415_);
lean_ctor_set(v_reuseFailAlloc_5437_, 22, v_H_5416_);
lean_ctor_set(v_reuseFailAlloc_5437_, 23, v_m_5417_);
lean_ctor_set(v_reuseFailAlloc_5437_, 24, v_s_5418_);
lean_ctor_set(v_reuseFailAlloc_5437_, 25, v___x_5434_);
lean_ctor_set(v_reuseFailAlloc_5437_, 26, v_A_5419_);
lean_ctor_set(v_reuseFailAlloc_5437_, 27, v_n_5420_);
lean_ctor_set(v_reuseFailAlloc_5437_, 28, v_N_5421_);
lean_ctor_set(v_reuseFailAlloc_5437_, 29, v_V_5422_);
lean_ctor_set(v_reuseFailAlloc_5437_, 30, v_z_5423_);
lean_ctor_set(v_reuseFailAlloc_5437_, 31, v_zabbrev_5424_);
lean_ctor_set(v_reuseFailAlloc_5437_, 32, v_v_5425_);
lean_ctor_set(v_reuseFailAlloc_5437_, 33, v_O_5426_);
lean_ctor_set(v_reuseFailAlloc_5437_, 34, v_X_5427_);
lean_ctor_set(v_reuseFailAlloc_5437_, 35, v_x_5428_);
lean_ctor_set(v_reuseFailAlloc_5437_, 36, v_Z_5429_);
v___x_5436_ = v_reuseFailAlloc_5437_;
goto v_reusejp_5435_;
}
v_reusejp_5435_:
{
return v___x_5436_;
}
}
}
}
}
case 26:
{
lean_object* v___x_5444_; uint8_t v_isShared_5445_; uint8_t v_isSharedCheck_5493_; 
v_isSharedCheck_5493_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_5493_ == 0)
{
lean_object* v_unused_5494_; 
v_unused_5494_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_5494_);
v___x_5444_ = v_modifier_4124_;
v_isShared_5445_ = v_isSharedCheck_5493_;
goto v_resetjp_5443_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_5444_ = lean_box(0);
v_isShared_5445_ = v_isSharedCheck_5493_;
goto v_resetjp_5443_;
}
v_resetjp_5443_:
{
lean_object* v_G_5446_; lean_object* v_y_5447_; lean_object* v_u_5448_; lean_object* v_Y_5449_; lean_object* v_D_5450_; lean_object* v_M_5451_; lean_object* v_L_5452_; lean_object* v_d_5453_; lean_object* v_Q_5454_; lean_object* v_q_5455_; lean_object* v_w_5456_; lean_object* v_W_5457_; lean_object* v_E_5458_; lean_object* v_e_5459_; lean_object* v_c_5460_; lean_object* v_F_5461_; lean_object* v_a_5462_; lean_object* v_b_5463_; lean_object* v_B_5464_; lean_object* v_h_5465_; lean_object* v_K_5466_; lean_object* v_k_5467_; lean_object* v_H_5468_; lean_object* v_m_5469_; lean_object* v_s_5470_; lean_object* v_S_5471_; lean_object* v_n_5472_; lean_object* v_N_5473_; lean_object* v_V_5474_; lean_object* v_z_5475_; lean_object* v_zabbrev_5476_; lean_object* v_v_5477_; lean_object* v_O_5478_; lean_object* v_X_5479_; lean_object* v_x_5480_; lean_object* v_Z_5481_; lean_object* v___x_5483_; uint8_t v_isShared_5484_; uint8_t v_isSharedCheck_5491_; 
v_G_5446_ = lean_ctor_get(v_date_4123_, 0);
v_y_5447_ = lean_ctor_get(v_date_4123_, 1);
v_u_5448_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5449_ = lean_ctor_get(v_date_4123_, 3);
v_D_5450_ = lean_ctor_get(v_date_4123_, 4);
v_M_5451_ = lean_ctor_get(v_date_4123_, 5);
v_L_5452_ = lean_ctor_get(v_date_4123_, 6);
v_d_5453_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5454_ = lean_ctor_get(v_date_4123_, 8);
v_q_5455_ = lean_ctor_get(v_date_4123_, 9);
v_w_5456_ = lean_ctor_get(v_date_4123_, 10);
v_W_5457_ = lean_ctor_get(v_date_4123_, 11);
v_E_5458_ = lean_ctor_get(v_date_4123_, 12);
v_e_5459_ = lean_ctor_get(v_date_4123_, 13);
v_c_5460_ = lean_ctor_get(v_date_4123_, 14);
v_F_5461_ = lean_ctor_get(v_date_4123_, 15);
v_a_5462_ = lean_ctor_get(v_date_4123_, 16);
v_b_5463_ = lean_ctor_get(v_date_4123_, 17);
v_B_5464_ = lean_ctor_get(v_date_4123_, 18);
v_h_5465_ = lean_ctor_get(v_date_4123_, 19);
v_K_5466_ = lean_ctor_get(v_date_4123_, 20);
v_k_5467_ = lean_ctor_get(v_date_4123_, 21);
v_H_5468_ = lean_ctor_get(v_date_4123_, 22);
v_m_5469_ = lean_ctor_get(v_date_4123_, 23);
v_s_5470_ = lean_ctor_get(v_date_4123_, 24);
v_S_5471_ = lean_ctor_get(v_date_4123_, 25);
v_n_5472_ = lean_ctor_get(v_date_4123_, 27);
v_N_5473_ = lean_ctor_get(v_date_4123_, 28);
v_V_5474_ = lean_ctor_get(v_date_4123_, 29);
v_z_5475_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_5476_ = lean_ctor_get(v_date_4123_, 31);
v_v_5477_ = lean_ctor_get(v_date_4123_, 32);
v_O_5478_ = lean_ctor_get(v_date_4123_, 33);
v_X_5479_ = lean_ctor_get(v_date_4123_, 34);
v_x_5480_ = lean_ctor_get(v_date_4123_, 35);
v_Z_5481_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5491_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5491_ == 0)
{
lean_object* v_unused_5492_; 
v_unused_5492_ = lean_ctor_get(v_date_4123_, 26);
lean_dec(v_unused_5492_);
v___x_5483_ = v_date_4123_;
v_isShared_5484_ = v_isSharedCheck_5491_;
goto v_resetjp_5482_;
}
else
{
lean_inc(v_Z_5481_);
lean_inc(v_x_5480_);
lean_inc(v_X_5479_);
lean_inc(v_O_5478_);
lean_inc(v_v_5477_);
lean_inc(v_zabbrev_5476_);
lean_inc(v_z_5475_);
lean_inc(v_V_5474_);
lean_inc(v_N_5473_);
lean_inc(v_n_5472_);
lean_inc(v_S_5471_);
lean_inc(v_s_5470_);
lean_inc(v_m_5469_);
lean_inc(v_H_5468_);
lean_inc(v_k_5467_);
lean_inc(v_K_5466_);
lean_inc(v_h_5465_);
lean_inc(v_B_5464_);
lean_inc(v_b_5463_);
lean_inc(v_a_5462_);
lean_inc(v_F_5461_);
lean_inc(v_c_5460_);
lean_inc(v_e_5459_);
lean_inc(v_E_5458_);
lean_inc(v_W_5457_);
lean_inc(v_w_5456_);
lean_inc(v_q_5455_);
lean_inc(v_Q_5454_);
lean_inc(v_d_5453_);
lean_inc(v_L_5452_);
lean_inc(v_M_5451_);
lean_inc(v_D_5450_);
lean_inc(v_Y_5449_);
lean_inc(v_u_5448_);
lean_inc(v_y_5447_);
lean_inc(v_G_5446_);
lean_dec(v_date_4123_);
v___x_5483_ = lean_box(0);
v_isShared_5484_ = v_isSharedCheck_5491_;
goto v_resetjp_5482_;
}
v_resetjp_5482_:
{
lean_object* v___x_5486_; 
if (v_isShared_5445_ == 0)
{
lean_ctor_set_tag(v___x_5444_, 1);
lean_ctor_set(v___x_5444_, 0, v_data_4125_);
v___x_5486_ = v___x_5444_;
goto v_reusejp_5485_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v_data_4125_);
v___x_5486_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5485_;
}
v_reusejp_5485_:
{
lean_object* v___x_5488_; 
if (v_isShared_5484_ == 0)
{
lean_ctor_set(v___x_5483_, 26, v___x_5486_);
v___x_5488_ = v___x_5483_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5489_; 
v_reuseFailAlloc_5489_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5489_, 0, v_G_5446_);
lean_ctor_set(v_reuseFailAlloc_5489_, 1, v_y_5447_);
lean_ctor_set(v_reuseFailAlloc_5489_, 2, v_u_5448_);
lean_ctor_set(v_reuseFailAlloc_5489_, 3, v_Y_5449_);
lean_ctor_set(v_reuseFailAlloc_5489_, 4, v_D_5450_);
lean_ctor_set(v_reuseFailAlloc_5489_, 5, v_M_5451_);
lean_ctor_set(v_reuseFailAlloc_5489_, 6, v_L_5452_);
lean_ctor_set(v_reuseFailAlloc_5489_, 7, v_d_5453_);
lean_ctor_set(v_reuseFailAlloc_5489_, 8, v_Q_5454_);
lean_ctor_set(v_reuseFailAlloc_5489_, 9, v_q_5455_);
lean_ctor_set(v_reuseFailAlloc_5489_, 10, v_w_5456_);
lean_ctor_set(v_reuseFailAlloc_5489_, 11, v_W_5457_);
lean_ctor_set(v_reuseFailAlloc_5489_, 12, v_E_5458_);
lean_ctor_set(v_reuseFailAlloc_5489_, 13, v_e_5459_);
lean_ctor_set(v_reuseFailAlloc_5489_, 14, v_c_5460_);
lean_ctor_set(v_reuseFailAlloc_5489_, 15, v_F_5461_);
lean_ctor_set(v_reuseFailAlloc_5489_, 16, v_a_5462_);
lean_ctor_set(v_reuseFailAlloc_5489_, 17, v_b_5463_);
lean_ctor_set(v_reuseFailAlloc_5489_, 18, v_B_5464_);
lean_ctor_set(v_reuseFailAlloc_5489_, 19, v_h_5465_);
lean_ctor_set(v_reuseFailAlloc_5489_, 20, v_K_5466_);
lean_ctor_set(v_reuseFailAlloc_5489_, 21, v_k_5467_);
lean_ctor_set(v_reuseFailAlloc_5489_, 22, v_H_5468_);
lean_ctor_set(v_reuseFailAlloc_5489_, 23, v_m_5469_);
lean_ctor_set(v_reuseFailAlloc_5489_, 24, v_s_5470_);
lean_ctor_set(v_reuseFailAlloc_5489_, 25, v_S_5471_);
lean_ctor_set(v_reuseFailAlloc_5489_, 26, v___x_5486_);
lean_ctor_set(v_reuseFailAlloc_5489_, 27, v_n_5472_);
lean_ctor_set(v_reuseFailAlloc_5489_, 28, v_N_5473_);
lean_ctor_set(v_reuseFailAlloc_5489_, 29, v_V_5474_);
lean_ctor_set(v_reuseFailAlloc_5489_, 30, v_z_5475_);
lean_ctor_set(v_reuseFailAlloc_5489_, 31, v_zabbrev_5476_);
lean_ctor_set(v_reuseFailAlloc_5489_, 32, v_v_5477_);
lean_ctor_set(v_reuseFailAlloc_5489_, 33, v_O_5478_);
lean_ctor_set(v_reuseFailAlloc_5489_, 34, v_X_5479_);
lean_ctor_set(v_reuseFailAlloc_5489_, 35, v_x_5480_);
lean_ctor_set(v_reuseFailAlloc_5489_, 36, v_Z_5481_);
v___x_5488_ = v_reuseFailAlloc_5489_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
return v___x_5488_;
}
}
}
}
}
case 27:
{
lean_object* v___x_5496_; uint8_t v_isShared_5497_; uint8_t v_isSharedCheck_5545_; 
v_isSharedCheck_5545_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_5545_ == 0)
{
lean_object* v_unused_5546_; 
v_unused_5546_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_5546_);
v___x_5496_ = v_modifier_4124_;
v_isShared_5497_ = v_isSharedCheck_5545_;
goto v_resetjp_5495_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_5496_ = lean_box(0);
v_isShared_5497_ = v_isSharedCheck_5545_;
goto v_resetjp_5495_;
}
v_resetjp_5495_:
{
lean_object* v_G_5498_; lean_object* v_y_5499_; lean_object* v_u_5500_; lean_object* v_Y_5501_; lean_object* v_D_5502_; lean_object* v_M_5503_; lean_object* v_L_5504_; lean_object* v_d_5505_; lean_object* v_Q_5506_; lean_object* v_q_5507_; lean_object* v_w_5508_; lean_object* v_W_5509_; lean_object* v_E_5510_; lean_object* v_e_5511_; lean_object* v_c_5512_; lean_object* v_F_5513_; lean_object* v_a_5514_; lean_object* v_b_5515_; lean_object* v_B_5516_; lean_object* v_h_5517_; lean_object* v_K_5518_; lean_object* v_k_5519_; lean_object* v_H_5520_; lean_object* v_m_5521_; lean_object* v_s_5522_; lean_object* v_S_5523_; lean_object* v_A_5524_; lean_object* v_N_5525_; lean_object* v_V_5526_; lean_object* v_z_5527_; lean_object* v_zabbrev_5528_; lean_object* v_v_5529_; lean_object* v_O_5530_; lean_object* v_X_5531_; lean_object* v_x_5532_; lean_object* v_Z_5533_; lean_object* v___x_5535_; uint8_t v_isShared_5536_; uint8_t v_isSharedCheck_5543_; 
v_G_5498_ = lean_ctor_get(v_date_4123_, 0);
v_y_5499_ = lean_ctor_get(v_date_4123_, 1);
v_u_5500_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5501_ = lean_ctor_get(v_date_4123_, 3);
v_D_5502_ = lean_ctor_get(v_date_4123_, 4);
v_M_5503_ = lean_ctor_get(v_date_4123_, 5);
v_L_5504_ = lean_ctor_get(v_date_4123_, 6);
v_d_5505_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5506_ = lean_ctor_get(v_date_4123_, 8);
v_q_5507_ = lean_ctor_get(v_date_4123_, 9);
v_w_5508_ = lean_ctor_get(v_date_4123_, 10);
v_W_5509_ = lean_ctor_get(v_date_4123_, 11);
v_E_5510_ = lean_ctor_get(v_date_4123_, 12);
v_e_5511_ = lean_ctor_get(v_date_4123_, 13);
v_c_5512_ = lean_ctor_get(v_date_4123_, 14);
v_F_5513_ = lean_ctor_get(v_date_4123_, 15);
v_a_5514_ = lean_ctor_get(v_date_4123_, 16);
v_b_5515_ = lean_ctor_get(v_date_4123_, 17);
v_B_5516_ = lean_ctor_get(v_date_4123_, 18);
v_h_5517_ = lean_ctor_get(v_date_4123_, 19);
v_K_5518_ = lean_ctor_get(v_date_4123_, 20);
v_k_5519_ = lean_ctor_get(v_date_4123_, 21);
v_H_5520_ = lean_ctor_get(v_date_4123_, 22);
v_m_5521_ = lean_ctor_get(v_date_4123_, 23);
v_s_5522_ = lean_ctor_get(v_date_4123_, 24);
v_S_5523_ = lean_ctor_get(v_date_4123_, 25);
v_A_5524_ = lean_ctor_get(v_date_4123_, 26);
v_N_5525_ = lean_ctor_get(v_date_4123_, 28);
v_V_5526_ = lean_ctor_get(v_date_4123_, 29);
v_z_5527_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_5528_ = lean_ctor_get(v_date_4123_, 31);
v_v_5529_ = lean_ctor_get(v_date_4123_, 32);
v_O_5530_ = lean_ctor_get(v_date_4123_, 33);
v_X_5531_ = lean_ctor_get(v_date_4123_, 34);
v_x_5532_ = lean_ctor_get(v_date_4123_, 35);
v_Z_5533_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5543_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5543_ == 0)
{
lean_object* v_unused_5544_; 
v_unused_5544_ = lean_ctor_get(v_date_4123_, 27);
lean_dec(v_unused_5544_);
v___x_5535_ = v_date_4123_;
v_isShared_5536_ = v_isSharedCheck_5543_;
goto v_resetjp_5534_;
}
else
{
lean_inc(v_Z_5533_);
lean_inc(v_x_5532_);
lean_inc(v_X_5531_);
lean_inc(v_O_5530_);
lean_inc(v_v_5529_);
lean_inc(v_zabbrev_5528_);
lean_inc(v_z_5527_);
lean_inc(v_V_5526_);
lean_inc(v_N_5525_);
lean_inc(v_A_5524_);
lean_inc(v_S_5523_);
lean_inc(v_s_5522_);
lean_inc(v_m_5521_);
lean_inc(v_H_5520_);
lean_inc(v_k_5519_);
lean_inc(v_K_5518_);
lean_inc(v_h_5517_);
lean_inc(v_B_5516_);
lean_inc(v_b_5515_);
lean_inc(v_a_5514_);
lean_inc(v_F_5513_);
lean_inc(v_c_5512_);
lean_inc(v_e_5511_);
lean_inc(v_E_5510_);
lean_inc(v_W_5509_);
lean_inc(v_w_5508_);
lean_inc(v_q_5507_);
lean_inc(v_Q_5506_);
lean_inc(v_d_5505_);
lean_inc(v_L_5504_);
lean_inc(v_M_5503_);
lean_inc(v_D_5502_);
lean_inc(v_Y_5501_);
lean_inc(v_u_5500_);
lean_inc(v_y_5499_);
lean_inc(v_G_5498_);
lean_dec(v_date_4123_);
v___x_5535_ = lean_box(0);
v_isShared_5536_ = v_isSharedCheck_5543_;
goto v_resetjp_5534_;
}
v_resetjp_5534_:
{
lean_object* v___x_5538_; 
if (v_isShared_5497_ == 0)
{
lean_ctor_set_tag(v___x_5496_, 1);
lean_ctor_set(v___x_5496_, 0, v_data_4125_);
v___x_5538_ = v___x_5496_;
goto v_reusejp_5537_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_data_4125_);
v___x_5538_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5537_;
}
v_reusejp_5537_:
{
lean_object* v___x_5540_; 
if (v_isShared_5536_ == 0)
{
lean_ctor_set(v___x_5535_, 27, v___x_5538_);
v___x_5540_ = v___x_5535_;
goto v_reusejp_5539_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_G_5498_);
lean_ctor_set(v_reuseFailAlloc_5541_, 1, v_y_5499_);
lean_ctor_set(v_reuseFailAlloc_5541_, 2, v_u_5500_);
lean_ctor_set(v_reuseFailAlloc_5541_, 3, v_Y_5501_);
lean_ctor_set(v_reuseFailAlloc_5541_, 4, v_D_5502_);
lean_ctor_set(v_reuseFailAlloc_5541_, 5, v_M_5503_);
lean_ctor_set(v_reuseFailAlloc_5541_, 6, v_L_5504_);
lean_ctor_set(v_reuseFailAlloc_5541_, 7, v_d_5505_);
lean_ctor_set(v_reuseFailAlloc_5541_, 8, v_Q_5506_);
lean_ctor_set(v_reuseFailAlloc_5541_, 9, v_q_5507_);
lean_ctor_set(v_reuseFailAlloc_5541_, 10, v_w_5508_);
lean_ctor_set(v_reuseFailAlloc_5541_, 11, v_W_5509_);
lean_ctor_set(v_reuseFailAlloc_5541_, 12, v_E_5510_);
lean_ctor_set(v_reuseFailAlloc_5541_, 13, v_e_5511_);
lean_ctor_set(v_reuseFailAlloc_5541_, 14, v_c_5512_);
lean_ctor_set(v_reuseFailAlloc_5541_, 15, v_F_5513_);
lean_ctor_set(v_reuseFailAlloc_5541_, 16, v_a_5514_);
lean_ctor_set(v_reuseFailAlloc_5541_, 17, v_b_5515_);
lean_ctor_set(v_reuseFailAlloc_5541_, 18, v_B_5516_);
lean_ctor_set(v_reuseFailAlloc_5541_, 19, v_h_5517_);
lean_ctor_set(v_reuseFailAlloc_5541_, 20, v_K_5518_);
lean_ctor_set(v_reuseFailAlloc_5541_, 21, v_k_5519_);
lean_ctor_set(v_reuseFailAlloc_5541_, 22, v_H_5520_);
lean_ctor_set(v_reuseFailAlloc_5541_, 23, v_m_5521_);
lean_ctor_set(v_reuseFailAlloc_5541_, 24, v_s_5522_);
lean_ctor_set(v_reuseFailAlloc_5541_, 25, v_S_5523_);
lean_ctor_set(v_reuseFailAlloc_5541_, 26, v_A_5524_);
lean_ctor_set(v_reuseFailAlloc_5541_, 27, v___x_5538_);
lean_ctor_set(v_reuseFailAlloc_5541_, 28, v_N_5525_);
lean_ctor_set(v_reuseFailAlloc_5541_, 29, v_V_5526_);
lean_ctor_set(v_reuseFailAlloc_5541_, 30, v_z_5527_);
lean_ctor_set(v_reuseFailAlloc_5541_, 31, v_zabbrev_5528_);
lean_ctor_set(v_reuseFailAlloc_5541_, 32, v_v_5529_);
lean_ctor_set(v_reuseFailAlloc_5541_, 33, v_O_5530_);
lean_ctor_set(v_reuseFailAlloc_5541_, 34, v_X_5531_);
lean_ctor_set(v_reuseFailAlloc_5541_, 35, v_x_5532_);
lean_ctor_set(v_reuseFailAlloc_5541_, 36, v_Z_5533_);
v___x_5540_ = v_reuseFailAlloc_5541_;
goto v_reusejp_5539_;
}
v_reusejp_5539_:
{
return v___x_5540_;
}
}
}
}
}
case 28:
{
lean_object* v___x_5548_; uint8_t v_isShared_5549_; uint8_t v_isSharedCheck_5597_; 
v_isSharedCheck_5597_ = !lean_is_exclusive(v_modifier_4124_);
if (v_isSharedCheck_5597_ == 0)
{
lean_object* v_unused_5598_; 
v_unused_5598_ = lean_ctor_get(v_modifier_4124_, 0);
lean_dec(v_unused_5598_);
v___x_5548_ = v_modifier_4124_;
v_isShared_5549_ = v_isSharedCheck_5597_;
goto v_resetjp_5547_;
}
else
{
lean_dec(v_modifier_4124_);
v___x_5548_ = lean_box(0);
v_isShared_5549_ = v_isSharedCheck_5597_;
goto v_resetjp_5547_;
}
v_resetjp_5547_:
{
lean_object* v_G_5550_; lean_object* v_y_5551_; lean_object* v_u_5552_; lean_object* v_Y_5553_; lean_object* v_D_5554_; lean_object* v_M_5555_; lean_object* v_L_5556_; lean_object* v_d_5557_; lean_object* v_Q_5558_; lean_object* v_q_5559_; lean_object* v_w_5560_; lean_object* v_W_5561_; lean_object* v_E_5562_; lean_object* v_e_5563_; lean_object* v_c_5564_; lean_object* v_F_5565_; lean_object* v_a_5566_; lean_object* v_b_5567_; lean_object* v_B_5568_; lean_object* v_h_5569_; lean_object* v_K_5570_; lean_object* v_k_5571_; lean_object* v_H_5572_; lean_object* v_m_5573_; lean_object* v_s_5574_; lean_object* v_S_5575_; lean_object* v_A_5576_; lean_object* v_n_5577_; lean_object* v_V_5578_; lean_object* v_z_5579_; lean_object* v_zabbrev_5580_; lean_object* v_v_5581_; lean_object* v_O_5582_; lean_object* v_X_5583_; lean_object* v_x_5584_; lean_object* v_Z_5585_; lean_object* v___x_5587_; uint8_t v_isShared_5588_; uint8_t v_isSharedCheck_5595_; 
v_G_5550_ = lean_ctor_get(v_date_4123_, 0);
v_y_5551_ = lean_ctor_get(v_date_4123_, 1);
v_u_5552_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5553_ = lean_ctor_get(v_date_4123_, 3);
v_D_5554_ = lean_ctor_get(v_date_4123_, 4);
v_M_5555_ = lean_ctor_get(v_date_4123_, 5);
v_L_5556_ = lean_ctor_get(v_date_4123_, 6);
v_d_5557_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5558_ = lean_ctor_get(v_date_4123_, 8);
v_q_5559_ = lean_ctor_get(v_date_4123_, 9);
v_w_5560_ = lean_ctor_get(v_date_4123_, 10);
v_W_5561_ = lean_ctor_get(v_date_4123_, 11);
v_E_5562_ = lean_ctor_get(v_date_4123_, 12);
v_e_5563_ = lean_ctor_get(v_date_4123_, 13);
v_c_5564_ = lean_ctor_get(v_date_4123_, 14);
v_F_5565_ = lean_ctor_get(v_date_4123_, 15);
v_a_5566_ = lean_ctor_get(v_date_4123_, 16);
v_b_5567_ = lean_ctor_get(v_date_4123_, 17);
v_B_5568_ = lean_ctor_get(v_date_4123_, 18);
v_h_5569_ = lean_ctor_get(v_date_4123_, 19);
v_K_5570_ = lean_ctor_get(v_date_4123_, 20);
v_k_5571_ = lean_ctor_get(v_date_4123_, 21);
v_H_5572_ = lean_ctor_get(v_date_4123_, 22);
v_m_5573_ = lean_ctor_get(v_date_4123_, 23);
v_s_5574_ = lean_ctor_get(v_date_4123_, 24);
v_S_5575_ = lean_ctor_get(v_date_4123_, 25);
v_A_5576_ = lean_ctor_get(v_date_4123_, 26);
v_n_5577_ = lean_ctor_get(v_date_4123_, 27);
v_V_5578_ = lean_ctor_get(v_date_4123_, 29);
v_z_5579_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_5580_ = lean_ctor_get(v_date_4123_, 31);
v_v_5581_ = lean_ctor_get(v_date_4123_, 32);
v_O_5582_ = lean_ctor_get(v_date_4123_, 33);
v_X_5583_ = lean_ctor_get(v_date_4123_, 34);
v_x_5584_ = lean_ctor_get(v_date_4123_, 35);
v_Z_5585_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5595_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5595_ == 0)
{
lean_object* v_unused_5596_; 
v_unused_5596_ = lean_ctor_get(v_date_4123_, 28);
lean_dec(v_unused_5596_);
v___x_5587_ = v_date_4123_;
v_isShared_5588_ = v_isSharedCheck_5595_;
goto v_resetjp_5586_;
}
else
{
lean_inc(v_Z_5585_);
lean_inc(v_x_5584_);
lean_inc(v_X_5583_);
lean_inc(v_O_5582_);
lean_inc(v_v_5581_);
lean_inc(v_zabbrev_5580_);
lean_inc(v_z_5579_);
lean_inc(v_V_5578_);
lean_inc(v_n_5577_);
lean_inc(v_A_5576_);
lean_inc(v_S_5575_);
lean_inc(v_s_5574_);
lean_inc(v_m_5573_);
lean_inc(v_H_5572_);
lean_inc(v_k_5571_);
lean_inc(v_K_5570_);
lean_inc(v_h_5569_);
lean_inc(v_B_5568_);
lean_inc(v_b_5567_);
lean_inc(v_a_5566_);
lean_inc(v_F_5565_);
lean_inc(v_c_5564_);
lean_inc(v_e_5563_);
lean_inc(v_E_5562_);
lean_inc(v_W_5561_);
lean_inc(v_w_5560_);
lean_inc(v_q_5559_);
lean_inc(v_Q_5558_);
lean_inc(v_d_5557_);
lean_inc(v_L_5556_);
lean_inc(v_M_5555_);
lean_inc(v_D_5554_);
lean_inc(v_Y_5553_);
lean_inc(v_u_5552_);
lean_inc(v_y_5551_);
lean_inc(v_G_5550_);
lean_dec(v_date_4123_);
v___x_5587_ = lean_box(0);
v_isShared_5588_ = v_isSharedCheck_5595_;
goto v_resetjp_5586_;
}
v_resetjp_5586_:
{
lean_object* v___x_5590_; 
if (v_isShared_5549_ == 0)
{
lean_ctor_set_tag(v___x_5548_, 1);
lean_ctor_set(v___x_5548_, 0, v_data_4125_);
v___x_5590_ = v___x_5548_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v_data_4125_);
v___x_5590_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
lean_object* v___x_5592_; 
if (v_isShared_5588_ == 0)
{
lean_ctor_set(v___x_5587_, 28, v___x_5590_);
v___x_5592_ = v___x_5587_;
goto v_reusejp_5591_;
}
else
{
lean_object* v_reuseFailAlloc_5593_; 
v_reuseFailAlloc_5593_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5593_, 0, v_G_5550_);
lean_ctor_set(v_reuseFailAlloc_5593_, 1, v_y_5551_);
lean_ctor_set(v_reuseFailAlloc_5593_, 2, v_u_5552_);
lean_ctor_set(v_reuseFailAlloc_5593_, 3, v_Y_5553_);
lean_ctor_set(v_reuseFailAlloc_5593_, 4, v_D_5554_);
lean_ctor_set(v_reuseFailAlloc_5593_, 5, v_M_5555_);
lean_ctor_set(v_reuseFailAlloc_5593_, 6, v_L_5556_);
lean_ctor_set(v_reuseFailAlloc_5593_, 7, v_d_5557_);
lean_ctor_set(v_reuseFailAlloc_5593_, 8, v_Q_5558_);
lean_ctor_set(v_reuseFailAlloc_5593_, 9, v_q_5559_);
lean_ctor_set(v_reuseFailAlloc_5593_, 10, v_w_5560_);
lean_ctor_set(v_reuseFailAlloc_5593_, 11, v_W_5561_);
lean_ctor_set(v_reuseFailAlloc_5593_, 12, v_E_5562_);
lean_ctor_set(v_reuseFailAlloc_5593_, 13, v_e_5563_);
lean_ctor_set(v_reuseFailAlloc_5593_, 14, v_c_5564_);
lean_ctor_set(v_reuseFailAlloc_5593_, 15, v_F_5565_);
lean_ctor_set(v_reuseFailAlloc_5593_, 16, v_a_5566_);
lean_ctor_set(v_reuseFailAlloc_5593_, 17, v_b_5567_);
lean_ctor_set(v_reuseFailAlloc_5593_, 18, v_B_5568_);
lean_ctor_set(v_reuseFailAlloc_5593_, 19, v_h_5569_);
lean_ctor_set(v_reuseFailAlloc_5593_, 20, v_K_5570_);
lean_ctor_set(v_reuseFailAlloc_5593_, 21, v_k_5571_);
lean_ctor_set(v_reuseFailAlloc_5593_, 22, v_H_5572_);
lean_ctor_set(v_reuseFailAlloc_5593_, 23, v_m_5573_);
lean_ctor_set(v_reuseFailAlloc_5593_, 24, v_s_5574_);
lean_ctor_set(v_reuseFailAlloc_5593_, 25, v_S_5575_);
lean_ctor_set(v_reuseFailAlloc_5593_, 26, v_A_5576_);
lean_ctor_set(v_reuseFailAlloc_5593_, 27, v_n_5577_);
lean_ctor_set(v_reuseFailAlloc_5593_, 28, v___x_5590_);
lean_ctor_set(v_reuseFailAlloc_5593_, 29, v_V_5578_);
lean_ctor_set(v_reuseFailAlloc_5593_, 30, v_z_5579_);
lean_ctor_set(v_reuseFailAlloc_5593_, 31, v_zabbrev_5580_);
lean_ctor_set(v_reuseFailAlloc_5593_, 32, v_v_5581_);
lean_ctor_set(v_reuseFailAlloc_5593_, 33, v_O_5582_);
lean_ctor_set(v_reuseFailAlloc_5593_, 34, v_X_5583_);
lean_ctor_set(v_reuseFailAlloc_5593_, 35, v_x_5584_);
lean_ctor_set(v_reuseFailAlloc_5593_, 36, v_Z_5585_);
v___x_5592_ = v_reuseFailAlloc_5593_;
goto v_reusejp_5591_;
}
v_reusejp_5591_:
{
return v___x_5592_;
}
}
}
}
}
case 29:
{
lean_object* v_G_5599_; lean_object* v_y_5600_; lean_object* v_u_5601_; lean_object* v_Y_5602_; lean_object* v_D_5603_; lean_object* v_M_5604_; lean_object* v_L_5605_; lean_object* v_d_5606_; lean_object* v_Q_5607_; lean_object* v_q_5608_; lean_object* v_w_5609_; lean_object* v_W_5610_; lean_object* v_E_5611_; lean_object* v_e_5612_; lean_object* v_c_5613_; lean_object* v_F_5614_; lean_object* v_a_5615_; lean_object* v_b_5616_; lean_object* v_B_5617_; lean_object* v_h_5618_; lean_object* v_K_5619_; lean_object* v_k_5620_; lean_object* v_H_5621_; lean_object* v_m_5622_; lean_object* v_s_5623_; lean_object* v_S_5624_; lean_object* v_A_5625_; lean_object* v_n_5626_; lean_object* v_N_5627_; lean_object* v_z_5628_; lean_object* v_zabbrev_5629_; lean_object* v_v_5630_; lean_object* v_O_5631_; lean_object* v_X_5632_; lean_object* v_x_5633_; lean_object* v_Z_5634_; lean_object* v___x_5636_; uint8_t v_isShared_5637_; uint8_t v_isSharedCheck_5642_; 
lean_dec_ref_known(v_modifier_4124_, 0);
v_G_5599_ = lean_ctor_get(v_date_4123_, 0);
v_y_5600_ = lean_ctor_get(v_date_4123_, 1);
v_u_5601_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5602_ = lean_ctor_get(v_date_4123_, 3);
v_D_5603_ = lean_ctor_get(v_date_4123_, 4);
v_M_5604_ = lean_ctor_get(v_date_4123_, 5);
v_L_5605_ = lean_ctor_get(v_date_4123_, 6);
v_d_5606_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5607_ = lean_ctor_get(v_date_4123_, 8);
v_q_5608_ = lean_ctor_get(v_date_4123_, 9);
v_w_5609_ = lean_ctor_get(v_date_4123_, 10);
v_W_5610_ = lean_ctor_get(v_date_4123_, 11);
v_E_5611_ = lean_ctor_get(v_date_4123_, 12);
v_e_5612_ = lean_ctor_get(v_date_4123_, 13);
v_c_5613_ = lean_ctor_get(v_date_4123_, 14);
v_F_5614_ = lean_ctor_get(v_date_4123_, 15);
v_a_5615_ = lean_ctor_get(v_date_4123_, 16);
v_b_5616_ = lean_ctor_get(v_date_4123_, 17);
v_B_5617_ = lean_ctor_get(v_date_4123_, 18);
v_h_5618_ = lean_ctor_get(v_date_4123_, 19);
v_K_5619_ = lean_ctor_get(v_date_4123_, 20);
v_k_5620_ = lean_ctor_get(v_date_4123_, 21);
v_H_5621_ = lean_ctor_get(v_date_4123_, 22);
v_m_5622_ = lean_ctor_get(v_date_4123_, 23);
v_s_5623_ = lean_ctor_get(v_date_4123_, 24);
v_S_5624_ = lean_ctor_get(v_date_4123_, 25);
v_A_5625_ = lean_ctor_get(v_date_4123_, 26);
v_n_5626_ = lean_ctor_get(v_date_4123_, 27);
v_N_5627_ = lean_ctor_get(v_date_4123_, 28);
v_z_5628_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_5629_ = lean_ctor_get(v_date_4123_, 31);
v_v_5630_ = lean_ctor_get(v_date_4123_, 32);
v_O_5631_ = lean_ctor_get(v_date_4123_, 33);
v_X_5632_ = lean_ctor_get(v_date_4123_, 34);
v_x_5633_ = lean_ctor_get(v_date_4123_, 35);
v_Z_5634_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5642_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5642_ == 0)
{
lean_object* v_unused_5643_; 
v_unused_5643_ = lean_ctor_get(v_date_4123_, 29);
lean_dec(v_unused_5643_);
v___x_5636_ = v_date_4123_;
v_isShared_5637_ = v_isSharedCheck_5642_;
goto v_resetjp_5635_;
}
else
{
lean_inc(v_Z_5634_);
lean_inc(v_x_5633_);
lean_inc(v_X_5632_);
lean_inc(v_O_5631_);
lean_inc(v_v_5630_);
lean_inc(v_zabbrev_5629_);
lean_inc(v_z_5628_);
lean_inc(v_N_5627_);
lean_inc(v_n_5626_);
lean_inc(v_A_5625_);
lean_inc(v_S_5624_);
lean_inc(v_s_5623_);
lean_inc(v_m_5622_);
lean_inc(v_H_5621_);
lean_inc(v_k_5620_);
lean_inc(v_K_5619_);
lean_inc(v_h_5618_);
lean_inc(v_B_5617_);
lean_inc(v_b_5616_);
lean_inc(v_a_5615_);
lean_inc(v_F_5614_);
lean_inc(v_c_5613_);
lean_inc(v_e_5612_);
lean_inc(v_E_5611_);
lean_inc(v_W_5610_);
lean_inc(v_w_5609_);
lean_inc(v_q_5608_);
lean_inc(v_Q_5607_);
lean_inc(v_d_5606_);
lean_inc(v_L_5605_);
lean_inc(v_M_5604_);
lean_inc(v_D_5603_);
lean_inc(v_Y_5602_);
lean_inc(v_u_5601_);
lean_inc(v_y_5600_);
lean_inc(v_G_5599_);
lean_dec(v_date_4123_);
v___x_5636_ = lean_box(0);
v_isShared_5637_ = v_isSharedCheck_5642_;
goto v_resetjp_5635_;
}
v_resetjp_5635_:
{
lean_object* v___x_5638_; lean_object* v___x_5640_; 
v___x_5638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5638_, 0, v_data_4125_);
if (v_isShared_5637_ == 0)
{
lean_ctor_set(v___x_5636_, 29, v___x_5638_);
v___x_5640_ = v___x_5636_;
goto v_reusejp_5639_;
}
else
{
lean_object* v_reuseFailAlloc_5641_; 
v_reuseFailAlloc_5641_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5641_, 0, v_G_5599_);
lean_ctor_set(v_reuseFailAlloc_5641_, 1, v_y_5600_);
lean_ctor_set(v_reuseFailAlloc_5641_, 2, v_u_5601_);
lean_ctor_set(v_reuseFailAlloc_5641_, 3, v_Y_5602_);
lean_ctor_set(v_reuseFailAlloc_5641_, 4, v_D_5603_);
lean_ctor_set(v_reuseFailAlloc_5641_, 5, v_M_5604_);
lean_ctor_set(v_reuseFailAlloc_5641_, 6, v_L_5605_);
lean_ctor_set(v_reuseFailAlloc_5641_, 7, v_d_5606_);
lean_ctor_set(v_reuseFailAlloc_5641_, 8, v_Q_5607_);
lean_ctor_set(v_reuseFailAlloc_5641_, 9, v_q_5608_);
lean_ctor_set(v_reuseFailAlloc_5641_, 10, v_w_5609_);
lean_ctor_set(v_reuseFailAlloc_5641_, 11, v_W_5610_);
lean_ctor_set(v_reuseFailAlloc_5641_, 12, v_E_5611_);
lean_ctor_set(v_reuseFailAlloc_5641_, 13, v_e_5612_);
lean_ctor_set(v_reuseFailAlloc_5641_, 14, v_c_5613_);
lean_ctor_set(v_reuseFailAlloc_5641_, 15, v_F_5614_);
lean_ctor_set(v_reuseFailAlloc_5641_, 16, v_a_5615_);
lean_ctor_set(v_reuseFailAlloc_5641_, 17, v_b_5616_);
lean_ctor_set(v_reuseFailAlloc_5641_, 18, v_B_5617_);
lean_ctor_set(v_reuseFailAlloc_5641_, 19, v_h_5618_);
lean_ctor_set(v_reuseFailAlloc_5641_, 20, v_K_5619_);
lean_ctor_set(v_reuseFailAlloc_5641_, 21, v_k_5620_);
lean_ctor_set(v_reuseFailAlloc_5641_, 22, v_H_5621_);
lean_ctor_set(v_reuseFailAlloc_5641_, 23, v_m_5622_);
lean_ctor_set(v_reuseFailAlloc_5641_, 24, v_s_5623_);
lean_ctor_set(v_reuseFailAlloc_5641_, 25, v_S_5624_);
lean_ctor_set(v_reuseFailAlloc_5641_, 26, v_A_5625_);
lean_ctor_set(v_reuseFailAlloc_5641_, 27, v_n_5626_);
lean_ctor_set(v_reuseFailAlloc_5641_, 28, v_N_5627_);
lean_ctor_set(v_reuseFailAlloc_5641_, 29, v___x_5638_);
lean_ctor_set(v_reuseFailAlloc_5641_, 30, v_z_5628_);
lean_ctor_set(v_reuseFailAlloc_5641_, 31, v_zabbrev_5629_);
lean_ctor_set(v_reuseFailAlloc_5641_, 32, v_v_5630_);
lean_ctor_set(v_reuseFailAlloc_5641_, 33, v_O_5631_);
lean_ctor_set(v_reuseFailAlloc_5641_, 34, v_X_5632_);
lean_ctor_set(v_reuseFailAlloc_5641_, 35, v_x_5633_);
lean_ctor_set(v_reuseFailAlloc_5641_, 36, v_Z_5634_);
v___x_5640_ = v_reuseFailAlloc_5641_;
goto v_reusejp_5639_;
}
v_reusejp_5639_:
{
return v___x_5640_;
}
}
}
case 30:
{
uint8_t v_presentation_5644_; 
v_presentation_5644_ = lean_ctor_get_uint8(v_modifier_4124_, 0);
lean_dec_ref_known(v_modifier_4124_, 0);
if (v_presentation_5644_ == 0)
{
lean_object* v_G_5645_; lean_object* v_y_5646_; lean_object* v_u_5647_; lean_object* v_Y_5648_; lean_object* v_D_5649_; lean_object* v_M_5650_; lean_object* v_L_5651_; lean_object* v_d_5652_; lean_object* v_Q_5653_; lean_object* v_q_5654_; lean_object* v_w_5655_; lean_object* v_W_5656_; lean_object* v_E_5657_; lean_object* v_e_5658_; lean_object* v_c_5659_; lean_object* v_F_5660_; lean_object* v_a_5661_; lean_object* v_b_5662_; lean_object* v_B_5663_; lean_object* v_h_5664_; lean_object* v_K_5665_; lean_object* v_k_5666_; lean_object* v_H_5667_; lean_object* v_m_5668_; lean_object* v_s_5669_; lean_object* v_S_5670_; lean_object* v_A_5671_; lean_object* v_n_5672_; lean_object* v_N_5673_; lean_object* v_V_5674_; lean_object* v_z_5675_; lean_object* v_v_5676_; lean_object* v_O_5677_; lean_object* v_X_5678_; lean_object* v_x_5679_; lean_object* v_Z_5680_; lean_object* v___x_5682_; uint8_t v_isShared_5683_; uint8_t v_isSharedCheck_5688_; 
v_G_5645_ = lean_ctor_get(v_date_4123_, 0);
v_y_5646_ = lean_ctor_get(v_date_4123_, 1);
v_u_5647_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5648_ = lean_ctor_get(v_date_4123_, 3);
v_D_5649_ = lean_ctor_get(v_date_4123_, 4);
v_M_5650_ = lean_ctor_get(v_date_4123_, 5);
v_L_5651_ = lean_ctor_get(v_date_4123_, 6);
v_d_5652_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5653_ = lean_ctor_get(v_date_4123_, 8);
v_q_5654_ = lean_ctor_get(v_date_4123_, 9);
v_w_5655_ = lean_ctor_get(v_date_4123_, 10);
v_W_5656_ = lean_ctor_get(v_date_4123_, 11);
v_E_5657_ = lean_ctor_get(v_date_4123_, 12);
v_e_5658_ = lean_ctor_get(v_date_4123_, 13);
v_c_5659_ = lean_ctor_get(v_date_4123_, 14);
v_F_5660_ = lean_ctor_get(v_date_4123_, 15);
v_a_5661_ = lean_ctor_get(v_date_4123_, 16);
v_b_5662_ = lean_ctor_get(v_date_4123_, 17);
v_B_5663_ = lean_ctor_get(v_date_4123_, 18);
v_h_5664_ = lean_ctor_get(v_date_4123_, 19);
v_K_5665_ = lean_ctor_get(v_date_4123_, 20);
v_k_5666_ = lean_ctor_get(v_date_4123_, 21);
v_H_5667_ = lean_ctor_get(v_date_4123_, 22);
v_m_5668_ = lean_ctor_get(v_date_4123_, 23);
v_s_5669_ = lean_ctor_get(v_date_4123_, 24);
v_S_5670_ = lean_ctor_get(v_date_4123_, 25);
v_A_5671_ = lean_ctor_get(v_date_4123_, 26);
v_n_5672_ = lean_ctor_get(v_date_4123_, 27);
v_N_5673_ = lean_ctor_get(v_date_4123_, 28);
v_V_5674_ = lean_ctor_get(v_date_4123_, 29);
v_z_5675_ = lean_ctor_get(v_date_4123_, 30);
v_v_5676_ = lean_ctor_get(v_date_4123_, 32);
v_O_5677_ = lean_ctor_get(v_date_4123_, 33);
v_X_5678_ = lean_ctor_get(v_date_4123_, 34);
v_x_5679_ = lean_ctor_get(v_date_4123_, 35);
v_Z_5680_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5688_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5688_ == 0)
{
lean_object* v_unused_5689_; 
v_unused_5689_ = lean_ctor_get(v_date_4123_, 31);
lean_dec(v_unused_5689_);
v___x_5682_ = v_date_4123_;
v_isShared_5683_ = v_isSharedCheck_5688_;
goto v_resetjp_5681_;
}
else
{
lean_inc(v_Z_5680_);
lean_inc(v_x_5679_);
lean_inc(v_X_5678_);
lean_inc(v_O_5677_);
lean_inc(v_v_5676_);
lean_inc(v_z_5675_);
lean_inc(v_V_5674_);
lean_inc(v_N_5673_);
lean_inc(v_n_5672_);
lean_inc(v_A_5671_);
lean_inc(v_S_5670_);
lean_inc(v_s_5669_);
lean_inc(v_m_5668_);
lean_inc(v_H_5667_);
lean_inc(v_k_5666_);
lean_inc(v_K_5665_);
lean_inc(v_h_5664_);
lean_inc(v_B_5663_);
lean_inc(v_b_5662_);
lean_inc(v_a_5661_);
lean_inc(v_F_5660_);
lean_inc(v_c_5659_);
lean_inc(v_e_5658_);
lean_inc(v_E_5657_);
lean_inc(v_W_5656_);
lean_inc(v_w_5655_);
lean_inc(v_q_5654_);
lean_inc(v_Q_5653_);
lean_inc(v_d_5652_);
lean_inc(v_L_5651_);
lean_inc(v_M_5650_);
lean_inc(v_D_5649_);
lean_inc(v_Y_5648_);
lean_inc(v_u_5647_);
lean_inc(v_y_5646_);
lean_inc(v_G_5645_);
lean_dec(v_date_4123_);
v___x_5682_ = lean_box(0);
v_isShared_5683_ = v_isSharedCheck_5688_;
goto v_resetjp_5681_;
}
v_resetjp_5681_:
{
lean_object* v___x_5684_; lean_object* v___x_5686_; 
v___x_5684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5684_, 0, v_data_4125_);
if (v_isShared_5683_ == 0)
{
lean_ctor_set(v___x_5682_, 31, v___x_5684_);
v___x_5686_ = v___x_5682_;
goto v_reusejp_5685_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v_G_5645_);
lean_ctor_set(v_reuseFailAlloc_5687_, 1, v_y_5646_);
lean_ctor_set(v_reuseFailAlloc_5687_, 2, v_u_5647_);
lean_ctor_set(v_reuseFailAlloc_5687_, 3, v_Y_5648_);
lean_ctor_set(v_reuseFailAlloc_5687_, 4, v_D_5649_);
lean_ctor_set(v_reuseFailAlloc_5687_, 5, v_M_5650_);
lean_ctor_set(v_reuseFailAlloc_5687_, 6, v_L_5651_);
lean_ctor_set(v_reuseFailAlloc_5687_, 7, v_d_5652_);
lean_ctor_set(v_reuseFailAlloc_5687_, 8, v_Q_5653_);
lean_ctor_set(v_reuseFailAlloc_5687_, 9, v_q_5654_);
lean_ctor_set(v_reuseFailAlloc_5687_, 10, v_w_5655_);
lean_ctor_set(v_reuseFailAlloc_5687_, 11, v_W_5656_);
lean_ctor_set(v_reuseFailAlloc_5687_, 12, v_E_5657_);
lean_ctor_set(v_reuseFailAlloc_5687_, 13, v_e_5658_);
lean_ctor_set(v_reuseFailAlloc_5687_, 14, v_c_5659_);
lean_ctor_set(v_reuseFailAlloc_5687_, 15, v_F_5660_);
lean_ctor_set(v_reuseFailAlloc_5687_, 16, v_a_5661_);
lean_ctor_set(v_reuseFailAlloc_5687_, 17, v_b_5662_);
lean_ctor_set(v_reuseFailAlloc_5687_, 18, v_B_5663_);
lean_ctor_set(v_reuseFailAlloc_5687_, 19, v_h_5664_);
lean_ctor_set(v_reuseFailAlloc_5687_, 20, v_K_5665_);
lean_ctor_set(v_reuseFailAlloc_5687_, 21, v_k_5666_);
lean_ctor_set(v_reuseFailAlloc_5687_, 22, v_H_5667_);
lean_ctor_set(v_reuseFailAlloc_5687_, 23, v_m_5668_);
lean_ctor_set(v_reuseFailAlloc_5687_, 24, v_s_5669_);
lean_ctor_set(v_reuseFailAlloc_5687_, 25, v_S_5670_);
lean_ctor_set(v_reuseFailAlloc_5687_, 26, v_A_5671_);
lean_ctor_set(v_reuseFailAlloc_5687_, 27, v_n_5672_);
lean_ctor_set(v_reuseFailAlloc_5687_, 28, v_N_5673_);
lean_ctor_set(v_reuseFailAlloc_5687_, 29, v_V_5674_);
lean_ctor_set(v_reuseFailAlloc_5687_, 30, v_z_5675_);
lean_ctor_set(v_reuseFailAlloc_5687_, 31, v___x_5684_);
lean_ctor_set(v_reuseFailAlloc_5687_, 32, v_v_5676_);
lean_ctor_set(v_reuseFailAlloc_5687_, 33, v_O_5677_);
lean_ctor_set(v_reuseFailAlloc_5687_, 34, v_X_5678_);
lean_ctor_set(v_reuseFailAlloc_5687_, 35, v_x_5679_);
lean_ctor_set(v_reuseFailAlloc_5687_, 36, v_Z_5680_);
v___x_5686_ = v_reuseFailAlloc_5687_;
goto v_reusejp_5685_;
}
v_reusejp_5685_:
{
return v___x_5686_;
}
}
}
else
{
lean_object* v_G_5690_; lean_object* v_y_5691_; lean_object* v_u_5692_; lean_object* v_Y_5693_; lean_object* v_D_5694_; lean_object* v_M_5695_; lean_object* v_L_5696_; lean_object* v_d_5697_; lean_object* v_Q_5698_; lean_object* v_q_5699_; lean_object* v_w_5700_; lean_object* v_W_5701_; lean_object* v_E_5702_; lean_object* v_e_5703_; lean_object* v_c_5704_; lean_object* v_F_5705_; lean_object* v_a_5706_; lean_object* v_b_5707_; lean_object* v_B_5708_; lean_object* v_h_5709_; lean_object* v_K_5710_; lean_object* v_k_5711_; lean_object* v_H_5712_; lean_object* v_m_5713_; lean_object* v_s_5714_; lean_object* v_S_5715_; lean_object* v_A_5716_; lean_object* v_n_5717_; lean_object* v_N_5718_; lean_object* v_V_5719_; lean_object* v_zabbrev_5720_; lean_object* v_v_5721_; lean_object* v_O_5722_; lean_object* v_X_5723_; lean_object* v_x_5724_; lean_object* v_Z_5725_; lean_object* v___x_5727_; uint8_t v_isShared_5728_; uint8_t v_isSharedCheck_5733_; 
v_G_5690_ = lean_ctor_get(v_date_4123_, 0);
v_y_5691_ = lean_ctor_get(v_date_4123_, 1);
v_u_5692_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5693_ = lean_ctor_get(v_date_4123_, 3);
v_D_5694_ = lean_ctor_get(v_date_4123_, 4);
v_M_5695_ = lean_ctor_get(v_date_4123_, 5);
v_L_5696_ = lean_ctor_get(v_date_4123_, 6);
v_d_5697_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5698_ = lean_ctor_get(v_date_4123_, 8);
v_q_5699_ = lean_ctor_get(v_date_4123_, 9);
v_w_5700_ = lean_ctor_get(v_date_4123_, 10);
v_W_5701_ = lean_ctor_get(v_date_4123_, 11);
v_E_5702_ = lean_ctor_get(v_date_4123_, 12);
v_e_5703_ = lean_ctor_get(v_date_4123_, 13);
v_c_5704_ = lean_ctor_get(v_date_4123_, 14);
v_F_5705_ = lean_ctor_get(v_date_4123_, 15);
v_a_5706_ = lean_ctor_get(v_date_4123_, 16);
v_b_5707_ = lean_ctor_get(v_date_4123_, 17);
v_B_5708_ = lean_ctor_get(v_date_4123_, 18);
v_h_5709_ = lean_ctor_get(v_date_4123_, 19);
v_K_5710_ = lean_ctor_get(v_date_4123_, 20);
v_k_5711_ = lean_ctor_get(v_date_4123_, 21);
v_H_5712_ = lean_ctor_get(v_date_4123_, 22);
v_m_5713_ = lean_ctor_get(v_date_4123_, 23);
v_s_5714_ = lean_ctor_get(v_date_4123_, 24);
v_S_5715_ = lean_ctor_get(v_date_4123_, 25);
v_A_5716_ = lean_ctor_get(v_date_4123_, 26);
v_n_5717_ = lean_ctor_get(v_date_4123_, 27);
v_N_5718_ = lean_ctor_get(v_date_4123_, 28);
v_V_5719_ = lean_ctor_get(v_date_4123_, 29);
v_zabbrev_5720_ = lean_ctor_get(v_date_4123_, 31);
v_v_5721_ = lean_ctor_get(v_date_4123_, 32);
v_O_5722_ = lean_ctor_get(v_date_4123_, 33);
v_X_5723_ = lean_ctor_get(v_date_4123_, 34);
v_x_5724_ = lean_ctor_get(v_date_4123_, 35);
v_Z_5725_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5733_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5733_ == 0)
{
lean_object* v_unused_5734_; 
v_unused_5734_ = lean_ctor_get(v_date_4123_, 30);
lean_dec(v_unused_5734_);
v___x_5727_ = v_date_4123_;
v_isShared_5728_ = v_isSharedCheck_5733_;
goto v_resetjp_5726_;
}
else
{
lean_inc(v_Z_5725_);
lean_inc(v_x_5724_);
lean_inc(v_X_5723_);
lean_inc(v_O_5722_);
lean_inc(v_v_5721_);
lean_inc(v_zabbrev_5720_);
lean_inc(v_V_5719_);
lean_inc(v_N_5718_);
lean_inc(v_n_5717_);
lean_inc(v_A_5716_);
lean_inc(v_S_5715_);
lean_inc(v_s_5714_);
lean_inc(v_m_5713_);
lean_inc(v_H_5712_);
lean_inc(v_k_5711_);
lean_inc(v_K_5710_);
lean_inc(v_h_5709_);
lean_inc(v_B_5708_);
lean_inc(v_b_5707_);
lean_inc(v_a_5706_);
lean_inc(v_F_5705_);
lean_inc(v_c_5704_);
lean_inc(v_e_5703_);
lean_inc(v_E_5702_);
lean_inc(v_W_5701_);
lean_inc(v_w_5700_);
lean_inc(v_q_5699_);
lean_inc(v_Q_5698_);
lean_inc(v_d_5697_);
lean_inc(v_L_5696_);
lean_inc(v_M_5695_);
lean_inc(v_D_5694_);
lean_inc(v_Y_5693_);
lean_inc(v_u_5692_);
lean_inc(v_y_5691_);
lean_inc(v_G_5690_);
lean_dec(v_date_4123_);
v___x_5727_ = lean_box(0);
v_isShared_5728_ = v_isSharedCheck_5733_;
goto v_resetjp_5726_;
}
v_resetjp_5726_:
{
lean_object* v___x_5729_; lean_object* v___x_5731_; 
v___x_5729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5729_, 0, v_data_4125_);
if (v_isShared_5728_ == 0)
{
lean_ctor_set(v___x_5727_, 30, v___x_5729_);
v___x_5731_ = v___x_5727_;
goto v_reusejp_5730_;
}
else
{
lean_object* v_reuseFailAlloc_5732_; 
v_reuseFailAlloc_5732_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5732_, 0, v_G_5690_);
lean_ctor_set(v_reuseFailAlloc_5732_, 1, v_y_5691_);
lean_ctor_set(v_reuseFailAlloc_5732_, 2, v_u_5692_);
lean_ctor_set(v_reuseFailAlloc_5732_, 3, v_Y_5693_);
lean_ctor_set(v_reuseFailAlloc_5732_, 4, v_D_5694_);
lean_ctor_set(v_reuseFailAlloc_5732_, 5, v_M_5695_);
lean_ctor_set(v_reuseFailAlloc_5732_, 6, v_L_5696_);
lean_ctor_set(v_reuseFailAlloc_5732_, 7, v_d_5697_);
lean_ctor_set(v_reuseFailAlloc_5732_, 8, v_Q_5698_);
lean_ctor_set(v_reuseFailAlloc_5732_, 9, v_q_5699_);
lean_ctor_set(v_reuseFailAlloc_5732_, 10, v_w_5700_);
lean_ctor_set(v_reuseFailAlloc_5732_, 11, v_W_5701_);
lean_ctor_set(v_reuseFailAlloc_5732_, 12, v_E_5702_);
lean_ctor_set(v_reuseFailAlloc_5732_, 13, v_e_5703_);
lean_ctor_set(v_reuseFailAlloc_5732_, 14, v_c_5704_);
lean_ctor_set(v_reuseFailAlloc_5732_, 15, v_F_5705_);
lean_ctor_set(v_reuseFailAlloc_5732_, 16, v_a_5706_);
lean_ctor_set(v_reuseFailAlloc_5732_, 17, v_b_5707_);
lean_ctor_set(v_reuseFailAlloc_5732_, 18, v_B_5708_);
lean_ctor_set(v_reuseFailAlloc_5732_, 19, v_h_5709_);
lean_ctor_set(v_reuseFailAlloc_5732_, 20, v_K_5710_);
lean_ctor_set(v_reuseFailAlloc_5732_, 21, v_k_5711_);
lean_ctor_set(v_reuseFailAlloc_5732_, 22, v_H_5712_);
lean_ctor_set(v_reuseFailAlloc_5732_, 23, v_m_5713_);
lean_ctor_set(v_reuseFailAlloc_5732_, 24, v_s_5714_);
lean_ctor_set(v_reuseFailAlloc_5732_, 25, v_S_5715_);
lean_ctor_set(v_reuseFailAlloc_5732_, 26, v_A_5716_);
lean_ctor_set(v_reuseFailAlloc_5732_, 27, v_n_5717_);
lean_ctor_set(v_reuseFailAlloc_5732_, 28, v_N_5718_);
lean_ctor_set(v_reuseFailAlloc_5732_, 29, v_V_5719_);
lean_ctor_set(v_reuseFailAlloc_5732_, 30, v___x_5729_);
lean_ctor_set(v_reuseFailAlloc_5732_, 31, v_zabbrev_5720_);
lean_ctor_set(v_reuseFailAlloc_5732_, 32, v_v_5721_);
lean_ctor_set(v_reuseFailAlloc_5732_, 33, v_O_5722_);
lean_ctor_set(v_reuseFailAlloc_5732_, 34, v_X_5723_);
lean_ctor_set(v_reuseFailAlloc_5732_, 35, v_x_5724_);
lean_ctor_set(v_reuseFailAlloc_5732_, 36, v_Z_5725_);
v___x_5731_ = v_reuseFailAlloc_5732_;
goto v_reusejp_5730_;
}
v_reusejp_5730_:
{
return v___x_5731_;
}
}
}
}
case 31:
{
uint8_t v_presentation_5735_; 
v_presentation_5735_ = lean_ctor_get_uint8(v_modifier_4124_, 0);
lean_dec_ref_known(v_modifier_4124_, 0);
if (v_presentation_5735_ == 0)
{
lean_object* v_G_5736_; lean_object* v_y_5737_; lean_object* v_u_5738_; lean_object* v_Y_5739_; lean_object* v_D_5740_; lean_object* v_M_5741_; lean_object* v_L_5742_; lean_object* v_d_5743_; lean_object* v_Q_5744_; lean_object* v_q_5745_; lean_object* v_w_5746_; lean_object* v_W_5747_; lean_object* v_E_5748_; lean_object* v_e_5749_; lean_object* v_c_5750_; lean_object* v_F_5751_; lean_object* v_a_5752_; lean_object* v_b_5753_; lean_object* v_B_5754_; lean_object* v_h_5755_; lean_object* v_K_5756_; lean_object* v_k_5757_; lean_object* v_H_5758_; lean_object* v_m_5759_; lean_object* v_s_5760_; lean_object* v_S_5761_; lean_object* v_A_5762_; lean_object* v_n_5763_; lean_object* v_N_5764_; lean_object* v_V_5765_; lean_object* v_z_5766_; lean_object* v_v_5767_; lean_object* v_O_5768_; lean_object* v_X_5769_; lean_object* v_x_5770_; lean_object* v_Z_5771_; lean_object* v___x_5773_; uint8_t v_isShared_5774_; uint8_t v_isSharedCheck_5779_; 
v_G_5736_ = lean_ctor_get(v_date_4123_, 0);
v_y_5737_ = lean_ctor_get(v_date_4123_, 1);
v_u_5738_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5739_ = lean_ctor_get(v_date_4123_, 3);
v_D_5740_ = lean_ctor_get(v_date_4123_, 4);
v_M_5741_ = lean_ctor_get(v_date_4123_, 5);
v_L_5742_ = lean_ctor_get(v_date_4123_, 6);
v_d_5743_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5744_ = lean_ctor_get(v_date_4123_, 8);
v_q_5745_ = lean_ctor_get(v_date_4123_, 9);
v_w_5746_ = lean_ctor_get(v_date_4123_, 10);
v_W_5747_ = lean_ctor_get(v_date_4123_, 11);
v_E_5748_ = lean_ctor_get(v_date_4123_, 12);
v_e_5749_ = lean_ctor_get(v_date_4123_, 13);
v_c_5750_ = lean_ctor_get(v_date_4123_, 14);
v_F_5751_ = lean_ctor_get(v_date_4123_, 15);
v_a_5752_ = lean_ctor_get(v_date_4123_, 16);
v_b_5753_ = lean_ctor_get(v_date_4123_, 17);
v_B_5754_ = lean_ctor_get(v_date_4123_, 18);
v_h_5755_ = lean_ctor_get(v_date_4123_, 19);
v_K_5756_ = lean_ctor_get(v_date_4123_, 20);
v_k_5757_ = lean_ctor_get(v_date_4123_, 21);
v_H_5758_ = lean_ctor_get(v_date_4123_, 22);
v_m_5759_ = lean_ctor_get(v_date_4123_, 23);
v_s_5760_ = lean_ctor_get(v_date_4123_, 24);
v_S_5761_ = lean_ctor_get(v_date_4123_, 25);
v_A_5762_ = lean_ctor_get(v_date_4123_, 26);
v_n_5763_ = lean_ctor_get(v_date_4123_, 27);
v_N_5764_ = lean_ctor_get(v_date_4123_, 28);
v_V_5765_ = lean_ctor_get(v_date_4123_, 29);
v_z_5766_ = lean_ctor_get(v_date_4123_, 30);
v_v_5767_ = lean_ctor_get(v_date_4123_, 32);
v_O_5768_ = lean_ctor_get(v_date_4123_, 33);
v_X_5769_ = lean_ctor_get(v_date_4123_, 34);
v_x_5770_ = lean_ctor_get(v_date_4123_, 35);
v_Z_5771_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5779_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5779_ == 0)
{
lean_object* v_unused_5780_; 
v_unused_5780_ = lean_ctor_get(v_date_4123_, 31);
lean_dec(v_unused_5780_);
v___x_5773_ = v_date_4123_;
v_isShared_5774_ = v_isSharedCheck_5779_;
goto v_resetjp_5772_;
}
else
{
lean_inc(v_Z_5771_);
lean_inc(v_x_5770_);
lean_inc(v_X_5769_);
lean_inc(v_O_5768_);
lean_inc(v_v_5767_);
lean_inc(v_z_5766_);
lean_inc(v_V_5765_);
lean_inc(v_N_5764_);
lean_inc(v_n_5763_);
lean_inc(v_A_5762_);
lean_inc(v_S_5761_);
lean_inc(v_s_5760_);
lean_inc(v_m_5759_);
lean_inc(v_H_5758_);
lean_inc(v_k_5757_);
lean_inc(v_K_5756_);
lean_inc(v_h_5755_);
lean_inc(v_B_5754_);
lean_inc(v_b_5753_);
lean_inc(v_a_5752_);
lean_inc(v_F_5751_);
lean_inc(v_c_5750_);
lean_inc(v_e_5749_);
lean_inc(v_E_5748_);
lean_inc(v_W_5747_);
lean_inc(v_w_5746_);
lean_inc(v_q_5745_);
lean_inc(v_Q_5744_);
lean_inc(v_d_5743_);
lean_inc(v_L_5742_);
lean_inc(v_M_5741_);
lean_inc(v_D_5740_);
lean_inc(v_Y_5739_);
lean_inc(v_u_5738_);
lean_inc(v_y_5737_);
lean_inc(v_G_5736_);
lean_dec(v_date_4123_);
v___x_5773_ = lean_box(0);
v_isShared_5774_ = v_isSharedCheck_5779_;
goto v_resetjp_5772_;
}
v_resetjp_5772_:
{
lean_object* v___x_5775_; lean_object* v___x_5777_; 
v___x_5775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5775_, 0, v_data_4125_);
if (v_isShared_5774_ == 0)
{
lean_ctor_set(v___x_5773_, 31, v___x_5775_);
v___x_5777_ = v___x_5773_;
goto v_reusejp_5776_;
}
else
{
lean_object* v_reuseFailAlloc_5778_; 
v_reuseFailAlloc_5778_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5778_, 0, v_G_5736_);
lean_ctor_set(v_reuseFailAlloc_5778_, 1, v_y_5737_);
lean_ctor_set(v_reuseFailAlloc_5778_, 2, v_u_5738_);
lean_ctor_set(v_reuseFailAlloc_5778_, 3, v_Y_5739_);
lean_ctor_set(v_reuseFailAlloc_5778_, 4, v_D_5740_);
lean_ctor_set(v_reuseFailAlloc_5778_, 5, v_M_5741_);
lean_ctor_set(v_reuseFailAlloc_5778_, 6, v_L_5742_);
lean_ctor_set(v_reuseFailAlloc_5778_, 7, v_d_5743_);
lean_ctor_set(v_reuseFailAlloc_5778_, 8, v_Q_5744_);
lean_ctor_set(v_reuseFailAlloc_5778_, 9, v_q_5745_);
lean_ctor_set(v_reuseFailAlloc_5778_, 10, v_w_5746_);
lean_ctor_set(v_reuseFailAlloc_5778_, 11, v_W_5747_);
lean_ctor_set(v_reuseFailAlloc_5778_, 12, v_E_5748_);
lean_ctor_set(v_reuseFailAlloc_5778_, 13, v_e_5749_);
lean_ctor_set(v_reuseFailAlloc_5778_, 14, v_c_5750_);
lean_ctor_set(v_reuseFailAlloc_5778_, 15, v_F_5751_);
lean_ctor_set(v_reuseFailAlloc_5778_, 16, v_a_5752_);
lean_ctor_set(v_reuseFailAlloc_5778_, 17, v_b_5753_);
lean_ctor_set(v_reuseFailAlloc_5778_, 18, v_B_5754_);
lean_ctor_set(v_reuseFailAlloc_5778_, 19, v_h_5755_);
lean_ctor_set(v_reuseFailAlloc_5778_, 20, v_K_5756_);
lean_ctor_set(v_reuseFailAlloc_5778_, 21, v_k_5757_);
lean_ctor_set(v_reuseFailAlloc_5778_, 22, v_H_5758_);
lean_ctor_set(v_reuseFailAlloc_5778_, 23, v_m_5759_);
lean_ctor_set(v_reuseFailAlloc_5778_, 24, v_s_5760_);
lean_ctor_set(v_reuseFailAlloc_5778_, 25, v_S_5761_);
lean_ctor_set(v_reuseFailAlloc_5778_, 26, v_A_5762_);
lean_ctor_set(v_reuseFailAlloc_5778_, 27, v_n_5763_);
lean_ctor_set(v_reuseFailAlloc_5778_, 28, v_N_5764_);
lean_ctor_set(v_reuseFailAlloc_5778_, 29, v_V_5765_);
lean_ctor_set(v_reuseFailAlloc_5778_, 30, v_z_5766_);
lean_ctor_set(v_reuseFailAlloc_5778_, 31, v___x_5775_);
lean_ctor_set(v_reuseFailAlloc_5778_, 32, v_v_5767_);
lean_ctor_set(v_reuseFailAlloc_5778_, 33, v_O_5768_);
lean_ctor_set(v_reuseFailAlloc_5778_, 34, v_X_5769_);
lean_ctor_set(v_reuseFailAlloc_5778_, 35, v_x_5770_);
lean_ctor_set(v_reuseFailAlloc_5778_, 36, v_Z_5771_);
v___x_5777_ = v_reuseFailAlloc_5778_;
goto v_reusejp_5776_;
}
v_reusejp_5776_:
{
return v___x_5777_;
}
}
}
else
{
lean_object* v_G_5781_; lean_object* v_y_5782_; lean_object* v_u_5783_; lean_object* v_Y_5784_; lean_object* v_D_5785_; lean_object* v_M_5786_; lean_object* v_L_5787_; lean_object* v_d_5788_; lean_object* v_Q_5789_; lean_object* v_q_5790_; lean_object* v_w_5791_; lean_object* v_W_5792_; lean_object* v_E_5793_; lean_object* v_e_5794_; lean_object* v_c_5795_; lean_object* v_F_5796_; lean_object* v_a_5797_; lean_object* v_b_5798_; lean_object* v_B_5799_; lean_object* v_h_5800_; lean_object* v_K_5801_; lean_object* v_k_5802_; lean_object* v_H_5803_; lean_object* v_m_5804_; lean_object* v_s_5805_; lean_object* v_S_5806_; lean_object* v_A_5807_; lean_object* v_n_5808_; lean_object* v_N_5809_; lean_object* v_V_5810_; lean_object* v_z_5811_; lean_object* v_zabbrev_5812_; lean_object* v_O_5813_; lean_object* v_X_5814_; lean_object* v_x_5815_; lean_object* v_Z_5816_; lean_object* v___x_5818_; uint8_t v_isShared_5819_; uint8_t v_isSharedCheck_5824_; 
v_G_5781_ = lean_ctor_get(v_date_4123_, 0);
v_y_5782_ = lean_ctor_get(v_date_4123_, 1);
v_u_5783_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5784_ = lean_ctor_get(v_date_4123_, 3);
v_D_5785_ = lean_ctor_get(v_date_4123_, 4);
v_M_5786_ = lean_ctor_get(v_date_4123_, 5);
v_L_5787_ = lean_ctor_get(v_date_4123_, 6);
v_d_5788_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5789_ = lean_ctor_get(v_date_4123_, 8);
v_q_5790_ = lean_ctor_get(v_date_4123_, 9);
v_w_5791_ = lean_ctor_get(v_date_4123_, 10);
v_W_5792_ = lean_ctor_get(v_date_4123_, 11);
v_E_5793_ = lean_ctor_get(v_date_4123_, 12);
v_e_5794_ = lean_ctor_get(v_date_4123_, 13);
v_c_5795_ = lean_ctor_get(v_date_4123_, 14);
v_F_5796_ = lean_ctor_get(v_date_4123_, 15);
v_a_5797_ = lean_ctor_get(v_date_4123_, 16);
v_b_5798_ = lean_ctor_get(v_date_4123_, 17);
v_B_5799_ = lean_ctor_get(v_date_4123_, 18);
v_h_5800_ = lean_ctor_get(v_date_4123_, 19);
v_K_5801_ = lean_ctor_get(v_date_4123_, 20);
v_k_5802_ = lean_ctor_get(v_date_4123_, 21);
v_H_5803_ = lean_ctor_get(v_date_4123_, 22);
v_m_5804_ = lean_ctor_get(v_date_4123_, 23);
v_s_5805_ = lean_ctor_get(v_date_4123_, 24);
v_S_5806_ = lean_ctor_get(v_date_4123_, 25);
v_A_5807_ = lean_ctor_get(v_date_4123_, 26);
v_n_5808_ = lean_ctor_get(v_date_4123_, 27);
v_N_5809_ = lean_ctor_get(v_date_4123_, 28);
v_V_5810_ = lean_ctor_get(v_date_4123_, 29);
v_z_5811_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_5812_ = lean_ctor_get(v_date_4123_, 31);
v_O_5813_ = lean_ctor_get(v_date_4123_, 33);
v_X_5814_ = lean_ctor_get(v_date_4123_, 34);
v_x_5815_ = lean_ctor_get(v_date_4123_, 35);
v_Z_5816_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5824_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5824_ == 0)
{
lean_object* v_unused_5825_; 
v_unused_5825_ = lean_ctor_get(v_date_4123_, 32);
lean_dec(v_unused_5825_);
v___x_5818_ = v_date_4123_;
v_isShared_5819_ = v_isSharedCheck_5824_;
goto v_resetjp_5817_;
}
else
{
lean_inc(v_Z_5816_);
lean_inc(v_x_5815_);
lean_inc(v_X_5814_);
lean_inc(v_O_5813_);
lean_inc(v_zabbrev_5812_);
lean_inc(v_z_5811_);
lean_inc(v_V_5810_);
lean_inc(v_N_5809_);
lean_inc(v_n_5808_);
lean_inc(v_A_5807_);
lean_inc(v_S_5806_);
lean_inc(v_s_5805_);
lean_inc(v_m_5804_);
lean_inc(v_H_5803_);
lean_inc(v_k_5802_);
lean_inc(v_K_5801_);
lean_inc(v_h_5800_);
lean_inc(v_B_5799_);
lean_inc(v_b_5798_);
lean_inc(v_a_5797_);
lean_inc(v_F_5796_);
lean_inc(v_c_5795_);
lean_inc(v_e_5794_);
lean_inc(v_E_5793_);
lean_inc(v_W_5792_);
lean_inc(v_w_5791_);
lean_inc(v_q_5790_);
lean_inc(v_Q_5789_);
lean_inc(v_d_5788_);
lean_inc(v_L_5787_);
lean_inc(v_M_5786_);
lean_inc(v_D_5785_);
lean_inc(v_Y_5784_);
lean_inc(v_u_5783_);
lean_inc(v_y_5782_);
lean_inc(v_G_5781_);
lean_dec(v_date_4123_);
v___x_5818_ = lean_box(0);
v_isShared_5819_ = v_isSharedCheck_5824_;
goto v_resetjp_5817_;
}
v_resetjp_5817_:
{
lean_object* v___x_5820_; lean_object* v___x_5822_; 
v___x_5820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5820_, 0, v_data_4125_);
if (v_isShared_5819_ == 0)
{
lean_ctor_set(v___x_5818_, 32, v___x_5820_);
v___x_5822_ = v___x_5818_;
goto v_reusejp_5821_;
}
else
{
lean_object* v_reuseFailAlloc_5823_; 
v_reuseFailAlloc_5823_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5823_, 0, v_G_5781_);
lean_ctor_set(v_reuseFailAlloc_5823_, 1, v_y_5782_);
lean_ctor_set(v_reuseFailAlloc_5823_, 2, v_u_5783_);
lean_ctor_set(v_reuseFailAlloc_5823_, 3, v_Y_5784_);
lean_ctor_set(v_reuseFailAlloc_5823_, 4, v_D_5785_);
lean_ctor_set(v_reuseFailAlloc_5823_, 5, v_M_5786_);
lean_ctor_set(v_reuseFailAlloc_5823_, 6, v_L_5787_);
lean_ctor_set(v_reuseFailAlloc_5823_, 7, v_d_5788_);
lean_ctor_set(v_reuseFailAlloc_5823_, 8, v_Q_5789_);
lean_ctor_set(v_reuseFailAlloc_5823_, 9, v_q_5790_);
lean_ctor_set(v_reuseFailAlloc_5823_, 10, v_w_5791_);
lean_ctor_set(v_reuseFailAlloc_5823_, 11, v_W_5792_);
lean_ctor_set(v_reuseFailAlloc_5823_, 12, v_E_5793_);
lean_ctor_set(v_reuseFailAlloc_5823_, 13, v_e_5794_);
lean_ctor_set(v_reuseFailAlloc_5823_, 14, v_c_5795_);
lean_ctor_set(v_reuseFailAlloc_5823_, 15, v_F_5796_);
lean_ctor_set(v_reuseFailAlloc_5823_, 16, v_a_5797_);
lean_ctor_set(v_reuseFailAlloc_5823_, 17, v_b_5798_);
lean_ctor_set(v_reuseFailAlloc_5823_, 18, v_B_5799_);
lean_ctor_set(v_reuseFailAlloc_5823_, 19, v_h_5800_);
lean_ctor_set(v_reuseFailAlloc_5823_, 20, v_K_5801_);
lean_ctor_set(v_reuseFailAlloc_5823_, 21, v_k_5802_);
lean_ctor_set(v_reuseFailAlloc_5823_, 22, v_H_5803_);
lean_ctor_set(v_reuseFailAlloc_5823_, 23, v_m_5804_);
lean_ctor_set(v_reuseFailAlloc_5823_, 24, v_s_5805_);
lean_ctor_set(v_reuseFailAlloc_5823_, 25, v_S_5806_);
lean_ctor_set(v_reuseFailAlloc_5823_, 26, v_A_5807_);
lean_ctor_set(v_reuseFailAlloc_5823_, 27, v_n_5808_);
lean_ctor_set(v_reuseFailAlloc_5823_, 28, v_N_5809_);
lean_ctor_set(v_reuseFailAlloc_5823_, 29, v_V_5810_);
lean_ctor_set(v_reuseFailAlloc_5823_, 30, v_z_5811_);
lean_ctor_set(v_reuseFailAlloc_5823_, 31, v_zabbrev_5812_);
lean_ctor_set(v_reuseFailAlloc_5823_, 32, v___x_5820_);
lean_ctor_set(v_reuseFailAlloc_5823_, 33, v_O_5813_);
lean_ctor_set(v_reuseFailAlloc_5823_, 34, v_X_5814_);
lean_ctor_set(v_reuseFailAlloc_5823_, 35, v_x_5815_);
lean_ctor_set(v_reuseFailAlloc_5823_, 36, v_Z_5816_);
v___x_5822_ = v_reuseFailAlloc_5823_;
goto v_reusejp_5821_;
}
v_reusejp_5821_:
{
return v___x_5822_;
}
}
}
}
case 32:
{
lean_object* v_G_5826_; lean_object* v_y_5827_; lean_object* v_u_5828_; lean_object* v_Y_5829_; lean_object* v_D_5830_; lean_object* v_M_5831_; lean_object* v_L_5832_; lean_object* v_d_5833_; lean_object* v_Q_5834_; lean_object* v_q_5835_; lean_object* v_w_5836_; lean_object* v_W_5837_; lean_object* v_E_5838_; lean_object* v_e_5839_; lean_object* v_c_5840_; lean_object* v_F_5841_; lean_object* v_a_5842_; lean_object* v_b_5843_; lean_object* v_B_5844_; lean_object* v_h_5845_; lean_object* v_K_5846_; lean_object* v_k_5847_; lean_object* v_H_5848_; lean_object* v_m_5849_; lean_object* v_s_5850_; lean_object* v_S_5851_; lean_object* v_A_5852_; lean_object* v_n_5853_; lean_object* v_N_5854_; lean_object* v_V_5855_; lean_object* v_z_5856_; lean_object* v_zabbrev_5857_; lean_object* v_v_5858_; lean_object* v_X_5859_; lean_object* v_x_5860_; lean_object* v_Z_5861_; lean_object* v___x_5863_; uint8_t v_isShared_5864_; uint8_t v_isSharedCheck_5869_; 
lean_dec_ref_known(v_modifier_4124_, 0);
v_G_5826_ = lean_ctor_get(v_date_4123_, 0);
v_y_5827_ = lean_ctor_get(v_date_4123_, 1);
v_u_5828_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5829_ = lean_ctor_get(v_date_4123_, 3);
v_D_5830_ = lean_ctor_get(v_date_4123_, 4);
v_M_5831_ = lean_ctor_get(v_date_4123_, 5);
v_L_5832_ = lean_ctor_get(v_date_4123_, 6);
v_d_5833_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5834_ = lean_ctor_get(v_date_4123_, 8);
v_q_5835_ = lean_ctor_get(v_date_4123_, 9);
v_w_5836_ = lean_ctor_get(v_date_4123_, 10);
v_W_5837_ = lean_ctor_get(v_date_4123_, 11);
v_E_5838_ = lean_ctor_get(v_date_4123_, 12);
v_e_5839_ = lean_ctor_get(v_date_4123_, 13);
v_c_5840_ = lean_ctor_get(v_date_4123_, 14);
v_F_5841_ = lean_ctor_get(v_date_4123_, 15);
v_a_5842_ = lean_ctor_get(v_date_4123_, 16);
v_b_5843_ = lean_ctor_get(v_date_4123_, 17);
v_B_5844_ = lean_ctor_get(v_date_4123_, 18);
v_h_5845_ = lean_ctor_get(v_date_4123_, 19);
v_K_5846_ = lean_ctor_get(v_date_4123_, 20);
v_k_5847_ = lean_ctor_get(v_date_4123_, 21);
v_H_5848_ = lean_ctor_get(v_date_4123_, 22);
v_m_5849_ = lean_ctor_get(v_date_4123_, 23);
v_s_5850_ = lean_ctor_get(v_date_4123_, 24);
v_S_5851_ = lean_ctor_get(v_date_4123_, 25);
v_A_5852_ = lean_ctor_get(v_date_4123_, 26);
v_n_5853_ = lean_ctor_get(v_date_4123_, 27);
v_N_5854_ = lean_ctor_get(v_date_4123_, 28);
v_V_5855_ = lean_ctor_get(v_date_4123_, 29);
v_z_5856_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_5857_ = lean_ctor_get(v_date_4123_, 31);
v_v_5858_ = lean_ctor_get(v_date_4123_, 32);
v_X_5859_ = lean_ctor_get(v_date_4123_, 34);
v_x_5860_ = lean_ctor_get(v_date_4123_, 35);
v_Z_5861_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5869_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5869_ == 0)
{
lean_object* v_unused_5870_; 
v_unused_5870_ = lean_ctor_get(v_date_4123_, 33);
lean_dec(v_unused_5870_);
v___x_5863_ = v_date_4123_;
v_isShared_5864_ = v_isSharedCheck_5869_;
goto v_resetjp_5862_;
}
else
{
lean_inc(v_Z_5861_);
lean_inc(v_x_5860_);
lean_inc(v_X_5859_);
lean_inc(v_v_5858_);
lean_inc(v_zabbrev_5857_);
lean_inc(v_z_5856_);
lean_inc(v_V_5855_);
lean_inc(v_N_5854_);
lean_inc(v_n_5853_);
lean_inc(v_A_5852_);
lean_inc(v_S_5851_);
lean_inc(v_s_5850_);
lean_inc(v_m_5849_);
lean_inc(v_H_5848_);
lean_inc(v_k_5847_);
lean_inc(v_K_5846_);
lean_inc(v_h_5845_);
lean_inc(v_B_5844_);
lean_inc(v_b_5843_);
lean_inc(v_a_5842_);
lean_inc(v_F_5841_);
lean_inc(v_c_5840_);
lean_inc(v_e_5839_);
lean_inc(v_E_5838_);
lean_inc(v_W_5837_);
lean_inc(v_w_5836_);
lean_inc(v_q_5835_);
lean_inc(v_Q_5834_);
lean_inc(v_d_5833_);
lean_inc(v_L_5832_);
lean_inc(v_M_5831_);
lean_inc(v_D_5830_);
lean_inc(v_Y_5829_);
lean_inc(v_u_5828_);
lean_inc(v_y_5827_);
lean_inc(v_G_5826_);
lean_dec(v_date_4123_);
v___x_5863_ = lean_box(0);
v_isShared_5864_ = v_isSharedCheck_5869_;
goto v_resetjp_5862_;
}
v_resetjp_5862_:
{
lean_object* v___x_5865_; lean_object* v___x_5867_; 
v___x_5865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5865_, 0, v_data_4125_);
if (v_isShared_5864_ == 0)
{
lean_ctor_set(v___x_5863_, 33, v___x_5865_);
v___x_5867_ = v___x_5863_;
goto v_reusejp_5866_;
}
else
{
lean_object* v_reuseFailAlloc_5868_; 
v_reuseFailAlloc_5868_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5868_, 0, v_G_5826_);
lean_ctor_set(v_reuseFailAlloc_5868_, 1, v_y_5827_);
lean_ctor_set(v_reuseFailAlloc_5868_, 2, v_u_5828_);
lean_ctor_set(v_reuseFailAlloc_5868_, 3, v_Y_5829_);
lean_ctor_set(v_reuseFailAlloc_5868_, 4, v_D_5830_);
lean_ctor_set(v_reuseFailAlloc_5868_, 5, v_M_5831_);
lean_ctor_set(v_reuseFailAlloc_5868_, 6, v_L_5832_);
lean_ctor_set(v_reuseFailAlloc_5868_, 7, v_d_5833_);
lean_ctor_set(v_reuseFailAlloc_5868_, 8, v_Q_5834_);
lean_ctor_set(v_reuseFailAlloc_5868_, 9, v_q_5835_);
lean_ctor_set(v_reuseFailAlloc_5868_, 10, v_w_5836_);
lean_ctor_set(v_reuseFailAlloc_5868_, 11, v_W_5837_);
lean_ctor_set(v_reuseFailAlloc_5868_, 12, v_E_5838_);
lean_ctor_set(v_reuseFailAlloc_5868_, 13, v_e_5839_);
lean_ctor_set(v_reuseFailAlloc_5868_, 14, v_c_5840_);
lean_ctor_set(v_reuseFailAlloc_5868_, 15, v_F_5841_);
lean_ctor_set(v_reuseFailAlloc_5868_, 16, v_a_5842_);
lean_ctor_set(v_reuseFailAlloc_5868_, 17, v_b_5843_);
lean_ctor_set(v_reuseFailAlloc_5868_, 18, v_B_5844_);
lean_ctor_set(v_reuseFailAlloc_5868_, 19, v_h_5845_);
lean_ctor_set(v_reuseFailAlloc_5868_, 20, v_K_5846_);
lean_ctor_set(v_reuseFailAlloc_5868_, 21, v_k_5847_);
lean_ctor_set(v_reuseFailAlloc_5868_, 22, v_H_5848_);
lean_ctor_set(v_reuseFailAlloc_5868_, 23, v_m_5849_);
lean_ctor_set(v_reuseFailAlloc_5868_, 24, v_s_5850_);
lean_ctor_set(v_reuseFailAlloc_5868_, 25, v_S_5851_);
lean_ctor_set(v_reuseFailAlloc_5868_, 26, v_A_5852_);
lean_ctor_set(v_reuseFailAlloc_5868_, 27, v_n_5853_);
lean_ctor_set(v_reuseFailAlloc_5868_, 28, v_N_5854_);
lean_ctor_set(v_reuseFailAlloc_5868_, 29, v_V_5855_);
lean_ctor_set(v_reuseFailAlloc_5868_, 30, v_z_5856_);
lean_ctor_set(v_reuseFailAlloc_5868_, 31, v_zabbrev_5857_);
lean_ctor_set(v_reuseFailAlloc_5868_, 32, v_v_5858_);
lean_ctor_set(v_reuseFailAlloc_5868_, 33, v___x_5865_);
lean_ctor_set(v_reuseFailAlloc_5868_, 34, v_X_5859_);
lean_ctor_set(v_reuseFailAlloc_5868_, 35, v_x_5860_);
lean_ctor_set(v_reuseFailAlloc_5868_, 36, v_Z_5861_);
v___x_5867_ = v_reuseFailAlloc_5868_;
goto v_reusejp_5866_;
}
v_reusejp_5866_:
{
return v___x_5867_;
}
}
}
case 33:
{
lean_object* v_G_5871_; lean_object* v_y_5872_; lean_object* v_u_5873_; lean_object* v_Y_5874_; lean_object* v_D_5875_; lean_object* v_M_5876_; lean_object* v_L_5877_; lean_object* v_d_5878_; lean_object* v_Q_5879_; lean_object* v_q_5880_; lean_object* v_w_5881_; lean_object* v_W_5882_; lean_object* v_E_5883_; lean_object* v_e_5884_; lean_object* v_c_5885_; lean_object* v_F_5886_; lean_object* v_a_5887_; lean_object* v_b_5888_; lean_object* v_B_5889_; lean_object* v_h_5890_; lean_object* v_K_5891_; lean_object* v_k_5892_; lean_object* v_H_5893_; lean_object* v_m_5894_; lean_object* v_s_5895_; lean_object* v_S_5896_; lean_object* v_A_5897_; lean_object* v_n_5898_; lean_object* v_N_5899_; lean_object* v_V_5900_; lean_object* v_z_5901_; lean_object* v_zabbrev_5902_; lean_object* v_v_5903_; lean_object* v_O_5904_; lean_object* v_x_5905_; lean_object* v_Z_5906_; lean_object* v___x_5908_; uint8_t v_isShared_5909_; uint8_t v_isSharedCheck_5914_; 
lean_dec_ref_known(v_modifier_4124_, 0);
v_G_5871_ = lean_ctor_get(v_date_4123_, 0);
v_y_5872_ = lean_ctor_get(v_date_4123_, 1);
v_u_5873_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5874_ = lean_ctor_get(v_date_4123_, 3);
v_D_5875_ = lean_ctor_get(v_date_4123_, 4);
v_M_5876_ = lean_ctor_get(v_date_4123_, 5);
v_L_5877_ = lean_ctor_get(v_date_4123_, 6);
v_d_5878_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5879_ = lean_ctor_get(v_date_4123_, 8);
v_q_5880_ = lean_ctor_get(v_date_4123_, 9);
v_w_5881_ = lean_ctor_get(v_date_4123_, 10);
v_W_5882_ = lean_ctor_get(v_date_4123_, 11);
v_E_5883_ = lean_ctor_get(v_date_4123_, 12);
v_e_5884_ = lean_ctor_get(v_date_4123_, 13);
v_c_5885_ = lean_ctor_get(v_date_4123_, 14);
v_F_5886_ = lean_ctor_get(v_date_4123_, 15);
v_a_5887_ = lean_ctor_get(v_date_4123_, 16);
v_b_5888_ = lean_ctor_get(v_date_4123_, 17);
v_B_5889_ = lean_ctor_get(v_date_4123_, 18);
v_h_5890_ = lean_ctor_get(v_date_4123_, 19);
v_K_5891_ = lean_ctor_get(v_date_4123_, 20);
v_k_5892_ = lean_ctor_get(v_date_4123_, 21);
v_H_5893_ = lean_ctor_get(v_date_4123_, 22);
v_m_5894_ = lean_ctor_get(v_date_4123_, 23);
v_s_5895_ = lean_ctor_get(v_date_4123_, 24);
v_S_5896_ = lean_ctor_get(v_date_4123_, 25);
v_A_5897_ = lean_ctor_get(v_date_4123_, 26);
v_n_5898_ = lean_ctor_get(v_date_4123_, 27);
v_N_5899_ = lean_ctor_get(v_date_4123_, 28);
v_V_5900_ = lean_ctor_get(v_date_4123_, 29);
v_z_5901_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_5902_ = lean_ctor_get(v_date_4123_, 31);
v_v_5903_ = lean_ctor_get(v_date_4123_, 32);
v_O_5904_ = lean_ctor_get(v_date_4123_, 33);
v_x_5905_ = lean_ctor_get(v_date_4123_, 35);
v_Z_5906_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5914_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5914_ == 0)
{
lean_object* v_unused_5915_; 
v_unused_5915_ = lean_ctor_get(v_date_4123_, 34);
lean_dec(v_unused_5915_);
v___x_5908_ = v_date_4123_;
v_isShared_5909_ = v_isSharedCheck_5914_;
goto v_resetjp_5907_;
}
else
{
lean_inc(v_Z_5906_);
lean_inc(v_x_5905_);
lean_inc(v_O_5904_);
lean_inc(v_v_5903_);
lean_inc(v_zabbrev_5902_);
lean_inc(v_z_5901_);
lean_inc(v_V_5900_);
lean_inc(v_N_5899_);
lean_inc(v_n_5898_);
lean_inc(v_A_5897_);
lean_inc(v_S_5896_);
lean_inc(v_s_5895_);
lean_inc(v_m_5894_);
lean_inc(v_H_5893_);
lean_inc(v_k_5892_);
lean_inc(v_K_5891_);
lean_inc(v_h_5890_);
lean_inc(v_B_5889_);
lean_inc(v_b_5888_);
lean_inc(v_a_5887_);
lean_inc(v_F_5886_);
lean_inc(v_c_5885_);
lean_inc(v_e_5884_);
lean_inc(v_E_5883_);
lean_inc(v_W_5882_);
lean_inc(v_w_5881_);
lean_inc(v_q_5880_);
lean_inc(v_Q_5879_);
lean_inc(v_d_5878_);
lean_inc(v_L_5877_);
lean_inc(v_M_5876_);
lean_inc(v_D_5875_);
lean_inc(v_Y_5874_);
lean_inc(v_u_5873_);
lean_inc(v_y_5872_);
lean_inc(v_G_5871_);
lean_dec(v_date_4123_);
v___x_5908_ = lean_box(0);
v_isShared_5909_ = v_isSharedCheck_5914_;
goto v_resetjp_5907_;
}
v_resetjp_5907_:
{
lean_object* v___x_5910_; lean_object* v___x_5912_; 
v___x_5910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5910_, 0, v_data_4125_);
if (v_isShared_5909_ == 0)
{
lean_ctor_set(v___x_5908_, 34, v___x_5910_);
v___x_5912_ = v___x_5908_;
goto v_reusejp_5911_;
}
else
{
lean_object* v_reuseFailAlloc_5913_; 
v_reuseFailAlloc_5913_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5913_, 0, v_G_5871_);
lean_ctor_set(v_reuseFailAlloc_5913_, 1, v_y_5872_);
lean_ctor_set(v_reuseFailAlloc_5913_, 2, v_u_5873_);
lean_ctor_set(v_reuseFailAlloc_5913_, 3, v_Y_5874_);
lean_ctor_set(v_reuseFailAlloc_5913_, 4, v_D_5875_);
lean_ctor_set(v_reuseFailAlloc_5913_, 5, v_M_5876_);
lean_ctor_set(v_reuseFailAlloc_5913_, 6, v_L_5877_);
lean_ctor_set(v_reuseFailAlloc_5913_, 7, v_d_5878_);
lean_ctor_set(v_reuseFailAlloc_5913_, 8, v_Q_5879_);
lean_ctor_set(v_reuseFailAlloc_5913_, 9, v_q_5880_);
lean_ctor_set(v_reuseFailAlloc_5913_, 10, v_w_5881_);
lean_ctor_set(v_reuseFailAlloc_5913_, 11, v_W_5882_);
lean_ctor_set(v_reuseFailAlloc_5913_, 12, v_E_5883_);
lean_ctor_set(v_reuseFailAlloc_5913_, 13, v_e_5884_);
lean_ctor_set(v_reuseFailAlloc_5913_, 14, v_c_5885_);
lean_ctor_set(v_reuseFailAlloc_5913_, 15, v_F_5886_);
lean_ctor_set(v_reuseFailAlloc_5913_, 16, v_a_5887_);
lean_ctor_set(v_reuseFailAlloc_5913_, 17, v_b_5888_);
lean_ctor_set(v_reuseFailAlloc_5913_, 18, v_B_5889_);
lean_ctor_set(v_reuseFailAlloc_5913_, 19, v_h_5890_);
lean_ctor_set(v_reuseFailAlloc_5913_, 20, v_K_5891_);
lean_ctor_set(v_reuseFailAlloc_5913_, 21, v_k_5892_);
lean_ctor_set(v_reuseFailAlloc_5913_, 22, v_H_5893_);
lean_ctor_set(v_reuseFailAlloc_5913_, 23, v_m_5894_);
lean_ctor_set(v_reuseFailAlloc_5913_, 24, v_s_5895_);
lean_ctor_set(v_reuseFailAlloc_5913_, 25, v_S_5896_);
lean_ctor_set(v_reuseFailAlloc_5913_, 26, v_A_5897_);
lean_ctor_set(v_reuseFailAlloc_5913_, 27, v_n_5898_);
lean_ctor_set(v_reuseFailAlloc_5913_, 28, v_N_5899_);
lean_ctor_set(v_reuseFailAlloc_5913_, 29, v_V_5900_);
lean_ctor_set(v_reuseFailAlloc_5913_, 30, v_z_5901_);
lean_ctor_set(v_reuseFailAlloc_5913_, 31, v_zabbrev_5902_);
lean_ctor_set(v_reuseFailAlloc_5913_, 32, v_v_5903_);
lean_ctor_set(v_reuseFailAlloc_5913_, 33, v_O_5904_);
lean_ctor_set(v_reuseFailAlloc_5913_, 34, v___x_5910_);
lean_ctor_set(v_reuseFailAlloc_5913_, 35, v_x_5905_);
lean_ctor_set(v_reuseFailAlloc_5913_, 36, v_Z_5906_);
v___x_5912_ = v_reuseFailAlloc_5913_;
goto v_reusejp_5911_;
}
v_reusejp_5911_:
{
return v___x_5912_;
}
}
}
case 34:
{
lean_object* v_G_5916_; lean_object* v_y_5917_; lean_object* v_u_5918_; lean_object* v_Y_5919_; lean_object* v_D_5920_; lean_object* v_M_5921_; lean_object* v_L_5922_; lean_object* v_d_5923_; lean_object* v_Q_5924_; lean_object* v_q_5925_; lean_object* v_w_5926_; lean_object* v_W_5927_; lean_object* v_E_5928_; lean_object* v_e_5929_; lean_object* v_c_5930_; lean_object* v_F_5931_; lean_object* v_a_5932_; lean_object* v_b_5933_; lean_object* v_B_5934_; lean_object* v_h_5935_; lean_object* v_K_5936_; lean_object* v_k_5937_; lean_object* v_H_5938_; lean_object* v_m_5939_; lean_object* v_s_5940_; lean_object* v_S_5941_; lean_object* v_A_5942_; lean_object* v_n_5943_; lean_object* v_N_5944_; lean_object* v_V_5945_; lean_object* v_z_5946_; lean_object* v_zabbrev_5947_; lean_object* v_v_5948_; lean_object* v_O_5949_; lean_object* v_X_5950_; lean_object* v_Z_5951_; lean_object* v___x_5953_; uint8_t v_isShared_5954_; uint8_t v_isSharedCheck_5959_; 
lean_dec_ref_known(v_modifier_4124_, 0);
v_G_5916_ = lean_ctor_get(v_date_4123_, 0);
v_y_5917_ = lean_ctor_get(v_date_4123_, 1);
v_u_5918_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5919_ = lean_ctor_get(v_date_4123_, 3);
v_D_5920_ = lean_ctor_get(v_date_4123_, 4);
v_M_5921_ = lean_ctor_get(v_date_4123_, 5);
v_L_5922_ = lean_ctor_get(v_date_4123_, 6);
v_d_5923_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5924_ = lean_ctor_get(v_date_4123_, 8);
v_q_5925_ = lean_ctor_get(v_date_4123_, 9);
v_w_5926_ = lean_ctor_get(v_date_4123_, 10);
v_W_5927_ = lean_ctor_get(v_date_4123_, 11);
v_E_5928_ = lean_ctor_get(v_date_4123_, 12);
v_e_5929_ = lean_ctor_get(v_date_4123_, 13);
v_c_5930_ = lean_ctor_get(v_date_4123_, 14);
v_F_5931_ = lean_ctor_get(v_date_4123_, 15);
v_a_5932_ = lean_ctor_get(v_date_4123_, 16);
v_b_5933_ = lean_ctor_get(v_date_4123_, 17);
v_B_5934_ = lean_ctor_get(v_date_4123_, 18);
v_h_5935_ = lean_ctor_get(v_date_4123_, 19);
v_K_5936_ = lean_ctor_get(v_date_4123_, 20);
v_k_5937_ = lean_ctor_get(v_date_4123_, 21);
v_H_5938_ = lean_ctor_get(v_date_4123_, 22);
v_m_5939_ = lean_ctor_get(v_date_4123_, 23);
v_s_5940_ = lean_ctor_get(v_date_4123_, 24);
v_S_5941_ = lean_ctor_get(v_date_4123_, 25);
v_A_5942_ = lean_ctor_get(v_date_4123_, 26);
v_n_5943_ = lean_ctor_get(v_date_4123_, 27);
v_N_5944_ = lean_ctor_get(v_date_4123_, 28);
v_V_5945_ = lean_ctor_get(v_date_4123_, 29);
v_z_5946_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_5947_ = lean_ctor_get(v_date_4123_, 31);
v_v_5948_ = lean_ctor_get(v_date_4123_, 32);
v_O_5949_ = lean_ctor_get(v_date_4123_, 33);
v_X_5950_ = lean_ctor_get(v_date_4123_, 34);
v_Z_5951_ = lean_ctor_get(v_date_4123_, 36);
v_isSharedCheck_5959_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_5959_ == 0)
{
lean_object* v_unused_5960_; 
v_unused_5960_ = lean_ctor_get(v_date_4123_, 35);
lean_dec(v_unused_5960_);
v___x_5953_ = v_date_4123_;
v_isShared_5954_ = v_isSharedCheck_5959_;
goto v_resetjp_5952_;
}
else
{
lean_inc(v_Z_5951_);
lean_inc(v_X_5950_);
lean_inc(v_O_5949_);
lean_inc(v_v_5948_);
lean_inc(v_zabbrev_5947_);
lean_inc(v_z_5946_);
lean_inc(v_V_5945_);
lean_inc(v_N_5944_);
lean_inc(v_n_5943_);
lean_inc(v_A_5942_);
lean_inc(v_S_5941_);
lean_inc(v_s_5940_);
lean_inc(v_m_5939_);
lean_inc(v_H_5938_);
lean_inc(v_k_5937_);
lean_inc(v_K_5936_);
lean_inc(v_h_5935_);
lean_inc(v_B_5934_);
lean_inc(v_b_5933_);
lean_inc(v_a_5932_);
lean_inc(v_F_5931_);
lean_inc(v_c_5930_);
lean_inc(v_e_5929_);
lean_inc(v_E_5928_);
lean_inc(v_W_5927_);
lean_inc(v_w_5926_);
lean_inc(v_q_5925_);
lean_inc(v_Q_5924_);
lean_inc(v_d_5923_);
lean_inc(v_L_5922_);
lean_inc(v_M_5921_);
lean_inc(v_D_5920_);
lean_inc(v_Y_5919_);
lean_inc(v_u_5918_);
lean_inc(v_y_5917_);
lean_inc(v_G_5916_);
lean_dec(v_date_4123_);
v___x_5953_ = lean_box(0);
v_isShared_5954_ = v_isSharedCheck_5959_;
goto v_resetjp_5952_;
}
v_resetjp_5952_:
{
lean_object* v___x_5955_; lean_object* v___x_5957_; 
v___x_5955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5955_, 0, v_data_4125_);
if (v_isShared_5954_ == 0)
{
lean_ctor_set(v___x_5953_, 35, v___x_5955_);
v___x_5957_ = v___x_5953_;
goto v_reusejp_5956_;
}
else
{
lean_object* v_reuseFailAlloc_5958_; 
v_reuseFailAlloc_5958_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5958_, 0, v_G_5916_);
lean_ctor_set(v_reuseFailAlloc_5958_, 1, v_y_5917_);
lean_ctor_set(v_reuseFailAlloc_5958_, 2, v_u_5918_);
lean_ctor_set(v_reuseFailAlloc_5958_, 3, v_Y_5919_);
lean_ctor_set(v_reuseFailAlloc_5958_, 4, v_D_5920_);
lean_ctor_set(v_reuseFailAlloc_5958_, 5, v_M_5921_);
lean_ctor_set(v_reuseFailAlloc_5958_, 6, v_L_5922_);
lean_ctor_set(v_reuseFailAlloc_5958_, 7, v_d_5923_);
lean_ctor_set(v_reuseFailAlloc_5958_, 8, v_Q_5924_);
lean_ctor_set(v_reuseFailAlloc_5958_, 9, v_q_5925_);
lean_ctor_set(v_reuseFailAlloc_5958_, 10, v_w_5926_);
lean_ctor_set(v_reuseFailAlloc_5958_, 11, v_W_5927_);
lean_ctor_set(v_reuseFailAlloc_5958_, 12, v_E_5928_);
lean_ctor_set(v_reuseFailAlloc_5958_, 13, v_e_5929_);
lean_ctor_set(v_reuseFailAlloc_5958_, 14, v_c_5930_);
lean_ctor_set(v_reuseFailAlloc_5958_, 15, v_F_5931_);
lean_ctor_set(v_reuseFailAlloc_5958_, 16, v_a_5932_);
lean_ctor_set(v_reuseFailAlloc_5958_, 17, v_b_5933_);
lean_ctor_set(v_reuseFailAlloc_5958_, 18, v_B_5934_);
lean_ctor_set(v_reuseFailAlloc_5958_, 19, v_h_5935_);
lean_ctor_set(v_reuseFailAlloc_5958_, 20, v_K_5936_);
lean_ctor_set(v_reuseFailAlloc_5958_, 21, v_k_5937_);
lean_ctor_set(v_reuseFailAlloc_5958_, 22, v_H_5938_);
lean_ctor_set(v_reuseFailAlloc_5958_, 23, v_m_5939_);
lean_ctor_set(v_reuseFailAlloc_5958_, 24, v_s_5940_);
lean_ctor_set(v_reuseFailAlloc_5958_, 25, v_S_5941_);
lean_ctor_set(v_reuseFailAlloc_5958_, 26, v_A_5942_);
lean_ctor_set(v_reuseFailAlloc_5958_, 27, v_n_5943_);
lean_ctor_set(v_reuseFailAlloc_5958_, 28, v_N_5944_);
lean_ctor_set(v_reuseFailAlloc_5958_, 29, v_V_5945_);
lean_ctor_set(v_reuseFailAlloc_5958_, 30, v_z_5946_);
lean_ctor_set(v_reuseFailAlloc_5958_, 31, v_zabbrev_5947_);
lean_ctor_set(v_reuseFailAlloc_5958_, 32, v_v_5948_);
lean_ctor_set(v_reuseFailAlloc_5958_, 33, v_O_5949_);
lean_ctor_set(v_reuseFailAlloc_5958_, 34, v_X_5950_);
lean_ctor_set(v_reuseFailAlloc_5958_, 35, v___x_5955_);
lean_ctor_set(v_reuseFailAlloc_5958_, 36, v_Z_5951_);
v___x_5957_ = v_reuseFailAlloc_5958_;
goto v_reusejp_5956_;
}
v_reusejp_5956_:
{
return v___x_5957_;
}
}
}
default: 
{
lean_object* v_G_5961_; lean_object* v_y_5962_; lean_object* v_u_5963_; lean_object* v_Y_5964_; lean_object* v_D_5965_; lean_object* v_M_5966_; lean_object* v_L_5967_; lean_object* v_d_5968_; lean_object* v_Q_5969_; lean_object* v_q_5970_; lean_object* v_w_5971_; lean_object* v_W_5972_; lean_object* v_E_5973_; lean_object* v_e_5974_; lean_object* v_c_5975_; lean_object* v_F_5976_; lean_object* v_a_5977_; lean_object* v_b_5978_; lean_object* v_B_5979_; lean_object* v_h_5980_; lean_object* v_K_5981_; lean_object* v_k_5982_; lean_object* v_H_5983_; lean_object* v_m_5984_; lean_object* v_s_5985_; lean_object* v_S_5986_; lean_object* v_A_5987_; lean_object* v_n_5988_; lean_object* v_N_5989_; lean_object* v_V_5990_; lean_object* v_z_5991_; lean_object* v_zabbrev_5992_; lean_object* v_v_5993_; lean_object* v_O_5994_; lean_object* v_X_5995_; lean_object* v_x_5996_; lean_object* v___x_5998_; uint8_t v_isShared_5999_; uint8_t v_isSharedCheck_6004_; 
lean_dec_ref_known(v_modifier_4124_, 0);
v_G_5961_ = lean_ctor_get(v_date_4123_, 0);
v_y_5962_ = lean_ctor_get(v_date_4123_, 1);
v_u_5963_ = lean_ctor_get(v_date_4123_, 2);
v_Y_5964_ = lean_ctor_get(v_date_4123_, 3);
v_D_5965_ = lean_ctor_get(v_date_4123_, 4);
v_M_5966_ = lean_ctor_get(v_date_4123_, 5);
v_L_5967_ = lean_ctor_get(v_date_4123_, 6);
v_d_5968_ = lean_ctor_get(v_date_4123_, 7);
v_Q_5969_ = lean_ctor_get(v_date_4123_, 8);
v_q_5970_ = lean_ctor_get(v_date_4123_, 9);
v_w_5971_ = lean_ctor_get(v_date_4123_, 10);
v_W_5972_ = lean_ctor_get(v_date_4123_, 11);
v_E_5973_ = lean_ctor_get(v_date_4123_, 12);
v_e_5974_ = lean_ctor_get(v_date_4123_, 13);
v_c_5975_ = lean_ctor_get(v_date_4123_, 14);
v_F_5976_ = lean_ctor_get(v_date_4123_, 15);
v_a_5977_ = lean_ctor_get(v_date_4123_, 16);
v_b_5978_ = lean_ctor_get(v_date_4123_, 17);
v_B_5979_ = lean_ctor_get(v_date_4123_, 18);
v_h_5980_ = lean_ctor_get(v_date_4123_, 19);
v_K_5981_ = lean_ctor_get(v_date_4123_, 20);
v_k_5982_ = lean_ctor_get(v_date_4123_, 21);
v_H_5983_ = lean_ctor_get(v_date_4123_, 22);
v_m_5984_ = lean_ctor_get(v_date_4123_, 23);
v_s_5985_ = lean_ctor_get(v_date_4123_, 24);
v_S_5986_ = lean_ctor_get(v_date_4123_, 25);
v_A_5987_ = lean_ctor_get(v_date_4123_, 26);
v_n_5988_ = lean_ctor_get(v_date_4123_, 27);
v_N_5989_ = lean_ctor_get(v_date_4123_, 28);
v_V_5990_ = lean_ctor_get(v_date_4123_, 29);
v_z_5991_ = lean_ctor_get(v_date_4123_, 30);
v_zabbrev_5992_ = lean_ctor_get(v_date_4123_, 31);
v_v_5993_ = lean_ctor_get(v_date_4123_, 32);
v_O_5994_ = lean_ctor_get(v_date_4123_, 33);
v_X_5995_ = lean_ctor_get(v_date_4123_, 34);
v_x_5996_ = lean_ctor_get(v_date_4123_, 35);
v_isSharedCheck_6004_ = !lean_is_exclusive(v_date_4123_);
if (v_isSharedCheck_6004_ == 0)
{
lean_object* v_unused_6005_; 
v_unused_6005_ = lean_ctor_get(v_date_4123_, 36);
lean_dec(v_unused_6005_);
v___x_5998_ = v_date_4123_;
v_isShared_5999_ = v_isSharedCheck_6004_;
goto v_resetjp_5997_;
}
else
{
lean_inc(v_x_5996_);
lean_inc(v_X_5995_);
lean_inc(v_O_5994_);
lean_inc(v_v_5993_);
lean_inc(v_zabbrev_5992_);
lean_inc(v_z_5991_);
lean_inc(v_V_5990_);
lean_inc(v_N_5989_);
lean_inc(v_n_5988_);
lean_inc(v_A_5987_);
lean_inc(v_S_5986_);
lean_inc(v_s_5985_);
lean_inc(v_m_5984_);
lean_inc(v_H_5983_);
lean_inc(v_k_5982_);
lean_inc(v_K_5981_);
lean_inc(v_h_5980_);
lean_inc(v_B_5979_);
lean_inc(v_b_5978_);
lean_inc(v_a_5977_);
lean_inc(v_F_5976_);
lean_inc(v_c_5975_);
lean_inc(v_e_5974_);
lean_inc(v_E_5973_);
lean_inc(v_W_5972_);
lean_inc(v_w_5971_);
lean_inc(v_q_5970_);
lean_inc(v_Q_5969_);
lean_inc(v_d_5968_);
lean_inc(v_L_5967_);
lean_inc(v_M_5966_);
lean_inc(v_D_5965_);
lean_inc(v_Y_5964_);
lean_inc(v_u_5963_);
lean_inc(v_y_5962_);
lean_inc(v_G_5961_);
lean_dec(v_date_4123_);
v___x_5998_ = lean_box(0);
v_isShared_5999_ = v_isSharedCheck_6004_;
goto v_resetjp_5997_;
}
v_resetjp_5997_:
{
lean_object* v___x_6000_; lean_object* v___x_6002_; 
v___x_6000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6000_, 0, v_data_4125_);
if (v_isShared_5999_ == 0)
{
lean_ctor_set(v___x_5998_, 36, v___x_6000_);
v___x_6002_ = v___x_5998_;
goto v_reusejp_6001_;
}
else
{
lean_object* v_reuseFailAlloc_6003_; 
v_reuseFailAlloc_6003_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6003_, 0, v_G_5961_);
lean_ctor_set(v_reuseFailAlloc_6003_, 1, v_y_5962_);
lean_ctor_set(v_reuseFailAlloc_6003_, 2, v_u_5963_);
lean_ctor_set(v_reuseFailAlloc_6003_, 3, v_Y_5964_);
lean_ctor_set(v_reuseFailAlloc_6003_, 4, v_D_5965_);
lean_ctor_set(v_reuseFailAlloc_6003_, 5, v_M_5966_);
lean_ctor_set(v_reuseFailAlloc_6003_, 6, v_L_5967_);
lean_ctor_set(v_reuseFailAlloc_6003_, 7, v_d_5968_);
lean_ctor_set(v_reuseFailAlloc_6003_, 8, v_Q_5969_);
lean_ctor_set(v_reuseFailAlloc_6003_, 9, v_q_5970_);
lean_ctor_set(v_reuseFailAlloc_6003_, 10, v_w_5971_);
lean_ctor_set(v_reuseFailAlloc_6003_, 11, v_W_5972_);
lean_ctor_set(v_reuseFailAlloc_6003_, 12, v_E_5973_);
lean_ctor_set(v_reuseFailAlloc_6003_, 13, v_e_5974_);
lean_ctor_set(v_reuseFailAlloc_6003_, 14, v_c_5975_);
lean_ctor_set(v_reuseFailAlloc_6003_, 15, v_F_5976_);
lean_ctor_set(v_reuseFailAlloc_6003_, 16, v_a_5977_);
lean_ctor_set(v_reuseFailAlloc_6003_, 17, v_b_5978_);
lean_ctor_set(v_reuseFailAlloc_6003_, 18, v_B_5979_);
lean_ctor_set(v_reuseFailAlloc_6003_, 19, v_h_5980_);
lean_ctor_set(v_reuseFailAlloc_6003_, 20, v_K_5981_);
lean_ctor_set(v_reuseFailAlloc_6003_, 21, v_k_5982_);
lean_ctor_set(v_reuseFailAlloc_6003_, 22, v_H_5983_);
lean_ctor_set(v_reuseFailAlloc_6003_, 23, v_m_5984_);
lean_ctor_set(v_reuseFailAlloc_6003_, 24, v_s_5985_);
lean_ctor_set(v_reuseFailAlloc_6003_, 25, v_S_5986_);
lean_ctor_set(v_reuseFailAlloc_6003_, 26, v_A_5987_);
lean_ctor_set(v_reuseFailAlloc_6003_, 27, v_n_5988_);
lean_ctor_set(v_reuseFailAlloc_6003_, 28, v_N_5989_);
lean_ctor_set(v_reuseFailAlloc_6003_, 29, v_V_5990_);
lean_ctor_set(v_reuseFailAlloc_6003_, 30, v_z_5991_);
lean_ctor_set(v_reuseFailAlloc_6003_, 31, v_zabbrev_5992_);
lean_ctor_set(v_reuseFailAlloc_6003_, 32, v_v_5993_);
lean_ctor_set(v_reuseFailAlloc_6003_, 33, v_O_5994_);
lean_ctor_set(v_reuseFailAlloc_6003_, 34, v_X_5995_);
lean_ctor_set(v_reuseFailAlloc_6003_, 35, v_x_5996_);
lean_ctor_set(v_reuseFailAlloc_6003_, 36, v___x_6000_);
v___x_6002_ = v_reuseFailAlloc_6003_;
goto v_reusejp_6001_;
}
v_reusejp_6001_:
{
return v___x_6002_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(lean_object* v_year_6006_, uint8_t v_x_6007_){
_start:
{
if (v_x_6007_ == 0)
{
lean_object* v___x_6008_; lean_object* v___x_6009_; 
v___x_6008_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6009_ = lean_int_sub(v___x_6008_, v_year_6006_);
return v___x_6009_;
}
else
{
lean_inc(v_year_6006_);
return v_year_6006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra___boxed(lean_object* v_year_6010_, lean_object* v_x_6011_){
_start:
{
uint8_t v_x_36__boxed_6012_; lean_object* v_res_6013_; 
v_x_36__boxed_6012_ = lean_unbox(v_x_6011_);
v_res_6013_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_year_6010_, v_x_36__boxed_6012_);
lean_dec(v_year_6010_);
return v_res_6013_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(uint8_t v_x_6014_){
_start:
{
switch(v_x_6014_)
{
case 1:
{
uint8_t v___x_6015_; 
v___x_6015_ = 1;
return v___x_6015_;
}
case 2:
{
uint8_t v___x_6016_; 
v___x_6016_ = 1;
return v___x_6016_;
}
default: 
{
uint8_t v___x_6017_; 
v___x_6017_ = 0;
return v___x_6017_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod___boxed(lean_object* v_x_6018_){
_start:
{
uint8_t v_x_28__boxed_6019_; uint8_t v_res_6020_; lean_object* v_r_6021_; 
v_x_28__boxed_6019_ = lean_unbox(v_x_6018_);
v_res_6020_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v_x_28__boxed_6019_);
v_r_6021_ = lean_box(v_res_6020_);
return v_r_6021_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(lean_object* v_hour_6022_, uint8_t v_x_6023_){
_start:
{
switch(v_x_6023_)
{
case 1:
{
lean_object* v___x_6024_; uint8_t v___x_6025_; 
v___x_6024_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__0, &l_Std_Time_classifyExtendedDayPeriod___closed__0_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__0);
v___x_6025_ = lean_int_dec_lt(v_hour_6022_, v___x_6024_);
if (v___x_6025_ == 0)
{
uint8_t v___x_6026_; 
v___x_6026_ = 1;
return v___x_6026_;
}
else
{
uint8_t v___x_6027_; 
v___x_6027_ = 0;
return v___x_6027_;
}
}
case 3:
{
uint8_t v___x_6028_; 
v___x_6028_ = 1;
return v___x_6028_;
}
case 4:
{
uint8_t v___x_6029_; 
v___x_6029_ = 1;
return v___x_6029_;
}
case 5:
{
uint8_t v___x_6030_; 
v___x_6030_ = 1;
return v___x_6030_;
}
default: 
{
uint8_t v___x_6031_; 
v___x_6031_ = 0;
return v___x_6031_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod___boxed(lean_object* v_hour_6032_, lean_object* v_x_6033_){
_start:
{
uint8_t v_x_56__boxed_6034_; uint8_t v_res_6035_; lean_object* v_r_6036_; 
v_x_56__boxed_6034_ = lean_unbox(v_x_6033_);
v_res_6035_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v_hour_6032_, v_x_56__boxed_6034_);
lean_dec(v_hour_6032_);
v_r_6036_ = lean_box(v_res_6035_);
return v_r_6036_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_offsetOfZoneId_x3f___lam__0(lean_object* v___x_6037_, lean_object* v___y_6038_){
_start:
{
lean_object* v_pos_6040_; lean_object* v___x_6060_; 
lean_inc_ref(v___y_6038_);
v___x_6060_ = l_Std_Internal_Parsec_String_pstring(v___x_6037_, v___y_6038_);
if (lean_obj_tag(v___x_6060_) == 0)
{
lean_object* v_pos_6061_; 
lean_dec_ref(v___y_6038_);
v_pos_6061_ = lean_ctor_get(v___x_6060_, 0);
lean_inc(v_pos_6061_);
lean_dec_ref_known(v___x_6060_, 2);
v_pos_6040_ = v_pos_6061_;
goto v___jp_6039_;
}
else
{
lean_object* v_pos_6062_; lean_object* v_err_6063_; lean_object* v___x_6065_; uint8_t v_isShared_6066_; uint8_t v_isSharedCheck_6073_; 
v_pos_6062_ = lean_ctor_get(v___x_6060_, 0);
v_err_6063_ = lean_ctor_get(v___x_6060_, 1);
v_isSharedCheck_6073_ = !lean_is_exclusive(v___x_6060_);
if (v_isSharedCheck_6073_ == 0)
{
v___x_6065_ = v___x_6060_;
v_isShared_6066_ = v_isSharedCheck_6073_;
goto v_resetjp_6064_;
}
else
{
lean_inc(v_err_6063_);
lean_inc(v_pos_6062_);
lean_dec(v___x_6060_);
v___x_6065_ = lean_box(0);
v_isShared_6066_ = v_isSharedCheck_6073_;
goto v_resetjp_6064_;
}
v_resetjp_6064_:
{
lean_object* v_snd_6067_; lean_object* v_snd_6068_; uint8_t v_decide_6069_; 
v_snd_6067_ = lean_ctor_get(v___y_6038_, 1);
lean_inc(v_snd_6067_);
lean_dec_ref(v___y_6038_);
v_snd_6068_ = lean_ctor_get(v_pos_6062_, 1);
v_decide_6069_ = lean_nat_dec_eq(v_snd_6067_, v_snd_6068_);
lean_dec(v_snd_6067_);
if (v_decide_6069_ == 0)
{
lean_object* v___x_6071_; 
if (v_isShared_6066_ == 0)
{
v___x_6071_ = v___x_6065_;
goto v_reusejp_6070_;
}
else
{
lean_object* v_reuseFailAlloc_6072_; 
v_reuseFailAlloc_6072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_pos_6062_);
lean_ctor_set(v_reuseFailAlloc_6072_, 1, v_err_6063_);
v___x_6071_ = v_reuseFailAlloc_6072_;
goto v_reusejp_6070_;
}
v_reusejp_6070_:
{
return v___x_6071_;
}
}
else
{
lean_del_object(v___x_6065_);
lean_dec(v_err_6063_);
v_pos_6040_ = v_pos_6062_;
goto v___jp_6039_;
}
}
}
v___jp_6039_:
{
uint8_t v___x_6041_; uint8_t v___x_6042_; uint8_t v___x_6043_; lean_object* v___x_6044_; 
v___x_6041_ = 0;
v___x_6042_ = 2;
v___x_6043_ = 1;
v___x_6044_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_6041_, v___x_6042_, v___x_6043_, v_pos_6040_);
if (lean_obj_tag(v___x_6044_) == 0)
{
lean_object* v_pos_6045_; lean_object* v_fst_6046_; lean_object* v_snd_6047_; lean_object* v___x_6048_; uint8_t v_decide_6049_; 
v_pos_6045_ = lean_ctor_get(v___x_6044_, 0);
v_fst_6046_ = lean_ctor_get(v_pos_6045_, 0);
v_snd_6047_ = lean_ctor_get(v_pos_6045_, 1);
v___x_6048_ = lean_string_utf8_byte_size(v_fst_6046_);
v_decide_6049_ = lean_nat_dec_eq(v_snd_6047_, v___x_6048_);
if (v_decide_6049_ == 0)
{
lean_object* v___x_6051_; uint8_t v_isShared_6052_; uint8_t v_isSharedCheck_6057_; 
lean_inc(v_pos_6045_);
v_isSharedCheck_6057_ = !lean_is_exclusive(v___x_6044_);
if (v_isSharedCheck_6057_ == 0)
{
lean_object* v_unused_6058_; lean_object* v_unused_6059_; 
v_unused_6058_ = lean_ctor_get(v___x_6044_, 1);
lean_dec(v_unused_6058_);
v_unused_6059_ = lean_ctor_get(v___x_6044_, 0);
lean_dec(v_unused_6059_);
v___x_6051_ = v___x_6044_;
v_isShared_6052_ = v_isSharedCheck_6057_;
goto v_resetjp_6050_;
}
else
{
lean_dec(v___x_6044_);
v___x_6051_ = lean_box(0);
v_isShared_6052_ = v_isSharedCheck_6057_;
goto v_resetjp_6050_;
}
v_resetjp_6050_:
{
lean_object* v___x_6053_; lean_object* v___x_6055_; 
v___x_6053_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_6052_ == 0)
{
lean_ctor_set_tag(v___x_6051_, 1);
lean_ctor_set(v___x_6051_, 1, v___x_6053_);
v___x_6055_ = v___x_6051_;
goto v_reusejp_6054_;
}
else
{
lean_object* v_reuseFailAlloc_6056_; 
v_reuseFailAlloc_6056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6056_, 0, v_pos_6045_);
lean_ctor_set(v_reuseFailAlloc_6056_, 1, v___x_6053_);
v___x_6055_ = v_reuseFailAlloc_6056_;
goto v_reusejp_6054_;
}
v_reusejp_6054_:
{
return v___x_6055_;
}
}
}
else
{
return v___x_6044_;
}
}
else
{
return v___x_6044_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_offsetOfZoneId_x3f(lean_object* v_id_6076_){
_start:
{
lean_object* v___f_6077_; lean_object* v___x_6078_; 
v___f_6077_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_offsetOfZoneId_x3f___closed__0));
v___x_6078_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_6077_, v_id_6076_);
if (lean_obj_tag(v___x_6078_) == 0)
{
lean_object* v___x_6079_; 
lean_dec_ref_known(v___x_6078_, 1);
v___x_6079_ = lean_box(0);
return v___x_6079_;
}
else
{
lean_object* v_a_6080_; lean_object* v___x_6082_; uint8_t v_isShared_6083_; uint8_t v_isSharedCheck_6087_; 
v_a_6080_ = lean_ctor_get(v___x_6078_, 0);
v_isSharedCheck_6087_ = !lean_is_exclusive(v___x_6078_);
if (v_isSharedCheck_6087_ == 0)
{
v___x_6082_ = v___x_6078_;
v_isShared_6083_ = v_isSharedCheck_6087_;
goto v_resetjp_6081_;
}
else
{
lean_inc(v_a_6080_);
lean_dec(v___x_6078_);
v___x_6082_ = lean_box(0);
v_isShared_6083_ = v_isSharedCheck_6087_;
goto v_resetjp_6081_;
}
v_resetjp_6081_:
{
lean_object* v___x_6085_; 
if (v_isShared_6083_ == 0)
{
v___x_6085_ = v___x_6082_;
goto v_reusejp_6084_;
}
else
{
lean_object* v_reuseFailAlloc_6086_; 
v_reuseFailAlloc_6086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6086_, 0, v_a_6080_);
v___x_6085_ = v_reuseFailAlloc_6086_;
goto v_reusejp_6084_;
}
v_reusejp_6084_:
{
return v___x_6085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekDate(lean_object* v_dateformat_6088_, lean_object* v_year_6089_, lean_object* v_week_6090_, uint8_t v_weekday_6091_){
_start:
{
uint8_t v_firstDayOfWeek_6092_; lean_object* v_minimalDaysInFirstWeek_6093_; lean_object* v_start_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v_dayOfWeek_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v_dateDays_6104_; lean_object* v___x_6105_; lean_object* v_date_6106_; lean_object* v___x_6107_; uint8_t v___x_6108_; 
v_firstDayOfWeek_6092_ = lean_ctor_get_uint8(v_dateformat_6088_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_6093_ = lean_ctor_get(v_dateformat_6088_, 0);
lean_inc(v_year_6089_);
v_start_6094_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v_year_6089_, v_firstDayOfWeek_6092_, v_minimalDaysInFirstWeek_6093_);
v___x_6095_ = l_Std_Time_Weekday_toOrdinal(v_weekday_6091_);
v___x_6096_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_6092_);
v___x_6097_ = lean_int_sub(v___x_6095_, v___x_6096_);
lean_dec(v___x_6096_);
lean_dec(v___x_6095_);
v___x_6098_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v_dayOfWeek_6099_ = lean_int_emod(v___x_6097_, v___x_6098_);
lean_dec(v___x_6097_);
v___x_6100_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6101_ = lean_int_sub(v_week_6090_, v___x_6100_);
v___x_6102_ = lean_int_mul(v___x_6101_, v___x_6098_);
lean_dec(v___x_6101_);
v___x_6103_ = lean_int_add(v___x_6102_, v_dayOfWeek_6099_);
lean_dec(v_dayOfWeek_6099_);
lean_dec(v___x_6102_);
v_dateDays_6104_ = l_Std_Time_PlainDate_toEpochDay(v_start_6094_);
v___x_6105_ = lean_int_add(v_dateDays_6104_, v___x_6103_);
lean_dec(v___x_6103_);
lean_dec(v_dateDays_6104_);
v_date_6106_ = l_Std_Time_PlainDate_ofEpochDay(v___x_6105_);
lean_dec(v___x_6105_);
lean_inc_ref(v_date_6106_);
v___x_6107_ = l_Std_Time_PlainDate_weekYear(v_date_6106_, v_firstDayOfWeek_6092_, v_minimalDaysInFirstWeek_6093_);
v___x_6108_ = lean_int_dec_eq(v___x_6107_, v_year_6089_);
lean_dec(v_year_6089_);
lean_dec(v___x_6107_);
if (v___x_6108_ == 0)
{
lean_object* v___x_6109_; 
lean_dec_ref(v_date_6106_);
v___x_6109_ = lean_box(0);
return v___x_6109_;
}
else
{
lean_object* v___x_6110_; 
v___x_6110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6110_, 0, v_date_6106_);
return v___x_6110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekDate___boxed(lean_object* v_dateformat_6111_, lean_object* v_year_6112_, lean_object* v_week_6113_, lean_object* v_weekday_6114_){
_start:
{
uint8_t v_weekday_boxed_6115_; lean_object* v_res_6116_; 
v_weekday_boxed_6115_ = lean_unbox(v_weekday_6114_);
v_res_6116_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekDate(v_dateformat_6111_, v_year_6112_, v_week_6113_, v_weekday_boxed_6115_);
lean_dec(v_week_6113_);
lean_dec_ref(v_dateformat_6111_);
return v_res_6116_;
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___at___00__private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay_spec__0(lean_object* v_month_6117_, lean_object* v_day_6118_, lean_object* v_dateformat_6119_, lean_object* v_year_6120_, lean_object* v_x_6121_){
_start:
{
if (lean_obj_tag(v_x_6121_) == 0)
{
lean_object* v___x_6122_; 
lean_dec(v_day_6118_);
lean_dec(v_month_6117_);
v___x_6122_ = lean_box(0);
return v___x_6122_;
}
else
{
lean_object* v_head_6123_; lean_object* v_tail_6124_; uint8_t v___y_6126_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; uint8_t v___x_6140_; 
v_head_6123_ = lean_ctor_get(v_x_6121_, 0);
v_tail_6124_ = lean_ctor_get(v_x_6121_, 1);
v___x_6137_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0);
v___x_6138_ = lean_int_mod(v_head_6123_, v___x_6137_);
v___x_6139_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6140_ = lean_int_dec_eq(v___x_6138_, v___x_6139_);
lean_dec(v___x_6138_);
if (v___x_6140_ == 0)
{
v___y_6126_ = v___x_6140_;
goto v___jp_6125_;
}
else
{
lean_object* v___x_6141_; lean_object* v___x_6142_; uint8_t v___x_6143_; 
v___x_6141_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_6142_ = lean_int_mod(v_head_6123_, v___x_6141_);
v___x_6143_ = lean_int_dec_eq(v___x_6142_, v___x_6139_);
lean_dec(v___x_6142_);
if (v___x_6143_ == 0)
{
v___y_6126_ = v___x_6140_;
goto v___jp_6125_;
}
else
{
lean_object* v___x_6144_; lean_object* v___x_6145_; uint8_t v___x_6146_; 
v___x_6144_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1);
v___x_6145_ = lean_int_mod(v_head_6123_, v___x_6144_);
v___x_6146_ = lean_int_dec_eq(v___x_6145_, v___x_6139_);
lean_dec(v___x_6145_);
v___y_6126_ = v___x_6146_;
goto v___jp_6125_;
}
}
v___jp_6125_:
{
lean_object* v___x_6127_; uint8_t v___x_6128_; 
v___x_6127_ = l_Std_Time_Month_Ordinal_days(v___y_6126_, v_month_6117_);
v___x_6128_ = lean_int_dec_le(v_day_6118_, v___x_6127_);
lean_dec(v___x_6127_);
if (v___x_6128_ == 0)
{
v_x_6121_ = v_tail_6124_;
goto _start;
}
else
{
uint8_t v_firstDayOfWeek_6130_; lean_object* v_minimalDaysInFirstWeek_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; uint8_t v___x_6135_; 
v_firstDayOfWeek_6130_ = lean_ctor_get_uint8(v_dateformat_6119_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_6131_ = lean_ctor_get(v_dateformat_6119_, 0);
lean_inc(v_day_6118_);
lean_inc(v_month_6117_);
lean_inc(v_head_6123_);
v___x_6132_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6132_, 0, v_head_6123_);
lean_ctor_set(v___x_6132_, 1, v_month_6117_);
lean_ctor_set(v___x_6132_, 2, v_day_6118_);
lean_inc_ref(v___x_6132_);
v___x_6133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6133_, 0, v___x_6132_);
v___x_6134_ = l_Std_Time_PlainDate_weekYear(v___x_6132_, v_firstDayOfWeek_6130_, v_minimalDaysInFirstWeek_6131_);
v___x_6135_ = lean_int_dec_eq(v___x_6134_, v_year_6120_);
lean_dec(v___x_6134_);
if (v___x_6135_ == 0)
{
lean_dec_ref_known(v___x_6133_, 1);
v_x_6121_ = v_tail_6124_;
goto _start;
}
else
{
lean_dec(v_day_6118_);
lean_dec(v_month_6117_);
return v___x_6133_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___at___00__private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay_spec__0___boxed(lean_object* v_month_6147_, lean_object* v_day_6148_, lean_object* v_dateformat_6149_, lean_object* v_year_6150_, lean_object* v_x_6151_){
_start:
{
lean_object* v_res_6152_; 
v_res_6152_ = l_List_findSome_x3f___at___00__private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay_spec__0(v_month_6147_, v_day_6148_, v_dateformat_6149_, v_year_6150_, v_x_6151_);
lean_dec(v_x_6151_);
lean_dec(v_year_6150_);
lean_dec_ref(v_dateformat_6149_);
return v_res_6152_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay(lean_object* v_dateformat_6153_, lean_object* v_year_6154_, lean_object* v_month_6155_, lean_object* v_day_6156_){
_start:
{
lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; 
v___x_6157_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6158_ = lean_int_sub(v_year_6154_, v___x_6157_);
v___x_6159_ = lean_int_add(v_year_6154_, v___x_6157_);
v___x_6160_ = lean_box(0);
v___x_6161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6161_, 0, v___x_6159_);
lean_ctor_set(v___x_6161_, 1, v___x_6160_);
v___x_6162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6162_, 0, v___x_6158_);
lean_ctor_set(v___x_6162_, 1, v___x_6161_);
lean_inc(v_year_6154_);
v___x_6163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6163_, 0, v_year_6154_);
lean_ctor_set(v___x_6163_, 1, v___x_6162_);
v___x_6164_ = l_List_findSome_x3f___at___00__private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay_spec__0(v_month_6155_, v_day_6156_, v_dateformat_6153_, v_year_6154_, v___x_6163_);
lean_dec_ref_known(v___x_6163_, 2);
lean_dec(v_year_6154_);
return v___x_6164_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay___boxed(lean_object* v_dateformat_6165_, lean_object* v_year_6166_, lean_object* v_month_6167_, lean_object* v_day_6168_){
_start:
{
lean_object* v_res_6169_; 
v_res_6169_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay(v_dateformat_6165_, v_year_6166_, v_month_6167_, v_day_6168_);
lean_dec_ref(v_dateformat_6165_);
return v_res_6169_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__0(void){
_start:
{
lean_object* v___x_6170_; lean_object* v___x_6171_; 
v___x_6170_ = lean_unsigned_to_nat(11u);
v___x_6171_ = lean_nat_to_int(v___x_6170_);
return v___x_6171_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; 
v___x_6172_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__0);
v___x_6173_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6174_ = lean_int_add(v___x_6173_, v___x_6172_);
return v___x_6174_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__2(void){
_start:
{
lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; 
v___x_6175_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6176_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__1);
v___x_6177_ = lean_int_sub(v___x_6176_, v___x_6175_);
return v___x_6177_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3(void){
_start:
{
lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v_range_6180_; 
v___x_6178_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6179_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__2);
v_range_6180_ = lean_int_add(v___x_6179_, v___x_6178_);
return v_range_6180_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4(void){
_start:
{
lean_object* v___x_6181_; lean_object* v___x_6182_; 
v___x_6181_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6182_ = lean_int_sub(v___x_6181_, v___x_6181_);
return v___x_6182_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__5(void){
_start:
{
lean_object* v_range_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; 
v_range_6183_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3);
v___x_6184_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4);
v___x_6185_ = lean_int_emod(v___x_6184_, v_range_6183_);
return v___x_6185_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__6(void){
_start:
{
lean_object* v_range_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; 
v_range_6186_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3);
v___x_6187_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__5);
v___x_6188_ = lean_int_add(v___x_6187_, v_range_6186_);
return v___x_6188_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__7(void){
_start:
{
lean_object* v_range_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; 
v_range_6189_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3);
v___x_6190_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__6);
v___x_6191_ = lean_int_emod(v___x_6190_, v_range_6189_);
return v___x_6191_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__8(void){
_start:
{
lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; 
v___x_6192_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6193_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__7, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__7_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__7);
v___x_6194_ = lean_int_add(v___x_6193_, v___x_6192_);
return v___x_6194_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__9(void){
_start:
{
lean_object* v___x_6195_; lean_object* v___x_6196_; 
v___x_6195_ = lean_unsigned_to_nat(30u);
v___x_6196_ = lean_nat_to_int(v___x_6195_);
return v___x_6196_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__10(void){
_start:
{
lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; 
v___x_6197_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__9, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__9_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__9);
v___x_6198_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6199_ = lean_int_add(v___x_6198_, v___x_6197_);
return v___x_6199_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__11(void){
_start:
{
lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; 
v___x_6200_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6201_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__10, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__10_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__10);
v___x_6202_ = lean_int_sub(v___x_6201_, v___x_6200_);
return v___x_6202_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12(void){
_start:
{
lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v_range_6205_; 
v___x_6203_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6204_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__11, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__11_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__11);
v_range_6205_ = lean_int_add(v___x_6204_, v___x_6203_);
return v_range_6205_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__13(void){
_start:
{
lean_object* v_range_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; 
v_range_6206_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12);
v___x_6207_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4);
v___x_6208_ = lean_int_emod(v___x_6207_, v_range_6206_);
return v___x_6208_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__14(void){
_start:
{
lean_object* v_range_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; 
v_range_6209_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12);
v___x_6210_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__13, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__13_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__13);
v___x_6211_ = lean_int_add(v___x_6210_, v_range_6209_);
return v___x_6211_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__15(void){
_start:
{
lean_object* v_range_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; 
v_range_6212_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12);
v___x_6213_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__14, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__14_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__14);
v___x_6214_ = lean_int_emod(v___x_6213_, v_range_6212_);
return v___x_6214_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__16(void){
_start:
{
lean_object* v___x_6215_; lean_object* v___x_6216_; lean_object* v___x_6217_; 
v___x_6215_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6216_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__15);
v___x_6217_ = lean_int_add(v___x_6216_, v___x_6215_);
return v___x_6217_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(lean_object* v_year_x3f_6218_, lean_object* v_x_6219_){
_start:
{
lean_object* v___y_6221_; lean_object* v___y_6222_; lean_object* v___y_6223_; uint8_t v___y_6224_; lean_object* v___y_6231_; 
if (lean_obj_tag(v_year_x3f_6218_) == 0)
{
lean_object* v___x_6244_; 
v___x_6244_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6231_ = v___x_6244_;
goto v___jp_6230_;
}
else
{
lean_object* v_val_6245_; 
v_val_6245_ = lean_ctor_get(v_year_x3f_6218_, 0);
lean_inc(v_val_6245_);
lean_dec_ref_known(v_year_x3f_6218_, 1);
v___y_6231_ = v_val_6245_;
goto v___jp_6230_;
}
v___jp_6220_:
{
lean_object* v___x_6225_; uint8_t v___x_6226_; 
v___x_6225_ = l_Std_Time_Month_Ordinal_days(v___y_6224_, v___y_6222_);
v___x_6226_ = lean_int_dec_le(v___y_6223_, v___x_6225_);
lean_dec(v___x_6225_);
if (v___x_6226_ == 0)
{
lean_object* v___x_6227_; 
lean_dec(v___y_6221_);
v___x_6227_ = lean_box(0);
return v___x_6227_;
}
else
{
lean_object* v___x_6228_; lean_object* v___x_6229_; 
lean_inc(v___y_6223_);
lean_inc(v___y_6222_);
v___x_6228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6228_, 0, v___y_6221_);
lean_ctor_set(v___x_6228_, 1, v___y_6222_);
lean_ctor_set(v___x_6228_, 2, v___y_6223_);
v___x_6229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6229_, 0, v___x_6228_);
return v___x_6229_;
}
}
v___jp_6230_:
{
lean_object* v___x_6232_; lean_object* v___x_6233_; lean_object* v___x_6234_; lean_object* v___x_6235_; lean_object* v___x_6236_; uint8_t v___x_6237_; 
v___x_6232_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__8);
v___x_6233_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__16);
v___x_6234_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0);
v___x_6235_ = lean_int_mod(v___y_6231_, v___x_6234_);
v___x_6236_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6237_ = lean_int_dec_eq(v___x_6235_, v___x_6236_);
lean_dec(v___x_6235_);
if (v___x_6237_ == 0)
{
v___y_6221_ = v___y_6231_;
v___y_6222_ = v___x_6232_;
v___y_6223_ = v___x_6233_;
v___y_6224_ = v___x_6237_;
goto v___jp_6220_;
}
else
{
lean_object* v___x_6238_; lean_object* v___x_6239_; uint8_t v___x_6240_; 
v___x_6238_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_6239_ = lean_int_mod(v___y_6231_, v___x_6238_);
v___x_6240_ = lean_int_dec_eq(v___x_6239_, v___x_6236_);
lean_dec(v___x_6239_);
if (v___x_6240_ == 0)
{
v___y_6221_ = v___y_6231_;
v___y_6222_ = v___x_6232_;
v___y_6223_ = v___x_6233_;
v___y_6224_ = v___x_6237_;
goto v___jp_6220_;
}
else
{
lean_object* v___x_6241_; lean_object* v___x_6242_; uint8_t v___x_6243_; 
v___x_6241_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1);
v___x_6242_ = lean_int_mod(v___y_6231_, v___x_6241_);
v___x_6243_ = lean_int_dec_eq(v___x_6242_, v___x_6236_);
lean_dec(v___x_6242_);
v___y_6221_ = v___y_6231_;
v___y_6222_ = v___x_6232_;
v___y_6223_ = v___x_6233_;
v___y_6224_ = v___x_6243_;
goto v___jp_6220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed(lean_object* v_year_x3f_6246_, lean_object* v_x_6247_){
_start:
{
lean_object* v_res_6248_; 
v_res_6248_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(v_year_x3f_6246_, v_x_6247_);
lean_dec(v_x_6247_);
return v_res_6248_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(lean_object* v_val_6249_, lean_object* v_x_6250_){
_start:
{
lean_inc_ref(v_val_6249_);
return v_val_6249_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1___boxed(lean_object* v_val_6251_, lean_object* v_x_6252_){
_start:
{
lean_object* v_res_6253_; 
v_res_6253_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(v_val_6251_, v_x_6252_);
lean_dec_ref(v_val_6251_);
return v_res_6253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__2(lean_object* v_h_6254_, lean_object* v_K_6255_, uint8_t v_marker_6256_){
_start:
{
if (lean_obj_tag(v_h_6254_) == 0)
{
if (lean_obj_tag(v_K_6255_) == 0)
{
return v_K_6255_;
}
else
{
if (v_marker_6256_ == 0)
{
lean_object* v_val_6257_; lean_object* v___x_6259_; uint8_t v_isShared_6260_; uint8_t v_isSharedCheck_6264_; 
v_val_6257_ = lean_ctor_get(v_K_6255_, 0);
v_isSharedCheck_6264_ = !lean_is_exclusive(v_K_6255_);
if (v_isSharedCheck_6264_ == 0)
{
v___x_6259_ = v_K_6255_;
v_isShared_6260_ = v_isSharedCheck_6264_;
goto v_resetjp_6258_;
}
else
{
lean_inc(v_val_6257_);
lean_dec(v_K_6255_);
v___x_6259_ = lean_box(0);
v_isShared_6260_ = v_isSharedCheck_6264_;
goto v_resetjp_6258_;
}
v_resetjp_6258_:
{
lean_object* v___x_6262_; 
if (v_isShared_6260_ == 0)
{
v___x_6262_ = v___x_6259_;
goto v_reusejp_6261_;
}
else
{
lean_object* v_reuseFailAlloc_6263_; 
v_reuseFailAlloc_6263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6263_, 0, v_val_6257_);
v___x_6262_ = v_reuseFailAlloc_6263_;
goto v_reusejp_6261_;
}
v_reusejp_6261_:
{
return v___x_6262_;
}
}
}
else
{
lean_object* v_val_6265_; lean_object* v___x_6267_; uint8_t v_isShared_6268_; uint8_t v_isSharedCheck_6274_; 
v_val_6265_ = lean_ctor_get(v_K_6255_, 0);
v_isSharedCheck_6274_ = !lean_is_exclusive(v_K_6255_);
if (v_isSharedCheck_6274_ == 0)
{
v___x_6267_ = v_K_6255_;
v_isShared_6268_ = v_isSharedCheck_6274_;
goto v_resetjp_6266_;
}
else
{
lean_inc(v_val_6265_);
lean_dec(v_K_6255_);
v___x_6267_ = lean_box(0);
v_isShared_6268_ = v_isSharedCheck_6274_;
goto v_resetjp_6266_;
}
v_resetjp_6266_:
{
lean_object* v___x_6269_; lean_object* v___x_6270_; lean_object* v___x_6272_; 
v___x_6269_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_6270_ = lean_int_add(v_val_6265_, v___x_6269_);
lean_dec(v_val_6265_);
if (v_isShared_6268_ == 0)
{
lean_ctor_set(v___x_6267_, 0, v___x_6270_);
v___x_6272_ = v___x_6267_;
goto v_reusejp_6271_;
}
else
{
lean_object* v_reuseFailAlloc_6273_; 
v_reuseFailAlloc_6273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6273_, 0, v___x_6270_);
v___x_6272_ = v_reuseFailAlloc_6273_;
goto v_reusejp_6271_;
}
v_reusejp_6271_:
{
return v___x_6272_;
}
}
}
}
}
else
{
lean_object* v_val_6275_; lean_object* v___x_6277_; uint8_t v_isShared_6278_; uint8_t v_isSharedCheck_6283_; 
lean_dec(v_K_6255_);
v_val_6275_ = lean_ctor_get(v_h_6254_, 0);
v_isSharedCheck_6283_ = !lean_is_exclusive(v_h_6254_);
if (v_isSharedCheck_6283_ == 0)
{
v___x_6277_ = v_h_6254_;
v_isShared_6278_ = v_isSharedCheck_6283_;
goto v_resetjp_6276_;
}
else
{
lean_inc(v_val_6275_);
lean_dec(v_h_6254_);
v___x_6277_ = lean_box(0);
v_isShared_6278_ = v_isSharedCheck_6283_;
goto v_resetjp_6276_;
}
v_resetjp_6276_:
{
lean_object* v___x_6279_; lean_object* v___x_6281_; 
v___x_6279_ = l_Std_Time_HourMarker_toAbsolute(v_marker_6256_, v_val_6275_);
lean_dec(v_val_6275_);
if (v_isShared_6278_ == 0)
{
lean_ctor_set(v___x_6277_, 0, v___x_6279_);
v___x_6281_ = v___x_6277_;
goto v_reusejp_6280_;
}
else
{
lean_object* v_reuseFailAlloc_6282_; 
v_reuseFailAlloc_6282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6282_, 0, v___x_6279_);
v___x_6281_ = v_reuseFailAlloc_6282_;
goto v_reusejp_6280_;
}
v_reusejp_6280_:
{
return v___x_6281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__2___boxed(lean_object* v_h_6284_, lean_object* v_K_6285_, lean_object* v_marker_6286_){
_start:
{
uint8_t v_marker_boxed_6287_; lean_object* v_res_6288_; 
v_marker_boxed_6287_ = lean_unbox(v_marker_6286_);
v_res_6288_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__2(v_h_6284_, v_K_6285_, v_marker_boxed_6287_);
return v_res_6288_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__3(lean_object* v___y_6289_, lean_object* v_00___6290_){
_start:
{
uint8_t v___x_6291_; lean_object* v___x_6292_; 
v___x_6291_ = 1;
v___x_6292_ = l_Std_Time_TimeZone_Offset_toIsoString(v___y_6289_, v___x_6291_);
return v___x_6292_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1(void){
_start:
{
lean_object* v___x_6295_; lean_object* v___x_6296_; 
v___x_6295_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6296_ = lean_int_neg(v___x_6295_);
return v___x_6296_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2(void){
_start:
{
lean_object* v___x_6297_; lean_object* v___x_6298_; 
v___x_6297_ = lean_unsigned_to_nat(1000000u);
v___x_6298_ = lean_nat_to_int(v___x_6297_);
return v___x_6298_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3(void){
_start:
{
lean_object* v___x_6299_; lean_object* v___x_6300_; lean_object* v___x_6301_; 
v___x_6299_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5);
v___x_6300_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6301_ = lean_int_add(v___x_6300_, v___x_6299_);
return v___x_6301_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4(void){
_start:
{
lean_object* v___x_6302_; lean_object* v___x_6303_; lean_object* v___x_6304_; 
v___x_6302_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6303_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3);
v___x_6304_ = lean_int_sub(v___x_6303_, v___x_6302_);
return v___x_6304_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5(void){
_start:
{
lean_object* v___x_6305_; lean_object* v___x_6306_; lean_object* v_range_6307_; 
v___x_6305_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6306_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4);
v_range_6307_ = lean_int_add(v___x_6306_, v___x_6305_);
return v_range_6307_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6(void){
_start:
{
lean_object* v___x_6308_; lean_object* v___x_6309_; 
v___x_6308_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6309_ = lean_int_sub(v___x_6308_, v___x_6308_);
return v___x_6309_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7(void){
_start:
{
lean_object* v_range_6310_; lean_object* v___x_6311_; lean_object* v___x_6312_; 
v_range_6310_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5);
v___x_6311_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6);
v___x_6312_ = lean_int_emod(v___x_6311_, v_range_6310_);
return v___x_6312_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8(void){
_start:
{
lean_object* v_range_6313_; lean_object* v___x_6314_; lean_object* v___x_6315_; 
v_range_6313_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5);
v___x_6314_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7);
v___x_6315_ = lean_int_add(v___x_6314_, v_range_6313_);
return v___x_6315_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9(void){
_start:
{
lean_object* v_range_6316_; lean_object* v___x_6317_; lean_object* v___x_6318_; 
v_range_6316_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5);
v___x_6317_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8);
v___x_6318_ = lean_int_emod(v___x_6317_, v_range_6316_);
return v___x_6318_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10(void){
_start:
{
lean_object* v___x_6319_; lean_object* v___x_6320_; lean_object* v___x_6321_; 
v___x_6319_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6320_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9);
v___x_6321_ = lean_int_add(v___x_6320_, v___x_6319_);
return v___x_6321_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11(void){
_start:
{
lean_object* v___x_6322_; lean_object* v___x_6323_; 
v___x_6322_ = lean_unsigned_to_nat(24u);
v___x_6323_ = lean_nat_to_int(v___x_6322_);
return v___x_6323_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12(void){
_start:
{
lean_object* v___x_6324_; lean_object* v___x_6325_; 
v___x_6324_ = lean_unsigned_to_nat(52u);
v___x_6325_ = lean_nat_to_int(v___x_6324_);
return v___x_6325_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13(void){
_start:
{
lean_object* v___x_6326_; lean_object* v___x_6327_; lean_object* v___x_6328_; 
v___x_6326_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12);
v___x_6327_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6328_ = lean_int_add(v___x_6327_, v___x_6326_);
return v___x_6328_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14(void){
_start:
{
lean_object* v___x_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; 
v___x_6329_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6330_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13);
v___x_6331_ = lean_int_sub(v___x_6330_, v___x_6329_);
return v___x_6331_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15(void){
_start:
{
lean_object* v___x_6332_; lean_object* v___x_6333_; lean_object* v_range_6334_; 
v___x_6332_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6333_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14);
v_range_6334_ = lean_int_add(v___x_6333_, v___x_6332_);
return v_range_6334_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16(void){
_start:
{
lean_object* v_range_6335_; lean_object* v___x_6336_; lean_object* v___x_6337_; 
v_range_6335_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v___x_6336_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4);
v___x_6337_ = lean_int_emod(v___x_6336_, v_range_6335_);
return v___x_6337_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17(void){
_start:
{
lean_object* v_range_6338_; lean_object* v___x_6339_; lean_object* v___x_6340_; 
v_range_6338_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v___x_6339_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16);
v___x_6340_ = lean_int_add(v___x_6339_, v_range_6338_);
return v___x_6340_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18(void){
_start:
{
lean_object* v_range_6341_; lean_object* v___x_6342_; lean_object* v___x_6343_; 
v_range_6341_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v___x_6342_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17);
v___x_6343_ = lean_int_emod(v___x_6342_, v_range_6341_);
return v___x_6343_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19(void){
_start:
{
lean_object* v___x_6344_; lean_object* v___x_6345_; lean_object* v___x_6346_; 
v___x_6344_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6345_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18);
v___x_6346_ = lean_int_add(v___x_6345_, v___x_6344_);
return v___x_6346_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(lean_object* v_builder_6347_, lean_object* v_aw_6348_, lean_object* v_dateformat_6349_){
_start:
{
lean_object* v___y_6351_; lean_object* v___y_6352_; lean_object* v___y_6391_; lean_object* v___y_6392_; lean_object* v___y_6395_; lean_object* v___y_6396_; lean_object* v___y_6397_; lean_object* v_G_6408_; lean_object* v_y_6409_; lean_object* v_u_6410_; lean_object* v_Y_6411_; lean_object* v_D_6412_; lean_object* v_M_6413_; lean_object* v_L_6414_; lean_object* v_d_6415_; lean_object* v_w_6416_; lean_object* v_E_6417_; lean_object* v_e_6418_; lean_object* v_c_6419_; lean_object* v_a_6420_; lean_object* v_b_6421_; lean_object* v_B_6422_; lean_object* v_h_6423_; lean_object* v_K_6424_; lean_object* v_k_6425_; lean_object* v_H_6426_; lean_object* v_m_6427_; lean_object* v_s_6428_; lean_object* v_S_6429_; lean_object* v_A_6430_; lean_object* v_n_6431_; lean_object* v_N_6432_; lean_object* v_V_6433_; lean_object* v_z_6434_; lean_object* v_zabbrev_6435_; lean_object* v_v_6436_; lean_object* v_O_6437_; lean_object* v_X_6438_; lean_object* v_x_6439_; lean_object* v_Z_6440_; lean_object* v___y_6442_; lean_object* v___y_6443_; lean_object* v___y_6444_; lean_object* v___y_6445_; lean_object* v___y_6446_; lean_object* v___y_6447_; lean_object* v___y_6456_; lean_object* v___y_6457_; lean_object* v___y_6458_; lean_object* v___y_6459_; lean_object* v___y_6460_; lean_object* v___y_6465_; uint8_t v___y_6466_; lean_object* v___y_6467_; lean_object* v___y_6468_; lean_object* v___y_6469_; lean_object* v___y_6474_; uint8_t v___y_6475_; lean_object* v___y_6476_; lean_object* v___y_6477_; lean_object* v___y_6481_; uint8_t v___y_6482_; lean_object* v___y_6483_; lean_object* v___y_6484_; lean_object* v___y_6485_; lean_object* v___y_6493_; uint8_t v___y_6494_; lean_object* v___y_6495_; lean_object* v___y_6496_; lean_object* v___y_6497_; lean_object* v___y_6498_; lean_object* v___y_6503_; uint8_t v___y_6504_; lean_object* v___y_6505_; lean_object* v___y_6506_; lean_object* v___y_6507_; lean_object* v___y_6508_; lean_object* v___y_6509_; lean_object* v___y_6511_; uint8_t v___y_6512_; lean_object* v___y_6513_; lean_object* v___y_6514_; lean_object* v___y_6515_; lean_object* v___y_6516_; lean_object* v___y_6517_; lean_object* v___y_6529_; lean_object* v___y_6530_; uint8_t v___y_6531_; lean_object* v___y_6532_; lean_object* v___y_6533_; lean_object* v___y_6534_; lean_object* v___y_6535_; lean_object* v___y_6536_; lean_object* v___y_6537_; lean_object* v___y_6550_; lean_object* v___y_6551_; uint8_t v___y_6552_; lean_object* v___y_6553_; lean_object* v___y_6554_; lean_object* v___y_6555_; lean_object* v___y_6556_; lean_object* v___y_6557_; lean_object* v___y_6558_; lean_object* v___y_6559_; uint8_t v___y_6574_; lean_object* v___y_6575_; lean_object* v___y_6576_; uint8_t v___y_6598_; lean_object* v___y_6599_; lean_object* v___y_6600_; lean_object* v___y_6601_; uint8_t v___y_6602_; uint8_t v___y_6608_; lean_object* v___y_6609_; lean_object* v___y_6610_; lean_object* v___y_6611_; uint8_t v___y_6612_; uint8_t v___y_6619_; lean_object* v___y_6620_; lean_object* v___y_6621_; lean_object* v___y_6622_; lean_object* v___y_6623_; lean_object* v___y_6624_; uint8_t v___y_6641_; lean_object* v___y_6642_; lean_object* v___y_6643_; lean_object* v___y_6644_; lean_object* v___y_6645_; uint8_t v___y_6648_; lean_object* v___y_6649_; lean_object* v___y_6650_; lean_object* v___y_6651_; lean_object* v___y_6652_; uint8_t v___y_6655_; lean_object* v___y_6656_; lean_object* v___y_6657_; lean_object* v___y_6658_; uint8_t v___y_6671_; lean_object* v___y_6672_; lean_object* v___y_6673_; lean_object* v___y_6674_; lean_object* v___y_6675_; uint8_t v___y_6676_; uint8_t v___y_6683_; lean_object* v___y_6684_; lean_object* v___y_6685_; lean_object* v___y_6686_; lean_object* v___y_6687_; uint8_t v___y_6699_; lean_object* v___y_6700_; lean_object* v___y_6701_; lean_object* v___y_6702_; uint8_t v___y_6705_; lean_object* v___y_6706_; lean_object* v___y_6707_; lean_object* v___y_6708_; lean_object* v___y_6709_; uint8_t v___y_6714_; lean_object* v___y_6715_; lean_object* v___y_6716_; lean_object* v___y_6717_; uint8_t v___y_6721_; lean_object* v___y_6722_; lean_object* v___y_6723_; lean_object* v___y_6726_; lean_object* v___y_6727_; lean_object* v_val_6728_; lean_object* v___y_6731_; uint8_t v___y_6732_; lean_object* v___y_6733_; lean_object* v___y_6756_; lean_object* v___y_6757_; lean_object* v___y_6758_; lean_object* v___y_6783_; lean_object* v___y_6784_; lean_object* v___y_6785_; lean_object* v___y_6790_; lean_object* v_val_6800_; 
v_G_6408_ = lean_ctor_get(v_builder_6347_, 0);
lean_inc(v_G_6408_);
v_y_6409_ = lean_ctor_get(v_builder_6347_, 1);
lean_inc(v_y_6409_);
v_u_6410_ = lean_ctor_get(v_builder_6347_, 2);
lean_inc(v_u_6410_);
v_Y_6411_ = lean_ctor_get(v_builder_6347_, 3);
lean_inc(v_Y_6411_);
v_D_6412_ = lean_ctor_get(v_builder_6347_, 4);
lean_inc(v_D_6412_);
v_M_6413_ = lean_ctor_get(v_builder_6347_, 5);
lean_inc(v_M_6413_);
v_L_6414_ = lean_ctor_get(v_builder_6347_, 6);
lean_inc(v_L_6414_);
v_d_6415_ = lean_ctor_get(v_builder_6347_, 7);
lean_inc(v_d_6415_);
v_w_6416_ = lean_ctor_get(v_builder_6347_, 10);
lean_inc(v_w_6416_);
v_E_6417_ = lean_ctor_get(v_builder_6347_, 12);
lean_inc(v_E_6417_);
v_e_6418_ = lean_ctor_get(v_builder_6347_, 13);
lean_inc(v_e_6418_);
v_c_6419_ = lean_ctor_get(v_builder_6347_, 14);
lean_inc(v_c_6419_);
v_a_6420_ = lean_ctor_get(v_builder_6347_, 16);
lean_inc(v_a_6420_);
v_b_6421_ = lean_ctor_get(v_builder_6347_, 17);
lean_inc(v_b_6421_);
v_B_6422_ = lean_ctor_get(v_builder_6347_, 18);
lean_inc(v_B_6422_);
v_h_6423_ = lean_ctor_get(v_builder_6347_, 19);
lean_inc(v_h_6423_);
v_K_6424_ = lean_ctor_get(v_builder_6347_, 20);
lean_inc(v_K_6424_);
v_k_6425_ = lean_ctor_get(v_builder_6347_, 21);
lean_inc(v_k_6425_);
v_H_6426_ = lean_ctor_get(v_builder_6347_, 22);
lean_inc(v_H_6426_);
v_m_6427_ = lean_ctor_get(v_builder_6347_, 23);
lean_inc(v_m_6427_);
v_s_6428_ = lean_ctor_get(v_builder_6347_, 24);
lean_inc(v_s_6428_);
v_S_6429_ = lean_ctor_get(v_builder_6347_, 25);
lean_inc(v_S_6429_);
v_A_6430_ = lean_ctor_get(v_builder_6347_, 26);
lean_inc(v_A_6430_);
v_n_6431_ = lean_ctor_get(v_builder_6347_, 27);
lean_inc(v_n_6431_);
v_N_6432_ = lean_ctor_get(v_builder_6347_, 28);
lean_inc(v_N_6432_);
v_V_6433_ = lean_ctor_get(v_builder_6347_, 29);
lean_inc(v_V_6433_);
v_z_6434_ = lean_ctor_get(v_builder_6347_, 30);
lean_inc(v_z_6434_);
v_zabbrev_6435_ = lean_ctor_get(v_builder_6347_, 31);
lean_inc(v_zabbrev_6435_);
v_v_6436_ = lean_ctor_get(v_builder_6347_, 32);
lean_inc(v_v_6436_);
v_O_6437_ = lean_ctor_get(v_builder_6347_, 33);
lean_inc(v_O_6437_);
v_X_6438_ = lean_ctor_get(v_builder_6347_, 34);
lean_inc(v_X_6438_);
v_x_6439_ = lean_ctor_get(v_builder_6347_, 35);
lean_inc(v_x_6439_);
v_Z_6440_ = lean_ctor_get(v_builder_6347_, 36);
lean_inc(v_Z_6440_);
lean_dec_ref(v_builder_6347_);
if (lean_obj_tag(v_O_6437_) == 0)
{
if (lean_obj_tag(v_X_6438_) == 0)
{
if (lean_obj_tag(v_x_6439_) == 0)
{
if (lean_obj_tag(v_Z_6440_) == 0)
{
if (lean_obj_tag(v_V_6433_) == 0)
{
if (lean_obj_tag(v_v_6436_) == 0)
{
if (lean_obj_tag(v_z_6434_) == 0)
{
if (lean_obj_tag(v_zabbrev_6435_) == 0)
{
goto v___jp_6797_;
}
else
{
lean_object* v_val_6803_; 
v_val_6803_ = lean_ctor_get(v_zabbrev_6435_, 0);
lean_inc(v_val_6803_);
v_val_6800_ = v_val_6803_;
goto v___jp_6799_;
}
}
else
{
lean_object* v_val_6804_; 
v_val_6804_ = lean_ctor_get(v_z_6434_, 0);
lean_inc(v_val_6804_);
v_val_6800_ = v_val_6804_;
goto v___jp_6799_;
}
}
else
{
lean_object* v_val_6805_; 
v_val_6805_ = lean_ctor_get(v_v_6436_, 0);
lean_inc(v_val_6805_);
v_val_6800_ = v_val_6805_;
goto v___jp_6799_;
}
}
else
{
lean_object* v_val_6806_; 
v_val_6806_ = lean_ctor_get(v_V_6433_, 0);
lean_inc(v_val_6806_);
v_val_6800_ = v_val_6806_;
goto v___jp_6799_;
}
}
else
{
lean_object* v_val_6807_; 
v_val_6807_ = lean_ctor_get(v_Z_6440_, 0);
lean_inc(v_val_6807_);
lean_dec_ref_known(v_Z_6440_, 1);
v___y_6790_ = v_val_6807_;
goto v___jp_6789_;
}
}
else
{
lean_object* v_val_6808_; 
lean_dec(v_Z_6440_);
v_val_6808_ = lean_ctor_get(v_x_6439_, 0);
lean_inc(v_val_6808_);
lean_dec_ref_known(v_x_6439_, 1);
v___y_6790_ = v_val_6808_;
goto v___jp_6789_;
}
}
else
{
lean_object* v_val_6809_; 
lean_dec(v_Z_6440_);
lean_dec(v_x_6439_);
v_val_6809_ = lean_ctor_get(v_X_6438_, 0);
lean_inc(v_val_6809_);
lean_dec_ref_known(v_X_6438_, 1);
v___y_6790_ = v_val_6809_;
goto v___jp_6789_;
}
}
else
{
lean_object* v_val_6810_; 
lean_dec(v_Z_6440_);
lean_dec(v_x_6439_);
lean_dec(v_X_6438_);
v_val_6810_ = lean_ctor_get(v_O_6437_, 0);
lean_inc(v_val_6810_);
lean_dec_ref_known(v_O_6437_, 1);
v___y_6790_ = v_val_6810_;
goto v___jp_6789_;
}
v___jp_6350_:
{
if (lean_obj_tag(v___y_6351_) == 0)
{
lean_object* v___x_6353_; 
lean_dec_ref(v___y_6352_);
v___x_6353_ = lean_box(0);
return v___x_6353_;
}
else
{
lean_object* v_val_6354_; lean_object* v___x_6356_; uint8_t v_isShared_6357_; uint8_t v_isSharedCheck_6389_; 
v_val_6354_ = lean_ctor_get(v___y_6351_, 0);
v_isSharedCheck_6389_ = !lean_is_exclusive(v___y_6351_);
if (v_isSharedCheck_6389_ == 0)
{
v___x_6356_ = v___y_6351_;
v_isShared_6357_ = v_isSharedCheck_6389_;
goto v_resetjp_6355_;
}
else
{
lean_inc(v_val_6354_);
lean_dec(v___y_6351_);
v___x_6356_ = lean_box(0);
v_isShared_6357_ = v_isSharedCheck_6389_;
goto v_resetjp_6355_;
}
v_resetjp_6355_:
{
lean_object* v_offset_6358_; lean_object* v_name_6359_; lean_object* v_abbreviation_6360_; uint8_t v_isDST_6361_; uint8_t v___x_6362_; uint8_t v___x_6363_; lean_object* v_ltt_6364_; lean_object* v___x_6365_; lean_object* v___x_6366_; lean_object* v___x_6367_; lean_object* v_wt_6368_; lean_object* v_ltt_6369_; lean_object* v_tz_6370_; lean_object* v_offset_6371_; lean_object* v_second_6372_; lean_object* v_nano_6373_; lean_object* v___f_6374_; lean_object* v___x_6375_; lean_object* v___x_6376_; lean_object* v___x_6377_; lean_object* v___x_6378_; lean_object* v___x_6379_; lean_object* v_nanos_6380_; lean_object* v___x_6381_; lean_object* v_nanos_6382_; lean_object* v___x_6383_; lean_object* v___x_6384_; lean_object* v___x_6385_; lean_object* v___x_6387_; 
v_offset_6358_ = lean_ctor_get(v___y_6352_, 0);
lean_inc(v_offset_6358_);
v_name_6359_ = lean_ctor_get(v___y_6352_, 1);
lean_inc_ref(v_name_6359_);
v_abbreviation_6360_ = lean_ctor_get(v___y_6352_, 2);
lean_inc_ref(v_abbreviation_6360_);
v_isDST_6361_ = lean_ctor_get_uint8(v___y_6352_, sizeof(void*)*3);
lean_dec_ref(v___y_6352_);
v___x_6362_ = 0;
v___x_6363_ = 1;
v_ltt_6364_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6364_, 0, v_offset_6358_);
lean_ctor_set(v_ltt_6364_, 1, v_abbreviation_6360_);
lean_ctor_set(v_ltt_6364_, 2, v_name_6359_);
lean_ctor_set_uint8(v_ltt_6364_, sizeof(void*)*3, v_isDST_6361_);
lean_ctor_set_uint8(v_ltt_6364_, sizeof(void*)*3 + 1, v___x_6362_);
lean_ctor_set_uint8(v_ltt_6364_, sizeof(void*)*3 + 2, v___x_6363_);
v___x_6365_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6366_ = lean_box(0);
v___x_6367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6367_, 0, v_ltt_6364_);
lean_ctor_set(v___x_6367_, 1, v___x_6365_);
lean_ctor_set(v___x_6367_, 2, v___x_6366_);
lean_inc(v_val_6354_);
v_wt_6368_ = l_Std_Time_PlainDateTime_toWallTime(v_val_6354_);
lean_inc_ref(v___x_6367_);
v_ltt_6369_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_6367_, v_wt_6368_);
v_tz_6370_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_6369_);
lean_dec_ref(v_ltt_6369_);
v_offset_6371_ = lean_ctor_get(v_tz_6370_, 0);
v_second_6372_ = lean_ctor_get(v_wt_6368_, 0);
lean_inc(v_second_6372_);
v_nano_6373_ = lean_ctor_get(v_wt_6368_, 1);
lean_inc(v_nano_6373_);
lean_dec_ref(v_wt_6368_);
v___f_6374_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1___boxed), 2, 1);
lean_closure_set(v___f_6374_, 0, v_val_6354_);
v___x_6375_ = lean_mk_thunk(v___f_6374_);
v___x_6376_ = lean_int_neg(v_offset_6371_);
v___x_6377_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1);
v___x_6378_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3);
v___x_6379_ = lean_int_mul(v_second_6372_, v___x_6378_);
lean_dec(v_second_6372_);
v_nanos_6380_ = lean_int_add(v___x_6379_, v_nano_6373_);
lean_dec(v_nano_6373_);
lean_dec(v___x_6379_);
v___x_6381_ = lean_int_mul(v___x_6376_, v___x_6378_);
lean_dec(v___x_6376_);
v_nanos_6382_ = lean_int_add(v___x_6381_, v___x_6377_);
lean_dec(v___x_6381_);
v___x_6383_ = lean_int_add(v_nanos_6380_, v_nanos_6382_);
lean_dec(v_nanos_6382_);
lean_dec(v_nanos_6380_);
v___x_6384_ = l_Std_Time_Duration_ofNanoseconds(v___x_6383_);
lean_dec(v___x_6383_);
v___x_6385_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6385_, 0, v___x_6375_);
lean_ctor_set(v___x_6385_, 1, v___x_6384_);
lean_ctor_set(v___x_6385_, 2, v___x_6367_);
lean_ctor_set(v___x_6385_, 3, v_tz_6370_);
if (v_isShared_6357_ == 0)
{
lean_ctor_set(v___x_6356_, 0, v___x_6385_);
v___x_6387_ = v___x_6356_;
goto v_reusejp_6386_;
}
else
{
lean_object* v_reuseFailAlloc_6388_; 
v_reuseFailAlloc_6388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6388_, 0, v___x_6385_);
v___x_6387_ = v_reuseFailAlloc_6388_;
goto v_reusejp_6386_;
}
v_reusejp_6386_:
{
return v___x_6387_;
}
}
}
}
v___jp_6390_:
{
if (lean_obj_tag(v_aw_6348_) == 0)
{
lean_object* v_a_6393_; 
lean_dec_ref(v___y_6391_);
v_a_6393_ = lean_ctor_get(v_aw_6348_, 0);
lean_inc_ref(v_a_6393_);
lean_dec_ref_known(v_aw_6348_, 1);
v___y_6351_ = v___y_6392_;
v___y_6352_ = v_a_6393_;
goto v___jp_6350_;
}
else
{
v___y_6351_ = v___y_6392_;
v___y_6352_ = v___y_6391_;
goto v___jp_6350_;
}
}
v___jp_6394_:
{
if (lean_obj_tag(v___y_6395_) == 0)
{
lean_object* v___x_6398_; 
lean_dec_ref(v___y_6397_);
v___x_6398_ = lean_box(0);
v___y_6391_ = v___y_6396_;
v___y_6392_ = v___x_6398_;
goto v___jp_6390_;
}
else
{
lean_object* v_val_6399_; lean_object* v___x_6401_; uint8_t v_isShared_6402_; uint8_t v_isSharedCheck_6407_; 
v_val_6399_ = lean_ctor_get(v___y_6395_, 0);
v_isSharedCheck_6407_ = !lean_is_exclusive(v___y_6395_);
if (v_isSharedCheck_6407_ == 0)
{
v___x_6401_ = v___y_6395_;
v_isShared_6402_ = v_isSharedCheck_6407_;
goto v_resetjp_6400_;
}
else
{
lean_inc(v_val_6399_);
lean_dec(v___y_6395_);
v___x_6401_ = lean_box(0);
v_isShared_6402_ = v_isSharedCheck_6407_;
goto v_resetjp_6400_;
}
v_resetjp_6400_:
{
lean_object* v___x_6403_; lean_object* v___x_6405_; 
v___x_6403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6403_, 0, v_val_6399_);
lean_ctor_set(v___x_6403_, 1, v___y_6397_);
if (v_isShared_6402_ == 0)
{
lean_ctor_set(v___x_6401_, 0, v___x_6403_);
v___x_6405_ = v___x_6401_;
goto v_reusejp_6404_;
}
else
{
lean_object* v_reuseFailAlloc_6406_; 
v_reuseFailAlloc_6406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6406_, 0, v___x_6403_);
v___x_6405_ = v_reuseFailAlloc_6406_;
goto v_reusejp_6404_;
}
v_reusejp_6404_:
{
v___y_6391_ = v___y_6396_;
v___y_6392_ = v___x_6405_;
goto v___jp_6390_;
}
}
}
}
v___jp_6441_:
{
if (lean_obj_tag(v_N_6432_) == 0)
{
if (lean_obj_tag(v_A_6430_) == 0)
{
lean_object* v___x_6448_; 
v___x_6448_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6448_, 0, v___y_6444_);
lean_ctor_set(v___x_6448_, 1, v___y_6443_);
lean_ctor_set(v___x_6448_, 2, v___y_6446_);
lean_ctor_set(v___x_6448_, 3, v___y_6447_);
v___y_6395_ = v___y_6442_;
v___y_6396_ = v___y_6445_;
v___y_6397_ = v___x_6448_;
goto v___jp_6394_;
}
else
{
lean_object* v_val_6449_; lean_object* v___x_6450_; lean_object* v___x_6451_; lean_object* v___x_6452_; 
lean_dec(v___y_6447_);
lean_dec(v___y_6446_);
lean_dec(v___y_6444_);
lean_dec(v___y_6443_);
v_val_6449_ = lean_ctor_get(v_A_6430_, 0);
lean_inc(v_val_6449_);
lean_dec_ref_known(v_A_6430_, 1);
v___x_6450_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2);
v___x_6451_ = lean_int_mul(v_val_6449_, v___x_6450_);
lean_dec(v_val_6449_);
v___x_6452_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_6451_);
lean_dec(v___x_6451_);
v___y_6395_ = v___y_6442_;
v___y_6396_ = v___y_6445_;
v___y_6397_ = v___x_6452_;
goto v___jp_6394_;
}
}
else
{
lean_object* v_val_6453_; lean_object* v___x_6454_; 
lean_dec(v___y_6447_);
lean_dec(v___y_6446_);
lean_dec(v___y_6444_);
lean_dec(v___y_6443_);
lean_dec(v_A_6430_);
v_val_6453_ = lean_ctor_get(v_N_6432_, 0);
lean_inc(v_val_6453_);
lean_dec_ref_known(v_N_6432_, 1);
v___x_6454_ = l_Std_Time_PlainTime_ofNanoseconds(v_val_6453_);
lean_dec(v_val_6453_);
v___y_6395_ = v___y_6442_;
v___y_6396_ = v___y_6445_;
v___y_6397_ = v___x_6454_;
goto v___jp_6394_;
}
}
v___jp_6455_:
{
if (lean_obj_tag(v_n_6431_) == 0)
{
if (lean_obj_tag(v_S_6429_) == 0)
{
lean_object* v___x_6461_; 
v___x_6461_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6442_ = v___y_6456_;
v___y_6443_ = v___y_6457_;
v___y_6444_ = v___y_6458_;
v___y_6445_ = v___y_6459_;
v___y_6446_ = v___y_6460_;
v___y_6447_ = v___x_6461_;
goto v___jp_6441_;
}
else
{
lean_object* v_val_6462_; 
v_val_6462_ = lean_ctor_get(v_S_6429_, 0);
lean_inc(v_val_6462_);
lean_dec_ref_known(v_S_6429_, 1);
v___y_6442_ = v___y_6456_;
v___y_6443_ = v___y_6457_;
v___y_6444_ = v___y_6458_;
v___y_6445_ = v___y_6459_;
v___y_6446_ = v___y_6460_;
v___y_6447_ = v_val_6462_;
goto v___jp_6441_;
}
}
else
{
lean_object* v_val_6463_; 
lean_dec(v_S_6429_);
v_val_6463_ = lean_ctor_get(v_n_6431_, 0);
lean_inc(v_val_6463_);
lean_dec_ref_known(v_n_6431_, 1);
v___y_6442_ = v___y_6456_;
v___y_6443_ = v___y_6457_;
v___y_6444_ = v___y_6458_;
v___y_6445_ = v___y_6459_;
v___y_6446_ = v___y_6460_;
v___y_6447_ = v_val_6463_;
goto v___jp_6441_;
}
}
v___jp_6464_:
{
if (lean_obj_tag(v_s_6428_) == 0)
{
lean_object* v___x_6470_; lean_object* v___x_6471_; 
v___x_6470_ = lean_unsigned_to_nat(0u);
v___x_6471_ = l_Std_Time_Second_instOfNatOrdinal(v___y_6466_, v___x_6470_);
v___y_6456_ = v___y_6465_;
v___y_6457_ = v___y_6469_;
v___y_6458_ = v___y_6467_;
v___y_6459_ = v___y_6468_;
v___y_6460_ = v___x_6471_;
goto v___jp_6455_;
}
else
{
lean_object* v_val_6472_; 
v_val_6472_ = lean_ctor_get(v_s_6428_, 0);
lean_inc(v_val_6472_);
lean_dec_ref_known(v_s_6428_, 1);
v___y_6456_ = v___y_6465_;
v___y_6457_ = v___y_6469_;
v___y_6458_ = v___y_6467_;
v___y_6459_ = v___y_6468_;
v___y_6460_ = v_val_6472_;
goto v___jp_6455_;
}
}
v___jp_6473_:
{
if (lean_obj_tag(v_m_6427_) == 0)
{
lean_object* v___x_6478_; 
v___x_6478_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10);
v___y_6465_ = v___y_6474_;
v___y_6466_ = v___y_6475_;
v___y_6467_ = v___y_6477_;
v___y_6468_ = v___y_6476_;
v___y_6469_ = v___x_6478_;
goto v___jp_6464_;
}
else
{
lean_object* v_val_6479_; 
v_val_6479_ = lean_ctor_get(v_m_6427_, 0);
lean_inc(v_val_6479_);
lean_dec_ref_known(v_m_6427_, 1);
v___y_6465_ = v___y_6474_;
v___y_6466_ = v___y_6475_;
v___y_6467_ = v___y_6477_;
v___y_6468_ = v___y_6476_;
v___y_6469_ = v_val_6479_;
goto v___jp_6464_;
}
}
v___jp_6480_:
{
if (lean_obj_tag(v___y_6484_) == 0)
{
uint8_t v___x_6486_; lean_object* v___x_6487_; lean_object* v___x_6488_; 
v___x_6486_ = 0;
v___x_6487_ = lean_box(v___x_6486_);
v___x_6488_ = lean_apply_1(v___y_6483_, v___x_6487_);
if (lean_obj_tag(v___x_6488_) == 0)
{
lean_object* v___x_6489_; 
v___x_6489_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6474_ = v___y_6481_;
v___y_6475_ = v___y_6482_;
v___y_6476_ = v___y_6485_;
v___y_6477_ = v___x_6489_;
goto v___jp_6473_;
}
else
{
lean_object* v_val_6490_; 
v_val_6490_ = lean_ctor_get(v___x_6488_, 0);
lean_inc(v_val_6490_);
lean_dec_ref_known(v___x_6488_, 1);
v___y_6474_ = v___y_6481_;
v___y_6475_ = v___y_6482_;
v___y_6476_ = v___y_6485_;
v___y_6477_ = v_val_6490_;
goto v___jp_6473_;
}
}
else
{
lean_object* v_val_6491_; 
lean_dec_ref(v___y_6483_);
v_val_6491_ = lean_ctor_get(v___y_6484_, 0);
lean_inc(v_val_6491_);
lean_dec_ref_known(v___y_6484_, 1);
v___y_6474_ = v___y_6481_;
v___y_6475_ = v___y_6482_;
v___y_6476_ = v___y_6485_;
v___y_6477_ = v_val_6491_;
goto v___jp_6473_;
}
}
v___jp_6492_:
{
if (lean_obj_tag(v___y_6495_) == 0)
{
v___y_6481_ = v___y_6493_;
v___y_6482_ = v___y_6494_;
v___y_6483_ = v___y_6496_;
v___y_6484_ = v___y_6498_;
v___y_6485_ = v___y_6497_;
goto v___jp_6480_;
}
else
{
lean_object* v_val_6499_; lean_object* v___x_6500_; 
v_val_6499_ = lean_ctor_get(v___y_6495_, 0);
lean_inc(v_val_6499_);
lean_dec_ref_known(v___y_6495_, 1);
lean_inc_ref(v___y_6496_);
v___x_6500_ = lean_apply_1(v___y_6496_, v_val_6499_);
if (lean_obj_tag(v___x_6500_) == 0)
{
v___y_6481_ = v___y_6493_;
v___y_6482_ = v___y_6494_;
v___y_6483_ = v___y_6496_;
v___y_6484_ = v___y_6498_;
v___y_6485_ = v___y_6497_;
goto v___jp_6480_;
}
else
{
lean_object* v_val_6501_; 
lean_dec(v___y_6498_);
lean_dec_ref(v___y_6496_);
v_val_6501_ = lean_ctor_get(v___x_6500_, 0);
lean_inc(v_val_6501_);
lean_dec_ref_known(v___x_6500_, 1);
v___y_6474_ = v___y_6493_;
v___y_6475_ = v___y_6494_;
v___y_6476_ = v___y_6497_;
v___y_6477_ = v_val_6501_;
goto v___jp_6473_;
}
}
}
v___jp_6502_:
{
if (lean_obj_tag(v___y_6505_) == 0)
{
v___y_6493_ = v___y_6503_;
v___y_6494_ = v___y_6504_;
v___y_6495_ = v___y_6507_;
v___y_6496_ = v___y_6506_;
v___y_6497_ = v___y_6508_;
v___y_6498_ = v___y_6509_;
goto v___jp_6492_;
}
else
{
lean_dec(v___y_6509_);
v___y_6493_ = v___y_6503_;
v___y_6494_ = v___y_6504_;
v___y_6495_ = v___y_6507_;
v___y_6496_ = v___y_6506_;
v___y_6497_ = v___y_6508_;
v___y_6498_ = v___y_6505_;
goto v___jp_6492_;
}
}
v___jp_6510_:
{
if (lean_obj_tag(v___y_6513_) == 0)
{
v___y_6503_ = v___y_6511_;
v___y_6504_ = v___y_6512_;
v___y_6505_ = v___y_6514_;
v___y_6506_ = v___y_6515_;
v___y_6507_ = v___y_6517_;
v___y_6508_ = v___y_6516_;
v___y_6509_ = v___y_6513_;
goto v___jp_6502_;
}
else
{
lean_object* v_val_6518_; lean_object* v___x_6520_; uint8_t v_isShared_6521_; uint8_t v_isSharedCheck_6527_; 
v_val_6518_ = lean_ctor_get(v___y_6513_, 0);
v_isSharedCheck_6527_ = !lean_is_exclusive(v___y_6513_);
if (v_isSharedCheck_6527_ == 0)
{
v___x_6520_ = v___y_6513_;
v_isShared_6521_ = v_isSharedCheck_6527_;
goto v_resetjp_6519_;
}
else
{
lean_inc(v_val_6518_);
lean_dec(v___y_6513_);
v___x_6520_ = lean_box(0);
v_isShared_6521_ = v_isSharedCheck_6527_;
goto v_resetjp_6519_;
}
v_resetjp_6519_:
{
lean_object* v___x_6522_; lean_object* v___x_6523_; lean_object* v___x_6525_; 
v___x_6522_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11);
v___x_6523_ = lean_int_emod(v_val_6518_, v___x_6522_);
lean_dec(v_val_6518_);
if (v_isShared_6521_ == 0)
{
lean_ctor_set(v___x_6520_, 0, v___x_6523_);
v___x_6525_ = v___x_6520_;
goto v_reusejp_6524_;
}
else
{
lean_object* v_reuseFailAlloc_6526_; 
v_reuseFailAlloc_6526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6526_, 0, v___x_6523_);
v___x_6525_ = v_reuseFailAlloc_6526_;
goto v_reusejp_6524_;
}
v_reusejp_6524_:
{
v___y_6503_ = v___y_6511_;
v___y_6504_ = v___y_6512_;
v___y_6505_ = v___y_6514_;
v___y_6506_ = v___y_6515_;
v___y_6507_ = v___y_6517_;
v___y_6508_ = v___y_6516_;
v___y_6509_ = v___x_6525_;
goto v___jp_6502_;
}
}
}
}
v___jp_6528_:
{
if (lean_obj_tag(v___y_6536_) == 0)
{
lean_dec(v___y_6537_);
v___y_6511_ = v___y_6529_;
v___y_6512_ = v___y_6531_;
v___y_6513_ = v___y_6533_;
v___y_6514_ = v___y_6532_;
v___y_6515_ = v___y_6534_;
v___y_6516_ = v___y_6535_;
v___y_6517_ = v___y_6530_;
goto v___jp_6510_;
}
else
{
lean_object* v_val_6538_; lean_object* v___x_6540_; uint8_t v_isShared_6541_; uint8_t v_isSharedCheck_6548_; 
lean_dec(v___y_6530_);
v_val_6538_ = lean_ctor_get(v___y_6536_, 0);
v_isSharedCheck_6548_ = !lean_is_exclusive(v___y_6536_);
if (v_isSharedCheck_6548_ == 0)
{
v___x_6540_ = v___y_6536_;
v_isShared_6541_ = v_isSharedCheck_6548_;
goto v_resetjp_6539_;
}
else
{
lean_inc(v_val_6538_);
lean_dec(v___y_6536_);
v___x_6540_ = lean_box(0);
v_isShared_6541_ = v_isSharedCheck_6548_;
goto v_resetjp_6539_;
}
v_resetjp_6539_:
{
uint8_t v___x_6542_; uint8_t v___x_6543_; lean_object* v___x_6544_; lean_object* v___x_6546_; 
v___x_6542_ = lean_unbox(v_val_6538_);
lean_dec(v_val_6538_);
v___x_6543_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v___y_6537_, v___x_6542_);
lean_dec(v___y_6537_);
v___x_6544_ = lean_box(v___x_6543_);
if (v_isShared_6541_ == 0)
{
lean_ctor_set(v___x_6540_, 0, v___x_6544_);
v___x_6546_ = v___x_6540_;
goto v_reusejp_6545_;
}
else
{
lean_object* v_reuseFailAlloc_6547_; 
v_reuseFailAlloc_6547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6547_, 0, v___x_6544_);
v___x_6546_ = v_reuseFailAlloc_6547_;
goto v_reusejp_6545_;
}
v_reusejp_6545_:
{
v___y_6511_ = v___y_6529_;
v___y_6512_ = v___y_6531_;
v___y_6513_ = v___y_6533_;
v___y_6514_ = v___y_6532_;
v___y_6515_ = v___y_6534_;
v___y_6516_ = v___y_6535_;
v___y_6517_ = v___x_6546_;
goto v___jp_6510_;
}
}
}
}
v___jp_6549_:
{
if (lean_obj_tag(v___y_6550_) == 0)
{
if (lean_obj_tag(v___y_6555_) == 0)
{
if (lean_obj_tag(v___y_6559_) == 0)
{
lean_object* v___x_6560_; 
v___x_6560_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6529_ = v___y_6551_;
v___y_6530_ = v___y_6550_;
v___y_6531_ = v___y_6552_;
v___y_6532_ = v___y_6554_;
v___y_6533_ = v___y_6553_;
v___y_6534_ = v___y_6556_;
v___y_6535_ = v___y_6557_;
v___y_6536_ = v___y_6558_;
v___y_6537_ = v___x_6560_;
goto v___jp_6528_;
}
else
{
lean_object* v_val_6561_; 
v_val_6561_ = lean_ctor_get(v___y_6559_, 0);
lean_inc(v_val_6561_);
lean_dec_ref_known(v___y_6559_, 1);
v___y_6529_ = v___y_6551_;
v___y_6530_ = v___y_6550_;
v___y_6531_ = v___y_6552_;
v___y_6532_ = v___y_6554_;
v___y_6533_ = v___y_6553_;
v___y_6534_ = v___y_6556_;
v___y_6535_ = v___y_6557_;
v___y_6536_ = v___y_6558_;
v___y_6537_ = v_val_6561_;
goto v___jp_6528_;
}
}
else
{
lean_object* v_val_6562_; lean_object* v___x_6564_; uint8_t v_isShared_6565_; uint8_t v_isSharedCheck_6572_; 
lean_dec(v___y_6559_);
lean_dec(v___y_6558_);
v_val_6562_ = lean_ctor_get(v___y_6555_, 0);
v_isSharedCheck_6572_ = !lean_is_exclusive(v___y_6555_);
if (v_isSharedCheck_6572_ == 0)
{
v___x_6564_ = v___y_6555_;
v_isShared_6565_ = v_isSharedCheck_6572_;
goto v_resetjp_6563_;
}
else
{
lean_inc(v_val_6562_);
lean_dec(v___y_6555_);
v___x_6564_ = lean_box(0);
v_isShared_6565_ = v_isSharedCheck_6572_;
goto v_resetjp_6563_;
}
v_resetjp_6563_:
{
uint8_t v___x_6566_; uint8_t v___x_6567_; lean_object* v___x_6568_; lean_object* v___x_6570_; 
v___x_6566_ = lean_unbox(v_val_6562_);
lean_dec(v_val_6562_);
v___x_6567_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v___x_6566_);
v___x_6568_ = lean_box(v___x_6567_);
if (v_isShared_6565_ == 0)
{
lean_ctor_set(v___x_6564_, 0, v___x_6568_);
v___x_6570_ = v___x_6564_;
goto v_reusejp_6569_;
}
else
{
lean_object* v_reuseFailAlloc_6571_; 
v_reuseFailAlloc_6571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6571_, 0, v___x_6568_);
v___x_6570_ = v_reuseFailAlloc_6571_;
goto v_reusejp_6569_;
}
v_reusejp_6569_:
{
v___y_6511_ = v___y_6551_;
v___y_6512_ = v___y_6552_;
v___y_6513_ = v___y_6553_;
v___y_6514_ = v___y_6554_;
v___y_6515_ = v___y_6556_;
v___y_6516_ = v___y_6557_;
v___y_6517_ = v___x_6570_;
goto v___jp_6510_;
}
}
}
}
else
{
lean_dec(v___y_6559_);
lean_dec(v___y_6558_);
lean_dec(v___y_6555_);
v___y_6511_ = v___y_6551_;
v___y_6512_ = v___y_6552_;
v___y_6513_ = v___y_6553_;
v___y_6514_ = v___y_6554_;
v___y_6515_ = v___y_6556_;
v___y_6516_ = v___y_6557_;
v___y_6517_ = v___y_6550_;
goto v___jp_6510_;
}
}
v___jp_6573_:
{
lean_object* v_ofHalfDay_6577_; 
lean_inc(v_K_6424_);
lean_inc(v_h_6423_);
v_ofHalfDay_6577_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__2___boxed), 3, 2);
lean_closure_set(v_ofHalfDay_6577_, 0, v_h_6423_);
lean_closure_set(v_ofHalfDay_6577_, 1, v_K_6424_);
if (lean_obj_tag(v_h_6423_) == 0)
{
if (lean_obj_tag(v_K_6424_) == 0)
{
lean_object* v___x_6578_; 
v___x_6578_ = lean_box(0);
v___y_6550_ = v_a_6420_;
v___y_6551_ = v___y_6576_;
v___y_6552_ = v___y_6574_;
v___y_6553_ = v_k_6425_;
v___y_6554_ = v_H_6426_;
v___y_6555_ = v_b_6421_;
v___y_6556_ = v_ofHalfDay_6577_;
v___y_6557_ = v___y_6575_;
v___y_6558_ = v_B_6422_;
v___y_6559_ = v___x_6578_;
goto v___jp_6549_;
}
else
{
lean_object* v_val_6579_; lean_object* v___x_6581_; uint8_t v_isShared_6582_; uint8_t v_isSharedCheck_6586_; 
v_val_6579_ = lean_ctor_get(v_K_6424_, 0);
v_isSharedCheck_6586_ = !lean_is_exclusive(v_K_6424_);
if (v_isSharedCheck_6586_ == 0)
{
v___x_6581_ = v_K_6424_;
v_isShared_6582_ = v_isSharedCheck_6586_;
goto v_resetjp_6580_;
}
else
{
lean_inc(v_val_6579_);
lean_dec(v_K_6424_);
v___x_6581_ = lean_box(0);
v_isShared_6582_ = v_isSharedCheck_6586_;
goto v_resetjp_6580_;
}
v_resetjp_6580_:
{
lean_object* v___x_6584_; 
if (v_isShared_6582_ == 0)
{
v___x_6584_ = v___x_6581_;
goto v_reusejp_6583_;
}
else
{
lean_object* v_reuseFailAlloc_6585_; 
v_reuseFailAlloc_6585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6585_, 0, v_val_6579_);
v___x_6584_ = v_reuseFailAlloc_6585_;
goto v_reusejp_6583_;
}
v_reusejp_6583_:
{
v___y_6550_ = v_a_6420_;
v___y_6551_ = v___y_6576_;
v___y_6552_ = v___y_6574_;
v___y_6553_ = v_k_6425_;
v___y_6554_ = v_H_6426_;
v___y_6555_ = v_b_6421_;
v___y_6556_ = v_ofHalfDay_6577_;
v___y_6557_ = v___y_6575_;
v___y_6558_ = v_B_6422_;
v___y_6559_ = v___x_6584_;
goto v___jp_6549_;
}
}
}
}
else
{
lean_object* v_val_6587_; lean_object* v___x_6589_; uint8_t v_isShared_6590_; uint8_t v_isSharedCheck_6596_; 
lean_dec(v_K_6424_);
v_val_6587_ = lean_ctor_get(v_h_6423_, 0);
v_isSharedCheck_6596_ = !lean_is_exclusive(v_h_6423_);
if (v_isSharedCheck_6596_ == 0)
{
v___x_6589_ = v_h_6423_;
v_isShared_6590_ = v_isSharedCheck_6596_;
goto v_resetjp_6588_;
}
else
{
lean_inc(v_val_6587_);
lean_dec(v_h_6423_);
v___x_6589_ = lean_box(0);
v_isShared_6590_ = v_isSharedCheck_6596_;
goto v_resetjp_6588_;
}
v_resetjp_6588_:
{
lean_object* v___x_6591_; lean_object* v___x_6592_; lean_object* v___x_6594_; 
v___x_6591_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_6592_ = lean_int_emod(v_val_6587_, v___x_6591_);
lean_dec(v_val_6587_);
if (v_isShared_6590_ == 0)
{
lean_ctor_set(v___x_6589_, 0, v___x_6592_);
v___x_6594_ = v___x_6589_;
goto v_reusejp_6593_;
}
else
{
lean_object* v_reuseFailAlloc_6595_; 
v_reuseFailAlloc_6595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6595_, 0, v___x_6592_);
v___x_6594_ = v_reuseFailAlloc_6595_;
goto v_reusejp_6593_;
}
v_reusejp_6593_:
{
v___y_6550_ = v_a_6420_;
v___y_6551_ = v___y_6576_;
v___y_6552_ = v___y_6574_;
v___y_6553_ = v_k_6425_;
v___y_6554_ = v_H_6426_;
v___y_6555_ = v_b_6421_;
v___y_6556_ = v_ofHalfDay_6577_;
v___y_6557_ = v___y_6575_;
v___y_6558_ = v_B_6422_;
v___y_6559_ = v___x_6594_;
goto v___jp_6549_;
}
}
}
}
v___jp_6597_:
{
if (lean_obj_tag(v___y_6599_) == 0)
{
lean_object* v___x_6603_; lean_object* v___x_6604_; 
v___x_6603_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19);
v___x_6604_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekDate(v_dateformat_6349_, v___y_6601_, v___x_6603_, v___y_6602_);
v___y_6574_ = v___y_6598_;
v___y_6575_ = v___y_6600_;
v___y_6576_ = v___x_6604_;
goto v___jp_6573_;
}
else
{
lean_object* v_val_6605_; lean_object* v___x_6606_; 
v_val_6605_ = lean_ctor_get(v___y_6599_, 0);
lean_inc(v_val_6605_);
lean_dec_ref_known(v___y_6599_, 1);
v___x_6606_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekDate(v_dateformat_6349_, v___y_6601_, v_val_6605_, v___y_6602_);
lean_dec(v_val_6605_);
v___y_6574_ = v___y_6598_;
v___y_6575_ = v___y_6600_;
v___y_6576_ = v___x_6606_;
goto v___jp_6573_;
}
}
v___jp_6607_:
{
lean_object* v_val_6613_; lean_object* v_fst_6614_; lean_object* v_snd_6615_; lean_object* v___x_6616_; lean_object* v___x_6617_; 
v_val_6613_ = l_Std_Time_ValidDate_ofOrdinal(v___y_6612_, v___y_6609_);
lean_dec(v___y_6609_);
v_fst_6614_ = lean_ctor_get(v_val_6613_, 0);
lean_inc(v_fst_6614_);
v_snd_6615_ = lean_ctor_get(v_val_6613_, 1);
lean_inc(v_snd_6615_);
lean_dec_ref(v_val_6613_);
v___x_6616_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6616_, 0, v___y_6610_);
lean_ctor_set(v___x_6616_, 1, v_fst_6614_);
lean_ctor_set(v___x_6616_, 2, v_snd_6615_);
v___x_6617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6617_, 0, v___x_6616_);
v___y_6574_ = v___y_6608_;
v___y_6575_ = v___y_6611_;
v___y_6576_ = v___x_6617_;
goto v___jp_6573_;
}
v___jp_6618_:
{
uint8_t v___x_6625_; 
v___x_6625_ = lean_int_dec_le(v___y_6623_, v___y_6620_);
if (v___x_6625_ == 0)
{
lean_object* v___x_6626_; 
lean_dec(v___y_6624_);
lean_dec(v___y_6621_);
lean_dec(v___y_6620_);
v___x_6626_ = lean_box(0);
v___y_6574_ = v___y_6619_;
v___y_6575_ = v___y_6622_;
v___y_6576_ = v___x_6626_;
goto v___jp_6573_;
}
else
{
lean_object* v___x_6627_; uint8_t v___x_6628_; 
v___x_6627_ = lean_nat_to_int(v___y_6624_);
v___x_6628_ = lean_int_dec_le(v___y_6620_, v___x_6627_);
lean_dec(v___x_6627_);
if (v___x_6628_ == 0)
{
lean_object* v___x_6629_; 
lean_dec(v___y_6621_);
lean_dec(v___y_6620_);
v___x_6629_ = lean_box(0);
v___y_6574_ = v___y_6619_;
v___y_6575_ = v___y_6622_;
v___y_6576_ = v___x_6629_;
goto v___jp_6573_;
}
else
{
lean_object* v___x_6630_; lean_object* v___x_6631_; lean_object* v___x_6632_; uint8_t v___x_6633_; 
v___x_6630_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0);
v___x_6631_ = lean_int_mod(v___y_6621_, v___x_6630_);
v___x_6632_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6633_ = lean_int_dec_eq(v___x_6631_, v___x_6632_);
lean_dec(v___x_6631_);
if (v___x_6633_ == 0)
{
v___y_6608_ = v___y_6619_;
v___y_6609_ = v___y_6620_;
v___y_6610_ = v___y_6621_;
v___y_6611_ = v___y_6622_;
v___y_6612_ = v___x_6633_;
goto v___jp_6607_;
}
else
{
lean_object* v___x_6634_; lean_object* v___x_6635_; uint8_t v___x_6636_; 
v___x_6634_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_6635_ = lean_int_mod(v___y_6621_, v___x_6634_);
v___x_6636_ = lean_int_dec_eq(v___x_6635_, v___x_6632_);
lean_dec(v___x_6635_);
if (v___x_6636_ == 0)
{
v___y_6608_ = v___y_6619_;
v___y_6609_ = v___y_6620_;
v___y_6610_ = v___y_6621_;
v___y_6611_ = v___y_6622_;
v___y_6612_ = v___x_6633_;
goto v___jp_6607_;
}
else
{
lean_object* v___x_6637_; lean_object* v___x_6638_; uint8_t v___x_6639_; 
v___x_6637_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1);
v___x_6638_ = lean_int_mod(v___y_6621_, v___x_6637_);
v___x_6639_ = lean_int_dec_eq(v___x_6638_, v___x_6632_);
lean_dec(v___x_6638_);
v___y_6608_ = v___y_6619_;
v___y_6609_ = v___y_6620_;
v___y_6610_ = v___y_6621_;
v___y_6611_ = v___y_6622_;
v___y_6612_ = v___x_6639_;
goto v___jp_6607_;
}
}
}
}
}
v___jp_6640_:
{
lean_object* v___x_6646_; 
v___x_6646_ = lean_unsigned_to_nat(365u);
v___y_6619_ = v___y_6641_;
v___y_6620_ = v___y_6642_;
v___y_6621_ = v___y_6643_;
v___y_6622_ = v___y_6644_;
v___y_6623_ = v___y_6645_;
v___y_6624_ = v___x_6646_;
goto v___jp_6618_;
}
v___jp_6647_:
{
lean_object* v___x_6653_; 
v___x_6653_ = lean_unsigned_to_nat(366u);
v___y_6619_ = v___y_6648_;
v___y_6620_ = v___y_6649_;
v___y_6621_ = v___y_6650_;
v___y_6622_ = v___y_6651_;
v___y_6623_ = v___y_6652_;
v___y_6624_ = v___x_6653_;
goto v___jp_6618_;
}
v___jp_6654_:
{
lean_object* v___x_6659_; lean_object* v___x_6660_; lean_object* v___x_6661_; lean_object* v___x_6662_; uint8_t v___x_6663_; 
v___x_6659_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6660_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0);
v___x_6661_ = lean_int_mod(v___y_6658_, v___x_6660_);
v___x_6662_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6663_ = lean_int_dec_eq(v___x_6661_, v___x_6662_);
lean_dec(v___x_6661_);
if (v___x_6663_ == 0)
{
v___y_6641_ = v___y_6655_;
v___y_6642_ = v___y_6656_;
v___y_6643_ = v___y_6658_;
v___y_6644_ = v___y_6657_;
v___y_6645_ = v___x_6659_;
goto v___jp_6640_;
}
else
{
lean_object* v___x_6664_; lean_object* v___x_6665_; uint8_t v___x_6666_; 
v___x_6664_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_6665_ = lean_int_mod(v___y_6658_, v___x_6664_);
v___x_6666_ = lean_int_dec_eq(v___x_6665_, v___x_6662_);
lean_dec(v___x_6665_);
if (v___x_6666_ == 0)
{
v___y_6648_ = v___y_6655_;
v___y_6649_ = v___y_6656_;
v___y_6650_ = v___y_6658_;
v___y_6651_ = v___y_6657_;
v___y_6652_ = v___x_6659_;
goto v___jp_6647_;
}
else
{
lean_object* v___x_6667_; lean_object* v___x_6668_; uint8_t v___x_6669_; 
v___x_6667_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1);
v___x_6668_ = lean_int_mod(v___y_6658_, v___x_6667_);
v___x_6669_ = lean_int_dec_eq(v___x_6668_, v___x_6662_);
lean_dec(v___x_6668_);
if (v___x_6669_ == 0)
{
v___y_6641_ = v___y_6655_;
v___y_6642_ = v___y_6656_;
v___y_6643_ = v___y_6658_;
v___y_6644_ = v___y_6657_;
v___y_6645_ = v___x_6659_;
goto v___jp_6640_;
}
else
{
v___y_6648_ = v___y_6655_;
v___y_6649_ = v___y_6656_;
v___y_6650_ = v___y_6658_;
v___y_6651_ = v___y_6657_;
v___y_6652_ = v___x_6659_;
goto v___jp_6647_;
}
}
}
}
v___jp_6670_:
{
lean_object* v___x_6677_; uint8_t v___x_6678_; 
v___x_6677_ = l_Std_Time_Month_Ordinal_days(v___y_6676_, v___y_6675_);
v___x_6678_ = lean_int_dec_le(v___y_6672_, v___x_6677_);
lean_dec(v___x_6677_);
if (v___x_6678_ == 0)
{
lean_object* v___x_6679_; 
lean_dec(v___y_6675_);
lean_dec(v___y_6673_);
lean_dec(v___y_6672_);
v___x_6679_ = lean_box(0);
v___y_6574_ = v___y_6671_;
v___y_6575_ = v___y_6674_;
v___y_6576_ = v___x_6679_;
goto v___jp_6573_;
}
else
{
lean_object* v___x_6680_; lean_object* v___x_6681_; 
v___x_6680_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6680_, 0, v___y_6673_);
lean_ctor_set(v___x_6680_, 1, v___y_6675_);
lean_ctor_set(v___x_6680_, 2, v___y_6672_);
v___x_6681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6681_, 0, v___x_6680_);
v___y_6574_ = v___y_6671_;
v___y_6575_ = v___y_6674_;
v___y_6576_ = v___x_6681_;
goto v___jp_6573_;
}
}
v___jp_6682_:
{
lean_object* v___x_6688_; lean_object* v___x_6689_; lean_object* v___x_6690_; uint8_t v___x_6691_; 
v___x_6688_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0);
v___x_6689_ = lean_int_mod(v___y_6687_, v___x_6688_);
v___x_6690_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6691_ = lean_int_dec_eq(v___x_6689_, v___x_6690_);
lean_dec(v___x_6689_);
if (v___x_6691_ == 0)
{
v___y_6671_ = v___y_6683_;
v___y_6672_ = v___y_6684_;
v___y_6673_ = v___y_6687_;
v___y_6674_ = v___y_6685_;
v___y_6675_ = v___y_6686_;
v___y_6676_ = v___x_6691_;
goto v___jp_6670_;
}
else
{
lean_object* v___x_6692_; lean_object* v___x_6693_; uint8_t v___x_6694_; 
v___x_6692_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_6693_ = lean_int_mod(v___y_6687_, v___x_6692_);
v___x_6694_ = lean_int_dec_eq(v___x_6693_, v___x_6690_);
lean_dec(v___x_6693_);
if (v___x_6694_ == 0)
{
v___y_6671_ = v___y_6683_;
v___y_6672_ = v___y_6684_;
v___y_6673_ = v___y_6687_;
v___y_6674_ = v___y_6685_;
v___y_6675_ = v___y_6686_;
v___y_6676_ = v___x_6691_;
goto v___jp_6670_;
}
else
{
lean_object* v___x_6695_; lean_object* v___x_6696_; uint8_t v___x_6697_; 
v___x_6695_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1);
v___x_6696_ = lean_int_mod(v___y_6687_, v___x_6695_);
v___x_6697_ = lean_int_dec_eq(v___x_6696_, v___x_6690_);
lean_dec(v___x_6696_);
v___y_6671_ = v___y_6683_;
v___y_6672_ = v___y_6684_;
v___y_6673_ = v___y_6687_;
v___y_6674_ = v___y_6685_;
v___y_6675_ = v___y_6686_;
v___y_6676_ = v___x_6697_;
goto v___jp_6670_;
}
}
}
v___jp_6698_:
{
lean_object* v___x_6703_; 
v___x_6703_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6683_ = v___y_6699_;
v___y_6684_ = v___y_6700_;
v___y_6685_ = v___y_6701_;
v___y_6686_ = v___y_6702_;
v___y_6687_ = v___x_6703_;
goto v___jp_6682_;
}
v___jp_6704_:
{
if (lean_obj_tag(v___y_6708_) == 0)
{
if (lean_obj_tag(v_Y_6411_) == 1)
{
lean_object* v_val_6710_; lean_object* v___x_6711_; 
v_val_6710_ = lean_ctor_get(v_Y_6411_, 0);
lean_inc(v_val_6710_);
lean_dec_ref_known(v_Y_6411_, 1);
v___x_6711_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay(v_dateformat_6349_, v_val_6710_, v___y_6707_, v___y_6709_);
v___y_6574_ = v___y_6705_;
v___y_6575_ = v___y_6706_;
v___y_6576_ = v___x_6711_;
goto v___jp_6573_;
}
else
{
lean_dec(v_Y_6411_);
v___y_6699_ = v___y_6705_;
v___y_6700_ = v___y_6709_;
v___y_6701_ = v___y_6706_;
v___y_6702_ = v___y_6707_;
goto v___jp_6698_;
}
}
else
{
lean_dec(v_Y_6411_);
if (lean_obj_tag(v___y_6708_) == 0)
{
v___y_6699_ = v___y_6705_;
v___y_6700_ = v___y_6709_;
v___y_6701_ = v___y_6706_;
v___y_6702_ = v___y_6707_;
goto v___jp_6698_;
}
else
{
lean_object* v_val_6712_; 
v_val_6712_ = lean_ctor_get(v___y_6708_, 0);
lean_inc(v_val_6712_);
lean_dec_ref_known(v___y_6708_, 1);
v___y_6683_ = v___y_6705_;
v___y_6684_ = v___y_6709_;
v___y_6685_ = v___y_6706_;
v___y_6686_ = v___y_6707_;
v___y_6687_ = v_val_6712_;
goto v___jp_6682_;
}
}
}
v___jp_6713_:
{
if (lean_obj_tag(v_d_6415_) == 0)
{
lean_object* v___x_6718_; 
v___x_6718_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__16);
v___y_6705_ = v___y_6714_;
v___y_6706_ = v___y_6715_;
v___y_6707_ = v___y_6717_;
v___y_6708_ = v___y_6716_;
v___y_6709_ = v___x_6718_;
goto v___jp_6704_;
}
else
{
lean_object* v_val_6719_; 
v_val_6719_ = lean_ctor_get(v_d_6415_, 0);
lean_inc(v_val_6719_);
lean_dec_ref_known(v_d_6415_, 1);
v___y_6705_ = v___y_6714_;
v___y_6706_ = v___y_6715_;
v___y_6707_ = v___y_6717_;
v___y_6708_ = v___y_6716_;
v___y_6709_ = v_val_6719_;
goto v___jp_6704_;
}
}
v___jp_6720_:
{
lean_object* v___x_6724_; 
v___x_6724_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__8);
v___y_6714_ = v___y_6721_;
v___y_6715_ = v___y_6722_;
v___y_6716_ = v___y_6723_;
v___y_6717_ = v___x_6724_;
goto v___jp_6713_;
}
v___jp_6725_:
{
uint8_t v___x_6729_; 
v___x_6729_ = 1;
v___y_6714_ = v___x_6729_;
v___y_6715_ = v___y_6726_;
v___y_6716_ = v___y_6727_;
v___y_6717_ = v_val_6728_;
goto v___jp_6713_;
}
v___jp_6730_:
{
if (lean_obj_tag(v_M_6413_) == 0)
{
if (lean_obj_tag(v_L_6414_) == 0)
{
uint8_t v___x_6734_; 
v___x_6734_ = 1;
if (lean_obj_tag(v_d_6415_) == 0)
{
if (lean_obj_tag(v_D_6412_) == 1)
{
lean_object* v_val_6735_; 
lean_dec(v_c_6419_);
lean_dec(v_e_6418_);
lean_dec(v_E_6417_);
lean_dec(v_w_6416_);
lean_dec(v_Y_6411_);
v_val_6735_ = lean_ctor_get(v_D_6412_, 0);
lean_inc(v_val_6735_);
lean_dec_ref_known(v_D_6412_, 1);
if (lean_obj_tag(v___y_6733_) == 0)
{
lean_object* v_snd_6736_; lean_object* v___x_6737_; 
v_snd_6736_ = lean_ctor_get(v_val_6735_, 1);
lean_inc(v_snd_6736_);
lean_dec(v_val_6735_);
v___x_6737_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6655_ = v___x_6734_;
v___y_6656_ = v_snd_6736_;
v___y_6657_ = v___y_6731_;
v___y_6658_ = v___x_6737_;
goto v___jp_6654_;
}
else
{
lean_object* v_snd_6738_; lean_object* v_val_6739_; 
v_snd_6738_ = lean_ctor_get(v_val_6735_, 1);
lean_inc(v_snd_6738_);
lean_dec(v_val_6735_);
v_val_6739_ = lean_ctor_get(v___y_6733_, 0);
lean_inc(v_val_6739_);
lean_dec_ref_known(v___y_6733_, 1);
v___y_6655_ = v___x_6734_;
v___y_6656_ = v_snd_6738_;
v___y_6657_ = v___y_6731_;
v___y_6658_ = v_val_6739_;
goto v___jp_6654_;
}
}
else
{
lean_dec(v_D_6412_);
if (lean_obj_tag(v___y_6733_) == 0)
{
if (lean_obj_tag(v_Y_6411_) == 1)
{
if (lean_obj_tag(v_e_6418_) == 0)
{
if (lean_obj_tag(v_c_6419_) == 0)
{
if (lean_obj_tag(v_E_6417_) == 0)
{
lean_object* v_val_6740_; uint8_t v_firstDayOfWeek_6741_; 
v_val_6740_ = lean_ctor_get(v_Y_6411_, 0);
lean_inc(v_val_6740_);
lean_dec_ref_known(v_Y_6411_, 1);
v_firstDayOfWeek_6741_ = lean_ctor_get_uint8(v_dateformat_6349_, sizeof(void*)*2);
v___y_6598_ = v___x_6734_;
v___y_6599_ = v_w_6416_;
v___y_6600_ = v___y_6731_;
v___y_6601_ = v_val_6740_;
v___y_6602_ = v_firstDayOfWeek_6741_;
goto v___jp_6597_;
}
else
{
lean_object* v_val_6742_; lean_object* v_val_6743_; uint8_t v___x_6744_; 
v_val_6742_ = lean_ctor_get(v_Y_6411_, 0);
lean_inc(v_val_6742_);
lean_dec_ref_known(v_Y_6411_, 1);
v_val_6743_ = lean_ctor_get(v_E_6417_, 0);
lean_inc(v_val_6743_);
lean_dec_ref_known(v_E_6417_, 1);
v___x_6744_ = lean_unbox(v_val_6743_);
lean_dec(v_val_6743_);
v___y_6598_ = v___x_6734_;
v___y_6599_ = v_w_6416_;
v___y_6600_ = v___y_6731_;
v___y_6601_ = v_val_6742_;
v___y_6602_ = v___x_6744_;
goto v___jp_6597_;
}
}
else
{
lean_object* v_val_6745_; lean_object* v_val_6746_; uint8_t v___x_6747_; 
lean_dec(v_E_6417_);
v_val_6745_ = lean_ctor_get(v_Y_6411_, 0);
lean_inc(v_val_6745_);
lean_dec_ref_known(v_Y_6411_, 1);
v_val_6746_ = lean_ctor_get(v_c_6419_, 0);
lean_inc(v_val_6746_);
lean_dec_ref_known(v_c_6419_, 1);
v___x_6747_ = lean_unbox(v_val_6746_);
lean_dec(v_val_6746_);
v___y_6598_ = v___x_6734_;
v___y_6599_ = v_w_6416_;
v___y_6600_ = v___y_6731_;
v___y_6601_ = v_val_6745_;
v___y_6602_ = v___x_6747_;
goto v___jp_6597_;
}
}
else
{
lean_object* v_val_6748_; lean_object* v_val_6749_; uint8_t v___x_6750_; 
lean_dec(v_c_6419_);
lean_dec(v_E_6417_);
v_val_6748_ = lean_ctor_get(v_Y_6411_, 0);
lean_inc(v_val_6748_);
lean_dec_ref_known(v_Y_6411_, 1);
v_val_6749_ = lean_ctor_get(v_e_6418_, 0);
lean_inc(v_val_6749_);
lean_dec_ref_known(v_e_6418_, 1);
v___x_6750_ = lean_unbox(v_val_6749_);
lean_dec(v_val_6749_);
v___y_6598_ = v___x_6734_;
v___y_6599_ = v_w_6416_;
v___y_6600_ = v___y_6731_;
v___y_6601_ = v_val_6748_;
v___y_6602_ = v___x_6750_;
goto v___jp_6597_;
}
}
else
{
lean_object* v___x_6751_; 
lean_dec(v_c_6419_);
lean_dec(v_e_6418_);
lean_dec(v_E_6417_);
lean_dec(v_w_6416_);
v___x_6751_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(v___y_6733_, v_Y_6411_);
lean_dec(v_Y_6411_);
v___y_6574_ = v___x_6734_;
v___y_6575_ = v___y_6731_;
v___y_6576_ = v___x_6751_;
goto v___jp_6573_;
}
}
else
{
lean_object* v___x_6752_; 
lean_dec(v_c_6419_);
lean_dec(v_e_6418_);
lean_dec(v_E_6417_);
lean_dec(v_w_6416_);
v___x_6752_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(v___y_6733_, v_Y_6411_);
lean_dec(v_Y_6411_);
v___y_6574_ = v___x_6734_;
v___y_6575_ = v___y_6731_;
v___y_6576_ = v___x_6752_;
goto v___jp_6573_;
}
}
}
else
{
lean_dec(v_c_6419_);
lean_dec(v_e_6418_);
lean_dec(v_E_6417_);
lean_dec(v_w_6416_);
lean_dec(v_D_6412_);
v___y_6721_ = v___x_6734_;
v___y_6722_ = v___y_6731_;
v___y_6723_ = v___y_6733_;
goto v___jp_6720_;
}
}
else
{
lean_object* v_val_6753_; 
lean_dec(v_c_6419_);
lean_dec(v_e_6418_);
lean_dec(v_E_6417_);
lean_dec(v_w_6416_);
lean_dec(v_D_6412_);
v_val_6753_ = lean_ctor_get(v_L_6414_, 0);
lean_inc(v_val_6753_);
lean_dec_ref_known(v_L_6414_, 1);
v___y_6726_ = v___y_6731_;
v___y_6727_ = v___y_6733_;
v_val_6728_ = v_val_6753_;
goto v___jp_6725_;
}
}
else
{
lean_object* v_val_6754_; 
lean_dec(v_c_6419_);
lean_dec(v_e_6418_);
lean_dec(v_E_6417_);
lean_dec(v_w_6416_);
lean_dec(v_L_6414_);
lean_dec(v_D_6412_);
v_val_6754_ = lean_ctor_get(v_M_6413_, 0);
lean_inc(v_val_6754_);
lean_dec_ref_known(v_M_6413_, 1);
v___y_6726_ = v___y_6731_;
v___y_6727_ = v___y_6733_;
v_val_6728_ = v_val_6754_;
goto v___jp_6725_;
}
}
v___jp_6755_:
{
uint8_t v___x_6759_; lean_object* v_tz_6760_; 
v___x_6759_ = 0;
v_tz_6760_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_tz_6760_, 0, v___y_6756_);
lean_ctor_set(v_tz_6760_, 1, v___y_6757_);
lean_ctor_set(v_tz_6760_, 2, v___y_6758_);
lean_ctor_set_uint8(v_tz_6760_, sizeof(void*)*3, v___x_6759_);
if (lean_obj_tag(v_u_6410_) == 0)
{
if (lean_obj_tag(v_y_6409_) == 0)
{
lean_dec(v_G_6408_);
v___y_6731_ = v_tz_6760_;
v___y_6732_ = v___x_6759_;
v___y_6733_ = v_y_6409_;
goto v___jp_6730_;
}
else
{
if (lean_obj_tag(v_G_6408_) == 0)
{
lean_object* v_val_6761_; lean_object* v___x_6763_; uint8_t v_isShared_6764_; uint8_t v_isSharedCheck_6770_; 
v_val_6761_ = lean_ctor_get(v_y_6409_, 0);
v_isSharedCheck_6770_ = !lean_is_exclusive(v_y_6409_);
if (v_isSharedCheck_6770_ == 0)
{
v___x_6763_ = v_y_6409_;
v_isShared_6764_ = v_isSharedCheck_6770_;
goto v_resetjp_6762_;
}
else
{
lean_inc(v_val_6761_);
lean_dec(v_y_6409_);
v___x_6763_ = lean_box(0);
v_isShared_6764_ = v_isSharedCheck_6770_;
goto v_resetjp_6762_;
}
v_resetjp_6762_:
{
uint8_t v___x_6765_; lean_object* v___x_6766_; lean_object* v___x_6768_; 
v___x_6765_ = 1;
v___x_6766_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_val_6761_, v___x_6765_);
lean_dec(v_val_6761_);
if (v_isShared_6764_ == 0)
{
lean_ctor_set(v___x_6763_, 0, v___x_6766_);
v___x_6768_ = v___x_6763_;
goto v_reusejp_6767_;
}
else
{
lean_object* v_reuseFailAlloc_6769_; 
v_reuseFailAlloc_6769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6769_, 0, v___x_6766_);
v___x_6768_ = v_reuseFailAlloc_6769_;
goto v_reusejp_6767_;
}
v_reusejp_6767_:
{
v___y_6731_ = v_tz_6760_;
v___y_6732_ = v___x_6759_;
v___y_6733_ = v___x_6768_;
goto v___jp_6730_;
}
}
}
else
{
lean_object* v_val_6771_; lean_object* v_val_6772_; lean_object* v___x_6774_; uint8_t v_isShared_6775_; uint8_t v_isSharedCheck_6781_; 
v_val_6771_ = lean_ctor_get(v_y_6409_, 0);
lean_inc(v_val_6771_);
lean_dec_ref_known(v_y_6409_, 1);
v_val_6772_ = lean_ctor_get(v_G_6408_, 0);
v_isSharedCheck_6781_ = !lean_is_exclusive(v_G_6408_);
if (v_isSharedCheck_6781_ == 0)
{
v___x_6774_ = v_G_6408_;
v_isShared_6775_ = v_isSharedCheck_6781_;
goto v_resetjp_6773_;
}
else
{
lean_inc(v_val_6772_);
lean_dec(v_G_6408_);
v___x_6774_ = lean_box(0);
v_isShared_6775_ = v_isSharedCheck_6781_;
goto v_resetjp_6773_;
}
v_resetjp_6773_:
{
uint8_t v___x_6776_; lean_object* v___x_6777_; lean_object* v___x_6779_; 
v___x_6776_ = lean_unbox(v_val_6772_);
lean_dec(v_val_6772_);
v___x_6777_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_val_6771_, v___x_6776_);
lean_dec(v_val_6771_);
if (v_isShared_6775_ == 0)
{
lean_ctor_set(v___x_6774_, 0, v___x_6777_);
v___x_6779_ = v___x_6774_;
goto v_reusejp_6778_;
}
else
{
lean_object* v_reuseFailAlloc_6780_; 
v_reuseFailAlloc_6780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6780_, 0, v___x_6777_);
v___x_6779_ = v_reuseFailAlloc_6780_;
goto v_reusejp_6778_;
}
v_reusejp_6778_:
{
v___y_6731_ = v_tz_6760_;
v___y_6732_ = v___x_6759_;
v___y_6733_ = v___x_6779_;
goto v___jp_6730_;
}
}
}
}
}
else
{
lean_dec(v_y_6409_);
lean_dec(v_G_6408_);
v___y_6731_ = v_tz_6760_;
v___y_6732_ = v___x_6759_;
v___y_6733_ = v_u_6410_;
goto v___jp_6730_;
}
}
v___jp_6782_:
{
if (lean_obj_tag(v_zabbrev_6435_) == 0)
{
lean_object* v___x_6786_; lean_object* v___x_6787_; 
v___x_6786_ = lean_box(0);
v___x_6787_ = lean_apply_1(v___y_6783_, v___x_6786_);
v___y_6756_ = v___y_6784_;
v___y_6757_ = v___y_6785_;
v___y_6758_ = v___x_6787_;
goto v___jp_6755_;
}
else
{
lean_object* v_val_6788_; 
lean_dec_ref(v___y_6783_);
v_val_6788_ = lean_ctor_get(v_zabbrev_6435_, 0);
lean_inc(v_val_6788_);
lean_dec_ref_known(v_zabbrev_6435_, 1);
v___y_6756_ = v___y_6784_;
v___y_6757_ = v___y_6785_;
v___y_6758_ = v_val_6788_;
goto v___jp_6755_;
}
}
v___jp_6789_:
{
lean_object* v___f_6791_; 
lean_inc(v___y_6790_);
v___f_6791_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__3), 2, 1);
lean_closure_set(v___f_6791_, 0, v___y_6790_);
if (lean_obj_tag(v_V_6433_) == 0)
{
if (lean_obj_tag(v_v_6436_) == 0)
{
if (lean_obj_tag(v_z_6434_) == 0)
{
lean_object* v___x_6792_; lean_object* v___x_6793_; 
v___x_6792_ = lean_box(0);
lean_inc(v___y_6790_);
v___x_6793_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__3(v___y_6790_, v___x_6792_);
v___y_6783_ = v___f_6791_;
v___y_6784_ = v___y_6790_;
v___y_6785_ = v___x_6793_;
goto v___jp_6782_;
}
else
{
lean_object* v_val_6794_; 
v_val_6794_ = lean_ctor_get(v_z_6434_, 0);
lean_inc(v_val_6794_);
lean_dec_ref_known(v_z_6434_, 1);
v___y_6783_ = v___f_6791_;
v___y_6784_ = v___y_6790_;
v___y_6785_ = v_val_6794_;
goto v___jp_6782_;
}
}
else
{
lean_object* v_val_6795_; 
lean_dec(v_z_6434_);
v_val_6795_ = lean_ctor_get(v_v_6436_, 0);
lean_inc(v_val_6795_);
lean_dec_ref_known(v_v_6436_, 1);
v___y_6783_ = v___f_6791_;
v___y_6784_ = v___y_6790_;
v___y_6785_ = v_val_6795_;
goto v___jp_6782_;
}
}
else
{
lean_object* v_val_6796_; 
lean_dec(v_v_6436_);
lean_dec(v_z_6434_);
v_val_6796_ = lean_ctor_get(v_V_6433_, 0);
lean_inc(v_val_6796_);
lean_dec_ref_known(v_V_6433_, 1);
v___y_6783_ = v___f_6791_;
v___y_6784_ = v___y_6790_;
v___y_6785_ = v_val_6796_;
goto v___jp_6782_;
}
}
v___jp_6797_:
{
lean_object* v___x_6798_; 
v___x_6798_ = l_Std_Time_TimeZone_Offset_zero;
v___y_6790_ = v___x_6798_;
goto v___jp_6789_;
}
v___jp_6799_:
{
lean_object* v___x_6801_; 
v___x_6801_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_offsetOfZoneId_x3f(v_val_6800_);
if (lean_obj_tag(v___x_6801_) == 0)
{
goto v___jp_6797_;
}
else
{
lean_object* v_val_6802_; 
v_val_6802_ = lean_ctor_get(v___x_6801_, 0);
lean_inc(v_val_6802_);
lean_dec_ref_known(v___x_6801_, 1);
v___y_6790_ = v_val_6802_;
goto v___jp_6789_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___boxed(lean_object* v_builder_6811_, lean_object* v_aw_6812_, lean_object* v_dateformat_6813_){
_start:
{
lean_object* v_res_6814_; 
v_res_6814_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(v_builder_6811_, v_aw_6812_, v_dateformat_6813_);
lean_dec_ref(v_dateformat_6813_);
return v_res_6814_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(lean_object* v_date_6815_, lean_object* v_config_6816_, lean_object* v_mod_6817_, lean_object* v_rest_6818_, lean_object* v_a_6819_){
_start:
{
if (lean_obj_tag(v_mod_6817_) == 0)
{
lean_object* v_val_6820_; lean_object* v___x_6821_; 
lean_dec(v_rest_6818_);
lean_dec_ref(v_config_6816_);
v_val_6820_ = lean_ctor_get(v_mod_6817_, 0);
lean_inc_ref(v_val_6820_);
lean_dec_ref_known(v_mod_6817_, 1);
v___x_6821_ = l_Std_Internal_Parsec_String_pstring(v_val_6820_, v_a_6819_);
if (lean_obj_tag(v___x_6821_) == 0)
{
lean_object* v_pos_6822_; lean_object* v___x_6824_; uint8_t v_isShared_6825_; uint8_t v_isSharedCheck_6829_; 
v_pos_6822_ = lean_ctor_get(v___x_6821_, 0);
v_isSharedCheck_6829_ = !lean_is_exclusive(v___x_6821_);
if (v_isSharedCheck_6829_ == 0)
{
lean_object* v_unused_6830_; 
v_unused_6830_ = lean_ctor_get(v___x_6821_, 1);
lean_dec(v_unused_6830_);
v___x_6824_ = v___x_6821_;
v_isShared_6825_ = v_isSharedCheck_6829_;
goto v_resetjp_6823_;
}
else
{
lean_inc(v_pos_6822_);
lean_dec(v___x_6821_);
v___x_6824_ = lean_box(0);
v_isShared_6825_ = v_isSharedCheck_6829_;
goto v_resetjp_6823_;
}
v_resetjp_6823_:
{
lean_object* v___x_6827_; 
if (v_isShared_6825_ == 0)
{
lean_ctor_set(v___x_6824_, 1, v_date_6815_);
v___x_6827_ = v___x_6824_;
goto v_reusejp_6826_;
}
else
{
lean_object* v_reuseFailAlloc_6828_; 
v_reuseFailAlloc_6828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6828_, 0, v_pos_6822_);
lean_ctor_set(v_reuseFailAlloc_6828_, 1, v_date_6815_);
v___x_6827_ = v_reuseFailAlloc_6828_;
goto v_reusejp_6826_;
}
v_reusejp_6826_:
{
return v___x_6827_;
}
}
}
else
{
lean_object* v_pos_6831_; lean_object* v_err_6832_; lean_object* v___x_6834_; uint8_t v_isShared_6835_; uint8_t v_isSharedCheck_6839_; 
lean_dec_ref(v_date_6815_);
v_pos_6831_ = lean_ctor_get(v___x_6821_, 0);
v_err_6832_ = lean_ctor_get(v___x_6821_, 1);
v_isSharedCheck_6839_ = !lean_is_exclusive(v___x_6821_);
if (v_isSharedCheck_6839_ == 0)
{
v___x_6834_ = v___x_6821_;
v_isShared_6835_ = v_isSharedCheck_6839_;
goto v_resetjp_6833_;
}
else
{
lean_inc(v_err_6832_);
lean_inc(v_pos_6831_);
lean_dec(v___x_6821_);
v___x_6834_ = lean_box(0);
v_isShared_6835_ = v_isSharedCheck_6839_;
goto v_resetjp_6833_;
}
v_resetjp_6833_:
{
lean_object* v___x_6837_; 
if (v_isShared_6835_ == 0)
{
v___x_6837_ = v___x_6834_;
goto v_reusejp_6836_;
}
else
{
lean_object* v_reuseFailAlloc_6838_; 
v_reuseFailAlloc_6838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6838_, 0, v_pos_6831_);
lean_ctor_set(v_reuseFailAlloc_6838_, 1, v_err_6832_);
v___x_6837_ = v_reuseFailAlloc_6838_;
goto v_reusejp_6836_;
}
v_reusejp_6836_:
{
return v___x_6837_;
}
}
}
}
else
{
lean_object* v_modifier_6840_; lean_object* v___x_6841_; lean_object* v___x_6842_; 
v_modifier_6840_ = lean_ctor_get(v_mod_6817_, 0);
lean_inc_ref_n(v_modifier_6840_, 2);
lean_dec_ref_known(v_mod_6817_, 1);
v___x_6841_ = l___private_Std_Time_Format_Basic_0__Std_Time_reservedDigits(v_rest_6818_);
v___x_6842_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_6816_, v___x_6841_, v_modifier_6840_, v_a_6819_);
if (lean_obj_tag(v___x_6842_) == 0)
{
lean_object* v_pos_6843_; lean_object* v_res_6844_; lean_object* v___x_6846_; uint8_t v_isShared_6847_; uint8_t v_isSharedCheck_6852_; 
v_pos_6843_ = lean_ctor_get(v___x_6842_, 0);
v_res_6844_ = lean_ctor_get(v___x_6842_, 1);
v_isSharedCheck_6852_ = !lean_is_exclusive(v___x_6842_);
if (v_isSharedCheck_6852_ == 0)
{
v___x_6846_ = v___x_6842_;
v_isShared_6847_ = v_isSharedCheck_6852_;
goto v_resetjp_6845_;
}
else
{
lean_inc(v_res_6844_);
lean_inc(v_pos_6843_);
lean_dec(v___x_6842_);
v___x_6846_ = lean_box(0);
v_isShared_6847_ = v_isSharedCheck_6852_;
goto v_resetjp_6845_;
}
v_resetjp_6845_:
{
lean_object* v___x_6848_; lean_object* v___x_6850_; 
v___x_6848_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(v_date_6815_, v_modifier_6840_, v_res_6844_);
if (v_isShared_6847_ == 0)
{
lean_ctor_set(v___x_6846_, 1, v___x_6848_);
v___x_6850_ = v___x_6846_;
goto v_reusejp_6849_;
}
else
{
lean_object* v_reuseFailAlloc_6851_; 
v_reuseFailAlloc_6851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6851_, 0, v_pos_6843_);
lean_ctor_set(v_reuseFailAlloc_6851_, 1, v___x_6848_);
v___x_6850_ = v_reuseFailAlloc_6851_;
goto v_reusejp_6849_;
}
v_reusejp_6849_:
{
return v___x_6850_;
}
}
}
else
{
lean_object* v_pos_6853_; lean_object* v_err_6854_; lean_object* v___x_6856_; uint8_t v_isShared_6857_; uint8_t v_isSharedCheck_6861_; 
lean_dec_ref(v_modifier_6840_);
lean_dec_ref(v_date_6815_);
v_pos_6853_ = lean_ctor_get(v___x_6842_, 0);
v_err_6854_ = lean_ctor_get(v___x_6842_, 1);
v_isSharedCheck_6861_ = !lean_is_exclusive(v___x_6842_);
if (v_isSharedCheck_6861_ == 0)
{
v___x_6856_ = v___x_6842_;
v_isShared_6857_ = v_isSharedCheck_6861_;
goto v_resetjp_6855_;
}
else
{
lean_inc(v_err_6854_);
lean_inc(v_pos_6853_);
lean_dec(v___x_6842_);
v___x_6856_ = lean_box(0);
v_isShared_6857_ = v_isSharedCheck_6861_;
goto v_resetjp_6855_;
}
v_resetjp_6855_:
{
lean_object* v___x_6859_; 
if (v_isShared_6857_ == 0)
{
v___x_6859_ = v___x_6856_;
goto v_reusejp_6858_;
}
else
{
lean_object* v_reuseFailAlloc_6860_; 
v_reuseFailAlloc_6860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6860_, 0, v_pos_6853_);
lean_ctor_set(v_reuseFailAlloc_6860_, 1, v_err_6854_);
v___x_6859_ = v_reuseFailAlloc_6860_;
goto v_reusejp_6858_;
}
v_reusejp_6858_:
{
return v___x_6859_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___redArg(lean_object* v_input_6862_, lean_object* v_config_6863_){
_start:
{
lean_object* v___x_6864_; lean_object* v___x_6865_; 
v___x_6864_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6865_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6864_, v_input_6862_);
if (lean_obj_tag(v___x_6865_) == 0)
{
lean_object* v_a_6866_; lean_object* v___x_6868_; uint8_t v_isShared_6869_; uint8_t v_isSharedCheck_6873_; 
lean_dec_ref(v_config_6863_);
v_a_6866_ = lean_ctor_get(v___x_6865_, 0);
v_isSharedCheck_6873_ = !lean_is_exclusive(v___x_6865_);
if (v_isSharedCheck_6873_ == 0)
{
v___x_6868_ = v___x_6865_;
v_isShared_6869_ = v_isSharedCheck_6873_;
goto v_resetjp_6867_;
}
else
{
lean_inc(v_a_6866_);
lean_dec(v___x_6865_);
v___x_6868_ = lean_box(0);
v_isShared_6869_ = v_isSharedCheck_6873_;
goto v_resetjp_6867_;
}
v_resetjp_6867_:
{
lean_object* v___x_6871_; 
if (v_isShared_6869_ == 0)
{
v___x_6871_ = v___x_6868_;
goto v_reusejp_6870_;
}
else
{
lean_object* v_reuseFailAlloc_6872_; 
v_reuseFailAlloc_6872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6872_, 0, v_a_6866_);
v___x_6871_ = v_reuseFailAlloc_6872_;
goto v_reusejp_6870_;
}
v_reusejp_6870_:
{
return v___x_6871_;
}
}
}
else
{
lean_object* v_a_6874_; lean_object* v___x_6876_; uint8_t v_isShared_6877_; uint8_t v_isSharedCheck_6882_; 
v_a_6874_ = lean_ctor_get(v___x_6865_, 0);
v_isSharedCheck_6882_ = !lean_is_exclusive(v___x_6865_);
if (v_isSharedCheck_6882_ == 0)
{
v___x_6876_ = v___x_6865_;
v_isShared_6877_ = v_isSharedCheck_6882_;
goto v_resetjp_6875_;
}
else
{
lean_inc(v_a_6874_);
lean_dec(v___x_6865_);
v___x_6876_ = lean_box(0);
v_isShared_6877_ = v_isSharedCheck_6882_;
goto v_resetjp_6875_;
}
v_resetjp_6875_:
{
lean_object* v___x_6878_; lean_object* v___x_6880_; 
v___x_6878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6878_, 0, v_config_6863_);
lean_ctor_set(v___x_6878_, 1, v_a_6874_);
if (v_isShared_6877_ == 0)
{
lean_ctor_set(v___x_6876_, 0, v___x_6878_);
v___x_6880_ = v___x_6876_;
goto v_reusejp_6879_;
}
else
{
lean_object* v_reuseFailAlloc_6881_; 
v_reuseFailAlloc_6881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6881_, 0, v___x_6878_);
v___x_6880_ = v_reuseFailAlloc_6881_;
goto v_reusejp_6879_;
}
v_reusejp_6879_:
{
return v___x_6880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec(lean_object* v_tz_6883_, lean_object* v_input_6884_, lean_object* v_config_6885_){
_start:
{
lean_object* v___x_6886_; 
v___x_6886_ = l_Std_Time_GenericFormat_spec___redArg(v_input_6884_, v_config_6885_);
return v___x_6886_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___boxed(lean_object* v_tz_6887_, lean_object* v_input_6888_, lean_object* v_config_6889_){
_start:
{
lean_object* v_res_6890_; 
v_res_6890_ = l_Std_Time_GenericFormat_spec(v_tz_6887_, v_input_6888_, v_config_6889_);
lean_dec(v_tz_6887_);
return v_res_6890_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(lean_object* v_msg_6891_){
_start:
{
lean_object* v___x_6892_; lean_object* v___x_6893_; 
v___x_6892_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0);
v___x_6893_ = lean_panic_fn_borrowed(v___x_6892_, v_msg_6891_);
return v___x_6893_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(lean_object* v_tz_6894_, lean_object* v_msg_6895_){
_start:
{
lean_object* v___x_6896_; 
v___x_6896_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(v_msg_6895_);
return v___x_6896_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___boxed(lean_object* v_tz_6897_, lean_object* v_msg_6898_){
_start:
{
lean_object* v_res_6899_; 
v_res_6899_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(v_tz_6897_, v_msg_6898_);
lean_dec(v_tz_6897_);
return v_res_6899_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21(lean_object* v_tz_6902_, lean_object* v_input_6903_, lean_object* v_config_6904_){
_start:
{
lean_object* v___x_6905_; lean_object* v___x_6906_; 
v___x_6905_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6906_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6905_, v_input_6903_);
if (lean_obj_tag(v___x_6906_) == 0)
{
lean_object* v_a_6907_; lean_object* v___x_6908_; lean_object* v___x_6909_; lean_object* v___x_6910_; lean_object* v___x_6911_; lean_object* v___x_6912_; lean_object* v___x_6913_; 
lean_dec_ref(v_config_6904_);
v_a_6907_ = lean_ctor_get(v___x_6906_, 0);
lean_inc(v_a_6907_);
lean_dec_ref_known(v___x_6906_, 1);
v___x_6908_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_6909_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__1));
v___x_6910_ = lean_unsigned_to_nat(935u);
v___x_6911_ = lean_unsigned_to_nat(18u);
v___x_6912_ = l_mkPanicMessageWithDecl(v___x_6908_, v___x_6909_, v___x_6910_, v___x_6911_, v_a_6907_);
lean_dec(v_a_6907_);
v___x_6913_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(v___x_6912_);
return v___x_6913_;
}
else
{
lean_object* v_a_6914_; lean_object* v___x_6915_; 
v_a_6914_ = lean_ctor_get(v___x_6906_, 0);
lean_inc(v_a_6914_);
lean_dec_ref_known(v___x_6906_, 1);
v___x_6915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6915_, 0, v_config_6904_);
lean_ctor_set(v___x_6915_, 1, v_a_6914_);
return v___x_6915_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21___boxed(lean_object* v_tz_6916_, lean_object* v_input_6917_, lean_object* v_config_6918_){
_start:
{
lean_object* v_res_6919_; 
v_res_6919_ = l_Std_Time_GenericFormat_spec_x21(v_tz_6916_, v_input_6917_, v_config_6918_);
lean_dec(v_tz_6916_);
return v_res_6919_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(lean_object* v_config_6923_, lean_object* v_aw_6924_, lean_object* v_builder_6925_, lean_object* v_x_6926_, lean_object* v_a_6927_){
_start:
{
if (lean_obj_tag(v_x_6926_) == 0)
{
lean_object* v_dateformat_6928_; lean_object* v___x_6929_; 
v_dateformat_6928_ = lean_ctor_get(v_config_6923_, 0);
lean_inc_ref(v_dateformat_6928_);
lean_dec_ref(v_config_6923_);
v___x_6929_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(v_builder_6925_, v_aw_6924_, v_dateformat_6928_);
lean_dec_ref(v_dateformat_6928_);
if (lean_obj_tag(v___x_6929_) == 0)
{
lean_object* v___x_6930_; lean_object* v___x_6931_; 
v___x_6930_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go___closed__1));
v___x_6931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6931_, 0, v_a_6927_);
lean_ctor_set(v___x_6931_, 1, v___x_6930_);
return v___x_6931_;
}
else
{
lean_object* v_val_6932_; lean_object* v___x_6933_; 
v_val_6932_ = lean_ctor_get(v___x_6929_, 0);
lean_inc(v_val_6932_);
lean_dec_ref_known(v___x_6929_, 1);
v___x_6933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6933_, 0, v_a_6927_);
lean_ctor_set(v___x_6933_, 1, v_val_6932_);
return v___x_6933_;
}
}
else
{
lean_object* v_head_6934_; lean_object* v_tail_6935_; lean_object* v___x_6936_; 
v_head_6934_ = lean_ctor_get(v_x_6926_, 0);
lean_inc(v_head_6934_);
v_tail_6935_ = lean_ctor_get(v_x_6926_, 1);
lean_inc_n(v_tail_6935_, 2);
lean_dec_ref_known(v_x_6926_, 2);
lean_inc_ref(v_config_6923_);
v___x_6936_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(v_builder_6925_, v_config_6923_, v_head_6934_, v_tail_6935_, v_a_6927_);
if (lean_obj_tag(v___x_6936_) == 0)
{
lean_object* v_pos_6937_; lean_object* v_res_6938_; 
v_pos_6937_ = lean_ctor_get(v___x_6936_, 0);
lean_inc(v_pos_6937_);
v_res_6938_ = lean_ctor_get(v___x_6936_, 1);
lean_inc(v_res_6938_);
lean_dec_ref_known(v___x_6936_, 2);
v_builder_6925_ = v_res_6938_;
v_x_6926_ = v_tail_6935_;
v_a_6927_ = v_pos_6937_;
goto _start;
}
else
{
lean_object* v_pos_6940_; lean_object* v_err_6941_; lean_object* v___x_6943_; uint8_t v_isShared_6944_; uint8_t v_isSharedCheck_6948_; 
lean_dec(v_tail_6935_);
lean_dec(v_aw_6924_);
lean_dec_ref(v_config_6923_);
v_pos_6940_ = lean_ctor_get(v___x_6936_, 0);
v_err_6941_ = lean_ctor_get(v___x_6936_, 1);
v_isSharedCheck_6948_ = !lean_is_exclusive(v___x_6936_);
if (v_isSharedCheck_6948_ == 0)
{
v___x_6943_ = v___x_6936_;
v_isShared_6944_ = v_isSharedCheck_6948_;
goto v_resetjp_6942_;
}
else
{
lean_inc(v_err_6941_);
lean_inc(v_pos_6940_);
lean_dec(v___x_6936_);
v___x_6943_ = lean_box(0);
v_isShared_6944_ = v_isSharedCheck_6948_;
goto v_resetjp_6942_;
}
v_resetjp_6942_:
{
lean_object* v___x_6946_; 
if (v_isShared_6944_ == 0)
{
v___x_6946_ = v___x_6943_;
goto v_reusejp_6945_;
}
else
{
lean_object* v_reuseFailAlloc_6947_; 
v_reuseFailAlloc_6947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6947_, 0, v_pos_6940_);
lean_ctor_set(v_reuseFailAlloc_6947_, 1, v_err_6941_);
v___x_6946_ = v_reuseFailAlloc_6947_;
goto v_reusejp_6945_;
}
v_reusejp_6945_:
{
return v___x_6946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(lean_object* v_format_6951_, lean_object* v_config_6952_, lean_object* v_aw_6953_, lean_object* v_a_6954_){
_start:
{
lean_object* v___x_6955_; lean_object* v___x_6956_; 
v___x_6955_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser___closed__0));
v___x_6956_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(v_config_6952_, v_aw_6953_, v___x_6955_, v_format_6951_, v_a_6954_);
return v___x_6956_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(lean_object* v_config_6960_, lean_object* v_format_6961_, lean_object* v_func_6962_, lean_object* v_a_6963_){
_start:
{
if (lean_obj_tag(v_format_6961_) == 0)
{
lean_dec_ref(v_config_6960_);
if (lean_obj_tag(v_func_6962_) == 0)
{
lean_object* v___x_6964_; lean_object* v___x_6965_; 
v___x_6964_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg___closed__1));
v___x_6965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6965_, 0, v_a_6963_);
lean_ctor_set(v___x_6965_, 1, v___x_6964_);
return v___x_6965_;
}
else
{
lean_object* v_val_6966_; lean_object* v_fst_6967_; lean_object* v_snd_6968_; lean_object* v___x_6969_; uint8_t v_decide_6970_; 
v_val_6966_ = lean_ctor_get(v_func_6962_, 0);
lean_inc(v_val_6966_);
lean_dec_ref_known(v_func_6962_, 1);
v_fst_6967_ = lean_ctor_get(v_a_6963_, 0);
v_snd_6968_ = lean_ctor_get(v_a_6963_, 1);
v___x_6969_ = lean_string_utf8_byte_size(v_fst_6967_);
v_decide_6970_ = lean_nat_dec_eq(v_snd_6968_, v___x_6969_);
if (v_decide_6970_ == 0)
{
lean_object* v___x_6971_; lean_object* v___x_6972_; 
lean_dec(v_val_6966_);
v___x_6971_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
v___x_6972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6972_, 0, v_a_6963_);
lean_ctor_set(v___x_6972_, 1, v___x_6971_);
return v___x_6972_;
}
else
{
lean_object* v___x_6973_; 
v___x_6973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6973_, 0, v_a_6963_);
lean_ctor_set(v___x_6973_, 1, v_val_6966_);
return v___x_6973_;
}
}
}
else
{
lean_object* v_head_6974_; 
v_head_6974_ = lean_ctor_get(v_format_6961_, 0);
lean_inc(v_head_6974_);
if (lean_obj_tag(v_head_6974_) == 0)
{
lean_object* v_tail_6975_; lean_object* v_val_6976_; lean_object* v___x_6977_; 
v_tail_6975_ = lean_ctor_get(v_format_6961_, 1);
lean_inc(v_tail_6975_);
lean_dec_ref_known(v_format_6961_, 2);
v_val_6976_ = lean_ctor_get(v_head_6974_, 0);
lean_inc_ref(v_val_6976_);
lean_dec_ref_known(v_head_6974_, 1);
v___x_6977_ = l_Std_Internal_Parsec_String_pstring(v_val_6976_, v_a_6963_);
if (lean_obj_tag(v___x_6977_) == 0)
{
lean_object* v_pos_6978_; 
v_pos_6978_ = lean_ctor_get(v___x_6977_, 0);
lean_inc(v_pos_6978_);
lean_dec_ref_known(v___x_6977_, 2);
v_format_6961_ = v_tail_6975_;
v_a_6963_ = v_pos_6978_;
goto _start;
}
else
{
lean_object* v_pos_6980_; lean_object* v_err_6981_; lean_object* v___x_6983_; uint8_t v_isShared_6984_; uint8_t v_isSharedCheck_6988_; 
lean_dec(v_tail_6975_);
lean_dec(v_func_6962_);
lean_dec_ref(v_config_6960_);
v_pos_6980_ = lean_ctor_get(v___x_6977_, 0);
v_err_6981_ = lean_ctor_get(v___x_6977_, 1);
v_isSharedCheck_6988_ = !lean_is_exclusive(v___x_6977_);
if (v_isSharedCheck_6988_ == 0)
{
v___x_6983_ = v___x_6977_;
v_isShared_6984_ = v_isSharedCheck_6988_;
goto v_resetjp_6982_;
}
else
{
lean_inc(v_err_6981_);
lean_inc(v_pos_6980_);
lean_dec(v___x_6977_);
v___x_6983_ = lean_box(0);
v_isShared_6984_ = v_isSharedCheck_6988_;
goto v_resetjp_6982_;
}
v_resetjp_6982_:
{
lean_object* v___x_6986_; 
if (v_isShared_6984_ == 0)
{
v___x_6986_ = v___x_6983_;
goto v_reusejp_6985_;
}
else
{
lean_object* v_reuseFailAlloc_6987_; 
v_reuseFailAlloc_6987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6987_, 0, v_pos_6980_);
lean_ctor_set(v_reuseFailAlloc_6987_, 1, v_err_6981_);
v___x_6986_ = v_reuseFailAlloc_6987_;
goto v_reusejp_6985_;
}
v_reusejp_6985_:
{
return v___x_6986_;
}
}
}
}
else
{
lean_object* v_tail_6989_; lean_object* v_modifier_6990_; lean_object* v___x_6991_; lean_object* v___x_6992_; 
v_tail_6989_ = lean_ctor_get(v_format_6961_, 1);
lean_inc_n(v_tail_6989_, 2);
lean_dec_ref_known(v_format_6961_, 2);
v_modifier_6990_ = lean_ctor_get(v_head_6974_, 0);
lean_inc_ref(v_modifier_6990_);
lean_dec_ref_known(v_head_6974_, 1);
v___x_6991_ = l___private_Std_Time_Format_Basic_0__Std_Time_reservedDigits(v_tail_6989_);
lean_inc_ref(v_config_6960_);
v___x_6992_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_6960_, v___x_6991_, v_modifier_6990_, v_a_6963_);
if (lean_obj_tag(v___x_6992_) == 0)
{
lean_object* v_pos_6993_; lean_object* v_res_6994_; lean_object* v___x_6995_; 
v_pos_6993_ = lean_ctor_get(v___x_6992_, 0);
lean_inc(v_pos_6993_);
v_res_6994_ = lean_ctor_get(v___x_6992_, 1);
lean_inc(v_res_6994_);
lean_dec_ref_known(v___x_6992_, 2);
v___x_6995_ = lean_apply_1(v_func_6962_, v_res_6994_);
v_format_6961_ = v_tail_6989_;
v_func_6962_ = v___x_6995_;
v_a_6963_ = v_pos_6993_;
goto _start;
}
else
{
lean_object* v_pos_6997_; lean_object* v_err_6998_; lean_object* v___x_7000_; uint8_t v_isShared_7001_; uint8_t v_isSharedCheck_7005_; 
lean_dec(v_tail_6989_);
lean_dec(v_func_6962_);
lean_dec_ref(v_config_6960_);
v_pos_6997_ = lean_ctor_get(v___x_6992_, 0);
v_err_6998_ = lean_ctor_get(v___x_6992_, 1);
v_isSharedCheck_7005_ = !lean_is_exclusive(v___x_6992_);
if (v_isSharedCheck_7005_ == 0)
{
v___x_7000_ = v___x_6992_;
v_isShared_7001_ = v_isSharedCheck_7005_;
goto v_resetjp_6999_;
}
else
{
lean_inc(v_err_6998_);
lean_inc(v_pos_6997_);
lean_dec(v___x_6992_);
v___x_7000_ = lean_box(0);
v_isShared_7001_ = v_isSharedCheck_7005_;
goto v_resetjp_6999_;
}
v_resetjp_6999_:
{
lean_object* v___x_7003_; 
if (v_isShared_7001_ == 0)
{
v___x_7003_ = v___x_7000_;
goto v_reusejp_7002_;
}
else
{
lean_object* v_reuseFailAlloc_7004_; 
v_reuseFailAlloc_7004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7004_, 0, v_pos_6997_);
lean_ctor_set(v_reuseFailAlloc_7004_, 1, v_err_6998_);
v___x_7003_ = v_reuseFailAlloc_7004_;
goto v_reusejp_7002_;
}
v_reusejp_7002_:
{
return v___x_7003_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go(lean_object* v_00_u03b1_7006_, lean_object* v_config_7007_, lean_object* v_format_7008_, lean_object* v_func_7009_, lean_object* v_a_7010_){
_start:
{
lean_object* v___x_7011_; 
v___x_7011_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7007_, v_format_7008_, v_func_7009_, v_a_7010_);
return v___x_7011_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser___redArg(lean_object* v_format_7012_, lean_object* v_config_7013_, lean_object* v_func_7014_, lean_object* v_a_7015_){
_start:
{
lean_object* v___x_7016_; 
v___x_7016_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7013_, v_format_7012_, v_func_7014_, v_a_7015_);
return v___x_7016_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser(lean_object* v_00_u03b1_7017_, lean_object* v_format_7018_, lean_object* v_config_7019_, lean_object* v_func_7020_, lean_object* v_a_7021_){
_start:
{
lean_object* v___x_7022_; 
v___x_7022_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7019_, v_format_7018_, v_func_7020_, v_a_7021_);
return v___x_7022_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse___lam__0(lean_object* v_string_7023_, lean_object* v_config_7024_, lean_object* v_aw_7025_, lean_object* v___y_7026_){
_start:
{
lean_object* v___x_7027_; 
v___x_7027_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(v_string_7023_, v_config_7024_, v_aw_7025_, v___y_7026_);
if (lean_obj_tag(v___x_7027_) == 0)
{
lean_object* v_pos_7028_; lean_object* v_fst_7029_; lean_object* v_snd_7030_; lean_object* v___x_7031_; uint8_t v_decide_7032_; 
v_pos_7028_ = lean_ctor_get(v___x_7027_, 0);
v_fst_7029_ = lean_ctor_get(v_pos_7028_, 0);
v_snd_7030_ = lean_ctor_get(v_pos_7028_, 1);
v___x_7031_ = lean_string_utf8_byte_size(v_fst_7029_);
v_decide_7032_ = lean_nat_dec_eq(v_snd_7030_, v___x_7031_);
if (v_decide_7032_ == 0)
{
lean_object* v___x_7034_; uint8_t v_isShared_7035_; uint8_t v_isSharedCheck_7040_; 
lean_inc(v_pos_7028_);
v_isSharedCheck_7040_ = !lean_is_exclusive(v___x_7027_);
if (v_isSharedCheck_7040_ == 0)
{
lean_object* v_unused_7041_; lean_object* v_unused_7042_; 
v_unused_7041_ = lean_ctor_get(v___x_7027_, 1);
lean_dec(v_unused_7041_);
v_unused_7042_ = lean_ctor_get(v___x_7027_, 0);
lean_dec(v_unused_7042_);
v___x_7034_ = v___x_7027_;
v_isShared_7035_ = v_isSharedCheck_7040_;
goto v_resetjp_7033_;
}
else
{
lean_dec(v___x_7027_);
v___x_7034_ = lean_box(0);
v_isShared_7035_ = v_isSharedCheck_7040_;
goto v_resetjp_7033_;
}
v_resetjp_7033_:
{
lean_object* v___x_7036_; lean_object* v___x_7038_; 
v___x_7036_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_7035_ == 0)
{
lean_ctor_set_tag(v___x_7034_, 1);
lean_ctor_set(v___x_7034_, 1, v___x_7036_);
v___x_7038_ = v___x_7034_;
goto v_reusejp_7037_;
}
else
{
lean_object* v_reuseFailAlloc_7039_; 
v_reuseFailAlloc_7039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7039_, 0, v_pos_7028_);
lean_ctor_set(v_reuseFailAlloc_7039_, 1, v___x_7036_);
v___x_7038_ = v_reuseFailAlloc_7039_;
goto v_reusejp_7037_;
}
v_reusejp_7037_:
{
return v___x_7038_;
}
}
}
else
{
return v___x_7027_;
}
}
else
{
return v___x_7027_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse(lean_object* v_aw_7043_, lean_object* v_format_7044_, lean_object* v_input_7045_){
_start:
{
lean_object* v_config_7046_; lean_object* v_string_7047_; lean_object* v___f_7048_; lean_object* v___x_7049_; 
v_config_7046_ = lean_ctor_get(v_format_7044_, 0);
lean_inc_ref(v_config_7046_);
v_string_7047_ = lean_ctor_get(v_format_7044_, 1);
lean_inc(v_string_7047_);
lean_dec_ref(v_format_7044_);
v___f_7048_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parse___lam__0), 4, 3);
lean_closure_set(v___f_7048_, 0, v_string_7047_);
lean_closure_set(v___f_7048_, 1, v_config_7046_);
lean_closure_set(v___f_7048_, 2, v_aw_7043_);
v___x_7049_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_7048_, v_input_7045_);
return v___x_7049_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(lean_object* v_msg_7050_){
_start:
{
lean_object* v___x_7051_; lean_object* v___x_7052_; 
v___x_7051_ = l_Std_Time_instInhabitedDateTime;
v___x_7052_ = lean_panic_fn_borrowed(v___x_7051_, v_msg_7050_);
return v___x_7052_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse_x21(lean_object* v_aw_7054_, lean_object* v_format_7055_, lean_object* v_input_7056_){
_start:
{
lean_object* v___x_7057_; 
v___x_7057_ = l_Std_Time_GenericFormat_parse(v_aw_7054_, v_format_7055_, v_input_7056_);
if (lean_obj_tag(v___x_7057_) == 0)
{
lean_object* v_a_7058_; lean_object* v___x_7059_; lean_object* v___x_7060_; lean_object* v___x_7061_; lean_object* v___x_7062_; lean_object* v___x_7063_; lean_object* v___x_7064_; 
v_a_7058_ = lean_ctor_get(v___x_7057_, 0);
lean_inc(v_a_7058_);
lean_dec_ref_known(v___x_7057_, 1);
v___x_7059_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_7060_ = ((lean_object*)(l_Std_Time_GenericFormat_parse_x21___closed__0));
v___x_7061_ = lean_unsigned_to_nat(975u);
v___x_7062_ = lean_unsigned_to_nat(18u);
v___x_7063_ = l_mkPanicMessageWithDecl(v___x_7059_, v___x_7060_, v___x_7061_, v___x_7062_, v_a_7058_);
lean_dec(v_a_7058_);
v___x_7064_ = l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(v___x_7063_);
return v___x_7064_;
}
else
{
lean_object* v_a_7065_; 
v_a_7065_ = lean_ctor_get(v___x_7057_, 0);
lean_inc(v_a_7065_);
lean_dec_ref_known(v___x_7057_, 1);
return v_a_7065_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0(lean_object* v_config_7066_, lean_object* v_string_7067_, lean_object* v_builder_7068_, lean_object* v___y_7069_){
_start:
{
lean_object* v___x_7070_; 
v___x_7070_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7066_, v_string_7067_, v_builder_7068_, v___y_7069_);
return v___x_7070_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg(lean_object* v_format_7071_, lean_object* v_builder_7072_, lean_object* v_input_7073_){
_start:
{
lean_object* v_config_7074_; lean_object* v_string_7075_; lean_object* v___f_7076_; lean_object* v___x_7077_; 
v_config_7074_ = lean_ctor_get(v_format_7071_, 0);
lean_inc_ref(v_config_7074_);
v_string_7075_ = lean_ctor_get(v_format_7071_, 1);
lean_inc(v_string_7075_);
lean_dec_ref(v_format_7071_);
v___f_7076_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0), 4, 3);
lean_closure_set(v___f_7076_, 0, v_config_7074_);
lean_closure_set(v___f_7076_, 1, v_string_7075_);
lean_closure_set(v___f_7076_, 2, v_builder_7072_);
v___x_7077_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_7076_, v_input_7073_);
return v___x_7077_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder(lean_object* v_aw_7078_, lean_object* v_00_u03b1_7079_, lean_object* v_format_7080_, lean_object* v_builder_7081_, lean_object* v_input_7082_){
_start:
{
lean_object* v___x_7083_; 
v___x_7083_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_7080_, v_builder_7081_, v_input_7082_);
return v___x_7083_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___boxed(lean_object* v_aw_7084_, lean_object* v_00_u03b1_7085_, lean_object* v_format_7086_, lean_object* v_builder_7087_, lean_object* v_input_7088_){
_start:
{
lean_object* v_res_7089_; 
v_res_7089_ = l_Std_Time_GenericFormat_parseBuilder(v_aw_7084_, v_00_u03b1_7085_, v_format_7086_, v_builder_7087_, v_input_7088_);
lean_dec(v_aw_7084_);
return v_res_7089_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg(lean_object* v_inst_7091_, lean_object* v_format_7092_, lean_object* v_builder_7093_, lean_object* v_input_7094_){
_start:
{
lean_object* v___x_7095_; 
v___x_7095_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_7092_, v_builder_7093_, v_input_7094_);
if (lean_obj_tag(v___x_7095_) == 0)
{
lean_object* v_a_7096_; lean_object* v___x_7097_; lean_object* v___x_7098_; lean_object* v___x_7099_; lean_object* v___x_7100_; lean_object* v___x_7101_; lean_object* v___x_7102_; 
v_a_7096_ = lean_ctor_get(v___x_7095_, 0);
lean_inc(v_a_7096_);
lean_dec_ref_known(v___x_7095_, 1);
v___x_7097_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_7098_ = ((lean_object*)(l_Std_Time_GenericFormat_parseBuilder_x21___redArg___closed__0));
v___x_7099_ = lean_unsigned_to_nat(989u);
v___x_7100_ = lean_unsigned_to_nat(18u);
v___x_7101_ = l_mkPanicMessageWithDecl(v___x_7097_, v___x_7098_, v___x_7099_, v___x_7100_, v_a_7096_);
lean_dec(v_a_7096_);
v___x_7102_ = l_panic___redArg(v_inst_7091_, v___x_7101_);
return v___x_7102_;
}
else
{
lean_object* v_a_7103_; 
v_a_7103_ = lean_ctor_get(v___x_7095_, 0);
lean_inc(v_a_7103_);
lean_dec_ref_known(v___x_7095_, 1);
return v_a_7103_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg___boxed(lean_object* v_inst_7104_, lean_object* v_format_7105_, lean_object* v_builder_7106_, lean_object* v_input_7107_){
_start:
{
lean_object* v_res_7108_; 
v_res_7108_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7104_, v_format_7105_, v_builder_7106_, v_input_7107_);
lean_dec(v_inst_7104_);
return v_res_7108_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21(lean_object* v_00_u03b1_7109_, lean_object* v_aw_7110_, lean_object* v_inst_7111_, lean_object* v_format_7112_, lean_object* v_builder_7113_, lean_object* v_input_7114_){
_start:
{
lean_object* v___x_7115_; 
v___x_7115_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7111_, v_format_7112_, v_builder_7113_, v_input_7114_);
return v___x_7115_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___boxed(lean_object* v_00_u03b1_7116_, lean_object* v_aw_7117_, lean_object* v_inst_7118_, lean_object* v_format_7119_, lean_object* v_builder_7120_, lean_object* v_input_7121_){
_start:
{
lean_object* v_res_7122_; 
v_res_7122_ = l_Std_Time_GenericFormat_parseBuilder_x21(v_00_u03b1_7116_, v_aw_7117_, v_inst_7118_, v_format_7119_, v_builder_7120_, v_input_7121_);
lean_dec(v_inst_7118_);
lean_dec(v_aw_7117_);
return v_res_7122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(lean_object* v_getInfo_7123_, lean_object* v_dateformat_7124_, lean_object* v_data_7125_, lean_object* v_format_7126_){
_start:
{
if (lean_obj_tag(v_format_7126_) == 0)
{
lean_object* v___x_7127_; 
lean_dec_ref(v_dateformat_7124_);
lean_dec_ref(v_getInfo_7123_);
v___x_7127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7127_, 0, v_data_7125_);
return v___x_7127_;
}
else
{
lean_object* v_head_7128_; 
v_head_7128_ = lean_ctor_get(v_format_7126_, 0);
lean_inc(v_head_7128_);
if (lean_obj_tag(v_head_7128_) == 0)
{
lean_object* v_tail_7129_; lean_object* v_val_7130_; lean_object* v___x_7131_; 
v_tail_7129_ = lean_ctor_get(v_format_7126_, 1);
lean_inc(v_tail_7129_);
lean_dec_ref_known(v_format_7126_, 2);
v_val_7130_ = lean_ctor_get(v_head_7128_, 0);
lean_inc_ref(v_val_7130_);
lean_dec_ref_known(v_head_7128_, 1);
v___x_7131_ = lean_string_append(v_data_7125_, v_val_7130_);
lean_dec_ref(v_val_7130_);
v_data_7125_ = v___x_7131_;
v_format_7126_ = v_tail_7129_;
goto _start;
}
else
{
lean_object* v_tail_7133_; lean_object* v_modifier_7134_; lean_object* v___x_7135_; 
v_tail_7133_ = lean_ctor_get(v_format_7126_, 1);
lean_inc(v_tail_7133_);
lean_dec_ref_known(v_format_7126_, 2);
v_modifier_7134_ = lean_ctor_get(v_head_7128_, 0);
lean_inc_ref_n(v_modifier_7134_, 2);
lean_dec_ref_known(v_head_7128_, 1);
lean_inc_ref(v_getInfo_7123_);
v___x_7135_ = lean_apply_1(v_getInfo_7123_, v_modifier_7134_);
if (lean_obj_tag(v___x_7135_) == 0)
{
lean_object* v___x_7136_; 
lean_dec_ref(v_modifier_7134_);
lean_dec(v_tail_7133_);
lean_dec_ref(v_data_7125_);
lean_dec_ref(v_dateformat_7124_);
lean_dec_ref(v_getInfo_7123_);
v___x_7136_ = lean_box(0);
return v___x_7136_;
}
else
{
lean_object* v_val_7137_; lean_object* v___x_7138_; lean_object* v___x_7139_; 
v_val_7137_ = lean_ctor_get(v___x_7135_, 0);
lean_inc(v_val_7137_);
lean_dec_ref_known(v___x_7135_, 1);
lean_inc_ref(v_dateformat_7124_);
v___x_7138_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7124_, v_modifier_7134_, v_val_7137_);
v___x_7139_ = lean_string_append(v_data_7125_, v___x_7138_);
lean_dec_ref(v___x_7138_);
v_data_7125_ = v___x_7139_;
v_format_7126_ = v_tail_7133_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___redArg(lean_object* v_format_7141_, lean_object* v_getInfo_7142_){
_start:
{
lean_object* v_config_7143_; lean_object* v_string_7144_; lean_object* v_dateformat_7145_; lean_object* v___x_7146_; lean_object* v___x_7147_; 
v_config_7143_ = lean_ctor_get(v_format_7141_, 0);
lean_inc_ref(v_config_7143_);
v_string_7144_ = lean_ctor_get(v_format_7141_, 1);
lean_inc(v_string_7144_);
lean_dec_ref(v_format_7141_);
v_dateformat_7145_ = lean_ctor_get(v_config_7143_, 0);
lean_inc_ref(v_dateformat_7145_);
lean_dec_ref(v_config_7143_);
v___x_7146_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_7147_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(v_getInfo_7142_, v_dateformat_7145_, v___x_7146_, v_string_7144_);
return v___x_7147_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric(lean_object* v_aw_7148_, lean_object* v_format_7149_, lean_object* v_getInfo_7150_){
_start:
{
lean_object* v___x_7151_; 
v___x_7151_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_format_7149_, v_getInfo_7150_);
return v___x_7151_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___boxed(lean_object* v_aw_7152_, lean_object* v_format_7153_, lean_object* v_getInfo_7154_){
_start:
{
lean_object* v_res_7155_; 
v_res_7155_ = l_Std_Time_GenericFormat_formatGeneric(v_aw_7152_, v_format_7153_, v_getInfo_7154_);
lean_dec(v_aw_7152_);
return v_res_7155_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatParts___redArg(lean_object* v_format_7156_, lean_object* v_date_7157_, lean_object* v_time_7158_, lean_object* v_zone_7159_){
_start:
{
lean_object* v_config_7160_; lean_object* v_dateformat_7161_; lean_object* v___x_7162_; lean_object* v___x_7163_; 
v_config_7160_ = lean_ctor_get(v_format_7156_, 0);
v_dateformat_7161_ = lean_ctor_get(v_config_7160_, 0);
lean_inc_ref(v_dateformat_7161_);
v___x_7162_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___boxed), 5, 4);
lean_closure_set(v___x_7162_, 0, v_dateformat_7161_);
lean_closure_set(v___x_7162_, 1, v_date_7157_);
lean_closure_set(v___x_7162_, 2, v_time_7158_);
lean_closure_set(v___x_7162_, 3, v_zone_7159_);
v___x_7163_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_format_7156_, v___x_7162_);
return v___x_7163_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatParts(lean_object* v_aw_7164_, lean_object* v_format_7165_, lean_object* v_date_7166_, lean_object* v_time_7167_, lean_object* v_zone_7168_){
_start:
{
lean_object* v___x_7169_; 
v___x_7169_ = l_Std_Time_GenericFormat_formatParts___redArg(v_format_7165_, v_date_7166_, v_time_7167_, v_zone_7168_);
return v___x_7169_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatParts___boxed(lean_object* v_aw_7170_, lean_object* v_format_7171_, lean_object* v_date_7172_, lean_object* v_time_7173_, lean_object* v_zone_7174_){
_start:
{
lean_object* v_res_7175_; 
v_res_7175_ = l_Std_Time_GenericFormat_formatParts(v_aw_7170_, v_format_7171_, v_date_7172_, v_time_7173_, v_zone_7174_);
lean_dec(v_aw_7170_);
return v_res_7175_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format___lam__0(lean_object* v_tz_7176_, lean_object* v_timestamp_7177_, lean_object* v___x_7178_, lean_object* v_x_7179_){
_start:
{
lean_object* v_offset_7180_; lean_object* v_second_7181_; lean_object* v_nano_7182_; lean_object* v___x_7183_; lean_object* v___x_7184_; lean_object* v___x_7185_; lean_object* v_nanos_7186_; lean_object* v___x_7187_; lean_object* v_nanos_7188_; lean_object* v___x_7189_; lean_object* v___x_7190_; lean_object* v___x_7191_; 
v_offset_7180_ = lean_ctor_get(v_tz_7176_, 0);
v_second_7181_ = lean_ctor_get(v_timestamp_7177_, 0);
v_nano_7182_ = lean_ctor_get(v_timestamp_7177_, 1);
v___x_7183_ = lean_nat_to_int(v___x_7178_);
v___x_7184_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3);
v___x_7185_ = lean_int_mul(v_second_7181_, v___x_7184_);
v_nanos_7186_ = lean_int_add(v___x_7185_, v_nano_7182_);
lean_dec(v___x_7185_);
v___x_7187_ = lean_int_mul(v_offset_7180_, v___x_7184_);
v_nanos_7188_ = lean_int_add(v___x_7187_, v___x_7183_);
lean_dec(v___x_7183_);
lean_dec(v___x_7187_);
v___x_7189_ = lean_int_add(v_nanos_7186_, v_nanos_7188_);
lean_dec(v_nanos_7188_);
lean_dec(v_nanos_7186_);
v___x_7190_ = l_Std_Time_Duration_ofNanoseconds(v___x_7189_);
lean_dec(v___x_7189_);
v___x_7191_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_7190_);
return v___x_7191_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format___lam__0___boxed(lean_object* v_tz_7192_, lean_object* v_timestamp_7193_, lean_object* v___x_7194_, lean_object* v_x_7195_){
_start:
{
lean_object* v_res_7196_; 
v_res_7196_ = l_Std_Time_GenericFormat_format___lam__0(v_tz_7192_, v_timestamp_7193_, v___x_7194_, v_x_7195_);
lean_dec_ref(v_timestamp_7193_);
lean_dec_ref(v_tz_7192_);
return v_res_7196_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format(lean_object* v_aw_7197_, lean_object* v_format_7198_, lean_object* v_date_7199_){
_start:
{
lean_object* v_date_7201_; lean_object* v_timezone_7202_; 
if (lean_obj_tag(v_aw_7197_) == 0)
{
lean_object* v_a_7212_; lean_object* v_offset_7213_; lean_object* v_name_7214_; lean_object* v_abbreviation_7215_; uint8_t v_isDST_7216_; lean_object* v_timestamp_7217_; uint8_t v___x_7218_; uint8_t v___x_7219_; lean_object* v_ltt_7220_; lean_object* v___x_7221_; lean_object* v___x_7222_; lean_object* v___x_7223_; lean_object* v___x_7224_; lean_object* v_tz_7225_; lean_object* v___f_7226_; lean_object* v___x_7227_; 
v_a_7212_ = lean_ctor_get(v_aw_7197_, 0);
v_offset_7213_ = lean_ctor_get(v_a_7212_, 0);
v_name_7214_ = lean_ctor_get(v_a_7212_, 1);
v_abbreviation_7215_ = lean_ctor_get(v_a_7212_, 2);
v_isDST_7216_ = lean_ctor_get_uint8(v_a_7212_, sizeof(void*)*3);
v_timestamp_7217_ = lean_ctor_get(v_date_7199_, 1);
lean_inc_ref(v_timestamp_7217_);
lean_dec_ref(v_date_7199_);
v___x_7218_ = 0;
v___x_7219_ = 1;
lean_inc_ref(v_name_7214_);
lean_inc_ref(v_abbreviation_7215_);
lean_inc(v_offset_7213_);
v_ltt_7220_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_7220_, 0, v_offset_7213_);
lean_ctor_set(v_ltt_7220_, 1, v_abbreviation_7215_);
lean_ctor_set(v_ltt_7220_, 2, v_name_7214_);
lean_ctor_set_uint8(v_ltt_7220_, sizeof(void*)*3, v_isDST_7216_);
lean_ctor_set_uint8(v_ltt_7220_, sizeof(void*)*3 + 1, v___x_7218_);
lean_ctor_set_uint8(v_ltt_7220_, sizeof(void*)*3 + 2, v___x_7219_);
v___x_7221_ = lean_unsigned_to_nat(0u);
v___x_7222_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_7223_ = lean_box(0);
v___x_7224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_7224_, 0, v_ltt_7220_);
lean_ctor_set(v___x_7224_, 1, v___x_7222_);
lean_ctor_set(v___x_7224_, 2, v___x_7223_);
v_tz_7225_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_7224_, v_timestamp_7217_);
lean_inc_ref(v_tz_7225_);
v___f_7226_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_format___lam__0___boxed), 4, 3);
lean_closure_set(v___f_7226_, 0, v_tz_7225_);
lean_closure_set(v___f_7226_, 1, v_timestamp_7217_);
lean_closure_set(v___f_7226_, 2, v___x_7221_);
v___x_7227_ = lean_mk_thunk(v___f_7226_);
v_date_7201_ = v___x_7227_;
v_timezone_7202_ = v_tz_7225_;
goto v___jp_7200_;
}
else
{
lean_object* v_date_7228_; lean_object* v_timezone_7229_; 
v_date_7228_ = lean_ctor_get(v_date_7199_, 0);
lean_inc_ref(v_date_7228_);
v_timezone_7229_ = lean_ctor_get(v_date_7199_, 3);
lean_inc_ref(v_timezone_7229_);
lean_dec_ref(v_date_7199_);
v_date_7201_ = v_date_7228_;
v_timezone_7202_ = v_timezone_7229_;
goto v___jp_7200_;
}
v___jp_7200_:
{
lean_object* v_pdt_7203_; lean_object* v_date_7204_; lean_object* v_time_7205_; lean_object* v___x_7206_; lean_object* v___x_7207_; lean_object* v___x_7208_; lean_object* v___x_7209_; 
v_pdt_7203_ = lean_thunk_get_own(v_date_7201_);
lean_dec_ref(v_date_7201_);
v_date_7204_ = lean_ctor_get(v_pdt_7203_, 0);
lean_inc_ref(v_date_7204_);
v_time_7205_ = lean_ctor_get(v_pdt_7203_, 1);
lean_inc_ref(v_time_7205_);
lean_dec(v_pdt_7203_);
v___x_7206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7206_, 0, v_date_7204_);
v___x_7207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7207_, 0, v_time_7205_);
v___x_7208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7208_, 0, v_timezone_7202_);
v___x_7209_ = l_Std_Time_GenericFormat_formatParts___redArg(v_format_7198_, v___x_7206_, v___x_7207_, v___x_7208_);
if (lean_obj_tag(v___x_7209_) == 0)
{
lean_object* v___x_7210_; 
v___x_7210_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
return v___x_7210_;
}
else
{
lean_object* v_val_7211_; 
v_val_7211_ = lean_ctor_get(v___x_7209_, 0);
lean_inc(v_val_7211_);
lean_dec_ref_known(v___x_7209_, 1);
return v_val_7211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format___boxed(lean_object* v_aw_7230_, lean_object* v_format_7231_, lean_object* v_date_7232_){
_start:
{
lean_object* v_res_7233_; 
v_res_7233_ = l_Std_Time_GenericFormat_format(v_aw_7230_, v_format_7231_, v_date_7232_);
lean_dec(v_aw_7230_);
return v_res_7233_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(lean_object* v_dateformat_7234_, lean_object* v_data_7235_, lean_object* v_format_7236_){
_start:
{
if (lean_obj_tag(v_format_7236_) == 0)
{
lean_dec_ref(v_dateformat_7234_);
return v_data_7235_;
}
else
{
lean_object* v_head_7237_; 
v_head_7237_ = lean_ctor_get(v_format_7236_, 0);
lean_inc(v_head_7237_);
if (lean_obj_tag(v_head_7237_) == 0)
{
lean_object* v_tail_7238_; lean_object* v_val_7239_; lean_object* v___x_7240_; 
v_tail_7238_ = lean_ctor_get(v_format_7236_, 1);
lean_inc(v_tail_7238_);
lean_dec_ref_known(v_format_7236_, 2);
v_val_7239_ = lean_ctor_get(v_head_7237_, 0);
lean_inc_ref(v_val_7239_);
lean_dec_ref_known(v_head_7237_, 1);
v___x_7240_ = lean_string_append(v_data_7235_, v_val_7239_);
lean_dec_ref(v_val_7239_);
v_data_7235_ = v___x_7240_;
v_format_7236_ = v_tail_7238_;
goto _start;
}
else
{
lean_object* v_tail_7242_; lean_object* v_modifier_7243_; lean_object* v___f_7244_; 
v_tail_7242_ = lean_ctor_get(v_format_7236_, 1);
lean_inc(v_tail_7242_);
lean_dec_ref_known(v_format_7236_, 2);
v_modifier_7243_ = lean_ctor_get(v_head_7237_, 0);
lean_inc_ref(v_modifier_7243_);
lean_dec_ref_known(v_head_7237_, 1);
v___f_7244_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0), 5, 4);
lean_closure_set(v___f_7244_, 0, v_dateformat_7234_);
lean_closure_set(v___f_7244_, 1, v_modifier_7243_);
lean_closure_set(v___f_7244_, 2, v_data_7235_);
lean_closure_set(v___f_7244_, 3, v_tail_7242_);
return v___f_7244_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0(lean_object* v_dateformat_7245_, lean_object* v_modifier_7246_, lean_object* v_data_7247_, lean_object* v_tail_7248_, lean_object* v___y_7249_){
_start:
{
lean_object* v___x_7250_; lean_object* v___x_7251_; lean_object* v___x_7252_; 
lean_inc_ref(v_dateformat_7245_);
v___x_7250_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7245_, v_modifier_7246_, v___y_7249_);
v___x_7251_ = lean_string_append(v_data_7247_, v___x_7250_);
lean_dec_ref(v___x_7250_);
v___x_7252_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7245_, v___x_7251_, v_tail_7248_);
return v___x_7252_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___redArg(lean_object* v_format_7253_){
_start:
{
lean_object* v_config_7254_; lean_object* v_string_7255_; lean_object* v_dateformat_7256_; lean_object* v___x_7257_; lean_object* v___x_7258_; 
v_config_7254_ = lean_ctor_get(v_format_7253_, 0);
lean_inc_ref(v_config_7254_);
v_string_7255_ = lean_ctor_get(v_format_7253_, 1);
lean_inc(v_string_7255_);
lean_dec_ref(v_format_7253_);
v_dateformat_7256_ = lean_ctor_get(v_config_7254_, 0);
lean_inc_ref(v_dateformat_7256_);
lean_dec_ref(v_config_7254_);
v___x_7257_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_7258_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7256_, v___x_7257_, v_string_7255_);
return v___x_7258_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder(lean_object* v_aw_7259_, lean_object* v_format_7260_){
_start:
{
lean_object* v___x_7261_; 
v___x_7261_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v_format_7260_);
return v___x_7261_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___boxed(lean_object* v_aw_7262_, lean_object* v_format_7263_){
_start:
{
lean_object* v_res_7264_; 
v_res_7264_ = l_Std_Time_GenericFormat_formatBuilder(v_aw_7262_, v_format_7263_);
lean_dec(v_aw_7262_);
return v_res_7264_;
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
l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0___boxed__const__1 = _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0___boxed__const__1);
l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1___boxed__const__1 = _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1___boxed__const__1();
lean_mark_persistent(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1___boxed__const__1);
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
