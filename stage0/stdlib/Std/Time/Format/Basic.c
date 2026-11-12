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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_FormatType_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_FormatType_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_2334_ = lean_nat_to_int(v___y_2331_);
v___x_2335_ = lean_int_mul(v___y_2333_, v___x_2334_);
lean_dec(v___x_2334_);
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___y_2332_);
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
v___y_2331_ = v_res_2343_;
v___y_2332_ = v_pos_2342_;
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
v___y_2331_ = v_res_2364_;
v___y_2332_ = v_pos_2363_;
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
v___x_2928_ = lean_nat_to_int(v___y_2922_);
v___x_2929_ = lean_int_mul(v___y_2927_, v___x_2928_);
lean_dec(v___x_2928_);
lean_dec(v___y_2927_);
v___x_2930_ = lean_int_add(v___y_2926_, v___x_2929_);
lean_dec(v___x_2929_);
lean_dec(v___y_2926_);
if (lean_obj_tag(v___y_2921_) == 0)
{
lean_inc(v___y_2923_);
v___y_2913_ = v___x_2930_;
v___y_2914_ = v___y_2924_;
v___y_2915_ = v___y_2925_;
v___y_2916_ = v___y_2923_;
goto v___jp_2912_;
}
else
{
lean_object* v_val_2931_; 
v_val_2931_ = lean_ctor_get(v___y_2921_, 0);
lean_inc(v_val_2931_);
lean_dec_ref_known(v___y_2921_, 1);
v___y_2913_ = v___x_2930_;
v___y_2914_ = v___y_2924_;
v___y_2915_ = v___y_2925_;
v___y_2916_ = v_val_2931_;
goto v___jp_2912_;
}
}
v___jp_2932_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2);
v___x_2941_ = lean_int_mul(v___y_2938_, v___x_2940_);
lean_dec(v___y_2938_);
if (lean_obj_tag(v___y_2937_) == 0)
{
lean_inc(v___y_2935_);
v___y_2921_ = v___y_2934_;
v___y_2922_ = v___y_2933_;
v___y_2923_ = v___y_2935_;
v___y_2924_ = v___y_2939_;
v___y_2925_ = v___y_2936_;
v___y_2926_ = v___x_2941_;
v___y_2927_ = v___y_2935_;
goto v___jp_2920_;
}
else
{
lean_object* v_val_2942_; 
v_val_2942_ = lean_ctor_get(v___y_2937_, 0);
lean_inc(v_val_2942_);
lean_dec_ref_known(v___y_2937_, 1);
v___y_2921_ = v___y_2934_;
v___y_2922_ = v___y_2933_;
v___y_2923_ = v___y_2935_;
v___y_2924_ = v___y_2939_;
v___y_2925_ = v___y_2936_;
v___y_2926_ = v___x_2941_;
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
v___y_2933_ = v___y_2949_;
v___y_2934_ = v_res_2957_;
v___y_2935_ = v___y_2950_;
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
lean_dec(v___y_2949_);
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
v___y_2933_ = v___y_2949_;
v___y_2934_ = v_res_2957_;
v___y_2935_ = v___y_2950_;
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
lean_dec(v___y_2949_);
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
v___y_2949_ = v___x_3004_;
v___y_2950_ = v___x_3000_;
v___y_2951_ = v_res_2995_;
v___y_2952_ = v_res_3007_;
v___y_2953_ = v___x_2999_;
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
v___y_2949_ = v___x_3004_;
v___y_2950_ = v___x_3000_;
v___y_2951_ = v_res_2995_;
v___y_2952_ = v_res_3007_;
v___y_2953_ = v___x_2999_;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_FormatType_match__1_splitter___redArg(lean_object* v_x_4123_, lean_object* v_h__1_4124_, lean_object* v_h__2_4125_, lean_object* v_h__3_4126_){
_start:
{
if (lean_obj_tag(v_x_4123_) == 0)
{
lean_object* v___x_4127_; lean_object* v___x_4128_; 
lean_dec(v_h__2_4125_);
lean_dec(v_h__1_4124_);
v___x_4127_ = lean_box(0);
v___x_4128_ = lean_apply_1(v_h__3_4126_, v___x_4127_);
return v___x_4128_;
}
else
{
lean_object* v_head_4129_; 
lean_dec(v_h__3_4126_);
v_head_4129_ = lean_ctor_get(v_x_4123_, 0);
lean_inc(v_head_4129_);
if (lean_obj_tag(v_head_4129_) == 0)
{
lean_object* v_tail_4130_; lean_object* v_val_4131_; lean_object* v___x_4132_; 
lean_dec(v_h__1_4124_);
v_tail_4130_ = lean_ctor_get(v_x_4123_, 1);
lean_inc(v_tail_4130_);
lean_dec_ref_known(v_x_4123_, 2);
v_val_4131_ = lean_ctor_get(v_head_4129_, 0);
lean_inc_ref(v_val_4131_);
lean_dec_ref_known(v_head_4129_, 1);
v___x_4132_ = lean_apply_2(v_h__2_4125_, v_val_4131_, v_tail_4130_);
return v___x_4132_;
}
else
{
lean_object* v_tail_4133_; lean_object* v_modifier_4134_; lean_object* v___x_4135_; 
lean_dec(v_h__2_4125_);
v_tail_4133_ = lean_ctor_get(v_x_4123_, 1);
lean_inc(v_tail_4133_);
lean_dec_ref_known(v_x_4123_, 2);
v_modifier_4134_ = lean_ctor_get(v_head_4129_, 0);
lean_inc_ref(v_modifier_4134_);
lean_dec_ref_known(v_head_4129_, 1);
v___x_4135_ = lean_apply_2(v_h__1_4124_, v_modifier_4134_, v_tail_4133_);
return v___x_4135_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_FormatType_match__1_splitter(lean_object* v_motive_4136_, lean_object* v_x_4137_, lean_object* v_h__1_4138_, lean_object* v_h__2_4139_, lean_object* v_h__3_4140_){
_start:
{
if (lean_obj_tag(v_x_4137_) == 0)
{
lean_object* v___x_4141_; lean_object* v___x_4142_; 
lean_dec(v_h__2_4139_);
lean_dec(v_h__1_4138_);
v___x_4141_ = lean_box(0);
v___x_4142_ = lean_apply_1(v_h__3_4140_, v___x_4141_);
return v___x_4142_;
}
else
{
lean_object* v_head_4143_; 
lean_dec(v_h__3_4140_);
v_head_4143_ = lean_ctor_get(v_x_4137_, 0);
lean_inc(v_head_4143_);
if (lean_obj_tag(v_head_4143_) == 0)
{
lean_object* v_tail_4144_; lean_object* v_val_4145_; lean_object* v___x_4146_; 
lean_dec(v_h__1_4138_);
v_tail_4144_ = lean_ctor_get(v_x_4137_, 1);
lean_inc(v_tail_4144_);
lean_dec_ref_known(v_x_4137_, 2);
v_val_4145_ = lean_ctor_get(v_head_4143_, 0);
lean_inc_ref(v_val_4145_);
lean_dec_ref_known(v_head_4143_, 1);
v___x_4146_ = lean_apply_2(v_h__2_4139_, v_val_4145_, v_tail_4144_);
return v___x_4146_;
}
else
{
lean_object* v_tail_4147_; lean_object* v_modifier_4148_; lean_object* v___x_4149_; 
lean_dec(v_h__2_4139_);
v_tail_4147_ = lean_ctor_get(v_x_4137_, 1);
lean_inc(v_tail_4147_);
lean_dec_ref_known(v_x_4137_, 2);
v_modifier_4148_ = lean_ctor_get(v_head_4143_, 0);
lean_inc_ref(v_modifier_4148_);
lean_dec_ref_known(v_head_4143_, 1);
v___x_4149_ = lean_apply_2(v_h__1_4138_, v_modifier_4148_, v_tail_4147_);
return v___x_4149_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(lean_object* v_date_4150_, lean_object* v_modifier_4151_, lean_object* v_data_4152_){
_start:
{
switch(lean_obj_tag(v_modifier_4151_))
{
case 0:
{
lean_object* v_y_4153_; lean_object* v_u_4154_; lean_object* v_Y_4155_; lean_object* v_D_4156_; lean_object* v_M_4157_; lean_object* v_L_4158_; lean_object* v_d_4159_; lean_object* v_Q_4160_; lean_object* v_q_4161_; lean_object* v_w_4162_; lean_object* v_W_4163_; lean_object* v_E_4164_; lean_object* v_e_4165_; lean_object* v_c_4166_; lean_object* v_F_4167_; lean_object* v_a_4168_; lean_object* v_b_4169_; lean_object* v_B_4170_; lean_object* v_h_4171_; lean_object* v_K_4172_; lean_object* v_k_4173_; lean_object* v_H_4174_; lean_object* v_m_4175_; lean_object* v_s_4176_; lean_object* v_S_4177_; lean_object* v_A_4178_; lean_object* v_n_4179_; lean_object* v_N_4180_; lean_object* v_V_4181_; lean_object* v_z_4182_; lean_object* v_zabbrev_4183_; lean_object* v_v_4184_; lean_object* v_O_4185_; lean_object* v_X_4186_; lean_object* v_x_4187_; lean_object* v_Z_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4196_; 
lean_dec_ref_known(v_modifier_4151_, 0);
v_y_4153_ = lean_ctor_get(v_date_4150_, 1);
v_u_4154_ = lean_ctor_get(v_date_4150_, 2);
v_Y_4155_ = lean_ctor_get(v_date_4150_, 3);
v_D_4156_ = lean_ctor_get(v_date_4150_, 4);
v_M_4157_ = lean_ctor_get(v_date_4150_, 5);
v_L_4158_ = lean_ctor_get(v_date_4150_, 6);
v_d_4159_ = lean_ctor_get(v_date_4150_, 7);
v_Q_4160_ = lean_ctor_get(v_date_4150_, 8);
v_q_4161_ = lean_ctor_get(v_date_4150_, 9);
v_w_4162_ = lean_ctor_get(v_date_4150_, 10);
v_W_4163_ = lean_ctor_get(v_date_4150_, 11);
v_E_4164_ = lean_ctor_get(v_date_4150_, 12);
v_e_4165_ = lean_ctor_get(v_date_4150_, 13);
v_c_4166_ = lean_ctor_get(v_date_4150_, 14);
v_F_4167_ = lean_ctor_get(v_date_4150_, 15);
v_a_4168_ = lean_ctor_get(v_date_4150_, 16);
v_b_4169_ = lean_ctor_get(v_date_4150_, 17);
v_B_4170_ = lean_ctor_get(v_date_4150_, 18);
v_h_4171_ = lean_ctor_get(v_date_4150_, 19);
v_K_4172_ = lean_ctor_get(v_date_4150_, 20);
v_k_4173_ = lean_ctor_get(v_date_4150_, 21);
v_H_4174_ = lean_ctor_get(v_date_4150_, 22);
v_m_4175_ = lean_ctor_get(v_date_4150_, 23);
v_s_4176_ = lean_ctor_get(v_date_4150_, 24);
v_S_4177_ = lean_ctor_get(v_date_4150_, 25);
v_A_4178_ = lean_ctor_get(v_date_4150_, 26);
v_n_4179_ = lean_ctor_get(v_date_4150_, 27);
v_N_4180_ = lean_ctor_get(v_date_4150_, 28);
v_V_4181_ = lean_ctor_get(v_date_4150_, 29);
v_z_4182_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_4183_ = lean_ctor_get(v_date_4150_, 31);
v_v_4184_ = lean_ctor_get(v_date_4150_, 32);
v_O_4185_ = lean_ctor_get(v_date_4150_, 33);
v_X_4186_ = lean_ctor_get(v_date_4150_, 34);
v_x_4187_ = lean_ctor_get(v_date_4150_, 35);
v_Z_4188_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_4196_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_4196_ == 0)
{
lean_object* v_unused_4197_; 
v_unused_4197_ = lean_ctor_get(v_date_4150_, 0);
lean_dec(v_unused_4197_);
v___x_4190_ = v_date_4150_;
v_isShared_4191_ = v_isSharedCheck_4196_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_Z_4188_);
lean_inc(v_x_4187_);
lean_inc(v_X_4186_);
lean_inc(v_O_4185_);
lean_inc(v_v_4184_);
lean_inc(v_zabbrev_4183_);
lean_inc(v_z_4182_);
lean_inc(v_V_4181_);
lean_inc(v_N_4180_);
lean_inc(v_n_4179_);
lean_inc(v_A_4178_);
lean_inc(v_S_4177_);
lean_inc(v_s_4176_);
lean_inc(v_m_4175_);
lean_inc(v_H_4174_);
lean_inc(v_k_4173_);
lean_inc(v_K_4172_);
lean_inc(v_h_4171_);
lean_inc(v_B_4170_);
lean_inc(v_b_4169_);
lean_inc(v_a_4168_);
lean_inc(v_F_4167_);
lean_inc(v_c_4166_);
lean_inc(v_e_4165_);
lean_inc(v_E_4164_);
lean_inc(v_W_4163_);
lean_inc(v_w_4162_);
lean_inc(v_q_4161_);
lean_inc(v_Q_4160_);
lean_inc(v_d_4159_);
lean_inc(v_L_4158_);
lean_inc(v_M_4157_);
lean_inc(v_D_4156_);
lean_inc(v_Y_4155_);
lean_inc(v_u_4154_);
lean_inc(v_y_4153_);
lean_dec(v_date_4150_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4196_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4192_; lean_object* v___x_4194_; 
v___x_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4192_, 0, v_data_4152_);
if (v_isShared_4191_ == 0)
{
lean_ctor_set(v___x_4190_, 0, v___x_4192_);
v___x_4194_ = v___x_4190_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v___x_4192_);
lean_ctor_set(v_reuseFailAlloc_4195_, 1, v_y_4153_);
lean_ctor_set(v_reuseFailAlloc_4195_, 2, v_u_4154_);
lean_ctor_set(v_reuseFailAlloc_4195_, 3, v_Y_4155_);
lean_ctor_set(v_reuseFailAlloc_4195_, 4, v_D_4156_);
lean_ctor_set(v_reuseFailAlloc_4195_, 5, v_M_4157_);
lean_ctor_set(v_reuseFailAlloc_4195_, 6, v_L_4158_);
lean_ctor_set(v_reuseFailAlloc_4195_, 7, v_d_4159_);
lean_ctor_set(v_reuseFailAlloc_4195_, 8, v_Q_4160_);
lean_ctor_set(v_reuseFailAlloc_4195_, 9, v_q_4161_);
lean_ctor_set(v_reuseFailAlloc_4195_, 10, v_w_4162_);
lean_ctor_set(v_reuseFailAlloc_4195_, 11, v_W_4163_);
lean_ctor_set(v_reuseFailAlloc_4195_, 12, v_E_4164_);
lean_ctor_set(v_reuseFailAlloc_4195_, 13, v_e_4165_);
lean_ctor_set(v_reuseFailAlloc_4195_, 14, v_c_4166_);
lean_ctor_set(v_reuseFailAlloc_4195_, 15, v_F_4167_);
lean_ctor_set(v_reuseFailAlloc_4195_, 16, v_a_4168_);
lean_ctor_set(v_reuseFailAlloc_4195_, 17, v_b_4169_);
lean_ctor_set(v_reuseFailAlloc_4195_, 18, v_B_4170_);
lean_ctor_set(v_reuseFailAlloc_4195_, 19, v_h_4171_);
lean_ctor_set(v_reuseFailAlloc_4195_, 20, v_K_4172_);
lean_ctor_set(v_reuseFailAlloc_4195_, 21, v_k_4173_);
lean_ctor_set(v_reuseFailAlloc_4195_, 22, v_H_4174_);
lean_ctor_set(v_reuseFailAlloc_4195_, 23, v_m_4175_);
lean_ctor_set(v_reuseFailAlloc_4195_, 24, v_s_4176_);
lean_ctor_set(v_reuseFailAlloc_4195_, 25, v_S_4177_);
lean_ctor_set(v_reuseFailAlloc_4195_, 26, v_A_4178_);
lean_ctor_set(v_reuseFailAlloc_4195_, 27, v_n_4179_);
lean_ctor_set(v_reuseFailAlloc_4195_, 28, v_N_4180_);
lean_ctor_set(v_reuseFailAlloc_4195_, 29, v_V_4181_);
lean_ctor_set(v_reuseFailAlloc_4195_, 30, v_z_4182_);
lean_ctor_set(v_reuseFailAlloc_4195_, 31, v_zabbrev_4183_);
lean_ctor_set(v_reuseFailAlloc_4195_, 32, v_v_4184_);
lean_ctor_set(v_reuseFailAlloc_4195_, 33, v_O_4185_);
lean_ctor_set(v_reuseFailAlloc_4195_, 34, v_X_4186_);
lean_ctor_set(v_reuseFailAlloc_4195_, 35, v_x_4187_);
lean_ctor_set(v_reuseFailAlloc_4195_, 36, v_Z_4188_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
}
case 1:
{
lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4248_; 
v_isSharedCheck_4248_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_4248_ == 0)
{
lean_object* v_unused_4249_; 
v_unused_4249_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_4249_);
v___x_4199_ = v_modifier_4151_;
v_isShared_4200_ = v_isSharedCheck_4248_;
goto v_resetjp_4198_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4248_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v_G_4201_; lean_object* v_y_4202_; lean_object* v_Y_4203_; lean_object* v_D_4204_; lean_object* v_M_4205_; lean_object* v_L_4206_; lean_object* v_d_4207_; lean_object* v_Q_4208_; lean_object* v_q_4209_; lean_object* v_w_4210_; lean_object* v_W_4211_; lean_object* v_E_4212_; lean_object* v_e_4213_; lean_object* v_c_4214_; lean_object* v_F_4215_; lean_object* v_a_4216_; lean_object* v_b_4217_; lean_object* v_B_4218_; lean_object* v_h_4219_; lean_object* v_K_4220_; lean_object* v_k_4221_; lean_object* v_H_4222_; lean_object* v_m_4223_; lean_object* v_s_4224_; lean_object* v_S_4225_; lean_object* v_A_4226_; lean_object* v_n_4227_; lean_object* v_N_4228_; lean_object* v_V_4229_; lean_object* v_z_4230_; lean_object* v_zabbrev_4231_; lean_object* v_v_4232_; lean_object* v_O_4233_; lean_object* v_X_4234_; lean_object* v_x_4235_; lean_object* v_Z_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4246_; 
v_G_4201_ = lean_ctor_get(v_date_4150_, 0);
v_y_4202_ = lean_ctor_get(v_date_4150_, 1);
v_Y_4203_ = lean_ctor_get(v_date_4150_, 3);
v_D_4204_ = lean_ctor_get(v_date_4150_, 4);
v_M_4205_ = lean_ctor_get(v_date_4150_, 5);
v_L_4206_ = lean_ctor_get(v_date_4150_, 6);
v_d_4207_ = lean_ctor_get(v_date_4150_, 7);
v_Q_4208_ = lean_ctor_get(v_date_4150_, 8);
v_q_4209_ = lean_ctor_get(v_date_4150_, 9);
v_w_4210_ = lean_ctor_get(v_date_4150_, 10);
v_W_4211_ = lean_ctor_get(v_date_4150_, 11);
v_E_4212_ = lean_ctor_get(v_date_4150_, 12);
v_e_4213_ = lean_ctor_get(v_date_4150_, 13);
v_c_4214_ = lean_ctor_get(v_date_4150_, 14);
v_F_4215_ = lean_ctor_get(v_date_4150_, 15);
v_a_4216_ = lean_ctor_get(v_date_4150_, 16);
v_b_4217_ = lean_ctor_get(v_date_4150_, 17);
v_B_4218_ = lean_ctor_get(v_date_4150_, 18);
v_h_4219_ = lean_ctor_get(v_date_4150_, 19);
v_K_4220_ = lean_ctor_get(v_date_4150_, 20);
v_k_4221_ = lean_ctor_get(v_date_4150_, 21);
v_H_4222_ = lean_ctor_get(v_date_4150_, 22);
v_m_4223_ = lean_ctor_get(v_date_4150_, 23);
v_s_4224_ = lean_ctor_get(v_date_4150_, 24);
v_S_4225_ = lean_ctor_get(v_date_4150_, 25);
v_A_4226_ = lean_ctor_get(v_date_4150_, 26);
v_n_4227_ = lean_ctor_get(v_date_4150_, 27);
v_N_4228_ = lean_ctor_get(v_date_4150_, 28);
v_V_4229_ = lean_ctor_get(v_date_4150_, 29);
v_z_4230_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_4231_ = lean_ctor_get(v_date_4150_, 31);
v_v_4232_ = lean_ctor_get(v_date_4150_, 32);
v_O_4233_ = lean_ctor_get(v_date_4150_, 33);
v_X_4234_ = lean_ctor_get(v_date_4150_, 34);
v_x_4235_ = lean_ctor_get(v_date_4150_, 35);
v_Z_4236_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_4246_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_4246_ == 0)
{
lean_object* v_unused_4247_; 
v_unused_4247_ = lean_ctor_get(v_date_4150_, 2);
lean_dec(v_unused_4247_);
v___x_4238_ = v_date_4150_;
v_isShared_4239_ = v_isSharedCheck_4246_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_Z_4236_);
lean_inc(v_x_4235_);
lean_inc(v_X_4234_);
lean_inc(v_O_4233_);
lean_inc(v_v_4232_);
lean_inc(v_zabbrev_4231_);
lean_inc(v_z_4230_);
lean_inc(v_V_4229_);
lean_inc(v_N_4228_);
lean_inc(v_n_4227_);
lean_inc(v_A_4226_);
lean_inc(v_S_4225_);
lean_inc(v_s_4224_);
lean_inc(v_m_4223_);
lean_inc(v_H_4222_);
lean_inc(v_k_4221_);
lean_inc(v_K_4220_);
lean_inc(v_h_4219_);
lean_inc(v_B_4218_);
lean_inc(v_b_4217_);
lean_inc(v_a_4216_);
lean_inc(v_F_4215_);
lean_inc(v_c_4214_);
lean_inc(v_e_4213_);
lean_inc(v_E_4212_);
lean_inc(v_W_4211_);
lean_inc(v_w_4210_);
lean_inc(v_q_4209_);
lean_inc(v_Q_4208_);
lean_inc(v_d_4207_);
lean_inc(v_L_4206_);
lean_inc(v_M_4205_);
lean_inc(v_D_4204_);
lean_inc(v_Y_4203_);
lean_inc(v_y_4202_);
lean_inc(v_G_4201_);
lean_dec(v_date_4150_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4246_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 0, v_data_4152_);
v___x_4241_ = v___x_4199_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_data_4152_);
v___x_4241_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
lean_object* v___x_4243_; 
if (v_isShared_4239_ == 0)
{
lean_ctor_set(v___x_4238_, 2, v___x_4241_);
v___x_4243_ = v___x_4238_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_G_4201_);
lean_ctor_set(v_reuseFailAlloc_4244_, 1, v_y_4202_);
lean_ctor_set(v_reuseFailAlloc_4244_, 2, v___x_4241_);
lean_ctor_set(v_reuseFailAlloc_4244_, 3, v_Y_4203_);
lean_ctor_set(v_reuseFailAlloc_4244_, 4, v_D_4204_);
lean_ctor_set(v_reuseFailAlloc_4244_, 5, v_M_4205_);
lean_ctor_set(v_reuseFailAlloc_4244_, 6, v_L_4206_);
lean_ctor_set(v_reuseFailAlloc_4244_, 7, v_d_4207_);
lean_ctor_set(v_reuseFailAlloc_4244_, 8, v_Q_4208_);
lean_ctor_set(v_reuseFailAlloc_4244_, 9, v_q_4209_);
lean_ctor_set(v_reuseFailAlloc_4244_, 10, v_w_4210_);
lean_ctor_set(v_reuseFailAlloc_4244_, 11, v_W_4211_);
lean_ctor_set(v_reuseFailAlloc_4244_, 12, v_E_4212_);
lean_ctor_set(v_reuseFailAlloc_4244_, 13, v_e_4213_);
lean_ctor_set(v_reuseFailAlloc_4244_, 14, v_c_4214_);
lean_ctor_set(v_reuseFailAlloc_4244_, 15, v_F_4215_);
lean_ctor_set(v_reuseFailAlloc_4244_, 16, v_a_4216_);
lean_ctor_set(v_reuseFailAlloc_4244_, 17, v_b_4217_);
lean_ctor_set(v_reuseFailAlloc_4244_, 18, v_B_4218_);
lean_ctor_set(v_reuseFailAlloc_4244_, 19, v_h_4219_);
lean_ctor_set(v_reuseFailAlloc_4244_, 20, v_K_4220_);
lean_ctor_set(v_reuseFailAlloc_4244_, 21, v_k_4221_);
lean_ctor_set(v_reuseFailAlloc_4244_, 22, v_H_4222_);
lean_ctor_set(v_reuseFailAlloc_4244_, 23, v_m_4223_);
lean_ctor_set(v_reuseFailAlloc_4244_, 24, v_s_4224_);
lean_ctor_set(v_reuseFailAlloc_4244_, 25, v_S_4225_);
lean_ctor_set(v_reuseFailAlloc_4244_, 26, v_A_4226_);
lean_ctor_set(v_reuseFailAlloc_4244_, 27, v_n_4227_);
lean_ctor_set(v_reuseFailAlloc_4244_, 28, v_N_4228_);
lean_ctor_set(v_reuseFailAlloc_4244_, 29, v_V_4229_);
lean_ctor_set(v_reuseFailAlloc_4244_, 30, v_z_4230_);
lean_ctor_set(v_reuseFailAlloc_4244_, 31, v_zabbrev_4231_);
lean_ctor_set(v_reuseFailAlloc_4244_, 32, v_v_4232_);
lean_ctor_set(v_reuseFailAlloc_4244_, 33, v_O_4233_);
lean_ctor_set(v_reuseFailAlloc_4244_, 34, v_X_4234_);
lean_ctor_set(v_reuseFailAlloc_4244_, 35, v_x_4235_);
lean_ctor_set(v_reuseFailAlloc_4244_, 36, v_Z_4236_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
}
case 2:
{
lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4300_; 
v_isSharedCheck_4300_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_4300_ == 0)
{
lean_object* v_unused_4301_; 
v_unused_4301_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_4301_);
v___x_4251_ = v_modifier_4151_;
v_isShared_4252_ = v_isSharedCheck_4300_;
goto v_resetjp_4250_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4300_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v_G_4253_; lean_object* v_u_4254_; lean_object* v_Y_4255_; lean_object* v_D_4256_; lean_object* v_M_4257_; lean_object* v_L_4258_; lean_object* v_d_4259_; lean_object* v_Q_4260_; lean_object* v_q_4261_; lean_object* v_w_4262_; lean_object* v_W_4263_; lean_object* v_E_4264_; lean_object* v_e_4265_; lean_object* v_c_4266_; lean_object* v_F_4267_; lean_object* v_a_4268_; lean_object* v_b_4269_; lean_object* v_B_4270_; lean_object* v_h_4271_; lean_object* v_K_4272_; lean_object* v_k_4273_; lean_object* v_H_4274_; lean_object* v_m_4275_; lean_object* v_s_4276_; lean_object* v_S_4277_; lean_object* v_A_4278_; lean_object* v_n_4279_; lean_object* v_N_4280_; lean_object* v_V_4281_; lean_object* v_z_4282_; lean_object* v_zabbrev_4283_; lean_object* v_v_4284_; lean_object* v_O_4285_; lean_object* v_X_4286_; lean_object* v_x_4287_; lean_object* v_Z_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4298_; 
v_G_4253_ = lean_ctor_get(v_date_4150_, 0);
v_u_4254_ = lean_ctor_get(v_date_4150_, 2);
v_Y_4255_ = lean_ctor_get(v_date_4150_, 3);
v_D_4256_ = lean_ctor_get(v_date_4150_, 4);
v_M_4257_ = lean_ctor_get(v_date_4150_, 5);
v_L_4258_ = lean_ctor_get(v_date_4150_, 6);
v_d_4259_ = lean_ctor_get(v_date_4150_, 7);
v_Q_4260_ = lean_ctor_get(v_date_4150_, 8);
v_q_4261_ = lean_ctor_get(v_date_4150_, 9);
v_w_4262_ = lean_ctor_get(v_date_4150_, 10);
v_W_4263_ = lean_ctor_get(v_date_4150_, 11);
v_E_4264_ = lean_ctor_get(v_date_4150_, 12);
v_e_4265_ = lean_ctor_get(v_date_4150_, 13);
v_c_4266_ = lean_ctor_get(v_date_4150_, 14);
v_F_4267_ = lean_ctor_get(v_date_4150_, 15);
v_a_4268_ = lean_ctor_get(v_date_4150_, 16);
v_b_4269_ = lean_ctor_get(v_date_4150_, 17);
v_B_4270_ = lean_ctor_get(v_date_4150_, 18);
v_h_4271_ = lean_ctor_get(v_date_4150_, 19);
v_K_4272_ = lean_ctor_get(v_date_4150_, 20);
v_k_4273_ = lean_ctor_get(v_date_4150_, 21);
v_H_4274_ = lean_ctor_get(v_date_4150_, 22);
v_m_4275_ = lean_ctor_get(v_date_4150_, 23);
v_s_4276_ = lean_ctor_get(v_date_4150_, 24);
v_S_4277_ = lean_ctor_get(v_date_4150_, 25);
v_A_4278_ = lean_ctor_get(v_date_4150_, 26);
v_n_4279_ = lean_ctor_get(v_date_4150_, 27);
v_N_4280_ = lean_ctor_get(v_date_4150_, 28);
v_V_4281_ = lean_ctor_get(v_date_4150_, 29);
v_z_4282_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_4283_ = lean_ctor_get(v_date_4150_, 31);
v_v_4284_ = lean_ctor_get(v_date_4150_, 32);
v_O_4285_ = lean_ctor_get(v_date_4150_, 33);
v_X_4286_ = lean_ctor_get(v_date_4150_, 34);
v_x_4287_ = lean_ctor_get(v_date_4150_, 35);
v_Z_4288_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_4298_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_4298_ == 0)
{
lean_object* v_unused_4299_; 
v_unused_4299_ = lean_ctor_get(v_date_4150_, 1);
lean_dec(v_unused_4299_);
v___x_4290_ = v_date_4150_;
v_isShared_4291_ = v_isSharedCheck_4298_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_Z_4288_);
lean_inc(v_x_4287_);
lean_inc(v_X_4286_);
lean_inc(v_O_4285_);
lean_inc(v_v_4284_);
lean_inc(v_zabbrev_4283_);
lean_inc(v_z_4282_);
lean_inc(v_V_4281_);
lean_inc(v_N_4280_);
lean_inc(v_n_4279_);
lean_inc(v_A_4278_);
lean_inc(v_S_4277_);
lean_inc(v_s_4276_);
lean_inc(v_m_4275_);
lean_inc(v_H_4274_);
lean_inc(v_k_4273_);
lean_inc(v_K_4272_);
lean_inc(v_h_4271_);
lean_inc(v_B_4270_);
lean_inc(v_b_4269_);
lean_inc(v_a_4268_);
lean_inc(v_F_4267_);
lean_inc(v_c_4266_);
lean_inc(v_e_4265_);
lean_inc(v_E_4264_);
lean_inc(v_W_4263_);
lean_inc(v_w_4262_);
lean_inc(v_q_4261_);
lean_inc(v_Q_4260_);
lean_inc(v_d_4259_);
lean_inc(v_L_4258_);
lean_inc(v_M_4257_);
lean_inc(v_D_4256_);
lean_inc(v_Y_4255_);
lean_inc(v_u_4254_);
lean_inc(v_G_4253_);
lean_dec(v_date_4150_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4298_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4293_; 
if (v_isShared_4252_ == 0)
{
lean_ctor_set_tag(v___x_4251_, 1);
lean_ctor_set(v___x_4251_, 0, v_data_4152_);
v___x_4293_ = v___x_4251_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_data_4152_);
v___x_4293_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
lean_object* v___x_4295_; 
if (v_isShared_4291_ == 0)
{
lean_ctor_set(v___x_4290_, 1, v___x_4293_);
v___x_4295_ = v___x_4290_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_G_4253_);
lean_ctor_set(v_reuseFailAlloc_4296_, 1, v___x_4293_);
lean_ctor_set(v_reuseFailAlloc_4296_, 2, v_u_4254_);
lean_ctor_set(v_reuseFailAlloc_4296_, 3, v_Y_4255_);
lean_ctor_set(v_reuseFailAlloc_4296_, 4, v_D_4256_);
lean_ctor_set(v_reuseFailAlloc_4296_, 5, v_M_4257_);
lean_ctor_set(v_reuseFailAlloc_4296_, 6, v_L_4258_);
lean_ctor_set(v_reuseFailAlloc_4296_, 7, v_d_4259_);
lean_ctor_set(v_reuseFailAlloc_4296_, 8, v_Q_4260_);
lean_ctor_set(v_reuseFailAlloc_4296_, 9, v_q_4261_);
lean_ctor_set(v_reuseFailAlloc_4296_, 10, v_w_4262_);
lean_ctor_set(v_reuseFailAlloc_4296_, 11, v_W_4263_);
lean_ctor_set(v_reuseFailAlloc_4296_, 12, v_E_4264_);
lean_ctor_set(v_reuseFailAlloc_4296_, 13, v_e_4265_);
lean_ctor_set(v_reuseFailAlloc_4296_, 14, v_c_4266_);
lean_ctor_set(v_reuseFailAlloc_4296_, 15, v_F_4267_);
lean_ctor_set(v_reuseFailAlloc_4296_, 16, v_a_4268_);
lean_ctor_set(v_reuseFailAlloc_4296_, 17, v_b_4269_);
lean_ctor_set(v_reuseFailAlloc_4296_, 18, v_B_4270_);
lean_ctor_set(v_reuseFailAlloc_4296_, 19, v_h_4271_);
lean_ctor_set(v_reuseFailAlloc_4296_, 20, v_K_4272_);
lean_ctor_set(v_reuseFailAlloc_4296_, 21, v_k_4273_);
lean_ctor_set(v_reuseFailAlloc_4296_, 22, v_H_4274_);
lean_ctor_set(v_reuseFailAlloc_4296_, 23, v_m_4275_);
lean_ctor_set(v_reuseFailAlloc_4296_, 24, v_s_4276_);
lean_ctor_set(v_reuseFailAlloc_4296_, 25, v_S_4277_);
lean_ctor_set(v_reuseFailAlloc_4296_, 26, v_A_4278_);
lean_ctor_set(v_reuseFailAlloc_4296_, 27, v_n_4279_);
lean_ctor_set(v_reuseFailAlloc_4296_, 28, v_N_4280_);
lean_ctor_set(v_reuseFailAlloc_4296_, 29, v_V_4281_);
lean_ctor_set(v_reuseFailAlloc_4296_, 30, v_z_4282_);
lean_ctor_set(v_reuseFailAlloc_4296_, 31, v_zabbrev_4283_);
lean_ctor_set(v_reuseFailAlloc_4296_, 32, v_v_4284_);
lean_ctor_set(v_reuseFailAlloc_4296_, 33, v_O_4285_);
lean_ctor_set(v_reuseFailAlloc_4296_, 34, v_X_4286_);
lean_ctor_set(v_reuseFailAlloc_4296_, 35, v_x_4287_);
lean_ctor_set(v_reuseFailAlloc_4296_, 36, v_Z_4288_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
return v___x_4295_;
}
}
}
}
}
case 3:
{
lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4352_; 
v_isSharedCheck_4352_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_4352_ == 0)
{
lean_object* v_unused_4353_; 
v_unused_4353_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_4353_);
v___x_4303_ = v_modifier_4151_;
v_isShared_4304_ = v_isSharedCheck_4352_;
goto v_resetjp_4302_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4352_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v_G_4305_; lean_object* v_y_4306_; lean_object* v_u_4307_; lean_object* v_Y_4308_; lean_object* v_M_4309_; lean_object* v_L_4310_; lean_object* v_d_4311_; lean_object* v_Q_4312_; lean_object* v_q_4313_; lean_object* v_w_4314_; lean_object* v_W_4315_; lean_object* v_E_4316_; lean_object* v_e_4317_; lean_object* v_c_4318_; lean_object* v_F_4319_; lean_object* v_a_4320_; lean_object* v_b_4321_; lean_object* v_B_4322_; lean_object* v_h_4323_; lean_object* v_K_4324_; lean_object* v_k_4325_; lean_object* v_H_4326_; lean_object* v_m_4327_; lean_object* v_s_4328_; lean_object* v_S_4329_; lean_object* v_A_4330_; lean_object* v_n_4331_; lean_object* v_N_4332_; lean_object* v_V_4333_; lean_object* v_z_4334_; lean_object* v_zabbrev_4335_; lean_object* v_v_4336_; lean_object* v_O_4337_; lean_object* v_X_4338_; lean_object* v_x_4339_; lean_object* v_Z_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4350_; 
v_G_4305_ = lean_ctor_get(v_date_4150_, 0);
v_y_4306_ = lean_ctor_get(v_date_4150_, 1);
v_u_4307_ = lean_ctor_get(v_date_4150_, 2);
v_Y_4308_ = lean_ctor_get(v_date_4150_, 3);
v_M_4309_ = lean_ctor_get(v_date_4150_, 5);
v_L_4310_ = lean_ctor_get(v_date_4150_, 6);
v_d_4311_ = lean_ctor_get(v_date_4150_, 7);
v_Q_4312_ = lean_ctor_get(v_date_4150_, 8);
v_q_4313_ = lean_ctor_get(v_date_4150_, 9);
v_w_4314_ = lean_ctor_get(v_date_4150_, 10);
v_W_4315_ = lean_ctor_get(v_date_4150_, 11);
v_E_4316_ = lean_ctor_get(v_date_4150_, 12);
v_e_4317_ = lean_ctor_get(v_date_4150_, 13);
v_c_4318_ = lean_ctor_get(v_date_4150_, 14);
v_F_4319_ = lean_ctor_get(v_date_4150_, 15);
v_a_4320_ = lean_ctor_get(v_date_4150_, 16);
v_b_4321_ = lean_ctor_get(v_date_4150_, 17);
v_B_4322_ = lean_ctor_get(v_date_4150_, 18);
v_h_4323_ = lean_ctor_get(v_date_4150_, 19);
v_K_4324_ = lean_ctor_get(v_date_4150_, 20);
v_k_4325_ = lean_ctor_get(v_date_4150_, 21);
v_H_4326_ = lean_ctor_get(v_date_4150_, 22);
v_m_4327_ = lean_ctor_get(v_date_4150_, 23);
v_s_4328_ = lean_ctor_get(v_date_4150_, 24);
v_S_4329_ = lean_ctor_get(v_date_4150_, 25);
v_A_4330_ = lean_ctor_get(v_date_4150_, 26);
v_n_4331_ = lean_ctor_get(v_date_4150_, 27);
v_N_4332_ = lean_ctor_get(v_date_4150_, 28);
v_V_4333_ = lean_ctor_get(v_date_4150_, 29);
v_z_4334_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_4335_ = lean_ctor_get(v_date_4150_, 31);
v_v_4336_ = lean_ctor_get(v_date_4150_, 32);
v_O_4337_ = lean_ctor_get(v_date_4150_, 33);
v_X_4338_ = lean_ctor_get(v_date_4150_, 34);
v_x_4339_ = lean_ctor_get(v_date_4150_, 35);
v_Z_4340_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_4350_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_4350_ == 0)
{
lean_object* v_unused_4351_; 
v_unused_4351_ = lean_ctor_get(v_date_4150_, 4);
lean_dec(v_unused_4351_);
v___x_4342_ = v_date_4150_;
v_isShared_4343_ = v_isSharedCheck_4350_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_Z_4340_);
lean_inc(v_x_4339_);
lean_inc(v_X_4338_);
lean_inc(v_O_4337_);
lean_inc(v_v_4336_);
lean_inc(v_zabbrev_4335_);
lean_inc(v_z_4334_);
lean_inc(v_V_4333_);
lean_inc(v_N_4332_);
lean_inc(v_n_4331_);
lean_inc(v_A_4330_);
lean_inc(v_S_4329_);
lean_inc(v_s_4328_);
lean_inc(v_m_4327_);
lean_inc(v_H_4326_);
lean_inc(v_k_4325_);
lean_inc(v_K_4324_);
lean_inc(v_h_4323_);
lean_inc(v_B_4322_);
lean_inc(v_b_4321_);
lean_inc(v_a_4320_);
lean_inc(v_F_4319_);
lean_inc(v_c_4318_);
lean_inc(v_e_4317_);
lean_inc(v_E_4316_);
lean_inc(v_W_4315_);
lean_inc(v_w_4314_);
lean_inc(v_q_4313_);
lean_inc(v_Q_4312_);
lean_inc(v_d_4311_);
lean_inc(v_L_4310_);
lean_inc(v_M_4309_);
lean_inc(v_Y_4308_);
lean_inc(v_u_4307_);
lean_inc(v_y_4306_);
lean_inc(v_G_4305_);
lean_dec(v_date_4150_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4350_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4345_; 
if (v_isShared_4304_ == 0)
{
lean_ctor_set_tag(v___x_4303_, 1);
lean_ctor_set(v___x_4303_, 0, v_data_4152_);
v___x_4345_ = v___x_4303_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_data_4152_);
v___x_4345_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
lean_object* v___x_4347_; 
if (v_isShared_4343_ == 0)
{
lean_ctor_set(v___x_4342_, 4, v___x_4345_);
v___x_4347_ = v___x_4342_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_G_4305_);
lean_ctor_set(v_reuseFailAlloc_4348_, 1, v_y_4306_);
lean_ctor_set(v_reuseFailAlloc_4348_, 2, v_u_4307_);
lean_ctor_set(v_reuseFailAlloc_4348_, 3, v_Y_4308_);
lean_ctor_set(v_reuseFailAlloc_4348_, 4, v___x_4345_);
lean_ctor_set(v_reuseFailAlloc_4348_, 5, v_M_4309_);
lean_ctor_set(v_reuseFailAlloc_4348_, 6, v_L_4310_);
lean_ctor_set(v_reuseFailAlloc_4348_, 7, v_d_4311_);
lean_ctor_set(v_reuseFailAlloc_4348_, 8, v_Q_4312_);
lean_ctor_set(v_reuseFailAlloc_4348_, 9, v_q_4313_);
lean_ctor_set(v_reuseFailAlloc_4348_, 10, v_w_4314_);
lean_ctor_set(v_reuseFailAlloc_4348_, 11, v_W_4315_);
lean_ctor_set(v_reuseFailAlloc_4348_, 12, v_E_4316_);
lean_ctor_set(v_reuseFailAlloc_4348_, 13, v_e_4317_);
lean_ctor_set(v_reuseFailAlloc_4348_, 14, v_c_4318_);
lean_ctor_set(v_reuseFailAlloc_4348_, 15, v_F_4319_);
lean_ctor_set(v_reuseFailAlloc_4348_, 16, v_a_4320_);
lean_ctor_set(v_reuseFailAlloc_4348_, 17, v_b_4321_);
lean_ctor_set(v_reuseFailAlloc_4348_, 18, v_B_4322_);
lean_ctor_set(v_reuseFailAlloc_4348_, 19, v_h_4323_);
lean_ctor_set(v_reuseFailAlloc_4348_, 20, v_K_4324_);
lean_ctor_set(v_reuseFailAlloc_4348_, 21, v_k_4325_);
lean_ctor_set(v_reuseFailAlloc_4348_, 22, v_H_4326_);
lean_ctor_set(v_reuseFailAlloc_4348_, 23, v_m_4327_);
lean_ctor_set(v_reuseFailAlloc_4348_, 24, v_s_4328_);
lean_ctor_set(v_reuseFailAlloc_4348_, 25, v_S_4329_);
lean_ctor_set(v_reuseFailAlloc_4348_, 26, v_A_4330_);
lean_ctor_set(v_reuseFailAlloc_4348_, 27, v_n_4331_);
lean_ctor_set(v_reuseFailAlloc_4348_, 28, v_N_4332_);
lean_ctor_set(v_reuseFailAlloc_4348_, 29, v_V_4333_);
lean_ctor_set(v_reuseFailAlloc_4348_, 30, v_z_4334_);
lean_ctor_set(v_reuseFailAlloc_4348_, 31, v_zabbrev_4335_);
lean_ctor_set(v_reuseFailAlloc_4348_, 32, v_v_4336_);
lean_ctor_set(v_reuseFailAlloc_4348_, 33, v_O_4337_);
lean_ctor_set(v_reuseFailAlloc_4348_, 34, v_X_4338_);
lean_ctor_set(v_reuseFailAlloc_4348_, 35, v_x_4339_);
lean_ctor_set(v_reuseFailAlloc_4348_, 36, v_Z_4340_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
return v___x_4347_;
}
}
}
}
}
case 4:
{
lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4404_; 
v_isSharedCheck_4404_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_4404_ == 0)
{
lean_object* v_unused_4405_; 
v_unused_4405_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_4405_);
v___x_4355_ = v_modifier_4151_;
v_isShared_4356_ = v_isSharedCheck_4404_;
goto v_resetjp_4354_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4404_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v_G_4357_; lean_object* v_y_4358_; lean_object* v_u_4359_; lean_object* v_Y_4360_; lean_object* v_D_4361_; lean_object* v_L_4362_; lean_object* v_d_4363_; lean_object* v_Q_4364_; lean_object* v_q_4365_; lean_object* v_w_4366_; lean_object* v_W_4367_; lean_object* v_E_4368_; lean_object* v_e_4369_; lean_object* v_c_4370_; lean_object* v_F_4371_; lean_object* v_a_4372_; lean_object* v_b_4373_; lean_object* v_B_4374_; lean_object* v_h_4375_; lean_object* v_K_4376_; lean_object* v_k_4377_; lean_object* v_H_4378_; lean_object* v_m_4379_; lean_object* v_s_4380_; lean_object* v_S_4381_; lean_object* v_A_4382_; lean_object* v_n_4383_; lean_object* v_N_4384_; lean_object* v_V_4385_; lean_object* v_z_4386_; lean_object* v_zabbrev_4387_; lean_object* v_v_4388_; lean_object* v_O_4389_; lean_object* v_X_4390_; lean_object* v_x_4391_; lean_object* v_Z_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4402_; 
v_G_4357_ = lean_ctor_get(v_date_4150_, 0);
v_y_4358_ = lean_ctor_get(v_date_4150_, 1);
v_u_4359_ = lean_ctor_get(v_date_4150_, 2);
v_Y_4360_ = lean_ctor_get(v_date_4150_, 3);
v_D_4361_ = lean_ctor_get(v_date_4150_, 4);
v_L_4362_ = lean_ctor_get(v_date_4150_, 6);
v_d_4363_ = lean_ctor_get(v_date_4150_, 7);
v_Q_4364_ = lean_ctor_get(v_date_4150_, 8);
v_q_4365_ = lean_ctor_get(v_date_4150_, 9);
v_w_4366_ = lean_ctor_get(v_date_4150_, 10);
v_W_4367_ = lean_ctor_get(v_date_4150_, 11);
v_E_4368_ = lean_ctor_get(v_date_4150_, 12);
v_e_4369_ = lean_ctor_get(v_date_4150_, 13);
v_c_4370_ = lean_ctor_get(v_date_4150_, 14);
v_F_4371_ = lean_ctor_get(v_date_4150_, 15);
v_a_4372_ = lean_ctor_get(v_date_4150_, 16);
v_b_4373_ = lean_ctor_get(v_date_4150_, 17);
v_B_4374_ = lean_ctor_get(v_date_4150_, 18);
v_h_4375_ = lean_ctor_get(v_date_4150_, 19);
v_K_4376_ = lean_ctor_get(v_date_4150_, 20);
v_k_4377_ = lean_ctor_get(v_date_4150_, 21);
v_H_4378_ = lean_ctor_get(v_date_4150_, 22);
v_m_4379_ = lean_ctor_get(v_date_4150_, 23);
v_s_4380_ = lean_ctor_get(v_date_4150_, 24);
v_S_4381_ = lean_ctor_get(v_date_4150_, 25);
v_A_4382_ = lean_ctor_get(v_date_4150_, 26);
v_n_4383_ = lean_ctor_get(v_date_4150_, 27);
v_N_4384_ = lean_ctor_get(v_date_4150_, 28);
v_V_4385_ = lean_ctor_get(v_date_4150_, 29);
v_z_4386_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_4387_ = lean_ctor_get(v_date_4150_, 31);
v_v_4388_ = lean_ctor_get(v_date_4150_, 32);
v_O_4389_ = lean_ctor_get(v_date_4150_, 33);
v_X_4390_ = lean_ctor_get(v_date_4150_, 34);
v_x_4391_ = lean_ctor_get(v_date_4150_, 35);
v_Z_4392_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_4402_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_4402_ == 0)
{
lean_object* v_unused_4403_; 
v_unused_4403_ = lean_ctor_get(v_date_4150_, 5);
lean_dec(v_unused_4403_);
v___x_4394_ = v_date_4150_;
v_isShared_4395_ = v_isSharedCheck_4402_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_Z_4392_);
lean_inc(v_x_4391_);
lean_inc(v_X_4390_);
lean_inc(v_O_4389_);
lean_inc(v_v_4388_);
lean_inc(v_zabbrev_4387_);
lean_inc(v_z_4386_);
lean_inc(v_V_4385_);
lean_inc(v_N_4384_);
lean_inc(v_n_4383_);
lean_inc(v_A_4382_);
lean_inc(v_S_4381_);
lean_inc(v_s_4380_);
lean_inc(v_m_4379_);
lean_inc(v_H_4378_);
lean_inc(v_k_4377_);
lean_inc(v_K_4376_);
lean_inc(v_h_4375_);
lean_inc(v_B_4374_);
lean_inc(v_b_4373_);
lean_inc(v_a_4372_);
lean_inc(v_F_4371_);
lean_inc(v_c_4370_);
lean_inc(v_e_4369_);
lean_inc(v_E_4368_);
lean_inc(v_W_4367_);
lean_inc(v_w_4366_);
lean_inc(v_q_4365_);
lean_inc(v_Q_4364_);
lean_inc(v_d_4363_);
lean_inc(v_L_4362_);
lean_inc(v_D_4361_);
lean_inc(v_Y_4360_);
lean_inc(v_u_4359_);
lean_inc(v_y_4358_);
lean_inc(v_G_4357_);
lean_dec(v_date_4150_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4402_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4397_; 
if (v_isShared_4356_ == 0)
{
lean_ctor_set_tag(v___x_4355_, 1);
lean_ctor_set(v___x_4355_, 0, v_data_4152_);
v___x_4397_ = v___x_4355_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_data_4152_);
v___x_4397_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
lean_object* v___x_4399_; 
if (v_isShared_4395_ == 0)
{
lean_ctor_set(v___x_4394_, 5, v___x_4397_);
v___x_4399_ = v___x_4394_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_G_4357_);
lean_ctor_set(v_reuseFailAlloc_4400_, 1, v_y_4358_);
lean_ctor_set(v_reuseFailAlloc_4400_, 2, v_u_4359_);
lean_ctor_set(v_reuseFailAlloc_4400_, 3, v_Y_4360_);
lean_ctor_set(v_reuseFailAlloc_4400_, 4, v_D_4361_);
lean_ctor_set(v_reuseFailAlloc_4400_, 5, v___x_4397_);
lean_ctor_set(v_reuseFailAlloc_4400_, 6, v_L_4362_);
lean_ctor_set(v_reuseFailAlloc_4400_, 7, v_d_4363_);
lean_ctor_set(v_reuseFailAlloc_4400_, 8, v_Q_4364_);
lean_ctor_set(v_reuseFailAlloc_4400_, 9, v_q_4365_);
lean_ctor_set(v_reuseFailAlloc_4400_, 10, v_w_4366_);
lean_ctor_set(v_reuseFailAlloc_4400_, 11, v_W_4367_);
lean_ctor_set(v_reuseFailAlloc_4400_, 12, v_E_4368_);
lean_ctor_set(v_reuseFailAlloc_4400_, 13, v_e_4369_);
lean_ctor_set(v_reuseFailAlloc_4400_, 14, v_c_4370_);
lean_ctor_set(v_reuseFailAlloc_4400_, 15, v_F_4371_);
lean_ctor_set(v_reuseFailAlloc_4400_, 16, v_a_4372_);
lean_ctor_set(v_reuseFailAlloc_4400_, 17, v_b_4373_);
lean_ctor_set(v_reuseFailAlloc_4400_, 18, v_B_4374_);
lean_ctor_set(v_reuseFailAlloc_4400_, 19, v_h_4375_);
lean_ctor_set(v_reuseFailAlloc_4400_, 20, v_K_4376_);
lean_ctor_set(v_reuseFailAlloc_4400_, 21, v_k_4377_);
lean_ctor_set(v_reuseFailAlloc_4400_, 22, v_H_4378_);
lean_ctor_set(v_reuseFailAlloc_4400_, 23, v_m_4379_);
lean_ctor_set(v_reuseFailAlloc_4400_, 24, v_s_4380_);
lean_ctor_set(v_reuseFailAlloc_4400_, 25, v_S_4381_);
lean_ctor_set(v_reuseFailAlloc_4400_, 26, v_A_4382_);
lean_ctor_set(v_reuseFailAlloc_4400_, 27, v_n_4383_);
lean_ctor_set(v_reuseFailAlloc_4400_, 28, v_N_4384_);
lean_ctor_set(v_reuseFailAlloc_4400_, 29, v_V_4385_);
lean_ctor_set(v_reuseFailAlloc_4400_, 30, v_z_4386_);
lean_ctor_set(v_reuseFailAlloc_4400_, 31, v_zabbrev_4387_);
lean_ctor_set(v_reuseFailAlloc_4400_, 32, v_v_4388_);
lean_ctor_set(v_reuseFailAlloc_4400_, 33, v_O_4389_);
lean_ctor_set(v_reuseFailAlloc_4400_, 34, v_X_4390_);
lean_ctor_set(v_reuseFailAlloc_4400_, 35, v_x_4391_);
lean_ctor_set(v_reuseFailAlloc_4400_, 36, v_Z_4392_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
return v___x_4399_;
}
}
}
}
}
case 5:
{
lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4456_; 
v_isSharedCheck_4456_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_4456_ == 0)
{
lean_object* v_unused_4457_; 
v_unused_4457_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_4457_);
v___x_4407_ = v_modifier_4151_;
v_isShared_4408_ = v_isSharedCheck_4456_;
goto v_resetjp_4406_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4456_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v_G_4409_; lean_object* v_y_4410_; lean_object* v_u_4411_; lean_object* v_Y_4412_; lean_object* v_D_4413_; lean_object* v_M_4414_; lean_object* v_d_4415_; lean_object* v_Q_4416_; lean_object* v_q_4417_; lean_object* v_w_4418_; lean_object* v_W_4419_; lean_object* v_E_4420_; lean_object* v_e_4421_; lean_object* v_c_4422_; lean_object* v_F_4423_; lean_object* v_a_4424_; lean_object* v_b_4425_; lean_object* v_B_4426_; lean_object* v_h_4427_; lean_object* v_K_4428_; lean_object* v_k_4429_; lean_object* v_H_4430_; lean_object* v_m_4431_; lean_object* v_s_4432_; lean_object* v_S_4433_; lean_object* v_A_4434_; lean_object* v_n_4435_; lean_object* v_N_4436_; lean_object* v_V_4437_; lean_object* v_z_4438_; lean_object* v_zabbrev_4439_; lean_object* v_v_4440_; lean_object* v_O_4441_; lean_object* v_X_4442_; lean_object* v_x_4443_; lean_object* v_Z_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4454_; 
v_G_4409_ = lean_ctor_get(v_date_4150_, 0);
v_y_4410_ = lean_ctor_get(v_date_4150_, 1);
v_u_4411_ = lean_ctor_get(v_date_4150_, 2);
v_Y_4412_ = lean_ctor_get(v_date_4150_, 3);
v_D_4413_ = lean_ctor_get(v_date_4150_, 4);
v_M_4414_ = lean_ctor_get(v_date_4150_, 5);
v_d_4415_ = lean_ctor_get(v_date_4150_, 7);
v_Q_4416_ = lean_ctor_get(v_date_4150_, 8);
v_q_4417_ = lean_ctor_get(v_date_4150_, 9);
v_w_4418_ = lean_ctor_get(v_date_4150_, 10);
v_W_4419_ = lean_ctor_get(v_date_4150_, 11);
v_E_4420_ = lean_ctor_get(v_date_4150_, 12);
v_e_4421_ = lean_ctor_get(v_date_4150_, 13);
v_c_4422_ = lean_ctor_get(v_date_4150_, 14);
v_F_4423_ = lean_ctor_get(v_date_4150_, 15);
v_a_4424_ = lean_ctor_get(v_date_4150_, 16);
v_b_4425_ = lean_ctor_get(v_date_4150_, 17);
v_B_4426_ = lean_ctor_get(v_date_4150_, 18);
v_h_4427_ = lean_ctor_get(v_date_4150_, 19);
v_K_4428_ = lean_ctor_get(v_date_4150_, 20);
v_k_4429_ = lean_ctor_get(v_date_4150_, 21);
v_H_4430_ = lean_ctor_get(v_date_4150_, 22);
v_m_4431_ = lean_ctor_get(v_date_4150_, 23);
v_s_4432_ = lean_ctor_get(v_date_4150_, 24);
v_S_4433_ = lean_ctor_get(v_date_4150_, 25);
v_A_4434_ = lean_ctor_get(v_date_4150_, 26);
v_n_4435_ = lean_ctor_get(v_date_4150_, 27);
v_N_4436_ = lean_ctor_get(v_date_4150_, 28);
v_V_4437_ = lean_ctor_get(v_date_4150_, 29);
v_z_4438_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_4439_ = lean_ctor_get(v_date_4150_, 31);
v_v_4440_ = lean_ctor_get(v_date_4150_, 32);
v_O_4441_ = lean_ctor_get(v_date_4150_, 33);
v_X_4442_ = lean_ctor_get(v_date_4150_, 34);
v_x_4443_ = lean_ctor_get(v_date_4150_, 35);
v_Z_4444_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_4454_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_4454_ == 0)
{
lean_object* v_unused_4455_; 
v_unused_4455_ = lean_ctor_get(v_date_4150_, 6);
lean_dec(v_unused_4455_);
v___x_4446_ = v_date_4150_;
v_isShared_4447_ = v_isSharedCheck_4454_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_Z_4444_);
lean_inc(v_x_4443_);
lean_inc(v_X_4442_);
lean_inc(v_O_4441_);
lean_inc(v_v_4440_);
lean_inc(v_zabbrev_4439_);
lean_inc(v_z_4438_);
lean_inc(v_V_4437_);
lean_inc(v_N_4436_);
lean_inc(v_n_4435_);
lean_inc(v_A_4434_);
lean_inc(v_S_4433_);
lean_inc(v_s_4432_);
lean_inc(v_m_4431_);
lean_inc(v_H_4430_);
lean_inc(v_k_4429_);
lean_inc(v_K_4428_);
lean_inc(v_h_4427_);
lean_inc(v_B_4426_);
lean_inc(v_b_4425_);
lean_inc(v_a_4424_);
lean_inc(v_F_4423_);
lean_inc(v_c_4422_);
lean_inc(v_e_4421_);
lean_inc(v_E_4420_);
lean_inc(v_W_4419_);
lean_inc(v_w_4418_);
lean_inc(v_q_4417_);
lean_inc(v_Q_4416_);
lean_inc(v_d_4415_);
lean_inc(v_M_4414_);
lean_inc(v_D_4413_);
lean_inc(v_Y_4412_);
lean_inc(v_u_4411_);
lean_inc(v_y_4410_);
lean_inc(v_G_4409_);
lean_dec(v_date_4150_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4454_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4449_; 
if (v_isShared_4408_ == 0)
{
lean_ctor_set_tag(v___x_4407_, 1);
lean_ctor_set(v___x_4407_, 0, v_data_4152_);
v___x_4449_ = v___x_4407_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_data_4152_);
v___x_4449_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
lean_object* v___x_4451_; 
if (v_isShared_4447_ == 0)
{
lean_ctor_set(v___x_4446_, 6, v___x_4449_);
v___x_4451_ = v___x_4446_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_G_4409_);
lean_ctor_set(v_reuseFailAlloc_4452_, 1, v_y_4410_);
lean_ctor_set(v_reuseFailAlloc_4452_, 2, v_u_4411_);
lean_ctor_set(v_reuseFailAlloc_4452_, 3, v_Y_4412_);
lean_ctor_set(v_reuseFailAlloc_4452_, 4, v_D_4413_);
lean_ctor_set(v_reuseFailAlloc_4452_, 5, v_M_4414_);
lean_ctor_set(v_reuseFailAlloc_4452_, 6, v___x_4449_);
lean_ctor_set(v_reuseFailAlloc_4452_, 7, v_d_4415_);
lean_ctor_set(v_reuseFailAlloc_4452_, 8, v_Q_4416_);
lean_ctor_set(v_reuseFailAlloc_4452_, 9, v_q_4417_);
lean_ctor_set(v_reuseFailAlloc_4452_, 10, v_w_4418_);
lean_ctor_set(v_reuseFailAlloc_4452_, 11, v_W_4419_);
lean_ctor_set(v_reuseFailAlloc_4452_, 12, v_E_4420_);
lean_ctor_set(v_reuseFailAlloc_4452_, 13, v_e_4421_);
lean_ctor_set(v_reuseFailAlloc_4452_, 14, v_c_4422_);
lean_ctor_set(v_reuseFailAlloc_4452_, 15, v_F_4423_);
lean_ctor_set(v_reuseFailAlloc_4452_, 16, v_a_4424_);
lean_ctor_set(v_reuseFailAlloc_4452_, 17, v_b_4425_);
lean_ctor_set(v_reuseFailAlloc_4452_, 18, v_B_4426_);
lean_ctor_set(v_reuseFailAlloc_4452_, 19, v_h_4427_);
lean_ctor_set(v_reuseFailAlloc_4452_, 20, v_K_4428_);
lean_ctor_set(v_reuseFailAlloc_4452_, 21, v_k_4429_);
lean_ctor_set(v_reuseFailAlloc_4452_, 22, v_H_4430_);
lean_ctor_set(v_reuseFailAlloc_4452_, 23, v_m_4431_);
lean_ctor_set(v_reuseFailAlloc_4452_, 24, v_s_4432_);
lean_ctor_set(v_reuseFailAlloc_4452_, 25, v_S_4433_);
lean_ctor_set(v_reuseFailAlloc_4452_, 26, v_A_4434_);
lean_ctor_set(v_reuseFailAlloc_4452_, 27, v_n_4435_);
lean_ctor_set(v_reuseFailAlloc_4452_, 28, v_N_4436_);
lean_ctor_set(v_reuseFailAlloc_4452_, 29, v_V_4437_);
lean_ctor_set(v_reuseFailAlloc_4452_, 30, v_z_4438_);
lean_ctor_set(v_reuseFailAlloc_4452_, 31, v_zabbrev_4439_);
lean_ctor_set(v_reuseFailAlloc_4452_, 32, v_v_4440_);
lean_ctor_set(v_reuseFailAlloc_4452_, 33, v_O_4441_);
lean_ctor_set(v_reuseFailAlloc_4452_, 34, v_X_4442_);
lean_ctor_set(v_reuseFailAlloc_4452_, 35, v_x_4443_);
lean_ctor_set(v_reuseFailAlloc_4452_, 36, v_Z_4444_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
return v___x_4451_;
}
}
}
}
}
case 6:
{
lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4508_; 
v_isSharedCheck_4508_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_4508_ == 0)
{
lean_object* v_unused_4509_; 
v_unused_4509_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_4509_);
v___x_4459_ = v_modifier_4151_;
v_isShared_4460_ = v_isSharedCheck_4508_;
goto v_resetjp_4458_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4508_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v_G_4461_; lean_object* v_y_4462_; lean_object* v_u_4463_; lean_object* v_Y_4464_; lean_object* v_D_4465_; lean_object* v_M_4466_; lean_object* v_L_4467_; lean_object* v_Q_4468_; lean_object* v_q_4469_; lean_object* v_w_4470_; lean_object* v_W_4471_; lean_object* v_E_4472_; lean_object* v_e_4473_; lean_object* v_c_4474_; lean_object* v_F_4475_; lean_object* v_a_4476_; lean_object* v_b_4477_; lean_object* v_B_4478_; lean_object* v_h_4479_; lean_object* v_K_4480_; lean_object* v_k_4481_; lean_object* v_H_4482_; lean_object* v_m_4483_; lean_object* v_s_4484_; lean_object* v_S_4485_; lean_object* v_A_4486_; lean_object* v_n_4487_; lean_object* v_N_4488_; lean_object* v_V_4489_; lean_object* v_z_4490_; lean_object* v_zabbrev_4491_; lean_object* v_v_4492_; lean_object* v_O_4493_; lean_object* v_X_4494_; lean_object* v_x_4495_; lean_object* v_Z_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4506_; 
v_G_4461_ = lean_ctor_get(v_date_4150_, 0);
v_y_4462_ = lean_ctor_get(v_date_4150_, 1);
v_u_4463_ = lean_ctor_get(v_date_4150_, 2);
v_Y_4464_ = lean_ctor_get(v_date_4150_, 3);
v_D_4465_ = lean_ctor_get(v_date_4150_, 4);
v_M_4466_ = lean_ctor_get(v_date_4150_, 5);
v_L_4467_ = lean_ctor_get(v_date_4150_, 6);
v_Q_4468_ = lean_ctor_get(v_date_4150_, 8);
v_q_4469_ = lean_ctor_get(v_date_4150_, 9);
v_w_4470_ = lean_ctor_get(v_date_4150_, 10);
v_W_4471_ = lean_ctor_get(v_date_4150_, 11);
v_E_4472_ = lean_ctor_get(v_date_4150_, 12);
v_e_4473_ = lean_ctor_get(v_date_4150_, 13);
v_c_4474_ = lean_ctor_get(v_date_4150_, 14);
v_F_4475_ = lean_ctor_get(v_date_4150_, 15);
v_a_4476_ = lean_ctor_get(v_date_4150_, 16);
v_b_4477_ = lean_ctor_get(v_date_4150_, 17);
v_B_4478_ = lean_ctor_get(v_date_4150_, 18);
v_h_4479_ = lean_ctor_get(v_date_4150_, 19);
v_K_4480_ = lean_ctor_get(v_date_4150_, 20);
v_k_4481_ = lean_ctor_get(v_date_4150_, 21);
v_H_4482_ = lean_ctor_get(v_date_4150_, 22);
v_m_4483_ = lean_ctor_get(v_date_4150_, 23);
v_s_4484_ = lean_ctor_get(v_date_4150_, 24);
v_S_4485_ = lean_ctor_get(v_date_4150_, 25);
v_A_4486_ = lean_ctor_get(v_date_4150_, 26);
v_n_4487_ = lean_ctor_get(v_date_4150_, 27);
v_N_4488_ = lean_ctor_get(v_date_4150_, 28);
v_V_4489_ = lean_ctor_get(v_date_4150_, 29);
v_z_4490_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_4491_ = lean_ctor_get(v_date_4150_, 31);
v_v_4492_ = lean_ctor_get(v_date_4150_, 32);
v_O_4493_ = lean_ctor_get(v_date_4150_, 33);
v_X_4494_ = lean_ctor_get(v_date_4150_, 34);
v_x_4495_ = lean_ctor_get(v_date_4150_, 35);
v_Z_4496_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_4506_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_4506_ == 0)
{
lean_object* v_unused_4507_; 
v_unused_4507_ = lean_ctor_get(v_date_4150_, 7);
lean_dec(v_unused_4507_);
v___x_4498_ = v_date_4150_;
v_isShared_4499_ = v_isSharedCheck_4506_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_Z_4496_);
lean_inc(v_x_4495_);
lean_inc(v_X_4494_);
lean_inc(v_O_4493_);
lean_inc(v_v_4492_);
lean_inc(v_zabbrev_4491_);
lean_inc(v_z_4490_);
lean_inc(v_V_4489_);
lean_inc(v_N_4488_);
lean_inc(v_n_4487_);
lean_inc(v_A_4486_);
lean_inc(v_S_4485_);
lean_inc(v_s_4484_);
lean_inc(v_m_4483_);
lean_inc(v_H_4482_);
lean_inc(v_k_4481_);
lean_inc(v_K_4480_);
lean_inc(v_h_4479_);
lean_inc(v_B_4478_);
lean_inc(v_b_4477_);
lean_inc(v_a_4476_);
lean_inc(v_F_4475_);
lean_inc(v_c_4474_);
lean_inc(v_e_4473_);
lean_inc(v_E_4472_);
lean_inc(v_W_4471_);
lean_inc(v_w_4470_);
lean_inc(v_q_4469_);
lean_inc(v_Q_4468_);
lean_inc(v_L_4467_);
lean_inc(v_M_4466_);
lean_inc(v_D_4465_);
lean_inc(v_Y_4464_);
lean_inc(v_u_4463_);
lean_inc(v_y_4462_);
lean_inc(v_G_4461_);
lean_dec(v_date_4150_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4506_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v___x_4501_; 
if (v_isShared_4460_ == 0)
{
lean_ctor_set_tag(v___x_4459_, 1);
lean_ctor_set(v___x_4459_, 0, v_data_4152_);
v___x_4501_ = v___x_4459_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_data_4152_);
v___x_4501_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
lean_object* v___x_4503_; 
if (v_isShared_4499_ == 0)
{
lean_ctor_set(v___x_4498_, 7, v___x_4501_);
v___x_4503_ = v___x_4498_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_G_4461_);
lean_ctor_set(v_reuseFailAlloc_4504_, 1, v_y_4462_);
lean_ctor_set(v_reuseFailAlloc_4504_, 2, v_u_4463_);
lean_ctor_set(v_reuseFailAlloc_4504_, 3, v_Y_4464_);
lean_ctor_set(v_reuseFailAlloc_4504_, 4, v_D_4465_);
lean_ctor_set(v_reuseFailAlloc_4504_, 5, v_M_4466_);
lean_ctor_set(v_reuseFailAlloc_4504_, 6, v_L_4467_);
lean_ctor_set(v_reuseFailAlloc_4504_, 7, v___x_4501_);
lean_ctor_set(v_reuseFailAlloc_4504_, 8, v_Q_4468_);
lean_ctor_set(v_reuseFailAlloc_4504_, 9, v_q_4469_);
lean_ctor_set(v_reuseFailAlloc_4504_, 10, v_w_4470_);
lean_ctor_set(v_reuseFailAlloc_4504_, 11, v_W_4471_);
lean_ctor_set(v_reuseFailAlloc_4504_, 12, v_E_4472_);
lean_ctor_set(v_reuseFailAlloc_4504_, 13, v_e_4473_);
lean_ctor_set(v_reuseFailAlloc_4504_, 14, v_c_4474_);
lean_ctor_set(v_reuseFailAlloc_4504_, 15, v_F_4475_);
lean_ctor_set(v_reuseFailAlloc_4504_, 16, v_a_4476_);
lean_ctor_set(v_reuseFailAlloc_4504_, 17, v_b_4477_);
lean_ctor_set(v_reuseFailAlloc_4504_, 18, v_B_4478_);
lean_ctor_set(v_reuseFailAlloc_4504_, 19, v_h_4479_);
lean_ctor_set(v_reuseFailAlloc_4504_, 20, v_K_4480_);
lean_ctor_set(v_reuseFailAlloc_4504_, 21, v_k_4481_);
lean_ctor_set(v_reuseFailAlloc_4504_, 22, v_H_4482_);
lean_ctor_set(v_reuseFailAlloc_4504_, 23, v_m_4483_);
lean_ctor_set(v_reuseFailAlloc_4504_, 24, v_s_4484_);
lean_ctor_set(v_reuseFailAlloc_4504_, 25, v_S_4485_);
lean_ctor_set(v_reuseFailAlloc_4504_, 26, v_A_4486_);
lean_ctor_set(v_reuseFailAlloc_4504_, 27, v_n_4487_);
lean_ctor_set(v_reuseFailAlloc_4504_, 28, v_N_4488_);
lean_ctor_set(v_reuseFailAlloc_4504_, 29, v_V_4489_);
lean_ctor_set(v_reuseFailAlloc_4504_, 30, v_z_4490_);
lean_ctor_set(v_reuseFailAlloc_4504_, 31, v_zabbrev_4491_);
lean_ctor_set(v_reuseFailAlloc_4504_, 32, v_v_4492_);
lean_ctor_set(v_reuseFailAlloc_4504_, 33, v_O_4493_);
lean_ctor_set(v_reuseFailAlloc_4504_, 34, v_X_4494_);
lean_ctor_set(v_reuseFailAlloc_4504_, 35, v_x_4495_);
lean_ctor_set(v_reuseFailAlloc_4504_, 36, v_Z_4496_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
}
}
case 7:
{
lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4560_; 
v_isSharedCheck_4560_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_4560_ == 0)
{
lean_object* v_unused_4561_; 
v_unused_4561_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_4561_);
v___x_4511_ = v_modifier_4151_;
v_isShared_4512_ = v_isSharedCheck_4560_;
goto v_resetjp_4510_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4560_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v_G_4513_; lean_object* v_y_4514_; lean_object* v_u_4515_; lean_object* v_Y_4516_; lean_object* v_D_4517_; lean_object* v_M_4518_; lean_object* v_L_4519_; lean_object* v_d_4520_; lean_object* v_q_4521_; lean_object* v_w_4522_; lean_object* v_W_4523_; lean_object* v_E_4524_; lean_object* v_e_4525_; lean_object* v_c_4526_; lean_object* v_F_4527_; lean_object* v_a_4528_; lean_object* v_b_4529_; lean_object* v_B_4530_; lean_object* v_h_4531_; lean_object* v_K_4532_; lean_object* v_k_4533_; lean_object* v_H_4534_; lean_object* v_m_4535_; lean_object* v_s_4536_; lean_object* v_S_4537_; lean_object* v_A_4538_; lean_object* v_n_4539_; lean_object* v_N_4540_; lean_object* v_V_4541_; lean_object* v_z_4542_; lean_object* v_zabbrev_4543_; lean_object* v_v_4544_; lean_object* v_O_4545_; lean_object* v_X_4546_; lean_object* v_x_4547_; lean_object* v_Z_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4558_; 
v_G_4513_ = lean_ctor_get(v_date_4150_, 0);
v_y_4514_ = lean_ctor_get(v_date_4150_, 1);
v_u_4515_ = lean_ctor_get(v_date_4150_, 2);
v_Y_4516_ = lean_ctor_get(v_date_4150_, 3);
v_D_4517_ = lean_ctor_get(v_date_4150_, 4);
v_M_4518_ = lean_ctor_get(v_date_4150_, 5);
v_L_4519_ = lean_ctor_get(v_date_4150_, 6);
v_d_4520_ = lean_ctor_get(v_date_4150_, 7);
v_q_4521_ = lean_ctor_get(v_date_4150_, 9);
v_w_4522_ = lean_ctor_get(v_date_4150_, 10);
v_W_4523_ = lean_ctor_get(v_date_4150_, 11);
v_E_4524_ = lean_ctor_get(v_date_4150_, 12);
v_e_4525_ = lean_ctor_get(v_date_4150_, 13);
v_c_4526_ = lean_ctor_get(v_date_4150_, 14);
v_F_4527_ = lean_ctor_get(v_date_4150_, 15);
v_a_4528_ = lean_ctor_get(v_date_4150_, 16);
v_b_4529_ = lean_ctor_get(v_date_4150_, 17);
v_B_4530_ = lean_ctor_get(v_date_4150_, 18);
v_h_4531_ = lean_ctor_get(v_date_4150_, 19);
v_K_4532_ = lean_ctor_get(v_date_4150_, 20);
v_k_4533_ = lean_ctor_get(v_date_4150_, 21);
v_H_4534_ = lean_ctor_get(v_date_4150_, 22);
v_m_4535_ = lean_ctor_get(v_date_4150_, 23);
v_s_4536_ = lean_ctor_get(v_date_4150_, 24);
v_S_4537_ = lean_ctor_get(v_date_4150_, 25);
v_A_4538_ = lean_ctor_get(v_date_4150_, 26);
v_n_4539_ = lean_ctor_get(v_date_4150_, 27);
v_N_4540_ = lean_ctor_get(v_date_4150_, 28);
v_V_4541_ = lean_ctor_get(v_date_4150_, 29);
v_z_4542_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_4543_ = lean_ctor_get(v_date_4150_, 31);
v_v_4544_ = lean_ctor_get(v_date_4150_, 32);
v_O_4545_ = lean_ctor_get(v_date_4150_, 33);
v_X_4546_ = lean_ctor_get(v_date_4150_, 34);
v_x_4547_ = lean_ctor_get(v_date_4150_, 35);
v_Z_4548_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_4558_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_4558_ == 0)
{
lean_object* v_unused_4559_; 
v_unused_4559_ = lean_ctor_get(v_date_4150_, 8);
lean_dec(v_unused_4559_);
v___x_4550_ = v_date_4150_;
v_isShared_4551_ = v_isSharedCheck_4558_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_Z_4548_);
lean_inc(v_x_4547_);
lean_inc(v_X_4546_);
lean_inc(v_O_4545_);
lean_inc(v_v_4544_);
lean_inc(v_zabbrev_4543_);
lean_inc(v_z_4542_);
lean_inc(v_V_4541_);
lean_inc(v_N_4540_);
lean_inc(v_n_4539_);
lean_inc(v_A_4538_);
lean_inc(v_S_4537_);
lean_inc(v_s_4536_);
lean_inc(v_m_4535_);
lean_inc(v_H_4534_);
lean_inc(v_k_4533_);
lean_inc(v_K_4532_);
lean_inc(v_h_4531_);
lean_inc(v_B_4530_);
lean_inc(v_b_4529_);
lean_inc(v_a_4528_);
lean_inc(v_F_4527_);
lean_inc(v_c_4526_);
lean_inc(v_e_4525_);
lean_inc(v_E_4524_);
lean_inc(v_W_4523_);
lean_inc(v_w_4522_);
lean_inc(v_q_4521_);
lean_inc(v_d_4520_);
lean_inc(v_L_4519_);
lean_inc(v_M_4518_);
lean_inc(v_D_4517_);
lean_inc(v_Y_4516_);
lean_inc(v_u_4515_);
lean_inc(v_y_4514_);
lean_inc(v_G_4513_);
lean_dec(v_date_4150_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4558_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4553_; 
if (v_isShared_4512_ == 0)
{
lean_ctor_set_tag(v___x_4511_, 1);
lean_ctor_set(v___x_4511_, 0, v_data_4152_);
v___x_4553_ = v___x_4511_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_data_4152_);
v___x_4553_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
lean_object* v___x_4555_; 
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 8, v___x_4553_);
v___x_4555_ = v___x_4550_;
goto v_reusejp_4554_;
}
else
{
lean_object* v_reuseFailAlloc_4556_; 
v_reuseFailAlloc_4556_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4556_, 0, v_G_4513_);
lean_ctor_set(v_reuseFailAlloc_4556_, 1, v_y_4514_);
lean_ctor_set(v_reuseFailAlloc_4556_, 2, v_u_4515_);
lean_ctor_set(v_reuseFailAlloc_4556_, 3, v_Y_4516_);
lean_ctor_set(v_reuseFailAlloc_4556_, 4, v_D_4517_);
lean_ctor_set(v_reuseFailAlloc_4556_, 5, v_M_4518_);
lean_ctor_set(v_reuseFailAlloc_4556_, 6, v_L_4519_);
lean_ctor_set(v_reuseFailAlloc_4556_, 7, v_d_4520_);
lean_ctor_set(v_reuseFailAlloc_4556_, 8, v___x_4553_);
lean_ctor_set(v_reuseFailAlloc_4556_, 9, v_q_4521_);
lean_ctor_set(v_reuseFailAlloc_4556_, 10, v_w_4522_);
lean_ctor_set(v_reuseFailAlloc_4556_, 11, v_W_4523_);
lean_ctor_set(v_reuseFailAlloc_4556_, 12, v_E_4524_);
lean_ctor_set(v_reuseFailAlloc_4556_, 13, v_e_4525_);
lean_ctor_set(v_reuseFailAlloc_4556_, 14, v_c_4526_);
lean_ctor_set(v_reuseFailAlloc_4556_, 15, v_F_4527_);
lean_ctor_set(v_reuseFailAlloc_4556_, 16, v_a_4528_);
lean_ctor_set(v_reuseFailAlloc_4556_, 17, v_b_4529_);
lean_ctor_set(v_reuseFailAlloc_4556_, 18, v_B_4530_);
lean_ctor_set(v_reuseFailAlloc_4556_, 19, v_h_4531_);
lean_ctor_set(v_reuseFailAlloc_4556_, 20, v_K_4532_);
lean_ctor_set(v_reuseFailAlloc_4556_, 21, v_k_4533_);
lean_ctor_set(v_reuseFailAlloc_4556_, 22, v_H_4534_);
lean_ctor_set(v_reuseFailAlloc_4556_, 23, v_m_4535_);
lean_ctor_set(v_reuseFailAlloc_4556_, 24, v_s_4536_);
lean_ctor_set(v_reuseFailAlloc_4556_, 25, v_S_4537_);
lean_ctor_set(v_reuseFailAlloc_4556_, 26, v_A_4538_);
lean_ctor_set(v_reuseFailAlloc_4556_, 27, v_n_4539_);
lean_ctor_set(v_reuseFailAlloc_4556_, 28, v_N_4540_);
lean_ctor_set(v_reuseFailAlloc_4556_, 29, v_V_4541_);
lean_ctor_set(v_reuseFailAlloc_4556_, 30, v_z_4542_);
lean_ctor_set(v_reuseFailAlloc_4556_, 31, v_zabbrev_4543_);
lean_ctor_set(v_reuseFailAlloc_4556_, 32, v_v_4544_);
lean_ctor_set(v_reuseFailAlloc_4556_, 33, v_O_4545_);
lean_ctor_set(v_reuseFailAlloc_4556_, 34, v_X_4546_);
lean_ctor_set(v_reuseFailAlloc_4556_, 35, v_x_4547_);
lean_ctor_set(v_reuseFailAlloc_4556_, 36, v_Z_4548_);
v___x_4555_ = v_reuseFailAlloc_4556_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
return v___x_4555_;
}
}
}
}
}
case 8:
{
lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4612_; 
v_isSharedCheck_4612_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_4612_ == 0)
{
lean_object* v_unused_4613_; 
v_unused_4613_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_4613_);
v___x_4563_ = v_modifier_4151_;
v_isShared_4564_ = v_isSharedCheck_4612_;
goto v_resetjp_4562_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4612_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v_G_4565_; lean_object* v_y_4566_; lean_object* v_u_4567_; lean_object* v_Y_4568_; lean_object* v_D_4569_; lean_object* v_M_4570_; lean_object* v_L_4571_; lean_object* v_d_4572_; lean_object* v_Q_4573_; lean_object* v_w_4574_; lean_object* v_W_4575_; lean_object* v_E_4576_; lean_object* v_e_4577_; lean_object* v_c_4578_; lean_object* v_F_4579_; lean_object* v_a_4580_; lean_object* v_b_4581_; lean_object* v_B_4582_; lean_object* v_h_4583_; lean_object* v_K_4584_; lean_object* v_k_4585_; lean_object* v_H_4586_; lean_object* v_m_4587_; lean_object* v_s_4588_; lean_object* v_S_4589_; lean_object* v_A_4590_; lean_object* v_n_4591_; lean_object* v_N_4592_; lean_object* v_V_4593_; lean_object* v_z_4594_; lean_object* v_zabbrev_4595_; lean_object* v_v_4596_; lean_object* v_O_4597_; lean_object* v_X_4598_; lean_object* v_x_4599_; lean_object* v_Z_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4610_; 
v_G_4565_ = lean_ctor_get(v_date_4150_, 0);
v_y_4566_ = lean_ctor_get(v_date_4150_, 1);
v_u_4567_ = lean_ctor_get(v_date_4150_, 2);
v_Y_4568_ = lean_ctor_get(v_date_4150_, 3);
v_D_4569_ = lean_ctor_get(v_date_4150_, 4);
v_M_4570_ = lean_ctor_get(v_date_4150_, 5);
v_L_4571_ = lean_ctor_get(v_date_4150_, 6);
v_d_4572_ = lean_ctor_get(v_date_4150_, 7);
v_Q_4573_ = lean_ctor_get(v_date_4150_, 8);
v_w_4574_ = lean_ctor_get(v_date_4150_, 10);
v_W_4575_ = lean_ctor_get(v_date_4150_, 11);
v_E_4576_ = lean_ctor_get(v_date_4150_, 12);
v_e_4577_ = lean_ctor_get(v_date_4150_, 13);
v_c_4578_ = lean_ctor_get(v_date_4150_, 14);
v_F_4579_ = lean_ctor_get(v_date_4150_, 15);
v_a_4580_ = lean_ctor_get(v_date_4150_, 16);
v_b_4581_ = lean_ctor_get(v_date_4150_, 17);
v_B_4582_ = lean_ctor_get(v_date_4150_, 18);
v_h_4583_ = lean_ctor_get(v_date_4150_, 19);
v_K_4584_ = lean_ctor_get(v_date_4150_, 20);
v_k_4585_ = lean_ctor_get(v_date_4150_, 21);
v_H_4586_ = lean_ctor_get(v_date_4150_, 22);
v_m_4587_ = lean_ctor_get(v_date_4150_, 23);
v_s_4588_ = lean_ctor_get(v_date_4150_, 24);
v_S_4589_ = lean_ctor_get(v_date_4150_, 25);
v_A_4590_ = lean_ctor_get(v_date_4150_, 26);
v_n_4591_ = lean_ctor_get(v_date_4150_, 27);
v_N_4592_ = lean_ctor_get(v_date_4150_, 28);
v_V_4593_ = lean_ctor_get(v_date_4150_, 29);
v_z_4594_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_4595_ = lean_ctor_get(v_date_4150_, 31);
v_v_4596_ = lean_ctor_get(v_date_4150_, 32);
v_O_4597_ = lean_ctor_get(v_date_4150_, 33);
v_X_4598_ = lean_ctor_get(v_date_4150_, 34);
v_x_4599_ = lean_ctor_get(v_date_4150_, 35);
v_Z_4600_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_4610_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_4610_ == 0)
{
lean_object* v_unused_4611_; 
v_unused_4611_ = lean_ctor_get(v_date_4150_, 9);
lean_dec(v_unused_4611_);
v___x_4602_ = v_date_4150_;
v_isShared_4603_ = v_isSharedCheck_4610_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_Z_4600_);
lean_inc(v_x_4599_);
lean_inc(v_X_4598_);
lean_inc(v_O_4597_);
lean_inc(v_v_4596_);
lean_inc(v_zabbrev_4595_);
lean_inc(v_z_4594_);
lean_inc(v_V_4593_);
lean_inc(v_N_4592_);
lean_inc(v_n_4591_);
lean_inc(v_A_4590_);
lean_inc(v_S_4589_);
lean_inc(v_s_4588_);
lean_inc(v_m_4587_);
lean_inc(v_H_4586_);
lean_inc(v_k_4585_);
lean_inc(v_K_4584_);
lean_inc(v_h_4583_);
lean_inc(v_B_4582_);
lean_inc(v_b_4581_);
lean_inc(v_a_4580_);
lean_inc(v_F_4579_);
lean_inc(v_c_4578_);
lean_inc(v_e_4577_);
lean_inc(v_E_4576_);
lean_inc(v_W_4575_);
lean_inc(v_w_4574_);
lean_inc(v_Q_4573_);
lean_inc(v_d_4572_);
lean_inc(v_L_4571_);
lean_inc(v_M_4570_);
lean_inc(v_D_4569_);
lean_inc(v_Y_4568_);
lean_inc(v_u_4567_);
lean_inc(v_y_4566_);
lean_inc(v_G_4565_);
lean_dec(v_date_4150_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4610_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4605_; 
if (v_isShared_4564_ == 0)
{
lean_ctor_set_tag(v___x_4563_, 1);
lean_ctor_set(v___x_4563_, 0, v_data_4152_);
v___x_4605_ = v___x_4563_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_data_4152_);
v___x_4605_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
lean_object* v___x_4607_; 
if (v_isShared_4603_ == 0)
{
lean_ctor_set(v___x_4602_, 9, v___x_4605_);
v___x_4607_ = v___x_4602_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v_G_4565_);
lean_ctor_set(v_reuseFailAlloc_4608_, 1, v_y_4566_);
lean_ctor_set(v_reuseFailAlloc_4608_, 2, v_u_4567_);
lean_ctor_set(v_reuseFailAlloc_4608_, 3, v_Y_4568_);
lean_ctor_set(v_reuseFailAlloc_4608_, 4, v_D_4569_);
lean_ctor_set(v_reuseFailAlloc_4608_, 5, v_M_4570_);
lean_ctor_set(v_reuseFailAlloc_4608_, 6, v_L_4571_);
lean_ctor_set(v_reuseFailAlloc_4608_, 7, v_d_4572_);
lean_ctor_set(v_reuseFailAlloc_4608_, 8, v_Q_4573_);
lean_ctor_set(v_reuseFailAlloc_4608_, 9, v___x_4605_);
lean_ctor_set(v_reuseFailAlloc_4608_, 10, v_w_4574_);
lean_ctor_set(v_reuseFailAlloc_4608_, 11, v_W_4575_);
lean_ctor_set(v_reuseFailAlloc_4608_, 12, v_E_4576_);
lean_ctor_set(v_reuseFailAlloc_4608_, 13, v_e_4577_);
lean_ctor_set(v_reuseFailAlloc_4608_, 14, v_c_4578_);
lean_ctor_set(v_reuseFailAlloc_4608_, 15, v_F_4579_);
lean_ctor_set(v_reuseFailAlloc_4608_, 16, v_a_4580_);
lean_ctor_set(v_reuseFailAlloc_4608_, 17, v_b_4581_);
lean_ctor_set(v_reuseFailAlloc_4608_, 18, v_B_4582_);
lean_ctor_set(v_reuseFailAlloc_4608_, 19, v_h_4583_);
lean_ctor_set(v_reuseFailAlloc_4608_, 20, v_K_4584_);
lean_ctor_set(v_reuseFailAlloc_4608_, 21, v_k_4585_);
lean_ctor_set(v_reuseFailAlloc_4608_, 22, v_H_4586_);
lean_ctor_set(v_reuseFailAlloc_4608_, 23, v_m_4587_);
lean_ctor_set(v_reuseFailAlloc_4608_, 24, v_s_4588_);
lean_ctor_set(v_reuseFailAlloc_4608_, 25, v_S_4589_);
lean_ctor_set(v_reuseFailAlloc_4608_, 26, v_A_4590_);
lean_ctor_set(v_reuseFailAlloc_4608_, 27, v_n_4591_);
lean_ctor_set(v_reuseFailAlloc_4608_, 28, v_N_4592_);
lean_ctor_set(v_reuseFailAlloc_4608_, 29, v_V_4593_);
lean_ctor_set(v_reuseFailAlloc_4608_, 30, v_z_4594_);
lean_ctor_set(v_reuseFailAlloc_4608_, 31, v_zabbrev_4595_);
lean_ctor_set(v_reuseFailAlloc_4608_, 32, v_v_4596_);
lean_ctor_set(v_reuseFailAlloc_4608_, 33, v_O_4597_);
lean_ctor_set(v_reuseFailAlloc_4608_, 34, v_X_4598_);
lean_ctor_set(v_reuseFailAlloc_4608_, 35, v_x_4599_);
lean_ctor_set(v_reuseFailAlloc_4608_, 36, v_Z_4600_);
v___x_4607_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
return v___x_4607_;
}
}
}
}
}
case 9:
{
lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4664_; 
v_isSharedCheck_4664_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_4664_ == 0)
{
lean_object* v_unused_4665_; 
v_unused_4665_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_4665_);
v___x_4615_ = v_modifier_4151_;
v_isShared_4616_ = v_isSharedCheck_4664_;
goto v_resetjp_4614_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4664_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v_G_4617_; lean_object* v_y_4618_; lean_object* v_u_4619_; lean_object* v_D_4620_; lean_object* v_M_4621_; lean_object* v_L_4622_; lean_object* v_d_4623_; lean_object* v_Q_4624_; lean_object* v_q_4625_; lean_object* v_w_4626_; lean_object* v_W_4627_; lean_object* v_E_4628_; lean_object* v_e_4629_; lean_object* v_c_4630_; lean_object* v_F_4631_; lean_object* v_a_4632_; lean_object* v_b_4633_; lean_object* v_B_4634_; lean_object* v_h_4635_; lean_object* v_K_4636_; lean_object* v_k_4637_; lean_object* v_H_4638_; lean_object* v_m_4639_; lean_object* v_s_4640_; lean_object* v_S_4641_; lean_object* v_A_4642_; lean_object* v_n_4643_; lean_object* v_N_4644_; lean_object* v_V_4645_; lean_object* v_z_4646_; lean_object* v_zabbrev_4647_; lean_object* v_v_4648_; lean_object* v_O_4649_; lean_object* v_X_4650_; lean_object* v_x_4651_; lean_object* v_Z_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4662_; 
v_G_4617_ = lean_ctor_get(v_date_4150_, 0);
v_y_4618_ = lean_ctor_get(v_date_4150_, 1);
v_u_4619_ = lean_ctor_get(v_date_4150_, 2);
v_D_4620_ = lean_ctor_get(v_date_4150_, 4);
v_M_4621_ = lean_ctor_get(v_date_4150_, 5);
v_L_4622_ = lean_ctor_get(v_date_4150_, 6);
v_d_4623_ = lean_ctor_get(v_date_4150_, 7);
v_Q_4624_ = lean_ctor_get(v_date_4150_, 8);
v_q_4625_ = lean_ctor_get(v_date_4150_, 9);
v_w_4626_ = lean_ctor_get(v_date_4150_, 10);
v_W_4627_ = lean_ctor_get(v_date_4150_, 11);
v_E_4628_ = lean_ctor_get(v_date_4150_, 12);
v_e_4629_ = lean_ctor_get(v_date_4150_, 13);
v_c_4630_ = lean_ctor_get(v_date_4150_, 14);
v_F_4631_ = lean_ctor_get(v_date_4150_, 15);
v_a_4632_ = lean_ctor_get(v_date_4150_, 16);
v_b_4633_ = lean_ctor_get(v_date_4150_, 17);
v_B_4634_ = lean_ctor_get(v_date_4150_, 18);
v_h_4635_ = lean_ctor_get(v_date_4150_, 19);
v_K_4636_ = lean_ctor_get(v_date_4150_, 20);
v_k_4637_ = lean_ctor_get(v_date_4150_, 21);
v_H_4638_ = lean_ctor_get(v_date_4150_, 22);
v_m_4639_ = lean_ctor_get(v_date_4150_, 23);
v_s_4640_ = lean_ctor_get(v_date_4150_, 24);
v_S_4641_ = lean_ctor_get(v_date_4150_, 25);
v_A_4642_ = lean_ctor_get(v_date_4150_, 26);
v_n_4643_ = lean_ctor_get(v_date_4150_, 27);
v_N_4644_ = lean_ctor_get(v_date_4150_, 28);
v_V_4645_ = lean_ctor_get(v_date_4150_, 29);
v_z_4646_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_4647_ = lean_ctor_get(v_date_4150_, 31);
v_v_4648_ = lean_ctor_get(v_date_4150_, 32);
v_O_4649_ = lean_ctor_get(v_date_4150_, 33);
v_X_4650_ = lean_ctor_get(v_date_4150_, 34);
v_x_4651_ = lean_ctor_get(v_date_4150_, 35);
v_Z_4652_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_4662_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_4662_ == 0)
{
lean_object* v_unused_4663_; 
v_unused_4663_ = lean_ctor_get(v_date_4150_, 3);
lean_dec(v_unused_4663_);
v___x_4654_ = v_date_4150_;
v_isShared_4655_ = v_isSharedCheck_4662_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_Z_4652_);
lean_inc(v_x_4651_);
lean_inc(v_X_4650_);
lean_inc(v_O_4649_);
lean_inc(v_v_4648_);
lean_inc(v_zabbrev_4647_);
lean_inc(v_z_4646_);
lean_inc(v_V_4645_);
lean_inc(v_N_4644_);
lean_inc(v_n_4643_);
lean_inc(v_A_4642_);
lean_inc(v_S_4641_);
lean_inc(v_s_4640_);
lean_inc(v_m_4639_);
lean_inc(v_H_4638_);
lean_inc(v_k_4637_);
lean_inc(v_K_4636_);
lean_inc(v_h_4635_);
lean_inc(v_B_4634_);
lean_inc(v_b_4633_);
lean_inc(v_a_4632_);
lean_inc(v_F_4631_);
lean_inc(v_c_4630_);
lean_inc(v_e_4629_);
lean_inc(v_E_4628_);
lean_inc(v_W_4627_);
lean_inc(v_w_4626_);
lean_inc(v_q_4625_);
lean_inc(v_Q_4624_);
lean_inc(v_d_4623_);
lean_inc(v_L_4622_);
lean_inc(v_M_4621_);
lean_inc(v_D_4620_);
lean_inc(v_u_4619_);
lean_inc(v_y_4618_);
lean_inc(v_G_4617_);
lean_dec(v_date_4150_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4662_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4657_; 
if (v_isShared_4616_ == 0)
{
lean_ctor_set_tag(v___x_4615_, 1);
lean_ctor_set(v___x_4615_, 0, v_data_4152_);
v___x_4657_ = v___x_4615_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_data_4152_);
v___x_4657_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
lean_object* v___x_4659_; 
if (v_isShared_4655_ == 0)
{
lean_ctor_set(v___x_4654_, 3, v___x_4657_);
v___x_4659_ = v___x_4654_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_G_4617_);
lean_ctor_set(v_reuseFailAlloc_4660_, 1, v_y_4618_);
lean_ctor_set(v_reuseFailAlloc_4660_, 2, v_u_4619_);
lean_ctor_set(v_reuseFailAlloc_4660_, 3, v___x_4657_);
lean_ctor_set(v_reuseFailAlloc_4660_, 4, v_D_4620_);
lean_ctor_set(v_reuseFailAlloc_4660_, 5, v_M_4621_);
lean_ctor_set(v_reuseFailAlloc_4660_, 6, v_L_4622_);
lean_ctor_set(v_reuseFailAlloc_4660_, 7, v_d_4623_);
lean_ctor_set(v_reuseFailAlloc_4660_, 8, v_Q_4624_);
lean_ctor_set(v_reuseFailAlloc_4660_, 9, v_q_4625_);
lean_ctor_set(v_reuseFailAlloc_4660_, 10, v_w_4626_);
lean_ctor_set(v_reuseFailAlloc_4660_, 11, v_W_4627_);
lean_ctor_set(v_reuseFailAlloc_4660_, 12, v_E_4628_);
lean_ctor_set(v_reuseFailAlloc_4660_, 13, v_e_4629_);
lean_ctor_set(v_reuseFailAlloc_4660_, 14, v_c_4630_);
lean_ctor_set(v_reuseFailAlloc_4660_, 15, v_F_4631_);
lean_ctor_set(v_reuseFailAlloc_4660_, 16, v_a_4632_);
lean_ctor_set(v_reuseFailAlloc_4660_, 17, v_b_4633_);
lean_ctor_set(v_reuseFailAlloc_4660_, 18, v_B_4634_);
lean_ctor_set(v_reuseFailAlloc_4660_, 19, v_h_4635_);
lean_ctor_set(v_reuseFailAlloc_4660_, 20, v_K_4636_);
lean_ctor_set(v_reuseFailAlloc_4660_, 21, v_k_4637_);
lean_ctor_set(v_reuseFailAlloc_4660_, 22, v_H_4638_);
lean_ctor_set(v_reuseFailAlloc_4660_, 23, v_m_4639_);
lean_ctor_set(v_reuseFailAlloc_4660_, 24, v_s_4640_);
lean_ctor_set(v_reuseFailAlloc_4660_, 25, v_S_4641_);
lean_ctor_set(v_reuseFailAlloc_4660_, 26, v_A_4642_);
lean_ctor_set(v_reuseFailAlloc_4660_, 27, v_n_4643_);
lean_ctor_set(v_reuseFailAlloc_4660_, 28, v_N_4644_);
lean_ctor_set(v_reuseFailAlloc_4660_, 29, v_V_4645_);
lean_ctor_set(v_reuseFailAlloc_4660_, 30, v_z_4646_);
lean_ctor_set(v_reuseFailAlloc_4660_, 31, v_zabbrev_4647_);
lean_ctor_set(v_reuseFailAlloc_4660_, 32, v_v_4648_);
lean_ctor_set(v_reuseFailAlloc_4660_, 33, v_O_4649_);
lean_ctor_set(v_reuseFailAlloc_4660_, 34, v_X_4650_);
lean_ctor_set(v_reuseFailAlloc_4660_, 35, v_x_4651_);
lean_ctor_set(v_reuseFailAlloc_4660_, 36, v_Z_4652_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
}
}
case 10:
{
lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4716_; 
v_isSharedCheck_4716_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_4716_ == 0)
{
lean_object* v_unused_4717_; 
v_unused_4717_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_4717_);
v___x_4667_ = v_modifier_4151_;
v_isShared_4668_ = v_isSharedCheck_4716_;
goto v_resetjp_4666_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4716_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v_G_4669_; lean_object* v_y_4670_; lean_object* v_u_4671_; lean_object* v_Y_4672_; lean_object* v_D_4673_; lean_object* v_M_4674_; lean_object* v_L_4675_; lean_object* v_d_4676_; lean_object* v_Q_4677_; lean_object* v_q_4678_; lean_object* v_W_4679_; lean_object* v_E_4680_; lean_object* v_e_4681_; lean_object* v_c_4682_; lean_object* v_F_4683_; lean_object* v_a_4684_; lean_object* v_b_4685_; lean_object* v_B_4686_; lean_object* v_h_4687_; lean_object* v_K_4688_; lean_object* v_k_4689_; lean_object* v_H_4690_; lean_object* v_m_4691_; lean_object* v_s_4692_; lean_object* v_S_4693_; lean_object* v_A_4694_; lean_object* v_n_4695_; lean_object* v_N_4696_; lean_object* v_V_4697_; lean_object* v_z_4698_; lean_object* v_zabbrev_4699_; lean_object* v_v_4700_; lean_object* v_O_4701_; lean_object* v_X_4702_; lean_object* v_x_4703_; lean_object* v_Z_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4714_; 
v_G_4669_ = lean_ctor_get(v_date_4150_, 0);
v_y_4670_ = lean_ctor_get(v_date_4150_, 1);
v_u_4671_ = lean_ctor_get(v_date_4150_, 2);
v_Y_4672_ = lean_ctor_get(v_date_4150_, 3);
v_D_4673_ = lean_ctor_get(v_date_4150_, 4);
v_M_4674_ = lean_ctor_get(v_date_4150_, 5);
v_L_4675_ = lean_ctor_get(v_date_4150_, 6);
v_d_4676_ = lean_ctor_get(v_date_4150_, 7);
v_Q_4677_ = lean_ctor_get(v_date_4150_, 8);
v_q_4678_ = lean_ctor_get(v_date_4150_, 9);
v_W_4679_ = lean_ctor_get(v_date_4150_, 11);
v_E_4680_ = lean_ctor_get(v_date_4150_, 12);
v_e_4681_ = lean_ctor_get(v_date_4150_, 13);
v_c_4682_ = lean_ctor_get(v_date_4150_, 14);
v_F_4683_ = lean_ctor_get(v_date_4150_, 15);
v_a_4684_ = lean_ctor_get(v_date_4150_, 16);
v_b_4685_ = lean_ctor_get(v_date_4150_, 17);
v_B_4686_ = lean_ctor_get(v_date_4150_, 18);
v_h_4687_ = lean_ctor_get(v_date_4150_, 19);
v_K_4688_ = lean_ctor_get(v_date_4150_, 20);
v_k_4689_ = lean_ctor_get(v_date_4150_, 21);
v_H_4690_ = lean_ctor_get(v_date_4150_, 22);
v_m_4691_ = lean_ctor_get(v_date_4150_, 23);
v_s_4692_ = lean_ctor_get(v_date_4150_, 24);
v_S_4693_ = lean_ctor_get(v_date_4150_, 25);
v_A_4694_ = lean_ctor_get(v_date_4150_, 26);
v_n_4695_ = lean_ctor_get(v_date_4150_, 27);
v_N_4696_ = lean_ctor_get(v_date_4150_, 28);
v_V_4697_ = lean_ctor_get(v_date_4150_, 29);
v_z_4698_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_4699_ = lean_ctor_get(v_date_4150_, 31);
v_v_4700_ = lean_ctor_get(v_date_4150_, 32);
v_O_4701_ = lean_ctor_get(v_date_4150_, 33);
v_X_4702_ = lean_ctor_get(v_date_4150_, 34);
v_x_4703_ = lean_ctor_get(v_date_4150_, 35);
v_Z_4704_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_4714_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_4714_ == 0)
{
lean_object* v_unused_4715_; 
v_unused_4715_ = lean_ctor_get(v_date_4150_, 10);
lean_dec(v_unused_4715_);
v___x_4706_ = v_date_4150_;
v_isShared_4707_ = v_isSharedCheck_4714_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_Z_4704_);
lean_inc(v_x_4703_);
lean_inc(v_X_4702_);
lean_inc(v_O_4701_);
lean_inc(v_v_4700_);
lean_inc(v_zabbrev_4699_);
lean_inc(v_z_4698_);
lean_inc(v_V_4697_);
lean_inc(v_N_4696_);
lean_inc(v_n_4695_);
lean_inc(v_A_4694_);
lean_inc(v_S_4693_);
lean_inc(v_s_4692_);
lean_inc(v_m_4691_);
lean_inc(v_H_4690_);
lean_inc(v_k_4689_);
lean_inc(v_K_4688_);
lean_inc(v_h_4687_);
lean_inc(v_B_4686_);
lean_inc(v_b_4685_);
lean_inc(v_a_4684_);
lean_inc(v_F_4683_);
lean_inc(v_c_4682_);
lean_inc(v_e_4681_);
lean_inc(v_E_4680_);
lean_inc(v_W_4679_);
lean_inc(v_q_4678_);
lean_inc(v_Q_4677_);
lean_inc(v_d_4676_);
lean_inc(v_L_4675_);
lean_inc(v_M_4674_);
lean_inc(v_D_4673_);
lean_inc(v_Y_4672_);
lean_inc(v_u_4671_);
lean_inc(v_y_4670_);
lean_inc(v_G_4669_);
lean_dec(v_date_4150_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4714_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4709_; 
if (v_isShared_4668_ == 0)
{
lean_ctor_set_tag(v___x_4667_, 1);
lean_ctor_set(v___x_4667_, 0, v_data_4152_);
v___x_4709_ = v___x_4667_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v_data_4152_);
v___x_4709_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
lean_object* v___x_4711_; 
if (v_isShared_4707_ == 0)
{
lean_ctor_set(v___x_4706_, 10, v___x_4709_);
v___x_4711_ = v___x_4706_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v_G_4669_);
lean_ctor_set(v_reuseFailAlloc_4712_, 1, v_y_4670_);
lean_ctor_set(v_reuseFailAlloc_4712_, 2, v_u_4671_);
lean_ctor_set(v_reuseFailAlloc_4712_, 3, v_Y_4672_);
lean_ctor_set(v_reuseFailAlloc_4712_, 4, v_D_4673_);
lean_ctor_set(v_reuseFailAlloc_4712_, 5, v_M_4674_);
lean_ctor_set(v_reuseFailAlloc_4712_, 6, v_L_4675_);
lean_ctor_set(v_reuseFailAlloc_4712_, 7, v_d_4676_);
lean_ctor_set(v_reuseFailAlloc_4712_, 8, v_Q_4677_);
lean_ctor_set(v_reuseFailAlloc_4712_, 9, v_q_4678_);
lean_ctor_set(v_reuseFailAlloc_4712_, 10, v___x_4709_);
lean_ctor_set(v_reuseFailAlloc_4712_, 11, v_W_4679_);
lean_ctor_set(v_reuseFailAlloc_4712_, 12, v_E_4680_);
lean_ctor_set(v_reuseFailAlloc_4712_, 13, v_e_4681_);
lean_ctor_set(v_reuseFailAlloc_4712_, 14, v_c_4682_);
lean_ctor_set(v_reuseFailAlloc_4712_, 15, v_F_4683_);
lean_ctor_set(v_reuseFailAlloc_4712_, 16, v_a_4684_);
lean_ctor_set(v_reuseFailAlloc_4712_, 17, v_b_4685_);
lean_ctor_set(v_reuseFailAlloc_4712_, 18, v_B_4686_);
lean_ctor_set(v_reuseFailAlloc_4712_, 19, v_h_4687_);
lean_ctor_set(v_reuseFailAlloc_4712_, 20, v_K_4688_);
lean_ctor_set(v_reuseFailAlloc_4712_, 21, v_k_4689_);
lean_ctor_set(v_reuseFailAlloc_4712_, 22, v_H_4690_);
lean_ctor_set(v_reuseFailAlloc_4712_, 23, v_m_4691_);
lean_ctor_set(v_reuseFailAlloc_4712_, 24, v_s_4692_);
lean_ctor_set(v_reuseFailAlloc_4712_, 25, v_S_4693_);
lean_ctor_set(v_reuseFailAlloc_4712_, 26, v_A_4694_);
lean_ctor_set(v_reuseFailAlloc_4712_, 27, v_n_4695_);
lean_ctor_set(v_reuseFailAlloc_4712_, 28, v_N_4696_);
lean_ctor_set(v_reuseFailAlloc_4712_, 29, v_V_4697_);
lean_ctor_set(v_reuseFailAlloc_4712_, 30, v_z_4698_);
lean_ctor_set(v_reuseFailAlloc_4712_, 31, v_zabbrev_4699_);
lean_ctor_set(v_reuseFailAlloc_4712_, 32, v_v_4700_);
lean_ctor_set(v_reuseFailAlloc_4712_, 33, v_O_4701_);
lean_ctor_set(v_reuseFailAlloc_4712_, 34, v_X_4702_);
lean_ctor_set(v_reuseFailAlloc_4712_, 35, v_x_4703_);
lean_ctor_set(v_reuseFailAlloc_4712_, 36, v_Z_4704_);
v___x_4711_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
return v___x_4711_;
}
}
}
}
}
case 11:
{
lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4768_; 
v_isSharedCheck_4768_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_4768_ == 0)
{
lean_object* v_unused_4769_; 
v_unused_4769_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_4769_);
v___x_4719_ = v_modifier_4151_;
v_isShared_4720_ = v_isSharedCheck_4768_;
goto v_resetjp_4718_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4768_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v_G_4721_; lean_object* v_y_4722_; lean_object* v_u_4723_; lean_object* v_Y_4724_; lean_object* v_D_4725_; lean_object* v_M_4726_; lean_object* v_L_4727_; lean_object* v_d_4728_; lean_object* v_Q_4729_; lean_object* v_q_4730_; lean_object* v_w_4731_; lean_object* v_E_4732_; lean_object* v_e_4733_; lean_object* v_c_4734_; lean_object* v_F_4735_; lean_object* v_a_4736_; lean_object* v_b_4737_; lean_object* v_B_4738_; lean_object* v_h_4739_; lean_object* v_K_4740_; lean_object* v_k_4741_; lean_object* v_H_4742_; lean_object* v_m_4743_; lean_object* v_s_4744_; lean_object* v_S_4745_; lean_object* v_A_4746_; lean_object* v_n_4747_; lean_object* v_N_4748_; lean_object* v_V_4749_; lean_object* v_z_4750_; lean_object* v_zabbrev_4751_; lean_object* v_v_4752_; lean_object* v_O_4753_; lean_object* v_X_4754_; lean_object* v_x_4755_; lean_object* v_Z_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4766_; 
v_G_4721_ = lean_ctor_get(v_date_4150_, 0);
v_y_4722_ = lean_ctor_get(v_date_4150_, 1);
v_u_4723_ = lean_ctor_get(v_date_4150_, 2);
v_Y_4724_ = lean_ctor_get(v_date_4150_, 3);
v_D_4725_ = lean_ctor_get(v_date_4150_, 4);
v_M_4726_ = lean_ctor_get(v_date_4150_, 5);
v_L_4727_ = lean_ctor_get(v_date_4150_, 6);
v_d_4728_ = lean_ctor_get(v_date_4150_, 7);
v_Q_4729_ = lean_ctor_get(v_date_4150_, 8);
v_q_4730_ = lean_ctor_get(v_date_4150_, 9);
v_w_4731_ = lean_ctor_get(v_date_4150_, 10);
v_E_4732_ = lean_ctor_get(v_date_4150_, 12);
v_e_4733_ = lean_ctor_get(v_date_4150_, 13);
v_c_4734_ = lean_ctor_get(v_date_4150_, 14);
v_F_4735_ = lean_ctor_get(v_date_4150_, 15);
v_a_4736_ = lean_ctor_get(v_date_4150_, 16);
v_b_4737_ = lean_ctor_get(v_date_4150_, 17);
v_B_4738_ = lean_ctor_get(v_date_4150_, 18);
v_h_4739_ = lean_ctor_get(v_date_4150_, 19);
v_K_4740_ = lean_ctor_get(v_date_4150_, 20);
v_k_4741_ = lean_ctor_get(v_date_4150_, 21);
v_H_4742_ = lean_ctor_get(v_date_4150_, 22);
v_m_4743_ = lean_ctor_get(v_date_4150_, 23);
v_s_4744_ = lean_ctor_get(v_date_4150_, 24);
v_S_4745_ = lean_ctor_get(v_date_4150_, 25);
v_A_4746_ = lean_ctor_get(v_date_4150_, 26);
v_n_4747_ = lean_ctor_get(v_date_4150_, 27);
v_N_4748_ = lean_ctor_get(v_date_4150_, 28);
v_V_4749_ = lean_ctor_get(v_date_4150_, 29);
v_z_4750_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_4751_ = lean_ctor_get(v_date_4150_, 31);
v_v_4752_ = lean_ctor_get(v_date_4150_, 32);
v_O_4753_ = lean_ctor_get(v_date_4150_, 33);
v_X_4754_ = lean_ctor_get(v_date_4150_, 34);
v_x_4755_ = lean_ctor_get(v_date_4150_, 35);
v_Z_4756_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_4766_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_4766_ == 0)
{
lean_object* v_unused_4767_; 
v_unused_4767_ = lean_ctor_get(v_date_4150_, 11);
lean_dec(v_unused_4767_);
v___x_4758_ = v_date_4150_;
v_isShared_4759_ = v_isSharedCheck_4766_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_Z_4756_);
lean_inc(v_x_4755_);
lean_inc(v_X_4754_);
lean_inc(v_O_4753_);
lean_inc(v_v_4752_);
lean_inc(v_zabbrev_4751_);
lean_inc(v_z_4750_);
lean_inc(v_V_4749_);
lean_inc(v_N_4748_);
lean_inc(v_n_4747_);
lean_inc(v_A_4746_);
lean_inc(v_S_4745_);
lean_inc(v_s_4744_);
lean_inc(v_m_4743_);
lean_inc(v_H_4742_);
lean_inc(v_k_4741_);
lean_inc(v_K_4740_);
lean_inc(v_h_4739_);
lean_inc(v_B_4738_);
lean_inc(v_b_4737_);
lean_inc(v_a_4736_);
lean_inc(v_F_4735_);
lean_inc(v_c_4734_);
lean_inc(v_e_4733_);
lean_inc(v_E_4732_);
lean_inc(v_w_4731_);
lean_inc(v_q_4730_);
lean_inc(v_Q_4729_);
lean_inc(v_d_4728_);
lean_inc(v_L_4727_);
lean_inc(v_M_4726_);
lean_inc(v_D_4725_);
lean_inc(v_Y_4724_);
lean_inc(v_u_4723_);
lean_inc(v_y_4722_);
lean_inc(v_G_4721_);
lean_dec(v_date_4150_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4766_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4761_; 
if (v_isShared_4720_ == 0)
{
lean_ctor_set_tag(v___x_4719_, 1);
lean_ctor_set(v___x_4719_, 0, v_data_4152_);
v___x_4761_ = v___x_4719_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_data_4152_);
v___x_4761_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
lean_object* v___x_4763_; 
if (v_isShared_4759_ == 0)
{
lean_ctor_set(v___x_4758_, 11, v___x_4761_);
v___x_4763_ = v___x_4758_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_G_4721_);
lean_ctor_set(v_reuseFailAlloc_4764_, 1, v_y_4722_);
lean_ctor_set(v_reuseFailAlloc_4764_, 2, v_u_4723_);
lean_ctor_set(v_reuseFailAlloc_4764_, 3, v_Y_4724_);
lean_ctor_set(v_reuseFailAlloc_4764_, 4, v_D_4725_);
lean_ctor_set(v_reuseFailAlloc_4764_, 5, v_M_4726_);
lean_ctor_set(v_reuseFailAlloc_4764_, 6, v_L_4727_);
lean_ctor_set(v_reuseFailAlloc_4764_, 7, v_d_4728_);
lean_ctor_set(v_reuseFailAlloc_4764_, 8, v_Q_4729_);
lean_ctor_set(v_reuseFailAlloc_4764_, 9, v_q_4730_);
lean_ctor_set(v_reuseFailAlloc_4764_, 10, v_w_4731_);
lean_ctor_set(v_reuseFailAlloc_4764_, 11, v___x_4761_);
lean_ctor_set(v_reuseFailAlloc_4764_, 12, v_E_4732_);
lean_ctor_set(v_reuseFailAlloc_4764_, 13, v_e_4733_);
lean_ctor_set(v_reuseFailAlloc_4764_, 14, v_c_4734_);
lean_ctor_set(v_reuseFailAlloc_4764_, 15, v_F_4735_);
lean_ctor_set(v_reuseFailAlloc_4764_, 16, v_a_4736_);
lean_ctor_set(v_reuseFailAlloc_4764_, 17, v_b_4737_);
lean_ctor_set(v_reuseFailAlloc_4764_, 18, v_B_4738_);
lean_ctor_set(v_reuseFailAlloc_4764_, 19, v_h_4739_);
lean_ctor_set(v_reuseFailAlloc_4764_, 20, v_K_4740_);
lean_ctor_set(v_reuseFailAlloc_4764_, 21, v_k_4741_);
lean_ctor_set(v_reuseFailAlloc_4764_, 22, v_H_4742_);
lean_ctor_set(v_reuseFailAlloc_4764_, 23, v_m_4743_);
lean_ctor_set(v_reuseFailAlloc_4764_, 24, v_s_4744_);
lean_ctor_set(v_reuseFailAlloc_4764_, 25, v_S_4745_);
lean_ctor_set(v_reuseFailAlloc_4764_, 26, v_A_4746_);
lean_ctor_set(v_reuseFailAlloc_4764_, 27, v_n_4747_);
lean_ctor_set(v_reuseFailAlloc_4764_, 28, v_N_4748_);
lean_ctor_set(v_reuseFailAlloc_4764_, 29, v_V_4749_);
lean_ctor_set(v_reuseFailAlloc_4764_, 30, v_z_4750_);
lean_ctor_set(v_reuseFailAlloc_4764_, 31, v_zabbrev_4751_);
lean_ctor_set(v_reuseFailAlloc_4764_, 32, v_v_4752_);
lean_ctor_set(v_reuseFailAlloc_4764_, 33, v_O_4753_);
lean_ctor_set(v_reuseFailAlloc_4764_, 34, v_X_4754_);
lean_ctor_set(v_reuseFailAlloc_4764_, 35, v_x_4755_);
lean_ctor_set(v_reuseFailAlloc_4764_, 36, v_Z_4756_);
v___x_4763_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
return v___x_4763_;
}
}
}
}
}
case 12:
{
lean_object* v_G_4770_; lean_object* v_y_4771_; lean_object* v_u_4772_; lean_object* v_Y_4773_; lean_object* v_D_4774_; lean_object* v_M_4775_; lean_object* v_L_4776_; lean_object* v_d_4777_; lean_object* v_Q_4778_; lean_object* v_q_4779_; lean_object* v_w_4780_; lean_object* v_W_4781_; lean_object* v_e_4782_; lean_object* v_c_4783_; lean_object* v_F_4784_; lean_object* v_a_4785_; lean_object* v_b_4786_; lean_object* v_B_4787_; lean_object* v_h_4788_; lean_object* v_K_4789_; lean_object* v_k_4790_; lean_object* v_H_4791_; lean_object* v_m_4792_; lean_object* v_s_4793_; lean_object* v_S_4794_; lean_object* v_A_4795_; lean_object* v_n_4796_; lean_object* v_N_4797_; lean_object* v_V_4798_; lean_object* v_z_4799_; lean_object* v_zabbrev_4800_; lean_object* v_v_4801_; lean_object* v_O_4802_; lean_object* v_X_4803_; lean_object* v_x_4804_; lean_object* v_Z_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4813_; 
lean_dec_ref_known(v_modifier_4151_, 0);
v_G_4770_ = lean_ctor_get(v_date_4150_, 0);
v_y_4771_ = lean_ctor_get(v_date_4150_, 1);
v_u_4772_ = lean_ctor_get(v_date_4150_, 2);
v_Y_4773_ = lean_ctor_get(v_date_4150_, 3);
v_D_4774_ = lean_ctor_get(v_date_4150_, 4);
v_M_4775_ = lean_ctor_get(v_date_4150_, 5);
v_L_4776_ = lean_ctor_get(v_date_4150_, 6);
v_d_4777_ = lean_ctor_get(v_date_4150_, 7);
v_Q_4778_ = lean_ctor_get(v_date_4150_, 8);
v_q_4779_ = lean_ctor_get(v_date_4150_, 9);
v_w_4780_ = lean_ctor_get(v_date_4150_, 10);
v_W_4781_ = lean_ctor_get(v_date_4150_, 11);
v_e_4782_ = lean_ctor_get(v_date_4150_, 13);
v_c_4783_ = lean_ctor_get(v_date_4150_, 14);
v_F_4784_ = lean_ctor_get(v_date_4150_, 15);
v_a_4785_ = lean_ctor_get(v_date_4150_, 16);
v_b_4786_ = lean_ctor_get(v_date_4150_, 17);
v_B_4787_ = lean_ctor_get(v_date_4150_, 18);
v_h_4788_ = lean_ctor_get(v_date_4150_, 19);
v_K_4789_ = lean_ctor_get(v_date_4150_, 20);
v_k_4790_ = lean_ctor_get(v_date_4150_, 21);
v_H_4791_ = lean_ctor_get(v_date_4150_, 22);
v_m_4792_ = lean_ctor_get(v_date_4150_, 23);
v_s_4793_ = lean_ctor_get(v_date_4150_, 24);
v_S_4794_ = lean_ctor_get(v_date_4150_, 25);
v_A_4795_ = lean_ctor_get(v_date_4150_, 26);
v_n_4796_ = lean_ctor_get(v_date_4150_, 27);
v_N_4797_ = lean_ctor_get(v_date_4150_, 28);
v_V_4798_ = lean_ctor_get(v_date_4150_, 29);
v_z_4799_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_4800_ = lean_ctor_get(v_date_4150_, 31);
v_v_4801_ = lean_ctor_get(v_date_4150_, 32);
v_O_4802_ = lean_ctor_get(v_date_4150_, 33);
v_X_4803_ = lean_ctor_get(v_date_4150_, 34);
v_x_4804_ = lean_ctor_get(v_date_4150_, 35);
v_Z_4805_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_4813_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_4813_ == 0)
{
lean_object* v_unused_4814_; 
v_unused_4814_ = lean_ctor_get(v_date_4150_, 12);
lean_dec(v_unused_4814_);
v___x_4807_ = v_date_4150_;
v_isShared_4808_ = v_isSharedCheck_4813_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_Z_4805_);
lean_inc(v_x_4804_);
lean_inc(v_X_4803_);
lean_inc(v_O_4802_);
lean_inc(v_v_4801_);
lean_inc(v_zabbrev_4800_);
lean_inc(v_z_4799_);
lean_inc(v_V_4798_);
lean_inc(v_N_4797_);
lean_inc(v_n_4796_);
lean_inc(v_A_4795_);
lean_inc(v_S_4794_);
lean_inc(v_s_4793_);
lean_inc(v_m_4792_);
lean_inc(v_H_4791_);
lean_inc(v_k_4790_);
lean_inc(v_K_4789_);
lean_inc(v_h_4788_);
lean_inc(v_B_4787_);
lean_inc(v_b_4786_);
lean_inc(v_a_4785_);
lean_inc(v_F_4784_);
lean_inc(v_c_4783_);
lean_inc(v_e_4782_);
lean_inc(v_W_4781_);
lean_inc(v_w_4780_);
lean_inc(v_q_4779_);
lean_inc(v_Q_4778_);
lean_inc(v_d_4777_);
lean_inc(v_L_4776_);
lean_inc(v_M_4775_);
lean_inc(v_D_4774_);
lean_inc(v_Y_4773_);
lean_inc(v_u_4772_);
lean_inc(v_y_4771_);
lean_inc(v_G_4770_);
lean_dec(v_date_4150_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4813_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4809_; lean_object* v___x_4811_; 
v___x_4809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4809_, 0, v_data_4152_);
if (v_isShared_4808_ == 0)
{
lean_ctor_set(v___x_4807_, 12, v___x_4809_);
v___x_4811_ = v___x_4807_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v_G_4770_);
lean_ctor_set(v_reuseFailAlloc_4812_, 1, v_y_4771_);
lean_ctor_set(v_reuseFailAlloc_4812_, 2, v_u_4772_);
lean_ctor_set(v_reuseFailAlloc_4812_, 3, v_Y_4773_);
lean_ctor_set(v_reuseFailAlloc_4812_, 4, v_D_4774_);
lean_ctor_set(v_reuseFailAlloc_4812_, 5, v_M_4775_);
lean_ctor_set(v_reuseFailAlloc_4812_, 6, v_L_4776_);
lean_ctor_set(v_reuseFailAlloc_4812_, 7, v_d_4777_);
lean_ctor_set(v_reuseFailAlloc_4812_, 8, v_Q_4778_);
lean_ctor_set(v_reuseFailAlloc_4812_, 9, v_q_4779_);
lean_ctor_set(v_reuseFailAlloc_4812_, 10, v_w_4780_);
lean_ctor_set(v_reuseFailAlloc_4812_, 11, v_W_4781_);
lean_ctor_set(v_reuseFailAlloc_4812_, 12, v___x_4809_);
lean_ctor_set(v_reuseFailAlloc_4812_, 13, v_e_4782_);
lean_ctor_set(v_reuseFailAlloc_4812_, 14, v_c_4783_);
lean_ctor_set(v_reuseFailAlloc_4812_, 15, v_F_4784_);
lean_ctor_set(v_reuseFailAlloc_4812_, 16, v_a_4785_);
lean_ctor_set(v_reuseFailAlloc_4812_, 17, v_b_4786_);
lean_ctor_set(v_reuseFailAlloc_4812_, 18, v_B_4787_);
lean_ctor_set(v_reuseFailAlloc_4812_, 19, v_h_4788_);
lean_ctor_set(v_reuseFailAlloc_4812_, 20, v_K_4789_);
lean_ctor_set(v_reuseFailAlloc_4812_, 21, v_k_4790_);
lean_ctor_set(v_reuseFailAlloc_4812_, 22, v_H_4791_);
lean_ctor_set(v_reuseFailAlloc_4812_, 23, v_m_4792_);
lean_ctor_set(v_reuseFailAlloc_4812_, 24, v_s_4793_);
lean_ctor_set(v_reuseFailAlloc_4812_, 25, v_S_4794_);
lean_ctor_set(v_reuseFailAlloc_4812_, 26, v_A_4795_);
lean_ctor_set(v_reuseFailAlloc_4812_, 27, v_n_4796_);
lean_ctor_set(v_reuseFailAlloc_4812_, 28, v_N_4797_);
lean_ctor_set(v_reuseFailAlloc_4812_, 29, v_V_4798_);
lean_ctor_set(v_reuseFailAlloc_4812_, 30, v_z_4799_);
lean_ctor_set(v_reuseFailAlloc_4812_, 31, v_zabbrev_4800_);
lean_ctor_set(v_reuseFailAlloc_4812_, 32, v_v_4801_);
lean_ctor_set(v_reuseFailAlloc_4812_, 33, v_O_4802_);
lean_ctor_set(v_reuseFailAlloc_4812_, 34, v_X_4803_);
lean_ctor_set(v_reuseFailAlloc_4812_, 35, v_x_4804_);
lean_ctor_set(v_reuseFailAlloc_4812_, 36, v_Z_4805_);
v___x_4811_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
return v___x_4811_;
}
}
}
case 13:
{
lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4865_; 
v_isSharedCheck_4865_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_4865_ == 0)
{
lean_object* v_unused_4866_; 
v_unused_4866_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_4866_);
v___x_4816_ = v_modifier_4151_;
v_isShared_4817_ = v_isSharedCheck_4865_;
goto v_resetjp_4815_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4865_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v_G_4818_; lean_object* v_y_4819_; lean_object* v_u_4820_; lean_object* v_Y_4821_; lean_object* v_D_4822_; lean_object* v_M_4823_; lean_object* v_L_4824_; lean_object* v_d_4825_; lean_object* v_Q_4826_; lean_object* v_q_4827_; lean_object* v_w_4828_; lean_object* v_W_4829_; lean_object* v_E_4830_; lean_object* v_c_4831_; lean_object* v_F_4832_; lean_object* v_a_4833_; lean_object* v_b_4834_; lean_object* v_B_4835_; lean_object* v_h_4836_; lean_object* v_K_4837_; lean_object* v_k_4838_; lean_object* v_H_4839_; lean_object* v_m_4840_; lean_object* v_s_4841_; lean_object* v_S_4842_; lean_object* v_A_4843_; lean_object* v_n_4844_; lean_object* v_N_4845_; lean_object* v_V_4846_; lean_object* v_z_4847_; lean_object* v_zabbrev_4848_; lean_object* v_v_4849_; lean_object* v_O_4850_; lean_object* v_X_4851_; lean_object* v_x_4852_; lean_object* v_Z_4853_; lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_4863_; 
v_G_4818_ = lean_ctor_get(v_date_4150_, 0);
v_y_4819_ = lean_ctor_get(v_date_4150_, 1);
v_u_4820_ = lean_ctor_get(v_date_4150_, 2);
v_Y_4821_ = lean_ctor_get(v_date_4150_, 3);
v_D_4822_ = lean_ctor_get(v_date_4150_, 4);
v_M_4823_ = lean_ctor_get(v_date_4150_, 5);
v_L_4824_ = lean_ctor_get(v_date_4150_, 6);
v_d_4825_ = lean_ctor_get(v_date_4150_, 7);
v_Q_4826_ = lean_ctor_get(v_date_4150_, 8);
v_q_4827_ = lean_ctor_get(v_date_4150_, 9);
v_w_4828_ = lean_ctor_get(v_date_4150_, 10);
v_W_4829_ = lean_ctor_get(v_date_4150_, 11);
v_E_4830_ = lean_ctor_get(v_date_4150_, 12);
v_c_4831_ = lean_ctor_get(v_date_4150_, 14);
v_F_4832_ = lean_ctor_get(v_date_4150_, 15);
v_a_4833_ = lean_ctor_get(v_date_4150_, 16);
v_b_4834_ = lean_ctor_get(v_date_4150_, 17);
v_B_4835_ = lean_ctor_get(v_date_4150_, 18);
v_h_4836_ = lean_ctor_get(v_date_4150_, 19);
v_K_4837_ = lean_ctor_get(v_date_4150_, 20);
v_k_4838_ = lean_ctor_get(v_date_4150_, 21);
v_H_4839_ = lean_ctor_get(v_date_4150_, 22);
v_m_4840_ = lean_ctor_get(v_date_4150_, 23);
v_s_4841_ = lean_ctor_get(v_date_4150_, 24);
v_S_4842_ = lean_ctor_get(v_date_4150_, 25);
v_A_4843_ = lean_ctor_get(v_date_4150_, 26);
v_n_4844_ = lean_ctor_get(v_date_4150_, 27);
v_N_4845_ = lean_ctor_get(v_date_4150_, 28);
v_V_4846_ = lean_ctor_get(v_date_4150_, 29);
v_z_4847_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_4848_ = lean_ctor_get(v_date_4150_, 31);
v_v_4849_ = lean_ctor_get(v_date_4150_, 32);
v_O_4850_ = lean_ctor_get(v_date_4150_, 33);
v_X_4851_ = lean_ctor_get(v_date_4150_, 34);
v_x_4852_ = lean_ctor_get(v_date_4150_, 35);
v_Z_4853_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_4863_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_4863_ == 0)
{
lean_object* v_unused_4864_; 
v_unused_4864_ = lean_ctor_get(v_date_4150_, 13);
lean_dec(v_unused_4864_);
v___x_4855_ = v_date_4150_;
v_isShared_4856_ = v_isSharedCheck_4863_;
goto v_resetjp_4854_;
}
else
{
lean_inc(v_Z_4853_);
lean_inc(v_x_4852_);
lean_inc(v_X_4851_);
lean_inc(v_O_4850_);
lean_inc(v_v_4849_);
lean_inc(v_zabbrev_4848_);
lean_inc(v_z_4847_);
lean_inc(v_V_4846_);
lean_inc(v_N_4845_);
lean_inc(v_n_4844_);
lean_inc(v_A_4843_);
lean_inc(v_S_4842_);
lean_inc(v_s_4841_);
lean_inc(v_m_4840_);
lean_inc(v_H_4839_);
lean_inc(v_k_4838_);
lean_inc(v_K_4837_);
lean_inc(v_h_4836_);
lean_inc(v_B_4835_);
lean_inc(v_b_4834_);
lean_inc(v_a_4833_);
lean_inc(v_F_4832_);
lean_inc(v_c_4831_);
lean_inc(v_E_4830_);
lean_inc(v_W_4829_);
lean_inc(v_w_4828_);
lean_inc(v_q_4827_);
lean_inc(v_Q_4826_);
lean_inc(v_d_4825_);
lean_inc(v_L_4824_);
lean_inc(v_M_4823_);
lean_inc(v_D_4822_);
lean_inc(v_Y_4821_);
lean_inc(v_u_4820_);
lean_inc(v_y_4819_);
lean_inc(v_G_4818_);
lean_dec(v_date_4150_);
v___x_4855_ = lean_box(0);
v_isShared_4856_ = v_isSharedCheck_4863_;
goto v_resetjp_4854_;
}
v_resetjp_4854_:
{
lean_object* v___x_4858_; 
if (v_isShared_4817_ == 0)
{
lean_ctor_set_tag(v___x_4816_, 1);
lean_ctor_set(v___x_4816_, 0, v_data_4152_);
v___x_4858_ = v___x_4816_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_data_4152_);
v___x_4858_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
lean_object* v___x_4860_; 
if (v_isShared_4856_ == 0)
{
lean_ctor_set(v___x_4855_, 13, v___x_4858_);
v___x_4860_ = v___x_4855_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v_G_4818_);
lean_ctor_set(v_reuseFailAlloc_4861_, 1, v_y_4819_);
lean_ctor_set(v_reuseFailAlloc_4861_, 2, v_u_4820_);
lean_ctor_set(v_reuseFailAlloc_4861_, 3, v_Y_4821_);
lean_ctor_set(v_reuseFailAlloc_4861_, 4, v_D_4822_);
lean_ctor_set(v_reuseFailAlloc_4861_, 5, v_M_4823_);
lean_ctor_set(v_reuseFailAlloc_4861_, 6, v_L_4824_);
lean_ctor_set(v_reuseFailAlloc_4861_, 7, v_d_4825_);
lean_ctor_set(v_reuseFailAlloc_4861_, 8, v_Q_4826_);
lean_ctor_set(v_reuseFailAlloc_4861_, 9, v_q_4827_);
lean_ctor_set(v_reuseFailAlloc_4861_, 10, v_w_4828_);
lean_ctor_set(v_reuseFailAlloc_4861_, 11, v_W_4829_);
lean_ctor_set(v_reuseFailAlloc_4861_, 12, v_E_4830_);
lean_ctor_set(v_reuseFailAlloc_4861_, 13, v___x_4858_);
lean_ctor_set(v_reuseFailAlloc_4861_, 14, v_c_4831_);
lean_ctor_set(v_reuseFailAlloc_4861_, 15, v_F_4832_);
lean_ctor_set(v_reuseFailAlloc_4861_, 16, v_a_4833_);
lean_ctor_set(v_reuseFailAlloc_4861_, 17, v_b_4834_);
lean_ctor_set(v_reuseFailAlloc_4861_, 18, v_B_4835_);
lean_ctor_set(v_reuseFailAlloc_4861_, 19, v_h_4836_);
lean_ctor_set(v_reuseFailAlloc_4861_, 20, v_K_4837_);
lean_ctor_set(v_reuseFailAlloc_4861_, 21, v_k_4838_);
lean_ctor_set(v_reuseFailAlloc_4861_, 22, v_H_4839_);
lean_ctor_set(v_reuseFailAlloc_4861_, 23, v_m_4840_);
lean_ctor_set(v_reuseFailAlloc_4861_, 24, v_s_4841_);
lean_ctor_set(v_reuseFailAlloc_4861_, 25, v_S_4842_);
lean_ctor_set(v_reuseFailAlloc_4861_, 26, v_A_4843_);
lean_ctor_set(v_reuseFailAlloc_4861_, 27, v_n_4844_);
lean_ctor_set(v_reuseFailAlloc_4861_, 28, v_N_4845_);
lean_ctor_set(v_reuseFailAlloc_4861_, 29, v_V_4846_);
lean_ctor_set(v_reuseFailAlloc_4861_, 30, v_z_4847_);
lean_ctor_set(v_reuseFailAlloc_4861_, 31, v_zabbrev_4848_);
lean_ctor_set(v_reuseFailAlloc_4861_, 32, v_v_4849_);
lean_ctor_set(v_reuseFailAlloc_4861_, 33, v_O_4850_);
lean_ctor_set(v_reuseFailAlloc_4861_, 34, v_X_4851_);
lean_ctor_set(v_reuseFailAlloc_4861_, 35, v_x_4852_);
lean_ctor_set(v_reuseFailAlloc_4861_, 36, v_Z_4853_);
v___x_4860_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
return v___x_4860_;
}
}
}
}
}
case 14:
{
lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4917_; 
v_isSharedCheck_4917_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_4917_ == 0)
{
lean_object* v_unused_4918_; 
v_unused_4918_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_4918_);
v___x_4868_ = v_modifier_4151_;
v_isShared_4869_ = v_isSharedCheck_4917_;
goto v_resetjp_4867_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4917_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
lean_object* v_G_4870_; lean_object* v_y_4871_; lean_object* v_u_4872_; lean_object* v_Y_4873_; lean_object* v_D_4874_; lean_object* v_M_4875_; lean_object* v_L_4876_; lean_object* v_d_4877_; lean_object* v_Q_4878_; lean_object* v_q_4879_; lean_object* v_w_4880_; lean_object* v_W_4881_; lean_object* v_E_4882_; lean_object* v_e_4883_; lean_object* v_F_4884_; lean_object* v_a_4885_; lean_object* v_b_4886_; lean_object* v_B_4887_; lean_object* v_h_4888_; lean_object* v_K_4889_; lean_object* v_k_4890_; lean_object* v_H_4891_; lean_object* v_m_4892_; lean_object* v_s_4893_; lean_object* v_S_4894_; lean_object* v_A_4895_; lean_object* v_n_4896_; lean_object* v_N_4897_; lean_object* v_V_4898_; lean_object* v_z_4899_; lean_object* v_zabbrev_4900_; lean_object* v_v_4901_; lean_object* v_O_4902_; lean_object* v_X_4903_; lean_object* v_x_4904_; lean_object* v_Z_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4915_; 
v_G_4870_ = lean_ctor_get(v_date_4150_, 0);
v_y_4871_ = lean_ctor_get(v_date_4150_, 1);
v_u_4872_ = lean_ctor_get(v_date_4150_, 2);
v_Y_4873_ = lean_ctor_get(v_date_4150_, 3);
v_D_4874_ = lean_ctor_get(v_date_4150_, 4);
v_M_4875_ = lean_ctor_get(v_date_4150_, 5);
v_L_4876_ = lean_ctor_get(v_date_4150_, 6);
v_d_4877_ = lean_ctor_get(v_date_4150_, 7);
v_Q_4878_ = lean_ctor_get(v_date_4150_, 8);
v_q_4879_ = lean_ctor_get(v_date_4150_, 9);
v_w_4880_ = lean_ctor_get(v_date_4150_, 10);
v_W_4881_ = lean_ctor_get(v_date_4150_, 11);
v_E_4882_ = lean_ctor_get(v_date_4150_, 12);
v_e_4883_ = lean_ctor_get(v_date_4150_, 13);
v_F_4884_ = lean_ctor_get(v_date_4150_, 15);
v_a_4885_ = lean_ctor_get(v_date_4150_, 16);
v_b_4886_ = lean_ctor_get(v_date_4150_, 17);
v_B_4887_ = lean_ctor_get(v_date_4150_, 18);
v_h_4888_ = lean_ctor_get(v_date_4150_, 19);
v_K_4889_ = lean_ctor_get(v_date_4150_, 20);
v_k_4890_ = lean_ctor_get(v_date_4150_, 21);
v_H_4891_ = lean_ctor_get(v_date_4150_, 22);
v_m_4892_ = lean_ctor_get(v_date_4150_, 23);
v_s_4893_ = lean_ctor_get(v_date_4150_, 24);
v_S_4894_ = lean_ctor_get(v_date_4150_, 25);
v_A_4895_ = lean_ctor_get(v_date_4150_, 26);
v_n_4896_ = lean_ctor_get(v_date_4150_, 27);
v_N_4897_ = lean_ctor_get(v_date_4150_, 28);
v_V_4898_ = lean_ctor_get(v_date_4150_, 29);
v_z_4899_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_4900_ = lean_ctor_get(v_date_4150_, 31);
v_v_4901_ = lean_ctor_get(v_date_4150_, 32);
v_O_4902_ = lean_ctor_get(v_date_4150_, 33);
v_X_4903_ = lean_ctor_get(v_date_4150_, 34);
v_x_4904_ = lean_ctor_get(v_date_4150_, 35);
v_Z_4905_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_4915_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_4915_ == 0)
{
lean_object* v_unused_4916_; 
v_unused_4916_ = lean_ctor_get(v_date_4150_, 14);
lean_dec(v_unused_4916_);
v___x_4907_ = v_date_4150_;
v_isShared_4908_ = v_isSharedCheck_4915_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_Z_4905_);
lean_inc(v_x_4904_);
lean_inc(v_X_4903_);
lean_inc(v_O_4902_);
lean_inc(v_v_4901_);
lean_inc(v_zabbrev_4900_);
lean_inc(v_z_4899_);
lean_inc(v_V_4898_);
lean_inc(v_N_4897_);
lean_inc(v_n_4896_);
lean_inc(v_A_4895_);
lean_inc(v_S_4894_);
lean_inc(v_s_4893_);
lean_inc(v_m_4892_);
lean_inc(v_H_4891_);
lean_inc(v_k_4890_);
lean_inc(v_K_4889_);
lean_inc(v_h_4888_);
lean_inc(v_B_4887_);
lean_inc(v_b_4886_);
lean_inc(v_a_4885_);
lean_inc(v_F_4884_);
lean_inc(v_e_4883_);
lean_inc(v_E_4882_);
lean_inc(v_W_4881_);
lean_inc(v_w_4880_);
lean_inc(v_q_4879_);
lean_inc(v_Q_4878_);
lean_inc(v_d_4877_);
lean_inc(v_L_4876_);
lean_inc(v_M_4875_);
lean_inc(v_D_4874_);
lean_inc(v_Y_4873_);
lean_inc(v_u_4872_);
lean_inc(v_y_4871_);
lean_inc(v_G_4870_);
lean_dec(v_date_4150_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4915_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4910_; 
if (v_isShared_4869_ == 0)
{
lean_ctor_set_tag(v___x_4868_, 1);
lean_ctor_set(v___x_4868_, 0, v_data_4152_);
v___x_4910_ = v___x_4868_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v_data_4152_);
v___x_4910_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
lean_object* v___x_4912_; 
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 14, v___x_4910_);
v___x_4912_ = v___x_4907_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v_G_4870_);
lean_ctor_set(v_reuseFailAlloc_4913_, 1, v_y_4871_);
lean_ctor_set(v_reuseFailAlloc_4913_, 2, v_u_4872_);
lean_ctor_set(v_reuseFailAlloc_4913_, 3, v_Y_4873_);
lean_ctor_set(v_reuseFailAlloc_4913_, 4, v_D_4874_);
lean_ctor_set(v_reuseFailAlloc_4913_, 5, v_M_4875_);
lean_ctor_set(v_reuseFailAlloc_4913_, 6, v_L_4876_);
lean_ctor_set(v_reuseFailAlloc_4913_, 7, v_d_4877_);
lean_ctor_set(v_reuseFailAlloc_4913_, 8, v_Q_4878_);
lean_ctor_set(v_reuseFailAlloc_4913_, 9, v_q_4879_);
lean_ctor_set(v_reuseFailAlloc_4913_, 10, v_w_4880_);
lean_ctor_set(v_reuseFailAlloc_4913_, 11, v_W_4881_);
lean_ctor_set(v_reuseFailAlloc_4913_, 12, v_E_4882_);
lean_ctor_set(v_reuseFailAlloc_4913_, 13, v_e_4883_);
lean_ctor_set(v_reuseFailAlloc_4913_, 14, v___x_4910_);
lean_ctor_set(v_reuseFailAlloc_4913_, 15, v_F_4884_);
lean_ctor_set(v_reuseFailAlloc_4913_, 16, v_a_4885_);
lean_ctor_set(v_reuseFailAlloc_4913_, 17, v_b_4886_);
lean_ctor_set(v_reuseFailAlloc_4913_, 18, v_B_4887_);
lean_ctor_set(v_reuseFailAlloc_4913_, 19, v_h_4888_);
lean_ctor_set(v_reuseFailAlloc_4913_, 20, v_K_4889_);
lean_ctor_set(v_reuseFailAlloc_4913_, 21, v_k_4890_);
lean_ctor_set(v_reuseFailAlloc_4913_, 22, v_H_4891_);
lean_ctor_set(v_reuseFailAlloc_4913_, 23, v_m_4892_);
lean_ctor_set(v_reuseFailAlloc_4913_, 24, v_s_4893_);
lean_ctor_set(v_reuseFailAlloc_4913_, 25, v_S_4894_);
lean_ctor_set(v_reuseFailAlloc_4913_, 26, v_A_4895_);
lean_ctor_set(v_reuseFailAlloc_4913_, 27, v_n_4896_);
lean_ctor_set(v_reuseFailAlloc_4913_, 28, v_N_4897_);
lean_ctor_set(v_reuseFailAlloc_4913_, 29, v_V_4898_);
lean_ctor_set(v_reuseFailAlloc_4913_, 30, v_z_4899_);
lean_ctor_set(v_reuseFailAlloc_4913_, 31, v_zabbrev_4900_);
lean_ctor_set(v_reuseFailAlloc_4913_, 32, v_v_4901_);
lean_ctor_set(v_reuseFailAlloc_4913_, 33, v_O_4902_);
lean_ctor_set(v_reuseFailAlloc_4913_, 34, v_X_4903_);
lean_ctor_set(v_reuseFailAlloc_4913_, 35, v_x_4904_);
lean_ctor_set(v_reuseFailAlloc_4913_, 36, v_Z_4905_);
v___x_4912_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
return v___x_4912_;
}
}
}
}
}
case 15:
{
lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4969_; 
v_isSharedCheck_4969_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_4969_ == 0)
{
lean_object* v_unused_4970_; 
v_unused_4970_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_4970_);
v___x_4920_ = v_modifier_4151_;
v_isShared_4921_ = v_isSharedCheck_4969_;
goto v_resetjp_4919_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4969_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v_G_4922_; lean_object* v_y_4923_; lean_object* v_u_4924_; lean_object* v_Y_4925_; lean_object* v_D_4926_; lean_object* v_M_4927_; lean_object* v_L_4928_; lean_object* v_d_4929_; lean_object* v_Q_4930_; lean_object* v_q_4931_; lean_object* v_w_4932_; lean_object* v_W_4933_; lean_object* v_E_4934_; lean_object* v_e_4935_; lean_object* v_c_4936_; lean_object* v_a_4937_; lean_object* v_b_4938_; lean_object* v_B_4939_; lean_object* v_h_4940_; lean_object* v_K_4941_; lean_object* v_k_4942_; lean_object* v_H_4943_; lean_object* v_m_4944_; lean_object* v_s_4945_; lean_object* v_S_4946_; lean_object* v_A_4947_; lean_object* v_n_4948_; lean_object* v_N_4949_; lean_object* v_V_4950_; lean_object* v_z_4951_; lean_object* v_zabbrev_4952_; lean_object* v_v_4953_; lean_object* v_O_4954_; lean_object* v_X_4955_; lean_object* v_x_4956_; lean_object* v_Z_4957_; lean_object* v___x_4959_; uint8_t v_isShared_4960_; uint8_t v_isSharedCheck_4967_; 
v_G_4922_ = lean_ctor_get(v_date_4150_, 0);
v_y_4923_ = lean_ctor_get(v_date_4150_, 1);
v_u_4924_ = lean_ctor_get(v_date_4150_, 2);
v_Y_4925_ = lean_ctor_get(v_date_4150_, 3);
v_D_4926_ = lean_ctor_get(v_date_4150_, 4);
v_M_4927_ = lean_ctor_get(v_date_4150_, 5);
v_L_4928_ = lean_ctor_get(v_date_4150_, 6);
v_d_4929_ = lean_ctor_get(v_date_4150_, 7);
v_Q_4930_ = lean_ctor_get(v_date_4150_, 8);
v_q_4931_ = lean_ctor_get(v_date_4150_, 9);
v_w_4932_ = lean_ctor_get(v_date_4150_, 10);
v_W_4933_ = lean_ctor_get(v_date_4150_, 11);
v_E_4934_ = lean_ctor_get(v_date_4150_, 12);
v_e_4935_ = lean_ctor_get(v_date_4150_, 13);
v_c_4936_ = lean_ctor_get(v_date_4150_, 14);
v_a_4937_ = lean_ctor_get(v_date_4150_, 16);
v_b_4938_ = lean_ctor_get(v_date_4150_, 17);
v_B_4939_ = lean_ctor_get(v_date_4150_, 18);
v_h_4940_ = lean_ctor_get(v_date_4150_, 19);
v_K_4941_ = lean_ctor_get(v_date_4150_, 20);
v_k_4942_ = lean_ctor_get(v_date_4150_, 21);
v_H_4943_ = lean_ctor_get(v_date_4150_, 22);
v_m_4944_ = lean_ctor_get(v_date_4150_, 23);
v_s_4945_ = lean_ctor_get(v_date_4150_, 24);
v_S_4946_ = lean_ctor_get(v_date_4150_, 25);
v_A_4947_ = lean_ctor_get(v_date_4150_, 26);
v_n_4948_ = lean_ctor_get(v_date_4150_, 27);
v_N_4949_ = lean_ctor_get(v_date_4150_, 28);
v_V_4950_ = lean_ctor_get(v_date_4150_, 29);
v_z_4951_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_4952_ = lean_ctor_get(v_date_4150_, 31);
v_v_4953_ = lean_ctor_get(v_date_4150_, 32);
v_O_4954_ = lean_ctor_get(v_date_4150_, 33);
v_X_4955_ = lean_ctor_get(v_date_4150_, 34);
v_x_4956_ = lean_ctor_get(v_date_4150_, 35);
v_Z_4957_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_4967_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_4967_ == 0)
{
lean_object* v_unused_4968_; 
v_unused_4968_ = lean_ctor_get(v_date_4150_, 15);
lean_dec(v_unused_4968_);
v___x_4959_ = v_date_4150_;
v_isShared_4960_ = v_isSharedCheck_4967_;
goto v_resetjp_4958_;
}
else
{
lean_inc(v_Z_4957_);
lean_inc(v_x_4956_);
lean_inc(v_X_4955_);
lean_inc(v_O_4954_);
lean_inc(v_v_4953_);
lean_inc(v_zabbrev_4952_);
lean_inc(v_z_4951_);
lean_inc(v_V_4950_);
lean_inc(v_N_4949_);
lean_inc(v_n_4948_);
lean_inc(v_A_4947_);
lean_inc(v_S_4946_);
lean_inc(v_s_4945_);
lean_inc(v_m_4944_);
lean_inc(v_H_4943_);
lean_inc(v_k_4942_);
lean_inc(v_K_4941_);
lean_inc(v_h_4940_);
lean_inc(v_B_4939_);
lean_inc(v_b_4938_);
lean_inc(v_a_4937_);
lean_inc(v_c_4936_);
lean_inc(v_e_4935_);
lean_inc(v_E_4934_);
lean_inc(v_W_4933_);
lean_inc(v_w_4932_);
lean_inc(v_q_4931_);
lean_inc(v_Q_4930_);
lean_inc(v_d_4929_);
lean_inc(v_L_4928_);
lean_inc(v_M_4927_);
lean_inc(v_D_4926_);
lean_inc(v_Y_4925_);
lean_inc(v_u_4924_);
lean_inc(v_y_4923_);
lean_inc(v_G_4922_);
lean_dec(v_date_4150_);
v___x_4959_ = lean_box(0);
v_isShared_4960_ = v_isSharedCheck_4967_;
goto v_resetjp_4958_;
}
v_resetjp_4958_:
{
lean_object* v___x_4962_; 
if (v_isShared_4921_ == 0)
{
lean_ctor_set_tag(v___x_4920_, 1);
lean_ctor_set(v___x_4920_, 0, v_data_4152_);
v___x_4962_ = v___x_4920_;
goto v_reusejp_4961_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v_data_4152_);
v___x_4962_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4961_;
}
v_reusejp_4961_:
{
lean_object* v___x_4964_; 
if (v_isShared_4960_ == 0)
{
lean_ctor_set(v___x_4959_, 15, v___x_4962_);
v___x_4964_ = v___x_4959_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4965_; 
v_reuseFailAlloc_4965_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4965_, 0, v_G_4922_);
lean_ctor_set(v_reuseFailAlloc_4965_, 1, v_y_4923_);
lean_ctor_set(v_reuseFailAlloc_4965_, 2, v_u_4924_);
lean_ctor_set(v_reuseFailAlloc_4965_, 3, v_Y_4925_);
lean_ctor_set(v_reuseFailAlloc_4965_, 4, v_D_4926_);
lean_ctor_set(v_reuseFailAlloc_4965_, 5, v_M_4927_);
lean_ctor_set(v_reuseFailAlloc_4965_, 6, v_L_4928_);
lean_ctor_set(v_reuseFailAlloc_4965_, 7, v_d_4929_);
lean_ctor_set(v_reuseFailAlloc_4965_, 8, v_Q_4930_);
lean_ctor_set(v_reuseFailAlloc_4965_, 9, v_q_4931_);
lean_ctor_set(v_reuseFailAlloc_4965_, 10, v_w_4932_);
lean_ctor_set(v_reuseFailAlloc_4965_, 11, v_W_4933_);
lean_ctor_set(v_reuseFailAlloc_4965_, 12, v_E_4934_);
lean_ctor_set(v_reuseFailAlloc_4965_, 13, v_e_4935_);
lean_ctor_set(v_reuseFailAlloc_4965_, 14, v_c_4936_);
lean_ctor_set(v_reuseFailAlloc_4965_, 15, v___x_4962_);
lean_ctor_set(v_reuseFailAlloc_4965_, 16, v_a_4937_);
lean_ctor_set(v_reuseFailAlloc_4965_, 17, v_b_4938_);
lean_ctor_set(v_reuseFailAlloc_4965_, 18, v_B_4939_);
lean_ctor_set(v_reuseFailAlloc_4965_, 19, v_h_4940_);
lean_ctor_set(v_reuseFailAlloc_4965_, 20, v_K_4941_);
lean_ctor_set(v_reuseFailAlloc_4965_, 21, v_k_4942_);
lean_ctor_set(v_reuseFailAlloc_4965_, 22, v_H_4943_);
lean_ctor_set(v_reuseFailAlloc_4965_, 23, v_m_4944_);
lean_ctor_set(v_reuseFailAlloc_4965_, 24, v_s_4945_);
lean_ctor_set(v_reuseFailAlloc_4965_, 25, v_S_4946_);
lean_ctor_set(v_reuseFailAlloc_4965_, 26, v_A_4947_);
lean_ctor_set(v_reuseFailAlloc_4965_, 27, v_n_4948_);
lean_ctor_set(v_reuseFailAlloc_4965_, 28, v_N_4949_);
lean_ctor_set(v_reuseFailAlloc_4965_, 29, v_V_4950_);
lean_ctor_set(v_reuseFailAlloc_4965_, 30, v_z_4951_);
lean_ctor_set(v_reuseFailAlloc_4965_, 31, v_zabbrev_4952_);
lean_ctor_set(v_reuseFailAlloc_4965_, 32, v_v_4953_);
lean_ctor_set(v_reuseFailAlloc_4965_, 33, v_O_4954_);
lean_ctor_set(v_reuseFailAlloc_4965_, 34, v_X_4955_);
lean_ctor_set(v_reuseFailAlloc_4965_, 35, v_x_4956_);
lean_ctor_set(v_reuseFailAlloc_4965_, 36, v_Z_4957_);
v___x_4964_ = v_reuseFailAlloc_4965_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
return v___x_4964_;
}
}
}
}
}
case 16:
{
lean_object* v_G_4971_; lean_object* v_y_4972_; lean_object* v_u_4973_; lean_object* v_Y_4974_; lean_object* v_D_4975_; lean_object* v_M_4976_; lean_object* v_L_4977_; lean_object* v_d_4978_; lean_object* v_Q_4979_; lean_object* v_q_4980_; lean_object* v_w_4981_; lean_object* v_W_4982_; lean_object* v_E_4983_; lean_object* v_e_4984_; lean_object* v_c_4985_; lean_object* v_F_4986_; lean_object* v_b_4987_; lean_object* v_B_4988_; lean_object* v_h_4989_; lean_object* v_K_4990_; lean_object* v_k_4991_; lean_object* v_H_4992_; lean_object* v_m_4993_; lean_object* v_s_4994_; lean_object* v_S_4995_; lean_object* v_A_4996_; lean_object* v_n_4997_; lean_object* v_N_4998_; lean_object* v_V_4999_; lean_object* v_z_5000_; lean_object* v_zabbrev_5001_; lean_object* v_v_5002_; lean_object* v_O_5003_; lean_object* v_X_5004_; lean_object* v_x_5005_; lean_object* v_Z_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5014_; 
lean_dec_ref_known(v_modifier_4151_, 0);
v_G_4971_ = lean_ctor_get(v_date_4150_, 0);
v_y_4972_ = lean_ctor_get(v_date_4150_, 1);
v_u_4973_ = lean_ctor_get(v_date_4150_, 2);
v_Y_4974_ = lean_ctor_get(v_date_4150_, 3);
v_D_4975_ = lean_ctor_get(v_date_4150_, 4);
v_M_4976_ = lean_ctor_get(v_date_4150_, 5);
v_L_4977_ = lean_ctor_get(v_date_4150_, 6);
v_d_4978_ = lean_ctor_get(v_date_4150_, 7);
v_Q_4979_ = lean_ctor_get(v_date_4150_, 8);
v_q_4980_ = lean_ctor_get(v_date_4150_, 9);
v_w_4981_ = lean_ctor_get(v_date_4150_, 10);
v_W_4982_ = lean_ctor_get(v_date_4150_, 11);
v_E_4983_ = lean_ctor_get(v_date_4150_, 12);
v_e_4984_ = lean_ctor_get(v_date_4150_, 13);
v_c_4985_ = lean_ctor_get(v_date_4150_, 14);
v_F_4986_ = lean_ctor_get(v_date_4150_, 15);
v_b_4987_ = lean_ctor_get(v_date_4150_, 17);
v_B_4988_ = lean_ctor_get(v_date_4150_, 18);
v_h_4989_ = lean_ctor_get(v_date_4150_, 19);
v_K_4990_ = lean_ctor_get(v_date_4150_, 20);
v_k_4991_ = lean_ctor_get(v_date_4150_, 21);
v_H_4992_ = lean_ctor_get(v_date_4150_, 22);
v_m_4993_ = lean_ctor_get(v_date_4150_, 23);
v_s_4994_ = lean_ctor_get(v_date_4150_, 24);
v_S_4995_ = lean_ctor_get(v_date_4150_, 25);
v_A_4996_ = lean_ctor_get(v_date_4150_, 26);
v_n_4997_ = lean_ctor_get(v_date_4150_, 27);
v_N_4998_ = lean_ctor_get(v_date_4150_, 28);
v_V_4999_ = lean_ctor_get(v_date_4150_, 29);
v_z_5000_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_5001_ = lean_ctor_get(v_date_4150_, 31);
v_v_5002_ = lean_ctor_get(v_date_4150_, 32);
v_O_5003_ = lean_ctor_get(v_date_4150_, 33);
v_X_5004_ = lean_ctor_get(v_date_4150_, 34);
v_x_5005_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5006_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5014_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5014_ == 0)
{
lean_object* v_unused_5015_; 
v_unused_5015_ = lean_ctor_get(v_date_4150_, 16);
lean_dec(v_unused_5015_);
v___x_5008_ = v_date_4150_;
v_isShared_5009_ = v_isSharedCheck_5014_;
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
lean_inc(v_F_4986_);
lean_inc(v_c_4985_);
lean_inc(v_e_4984_);
lean_inc(v_E_4983_);
lean_inc(v_W_4982_);
lean_inc(v_w_4981_);
lean_inc(v_q_4980_);
lean_inc(v_Q_4979_);
lean_inc(v_d_4978_);
lean_inc(v_L_4977_);
lean_inc(v_M_4976_);
lean_inc(v_D_4975_);
lean_inc(v_Y_4974_);
lean_inc(v_u_4973_);
lean_inc(v_y_4972_);
lean_inc(v_G_4971_);
lean_dec(v_date_4150_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5014_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v___x_5010_; lean_object* v___x_5012_; 
v___x_5010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5010_, 0, v_data_4152_);
if (v_isShared_5009_ == 0)
{
lean_ctor_set(v___x_5008_, 16, v___x_5010_);
v___x_5012_ = v___x_5008_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v_G_4971_);
lean_ctor_set(v_reuseFailAlloc_5013_, 1, v_y_4972_);
lean_ctor_set(v_reuseFailAlloc_5013_, 2, v_u_4973_);
lean_ctor_set(v_reuseFailAlloc_5013_, 3, v_Y_4974_);
lean_ctor_set(v_reuseFailAlloc_5013_, 4, v_D_4975_);
lean_ctor_set(v_reuseFailAlloc_5013_, 5, v_M_4976_);
lean_ctor_set(v_reuseFailAlloc_5013_, 6, v_L_4977_);
lean_ctor_set(v_reuseFailAlloc_5013_, 7, v_d_4978_);
lean_ctor_set(v_reuseFailAlloc_5013_, 8, v_Q_4979_);
lean_ctor_set(v_reuseFailAlloc_5013_, 9, v_q_4980_);
lean_ctor_set(v_reuseFailAlloc_5013_, 10, v_w_4981_);
lean_ctor_set(v_reuseFailAlloc_5013_, 11, v_W_4982_);
lean_ctor_set(v_reuseFailAlloc_5013_, 12, v_E_4983_);
lean_ctor_set(v_reuseFailAlloc_5013_, 13, v_e_4984_);
lean_ctor_set(v_reuseFailAlloc_5013_, 14, v_c_4985_);
lean_ctor_set(v_reuseFailAlloc_5013_, 15, v_F_4986_);
lean_ctor_set(v_reuseFailAlloc_5013_, 16, v___x_5010_);
lean_ctor_set(v_reuseFailAlloc_5013_, 17, v_b_4987_);
lean_ctor_set(v_reuseFailAlloc_5013_, 18, v_B_4988_);
lean_ctor_set(v_reuseFailAlloc_5013_, 19, v_h_4989_);
lean_ctor_set(v_reuseFailAlloc_5013_, 20, v_K_4990_);
lean_ctor_set(v_reuseFailAlloc_5013_, 21, v_k_4991_);
lean_ctor_set(v_reuseFailAlloc_5013_, 22, v_H_4992_);
lean_ctor_set(v_reuseFailAlloc_5013_, 23, v_m_4993_);
lean_ctor_set(v_reuseFailAlloc_5013_, 24, v_s_4994_);
lean_ctor_set(v_reuseFailAlloc_5013_, 25, v_S_4995_);
lean_ctor_set(v_reuseFailAlloc_5013_, 26, v_A_4996_);
lean_ctor_set(v_reuseFailAlloc_5013_, 27, v_n_4997_);
lean_ctor_set(v_reuseFailAlloc_5013_, 28, v_N_4998_);
lean_ctor_set(v_reuseFailAlloc_5013_, 29, v_V_4999_);
lean_ctor_set(v_reuseFailAlloc_5013_, 30, v_z_5000_);
lean_ctor_set(v_reuseFailAlloc_5013_, 31, v_zabbrev_5001_);
lean_ctor_set(v_reuseFailAlloc_5013_, 32, v_v_5002_);
lean_ctor_set(v_reuseFailAlloc_5013_, 33, v_O_5003_);
lean_ctor_set(v_reuseFailAlloc_5013_, 34, v_X_5004_);
lean_ctor_set(v_reuseFailAlloc_5013_, 35, v_x_5005_);
lean_ctor_set(v_reuseFailAlloc_5013_, 36, v_Z_5006_);
v___x_5012_ = v_reuseFailAlloc_5013_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
return v___x_5012_;
}
}
}
case 17:
{
lean_object* v_G_5016_; lean_object* v_y_5017_; lean_object* v_u_5018_; lean_object* v_Y_5019_; lean_object* v_D_5020_; lean_object* v_M_5021_; lean_object* v_L_5022_; lean_object* v_d_5023_; lean_object* v_Q_5024_; lean_object* v_q_5025_; lean_object* v_w_5026_; lean_object* v_W_5027_; lean_object* v_E_5028_; lean_object* v_e_5029_; lean_object* v_c_5030_; lean_object* v_F_5031_; lean_object* v_a_5032_; lean_object* v_B_5033_; lean_object* v_h_5034_; lean_object* v_K_5035_; lean_object* v_k_5036_; lean_object* v_H_5037_; lean_object* v_m_5038_; lean_object* v_s_5039_; lean_object* v_S_5040_; lean_object* v_A_5041_; lean_object* v_n_5042_; lean_object* v_N_5043_; lean_object* v_V_5044_; lean_object* v_z_5045_; lean_object* v_zabbrev_5046_; lean_object* v_v_5047_; lean_object* v_O_5048_; lean_object* v_X_5049_; lean_object* v_x_5050_; lean_object* v_Z_5051_; lean_object* v___x_5053_; uint8_t v_isShared_5054_; uint8_t v_isSharedCheck_5059_; 
lean_dec_ref_known(v_modifier_4151_, 0);
v_G_5016_ = lean_ctor_get(v_date_4150_, 0);
v_y_5017_ = lean_ctor_get(v_date_4150_, 1);
v_u_5018_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5019_ = lean_ctor_get(v_date_4150_, 3);
v_D_5020_ = lean_ctor_get(v_date_4150_, 4);
v_M_5021_ = lean_ctor_get(v_date_4150_, 5);
v_L_5022_ = lean_ctor_get(v_date_4150_, 6);
v_d_5023_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5024_ = lean_ctor_get(v_date_4150_, 8);
v_q_5025_ = lean_ctor_get(v_date_4150_, 9);
v_w_5026_ = lean_ctor_get(v_date_4150_, 10);
v_W_5027_ = lean_ctor_get(v_date_4150_, 11);
v_E_5028_ = lean_ctor_get(v_date_4150_, 12);
v_e_5029_ = lean_ctor_get(v_date_4150_, 13);
v_c_5030_ = lean_ctor_get(v_date_4150_, 14);
v_F_5031_ = lean_ctor_get(v_date_4150_, 15);
v_a_5032_ = lean_ctor_get(v_date_4150_, 16);
v_B_5033_ = lean_ctor_get(v_date_4150_, 18);
v_h_5034_ = lean_ctor_get(v_date_4150_, 19);
v_K_5035_ = lean_ctor_get(v_date_4150_, 20);
v_k_5036_ = lean_ctor_get(v_date_4150_, 21);
v_H_5037_ = lean_ctor_get(v_date_4150_, 22);
v_m_5038_ = lean_ctor_get(v_date_4150_, 23);
v_s_5039_ = lean_ctor_get(v_date_4150_, 24);
v_S_5040_ = lean_ctor_get(v_date_4150_, 25);
v_A_5041_ = lean_ctor_get(v_date_4150_, 26);
v_n_5042_ = lean_ctor_get(v_date_4150_, 27);
v_N_5043_ = lean_ctor_get(v_date_4150_, 28);
v_V_5044_ = lean_ctor_get(v_date_4150_, 29);
v_z_5045_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_5046_ = lean_ctor_get(v_date_4150_, 31);
v_v_5047_ = lean_ctor_get(v_date_4150_, 32);
v_O_5048_ = lean_ctor_get(v_date_4150_, 33);
v_X_5049_ = lean_ctor_get(v_date_4150_, 34);
v_x_5050_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5051_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5059_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5059_ == 0)
{
lean_object* v_unused_5060_; 
v_unused_5060_ = lean_ctor_get(v_date_4150_, 17);
lean_dec(v_unused_5060_);
v___x_5053_ = v_date_4150_;
v_isShared_5054_ = v_isSharedCheck_5059_;
goto v_resetjp_5052_;
}
else
{
lean_inc(v_Z_5051_);
lean_inc(v_x_5050_);
lean_inc(v_X_5049_);
lean_inc(v_O_5048_);
lean_inc(v_v_5047_);
lean_inc(v_zabbrev_5046_);
lean_inc(v_z_5045_);
lean_inc(v_V_5044_);
lean_inc(v_N_5043_);
lean_inc(v_n_5042_);
lean_inc(v_A_5041_);
lean_inc(v_S_5040_);
lean_inc(v_s_5039_);
lean_inc(v_m_5038_);
lean_inc(v_H_5037_);
lean_inc(v_k_5036_);
lean_inc(v_K_5035_);
lean_inc(v_h_5034_);
lean_inc(v_B_5033_);
lean_inc(v_a_5032_);
lean_inc(v_F_5031_);
lean_inc(v_c_5030_);
lean_inc(v_e_5029_);
lean_inc(v_E_5028_);
lean_inc(v_W_5027_);
lean_inc(v_w_5026_);
lean_inc(v_q_5025_);
lean_inc(v_Q_5024_);
lean_inc(v_d_5023_);
lean_inc(v_L_5022_);
lean_inc(v_M_5021_);
lean_inc(v_D_5020_);
lean_inc(v_Y_5019_);
lean_inc(v_u_5018_);
lean_inc(v_y_5017_);
lean_inc(v_G_5016_);
lean_dec(v_date_4150_);
v___x_5053_ = lean_box(0);
v_isShared_5054_ = v_isSharedCheck_5059_;
goto v_resetjp_5052_;
}
v_resetjp_5052_:
{
lean_object* v___x_5055_; lean_object* v___x_5057_; 
v___x_5055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5055_, 0, v_data_4152_);
if (v_isShared_5054_ == 0)
{
lean_ctor_set(v___x_5053_, 17, v___x_5055_);
v___x_5057_ = v___x_5053_;
goto v_reusejp_5056_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v_G_5016_);
lean_ctor_set(v_reuseFailAlloc_5058_, 1, v_y_5017_);
lean_ctor_set(v_reuseFailAlloc_5058_, 2, v_u_5018_);
lean_ctor_set(v_reuseFailAlloc_5058_, 3, v_Y_5019_);
lean_ctor_set(v_reuseFailAlloc_5058_, 4, v_D_5020_);
lean_ctor_set(v_reuseFailAlloc_5058_, 5, v_M_5021_);
lean_ctor_set(v_reuseFailAlloc_5058_, 6, v_L_5022_);
lean_ctor_set(v_reuseFailAlloc_5058_, 7, v_d_5023_);
lean_ctor_set(v_reuseFailAlloc_5058_, 8, v_Q_5024_);
lean_ctor_set(v_reuseFailAlloc_5058_, 9, v_q_5025_);
lean_ctor_set(v_reuseFailAlloc_5058_, 10, v_w_5026_);
lean_ctor_set(v_reuseFailAlloc_5058_, 11, v_W_5027_);
lean_ctor_set(v_reuseFailAlloc_5058_, 12, v_E_5028_);
lean_ctor_set(v_reuseFailAlloc_5058_, 13, v_e_5029_);
lean_ctor_set(v_reuseFailAlloc_5058_, 14, v_c_5030_);
lean_ctor_set(v_reuseFailAlloc_5058_, 15, v_F_5031_);
lean_ctor_set(v_reuseFailAlloc_5058_, 16, v_a_5032_);
lean_ctor_set(v_reuseFailAlloc_5058_, 17, v___x_5055_);
lean_ctor_set(v_reuseFailAlloc_5058_, 18, v_B_5033_);
lean_ctor_set(v_reuseFailAlloc_5058_, 19, v_h_5034_);
lean_ctor_set(v_reuseFailAlloc_5058_, 20, v_K_5035_);
lean_ctor_set(v_reuseFailAlloc_5058_, 21, v_k_5036_);
lean_ctor_set(v_reuseFailAlloc_5058_, 22, v_H_5037_);
lean_ctor_set(v_reuseFailAlloc_5058_, 23, v_m_5038_);
lean_ctor_set(v_reuseFailAlloc_5058_, 24, v_s_5039_);
lean_ctor_set(v_reuseFailAlloc_5058_, 25, v_S_5040_);
lean_ctor_set(v_reuseFailAlloc_5058_, 26, v_A_5041_);
lean_ctor_set(v_reuseFailAlloc_5058_, 27, v_n_5042_);
lean_ctor_set(v_reuseFailAlloc_5058_, 28, v_N_5043_);
lean_ctor_set(v_reuseFailAlloc_5058_, 29, v_V_5044_);
lean_ctor_set(v_reuseFailAlloc_5058_, 30, v_z_5045_);
lean_ctor_set(v_reuseFailAlloc_5058_, 31, v_zabbrev_5046_);
lean_ctor_set(v_reuseFailAlloc_5058_, 32, v_v_5047_);
lean_ctor_set(v_reuseFailAlloc_5058_, 33, v_O_5048_);
lean_ctor_set(v_reuseFailAlloc_5058_, 34, v_X_5049_);
lean_ctor_set(v_reuseFailAlloc_5058_, 35, v_x_5050_);
lean_ctor_set(v_reuseFailAlloc_5058_, 36, v_Z_5051_);
v___x_5057_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5056_;
}
v_reusejp_5056_:
{
return v___x_5057_;
}
}
}
case 18:
{
lean_object* v_G_5061_; lean_object* v_y_5062_; lean_object* v_u_5063_; lean_object* v_Y_5064_; lean_object* v_D_5065_; lean_object* v_M_5066_; lean_object* v_L_5067_; lean_object* v_d_5068_; lean_object* v_Q_5069_; lean_object* v_q_5070_; lean_object* v_w_5071_; lean_object* v_W_5072_; lean_object* v_E_5073_; lean_object* v_e_5074_; lean_object* v_c_5075_; lean_object* v_F_5076_; lean_object* v_a_5077_; lean_object* v_b_5078_; lean_object* v_h_5079_; lean_object* v_K_5080_; lean_object* v_k_5081_; lean_object* v_H_5082_; lean_object* v_m_5083_; lean_object* v_s_5084_; lean_object* v_S_5085_; lean_object* v_A_5086_; lean_object* v_n_5087_; lean_object* v_N_5088_; lean_object* v_V_5089_; lean_object* v_z_5090_; lean_object* v_zabbrev_5091_; lean_object* v_v_5092_; lean_object* v_O_5093_; lean_object* v_X_5094_; lean_object* v_x_5095_; lean_object* v_Z_5096_; lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5104_; 
lean_dec_ref_known(v_modifier_4151_, 0);
v_G_5061_ = lean_ctor_get(v_date_4150_, 0);
v_y_5062_ = lean_ctor_get(v_date_4150_, 1);
v_u_5063_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5064_ = lean_ctor_get(v_date_4150_, 3);
v_D_5065_ = lean_ctor_get(v_date_4150_, 4);
v_M_5066_ = lean_ctor_get(v_date_4150_, 5);
v_L_5067_ = lean_ctor_get(v_date_4150_, 6);
v_d_5068_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5069_ = lean_ctor_get(v_date_4150_, 8);
v_q_5070_ = lean_ctor_get(v_date_4150_, 9);
v_w_5071_ = lean_ctor_get(v_date_4150_, 10);
v_W_5072_ = lean_ctor_get(v_date_4150_, 11);
v_E_5073_ = lean_ctor_get(v_date_4150_, 12);
v_e_5074_ = lean_ctor_get(v_date_4150_, 13);
v_c_5075_ = lean_ctor_get(v_date_4150_, 14);
v_F_5076_ = lean_ctor_get(v_date_4150_, 15);
v_a_5077_ = lean_ctor_get(v_date_4150_, 16);
v_b_5078_ = lean_ctor_get(v_date_4150_, 17);
v_h_5079_ = lean_ctor_get(v_date_4150_, 19);
v_K_5080_ = lean_ctor_get(v_date_4150_, 20);
v_k_5081_ = lean_ctor_get(v_date_4150_, 21);
v_H_5082_ = lean_ctor_get(v_date_4150_, 22);
v_m_5083_ = lean_ctor_get(v_date_4150_, 23);
v_s_5084_ = lean_ctor_get(v_date_4150_, 24);
v_S_5085_ = lean_ctor_get(v_date_4150_, 25);
v_A_5086_ = lean_ctor_get(v_date_4150_, 26);
v_n_5087_ = lean_ctor_get(v_date_4150_, 27);
v_N_5088_ = lean_ctor_get(v_date_4150_, 28);
v_V_5089_ = lean_ctor_get(v_date_4150_, 29);
v_z_5090_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_5091_ = lean_ctor_get(v_date_4150_, 31);
v_v_5092_ = lean_ctor_get(v_date_4150_, 32);
v_O_5093_ = lean_ctor_get(v_date_4150_, 33);
v_X_5094_ = lean_ctor_get(v_date_4150_, 34);
v_x_5095_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5096_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5104_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5104_ == 0)
{
lean_object* v_unused_5105_; 
v_unused_5105_ = lean_ctor_get(v_date_4150_, 18);
lean_dec(v_unused_5105_);
v___x_5098_ = v_date_4150_;
v_isShared_5099_ = v_isSharedCheck_5104_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_Z_5096_);
lean_inc(v_x_5095_);
lean_inc(v_X_5094_);
lean_inc(v_O_5093_);
lean_inc(v_v_5092_);
lean_inc(v_zabbrev_5091_);
lean_inc(v_z_5090_);
lean_inc(v_V_5089_);
lean_inc(v_N_5088_);
lean_inc(v_n_5087_);
lean_inc(v_A_5086_);
lean_inc(v_S_5085_);
lean_inc(v_s_5084_);
lean_inc(v_m_5083_);
lean_inc(v_H_5082_);
lean_inc(v_k_5081_);
lean_inc(v_K_5080_);
lean_inc(v_h_5079_);
lean_inc(v_b_5078_);
lean_inc(v_a_5077_);
lean_inc(v_F_5076_);
lean_inc(v_c_5075_);
lean_inc(v_e_5074_);
lean_inc(v_E_5073_);
lean_inc(v_W_5072_);
lean_inc(v_w_5071_);
lean_inc(v_q_5070_);
lean_inc(v_Q_5069_);
lean_inc(v_d_5068_);
lean_inc(v_L_5067_);
lean_inc(v_M_5066_);
lean_inc(v_D_5065_);
lean_inc(v_Y_5064_);
lean_inc(v_u_5063_);
lean_inc(v_y_5062_);
lean_inc(v_G_5061_);
lean_dec(v_date_4150_);
v___x_5098_ = lean_box(0);
v_isShared_5099_ = v_isSharedCheck_5104_;
goto v_resetjp_5097_;
}
v_resetjp_5097_:
{
lean_object* v___x_5100_; lean_object* v___x_5102_; 
v___x_5100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5100_, 0, v_data_4152_);
if (v_isShared_5099_ == 0)
{
lean_ctor_set(v___x_5098_, 18, v___x_5100_);
v___x_5102_ = v___x_5098_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_G_5061_);
lean_ctor_set(v_reuseFailAlloc_5103_, 1, v_y_5062_);
lean_ctor_set(v_reuseFailAlloc_5103_, 2, v_u_5063_);
lean_ctor_set(v_reuseFailAlloc_5103_, 3, v_Y_5064_);
lean_ctor_set(v_reuseFailAlloc_5103_, 4, v_D_5065_);
lean_ctor_set(v_reuseFailAlloc_5103_, 5, v_M_5066_);
lean_ctor_set(v_reuseFailAlloc_5103_, 6, v_L_5067_);
lean_ctor_set(v_reuseFailAlloc_5103_, 7, v_d_5068_);
lean_ctor_set(v_reuseFailAlloc_5103_, 8, v_Q_5069_);
lean_ctor_set(v_reuseFailAlloc_5103_, 9, v_q_5070_);
lean_ctor_set(v_reuseFailAlloc_5103_, 10, v_w_5071_);
lean_ctor_set(v_reuseFailAlloc_5103_, 11, v_W_5072_);
lean_ctor_set(v_reuseFailAlloc_5103_, 12, v_E_5073_);
lean_ctor_set(v_reuseFailAlloc_5103_, 13, v_e_5074_);
lean_ctor_set(v_reuseFailAlloc_5103_, 14, v_c_5075_);
lean_ctor_set(v_reuseFailAlloc_5103_, 15, v_F_5076_);
lean_ctor_set(v_reuseFailAlloc_5103_, 16, v_a_5077_);
lean_ctor_set(v_reuseFailAlloc_5103_, 17, v_b_5078_);
lean_ctor_set(v_reuseFailAlloc_5103_, 18, v___x_5100_);
lean_ctor_set(v_reuseFailAlloc_5103_, 19, v_h_5079_);
lean_ctor_set(v_reuseFailAlloc_5103_, 20, v_K_5080_);
lean_ctor_set(v_reuseFailAlloc_5103_, 21, v_k_5081_);
lean_ctor_set(v_reuseFailAlloc_5103_, 22, v_H_5082_);
lean_ctor_set(v_reuseFailAlloc_5103_, 23, v_m_5083_);
lean_ctor_set(v_reuseFailAlloc_5103_, 24, v_s_5084_);
lean_ctor_set(v_reuseFailAlloc_5103_, 25, v_S_5085_);
lean_ctor_set(v_reuseFailAlloc_5103_, 26, v_A_5086_);
lean_ctor_set(v_reuseFailAlloc_5103_, 27, v_n_5087_);
lean_ctor_set(v_reuseFailAlloc_5103_, 28, v_N_5088_);
lean_ctor_set(v_reuseFailAlloc_5103_, 29, v_V_5089_);
lean_ctor_set(v_reuseFailAlloc_5103_, 30, v_z_5090_);
lean_ctor_set(v_reuseFailAlloc_5103_, 31, v_zabbrev_5091_);
lean_ctor_set(v_reuseFailAlloc_5103_, 32, v_v_5092_);
lean_ctor_set(v_reuseFailAlloc_5103_, 33, v_O_5093_);
lean_ctor_set(v_reuseFailAlloc_5103_, 34, v_X_5094_);
lean_ctor_set(v_reuseFailAlloc_5103_, 35, v_x_5095_);
lean_ctor_set(v_reuseFailAlloc_5103_, 36, v_Z_5096_);
v___x_5102_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5101_;
}
v_reusejp_5101_:
{
return v___x_5102_;
}
}
}
case 19:
{
lean_object* v___x_5107_; uint8_t v_isShared_5108_; uint8_t v_isSharedCheck_5156_; 
v_isSharedCheck_5156_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_5156_ == 0)
{
lean_object* v_unused_5157_; 
v_unused_5157_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_5157_);
v___x_5107_ = v_modifier_4151_;
v_isShared_5108_ = v_isSharedCheck_5156_;
goto v_resetjp_5106_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_5107_ = lean_box(0);
v_isShared_5108_ = v_isSharedCheck_5156_;
goto v_resetjp_5106_;
}
v_resetjp_5106_:
{
lean_object* v_G_5109_; lean_object* v_y_5110_; lean_object* v_u_5111_; lean_object* v_Y_5112_; lean_object* v_D_5113_; lean_object* v_M_5114_; lean_object* v_L_5115_; lean_object* v_d_5116_; lean_object* v_Q_5117_; lean_object* v_q_5118_; lean_object* v_w_5119_; lean_object* v_W_5120_; lean_object* v_E_5121_; lean_object* v_e_5122_; lean_object* v_c_5123_; lean_object* v_F_5124_; lean_object* v_a_5125_; lean_object* v_b_5126_; lean_object* v_B_5127_; lean_object* v_K_5128_; lean_object* v_k_5129_; lean_object* v_H_5130_; lean_object* v_m_5131_; lean_object* v_s_5132_; lean_object* v_S_5133_; lean_object* v_A_5134_; lean_object* v_n_5135_; lean_object* v_N_5136_; lean_object* v_V_5137_; lean_object* v_z_5138_; lean_object* v_zabbrev_5139_; lean_object* v_v_5140_; lean_object* v_O_5141_; lean_object* v_X_5142_; lean_object* v_x_5143_; lean_object* v_Z_5144_; lean_object* v___x_5146_; uint8_t v_isShared_5147_; uint8_t v_isSharedCheck_5154_; 
v_G_5109_ = lean_ctor_get(v_date_4150_, 0);
v_y_5110_ = lean_ctor_get(v_date_4150_, 1);
v_u_5111_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5112_ = lean_ctor_get(v_date_4150_, 3);
v_D_5113_ = lean_ctor_get(v_date_4150_, 4);
v_M_5114_ = lean_ctor_get(v_date_4150_, 5);
v_L_5115_ = lean_ctor_get(v_date_4150_, 6);
v_d_5116_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5117_ = lean_ctor_get(v_date_4150_, 8);
v_q_5118_ = lean_ctor_get(v_date_4150_, 9);
v_w_5119_ = lean_ctor_get(v_date_4150_, 10);
v_W_5120_ = lean_ctor_get(v_date_4150_, 11);
v_E_5121_ = lean_ctor_get(v_date_4150_, 12);
v_e_5122_ = lean_ctor_get(v_date_4150_, 13);
v_c_5123_ = lean_ctor_get(v_date_4150_, 14);
v_F_5124_ = lean_ctor_get(v_date_4150_, 15);
v_a_5125_ = lean_ctor_get(v_date_4150_, 16);
v_b_5126_ = lean_ctor_get(v_date_4150_, 17);
v_B_5127_ = lean_ctor_get(v_date_4150_, 18);
v_K_5128_ = lean_ctor_get(v_date_4150_, 20);
v_k_5129_ = lean_ctor_get(v_date_4150_, 21);
v_H_5130_ = lean_ctor_get(v_date_4150_, 22);
v_m_5131_ = lean_ctor_get(v_date_4150_, 23);
v_s_5132_ = lean_ctor_get(v_date_4150_, 24);
v_S_5133_ = lean_ctor_get(v_date_4150_, 25);
v_A_5134_ = lean_ctor_get(v_date_4150_, 26);
v_n_5135_ = lean_ctor_get(v_date_4150_, 27);
v_N_5136_ = lean_ctor_get(v_date_4150_, 28);
v_V_5137_ = lean_ctor_get(v_date_4150_, 29);
v_z_5138_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_5139_ = lean_ctor_get(v_date_4150_, 31);
v_v_5140_ = lean_ctor_get(v_date_4150_, 32);
v_O_5141_ = lean_ctor_get(v_date_4150_, 33);
v_X_5142_ = lean_ctor_get(v_date_4150_, 34);
v_x_5143_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5144_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5154_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5154_ == 0)
{
lean_object* v_unused_5155_; 
v_unused_5155_ = lean_ctor_get(v_date_4150_, 19);
lean_dec(v_unused_5155_);
v___x_5146_ = v_date_4150_;
v_isShared_5147_ = v_isSharedCheck_5154_;
goto v_resetjp_5145_;
}
else
{
lean_inc(v_Z_5144_);
lean_inc(v_x_5143_);
lean_inc(v_X_5142_);
lean_inc(v_O_5141_);
lean_inc(v_v_5140_);
lean_inc(v_zabbrev_5139_);
lean_inc(v_z_5138_);
lean_inc(v_V_5137_);
lean_inc(v_N_5136_);
lean_inc(v_n_5135_);
lean_inc(v_A_5134_);
lean_inc(v_S_5133_);
lean_inc(v_s_5132_);
lean_inc(v_m_5131_);
lean_inc(v_H_5130_);
lean_inc(v_k_5129_);
lean_inc(v_K_5128_);
lean_inc(v_B_5127_);
lean_inc(v_b_5126_);
lean_inc(v_a_5125_);
lean_inc(v_F_5124_);
lean_inc(v_c_5123_);
lean_inc(v_e_5122_);
lean_inc(v_E_5121_);
lean_inc(v_W_5120_);
lean_inc(v_w_5119_);
lean_inc(v_q_5118_);
lean_inc(v_Q_5117_);
lean_inc(v_d_5116_);
lean_inc(v_L_5115_);
lean_inc(v_M_5114_);
lean_inc(v_D_5113_);
lean_inc(v_Y_5112_);
lean_inc(v_u_5111_);
lean_inc(v_y_5110_);
lean_inc(v_G_5109_);
lean_dec(v_date_4150_);
v___x_5146_ = lean_box(0);
v_isShared_5147_ = v_isSharedCheck_5154_;
goto v_resetjp_5145_;
}
v_resetjp_5145_:
{
lean_object* v___x_5149_; 
if (v_isShared_5108_ == 0)
{
lean_ctor_set_tag(v___x_5107_, 1);
lean_ctor_set(v___x_5107_, 0, v_data_4152_);
v___x_5149_ = v___x_5107_;
goto v_reusejp_5148_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_data_4152_);
v___x_5149_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5148_;
}
v_reusejp_5148_:
{
lean_object* v___x_5151_; 
if (v_isShared_5147_ == 0)
{
lean_ctor_set(v___x_5146_, 19, v___x_5149_);
v___x_5151_ = v___x_5146_;
goto v_reusejp_5150_;
}
else
{
lean_object* v_reuseFailAlloc_5152_; 
v_reuseFailAlloc_5152_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5152_, 0, v_G_5109_);
lean_ctor_set(v_reuseFailAlloc_5152_, 1, v_y_5110_);
lean_ctor_set(v_reuseFailAlloc_5152_, 2, v_u_5111_);
lean_ctor_set(v_reuseFailAlloc_5152_, 3, v_Y_5112_);
lean_ctor_set(v_reuseFailAlloc_5152_, 4, v_D_5113_);
lean_ctor_set(v_reuseFailAlloc_5152_, 5, v_M_5114_);
lean_ctor_set(v_reuseFailAlloc_5152_, 6, v_L_5115_);
lean_ctor_set(v_reuseFailAlloc_5152_, 7, v_d_5116_);
lean_ctor_set(v_reuseFailAlloc_5152_, 8, v_Q_5117_);
lean_ctor_set(v_reuseFailAlloc_5152_, 9, v_q_5118_);
lean_ctor_set(v_reuseFailAlloc_5152_, 10, v_w_5119_);
lean_ctor_set(v_reuseFailAlloc_5152_, 11, v_W_5120_);
lean_ctor_set(v_reuseFailAlloc_5152_, 12, v_E_5121_);
lean_ctor_set(v_reuseFailAlloc_5152_, 13, v_e_5122_);
lean_ctor_set(v_reuseFailAlloc_5152_, 14, v_c_5123_);
lean_ctor_set(v_reuseFailAlloc_5152_, 15, v_F_5124_);
lean_ctor_set(v_reuseFailAlloc_5152_, 16, v_a_5125_);
lean_ctor_set(v_reuseFailAlloc_5152_, 17, v_b_5126_);
lean_ctor_set(v_reuseFailAlloc_5152_, 18, v_B_5127_);
lean_ctor_set(v_reuseFailAlloc_5152_, 19, v___x_5149_);
lean_ctor_set(v_reuseFailAlloc_5152_, 20, v_K_5128_);
lean_ctor_set(v_reuseFailAlloc_5152_, 21, v_k_5129_);
lean_ctor_set(v_reuseFailAlloc_5152_, 22, v_H_5130_);
lean_ctor_set(v_reuseFailAlloc_5152_, 23, v_m_5131_);
lean_ctor_set(v_reuseFailAlloc_5152_, 24, v_s_5132_);
lean_ctor_set(v_reuseFailAlloc_5152_, 25, v_S_5133_);
lean_ctor_set(v_reuseFailAlloc_5152_, 26, v_A_5134_);
lean_ctor_set(v_reuseFailAlloc_5152_, 27, v_n_5135_);
lean_ctor_set(v_reuseFailAlloc_5152_, 28, v_N_5136_);
lean_ctor_set(v_reuseFailAlloc_5152_, 29, v_V_5137_);
lean_ctor_set(v_reuseFailAlloc_5152_, 30, v_z_5138_);
lean_ctor_set(v_reuseFailAlloc_5152_, 31, v_zabbrev_5139_);
lean_ctor_set(v_reuseFailAlloc_5152_, 32, v_v_5140_);
lean_ctor_set(v_reuseFailAlloc_5152_, 33, v_O_5141_);
lean_ctor_set(v_reuseFailAlloc_5152_, 34, v_X_5142_);
lean_ctor_set(v_reuseFailAlloc_5152_, 35, v_x_5143_);
lean_ctor_set(v_reuseFailAlloc_5152_, 36, v_Z_5144_);
v___x_5151_ = v_reuseFailAlloc_5152_;
goto v_reusejp_5150_;
}
v_reusejp_5150_:
{
return v___x_5151_;
}
}
}
}
}
case 20:
{
lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5208_; 
v_isSharedCheck_5208_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_5208_ == 0)
{
lean_object* v_unused_5209_; 
v_unused_5209_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_5209_);
v___x_5159_ = v_modifier_4151_;
v_isShared_5160_ = v_isSharedCheck_5208_;
goto v_resetjp_5158_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5208_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v_G_5161_; lean_object* v_y_5162_; lean_object* v_u_5163_; lean_object* v_Y_5164_; lean_object* v_D_5165_; lean_object* v_M_5166_; lean_object* v_L_5167_; lean_object* v_d_5168_; lean_object* v_Q_5169_; lean_object* v_q_5170_; lean_object* v_w_5171_; lean_object* v_W_5172_; lean_object* v_E_5173_; lean_object* v_e_5174_; lean_object* v_c_5175_; lean_object* v_F_5176_; lean_object* v_a_5177_; lean_object* v_b_5178_; lean_object* v_B_5179_; lean_object* v_h_5180_; lean_object* v_k_5181_; lean_object* v_H_5182_; lean_object* v_m_5183_; lean_object* v_s_5184_; lean_object* v_S_5185_; lean_object* v_A_5186_; lean_object* v_n_5187_; lean_object* v_N_5188_; lean_object* v_V_5189_; lean_object* v_z_5190_; lean_object* v_zabbrev_5191_; lean_object* v_v_5192_; lean_object* v_O_5193_; lean_object* v_X_5194_; lean_object* v_x_5195_; lean_object* v_Z_5196_; lean_object* v___x_5198_; uint8_t v_isShared_5199_; uint8_t v_isSharedCheck_5206_; 
v_G_5161_ = lean_ctor_get(v_date_4150_, 0);
v_y_5162_ = lean_ctor_get(v_date_4150_, 1);
v_u_5163_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5164_ = lean_ctor_get(v_date_4150_, 3);
v_D_5165_ = lean_ctor_get(v_date_4150_, 4);
v_M_5166_ = lean_ctor_get(v_date_4150_, 5);
v_L_5167_ = lean_ctor_get(v_date_4150_, 6);
v_d_5168_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5169_ = lean_ctor_get(v_date_4150_, 8);
v_q_5170_ = lean_ctor_get(v_date_4150_, 9);
v_w_5171_ = lean_ctor_get(v_date_4150_, 10);
v_W_5172_ = lean_ctor_get(v_date_4150_, 11);
v_E_5173_ = lean_ctor_get(v_date_4150_, 12);
v_e_5174_ = lean_ctor_get(v_date_4150_, 13);
v_c_5175_ = lean_ctor_get(v_date_4150_, 14);
v_F_5176_ = lean_ctor_get(v_date_4150_, 15);
v_a_5177_ = lean_ctor_get(v_date_4150_, 16);
v_b_5178_ = lean_ctor_get(v_date_4150_, 17);
v_B_5179_ = lean_ctor_get(v_date_4150_, 18);
v_h_5180_ = lean_ctor_get(v_date_4150_, 19);
v_k_5181_ = lean_ctor_get(v_date_4150_, 21);
v_H_5182_ = lean_ctor_get(v_date_4150_, 22);
v_m_5183_ = lean_ctor_get(v_date_4150_, 23);
v_s_5184_ = lean_ctor_get(v_date_4150_, 24);
v_S_5185_ = lean_ctor_get(v_date_4150_, 25);
v_A_5186_ = lean_ctor_get(v_date_4150_, 26);
v_n_5187_ = lean_ctor_get(v_date_4150_, 27);
v_N_5188_ = lean_ctor_get(v_date_4150_, 28);
v_V_5189_ = lean_ctor_get(v_date_4150_, 29);
v_z_5190_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_5191_ = lean_ctor_get(v_date_4150_, 31);
v_v_5192_ = lean_ctor_get(v_date_4150_, 32);
v_O_5193_ = lean_ctor_get(v_date_4150_, 33);
v_X_5194_ = lean_ctor_get(v_date_4150_, 34);
v_x_5195_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5196_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5206_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5206_ == 0)
{
lean_object* v_unused_5207_; 
v_unused_5207_ = lean_ctor_get(v_date_4150_, 20);
lean_dec(v_unused_5207_);
v___x_5198_ = v_date_4150_;
v_isShared_5199_ = v_isSharedCheck_5206_;
goto v_resetjp_5197_;
}
else
{
lean_inc(v_Z_5196_);
lean_inc(v_x_5195_);
lean_inc(v_X_5194_);
lean_inc(v_O_5193_);
lean_inc(v_v_5192_);
lean_inc(v_zabbrev_5191_);
lean_inc(v_z_5190_);
lean_inc(v_V_5189_);
lean_inc(v_N_5188_);
lean_inc(v_n_5187_);
lean_inc(v_A_5186_);
lean_inc(v_S_5185_);
lean_inc(v_s_5184_);
lean_inc(v_m_5183_);
lean_inc(v_H_5182_);
lean_inc(v_k_5181_);
lean_inc(v_h_5180_);
lean_inc(v_B_5179_);
lean_inc(v_b_5178_);
lean_inc(v_a_5177_);
lean_inc(v_F_5176_);
lean_inc(v_c_5175_);
lean_inc(v_e_5174_);
lean_inc(v_E_5173_);
lean_inc(v_W_5172_);
lean_inc(v_w_5171_);
lean_inc(v_q_5170_);
lean_inc(v_Q_5169_);
lean_inc(v_d_5168_);
lean_inc(v_L_5167_);
lean_inc(v_M_5166_);
lean_inc(v_D_5165_);
lean_inc(v_Y_5164_);
lean_inc(v_u_5163_);
lean_inc(v_y_5162_);
lean_inc(v_G_5161_);
lean_dec(v_date_4150_);
v___x_5198_ = lean_box(0);
v_isShared_5199_ = v_isSharedCheck_5206_;
goto v_resetjp_5197_;
}
v_resetjp_5197_:
{
lean_object* v___x_5201_; 
if (v_isShared_5160_ == 0)
{
lean_ctor_set_tag(v___x_5159_, 1);
lean_ctor_set(v___x_5159_, 0, v_data_4152_);
v___x_5201_ = v___x_5159_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5205_; 
v_reuseFailAlloc_5205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5205_, 0, v_data_4152_);
v___x_5201_ = v_reuseFailAlloc_5205_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
lean_object* v___x_5203_; 
if (v_isShared_5199_ == 0)
{
lean_ctor_set(v___x_5198_, 20, v___x_5201_);
v___x_5203_ = v___x_5198_;
goto v_reusejp_5202_;
}
else
{
lean_object* v_reuseFailAlloc_5204_; 
v_reuseFailAlloc_5204_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_G_5161_);
lean_ctor_set(v_reuseFailAlloc_5204_, 1, v_y_5162_);
lean_ctor_set(v_reuseFailAlloc_5204_, 2, v_u_5163_);
lean_ctor_set(v_reuseFailAlloc_5204_, 3, v_Y_5164_);
lean_ctor_set(v_reuseFailAlloc_5204_, 4, v_D_5165_);
lean_ctor_set(v_reuseFailAlloc_5204_, 5, v_M_5166_);
lean_ctor_set(v_reuseFailAlloc_5204_, 6, v_L_5167_);
lean_ctor_set(v_reuseFailAlloc_5204_, 7, v_d_5168_);
lean_ctor_set(v_reuseFailAlloc_5204_, 8, v_Q_5169_);
lean_ctor_set(v_reuseFailAlloc_5204_, 9, v_q_5170_);
lean_ctor_set(v_reuseFailAlloc_5204_, 10, v_w_5171_);
lean_ctor_set(v_reuseFailAlloc_5204_, 11, v_W_5172_);
lean_ctor_set(v_reuseFailAlloc_5204_, 12, v_E_5173_);
lean_ctor_set(v_reuseFailAlloc_5204_, 13, v_e_5174_);
lean_ctor_set(v_reuseFailAlloc_5204_, 14, v_c_5175_);
lean_ctor_set(v_reuseFailAlloc_5204_, 15, v_F_5176_);
lean_ctor_set(v_reuseFailAlloc_5204_, 16, v_a_5177_);
lean_ctor_set(v_reuseFailAlloc_5204_, 17, v_b_5178_);
lean_ctor_set(v_reuseFailAlloc_5204_, 18, v_B_5179_);
lean_ctor_set(v_reuseFailAlloc_5204_, 19, v_h_5180_);
lean_ctor_set(v_reuseFailAlloc_5204_, 20, v___x_5201_);
lean_ctor_set(v_reuseFailAlloc_5204_, 21, v_k_5181_);
lean_ctor_set(v_reuseFailAlloc_5204_, 22, v_H_5182_);
lean_ctor_set(v_reuseFailAlloc_5204_, 23, v_m_5183_);
lean_ctor_set(v_reuseFailAlloc_5204_, 24, v_s_5184_);
lean_ctor_set(v_reuseFailAlloc_5204_, 25, v_S_5185_);
lean_ctor_set(v_reuseFailAlloc_5204_, 26, v_A_5186_);
lean_ctor_set(v_reuseFailAlloc_5204_, 27, v_n_5187_);
lean_ctor_set(v_reuseFailAlloc_5204_, 28, v_N_5188_);
lean_ctor_set(v_reuseFailAlloc_5204_, 29, v_V_5189_);
lean_ctor_set(v_reuseFailAlloc_5204_, 30, v_z_5190_);
lean_ctor_set(v_reuseFailAlloc_5204_, 31, v_zabbrev_5191_);
lean_ctor_set(v_reuseFailAlloc_5204_, 32, v_v_5192_);
lean_ctor_set(v_reuseFailAlloc_5204_, 33, v_O_5193_);
lean_ctor_set(v_reuseFailAlloc_5204_, 34, v_X_5194_);
lean_ctor_set(v_reuseFailAlloc_5204_, 35, v_x_5195_);
lean_ctor_set(v_reuseFailAlloc_5204_, 36, v_Z_5196_);
v___x_5203_ = v_reuseFailAlloc_5204_;
goto v_reusejp_5202_;
}
v_reusejp_5202_:
{
return v___x_5203_;
}
}
}
}
}
case 21:
{
lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5260_; 
v_isSharedCheck_5260_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_5260_ == 0)
{
lean_object* v_unused_5261_; 
v_unused_5261_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_5261_);
v___x_5211_ = v_modifier_4151_;
v_isShared_5212_ = v_isSharedCheck_5260_;
goto v_resetjp_5210_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5260_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
lean_object* v_G_5213_; lean_object* v_y_5214_; lean_object* v_u_5215_; lean_object* v_Y_5216_; lean_object* v_D_5217_; lean_object* v_M_5218_; lean_object* v_L_5219_; lean_object* v_d_5220_; lean_object* v_Q_5221_; lean_object* v_q_5222_; lean_object* v_w_5223_; lean_object* v_W_5224_; lean_object* v_E_5225_; lean_object* v_e_5226_; lean_object* v_c_5227_; lean_object* v_F_5228_; lean_object* v_a_5229_; lean_object* v_b_5230_; lean_object* v_B_5231_; lean_object* v_h_5232_; lean_object* v_K_5233_; lean_object* v_H_5234_; lean_object* v_m_5235_; lean_object* v_s_5236_; lean_object* v_S_5237_; lean_object* v_A_5238_; lean_object* v_n_5239_; lean_object* v_N_5240_; lean_object* v_V_5241_; lean_object* v_z_5242_; lean_object* v_zabbrev_5243_; lean_object* v_v_5244_; lean_object* v_O_5245_; lean_object* v_X_5246_; lean_object* v_x_5247_; lean_object* v_Z_5248_; lean_object* v___x_5250_; uint8_t v_isShared_5251_; uint8_t v_isSharedCheck_5258_; 
v_G_5213_ = lean_ctor_get(v_date_4150_, 0);
v_y_5214_ = lean_ctor_get(v_date_4150_, 1);
v_u_5215_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5216_ = lean_ctor_get(v_date_4150_, 3);
v_D_5217_ = lean_ctor_get(v_date_4150_, 4);
v_M_5218_ = lean_ctor_get(v_date_4150_, 5);
v_L_5219_ = lean_ctor_get(v_date_4150_, 6);
v_d_5220_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5221_ = lean_ctor_get(v_date_4150_, 8);
v_q_5222_ = lean_ctor_get(v_date_4150_, 9);
v_w_5223_ = lean_ctor_get(v_date_4150_, 10);
v_W_5224_ = lean_ctor_get(v_date_4150_, 11);
v_E_5225_ = lean_ctor_get(v_date_4150_, 12);
v_e_5226_ = lean_ctor_get(v_date_4150_, 13);
v_c_5227_ = lean_ctor_get(v_date_4150_, 14);
v_F_5228_ = lean_ctor_get(v_date_4150_, 15);
v_a_5229_ = lean_ctor_get(v_date_4150_, 16);
v_b_5230_ = lean_ctor_get(v_date_4150_, 17);
v_B_5231_ = lean_ctor_get(v_date_4150_, 18);
v_h_5232_ = lean_ctor_get(v_date_4150_, 19);
v_K_5233_ = lean_ctor_get(v_date_4150_, 20);
v_H_5234_ = lean_ctor_get(v_date_4150_, 22);
v_m_5235_ = lean_ctor_get(v_date_4150_, 23);
v_s_5236_ = lean_ctor_get(v_date_4150_, 24);
v_S_5237_ = lean_ctor_get(v_date_4150_, 25);
v_A_5238_ = lean_ctor_get(v_date_4150_, 26);
v_n_5239_ = lean_ctor_get(v_date_4150_, 27);
v_N_5240_ = lean_ctor_get(v_date_4150_, 28);
v_V_5241_ = lean_ctor_get(v_date_4150_, 29);
v_z_5242_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_5243_ = lean_ctor_get(v_date_4150_, 31);
v_v_5244_ = lean_ctor_get(v_date_4150_, 32);
v_O_5245_ = lean_ctor_get(v_date_4150_, 33);
v_X_5246_ = lean_ctor_get(v_date_4150_, 34);
v_x_5247_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5248_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5258_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5258_ == 0)
{
lean_object* v_unused_5259_; 
v_unused_5259_ = lean_ctor_get(v_date_4150_, 21);
lean_dec(v_unused_5259_);
v___x_5250_ = v_date_4150_;
v_isShared_5251_ = v_isSharedCheck_5258_;
goto v_resetjp_5249_;
}
else
{
lean_inc(v_Z_5248_);
lean_inc(v_x_5247_);
lean_inc(v_X_5246_);
lean_inc(v_O_5245_);
lean_inc(v_v_5244_);
lean_inc(v_zabbrev_5243_);
lean_inc(v_z_5242_);
lean_inc(v_V_5241_);
lean_inc(v_N_5240_);
lean_inc(v_n_5239_);
lean_inc(v_A_5238_);
lean_inc(v_S_5237_);
lean_inc(v_s_5236_);
lean_inc(v_m_5235_);
lean_inc(v_H_5234_);
lean_inc(v_K_5233_);
lean_inc(v_h_5232_);
lean_inc(v_B_5231_);
lean_inc(v_b_5230_);
lean_inc(v_a_5229_);
lean_inc(v_F_5228_);
lean_inc(v_c_5227_);
lean_inc(v_e_5226_);
lean_inc(v_E_5225_);
lean_inc(v_W_5224_);
lean_inc(v_w_5223_);
lean_inc(v_q_5222_);
lean_inc(v_Q_5221_);
lean_inc(v_d_5220_);
lean_inc(v_L_5219_);
lean_inc(v_M_5218_);
lean_inc(v_D_5217_);
lean_inc(v_Y_5216_);
lean_inc(v_u_5215_);
lean_inc(v_y_5214_);
lean_inc(v_G_5213_);
lean_dec(v_date_4150_);
v___x_5250_ = lean_box(0);
v_isShared_5251_ = v_isSharedCheck_5258_;
goto v_resetjp_5249_;
}
v_resetjp_5249_:
{
lean_object* v___x_5253_; 
if (v_isShared_5212_ == 0)
{
lean_ctor_set_tag(v___x_5211_, 1);
lean_ctor_set(v___x_5211_, 0, v_data_4152_);
v___x_5253_ = v___x_5211_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5257_; 
v_reuseFailAlloc_5257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5257_, 0, v_data_4152_);
v___x_5253_ = v_reuseFailAlloc_5257_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
lean_object* v___x_5255_; 
if (v_isShared_5251_ == 0)
{
lean_ctor_set(v___x_5250_, 21, v___x_5253_);
v___x_5255_ = v___x_5250_;
goto v_reusejp_5254_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v_G_5213_);
lean_ctor_set(v_reuseFailAlloc_5256_, 1, v_y_5214_);
lean_ctor_set(v_reuseFailAlloc_5256_, 2, v_u_5215_);
lean_ctor_set(v_reuseFailAlloc_5256_, 3, v_Y_5216_);
lean_ctor_set(v_reuseFailAlloc_5256_, 4, v_D_5217_);
lean_ctor_set(v_reuseFailAlloc_5256_, 5, v_M_5218_);
lean_ctor_set(v_reuseFailAlloc_5256_, 6, v_L_5219_);
lean_ctor_set(v_reuseFailAlloc_5256_, 7, v_d_5220_);
lean_ctor_set(v_reuseFailAlloc_5256_, 8, v_Q_5221_);
lean_ctor_set(v_reuseFailAlloc_5256_, 9, v_q_5222_);
lean_ctor_set(v_reuseFailAlloc_5256_, 10, v_w_5223_);
lean_ctor_set(v_reuseFailAlloc_5256_, 11, v_W_5224_);
lean_ctor_set(v_reuseFailAlloc_5256_, 12, v_E_5225_);
lean_ctor_set(v_reuseFailAlloc_5256_, 13, v_e_5226_);
lean_ctor_set(v_reuseFailAlloc_5256_, 14, v_c_5227_);
lean_ctor_set(v_reuseFailAlloc_5256_, 15, v_F_5228_);
lean_ctor_set(v_reuseFailAlloc_5256_, 16, v_a_5229_);
lean_ctor_set(v_reuseFailAlloc_5256_, 17, v_b_5230_);
lean_ctor_set(v_reuseFailAlloc_5256_, 18, v_B_5231_);
lean_ctor_set(v_reuseFailAlloc_5256_, 19, v_h_5232_);
lean_ctor_set(v_reuseFailAlloc_5256_, 20, v_K_5233_);
lean_ctor_set(v_reuseFailAlloc_5256_, 21, v___x_5253_);
lean_ctor_set(v_reuseFailAlloc_5256_, 22, v_H_5234_);
lean_ctor_set(v_reuseFailAlloc_5256_, 23, v_m_5235_);
lean_ctor_set(v_reuseFailAlloc_5256_, 24, v_s_5236_);
lean_ctor_set(v_reuseFailAlloc_5256_, 25, v_S_5237_);
lean_ctor_set(v_reuseFailAlloc_5256_, 26, v_A_5238_);
lean_ctor_set(v_reuseFailAlloc_5256_, 27, v_n_5239_);
lean_ctor_set(v_reuseFailAlloc_5256_, 28, v_N_5240_);
lean_ctor_set(v_reuseFailAlloc_5256_, 29, v_V_5241_);
lean_ctor_set(v_reuseFailAlloc_5256_, 30, v_z_5242_);
lean_ctor_set(v_reuseFailAlloc_5256_, 31, v_zabbrev_5243_);
lean_ctor_set(v_reuseFailAlloc_5256_, 32, v_v_5244_);
lean_ctor_set(v_reuseFailAlloc_5256_, 33, v_O_5245_);
lean_ctor_set(v_reuseFailAlloc_5256_, 34, v_X_5246_);
lean_ctor_set(v_reuseFailAlloc_5256_, 35, v_x_5247_);
lean_ctor_set(v_reuseFailAlloc_5256_, 36, v_Z_5248_);
v___x_5255_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5254_;
}
v_reusejp_5254_:
{
return v___x_5255_;
}
}
}
}
}
case 22:
{
lean_object* v___x_5263_; uint8_t v_isShared_5264_; uint8_t v_isSharedCheck_5312_; 
v_isSharedCheck_5312_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_5312_ == 0)
{
lean_object* v_unused_5313_; 
v_unused_5313_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_5313_);
v___x_5263_ = v_modifier_4151_;
v_isShared_5264_ = v_isSharedCheck_5312_;
goto v_resetjp_5262_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_5263_ = lean_box(0);
v_isShared_5264_ = v_isSharedCheck_5312_;
goto v_resetjp_5262_;
}
v_resetjp_5262_:
{
lean_object* v_G_5265_; lean_object* v_y_5266_; lean_object* v_u_5267_; lean_object* v_Y_5268_; lean_object* v_D_5269_; lean_object* v_M_5270_; lean_object* v_L_5271_; lean_object* v_d_5272_; lean_object* v_Q_5273_; lean_object* v_q_5274_; lean_object* v_w_5275_; lean_object* v_W_5276_; lean_object* v_E_5277_; lean_object* v_e_5278_; lean_object* v_c_5279_; lean_object* v_F_5280_; lean_object* v_a_5281_; lean_object* v_b_5282_; lean_object* v_B_5283_; lean_object* v_h_5284_; lean_object* v_K_5285_; lean_object* v_k_5286_; lean_object* v_m_5287_; lean_object* v_s_5288_; lean_object* v_S_5289_; lean_object* v_A_5290_; lean_object* v_n_5291_; lean_object* v_N_5292_; lean_object* v_V_5293_; lean_object* v_z_5294_; lean_object* v_zabbrev_5295_; lean_object* v_v_5296_; lean_object* v_O_5297_; lean_object* v_X_5298_; lean_object* v_x_5299_; lean_object* v_Z_5300_; lean_object* v___x_5302_; uint8_t v_isShared_5303_; uint8_t v_isSharedCheck_5310_; 
v_G_5265_ = lean_ctor_get(v_date_4150_, 0);
v_y_5266_ = lean_ctor_get(v_date_4150_, 1);
v_u_5267_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5268_ = lean_ctor_get(v_date_4150_, 3);
v_D_5269_ = lean_ctor_get(v_date_4150_, 4);
v_M_5270_ = lean_ctor_get(v_date_4150_, 5);
v_L_5271_ = lean_ctor_get(v_date_4150_, 6);
v_d_5272_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5273_ = lean_ctor_get(v_date_4150_, 8);
v_q_5274_ = lean_ctor_get(v_date_4150_, 9);
v_w_5275_ = lean_ctor_get(v_date_4150_, 10);
v_W_5276_ = lean_ctor_get(v_date_4150_, 11);
v_E_5277_ = lean_ctor_get(v_date_4150_, 12);
v_e_5278_ = lean_ctor_get(v_date_4150_, 13);
v_c_5279_ = lean_ctor_get(v_date_4150_, 14);
v_F_5280_ = lean_ctor_get(v_date_4150_, 15);
v_a_5281_ = lean_ctor_get(v_date_4150_, 16);
v_b_5282_ = lean_ctor_get(v_date_4150_, 17);
v_B_5283_ = lean_ctor_get(v_date_4150_, 18);
v_h_5284_ = lean_ctor_get(v_date_4150_, 19);
v_K_5285_ = lean_ctor_get(v_date_4150_, 20);
v_k_5286_ = lean_ctor_get(v_date_4150_, 21);
v_m_5287_ = lean_ctor_get(v_date_4150_, 23);
v_s_5288_ = lean_ctor_get(v_date_4150_, 24);
v_S_5289_ = lean_ctor_get(v_date_4150_, 25);
v_A_5290_ = lean_ctor_get(v_date_4150_, 26);
v_n_5291_ = lean_ctor_get(v_date_4150_, 27);
v_N_5292_ = lean_ctor_get(v_date_4150_, 28);
v_V_5293_ = lean_ctor_get(v_date_4150_, 29);
v_z_5294_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_5295_ = lean_ctor_get(v_date_4150_, 31);
v_v_5296_ = lean_ctor_get(v_date_4150_, 32);
v_O_5297_ = lean_ctor_get(v_date_4150_, 33);
v_X_5298_ = lean_ctor_get(v_date_4150_, 34);
v_x_5299_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5300_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5310_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5310_ == 0)
{
lean_object* v_unused_5311_; 
v_unused_5311_ = lean_ctor_get(v_date_4150_, 22);
lean_dec(v_unused_5311_);
v___x_5302_ = v_date_4150_;
v_isShared_5303_ = v_isSharedCheck_5310_;
goto v_resetjp_5301_;
}
else
{
lean_inc(v_Z_5300_);
lean_inc(v_x_5299_);
lean_inc(v_X_5298_);
lean_inc(v_O_5297_);
lean_inc(v_v_5296_);
lean_inc(v_zabbrev_5295_);
lean_inc(v_z_5294_);
lean_inc(v_V_5293_);
lean_inc(v_N_5292_);
lean_inc(v_n_5291_);
lean_inc(v_A_5290_);
lean_inc(v_S_5289_);
lean_inc(v_s_5288_);
lean_inc(v_m_5287_);
lean_inc(v_k_5286_);
lean_inc(v_K_5285_);
lean_inc(v_h_5284_);
lean_inc(v_B_5283_);
lean_inc(v_b_5282_);
lean_inc(v_a_5281_);
lean_inc(v_F_5280_);
lean_inc(v_c_5279_);
lean_inc(v_e_5278_);
lean_inc(v_E_5277_);
lean_inc(v_W_5276_);
lean_inc(v_w_5275_);
lean_inc(v_q_5274_);
lean_inc(v_Q_5273_);
lean_inc(v_d_5272_);
lean_inc(v_L_5271_);
lean_inc(v_M_5270_);
lean_inc(v_D_5269_);
lean_inc(v_Y_5268_);
lean_inc(v_u_5267_);
lean_inc(v_y_5266_);
lean_inc(v_G_5265_);
lean_dec(v_date_4150_);
v___x_5302_ = lean_box(0);
v_isShared_5303_ = v_isSharedCheck_5310_;
goto v_resetjp_5301_;
}
v_resetjp_5301_:
{
lean_object* v___x_5305_; 
if (v_isShared_5264_ == 0)
{
lean_ctor_set_tag(v___x_5263_, 1);
lean_ctor_set(v___x_5263_, 0, v_data_4152_);
v___x_5305_ = v___x_5263_;
goto v_reusejp_5304_;
}
else
{
lean_object* v_reuseFailAlloc_5309_; 
v_reuseFailAlloc_5309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5309_, 0, v_data_4152_);
v___x_5305_ = v_reuseFailAlloc_5309_;
goto v_reusejp_5304_;
}
v_reusejp_5304_:
{
lean_object* v___x_5307_; 
if (v_isShared_5303_ == 0)
{
lean_ctor_set(v___x_5302_, 22, v___x_5305_);
v___x_5307_ = v___x_5302_;
goto v_reusejp_5306_;
}
else
{
lean_object* v_reuseFailAlloc_5308_; 
v_reuseFailAlloc_5308_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5308_, 0, v_G_5265_);
lean_ctor_set(v_reuseFailAlloc_5308_, 1, v_y_5266_);
lean_ctor_set(v_reuseFailAlloc_5308_, 2, v_u_5267_);
lean_ctor_set(v_reuseFailAlloc_5308_, 3, v_Y_5268_);
lean_ctor_set(v_reuseFailAlloc_5308_, 4, v_D_5269_);
lean_ctor_set(v_reuseFailAlloc_5308_, 5, v_M_5270_);
lean_ctor_set(v_reuseFailAlloc_5308_, 6, v_L_5271_);
lean_ctor_set(v_reuseFailAlloc_5308_, 7, v_d_5272_);
lean_ctor_set(v_reuseFailAlloc_5308_, 8, v_Q_5273_);
lean_ctor_set(v_reuseFailAlloc_5308_, 9, v_q_5274_);
lean_ctor_set(v_reuseFailAlloc_5308_, 10, v_w_5275_);
lean_ctor_set(v_reuseFailAlloc_5308_, 11, v_W_5276_);
lean_ctor_set(v_reuseFailAlloc_5308_, 12, v_E_5277_);
lean_ctor_set(v_reuseFailAlloc_5308_, 13, v_e_5278_);
lean_ctor_set(v_reuseFailAlloc_5308_, 14, v_c_5279_);
lean_ctor_set(v_reuseFailAlloc_5308_, 15, v_F_5280_);
lean_ctor_set(v_reuseFailAlloc_5308_, 16, v_a_5281_);
lean_ctor_set(v_reuseFailAlloc_5308_, 17, v_b_5282_);
lean_ctor_set(v_reuseFailAlloc_5308_, 18, v_B_5283_);
lean_ctor_set(v_reuseFailAlloc_5308_, 19, v_h_5284_);
lean_ctor_set(v_reuseFailAlloc_5308_, 20, v_K_5285_);
lean_ctor_set(v_reuseFailAlloc_5308_, 21, v_k_5286_);
lean_ctor_set(v_reuseFailAlloc_5308_, 22, v___x_5305_);
lean_ctor_set(v_reuseFailAlloc_5308_, 23, v_m_5287_);
lean_ctor_set(v_reuseFailAlloc_5308_, 24, v_s_5288_);
lean_ctor_set(v_reuseFailAlloc_5308_, 25, v_S_5289_);
lean_ctor_set(v_reuseFailAlloc_5308_, 26, v_A_5290_);
lean_ctor_set(v_reuseFailAlloc_5308_, 27, v_n_5291_);
lean_ctor_set(v_reuseFailAlloc_5308_, 28, v_N_5292_);
lean_ctor_set(v_reuseFailAlloc_5308_, 29, v_V_5293_);
lean_ctor_set(v_reuseFailAlloc_5308_, 30, v_z_5294_);
lean_ctor_set(v_reuseFailAlloc_5308_, 31, v_zabbrev_5295_);
lean_ctor_set(v_reuseFailAlloc_5308_, 32, v_v_5296_);
lean_ctor_set(v_reuseFailAlloc_5308_, 33, v_O_5297_);
lean_ctor_set(v_reuseFailAlloc_5308_, 34, v_X_5298_);
lean_ctor_set(v_reuseFailAlloc_5308_, 35, v_x_5299_);
lean_ctor_set(v_reuseFailAlloc_5308_, 36, v_Z_5300_);
v___x_5307_ = v_reuseFailAlloc_5308_;
goto v_reusejp_5306_;
}
v_reusejp_5306_:
{
return v___x_5307_;
}
}
}
}
}
case 23:
{
lean_object* v___x_5315_; uint8_t v_isShared_5316_; uint8_t v_isSharedCheck_5364_; 
v_isSharedCheck_5364_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_5364_ == 0)
{
lean_object* v_unused_5365_; 
v_unused_5365_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_5365_);
v___x_5315_ = v_modifier_4151_;
v_isShared_5316_ = v_isSharedCheck_5364_;
goto v_resetjp_5314_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_5315_ = lean_box(0);
v_isShared_5316_ = v_isSharedCheck_5364_;
goto v_resetjp_5314_;
}
v_resetjp_5314_:
{
lean_object* v_G_5317_; lean_object* v_y_5318_; lean_object* v_u_5319_; lean_object* v_Y_5320_; lean_object* v_D_5321_; lean_object* v_M_5322_; lean_object* v_L_5323_; lean_object* v_d_5324_; lean_object* v_Q_5325_; lean_object* v_q_5326_; lean_object* v_w_5327_; lean_object* v_W_5328_; lean_object* v_E_5329_; lean_object* v_e_5330_; lean_object* v_c_5331_; lean_object* v_F_5332_; lean_object* v_a_5333_; lean_object* v_b_5334_; lean_object* v_B_5335_; lean_object* v_h_5336_; lean_object* v_K_5337_; lean_object* v_k_5338_; lean_object* v_H_5339_; lean_object* v_s_5340_; lean_object* v_S_5341_; lean_object* v_A_5342_; lean_object* v_n_5343_; lean_object* v_N_5344_; lean_object* v_V_5345_; lean_object* v_z_5346_; lean_object* v_zabbrev_5347_; lean_object* v_v_5348_; lean_object* v_O_5349_; lean_object* v_X_5350_; lean_object* v_x_5351_; lean_object* v_Z_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5362_; 
v_G_5317_ = lean_ctor_get(v_date_4150_, 0);
v_y_5318_ = lean_ctor_get(v_date_4150_, 1);
v_u_5319_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5320_ = lean_ctor_get(v_date_4150_, 3);
v_D_5321_ = lean_ctor_get(v_date_4150_, 4);
v_M_5322_ = lean_ctor_get(v_date_4150_, 5);
v_L_5323_ = lean_ctor_get(v_date_4150_, 6);
v_d_5324_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5325_ = lean_ctor_get(v_date_4150_, 8);
v_q_5326_ = lean_ctor_get(v_date_4150_, 9);
v_w_5327_ = lean_ctor_get(v_date_4150_, 10);
v_W_5328_ = lean_ctor_get(v_date_4150_, 11);
v_E_5329_ = lean_ctor_get(v_date_4150_, 12);
v_e_5330_ = lean_ctor_get(v_date_4150_, 13);
v_c_5331_ = lean_ctor_get(v_date_4150_, 14);
v_F_5332_ = lean_ctor_get(v_date_4150_, 15);
v_a_5333_ = lean_ctor_get(v_date_4150_, 16);
v_b_5334_ = lean_ctor_get(v_date_4150_, 17);
v_B_5335_ = lean_ctor_get(v_date_4150_, 18);
v_h_5336_ = lean_ctor_get(v_date_4150_, 19);
v_K_5337_ = lean_ctor_get(v_date_4150_, 20);
v_k_5338_ = lean_ctor_get(v_date_4150_, 21);
v_H_5339_ = lean_ctor_get(v_date_4150_, 22);
v_s_5340_ = lean_ctor_get(v_date_4150_, 24);
v_S_5341_ = lean_ctor_get(v_date_4150_, 25);
v_A_5342_ = lean_ctor_get(v_date_4150_, 26);
v_n_5343_ = lean_ctor_get(v_date_4150_, 27);
v_N_5344_ = lean_ctor_get(v_date_4150_, 28);
v_V_5345_ = lean_ctor_get(v_date_4150_, 29);
v_z_5346_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_5347_ = lean_ctor_get(v_date_4150_, 31);
v_v_5348_ = lean_ctor_get(v_date_4150_, 32);
v_O_5349_ = lean_ctor_get(v_date_4150_, 33);
v_X_5350_ = lean_ctor_get(v_date_4150_, 34);
v_x_5351_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5352_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5362_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5362_ == 0)
{
lean_object* v_unused_5363_; 
v_unused_5363_ = lean_ctor_get(v_date_4150_, 23);
lean_dec(v_unused_5363_);
v___x_5354_ = v_date_4150_;
v_isShared_5355_ = v_isSharedCheck_5362_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_Z_5352_);
lean_inc(v_x_5351_);
lean_inc(v_X_5350_);
lean_inc(v_O_5349_);
lean_inc(v_v_5348_);
lean_inc(v_zabbrev_5347_);
lean_inc(v_z_5346_);
lean_inc(v_V_5345_);
lean_inc(v_N_5344_);
lean_inc(v_n_5343_);
lean_inc(v_A_5342_);
lean_inc(v_S_5341_);
lean_inc(v_s_5340_);
lean_inc(v_H_5339_);
lean_inc(v_k_5338_);
lean_inc(v_K_5337_);
lean_inc(v_h_5336_);
lean_inc(v_B_5335_);
lean_inc(v_b_5334_);
lean_inc(v_a_5333_);
lean_inc(v_F_5332_);
lean_inc(v_c_5331_);
lean_inc(v_e_5330_);
lean_inc(v_E_5329_);
lean_inc(v_W_5328_);
lean_inc(v_w_5327_);
lean_inc(v_q_5326_);
lean_inc(v_Q_5325_);
lean_inc(v_d_5324_);
lean_inc(v_L_5323_);
lean_inc(v_M_5322_);
lean_inc(v_D_5321_);
lean_inc(v_Y_5320_);
lean_inc(v_u_5319_);
lean_inc(v_y_5318_);
lean_inc(v_G_5317_);
lean_dec(v_date_4150_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5362_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
lean_object* v___x_5357_; 
if (v_isShared_5316_ == 0)
{
lean_ctor_set_tag(v___x_5315_, 1);
lean_ctor_set(v___x_5315_, 0, v_data_4152_);
v___x_5357_ = v___x_5315_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5361_; 
v_reuseFailAlloc_5361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5361_, 0, v_data_4152_);
v___x_5357_ = v_reuseFailAlloc_5361_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
lean_object* v___x_5359_; 
if (v_isShared_5355_ == 0)
{
lean_ctor_set(v___x_5354_, 23, v___x_5357_);
v___x_5359_ = v___x_5354_;
goto v_reusejp_5358_;
}
else
{
lean_object* v_reuseFailAlloc_5360_; 
v_reuseFailAlloc_5360_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5360_, 0, v_G_5317_);
lean_ctor_set(v_reuseFailAlloc_5360_, 1, v_y_5318_);
lean_ctor_set(v_reuseFailAlloc_5360_, 2, v_u_5319_);
lean_ctor_set(v_reuseFailAlloc_5360_, 3, v_Y_5320_);
lean_ctor_set(v_reuseFailAlloc_5360_, 4, v_D_5321_);
lean_ctor_set(v_reuseFailAlloc_5360_, 5, v_M_5322_);
lean_ctor_set(v_reuseFailAlloc_5360_, 6, v_L_5323_);
lean_ctor_set(v_reuseFailAlloc_5360_, 7, v_d_5324_);
lean_ctor_set(v_reuseFailAlloc_5360_, 8, v_Q_5325_);
lean_ctor_set(v_reuseFailAlloc_5360_, 9, v_q_5326_);
lean_ctor_set(v_reuseFailAlloc_5360_, 10, v_w_5327_);
lean_ctor_set(v_reuseFailAlloc_5360_, 11, v_W_5328_);
lean_ctor_set(v_reuseFailAlloc_5360_, 12, v_E_5329_);
lean_ctor_set(v_reuseFailAlloc_5360_, 13, v_e_5330_);
lean_ctor_set(v_reuseFailAlloc_5360_, 14, v_c_5331_);
lean_ctor_set(v_reuseFailAlloc_5360_, 15, v_F_5332_);
lean_ctor_set(v_reuseFailAlloc_5360_, 16, v_a_5333_);
lean_ctor_set(v_reuseFailAlloc_5360_, 17, v_b_5334_);
lean_ctor_set(v_reuseFailAlloc_5360_, 18, v_B_5335_);
lean_ctor_set(v_reuseFailAlloc_5360_, 19, v_h_5336_);
lean_ctor_set(v_reuseFailAlloc_5360_, 20, v_K_5337_);
lean_ctor_set(v_reuseFailAlloc_5360_, 21, v_k_5338_);
lean_ctor_set(v_reuseFailAlloc_5360_, 22, v_H_5339_);
lean_ctor_set(v_reuseFailAlloc_5360_, 23, v___x_5357_);
lean_ctor_set(v_reuseFailAlloc_5360_, 24, v_s_5340_);
lean_ctor_set(v_reuseFailAlloc_5360_, 25, v_S_5341_);
lean_ctor_set(v_reuseFailAlloc_5360_, 26, v_A_5342_);
lean_ctor_set(v_reuseFailAlloc_5360_, 27, v_n_5343_);
lean_ctor_set(v_reuseFailAlloc_5360_, 28, v_N_5344_);
lean_ctor_set(v_reuseFailAlloc_5360_, 29, v_V_5345_);
lean_ctor_set(v_reuseFailAlloc_5360_, 30, v_z_5346_);
lean_ctor_set(v_reuseFailAlloc_5360_, 31, v_zabbrev_5347_);
lean_ctor_set(v_reuseFailAlloc_5360_, 32, v_v_5348_);
lean_ctor_set(v_reuseFailAlloc_5360_, 33, v_O_5349_);
lean_ctor_set(v_reuseFailAlloc_5360_, 34, v_X_5350_);
lean_ctor_set(v_reuseFailAlloc_5360_, 35, v_x_5351_);
lean_ctor_set(v_reuseFailAlloc_5360_, 36, v_Z_5352_);
v___x_5359_ = v_reuseFailAlloc_5360_;
goto v_reusejp_5358_;
}
v_reusejp_5358_:
{
return v___x_5359_;
}
}
}
}
}
case 24:
{
lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5416_; 
v_isSharedCheck_5416_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_5416_ == 0)
{
lean_object* v_unused_5417_; 
v_unused_5417_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_5417_);
v___x_5367_ = v_modifier_4151_;
v_isShared_5368_ = v_isSharedCheck_5416_;
goto v_resetjp_5366_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5416_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
lean_object* v_G_5369_; lean_object* v_y_5370_; lean_object* v_u_5371_; lean_object* v_Y_5372_; lean_object* v_D_5373_; lean_object* v_M_5374_; lean_object* v_L_5375_; lean_object* v_d_5376_; lean_object* v_Q_5377_; lean_object* v_q_5378_; lean_object* v_w_5379_; lean_object* v_W_5380_; lean_object* v_E_5381_; lean_object* v_e_5382_; lean_object* v_c_5383_; lean_object* v_F_5384_; lean_object* v_a_5385_; lean_object* v_b_5386_; lean_object* v_B_5387_; lean_object* v_h_5388_; lean_object* v_K_5389_; lean_object* v_k_5390_; lean_object* v_H_5391_; lean_object* v_m_5392_; lean_object* v_S_5393_; lean_object* v_A_5394_; lean_object* v_n_5395_; lean_object* v_N_5396_; lean_object* v_V_5397_; lean_object* v_z_5398_; lean_object* v_zabbrev_5399_; lean_object* v_v_5400_; lean_object* v_O_5401_; lean_object* v_X_5402_; lean_object* v_x_5403_; lean_object* v_Z_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5414_; 
v_G_5369_ = lean_ctor_get(v_date_4150_, 0);
v_y_5370_ = lean_ctor_get(v_date_4150_, 1);
v_u_5371_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5372_ = lean_ctor_get(v_date_4150_, 3);
v_D_5373_ = lean_ctor_get(v_date_4150_, 4);
v_M_5374_ = lean_ctor_get(v_date_4150_, 5);
v_L_5375_ = lean_ctor_get(v_date_4150_, 6);
v_d_5376_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5377_ = lean_ctor_get(v_date_4150_, 8);
v_q_5378_ = lean_ctor_get(v_date_4150_, 9);
v_w_5379_ = lean_ctor_get(v_date_4150_, 10);
v_W_5380_ = lean_ctor_get(v_date_4150_, 11);
v_E_5381_ = lean_ctor_get(v_date_4150_, 12);
v_e_5382_ = lean_ctor_get(v_date_4150_, 13);
v_c_5383_ = lean_ctor_get(v_date_4150_, 14);
v_F_5384_ = lean_ctor_get(v_date_4150_, 15);
v_a_5385_ = lean_ctor_get(v_date_4150_, 16);
v_b_5386_ = lean_ctor_get(v_date_4150_, 17);
v_B_5387_ = lean_ctor_get(v_date_4150_, 18);
v_h_5388_ = lean_ctor_get(v_date_4150_, 19);
v_K_5389_ = lean_ctor_get(v_date_4150_, 20);
v_k_5390_ = lean_ctor_get(v_date_4150_, 21);
v_H_5391_ = lean_ctor_get(v_date_4150_, 22);
v_m_5392_ = lean_ctor_get(v_date_4150_, 23);
v_S_5393_ = lean_ctor_get(v_date_4150_, 25);
v_A_5394_ = lean_ctor_get(v_date_4150_, 26);
v_n_5395_ = lean_ctor_get(v_date_4150_, 27);
v_N_5396_ = lean_ctor_get(v_date_4150_, 28);
v_V_5397_ = lean_ctor_get(v_date_4150_, 29);
v_z_5398_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_5399_ = lean_ctor_get(v_date_4150_, 31);
v_v_5400_ = lean_ctor_get(v_date_4150_, 32);
v_O_5401_ = lean_ctor_get(v_date_4150_, 33);
v_X_5402_ = lean_ctor_get(v_date_4150_, 34);
v_x_5403_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5404_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5414_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5414_ == 0)
{
lean_object* v_unused_5415_; 
v_unused_5415_ = lean_ctor_get(v_date_4150_, 24);
lean_dec(v_unused_5415_);
v___x_5406_ = v_date_4150_;
v_isShared_5407_ = v_isSharedCheck_5414_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_Z_5404_);
lean_inc(v_x_5403_);
lean_inc(v_X_5402_);
lean_inc(v_O_5401_);
lean_inc(v_v_5400_);
lean_inc(v_zabbrev_5399_);
lean_inc(v_z_5398_);
lean_inc(v_V_5397_);
lean_inc(v_N_5396_);
lean_inc(v_n_5395_);
lean_inc(v_A_5394_);
lean_inc(v_S_5393_);
lean_inc(v_m_5392_);
lean_inc(v_H_5391_);
lean_inc(v_k_5390_);
lean_inc(v_K_5389_);
lean_inc(v_h_5388_);
lean_inc(v_B_5387_);
lean_inc(v_b_5386_);
lean_inc(v_a_5385_);
lean_inc(v_F_5384_);
lean_inc(v_c_5383_);
lean_inc(v_e_5382_);
lean_inc(v_E_5381_);
lean_inc(v_W_5380_);
lean_inc(v_w_5379_);
lean_inc(v_q_5378_);
lean_inc(v_Q_5377_);
lean_inc(v_d_5376_);
lean_inc(v_L_5375_);
lean_inc(v_M_5374_);
lean_inc(v_D_5373_);
lean_inc(v_Y_5372_);
lean_inc(v_u_5371_);
lean_inc(v_y_5370_);
lean_inc(v_G_5369_);
lean_dec(v_date_4150_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5414_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
lean_object* v___x_5409_; 
if (v_isShared_5368_ == 0)
{
lean_ctor_set_tag(v___x_5367_, 1);
lean_ctor_set(v___x_5367_, 0, v_data_4152_);
v___x_5409_ = v___x_5367_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5413_; 
v_reuseFailAlloc_5413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5413_, 0, v_data_4152_);
v___x_5409_ = v_reuseFailAlloc_5413_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
lean_object* v___x_5411_; 
if (v_isShared_5407_ == 0)
{
lean_ctor_set(v___x_5406_, 24, v___x_5409_);
v___x_5411_ = v___x_5406_;
goto v_reusejp_5410_;
}
else
{
lean_object* v_reuseFailAlloc_5412_; 
v_reuseFailAlloc_5412_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5412_, 0, v_G_5369_);
lean_ctor_set(v_reuseFailAlloc_5412_, 1, v_y_5370_);
lean_ctor_set(v_reuseFailAlloc_5412_, 2, v_u_5371_);
lean_ctor_set(v_reuseFailAlloc_5412_, 3, v_Y_5372_);
lean_ctor_set(v_reuseFailAlloc_5412_, 4, v_D_5373_);
lean_ctor_set(v_reuseFailAlloc_5412_, 5, v_M_5374_);
lean_ctor_set(v_reuseFailAlloc_5412_, 6, v_L_5375_);
lean_ctor_set(v_reuseFailAlloc_5412_, 7, v_d_5376_);
lean_ctor_set(v_reuseFailAlloc_5412_, 8, v_Q_5377_);
lean_ctor_set(v_reuseFailAlloc_5412_, 9, v_q_5378_);
lean_ctor_set(v_reuseFailAlloc_5412_, 10, v_w_5379_);
lean_ctor_set(v_reuseFailAlloc_5412_, 11, v_W_5380_);
lean_ctor_set(v_reuseFailAlloc_5412_, 12, v_E_5381_);
lean_ctor_set(v_reuseFailAlloc_5412_, 13, v_e_5382_);
lean_ctor_set(v_reuseFailAlloc_5412_, 14, v_c_5383_);
lean_ctor_set(v_reuseFailAlloc_5412_, 15, v_F_5384_);
lean_ctor_set(v_reuseFailAlloc_5412_, 16, v_a_5385_);
lean_ctor_set(v_reuseFailAlloc_5412_, 17, v_b_5386_);
lean_ctor_set(v_reuseFailAlloc_5412_, 18, v_B_5387_);
lean_ctor_set(v_reuseFailAlloc_5412_, 19, v_h_5388_);
lean_ctor_set(v_reuseFailAlloc_5412_, 20, v_K_5389_);
lean_ctor_set(v_reuseFailAlloc_5412_, 21, v_k_5390_);
lean_ctor_set(v_reuseFailAlloc_5412_, 22, v_H_5391_);
lean_ctor_set(v_reuseFailAlloc_5412_, 23, v_m_5392_);
lean_ctor_set(v_reuseFailAlloc_5412_, 24, v___x_5409_);
lean_ctor_set(v_reuseFailAlloc_5412_, 25, v_S_5393_);
lean_ctor_set(v_reuseFailAlloc_5412_, 26, v_A_5394_);
lean_ctor_set(v_reuseFailAlloc_5412_, 27, v_n_5395_);
lean_ctor_set(v_reuseFailAlloc_5412_, 28, v_N_5396_);
lean_ctor_set(v_reuseFailAlloc_5412_, 29, v_V_5397_);
lean_ctor_set(v_reuseFailAlloc_5412_, 30, v_z_5398_);
lean_ctor_set(v_reuseFailAlloc_5412_, 31, v_zabbrev_5399_);
lean_ctor_set(v_reuseFailAlloc_5412_, 32, v_v_5400_);
lean_ctor_set(v_reuseFailAlloc_5412_, 33, v_O_5401_);
lean_ctor_set(v_reuseFailAlloc_5412_, 34, v_X_5402_);
lean_ctor_set(v_reuseFailAlloc_5412_, 35, v_x_5403_);
lean_ctor_set(v_reuseFailAlloc_5412_, 36, v_Z_5404_);
v___x_5411_ = v_reuseFailAlloc_5412_;
goto v_reusejp_5410_;
}
v_reusejp_5410_:
{
return v___x_5411_;
}
}
}
}
}
case 25:
{
lean_object* v___x_5419_; uint8_t v_isShared_5420_; uint8_t v_isSharedCheck_5468_; 
v_isSharedCheck_5468_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_5468_ == 0)
{
lean_object* v_unused_5469_; 
v_unused_5469_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_5469_);
v___x_5419_ = v_modifier_4151_;
v_isShared_5420_ = v_isSharedCheck_5468_;
goto v_resetjp_5418_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_5419_ = lean_box(0);
v_isShared_5420_ = v_isSharedCheck_5468_;
goto v_resetjp_5418_;
}
v_resetjp_5418_:
{
lean_object* v_G_5421_; lean_object* v_y_5422_; lean_object* v_u_5423_; lean_object* v_Y_5424_; lean_object* v_D_5425_; lean_object* v_M_5426_; lean_object* v_L_5427_; lean_object* v_d_5428_; lean_object* v_Q_5429_; lean_object* v_q_5430_; lean_object* v_w_5431_; lean_object* v_W_5432_; lean_object* v_E_5433_; lean_object* v_e_5434_; lean_object* v_c_5435_; lean_object* v_F_5436_; lean_object* v_a_5437_; lean_object* v_b_5438_; lean_object* v_B_5439_; lean_object* v_h_5440_; lean_object* v_K_5441_; lean_object* v_k_5442_; lean_object* v_H_5443_; lean_object* v_m_5444_; lean_object* v_s_5445_; lean_object* v_A_5446_; lean_object* v_n_5447_; lean_object* v_N_5448_; lean_object* v_V_5449_; lean_object* v_z_5450_; lean_object* v_zabbrev_5451_; lean_object* v_v_5452_; lean_object* v_O_5453_; lean_object* v_X_5454_; lean_object* v_x_5455_; lean_object* v_Z_5456_; lean_object* v___x_5458_; uint8_t v_isShared_5459_; uint8_t v_isSharedCheck_5466_; 
v_G_5421_ = lean_ctor_get(v_date_4150_, 0);
v_y_5422_ = lean_ctor_get(v_date_4150_, 1);
v_u_5423_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5424_ = lean_ctor_get(v_date_4150_, 3);
v_D_5425_ = lean_ctor_get(v_date_4150_, 4);
v_M_5426_ = lean_ctor_get(v_date_4150_, 5);
v_L_5427_ = lean_ctor_get(v_date_4150_, 6);
v_d_5428_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5429_ = lean_ctor_get(v_date_4150_, 8);
v_q_5430_ = lean_ctor_get(v_date_4150_, 9);
v_w_5431_ = lean_ctor_get(v_date_4150_, 10);
v_W_5432_ = lean_ctor_get(v_date_4150_, 11);
v_E_5433_ = lean_ctor_get(v_date_4150_, 12);
v_e_5434_ = lean_ctor_get(v_date_4150_, 13);
v_c_5435_ = lean_ctor_get(v_date_4150_, 14);
v_F_5436_ = lean_ctor_get(v_date_4150_, 15);
v_a_5437_ = lean_ctor_get(v_date_4150_, 16);
v_b_5438_ = lean_ctor_get(v_date_4150_, 17);
v_B_5439_ = lean_ctor_get(v_date_4150_, 18);
v_h_5440_ = lean_ctor_get(v_date_4150_, 19);
v_K_5441_ = lean_ctor_get(v_date_4150_, 20);
v_k_5442_ = lean_ctor_get(v_date_4150_, 21);
v_H_5443_ = lean_ctor_get(v_date_4150_, 22);
v_m_5444_ = lean_ctor_get(v_date_4150_, 23);
v_s_5445_ = lean_ctor_get(v_date_4150_, 24);
v_A_5446_ = lean_ctor_get(v_date_4150_, 26);
v_n_5447_ = lean_ctor_get(v_date_4150_, 27);
v_N_5448_ = lean_ctor_get(v_date_4150_, 28);
v_V_5449_ = lean_ctor_get(v_date_4150_, 29);
v_z_5450_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_5451_ = lean_ctor_get(v_date_4150_, 31);
v_v_5452_ = lean_ctor_get(v_date_4150_, 32);
v_O_5453_ = lean_ctor_get(v_date_4150_, 33);
v_X_5454_ = lean_ctor_get(v_date_4150_, 34);
v_x_5455_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5456_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5466_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5466_ == 0)
{
lean_object* v_unused_5467_; 
v_unused_5467_ = lean_ctor_get(v_date_4150_, 25);
lean_dec(v_unused_5467_);
v___x_5458_ = v_date_4150_;
v_isShared_5459_ = v_isSharedCheck_5466_;
goto v_resetjp_5457_;
}
else
{
lean_inc(v_Z_5456_);
lean_inc(v_x_5455_);
lean_inc(v_X_5454_);
lean_inc(v_O_5453_);
lean_inc(v_v_5452_);
lean_inc(v_zabbrev_5451_);
lean_inc(v_z_5450_);
lean_inc(v_V_5449_);
lean_inc(v_N_5448_);
lean_inc(v_n_5447_);
lean_inc(v_A_5446_);
lean_inc(v_s_5445_);
lean_inc(v_m_5444_);
lean_inc(v_H_5443_);
lean_inc(v_k_5442_);
lean_inc(v_K_5441_);
lean_inc(v_h_5440_);
lean_inc(v_B_5439_);
lean_inc(v_b_5438_);
lean_inc(v_a_5437_);
lean_inc(v_F_5436_);
lean_inc(v_c_5435_);
lean_inc(v_e_5434_);
lean_inc(v_E_5433_);
lean_inc(v_W_5432_);
lean_inc(v_w_5431_);
lean_inc(v_q_5430_);
lean_inc(v_Q_5429_);
lean_inc(v_d_5428_);
lean_inc(v_L_5427_);
lean_inc(v_M_5426_);
lean_inc(v_D_5425_);
lean_inc(v_Y_5424_);
lean_inc(v_u_5423_);
lean_inc(v_y_5422_);
lean_inc(v_G_5421_);
lean_dec(v_date_4150_);
v___x_5458_ = lean_box(0);
v_isShared_5459_ = v_isSharedCheck_5466_;
goto v_resetjp_5457_;
}
v_resetjp_5457_:
{
lean_object* v___x_5461_; 
if (v_isShared_5420_ == 0)
{
lean_ctor_set_tag(v___x_5419_, 1);
lean_ctor_set(v___x_5419_, 0, v_data_4152_);
v___x_5461_ = v___x_5419_;
goto v_reusejp_5460_;
}
else
{
lean_object* v_reuseFailAlloc_5465_; 
v_reuseFailAlloc_5465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5465_, 0, v_data_4152_);
v___x_5461_ = v_reuseFailAlloc_5465_;
goto v_reusejp_5460_;
}
v_reusejp_5460_:
{
lean_object* v___x_5463_; 
if (v_isShared_5459_ == 0)
{
lean_ctor_set(v___x_5458_, 25, v___x_5461_);
v___x_5463_ = v___x_5458_;
goto v_reusejp_5462_;
}
else
{
lean_object* v_reuseFailAlloc_5464_; 
v_reuseFailAlloc_5464_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5464_, 0, v_G_5421_);
lean_ctor_set(v_reuseFailAlloc_5464_, 1, v_y_5422_);
lean_ctor_set(v_reuseFailAlloc_5464_, 2, v_u_5423_);
lean_ctor_set(v_reuseFailAlloc_5464_, 3, v_Y_5424_);
lean_ctor_set(v_reuseFailAlloc_5464_, 4, v_D_5425_);
lean_ctor_set(v_reuseFailAlloc_5464_, 5, v_M_5426_);
lean_ctor_set(v_reuseFailAlloc_5464_, 6, v_L_5427_);
lean_ctor_set(v_reuseFailAlloc_5464_, 7, v_d_5428_);
lean_ctor_set(v_reuseFailAlloc_5464_, 8, v_Q_5429_);
lean_ctor_set(v_reuseFailAlloc_5464_, 9, v_q_5430_);
lean_ctor_set(v_reuseFailAlloc_5464_, 10, v_w_5431_);
lean_ctor_set(v_reuseFailAlloc_5464_, 11, v_W_5432_);
lean_ctor_set(v_reuseFailAlloc_5464_, 12, v_E_5433_);
lean_ctor_set(v_reuseFailAlloc_5464_, 13, v_e_5434_);
lean_ctor_set(v_reuseFailAlloc_5464_, 14, v_c_5435_);
lean_ctor_set(v_reuseFailAlloc_5464_, 15, v_F_5436_);
lean_ctor_set(v_reuseFailAlloc_5464_, 16, v_a_5437_);
lean_ctor_set(v_reuseFailAlloc_5464_, 17, v_b_5438_);
lean_ctor_set(v_reuseFailAlloc_5464_, 18, v_B_5439_);
lean_ctor_set(v_reuseFailAlloc_5464_, 19, v_h_5440_);
lean_ctor_set(v_reuseFailAlloc_5464_, 20, v_K_5441_);
lean_ctor_set(v_reuseFailAlloc_5464_, 21, v_k_5442_);
lean_ctor_set(v_reuseFailAlloc_5464_, 22, v_H_5443_);
lean_ctor_set(v_reuseFailAlloc_5464_, 23, v_m_5444_);
lean_ctor_set(v_reuseFailAlloc_5464_, 24, v_s_5445_);
lean_ctor_set(v_reuseFailAlloc_5464_, 25, v___x_5461_);
lean_ctor_set(v_reuseFailAlloc_5464_, 26, v_A_5446_);
lean_ctor_set(v_reuseFailAlloc_5464_, 27, v_n_5447_);
lean_ctor_set(v_reuseFailAlloc_5464_, 28, v_N_5448_);
lean_ctor_set(v_reuseFailAlloc_5464_, 29, v_V_5449_);
lean_ctor_set(v_reuseFailAlloc_5464_, 30, v_z_5450_);
lean_ctor_set(v_reuseFailAlloc_5464_, 31, v_zabbrev_5451_);
lean_ctor_set(v_reuseFailAlloc_5464_, 32, v_v_5452_);
lean_ctor_set(v_reuseFailAlloc_5464_, 33, v_O_5453_);
lean_ctor_set(v_reuseFailAlloc_5464_, 34, v_X_5454_);
lean_ctor_set(v_reuseFailAlloc_5464_, 35, v_x_5455_);
lean_ctor_set(v_reuseFailAlloc_5464_, 36, v_Z_5456_);
v___x_5463_ = v_reuseFailAlloc_5464_;
goto v_reusejp_5462_;
}
v_reusejp_5462_:
{
return v___x_5463_;
}
}
}
}
}
case 26:
{
lean_object* v___x_5471_; uint8_t v_isShared_5472_; uint8_t v_isSharedCheck_5520_; 
v_isSharedCheck_5520_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_5520_ == 0)
{
lean_object* v_unused_5521_; 
v_unused_5521_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_5521_);
v___x_5471_ = v_modifier_4151_;
v_isShared_5472_ = v_isSharedCheck_5520_;
goto v_resetjp_5470_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_5471_ = lean_box(0);
v_isShared_5472_ = v_isSharedCheck_5520_;
goto v_resetjp_5470_;
}
v_resetjp_5470_:
{
lean_object* v_G_5473_; lean_object* v_y_5474_; lean_object* v_u_5475_; lean_object* v_Y_5476_; lean_object* v_D_5477_; lean_object* v_M_5478_; lean_object* v_L_5479_; lean_object* v_d_5480_; lean_object* v_Q_5481_; lean_object* v_q_5482_; lean_object* v_w_5483_; lean_object* v_W_5484_; lean_object* v_E_5485_; lean_object* v_e_5486_; lean_object* v_c_5487_; lean_object* v_F_5488_; lean_object* v_a_5489_; lean_object* v_b_5490_; lean_object* v_B_5491_; lean_object* v_h_5492_; lean_object* v_K_5493_; lean_object* v_k_5494_; lean_object* v_H_5495_; lean_object* v_m_5496_; lean_object* v_s_5497_; lean_object* v_S_5498_; lean_object* v_n_5499_; lean_object* v_N_5500_; lean_object* v_V_5501_; lean_object* v_z_5502_; lean_object* v_zabbrev_5503_; lean_object* v_v_5504_; lean_object* v_O_5505_; lean_object* v_X_5506_; lean_object* v_x_5507_; lean_object* v_Z_5508_; lean_object* v___x_5510_; uint8_t v_isShared_5511_; uint8_t v_isSharedCheck_5518_; 
v_G_5473_ = lean_ctor_get(v_date_4150_, 0);
v_y_5474_ = lean_ctor_get(v_date_4150_, 1);
v_u_5475_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5476_ = lean_ctor_get(v_date_4150_, 3);
v_D_5477_ = lean_ctor_get(v_date_4150_, 4);
v_M_5478_ = lean_ctor_get(v_date_4150_, 5);
v_L_5479_ = lean_ctor_get(v_date_4150_, 6);
v_d_5480_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5481_ = lean_ctor_get(v_date_4150_, 8);
v_q_5482_ = lean_ctor_get(v_date_4150_, 9);
v_w_5483_ = lean_ctor_get(v_date_4150_, 10);
v_W_5484_ = lean_ctor_get(v_date_4150_, 11);
v_E_5485_ = lean_ctor_get(v_date_4150_, 12);
v_e_5486_ = lean_ctor_get(v_date_4150_, 13);
v_c_5487_ = lean_ctor_get(v_date_4150_, 14);
v_F_5488_ = lean_ctor_get(v_date_4150_, 15);
v_a_5489_ = lean_ctor_get(v_date_4150_, 16);
v_b_5490_ = lean_ctor_get(v_date_4150_, 17);
v_B_5491_ = lean_ctor_get(v_date_4150_, 18);
v_h_5492_ = lean_ctor_get(v_date_4150_, 19);
v_K_5493_ = lean_ctor_get(v_date_4150_, 20);
v_k_5494_ = lean_ctor_get(v_date_4150_, 21);
v_H_5495_ = lean_ctor_get(v_date_4150_, 22);
v_m_5496_ = lean_ctor_get(v_date_4150_, 23);
v_s_5497_ = lean_ctor_get(v_date_4150_, 24);
v_S_5498_ = lean_ctor_get(v_date_4150_, 25);
v_n_5499_ = lean_ctor_get(v_date_4150_, 27);
v_N_5500_ = lean_ctor_get(v_date_4150_, 28);
v_V_5501_ = lean_ctor_get(v_date_4150_, 29);
v_z_5502_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_5503_ = lean_ctor_get(v_date_4150_, 31);
v_v_5504_ = lean_ctor_get(v_date_4150_, 32);
v_O_5505_ = lean_ctor_get(v_date_4150_, 33);
v_X_5506_ = lean_ctor_get(v_date_4150_, 34);
v_x_5507_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5508_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5518_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5518_ == 0)
{
lean_object* v_unused_5519_; 
v_unused_5519_ = lean_ctor_get(v_date_4150_, 26);
lean_dec(v_unused_5519_);
v___x_5510_ = v_date_4150_;
v_isShared_5511_ = v_isSharedCheck_5518_;
goto v_resetjp_5509_;
}
else
{
lean_inc(v_Z_5508_);
lean_inc(v_x_5507_);
lean_inc(v_X_5506_);
lean_inc(v_O_5505_);
lean_inc(v_v_5504_);
lean_inc(v_zabbrev_5503_);
lean_inc(v_z_5502_);
lean_inc(v_V_5501_);
lean_inc(v_N_5500_);
lean_inc(v_n_5499_);
lean_inc(v_S_5498_);
lean_inc(v_s_5497_);
lean_inc(v_m_5496_);
lean_inc(v_H_5495_);
lean_inc(v_k_5494_);
lean_inc(v_K_5493_);
lean_inc(v_h_5492_);
lean_inc(v_B_5491_);
lean_inc(v_b_5490_);
lean_inc(v_a_5489_);
lean_inc(v_F_5488_);
lean_inc(v_c_5487_);
lean_inc(v_e_5486_);
lean_inc(v_E_5485_);
lean_inc(v_W_5484_);
lean_inc(v_w_5483_);
lean_inc(v_q_5482_);
lean_inc(v_Q_5481_);
lean_inc(v_d_5480_);
lean_inc(v_L_5479_);
lean_inc(v_M_5478_);
lean_inc(v_D_5477_);
lean_inc(v_Y_5476_);
lean_inc(v_u_5475_);
lean_inc(v_y_5474_);
lean_inc(v_G_5473_);
lean_dec(v_date_4150_);
v___x_5510_ = lean_box(0);
v_isShared_5511_ = v_isSharedCheck_5518_;
goto v_resetjp_5509_;
}
v_resetjp_5509_:
{
lean_object* v___x_5513_; 
if (v_isShared_5472_ == 0)
{
lean_ctor_set_tag(v___x_5471_, 1);
lean_ctor_set(v___x_5471_, 0, v_data_4152_);
v___x_5513_ = v___x_5471_;
goto v_reusejp_5512_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_data_4152_);
v___x_5513_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5512_;
}
v_reusejp_5512_:
{
lean_object* v___x_5515_; 
if (v_isShared_5511_ == 0)
{
lean_ctor_set(v___x_5510_, 26, v___x_5513_);
v___x_5515_ = v___x_5510_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_G_5473_);
lean_ctor_set(v_reuseFailAlloc_5516_, 1, v_y_5474_);
lean_ctor_set(v_reuseFailAlloc_5516_, 2, v_u_5475_);
lean_ctor_set(v_reuseFailAlloc_5516_, 3, v_Y_5476_);
lean_ctor_set(v_reuseFailAlloc_5516_, 4, v_D_5477_);
lean_ctor_set(v_reuseFailAlloc_5516_, 5, v_M_5478_);
lean_ctor_set(v_reuseFailAlloc_5516_, 6, v_L_5479_);
lean_ctor_set(v_reuseFailAlloc_5516_, 7, v_d_5480_);
lean_ctor_set(v_reuseFailAlloc_5516_, 8, v_Q_5481_);
lean_ctor_set(v_reuseFailAlloc_5516_, 9, v_q_5482_);
lean_ctor_set(v_reuseFailAlloc_5516_, 10, v_w_5483_);
lean_ctor_set(v_reuseFailAlloc_5516_, 11, v_W_5484_);
lean_ctor_set(v_reuseFailAlloc_5516_, 12, v_E_5485_);
lean_ctor_set(v_reuseFailAlloc_5516_, 13, v_e_5486_);
lean_ctor_set(v_reuseFailAlloc_5516_, 14, v_c_5487_);
lean_ctor_set(v_reuseFailAlloc_5516_, 15, v_F_5488_);
lean_ctor_set(v_reuseFailAlloc_5516_, 16, v_a_5489_);
lean_ctor_set(v_reuseFailAlloc_5516_, 17, v_b_5490_);
lean_ctor_set(v_reuseFailAlloc_5516_, 18, v_B_5491_);
lean_ctor_set(v_reuseFailAlloc_5516_, 19, v_h_5492_);
lean_ctor_set(v_reuseFailAlloc_5516_, 20, v_K_5493_);
lean_ctor_set(v_reuseFailAlloc_5516_, 21, v_k_5494_);
lean_ctor_set(v_reuseFailAlloc_5516_, 22, v_H_5495_);
lean_ctor_set(v_reuseFailAlloc_5516_, 23, v_m_5496_);
lean_ctor_set(v_reuseFailAlloc_5516_, 24, v_s_5497_);
lean_ctor_set(v_reuseFailAlloc_5516_, 25, v_S_5498_);
lean_ctor_set(v_reuseFailAlloc_5516_, 26, v___x_5513_);
lean_ctor_set(v_reuseFailAlloc_5516_, 27, v_n_5499_);
lean_ctor_set(v_reuseFailAlloc_5516_, 28, v_N_5500_);
lean_ctor_set(v_reuseFailAlloc_5516_, 29, v_V_5501_);
lean_ctor_set(v_reuseFailAlloc_5516_, 30, v_z_5502_);
lean_ctor_set(v_reuseFailAlloc_5516_, 31, v_zabbrev_5503_);
lean_ctor_set(v_reuseFailAlloc_5516_, 32, v_v_5504_);
lean_ctor_set(v_reuseFailAlloc_5516_, 33, v_O_5505_);
lean_ctor_set(v_reuseFailAlloc_5516_, 34, v_X_5506_);
lean_ctor_set(v_reuseFailAlloc_5516_, 35, v_x_5507_);
lean_ctor_set(v_reuseFailAlloc_5516_, 36, v_Z_5508_);
v___x_5515_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
return v___x_5515_;
}
}
}
}
}
case 27:
{
lean_object* v___x_5523_; uint8_t v_isShared_5524_; uint8_t v_isSharedCheck_5572_; 
v_isSharedCheck_5572_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_5572_ == 0)
{
lean_object* v_unused_5573_; 
v_unused_5573_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_5573_);
v___x_5523_ = v_modifier_4151_;
v_isShared_5524_ = v_isSharedCheck_5572_;
goto v_resetjp_5522_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_5523_ = lean_box(0);
v_isShared_5524_ = v_isSharedCheck_5572_;
goto v_resetjp_5522_;
}
v_resetjp_5522_:
{
lean_object* v_G_5525_; lean_object* v_y_5526_; lean_object* v_u_5527_; lean_object* v_Y_5528_; lean_object* v_D_5529_; lean_object* v_M_5530_; lean_object* v_L_5531_; lean_object* v_d_5532_; lean_object* v_Q_5533_; lean_object* v_q_5534_; lean_object* v_w_5535_; lean_object* v_W_5536_; lean_object* v_E_5537_; lean_object* v_e_5538_; lean_object* v_c_5539_; lean_object* v_F_5540_; lean_object* v_a_5541_; lean_object* v_b_5542_; lean_object* v_B_5543_; lean_object* v_h_5544_; lean_object* v_K_5545_; lean_object* v_k_5546_; lean_object* v_H_5547_; lean_object* v_m_5548_; lean_object* v_s_5549_; lean_object* v_S_5550_; lean_object* v_A_5551_; lean_object* v_N_5552_; lean_object* v_V_5553_; lean_object* v_z_5554_; lean_object* v_zabbrev_5555_; lean_object* v_v_5556_; lean_object* v_O_5557_; lean_object* v_X_5558_; lean_object* v_x_5559_; lean_object* v_Z_5560_; lean_object* v___x_5562_; uint8_t v_isShared_5563_; uint8_t v_isSharedCheck_5570_; 
v_G_5525_ = lean_ctor_get(v_date_4150_, 0);
v_y_5526_ = lean_ctor_get(v_date_4150_, 1);
v_u_5527_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5528_ = lean_ctor_get(v_date_4150_, 3);
v_D_5529_ = lean_ctor_get(v_date_4150_, 4);
v_M_5530_ = lean_ctor_get(v_date_4150_, 5);
v_L_5531_ = lean_ctor_get(v_date_4150_, 6);
v_d_5532_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5533_ = lean_ctor_get(v_date_4150_, 8);
v_q_5534_ = lean_ctor_get(v_date_4150_, 9);
v_w_5535_ = lean_ctor_get(v_date_4150_, 10);
v_W_5536_ = lean_ctor_get(v_date_4150_, 11);
v_E_5537_ = lean_ctor_get(v_date_4150_, 12);
v_e_5538_ = lean_ctor_get(v_date_4150_, 13);
v_c_5539_ = lean_ctor_get(v_date_4150_, 14);
v_F_5540_ = lean_ctor_get(v_date_4150_, 15);
v_a_5541_ = lean_ctor_get(v_date_4150_, 16);
v_b_5542_ = lean_ctor_get(v_date_4150_, 17);
v_B_5543_ = lean_ctor_get(v_date_4150_, 18);
v_h_5544_ = lean_ctor_get(v_date_4150_, 19);
v_K_5545_ = lean_ctor_get(v_date_4150_, 20);
v_k_5546_ = lean_ctor_get(v_date_4150_, 21);
v_H_5547_ = lean_ctor_get(v_date_4150_, 22);
v_m_5548_ = lean_ctor_get(v_date_4150_, 23);
v_s_5549_ = lean_ctor_get(v_date_4150_, 24);
v_S_5550_ = lean_ctor_get(v_date_4150_, 25);
v_A_5551_ = lean_ctor_get(v_date_4150_, 26);
v_N_5552_ = lean_ctor_get(v_date_4150_, 28);
v_V_5553_ = lean_ctor_get(v_date_4150_, 29);
v_z_5554_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_5555_ = lean_ctor_get(v_date_4150_, 31);
v_v_5556_ = lean_ctor_get(v_date_4150_, 32);
v_O_5557_ = lean_ctor_get(v_date_4150_, 33);
v_X_5558_ = lean_ctor_get(v_date_4150_, 34);
v_x_5559_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5560_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5570_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5570_ == 0)
{
lean_object* v_unused_5571_; 
v_unused_5571_ = lean_ctor_get(v_date_4150_, 27);
lean_dec(v_unused_5571_);
v___x_5562_ = v_date_4150_;
v_isShared_5563_ = v_isSharedCheck_5570_;
goto v_resetjp_5561_;
}
else
{
lean_inc(v_Z_5560_);
lean_inc(v_x_5559_);
lean_inc(v_X_5558_);
lean_inc(v_O_5557_);
lean_inc(v_v_5556_);
lean_inc(v_zabbrev_5555_);
lean_inc(v_z_5554_);
lean_inc(v_V_5553_);
lean_inc(v_N_5552_);
lean_inc(v_A_5551_);
lean_inc(v_S_5550_);
lean_inc(v_s_5549_);
lean_inc(v_m_5548_);
lean_inc(v_H_5547_);
lean_inc(v_k_5546_);
lean_inc(v_K_5545_);
lean_inc(v_h_5544_);
lean_inc(v_B_5543_);
lean_inc(v_b_5542_);
lean_inc(v_a_5541_);
lean_inc(v_F_5540_);
lean_inc(v_c_5539_);
lean_inc(v_e_5538_);
lean_inc(v_E_5537_);
lean_inc(v_W_5536_);
lean_inc(v_w_5535_);
lean_inc(v_q_5534_);
lean_inc(v_Q_5533_);
lean_inc(v_d_5532_);
lean_inc(v_L_5531_);
lean_inc(v_M_5530_);
lean_inc(v_D_5529_);
lean_inc(v_Y_5528_);
lean_inc(v_u_5527_);
lean_inc(v_y_5526_);
lean_inc(v_G_5525_);
lean_dec(v_date_4150_);
v___x_5562_ = lean_box(0);
v_isShared_5563_ = v_isSharedCheck_5570_;
goto v_resetjp_5561_;
}
v_resetjp_5561_:
{
lean_object* v___x_5565_; 
if (v_isShared_5524_ == 0)
{
lean_ctor_set_tag(v___x_5523_, 1);
lean_ctor_set(v___x_5523_, 0, v_data_4152_);
v___x_5565_ = v___x_5523_;
goto v_reusejp_5564_;
}
else
{
lean_object* v_reuseFailAlloc_5569_; 
v_reuseFailAlloc_5569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5569_, 0, v_data_4152_);
v___x_5565_ = v_reuseFailAlloc_5569_;
goto v_reusejp_5564_;
}
v_reusejp_5564_:
{
lean_object* v___x_5567_; 
if (v_isShared_5563_ == 0)
{
lean_ctor_set(v___x_5562_, 27, v___x_5565_);
v___x_5567_ = v___x_5562_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_G_5525_);
lean_ctor_set(v_reuseFailAlloc_5568_, 1, v_y_5526_);
lean_ctor_set(v_reuseFailAlloc_5568_, 2, v_u_5527_);
lean_ctor_set(v_reuseFailAlloc_5568_, 3, v_Y_5528_);
lean_ctor_set(v_reuseFailAlloc_5568_, 4, v_D_5529_);
lean_ctor_set(v_reuseFailAlloc_5568_, 5, v_M_5530_);
lean_ctor_set(v_reuseFailAlloc_5568_, 6, v_L_5531_);
lean_ctor_set(v_reuseFailAlloc_5568_, 7, v_d_5532_);
lean_ctor_set(v_reuseFailAlloc_5568_, 8, v_Q_5533_);
lean_ctor_set(v_reuseFailAlloc_5568_, 9, v_q_5534_);
lean_ctor_set(v_reuseFailAlloc_5568_, 10, v_w_5535_);
lean_ctor_set(v_reuseFailAlloc_5568_, 11, v_W_5536_);
lean_ctor_set(v_reuseFailAlloc_5568_, 12, v_E_5537_);
lean_ctor_set(v_reuseFailAlloc_5568_, 13, v_e_5538_);
lean_ctor_set(v_reuseFailAlloc_5568_, 14, v_c_5539_);
lean_ctor_set(v_reuseFailAlloc_5568_, 15, v_F_5540_);
lean_ctor_set(v_reuseFailAlloc_5568_, 16, v_a_5541_);
lean_ctor_set(v_reuseFailAlloc_5568_, 17, v_b_5542_);
lean_ctor_set(v_reuseFailAlloc_5568_, 18, v_B_5543_);
lean_ctor_set(v_reuseFailAlloc_5568_, 19, v_h_5544_);
lean_ctor_set(v_reuseFailAlloc_5568_, 20, v_K_5545_);
lean_ctor_set(v_reuseFailAlloc_5568_, 21, v_k_5546_);
lean_ctor_set(v_reuseFailAlloc_5568_, 22, v_H_5547_);
lean_ctor_set(v_reuseFailAlloc_5568_, 23, v_m_5548_);
lean_ctor_set(v_reuseFailAlloc_5568_, 24, v_s_5549_);
lean_ctor_set(v_reuseFailAlloc_5568_, 25, v_S_5550_);
lean_ctor_set(v_reuseFailAlloc_5568_, 26, v_A_5551_);
lean_ctor_set(v_reuseFailAlloc_5568_, 27, v___x_5565_);
lean_ctor_set(v_reuseFailAlloc_5568_, 28, v_N_5552_);
lean_ctor_set(v_reuseFailAlloc_5568_, 29, v_V_5553_);
lean_ctor_set(v_reuseFailAlloc_5568_, 30, v_z_5554_);
lean_ctor_set(v_reuseFailAlloc_5568_, 31, v_zabbrev_5555_);
lean_ctor_set(v_reuseFailAlloc_5568_, 32, v_v_5556_);
lean_ctor_set(v_reuseFailAlloc_5568_, 33, v_O_5557_);
lean_ctor_set(v_reuseFailAlloc_5568_, 34, v_X_5558_);
lean_ctor_set(v_reuseFailAlloc_5568_, 35, v_x_5559_);
lean_ctor_set(v_reuseFailAlloc_5568_, 36, v_Z_5560_);
v___x_5567_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
return v___x_5567_;
}
}
}
}
}
case 28:
{
lean_object* v___x_5575_; uint8_t v_isShared_5576_; uint8_t v_isSharedCheck_5624_; 
v_isSharedCheck_5624_ = !lean_is_exclusive(v_modifier_4151_);
if (v_isSharedCheck_5624_ == 0)
{
lean_object* v_unused_5625_; 
v_unused_5625_ = lean_ctor_get(v_modifier_4151_, 0);
lean_dec(v_unused_5625_);
v___x_5575_ = v_modifier_4151_;
v_isShared_5576_ = v_isSharedCheck_5624_;
goto v_resetjp_5574_;
}
else
{
lean_dec(v_modifier_4151_);
v___x_5575_ = lean_box(0);
v_isShared_5576_ = v_isSharedCheck_5624_;
goto v_resetjp_5574_;
}
v_resetjp_5574_:
{
lean_object* v_G_5577_; lean_object* v_y_5578_; lean_object* v_u_5579_; lean_object* v_Y_5580_; lean_object* v_D_5581_; lean_object* v_M_5582_; lean_object* v_L_5583_; lean_object* v_d_5584_; lean_object* v_Q_5585_; lean_object* v_q_5586_; lean_object* v_w_5587_; lean_object* v_W_5588_; lean_object* v_E_5589_; lean_object* v_e_5590_; lean_object* v_c_5591_; lean_object* v_F_5592_; lean_object* v_a_5593_; lean_object* v_b_5594_; lean_object* v_B_5595_; lean_object* v_h_5596_; lean_object* v_K_5597_; lean_object* v_k_5598_; lean_object* v_H_5599_; lean_object* v_m_5600_; lean_object* v_s_5601_; lean_object* v_S_5602_; lean_object* v_A_5603_; lean_object* v_n_5604_; lean_object* v_V_5605_; lean_object* v_z_5606_; lean_object* v_zabbrev_5607_; lean_object* v_v_5608_; lean_object* v_O_5609_; lean_object* v_X_5610_; lean_object* v_x_5611_; lean_object* v_Z_5612_; lean_object* v___x_5614_; uint8_t v_isShared_5615_; uint8_t v_isSharedCheck_5622_; 
v_G_5577_ = lean_ctor_get(v_date_4150_, 0);
v_y_5578_ = lean_ctor_get(v_date_4150_, 1);
v_u_5579_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5580_ = lean_ctor_get(v_date_4150_, 3);
v_D_5581_ = lean_ctor_get(v_date_4150_, 4);
v_M_5582_ = lean_ctor_get(v_date_4150_, 5);
v_L_5583_ = lean_ctor_get(v_date_4150_, 6);
v_d_5584_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5585_ = lean_ctor_get(v_date_4150_, 8);
v_q_5586_ = lean_ctor_get(v_date_4150_, 9);
v_w_5587_ = lean_ctor_get(v_date_4150_, 10);
v_W_5588_ = lean_ctor_get(v_date_4150_, 11);
v_E_5589_ = lean_ctor_get(v_date_4150_, 12);
v_e_5590_ = lean_ctor_get(v_date_4150_, 13);
v_c_5591_ = lean_ctor_get(v_date_4150_, 14);
v_F_5592_ = lean_ctor_get(v_date_4150_, 15);
v_a_5593_ = lean_ctor_get(v_date_4150_, 16);
v_b_5594_ = lean_ctor_get(v_date_4150_, 17);
v_B_5595_ = lean_ctor_get(v_date_4150_, 18);
v_h_5596_ = lean_ctor_get(v_date_4150_, 19);
v_K_5597_ = lean_ctor_get(v_date_4150_, 20);
v_k_5598_ = lean_ctor_get(v_date_4150_, 21);
v_H_5599_ = lean_ctor_get(v_date_4150_, 22);
v_m_5600_ = lean_ctor_get(v_date_4150_, 23);
v_s_5601_ = lean_ctor_get(v_date_4150_, 24);
v_S_5602_ = lean_ctor_get(v_date_4150_, 25);
v_A_5603_ = lean_ctor_get(v_date_4150_, 26);
v_n_5604_ = lean_ctor_get(v_date_4150_, 27);
v_V_5605_ = lean_ctor_get(v_date_4150_, 29);
v_z_5606_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_5607_ = lean_ctor_get(v_date_4150_, 31);
v_v_5608_ = lean_ctor_get(v_date_4150_, 32);
v_O_5609_ = lean_ctor_get(v_date_4150_, 33);
v_X_5610_ = lean_ctor_get(v_date_4150_, 34);
v_x_5611_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5612_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5622_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5622_ == 0)
{
lean_object* v_unused_5623_; 
v_unused_5623_ = lean_ctor_get(v_date_4150_, 28);
lean_dec(v_unused_5623_);
v___x_5614_ = v_date_4150_;
v_isShared_5615_ = v_isSharedCheck_5622_;
goto v_resetjp_5613_;
}
else
{
lean_inc(v_Z_5612_);
lean_inc(v_x_5611_);
lean_inc(v_X_5610_);
lean_inc(v_O_5609_);
lean_inc(v_v_5608_);
lean_inc(v_zabbrev_5607_);
lean_inc(v_z_5606_);
lean_inc(v_V_5605_);
lean_inc(v_n_5604_);
lean_inc(v_A_5603_);
lean_inc(v_S_5602_);
lean_inc(v_s_5601_);
lean_inc(v_m_5600_);
lean_inc(v_H_5599_);
lean_inc(v_k_5598_);
lean_inc(v_K_5597_);
lean_inc(v_h_5596_);
lean_inc(v_B_5595_);
lean_inc(v_b_5594_);
lean_inc(v_a_5593_);
lean_inc(v_F_5592_);
lean_inc(v_c_5591_);
lean_inc(v_e_5590_);
lean_inc(v_E_5589_);
lean_inc(v_W_5588_);
lean_inc(v_w_5587_);
lean_inc(v_q_5586_);
lean_inc(v_Q_5585_);
lean_inc(v_d_5584_);
lean_inc(v_L_5583_);
lean_inc(v_M_5582_);
lean_inc(v_D_5581_);
lean_inc(v_Y_5580_);
lean_inc(v_u_5579_);
lean_inc(v_y_5578_);
lean_inc(v_G_5577_);
lean_dec(v_date_4150_);
v___x_5614_ = lean_box(0);
v_isShared_5615_ = v_isSharedCheck_5622_;
goto v_resetjp_5613_;
}
v_resetjp_5613_:
{
lean_object* v___x_5617_; 
if (v_isShared_5576_ == 0)
{
lean_ctor_set_tag(v___x_5575_, 1);
lean_ctor_set(v___x_5575_, 0, v_data_4152_);
v___x_5617_ = v___x_5575_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5621_; 
v_reuseFailAlloc_5621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5621_, 0, v_data_4152_);
v___x_5617_ = v_reuseFailAlloc_5621_;
goto v_reusejp_5616_;
}
v_reusejp_5616_:
{
lean_object* v___x_5619_; 
if (v_isShared_5615_ == 0)
{
lean_ctor_set(v___x_5614_, 28, v___x_5617_);
v___x_5619_ = v___x_5614_;
goto v_reusejp_5618_;
}
else
{
lean_object* v_reuseFailAlloc_5620_; 
v_reuseFailAlloc_5620_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5620_, 0, v_G_5577_);
lean_ctor_set(v_reuseFailAlloc_5620_, 1, v_y_5578_);
lean_ctor_set(v_reuseFailAlloc_5620_, 2, v_u_5579_);
lean_ctor_set(v_reuseFailAlloc_5620_, 3, v_Y_5580_);
lean_ctor_set(v_reuseFailAlloc_5620_, 4, v_D_5581_);
lean_ctor_set(v_reuseFailAlloc_5620_, 5, v_M_5582_);
lean_ctor_set(v_reuseFailAlloc_5620_, 6, v_L_5583_);
lean_ctor_set(v_reuseFailAlloc_5620_, 7, v_d_5584_);
lean_ctor_set(v_reuseFailAlloc_5620_, 8, v_Q_5585_);
lean_ctor_set(v_reuseFailAlloc_5620_, 9, v_q_5586_);
lean_ctor_set(v_reuseFailAlloc_5620_, 10, v_w_5587_);
lean_ctor_set(v_reuseFailAlloc_5620_, 11, v_W_5588_);
lean_ctor_set(v_reuseFailAlloc_5620_, 12, v_E_5589_);
lean_ctor_set(v_reuseFailAlloc_5620_, 13, v_e_5590_);
lean_ctor_set(v_reuseFailAlloc_5620_, 14, v_c_5591_);
lean_ctor_set(v_reuseFailAlloc_5620_, 15, v_F_5592_);
lean_ctor_set(v_reuseFailAlloc_5620_, 16, v_a_5593_);
lean_ctor_set(v_reuseFailAlloc_5620_, 17, v_b_5594_);
lean_ctor_set(v_reuseFailAlloc_5620_, 18, v_B_5595_);
lean_ctor_set(v_reuseFailAlloc_5620_, 19, v_h_5596_);
lean_ctor_set(v_reuseFailAlloc_5620_, 20, v_K_5597_);
lean_ctor_set(v_reuseFailAlloc_5620_, 21, v_k_5598_);
lean_ctor_set(v_reuseFailAlloc_5620_, 22, v_H_5599_);
lean_ctor_set(v_reuseFailAlloc_5620_, 23, v_m_5600_);
lean_ctor_set(v_reuseFailAlloc_5620_, 24, v_s_5601_);
lean_ctor_set(v_reuseFailAlloc_5620_, 25, v_S_5602_);
lean_ctor_set(v_reuseFailAlloc_5620_, 26, v_A_5603_);
lean_ctor_set(v_reuseFailAlloc_5620_, 27, v_n_5604_);
lean_ctor_set(v_reuseFailAlloc_5620_, 28, v___x_5617_);
lean_ctor_set(v_reuseFailAlloc_5620_, 29, v_V_5605_);
lean_ctor_set(v_reuseFailAlloc_5620_, 30, v_z_5606_);
lean_ctor_set(v_reuseFailAlloc_5620_, 31, v_zabbrev_5607_);
lean_ctor_set(v_reuseFailAlloc_5620_, 32, v_v_5608_);
lean_ctor_set(v_reuseFailAlloc_5620_, 33, v_O_5609_);
lean_ctor_set(v_reuseFailAlloc_5620_, 34, v_X_5610_);
lean_ctor_set(v_reuseFailAlloc_5620_, 35, v_x_5611_);
lean_ctor_set(v_reuseFailAlloc_5620_, 36, v_Z_5612_);
v___x_5619_ = v_reuseFailAlloc_5620_;
goto v_reusejp_5618_;
}
v_reusejp_5618_:
{
return v___x_5619_;
}
}
}
}
}
case 29:
{
lean_object* v_G_5626_; lean_object* v_y_5627_; lean_object* v_u_5628_; lean_object* v_Y_5629_; lean_object* v_D_5630_; lean_object* v_M_5631_; lean_object* v_L_5632_; lean_object* v_d_5633_; lean_object* v_Q_5634_; lean_object* v_q_5635_; lean_object* v_w_5636_; lean_object* v_W_5637_; lean_object* v_E_5638_; lean_object* v_e_5639_; lean_object* v_c_5640_; lean_object* v_F_5641_; lean_object* v_a_5642_; lean_object* v_b_5643_; lean_object* v_B_5644_; lean_object* v_h_5645_; lean_object* v_K_5646_; lean_object* v_k_5647_; lean_object* v_H_5648_; lean_object* v_m_5649_; lean_object* v_s_5650_; lean_object* v_S_5651_; lean_object* v_A_5652_; lean_object* v_n_5653_; lean_object* v_N_5654_; lean_object* v_z_5655_; lean_object* v_zabbrev_5656_; lean_object* v_v_5657_; lean_object* v_O_5658_; lean_object* v_X_5659_; lean_object* v_x_5660_; lean_object* v_Z_5661_; lean_object* v___x_5663_; uint8_t v_isShared_5664_; uint8_t v_isSharedCheck_5669_; 
lean_dec_ref_known(v_modifier_4151_, 0);
v_G_5626_ = lean_ctor_get(v_date_4150_, 0);
v_y_5627_ = lean_ctor_get(v_date_4150_, 1);
v_u_5628_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5629_ = lean_ctor_get(v_date_4150_, 3);
v_D_5630_ = lean_ctor_get(v_date_4150_, 4);
v_M_5631_ = lean_ctor_get(v_date_4150_, 5);
v_L_5632_ = lean_ctor_get(v_date_4150_, 6);
v_d_5633_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5634_ = lean_ctor_get(v_date_4150_, 8);
v_q_5635_ = lean_ctor_get(v_date_4150_, 9);
v_w_5636_ = lean_ctor_get(v_date_4150_, 10);
v_W_5637_ = lean_ctor_get(v_date_4150_, 11);
v_E_5638_ = lean_ctor_get(v_date_4150_, 12);
v_e_5639_ = lean_ctor_get(v_date_4150_, 13);
v_c_5640_ = lean_ctor_get(v_date_4150_, 14);
v_F_5641_ = lean_ctor_get(v_date_4150_, 15);
v_a_5642_ = lean_ctor_get(v_date_4150_, 16);
v_b_5643_ = lean_ctor_get(v_date_4150_, 17);
v_B_5644_ = lean_ctor_get(v_date_4150_, 18);
v_h_5645_ = lean_ctor_get(v_date_4150_, 19);
v_K_5646_ = lean_ctor_get(v_date_4150_, 20);
v_k_5647_ = lean_ctor_get(v_date_4150_, 21);
v_H_5648_ = lean_ctor_get(v_date_4150_, 22);
v_m_5649_ = lean_ctor_get(v_date_4150_, 23);
v_s_5650_ = lean_ctor_get(v_date_4150_, 24);
v_S_5651_ = lean_ctor_get(v_date_4150_, 25);
v_A_5652_ = lean_ctor_get(v_date_4150_, 26);
v_n_5653_ = lean_ctor_get(v_date_4150_, 27);
v_N_5654_ = lean_ctor_get(v_date_4150_, 28);
v_z_5655_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_5656_ = lean_ctor_get(v_date_4150_, 31);
v_v_5657_ = lean_ctor_get(v_date_4150_, 32);
v_O_5658_ = lean_ctor_get(v_date_4150_, 33);
v_X_5659_ = lean_ctor_get(v_date_4150_, 34);
v_x_5660_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5661_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5669_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5669_ == 0)
{
lean_object* v_unused_5670_; 
v_unused_5670_ = lean_ctor_get(v_date_4150_, 29);
lean_dec(v_unused_5670_);
v___x_5663_ = v_date_4150_;
v_isShared_5664_ = v_isSharedCheck_5669_;
goto v_resetjp_5662_;
}
else
{
lean_inc(v_Z_5661_);
lean_inc(v_x_5660_);
lean_inc(v_X_5659_);
lean_inc(v_O_5658_);
lean_inc(v_v_5657_);
lean_inc(v_zabbrev_5656_);
lean_inc(v_z_5655_);
lean_inc(v_N_5654_);
lean_inc(v_n_5653_);
lean_inc(v_A_5652_);
lean_inc(v_S_5651_);
lean_inc(v_s_5650_);
lean_inc(v_m_5649_);
lean_inc(v_H_5648_);
lean_inc(v_k_5647_);
lean_inc(v_K_5646_);
lean_inc(v_h_5645_);
lean_inc(v_B_5644_);
lean_inc(v_b_5643_);
lean_inc(v_a_5642_);
lean_inc(v_F_5641_);
lean_inc(v_c_5640_);
lean_inc(v_e_5639_);
lean_inc(v_E_5638_);
lean_inc(v_W_5637_);
lean_inc(v_w_5636_);
lean_inc(v_q_5635_);
lean_inc(v_Q_5634_);
lean_inc(v_d_5633_);
lean_inc(v_L_5632_);
lean_inc(v_M_5631_);
lean_inc(v_D_5630_);
lean_inc(v_Y_5629_);
lean_inc(v_u_5628_);
lean_inc(v_y_5627_);
lean_inc(v_G_5626_);
lean_dec(v_date_4150_);
v___x_5663_ = lean_box(0);
v_isShared_5664_ = v_isSharedCheck_5669_;
goto v_resetjp_5662_;
}
v_resetjp_5662_:
{
lean_object* v___x_5665_; lean_object* v___x_5667_; 
v___x_5665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5665_, 0, v_data_4152_);
if (v_isShared_5664_ == 0)
{
lean_ctor_set(v___x_5663_, 29, v___x_5665_);
v___x_5667_ = v___x_5663_;
goto v_reusejp_5666_;
}
else
{
lean_object* v_reuseFailAlloc_5668_; 
v_reuseFailAlloc_5668_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5668_, 0, v_G_5626_);
lean_ctor_set(v_reuseFailAlloc_5668_, 1, v_y_5627_);
lean_ctor_set(v_reuseFailAlloc_5668_, 2, v_u_5628_);
lean_ctor_set(v_reuseFailAlloc_5668_, 3, v_Y_5629_);
lean_ctor_set(v_reuseFailAlloc_5668_, 4, v_D_5630_);
lean_ctor_set(v_reuseFailAlloc_5668_, 5, v_M_5631_);
lean_ctor_set(v_reuseFailAlloc_5668_, 6, v_L_5632_);
lean_ctor_set(v_reuseFailAlloc_5668_, 7, v_d_5633_);
lean_ctor_set(v_reuseFailAlloc_5668_, 8, v_Q_5634_);
lean_ctor_set(v_reuseFailAlloc_5668_, 9, v_q_5635_);
lean_ctor_set(v_reuseFailAlloc_5668_, 10, v_w_5636_);
lean_ctor_set(v_reuseFailAlloc_5668_, 11, v_W_5637_);
lean_ctor_set(v_reuseFailAlloc_5668_, 12, v_E_5638_);
lean_ctor_set(v_reuseFailAlloc_5668_, 13, v_e_5639_);
lean_ctor_set(v_reuseFailAlloc_5668_, 14, v_c_5640_);
lean_ctor_set(v_reuseFailAlloc_5668_, 15, v_F_5641_);
lean_ctor_set(v_reuseFailAlloc_5668_, 16, v_a_5642_);
lean_ctor_set(v_reuseFailAlloc_5668_, 17, v_b_5643_);
lean_ctor_set(v_reuseFailAlloc_5668_, 18, v_B_5644_);
lean_ctor_set(v_reuseFailAlloc_5668_, 19, v_h_5645_);
lean_ctor_set(v_reuseFailAlloc_5668_, 20, v_K_5646_);
lean_ctor_set(v_reuseFailAlloc_5668_, 21, v_k_5647_);
lean_ctor_set(v_reuseFailAlloc_5668_, 22, v_H_5648_);
lean_ctor_set(v_reuseFailAlloc_5668_, 23, v_m_5649_);
lean_ctor_set(v_reuseFailAlloc_5668_, 24, v_s_5650_);
lean_ctor_set(v_reuseFailAlloc_5668_, 25, v_S_5651_);
lean_ctor_set(v_reuseFailAlloc_5668_, 26, v_A_5652_);
lean_ctor_set(v_reuseFailAlloc_5668_, 27, v_n_5653_);
lean_ctor_set(v_reuseFailAlloc_5668_, 28, v_N_5654_);
lean_ctor_set(v_reuseFailAlloc_5668_, 29, v___x_5665_);
lean_ctor_set(v_reuseFailAlloc_5668_, 30, v_z_5655_);
lean_ctor_set(v_reuseFailAlloc_5668_, 31, v_zabbrev_5656_);
lean_ctor_set(v_reuseFailAlloc_5668_, 32, v_v_5657_);
lean_ctor_set(v_reuseFailAlloc_5668_, 33, v_O_5658_);
lean_ctor_set(v_reuseFailAlloc_5668_, 34, v_X_5659_);
lean_ctor_set(v_reuseFailAlloc_5668_, 35, v_x_5660_);
lean_ctor_set(v_reuseFailAlloc_5668_, 36, v_Z_5661_);
v___x_5667_ = v_reuseFailAlloc_5668_;
goto v_reusejp_5666_;
}
v_reusejp_5666_:
{
return v___x_5667_;
}
}
}
case 30:
{
uint8_t v_presentation_5671_; 
v_presentation_5671_ = lean_ctor_get_uint8(v_modifier_4151_, 0);
lean_dec_ref_known(v_modifier_4151_, 0);
if (v_presentation_5671_ == 0)
{
lean_object* v_G_5672_; lean_object* v_y_5673_; lean_object* v_u_5674_; lean_object* v_Y_5675_; lean_object* v_D_5676_; lean_object* v_M_5677_; lean_object* v_L_5678_; lean_object* v_d_5679_; lean_object* v_Q_5680_; lean_object* v_q_5681_; lean_object* v_w_5682_; lean_object* v_W_5683_; lean_object* v_E_5684_; lean_object* v_e_5685_; lean_object* v_c_5686_; lean_object* v_F_5687_; lean_object* v_a_5688_; lean_object* v_b_5689_; lean_object* v_B_5690_; lean_object* v_h_5691_; lean_object* v_K_5692_; lean_object* v_k_5693_; lean_object* v_H_5694_; lean_object* v_m_5695_; lean_object* v_s_5696_; lean_object* v_S_5697_; lean_object* v_A_5698_; lean_object* v_n_5699_; lean_object* v_N_5700_; lean_object* v_V_5701_; lean_object* v_z_5702_; lean_object* v_v_5703_; lean_object* v_O_5704_; lean_object* v_X_5705_; lean_object* v_x_5706_; lean_object* v_Z_5707_; lean_object* v___x_5709_; uint8_t v_isShared_5710_; uint8_t v_isSharedCheck_5715_; 
v_G_5672_ = lean_ctor_get(v_date_4150_, 0);
v_y_5673_ = lean_ctor_get(v_date_4150_, 1);
v_u_5674_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5675_ = lean_ctor_get(v_date_4150_, 3);
v_D_5676_ = lean_ctor_get(v_date_4150_, 4);
v_M_5677_ = lean_ctor_get(v_date_4150_, 5);
v_L_5678_ = lean_ctor_get(v_date_4150_, 6);
v_d_5679_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5680_ = lean_ctor_get(v_date_4150_, 8);
v_q_5681_ = lean_ctor_get(v_date_4150_, 9);
v_w_5682_ = lean_ctor_get(v_date_4150_, 10);
v_W_5683_ = lean_ctor_get(v_date_4150_, 11);
v_E_5684_ = lean_ctor_get(v_date_4150_, 12);
v_e_5685_ = lean_ctor_get(v_date_4150_, 13);
v_c_5686_ = lean_ctor_get(v_date_4150_, 14);
v_F_5687_ = lean_ctor_get(v_date_4150_, 15);
v_a_5688_ = lean_ctor_get(v_date_4150_, 16);
v_b_5689_ = lean_ctor_get(v_date_4150_, 17);
v_B_5690_ = lean_ctor_get(v_date_4150_, 18);
v_h_5691_ = lean_ctor_get(v_date_4150_, 19);
v_K_5692_ = lean_ctor_get(v_date_4150_, 20);
v_k_5693_ = lean_ctor_get(v_date_4150_, 21);
v_H_5694_ = lean_ctor_get(v_date_4150_, 22);
v_m_5695_ = lean_ctor_get(v_date_4150_, 23);
v_s_5696_ = lean_ctor_get(v_date_4150_, 24);
v_S_5697_ = lean_ctor_get(v_date_4150_, 25);
v_A_5698_ = lean_ctor_get(v_date_4150_, 26);
v_n_5699_ = lean_ctor_get(v_date_4150_, 27);
v_N_5700_ = lean_ctor_get(v_date_4150_, 28);
v_V_5701_ = lean_ctor_get(v_date_4150_, 29);
v_z_5702_ = lean_ctor_get(v_date_4150_, 30);
v_v_5703_ = lean_ctor_get(v_date_4150_, 32);
v_O_5704_ = lean_ctor_get(v_date_4150_, 33);
v_X_5705_ = lean_ctor_get(v_date_4150_, 34);
v_x_5706_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5707_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5715_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5715_ == 0)
{
lean_object* v_unused_5716_; 
v_unused_5716_ = lean_ctor_get(v_date_4150_, 31);
lean_dec(v_unused_5716_);
v___x_5709_ = v_date_4150_;
v_isShared_5710_ = v_isSharedCheck_5715_;
goto v_resetjp_5708_;
}
else
{
lean_inc(v_Z_5707_);
lean_inc(v_x_5706_);
lean_inc(v_X_5705_);
lean_inc(v_O_5704_);
lean_inc(v_v_5703_);
lean_inc(v_z_5702_);
lean_inc(v_V_5701_);
lean_inc(v_N_5700_);
lean_inc(v_n_5699_);
lean_inc(v_A_5698_);
lean_inc(v_S_5697_);
lean_inc(v_s_5696_);
lean_inc(v_m_5695_);
lean_inc(v_H_5694_);
lean_inc(v_k_5693_);
lean_inc(v_K_5692_);
lean_inc(v_h_5691_);
lean_inc(v_B_5690_);
lean_inc(v_b_5689_);
lean_inc(v_a_5688_);
lean_inc(v_F_5687_);
lean_inc(v_c_5686_);
lean_inc(v_e_5685_);
lean_inc(v_E_5684_);
lean_inc(v_W_5683_);
lean_inc(v_w_5682_);
lean_inc(v_q_5681_);
lean_inc(v_Q_5680_);
lean_inc(v_d_5679_);
lean_inc(v_L_5678_);
lean_inc(v_M_5677_);
lean_inc(v_D_5676_);
lean_inc(v_Y_5675_);
lean_inc(v_u_5674_);
lean_inc(v_y_5673_);
lean_inc(v_G_5672_);
lean_dec(v_date_4150_);
v___x_5709_ = lean_box(0);
v_isShared_5710_ = v_isSharedCheck_5715_;
goto v_resetjp_5708_;
}
v_resetjp_5708_:
{
lean_object* v___x_5711_; lean_object* v___x_5713_; 
v___x_5711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5711_, 0, v_data_4152_);
if (v_isShared_5710_ == 0)
{
lean_ctor_set(v___x_5709_, 31, v___x_5711_);
v___x_5713_ = v___x_5709_;
goto v_reusejp_5712_;
}
else
{
lean_object* v_reuseFailAlloc_5714_; 
v_reuseFailAlloc_5714_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5714_, 0, v_G_5672_);
lean_ctor_set(v_reuseFailAlloc_5714_, 1, v_y_5673_);
lean_ctor_set(v_reuseFailAlloc_5714_, 2, v_u_5674_);
lean_ctor_set(v_reuseFailAlloc_5714_, 3, v_Y_5675_);
lean_ctor_set(v_reuseFailAlloc_5714_, 4, v_D_5676_);
lean_ctor_set(v_reuseFailAlloc_5714_, 5, v_M_5677_);
lean_ctor_set(v_reuseFailAlloc_5714_, 6, v_L_5678_);
lean_ctor_set(v_reuseFailAlloc_5714_, 7, v_d_5679_);
lean_ctor_set(v_reuseFailAlloc_5714_, 8, v_Q_5680_);
lean_ctor_set(v_reuseFailAlloc_5714_, 9, v_q_5681_);
lean_ctor_set(v_reuseFailAlloc_5714_, 10, v_w_5682_);
lean_ctor_set(v_reuseFailAlloc_5714_, 11, v_W_5683_);
lean_ctor_set(v_reuseFailAlloc_5714_, 12, v_E_5684_);
lean_ctor_set(v_reuseFailAlloc_5714_, 13, v_e_5685_);
lean_ctor_set(v_reuseFailAlloc_5714_, 14, v_c_5686_);
lean_ctor_set(v_reuseFailAlloc_5714_, 15, v_F_5687_);
lean_ctor_set(v_reuseFailAlloc_5714_, 16, v_a_5688_);
lean_ctor_set(v_reuseFailAlloc_5714_, 17, v_b_5689_);
lean_ctor_set(v_reuseFailAlloc_5714_, 18, v_B_5690_);
lean_ctor_set(v_reuseFailAlloc_5714_, 19, v_h_5691_);
lean_ctor_set(v_reuseFailAlloc_5714_, 20, v_K_5692_);
lean_ctor_set(v_reuseFailAlloc_5714_, 21, v_k_5693_);
lean_ctor_set(v_reuseFailAlloc_5714_, 22, v_H_5694_);
lean_ctor_set(v_reuseFailAlloc_5714_, 23, v_m_5695_);
lean_ctor_set(v_reuseFailAlloc_5714_, 24, v_s_5696_);
lean_ctor_set(v_reuseFailAlloc_5714_, 25, v_S_5697_);
lean_ctor_set(v_reuseFailAlloc_5714_, 26, v_A_5698_);
lean_ctor_set(v_reuseFailAlloc_5714_, 27, v_n_5699_);
lean_ctor_set(v_reuseFailAlloc_5714_, 28, v_N_5700_);
lean_ctor_set(v_reuseFailAlloc_5714_, 29, v_V_5701_);
lean_ctor_set(v_reuseFailAlloc_5714_, 30, v_z_5702_);
lean_ctor_set(v_reuseFailAlloc_5714_, 31, v___x_5711_);
lean_ctor_set(v_reuseFailAlloc_5714_, 32, v_v_5703_);
lean_ctor_set(v_reuseFailAlloc_5714_, 33, v_O_5704_);
lean_ctor_set(v_reuseFailAlloc_5714_, 34, v_X_5705_);
lean_ctor_set(v_reuseFailAlloc_5714_, 35, v_x_5706_);
lean_ctor_set(v_reuseFailAlloc_5714_, 36, v_Z_5707_);
v___x_5713_ = v_reuseFailAlloc_5714_;
goto v_reusejp_5712_;
}
v_reusejp_5712_:
{
return v___x_5713_;
}
}
}
else
{
lean_object* v_G_5717_; lean_object* v_y_5718_; lean_object* v_u_5719_; lean_object* v_Y_5720_; lean_object* v_D_5721_; lean_object* v_M_5722_; lean_object* v_L_5723_; lean_object* v_d_5724_; lean_object* v_Q_5725_; lean_object* v_q_5726_; lean_object* v_w_5727_; lean_object* v_W_5728_; lean_object* v_E_5729_; lean_object* v_e_5730_; lean_object* v_c_5731_; lean_object* v_F_5732_; lean_object* v_a_5733_; lean_object* v_b_5734_; lean_object* v_B_5735_; lean_object* v_h_5736_; lean_object* v_K_5737_; lean_object* v_k_5738_; lean_object* v_H_5739_; lean_object* v_m_5740_; lean_object* v_s_5741_; lean_object* v_S_5742_; lean_object* v_A_5743_; lean_object* v_n_5744_; lean_object* v_N_5745_; lean_object* v_V_5746_; lean_object* v_zabbrev_5747_; lean_object* v_v_5748_; lean_object* v_O_5749_; lean_object* v_X_5750_; lean_object* v_x_5751_; lean_object* v_Z_5752_; lean_object* v___x_5754_; uint8_t v_isShared_5755_; uint8_t v_isSharedCheck_5760_; 
v_G_5717_ = lean_ctor_get(v_date_4150_, 0);
v_y_5718_ = lean_ctor_get(v_date_4150_, 1);
v_u_5719_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5720_ = lean_ctor_get(v_date_4150_, 3);
v_D_5721_ = lean_ctor_get(v_date_4150_, 4);
v_M_5722_ = lean_ctor_get(v_date_4150_, 5);
v_L_5723_ = lean_ctor_get(v_date_4150_, 6);
v_d_5724_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5725_ = lean_ctor_get(v_date_4150_, 8);
v_q_5726_ = lean_ctor_get(v_date_4150_, 9);
v_w_5727_ = lean_ctor_get(v_date_4150_, 10);
v_W_5728_ = lean_ctor_get(v_date_4150_, 11);
v_E_5729_ = lean_ctor_get(v_date_4150_, 12);
v_e_5730_ = lean_ctor_get(v_date_4150_, 13);
v_c_5731_ = lean_ctor_get(v_date_4150_, 14);
v_F_5732_ = lean_ctor_get(v_date_4150_, 15);
v_a_5733_ = lean_ctor_get(v_date_4150_, 16);
v_b_5734_ = lean_ctor_get(v_date_4150_, 17);
v_B_5735_ = lean_ctor_get(v_date_4150_, 18);
v_h_5736_ = lean_ctor_get(v_date_4150_, 19);
v_K_5737_ = lean_ctor_get(v_date_4150_, 20);
v_k_5738_ = lean_ctor_get(v_date_4150_, 21);
v_H_5739_ = lean_ctor_get(v_date_4150_, 22);
v_m_5740_ = lean_ctor_get(v_date_4150_, 23);
v_s_5741_ = lean_ctor_get(v_date_4150_, 24);
v_S_5742_ = lean_ctor_get(v_date_4150_, 25);
v_A_5743_ = lean_ctor_get(v_date_4150_, 26);
v_n_5744_ = lean_ctor_get(v_date_4150_, 27);
v_N_5745_ = lean_ctor_get(v_date_4150_, 28);
v_V_5746_ = lean_ctor_get(v_date_4150_, 29);
v_zabbrev_5747_ = lean_ctor_get(v_date_4150_, 31);
v_v_5748_ = lean_ctor_get(v_date_4150_, 32);
v_O_5749_ = lean_ctor_get(v_date_4150_, 33);
v_X_5750_ = lean_ctor_get(v_date_4150_, 34);
v_x_5751_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5752_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5760_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5760_ == 0)
{
lean_object* v_unused_5761_; 
v_unused_5761_ = lean_ctor_get(v_date_4150_, 30);
lean_dec(v_unused_5761_);
v___x_5754_ = v_date_4150_;
v_isShared_5755_ = v_isSharedCheck_5760_;
goto v_resetjp_5753_;
}
else
{
lean_inc(v_Z_5752_);
lean_inc(v_x_5751_);
lean_inc(v_X_5750_);
lean_inc(v_O_5749_);
lean_inc(v_v_5748_);
lean_inc(v_zabbrev_5747_);
lean_inc(v_V_5746_);
lean_inc(v_N_5745_);
lean_inc(v_n_5744_);
lean_inc(v_A_5743_);
lean_inc(v_S_5742_);
lean_inc(v_s_5741_);
lean_inc(v_m_5740_);
lean_inc(v_H_5739_);
lean_inc(v_k_5738_);
lean_inc(v_K_5737_);
lean_inc(v_h_5736_);
lean_inc(v_B_5735_);
lean_inc(v_b_5734_);
lean_inc(v_a_5733_);
lean_inc(v_F_5732_);
lean_inc(v_c_5731_);
lean_inc(v_e_5730_);
lean_inc(v_E_5729_);
lean_inc(v_W_5728_);
lean_inc(v_w_5727_);
lean_inc(v_q_5726_);
lean_inc(v_Q_5725_);
lean_inc(v_d_5724_);
lean_inc(v_L_5723_);
lean_inc(v_M_5722_);
lean_inc(v_D_5721_);
lean_inc(v_Y_5720_);
lean_inc(v_u_5719_);
lean_inc(v_y_5718_);
lean_inc(v_G_5717_);
lean_dec(v_date_4150_);
v___x_5754_ = lean_box(0);
v_isShared_5755_ = v_isSharedCheck_5760_;
goto v_resetjp_5753_;
}
v_resetjp_5753_:
{
lean_object* v___x_5756_; lean_object* v___x_5758_; 
v___x_5756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5756_, 0, v_data_4152_);
if (v_isShared_5755_ == 0)
{
lean_ctor_set(v___x_5754_, 30, v___x_5756_);
v___x_5758_ = v___x_5754_;
goto v_reusejp_5757_;
}
else
{
lean_object* v_reuseFailAlloc_5759_; 
v_reuseFailAlloc_5759_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5759_, 0, v_G_5717_);
lean_ctor_set(v_reuseFailAlloc_5759_, 1, v_y_5718_);
lean_ctor_set(v_reuseFailAlloc_5759_, 2, v_u_5719_);
lean_ctor_set(v_reuseFailAlloc_5759_, 3, v_Y_5720_);
lean_ctor_set(v_reuseFailAlloc_5759_, 4, v_D_5721_);
lean_ctor_set(v_reuseFailAlloc_5759_, 5, v_M_5722_);
lean_ctor_set(v_reuseFailAlloc_5759_, 6, v_L_5723_);
lean_ctor_set(v_reuseFailAlloc_5759_, 7, v_d_5724_);
lean_ctor_set(v_reuseFailAlloc_5759_, 8, v_Q_5725_);
lean_ctor_set(v_reuseFailAlloc_5759_, 9, v_q_5726_);
lean_ctor_set(v_reuseFailAlloc_5759_, 10, v_w_5727_);
lean_ctor_set(v_reuseFailAlloc_5759_, 11, v_W_5728_);
lean_ctor_set(v_reuseFailAlloc_5759_, 12, v_E_5729_);
lean_ctor_set(v_reuseFailAlloc_5759_, 13, v_e_5730_);
lean_ctor_set(v_reuseFailAlloc_5759_, 14, v_c_5731_);
lean_ctor_set(v_reuseFailAlloc_5759_, 15, v_F_5732_);
lean_ctor_set(v_reuseFailAlloc_5759_, 16, v_a_5733_);
lean_ctor_set(v_reuseFailAlloc_5759_, 17, v_b_5734_);
lean_ctor_set(v_reuseFailAlloc_5759_, 18, v_B_5735_);
lean_ctor_set(v_reuseFailAlloc_5759_, 19, v_h_5736_);
lean_ctor_set(v_reuseFailAlloc_5759_, 20, v_K_5737_);
lean_ctor_set(v_reuseFailAlloc_5759_, 21, v_k_5738_);
lean_ctor_set(v_reuseFailAlloc_5759_, 22, v_H_5739_);
lean_ctor_set(v_reuseFailAlloc_5759_, 23, v_m_5740_);
lean_ctor_set(v_reuseFailAlloc_5759_, 24, v_s_5741_);
lean_ctor_set(v_reuseFailAlloc_5759_, 25, v_S_5742_);
lean_ctor_set(v_reuseFailAlloc_5759_, 26, v_A_5743_);
lean_ctor_set(v_reuseFailAlloc_5759_, 27, v_n_5744_);
lean_ctor_set(v_reuseFailAlloc_5759_, 28, v_N_5745_);
lean_ctor_set(v_reuseFailAlloc_5759_, 29, v_V_5746_);
lean_ctor_set(v_reuseFailAlloc_5759_, 30, v___x_5756_);
lean_ctor_set(v_reuseFailAlloc_5759_, 31, v_zabbrev_5747_);
lean_ctor_set(v_reuseFailAlloc_5759_, 32, v_v_5748_);
lean_ctor_set(v_reuseFailAlloc_5759_, 33, v_O_5749_);
lean_ctor_set(v_reuseFailAlloc_5759_, 34, v_X_5750_);
lean_ctor_set(v_reuseFailAlloc_5759_, 35, v_x_5751_);
lean_ctor_set(v_reuseFailAlloc_5759_, 36, v_Z_5752_);
v___x_5758_ = v_reuseFailAlloc_5759_;
goto v_reusejp_5757_;
}
v_reusejp_5757_:
{
return v___x_5758_;
}
}
}
}
case 31:
{
uint8_t v_presentation_5762_; 
v_presentation_5762_ = lean_ctor_get_uint8(v_modifier_4151_, 0);
lean_dec_ref_known(v_modifier_4151_, 0);
if (v_presentation_5762_ == 0)
{
lean_object* v_G_5763_; lean_object* v_y_5764_; lean_object* v_u_5765_; lean_object* v_Y_5766_; lean_object* v_D_5767_; lean_object* v_M_5768_; lean_object* v_L_5769_; lean_object* v_d_5770_; lean_object* v_Q_5771_; lean_object* v_q_5772_; lean_object* v_w_5773_; lean_object* v_W_5774_; lean_object* v_E_5775_; lean_object* v_e_5776_; lean_object* v_c_5777_; lean_object* v_F_5778_; lean_object* v_a_5779_; lean_object* v_b_5780_; lean_object* v_B_5781_; lean_object* v_h_5782_; lean_object* v_K_5783_; lean_object* v_k_5784_; lean_object* v_H_5785_; lean_object* v_m_5786_; lean_object* v_s_5787_; lean_object* v_S_5788_; lean_object* v_A_5789_; lean_object* v_n_5790_; lean_object* v_N_5791_; lean_object* v_V_5792_; lean_object* v_z_5793_; lean_object* v_v_5794_; lean_object* v_O_5795_; lean_object* v_X_5796_; lean_object* v_x_5797_; lean_object* v_Z_5798_; lean_object* v___x_5800_; uint8_t v_isShared_5801_; uint8_t v_isSharedCheck_5806_; 
v_G_5763_ = lean_ctor_get(v_date_4150_, 0);
v_y_5764_ = lean_ctor_get(v_date_4150_, 1);
v_u_5765_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5766_ = lean_ctor_get(v_date_4150_, 3);
v_D_5767_ = lean_ctor_get(v_date_4150_, 4);
v_M_5768_ = lean_ctor_get(v_date_4150_, 5);
v_L_5769_ = lean_ctor_get(v_date_4150_, 6);
v_d_5770_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5771_ = lean_ctor_get(v_date_4150_, 8);
v_q_5772_ = lean_ctor_get(v_date_4150_, 9);
v_w_5773_ = lean_ctor_get(v_date_4150_, 10);
v_W_5774_ = lean_ctor_get(v_date_4150_, 11);
v_E_5775_ = lean_ctor_get(v_date_4150_, 12);
v_e_5776_ = lean_ctor_get(v_date_4150_, 13);
v_c_5777_ = lean_ctor_get(v_date_4150_, 14);
v_F_5778_ = lean_ctor_get(v_date_4150_, 15);
v_a_5779_ = lean_ctor_get(v_date_4150_, 16);
v_b_5780_ = lean_ctor_get(v_date_4150_, 17);
v_B_5781_ = lean_ctor_get(v_date_4150_, 18);
v_h_5782_ = lean_ctor_get(v_date_4150_, 19);
v_K_5783_ = lean_ctor_get(v_date_4150_, 20);
v_k_5784_ = lean_ctor_get(v_date_4150_, 21);
v_H_5785_ = lean_ctor_get(v_date_4150_, 22);
v_m_5786_ = lean_ctor_get(v_date_4150_, 23);
v_s_5787_ = lean_ctor_get(v_date_4150_, 24);
v_S_5788_ = lean_ctor_get(v_date_4150_, 25);
v_A_5789_ = lean_ctor_get(v_date_4150_, 26);
v_n_5790_ = lean_ctor_get(v_date_4150_, 27);
v_N_5791_ = lean_ctor_get(v_date_4150_, 28);
v_V_5792_ = lean_ctor_get(v_date_4150_, 29);
v_z_5793_ = lean_ctor_get(v_date_4150_, 30);
v_v_5794_ = lean_ctor_get(v_date_4150_, 32);
v_O_5795_ = lean_ctor_get(v_date_4150_, 33);
v_X_5796_ = lean_ctor_get(v_date_4150_, 34);
v_x_5797_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5798_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5806_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5806_ == 0)
{
lean_object* v_unused_5807_; 
v_unused_5807_ = lean_ctor_get(v_date_4150_, 31);
lean_dec(v_unused_5807_);
v___x_5800_ = v_date_4150_;
v_isShared_5801_ = v_isSharedCheck_5806_;
goto v_resetjp_5799_;
}
else
{
lean_inc(v_Z_5798_);
lean_inc(v_x_5797_);
lean_inc(v_X_5796_);
lean_inc(v_O_5795_);
lean_inc(v_v_5794_);
lean_inc(v_z_5793_);
lean_inc(v_V_5792_);
lean_inc(v_N_5791_);
lean_inc(v_n_5790_);
lean_inc(v_A_5789_);
lean_inc(v_S_5788_);
lean_inc(v_s_5787_);
lean_inc(v_m_5786_);
lean_inc(v_H_5785_);
lean_inc(v_k_5784_);
lean_inc(v_K_5783_);
lean_inc(v_h_5782_);
lean_inc(v_B_5781_);
lean_inc(v_b_5780_);
lean_inc(v_a_5779_);
lean_inc(v_F_5778_);
lean_inc(v_c_5777_);
lean_inc(v_e_5776_);
lean_inc(v_E_5775_);
lean_inc(v_W_5774_);
lean_inc(v_w_5773_);
lean_inc(v_q_5772_);
lean_inc(v_Q_5771_);
lean_inc(v_d_5770_);
lean_inc(v_L_5769_);
lean_inc(v_M_5768_);
lean_inc(v_D_5767_);
lean_inc(v_Y_5766_);
lean_inc(v_u_5765_);
lean_inc(v_y_5764_);
lean_inc(v_G_5763_);
lean_dec(v_date_4150_);
v___x_5800_ = lean_box(0);
v_isShared_5801_ = v_isSharedCheck_5806_;
goto v_resetjp_5799_;
}
v_resetjp_5799_:
{
lean_object* v___x_5802_; lean_object* v___x_5804_; 
v___x_5802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5802_, 0, v_data_4152_);
if (v_isShared_5801_ == 0)
{
lean_ctor_set(v___x_5800_, 31, v___x_5802_);
v___x_5804_ = v___x_5800_;
goto v_reusejp_5803_;
}
else
{
lean_object* v_reuseFailAlloc_5805_; 
v_reuseFailAlloc_5805_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5805_, 0, v_G_5763_);
lean_ctor_set(v_reuseFailAlloc_5805_, 1, v_y_5764_);
lean_ctor_set(v_reuseFailAlloc_5805_, 2, v_u_5765_);
lean_ctor_set(v_reuseFailAlloc_5805_, 3, v_Y_5766_);
lean_ctor_set(v_reuseFailAlloc_5805_, 4, v_D_5767_);
lean_ctor_set(v_reuseFailAlloc_5805_, 5, v_M_5768_);
lean_ctor_set(v_reuseFailAlloc_5805_, 6, v_L_5769_);
lean_ctor_set(v_reuseFailAlloc_5805_, 7, v_d_5770_);
lean_ctor_set(v_reuseFailAlloc_5805_, 8, v_Q_5771_);
lean_ctor_set(v_reuseFailAlloc_5805_, 9, v_q_5772_);
lean_ctor_set(v_reuseFailAlloc_5805_, 10, v_w_5773_);
lean_ctor_set(v_reuseFailAlloc_5805_, 11, v_W_5774_);
lean_ctor_set(v_reuseFailAlloc_5805_, 12, v_E_5775_);
lean_ctor_set(v_reuseFailAlloc_5805_, 13, v_e_5776_);
lean_ctor_set(v_reuseFailAlloc_5805_, 14, v_c_5777_);
lean_ctor_set(v_reuseFailAlloc_5805_, 15, v_F_5778_);
lean_ctor_set(v_reuseFailAlloc_5805_, 16, v_a_5779_);
lean_ctor_set(v_reuseFailAlloc_5805_, 17, v_b_5780_);
lean_ctor_set(v_reuseFailAlloc_5805_, 18, v_B_5781_);
lean_ctor_set(v_reuseFailAlloc_5805_, 19, v_h_5782_);
lean_ctor_set(v_reuseFailAlloc_5805_, 20, v_K_5783_);
lean_ctor_set(v_reuseFailAlloc_5805_, 21, v_k_5784_);
lean_ctor_set(v_reuseFailAlloc_5805_, 22, v_H_5785_);
lean_ctor_set(v_reuseFailAlloc_5805_, 23, v_m_5786_);
lean_ctor_set(v_reuseFailAlloc_5805_, 24, v_s_5787_);
lean_ctor_set(v_reuseFailAlloc_5805_, 25, v_S_5788_);
lean_ctor_set(v_reuseFailAlloc_5805_, 26, v_A_5789_);
lean_ctor_set(v_reuseFailAlloc_5805_, 27, v_n_5790_);
lean_ctor_set(v_reuseFailAlloc_5805_, 28, v_N_5791_);
lean_ctor_set(v_reuseFailAlloc_5805_, 29, v_V_5792_);
lean_ctor_set(v_reuseFailAlloc_5805_, 30, v_z_5793_);
lean_ctor_set(v_reuseFailAlloc_5805_, 31, v___x_5802_);
lean_ctor_set(v_reuseFailAlloc_5805_, 32, v_v_5794_);
lean_ctor_set(v_reuseFailAlloc_5805_, 33, v_O_5795_);
lean_ctor_set(v_reuseFailAlloc_5805_, 34, v_X_5796_);
lean_ctor_set(v_reuseFailAlloc_5805_, 35, v_x_5797_);
lean_ctor_set(v_reuseFailAlloc_5805_, 36, v_Z_5798_);
v___x_5804_ = v_reuseFailAlloc_5805_;
goto v_reusejp_5803_;
}
v_reusejp_5803_:
{
return v___x_5804_;
}
}
}
else
{
lean_object* v_G_5808_; lean_object* v_y_5809_; lean_object* v_u_5810_; lean_object* v_Y_5811_; lean_object* v_D_5812_; lean_object* v_M_5813_; lean_object* v_L_5814_; lean_object* v_d_5815_; lean_object* v_Q_5816_; lean_object* v_q_5817_; lean_object* v_w_5818_; lean_object* v_W_5819_; lean_object* v_E_5820_; lean_object* v_e_5821_; lean_object* v_c_5822_; lean_object* v_F_5823_; lean_object* v_a_5824_; lean_object* v_b_5825_; lean_object* v_B_5826_; lean_object* v_h_5827_; lean_object* v_K_5828_; lean_object* v_k_5829_; lean_object* v_H_5830_; lean_object* v_m_5831_; lean_object* v_s_5832_; lean_object* v_S_5833_; lean_object* v_A_5834_; lean_object* v_n_5835_; lean_object* v_N_5836_; lean_object* v_V_5837_; lean_object* v_z_5838_; lean_object* v_zabbrev_5839_; lean_object* v_O_5840_; lean_object* v_X_5841_; lean_object* v_x_5842_; lean_object* v_Z_5843_; lean_object* v___x_5845_; uint8_t v_isShared_5846_; uint8_t v_isSharedCheck_5851_; 
v_G_5808_ = lean_ctor_get(v_date_4150_, 0);
v_y_5809_ = lean_ctor_get(v_date_4150_, 1);
v_u_5810_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5811_ = lean_ctor_get(v_date_4150_, 3);
v_D_5812_ = lean_ctor_get(v_date_4150_, 4);
v_M_5813_ = lean_ctor_get(v_date_4150_, 5);
v_L_5814_ = lean_ctor_get(v_date_4150_, 6);
v_d_5815_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5816_ = lean_ctor_get(v_date_4150_, 8);
v_q_5817_ = lean_ctor_get(v_date_4150_, 9);
v_w_5818_ = lean_ctor_get(v_date_4150_, 10);
v_W_5819_ = lean_ctor_get(v_date_4150_, 11);
v_E_5820_ = lean_ctor_get(v_date_4150_, 12);
v_e_5821_ = lean_ctor_get(v_date_4150_, 13);
v_c_5822_ = lean_ctor_get(v_date_4150_, 14);
v_F_5823_ = lean_ctor_get(v_date_4150_, 15);
v_a_5824_ = lean_ctor_get(v_date_4150_, 16);
v_b_5825_ = lean_ctor_get(v_date_4150_, 17);
v_B_5826_ = lean_ctor_get(v_date_4150_, 18);
v_h_5827_ = lean_ctor_get(v_date_4150_, 19);
v_K_5828_ = lean_ctor_get(v_date_4150_, 20);
v_k_5829_ = lean_ctor_get(v_date_4150_, 21);
v_H_5830_ = lean_ctor_get(v_date_4150_, 22);
v_m_5831_ = lean_ctor_get(v_date_4150_, 23);
v_s_5832_ = lean_ctor_get(v_date_4150_, 24);
v_S_5833_ = lean_ctor_get(v_date_4150_, 25);
v_A_5834_ = lean_ctor_get(v_date_4150_, 26);
v_n_5835_ = lean_ctor_get(v_date_4150_, 27);
v_N_5836_ = lean_ctor_get(v_date_4150_, 28);
v_V_5837_ = lean_ctor_get(v_date_4150_, 29);
v_z_5838_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_5839_ = lean_ctor_get(v_date_4150_, 31);
v_O_5840_ = lean_ctor_get(v_date_4150_, 33);
v_X_5841_ = lean_ctor_get(v_date_4150_, 34);
v_x_5842_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5843_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5851_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5851_ == 0)
{
lean_object* v_unused_5852_; 
v_unused_5852_ = lean_ctor_get(v_date_4150_, 32);
lean_dec(v_unused_5852_);
v___x_5845_ = v_date_4150_;
v_isShared_5846_ = v_isSharedCheck_5851_;
goto v_resetjp_5844_;
}
else
{
lean_inc(v_Z_5843_);
lean_inc(v_x_5842_);
lean_inc(v_X_5841_);
lean_inc(v_O_5840_);
lean_inc(v_zabbrev_5839_);
lean_inc(v_z_5838_);
lean_inc(v_V_5837_);
lean_inc(v_N_5836_);
lean_inc(v_n_5835_);
lean_inc(v_A_5834_);
lean_inc(v_S_5833_);
lean_inc(v_s_5832_);
lean_inc(v_m_5831_);
lean_inc(v_H_5830_);
lean_inc(v_k_5829_);
lean_inc(v_K_5828_);
lean_inc(v_h_5827_);
lean_inc(v_B_5826_);
lean_inc(v_b_5825_);
lean_inc(v_a_5824_);
lean_inc(v_F_5823_);
lean_inc(v_c_5822_);
lean_inc(v_e_5821_);
lean_inc(v_E_5820_);
lean_inc(v_W_5819_);
lean_inc(v_w_5818_);
lean_inc(v_q_5817_);
lean_inc(v_Q_5816_);
lean_inc(v_d_5815_);
lean_inc(v_L_5814_);
lean_inc(v_M_5813_);
lean_inc(v_D_5812_);
lean_inc(v_Y_5811_);
lean_inc(v_u_5810_);
lean_inc(v_y_5809_);
lean_inc(v_G_5808_);
lean_dec(v_date_4150_);
v___x_5845_ = lean_box(0);
v_isShared_5846_ = v_isSharedCheck_5851_;
goto v_resetjp_5844_;
}
v_resetjp_5844_:
{
lean_object* v___x_5847_; lean_object* v___x_5849_; 
v___x_5847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5847_, 0, v_data_4152_);
if (v_isShared_5846_ == 0)
{
lean_ctor_set(v___x_5845_, 32, v___x_5847_);
v___x_5849_ = v___x_5845_;
goto v_reusejp_5848_;
}
else
{
lean_object* v_reuseFailAlloc_5850_; 
v_reuseFailAlloc_5850_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5850_, 0, v_G_5808_);
lean_ctor_set(v_reuseFailAlloc_5850_, 1, v_y_5809_);
lean_ctor_set(v_reuseFailAlloc_5850_, 2, v_u_5810_);
lean_ctor_set(v_reuseFailAlloc_5850_, 3, v_Y_5811_);
lean_ctor_set(v_reuseFailAlloc_5850_, 4, v_D_5812_);
lean_ctor_set(v_reuseFailAlloc_5850_, 5, v_M_5813_);
lean_ctor_set(v_reuseFailAlloc_5850_, 6, v_L_5814_);
lean_ctor_set(v_reuseFailAlloc_5850_, 7, v_d_5815_);
lean_ctor_set(v_reuseFailAlloc_5850_, 8, v_Q_5816_);
lean_ctor_set(v_reuseFailAlloc_5850_, 9, v_q_5817_);
lean_ctor_set(v_reuseFailAlloc_5850_, 10, v_w_5818_);
lean_ctor_set(v_reuseFailAlloc_5850_, 11, v_W_5819_);
lean_ctor_set(v_reuseFailAlloc_5850_, 12, v_E_5820_);
lean_ctor_set(v_reuseFailAlloc_5850_, 13, v_e_5821_);
lean_ctor_set(v_reuseFailAlloc_5850_, 14, v_c_5822_);
lean_ctor_set(v_reuseFailAlloc_5850_, 15, v_F_5823_);
lean_ctor_set(v_reuseFailAlloc_5850_, 16, v_a_5824_);
lean_ctor_set(v_reuseFailAlloc_5850_, 17, v_b_5825_);
lean_ctor_set(v_reuseFailAlloc_5850_, 18, v_B_5826_);
lean_ctor_set(v_reuseFailAlloc_5850_, 19, v_h_5827_);
lean_ctor_set(v_reuseFailAlloc_5850_, 20, v_K_5828_);
lean_ctor_set(v_reuseFailAlloc_5850_, 21, v_k_5829_);
lean_ctor_set(v_reuseFailAlloc_5850_, 22, v_H_5830_);
lean_ctor_set(v_reuseFailAlloc_5850_, 23, v_m_5831_);
lean_ctor_set(v_reuseFailAlloc_5850_, 24, v_s_5832_);
lean_ctor_set(v_reuseFailAlloc_5850_, 25, v_S_5833_);
lean_ctor_set(v_reuseFailAlloc_5850_, 26, v_A_5834_);
lean_ctor_set(v_reuseFailAlloc_5850_, 27, v_n_5835_);
lean_ctor_set(v_reuseFailAlloc_5850_, 28, v_N_5836_);
lean_ctor_set(v_reuseFailAlloc_5850_, 29, v_V_5837_);
lean_ctor_set(v_reuseFailAlloc_5850_, 30, v_z_5838_);
lean_ctor_set(v_reuseFailAlloc_5850_, 31, v_zabbrev_5839_);
lean_ctor_set(v_reuseFailAlloc_5850_, 32, v___x_5847_);
lean_ctor_set(v_reuseFailAlloc_5850_, 33, v_O_5840_);
lean_ctor_set(v_reuseFailAlloc_5850_, 34, v_X_5841_);
lean_ctor_set(v_reuseFailAlloc_5850_, 35, v_x_5842_);
lean_ctor_set(v_reuseFailAlloc_5850_, 36, v_Z_5843_);
v___x_5849_ = v_reuseFailAlloc_5850_;
goto v_reusejp_5848_;
}
v_reusejp_5848_:
{
return v___x_5849_;
}
}
}
}
case 32:
{
lean_object* v_G_5853_; lean_object* v_y_5854_; lean_object* v_u_5855_; lean_object* v_Y_5856_; lean_object* v_D_5857_; lean_object* v_M_5858_; lean_object* v_L_5859_; lean_object* v_d_5860_; lean_object* v_Q_5861_; lean_object* v_q_5862_; lean_object* v_w_5863_; lean_object* v_W_5864_; lean_object* v_E_5865_; lean_object* v_e_5866_; lean_object* v_c_5867_; lean_object* v_F_5868_; lean_object* v_a_5869_; lean_object* v_b_5870_; lean_object* v_B_5871_; lean_object* v_h_5872_; lean_object* v_K_5873_; lean_object* v_k_5874_; lean_object* v_H_5875_; lean_object* v_m_5876_; lean_object* v_s_5877_; lean_object* v_S_5878_; lean_object* v_A_5879_; lean_object* v_n_5880_; lean_object* v_N_5881_; lean_object* v_V_5882_; lean_object* v_z_5883_; lean_object* v_zabbrev_5884_; lean_object* v_v_5885_; lean_object* v_X_5886_; lean_object* v_x_5887_; lean_object* v_Z_5888_; lean_object* v___x_5890_; uint8_t v_isShared_5891_; uint8_t v_isSharedCheck_5896_; 
lean_dec_ref_known(v_modifier_4151_, 0);
v_G_5853_ = lean_ctor_get(v_date_4150_, 0);
v_y_5854_ = lean_ctor_get(v_date_4150_, 1);
v_u_5855_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5856_ = lean_ctor_get(v_date_4150_, 3);
v_D_5857_ = lean_ctor_get(v_date_4150_, 4);
v_M_5858_ = lean_ctor_get(v_date_4150_, 5);
v_L_5859_ = lean_ctor_get(v_date_4150_, 6);
v_d_5860_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5861_ = lean_ctor_get(v_date_4150_, 8);
v_q_5862_ = lean_ctor_get(v_date_4150_, 9);
v_w_5863_ = lean_ctor_get(v_date_4150_, 10);
v_W_5864_ = lean_ctor_get(v_date_4150_, 11);
v_E_5865_ = lean_ctor_get(v_date_4150_, 12);
v_e_5866_ = lean_ctor_get(v_date_4150_, 13);
v_c_5867_ = lean_ctor_get(v_date_4150_, 14);
v_F_5868_ = lean_ctor_get(v_date_4150_, 15);
v_a_5869_ = lean_ctor_get(v_date_4150_, 16);
v_b_5870_ = lean_ctor_get(v_date_4150_, 17);
v_B_5871_ = lean_ctor_get(v_date_4150_, 18);
v_h_5872_ = lean_ctor_get(v_date_4150_, 19);
v_K_5873_ = lean_ctor_get(v_date_4150_, 20);
v_k_5874_ = lean_ctor_get(v_date_4150_, 21);
v_H_5875_ = lean_ctor_get(v_date_4150_, 22);
v_m_5876_ = lean_ctor_get(v_date_4150_, 23);
v_s_5877_ = lean_ctor_get(v_date_4150_, 24);
v_S_5878_ = lean_ctor_get(v_date_4150_, 25);
v_A_5879_ = lean_ctor_get(v_date_4150_, 26);
v_n_5880_ = lean_ctor_get(v_date_4150_, 27);
v_N_5881_ = lean_ctor_get(v_date_4150_, 28);
v_V_5882_ = lean_ctor_get(v_date_4150_, 29);
v_z_5883_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_5884_ = lean_ctor_get(v_date_4150_, 31);
v_v_5885_ = lean_ctor_get(v_date_4150_, 32);
v_X_5886_ = lean_ctor_get(v_date_4150_, 34);
v_x_5887_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5888_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5896_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5896_ == 0)
{
lean_object* v_unused_5897_; 
v_unused_5897_ = lean_ctor_get(v_date_4150_, 33);
lean_dec(v_unused_5897_);
v___x_5890_ = v_date_4150_;
v_isShared_5891_ = v_isSharedCheck_5896_;
goto v_resetjp_5889_;
}
else
{
lean_inc(v_Z_5888_);
lean_inc(v_x_5887_);
lean_inc(v_X_5886_);
lean_inc(v_v_5885_);
lean_inc(v_zabbrev_5884_);
lean_inc(v_z_5883_);
lean_inc(v_V_5882_);
lean_inc(v_N_5881_);
lean_inc(v_n_5880_);
lean_inc(v_A_5879_);
lean_inc(v_S_5878_);
lean_inc(v_s_5877_);
lean_inc(v_m_5876_);
lean_inc(v_H_5875_);
lean_inc(v_k_5874_);
lean_inc(v_K_5873_);
lean_inc(v_h_5872_);
lean_inc(v_B_5871_);
lean_inc(v_b_5870_);
lean_inc(v_a_5869_);
lean_inc(v_F_5868_);
lean_inc(v_c_5867_);
lean_inc(v_e_5866_);
lean_inc(v_E_5865_);
lean_inc(v_W_5864_);
lean_inc(v_w_5863_);
lean_inc(v_q_5862_);
lean_inc(v_Q_5861_);
lean_inc(v_d_5860_);
lean_inc(v_L_5859_);
lean_inc(v_M_5858_);
lean_inc(v_D_5857_);
lean_inc(v_Y_5856_);
lean_inc(v_u_5855_);
lean_inc(v_y_5854_);
lean_inc(v_G_5853_);
lean_dec(v_date_4150_);
v___x_5890_ = lean_box(0);
v_isShared_5891_ = v_isSharedCheck_5896_;
goto v_resetjp_5889_;
}
v_resetjp_5889_:
{
lean_object* v___x_5892_; lean_object* v___x_5894_; 
v___x_5892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5892_, 0, v_data_4152_);
if (v_isShared_5891_ == 0)
{
lean_ctor_set(v___x_5890_, 33, v___x_5892_);
v___x_5894_ = v___x_5890_;
goto v_reusejp_5893_;
}
else
{
lean_object* v_reuseFailAlloc_5895_; 
v_reuseFailAlloc_5895_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5895_, 0, v_G_5853_);
lean_ctor_set(v_reuseFailAlloc_5895_, 1, v_y_5854_);
lean_ctor_set(v_reuseFailAlloc_5895_, 2, v_u_5855_);
lean_ctor_set(v_reuseFailAlloc_5895_, 3, v_Y_5856_);
lean_ctor_set(v_reuseFailAlloc_5895_, 4, v_D_5857_);
lean_ctor_set(v_reuseFailAlloc_5895_, 5, v_M_5858_);
lean_ctor_set(v_reuseFailAlloc_5895_, 6, v_L_5859_);
lean_ctor_set(v_reuseFailAlloc_5895_, 7, v_d_5860_);
lean_ctor_set(v_reuseFailAlloc_5895_, 8, v_Q_5861_);
lean_ctor_set(v_reuseFailAlloc_5895_, 9, v_q_5862_);
lean_ctor_set(v_reuseFailAlloc_5895_, 10, v_w_5863_);
lean_ctor_set(v_reuseFailAlloc_5895_, 11, v_W_5864_);
lean_ctor_set(v_reuseFailAlloc_5895_, 12, v_E_5865_);
lean_ctor_set(v_reuseFailAlloc_5895_, 13, v_e_5866_);
lean_ctor_set(v_reuseFailAlloc_5895_, 14, v_c_5867_);
lean_ctor_set(v_reuseFailAlloc_5895_, 15, v_F_5868_);
lean_ctor_set(v_reuseFailAlloc_5895_, 16, v_a_5869_);
lean_ctor_set(v_reuseFailAlloc_5895_, 17, v_b_5870_);
lean_ctor_set(v_reuseFailAlloc_5895_, 18, v_B_5871_);
lean_ctor_set(v_reuseFailAlloc_5895_, 19, v_h_5872_);
lean_ctor_set(v_reuseFailAlloc_5895_, 20, v_K_5873_);
lean_ctor_set(v_reuseFailAlloc_5895_, 21, v_k_5874_);
lean_ctor_set(v_reuseFailAlloc_5895_, 22, v_H_5875_);
lean_ctor_set(v_reuseFailAlloc_5895_, 23, v_m_5876_);
lean_ctor_set(v_reuseFailAlloc_5895_, 24, v_s_5877_);
lean_ctor_set(v_reuseFailAlloc_5895_, 25, v_S_5878_);
lean_ctor_set(v_reuseFailAlloc_5895_, 26, v_A_5879_);
lean_ctor_set(v_reuseFailAlloc_5895_, 27, v_n_5880_);
lean_ctor_set(v_reuseFailAlloc_5895_, 28, v_N_5881_);
lean_ctor_set(v_reuseFailAlloc_5895_, 29, v_V_5882_);
lean_ctor_set(v_reuseFailAlloc_5895_, 30, v_z_5883_);
lean_ctor_set(v_reuseFailAlloc_5895_, 31, v_zabbrev_5884_);
lean_ctor_set(v_reuseFailAlloc_5895_, 32, v_v_5885_);
lean_ctor_set(v_reuseFailAlloc_5895_, 33, v___x_5892_);
lean_ctor_set(v_reuseFailAlloc_5895_, 34, v_X_5886_);
lean_ctor_set(v_reuseFailAlloc_5895_, 35, v_x_5887_);
lean_ctor_set(v_reuseFailAlloc_5895_, 36, v_Z_5888_);
v___x_5894_ = v_reuseFailAlloc_5895_;
goto v_reusejp_5893_;
}
v_reusejp_5893_:
{
return v___x_5894_;
}
}
}
case 33:
{
lean_object* v_G_5898_; lean_object* v_y_5899_; lean_object* v_u_5900_; lean_object* v_Y_5901_; lean_object* v_D_5902_; lean_object* v_M_5903_; lean_object* v_L_5904_; lean_object* v_d_5905_; lean_object* v_Q_5906_; lean_object* v_q_5907_; lean_object* v_w_5908_; lean_object* v_W_5909_; lean_object* v_E_5910_; lean_object* v_e_5911_; lean_object* v_c_5912_; lean_object* v_F_5913_; lean_object* v_a_5914_; lean_object* v_b_5915_; lean_object* v_B_5916_; lean_object* v_h_5917_; lean_object* v_K_5918_; lean_object* v_k_5919_; lean_object* v_H_5920_; lean_object* v_m_5921_; lean_object* v_s_5922_; lean_object* v_S_5923_; lean_object* v_A_5924_; lean_object* v_n_5925_; lean_object* v_N_5926_; lean_object* v_V_5927_; lean_object* v_z_5928_; lean_object* v_zabbrev_5929_; lean_object* v_v_5930_; lean_object* v_O_5931_; lean_object* v_x_5932_; lean_object* v_Z_5933_; lean_object* v___x_5935_; uint8_t v_isShared_5936_; uint8_t v_isSharedCheck_5941_; 
lean_dec_ref_known(v_modifier_4151_, 0);
v_G_5898_ = lean_ctor_get(v_date_4150_, 0);
v_y_5899_ = lean_ctor_get(v_date_4150_, 1);
v_u_5900_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5901_ = lean_ctor_get(v_date_4150_, 3);
v_D_5902_ = lean_ctor_get(v_date_4150_, 4);
v_M_5903_ = lean_ctor_get(v_date_4150_, 5);
v_L_5904_ = lean_ctor_get(v_date_4150_, 6);
v_d_5905_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5906_ = lean_ctor_get(v_date_4150_, 8);
v_q_5907_ = lean_ctor_get(v_date_4150_, 9);
v_w_5908_ = lean_ctor_get(v_date_4150_, 10);
v_W_5909_ = lean_ctor_get(v_date_4150_, 11);
v_E_5910_ = lean_ctor_get(v_date_4150_, 12);
v_e_5911_ = lean_ctor_get(v_date_4150_, 13);
v_c_5912_ = lean_ctor_get(v_date_4150_, 14);
v_F_5913_ = lean_ctor_get(v_date_4150_, 15);
v_a_5914_ = lean_ctor_get(v_date_4150_, 16);
v_b_5915_ = lean_ctor_get(v_date_4150_, 17);
v_B_5916_ = lean_ctor_get(v_date_4150_, 18);
v_h_5917_ = lean_ctor_get(v_date_4150_, 19);
v_K_5918_ = lean_ctor_get(v_date_4150_, 20);
v_k_5919_ = lean_ctor_get(v_date_4150_, 21);
v_H_5920_ = lean_ctor_get(v_date_4150_, 22);
v_m_5921_ = lean_ctor_get(v_date_4150_, 23);
v_s_5922_ = lean_ctor_get(v_date_4150_, 24);
v_S_5923_ = lean_ctor_get(v_date_4150_, 25);
v_A_5924_ = lean_ctor_get(v_date_4150_, 26);
v_n_5925_ = lean_ctor_get(v_date_4150_, 27);
v_N_5926_ = lean_ctor_get(v_date_4150_, 28);
v_V_5927_ = lean_ctor_get(v_date_4150_, 29);
v_z_5928_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_5929_ = lean_ctor_get(v_date_4150_, 31);
v_v_5930_ = lean_ctor_get(v_date_4150_, 32);
v_O_5931_ = lean_ctor_get(v_date_4150_, 33);
v_x_5932_ = lean_ctor_get(v_date_4150_, 35);
v_Z_5933_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5941_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5941_ == 0)
{
lean_object* v_unused_5942_; 
v_unused_5942_ = lean_ctor_get(v_date_4150_, 34);
lean_dec(v_unused_5942_);
v___x_5935_ = v_date_4150_;
v_isShared_5936_ = v_isSharedCheck_5941_;
goto v_resetjp_5934_;
}
else
{
lean_inc(v_Z_5933_);
lean_inc(v_x_5932_);
lean_inc(v_O_5931_);
lean_inc(v_v_5930_);
lean_inc(v_zabbrev_5929_);
lean_inc(v_z_5928_);
lean_inc(v_V_5927_);
lean_inc(v_N_5926_);
lean_inc(v_n_5925_);
lean_inc(v_A_5924_);
lean_inc(v_S_5923_);
lean_inc(v_s_5922_);
lean_inc(v_m_5921_);
lean_inc(v_H_5920_);
lean_inc(v_k_5919_);
lean_inc(v_K_5918_);
lean_inc(v_h_5917_);
lean_inc(v_B_5916_);
lean_inc(v_b_5915_);
lean_inc(v_a_5914_);
lean_inc(v_F_5913_);
lean_inc(v_c_5912_);
lean_inc(v_e_5911_);
lean_inc(v_E_5910_);
lean_inc(v_W_5909_);
lean_inc(v_w_5908_);
lean_inc(v_q_5907_);
lean_inc(v_Q_5906_);
lean_inc(v_d_5905_);
lean_inc(v_L_5904_);
lean_inc(v_M_5903_);
lean_inc(v_D_5902_);
lean_inc(v_Y_5901_);
lean_inc(v_u_5900_);
lean_inc(v_y_5899_);
lean_inc(v_G_5898_);
lean_dec(v_date_4150_);
v___x_5935_ = lean_box(0);
v_isShared_5936_ = v_isSharedCheck_5941_;
goto v_resetjp_5934_;
}
v_resetjp_5934_:
{
lean_object* v___x_5937_; lean_object* v___x_5939_; 
v___x_5937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5937_, 0, v_data_4152_);
if (v_isShared_5936_ == 0)
{
lean_ctor_set(v___x_5935_, 34, v___x_5937_);
v___x_5939_ = v___x_5935_;
goto v_reusejp_5938_;
}
else
{
lean_object* v_reuseFailAlloc_5940_; 
v_reuseFailAlloc_5940_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5940_, 0, v_G_5898_);
lean_ctor_set(v_reuseFailAlloc_5940_, 1, v_y_5899_);
lean_ctor_set(v_reuseFailAlloc_5940_, 2, v_u_5900_);
lean_ctor_set(v_reuseFailAlloc_5940_, 3, v_Y_5901_);
lean_ctor_set(v_reuseFailAlloc_5940_, 4, v_D_5902_);
lean_ctor_set(v_reuseFailAlloc_5940_, 5, v_M_5903_);
lean_ctor_set(v_reuseFailAlloc_5940_, 6, v_L_5904_);
lean_ctor_set(v_reuseFailAlloc_5940_, 7, v_d_5905_);
lean_ctor_set(v_reuseFailAlloc_5940_, 8, v_Q_5906_);
lean_ctor_set(v_reuseFailAlloc_5940_, 9, v_q_5907_);
lean_ctor_set(v_reuseFailAlloc_5940_, 10, v_w_5908_);
lean_ctor_set(v_reuseFailAlloc_5940_, 11, v_W_5909_);
lean_ctor_set(v_reuseFailAlloc_5940_, 12, v_E_5910_);
lean_ctor_set(v_reuseFailAlloc_5940_, 13, v_e_5911_);
lean_ctor_set(v_reuseFailAlloc_5940_, 14, v_c_5912_);
lean_ctor_set(v_reuseFailAlloc_5940_, 15, v_F_5913_);
lean_ctor_set(v_reuseFailAlloc_5940_, 16, v_a_5914_);
lean_ctor_set(v_reuseFailAlloc_5940_, 17, v_b_5915_);
lean_ctor_set(v_reuseFailAlloc_5940_, 18, v_B_5916_);
lean_ctor_set(v_reuseFailAlloc_5940_, 19, v_h_5917_);
lean_ctor_set(v_reuseFailAlloc_5940_, 20, v_K_5918_);
lean_ctor_set(v_reuseFailAlloc_5940_, 21, v_k_5919_);
lean_ctor_set(v_reuseFailAlloc_5940_, 22, v_H_5920_);
lean_ctor_set(v_reuseFailAlloc_5940_, 23, v_m_5921_);
lean_ctor_set(v_reuseFailAlloc_5940_, 24, v_s_5922_);
lean_ctor_set(v_reuseFailAlloc_5940_, 25, v_S_5923_);
lean_ctor_set(v_reuseFailAlloc_5940_, 26, v_A_5924_);
lean_ctor_set(v_reuseFailAlloc_5940_, 27, v_n_5925_);
lean_ctor_set(v_reuseFailAlloc_5940_, 28, v_N_5926_);
lean_ctor_set(v_reuseFailAlloc_5940_, 29, v_V_5927_);
lean_ctor_set(v_reuseFailAlloc_5940_, 30, v_z_5928_);
lean_ctor_set(v_reuseFailAlloc_5940_, 31, v_zabbrev_5929_);
lean_ctor_set(v_reuseFailAlloc_5940_, 32, v_v_5930_);
lean_ctor_set(v_reuseFailAlloc_5940_, 33, v_O_5931_);
lean_ctor_set(v_reuseFailAlloc_5940_, 34, v___x_5937_);
lean_ctor_set(v_reuseFailAlloc_5940_, 35, v_x_5932_);
lean_ctor_set(v_reuseFailAlloc_5940_, 36, v_Z_5933_);
v___x_5939_ = v_reuseFailAlloc_5940_;
goto v_reusejp_5938_;
}
v_reusejp_5938_:
{
return v___x_5939_;
}
}
}
case 34:
{
lean_object* v_G_5943_; lean_object* v_y_5944_; lean_object* v_u_5945_; lean_object* v_Y_5946_; lean_object* v_D_5947_; lean_object* v_M_5948_; lean_object* v_L_5949_; lean_object* v_d_5950_; lean_object* v_Q_5951_; lean_object* v_q_5952_; lean_object* v_w_5953_; lean_object* v_W_5954_; lean_object* v_E_5955_; lean_object* v_e_5956_; lean_object* v_c_5957_; lean_object* v_F_5958_; lean_object* v_a_5959_; lean_object* v_b_5960_; lean_object* v_B_5961_; lean_object* v_h_5962_; lean_object* v_K_5963_; lean_object* v_k_5964_; lean_object* v_H_5965_; lean_object* v_m_5966_; lean_object* v_s_5967_; lean_object* v_S_5968_; lean_object* v_A_5969_; lean_object* v_n_5970_; lean_object* v_N_5971_; lean_object* v_V_5972_; lean_object* v_z_5973_; lean_object* v_zabbrev_5974_; lean_object* v_v_5975_; lean_object* v_O_5976_; lean_object* v_X_5977_; lean_object* v_Z_5978_; lean_object* v___x_5980_; uint8_t v_isShared_5981_; uint8_t v_isSharedCheck_5986_; 
lean_dec_ref_known(v_modifier_4151_, 0);
v_G_5943_ = lean_ctor_get(v_date_4150_, 0);
v_y_5944_ = lean_ctor_get(v_date_4150_, 1);
v_u_5945_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5946_ = lean_ctor_get(v_date_4150_, 3);
v_D_5947_ = lean_ctor_get(v_date_4150_, 4);
v_M_5948_ = lean_ctor_get(v_date_4150_, 5);
v_L_5949_ = lean_ctor_get(v_date_4150_, 6);
v_d_5950_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5951_ = lean_ctor_get(v_date_4150_, 8);
v_q_5952_ = lean_ctor_get(v_date_4150_, 9);
v_w_5953_ = lean_ctor_get(v_date_4150_, 10);
v_W_5954_ = lean_ctor_get(v_date_4150_, 11);
v_E_5955_ = lean_ctor_get(v_date_4150_, 12);
v_e_5956_ = lean_ctor_get(v_date_4150_, 13);
v_c_5957_ = lean_ctor_get(v_date_4150_, 14);
v_F_5958_ = lean_ctor_get(v_date_4150_, 15);
v_a_5959_ = lean_ctor_get(v_date_4150_, 16);
v_b_5960_ = lean_ctor_get(v_date_4150_, 17);
v_B_5961_ = lean_ctor_get(v_date_4150_, 18);
v_h_5962_ = lean_ctor_get(v_date_4150_, 19);
v_K_5963_ = lean_ctor_get(v_date_4150_, 20);
v_k_5964_ = lean_ctor_get(v_date_4150_, 21);
v_H_5965_ = lean_ctor_get(v_date_4150_, 22);
v_m_5966_ = lean_ctor_get(v_date_4150_, 23);
v_s_5967_ = lean_ctor_get(v_date_4150_, 24);
v_S_5968_ = lean_ctor_get(v_date_4150_, 25);
v_A_5969_ = lean_ctor_get(v_date_4150_, 26);
v_n_5970_ = lean_ctor_get(v_date_4150_, 27);
v_N_5971_ = lean_ctor_get(v_date_4150_, 28);
v_V_5972_ = lean_ctor_get(v_date_4150_, 29);
v_z_5973_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_5974_ = lean_ctor_get(v_date_4150_, 31);
v_v_5975_ = lean_ctor_get(v_date_4150_, 32);
v_O_5976_ = lean_ctor_get(v_date_4150_, 33);
v_X_5977_ = lean_ctor_get(v_date_4150_, 34);
v_Z_5978_ = lean_ctor_get(v_date_4150_, 36);
v_isSharedCheck_5986_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_5986_ == 0)
{
lean_object* v_unused_5987_; 
v_unused_5987_ = lean_ctor_get(v_date_4150_, 35);
lean_dec(v_unused_5987_);
v___x_5980_ = v_date_4150_;
v_isShared_5981_ = v_isSharedCheck_5986_;
goto v_resetjp_5979_;
}
else
{
lean_inc(v_Z_5978_);
lean_inc(v_X_5977_);
lean_inc(v_O_5976_);
lean_inc(v_v_5975_);
lean_inc(v_zabbrev_5974_);
lean_inc(v_z_5973_);
lean_inc(v_V_5972_);
lean_inc(v_N_5971_);
lean_inc(v_n_5970_);
lean_inc(v_A_5969_);
lean_inc(v_S_5968_);
lean_inc(v_s_5967_);
lean_inc(v_m_5966_);
lean_inc(v_H_5965_);
lean_inc(v_k_5964_);
lean_inc(v_K_5963_);
lean_inc(v_h_5962_);
lean_inc(v_B_5961_);
lean_inc(v_b_5960_);
lean_inc(v_a_5959_);
lean_inc(v_F_5958_);
lean_inc(v_c_5957_);
lean_inc(v_e_5956_);
lean_inc(v_E_5955_);
lean_inc(v_W_5954_);
lean_inc(v_w_5953_);
lean_inc(v_q_5952_);
lean_inc(v_Q_5951_);
lean_inc(v_d_5950_);
lean_inc(v_L_5949_);
lean_inc(v_M_5948_);
lean_inc(v_D_5947_);
lean_inc(v_Y_5946_);
lean_inc(v_u_5945_);
lean_inc(v_y_5944_);
lean_inc(v_G_5943_);
lean_dec(v_date_4150_);
v___x_5980_ = lean_box(0);
v_isShared_5981_ = v_isSharedCheck_5986_;
goto v_resetjp_5979_;
}
v_resetjp_5979_:
{
lean_object* v___x_5982_; lean_object* v___x_5984_; 
v___x_5982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5982_, 0, v_data_4152_);
if (v_isShared_5981_ == 0)
{
lean_ctor_set(v___x_5980_, 35, v___x_5982_);
v___x_5984_ = v___x_5980_;
goto v_reusejp_5983_;
}
else
{
lean_object* v_reuseFailAlloc_5985_; 
v_reuseFailAlloc_5985_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5985_, 0, v_G_5943_);
lean_ctor_set(v_reuseFailAlloc_5985_, 1, v_y_5944_);
lean_ctor_set(v_reuseFailAlloc_5985_, 2, v_u_5945_);
lean_ctor_set(v_reuseFailAlloc_5985_, 3, v_Y_5946_);
lean_ctor_set(v_reuseFailAlloc_5985_, 4, v_D_5947_);
lean_ctor_set(v_reuseFailAlloc_5985_, 5, v_M_5948_);
lean_ctor_set(v_reuseFailAlloc_5985_, 6, v_L_5949_);
lean_ctor_set(v_reuseFailAlloc_5985_, 7, v_d_5950_);
lean_ctor_set(v_reuseFailAlloc_5985_, 8, v_Q_5951_);
lean_ctor_set(v_reuseFailAlloc_5985_, 9, v_q_5952_);
lean_ctor_set(v_reuseFailAlloc_5985_, 10, v_w_5953_);
lean_ctor_set(v_reuseFailAlloc_5985_, 11, v_W_5954_);
lean_ctor_set(v_reuseFailAlloc_5985_, 12, v_E_5955_);
lean_ctor_set(v_reuseFailAlloc_5985_, 13, v_e_5956_);
lean_ctor_set(v_reuseFailAlloc_5985_, 14, v_c_5957_);
lean_ctor_set(v_reuseFailAlloc_5985_, 15, v_F_5958_);
lean_ctor_set(v_reuseFailAlloc_5985_, 16, v_a_5959_);
lean_ctor_set(v_reuseFailAlloc_5985_, 17, v_b_5960_);
lean_ctor_set(v_reuseFailAlloc_5985_, 18, v_B_5961_);
lean_ctor_set(v_reuseFailAlloc_5985_, 19, v_h_5962_);
lean_ctor_set(v_reuseFailAlloc_5985_, 20, v_K_5963_);
lean_ctor_set(v_reuseFailAlloc_5985_, 21, v_k_5964_);
lean_ctor_set(v_reuseFailAlloc_5985_, 22, v_H_5965_);
lean_ctor_set(v_reuseFailAlloc_5985_, 23, v_m_5966_);
lean_ctor_set(v_reuseFailAlloc_5985_, 24, v_s_5967_);
lean_ctor_set(v_reuseFailAlloc_5985_, 25, v_S_5968_);
lean_ctor_set(v_reuseFailAlloc_5985_, 26, v_A_5969_);
lean_ctor_set(v_reuseFailAlloc_5985_, 27, v_n_5970_);
lean_ctor_set(v_reuseFailAlloc_5985_, 28, v_N_5971_);
lean_ctor_set(v_reuseFailAlloc_5985_, 29, v_V_5972_);
lean_ctor_set(v_reuseFailAlloc_5985_, 30, v_z_5973_);
lean_ctor_set(v_reuseFailAlloc_5985_, 31, v_zabbrev_5974_);
lean_ctor_set(v_reuseFailAlloc_5985_, 32, v_v_5975_);
lean_ctor_set(v_reuseFailAlloc_5985_, 33, v_O_5976_);
lean_ctor_set(v_reuseFailAlloc_5985_, 34, v_X_5977_);
lean_ctor_set(v_reuseFailAlloc_5985_, 35, v___x_5982_);
lean_ctor_set(v_reuseFailAlloc_5985_, 36, v_Z_5978_);
v___x_5984_ = v_reuseFailAlloc_5985_;
goto v_reusejp_5983_;
}
v_reusejp_5983_:
{
return v___x_5984_;
}
}
}
default: 
{
lean_object* v_G_5988_; lean_object* v_y_5989_; lean_object* v_u_5990_; lean_object* v_Y_5991_; lean_object* v_D_5992_; lean_object* v_M_5993_; lean_object* v_L_5994_; lean_object* v_d_5995_; lean_object* v_Q_5996_; lean_object* v_q_5997_; lean_object* v_w_5998_; lean_object* v_W_5999_; lean_object* v_E_6000_; lean_object* v_e_6001_; lean_object* v_c_6002_; lean_object* v_F_6003_; lean_object* v_a_6004_; lean_object* v_b_6005_; lean_object* v_B_6006_; lean_object* v_h_6007_; lean_object* v_K_6008_; lean_object* v_k_6009_; lean_object* v_H_6010_; lean_object* v_m_6011_; lean_object* v_s_6012_; lean_object* v_S_6013_; lean_object* v_A_6014_; lean_object* v_n_6015_; lean_object* v_N_6016_; lean_object* v_V_6017_; lean_object* v_z_6018_; lean_object* v_zabbrev_6019_; lean_object* v_v_6020_; lean_object* v_O_6021_; lean_object* v_X_6022_; lean_object* v_x_6023_; lean_object* v___x_6025_; uint8_t v_isShared_6026_; uint8_t v_isSharedCheck_6031_; 
lean_dec_ref_known(v_modifier_4151_, 0);
v_G_5988_ = lean_ctor_get(v_date_4150_, 0);
v_y_5989_ = lean_ctor_get(v_date_4150_, 1);
v_u_5990_ = lean_ctor_get(v_date_4150_, 2);
v_Y_5991_ = lean_ctor_get(v_date_4150_, 3);
v_D_5992_ = lean_ctor_get(v_date_4150_, 4);
v_M_5993_ = lean_ctor_get(v_date_4150_, 5);
v_L_5994_ = lean_ctor_get(v_date_4150_, 6);
v_d_5995_ = lean_ctor_get(v_date_4150_, 7);
v_Q_5996_ = lean_ctor_get(v_date_4150_, 8);
v_q_5997_ = lean_ctor_get(v_date_4150_, 9);
v_w_5998_ = lean_ctor_get(v_date_4150_, 10);
v_W_5999_ = lean_ctor_get(v_date_4150_, 11);
v_E_6000_ = lean_ctor_get(v_date_4150_, 12);
v_e_6001_ = lean_ctor_get(v_date_4150_, 13);
v_c_6002_ = lean_ctor_get(v_date_4150_, 14);
v_F_6003_ = lean_ctor_get(v_date_4150_, 15);
v_a_6004_ = lean_ctor_get(v_date_4150_, 16);
v_b_6005_ = lean_ctor_get(v_date_4150_, 17);
v_B_6006_ = lean_ctor_get(v_date_4150_, 18);
v_h_6007_ = lean_ctor_get(v_date_4150_, 19);
v_K_6008_ = lean_ctor_get(v_date_4150_, 20);
v_k_6009_ = lean_ctor_get(v_date_4150_, 21);
v_H_6010_ = lean_ctor_get(v_date_4150_, 22);
v_m_6011_ = lean_ctor_get(v_date_4150_, 23);
v_s_6012_ = lean_ctor_get(v_date_4150_, 24);
v_S_6013_ = lean_ctor_get(v_date_4150_, 25);
v_A_6014_ = lean_ctor_get(v_date_4150_, 26);
v_n_6015_ = lean_ctor_get(v_date_4150_, 27);
v_N_6016_ = lean_ctor_get(v_date_4150_, 28);
v_V_6017_ = lean_ctor_get(v_date_4150_, 29);
v_z_6018_ = lean_ctor_get(v_date_4150_, 30);
v_zabbrev_6019_ = lean_ctor_get(v_date_4150_, 31);
v_v_6020_ = lean_ctor_get(v_date_4150_, 32);
v_O_6021_ = lean_ctor_get(v_date_4150_, 33);
v_X_6022_ = lean_ctor_get(v_date_4150_, 34);
v_x_6023_ = lean_ctor_get(v_date_4150_, 35);
v_isSharedCheck_6031_ = !lean_is_exclusive(v_date_4150_);
if (v_isSharedCheck_6031_ == 0)
{
lean_object* v_unused_6032_; 
v_unused_6032_ = lean_ctor_get(v_date_4150_, 36);
lean_dec(v_unused_6032_);
v___x_6025_ = v_date_4150_;
v_isShared_6026_ = v_isSharedCheck_6031_;
goto v_resetjp_6024_;
}
else
{
lean_inc(v_x_6023_);
lean_inc(v_X_6022_);
lean_inc(v_O_6021_);
lean_inc(v_v_6020_);
lean_inc(v_zabbrev_6019_);
lean_inc(v_z_6018_);
lean_inc(v_V_6017_);
lean_inc(v_N_6016_);
lean_inc(v_n_6015_);
lean_inc(v_A_6014_);
lean_inc(v_S_6013_);
lean_inc(v_s_6012_);
lean_inc(v_m_6011_);
lean_inc(v_H_6010_);
lean_inc(v_k_6009_);
lean_inc(v_K_6008_);
lean_inc(v_h_6007_);
lean_inc(v_B_6006_);
lean_inc(v_b_6005_);
lean_inc(v_a_6004_);
lean_inc(v_F_6003_);
lean_inc(v_c_6002_);
lean_inc(v_e_6001_);
lean_inc(v_E_6000_);
lean_inc(v_W_5999_);
lean_inc(v_w_5998_);
lean_inc(v_q_5997_);
lean_inc(v_Q_5996_);
lean_inc(v_d_5995_);
lean_inc(v_L_5994_);
lean_inc(v_M_5993_);
lean_inc(v_D_5992_);
lean_inc(v_Y_5991_);
lean_inc(v_u_5990_);
lean_inc(v_y_5989_);
lean_inc(v_G_5988_);
lean_dec(v_date_4150_);
v___x_6025_ = lean_box(0);
v_isShared_6026_ = v_isSharedCheck_6031_;
goto v_resetjp_6024_;
}
v_resetjp_6024_:
{
lean_object* v___x_6027_; lean_object* v___x_6029_; 
v___x_6027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6027_, 0, v_data_4152_);
if (v_isShared_6026_ == 0)
{
lean_ctor_set(v___x_6025_, 36, v___x_6027_);
v___x_6029_ = v___x_6025_;
goto v_reusejp_6028_;
}
else
{
lean_object* v_reuseFailAlloc_6030_; 
v_reuseFailAlloc_6030_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6030_, 0, v_G_5988_);
lean_ctor_set(v_reuseFailAlloc_6030_, 1, v_y_5989_);
lean_ctor_set(v_reuseFailAlloc_6030_, 2, v_u_5990_);
lean_ctor_set(v_reuseFailAlloc_6030_, 3, v_Y_5991_);
lean_ctor_set(v_reuseFailAlloc_6030_, 4, v_D_5992_);
lean_ctor_set(v_reuseFailAlloc_6030_, 5, v_M_5993_);
lean_ctor_set(v_reuseFailAlloc_6030_, 6, v_L_5994_);
lean_ctor_set(v_reuseFailAlloc_6030_, 7, v_d_5995_);
lean_ctor_set(v_reuseFailAlloc_6030_, 8, v_Q_5996_);
lean_ctor_set(v_reuseFailAlloc_6030_, 9, v_q_5997_);
lean_ctor_set(v_reuseFailAlloc_6030_, 10, v_w_5998_);
lean_ctor_set(v_reuseFailAlloc_6030_, 11, v_W_5999_);
lean_ctor_set(v_reuseFailAlloc_6030_, 12, v_E_6000_);
lean_ctor_set(v_reuseFailAlloc_6030_, 13, v_e_6001_);
lean_ctor_set(v_reuseFailAlloc_6030_, 14, v_c_6002_);
lean_ctor_set(v_reuseFailAlloc_6030_, 15, v_F_6003_);
lean_ctor_set(v_reuseFailAlloc_6030_, 16, v_a_6004_);
lean_ctor_set(v_reuseFailAlloc_6030_, 17, v_b_6005_);
lean_ctor_set(v_reuseFailAlloc_6030_, 18, v_B_6006_);
lean_ctor_set(v_reuseFailAlloc_6030_, 19, v_h_6007_);
lean_ctor_set(v_reuseFailAlloc_6030_, 20, v_K_6008_);
lean_ctor_set(v_reuseFailAlloc_6030_, 21, v_k_6009_);
lean_ctor_set(v_reuseFailAlloc_6030_, 22, v_H_6010_);
lean_ctor_set(v_reuseFailAlloc_6030_, 23, v_m_6011_);
lean_ctor_set(v_reuseFailAlloc_6030_, 24, v_s_6012_);
lean_ctor_set(v_reuseFailAlloc_6030_, 25, v_S_6013_);
lean_ctor_set(v_reuseFailAlloc_6030_, 26, v_A_6014_);
lean_ctor_set(v_reuseFailAlloc_6030_, 27, v_n_6015_);
lean_ctor_set(v_reuseFailAlloc_6030_, 28, v_N_6016_);
lean_ctor_set(v_reuseFailAlloc_6030_, 29, v_V_6017_);
lean_ctor_set(v_reuseFailAlloc_6030_, 30, v_z_6018_);
lean_ctor_set(v_reuseFailAlloc_6030_, 31, v_zabbrev_6019_);
lean_ctor_set(v_reuseFailAlloc_6030_, 32, v_v_6020_);
lean_ctor_set(v_reuseFailAlloc_6030_, 33, v_O_6021_);
lean_ctor_set(v_reuseFailAlloc_6030_, 34, v_X_6022_);
lean_ctor_set(v_reuseFailAlloc_6030_, 35, v_x_6023_);
lean_ctor_set(v_reuseFailAlloc_6030_, 36, v___x_6027_);
v___x_6029_ = v_reuseFailAlloc_6030_;
goto v_reusejp_6028_;
}
v_reusejp_6028_:
{
return v___x_6029_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(lean_object* v_year_6033_, uint8_t v_x_6034_){
_start:
{
if (v_x_6034_ == 0)
{
lean_object* v___x_6035_; lean_object* v___x_6036_; 
v___x_6035_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6036_ = lean_int_sub(v___x_6035_, v_year_6033_);
return v___x_6036_;
}
else
{
lean_inc(v_year_6033_);
return v_year_6033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra___boxed(lean_object* v_year_6037_, lean_object* v_x_6038_){
_start:
{
uint8_t v_x_36__boxed_6039_; lean_object* v_res_6040_; 
v_x_36__boxed_6039_ = lean_unbox(v_x_6038_);
v_res_6040_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_year_6037_, v_x_36__boxed_6039_);
lean_dec(v_year_6037_);
return v_res_6040_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(uint8_t v_x_6041_){
_start:
{
switch(v_x_6041_)
{
case 1:
{
uint8_t v___x_6042_; 
v___x_6042_ = 1;
return v___x_6042_;
}
case 2:
{
uint8_t v___x_6043_; 
v___x_6043_ = 1;
return v___x_6043_;
}
default: 
{
uint8_t v___x_6044_; 
v___x_6044_ = 0;
return v___x_6044_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod___boxed(lean_object* v_x_6045_){
_start:
{
uint8_t v_x_28__boxed_6046_; uint8_t v_res_6047_; lean_object* v_r_6048_; 
v_x_28__boxed_6046_ = lean_unbox(v_x_6045_);
v_res_6047_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v_x_28__boxed_6046_);
v_r_6048_ = lean_box(v_res_6047_);
return v_r_6048_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(lean_object* v_hour_6049_, uint8_t v_x_6050_){
_start:
{
switch(v_x_6050_)
{
case 1:
{
lean_object* v___x_6051_; uint8_t v___x_6052_; 
v___x_6051_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__0, &l_Std_Time_classifyExtendedDayPeriod___closed__0_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__0);
v___x_6052_ = lean_int_dec_lt(v_hour_6049_, v___x_6051_);
if (v___x_6052_ == 0)
{
uint8_t v___x_6053_; 
v___x_6053_ = 1;
return v___x_6053_;
}
else
{
uint8_t v___x_6054_; 
v___x_6054_ = 0;
return v___x_6054_;
}
}
case 3:
{
uint8_t v___x_6055_; 
v___x_6055_ = 1;
return v___x_6055_;
}
case 4:
{
uint8_t v___x_6056_; 
v___x_6056_ = 1;
return v___x_6056_;
}
case 5:
{
uint8_t v___x_6057_; 
v___x_6057_ = 1;
return v___x_6057_;
}
default: 
{
uint8_t v___x_6058_; 
v___x_6058_ = 0;
return v___x_6058_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod___boxed(lean_object* v_hour_6059_, lean_object* v_x_6060_){
_start:
{
uint8_t v_x_56__boxed_6061_; uint8_t v_res_6062_; lean_object* v_r_6063_; 
v_x_56__boxed_6061_ = lean_unbox(v_x_6060_);
v_res_6062_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v_hour_6059_, v_x_56__boxed_6061_);
lean_dec(v_hour_6059_);
v_r_6063_ = lean_box(v_res_6062_);
return v_r_6063_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_offsetOfZoneId_x3f___lam__0(lean_object* v___x_6064_, lean_object* v___y_6065_){
_start:
{
lean_object* v_pos_6067_; lean_object* v___x_6087_; 
lean_inc_ref(v___y_6065_);
v___x_6087_ = l_Std_Internal_Parsec_String_pstring(v___x_6064_, v___y_6065_);
if (lean_obj_tag(v___x_6087_) == 0)
{
lean_object* v_pos_6088_; 
lean_dec_ref(v___y_6065_);
v_pos_6088_ = lean_ctor_get(v___x_6087_, 0);
lean_inc(v_pos_6088_);
lean_dec_ref_known(v___x_6087_, 2);
v_pos_6067_ = v_pos_6088_;
goto v___jp_6066_;
}
else
{
lean_object* v_pos_6089_; lean_object* v_err_6090_; lean_object* v___x_6092_; uint8_t v_isShared_6093_; uint8_t v_isSharedCheck_6100_; 
v_pos_6089_ = lean_ctor_get(v___x_6087_, 0);
v_err_6090_ = lean_ctor_get(v___x_6087_, 1);
v_isSharedCheck_6100_ = !lean_is_exclusive(v___x_6087_);
if (v_isSharedCheck_6100_ == 0)
{
v___x_6092_ = v___x_6087_;
v_isShared_6093_ = v_isSharedCheck_6100_;
goto v_resetjp_6091_;
}
else
{
lean_inc(v_err_6090_);
lean_inc(v_pos_6089_);
lean_dec(v___x_6087_);
v___x_6092_ = lean_box(0);
v_isShared_6093_ = v_isSharedCheck_6100_;
goto v_resetjp_6091_;
}
v_resetjp_6091_:
{
lean_object* v_snd_6094_; lean_object* v_snd_6095_; uint8_t v_decide_6096_; 
v_snd_6094_ = lean_ctor_get(v___y_6065_, 1);
lean_inc(v_snd_6094_);
lean_dec_ref(v___y_6065_);
v_snd_6095_ = lean_ctor_get(v_pos_6089_, 1);
v_decide_6096_ = lean_nat_dec_eq(v_snd_6094_, v_snd_6095_);
lean_dec(v_snd_6094_);
if (v_decide_6096_ == 0)
{
lean_object* v___x_6098_; 
if (v_isShared_6093_ == 0)
{
v___x_6098_ = v___x_6092_;
goto v_reusejp_6097_;
}
else
{
lean_object* v_reuseFailAlloc_6099_; 
v_reuseFailAlloc_6099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6099_, 0, v_pos_6089_);
lean_ctor_set(v_reuseFailAlloc_6099_, 1, v_err_6090_);
v___x_6098_ = v_reuseFailAlloc_6099_;
goto v_reusejp_6097_;
}
v_reusejp_6097_:
{
return v___x_6098_;
}
}
else
{
lean_del_object(v___x_6092_);
lean_dec(v_err_6090_);
v_pos_6067_ = v_pos_6089_;
goto v___jp_6066_;
}
}
}
v___jp_6066_:
{
uint8_t v___x_6068_; uint8_t v___x_6069_; uint8_t v___x_6070_; lean_object* v___x_6071_; 
v___x_6068_ = 0;
v___x_6069_ = 2;
v___x_6070_ = 1;
v___x_6071_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_6068_, v___x_6069_, v___x_6070_, v_pos_6067_);
if (lean_obj_tag(v___x_6071_) == 0)
{
lean_object* v_pos_6072_; lean_object* v_fst_6073_; lean_object* v_snd_6074_; lean_object* v___x_6075_; uint8_t v_decide_6076_; 
v_pos_6072_ = lean_ctor_get(v___x_6071_, 0);
v_fst_6073_ = lean_ctor_get(v_pos_6072_, 0);
v_snd_6074_ = lean_ctor_get(v_pos_6072_, 1);
v___x_6075_ = lean_string_utf8_byte_size(v_fst_6073_);
v_decide_6076_ = lean_nat_dec_eq(v_snd_6074_, v___x_6075_);
if (v_decide_6076_ == 0)
{
lean_object* v___x_6078_; uint8_t v_isShared_6079_; uint8_t v_isSharedCheck_6084_; 
lean_inc(v_pos_6072_);
v_isSharedCheck_6084_ = !lean_is_exclusive(v___x_6071_);
if (v_isSharedCheck_6084_ == 0)
{
lean_object* v_unused_6085_; lean_object* v_unused_6086_; 
v_unused_6085_ = lean_ctor_get(v___x_6071_, 1);
lean_dec(v_unused_6085_);
v_unused_6086_ = lean_ctor_get(v___x_6071_, 0);
lean_dec(v_unused_6086_);
v___x_6078_ = v___x_6071_;
v_isShared_6079_ = v_isSharedCheck_6084_;
goto v_resetjp_6077_;
}
else
{
lean_dec(v___x_6071_);
v___x_6078_ = lean_box(0);
v_isShared_6079_ = v_isSharedCheck_6084_;
goto v_resetjp_6077_;
}
v_resetjp_6077_:
{
lean_object* v___x_6080_; lean_object* v___x_6082_; 
v___x_6080_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_6079_ == 0)
{
lean_ctor_set_tag(v___x_6078_, 1);
lean_ctor_set(v___x_6078_, 1, v___x_6080_);
v___x_6082_ = v___x_6078_;
goto v_reusejp_6081_;
}
else
{
lean_object* v_reuseFailAlloc_6083_; 
v_reuseFailAlloc_6083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6083_, 0, v_pos_6072_);
lean_ctor_set(v_reuseFailAlloc_6083_, 1, v___x_6080_);
v___x_6082_ = v_reuseFailAlloc_6083_;
goto v_reusejp_6081_;
}
v_reusejp_6081_:
{
return v___x_6082_;
}
}
}
else
{
return v___x_6071_;
}
}
else
{
return v___x_6071_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_offsetOfZoneId_x3f(lean_object* v_id_6103_){
_start:
{
lean_object* v___f_6104_; lean_object* v___x_6105_; 
v___f_6104_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_offsetOfZoneId_x3f___closed__0));
v___x_6105_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_6104_, v_id_6103_);
if (lean_obj_tag(v___x_6105_) == 0)
{
lean_object* v___x_6106_; 
lean_dec_ref_known(v___x_6105_, 1);
v___x_6106_ = lean_box(0);
return v___x_6106_;
}
else
{
lean_object* v_a_6107_; lean_object* v___x_6109_; uint8_t v_isShared_6110_; uint8_t v_isSharedCheck_6114_; 
v_a_6107_ = lean_ctor_get(v___x_6105_, 0);
v_isSharedCheck_6114_ = !lean_is_exclusive(v___x_6105_);
if (v_isSharedCheck_6114_ == 0)
{
v___x_6109_ = v___x_6105_;
v_isShared_6110_ = v_isSharedCheck_6114_;
goto v_resetjp_6108_;
}
else
{
lean_inc(v_a_6107_);
lean_dec(v___x_6105_);
v___x_6109_ = lean_box(0);
v_isShared_6110_ = v_isSharedCheck_6114_;
goto v_resetjp_6108_;
}
v_resetjp_6108_:
{
lean_object* v___x_6112_; 
if (v_isShared_6110_ == 0)
{
v___x_6112_ = v___x_6109_;
goto v_reusejp_6111_;
}
else
{
lean_object* v_reuseFailAlloc_6113_; 
v_reuseFailAlloc_6113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6113_, 0, v_a_6107_);
v___x_6112_ = v_reuseFailAlloc_6113_;
goto v_reusejp_6111_;
}
v_reusejp_6111_:
{
return v___x_6112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekDate(lean_object* v_dateformat_6115_, lean_object* v_year_6116_, lean_object* v_week_6117_, uint8_t v_weekday_6118_){
_start:
{
uint8_t v_firstDayOfWeek_6119_; lean_object* v_minimalDaysInFirstWeek_6120_; lean_object* v_start_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v_dayOfWeek_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v_dateDays_6131_; lean_object* v___x_6132_; lean_object* v_date_6133_; lean_object* v___x_6134_; uint8_t v___x_6135_; 
v_firstDayOfWeek_6119_ = lean_ctor_get_uint8(v_dateformat_6115_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_6120_ = lean_ctor_get(v_dateformat_6115_, 0);
lean_inc(v_year_6116_);
v_start_6121_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v_year_6116_, v_firstDayOfWeek_6119_, v_minimalDaysInFirstWeek_6120_);
v___x_6122_ = l_Std_Time_Weekday_toOrdinal(v_weekday_6118_);
v___x_6123_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_6119_);
v___x_6124_ = lean_int_sub(v___x_6122_, v___x_6123_);
lean_dec(v___x_6123_);
lean_dec(v___x_6122_);
v___x_6125_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v_dayOfWeek_6126_ = lean_int_emod(v___x_6124_, v___x_6125_);
lean_dec(v___x_6124_);
v___x_6127_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6128_ = lean_int_sub(v_week_6117_, v___x_6127_);
v___x_6129_ = lean_int_mul(v___x_6128_, v___x_6125_);
lean_dec(v___x_6128_);
v___x_6130_ = lean_int_add(v___x_6129_, v_dayOfWeek_6126_);
lean_dec(v_dayOfWeek_6126_);
lean_dec(v___x_6129_);
v_dateDays_6131_ = l_Std_Time_PlainDate_toEpochDay(v_start_6121_);
v___x_6132_ = lean_int_add(v_dateDays_6131_, v___x_6130_);
lean_dec(v___x_6130_);
lean_dec(v_dateDays_6131_);
v_date_6133_ = l_Std_Time_PlainDate_ofEpochDay(v___x_6132_);
lean_dec(v___x_6132_);
lean_inc_ref(v_date_6133_);
v___x_6134_ = l_Std_Time_PlainDate_weekYear(v_date_6133_, v_firstDayOfWeek_6119_, v_minimalDaysInFirstWeek_6120_);
v___x_6135_ = lean_int_dec_eq(v___x_6134_, v_year_6116_);
lean_dec(v_year_6116_);
lean_dec(v___x_6134_);
if (v___x_6135_ == 0)
{
lean_object* v___x_6136_; 
lean_dec_ref(v_date_6133_);
v___x_6136_ = lean_box(0);
return v___x_6136_;
}
else
{
lean_object* v___x_6137_; 
v___x_6137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6137_, 0, v_date_6133_);
return v___x_6137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekDate___boxed(lean_object* v_dateformat_6138_, lean_object* v_year_6139_, lean_object* v_week_6140_, lean_object* v_weekday_6141_){
_start:
{
uint8_t v_weekday_boxed_6142_; lean_object* v_res_6143_; 
v_weekday_boxed_6142_ = lean_unbox(v_weekday_6141_);
v_res_6143_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekDate(v_dateformat_6138_, v_year_6139_, v_week_6140_, v_weekday_boxed_6142_);
lean_dec(v_week_6140_);
lean_dec_ref(v_dateformat_6138_);
return v_res_6143_;
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___at___00__private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay_spec__0(lean_object* v_month_6144_, lean_object* v_day_6145_, lean_object* v_dateformat_6146_, lean_object* v_year_6147_, lean_object* v_x_6148_){
_start:
{
if (lean_obj_tag(v_x_6148_) == 0)
{
lean_object* v___x_6149_; 
lean_dec(v_day_6145_);
lean_dec(v_month_6144_);
v___x_6149_ = lean_box(0);
return v___x_6149_;
}
else
{
lean_object* v_head_6150_; lean_object* v_tail_6151_; uint8_t v___y_6153_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; uint8_t v___x_6167_; 
v_head_6150_ = lean_ctor_get(v_x_6148_, 0);
v_tail_6151_ = lean_ctor_get(v_x_6148_, 1);
v___x_6164_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0);
v___x_6165_ = lean_int_mod(v_head_6150_, v___x_6164_);
v___x_6166_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6167_ = lean_int_dec_eq(v___x_6165_, v___x_6166_);
lean_dec(v___x_6165_);
if (v___x_6167_ == 0)
{
v___y_6153_ = v___x_6167_;
goto v___jp_6152_;
}
else
{
lean_object* v___x_6168_; lean_object* v___x_6169_; uint8_t v___x_6170_; 
v___x_6168_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_6169_ = lean_int_mod(v_head_6150_, v___x_6168_);
v___x_6170_ = lean_int_dec_eq(v___x_6169_, v___x_6166_);
lean_dec(v___x_6169_);
if (v___x_6170_ == 0)
{
v___y_6153_ = v___x_6167_;
goto v___jp_6152_;
}
else
{
lean_object* v___x_6171_; lean_object* v___x_6172_; uint8_t v___x_6173_; 
v___x_6171_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1);
v___x_6172_ = lean_int_mod(v_head_6150_, v___x_6171_);
v___x_6173_ = lean_int_dec_eq(v___x_6172_, v___x_6166_);
lean_dec(v___x_6172_);
v___y_6153_ = v___x_6173_;
goto v___jp_6152_;
}
}
v___jp_6152_:
{
lean_object* v___x_6154_; uint8_t v___x_6155_; 
v___x_6154_ = l_Std_Time_Month_Ordinal_days(v___y_6153_, v_month_6144_);
v___x_6155_ = lean_int_dec_le(v_day_6145_, v___x_6154_);
lean_dec(v___x_6154_);
if (v___x_6155_ == 0)
{
v_x_6148_ = v_tail_6151_;
goto _start;
}
else
{
uint8_t v_firstDayOfWeek_6157_; lean_object* v_minimalDaysInFirstWeek_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; uint8_t v___x_6162_; 
v_firstDayOfWeek_6157_ = lean_ctor_get_uint8(v_dateformat_6146_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_6158_ = lean_ctor_get(v_dateformat_6146_, 0);
lean_inc(v_day_6145_);
lean_inc(v_month_6144_);
lean_inc(v_head_6150_);
v___x_6159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6159_, 0, v_head_6150_);
lean_ctor_set(v___x_6159_, 1, v_month_6144_);
lean_ctor_set(v___x_6159_, 2, v_day_6145_);
lean_inc_ref(v___x_6159_);
v___x_6160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6160_, 0, v___x_6159_);
v___x_6161_ = l_Std_Time_PlainDate_weekYear(v___x_6159_, v_firstDayOfWeek_6157_, v_minimalDaysInFirstWeek_6158_);
v___x_6162_ = lean_int_dec_eq(v___x_6161_, v_year_6147_);
lean_dec(v___x_6161_);
if (v___x_6162_ == 0)
{
lean_dec_ref_known(v___x_6160_, 1);
v_x_6148_ = v_tail_6151_;
goto _start;
}
else
{
lean_dec(v_day_6145_);
lean_dec(v_month_6144_);
return v___x_6160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___at___00__private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay_spec__0___boxed(lean_object* v_month_6174_, lean_object* v_day_6175_, lean_object* v_dateformat_6176_, lean_object* v_year_6177_, lean_object* v_x_6178_){
_start:
{
lean_object* v_res_6179_; 
v_res_6179_ = l_List_findSome_x3f___at___00__private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay_spec__0(v_month_6174_, v_day_6175_, v_dateformat_6176_, v_year_6177_, v_x_6178_);
lean_dec(v_x_6178_);
lean_dec(v_year_6177_);
lean_dec_ref(v_dateformat_6176_);
return v_res_6179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay(lean_object* v_dateformat_6180_, lean_object* v_year_6181_, lean_object* v_month_6182_, lean_object* v_day_6183_){
_start:
{
lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; 
v___x_6184_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6185_ = lean_int_sub(v_year_6181_, v___x_6184_);
v___x_6186_ = lean_int_add(v_year_6181_, v___x_6184_);
v___x_6187_ = lean_box(0);
v___x_6188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6188_, 0, v___x_6186_);
lean_ctor_set(v___x_6188_, 1, v___x_6187_);
v___x_6189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6189_, 0, v___x_6185_);
lean_ctor_set(v___x_6189_, 1, v___x_6188_);
lean_inc(v_year_6181_);
v___x_6190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6190_, 0, v_year_6181_);
lean_ctor_set(v___x_6190_, 1, v___x_6189_);
v___x_6191_ = l_List_findSome_x3f___at___00__private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay_spec__0(v_month_6182_, v_day_6183_, v_dateformat_6180_, v_year_6181_, v___x_6190_);
lean_dec_ref_known(v___x_6190_, 2);
lean_dec(v_year_6181_);
return v___x_6191_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay___boxed(lean_object* v_dateformat_6192_, lean_object* v_year_6193_, lean_object* v_month_6194_, lean_object* v_day_6195_){
_start:
{
lean_object* v_res_6196_; 
v_res_6196_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay(v_dateformat_6192_, v_year_6193_, v_month_6194_, v_day_6195_);
lean_dec_ref(v_dateformat_6192_);
return v_res_6196_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__0(void){
_start:
{
lean_object* v___x_6197_; lean_object* v___x_6198_; 
v___x_6197_ = lean_unsigned_to_nat(11u);
v___x_6198_ = lean_nat_to_int(v___x_6197_);
return v___x_6198_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; 
v___x_6199_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__0);
v___x_6200_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6201_ = lean_int_add(v___x_6200_, v___x_6199_);
return v___x_6201_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__2(void){
_start:
{
lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; 
v___x_6202_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6203_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__1);
v___x_6204_ = lean_int_sub(v___x_6203_, v___x_6202_);
return v___x_6204_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3(void){
_start:
{
lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v_range_6207_; 
v___x_6205_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6206_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__2);
v_range_6207_ = lean_int_add(v___x_6206_, v___x_6205_);
return v_range_6207_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4(void){
_start:
{
lean_object* v___x_6208_; lean_object* v___x_6209_; 
v___x_6208_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6209_ = lean_int_sub(v___x_6208_, v___x_6208_);
return v___x_6209_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__5(void){
_start:
{
lean_object* v_range_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; 
v_range_6210_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3);
v___x_6211_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4);
v___x_6212_ = lean_int_emod(v___x_6211_, v_range_6210_);
return v___x_6212_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__6(void){
_start:
{
lean_object* v_range_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; 
v_range_6213_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3);
v___x_6214_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__5);
v___x_6215_ = lean_int_add(v___x_6214_, v_range_6213_);
return v___x_6215_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__7(void){
_start:
{
lean_object* v_range_6216_; lean_object* v___x_6217_; lean_object* v___x_6218_; 
v_range_6216_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__3);
v___x_6217_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__6);
v___x_6218_ = lean_int_emod(v___x_6217_, v_range_6216_);
return v___x_6218_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__8(void){
_start:
{
lean_object* v___x_6219_; lean_object* v___x_6220_; lean_object* v___x_6221_; 
v___x_6219_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6220_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__7, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__7_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__7);
v___x_6221_ = lean_int_add(v___x_6220_, v___x_6219_);
return v___x_6221_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__9(void){
_start:
{
lean_object* v___x_6222_; lean_object* v___x_6223_; 
v___x_6222_ = lean_unsigned_to_nat(30u);
v___x_6223_ = lean_nat_to_int(v___x_6222_);
return v___x_6223_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__10(void){
_start:
{
lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; 
v___x_6224_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__9, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__9_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__9);
v___x_6225_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6226_ = lean_int_add(v___x_6225_, v___x_6224_);
return v___x_6226_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__11(void){
_start:
{
lean_object* v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; 
v___x_6227_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6228_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__10, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__10_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__10);
v___x_6229_ = lean_int_sub(v___x_6228_, v___x_6227_);
return v___x_6229_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12(void){
_start:
{
lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v_range_6232_; 
v___x_6230_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6231_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__11, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__11_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__11);
v_range_6232_ = lean_int_add(v___x_6231_, v___x_6230_);
return v_range_6232_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__13(void){
_start:
{
lean_object* v_range_6233_; lean_object* v___x_6234_; lean_object* v___x_6235_; 
v_range_6233_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12);
v___x_6234_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4);
v___x_6235_ = lean_int_emod(v___x_6234_, v_range_6233_);
return v___x_6235_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__14(void){
_start:
{
lean_object* v_range_6236_; lean_object* v___x_6237_; lean_object* v___x_6238_; 
v_range_6236_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12);
v___x_6237_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__13, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__13_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__13);
v___x_6238_ = lean_int_add(v___x_6237_, v_range_6236_);
return v___x_6238_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__15(void){
_start:
{
lean_object* v_range_6239_; lean_object* v___x_6240_; lean_object* v___x_6241_; 
v_range_6239_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__12);
v___x_6240_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__14, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__14_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__14);
v___x_6241_ = lean_int_emod(v___x_6240_, v_range_6239_);
return v___x_6241_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__16(void){
_start:
{
lean_object* v___x_6242_; lean_object* v___x_6243_; lean_object* v___x_6244_; 
v___x_6242_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6243_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__15);
v___x_6244_ = lean_int_add(v___x_6243_, v___x_6242_);
return v___x_6244_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(lean_object* v_year_x3f_6245_, lean_object* v_x_6246_){
_start:
{
lean_object* v___y_6248_; lean_object* v___y_6249_; lean_object* v___y_6250_; uint8_t v___y_6251_; lean_object* v___y_6258_; 
if (lean_obj_tag(v_year_x3f_6245_) == 0)
{
lean_object* v___x_6271_; 
v___x_6271_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6258_ = v___x_6271_;
goto v___jp_6257_;
}
else
{
lean_object* v_val_6272_; 
v_val_6272_ = lean_ctor_get(v_year_x3f_6245_, 0);
lean_inc(v_val_6272_);
lean_dec_ref_known(v_year_x3f_6245_, 1);
v___y_6258_ = v_val_6272_;
goto v___jp_6257_;
}
v___jp_6247_:
{
lean_object* v___x_6252_; uint8_t v___x_6253_; 
v___x_6252_ = l_Std_Time_Month_Ordinal_days(v___y_6251_, v___y_6249_);
v___x_6253_ = lean_int_dec_le(v___y_6250_, v___x_6252_);
lean_dec(v___x_6252_);
if (v___x_6253_ == 0)
{
lean_object* v___x_6254_; 
lean_dec(v___y_6248_);
v___x_6254_ = lean_box(0);
return v___x_6254_;
}
else
{
lean_object* v___x_6255_; lean_object* v___x_6256_; 
lean_inc(v___y_6250_);
lean_inc(v___y_6249_);
v___x_6255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6255_, 0, v___y_6248_);
lean_ctor_set(v___x_6255_, 1, v___y_6249_);
lean_ctor_set(v___x_6255_, 2, v___y_6250_);
v___x_6256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6256_, 0, v___x_6255_);
return v___x_6256_;
}
}
v___jp_6257_:
{
lean_object* v___x_6259_; lean_object* v___x_6260_; lean_object* v___x_6261_; lean_object* v___x_6262_; lean_object* v___x_6263_; uint8_t v___x_6264_; 
v___x_6259_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__8);
v___x_6260_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__16);
v___x_6261_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0);
v___x_6262_ = lean_int_mod(v___y_6258_, v___x_6261_);
v___x_6263_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6264_ = lean_int_dec_eq(v___x_6262_, v___x_6263_);
lean_dec(v___x_6262_);
if (v___x_6264_ == 0)
{
v___y_6248_ = v___y_6258_;
v___y_6249_ = v___x_6259_;
v___y_6250_ = v___x_6260_;
v___y_6251_ = v___x_6264_;
goto v___jp_6247_;
}
else
{
lean_object* v___x_6265_; lean_object* v___x_6266_; uint8_t v___x_6267_; 
v___x_6265_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_6266_ = lean_int_mod(v___y_6258_, v___x_6265_);
v___x_6267_ = lean_int_dec_eq(v___x_6266_, v___x_6263_);
lean_dec(v___x_6266_);
if (v___x_6267_ == 0)
{
v___y_6248_ = v___y_6258_;
v___y_6249_ = v___x_6259_;
v___y_6250_ = v___x_6260_;
v___y_6251_ = v___x_6264_;
goto v___jp_6247_;
}
else
{
lean_object* v___x_6268_; lean_object* v___x_6269_; uint8_t v___x_6270_; 
v___x_6268_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1);
v___x_6269_ = lean_int_mod(v___y_6258_, v___x_6268_);
v___x_6270_ = lean_int_dec_eq(v___x_6269_, v___x_6263_);
lean_dec(v___x_6269_);
v___y_6248_ = v___y_6258_;
v___y_6249_ = v___x_6259_;
v___y_6250_ = v___x_6260_;
v___y_6251_ = v___x_6270_;
goto v___jp_6247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed(lean_object* v_year_x3f_6273_, lean_object* v_x_6274_){
_start:
{
lean_object* v_res_6275_; 
v_res_6275_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(v_year_x3f_6273_, v_x_6274_);
lean_dec(v_x_6274_);
return v_res_6275_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(lean_object* v_val_6276_, lean_object* v_x_6277_){
_start:
{
lean_inc_ref(v_val_6276_);
return v_val_6276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1___boxed(lean_object* v_val_6278_, lean_object* v_x_6279_){
_start:
{
lean_object* v_res_6280_; 
v_res_6280_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(v_val_6278_, v_x_6279_);
lean_dec_ref(v_val_6278_);
return v_res_6280_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__2(lean_object* v_h_6281_, lean_object* v_K_6282_, uint8_t v_marker_6283_){
_start:
{
if (lean_obj_tag(v_h_6281_) == 0)
{
if (lean_obj_tag(v_K_6282_) == 0)
{
return v_K_6282_;
}
else
{
if (v_marker_6283_ == 0)
{
lean_object* v_val_6284_; lean_object* v___x_6286_; uint8_t v_isShared_6287_; uint8_t v_isSharedCheck_6291_; 
v_val_6284_ = lean_ctor_get(v_K_6282_, 0);
v_isSharedCheck_6291_ = !lean_is_exclusive(v_K_6282_);
if (v_isSharedCheck_6291_ == 0)
{
v___x_6286_ = v_K_6282_;
v_isShared_6287_ = v_isSharedCheck_6291_;
goto v_resetjp_6285_;
}
else
{
lean_inc(v_val_6284_);
lean_dec(v_K_6282_);
v___x_6286_ = lean_box(0);
v_isShared_6287_ = v_isSharedCheck_6291_;
goto v_resetjp_6285_;
}
v_resetjp_6285_:
{
lean_object* v___x_6289_; 
if (v_isShared_6287_ == 0)
{
v___x_6289_ = v___x_6286_;
goto v_reusejp_6288_;
}
else
{
lean_object* v_reuseFailAlloc_6290_; 
v_reuseFailAlloc_6290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6290_, 0, v_val_6284_);
v___x_6289_ = v_reuseFailAlloc_6290_;
goto v_reusejp_6288_;
}
v_reusejp_6288_:
{
return v___x_6289_;
}
}
}
else
{
lean_object* v_val_6292_; lean_object* v___x_6294_; uint8_t v_isShared_6295_; uint8_t v_isSharedCheck_6301_; 
v_val_6292_ = lean_ctor_get(v_K_6282_, 0);
v_isSharedCheck_6301_ = !lean_is_exclusive(v_K_6282_);
if (v_isSharedCheck_6301_ == 0)
{
v___x_6294_ = v_K_6282_;
v_isShared_6295_ = v_isSharedCheck_6301_;
goto v_resetjp_6293_;
}
else
{
lean_inc(v_val_6292_);
lean_dec(v_K_6282_);
v___x_6294_ = lean_box(0);
v_isShared_6295_ = v_isSharedCheck_6301_;
goto v_resetjp_6293_;
}
v_resetjp_6293_:
{
lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6299_; 
v___x_6296_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_6297_ = lean_int_add(v_val_6292_, v___x_6296_);
lean_dec(v_val_6292_);
if (v_isShared_6295_ == 0)
{
lean_ctor_set(v___x_6294_, 0, v___x_6297_);
v___x_6299_ = v___x_6294_;
goto v_reusejp_6298_;
}
else
{
lean_object* v_reuseFailAlloc_6300_; 
v_reuseFailAlloc_6300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6300_, 0, v___x_6297_);
v___x_6299_ = v_reuseFailAlloc_6300_;
goto v_reusejp_6298_;
}
v_reusejp_6298_:
{
return v___x_6299_;
}
}
}
}
}
else
{
lean_object* v_val_6302_; lean_object* v___x_6304_; uint8_t v_isShared_6305_; uint8_t v_isSharedCheck_6310_; 
lean_dec(v_K_6282_);
v_val_6302_ = lean_ctor_get(v_h_6281_, 0);
v_isSharedCheck_6310_ = !lean_is_exclusive(v_h_6281_);
if (v_isSharedCheck_6310_ == 0)
{
v___x_6304_ = v_h_6281_;
v_isShared_6305_ = v_isSharedCheck_6310_;
goto v_resetjp_6303_;
}
else
{
lean_inc(v_val_6302_);
lean_dec(v_h_6281_);
v___x_6304_ = lean_box(0);
v_isShared_6305_ = v_isSharedCheck_6310_;
goto v_resetjp_6303_;
}
v_resetjp_6303_:
{
lean_object* v___x_6306_; lean_object* v___x_6308_; 
v___x_6306_ = l_Std_Time_HourMarker_toAbsolute(v_marker_6283_, v_val_6302_);
lean_dec(v_val_6302_);
if (v_isShared_6305_ == 0)
{
lean_ctor_set(v___x_6304_, 0, v___x_6306_);
v___x_6308_ = v___x_6304_;
goto v_reusejp_6307_;
}
else
{
lean_object* v_reuseFailAlloc_6309_; 
v_reuseFailAlloc_6309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6309_, 0, v___x_6306_);
v___x_6308_ = v_reuseFailAlloc_6309_;
goto v_reusejp_6307_;
}
v_reusejp_6307_:
{
return v___x_6308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__2___boxed(lean_object* v_h_6311_, lean_object* v_K_6312_, lean_object* v_marker_6313_){
_start:
{
uint8_t v_marker_boxed_6314_; lean_object* v_res_6315_; 
v_marker_boxed_6314_ = lean_unbox(v_marker_6313_);
v_res_6315_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__2(v_h_6311_, v_K_6312_, v_marker_boxed_6314_);
return v_res_6315_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__3(lean_object* v___y_6316_, lean_object* v_00___6317_){
_start:
{
uint8_t v___x_6318_; lean_object* v___x_6319_; 
v___x_6318_ = 1;
v___x_6319_ = l_Std_Time_TimeZone_Offset_toIsoString(v___y_6316_, v___x_6318_);
return v___x_6319_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1(void){
_start:
{
lean_object* v___x_6322_; lean_object* v___x_6323_; 
v___x_6322_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6323_ = lean_int_neg(v___x_6322_);
return v___x_6323_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2(void){
_start:
{
lean_object* v___x_6324_; lean_object* v___x_6325_; 
v___x_6324_ = lean_unsigned_to_nat(1000000u);
v___x_6325_ = lean_nat_to_int(v___x_6324_);
return v___x_6325_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3(void){
_start:
{
lean_object* v___x_6326_; lean_object* v___x_6327_; lean_object* v___x_6328_; 
v___x_6326_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5);
v___x_6327_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6328_ = lean_int_add(v___x_6327_, v___x_6326_);
return v___x_6328_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4(void){
_start:
{
lean_object* v___x_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; 
v___x_6329_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6330_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3);
v___x_6331_ = lean_int_sub(v___x_6330_, v___x_6329_);
return v___x_6331_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5(void){
_start:
{
lean_object* v___x_6332_; lean_object* v___x_6333_; lean_object* v_range_6334_; 
v___x_6332_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6333_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4);
v_range_6334_ = lean_int_add(v___x_6333_, v___x_6332_);
return v_range_6334_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6(void){
_start:
{
lean_object* v___x_6335_; lean_object* v___x_6336_; 
v___x_6335_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6336_ = lean_int_sub(v___x_6335_, v___x_6335_);
return v___x_6336_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7(void){
_start:
{
lean_object* v_range_6337_; lean_object* v___x_6338_; lean_object* v___x_6339_; 
v_range_6337_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5);
v___x_6338_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6);
v___x_6339_ = lean_int_emod(v___x_6338_, v_range_6337_);
return v___x_6339_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8(void){
_start:
{
lean_object* v_range_6340_; lean_object* v___x_6341_; lean_object* v___x_6342_; 
v_range_6340_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5);
v___x_6341_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7);
v___x_6342_ = lean_int_add(v___x_6341_, v_range_6340_);
return v___x_6342_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9(void){
_start:
{
lean_object* v_range_6343_; lean_object* v___x_6344_; lean_object* v___x_6345_; 
v_range_6343_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5);
v___x_6344_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8);
v___x_6345_ = lean_int_emod(v___x_6344_, v_range_6343_);
return v___x_6345_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10(void){
_start:
{
lean_object* v___x_6346_; lean_object* v___x_6347_; lean_object* v___x_6348_; 
v___x_6346_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6347_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9);
v___x_6348_ = lean_int_add(v___x_6347_, v___x_6346_);
return v___x_6348_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11(void){
_start:
{
lean_object* v___x_6349_; lean_object* v___x_6350_; 
v___x_6349_ = lean_unsigned_to_nat(24u);
v___x_6350_ = lean_nat_to_int(v___x_6349_);
return v___x_6350_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12(void){
_start:
{
lean_object* v___x_6351_; lean_object* v___x_6352_; 
v___x_6351_ = lean_unsigned_to_nat(52u);
v___x_6352_ = lean_nat_to_int(v___x_6351_);
return v___x_6352_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13(void){
_start:
{
lean_object* v___x_6353_; lean_object* v___x_6354_; lean_object* v___x_6355_; 
v___x_6353_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12);
v___x_6354_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6355_ = lean_int_add(v___x_6354_, v___x_6353_);
return v___x_6355_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14(void){
_start:
{
lean_object* v___x_6356_; lean_object* v___x_6357_; lean_object* v___x_6358_; 
v___x_6356_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6357_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13);
v___x_6358_ = lean_int_sub(v___x_6357_, v___x_6356_);
return v___x_6358_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15(void){
_start:
{
lean_object* v___x_6359_; lean_object* v___x_6360_; lean_object* v_range_6361_; 
v___x_6359_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6360_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14);
v_range_6361_ = lean_int_add(v___x_6360_, v___x_6359_);
return v_range_6361_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16(void){
_start:
{
lean_object* v_range_6362_; lean_object* v___x_6363_; lean_object* v___x_6364_; 
v_range_6362_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v___x_6363_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__4);
v___x_6364_ = lean_int_emod(v___x_6363_, v_range_6362_);
return v___x_6364_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17(void){
_start:
{
lean_object* v_range_6365_; lean_object* v___x_6366_; lean_object* v___x_6367_; 
v_range_6365_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v___x_6366_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16);
v___x_6367_ = lean_int_add(v___x_6366_, v_range_6365_);
return v___x_6367_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18(void){
_start:
{
lean_object* v_range_6368_; lean_object* v___x_6369_; lean_object* v___x_6370_; 
v_range_6368_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v___x_6369_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17);
v___x_6370_ = lean_int_emod(v___x_6369_, v_range_6368_);
return v___x_6370_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19(void){
_start:
{
lean_object* v___x_6371_; lean_object* v___x_6372_; lean_object* v___x_6373_; 
v___x_6371_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6372_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18);
v___x_6373_ = lean_int_add(v___x_6372_, v___x_6371_);
return v___x_6373_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(lean_object* v_builder_6374_, lean_object* v_aw_6375_, lean_object* v_dateformat_6376_){
_start:
{
lean_object* v___y_6378_; lean_object* v___y_6379_; lean_object* v___y_6418_; lean_object* v___y_6419_; lean_object* v___y_6422_; lean_object* v___y_6423_; lean_object* v___y_6424_; lean_object* v_G_6435_; lean_object* v_y_6436_; lean_object* v_u_6437_; lean_object* v_Y_6438_; lean_object* v_D_6439_; lean_object* v_M_6440_; lean_object* v_L_6441_; lean_object* v_d_6442_; lean_object* v_w_6443_; lean_object* v_E_6444_; lean_object* v_e_6445_; lean_object* v_c_6446_; lean_object* v_a_6447_; lean_object* v_b_6448_; lean_object* v_B_6449_; lean_object* v_h_6450_; lean_object* v_K_6451_; lean_object* v_k_6452_; lean_object* v_H_6453_; lean_object* v_m_6454_; lean_object* v_s_6455_; lean_object* v_S_6456_; lean_object* v_A_6457_; lean_object* v_n_6458_; lean_object* v_N_6459_; lean_object* v_V_6460_; lean_object* v_z_6461_; lean_object* v_zabbrev_6462_; lean_object* v_v_6463_; lean_object* v_O_6464_; lean_object* v_X_6465_; lean_object* v_x_6466_; lean_object* v_Z_6467_; lean_object* v___y_6469_; lean_object* v___y_6470_; lean_object* v___y_6471_; lean_object* v___y_6472_; lean_object* v___y_6473_; lean_object* v___y_6474_; lean_object* v___y_6483_; lean_object* v___y_6484_; lean_object* v___y_6485_; lean_object* v___y_6486_; lean_object* v___y_6487_; lean_object* v___y_6492_; lean_object* v___y_6493_; lean_object* v___y_6494_; uint8_t v___y_6495_; lean_object* v___y_6496_; lean_object* v___y_6501_; lean_object* v___y_6502_; uint8_t v___y_6503_; lean_object* v___y_6504_; lean_object* v___y_6508_; lean_object* v___y_6509_; lean_object* v___y_6510_; lean_object* v___y_6511_; uint8_t v___y_6512_; lean_object* v___y_6520_; lean_object* v___y_6521_; lean_object* v___y_6522_; lean_object* v___y_6523_; uint8_t v___y_6524_; lean_object* v___y_6525_; lean_object* v___y_6530_; lean_object* v___y_6531_; lean_object* v___y_6532_; lean_object* v___y_6533_; lean_object* v___y_6534_; uint8_t v___y_6535_; lean_object* v___y_6536_; lean_object* v___y_6538_; lean_object* v___y_6539_; lean_object* v___y_6540_; lean_object* v___y_6541_; uint8_t v___y_6542_; lean_object* v___y_6543_; lean_object* v___y_6544_; lean_object* v___y_6556_; lean_object* v___y_6557_; lean_object* v___y_6558_; lean_object* v___y_6559_; lean_object* v___y_6560_; lean_object* v___y_6561_; uint8_t v___y_6562_; lean_object* v___y_6563_; lean_object* v___y_6564_; lean_object* v___y_6577_; lean_object* v___y_6578_; lean_object* v___y_6579_; lean_object* v___y_6580_; lean_object* v___y_6581_; lean_object* v___y_6582_; lean_object* v___y_6583_; uint8_t v___y_6584_; lean_object* v___y_6585_; lean_object* v___y_6586_; lean_object* v___y_6601_; uint8_t v___y_6602_; lean_object* v___y_6603_; lean_object* v___y_6625_; lean_object* v___y_6626_; lean_object* v___y_6627_; uint8_t v___y_6628_; uint8_t v___y_6629_; lean_object* v___y_6635_; lean_object* v___y_6636_; uint8_t v___y_6637_; lean_object* v___y_6638_; uint8_t v___y_6639_; lean_object* v___y_6646_; lean_object* v___y_6647_; lean_object* v___y_6648_; uint8_t v___y_6649_; lean_object* v___y_6650_; lean_object* v___y_6651_; lean_object* v___y_6668_; lean_object* v___y_6669_; lean_object* v___y_6670_; uint8_t v___y_6671_; lean_object* v___y_6672_; lean_object* v___y_6675_; lean_object* v___y_6676_; lean_object* v___y_6677_; uint8_t v___y_6678_; lean_object* v___y_6679_; lean_object* v___y_6682_; uint8_t v___y_6683_; lean_object* v___y_6684_; lean_object* v___y_6685_; lean_object* v___y_6698_; lean_object* v___y_6699_; lean_object* v___y_6700_; lean_object* v___y_6701_; uint8_t v___y_6702_; uint8_t v___y_6703_; lean_object* v___y_6710_; lean_object* v___y_6711_; lean_object* v___y_6712_; uint8_t v___y_6713_; lean_object* v___y_6714_; lean_object* v___y_6726_; lean_object* v___y_6727_; lean_object* v___y_6728_; uint8_t v___y_6729_; lean_object* v___y_6732_; lean_object* v___y_6733_; lean_object* v___y_6734_; uint8_t v___y_6735_; lean_object* v___y_6736_; lean_object* v___y_6741_; lean_object* v___y_6742_; uint8_t v___y_6743_; lean_object* v___y_6744_; lean_object* v___y_6748_; lean_object* v___y_6749_; uint8_t v___y_6750_; lean_object* v___y_6753_; lean_object* v_val_6754_; lean_object* v___y_6755_; lean_object* v___y_6758_; uint8_t v___y_6759_; lean_object* v___y_6760_; lean_object* v___y_6783_; lean_object* v___y_6784_; lean_object* v___y_6785_; lean_object* v___y_6810_; lean_object* v___y_6811_; lean_object* v___y_6812_; lean_object* v___y_6817_; lean_object* v_val_6827_; 
v_G_6435_ = lean_ctor_get(v_builder_6374_, 0);
lean_inc(v_G_6435_);
v_y_6436_ = lean_ctor_get(v_builder_6374_, 1);
lean_inc(v_y_6436_);
v_u_6437_ = lean_ctor_get(v_builder_6374_, 2);
lean_inc(v_u_6437_);
v_Y_6438_ = lean_ctor_get(v_builder_6374_, 3);
lean_inc(v_Y_6438_);
v_D_6439_ = lean_ctor_get(v_builder_6374_, 4);
lean_inc(v_D_6439_);
v_M_6440_ = lean_ctor_get(v_builder_6374_, 5);
lean_inc(v_M_6440_);
v_L_6441_ = lean_ctor_get(v_builder_6374_, 6);
lean_inc(v_L_6441_);
v_d_6442_ = lean_ctor_get(v_builder_6374_, 7);
lean_inc(v_d_6442_);
v_w_6443_ = lean_ctor_get(v_builder_6374_, 10);
lean_inc(v_w_6443_);
v_E_6444_ = lean_ctor_get(v_builder_6374_, 12);
lean_inc(v_E_6444_);
v_e_6445_ = lean_ctor_get(v_builder_6374_, 13);
lean_inc(v_e_6445_);
v_c_6446_ = lean_ctor_get(v_builder_6374_, 14);
lean_inc(v_c_6446_);
v_a_6447_ = lean_ctor_get(v_builder_6374_, 16);
lean_inc(v_a_6447_);
v_b_6448_ = lean_ctor_get(v_builder_6374_, 17);
lean_inc(v_b_6448_);
v_B_6449_ = lean_ctor_get(v_builder_6374_, 18);
lean_inc(v_B_6449_);
v_h_6450_ = lean_ctor_get(v_builder_6374_, 19);
lean_inc(v_h_6450_);
v_K_6451_ = lean_ctor_get(v_builder_6374_, 20);
lean_inc(v_K_6451_);
v_k_6452_ = lean_ctor_get(v_builder_6374_, 21);
lean_inc(v_k_6452_);
v_H_6453_ = lean_ctor_get(v_builder_6374_, 22);
lean_inc(v_H_6453_);
v_m_6454_ = lean_ctor_get(v_builder_6374_, 23);
lean_inc(v_m_6454_);
v_s_6455_ = lean_ctor_get(v_builder_6374_, 24);
lean_inc(v_s_6455_);
v_S_6456_ = lean_ctor_get(v_builder_6374_, 25);
lean_inc(v_S_6456_);
v_A_6457_ = lean_ctor_get(v_builder_6374_, 26);
lean_inc(v_A_6457_);
v_n_6458_ = lean_ctor_get(v_builder_6374_, 27);
lean_inc(v_n_6458_);
v_N_6459_ = lean_ctor_get(v_builder_6374_, 28);
lean_inc(v_N_6459_);
v_V_6460_ = lean_ctor_get(v_builder_6374_, 29);
lean_inc(v_V_6460_);
v_z_6461_ = lean_ctor_get(v_builder_6374_, 30);
lean_inc(v_z_6461_);
v_zabbrev_6462_ = lean_ctor_get(v_builder_6374_, 31);
lean_inc(v_zabbrev_6462_);
v_v_6463_ = lean_ctor_get(v_builder_6374_, 32);
lean_inc(v_v_6463_);
v_O_6464_ = lean_ctor_get(v_builder_6374_, 33);
lean_inc(v_O_6464_);
v_X_6465_ = lean_ctor_get(v_builder_6374_, 34);
lean_inc(v_X_6465_);
v_x_6466_ = lean_ctor_get(v_builder_6374_, 35);
lean_inc(v_x_6466_);
v_Z_6467_ = lean_ctor_get(v_builder_6374_, 36);
lean_inc(v_Z_6467_);
lean_dec_ref(v_builder_6374_);
if (lean_obj_tag(v_O_6464_) == 0)
{
if (lean_obj_tag(v_X_6465_) == 0)
{
if (lean_obj_tag(v_x_6466_) == 0)
{
if (lean_obj_tag(v_Z_6467_) == 0)
{
if (lean_obj_tag(v_V_6460_) == 0)
{
if (lean_obj_tag(v_v_6463_) == 0)
{
if (lean_obj_tag(v_z_6461_) == 0)
{
if (lean_obj_tag(v_zabbrev_6462_) == 0)
{
goto v___jp_6824_;
}
else
{
lean_object* v_val_6830_; 
v_val_6830_ = lean_ctor_get(v_zabbrev_6462_, 0);
lean_inc(v_val_6830_);
v_val_6827_ = v_val_6830_;
goto v___jp_6826_;
}
}
else
{
lean_object* v_val_6831_; 
v_val_6831_ = lean_ctor_get(v_z_6461_, 0);
lean_inc(v_val_6831_);
v_val_6827_ = v_val_6831_;
goto v___jp_6826_;
}
}
else
{
lean_object* v_val_6832_; 
v_val_6832_ = lean_ctor_get(v_v_6463_, 0);
lean_inc(v_val_6832_);
v_val_6827_ = v_val_6832_;
goto v___jp_6826_;
}
}
else
{
lean_object* v_val_6833_; 
v_val_6833_ = lean_ctor_get(v_V_6460_, 0);
lean_inc(v_val_6833_);
v_val_6827_ = v_val_6833_;
goto v___jp_6826_;
}
}
else
{
lean_object* v_val_6834_; 
v_val_6834_ = lean_ctor_get(v_Z_6467_, 0);
lean_inc(v_val_6834_);
lean_dec_ref_known(v_Z_6467_, 1);
v___y_6817_ = v_val_6834_;
goto v___jp_6816_;
}
}
else
{
lean_object* v_val_6835_; 
lean_dec(v_Z_6467_);
v_val_6835_ = lean_ctor_get(v_x_6466_, 0);
lean_inc(v_val_6835_);
lean_dec_ref_known(v_x_6466_, 1);
v___y_6817_ = v_val_6835_;
goto v___jp_6816_;
}
}
else
{
lean_object* v_val_6836_; 
lean_dec(v_Z_6467_);
lean_dec(v_x_6466_);
v_val_6836_ = lean_ctor_get(v_X_6465_, 0);
lean_inc(v_val_6836_);
lean_dec_ref_known(v_X_6465_, 1);
v___y_6817_ = v_val_6836_;
goto v___jp_6816_;
}
}
else
{
lean_object* v_val_6837_; 
lean_dec(v_Z_6467_);
lean_dec(v_x_6466_);
lean_dec(v_X_6465_);
v_val_6837_ = lean_ctor_get(v_O_6464_, 0);
lean_inc(v_val_6837_);
lean_dec_ref_known(v_O_6464_, 1);
v___y_6817_ = v_val_6837_;
goto v___jp_6816_;
}
v___jp_6377_:
{
if (lean_obj_tag(v___y_6378_) == 0)
{
lean_object* v___x_6380_; 
lean_dec_ref(v___y_6379_);
v___x_6380_ = lean_box(0);
return v___x_6380_;
}
else
{
lean_object* v_val_6381_; lean_object* v___x_6383_; uint8_t v_isShared_6384_; uint8_t v_isSharedCheck_6416_; 
v_val_6381_ = lean_ctor_get(v___y_6378_, 0);
v_isSharedCheck_6416_ = !lean_is_exclusive(v___y_6378_);
if (v_isSharedCheck_6416_ == 0)
{
v___x_6383_ = v___y_6378_;
v_isShared_6384_ = v_isSharedCheck_6416_;
goto v_resetjp_6382_;
}
else
{
lean_inc(v_val_6381_);
lean_dec(v___y_6378_);
v___x_6383_ = lean_box(0);
v_isShared_6384_ = v_isSharedCheck_6416_;
goto v_resetjp_6382_;
}
v_resetjp_6382_:
{
lean_object* v_offset_6385_; lean_object* v_name_6386_; lean_object* v_abbreviation_6387_; uint8_t v_isDST_6388_; uint8_t v___x_6389_; uint8_t v___x_6390_; lean_object* v_ltt_6391_; lean_object* v___x_6392_; lean_object* v___x_6393_; lean_object* v___x_6394_; lean_object* v_wt_6395_; lean_object* v_ltt_6396_; lean_object* v_tz_6397_; lean_object* v_offset_6398_; lean_object* v_second_6399_; lean_object* v_nano_6400_; lean_object* v___f_6401_; lean_object* v___x_6402_; lean_object* v___x_6403_; lean_object* v___x_6404_; lean_object* v___x_6405_; lean_object* v___x_6406_; lean_object* v_nanos_6407_; lean_object* v___x_6408_; lean_object* v_nanos_6409_; lean_object* v___x_6410_; lean_object* v___x_6411_; lean_object* v___x_6412_; lean_object* v___x_6414_; 
v_offset_6385_ = lean_ctor_get(v___y_6379_, 0);
lean_inc(v_offset_6385_);
v_name_6386_ = lean_ctor_get(v___y_6379_, 1);
lean_inc_ref(v_name_6386_);
v_abbreviation_6387_ = lean_ctor_get(v___y_6379_, 2);
lean_inc_ref(v_abbreviation_6387_);
v_isDST_6388_ = lean_ctor_get_uint8(v___y_6379_, sizeof(void*)*3);
lean_dec_ref(v___y_6379_);
v___x_6389_ = 0;
v___x_6390_ = 1;
v_ltt_6391_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6391_, 0, v_offset_6385_);
lean_ctor_set(v_ltt_6391_, 1, v_abbreviation_6387_);
lean_ctor_set(v_ltt_6391_, 2, v_name_6386_);
lean_ctor_set_uint8(v_ltt_6391_, sizeof(void*)*3, v_isDST_6388_);
lean_ctor_set_uint8(v_ltt_6391_, sizeof(void*)*3 + 1, v___x_6389_);
lean_ctor_set_uint8(v_ltt_6391_, sizeof(void*)*3 + 2, v___x_6390_);
v___x_6392_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6393_ = lean_box(0);
v___x_6394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6394_, 0, v_ltt_6391_);
lean_ctor_set(v___x_6394_, 1, v___x_6392_);
lean_ctor_set(v___x_6394_, 2, v___x_6393_);
lean_inc(v_val_6381_);
v_wt_6395_ = l_Std_Time_PlainDateTime_toWallTime(v_val_6381_);
lean_inc_ref(v___x_6394_);
v_ltt_6396_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_6394_, v_wt_6395_);
v_tz_6397_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_6396_);
lean_dec_ref(v_ltt_6396_);
v_offset_6398_ = lean_ctor_get(v_tz_6397_, 0);
v_second_6399_ = lean_ctor_get(v_wt_6395_, 0);
lean_inc(v_second_6399_);
v_nano_6400_ = lean_ctor_get(v_wt_6395_, 1);
lean_inc(v_nano_6400_);
lean_dec_ref(v_wt_6395_);
v___f_6401_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1___boxed), 2, 1);
lean_closure_set(v___f_6401_, 0, v_val_6381_);
v___x_6402_ = lean_mk_thunk(v___f_6401_);
v___x_6403_ = lean_int_neg(v_offset_6398_);
v___x_6404_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1);
v___x_6405_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3);
v___x_6406_ = lean_int_mul(v_second_6399_, v___x_6405_);
lean_dec(v_second_6399_);
v_nanos_6407_ = lean_int_add(v___x_6406_, v_nano_6400_);
lean_dec(v_nano_6400_);
lean_dec(v___x_6406_);
v___x_6408_ = lean_int_mul(v___x_6403_, v___x_6405_);
lean_dec(v___x_6403_);
v_nanos_6409_ = lean_int_add(v___x_6408_, v___x_6404_);
lean_dec(v___x_6408_);
v___x_6410_ = lean_int_add(v_nanos_6407_, v_nanos_6409_);
lean_dec(v_nanos_6409_);
lean_dec(v_nanos_6407_);
v___x_6411_ = l_Std_Time_Duration_ofNanoseconds(v___x_6410_);
lean_dec(v___x_6410_);
v___x_6412_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6412_, 0, v___x_6402_);
lean_ctor_set(v___x_6412_, 1, v___x_6411_);
lean_ctor_set(v___x_6412_, 2, v___x_6394_);
lean_ctor_set(v___x_6412_, 3, v_tz_6397_);
if (v_isShared_6384_ == 0)
{
lean_ctor_set(v___x_6383_, 0, v___x_6412_);
v___x_6414_ = v___x_6383_;
goto v_reusejp_6413_;
}
else
{
lean_object* v_reuseFailAlloc_6415_; 
v_reuseFailAlloc_6415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6415_, 0, v___x_6412_);
v___x_6414_ = v_reuseFailAlloc_6415_;
goto v_reusejp_6413_;
}
v_reusejp_6413_:
{
return v___x_6414_;
}
}
}
}
v___jp_6417_:
{
if (lean_obj_tag(v_aw_6375_) == 0)
{
lean_object* v_a_6420_; 
lean_dec_ref(v___y_6418_);
v_a_6420_ = lean_ctor_get(v_aw_6375_, 0);
lean_inc_ref(v_a_6420_);
lean_dec_ref_known(v_aw_6375_, 1);
v___y_6378_ = v___y_6419_;
v___y_6379_ = v_a_6420_;
goto v___jp_6377_;
}
else
{
v___y_6378_ = v___y_6419_;
v___y_6379_ = v___y_6418_;
goto v___jp_6377_;
}
}
v___jp_6421_:
{
if (lean_obj_tag(v___y_6423_) == 0)
{
lean_object* v___x_6425_; 
lean_dec_ref(v___y_6424_);
v___x_6425_ = lean_box(0);
v___y_6418_ = v___y_6422_;
v___y_6419_ = v___x_6425_;
goto v___jp_6417_;
}
else
{
lean_object* v_val_6426_; lean_object* v___x_6428_; uint8_t v_isShared_6429_; uint8_t v_isSharedCheck_6434_; 
v_val_6426_ = lean_ctor_get(v___y_6423_, 0);
v_isSharedCheck_6434_ = !lean_is_exclusive(v___y_6423_);
if (v_isSharedCheck_6434_ == 0)
{
v___x_6428_ = v___y_6423_;
v_isShared_6429_ = v_isSharedCheck_6434_;
goto v_resetjp_6427_;
}
else
{
lean_inc(v_val_6426_);
lean_dec(v___y_6423_);
v___x_6428_ = lean_box(0);
v_isShared_6429_ = v_isSharedCheck_6434_;
goto v_resetjp_6427_;
}
v_resetjp_6427_:
{
lean_object* v___x_6430_; lean_object* v___x_6432_; 
v___x_6430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6430_, 0, v_val_6426_);
lean_ctor_set(v___x_6430_, 1, v___y_6424_);
if (v_isShared_6429_ == 0)
{
lean_ctor_set(v___x_6428_, 0, v___x_6430_);
v___x_6432_ = v___x_6428_;
goto v_reusejp_6431_;
}
else
{
lean_object* v_reuseFailAlloc_6433_; 
v_reuseFailAlloc_6433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6433_, 0, v___x_6430_);
v___x_6432_ = v_reuseFailAlloc_6433_;
goto v_reusejp_6431_;
}
v_reusejp_6431_:
{
v___y_6418_ = v___y_6422_;
v___y_6419_ = v___x_6432_;
goto v___jp_6417_;
}
}
}
}
v___jp_6468_:
{
if (lean_obj_tag(v_N_6459_) == 0)
{
if (lean_obj_tag(v_A_6457_) == 0)
{
lean_object* v___x_6475_; 
v___x_6475_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6475_, 0, v___y_6473_);
lean_ctor_set(v___x_6475_, 1, v___y_6470_);
lean_ctor_set(v___x_6475_, 2, v___y_6471_);
lean_ctor_set(v___x_6475_, 3, v___y_6474_);
v___y_6422_ = v___y_6469_;
v___y_6423_ = v___y_6472_;
v___y_6424_ = v___x_6475_;
goto v___jp_6421_;
}
else
{
lean_object* v_val_6476_; lean_object* v___x_6477_; lean_object* v___x_6478_; lean_object* v___x_6479_; 
lean_dec(v___y_6474_);
lean_dec(v___y_6473_);
lean_dec(v___y_6471_);
lean_dec(v___y_6470_);
v_val_6476_ = lean_ctor_get(v_A_6457_, 0);
lean_inc(v_val_6476_);
lean_dec_ref_known(v_A_6457_, 1);
v___x_6477_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2);
v___x_6478_ = lean_int_mul(v_val_6476_, v___x_6477_);
lean_dec(v_val_6476_);
v___x_6479_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_6478_);
lean_dec(v___x_6478_);
v___y_6422_ = v___y_6469_;
v___y_6423_ = v___y_6472_;
v___y_6424_ = v___x_6479_;
goto v___jp_6421_;
}
}
else
{
lean_object* v_val_6480_; lean_object* v___x_6481_; 
lean_dec(v___y_6474_);
lean_dec(v___y_6473_);
lean_dec(v___y_6471_);
lean_dec(v___y_6470_);
lean_dec(v_A_6457_);
v_val_6480_ = lean_ctor_get(v_N_6459_, 0);
lean_inc(v_val_6480_);
lean_dec_ref_known(v_N_6459_, 1);
v___x_6481_ = l_Std_Time_PlainTime_ofNanoseconds(v_val_6480_);
lean_dec(v_val_6480_);
v___y_6422_ = v___y_6469_;
v___y_6423_ = v___y_6472_;
v___y_6424_ = v___x_6481_;
goto v___jp_6421_;
}
}
v___jp_6482_:
{
if (lean_obj_tag(v_n_6458_) == 0)
{
if (lean_obj_tag(v_S_6456_) == 0)
{
lean_object* v___x_6488_; 
v___x_6488_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6469_ = v___y_6484_;
v___y_6470_ = v___y_6483_;
v___y_6471_ = v___y_6487_;
v___y_6472_ = v___y_6486_;
v___y_6473_ = v___y_6485_;
v___y_6474_ = v___x_6488_;
goto v___jp_6468_;
}
else
{
lean_object* v_val_6489_; 
v_val_6489_ = lean_ctor_get(v_S_6456_, 0);
lean_inc(v_val_6489_);
lean_dec_ref_known(v_S_6456_, 1);
v___y_6469_ = v___y_6484_;
v___y_6470_ = v___y_6483_;
v___y_6471_ = v___y_6487_;
v___y_6472_ = v___y_6486_;
v___y_6473_ = v___y_6485_;
v___y_6474_ = v_val_6489_;
goto v___jp_6468_;
}
}
else
{
lean_object* v_val_6490_; 
lean_dec(v_S_6456_);
v_val_6490_ = lean_ctor_get(v_n_6458_, 0);
lean_inc(v_val_6490_);
lean_dec_ref_known(v_n_6458_, 1);
v___y_6469_ = v___y_6484_;
v___y_6470_ = v___y_6483_;
v___y_6471_ = v___y_6487_;
v___y_6472_ = v___y_6486_;
v___y_6473_ = v___y_6485_;
v___y_6474_ = v_val_6490_;
goto v___jp_6468_;
}
}
v___jp_6491_:
{
if (lean_obj_tag(v_s_6455_) == 0)
{
lean_object* v___x_6497_; lean_object* v___x_6498_; 
v___x_6497_ = lean_unsigned_to_nat(0u);
v___x_6498_ = l_Std_Time_Second_instOfNatOrdinal(v___y_6495_, v___x_6497_);
v___y_6483_ = v___y_6496_;
v___y_6484_ = v___y_6492_;
v___y_6485_ = v___y_6494_;
v___y_6486_ = v___y_6493_;
v___y_6487_ = v___x_6498_;
goto v___jp_6482_;
}
else
{
lean_object* v_val_6499_; 
v_val_6499_ = lean_ctor_get(v_s_6455_, 0);
lean_inc(v_val_6499_);
lean_dec_ref_known(v_s_6455_, 1);
v___y_6483_ = v___y_6496_;
v___y_6484_ = v___y_6492_;
v___y_6485_ = v___y_6494_;
v___y_6486_ = v___y_6493_;
v___y_6487_ = v_val_6499_;
goto v___jp_6482_;
}
}
v___jp_6500_:
{
if (lean_obj_tag(v_m_6454_) == 0)
{
lean_object* v___x_6505_; 
v___x_6505_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10);
v___y_6492_ = v___y_6501_;
v___y_6493_ = v___y_6502_;
v___y_6494_ = v___y_6504_;
v___y_6495_ = v___y_6503_;
v___y_6496_ = v___x_6505_;
goto v___jp_6491_;
}
else
{
lean_object* v_val_6506_; 
v_val_6506_ = lean_ctor_get(v_m_6454_, 0);
lean_inc(v_val_6506_);
lean_dec_ref_known(v_m_6454_, 1);
v___y_6492_ = v___y_6501_;
v___y_6493_ = v___y_6502_;
v___y_6494_ = v___y_6504_;
v___y_6495_ = v___y_6503_;
v___y_6496_ = v_val_6506_;
goto v___jp_6491_;
}
}
v___jp_6507_:
{
if (lean_obj_tag(v___y_6509_) == 0)
{
uint8_t v___x_6513_; lean_object* v___x_6514_; lean_object* v___x_6515_; 
v___x_6513_ = 0;
v___x_6514_ = lean_box(v___x_6513_);
v___x_6515_ = lean_apply_1(v___y_6511_, v___x_6514_);
if (lean_obj_tag(v___x_6515_) == 0)
{
lean_object* v___x_6516_; 
v___x_6516_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6501_ = v___y_6508_;
v___y_6502_ = v___y_6510_;
v___y_6503_ = v___y_6512_;
v___y_6504_ = v___x_6516_;
goto v___jp_6500_;
}
else
{
lean_object* v_val_6517_; 
v_val_6517_ = lean_ctor_get(v___x_6515_, 0);
lean_inc(v_val_6517_);
lean_dec_ref_known(v___x_6515_, 1);
v___y_6501_ = v___y_6508_;
v___y_6502_ = v___y_6510_;
v___y_6503_ = v___y_6512_;
v___y_6504_ = v_val_6517_;
goto v___jp_6500_;
}
}
else
{
lean_object* v_val_6518_; 
lean_dec_ref(v___y_6511_);
v_val_6518_ = lean_ctor_get(v___y_6509_, 0);
lean_inc(v_val_6518_);
lean_dec_ref_known(v___y_6509_, 1);
v___y_6501_ = v___y_6508_;
v___y_6502_ = v___y_6510_;
v___y_6503_ = v___y_6512_;
v___y_6504_ = v_val_6518_;
goto v___jp_6500_;
}
}
v___jp_6519_:
{
if (lean_obj_tag(v___y_6522_) == 0)
{
v___y_6508_ = v___y_6520_;
v___y_6509_ = v___y_6525_;
v___y_6510_ = v___y_6521_;
v___y_6511_ = v___y_6523_;
v___y_6512_ = v___y_6524_;
goto v___jp_6507_;
}
else
{
lean_object* v_val_6526_; lean_object* v___x_6527_; 
v_val_6526_ = lean_ctor_get(v___y_6522_, 0);
lean_inc(v_val_6526_);
lean_dec_ref_known(v___y_6522_, 1);
lean_inc_ref(v___y_6523_);
v___x_6527_ = lean_apply_1(v___y_6523_, v_val_6526_);
if (lean_obj_tag(v___x_6527_) == 0)
{
v___y_6508_ = v___y_6520_;
v___y_6509_ = v___y_6525_;
v___y_6510_ = v___y_6521_;
v___y_6511_ = v___y_6523_;
v___y_6512_ = v___y_6524_;
goto v___jp_6507_;
}
else
{
lean_object* v_val_6528_; 
lean_dec(v___y_6525_);
lean_dec_ref(v___y_6523_);
v_val_6528_ = lean_ctor_get(v___x_6527_, 0);
lean_inc(v_val_6528_);
lean_dec_ref_known(v___x_6527_, 1);
v___y_6501_ = v___y_6520_;
v___y_6502_ = v___y_6521_;
v___y_6503_ = v___y_6524_;
v___y_6504_ = v_val_6528_;
goto v___jp_6500_;
}
}
}
v___jp_6529_:
{
if (lean_obj_tag(v___y_6534_) == 0)
{
v___y_6520_ = v___y_6530_;
v___y_6521_ = v___y_6531_;
v___y_6522_ = v___y_6533_;
v___y_6523_ = v___y_6532_;
v___y_6524_ = v___y_6535_;
v___y_6525_ = v___y_6536_;
goto v___jp_6519_;
}
else
{
lean_dec(v___y_6536_);
v___y_6520_ = v___y_6530_;
v___y_6521_ = v___y_6531_;
v___y_6522_ = v___y_6533_;
v___y_6523_ = v___y_6532_;
v___y_6524_ = v___y_6535_;
v___y_6525_ = v___y_6534_;
goto v___jp_6519_;
}
}
v___jp_6537_:
{
if (lean_obj_tag(v___y_6543_) == 0)
{
v___y_6530_ = v___y_6538_;
v___y_6531_ = v___y_6539_;
v___y_6532_ = v___y_6541_;
v___y_6533_ = v___y_6544_;
v___y_6534_ = v___y_6540_;
v___y_6535_ = v___y_6542_;
v___y_6536_ = v___y_6543_;
goto v___jp_6529_;
}
else
{
lean_object* v_val_6545_; lean_object* v___x_6547_; uint8_t v_isShared_6548_; uint8_t v_isSharedCheck_6554_; 
v_val_6545_ = lean_ctor_get(v___y_6543_, 0);
v_isSharedCheck_6554_ = !lean_is_exclusive(v___y_6543_);
if (v_isSharedCheck_6554_ == 0)
{
v___x_6547_ = v___y_6543_;
v_isShared_6548_ = v_isSharedCheck_6554_;
goto v_resetjp_6546_;
}
else
{
lean_inc(v_val_6545_);
lean_dec(v___y_6543_);
v___x_6547_ = lean_box(0);
v_isShared_6548_ = v_isSharedCheck_6554_;
goto v_resetjp_6546_;
}
v_resetjp_6546_:
{
lean_object* v___x_6549_; lean_object* v___x_6550_; lean_object* v___x_6552_; 
v___x_6549_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11);
v___x_6550_ = lean_int_emod(v_val_6545_, v___x_6549_);
lean_dec(v_val_6545_);
if (v_isShared_6548_ == 0)
{
lean_ctor_set(v___x_6547_, 0, v___x_6550_);
v___x_6552_ = v___x_6547_;
goto v_reusejp_6551_;
}
else
{
lean_object* v_reuseFailAlloc_6553_; 
v_reuseFailAlloc_6553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6553_, 0, v___x_6550_);
v___x_6552_ = v_reuseFailAlloc_6553_;
goto v_reusejp_6551_;
}
v_reusejp_6551_:
{
v___y_6530_ = v___y_6538_;
v___y_6531_ = v___y_6539_;
v___y_6532_ = v___y_6541_;
v___y_6533_ = v___y_6544_;
v___y_6534_ = v___y_6540_;
v___y_6535_ = v___y_6542_;
v___y_6536_ = v___x_6552_;
goto v___jp_6529_;
}
}
}
}
v___jp_6555_:
{
if (lean_obj_tag(v___y_6559_) == 0)
{
lean_dec(v___y_6564_);
v___y_6538_ = v___y_6556_;
v___y_6539_ = v___y_6558_;
v___y_6540_ = v___y_6561_;
v___y_6541_ = v___y_6560_;
v___y_6542_ = v___y_6562_;
v___y_6543_ = v___y_6563_;
v___y_6544_ = v___y_6557_;
goto v___jp_6537_;
}
else
{
lean_object* v_val_6565_; lean_object* v___x_6567_; uint8_t v_isShared_6568_; uint8_t v_isSharedCheck_6575_; 
lean_dec(v___y_6557_);
v_val_6565_ = lean_ctor_get(v___y_6559_, 0);
v_isSharedCheck_6575_ = !lean_is_exclusive(v___y_6559_);
if (v_isSharedCheck_6575_ == 0)
{
v___x_6567_ = v___y_6559_;
v_isShared_6568_ = v_isSharedCheck_6575_;
goto v_resetjp_6566_;
}
else
{
lean_inc(v_val_6565_);
lean_dec(v___y_6559_);
v___x_6567_ = lean_box(0);
v_isShared_6568_ = v_isSharedCheck_6575_;
goto v_resetjp_6566_;
}
v_resetjp_6566_:
{
uint8_t v___x_6569_; uint8_t v___x_6570_; lean_object* v___x_6571_; lean_object* v___x_6573_; 
v___x_6569_ = lean_unbox(v_val_6565_);
lean_dec(v_val_6565_);
v___x_6570_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v___y_6564_, v___x_6569_);
lean_dec(v___y_6564_);
v___x_6571_ = lean_box(v___x_6570_);
if (v_isShared_6568_ == 0)
{
lean_ctor_set(v___x_6567_, 0, v___x_6571_);
v___x_6573_ = v___x_6567_;
goto v_reusejp_6572_;
}
else
{
lean_object* v_reuseFailAlloc_6574_; 
v_reuseFailAlloc_6574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6574_, 0, v___x_6571_);
v___x_6573_ = v_reuseFailAlloc_6574_;
goto v_reusejp_6572_;
}
v_reusejp_6572_:
{
v___y_6538_ = v___y_6556_;
v___y_6539_ = v___y_6558_;
v___y_6540_ = v___y_6561_;
v___y_6541_ = v___y_6560_;
v___y_6542_ = v___y_6562_;
v___y_6543_ = v___y_6563_;
v___y_6544_ = v___x_6573_;
goto v___jp_6537_;
}
}
}
}
v___jp_6576_:
{
if (lean_obj_tag(v___y_6579_) == 0)
{
if (lean_obj_tag(v___y_6578_) == 0)
{
if (lean_obj_tag(v___y_6586_) == 0)
{
lean_object* v___x_6587_; 
v___x_6587_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6556_ = v___y_6577_;
v___y_6557_ = v___y_6579_;
v___y_6558_ = v___y_6580_;
v___y_6559_ = v___y_6581_;
v___y_6560_ = v___y_6583_;
v___y_6561_ = v___y_6582_;
v___y_6562_ = v___y_6584_;
v___y_6563_ = v___y_6585_;
v___y_6564_ = v___x_6587_;
goto v___jp_6555_;
}
else
{
lean_object* v_val_6588_; 
v_val_6588_ = lean_ctor_get(v___y_6586_, 0);
lean_inc(v_val_6588_);
lean_dec_ref_known(v___y_6586_, 1);
v___y_6556_ = v___y_6577_;
v___y_6557_ = v___y_6579_;
v___y_6558_ = v___y_6580_;
v___y_6559_ = v___y_6581_;
v___y_6560_ = v___y_6583_;
v___y_6561_ = v___y_6582_;
v___y_6562_ = v___y_6584_;
v___y_6563_ = v___y_6585_;
v___y_6564_ = v_val_6588_;
goto v___jp_6555_;
}
}
else
{
lean_object* v_val_6589_; lean_object* v___x_6591_; uint8_t v_isShared_6592_; uint8_t v_isSharedCheck_6599_; 
lean_dec(v___y_6586_);
lean_dec(v___y_6581_);
v_val_6589_ = lean_ctor_get(v___y_6578_, 0);
v_isSharedCheck_6599_ = !lean_is_exclusive(v___y_6578_);
if (v_isSharedCheck_6599_ == 0)
{
v___x_6591_ = v___y_6578_;
v_isShared_6592_ = v_isSharedCheck_6599_;
goto v_resetjp_6590_;
}
else
{
lean_inc(v_val_6589_);
lean_dec(v___y_6578_);
v___x_6591_ = lean_box(0);
v_isShared_6592_ = v_isSharedCheck_6599_;
goto v_resetjp_6590_;
}
v_resetjp_6590_:
{
uint8_t v___x_6593_; uint8_t v___x_6594_; lean_object* v___x_6595_; lean_object* v___x_6597_; 
v___x_6593_ = lean_unbox(v_val_6589_);
lean_dec(v_val_6589_);
v___x_6594_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v___x_6593_);
v___x_6595_ = lean_box(v___x_6594_);
if (v_isShared_6592_ == 0)
{
lean_ctor_set(v___x_6591_, 0, v___x_6595_);
v___x_6597_ = v___x_6591_;
goto v_reusejp_6596_;
}
else
{
lean_object* v_reuseFailAlloc_6598_; 
v_reuseFailAlloc_6598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6598_, 0, v___x_6595_);
v___x_6597_ = v_reuseFailAlloc_6598_;
goto v_reusejp_6596_;
}
v_reusejp_6596_:
{
v___y_6538_ = v___y_6577_;
v___y_6539_ = v___y_6580_;
v___y_6540_ = v___y_6582_;
v___y_6541_ = v___y_6583_;
v___y_6542_ = v___y_6584_;
v___y_6543_ = v___y_6585_;
v___y_6544_ = v___x_6597_;
goto v___jp_6537_;
}
}
}
}
else
{
lean_dec(v___y_6586_);
lean_dec(v___y_6581_);
lean_dec(v___y_6578_);
v___y_6538_ = v___y_6577_;
v___y_6539_ = v___y_6580_;
v___y_6540_ = v___y_6582_;
v___y_6541_ = v___y_6583_;
v___y_6542_ = v___y_6584_;
v___y_6543_ = v___y_6585_;
v___y_6544_ = v___y_6579_;
goto v___jp_6537_;
}
}
v___jp_6600_:
{
lean_object* v_ofHalfDay_6604_; 
lean_inc(v_K_6451_);
lean_inc(v_h_6450_);
v_ofHalfDay_6604_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__2___boxed), 3, 2);
lean_closure_set(v_ofHalfDay_6604_, 0, v_h_6450_);
lean_closure_set(v_ofHalfDay_6604_, 1, v_K_6451_);
if (lean_obj_tag(v_h_6450_) == 0)
{
if (lean_obj_tag(v_K_6451_) == 0)
{
lean_object* v___x_6605_; 
v___x_6605_ = lean_box(0);
v___y_6577_ = v___y_6601_;
v___y_6578_ = v_b_6448_;
v___y_6579_ = v_a_6447_;
v___y_6580_ = v___y_6603_;
v___y_6581_ = v_B_6449_;
v___y_6582_ = v_H_6453_;
v___y_6583_ = v_ofHalfDay_6604_;
v___y_6584_ = v___y_6602_;
v___y_6585_ = v_k_6452_;
v___y_6586_ = v___x_6605_;
goto v___jp_6576_;
}
else
{
lean_object* v_val_6606_; lean_object* v___x_6608_; uint8_t v_isShared_6609_; uint8_t v_isSharedCheck_6613_; 
v_val_6606_ = lean_ctor_get(v_K_6451_, 0);
v_isSharedCheck_6613_ = !lean_is_exclusive(v_K_6451_);
if (v_isSharedCheck_6613_ == 0)
{
v___x_6608_ = v_K_6451_;
v_isShared_6609_ = v_isSharedCheck_6613_;
goto v_resetjp_6607_;
}
else
{
lean_inc(v_val_6606_);
lean_dec(v_K_6451_);
v___x_6608_ = lean_box(0);
v_isShared_6609_ = v_isSharedCheck_6613_;
goto v_resetjp_6607_;
}
v_resetjp_6607_:
{
lean_object* v___x_6611_; 
if (v_isShared_6609_ == 0)
{
v___x_6611_ = v___x_6608_;
goto v_reusejp_6610_;
}
else
{
lean_object* v_reuseFailAlloc_6612_; 
v_reuseFailAlloc_6612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6612_, 0, v_val_6606_);
v___x_6611_ = v_reuseFailAlloc_6612_;
goto v_reusejp_6610_;
}
v_reusejp_6610_:
{
v___y_6577_ = v___y_6601_;
v___y_6578_ = v_b_6448_;
v___y_6579_ = v_a_6447_;
v___y_6580_ = v___y_6603_;
v___y_6581_ = v_B_6449_;
v___y_6582_ = v_H_6453_;
v___y_6583_ = v_ofHalfDay_6604_;
v___y_6584_ = v___y_6602_;
v___y_6585_ = v_k_6452_;
v___y_6586_ = v___x_6611_;
goto v___jp_6576_;
}
}
}
}
else
{
lean_object* v_val_6614_; lean_object* v___x_6616_; uint8_t v_isShared_6617_; uint8_t v_isSharedCheck_6623_; 
lean_dec(v_K_6451_);
v_val_6614_ = lean_ctor_get(v_h_6450_, 0);
v_isSharedCheck_6623_ = !lean_is_exclusive(v_h_6450_);
if (v_isSharedCheck_6623_ == 0)
{
v___x_6616_ = v_h_6450_;
v_isShared_6617_ = v_isSharedCheck_6623_;
goto v_resetjp_6615_;
}
else
{
lean_inc(v_val_6614_);
lean_dec(v_h_6450_);
v___x_6616_ = lean_box(0);
v_isShared_6617_ = v_isSharedCheck_6623_;
goto v_resetjp_6615_;
}
v_resetjp_6615_:
{
lean_object* v___x_6618_; lean_object* v___x_6619_; lean_object* v___x_6621_; 
v___x_6618_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_6619_ = lean_int_emod(v_val_6614_, v___x_6618_);
lean_dec(v_val_6614_);
if (v_isShared_6617_ == 0)
{
lean_ctor_set(v___x_6616_, 0, v___x_6619_);
v___x_6621_ = v___x_6616_;
goto v_reusejp_6620_;
}
else
{
lean_object* v_reuseFailAlloc_6622_; 
v_reuseFailAlloc_6622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6622_, 0, v___x_6619_);
v___x_6621_ = v_reuseFailAlloc_6622_;
goto v_reusejp_6620_;
}
v_reusejp_6620_:
{
v___y_6577_ = v___y_6601_;
v___y_6578_ = v_b_6448_;
v___y_6579_ = v_a_6447_;
v___y_6580_ = v___y_6603_;
v___y_6581_ = v_B_6449_;
v___y_6582_ = v_H_6453_;
v___y_6583_ = v_ofHalfDay_6604_;
v___y_6584_ = v___y_6602_;
v___y_6585_ = v_k_6452_;
v___y_6586_ = v___x_6621_;
goto v___jp_6576_;
}
}
}
}
v___jp_6624_:
{
if (lean_obj_tag(v___y_6626_) == 0)
{
lean_object* v___x_6630_; lean_object* v___x_6631_; 
v___x_6630_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19);
v___x_6631_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekDate(v_dateformat_6376_, v___y_6627_, v___x_6630_, v___y_6629_);
v___y_6601_ = v___y_6625_;
v___y_6602_ = v___y_6628_;
v___y_6603_ = v___x_6631_;
goto v___jp_6600_;
}
else
{
lean_object* v_val_6632_; lean_object* v___x_6633_; 
v_val_6632_ = lean_ctor_get(v___y_6626_, 0);
lean_inc(v_val_6632_);
lean_dec_ref_known(v___y_6626_, 1);
v___x_6633_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekDate(v_dateformat_6376_, v___y_6627_, v_val_6632_, v___y_6629_);
lean_dec(v_val_6632_);
v___y_6601_ = v___y_6625_;
v___y_6602_ = v___y_6628_;
v___y_6603_ = v___x_6633_;
goto v___jp_6600_;
}
}
v___jp_6634_:
{
lean_object* v_val_6640_; lean_object* v_fst_6641_; lean_object* v_snd_6642_; lean_object* v___x_6643_; lean_object* v___x_6644_; 
v_val_6640_ = l_Std_Time_ValidDate_ofOrdinal(v___y_6639_, v___y_6638_);
lean_dec(v___y_6638_);
v_fst_6641_ = lean_ctor_get(v_val_6640_, 0);
lean_inc(v_fst_6641_);
v_snd_6642_ = lean_ctor_get(v_val_6640_, 1);
lean_inc(v_snd_6642_);
lean_dec_ref(v_val_6640_);
v___x_6643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6643_, 0, v___y_6636_);
lean_ctor_set(v___x_6643_, 1, v_fst_6641_);
lean_ctor_set(v___x_6643_, 2, v_snd_6642_);
v___x_6644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6644_, 0, v___x_6643_);
v___y_6601_ = v___y_6635_;
v___y_6602_ = v___y_6637_;
v___y_6603_ = v___x_6644_;
goto v___jp_6600_;
}
v___jp_6645_:
{
uint8_t v___x_6652_; 
v___x_6652_ = lean_int_dec_le(v___y_6647_, v___y_6650_);
if (v___x_6652_ == 0)
{
lean_object* v___x_6653_; 
lean_dec(v___y_6651_);
lean_dec(v___y_6650_);
lean_dec(v___y_6648_);
v___x_6653_ = lean_box(0);
v___y_6601_ = v___y_6646_;
v___y_6602_ = v___y_6649_;
v___y_6603_ = v___x_6653_;
goto v___jp_6600_;
}
else
{
lean_object* v___x_6654_; uint8_t v___x_6655_; 
v___x_6654_ = lean_nat_to_int(v___y_6651_);
v___x_6655_ = lean_int_dec_le(v___y_6650_, v___x_6654_);
lean_dec(v___x_6654_);
if (v___x_6655_ == 0)
{
lean_object* v___x_6656_; 
lean_dec(v___y_6650_);
lean_dec(v___y_6648_);
v___x_6656_ = lean_box(0);
v___y_6601_ = v___y_6646_;
v___y_6602_ = v___y_6649_;
v___y_6603_ = v___x_6656_;
goto v___jp_6600_;
}
else
{
lean_object* v___x_6657_; lean_object* v___x_6658_; lean_object* v___x_6659_; uint8_t v___x_6660_; 
v___x_6657_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0);
v___x_6658_ = lean_int_mod(v___y_6648_, v___x_6657_);
v___x_6659_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6660_ = lean_int_dec_eq(v___x_6658_, v___x_6659_);
lean_dec(v___x_6658_);
if (v___x_6660_ == 0)
{
v___y_6635_ = v___y_6646_;
v___y_6636_ = v___y_6648_;
v___y_6637_ = v___y_6649_;
v___y_6638_ = v___y_6650_;
v___y_6639_ = v___x_6660_;
goto v___jp_6634_;
}
else
{
lean_object* v___x_6661_; lean_object* v___x_6662_; uint8_t v___x_6663_; 
v___x_6661_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_6662_ = lean_int_mod(v___y_6648_, v___x_6661_);
v___x_6663_ = lean_int_dec_eq(v___x_6662_, v___x_6659_);
lean_dec(v___x_6662_);
if (v___x_6663_ == 0)
{
v___y_6635_ = v___y_6646_;
v___y_6636_ = v___y_6648_;
v___y_6637_ = v___y_6649_;
v___y_6638_ = v___y_6650_;
v___y_6639_ = v___x_6660_;
goto v___jp_6634_;
}
else
{
lean_object* v___x_6664_; lean_object* v___x_6665_; uint8_t v___x_6666_; 
v___x_6664_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1);
v___x_6665_ = lean_int_mod(v___y_6648_, v___x_6664_);
v___x_6666_ = lean_int_dec_eq(v___x_6665_, v___x_6659_);
lean_dec(v___x_6665_);
v___y_6635_ = v___y_6646_;
v___y_6636_ = v___y_6648_;
v___y_6637_ = v___y_6649_;
v___y_6638_ = v___y_6650_;
v___y_6639_ = v___x_6666_;
goto v___jp_6634_;
}
}
}
}
}
v___jp_6667_:
{
lean_object* v___x_6673_; 
v___x_6673_ = lean_unsigned_to_nat(365u);
v___y_6646_ = v___y_6668_;
v___y_6647_ = v___y_6669_;
v___y_6648_ = v___y_6670_;
v___y_6649_ = v___y_6671_;
v___y_6650_ = v___y_6672_;
v___y_6651_ = v___x_6673_;
goto v___jp_6645_;
}
v___jp_6674_:
{
lean_object* v___x_6680_; 
v___x_6680_ = lean_unsigned_to_nat(366u);
v___y_6646_ = v___y_6675_;
v___y_6647_ = v___y_6676_;
v___y_6648_ = v___y_6677_;
v___y_6649_ = v___y_6678_;
v___y_6650_ = v___y_6679_;
v___y_6651_ = v___x_6680_;
goto v___jp_6645_;
}
v___jp_6681_:
{
lean_object* v___x_6686_; lean_object* v___x_6687_; lean_object* v___x_6688_; lean_object* v___x_6689_; uint8_t v___x_6690_; 
v___x_6686_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6687_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0);
v___x_6688_ = lean_int_mod(v___y_6685_, v___x_6687_);
v___x_6689_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6690_ = lean_int_dec_eq(v___x_6688_, v___x_6689_);
lean_dec(v___x_6688_);
if (v___x_6690_ == 0)
{
v___y_6668_ = v___y_6682_;
v___y_6669_ = v___x_6686_;
v___y_6670_ = v___y_6685_;
v___y_6671_ = v___y_6683_;
v___y_6672_ = v___y_6684_;
goto v___jp_6667_;
}
else
{
lean_object* v___x_6691_; lean_object* v___x_6692_; uint8_t v___x_6693_; 
v___x_6691_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_6692_ = lean_int_mod(v___y_6685_, v___x_6691_);
v___x_6693_ = lean_int_dec_eq(v___x_6692_, v___x_6689_);
lean_dec(v___x_6692_);
if (v___x_6693_ == 0)
{
v___y_6675_ = v___y_6682_;
v___y_6676_ = v___x_6686_;
v___y_6677_ = v___y_6685_;
v___y_6678_ = v___y_6683_;
v___y_6679_ = v___y_6684_;
goto v___jp_6674_;
}
else
{
lean_object* v___x_6694_; lean_object* v___x_6695_; uint8_t v___x_6696_; 
v___x_6694_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1);
v___x_6695_ = lean_int_mod(v___y_6685_, v___x_6694_);
v___x_6696_ = lean_int_dec_eq(v___x_6695_, v___x_6689_);
lean_dec(v___x_6695_);
if (v___x_6696_ == 0)
{
v___y_6668_ = v___y_6682_;
v___y_6669_ = v___x_6686_;
v___y_6670_ = v___y_6685_;
v___y_6671_ = v___y_6683_;
v___y_6672_ = v___y_6684_;
goto v___jp_6667_;
}
else
{
v___y_6675_ = v___y_6682_;
v___y_6676_ = v___x_6686_;
v___y_6677_ = v___y_6685_;
v___y_6678_ = v___y_6683_;
v___y_6679_ = v___y_6684_;
goto v___jp_6674_;
}
}
}
}
v___jp_6697_:
{
lean_object* v___x_6704_; uint8_t v___x_6705_; 
v___x_6704_ = l_Std_Time_Month_Ordinal_days(v___y_6703_, v___y_6701_);
v___x_6705_ = lean_int_dec_le(v___y_6699_, v___x_6704_);
lean_dec(v___x_6704_);
if (v___x_6705_ == 0)
{
lean_object* v___x_6706_; 
lean_dec(v___y_6701_);
lean_dec(v___y_6700_);
lean_dec(v___y_6699_);
v___x_6706_ = lean_box(0);
v___y_6601_ = v___y_6698_;
v___y_6602_ = v___y_6702_;
v___y_6603_ = v___x_6706_;
goto v___jp_6600_;
}
else
{
lean_object* v___x_6707_; lean_object* v___x_6708_; 
v___x_6707_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6707_, 0, v___y_6700_);
lean_ctor_set(v___x_6707_, 1, v___y_6701_);
lean_ctor_set(v___x_6707_, 2, v___y_6699_);
v___x_6708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6708_, 0, v___x_6707_);
v___y_6601_ = v___y_6698_;
v___y_6602_ = v___y_6702_;
v___y_6603_ = v___x_6708_;
goto v___jp_6600_;
}
}
v___jp_6709_:
{
lean_object* v___x_6715_; lean_object* v___x_6716_; lean_object* v___x_6717_; uint8_t v___x_6718_; 
v___x_6715_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__0);
v___x_6716_ = lean_int_mod(v___y_6714_, v___x_6715_);
v___x_6717_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6718_ = lean_int_dec_eq(v___x_6716_, v___x_6717_);
lean_dec(v___x_6716_);
if (v___x_6718_ == 0)
{
v___y_6698_ = v___y_6710_;
v___y_6699_ = v___y_6711_;
v___y_6700_ = v___y_6714_;
v___y_6701_ = v___y_6712_;
v___y_6702_ = v___y_6713_;
v___y_6703_ = v___x_6718_;
goto v___jp_6697_;
}
else
{
lean_object* v___x_6719_; lean_object* v___x_6720_; uint8_t v___x_6721_; 
v___x_6719_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_6720_ = lean_int_mod(v___y_6714_, v___x_6719_);
v___x_6721_ = lean_int_dec_eq(v___x_6720_, v___x_6717_);
lean_dec(v___x_6720_);
if (v___x_6721_ == 0)
{
v___y_6698_ = v___y_6710_;
v___y_6699_ = v___y_6711_;
v___y_6700_ = v___y_6714_;
v___y_6701_ = v___y_6712_;
v___y_6702_ = v___y_6713_;
v___y_6703_ = v___x_6718_;
goto v___jp_6697_;
}
else
{
lean_object* v___x_6722_; lean_object* v___x_6723_; uint8_t v___x_6724_; 
v___x_6722_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___closed__1);
v___x_6723_ = lean_int_mod(v___y_6714_, v___x_6722_);
v___x_6724_ = lean_int_dec_eq(v___x_6723_, v___x_6717_);
lean_dec(v___x_6723_);
v___y_6698_ = v___y_6710_;
v___y_6699_ = v___y_6711_;
v___y_6700_ = v___y_6714_;
v___y_6701_ = v___y_6712_;
v___y_6702_ = v___y_6713_;
v___y_6703_ = v___x_6724_;
goto v___jp_6697_;
}
}
}
v___jp_6725_:
{
lean_object* v___x_6730_; 
v___x_6730_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6710_ = v___y_6726_;
v___y_6711_ = v___y_6727_;
v___y_6712_ = v___y_6728_;
v___y_6713_ = v___y_6729_;
v___y_6714_ = v___x_6730_;
goto v___jp_6709_;
}
v___jp_6731_:
{
if (lean_obj_tag(v___y_6733_) == 0)
{
if (lean_obj_tag(v_Y_6438_) == 1)
{
lean_object* v_val_6737_; lean_object* v___x_6738_; 
v_val_6737_ = lean_ctor_get(v_Y_6438_, 0);
lean_inc(v_val_6737_);
lean_dec_ref_known(v_Y_6438_, 1);
v___x_6738_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_ofWeekYearMonthDay(v_dateformat_6376_, v_val_6737_, v___y_6734_, v___y_6736_);
v___y_6601_ = v___y_6732_;
v___y_6602_ = v___y_6735_;
v___y_6603_ = v___x_6738_;
goto v___jp_6600_;
}
else
{
lean_dec(v_Y_6438_);
v___y_6726_ = v___y_6732_;
v___y_6727_ = v___y_6736_;
v___y_6728_ = v___y_6734_;
v___y_6729_ = v___y_6735_;
goto v___jp_6725_;
}
}
else
{
lean_dec(v_Y_6438_);
if (lean_obj_tag(v___y_6733_) == 0)
{
v___y_6726_ = v___y_6732_;
v___y_6727_ = v___y_6736_;
v___y_6728_ = v___y_6734_;
v___y_6729_ = v___y_6735_;
goto v___jp_6725_;
}
else
{
lean_object* v_val_6739_; 
v_val_6739_ = lean_ctor_get(v___y_6733_, 0);
lean_inc(v_val_6739_);
lean_dec_ref_known(v___y_6733_, 1);
v___y_6710_ = v___y_6732_;
v___y_6711_ = v___y_6736_;
v___y_6712_ = v___y_6734_;
v___y_6713_ = v___y_6735_;
v___y_6714_ = v_val_6739_;
goto v___jp_6709_;
}
}
}
v___jp_6740_:
{
if (lean_obj_tag(v_d_6442_) == 0)
{
lean_object* v___x_6745_; 
v___x_6745_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__16);
v___y_6732_ = v___y_6741_;
v___y_6733_ = v___y_6742_;
v___y_6734_ = v___y_6744_;
v___y_6735_ = v___y_6743_;
v___y_6736_ = v___x_6745_;
goto v___jp_6731_;
}
else
{
lean_object* v_val_6746_; 
v_val_6746_ = lean_ctor_get(v_d_6442_, 0);
lean_inc(v_val_6746_);
lean_dec_ref_known(v_d_6442_, 1);
v___y_6732_ = v___y_6741_;
v___y_6733_ = v___y_6742_;
v___y_6734_ = v___y_6744_;
v___y_6735_ = v___y_6743_;
v___y_6736_ = v_val_6746_;
goto v___jp_6731_;
}
}
v___jp_6747_:
{
lean_object* v___x_6751_; 
v___x_6751_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___closed__8);
v___y_6741_ = v___y_6748_;
v___y_6742_ = v___y_6749_;
v___y_6743_ = v___y_6750_;
v___y_6744_ = v___x_6751_;
goto v___jp_6740_;
}
v___jp_6752_:
{
uint8_t v___x_6756_; 
v___x_6756_ = 1;
v___y_6741_ = v___y_6753_;
v___y_6742_ = v___y_6755_;
v___y_6743_ = v___x_6756_;
v___y_6744_ = v_val_6754_;
goto v___jp_6740_;
}
v___jp_6757_:
{
if (lean_obj_tag(v_M_6440_) == 0)
{
if (lean_obj_tag(v_L_6441_) == 0)
{
uint8_t v___x_6761_; 
v___x_6761_ = 1;
if (lean_obj_tag(v_d_6442_) == 0)
{
if (lean_obj_tag(v_D_6439_) == 1)
{
lean_object* v_val_6762_; 
lean_dec(v_c_6446_);
lean_dec(v_e_6445_);
lean_dec(v_E_6444_);
lean_dec(v_w_6443_);
lean_dec(v_Y_6438_);
v_val_6762_ = lean_ctor_get(v_D_6439_, 0);
lean_inc(v_val_6762_);
lean_dec_ref_known(v_D_6439_, 1);
if (lean_obj_tag(v___y_6760_) == 0)
{
lean_object* v_snd_6763_; lean_object* v___x_6764_; 
v_snd_6763_ = lean_ctor_get(v_val_6762_, 1);
lean_inc(v_snd_6763_);
lean_dec(v_val_6762_);
v___x_6764_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6682_ = v___y_6758_;
v___y_6683_ = v___x_6761_;
v___y_6684_ = v_snd_6763_;
v___y_6685_ = v___x_6764_;
goto v___jp_6681_;
}
else
{
lean_object* v_snd_6765_; lean_object* v_val_6766_; 
v_snd_6765_ = lean_ctor_get(v_val_6762_, 1);
lean_inc(v_snd_6765_);
lean_dec(v_val_6762_);
v_val_6766_ = lean_ctor_get(v___y_6760_, 0);
lean_inc(v_val_6766_);
lean_dec_ref_known(v___y_6760_, 1);
v___y_6682_ = v___y_6758_;
v___y_6683_ = v___x_6761_;
v___y_6684_ = v_snd_6765_;
v___y_6685_ = v_val_6766_;
goto v___jp_6681_;
}
}
else
{
lean_dec(v_D_6439_);
if (lean_obj_tag(v___y_6760_) == 0)
{
if (lean_obj_tag(v_Y_6438_) == 1)
{
if (lean_obj_tag(v_e_6445_) == 0)
{
if (lean_obj_tag(v_c_6446_) == 0)
{
if (lean_obj_tag(v_E_6444_) == 0)
{
lean_object* v_val_6767_; uint8_t v_firstDayOfWeek_6768_; 
v_val_6767_ = lean_ctor_get(v_Y_6438_, 0);
lean_inc(v_val_6767_);
lean_dec_ref_known(v_Y_6438_, 1);
v_firstDayOfWeek_6768_ = lean_ctor_get_uint8(v_dateformat_6376_, sizeof(void*)*2);
v___y_6625_ = v___y_6758_;
v___y_6626_ = v_w_6443_;
v___y_6627_ = v_val_6767_;
v___y_6628_ = v___x_6761_;
v___y_6629_ = v_firstDayOfWeek_6768_;
goto v___jp_6624_;
}
else
{
lean_object* v_val_6769_; lean_object* v_val_6770_; uint8_t v___x_6771_; 
v_val_6769_ = lean_ctor_get(v_Y_6438_, 0);
lean_inc(v_val_6769_);
lean_dec_ref_known(v_Y_6438_, 1);
v_val_6770_ = lean_ctor_get(v_E_6444_, 0);
lean_inc(v_val_6770_);
lean_dec_ref_known(v_E_6444_, 1);
v___x_6771_ = lean_unbox(v_val_6770_);
lean_dec(v_val_6770_);
v___y_6625_ = v___y_6758_;
v___y_6626_ = v_w_6443_;
v___y_6627_ = v_val_6769_;
v___y_6628_ = v___x_6761_;
v___y_6629_ = v___x_6771_;
goto v___jp_6624_;
}
}
else
{
lean_object* v_val_6772_; lean_object* v_val_6773_; uint8_t v___x_6774_; 
lean_dec(v_E_6444_);
v_val_6772_ = lean_ctor_get(v_Y_6438_, 0);
lean_inc(v_val_6772_);
lean_dec_ref_known(v_Y_6438_, 1);
v_val_6773_ = lean_ctor_get(v_c_6446_, 0);
lean_inc(v_val_6773_);
lean_dec_ref_known(v_c_6446_, 1);
v___x_6774_ = lean_unbox(v_val_6773_);
lean_dec(v_val_6773_);
v___y_6625_ = v___y_6758_;
v___y_6626_ = v_w_6443_;
v___y_6627_ = v_val_6772_;
v___y_6628_ = v___x_6761_;
v___y_6629_ = v___x_6774_;
goto v___jp_6624_;
}
}
else
{
lean_object* v_val_6775_; lean_object* v_val_6776_; uint8_t v___x_6777_; 
lean_dec(v_c_6446_);
lean_dec(v_E_6444_);
v_val_6775_ = lean_ctor_get(v_Y_6438_, 0);
lean_inc(v_val_6775_);
lean_dec_ref_known(v_Y_6438_, 1);
v_val_6776_ = lean_ctor_get(v_e_6445_, 0);
lean_inc(v_val_6776_);
lean_dec_ref_known(v_e_6445_, 1);
v___x_6777_ = lean_unbox(v_val_6776_);
lean_dec(v_val_6776_);
v___y_6625_ = v___y_6758_;
v___y_6626_ = v_w_6443_;
v___y_6627_ = v_val_6775_;
v___y_6628_ = v___x_6761_;
v___y_6629_ = v___x_6777_;
goto v___jp_6624_;
}
}
else
{
lean_object* v___x_6778_; 
lean_dec(v_c_6446_);
lean_dec(v_e_6445_);
lean_dec(v_E_6444_);
lean_dec(v_w_6443_);
v___x_6778_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(v___y_6760_, v_Y_6438_);
lean_dec(v_Y_6438_);
v___y_6601_ = v___y_6758_;
v___y_6602_ = v___x_6761_;
v___y_6603_ = v___x_6778_;
goto v___jp_6600_;
}
}
else
{
lean_object* v___x_6779_; 
lean_dec(v_c_6446_);
lean_dec(v_e_6445_);
lean_dec(v_E_6444_);
lean_dec(v_w_6443_);
v___x_6779_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(v___y_6760_, v_Y_6438_);
lean_dec(v_Y_6438_);
v___y_6601_ = v___y_6758_;
v___y_6602_ = v___x_6761_;
v___y_6603_ = v___x_6779_;
goto v___jp_6600_;
}
}
}
else
{
lean_dec(v_c_6446_);
lean_dec(v_e_6445_);
lean_dec(v_E_6444_);
lean_dec(v_w_6443_);
lean_dec(v_D_6439_);
v___y_6748_ = v___y_6758_;
v___y_6749_ = v___y_6760_;
v___y_6750_ = v___x_6761_;
goto v___jp_6747_;
}
}
else
{
lean_object* v_val_6780_; 
lean_dec(v_c_6446_);
lean_dec(v_e_6445_);
lean_dec(v_E_6444_);
lean_dec(v_w_6443_);
lean_dec(v_D_6439_);
v_val_6780_ = lean_ctor_get(v_L_6441_, 0);
lean_inc(v_val_6780_);
lean_dec_ref_known(v_L_6441_, 1);
v___y_6753_ = v___y_6758_;
v_val_6754_ = v_val_6780_;
v___y_6755_ = v___y_6760_;
goto v___jp_6752_;
}
}
else
{
lean_object* v_val_6781_; 
lean_dec(v_c_6446_);
lean_dec(v_e_6445_);
lean_dec(v_E_6444_);
lean_dec(v_w_6443_);
lean_dec(v_L_6441_);
lean_dec(v_D_6439_);
v_val_6781_ = lean_ctor_get(v_M_6440_, 0);
lean_inc(v_val_6781_);
lean_dec_ref_known(v_M_6440_, 1);
v___y_6753_ = v___y_6758_;
v_val_6754_ = v_val_6781_;
v___y_6755_ = v___y_6760_;
goto v___jp_6752_;
}
}
v___jp_6782_:
{
uint8_t v___x_6786_; lean_object* v_tz_6787_; 
v___x_6786_ = 0;
v_tz_6787_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_tz_6787_, 0, v___y_6783_);
lean_ctor_set(v_tz_6787_, 1, v___y_6784_);
lean_ctor_set(v_tz_6787_, 2, v___y_6785_);
lean_ctor_set_uint8(v_tz_6787_, sizeof(void*)*3, v___x_6786_);
if (lean_obj_tag(v_u_6437_) == 0)
{
if (lean_obj_tag(v_y_6436_) == 0)
{
lean_dec(v_G_6435_);
v___y_6758_ = v_tz_6787_;
v___y_6759_ = v___x_6786_;
v___y_6760_ = v_y_6436_;
goto v___jp_6757_;
}
else
{
if (lean_obj_tag(v_G_6435_) == 0)
{
lean_object* v_val_6788_; lean_object* v___x_6790_; uint8_t v_isShared_6791_; uint8_t v_isSharedCheck_6797_; 
v_val_6788_ = lean_ctor_get(v_y_6436_, 0);
v_isSharedCheck_6797_ = !lean_is_exclusive(v_y_6436_);
if (v_isSharedCheck_6797_ == 0)
{
v___x_6790_ = v_y_6436_;
v_isShared_6791_ = v_isSharedCheck_6797_;
goto v_resetjp_6789_;
}
else
{
lean_inc(v_val_6788_);
lean_dec(v_y_6436_);
v___x_6790_ = lean_box(0);
v_isShared_6791_ = v_isSharedCheck_6797_;
goto v_resetjp_6789_;
}
v_resetjp_6789_:
{
uint8_t v___x_6792_; lean_object* v___x_6793_; lean_object* v___x_6795_; 
v___x_6792_ = 1;
v___x_6793_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_val_6788_, v___x_6792_);
lean_dec(v_val_6788_);
if (v_isShared_6791_ == 0)
{
lean_ctor_set(v___x_6790_, 0, v___x_6793_);
v___x_6795_ = v___x_6790_;
goto v_reusejp_6794_;
}
else
{
lean_object* v_reuseFailAlloc_6796_; 
v_reuseFailAlloc_6796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6796_, 0, v___x_6793_);
v___x_6795_ = v_reuseFailAlloc_6796_;
goto v_reusejp_6794_;
}
v_reusejp_6794_:
{
v___y_6758_ = v_tz_6787_;
v___y_6759_ = v___x_6786_;
v___y_6760_ = v___x_6795_;
goto v___jp_6757_;
}
}
}
else
{
lean_object* v_val_6798_; lean_object* v_val_6799_; lean_object* v___x_6801_; uint8_t v_isShared_6802_; uint8_t v_isSharedCheck_6808_; 
v_val_6798_ = lean_ctor_get(v_y_6436_, 0);
lean_inc(v_val_6798_);
lean_dec_ref_known(v_y_6436_, 1);
v_val_6799_ = lean_ctor_get(v_G_6435_, 0);
v_isSharedCheck_6808_ = !lean_is_exclusive(v_G_6435_);
if (v_isSharedCheck_6808_ == 0)
{
v___x_6801_ = v_G_6435_;
v_isShared_6802_ = v_isSharedCheck_6808_;
goto v_resetjp_6800_;
}
else
{
lean_inc(v_val_6799_);
lean_dec(v_G_6435_);
v___x_6801_ = lean_box(0);
v_isShared_6802_ = v_isSharedCheck_6808_;
goto v_resetjp_6800_;
}
v_resetjp_6800_:
{
uint8_t v___x_6803_; lean_object* v___x_6804_; lean_object* v___x_6806_; 
v___x_6803_ = lean_unbox(v_val_6799_);
lean_dec(v_val_6799_);
v___x_6804_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_val_6798_, v___x_6803_);
lean_dec(v_val_6798_);
if (v_isShared_6802_ == 0)
{
lean_ctor_set(v___x_6801_, 0, v___x_6804_);
v___x_6806_ = v___x_6801_;
goto v_reusejp_6805_;
}
else
{
lean_object* v_reuseFailAlloc_6807_; 
v_reuseFailAlloc_6807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6807_, 0, v___x_6804_);
v___x_6806_ = v_reuseFailAlloc_6807_;
goto v_reusejp_6805_;
}
v_reusejp_6805_:
{
v___y_6758_ = v_tz_6787_;
v___y_6759_ = v___x_6786_;
v___y_6760_ = v___x_6806_;
goto v___jp_6757_;
}
}
}
}
}
else
{
lean_dec(v_y_6436_);
lean_dec(v_G_6435_);
v___y_6758_ = v_tz_6787_;
v___y_6759_ = v___x_6786_;
v___y_6760_ = v_u_6437_;
goto v___jp_6757_;
}
}
v___jp_6809_:
{
if (lean_obj_tag(v_zabbrev_6462_) == 0)
{
lean_object* v___x_6813_; lean_object* v___x_6814_; 
v___x_6813_ = lean_box(0);
v___x_6814_ = lean_apply_1(v___y_6811_, v___x_6813_);
v___y_6783_ = v___y_6810_;
v___y_6784_ = v___y_6812_;
v___y_6785_ = v___x_6814_;
goto v___jp_6782_;
}
else
{
lean_object* v_val_6815_; 
lean_dec_ref(v___y_6811_);
v_val_6815_ = lean_ctor_get(v_zabbrev_6462_, 0);
lean_inc(v_val_6815_);
lean_dec_ref_known(v_zabbrev_6462_, 1);
v___y_6783_ = v___y_6810_;
v___y_6784_ = v___y_6812_;
v___y_6785_ = v_val_6815_;
goto v___jp_6782_;
}
}
v___jp_6816_:
{
lean_object* v___f_6818_; 
lean_inc(v___y_6817_);
v___f_6818_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__3), 2, 1);
lean_closure_set(v___f_6818_, 0, v___y_6817_);
if (lean_obj_tag(v_V_6460_) == 0)
{
if (lean_obj_tag(v_v_6463_) == 0)
{
if (lean_obj_tag(v_z_6461_) == 0)
{
lean_object* v___x_6819_; lean_object* v___x_6820_; 
v___x_6819_ = lean_box(0);
lean_inc(v___y_6817_);
v___x_6820_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__3(v___y_6817_, v___x_6819_);
v___y_6810_ = v___y_6817_;
v___y_6811_ = v___f_6818_;
v___y_6812_ = v___x_6820_;
goto v___jp_6809_;
}
else
{
lean_object* v_val_6821_; 
v_val_6821_ = lean_ctor_get(v_z_6461_, 0);
lean_inc(v_val_6821_);
lean_dec_ref_known(v_z_6461_, 1);
v___y_6810_ = v___y_6817_;
v___y_6811_ = v___f_6818_;
v___y_6812_ = v_val_6821_;
goto v___jp_6809_;
}
}
else
{
lean_object* v_val_6822_; 
lean_dec(v_z_6461_);
v_val_6822_ = lean_ctor_get(v_v_6463_, 0);
lean_inc(v_val_6822_);
lean_dec_ref_known(v_v_6463_, 1);
v___y_6810_ = v___y_6817_;
v___y_6811_ = v___f_6818_;
v___y_6812_ = v_val_6822_;
goto v___jp_6809_;
}
}
else
{
lean_object* v_val_6823_; 
lean_dec(v_v_6463_);
lean_dec(v_z_6461_);
v_val_6823_ = lean_ctor_get(v_V_6460_, 0);
lean_inc(v_val_6823_);
lean_dec_ref_known(v_V_6460_, 1);
v___y_6810_ = v___y_6817_;
v___y_6811_ = v___f_6818_;
v___y_6812_ = v_val_6823_;
goto v___jp_6809_;
}
}
v___jp_6824_:
{
lean_object* v___x_6825_; 
v___x_6825_ = l_Std_Time_TimeZone_Offset_zero;
v___y_6817_ = v___x_6825_;
goto v___jp_6816_;
}
v___jp_6826_:
{
lean_object* v___x_6828_; 
v___x_6828_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_offsetOfZoneId_x3f(v_val_6827_);
if (lean_obj_tag(v___x_6828_) == 0)
{
goto v___jp_6824_;
}
else
{
lean_object* v_val_6829_; 
v_val_6829_ = lean_ctor_get(v___x_6828_, 0);
lean_inc(v_val_6829_);
lean_dec_ref_known(v___x_6828_, 1);
v___y_6817_ = v_val_6829_;
goto v___jp_6816_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___boxed(lean_object* v_builder_6838_, lean_object* v_aw_6839_, lean_object* v_dateformat_6840_){
_start:
{
lean_object* v_res_6841_; 
v_res_6841_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(v_builder_6838_, v_aw_6839_, v_dateformat_6840_);
lean_dec_ref(v_dateformat_6840_);
return v_res_6841_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(lean_object* v_date_6842_, lean_object* v_config_6843_, lean_object* v_mod_6844_, lean_object* v_rest_6845_, lean_object* v_a_6846_){
_start:
{
if (lean_obj_tag(v_mod_6844_) == 0)
{
lean_object* v_val_6847_; lean_object* v___x_6848_; 
lean_dec(v_rest_6845_);
lean_dec_ref(v_config_6843_);
v_val_6847_ = lean_ctor_get(v_mod_6844_, 0);
lean_inc_ref(v_val_6847_);
lean_dec_ref_known(v_mod_6844_, 1);
v___x_6848_ = l_Std_Internal_Parsec_String_pstring(v_val_6847_, v_a_6846_);
if (lean_obj_tag(v___x_6848_) == 0)
{
lean_object* v_pos_6849_; lean_object* v___x_6851_; uint8_t v_isShared_6852_; uint8_t v_isSharedCheck_6856_; 
v_pos_6849_ = lean_ctor_get(v___x_6848_, 0);
v_isSharedCheck_6856_ = !lean_is_exclusive(v___x_6848_);
if (v_isSharedCheck_6856_ == 0)
{
lean_object* v_unused_6857_; 
v_unused_6857_ = lean_ctor_get(v___x_6848_, 1);
lean_dec(v_unused_6857_);
v___x_6851_ = v___x_6848_;
v_isShared_6852_ = v_isSharedCheck_6856_;
goto v_resetjp_6850_;
}
else
{
lean_inc(v_pos_6849_);
lean_dec(v___x_6848_);
v___x_6851_ = lean_box(0);
v_isShared_6852_ = v_isSharedCheck_6856_;
goto v_resetjp_6850_;
}
v_resetjp_6850_:
{
lean_object* v___x_6854_; 
if (v_isShared_6852_ == 0)
{
lean_ctor_set(v___x_6851_, 1, v_date_6842_);
v___x_6854_ = v___x_6851_;
goto v_reusejp_6853_;
}
else
{
lean_object* v_reuseFailAlloc_6855_; 
v_reuseFailAlloc_6855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6855_, 0, v_pos_6849_);
lean_ctor_set(v_reuseFailAlloc_6855_, 1, v_date_6842_);
v___x_6854_ = v_reuseFailAlloc_6855_;
goto v_reusejp_6853_;
}
v_reusejp_6853_:
{
return v___x_6854_;
}
}
}
else
{
lean_object* v_pos_6858_; lean_object* v_err_6859_; lean_object* v___x_6861_; uint8_t v_isShared_6862_; uint8_t v_isSharedCheck_6866_; 
lean_dec_ref(v_date_6842_);
v_pos_6858_ = lean_ctor_get(v___x_6848_, 0);
v_err_6859_ = lean_ctor_get(v___x_6848_, 1);
v_isSharedCheck_6866_ = !lean_is_exclusive(v___x_6848_);
if (v_isSharedCheck_6866_ == 0)
{
v___x_6861_ = v___x_6848_;
v_isShared_6862_ = v_isSharedCheck_6866_;
goto v_resetjp_6860_;
}
else
{
lean_inc(v_err_6859_);
lean_inc(v_pos_6858_);
lean_dec(v___x_6848_);
v___x_6861_ = lean_box(0);
v_isShared_6862_ = v_isSharedCheck_6866_;
goto v_resetjp_6860_;
}
v_resetjp_6860_:
{
lean_object* v___x_6864_; 
if (v_isShared_6862_ == 0)
{
v___x_6864_ = v___x_6861_;
goto v_reusejp_6863_;
}
else
{
lean_object* v_reuseFailAlloc_6865_; 
v_reuseFailAlloc_6865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6865_, 0, v_pos_6858_);
lean_ctor_set(v_reuseFailAlloc_6865_, 1, v_err_6859_);
v___x_6864_ = v_reuseFailAlloc_6865_;
goto v_reusejp_6863_;
}
v_reusejp_6863_:
{
return v___x_6864_;
}
}
}
}
else
{
lean_object* v_modifier_6867_; lean_object* v___x_6868_; lean_object* v___x_6869_; 
v_modifier_6867_ = lean_ctor_get(v_mod_6844_, 0);
lean_inc_ref_n(v_modifier_6867_, 2);
lean_dec_ref_known(v_mod_6844_, 1);
v___x_6868_ = l___private_Std_Time_Format_Basic_0__Std_Time_reservedDigits(v_rest_6845_);
v___x_6869_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_6843_, v___x_6868_, v_modifier_6867_, v_a_6846_);
if (lean_obj_tag(v___x_6869_) == 0)
{
lean_object* v_pos_6870_; lean_object* v_res_6871_; lean_object* v___x_6873_; uint8_t v_isShared_6874_; uint8_t v_isSharedCheck_6879_; 
v_pos_6870_ = lean_ctor_get(v___x_6869_, 0);
v_res_6871_ = lean_ctor_get(v___x_6869_, 1);
v_isSharedCheck_6879_ = !lean_is_exclusive(v___x_6869_);
if (v_isSharedCheck_6879_ == 0)
{
v___x_6873_ = v___x_6869_;
v_isShared_6874_ = v_isSharedCheck_6879_;
goto v_resetjp_6872_;
}
else
{
lean_inc(v_res_6871_);
lean_inc(v_pos_6870_);
lean_dec(v___x_6869_);
v___x_6873_ = lean_box(0);
v_isShared_6874_ = v_isSharedCheck_6879_;
goto v_resetjp_6872_;
}
v_resetjp_6872_:
{
lean_object* v___x_6875_; lean_object* v___x_6877_; 
v___x_6875_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(v_date_6842_, v_modifier_6867_, v_res_6871_);
if (v_isShared_6874_ == 0)
{
lean_ctor_set(v___x_6873_, 1, v___x_6875_);
v___x_6877_ = v___x_6873_;
goto v_reusejp_6876_;
}
else
{
lean_object* v_reuseFailAlloc_6878_; 
v_reuseFailAlloc_6878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6878_, 0, v_pos_6870_);
lean_ctor_set(v_reuseFailAlloc_6878_, 1, v___x_6875_);
v___x_6877_ = v_reuseFailAlloc_6878_;
goto v_reusejp_6876_;
}
v_reusejp_6876_:
{
return v___x_6877_;
}
}
}
else
{
lean_object* v_pos_6880_; lean_object* v_err_6881_; lean_object* v___x_6883_; uint8_t v_isShared_6884_; uint8_t v_isSharedCheck_6888_; 
lean_dec_ref(v_modifier_6867_);
lean_dec_ref(v_date_6842_);
v_pos_6880_ = lean_ctor_get(v___x_6869_, 0);
v_err_6881_ = lean_ctor_get(v___x_6869_, 1);
v_isSharedCheck_6888_ = !lean_is_exclusive(v___x_6869_);
if (v_isSharedCheck_6888_ == 0)
{
v___x_6883_ = v___x_6869_;
v_isShared_6884_ = v_isSharedCheck_6888_;
goto v_resetjp_6882_;
}
else
{
lean_inc(v_err_6881_);
lean_inc(v_pos_6880_);
lean_dec(v___x_6869_);
v___x_6883_ = lean_box(0);
v_isShared_6884_ = v_isSharedCheck_6888_;
goto v_resetjp_6882_;
}
v_resetjp_6882_:
{
lean_object* v___x_6886_; 
if (v_isShared_6884_ == 0)
{
v___x_6886_ = v___x_6883_;
goto v_reusejp_6885_;
}
else
{
lean_object* v_reuseFailAlloc_6887_; 
v_reuseFailAlloc_6887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6887_, 0, v_pos_6880_);
lean_ctor_set(v_reuseFailAlloc_6887_, 1, v_err_6881_);
v___x_6886_ = v_reuseFailAlloc_6887_;
goto v_reusejp_6885_;
}
v_reusejp_6885_:
{
return v___x_6886_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___redArg(lean_object* v_input_6889_, lean_object* v_config_6890_){
_start:
{
lean_object* v___x_6891_; lean_object* v___x_6892_; 
v___x_6891_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6892_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6891_, v_input_6889_);
if (lean_obj_tag(v___x_6892_) == 0)
{
lean_object* v_a_6893_; lean_object* v___x_6895_; uint8_t v_isShared_6896_; uint8_t v_isSharedCheck_6900_; 
lean_dec_ref(v_config_6890_);
v_a_6893_ = lean_ctor_get(v___x_6892_, 0);
v_isSharedCheck_6900_ = !lean_is_exclusive(v___x_6892_);
if (v_isSharedCheck_6900_ == 0)
{
v___x_6895_ = v___x_6892_;
v_isShared_6896_ = v_isSharedCheck_6900_;
goto v_resetjp_6894_;
}
else
{
lean_inc(v_a_6893_);
lean_dec(v___x_6892_);
v___x_6895_ = lean_box(0);
v_isShared_6896_ = v_isSharedCheck_6900_;
goto v_resetjp_6894_;
}
v_resetjp_6894_:
{
lean_object* v___x_6898_; 
if (v_isShared_6896_ == 0)
{
v___x_6898_ = v___x_6895_;
goto v_reusejp_6897_;
}
else
{
lean_object* v_reuseFailAlloc_6899_; 
v_reuseFailAlloc_6899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6899_, 0, v_a_6893_);
v___x_6898_ = v_reuseFailAlloc_6899_;
goto v_reusejp_6897_;
}
v_reusejp_6897_:
{
return v___x_6898_;
}
}
}
else
{
lean_object* v_a_6901_; lean_object* v___x_6903_; uint8_t v_isShared_6904_; uint8_t v_isSharedCheck_6909_; 
v_a_6901_ = lean_ctor_get(v___x_6892_, 0);
v_isSharedCheck_6909_ = !lean_is_exclusive(v___x_6892_);
if (v_isSharedCheck_6909_ == 0)
{
v___x_6903_ = v___x_6892_;
v_isShared_6904_ = v_isSharedCheck_6909_;
goto v_resetjp_6902_;
}
else
{
lean_inc(v_a_6901_);
lean_dec(v___x_6892_);
v___x_6903_ = lean_box(0);
v_isShared_6904_ = v_isSharedCheck_6909_;
goto v_resetjp_6902_;
}
v_resetjp_6902_:
{
lean_object* v___x_6905_; lean_object* v___x_6907_; 
v___x_6905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6905_, 0, v_config_6890_);
lean_ctor_set(v___x_6905_, 1, v_a_6901_);
if (v_isShared_6904_ == 0)
{
lean_ctor_set(v___x_6903_, 0, v___x_6905_);
v___x_6907_ = v___x_6903_;
goto v_reusejp_6906_;
}
else
{
lean_object* v_reuseFailAlloc_6908_; 
v_reuseFailAlloc_6908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6908_, 0, v___x_6905_);
v___x_6907_ = v_reuseFailAlloc_6908_;
goto v_reusejp_6906_;
}
v_reusejp_6906_:
{
return v___x_6907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec(lean_object* v_tz_6910_, lean_object* v_input_6911_, lean_object* v_config_6912_){
_start:
{
lean_object* v___x_6913_; 
v___x_6913_ = l_Std_Time_GenericFormat_spec___redArg(v_input_6911_, v_config_6912_);
return v___x_6913_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___boxed(lean_object* v_tz_6914_, lean_object* v_input_6915_, lean_object* v_config_6916_){
_start:
{
lean_object* v_res_6917_; 
v_res_6917_ = l_Std_Time_GenericFormat_spec(v_tz_6914_, v_input_6915_, v_config_6916_);
lean_dec(v_tz_6914_);
return v_res_6917_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(lean_object* v_msg_6918_){
_start:
{
lean_object* v___x_6919_; lean_object* v___x_6920_; 
v___x_6919_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0);
v___x_6920_ = lean_panic_fn_borrowed(v___x_6919_, v_msg_6918_);
return v___x_6920_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(lean_object* v_tz_6921_, lean_object* v_msg_6922_){
_start:
{
lean_object* v___x_6923_; 
v___x_6923_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(v_msg_6922_);
return v___x_6923_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___boxed(lean_object* v_tz_6924_, lean_object* v_msg_6925_){
_start:
{
lean_object* v_res_6926_; 
v_res_6926_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(v_tz_6924_, v_msg_6925_);
lean_dec(v_tz_6924_);
return v_res_6926_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21(lean_object* v_tz_6929_, lean_object* v_input_6930_, lean_object* v_config_6931_){
_start:
{
lean_object* v___x_6932_; lean_object* v___x_6933_; 
v___x_6932_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6933_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6932_, v_input_6930_);
if (lean_obj_tag(v___x_6933_) == 0)
{
lean_object* v_a_6934_; lean_object* v___x_6935_; lean_object* v___x_6936_; lean_object* v___x_6937_; lean_object* v___x_6938_; lean_object* v___x_6939_; lean_object* v___x_6940_; 
lean_dec_ref(v_config_6931_);
v_a_6934_ = lean_ctor_get(v___x_6933_, 0);
lean_inc(v_a_6934_);
lean_dec_ref_known(v___x_6933_, 1);
v___x_6935_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_6936_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__1));
v___x_6937_ = lean_unsigned_to_nat(935u);
v___x_6938_ = lean_unsigned_to_nat(18u);
v___x_6939_ = l_mkPanicMessageWithDecl(v___x_6935_, v___x_6936_, v___x_6937_, v___x_6938_, v_a_6934_);
lean_dec(v_a_6934_);
v___x_6940_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(v___x_6939_);
return v___x_6940_;
}
else
{
lean_object* v_a_6941_; lean_object* v___x_6942_; 
v_a_6941_ = lean_ctor_get(v___x_6933_, 0);
lean_inc(v_a_6941_);
lean_dec_ref_known(v___x_6933_, 1);
v___x_6942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6942_, 0, v_config_6931_);
lean_ctor_set(v___x_6942_, 1, v_a_6941_);
return v___x_6942_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21___boxed(lean_object* v_tz_6943_, lean_object* v_input_6944_, lean_object* v_config_6945_){
_start:
{
lean_object* v_res_6946_; 
v_res_6946_ = l_Std_Time_GenericFormat_spec_x21(v_tz_6943_, v_input_6944_, v_config_6945_);
lean_dec(v_tz_6943_);
return v_res_6946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(lean_object* v_config_6950_, lean_object* v_aw_6951_, lean_object* v_builder_6952_, lean_object* v_x_6953_, lean_object* v_a_6954_){
_start:
{
if (lean_obj_tag(v_x_6953_) == 0)
{
lean_object* v_dateformat_6955_; lean_object* v___x_6956_; 
v_dateformat_6955_ = lean_ctor_get(v_config_6950_, 0);
lean_inc_ref(v_dateformat_6955_);
lean_dec_ref(v_config_6950_);
v___x_6956_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(v_builder_6952_, v_aw_6951_, v_dateformat_6955_);
lean_dec_ref(v_dateformat_6955_);
if (lean_obj_tag(v___x_6956_) == 0)
{
lean_object* v___x_6957_; lean_object* v___x_6958_; 
v___x_6957_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go___closed__1));
v___x_6958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6958_, 0, v_a_6954_);
lean_ctor_set(v___x_6958_, 1, v___x_6957_);
return v___x_6958_;
}
else
{
lean_object* v_val_6959_; lean_object* v___x_6960_; 
v_val_6959_ = lean_ctor_get(v___x_6956_, 0);
lean_inc(v_val_6959_);
lean_dec_ref_known(v___x_6956_, 1);
v___x_6960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6960_, 0, v_a_6954_);
lean_ctor_set(v___x_6960_, 1, v_val_6959_);
return v___x_6960_;
}
}
else
{
lean_object* v_head_6961_; lean_object* v_tail_6962_; lean_object* v___x_6963_; 
v_head_6961_ = lean_ctor_get(v_x_6953_, 0);
lean_inc(v_head_6961_);
v_tail_6962_ = lean_ctor_get(v_x_6953_, 1);
lean_inc_n(v_tail_6962_, 2);
lean_dec_ref_known(v_x_6953_, 2);
lean_inc_ref(v_config_6950_);
v___x_6963_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(v_builder_6952_, v_config_6950_, v_head_6961_, v_tail_6962_, v_a_6954_);
if (lean_obj_tag(v___x_6963_) == 0)
{
lean_object* v_pos_6964_; lean_object* v_res_6965_; 
v_pos_6964_ = lean_ctor_get(v___x_6963_, 0);
lean_inc(v_pos_6964_);
v_res_6965_ = lean_ctor_get(v___x_6963_, 1);
lean_inc(v_res_6965_);
lean_dec_ref_known(v___x_6963_, 2);
v_builder_6952_ = v_res_6965_;
v_x_6953_ = v_tail_6962_;
v_a_6954_ = v_pos_6964_;
goto _start;
}
else
{
lean_object* v_pos_6967_; lean_object* v_err_6968_; lean_object* v___x_6970_; uint8_t v_isShared_6971_; uint8_t v_isSharedCheck_6975_; 
lean_dec(v_tail_6962_);
lean_dec(v_aw_6951_);
lean_dec_ref(v_config_6950_);
v_pos_6967_ = lean_ctor_get(v___x_6963_, 0);
v_err_6968_ = lean_ctor_get(v___x_6963_, 1);
v_isSharedCheck_6975_ = !lean_is_exclusive(v___x_6963_);
if (v_isSharedCheck_6975_ == 0)
{
v___x_6970_ = v___x_6963_;
v_isShared_6971_ = v_isSharedCheck_6975_;
goto v_resetjp_6969_;
}
else
{
lean_inc(v_err_6968_);
lean_inc(v_pos_6967_);
lean_dec(v___x_6963_);
v___x_6970_ = lean_box(0);
v_isShared_6971_ = v_isSharedCheck_6975_;
goto v_resetjp_6969_;
}
v_resetjp_6969_:
{
lean_object* v___x_6973_; 
if (v_isShared_6971_ == 0)
{
v___x_6973_ = v___x_6970_;
goto v_reusejp_6972_;
}
else
{
lean_object* v_reuseFailAlloc_6974_; 
v_reuseFailAlloc_6974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6974_, 0, v_pos_6967_);
lean_ctor_set(v_reuseFailAlloc_6974_, 1, v_err_6968_);
v___x_6973_ = v_reuseFailAlloc_6974_;
goto v_reusejp_6972_;
}
v_reusejp_6972_:
{
return v___x_6973_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(lean_object* v_format_6978_, lean_object* v_config_6979_, lean_object* v_aw_6980_, lean_object* v_a_6981_){
_start:
{
lean_object* v___x_6982_; lean_object* v___x_6983_; 
v___x_6982_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser___closed__0));
v___x_6983_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(v_config_6979_, v_aw_6980_, v___x_6982_, v_format_6978_, v_a_6981_);
return v___x_6983_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(lean_object* v_config_6987_, lean_object* v_format_6988_, lean_object* v_func_6989_, lean_object* v_a_6990_){
_start:
{
if (lean_obj_tag(v_format_6988_) == 0)
{
lean_dec_ref(v_config_6987_);
if (lean_obj_tag(v_func_6989_) == 0)
{
lean_object* v___x_6991_; lean_object* v___x_6992_; 
v___x_6991_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg___closed__1));
v___x_6992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6992_, 0, v_a_6990_);
lean_ctor_set(v___x_6992_, 1, v___x_6991_);
return v___x_6992_;
}
else
{
lean_object* v_val_6993_; lean_object* v_fst_6994_; lean_object* v_snd_6995_; lean_object* v___x_6996_; uint8_t v_decide_6997_; 
v_val_6993_ = lean_ctor_get(v_func_6989_, 0);
lean_inc(v_val_6993_);
lean_dec_ref_known(v_func_6989_, 1);
v_fst_6994_ = lean_ctor_get(v_a_6990_, 0);
v_snd_6995_ = lean_ctor_get(v_a_6990_, 1);
v___x_6996_ = lean_string_utf8_byte_size(v_fst_6994_);
v_decide_6997_ = lean_nat_dec_eq(v_snd_6995_, v___x_6996_);
if (v_decide_6997_ == 0)
{
lean_object* v___x_6998_; lean_object* v___x_6999_; 
lean_dec(v_val_6993_);
v___x_6998_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
v___x_6999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6999_, 0, v_a_6990_);
lean_ctor_set(v___x_6999_, 1, v___x_6998_);
return v___x_6999_;
}
else
{
lean_object* v___x_7000_; 
v___x_7000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7000_, 0, v_a_6990_);
lean_ctor_set(v___x_7000_, 1, v_val_6993_);
return v___x_7000_;
}
}
}
else
{
lean_object* v_head_7001_; 
v_head_7001_ = lean_ctor_get(v_format_6988_, 0);
lean_inc(v_head_7001_);
if (lean_obj_tag(v_head_7001_) == 0)
{
lean_object* v_tail_7002_; lean_object* v_val_7003_; lean_object* v___x_7004_; 
v_tail_7002_ = lean_ctor_get(v_format_6988_, 1);
lean_inc(v_tail_7002_);
lean_dec_ref_known(v_format_6988_, 2);
v_val_7003_ = lean_ctor_get(v_head_7001_, 0);
lean_inc_ref(v_val_7003_);
lean_dec_ref_known(v_head_7001_, 1);
v___x_7004_ = l_Std_Internal_Parsec_String_pstring(v_val_7003_, v_a_6990_);
if (lean_obj_tag(v___x_7004_) == 0)
{
lean_object* v_pos_7005_; 
v_pos_7005_ = lean_ctor_get(v___x_7004_, 0);
lean_inc(v_pos_7005_);
lean_dec_ref_known(v___x_7004_, 2);
v_format_6988_ = v_tail_7002_;
v_a_6990_ = v_pos_7005_;
goto _start;
}
else
{
lean_object* v_pos_7007_; lean_object* v_err_7008_; lean_object* v___x_7010_; uint8_t v_isShared_7011_; uint8_t v_isSharedCheck_7015_; 
lean_dec(v_tail_7002_);
lean_dec(v_func_6989_);
lean_dec_ref(v_config_6987_);
v_pos_7007_ = lean_ctor_get(v___x_7004_, 0);
v_err_7008_ = lean_ctor_get(v___x_7004_, 1);
v_isSharedCheck_7015_ = !lean_is_exclusive(v___x_7004_);
if (v_isSharedCheck_7015_ == 0)
{
v___x_7010_ = v___x_7004_;
v_isShared_7011_ = v_isSharedCheck_7015_;
goto v_resetjp_7009_;
}
else
{
lean_inc(v_err_7008_);
lean_inc(v_pos_7007_);
lean_dec(v___x_7004_);
v___x_7010_ = lean_box(0);
v_isShared_7011_ = v_isSharedCheck_7015_;
goto v_resetjp_7009_;
}
v_resetjp_7009_:
{
lean_object* v___x_7013_; 
if (v_isShared_7011_ == 0)
{
v___x_7013_ = v___x_7010_;
goto v_reusejp_7012_;
}
else
{
lean_object* v_reuseFailAlloc_7014_; 
v_reuseFailAlloc_7014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7014_, 0, v_pos_7007_);
lean_ctor_set(v_reuseFailAlloc_7014_, 1, v_err_7008_);
v___x_7013_ = v_reuseFailAlloc_7014_;
goto v_reusejp_7012_;
}
v_reusejp_7012_:
{
return v___x_7013_;
}
}
}
}
else
{
lean_object* v_tail_7016_; lean_object* v_modifier_7017_; lean_object* v___x_7018_; lean_object* v___x_7019_; 
v_tail_7016_ = lean_ctor_get(v_format_6988_, 1);
lean_inc_n(v_tail_7016_, 2);
lean_dec_ref_known(v_format_6988_, 2);
v_modifier_7017_ = lean_ctor_get(v_head_7001_, 0);
lean_inc_ref(v_modifier_7017_);
lean_dec_ref_known(v_head_7001_, 1);
v___x_7018_ = l___private_Std_Time_Format_Basic_0__Std_Time_reservedDigits(v_tail_7016_);
lean_inc_ref(v_config_6987_);
v___x_7019_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_6987_, v___x_7018_, v_modifier_7017_, v_a_6990_);
if (lean_obj_tag(v___x_7019_) == 0)
{
lean_object* v_pos_7020_; lean_object* v_res_7021_; lean_object* v___x_7022_; 
v_pos_7020_ = lean_ctor_get(v___x_7019_, 0);
lean_inc(v_pos_7020_);
v_res_7021_ = lean_ctor_get(v___x_7019_, 1);
lean_inc(v_res_7021_);
lean_dec_ref_known(v___x_7019_, 2);
v___x_7022_ = lean_apply_1(v_func_6989_, v_res_7021_);
v_format_6988_ = v_tail_7016_;
v_func_6989_ = v___x_7022_;
v_a_6990_ = v_pos_7020_;
goto _start;
}
else
{
lean_object* v_pos_7024_; lean_object* v_err_7025_; lean_object* v___x_7027_; uint8_t v_isShared_7028_; uint8_t v_isSharedCheck_7032_; 
lean_dec(v_tail_7016_);
lean_dec(v_func_6989_);
lean_dec_ref(v_config_6987_);
v_pos_7024_ = lean_ctor_get(v___x_7019_, 0);
v_err_7025_ = lean_ctor_get(v___x_7019_, 1);
v_isSharedCheck_7032_ = !lean_is_exclusive(v___x_7019_);
if (v_isSharedCheck_7032_ == 0)
{
v___x_7027_ = v___x_7019_;
v_isShared_7028_ = v_isSharedCheck_7032_;
goto v_resetjp_7026_;
}
else
{
lean_inc(v_err_7025_);
lean_inc(v_pos_7024_);
lean_dec(v___x_7019_);
v___x_7027_ = lean_box(0);
v_isShared_7028_ = v_isSharedCheck_7032_;
goto v_resetjp_7026_;
}
v_resetjp_7026_:
{
lean_object* v___x_7030_; 
if (v_isShared_7028_ == 0)
{
v___x_7030_ = v___x_7027_;
goto v_reusejp_7029_;
}
else
{
lean_object* v_reuseFailAlloc_7031_; 
v_reuseFailAlloc_7031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7031_, 0, v_pos_7024_);
lean_ctor_set(v_reuseFailAlloc_7031_, 1, v_err_7025_);
v___x_7030_ = v_reuseFailAlloc_7031_;
goto v_reusejp_7029_;
}
v_reusejp_7029_:
{
return v___x_7030_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go(lean_object* v_00_u03b1_7033_, lean_object* v_config_7034_, lean_object* v_format_7035_, lean_object* v_func_7036_, lean_object* v_a_7037_){
_start:
{
lean_object* v___x_7038_; 
v___x_7038_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7034_, v_format_7035_, v_func_7036_, v_a_7037_);
return v___x_7038_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser___redArg(lean_object* v_format_7039_, lean_object* v_config_7040_, lean_object* v_func_7041_, lean_object* v_a_7042_){
_start:
{
lean_object* v___x_7043_; 
v___x_7043_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7040_, v_format_7039_, v_func_7041_, v_a_7042_);
return v___x_7043_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser(lean_object* v_00_u03b1_7044_, lean_object* v_format_7045_, lean_object* v_config_7046_, lean_object* v_func_7047_, lean_object* v_a_7048_){
_start:
{
lean_object* v___x_7049_; 
v___x_7049_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7046_, v_format_7045_, v_func_7047_, v_a_7048_);
return v___x_7049_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse___lam__0(lean_object* v_string_7050_, lean_object* v_config_7051_, lean_object* v_aw_7052_, lean_object* v___y_7053_){
_start:
{
lean_object* v___x_7054_; 
v___x_7054_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(v_string_7050_, v_config_7051_, v_aw_7052_, v___y_7053_);
if (lean_obj_tag(v___x_7054_) == 0)
{
lean_object* v_pos_7055_; lean_object* v_fst_7056_; lean_object* v_snd_7057_; lean_object* v___x_7058_; uint8_t v_decide_7059_; 
v_pos_7055_ = lean_ctor_get(v___x_7054_, 0);
v_fst_7056_ = lean_ctor_get(v_pos_7055_, 0);
v_snd_7057_ = lean_ctor_get(v_pos_7055_, 1);
v___x_7058_ = lean_string_utf8_byte_size(v_fst_7056_);
v_decide_7059_ = lean_nat_dec_eq(v_snd_7057_, v___x_7058_);
if (v_decide_7059_ == 0)
{
lean_object* v___x_7061_; uint8_t v_isShared_7062_; uint8_t v_isSharedCheck_7067_; 
lean_inc(v_pos_7055_);
v_isSharedCheck_7067_ = !lean_is_exclusive(v___x_7054_);
if (v_isSharedCheck_7067_ == 0)
{
lean_object* v_unused_7068_; lean_object* v_unused_7069_; 
v_unused_7068_ = lean_ctor_get(v___x_7054_, 1);
lean_dec(v_unused_7068_);
v_unused_7069_ = lean_ctor_get(v___x_7054_, 0);
lean_dec(v_unused_7069_);
v___x_7061_ = v___x_7054_;
v_isShared_7062_ = v_isSharedCheck_7067_;
goto v_resetjp_7060_;
}
else
{
lean_dec(v___x_7054_);
v___x_7061_ = lean_box(0);
v_isShared_7062_ = v_isSharedCheck_7067_;
goto v_resetjp_7060_;
}
v_resetjp_7060_:
{
lean_object* v___x_7063_; lean_object* v___x_7065_; 
v___x_7063_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_7062_ == 0)
{
lean_ctor_set_tag(v___x_7061_, 1);
lean_ctor_set(v___x_7061_, 1, v___x_7063_);
v___x_7065_ = v___x_7061_;
goto v_reusejp_7064_;
}
else
{
lean_object* v_reuseFailAlloc_7066_; 
v_reuseFailAlloc_7066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7066_, 0, v_pos_7055_);
lean_ctor_set(v_reuseFailAlloc_7066_, 1, v___x_7063_);
v___x_7065_ = v_reuseFailAlloc_7066_;
goto v_reusejp_7064_;
}
v_reusejp_7064_:
{
return v___x_7065_;
}
}
}
else
{
return v___x_7054_;
}
}
else
{
return v___x_7054_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse(lean_object* v_aw_7070_, lean_object* v_format_7071_, lean_object* v_input_7072_){
_start:
{
lean_object* v_config_7073_; lean_object* v_string_7074_; lean_object* v___f_7075_; lean_object* v___x_7076_; 
v_config_7073_ = lean_ctor_get(v_format_7071_, 0);
lean_inc_ref(v_config_7073_);
v_string_7074_ = lean_ctor_get(v_format_7071_, 1);
lean_inc(v_string_7074_);
lean_dec_ref(v_format_7071_);
v___f_7075_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parse___lam__0), 4, 3);
lean_closure_set(v___f_7075_, 0, v_string_7074_);
lean_closure_set(v___f_7075_, 1, v_config_7073_);
lean_closure_set(v___f_7075_, 2, v_aw_7070_);
v___x_7076_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_7075_, v_input_7072_);
return v___x_7076_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(lean_object* v_msg_7077_){
_start:
{
lean_object* v___x_7078_; lean_object* v___x_7079_; 
v___x_7078_ = l_Std_Time_instInhabitedDateTime;
v___x_7079_ = lean_panic_fn_borrowed(v___x_7078_, v_msg_7077_);
return v___x_7079_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse_x21(lean_object* v_aw_7081_, lean_object* v_format_7082_, lean_object* v_input_7083_){
_start:
{
lean_object* v___x_7084_; 
v___x_7084_ = l_Std_Time_GenericFormat_parse(v_aw_7081_, v_format_7082_, v_input_7083_);
if (lean_obj_tag(v___x_7084_) == 0)
{
lean_object* v_a_7085_; lean_object* v___x_7086_; lean_object* v___x_7087_; lean_object* v___x_7088_; lean_object* v___x_7089_; lean_object* v___x_7090_; lean_object* v___x_7091_; 
v_a_7085_ = lean_ctor_get(v___x_7084_, 0);
lean_inc(v_a_7085_);
lean_dec_ref_known(v___x_7084_, 1);
v___x_7086_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_7087_ = ((lean_object*)(l_Std_Time_GenericFormat_parse_x21___closed__0));
v___x_7088_ = lean_unsigned_to_nat(975u);
v___x_7089_ = lean_unsigned_to_nat(18u);
v___x_7090_ = l_mkPanicMessageWithDecl(v___x_7086_, v___x_7087_, v___x_7088_, v___x_7089_, v_a_7085_);
lean_dec(v_a_7085_);
v___x_7091_ = l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(v___x_7090_);
return v___x_7091_;
}
else
{
lean_object* v_a_7092_; 
v_a_7092_ = lean_ctor_get(v___x_7084_, 0);
lean_inc(v_a_7092_);
lean_dec_ref_known(v___x_7084_, 1);
return v_a_7092_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0(lean_object* v_config_7093_, lean_object* v_string_7094_, lean_object* v_builder_7095_, lean_object* v___y_7096_){
_start:
{
lean_object* v___x_7097_; 
v___x_7097_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7093_, v_string_7094_, v_builder_7095_, v___y_7096_);
return v___x_7097_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg(lean_object* v_format_7098_, lean_object* v_builder_7099_, lean_object* v_input_7100_){
_start:
{
lean_object* v_config_7101_; lean_object* v_string_7102_; lean_object* v___f_7103_; lean_object* v___x_7104_; 
v_config_7101_ = lean_ctor_get(v_format_7098_, 0);
lean_inc_ref(v_config_7101_);
v_string_7102_ = lean_ctor_get(v_format_7098_, 1);
lean_inc(v_string_7102_);
lean_dec_ref(v_format_7098_);
v___f_7103_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0), 4, 3);
lean_closure_set(v___f_7103_, 0, v_config_7101_);
lean_closure_set(v___f_7103_, 1, v_string_7102_);
lean_closure_set(v___f_7103_, 2, v_builder_7099_);
v___x_7104_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_7103_, v_input_7100_);
return v___x_7104_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder(lean_object* v_aw_7105_, lean_object* v_00_u03b1_7106_, lean_object* v_format_7107_, lean_object* v_builder_7108_, lean_object* v_input_7109_){
_start:
{
lean_object* v___x_7110_; 
v___x_7110_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_7107_, v_builder_7108_, v_input_7109_);
return v___x_7110_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___boxed(lean_object* v_aw_7111_, lean_object* v_00_u03b1_7112_, lean_object* v_format_7113_, lean_object* v_builder_7114_, lean_object* v_input_7115_){
_start:
{
lean_object* v_res_7116_; 
v_res_7116_ = l_Std_Time_GenericFormat_parseBuilder(v_aw_7111_, v_00_u03b1_7112_, v_format_7113_, v_builder_7114_, v_input_7115_);
lean_dec(v_aw_7111_);
return v_res_7116_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg(lean_object* v_inst_7118_, lean_object* v_format_7119_, lean_object* v_builder_7120_, lean_object* v_input_7121_){
_start:
{
lean_object* v___x_7122_; 
v___x_7122_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_7119_, v_builder_7120_, v_input_7121_);
if (lean_obj_tag(v___x_7122_) == 0)
{
lean_object* v_a_7123_; lean_object* v___x_7124_; lean_object* v___x_7125_; lean_object* v___x_7126_; lean_object* v___x_7127_; lean_object* v___x_7128_; lean_object* v___x_7129_; 
v_a_7123_ = lean_ctor_get(v___x_7122_, 0);
lean_inc(v_a_7123_);
lean_dec_ref_known(v___x_7122_, 1);
v___x_7124_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_7125_ = ((lean_object*)(l_Std_Time_GenericFormat_parseBuilder_x21___redArg___closed__0));
v___x_7126_ = lean_unsigned_to_nat(989u);
v___x_7127_ = lean_unsigned_to_nat(18u);
v___x_7128_ = l_mkPanicMessageWithDecl(v___x_7124_, v___x_7125_, v___x_7126_, v___x_7127_, v_a_7123_);
lean_dec(v_a_7123_);
v___x_7129_ = l_panic___redArg(v_inst_7118_, v___x_7128_);
return v___x_7129_;
}
else
{
lean_object* v_a_7130_; 
v_a_7130_ = lean_ctor_get(v___x_7122_, 0);
lean_inc(v_a_7130_);
lean_dec_ref_known(v___x_7122_, 1);
return v_a_7130_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg___boxed(lean_object* v_inst_7131_, lean_object* v_format_7132_, lean_object* v_builder_7133_, lean_object* v_input_7134_){
_start:
{
lean_object* v_res_7135_; 
v_res_7135_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7131_, v_format_7132_, v_builder_7133_, v_input_7134_);
lean_dec(v_inst_7131_);
return v_res_7135_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21(lean_object* v_00_u03b1_7136_, lean_object* v_aw_7137_, lean_object* v_inst_7138_, lean_object* v_format_7139_, lean_object* v_builder_7140_, lean_object* v_input_7141_){
_start:
{
lean_object* v___x_7142_; 
v___x_7142_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7138_, v_format_7139_, v_builder_7140_, v_input_7141_);
return v___x_7142_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___boxed(lean_object* v_00_u03b1_7143_, lean_object* v_aw_7144_, lean_object* v_inst_7145_, lean_object* v_format_7146_, lean_object* v_builder_7147_, lean_object* v_input_7148_){
_start:
{
lean_object* v_res_7149_; 
v_res_7149_ = l_Std_Time_GenericFormat_parseBuilder_x21(v_00_u03b1_7143_, v_aw_7144_, v_inst_7145_, v_format_7146_, v_builder_7147_, v_input_7148_);
lean_dec(v_inst_7145_);
lean_dec(v_aw_7144_);
return v_res_7149_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(lean_object* v_getInfo_7150_, lean_object* v_dateformat_7151_, lean_object* v_data_7152_, lean_object* v_format_7153_){
_start:
{
if (lean_obj_tag(v_format_7153_) == 0)
{
lean_object* v___x_7154_; 
lean_dec_ref(v_dateformat_7151_);
lean_dec_ref(v_getInfo_7150_);
v___x_7154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7154_, 0, v_data_7152_);
return v___x_7154_;
}
else
{
lean_object* v_head_7155_; 
v_head_7155_ = lean_ctor_get(v_format_7153_, 0);
lean_inc(v_head_7155_);
if (lean_obj_tag(v_head_7155_) == 0)
{
lean_object* v_tail_7156_; lean_object* v_val_7157_; lean_object* v___x_7158_; 
v_tail_7156_ = lean_ctor_get(v_format_7153_, 1);
lean_inc(v_tail_7156_);
lean_dec_ref_known(v_format_7153_, 2);
v_val_7157_ = lean_ctor_get(v_head_7155_, 0);
lean_inc_ref(v_val_7157_);
lean_dec_ref_known(v_head_7155_, 1);
v___x_7158_ = lean_string_append(v_data_7152_, v_val_7157_);
lean_dec_ref(v_val_7157_);
v_data_7152_ = v___x_7158_;
v_format_7153_ = v_tail_7156_;
goto _start;
}
else
{
lean_object* v_tail_7160_; lean_object* v_modifier_7161_; lean_object* v___x_7162_; 
v_tail_7160_ = lean_ctor_get(v_format_7153_, 1);
lean_inc(v_tail_7160_);
lean_dec_ref_known(v_format_7153_, 2);
v_modifier_7161_ = lean_ctor_get(v_head_7155_, 0);
lean_inc_ref_n(v_modifier_7161_, 2);
lean_dec_ref_known(v_head_7155_, 1);
lean_inc_ref(v_getInfo_7150_);
v___x_7162_ = lean_apply_1(v_getInfo_7150_, v_modifier_7161_);
if (lean_obj_tag(v___x_7162_) == 0)
{
lean_object* v___x_7163_; 
lean_dec_ref(v_modifier_7161_);
lean_dec(v_tail_7160_);
lean_dec_ref(v_data_7152_);
lean_dec_ref(v_dateformat_7151_);
lean_dec_ref(v_getInfo_7150_);
v___x_7163_ = lean_box(0);
return v___x_7163_;
}
else
{
lean_object* v_val_7164_; lean_object* v___x_7165_; lean_object* v___x_7166_; 
v_val_7164_ = lean_ctor_get(v___x_7162_, 0);
lean_inc(v_val_7164_);
lean_dec_ref_known(v___x_7162_, 1);
lean_inc_ref(v_dateformat_7151_);
v___x_7165_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7151_, v_modifier_7161_, v_val_7164_);
v___x_7166_ = lean_string_append(v_data_7152_, v___x_7165_);
lean_dec_ref(v___x_7165_);
v_data_7152_ = v___x_7166_;
v_format_7153_ = v_tail_7160_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___redArg(lean_object* v_format_7168_, lean_object* v_getInfo_7169_){
_start:
{
lean_object* v_config_7170_; lean_object* v_string_7171_; lean_object* v_dateformat_7172_; lean_object* v___x_7173_; lean_object* v___x_7174_; 
v_config_7170_ = lean_ctor_get(v_format_7168_, 0);
lean_inc_ref(v_config_7170_);
v_string_7171_ = lean_ctor_get(v_format_7168_, 1);
lean_inc(v_string_7171_);
lean_dec_ref(v_format_7168_);
v_dateformat_7172_ = lean_ctor_get(v_config_7170_, 0);
lean_inc_ref(v_dateformat_7172_);
lean_dec_ref(v_config_7170_);
v___x_7173_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_7174_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(v_getInfo_7169_, v_dateformat_7172_, v___x_7173_, v_string_7171_);
return v___x_7174_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric(lean_object* v_aw_7175_, lean_object* v_format_7176_, lean_object* v_getInfo_7177_){
_start:
{
lean_object* v___x_7178_; 
v___x_7178_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_format_7176_, v_getInfo_7177_);
return v___x_7178_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___boxed(lean_object* v_aw_7179_, lean_object* v_format_7180_, lean_object* v_getInfo_7181_){
_start:
{
lean_object* v_res_7182_; 
v_res_7182_ = l_Std_Time_GenericFormat_formatGeneric(v_aw_7179_, v_format_7180_, v_getInfo_7181_);
lean_dec(v_aw_7179_);
return v_res_7182_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatParts___redArg(lean_object* v_format_7183_, lean_object* v_date_7184_, lean_object* v_time_7185_, lean_object* v_zone_7186_){
_start:
{
lean_object* v_config_7187_; lean_object* v_dateformat_7188_; lean_object* v___x_7189_; lean_object* v___x_7190_; 
v_config_7187_ = lean_ctor_get(v_format_7183_, 0);
v_dateformat_7188_ = lean_ctor_get(v_config_7187_, 0);
lean_inc_ref(v_dateformat_7188_);
v___x_7189_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_fieldValue_x3f___boxed), 5, 4);
lean_closure_set(v___x_7189_, 0, v_dateformat_7188_);
lean_closure_set(v___x_7189_, 1, v_date_7184_);
lean_closure_set(v___x_7189_, 2, v_time_7185_);
lean_closure_set(v___x_7189_, 3, v_zone_7186_);
v___x_7190_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_format_7183_, v___x_7189_);
return v___x_7190_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatParts(lean_object* v_aw_7191_, lean_object* v_format_7192_, lean_object* v_date_7193_, lean_object* v_time_7194_, lean_object* v_zone_7195_){
_start:
{
lean_object* v___x_7196_; 
v___x_7196_ = l_Std_Time_GenericFormat_formatParts___redArg(v_format_7192_, v_date_7193_, v_time_7194_, v_zone_7195_);
return v___x_7196_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatParts___boxed(lean_object* v_aw_7197_, lean_object* v_format_7198_, lean_object* v_date_7199_, lean_object* v_time_7200_, lean_object* v_zone_7201_){
_start:
{
lean_object* v_res_7202_; 
v_res_7202_ = l_Std_Time_GenericFormat_formatParts(v_aw_7197_, v_format_7198_, v_date_7199_, v_time_7200_, v_zone_7201_);
lean_dec(v_aw_7197_);
return v_res_7202_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format___lam__0(lean_object* v_tz_7203_, lean_object* v_timestamp_7204_, lean_object* v___x_7205_, lean_object* v_x_7206_){
_start:
{
lean_object* v_offset_7207_; lean_object* v_second_7208_; lean_object* v_nano_7209_; lean_object* v___x_7210_; lean_object* v___x_7211_; lean_object* v___x_7212_; lean_object* v_nanos_7213_; lean_object* v___x_7214_; lean_object* v_nanos_7215_; lean_object* v___x_7216_; lean_object* v___x_7217_; lean_object* v___x_7218_; 
v_offset_7207_ = lean_ctor_get(v_tz_7203_, 0);
v_second_7208_ = lean_ctor_get(v_timestamp_7204_, 0);
v_nano_7209_ = lean_ctor_get(v_timestamp_7204_, 1);
v___x_7210_ = lean_nat_to_int(v___x_7205_);
v___x_7211_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3);
v___x_7212_ = lean_int_mul(v_second_7208_, v___x_7211_);
v_nanos_7213_ = lean_int_add(v___x_7212_, v_nano_7209_);
lean_dec(v___x_7212_);
v___x_7214_ = lean_int_mul(v_offset_7207_, v___x_7211_);
v_nanos_7215_ = lean_int_add(v___x_7214_, v___x_7210_);
lean_dec(v___x_7210_);
lean_dec(v___x_7214_);
v___x_7216_ = lean_int_add(v_nanos_7213_, v_nanos_7215_);
lean_dec(v_nanos_7215_);
lean_dec(v_nanos_7213_);
v___x_7217_ = l_Std_Time_Duration_ofNanoseconds(v___x_7216_);
lean_dec(v___x_7216_);
v___x_7218_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_7217_);
return v___x_7218_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format___lam__0___boxed(lean_object* v_tz_7219_, lean_object* v_timestamp_7220_, lean_object* v___x_7221_, lean_object* v_x_7222_){
_start:
{
lean_object* v_res_7223_; 
v_res_7223_ = l_Std_Time_GenericFormat_format___lam__0(v_tz_7219_, v_timestamp_7220_, v___x_7221_, v_x_7222_);
lean_dec_ref(v_timestamp_7220_);
lean_dec_ref(v_tz_7219_);
return v_res_7223_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format(lean_object* v_aw_7224_, lean_object* v_format_7225_, lean_object* v_date_7226_){
_start:
{
lean_object* v_date_7228_; lean_object* v_timezone_7229_; 
if (lean_obj_tag(v_aw_7224_) == 0)
{
lean_object* v_a_7239_; lean_object* v_offset_7240_; lean_object* v_name_7241_; lean_object* v_abbreviation_7242_; uint8_t v_isDST_7243_; lean_object* v_timestamp_7244_; uint8_t v___x_7245_; uint8_t v___x_7246_; lean_object* v_ltt_7247_; lean_object* v___x_7248_; lean_object* v___x_7249_; lean_object* v___x_7250_; lean_object* v___x_7251_; lean_object* v_tz_7252_; lean_object* v___f_7253_; lean_object* v___x_7254_; 
v_a_7239_ = lean_ctor_get(v_aw_7224_, 0);
v_offset_7240_ = lean_ctor_get(v_a_7239_, 0);
v_name_7241_ = lean_ctor_get(v_a_7239_, 1);
v_abbreviation_7242_ = lean_ctor_get(v_a_7239_, 2);
v_isDST_7243_ = lean_ctor_get_uint8(v_a_7239_, sizeof(void*)*3);
v_timestamp_7244_ = lean_ctor_get(v_date_7226_, 1);
lean_inc_ref(v_timestamp_7244_);
lean_dec_ref(v_date_7226_);
v___x_7245_ = 0;
v___x_7246_ = 1;
lean_inc_ref(v_name_7241_);
lean_inc_ref(v_abbreviation_7242_);
lean_inc(v_offset_7240_);
v_ltt_7247_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_7247_, 0, v_offset_7240_);
lean_ctor_set(v_ltt_7247_, 1, v_abbreviation_7242_);
lean_ctor_set(v_ltt_7247_, 2, v_name_7241_);
lean_ctor_set_uint8(v_ltt_7247_, sizeof(void*)*3, v_isDST_7243_);
lean_ctor_set_uint8(v_ltt_7247_, sizeof(void*)*3 + 1, v___x_7245_);
lean_ctor_set_uint8(v_ltt_7247_, sizeof(void*)*3 + 2, v___x_7246_);
v___x_7248_ = lean_unsigned_to_nat(0u);
v___x_7249_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_7250_ = lean_box(0);
v___x_7251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_7251_, 0, v_ltt_7247_);
lean_ctor_set(v___x_7251_, 1, v___x_7249_);
lean_ctor_set(v___x_7251_, 2, v___x_7250_);
v_tz_7252_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_7251_, v_timestamp_7244_);
lean_inc_ref(v_tz_7252_);
v___f_7253_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_format___lam__0___boxed), 4, 3);
lean_closure_set(v___f_7253_, 0, v_tz_7252_);
lean_closure_set(v___f_7253_, 1, v_timestamp_7244_);
lean_closure_set(v___f_7253_, 2, v___x_7248_);
v___x_7254_ = lean_mk_thunk(v___f_7253_);
v_date_7228_ = v___x_7254_;
v_timezone_7229_ = v_tz_7252_;
goto v___jp_7227_;
}
else
{
lean_object* v_date_7255_; lean_object* v_timezone_7256_; 
v_date_7255_ = lean_ctor_get(v_date_7226_, 0);
lean_inc_ref(v_date_7255_);
v_timezone_7256_ = lean_ctor_get(v_date_7226_, 3);
lean_inc_ref(v_timezone_7256_);
lean_dec_ref(v_date_7226_);
v_date_7228_ = v_date_7255_;
v_timezone_7229_ = v_timezone_7256_;
goto v___jp_7227_;
}
v___jp_7227_:
{
lean_object* v_pdt_7230_; lean_object* v_date_7231_; lean_object* v_time_7232_; lean_object* v___x_7233_; lean_object* v___x_7234_; lean_object* v___x_7235_; lean_object* v___x_7236_; 
v_pdt_7230_ = lean_thunk_get_own(v_date_7228_);
lean_dec_ref(v_date_7228_);
v_date_7231_ = lean_ctor_get(v_pdt_7230_, 0);
lean_inc_ref(v_date_7231_);
v_time_7232_ = lean_ctor_get(v_pdt_7230_, 1);
lean_inc_ref(v_time_7232_);
lean_dec(v_pdt_7230_);
v___x_7233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7233_, 0, v_date_7231_);
v___x_7234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7234_, 0, v_time_7232_);
v___x_7235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7235_, 0, v_timezone_7229_);
v___x_7236_ = l_Std_Time_GenericFormat_formatParts___redArg(v_format_7225_, v___x_7233_, v___x_7234_, v___x_7235_);
if (lean_obj_tag(v___x_7236_) == 0)
{
lean_object* v___x_7237_; 
v___x_7237_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
return v___x_7237_;
}
else
{
lean_object* v_val_7238_; 
v_val_7238_ = lean_ctor_get(v___x_7236_, 0);
lean_inc(v_val_7238_);
lean_dec_ref_known(v___x_7236_, 1);
return v_val_7238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format___boxed(lean_object* v_aw_7257_, lean_object* v_format_7258_, lean_object* v_date_7259_){
_start:
{
lean_object* v_res_7260_; 
v_res_7260_ = l_Std_Time_GenericFormat_format(v_aw_7257_, v_format_7258_, v_date_7259_);
lean_dec(v_aw_7257_);
return v_res_7260_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(lean_object* v_dateformat_7261_, lean_object* v_data_7262_, lean_object* v_format_7263_){
_start:
{
if (lean_obj_tag(v_format_7263_) == 0)
{
lean_dec_ref(v_dateformat_7261_);
return v_data_7262_;
}
else
{
lean_object* v_head_7264_; 
v_head_7264_ = lean_ctor_get(v_format_7263_, 0);
lean_inc(v_head_7264_);
if (lean_obj_tag(v_head_7264_) == 0)
{
lean_object* v_tail_7265_; lean_object* v_val_7266_; lean_object* v___x_7267_; 
v_tail_7265_ = lean_ctor_get(v_format_7263_, 1);
lean_inc(v_tail_7265_);
lean_dec_ref_known(v_format_7263_, 2);
v_val_7266_ = lean_ctor_get(v_head_7264_, 0);
lean_inc_ref(v_val_7266_);
lean_dec_ref_known(v_head_7264_, 1);
v___x_7267_ = lean_string_append(v_data_7262_, v_val_7266_);
lean_dec_ref(v_val_7266_);
v_data_7262_ = v___x_7267_;
v_format_7263_ = v_tail_7265_;
goto _start;
}
else
{
lean_object* v_tail_7269_; lean_object* v_modifier_7270_; lean_object* v___f_7271_; 
v_tail_7269_ = lean_ctor_get(v_format_7263_, 1);
lean_inc(v_tail_7269_);
lean_dec_ref_known(v_format_7263_, 2);
v_modifier_7270_ = lean_ctor_get(v_head_7264_, 0);
lean_inc_ref(v_modifier_7270_);
lean_dec_ref_known(v_head_7264_, 1);
v___f_7271_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0), 5, 4);
lean_closure_set(v___f_7271_, 0, v_dateformat_7261_);
lean_closure_set(v___f_7271_, 1, v_modifier_7270_);
lean_closure_set(v___f_7271_, 2, v_data_7262_);
lean_closure_set(v___f_7271_, 3, v_tail_7269_);
return v___f_7271_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0(lean_object* v_dateformat_7272_, lean_object* v_modifier_7273_, lean_object* v_data_7274_, lean_object* v_tail_7275_, lean_object* v___y_7276_){
_start:
{
lean_object* v___x_7277_; lean_object* v___x_7278_; lean_object* v___x_7279_; 
lean_inc_ref(v_dateformat_7272_);
v___x_7277_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7272_, v_modifier_7273_, v___y_7276_);
v___x_7278_ = lean_string_append(v_data_7274_, v___x_7277_);
lean_dec_ref(v___x_7277_);
v___x_7279_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7272_, v___x_7278_, v_tail_7275_);
return v___x_7279_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___redArg(lean_object* v_format_7280_){
_start:
{
lean_object* v_config_7281_; lean_object* v_string_7282_; lean_object* v_dateformat_7283_; lean_object* v___x_7284_; lean_object* v___x_7285_; 
v_config_7281_ = lean_ctor_get(v_format_7280_, 0);
lean_inc_ref(v_config_7281_);
v_string_7282_ = lean_ctor_get(v_format_7280_, 1);
lean_inc(v_string_7282_);
lean_dec_ref(v_format_7280_);
v_dateformat_7283_ = lean_ctor_get(v_config_7281_, 0);
lean_inc_ref(v_dateformat_7283_);
lean_dec_ref(v_config_7281_);
v___x_7284_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_7285_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7283_, v___x_7284_, v_string_7282_);
return v___x_7285_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder(lean_object* v_aw_7286_, lean_object* v_format_7287_){
_start:
{
lean_object* v___x_7288_; 
v___x_7288_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v_format_7287_);
return v___x_7288_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___boxed(lean_object* v_aw_7289_, lean_object* v_format_7290_){
_start:
{
lean_object* v_res_7291_; 
v_res_7291_ = l_Std_Time_GenericFormat_formatBuilder(v_aw_7289_, v_format_7290_);
lean_dec(v_aw_7289_);
return v_res_7291_;
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
