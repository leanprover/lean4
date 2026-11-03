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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t l_Std_Time_Weekday_ofOrdinal(lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_Internal_Parsec_String_pstring(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x21(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Std_Time_Weekday_toOrdinal(uint8_t);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
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
lean_object* l_Std_Time_PlainDateTime_toWallTime(lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
lean_object* l_Std_Time_Second_instOfNatOrdinal(uint8_t, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Awareness_getD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Awareness_getD___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___boxed(lean_object*);
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
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: '-'"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__11_value)}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12_value;
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: '+'"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__13_value)}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14_value;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Awareness_getD(lean_object* v_x_144_, lean_object* v_default_145_){
_start:
{
if (lean_obj_tag(v_x_144_) == 0)
{
lean_object* v_a_146_; 
v_a_146_ = lean_ctor_get(v_x_144_, 0);
lean_inc_ref(v_a_146_);
return v_a_146_;
}
else
{
lean_inc_ref(v_default_145_);
return v_default_145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Awareness_getD___boxed(lean_object* v_x_147_, lean_object* v_default_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Std_Time_Format_Basic_0__Std_Time_Awareness_getD(v_x_147_, v_default_148_);
lean_dec_ref(v_default_148_);
lean_dec(v_x_147_);
return v_res_149_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedFormatConfig_default___closed__0(void){
_start:
{
lean_object* v___x_150_; uint8_t v___x_151_; lean_object* v___x_152_; 
v___x_150_ = l_Std_Time_DateFormat_enUS;
v___x_151_ = 0;
v___x_152_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*1, v___x_151_);
return v___x_152_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedFormatConfig_default(void){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = lean_obj_once(&l_Std_Time_instInhabitedFormatConfig_default___closed__0, &l_Std_Time_instInhabitedFormatConfig_default___closed__0_once, _init_l_Std_Time_instInhabitedFormatConfig_default___closed__0);
return v___x_153_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedFormatConfig(void){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Std_Time_instInhabitedFormatConfig_default;
return v___x_154_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedGenericFormat_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_box(0);
v___x_156_ = l_Std_Time_instInhabitedFormatConfig_default;
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_155_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default___redArg(){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___redArg___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___redArg___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___redArg___closed__0);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default___redArg___boxed(lean_object* v___dummy_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_Time_instInhabitedGenericFormat_default___redArg();
return v_res_161_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0(void){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Std_Time_instInhabitedGenericFormat_default___redArg();
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default(lean_object* v_awareness_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat_default___boxed(lean_object* v_awareness_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_Time_instInhabitedGenericFormat_default(v_awareness_165_);
lean_dec(v_awareness_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat___redArg(){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat___redArg___boxed(lean_object* v___dummy_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Std_Time_instInhabitedGenericFormat___redArg();
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat(lean_object* v_a_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedGenericFormat___boxed(lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Std_Time_instInhabitedGenericFormat(v_a_173_);
lean_dec(v_a_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(lean_object* v_a_175_, lean_object* v_f_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = lean_apply_1(v_a_175_, v___y_177_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_pos_179_; lean_object* v_res_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_188_; 
v_pos_179_ = lean_ctor_get(v___x_178_, 0);
v_res_180_ = lean_ctor_get(v___x_178_, 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_188_ == 0)
{
v___x_182_ = v___x_178_;
v_isShared_183_ = v_isSharedCheck_188_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_res_180_);
lean_inc(v_pos_179_);
lean_dec(v___x_178_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_188_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_184_ = lean_apply_1(v_f_176_, v_res_180_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 1, v___x_184_);
v___x_186_ = v___x_182_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_pos_179_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
else
{
lean_object* v_pos_189_; lean_object* v_err_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
lean_dec(v_f_176_);
v_pos_189_ = lean_ctor_get(v___x_178_, 0);
v_err_190_ = lean_ctor_get(v___x_178_, 1);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_178_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_err_190_);
lean_inc(v_pos_189_);
lean_dec(v___x_178_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_pos_189_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_err_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1(lean_object* v_00_u03b1_198_, lean_object* v_00_u03b2_199_, lean_object* v_a_200_, lean_object* v_f_201_, lean_object* v___y_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v_a_200_, v_f_201_, v___y_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0(lean_object* v_acc_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_fst_209_; lean_object* v_snd_210_; lean_object* v_pos_212_; lean_object* v_snd_213_; lean_object* v_err_214_; lean_object* v___x_218_; uint8_t v_decide_219_; 
v_fst_209_ = lean_ctor_get(v_a_208_, 0);
v_snd_210_ = lean_ctor_get(v_a_208_, 1);
lean_inc(v_snd_210_);
v___x_218_ = lean_string_utf8_byte_size(v_fst_209_);
v_decide_219_ = lean_nat_dec_eq(v_snd_210_, v___x_218_);
if (v_decide_219_ == 0)
{
uint32_t v___x_220_; uint32_t v_c_221_; uint8_t v___x_222_; 
v___x_220_ = 34;
v_c_221_ = lean_string_utf8_get_fast(v_fst_209_, v_snd_210_);
v___x_222_ = lean_uint32_dec_eq(v_c_221_, v___x_220_);
if (v___x_222_ == 0)
{
lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_232_; 
lean_inc(v_fst_209_);
v_isSharedCheck_232_ = !lean_is_exclusive(v_a_208_);
if (v_isSharedCheck_232_ == 0)
{
lean_object* v_unused_233_; lean_object* v_unused_234_; 
v_unused_233_ = lean_ctor_get(v_a_208_, 1);
lean_dec(v_unused_233_);
v_unused_234_ = lean_ctor_get(v_a_208_, 0);
lean_dec(v_unused_234_);
v___x_224_ = v_a_208_;
v_isShared_225_ = v_isSharedCheck_232_;
goto v_resetjp_223_;
}
else
{
lean_dec(v_a_208_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_232_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v_it_x27_228_; 
v___x_226_ = lean_string_utf8_next_fast(v_fst_209_, v_snd_210_);
lean_dec(v_snd_210_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v___x_226_);
v_it_x27_228_ = v___x_224_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_fst_209_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v___x_226_);
v_it_x27_228_ = v_reuseFailAlloc_231_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; 
v___x_229_ = lean_string_push(v_acc_207_, v_c_221_);
v_acc_207_ = v___x_229_;
v_a_208_ = v_it_x27_228_;
goto _start;
}
}
}
else
{
lean_object* v___x_235_; 
v___x_235_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_210_);
v_pos_212_ = v_a_208_;
v_snd_213_ = v_snd_210_;
v_err_214_ = v___x_235_;
goto v___jp_211_;
}
}
else
{
lean_object* v___x_236_; 
v___x_236_ = lean_box(0);
lean_inc(v_snd_210_);
v_pos_212_ = v_a_208_;
v_snd_213_ = v_snd_210_;
v_err_214_ = v___x_236_;
goto v___jp_211_;
}
v___jp_211_:
{
uint8_t v_decide_215_; 
v_decide_215_ = lean_nat_dec_eq(v_snd_210_, v_snd_213_);
lean_dec(v_snd_213_);
lean_dec(v_snd_210_);
if (v_decide_215_ == 0)
{
lean_object* v___x_216_; 
lean_dec_ref(v_acc_207_);
lean_inc(v_err_214_);
v___x_216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_216_, 0, v_pos_212_);
lean_ctor_set(v___x_216_, 1, v_err_214_);
return v___x_216_;
}
else
{
lean_object* v___x_217_; 
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v_pos_212_);
lean_ctor_set(v___x_217_, 1, v_acc_207_);
return v___x_217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0(lean_object* v_acc_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_fst_239_; lean_object* v_snd_240_; lean_object* v_pos_242_; lean_object* v_snd_243_; lean_object* v_err_244_; lean_object* v___x_248_; uint8_t v_decide_249_; 
v_fst_239_ = lean_ctor_get(v_a_238_, 0);
v_snd_240_ = lean_ctor_get(v_a_238_, 1);
lean_inc(v_snd_240_);
v___x_248_ = lean_string_utf8_byte_size(v_fst_239_);
v_decide_249_ = lean_nat_dec_eq(v_snd_240_, v___x_248_);
if (v_decide_249_ == 0)
{
uint32_t v___x_250_; uint32_t v_c_251_; uint8_t v___x_252_; 
v___x_250_ = 34;
v_c_251_ = lean_string_utf8_get_fast(v_fst_239_, v_snd_240_);
v___x_252_ = lean_uint32_dec_eq(v_c_251_, v___x_250_);
if (v___x_252_ == 0)
{
lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_262_; 
lean_inc(v_fst_239_);
v_isSharedCheck_262_ = !lean_is_exclusive(v_a_238_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; lean_object* v_unused_264_; 
v_unused_263_ = lean_ctor_get(v_a_238_, 1);
lean_dec(v_unused_263_);
v_unused_264_ = lean_ctor_get(v_a_238_, 0);
lean_dec(v_unused_264_);
v___x_254_ = v_a_238_;
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
else
{
lean_dec(v_a_238_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v_it_x27_258_; 
v___x_256_ = lean_string_utf8_next_fast(v_fst_239_, v_snd_240_);
lean_dec(v_snd_240_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v___x_256_);
v_it_x27_258_ = v___x_254_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_fst_239_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v___x_256_);
v_it_x27_258_ = v_reuseFailAlloc_261_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_string_push(v_acc_237_, v_c_251_);
v___x_260_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0(v___x_259_, v_it_x27_258_);
return v___x_260_;
}
}
}
else
{
lean_object* v___x_265_; 
v___x_265_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_240_);
v_pos_242_ = v_a_238_;
v_snd_243_ = v_snd_240_;
v_err_244_ = v___x_265_;
goto v___jp_241_;
}
}
else
{
lean_object* v___x_266_; 
v___x_266_ = lean_box(0);
lean_inc(v_snd_240_);
v_pos_242_ = v_a_238_;
v_snd_243_ = v_snd_240_;
v_err_244_ = v___x_266_;
goto v___jp_241_;
}
v___jp_241_:
{
uint8_t v_decide_245_; 
v_decide_245_ = lean_nat_dec_eq(v_snd_240_, v_snd_243_);
lean_dec(v_snd_243_);
lean_dec(v_snd_240_);
if (v_decide_245_ == 0)
{
lean_object* v___x_246_; 
lean_dec_ref(v_acc_237_);
lean_inc(v_err_244_);
v___x_246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_246_, 0, v_pos_242_);
lean_ctor_set(v___x_246_, 1, v_err_244_);
return v___x_246_;
}
else
{
lean_object* v___x_247_; 
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v_pos_242_);
lean_ctor_set(v___x_247_, 1, v_acc_237_);
return v___x_247_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(uint32_t v___x_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_fst_273_; lean_object* v_snd_274_; lean_object* v___x_275_; uint8_t v_decide_276_; 
v_fst_273_ = lean_ctor_get(v___y_272_, 0);
v_snd_274_ = lean_ctor_get(v___y_272_, 1);
v___x_275_ = lean_string_utf8_byte_size(v_fst_273_);
v_decide_276_ = lean_nat_dec_eq(v_snd_274_, v___x_275_);
if (v_decide_276_ == 0)
{
uint32_t v_c_277_; uint8_t v___x_278_; 
v_c_277_ = lean_string_utf8_get_fast(v_fst_273_, v_snd_274_);
v___x_278_ = lean_uint32_dec_eq(v_c_277_, v___x_271_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_280_, 0, v___y_272_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
return v___x_280_;
}
else
{
lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_333_; 
lean_inc(v_snd_274_);
lean_inc(v_fst_273_);
v_isSharedCheck_333_ = !lean_is_exclusive(v___y_272_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; lean_object* v_unused_335_; 
v_unused_334_ = lean_ctor_get(v___y_272_, 1);
lean_dec(v_unused_334_);
v_unused_335_ = lean_ctor_get(v___y_272_, 0);
lean_dec(v_unused_335_);
v___x_282_ = v___y_272_;
v_isShared_283_ = v_isSharedCheck_333_;
goto v_resetjp_281_;
}
else
{
lean_dec(v___y_272_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_333_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v_it_x27_286_; 
v___x_284_ = lean_string_utf8_next_fast(v_fst_273_, v_snd_274_);
lean_dec(v_snd_274_);
lean_inc(v_fst_273_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v___x_284_);
v_it_x27_286_ = v___x_282_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_fst_273_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_284_);
v_it_x27_286_ = v_reuseFailAlloc_332_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
uint8_t v_decide_287_; 
v_decide_287_ = lean_nat_dec_eq(v___x_284_, v___x_275_);
if (v_decide_287_ == 0)
{
uint32_t v___x_288_; uint8_t v___x_289_; 
v___x_288_ = lean_string_utf8_get_fast(v_fst_273_, v___x_284_);
v___x_289_ = lean_uint32_dec_eq(v___x_288_, v___x_271_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
lean_dec_ref(v_it_x27_286_);
v___x_290_ = lean_string_utf8_next_fast(v_fst_273_, v___x_284_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v_fst_273_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_293_ = lean_string_push(v___x_292_, v___x_288_);
v___x_294_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0(v___x_293_, v___x_291_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_pos_295_; lean_object* v_res_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_327_; 
v_pos_295_ = lean_ctor_get(v___x_294_, 0);
v_res_296_ = lean_ctor_get(v___x_294_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_327_ == 0)
{
v___x_298_ = v___x_294_;
v_isShared_299_ = v_isSharedCheck_327_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_res_296_);
lean_inc(v_pos_295_);
lean_dec(v___x_294_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_327_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v_fst_300_; lean_object* v_snd_301_; lean_object* v___x_302_; uint8_t v_decide_303_; 
v_fst_300_ = lean_ctor_get(v_pos_295_, 0);
v_snd_301_ = lean_ctor_get(v_pos_295_, 1);
v___x_302_ = lean_string_utf8_byte_size(v_fst_300_);
v_decide_303_ = lean_nat_dec_eq(v_snd_301_, v___x_302_);
if (v_decide_303_ == 0)
{
uint32_t v_c_304_; uint8_t v___x_305_; 
v_c_304_ = lean_string_utf8_get_fast(v_fst_300_, v_snd_301_);
v___x_305_ = lean_uint32_dec_eq(v_c_304_, v___x_271_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; lean_object* v___x_308_; 
lean_dec(v_res_296_);
v___x_306_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
if (v_isShared_299_ == 0)
{
lean_ctor_set_tag(v___x_298_, 1);
lean_ctor_set(v___x_298_, 1, v___x_306_);
v___x_308_ = v___x_298_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_pos_295_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v___x_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
else
{
lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_320_; 
lean_inc(v_snd_301_);
lean_inc(v_fst_300_);
v_isSharedCheck_320_ = !lean_is_exclusive(v_pos_295_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; lean_object* v_unused_322_; 
v_unused_321_ = lean_ctor_get(v_pos_295_, 1);
lean_dec(v_unused_321_);
v_unused_322_ = lean_ctor_get(v_pos_295_, 0);
lean_dec(v_unused_322_);
v___x_311_ = v_pos_295_;
v_isShared_312_ = v_isSharedCheck_320_;
goto v_resetjp_310_;
}
else
{
lean_dec(v_pos_295_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_320_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v_it_x27_315_; 
v___x_313_ = lean_string_utf8_next_fast(v_fst_300_, v_snd_301_);
lean_dec(v_snd_301_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v___x_313_);
v_it_x27_315_ = v___x_311_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_fst_300_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v___x_313_);
v_it_x27_315_ = v_reuseFailAlloc_319_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_317_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v_it_x27_315_);
v___x_317_ = v___x_298_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_it_x27_315_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_res_296_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
else
{
lean_object* v___x_323_; lean_object* v___x_325_; 
lean_dec(v_res_296_);
v___x_323_ = lean_box(0);
if (v_isShared_299_ == 0)
{
lean_ctor_set_tag(v___x_298_, 1);
lean_ctor_set(v___x_298_, 1, v___x_323_);
v___x_325_ = v___x_298_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_pos_295_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
else
{
return v___x_294_;
}
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec(v_fst_273_);
v___x_328_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_329_, 0, v_it_x27_286_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
return v___x_329_;
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_fst_273_);
v___x_330_ = lean_box(0);
v___x_331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_331_, 0, v_it_x27_286_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
return v___x_331_;
}
}
}
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_box(0);
v___x_337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_337_, 0, v___y_272_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___boxed(lean_object* v___x_338_, lean_object* v___y_339_){
_start:
{
uint32_t v___x_11507__boxed_340_; lean_object* v_res_341_; 
v___x_11507__boxed_340_ = lean_unbox_uint32(v___x_338_);
lean_dec(v___x_338_);
v_res_341_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(v___x_11507__boxed_340_, v___y_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2_spec__3(lean_object* v_acc_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_fst_344_; lean_object* v_snd_345_; lean_object* v_pos_347_; lean_object* v_snd_348_; lean_object* v_err_349_; lean_object* v___x_353_; uint8_t v_decide_354_; 
v_fst_344_ = lean_ctor_get(v_a_343_, 0);
v_snd_345_ = lean_ctor_get(v_a_343_, 1);
lean_inc(v_snd_345_);
v___x_353_ = lean_string_utf8_byte_size(v_fst_344_);
v_decide_354_ = lean_nat_dec_eq(v_snd_345_, v___x_353_);
if (v_decide_354_ == 0)
{
uint32_t v___x_355_; uint32_t v_c_356_; uint8_t v___x_357_; 
v___x_355_ = 39;
v_c_356_ = lean_string_utf8_get_fast(v_fst_344_, v_snd_345_);
v___x_357_ = lean_uint32_dec_eq(v_c_356_, v___x_355_);
if (v___x_357_ == 0)
{
lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_367_; 
lean_inc(v_fst_344_);
v_isSharedCheck_367_ = !lean_is_exclusive(v_a_343_);
if (v_isSharedCheck_367_ == 0)
{
lean_object* v_unused_368_; lean_object* v_unused_369_; 
v_unused_368_ = lean_ctor_get(v_a_343_, 1);
lean_dec(v_unused_368_);
v_unused_369_ = lean_ctor_get(v_a_343_, 0);
lean_dec(v_unused_369_);
v___x_359_ = v_a_343_;
v_isShared_360_ = v_isSharedCheck_367_;
goto v_resetjp_358_;
}
else
{
lean_dec(v_a_343_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_367_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v_it_x27_363_; 
v___x_361_ = lean_string_utf8_next_fast(v_fst_344_, v_snd_345_);
lean_dec(v_snd_345_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 1, v___x_361_);
v_it_x27_363_ = v___x_359_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_fst_344_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v___x_361_);
v_it_x27_363_ = v_reuseFailAlloc_366_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_364_; 
v___x_364_ = lean_string_push(v_acc_342_, v_c_356_);
v_acc_342_ = v___x_364_;
v_a_343_ = v_it_x27_363_;
goto _start;
}
}
}
else
{
lean_object* v___x_370_; 
v___x_370_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_345_);
v_pos_347_ = v_a_343_;
v_snd_348_ = v_snd_345_;
v_err_349_ = v___x_370_;
goto v___jp_346_;
}
}
else
{
lean_object* v___x_371_; 
v___x_371_ = lean_box(0);
lean_inc(v_snd_345_);
v_pos_347_ = v_a_343_;
v_snd_348_ = v_snd_345_;
v_err_349_ = v___x_371_;
goto v___jp_346_;
}
v___jp_346_:
{
uint8_t v_decide_350_; 
v_decide_350_ = lean_nat_dec_eq(v_snd_345_, v_snd_348_);
lean_dec(v_snd_348_);
lean_dec(v_snd_345_);
if (v_decide_350_ == 0)
{
lean_object* v___x_351_; 
lean_dec_ref(v_acc_342_);
lean_inc(v_err_349_);
v___x_351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_351_, 0, v_pos_347_);
lean_ctor_set(v___x_351_, 1, v_err_349_);
return v___x_351_;
}
else
{
lean_object* v___x_352_; 
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v_pos_347_);
lean_ctor_set(v___x_352_, 1, v_acc_342_);
return v___x_352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2(lean_object* v_acc_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_fst_374_; lean_object* v_snd_375_; lean_object* v_pos_377_; lean_object* v_snd_378_; lean_object* v_err_379_; lean_object* v___x_383_; uint8_t v_decide_384_; 
v_fst_374_ = lean_ctor_get(v_a_373_, 0);
v_snd_375_ = lean_ctor_get(v_a_373_, 1);
lean_inc(v_snd_375_);
v___x_383_ = lean_string_utf8_byte_size(v_fst_374_);
v_decide_384_ = lean_nat_dec_eq(v_snd_375_, v___x_383_);
if (v_decide_384_ == 0)
{
uint32_t v___x_385_; uint32_t v_c_386_; uint8_t v___x_387_; 
v___x_385_ = 39;
v_c_386_ = lean_string_utf8_get_fast(v_fst_374_, v_snd_375_);
v___x_387_ = lean_uint32_dec_eq(v_c_386_, v___x_385_);
if (v___x_387_ == 0)
{
lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_397_; 
lean_inc(v_fst_374_);
v_isSharedCheck_397_ = !lean_is_exclusive(v_a_373_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; lean_object* v_unused_399_; 
v_unused_398_ = lean_ctor_get(v_a_373_, 1);
lean_dec(v_unused_398_);
v_unused_399_ = lean_ctor_get(v_a_373_, 0);
lean_dec(v_unused_399_);
v___x_389_ = v_a_373_;
v_isShared_390_ = v_isSharedCheck_397_;
goto v_resetjp_388_;
}
else
{
lean_dec(v_a_373_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_397_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v_it_x27_393_; 
v___x_391_ = lean_string_utf8_next_fast(v_fst_374_, v_snd_375_);
lean_dec(v_snd_375_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 1, v___x_391_);
v_it_x27_393_ = v___x_389_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_fst_374_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_391_);
v_it_x27_393_ = v_reuseFailAlloc_396_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_string_push(v_acc_372_, v_c_386_);
v___x_395_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2_spec__3(v___x_394_, v_it_x27_393_);
return v___x_395_;
}
}
}
else
{
lean_object* v___x_400_; 
v___x_400_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_375_);
v_pos_377_ = v_a_373_;
v_snd_378_ = v_snd_375_;
v_err_379_ = v___x_400_;
goto v___jp_376_;
}
}
else
{
lean_object* v___x_401_; 
v___x_401_ = lean_box(0);
lean_inc(v_snd_375_);
v_pos_377_ = v_a_373_;
v_snd_378_ = v_snd_375_;
v_err_379_ = v___x_401_;
goto v___jp_376_;
}
v___jp_376_:
{
uint8_t v_decide_380_; 
v_decide_380_ = lean_nat_dec_eq(v_snd_375_, v_snd_378_);
lean_dec(v_snd_378_);
lean_dec(v_snd_375_);
if (v_decide_380_ == 0)
{
lean_object* v___x_381_; 
lean_dec_ref(v_acc_372_);
lean_inc(v_err_379_);
v___x_381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_381_, 0, v_pos_377_);
lean_ctor_set(v___x_381_, 1, v_err_379_);
return v___x_381_;
}
else
{
lean_object* v___x_382_; 
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v_pos_377_);
lean_ctor_set(v___x_382_, 1, v_acc_372_);
return v___x_382_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0(uint32_t v___x_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_fst_407_; lean_object* v_snd_408_; lean_object* v___x_409_; uint8_t v_decide_410_; 
v_fst_407_ = lean_ctor_get(v___y_406_, 0);
v_snd_408_ = lean_ctor_get(v___y_406_, 1);
v___x_409_ = lean_string_utf8_byte_size(v_fst_407_);
v_decide_410_ = lean_nat_dec_eq(v_snd_408_, v___x_409_);
if (v_decide_410_ == 0)
{
uint32_t v_c_411_; uint8_t v___x_412_; 
v_c_411_ = lean_string_utf8_get_fast(v_fst_407_, v_snd_408_);
v___x_412_ = lean_uint32_dec_eq(v_c_411_, v___x_405_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__1));
v___x_414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_414_, 0, v___y_406_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
return v___x_414_;
}
else
{
lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_467_; 
lean_inc(v_snd_408_);
lean_inc(v_fst_407_);
v_isSharedCheck_467_ = !lean_is_exclusive(v___y_406_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; lean_object* v_unused_469_; 
v_unused_468_ = lean_ctor_get(v___y_406_, 1);
lean_dec(v_unused_468_);
v_unused_469_ = lean_ctor_get(v___y_406_, 0);
lean_dec(v_unused_469_);
v___x_416_ = v___y_406_;
v_isShared_417_ = v_isSharedCheck_467_;
goto v_resetjp_415_;
}
else
{
lean_dec(v___y_406_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_467_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v_it_x27_420_; 
v___x_418_ = lean_string_utf8_next_fast(v_fst_407_, v_snd_408_);
lean_dec(v_snd_408_);
lean_inc(v_fst_407_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v___x_418_);
v_it_x27_420_ = v___x_416_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_fst_407_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_418_);
v_it_x27_420_ = v_reuseFailAlloc_466_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
uint8_t v_decide_421_; 
v_decide_421_ = lean_nat_dec_eq(v___x_418_, v___x_409_);
if (v_decide_421_ == 0)
{
uint32_t v___x_422_; uint8_t v___x_423_; 
v___x_422_ = lean_string_utf8_get_fast(v_fst_407_, v___x_418_);
v___x_423_ = lean_uint32_dec_eq(v___x_422_, v___x_405_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec_ref(v_it_x27_420_);
v___x_424_ = lean_string_utf8_next_fast(v_fst_407_, v___x_418_);
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v_fst_407_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_427_ = lean_string_push(v___x_426_, v___x_422_);
v___x_428_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2(v___x_427_, v___x_425_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_pos_429_; lean_object* v_res_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_461_; 
v_pos_429_ = lean_ctor_get(v___x_428_, 0);
v_res_430_ = lean_ctor_get(v___x_428_, 1);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_461_ == 0)
{
v___x_432_ = v___x_428_;
v_isShared_433_ = v_isSharedCheck_461_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_res_430_);
lean_inc(v_pos_429_);
lean_dec(v___x_428_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_461_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v_fst_434_; lean_object* v_snd_435_; lean_object* v___x_436_; uint8_t v_decide_437_; 
v_fst_434_ = lean_ctor_get(v_pos_429_, 0);
v_snd_435_ = lean_ctor_get(v_pos_429_, 1);
v___x_436_ = lean_string_utf8_byte_size(v_fst_434_);
v_decide_437_ = lean_nat_dec_eq(v_snd_435_, v___x_436_);
if (v_decide_437_ == 0)
{
uint32_t v_c_438_; uint8_t v___x_439_; 
v_c_438_ = lean_string_utf8_get_fast(v_fst_434_, v_snd_435_);
v___x_439_ = lean_uint32_dec_eq(v_c_438_, v___x_405_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_442_; 
lean_dec(v_res_430_);
v___x_440_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__1));
if (v_isShared_433_ == 0)
{
lean_ctor_set_tag(v___x_432_, 1);
lean_ctor_set(v___x_432_, 1, v___x_440_);
v___x_442_ = v___x_432_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_pos_429_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
else
{
lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_454_; 
lean_inc(v_snd_435_);
lean_inc(v_fst_434_);
v_isSharedCheck_454_ = !lean_is_exclusive(v_pos_429_);
if (v_isSharedCheck_454_ == 0)
{
lean_object* v_unused_455_; lean_object* v_unused_456_; 
v_unused_455_ = lean_ctor_get(v_pos_429_, 1);
lean_dec(v_unused_455_);
v_unused_456_ = lean_ctor_get(v_pos_429_, 0);
lean_dec(v_unused_456_);
v___x_445_ = v_pos_429_;
v_isShared_446_ = v_isSharedCheck_454_;
goto v_resetjp_444_;
}
else
{
lean_dec(v_pos_429_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_454_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v_it_x27_449_; 
v___x_447_ = lean_string_utf8_next_fast(v_fst_434_, v_snd_435_);
lean_dec(v_snd_435_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v___x_447_);
v_it_x27_449_ = v___x_445_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_fst_434_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v___x_447_);
v_it_x27_449_ = v_reuseFailAlloc_453_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_451_; 
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v_it_x27_449_);
v___x_451_ = v___x_432_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_it_x27_449_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_res_430_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
else
{
lean_object* v___x_457_; lean_object* v___x_459_; 
lean_dec(v_res_430_);
v___x_457_ = lean_box(0);
if (v_isShared_433_ == 0)
{
lean_ctor_set_tag(v___x_432_, 1);
lean_ctor_set(v___x_432_, 1, v___x_457_);
v___x_459_ = v___x_432_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_pos_429_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
else
{
return v___x_428_;
}
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec(v_fst_407_);
v___x_462_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_463_, 0, v_it_x27_420_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
return v___x_463_;
}
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec(v_fst_407_);
v___x_464_ = lean_box(0);
v___x_465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_465_, 0, v_it_x27_420_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
return v___x_465_;
}
}
}
}
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_box(0);
v___x_471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_471_, 0, v___y_406_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___boxed(lean_object* v___x_472_, lean_object* v___y_473_){
_start:
{
uint32_t v___x_11750__boxed_474_; lean_object* v_res_475_; 
v___x_11750__boxed_474_ = lean_unbox_uint32(v___x_472_);
lean_dec(v___x_472_);
v_res_475_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0(v___x_11750__boxed_474_, v___y_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__3(lean_object* v_acc_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_fst_478_; lean_object* v_snd_479_; lean_object* v_pos_481_; lean_object* v_snd_482_; lean_object* v_err_483_; lean_object* v___x_489_; uint8_t v_decide_490_; 
v_fst_478_ = lean_ctor_get(v_a_477_, 0);
v_snd_479_ = lean_ctor_get(v_a_477_, 1);
lean_inc(v_snd_479_);
v___x_489_ = lean_string_utf8_byte_size(v_fst_478_);
v_decide_490_ = lean_nat_dec_eq(v_snd_479_, v___x_489_);
if (v_decide_490_ == 0)
{
uint32_t v___x_491_; uint32_t v___x_492_; uint32_t v_c_493_; lean_object* v___x_494_; lean_object* v_it_x27_495_; uint32_t v___x_506_; uint8_t v___x_507_; 
v___x_491_ = 39;
v___x_492_ = 34;
v_c_493_ = lean_string_utf8_get_fast(v_fst_478_, v_snd_479_);
v___x_494_ = lean_string_utf8_next_fast(v_fst_478_, v_snd_479_);
lean_inc(v_fst_478_);
v_it_x27_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_495_, 0, v_fst_478_);
lean_ctor_set(v_it_x27_495_, 1, v___x_494_);
v___x_506_ = 65;
v___x_507_ = lean_uint32_dec_le(v___x_506_, v_c_493_);
if (v___x_507_ == 0)
{
goto v___jp_501_;
}
else
{
uint32_t v___x_508_; uint8_t v___x_509_; 
v___x_508_ = 90;
v___x_509_ = lean_uint32_dec_le(v_c_493_, v___x_508_);
if (v___x_509_ == 0)
{
goto v___jp_501_;
}
else
{
lean_dec_ref_known(v_it_x27_495_, 2);
goto v___jp_487_;
}
}
v___jp_496_:
{
uint8_t v___x_497_; 
v___x_497_ = lean_uint32_dec_eq(v_c_493_, v___x_491_);
if (v___x_497_ == 0)
{
uint8_t v___x_498_; 
v___x_498_ = lean_uint32_dec_eq(v_c_493_, v___x_492_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
lean_dec(v_snd_479_);
lean_dec_ref(v_a_477_);
v___x_499_ = lean_string_push(v_acc_476_, v_c_493_);
v_acc_476_ = v___x_499_;
v_a_477_ = v_it_x27_495_;
goto _start;
}
else
{
lean_dec_ref_known(v_it_x27_495_, 2);
goto v___jp_487_;
}
}
else
{
lean_dec_ref_known(v_it_x27_495_, 2);
goto v___jp_487_;
}
}
v___jp_501_:
{
uint32_t v___x_502_; uint8_t v___x_503_; 
v___x_502_ = 97;
v___x_503_ = lean_uint32_dec_le(v___x_502_, v_c_493_);
if (v___x_503_ == 0)
{
goto v___jp_496_;
}
else
{
uint32_t v___x_504_; uint8_t v___x_505_; 
v___x_504_ = 122;
v___x_505_ = lean_uint32_dec_le(v_c_493_, v___x_504_);
if (v___x_505_ == 0)
{
goto v___jp_496_;
}
else
{
lean_dec_ref_known(v_it_x27_495_, 2);
goto v___jp_487_;
}
}
}
}
else
{
lean_object* v___x_510_; 
v___x_510_ = lean_box(0);
lean_inc(v_snd_479_);
v_pos_481_ = v_a_477_;
v_snd_482_ = v_snd_479_;
v_err_483_ = v___x_510_;
goto v___jp_480_;
}
v___jp_480_:
{
uint8_t v_decide_484_; 
v_decide_484_ = lean_nat_dec_eq(v_snd_479_, v_snd_482_);
lean_dec(v_snd_482_);
lean_dec(v_snd_479_);
if (v_decide_484_ == 0)
{
lean_object* v___x_485_; 
lean_dec_ref(v_acc_476_);
lean_inc(v_err_483_);
v___x_485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_485_, 0, v_pos_481_);
lean_ctor_set(v___x_485_, 1, v_err_483_);
return v___x_485_;
}
else
{
lean_object* v___x_486_; 
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v_pos_481_);
lean_ctor_set(v___x_486_, 1, v_acc_476_);
return v___x_486_;
}
}
v___jp_487_:
{
lean_object* v___x_488_; 
v___x_488_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_479_);
v_pos_481_ = v_a_477_;
v_snd_482_ = v_snd_479_;
v_err_483_ = v___x_488_;
goto v___jp_480_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(uint32_t v___x_511_, uint32_t v___x_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_fst_517_; lean_object* v_snd_518_; lean_object* v___x_519_; uint8_t v_decide_520_; 
v_fst_517_ = lean_ctor_get(v___y_513_, 0);
v_snd_518_ = lean_ctor_get(v___y_513_, 1);
v___x_519_ = lean_string_utf8_byte_size(v_fst_517_);
v_decide_520_ = lean_nat_dec_eq(v_snd_518_, v___x_519_);
if (v_decide_520_ == 0)
{
uint32_t v_c_521_; lean_object* v___x_522_; lean_object* v_it_x27_523_; uint32_t v___x_535_; uint8_t v___x_536_; 
v_c_521_ = lean_string_utf8_get_fast(v_fst_517_, v_snd_518_);
v___x_522_ = lean_string_utf8_next_fast(v_fst_517_, v_snd_518_);
lean_inc(v_fst_517_);
v_it_x27_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_523_, 0, v_fst_517_);
lean_ctor_set(v_it_x27_523_, 1, v___x_522_);
v___x_535_ = 65;
v___x_536_ = lean_uint32_dec_le(v___x_535_, v_c_521_);
if (v___x_536_ == 0)
{
goto v___jp_530_;
}
else
{
uint32_t v___x_537_; uint8_t v___x_538_; 
v___x_537_ = 90;
v___x_538_ = lean_uint32_dec_le(v_c_521_, v___x_537_);
if (v___x_538_ == 0)
{
goto v___jp_530_;
}
else
{
lean_dec_ref_known(v_it_x27_523_, 2);
goto v___jp_514_;
}
}
v___jp_524_:
{
uint8_t v___x_525_; 
v___x_525_ = lean_uint32_dec_eq(v_c_521_, v___x_511_);
if (v___x_525_ == 0)
{
uint8_t v___x_526_; 
v___x_526_ = lean_uint32_dec_eq(v_c_521_, v___x_512_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
lean_dec_ref(v___y_513_);
v___x_527_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_528_ = lean_string_push(v___x_527_, v_c_521_);
v___x_529_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__3(v___x_528_, v_it_x27_523_);
return v___x_529_;
}
else
{
lean_dec_ref_known(v_it_x27_523_, 2);
goto v___jp_514_;
}
}
else
{
lean_dec_ref_known(v_it_x27_523_, 2);
goto v___jp_514_;
}
}
v___jp_530_:
{
uint32_t v___x_531_; uint8_t v___x_532_; 
v___x_531_ = 97;
v___x_532_ = lean_uint32_dec_le(v___x_531_, v_c_521_);
if (v___x_532_ == 0)
{
goto v___jp_524_;
}
else
{
uint32_t v___x_533_; uint8_t v___x_534_; 
v___x_533_ = 122;
v___x_534_ = lean_uint32_dec_le(v_c_521_, v___x_533_);
if (v___x_534_ == 0)
{
goto v___jp_524_;
}
else
{
lean_dec_ref_known(v_it_x27_523_, 2);
goto v___jp_514_;
}
}
}
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_box(0);
v___x_540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_540_, 0, v___y_513_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
return v___x_540_;
}
v___jp_514_:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_516_, 0, v___y_513_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2___boxed(lean_object* v___x_541_, lean_object* v___x_542_, lean_object* v___y_543_){
_start:
{
uint32_t v___x_11941__boxed_544_; uint32_t v___x_11942__boxed_545_; lean_object* v_res_546_; 
v___x_11941__boxed_544_ = lean_unbox_uint32(v___x_541_);
lean_dec(v___x_541_);
v___x_11942__boxed_545_ = lean_unbox_uint32(v___x_542_);
lean_dec(v___x_542_);
v_res_546_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(v___x_11941__boxed_544_, v___x_11942__boxed_545_, v___y_543_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(uint32_t v___y_547_){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_548_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_549_ = lean_string_push(v___x_548_, v___y_547_);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3___boxed(lean_object* v___y_551_){
_start:
{
uint32_t v___y_11998__boxed_552_; lean_object* v_res_553_; 
v___y_11998__boxed_552_ = lean_unbox_uint32(v___y_551_);
lean_dec(v___y_551_);
v_res_553_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(v___y_11998__boxed_552_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4(lean_object* v___y_554_){
_start:
{
lean_object* v_fst_555_; lean_object* v_snd_556_; lean_object* v___x_557_; uint8_t v_decide_558_; 
v_fst_555_ = lean_ctor_get(v___y_554_, 0);
v_snd_556_ = lean_ctor_get(v___y_554_, 1);
v___x_557_ = lean_string_utf8_byte_size(v_fst_555_);
v_decide_558_ = lean_nat_dec_eq(v_snd_556_, v___x_557_);
if (v_decide_558_ == 0)
{
lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_569_; 
lean_inc(v_snd_556_);
lean_inc(v_fst_555_);
v_isSharedCheck_569_ = !lean_is_exclusive(v___y_554_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; lean_object* v_unused_571_; 
v_unused_570_ = lean_ctor_get(v___y_554_, 1);
lean_dec(v_unused_570_);
v_unused_571_ = lean_ctor_get(v___y_554_, 0);
lean_dec(v_unused_571_);
v___x_560_ = v___y_554_;
v_isShared_561_ = v_isSharedCheck_569_;
goto v_resetjp_559_;
}
else
{
lean_dec(v___y_554_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_569_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
uint32_t v_c_562_; lean_object* v___x_563_; lean_object* v_it_x27_565_; 
v_c_562_ = lean_string_utf8_get_fast(v_fst_555_, v_snd_556_);
v___x_563_ = lean_string_utf8_next_fast(v_fst_555_, v_snd_556_);
lean_dec(v_snd_556_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v___x_563_);
v_it_x27_565_ = v___x_560_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_fst_555_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v___x_563_);
v_it_x27_565_ = v_reuseFailAlloc_568_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_box_uint32(v_c_562_);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v_it_x27_565_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
return v___x_567_;
}
}
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_box(0);
v___x_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_573_, 0, v___y_554_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
return v___x_573_;
}
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_574_; lean_object* v___x_575_; 
v___x_574_ = 34;
v___x_575_ = lean_box_uint32(v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0(void){
_start:
{
lean_object* v___x_576_; lean_object* v___f_577_; 
v___x_576_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0___boxed__const__1;
v___f_577_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___boxed), 2, 1);
lean_closure_set(v___f_577_, 0, v___x_576_);
return v___f_577_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_578_; lean_object* v___x_579_; 
v___x_578_ = 39;
v___x_579_ = lean_box_uint32(v___x_578_);
return v___x_579_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1(void){
_start:
{
lean_object* v___x_580_; lean_object* v___f_581_; 
v___x_580_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1___boxed__const__1;
v___f_581_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___boxed), 2, 1);
lean_closure_set(v___f_581_, 0, v___x_580_);
return v___f_581_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___f_584_; 
v___x_582_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1___boxed__const__1;
v___x_583_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0___boxed__const__1;
v___f_584_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2___boxed), 3, 2);
lean_closure_set(v___f_584_, 0, v___x_582_);
lean_closure_set(v___f_584_, 1, v___x_583_);
return v___f_584_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart(lean_object* v_a_590_){
_start:
{
lean_object* v___x_591_; 
lean_inc_ref(v_a_590_);
v___x_591_ = l_Std_Time_parseModifier(v_a_590_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_pos_592_; lean_object* v_res_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_601_; 
lean_dec_ref(v_a_590_);
v_pos_592_ = lean_ctor_get(v___x_591_, 0);
v_res_593_ = lean_ctor_get(v___x_591_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_601_ == 0)
{
v___x_595_ = v___x_591_;
v_isShared_596_ = v_isSharedCheck_601_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_res_593_);
lean_inc(v_pos_592_);
lean_dec(v___x_591_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_601_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v_res_593_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 1, v___x_597_);
v___x_599_ = v___x_595_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_pos_592_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
else
{
lean_object* v_pos_602_; lean_object* v_err_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_660_; 
v_pos_602_ = lean_ctor_get(v___x_591_, 0);
v_err_603_ = lean_ctor_get(v___x_591_, 1);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_660_ == 0)
{
v___x_605_ = v___x_591_;
v_isShared_606_ = v_isSharedCheck_660_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_err_603_);
lean_inc(v_pos_602_);
lean_dec(v___x_591_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_660_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v_snd_607_; lean_object* v_fst_608_; lean_object* v_snd_609_; uint8_t v_decide_610_; 
v_snd_607_ = lean_ctor_get(v_a_590_, 1);
lean_inc(v_snd_607_);
lean_dec_ref(v_a_590_);
v_fst_608_ = lean_ctor_get(v_pos_602_, 0);
v_snd_609_ = lean_ctor_get(v_pos_602_, 1);
v_decide_610_ = lean_nat_dec_eq(v_snd_607_, v_snd_609_);
lean_dec(v_snd_607_);
if (v_decide_610_ == 0)
{
lean_object* v___x_612_; 
if (v_isShared_606_ == 0)
{
v___x_612_ = v___x_605_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_pos_602_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_err_603_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
else
{
lean_object* v___f_614_; lean_object* v___y_616_; lean_object* v_pos_617_; lean_object* v_snd_618_; lean_object* v___x_632_; uint8_t v_decide_633_; 
lean_inc(v_snd_609_);
lean_dec(v_err_603_);
v___f_614_ = ((lean_object*)(l_Std_Time_instCoeStringFormatPart___closed__0));
v___x_632_ = lean_string_utf8_byte_size(v_fst_608_);
v_decide_633_ = lean_nat_dec_eq(v_snd_609_, v___x_632_);
if (v_decide_633_ == 0)
{
uint32_t v___x_634_; uint32_t v_c_635_; uint8_t v___x_636_; 
v___x_634_ = 92;
v_c_635_ = lean_string_utf8_get_fast(v_fst_608_, v_snd_609_);
v___x_636_ = lean_uint32_dec_eq(v_c_635_, v___x_634_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_637_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__4));
lean_inc(v_pos_602_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 1, v___x_637_);
v___x_639_ = v___x_605_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_pos_602_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_inc(v_snd_609_);
v___y_616_ = v___x_639_;
v_pos_617_ = v_pos_602_;
v_snd_618_ = v_snd_609_;
goto v___jp_615_;
}
}
else
{
lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_653_; 
lean_inc(v_fst_608_);
lean_del_object(v___x_605_);
v_isSharedCheck_653_ = !lean_is_exclusive(v_pos_602_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; lean_object* v_unused_655_; 
v_unused_654_ = lean_ctor_get(v_pos_602_, 1);
lean_dec(v_unused_654_);
v_unused_655_ = lean_ctor_get(v_pos_602_, 0);
lean_dec(v_unused_655_);
v___x_642_ = v_pos_602_;
v_isShared_643_ = v_isSharedCheck_653_;
goto v_resetjp_641_;
}
else
{
lean_dec(v_pos_602_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_653_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___f_644_; lean_object* v___f_645_; lean_object* v___x_646_; lean_object* v_it_x27_648_; 
v___f_644_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__5));
v___f_645_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__6));
v___x_646_ = lean_string_utf8_next_fast(v_fst_608_, v_snd_609_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 1, v___x_646_);
v_it_x27_648_ = v___x_642_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_fst_608_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___x_646_);
v_it_x27_648_ = v_reuseFailAlloc_652_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_649_; 
v___x_649_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_645_, v___f_644_, v_it_x27_648_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_dec(v_snd_609_);
return v___x_649_;
}
else
{
lean_object* v_pos_650_; lean_object* v_snd_651_; 
v_pos_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_pos_650_);
v_snd_651_ = lean_ctor_get(v_pos_650_, 1);
lean_inc(v_snd_651_);
v___y_616_ = v___x_649_;
v_pos_617_ = v_pos_650_;
v_snd_618_ = v_snd_651_;
goto v___jp_615_;
}
}
}
}
}
else
{
lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_656_ = lean_box(0);
lean_inc(v_pos_602_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 1, v___x_656_);
v___x_658_ = v___x_605_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_pos_602_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_inc(v_snd_609_);
v___y_616_ = v___x_658_;
v_pos_617_ = v_pos_602_;
v_snd_618_ = v_snd_609_;
goto v___jp_615_;
}
}
v___jp_615_:
{
uint8_t v_decide_619_; 
v_decide_619_ = lean_nat_dec_eq(v_snd_609_, v_snd_618_);
lean_dec(v_snd_609_);
if (v_decide_619_ == 0)
{
lean_dec(v_snd_618_);
lean_dec_ref(v_pos_617_);
return v___y_616_;
}
else
{
lean_object* v___f_620_; lean_object* v___x_621_; 
lean_dec_ref(v___y_616_);
v___f_620_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0);
v___x_621_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_620_, v___f_614_, v_pos_617_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_dec(v_snd_618_);
return v___x_621_;
}
else
{
lean_object* v_pos_622_; lean_object* v_snd_623_; uint8_t v_decide_624_; 
v_pos_622_ = lean_ctor_get(v___x_621_, 0);
v_snd_623_ = lean_ctor_get(v_pos_622_, 1);
v_decide_624_ = lean_nat_dec_eq(v_snd_618_, v_snd_623_);
lean_dec(v_snd_618_);
if (v_decide_624_ == 0)
{
return v___x_621_;
}
else
{
lean_object* v___f_625_; lean_object* v___x_626_; 
lean_inc(v_snd_623_);
lean_inc(v_pos_622_);
lean_dec_ref_known(v___x_621_, 2);
v___f_625_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1);
v___x_626_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_625_, v___f_614_, v_pos_622_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_dec(v_snd_623_);
return v___x_626_;
}
else
{
lean_object* v_pos_627_; lean_object* v_snd_628_; uint8_t v_decide_629_; 
v_pos_627_ = lean_ctor_get(v___x_626_, 0);
v_snd_628_ = lean_ctor_get(v_pos_627_, 1);
v_decide_629_ = lean_nat_dec_eq(v_snd_623_, v_snd_628_);
lean_dec(v_snd_623_);
if (v_decide_629_ == 0)
{
return v___x_626_;
}
else
{
lean_object* v___f_630_; lean_object* v___x_631_; 
lean_inc(v_pos_627_);
lean_dec_ref_known(v___x_626_, 2);
v___f_630_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2);
v___x_631_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_630_, v___f_614_, v_pos_627_);
return v___x_631_;
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_specParser_spec__0(lean_object* v_acc_661_, lean_object* v_a_662_){
_start:
{
lean_object* v___x_663_; 
lean_inc_ref(v_a_662_);
v___x_663_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart(v_a_662_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_pos_664_; lean_object* v_res_665_; lean_object* v___x_666_; 
lean_dec_ref(v_a_662_);
v_pos_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_pos_664_);
v_res_665_ = lean_ctor_get(v___x_663_, 1);
lean_inc(v_res_665_);
lean_dec_ref_known(v___x_663_, 2);
v___x_666_ = lean_array_push(v_acc_661_, v_res_665_);
v_acc_661_ = v___x_666_;
v_a_662_ = v_pos_664_;
goto _start;
}
else
{
lean_object* v_pos_668_; lean_object* v_err_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_682_; 
v_pos_668_ = lean_ctor_get(v___x_663_, 0);
v_err_669_ = lean_ctor_get(v___x_663_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_682_ == 0)
{
v___x_671_ = v___x_663_;
v_isShared_672_ = v_isSharedCheck_682_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_err_669_);
lean_inc(v_pos_668_);
lean_dec(v___x_663_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_682_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v_snd_673_; lean_object* v_snd_674_; uint8_t v_decide_675_; 
v_snd_673_ = lean_ctor_get(v_a_662_, 1);
lean_inc(v_snd_673_);
lean_dec_ref(v_a_662_);
v_snd_674_ = lean_ctor_get(v_pos_668_, 1);
v_decide_675_ = lean_nat_dec_eq(v_snd_673_, v_snd_674_);
lean_dec(v_snd_673_);
if (v_decide_675_ == 0)
{
lean_object* v___x_677_; 
lean_dec_ref(v_acc_661_);
if (v_isShared_672_ == 0)
{
v___x_677_ = v___x_671_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_pos_668_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_err_669_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
else
{
lean_object* v___x_680_; 
lean_dec(v_err_669_);
if (v_isShared_672_ == 0)
{
lean_ctor_set_tag(v___x_671_, 0);
lean_ctor_set(v___x_671_, 1, v_acc_661_);
v___x_680_ = v___x_671_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_pos_668_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_acc_661_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParser(lean_object* v_a_688_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__0));
v___x_690_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_specParser_spec__0(v___x_689_, v_a_688_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_pos_691_; lean_object* v_res_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_708_; 
v_pos_691_ = lean_ctor_get(v___x_690_, 0);
v_res_692_ = lean_ctor_get(v___x_690_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_708_ == 0)
{
v___x_694_ = v___x_690_;
v_isShared_695_ = v_isSharedCheck_708_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_res_692_);
lean_inc(v_pos_691_);
lean_dec(v___x_690_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_708_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_fst_696_; lean_object* v_snd_697_; lean_object* v___x_698_; uint8_t v_decide_699_; 
v_fst_696_ = lean_ctor_get(v_pos_691_, 0);
v_snd_697_ = lean_ctor_get(v_pos_691_, 1);
v___x_698_ = lean_string_utf8_byte_size(v_fst_696_);
v_decide_699_ = lean_nat_dec_eq(v_snd_697_, v___x_698_);
if (v_decide_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_702_; 
lean_dec(v_res_692_);
v___x_700_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_695_ == 0)
{
lean_ctor_set_tag(v___x_694_, 1);
lean_ctor_set(v___x_694_, 1, v___x_700_);
v___x_702_ = v___x_694_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_pos_691_);
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
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = lean_array_to_list(v_res_692_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 1, v___x_704_);
v___x_706_ = v___x_694_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_pos_691_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v_pos_709_; lean_object* v_err_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
v_pos_709_ = lean_ctor_get(v___x_690_, 0);
v_err_710_ = lean_ctor_get(v___x_690_, 1);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_690_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_err_710_);
lean_inc(v_pos_709_);
lean_dec(v___x_690_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_pos_709_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_err_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParse(lean_object* v_s_718_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_720_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_719_, v_s_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(uint32_t v_a_721_, lean_object* v_x_722_, lean_object* v_x_723_){
_start:
{
lean_object* v_zero_724_; uint8_t v_isZero_725_; 
v_zero_724_ = lean_unsigned_to_nat(0u);
v_isZero_725_ = lean_nat_dec_eq(v_x_722_, v_zero_724_);
if (v_isZero_725_ == 1)
{
lean_dec(v_x_722_);
return v_x_723_;
}
else
{
lean_object* v_one_726_; lean_object* v_n_727_; lean_object* v___x_728_; 
v_one_726_ = lean_unsigned_to_nat(1u);
v_n_727_ = lean_nat_sub(v_x_722_, v_one_726_);
lean_dec(v_x_722_);
v___x_728_ = lean_string_push(v_x_723_, v_a_721_);
v_x_722_ = v_n_727_;
v_x_723_ = v___x_728_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1___boxed(lean_object* v_a_730_, lean_object* v_x_731_, lean_object* v_x_732_){
_start:
{
uint32_t v_a_boxed_733_; lean_object* v_res_734_; 
v_a_boxed_733_ = lean_unbox_uint32(v_a_730_);
lean_dec(v_a_730_);
v_res_734_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_boxed_733_, v_x_731_, v_x_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(lean_object* v___x_735_, lean_object* v_s_736_, lean_object* v_a_737_, lean_object* v_b_738_){
_start:
{
uint8_t v_decide_739_; 
v_decide_739_ = lean_nat_dec_eq(v_a_737_, v___x_735_);
if (v_decide_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = lean_string_utf8_next_fast(v_s_736_, v_a_737_);
lean_dec(v_a_737_);
v___x_741_ = lean_unsigned_to_nat(1u);
v___x_742_ = lean_nat_add(v_b_738_, v___x_741_);
lean_dec(v_b_738_);
v_a_737_ = v___x_740_;
v_b_738_ = v___x_742_;
goto _start;
}
else
{
lean_dec(v_a_737_);
return v_b_738_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg___boxed(lean_object* v___x_744_, lean_object* v_s_745_, lean_object* v_a_746_, lean_object* v_b_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_744_, v_s_745_, v_a_746_, v_b_747_);
lean_dec_ref(v_s_745_);
lean_dec(v___x_744_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(lean_object* v_n_749_, uint32_t v_a_750_, lean_object* v_s_751_){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_752_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = lean_string_utf8_byte_size(v_s_751_);
v___x_755_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_754_, v_s_751_, v___x_753_, v___x_753_);
v___x_756_ = lean_nat_sub(v_n_749_, v___x_755_);
lean_dec(v___x_755_);
v___x_757_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_750_, v___x_756_, v___x_752_);
v___x_758_ = lean_string_append(v___x_757_, v_s_751_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii___boxed(lean_object* v_n_759_, lean_object* v_a_760_, lean_object* v_s_761_){
_start:
{
uint32_t v_a_boxed_762_; lean_object* v_res_763_; 
v_a_boxed_762_ = lean_unbox_uint32(v_a_760_);
lean_dec(v_a_760_);
v_res_763_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v_n_759_, v_a_boxed_762_, v_s_761_);
lean_dec_ref(v_s_761_);
lean_dec(v_n_759_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0(lean_object* v___x_764_, lean_object* v___x_765_, lean_object* v_s_766_, lean_object* v_inst_767_, lean_object* v_R_768_, lean_object* v_a_769_, lean_object* v_b_770_, lean_object* v_c_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_764_, v_s_766_, v_a_769_, v_b_770_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___boxed(lean_object* v___x_773_, lean_object* v___x_774_, lean_object* v_s_775_, lean_object* v_inst_776_, lean_object* v_R_777_, lean_object* v_a_778_, lean_object* v_b_779_, lean_object* v_c_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0(v___x_773_, v___x_774_, v_s_775_, v_inst_776_, v_R_777_, v_a_778_, v_b_779_, v_c_780_);
lean_dec_ref(v_s_775_);
lean_dec_ref(v___x_774_);
lean_dec(v___x_773_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(lean_object* v_n_782_, uint32_t v_a_783_, lean_object* v_s_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_785_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = lean_string_utf8_byte_size(v_s_784_);
v___x_788_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_787_, v_s_784_, v___x_786_, v___x_786_);
v___x_789_ = lean_nat_sub(v_n_782_, v___x_788_);
lean_dec(v___x_788_);
v___x_790_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_783_, v___x_789_, v___x_785_);
v___x_791_ = lean_string_append(v_s_784_, v___x_790_);
lean_dec_ref(v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii___boxed(lean_object* v_n_792_, lean_object* v_a_793_, lean_object* v_s_794_){
_start:
{
uint32_t v_a_boxed_795_; lean_object* v_res_796_; 
v_a_boxed_795_ = lean_unbox_uint32(v_a_793_);
lean_dec(v_a_793_);
v_res_796_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_n_792_, v_a_boxed_795_, v_s_794_);
lean_dec(v_n_792_);
return v_res_796_;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad(lean_object* v_size_800_, lean_object* v_n_801_, uint8_t v_cut_802_){
_start:
{
lean_object* v_fst_804_; lean_object* v_snd_805_; lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_819_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_820_ = lean_int_dec_lt(v_n_801_, v___x_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; 
v___x_821_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v_fst_804_ = v___x_821_;
v_snd_805_ = v_n_801_;
goto v___jp_803_;
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_823_ = lean_int_neg(v_n_801_);
lean_dec(v_n_801_);
v_fst_804_ = v___x_822_;
v_snd_805_ = v___x_823_;
goto v___jp_803_;
}
v___jp_803_:
{
lean_object* v_numStr_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_numStr_806_ = l_Int_repr(v_snd_805_);
lean_dec(v_snd_805_);
v___x_807_ = lean_string_utf8_byte_size(v_numStr_806_);
v___x_808_ = lean_nat_dec_lt(v_size_800_, v___x_807_);
if (v___x_808_ == 0)
{
uint32_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_809_ = 48;
v___x_810_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v_size_800_, v___x_809_, v_numStr_806_);
lean_dec_ref(v_numStr_806_);
lean_inc_ref(v_fst_804_);
v___x_811_ = lean_string_append(v_fst_804_, v___x_810_);
lean_dec_ref(v___x_810_);
return v___x_811_;
}
else
{
if (v_cut_802_ == 0)
{
lean_object* v___x_812_; 
lean_inc_ref(v_fst_804_);
v___x_812_ = lean_string_append(v_fst_804_, v_numStr_806_);
lean_dec_ref(v_numStr_806_);
return v___x_812_;
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_813_ = lean_nat_sub(v___x_807_, v_size_800_);
v___x_814_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_numStr_806_);
v___x_815_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_815_, 0, v_numStr_806_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
lean_ctor_set(v___x_815_, 2, v___x_807_);
v___x_816_ = l_String_Slice_Pos_nextn(v___x_815_, v___x_814_, v___x_813_);
lean_dec_ref_known(v___x_815_, 3);
v___x_817_ = lean_string_utf8_extract_fast(v_numStr_806_, v___x_816_, v___x_807_);
lean_dec(v___x_816_);
lean_dec_ref(v_numStr_806_);
lean_inc_ref(v_fst_804_);
v___x_818_ = lean_string_append(v_fst_804_, v___x_817_);
lean_dec_ref(v___x_817_);
return v___x_818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad___boxed(lean_object* v_size_824_, lean_object* v_n_825_, lean_object* v_cut_826_){
_start:
{
uint8_t v_cut_boxed_827_; lean_object* v_res_828_; 
v_cut_boxed_827_ = lean_unbox(v_cut_826_);
v_res_828_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_size_824_, v_n_825_, v_cut_boxed_827_);
lean_dec(v_size_824_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate(lean_object* v_size_829_, lean_object* v_n_830_, uint8_t v_cut_831_){
_start:
{
lean_object* v_fst_833_; lean_object* v_snd_834_; lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_849_ = lean_int_dec_lt(v_n_830_, v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
v___x_850_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v_fst_833_ = v___x_850_;
v_snd_834_ = v_n_830_;
goto v___jp_832_;
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_852_ = lean_int_neg(v_n_830_);
lean_dec(v_n_830_);
v_fst_833_ = v___x_851_;
v_snd_834_ = v___x_852_;
goto v___jp_832_;
}
v___jp_832_:
{
lean_object* v_numStr_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v_numStr_835_ = l_Int_repr(v_snd_834_);
lean_dec(v_snd_834_);
v___x_836_ = lean_string_length(v_numStr_835_);
v___x_837_ = lean_nat_dec_lt(v_size_829_, v___x_836_);
if (v___x_837_ == 0)
{
uint32_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_838_ = 48;
v___x_839_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_size_829_, v___x_838_, v_numStr_835_);
lean_dec(v_size_829_);
lean_inc_ref(v_fst_833_);
v___x_840_ = lean_string_append(v_fst_833_, v___x_839_);
lean_dec_ref(v___x_839_);
return v___x_840_;
}
else
{
if (v_cut_831_ == 0)
{
lean_object* v___x_841_; 
lean_dec(v_size_829_);
lean_inc_ref(v_fst_833_);
v___x_841_ = lean_string_append(v_fst_833_, v_numStr_835_);
lean_dec_ref(v_numStr_835_);
return v___x_841_;
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_842_ = lean_unsigned_to_nat(0u);
v___x_843_ = lean_string_utf8_byte_size(v_numStr_835_);
lean_inc_ref(v_numStr_835_);
v___x_844_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_844_, 0, v_numStr_835_);
lean_ctor_set(v___x_844_, 1, v___x_842_);
lean_ctor_set(v___x_844_, 2, v___x_843_);
v___x_845_ = l_String_Slice_Pos_nextn(v___x_844_, v___x_842_, v_size_829_);
lean_dec_ref_known(v___x_844_, 3);
v___x_846_ = lean_string_utf8_extract_fast(v_numStr_835_, v___x_842_, v___x_845_);
lean_dec(v___x_845_);
lean_dec_ref(v_numStr_835_);
lean_inc_ref(v_fst_833_);
v___x_847_ = lean_string_append(v_fst_833_, v___x_846_);
lean_dec_ref(v___x_846_);
return v___x_847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate___boxed(lean_object* v_size_853_, lean_object* v_n_854_, lean_object* v_cut_855_){
_start:
{
uint8_t v_cut_boxed_856_; lean_object* v_res_857_; 
v_cut_boxed_856_ = lean_unbox(v_cut_855_);
v_res_857_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate(v_size_853_, v_n_854_, v_cut_boxed_856_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(uint8_t v_x_858_){
_start:
{
if (v_x_858_ == 0)
{
lean_object* v___x_859_; 
v___x_859_ = lean_unsigned_to_nat(0u);
return v___x_859_;
}
else
{
lean_object* v___x_860_; 
v___x_860_ = lean_unsigned_to_nat(1u);
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___boxed(lean_object* v_x_861_){
_start:
{
uint8_t v_x_40__boxed_862_; lean_object* v_res_863_; 
v_x_40__boxed_862_ = lean_unbox(v_x_861_);
v_res_863_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_x_40__boxed_862_);
return v_res_863_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_865_ = lean_int_neg(v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(lean_object* v_symbols_866_, lean_object* v_month_867_){
_start:
{
lean_object* v_monthLong_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v_monthLong_868_ = lean_ctor_get(v_symbols_866_, 0);
v___x_869_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_870_ = lean_int_add(v_month_867_, v___x_869_);
v___x_871_ = l_Int_toNat(v___x_870_);
lean_dec(v___x_870_);
v___x_872_ = lean_array_fget_borrowed(v_monthLong_868_, v___x_871_);
lean_dec(v___x_871_);
lean_inc(v___x_872_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___boxed(lean_object* v_symbols_873_, lean_object* v_month_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_873_, v_month_874_);
lean_dec(v_month_874_);
lean_dec_ref(v_symbols_873_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(lean_object* v_symbols_876_, lean_object* v_month_877_){
_start:
{
lean_object* v_monthShort_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v_monthShort_878_ = lean_ctor_get(v_symbols_876_, 1);
v___x_879_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_880_ = lean_int_add(v_month_877_, v___x_879_);
v___x_881_ = l_Int_toNat(v___x_880_);
lean_dec(v___x_880_);
v___x_882_ = lean_array_fget_borrowed(v_monthShort_878_, v___x_881_);
lean_dec(v___x_881_);
lean_inc(v___x_882_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort___boxed(lean_object* v_symbols_883_, lean_object* v_month_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_883_, v_month_884_);
lean_dec(v_month_884_);
lean_dec_ref(v_symbols_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(lean_object* v_symbols_886_, lean_object* v_month_887_){
_start:
{
lean_object* v_monthNarrow_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_monthNarrow_888_ = lean_ctor_get(v_symbols_886_, 2);
v___x_889_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_890_ = lean_int_add(v_month_887_, v___x_889_);
v___x_891_ = l_Int_toNat(v___x_890_);
lean_dec(v___x_890_);
v___x_892_ = lean_array_fget_borrowed(v_monthNarrow_888_, v___x_891_);
lean_dec(v___x_891_);
lean_inc(v___x_892_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow___boxed(lean_object* v_symbols_893_, lean_object* v_month_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_893_, v_month_894_);
lean_dec(v_month_894_);
lean_dec_ref(v_symbols_893_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(lean_object* v_symbols_896_, uint8_t v_wd_897_){
_start:
{
lean_object* v_weekdayLong_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_weekdayLong_898_ = lean_ctor_get(v_symbols_896_, 3);
v___x_899_ = l_Std_Time_Weekday_toOrdinal(v_wd_897_);
v___x_900_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_901_ = lean_int_add(v___x_899_, v___x_900_);
lean_dec(v___x_899_);
v___x_902_ = l_Int_toNat(v___x_901_);
lean_dec(v___x_901_);
v___x_903_ = lean_array_fget_borrowed(v_weekdayLong_898_, v___x_902_);
lean_dec(v___x_902_);
lean_inc(v___x_903_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong___boxed(lean_object* v_symbols_904_, lean_object* v_wd_905_){
_start:
{
uint8_t v_wd_boxed_906_; lean_object* v_res_907_; 
v_wd_boxed_906_ = lean_unbox(v_wd_905_);
v_res_907_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_904_, v_wd_boxed_906_);
lean_dec_ref(v_symbols_904_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(lean_object* v_symbols_908_, uint8_t v_wd_909_){
_start:
{
lean_object* v_weekdayShort_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_weekdayShort_910_ = lean_ctor_get(v_symbols_908_, 4);
v___x_911_ = l_Std_Time_Weekday_toOrdinal(v_wd_909_);
v___x_912_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_913_ = lean_int_add(v___x_911_, v___x_912_);
lean_dec(v___x_911_);
v___x_914_ = l_Int_toNat(v___x_913_);
lean_dec(v___x_913_);
v___x_915_ = lean_array_fget_borrowed(v_weekdayShort_910_, v___x_914_);
lean_dec(v___x_914_);
lean_inc(v___x_915_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort___boxed(lean_object* v_symbols_916_, lean_object* v_wd_917_){
_start:
{
uint8_t v_wd_boxed_918_; lean_object* v_res_919_; 
v_wd_boxed_918_ = lean_unbox(v_wd_917_);
v_res_919_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_916_, v_wd_boxed_918_);
lean_dec_ref(v_symbols_916_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(lean_object* v_symbols_920_, uint8_t v_wd_921_){
_start:
{
lean_object* v_weekdayNarrow_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v_weekdayNarrow_922_ = lean_ctor_get(v_symbols_920_, 5);
v___x_923_ = l_Std_Time_Weekday_toOrdinal(v_wd_921_);
v___x_924_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_925_ = lean_int_add(v___x_923_, v___x_924_);
lean_dec(v___x_923_);
v___x_926_ = l_Int_toNat(v___x_925_);
lean_dec(v___x_925_);
v___x_927_ = lean_array_fget_borrowed(v_weekdayNarrow_922_, v___x_926_);
lean_dec(v___x_926_);
lean_inc(v___x_927_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow___boxed(lean_object* v_symbols_928_, lean_object* v_wd_929_){
_start:
{
uint8_t v_wd_boxed_930_; lean_object* v_res_931_; 
v_wd_boxed_930_ = lean_unbox(v_wd_929_);
v_res_931_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_928_, v_wd_boxed_930_);
lean_dec_ref(v_symbols_928_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(lean_object* v_symbols_932_, uint8_t v_wd_933_){
_start:
{
lean_object* v_weekdayTwoLetter_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v_weekdayTwoLetter_934_ = lean_ctor_get(v_symbols_932_, 6);
v___x_935_ = l_Std_Time_Weekday_toOrdinal(v_wd_933_);
v___x_936_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_937_ = lean_int_add(v___x_935_, v___x_936_);
lean_dec(v___x_935_);
v___x_938_ = l_Int_toNat(v___x_937_);
lean_dec(v___x_937_);
v___x_939_ = lean_array_fget_borrowed(v_weekdayTwoLetter_934_, v___x_938_);
lean_dec(v___x_938_);
lean_inc(v___x_939_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter___boxed(lean_object* v_symbols_940_, lean_object* v_wd_941_){
_start:
{
uint8_t v_wd_boxed_942_; lean_object* v_res_943_; 
v_wd_boxed_942_ = lean_unbox(v_wd_941_);
v_res_943_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_940_, v_wd_boxed_942_);
lean_dec_ref(v_symbols_940_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(lean_object* v_symbols_944_, uint8_t v_era_945_){
_start:
{
lean_object* v_eraShort_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_eraShort_946_ = lean_ctor_get(v_symbols_944_, 7);
v___x_947_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_945_);
v___x_948_ = lean_array_fget_borrowed(v_eraShort_946_, v___x_947_);
lean_dec(v___x_947_);
lean_inc(v___x_948_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort___boxed(lean_object* v_symbols_949_, lean_object* v_era_950_){
_start:
{
uint8_t v_era_boxed_951_; lean_object* v_res_952_; 
v_era_boxed_951_ = lean_unbox(v_era_950_);
v_res_952_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(v_symbols_949_, v_era_boxed_951_);
lean_dec_ref(v_symbols_949_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(lean_object* v_symbols_953_, uint8_t v_era_954_){
_start:
{
lean_object* v_eraLong_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_eraLong_955_ = lean_ctor_get(v_symbols_953_, 8);
v___x_956_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_954_);
v___x_957_ = lean_array_fget_borrowed(v_eraLong_955_, v___x_956_);
lean_dec(v___x_956_);
lean_inc(v___x_957_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong___boxed(lean_object* v_symbols_958_, lean_object* v_era_959_){
_start:
{
uint8_t v_era_boxed_960_; lean_object* v_res_961_; 
v_era_boxed_960_ = lean_unbox(v_era_959_);
v_res_961_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(v_symbols_958_, v_era_boxed_960_);
lean_dec_ref(v_symbols_958_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(lean_object* v_symbols_962_, uint8_t v_era_963_){
_start:
{
lean_object* v_eraNarrow_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_eraNarrow_964_ = lean_ctor_get(v_symbols_962_, 9);
v___x_965_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_963_);
v___x_966_ = lean_array_fget_borrowed(v_eraNarrow_964_, v___x_965_);
lean_dec(v___x_965_);
lean_inc(v___x_966_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow___boxed(lean_object* v_symbols_967_, lean_object* v_era_968_){
_start:
{
uint8_t v_era_boxed_969_; lean_object* v_res_970_; 
v_era_boxed_969_ = lean_unbox(v_era_968_);
v_res_970_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(v_symbols_967_, v_era_boxed_969_);
lean_dec_ref(v_symbols_967_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(lean_object* v_x_975_){
_start:
{
lean_object* v_natZero_976_; lean_object* v_intZero_977_; uint8_t v_isNeg_978_; lean_object* v_a_979_; uint8_t v_isZero_980_; lean_object* v_one_981_; lean_object* v_n_982_; uint8_t v_isZero_983_; 
v_natZero_976_ = lean_unsigned_to_nat(0u);
v_intZero_977_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v_isNeg_978_ = lean_int_dec_lt(v_x_975_, v_intZero_977_);
v_a_979_ = lean_nat_abs(v_x_975_);
v_isZero_980_ = lean_nat_dec_eq(v_a_979_, v_natZero_976_);
v_one_981_ = lean_unsigned_to_nat(1u);
v_n_982_ = lean_nat_sub(v_a_979_, v_one_981_);
lean_dec(v_a_979_);
v_isZero_983_ = lean_nat_dec_eq(v_n_982_, v_natZero_976_);
if (v_isZero_983_ == 1)
{
lean_object* v___x_984_; 
lean_dec(v_n_982_);
v___x_984_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__0));
return v___x_984_;
}
else
{
lean_object* v_n_985_; uint8_t v_isZero_986_; 
v_n_985_ = lean_nat_sub(v_n_982_, v_one_981_);
lean_dec(v_n_982_);
v_isZero_986_ = lean_nat_dec_eq(v_n_985_, v_natZero_976_);
if (v_isZero_986_ == 1)
{
lean_object* v___x_987_; 
lean_dec(v_n_985_);
v___x_987_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__1));
return v___x_987_;
}
else
{
lean_object* v_n_988_; uint8_t v_isZero_989_; 
v_n_988_ = lean_nat_sub(v_n_985_, v_one_981_);
lean_dec(v_n_985_);
v_isZero_989_ = lean_nat_dec_eq(v_n_988_, v_natZero_976_);
if (v_isZero_989_ == 1)
{
lean_object* v___x_990_; 
lean_dec(v_n_988_);
v___x_990_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__2));
return v___x_990_;
}
else
{
lean_object* v_n_991_; uint8_t v_isZero_992_; lean_object* v___x_993_; 
v_n_991_ = lean_nat_sub(v_n_988_, v_one_981_);
lean_dec(v_n_988_);
v_isZero_992_ = lean_nat_dec_eq(v_n_991_, v_natZero_976_);
lean_dec(v_n_991_);
v___x_993_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__3));
return v___x_993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___boxed(lean_object* v_x_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_x_994_);
lean_dec(v_x_994_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(lean_object* v_symbols_996_, lean_object* v_q_997_){
_start:
{
lean_object* v_quarterShort_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_quarterShort_998_ = lean_ctor_get(v_symbols_996_, 10);
v___x_999_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1000_ = lean_int_add(v_q_997_, v___x_999_);
v___x_1001_ = l_Int_toNat(v___x_1000_);
lean_dec(v___x_1000_);
v___x_1002_ = lean_array_fget_borrowed(v_quarterShort_998_, v___x_1001_);
lean_dec(v___x_1001_);
lean_inc(v___x_1002_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort___boxed(lean_object* v_symbols_1003_, lean_object* v_q_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1003_, v_q_1004_);
lean_dec(v_q_1004_);
lean_dec_ref(v_symbols_1003_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(lean_object* v_symbols_1006_, lean_object* v_q_1007_){
_start:
{
lean_object* v_quarterLong_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_quarterLong_1008_ = lean_ctor_get(v_symbols_1006_, 11);
v___x_1009_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1010_ = lean_int_add(v_q_1007_, v___x_1009_);
v___x_1011_ = l_Int_toNat(v___x_1010_);
lean_dec(v___x_1010_);
v___x_1012_ = lean_array_fget_borrowed(v_quarterLong_1008_, v___x_1011_);
lean_dec(v___x_1011_);
lean_inc(v___x_1012_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong___boxed(lean_object* v_symbols_1013_, lean_object* v_q_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1013_, v_q_1014_);
lean_dec(v_q_1014_);
lean_dec_ref(v_symbols_1013_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(lean_object* v_symbols_1016_, lean_object* v_q_1017_){
_start:
{
lean_object* v_quarterNarrow_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_quarterNarrow_1018_ = lean_ctor_get(v_symbols_1016_, 12);
v___x_1019_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1020_ = lean_int_add(v_q_1017_, v___x_1019_);
v___x_1021_ = l_Int_toNat(v___x_1020_);
lean_dec(v___x_1020_);
v___x_1022_ = lean_array_fget_borrowed(v_quarterNarrow_1018_, v___x_1021_);
lean_dec(v___x_1021_);
lean_inc(v___x_1022_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow___boxed(lean_object* v_symbols_1023_, lean_object* v_q_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1023_, v_q_1024_);
lean_dec(v_q_1024_);
lean_dec_ref(v_symbols_1023_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(lean_object* v_symbols_1026_, uint8_t v_marker_1027_){
_start:
{
if (v_marker_1027_ == 0)
{
lean_object* v_amShort_1028_; 
v_amShort_1028_ = lean_ctor_get(v_symbols_1026_, 13);
lean_inc_ref(v_amShort_1028_);
return v_amShort_1028_;
}
else
{
lean_object* v_pmShort_1029_; 
v_pmShort_1029_ = lean_ctor_get(v_symbols_1026_, 14);
lean_inc_ref(v_pmShort_1029_);
return v_pmShort_1029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort___boxed(lean_object* v_symbols_1030_, lean_object* v_marker_1031_){
_start:
{
uint8_t v_marker_boxed_1032_; lean_object* v_res_1033_; 
v_marker_boxed_1032_ = lean_unbox(v_marker_1031_);
v_res_1033_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(v_symbols_1030_, v_marker_boxed_1032_);
lean_dec_ref(v_symbols_1030_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong(lean_object* v_symbols_1034_, uint8_t v_marker_1035_){
_start:
{
if (v_marker_1035_ == 0)
{
lean_object* v_amLong_1036_; 
v_amLong_1036_ = lean_ctor_get(v_symbols_1034_, 15);
lean_inc_ref(v_amLong_1036_);
return v_amLong_1036_;
}
else
{
lean_object* v_pmLong_1037_; 
v_pmLong_1037_ = lean_ctor_get(v_symbols_1034_, 16);
lean_inc_ref(v_pmLong_1037_);
return v_pmLong_1037_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong___boxed(lean_object* v_symbols_1038_, lean_object* v_marker_1039_){
_start:
{
uint8_t v_marker_boxed_1040_; lean_object* v_res_1041_; 
v_marker_boxed_1040_ = lean_unbox(v_marker_1039_);
v_res_1041_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong(v_symbols_1038_, v_marker_boxed_1040_);
lean_dec_ref(v_symbols_1038_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(lean_object* v_symbols_1042_, uint8_t v_marker_1043_){
_start:
{
if (v_marker_1043_ == 0)
{
lean_object* v_amNarrow_1044_; 
v_amNarrow_1044_ = lean_ctor_get(v_symbols_1042_, 17);
lean_inc_ref(v_amNarrow_1044_);
return v_amNarrow_1044_;
}
else
{
lean_object* v_pmNarrow_1045_; 
v_pmNarrow_1045_ = lean_ctor_get(v_symbols_1042_, 18);
lean_inc_ref(v_pmNarrow_1045_);
return v_pmNarrow_1045_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow___boxed(lean_object* v_symbols_1046_, lean_object* v_marker_1047_){
_start:
{
uint8_t v_marker_boxed_1048_; lean_object* v_res_1049_; 
v_marker_boxed_1048_ = lean_unbox(v_marker_1047_);
v_res_1049_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(v_symbols_1046_, v_marker_boxed_1048_);
lean_dec_ref(v_symbols_1046_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(lean_object* v_dp_1050_, uint8_t v_period_1051_){
_start:
{
switch(v_period_1051_)
{
case 0:
{
lean_object* v_am_1052_; 
v_am_1052_ = lean_ctor_get(v_dp_1050_, 0);
lean_inc_ref(v_am_1052_);
return v_am_1052_;
}
case 1:
{
lean_object* v_pm_1053_; 
v_pm_1053_ = lean_ctor_get(v_dp_1050_, 1);
lean_inc_ref(v_pm_1053_);
return v_pm_1053_;
}
case 2:
{
lean_object* v_noon_1054_; 
v_noon_1054_ = lean_ctor_get(v_dp_1050_, 2);
lean_inc_ref(v_noon_1054_);
return v_noon_1054_;
}
default: 
{
lean_object* v_midnight_1055_; 
v_midnight_1055_ = lean_ctor_get(v_dp_1050_, 3);
lean_inc_ref(v_midnight_1055_);
return v_midnight_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod___boxed(lean_object* v_dp_1056_, lean_object* v_period_1057_){
_start:
{
uint8_t v_period_boxed_1058_; lean_object* v_res_1059_; 
v_period_boxed_1058_ = lean_unbox(v_period_1057_);
v_res_1059_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dp_1056_, v_period_boxed_1058_);
lean_dec_ref(v_dp_1056_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(uint8_t v_x_1060_){
_start:
{
switch(v_x_1060_)
{
case 0:
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_unsigned_to_nat(0u);
return v___x_1061_;
}
case 1:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_unsigned_to_nat(1u);
return v___x_1062_;
}
case 2:
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_unsigned_to_nat(2u);
return v___x_1063_;
}
case 3:
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_unsigned_to_nat(3u);
return v___x_1064_;
}
case 4:
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_unsigned_to_nat(4u);
return v___x_1065_;
}
default: 
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_unsigned_to_nat(5u);
return v___x_1066_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___boxed(lean_object* v_x_1067_){
_start:
{
uint8_t v_x_112__boxed_1068_; lean_object* v_res_1069_; 
v_x_112__boxed_1068_ = lean_unbox(v_x_1067_);
v_res_1069_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(v_x_112__boxed_1068_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(lean_object* v_arr_1070_, uint8_t v_period_1071_){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(v_period_1071_);
v___x_1073_ = lean_array_fget_borrowed(v_arr_1070_, v___x_1072_);
lean_dec(v___x_1072_);
lean_inc(v___x_1073_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod___boxed(lean_object* v_arr_1074_, lean_object* v_period_1075_){
_start:
{
uint8_t v_period_boxed_1076_; lean_object* v_res_1077_; 
v_period_boxed_1076_ = lean_unbox(v_period_1075_);
v_res_1077_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_arr_1074_, v_period_boxed_1076_);
lean_dec_ref(v_arr_1074_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned(lean_object* v_data_1079_){
_start:
{
lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1080_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1081_ = lean_int_dec_lt(v_data_1079_, v___x_1080_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_1083_ = l_Int_repr(v_data_1079_);
v___x_1084_ = lean_string_append(v___x_1082_, v___x_1083_);
lean_dec_ref(v___x_1083_);
return v___x_1084_;
}
else
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Int_repr(v_data_1079_);
return v___x_1085_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___boxed(lean_object* v_data_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l___private_Std_Time_Format_Basic_0__Std_Time_toSigned(v_data_1086_);
lean_dec(v_data_1086_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___impl(uint8_t v_x_1088_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_box(v_x_1088_);
v___x_1090_ = lean_obj_tag_nat(v___x_1089_);
lean_dec(v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___impl___boxed(lean_object* v_x_1091_){
_start:
{
uint8_t v_x_4__boxed_1092_; lean_object* v_res_1093_; 
v_x_4__boxed_1092_ = lean_unbox(v_x_1091_);
v_res_1093_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___impl(v_x_4__boxed_1092_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg(lean_object* v_k_1094_){
_start:
{
lean_inc(v_k_1094_);
return v_k_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg___boxed(lean_object* v_k_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg(v_k_1095_);
lean_dec(v_k_1095_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(lean_object* v_motive_1097_, lean_object* v_ctorIdx_1098_, uint8_t v_t_1099_, lean_object* v_h_1100_, lean_object* v_k_1101_){
_start:
{
lean_inc(v_k_1101_);
return v_k_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___boxed(lean_object* v_motive_1102_, lean_object* v_ctorIdx_1103_, lean_object* v_t_1104_, lean_object* v_h_1105_, lean_object* v_k_1106_){
_start:
{
uint8_t v_t_boxed_1107_; lean_object* v_res_1108_; 
v_t_boxed_1107_ = lean_unbox(v_t_1104_);
v_res_1108_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(v_motive_1102_, v_ctorIdx_1103_, v_t_boxed_1107_, v_h_1105_, v_k_1106_);
lean_dec(v_k_1106_);
lean_dec(v_ctorIdx_1103_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg(lean_object* v_yes_1109_){
_start:
{
lean_inc(v_yes_1109_);
return v_yes_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg___boxed(lean_object* v_yes_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg(v_yes_1110_);
lean_dec(v_yes_1110_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(lean_object* v_motive_1112_, uint8_t v_t_1113_, lean_object* v_h_1114_, lean_object* v_yes_1115_){
_start:
{
lean_inc(v_yes_1115_);
return v_yes_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___boxed(lean_object* v_motive_1116_, lean_object* v_t_1117_, lean_object* v_h_1118_, lean_object* v_yes_1119_){
_start:
{
uint8_t v_t_boxed_1120_; lean_object* v_res_1121_; 
v_t_boxed_1120_ = lean_unbox(v_t_1117_);
v_res_1121_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(v_motive_1116_, v_t_boxed_1120_, v_h_1118_, v_yes_1119_);
lean_dec(v_yes_1119_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg(lean_object* v_no_1122_){
_start:
{
lean_inc(v_no_1122_);
return v_no_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg___boxed(lean_object* v_no_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg(v_no_1123_);
lean_dec(v_no_1123_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim(lean_object* v_motive_1125_, uint8_t v_t_1126_, lean_object* v_h_1127_, lean_object* v_no_1128_){
_start:
{
lean_inc(v_no_1128_);
return v_no_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___boxed(lean_object* v_motive_1129_, lean_object* v_t_1130_, lean_object* v_h_1131_, lean_object* v_no_1132_){
_start:
{
uint8_t v_t_boxed_1133_; lean_object* v_res_1134_; 
v_t_boxed_1133_ = lean_unbox(v_t_1130_);
v_res_1134_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim(v_motive_1129_, v_t_boxed_1133_, v_h_1131_, v_no_1132_);
lean_dec(v_no_1132_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg(lean_object* v_optional_1135_){
_start:
{
lean_inc(v_optional_1135_);
return v_optional_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg___boxed(lean_object* v_optional_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg(v_optional_1136_);
lean_dec(v_optional_1136_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(lean_object* v_motive_1138_, uint8_t v_t_1139_, lean_object* v_h_1140_, lean_object* v_optional_1141_){
_start:
{
lean_inc(v_optional_1141_);
return v_optional_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___boxed(lean_object* v_motive_1142_, lean_object* v_t_1143_, lean_object* v_h_1144_, lean_object* v_optional_1145_){
_start:
{
uint8_t v_t_boxed_1146_; lean_object* v_res_1147_; 
v_t_boxed_1146_ = lean_unbox(v_t_1143_);
v_res_1147_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(v_motive_1142_, v_t_boxed_1146_, v_h_1144_, v_optional_1145_);
lean_dec(v_optional_1145_);
return v_res_1147_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(uint8_t v_x_1148_, uint8_t v_y_1149_){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1150_ = lean_box(v_x_1148_);
v___x_1151_ = lean_obj_tag_nat(v___x_1150_);
lean_dec(v___x_1150_);
v___x_1152_ = lean_box(v_y_1149_);
v___x_1153_ = lean_obj_tag_nat(v___x_1152_);
lean_dec(v___x_1152_);
v___x_1154_ = lean_nat_dec_eq(v___x_1151_, v___x_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq___boxed(lean_object* v_x_1155_, lean_object* v_y_1156_){
_start:
{
uint8_t v_x_24__boxed_1157_; uint8_t v_y_25__boxed_1158_; uint8_t v_res_1159_; lean_object* v_r_1160_; 
v_x_24__boxed_1157_ = lean_unbox(v_x_1155_);
v_y_25__boxed_1158_ = lean_unbox(v_y_1156_);
v_res_1159_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_x_24__boxed_1157_, v_y_25__boxed_1158_);
v_r_1160_ = lean_box(v_res_1159_);
return v_r_1160_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__1(lean_object* v_a_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Rat_ofInt(v_a_1163_);
return v___x_1164_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_unsigned_to_nat(1000000000u);
v___x_1167_ = lean_nat_to_int(v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(lean_object* v_offset_1168_, uint8_t v_withMinutes_1169_, uint8_t v_withSeconds_1170_, uint8_t v_colon_1171_, uint8_t v_padHour_1172_){
_start:
{
uint32_t v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; uint32_t v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; uint8_t v___y_1192_; uint32_t v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1204_; uint8_t v___y_1205_; uint32_t v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1216_; uint32_t v___y_1217_; uint8_t v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1224_; uint32_t v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v_fst_1238_; lean_object* v_snd_1239_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1251_ = lean_int_dec_le(v___x_1250_, v_offset_1168_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1253_ = lean_int_neg(v_offset_1168_);
lean_dec(v_offset_1168_);
v_fst_1238_ = v___x_1252_;
v_snd_1239_ = v___x_1253_;
goto v___jp_1237_;
}
else
{
lean_object* v___x_1254_; 
v___x_1254_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v_fst_1238_ = v___x_1254_;
v_snd_1239_ = v_offset_1168_;
goto v___jp_1237_;
}
v___jp_1173_:
{
lean_object* v_second_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v_second_1179_ = lean_ctor_get(v___y_1176_, 2);
lean_inc(v_second_1179_);
lean_dec_ref(v___y_1176_);
v___x_1180_ = lean_string_append(v___y_1177_, v___y_1178_);
v___x_1181_ = l_Int_repr(v_second_1179_);
lean_dec(v_second_1179_);
v___x_1182_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___y_1175_, v___y_1174_, v___x_1181_);
lean_dec_ref(v___x_1181_);
v___x_1183_ = lean_string_append(v___x_1180_, v___x_1182_);
lean_dec_ref(v___x_1182_);
return v___x_1183_;
}
v___jp_1184_:
{
if (v_colon_1171_ == 0)
{
lean_object* v___x_1189_; 
v___x_1189_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___y_1174_ = v___y_1185_;
v___y_1175_ = v___y_1186_;
v___y_1176_ = v___y_1187_;
v___y_1177_ = v___y_1188_;
v___y_1178_ = v___x_1189_;
goto v___jp_1173_;
}
else
{
lean_object* v___x_1190_; 
v___x_1190_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___y_1174_ = v___y_1185_;
v___y_1175_ = v___y_1186_;
v___y_1176_ = v___y_1187_;
v___y_1177_ = v___y_1188_;
v___y_1178_ = v___x_1190_;
goto v___jp_1173_;
}
}
v___jp_1191_:
{
uint8_t v___x_1197_; 
v___x_1197_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withSeconds_1170_, v___y_1192_);
if (v___x_1197_ == 0)
{
uint8_t v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = 2;
v___x_1199_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withSeconds_1170_, v___x_1198_);
if (v___x_1199_ == 0)
{
lean_dec_ref(v___y_1195_);
return v___y_1196_;
}
else
{
lean_object* v_second_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v_second_1200_ = lean_ctor_get(v___y_1195_, 2);
v___x_1201_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1202_ = lean_int_dec_eq(v_second_1200_, v___x_1201_);
if (v___x_1202_ == 0)
{
v___y_1185_ = v___y_1193_;
v___y_1186_ = v___y_1194_;
v___y_1187_ = v___y_1195_;
v___y_1188_ = v___y_1196_;
goto v___jp_1184_;
}
else
{
lean_dec_ref(v___y_1195_);
return v___y_1196_;
}
}
}
else
{
v___y_1185_ = v___y_1193_;
v___y_1186_ = v___y_1194_;
v___y_1187_ = v___y_1195_;
v___y_1188_ = v___y_1196_;
goto v___jp_1184_;
}
}
v___jp_1203_:
{
lean_object* v_minute_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v_minute_1210_ = lean_ctor_get(v___y_1208_, 1);
v___x_1211_ = lean_string_append(v___y_1204_, v___y_1209_);
v___x_1212_ = l_Int_repr(v_minute_1210_);
v___x_1213_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___y_1207_, v___y_1206_, v___x_1212_);
lean_dec_ref(v___x_1212_);
v___x_1214_ = lean_string_append(v___x_1211_, v___x_1213_);
lean_dec_ref(v___x_1213_);
v___y_1192_ = v___y_1205_;
v___y_1193_ = v___y_1206_;
v___y_1194_ = v___y_1207_;
v___y_1195_ = v___y_1208_;
v___y_1196_ = v___x_1214_;
goto v___jp_1191_;
}
v___jp_1215_:
{
if (v_colon_1171_ == 0)
{
lean_object* v___x_1221_; 
v___x_1221_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___y_1204_ = v___y_1216_;
v___y_1205_ = v___y_1218_;
v___y_1206_ = v___y_1217_;
v___y_1207_ = v___y_1219_;
v___y_1208_ = v___y_1220_;
v___y_1209_ = v___x_1221_;
goto v___jp_1203_;
}
else
{
lean_object* v___x_1222_; 
v___x_1222_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___y_1204_ = v___y_1216_;
v___y_1205_ = v___y_1218_;
v___y_1206_ = v___y_1217_;
v___y_1207_ = v___y_1219_;
v___y_1208_ = v___y_1220_;
v___y_1209_ = v___x_1222_;
goto v___jp_1203_;
}
}
v___jp_1223_:
{
lean_object* v_data_1229_; uint8_t v___x_1230_; uint8_t v___x_1231_; 
lean_inc_ref(v___y_1224_);
v_data_1229_ = lean_string_append(v___y_1224_, v___y_1228_);
lean_dec_ref(v___y_1228_);
v___x_1230_ = 0;
v___x_1231_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withMinutes_1169_, v___x_1230_);
if (v___x_1231_ == 0)
{
uint8_t v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = 2;
v___x_1233_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withMinutes_1169_, v___x_1232_);
if (v___x_1233_ == 0)
{
v___y_1192_ = v___x_1230_;
v___y_1193_ = v___y_1225_;
v___y_1194_ = v___y_1226_;
v___y_1195_ = v___y_1227_;
v___y_1196_ = v_data_1229_;
goto v___jp_1191_;
}
else
{
lean_object* v_minute_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v_minute_1234_ = lean_ctor_get(v___y_1227_, 1);
v___x_1235_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1236_ = lean_int_dec_eq(v_minute_1234_, v___x_1235_);
if (v___x_1236_ == 0)
{
v___y_1216_ = v_data_1229_;
v___y_1217_ = v___y_1225_;
v___y_1218_ = v___x_1230_;
v___y_1219_ = v___y_1226_;
v___y_1220_ = v___y_1227_;
goto v___jp_1215_;
}
else
{
v___y_1192_ = v___x_1230_;
v___y_1193_ = v___y_1225_;
v___y_1194_ = v___y_1226_;
v___y_1195_ = v___y_1227_;
v___y_1196_ = v_data_1229_;
goto v___jp_1191_;
}
}
}
else
{
v___y_1216_ = v_data_1229_;
v___y_1217_ = v___y_1225_;
v___y_1218_ = v___x_1230_;
v___y_1219_ = v___y_1226_;
v___y_1220_ = v___y_1227_;
goto v___jp_1215_;
}
}
v___jp_1237_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v_time_1242_; lean_object* v___x_1243_; uint32_t v___x_1244_; 
v___x_1240_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_1241_ = lean_int_mul(v_snd_1239_, v___x_1240_);
lean_dec(v_snd_1239_);
v_time_1242_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1241_);
lean_dec(v___x_1241_);
v___x_1243_ = lean_unsigned_to_nat(2u);
v___x_1244_ = 48;
if (v_padHour_1172_ == 0)
{
lean_object* v_hour_1245_; lean_object* v___x_1246_; 
v_hour_1245_ = lean_ctor_get(v_time_1242_, 0);
v___x_1246_ = l_Int_repr(v_hour_1245_);
v___y_1224_ = v_fst_1238_;
v___y_1225_ = v___x_1244_;
v___y_1226_ = v___x_1243_;
v___y_1227_ = v_time_1242_;
v___y_1228_ = v___x_1246_;
goto v___jp_1223_;
}
else
{
lean_object* v_hour_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v_hour_1247_ = lean_ctor_get(v_time_1242_, 0);
v___x_1248_ = l_Int_repr(v_hour_1247_);
v___x_1249_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1243_, v___x_1244_, v___x_1248_);
lean_dec_ref(v___x_1248_);
v___y_1224_ = v_fst_1238_;
v___y_1225_ = v___x_1244_;
v___y_1226_ = v___x_1243_;
v___y_1227_ = v_time_1242_;
v___y_1228_ = v___x_1249_;
goto v___jp_1223_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___boxed(lean_object* v_offset_1255_, lean_object* v_withMinutes_1256_, lean_object* v_withSeconds_1257_, lean_object* v_colon_1258_, lean_object* v_padHour_1259_){
_start:
{
uint8_t v_withMinutes_boxed_1260_; uint8_t v_withSeconds_boxed_1261_; uint8_t v_colon_boxed_1262_; uint8_t v_padHour_boxed_1263_; lean_object* v_res_1264_; 
v_withMinutes_boxed_1260_ = lean_unbox(v_withMinutes_1256_);
v_withSeconds_boxed_1261_ = lean_unbox(v_withSeconds_1257_);
v_colon_boxed_1262_ = lean_unbox(v_colon_1258_);
v_padHour_boxed_1263_ = lean_unbox(v_padHour_1259_);
v_res_1264_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1255_, v_withMinutes_boxed_1260_, v_withSeconds_boxed_1261_, v_colon_boxed_1262_, v_padHour_boxed_1263_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0_spec__0(lean_object* v_a_1265_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_nat_to_int(v_a_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(lean_object* v_a_1267_){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = lean_nat_to_int(v_a_1267_);
v___x_1269_ = l_Rat_ofInt(v___x_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_classifyDayPeriod___lam__0(lean_object* v_minute_1270_, lean_object* v_second_1271_, lean_object* v_00___1272_){
_start:
{
lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1274_ = lean_int_dec_eq(v_minute_1270_, v___x_1273_);
if (v___x_1274_ == 0)
{
return v___x_1274_;
}
else
{
uint8_t v___x_1275_; 
v___x_1275_ = lean_int_dec_eq(v_second_1271_, v___x_1273_);
return v___x_1275_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyDayPeriod___lam__0___boxed(lean_object* v_minute_1276_, lean_object* v_second_1277_, lean_object* v_00___1278_){
_start:
{
uint8_t v_res_1279_; lean_object* v_r_1280_; 
v_res_1279_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1276_, v_second_1277_, v_00___1278_);
lean_dec(v_second_1277_);
lean_dec(v_minute_1276_);
v_r_1280_ = lean_box(v_res_1279_);
return v_r_1280_;
}
}
static lean_object* _init_l_Std_Time_classifyDayPeriod___closed__0(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_unsigned_to_nat(12u);
v___x_1282_ = lean_nat_to_int(v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_classifyDayPeriod(lean_object* v_hour_1283_, lean_object* v_minute_1284_, lean_object* v_second_1285_){
_start:
{
lean_object* v___y_1287_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1298_ = lean_int_dec_eq(v_hour_1283_, v___x_1297_);
if (v___x_1298_ == 0)
{
goto v___jp_1291_;
}
else
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = lean_box(0);
v___x_1300_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1284_, v_second_1285_, v___x_1299_);
if (v___x_1300_ == 0)
{
goto v___jp_1291_;
}
else
{
uint8_t v___x_1301_; 
v___x_1301_ = 3;
return v___x_1301_;
}
}
v___jp_1286_:
{
uint8_t v___x_1288_; 
v___x_1288_ = lean_int_dec_lt(v_hour_1283_, v___y_1287_);
if (v___x_1288_ == 0)
{
uint8_t v___x_1289_; 
v___x_1289_ = 1;
return v___x_1289_;
}
else
{
uint8_t v___x_1290_; 
v___x_1290_ = 0;
return v___x_1290_;
}
}
v___jp_1291_:
{
lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1293_ = lean_int_dec_eq(v_hour_1283_, v___x_1292_);
if (v___x_1293_ == 0)
{
v___y_1287_ = v___x_1292_;
goto v___jp_1286_;
}
else
{
lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = lean_box(0);
v___x_1295_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1284_, v_second_1285_, v___x_1294_);
if (v___x_1295_ == 0)
{
v___y_1287_ = v___x_1292_;
goto v___jp_1286_;
}
else
{
uint8_t v___x_1296_; 
v___x_1296_ = 2;
return v___x_1296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyDayPeriod___boxed(lean_object* v_hour_1302_, lean_object* v_minute_1303_, lean_object* v_second_1304_){
_start:
{
uint8_t v_res_1305_; lean_object* v_r_1306_; 
v_res_1305_ = l_Std_Time_classifyDayPeriod(v_hour_1302_, v_minute_1303_, v_second_1304_);
lean_dec(v_second_1304_);
lean_dec(v_minute_1303_);
lean_dec(v_hour_1302_);
v_r_1306_ = lean_box(v_res_1305_);
return v_r_1306_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__0(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = lean_unsigned_to_nat(6u);
v___x_1308_ = lean_nat_to_int(v___x_1307_);
return v___x_1308_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__1(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_unsigned_to_nat(18u);
v___x_1310_ = lean_nat_to_int(v___x_1309_);
return v___x_1310_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__2(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_unsigned_to_nat(21u);
v___x_1312_ = lean_nat_to_int(v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_classifyExtendedDayPeriod(lean_object* v_hour_1313_, lean_object* v_minute_1314_, lean_object* v_second_1315_){
_start:
{
lean_object* v___y_1317_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1337_ = lean_int_dec_eq(v_hour_1313_, v___x_1336_);
if (v___x_1337_ == 0)
{
goto v___jp_1330_;
}
else
{
lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1338_ = lean_box(0);
v___x_1339_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1314_, v_second_1315_, v___x_1338_);
if (v___x_1339_ == 0)
{
goto v___jp_1330_;
}
else
{
uint8_t v___x_1340_; 
v___x_1340_ = 0;
return v___x_1340_;
}
}
v___jp_1316_:
{
lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__0, &l_Std_Time_classifyExtendedDayPeriod___closed__0_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__0);
v___x_1319_ = lean_int_dec_lt(v_hour_1313_, v___x_1318_);
if (v___x_1319_ == 0)
{
uint8_t v___x_1320_; 
v___x_1320_ = lean_int_dec_lt(v_hour_1313_, v___y_1317_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1321_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__1, &l_Std_Time_classifyExtendedDayPeriod___closed__1_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__1);
v___x_1322_ = lean_int_dec_lt(v_hour_1313_, v___x_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__2, &l_Std_Time_classifyExtendedDayPeriod___closed__2_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__2);
v___x_1324_ = lean_int_dec_lt(v_hour_1313_, v___x_1323_);
if (v___x_1324_ == 0)
{
uint8_t v___x_1325_; 
v___x_1325_ = 1;
return v___x_1325_;
}
else
{
uint8_t v___x_1326_; 
v___x_1326_ = 5;
return v___x_1326_;
}
}
else
{
uint8_t v___x_1327_; 
v___x_1327_ = 4;
return v___x_1327_;
}
}
else
{
uint8_t v___x_1328_; 
v___x_1328_ = 2;
return v___x_1328_;
}
}
else
{
uint8_t v___x_1329_; 
v___x_1329_ = 1;
return v___x_1329_;
}
}
v___jp_1330_:
{
lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1331_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1332_ = lean_int_dec_eq(v_hour_1313_, v___x_1331_);
if (v___x_1332_ == 0)
{
v___y_1317_ = v___x_1331_;
goto v___jp_1316_;
}
else
{
lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1333_ = lean_box(0);
v___x_1334_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1314_, v_second_1315_, v___x_1333_);
if (v___x_1334_ == 0)
{
v___y_1317_ = v___x_1331_;
goto v___jp_1316_;
}
else
{
uint8_t v___x_1335_; 
v___x_1335_ = 3;
return v___x_1335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyExtendedDayPeriod___boxed(lean_object* v_hour_1341_, lean_object* v_minute_1342_, lean_object* v_second_1343_){
_start:
{
uint8_t v_res_1344_; lean_object* v_r_1345_; 
v_res_1344_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1341_, v_minute_1342_, v_second_1343_);
lean_dec(v_second_1343_);
lean_dec(v_minute_1342_);
lean_dec(v_hour_1341_);
v_r_1345_ = lean_box(v_res_1344_);
return v_r_1345_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_unsigned_to_nat(100u);
v___x_1347_ = lean_nat_to_int(v___x_1346_);
return v___x_1347_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_unsigned_to_nat(7u);
v___x_1349_ = lean_nat_to_int(v___x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(lean_object* v_dateformat_1353_, lean_object* v_modifier_1354_, lean_object* v_data_1355_){
_start:
{
switch(lean_obj_tag(v_modifier_1354_))
{
case 0:
{
uint8_t v_presentation_1356_; 
v_presentation_1356_ = lean_ctor_get_uint8(v_modifier_1354_, 0);
lean_dec_ref_known(v_modifier_1354_, 0);
switch(v_presentation_1356_)
{
case 1:
{
lean_object* v_symbols_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; 
v_symbols_1357_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1358_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1359_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(v_symbols_1357_, v___x_1358_);
return v___x_1359_;
}
case 2:
{
lean_object* v_symbols_1360_; uint8_t v___x_1361_; lean_object* v___x_1362_; 
v_symbols_1360_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1361_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1362_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(v_symbols_1360_, v___x_1361_);
return v___x_1362_;
}
default: 
{
lean_object* v_symbols_1363_; uint8_t v___x_1364_; lean_object* v___x_1365_; 
v_symbols_1363_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1364_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1365_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(v_symbols_1363_, v___x_1364_);
return v___x_1365_;
}
}
}
case 1:
{
lean_object* v_presentation_1366_; 
v_presentation_1366_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc(v_presentation_1366_);
lean_dec_ref_known(v_modifier_1354_, 1);
switch(lean_obj_tag(v_presentation_1366_))
{
case 0:
{
lean_object* v___x_1367_; uint8_t v___x_1368_; lean_object* v___x_1369_; 
v___x_1367_ = lean_unsigned_to_nat(0u);
v___x_1368_ = 0;
v___x_1369_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1367_, v_data_1355_, v___x_1368_);
return v___x_1369_;
}
case 1:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; lean_object* v___x_1374_; 
v___x_1370_ = lean_unsigned_to_nat(2u);
v___x_1371_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1372_ = lean_int_emod(v_data_1355_, v___x_1371_);
lean_dec(v_data_1355_);
v___x_1373_ = 0;
v___x_1374_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1370_, v___x_1372_, v___x_1373_);
return v___x_1374_;
}
case 2:
{
lean_object* v___x_1375_; uint8_t v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = lean_unsigned_to_nat(4u);
v___x_1376_ = 0;
v___x_1377_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1375_, v_data_1355_, v___x_1376_);
return v___x_1377_;
}
default: 
{
lean_object* v_num_1378_; uint8_t v___x_1379_; lean_object* v___x_1380_; 
v_num_1378_ = lean_ctor_get(v_presentation_1366_, 0);
lean_inc(v_num_1378_);
lean_dec_ref_known(v_presentation_1366_, 1);
v___x_1379_ = 0;
v___x_1380_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1378_, v_data_1355_, v___x_1379_);
lean_dec(v_num_1378_);
return v___x_1380_;
}
}
}
case 2:
{
lean_object* v_presentation_1381_; lean_object* v___x_1382_; lean_object* v___y_1384_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v_presentation_1381_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc(v_presentation_1381_);
lean_dec_ref_known(v_modifier_1354_, 1);
v___x_1382_ = lean_unsigned_to_nat(0u);
v___x_1398_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1399_ = lean_int_dec_le(v_data_1355_, v___x_1398_);
if (v___x_1399_ == 0)
{
v___y_1384_ = v_data_1355_;
goto v___jp_1383_;
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1400_ = lean_int_neg(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1401_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1402_ = lean_int_add(v___x_1400_, v___x_1401_);
lean_dec(v___x_1400_);
v___y_1384_ = v___x_1402_;
goto v___jp_1383_;
}
v___jp_1383_:
{
switch(lean_obj_tag(v_presentation_1381_))
{
case 0:
{
uint8_t v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = 0;
v___x_1386_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1382_, v___y_1384_, v___x_1385_);
return v___x_1386_;
}
case 1:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; lean_object* v___x_1391_; 
v___x_1387_ = lean_unsigned_to_nat(2u);
v___x_1388_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1389_ = lean_int_emod(v___y_1384_, v___x_1388_);
lean_dec(v___y_1384_);
v___x_1390_ = 0;
v___x_1391_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1387_, v___x_1389_, v___x_1390_);
return v___x_1391_;
}
case 2:
{
lean_object* v___x_1392_; uint8_t v___x_1393_; lean_object* v___x_1394_; 
v___x_1392_ = lean_unsigned_to_nat(4u);
v___x_1393_ = 0;
v___x_1394_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1392_, v___y_1384_, v___x_1393_);
return v___x_1394_;
}
default: 
{
lean_object* v_num_1395_; uint8_t v___x_1396_; lean_object* v___x_1397_; 
v_num_1395_ = lean_ctor_get(v_presentation_1381_, 0);
lean_inc(v_num_1395_);
lean_dec_ref_known(v_presentation_1381_, 1);
v___x_1396_ = 0;
v___x_1397_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1395_, v___y_1384_, v___x_1396_);
lean_dec(v_num_1395_);
return v___x_1397_;
}
}
}
}
case 3:
{
lean_object* v_presentation_1403_; lean_object* v_snd_1404_; uint8_t v___x_1405_; lean_object* v___x_1406_; 
v_presentation_1403_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc(v_presentation_1403_);
lean_dec_ref_known(v_modifier_1354_, 1);
v_snd_1404_ = lean_ctor_get(v_data_1355_, 1);
lean_inc(v_snd_1404_);
lean_dec(v_data_1355_);
v___x_1405_ = 0;
v___x_1406_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1403_, v_snd_1404_, v___x_1405_);
lean_dec(v_presentation_1403_);
return v___x_1406_;
}
case 4:
{
lean_object* v_presentation_1407_; 
v_presentation_1407_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc_ref(v_presentation_1407_);
lean_dec_ref_known(v_modifier_1354_, 1);
if (lean_obj_tag(v_presentation_1407_) == 0)
{
lean_object* v_val_1408_; uint8_t v___x_1409_; lean_object* v___x_1410_; 
v_val_1408_ = lean_ctor_get(v_presentation_1407_, 0);
lean_inc(v_val_1408_);
lean_dec_ref_known(v_presentation_1407_, 1);
v___x_1409_ = 0;
v___x_1410_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1408_, v_data_1355_, v___x_1409_);
lean_dec(v_val_1408_);
return v___x_1410_;
}
else
{
lean_object* v_val_1411_; uint8_t v___x_1412_; 
v_val_1411_ = lean_ctor_get(v_presentation_1407_, 0);
lean_inc(v_val_1411_);
lean_dec_ref_known(v_presentation_1407_, 1);
v___x_1412_ = lean_unbox(v_val_1411_);
lean_dec(v_val_1411_);
switch(v___x_1412_)
{
case 1:
{
lean_object* v_symbols_1413_; lean_object* v___x_1414_; 
v_symbols_1413_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1414_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_1413_, v_data_1355_);
lean_dec(v_data_1355_);
return v___x_1414_;
}
case 2:
{
lean_object* v_symbols_1415_; lean_object* v___x_1416_; 
v_symbols_1415_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1416_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_1415_, v_data_1355_);
lean_dec(v_data_1355_);
return v___x_1416_;
}
default: 
{
lean_object* v_symbols_1417_; lean_object* v___x_1418_; 
v_symbols_1417_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1418_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_1417_, v_data_1355_);
lean_dec(v_data_1355_);
return v___x_1418_;
}
}
}
}
case 5:
{
lean_object* v_presentation_1419_; 
v_presentation_1419_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc_ref(v_presentation_1419_);
lean_dec_ref_known(v_modifier_1354_, 1);
if (lean_obj_tag(v_presentation_1419_) == 0)
{
lean_object* v_val_1420_; uint8_t v___x_1421_; lean_object* v___x_1422_; 
v_val_1420_ = lean_ctor_get(v_presentation_1419_, 0);
lean_inc(v_val_1420_);
lean_dec_ref_known(v_presentation_1419_, 1);
v___x_1421_ = 0;
v___x_1422_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1420_, v_data_1355_, v___x_1421_);
lean_dec(v_val_1420_);
return v___x_1422_;
}
else
{
lean_object* v_val_1423_; uint8_t v___x_1424_; 
v_val_1423_ = lean_ctor_get(v_presentation_1419_, 0);
lean_inc(v_val_1423_);
lean_dec_ref_known(v_presentation_1419_, 1);
v___x_1424_ = lean_unbox(v_val_1423_);
lean_dec(v_val_1423_);
switch(v___x_1424_)
{
case 1:
{
lean_object* v_symbols_1425_; lean_object* v___x_1426_; 
v_symbols_1425_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1426_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_1425_, v_data_1355_);
lean_dec(v_data_1355_);
return v___x_1426_;
}
case 2:
{
lean_object* v_symbols_1427_; lean_object* v___x_1428_; 
v_symbols_1427_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1428_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_1427_, v_data_1355_);
lean_dec(v_data_1355_);
return v___x_1428_;
}
default: 
{
lean_object* v_symbols_1429_; lean_object* v___x_1430_; 
v_symbols_1429_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1430_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_1429_, v_data_1355_);
lean_dec(v_data_1355_);
return v___x_1430_;
}
}
}
}
case 6:
{
lean_object* v_presentation_1431_; uint8_t v___x_1432_; lean_object* v___x_1433_; 
v_presentation_1431_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc(v_presentation_1431_);
lean_dec_ref_known(v_modifier_1354_, 1);
v___x_1432_ = 0;
v___x_1433_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1431_, v_data_1355_, v___x_1432_);
lean_dec(v_presentation_1431_);
return v___x_1433_;
}
case 7:
{
lean_object* v_presentation_1434_; 
v_presentation_1434_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc_ref(v_presentation_1434_);
lean_dec_ref_known(v_modifier_1354_, 1);
if (lean_obj_tag(v_presentation_1434_) == 0)
{
lean_object* v_val_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; 
v_val_1435_ = lean_ctor_get(v_presentation_1434_, 0);
lean_inc(v_val_1435_);
lean_dec_ref_known(v_presentation_1434_, 1);
v___x_1436_ = 0;
v___x_1437_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1435_, v_data_1355_, v___x_1436_);
lean_dec(v_val_1435_);
return v___x_1437_;
}
else
{
lean_object* v_val_1438_; uint8_t v___x_1439_; 
v_val_1438_ = lean_ctor_get(v_presentation_1434_, 0);
lean_inc(v_val_1438_);
lean_dec_ref_known(v_presentation_1434_, 1);
v___x_1439_ = lean_unbox(v_val_1438_);
lean_dec(v_val_1438_);
switch(v___x_1439_)
{
case 0:
{
lean_object* v_symbols_1440_; lean_object* v___x_1441_; 
v_symbols_1440_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1441_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1440_, v_data_1355_);
lean_dec(v_data_1355_);
return v___x_1441_;
}
case 1:
{
lean_object* v_symbols_1442_; lean_object* v___x_1443_; 
v_symbols_1442_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1443_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1442_, v_data_1355_);
lean_dec(v_data_1355_);
return v___x_1443_;
}
case 2:
{
lean_object* v_symbols_1444_; lean_object* v___x_1445_; 
v_symbols_1444_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1445_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1444_, v_data_1355_);
lean_dec(v_data_1355_);
return v___x_1445_;
}
default: 
{
lean_object* v___x_1446_; 
v___x_1446_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_data_1355_);
lean_dec(v_data_1355_);
return v___x_1446_;
}
}
}
}
case 8:
{
lean_object* v_presentation_1447_; 
v_presentation_1447_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc_ref(v_presentation_1447_);
lean_dec_ref_known(v_modifier_1354_, 1);
if (lean_obj_tag(v_presentation_1447_) == 0)
{
lean_object* v_val_1448_; uint8_t v___x_1449_; lean_object* v___x_1450_; 
v_val_1448_ = lean_ctor_get(v_presentation_1447_, 0);
lean_inc(v_val_1448_);
lean_dec_ref_known(v_presentation_1447_, 1);
v___x_1449_ = 0;
v___x_1450_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1448_, v_data_1355_, v___x_1449_);
lean_dec(v_val_1448_);
return v___x_1450_;
}
else
{
lean_object* v_val_1451_; uint8_t v___x_1452_; 
v_val_1451_ = lean_ctor_get(v_presentation_1447_, 0);
lean_inc(v_val_1451_);
lean_dec_ref_known(v_presentation_1447_, 1);
v___x_1452_ = lean_unbox(v_val_1451_);
lean_dec(v_val_1451_);
switch(v___x_1452_)
{
case 0:
{
lean_object* v_symbols_1453_; lean_object* v___x_1454_; 
v_symbols_1453_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1454_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1453_, v_data_1355_);
lean_dec(v_data_1355_);
return v___x_1454_;
}
case 1:
{
lean_object* v_symbols_1455_; lean_object* v___x_1456_; 
v_symbols_1455_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1456_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1455_, v_data_1355_);
lean_dec(v_data_1355_);
return v___x_1456_;
}
case 2:
{
lean_object* v_symbols_1457_; lean_object* v___x_1458_; 
v_symbols_1457_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1458_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1457_, v_data_1355_);
lean_dec(v_data_1355_);
return v___x_1458_;
}
default: 
{
lean_object* v___x_1459_; 
v___x_1459_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_data_1355_);
lean_dec(v_data_1355_);
return v___x_1459_;
}
}
}
}
case 9:
{
lean_object* v_presentation_1460_; lean_object* v___x_1461_; lean_object* v___y_1463_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v_presentation_1460_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc(v_presentation_1460_);
lean_dec_ref_known(v_modifier_1354_, 1);
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1477_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1478_ = lean_int_dec_le(v_data_1355_, v___x_1477_);
if (v___x_1478_ == 0)
{
v___y_1463_ = v_data_1355_;
goto v___jp_1462_;
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1479_ = lean_int_neg(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1480_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1481_ = lean_int_add(v___x_1479_, v___x_1480_);
lean_dec(v___x_1479_);
v___y_1463_ = v___x_1481_;
goto v___jp_1462_;
}
v___jp_1462_:
{
switch(lean_obj_tag(v_presentation_1460_))
{
case 0:
{
uint8_t v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = 0;
v___x_1465_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1461_, v___y_1463_, v___x_1464_);
return v___x_1465_;
}
case 1:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; lean_object* v___x_1470_; 
v___x_1466_ = lean_unsigned_to_nat(2u);
v___x_1467_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1468_ = lean_int_emod(v___y_1463_, v___x_1467_);
lean_dec(v___y_1463_);
v___x_1469_ = 0;
v___x_1470_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1466_, v___x_1468_, v___x_1469_);
return v___x_1470_;
}
case 2:
{
lean_object* v___x_1471_; uint8_t v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = lean_unsigned_to_nat(4u);
v___x_1472_ = 0;
v___x_1473_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1471_, v___y_1463_, v___x_1472_);
return v___x_1473_;
}
default: 
{
lean_object* v_num_1474_; uint8_t v___x_1475_; lean_object* v___x_1476_; 
v_num_1474_ = lean_ctor_get(v_presentation_1460_, 0);
lean_inc(v_num_1474_);
lean_dec_ref_known(v_presentation_1460_, 1);
v___x_1475_ = 0;
v___x_1476_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1474_, v___y_1463_, v___x_1475_);
lean_dec(v_num_1474_);
return v___x_1476_;
}
}
}
}
case 10:
{
lean_object* v_presentation_1482_; uint8_t v___x_1483_; lean_object* v___x_1484_; 
v_presentation_1482_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc(v_presentation_1482_);
lean_dec_ref_known(v_modifier_1354_, 1);
v___x_1483_ = 0;
v___x_1484_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1482_, v_data_1355_, v___x_1483_);
lean_dec(v_presentation_1482_);
return v___x_1484_;
}
case 11:
{
lean_object* v_presentation_1485_; uint8_t v___x_1486_; lean_object* v___x_1487_; 
v_presentation_1485_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc(v_presentation_1485_);
lean_dec_ref_known(v_modifier_1354_, 1);
v___x_1486_ = 0;
v___x_1487_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1485_, v_data_1355_, v___x_1486_);
lean_dec(v_presentation_1485_);
return v___x_1487_;
}
case 12:
{
uint8_t v_presentation_1488_; 
v_presentation_1488_ = lean_ctor_get_uint8(v_modifier_1354_, 0);
lean_dec_ref_known(v_modifier_1354_, 0);
switch(v_presentation_1488_)
{
case 0:
{
lean_object* v_symbols_1489_; uint8_t v___x_1490_; lean_object* v___x_1491_; 
v_symbols_1489_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1490_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1491_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1489_, v___x_1490_);
return v___x_1491_;
}
case 1:
{
lean_object* v_symbols_1492_; uint8_t v___x_1493_; lean_object* v___x_1494_; 
v_symbols_1492_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1493_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1494_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1492_, v___x_1493_);
return v___x_1494_;
}
case 2:
{
lean_object* v_symbols_1495_; uint8_t v___x_1496_; lean_object* v___x_1497_; 
v_symbols_1495_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1496_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1497_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1495_, v___x_1496_);
return v___x_1497_;
}
default: 
{
lean_object* v_symbols_1498_; uint8_t v___x_1499_; lean_object* v___x_1500_; 
v_symbols_1498_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1499_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1500_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1498_, v___x_1499_);
return v___x_1500_;
}
}
}
case 13:
{
lean_object* v_presentation_1501_; 
v_presentation_1501_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc_ref(v_presentation_1501_);
lean_dec_ref_known(v_modifier_1354_, 1);
if (lean_obj_tag(v_presentation_1501_) == 0)
{
lean_object* v_val_1502_; uint8_t v_firstDayOfWeek_1503_; lean_object* v_firstOrd_1504_; uint8_t v___x_1505_; lean_object* v_dayOrd_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; lean_object* v___x_1514_; 
v_val_1502_ = lean_ctor_get(v_presentation_1501_, 0);
lean_inc(v_val_1502_);
lean_dec_ref_known(v_presentation_1501_, 1);
v_firstDayOfWeek_1503_ = lean_ctor_get_uint8(v_dateformat_1353_, sizeof(void*)*2);
v_firstOrd_1504_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_1503_);
v___x_1505_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v_dayOrd_1506_ = l_Std_Time_Weekday_toOrdinal(v___x_1505_);
v___x_1507_ = lean_int_sub(v_dayOrd_1506_, v_firstOrd_1504_);
lean_dec(v_firstOrd_1504_);
lean_dec(v_dayOrd_1506_);
v___x_1508_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_1509_ = lean_int_add(v___x_1507_, v___x_1508_);
lean_dec(v___x_1507_);
v___x_1510_ = lean_int_emod(v___x_1509_, v___x_1508_);
lean_dec(v___x_1509_);
v___x_1511_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1512_ = lean_int_add(v___x_1510_, v___x_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = 0;
v___x_1514_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1502_, v___x_1512_, v___x_1513_);
lean_dec(v_val_1502_);
return v___x_1514_;
}
else
{
lean_object* v_val_1515_; uint8_t v___x_1516_; 
v_val_1515_ = lean_ctor_get(v_presentation_1501_, 0);
lean_inc(v_val_1515_);
lean_dec_ref_known(v_presentation_1501_, 1);
v___x_1516_ = lean_unbox(v_val_1515_);
lean_dec(v_val_1515_);
switch(v___x_1516_)
{
case 0:
{
lean_object* v_symbols_1517_; uint8_t v___x_1518_; lean_object* v___x_1519_; 
v_symbols_1517_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1518_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1519_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1517_, v___x_1518_);
return v___x_1519_;
}
case 1:
{
lean_object* v_symbols_1520_; uint8_t v___x_1521_; lean_object* v___x_1522_; 
v_symbols_1520_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1521_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1522_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1520_, v___x_1521_);
return v___x_1522_;
}
case 2:
{
lean_object* v_symbols_1523_; uint8_t v___x_1524_; lean_object* v___x_1525_; 
v_symbols_1523_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1524_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1525_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1523_, v___x_1524_);
return v___x_1525_;
}
default: 
{
lean_object* v_symbols_1526_; uint8_t v___x_1527_; lean_object* v___x_1528_; 
v_symbols_1526_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1527_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1528_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1526_, v___x_1527_);
return v___x_1528_;
}
}
}
}
case 14:
{
lean_object* v_presentation_1529_; 
v_presentation_1529_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc_ref(v_presentation_1529_);
lean_dec_ref_known(v_modifier_1354_, 1);
if (lean_obj_tag(v_presentation_1529_) == 0)
{
lean_object* v_val_1530_; uint8_t v_firstDayOfWeek_1531_; lean_object* v_firstOrd_1532_; uint8_t v___x_1533_; lean_object* v_dayOrd_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; lean_object* v___x_1542_; 
v_val_1530_ = lean_ctor_get(v_presentation_1529_, 0);
lean_inc(v_val_1530_);
lean_dec_ref_known(v_presentation_1529_, 1);
v_firstDayOfWeek_1531_ = lean_ctor_get_uint8(v_dateformat_1353_, sizeof(void*)*2);
v_firstOrd_1532_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_1531_);
v___x_1533_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v_dayOrd_1534_ = l_Std_Time_Weekday_toOrdinal(v___x_1533_);
v___x_1535_ = lean_int_sub(v_dayOrd_1534_, v_firstOrd_1532_);
lean_dec(v_firstOrd_1532_);
lean_dec(v_dayOrd_1534_);
v___x_1536_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_1537_ = lean_int_add(v___x_1535_, v___x_1536_);
lean_dec(v___x_1535_);
v___x_1538_ = lean_int_emod(v___x_1537_, v___x_1536_);
lean_dec(v___x_1537_);
v___x_1539_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1540_ = lean_int_add(v___x_1538_, v___x_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = 0;
v___x_1542_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1530_, v___x_1540_, v___x_1541_);
lean_dec(v_val_1530_);
return v___x_1542_;
}
else
{
lean_object* v_val_1543_; uint8_t v___x_1544_; 
v_val_1543_ = lean_ctor_get(v_presentation_1529_, 0);
lean_inc(v_val_1543_);
lean_dec_ref_known(v_presentation_1529_, 1);
v___x_1544_ = lean_unbox(v_val_1543_);
lean_dec(v_val_1543_);
switch(v___x_1544_)
{
case 0:
{
lean_object* v_symbols_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; 
v_symbols_1545_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1546_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1547_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1545_, v___x_1546_);
return v___x_1547_;
}
case 1:
{
lean_object* v_symbols_1548_; uint8_t v___x_1549_; lean_object* v___x_1550_; 
v_symbols_1548_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1549_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1550_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1548_, v___x_1549_);
return v___x_1550_;
}
case 2:
{
lean_object* v_symbols_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; 
v_symbols_1551_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1552_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1553_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1551_, v___x_1552_);
return v___x_1553_;
}
default: 
{
lean_object* v_symbols_1554_; uint8_t v___x_1555_; lean_object* v___x_1556_; 
v_symbols_1554_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1555_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1556_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1554_, v___x_1555_);
return v___x_1556_;
}
}
}
}
case 15:
{
lean_object* v_presentation_1557_; uint8_t v___x_1558_; lean_object* v___x_1559_; 
v_presentation_1557_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc(v_presentation_1557_);
lean_dec_ref_known(v_modifier_1354_, 1);
v___x_1558_ = 0;
v___x_1559_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1557_, v_data_1355_, v___x_1558_);
lean_dec(v_presentation_1557_);
return v___x_1559_;
}
case 16:
{
uint8_t v_presentation_1560_; 
v_presentation_1560_ = lean_ctor_get_uint8(v_modifier_1354_, 0);
lean_dec_ref_known(v_modifier_1354_, 0);
if (v_presentation_1560_ == 2)
{
lean_object* v_symbols_1561_; uint8_t v___x_1562_; lean_object* v___x_1563_; 
v_symbols_1561_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1562_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1563_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(v_symbols_1561_, v___x_1562_);
return v___x_1563_;
}
else
{
lean_object* v_symbols_1564_; uint8_t v___x_1565_; lean_object* v___x_1566_; 
v_symbols_1564_ = lean_ctor_get(v_dateformat_1353_, 1);
v___x_1565_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1566_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(v_symbols_1564_, v___x_1565_);
return v___x_1566_;
}
}
case 17:
{
uint8_t v_presentation_1567_; 
v_presentation_1567_ = lean_ctor_get_uint8(v_modifier_1354_, 0);
lean_dec_ref_known(v_modifier_1354_, 0);
switch(v_presentation_1567_)
{
case 1:
{
lean_object* v_symbols_1568_; lean_object* v_dayPeriodLong_1569_; uint8_t v___x_1570_; lean_object* v___x_1571_; 
v_symbols_1568_ = lean_ctor_get(v_dateformat_1353_, 1);
v_dayPeriodLong_1569_ = lean_ctor_get(v_symbols_1568_, 20);
v___x_1570_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1571_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodLong_1569_, v___x_1570_);
return v___x_1571_;
}
case 2:
{
lean_object* v_symbols_1572_; lean_object* v_dayPeriodNarrow_1573_; uint8_t v___x_1574_; lean_object* v___x_1575_; 
v_symbols_1572_ = lean_ctor_get(v_dateformat_1353_, 1);
v_dayPeriodNarrow_1573_ = lean_ctor_get(v_symbols_1572_, 21);
v___x_1574_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1575_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodNarrow_1573_, v___x_1574_);
return v___x_1575_;
}
default: 
{
lean_object* v_symbols_1576_; lean_object* v_dayPeriodShort_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; 
v_symbols_1576_ = lean_ctor_get(v_dateformat_1353_, 1);
v_dayPeriodShort_1577_ = lean_ctor_get(v_symbols_1576_, 19);
v___x_1578_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1579_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodShort_1577_, v___x_1578_);
return v___x_1579_;
}
}
}
case 18:
{
uint8_t v_presentation_1580_; 
v_presentation_1580_ = lean_ctor_get_uint8(v_modifier_1354_, 0);
lean_dec_ref_known(v_modifier_1354_, 0);
switch(v_presentation_1580_)
{
case 1:
{
lean_object* v_symbols_1581_; lean_object* v_extendedDayPeriodLong_1582_; uint8_t v___x_1583_; lean_object* v___x_1584_; 
v_symbols_1581_ = lean_ctor_get(v_dateformat_1353_, 1);
v_extendedDayPeriodLong_1582_ = lean_ctor_get(v_symbols_1581_, 23);
v___x_1583_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1584_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodLong_1582_, v___x_1583_);
return v___x_1584_;
}
case 2:
{
lean_object* v_symbols_1585_; lean_object* v_extendedDayPeriodNarrow_1586_; uint8_t v___x_1587_; lean_object* v___x_1588_; 
v_symbols_1585_ = lean_ctor_get(v_dateformat_1353_, 1);
v_extendedDayPeriodNarrow_1586_ = lean_ctor_get(v_symbols_1585_, 24);
v___x_1587_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1588_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodNarrow_1586_, v___x_1587_);
return v___x_1588_;
}
default: 
{
lean_object* v_symbols_1589_; lean_object* v_extendedDayPeriodShort_1590_; uint8_t v___x_1591_; lean_object* v___x_1592_; 
v_symbols_1589_ = lean_ctor_get(v_dateformat_1353_, 1);
v_extendedDayPeriodShort_1590_ = lean_ctor_get(v_symbols_1589_, 22);
v___x_1591_ = lean_unbox(v_data_1355_);
lean_dec(v_data_1355_);
v___x_1592_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodShort_1590_, v___x_1591_);
return v___x_1592_;
}
}
}
case 19:
{
lean_object* v_presentation_1593_; uint8_t v___x_1594_; lean_object* v___x_1595_; 
v_presentation_1593_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc(v_presentation_1593_);
lean_dec_ref_known(v_modifier_1354_, 1);
v___x_1594_ = 0;
v___x_1595_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1593_, v_data_1355_, v___x_1594_);
lean_dec(v_presentation_1593_);
return v___x_1595_;
}
case 20:
{
lean_object* v_presentation_1596_; uint8_t v___x_1597_; lean_object* v___x_1598_; 
v_presentation_1596_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc(v_presentation_1596_);
lean_dec_ref_known(v_modifier_1354_, 1);
v___x_1597_ = 0;
v___x_1598_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1596_, v_data_1355_, v___x_1597_);
lean_dec(v_presentation_1596_);
return v___x_1598_;
}
case 21:
{
lean_object* v_presentation_1599_; uint8_t v___x_1600_; lean_object* v___x_1601_; 
v_presentation_1599_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc(v_presentation_1599_);
lean_dec_ref_known(v_modifier_1354_, 1);
v___x_1600_ = 0;
v___x_1601_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1599_, v_data_1355_, v___x_1600_);
lean_dec(v_presentation_1599_);
return v___x_1601_;
}
case 22:
{
lean_object* v_presentation_1602_; uint8_t v___x_1603_; lean_object* v___x_1604_; 
v_presentation_1602_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc(v_presentation_1602_);
lean_dec_ref_known(v_modifier_1354_, 1);
v___x_1603_ = 0;
v___x_1604_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1602_, v_data_1355_, v___x_1603_);
lean_dec(v_presentation_1602_);
return v___x_1604_;
}
case 23:
{
lean_object* v_presentation_1605_; uint8_t v___x_1606_; lean_object* v___x_1607_; 
v_presentation_1605_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc(v_presentation_1605_);
lean_dec_ref_known(v_modifier_1354_, 1);
v___x_1606_ = 0;
v___x_1607_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1605_, v_data_1355_, v___x_1606_);
lean_dec(v_presentation_1605_);
return v___x_1607_;
}
case 24:
{
lean_object* v_presentation_1608_; uint8_t v___x_1609_; lean_object* v___x_1610_; 
v_presentation_1608_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc(v_presentation_1608_);
lean_dec_ref_known(v_modifier_1354_, 1);
v___x_1609_ = 0;
v___x_1610_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1608_, v_data_1355_, v___x_1609_);
lean_dec(v_presentation_1608_);
return v___x_1610_;
}
case 25:
{
lean_object* v_presentation_1611_; 
v_presentation_1611_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc(v_presentation_1611_);
lean_dec_ref_known(v_modifier_1354_, 1);
if (lean_obj_tag(v_presentation_1611_) == 0)
{
lean_object* v___x_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = lean_unsigned_to_nat(9u);
v___x_1613_ = 0;
v___x_1614_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1612_, v_data_1355_, v___x_1613_);
return v___x_1614_;
}
else
{
lean_object* v_digits_1615_; lean_object* v___x_1616_; uint32_t v___x_1617_; lean_object* v___x_1618_; lean_object* v_s_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v_digits_1615_ = lean_ctor_get(v_presentation_1611_, 0);
lean_inc(v_digits_1615_);
lean_dec_ref_known(v_presentation_1611_, 1);
v___x_1616_ = lean_unsigned_to_nat(9u);
v___x_1617_ = 48;
v___x_1618_ = l_Int_repr(v_data_1355_);
lean_dec(v_data_1355_);
v_s_1619_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1616_, v___x_1617_, v___x_1618_);
lean_dec_ref(v___x_1618_);
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = lean_string_utf8_byte_size(v_s_1619_);
lean_inc_ref(v_s_1619_);
v___x_1622_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1622_, 0, v_s_1619_);
lean_ctor_set(v___x_1622_, 1, v___x_1620_);
lean_ctor_set(v___x_1622_, 2, v___x_1621_);
v___x_1623_ = l_String_Slice_Pos_nextn(v___x_1622_, v___x_1620_, v_digits_1615_);
lean_dec_ref_known(v___x_1622_, 3);
v___x_1624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1624_, 0, v_s_1619_);
lean_ctor_set(v___x_1624_, 1, v___x_1620_);
lean_ctor_set(v___x_1624_, 2, v___x_1623_);
v___x_1625_ = l_String_Slice_toString(v___x_1624_);
lean_dec_ref_known(v___x_1624_, 3);
return v___x_1625_;
}
}
case 26:
{
lean_object* v_presentation_1626_; uint8_t v___x_1627_; lean_object* v___x_1628_; 
v_presentation_1626_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc(v_presentation_1626_);
lean_dec_ref_known(v_modifier_1354_, 1);
v___x_1627_ = 0;
v___x_1628_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1626_, v_data_1355_, v___x_1627_);
lean_dec(v_presentation_1626_);
return v___x_1628_;
}
case 27:
{
lean_object* v_presentation_1629_; uint8_t v___x_1630_; lean_object* v___x_1631_; 
v_presentation_1629_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc(v_presentation_1629_);
lean_dec_ref_known(v_modifier_1354_, 1);
v___x_1630_ = 0;
v___x_1631_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1629_, v_data_1355_, v___x_1630_);
lean_dec(v_presentation_1629_);
return v___x_1631_;
}
case 28:
{
lean_object* v_presentation_1632_; uint8_t v___x_1633_; lean_object* v___x_1634_; 
v_presentation_1632_ = lean_ctor_get(v_modifier_1354_, 0);
lean_inc(v_presentation_1632_);
lean_dec_ref_known(v_modifier_1354_, 1);
v___x_1633_ = 0;
v___x_1634_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1632_, v_data_1355_, v___x_1633_);
lean_dec(v_presentation_1632_);
return v___x_1634_;
}
case 29:
{
uint8_t v_presentation_1635_; 
v_presentation_1635_ = lean_ctor_get_uint8(v_modifier_1354_, 0);
lean_dec_ref_known(v_modifier_1354_, 0);
if (v_presentation_1635_ == 0)
{
lean_object* v___x_1636_; 
lean_dec(v_data_1355_);
v___x_1636_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
return v___x_1636_;
}
else
{
return v_data_1355_;
}
}
case 32:
{
uint8_t v_presentation_1637_; 
v_presentation_1637_ = lean_ctor_get_uint8(v_modifier_1354_, 0);
lean_dec_ref_known(v_modifier_1354_, 0);
if (v_presentation_1637_ == 0)
{
lean_object* v_fst_1639_; lean_object* v_snd_1640_; lean_object* v___x_1663_; uint8_t v___x_1664_; 
v___x_1663_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1664_ = lean_int_dec_eq(v_data_1355_, v___x_1663_);
if (v___x_1664_ == 0)
{
uint8_t v___x_1665_; 
v___x_1665_ = lean_int_dec_le(v___x_1663_, v_data_1355_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1667_ = lean_int_neg(v_data_1355_);
lean_dec(v_data_1355_);
v_fst_1639_ = v___x_1666_;
v_snd_1640_ = v___x_1667_;
goto v___jp_1638_;
}
else
{
lean_object* v___x_1668_; 
v___x_1668_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v_fst_1639_ = v___x_1668_;
v_snd_1640_ = v_data_1355_;
goto v___jp_1638_;
}
}
else
{
lean_object* v___x_1669_; 
lean_dec(v_data_1355_);
v___x_1669_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1669_;
}
v___jp_1638_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v_t_1643_; lean_object* v_hour_1644_; lean_object* v_minute_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1641_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_1642_ = lean_int_mul(v_snd_1640_, v___x_1641_);
lean_dec(v_snd_1640_);
v_t_1643_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1642_);
lean_dec(v___x_1642_);
v_hour_1644_ = lean_ctor_get(v_t_1643_, 0);
lean_inc(v_hour_1644_);
v_minute_1645_ = lean_ctor_get(v_t_1643_, 1);
lean_inc(v_minute_1645_);
lean_dec_ref(v_t_1643_);
v___x_1646_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1647_ = lean_int_dec_eq(v_minute_1645_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; uint32_t v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1648_ = lean_unsigned_to_nat(2u);
v___x_1649_ = 48;
v___x_1650_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1651_ = lean_string_append(v___x_1650_, v_fst_1639_);
v___x_1652_ = l_Int_repr(v_hour_1644_);
lean_dec(v_hour_1644_);
v___x_1653_ = lean_string_append(v___x_1651_, v___x_1652_);
lean_dec_ref(v___x_1652_);
v___x_1654_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___x_1655_ = lean_string_append(v___x_1653_, v___x_1654_);
v___x_1656_ = l_Int_repr(v_minute_1645_);
lean_dec(v_minute_1645_);
v___x_1657_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1648_, v___x_1649_, v___x_1656_);
lean_dec_ref(v___x_1656_);
v___x_1658_ = lean_string_append(v___x_1655_, v___x_1657_);
lean_dec_ref(v___x_1657_);
return v___x_1658_;
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
lean_dec(v_minute_1645_);
v___x_1659_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1660_ = lean_string_append(v___x_1659_, v_fst_1639_);
v___x_1661_ = l_Int_repr(v_hour_1644_);
lean_dec(v_hour_1644_);
v___x_1662_ = lean_string_append(v___x_1660_, v___x_1661_);
lean_dec_ref(v___x_1661_);
return v___x_1662_;
}
}
}
else
{
lean_object* v___x_1670_; uint8_t v___x_1671_; 
v___x_1670_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1671_ = lean_int_dec_eq(v_data_1355_, v___x_1670_);
if (v___x_1671_ == 0)
{
uint8_t v___x_1672_; lean_object* v___x_1673_; uint8_t v___x_1674_; uint8_t v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1672_ = 1;
v___x_1673_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1674_ = 0;
v___x_1675_ = 1;
v___x_1676_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1355_, v___x_1674_, v___x_1675_, v___x_1672_, v___x_1672_);
v___x_1677_ = lean_string_append(v___x_1673_, v___x_1676_);
lean_dec_ref(v___x_1676_);
return v___x_1677_;
}
else
{
lean_object* v___x_1678_; 
lean_dec(v_data_1355_);
v___x_1678_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1678_;
}
}
}
case 33:
{
uint8_t v_presentation_1679_; lean_object* v___x_1680_; uint8_t v___x_1681_; 
v_presentation_1679_ = lean_ctor_get_uint8(v_modifier_1354_, 0);
lean_dec_ref_known(v_modifier_1354_, 0);
v___x_1680_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1681_ = lean_int_dec_eq(v_data_1355_, v___x_1680_);
if (v___x_1681_ == 0)
{
uint8_t v___x_1682_; 
v___x_1682_ = 1;
switch(v_presentation_1679_)
{
case 0:
{
uint8_t v___x_1683_; uint8_t v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = 2;
v___x_1684_ = 1;
v___x_1685_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1355_, v___x_1683_, v___x_1684_, v___x_1681_, v___x_1682_);
return v___x_1685_;
}
case 1:
{
uint8_t v___x_1686_; uint8_t v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = 0;
v___x_1687_ = 1;
v___x_1688_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1355_, v___x_1686_, v___x_1687_, v___x_1681_, v___x_1682_);
return v___x_1688_;
}
case 2:
{
uint8_t v___x_1689_; uint8_t v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = 0;
v___x_1690_ = 1;
v___x_1691_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1355_, v___x_1689_, v___x_1690_, v___x_1682_, v___x_1682_);
return v___x_1691_;
}
case 3:
{
uint8_t v___x_1692_; uint8_t v___x_1693_; lean_object* v___x_1694_; 
v___x_1692_ = 0;
v___x_1693_ = 2;
v___x_1694_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1355_, v___x_1692_, v___x_1693_, v___x_1681_, v___x_1682_);
return v___x_1694_;
}
default: 
{
uint8_t v___x_1695_; uint8_t v___x_1696_; lean_object* v___x_1697_; 
v___x_1695_ = 0;
v___x_1696_ = 2;
v___x_1697_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1355_, v___x_1695_, v___x_1696_, v___x_1682_, v___x_1682_);
return v___x_1697_;
}
}
}
else
{
lean_object* v___x_1698_; 
lean_dec(v_data_1355_);
v___x_1698_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
return v___x_1698_;
}
}
case 34:
{
uint8_t v_presentation_1699_; 
v_presentation_1699_ = lean_ctor_get_uint8(v_modifier_1354_, 0);
lean_dec_ref_known(v_modifier_1354_, 0);
switch(v_presentation_1699_)
{
case 0:
{
uint8_t v___x_1700_; uint8_t v___x_1701_; uint8_t v___x_1702_; uint8_t v___x_1703_; lean_object* v___x_1704_; 
v___x_1700_ = 2;
v___x_1701_ = 1;
v___x_1702_ = 0;
v___x_1703_ = 1;
v___x_1704_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1355_, v___x_1700_, v___x_1701_, v___x_1702_, v___x_1703_);
return v___x_1704_;
}
case 1:
{
uint8_t v___x_1705_; uint8_t v___x_1706_; uint8_t v___x_1707_; uint8_t v___x_1708_; lean_object* v___x_1709_; 
v___x_1705_ = 0;
v___x_1706_ = 1;
v___x_1707_ = 0;
v___x_1708_ = 1;
v___x_1709_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1355_, v___x_1705_, v___x_1706_, v___x_1707_, v___x_1708_);
return v___x_1709_;
}
case 2:
{
uint8_t v___x_1710_; uint8_t v___x_1711_; uint8_t v___x_1712_; lean_object* v___x_1713_; 
v___x_1710_ = 0;
v___x_1711_ = 1;
v___x_1712_ = 1;
v___x_1713_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1355_, v___x_1710_, v___x_1711_, v___x_1712_, v___x_1712_);
return v___x_1713_;
}
case 3:
{
uint8_t v___x_1714_; uint8_t v___x_1715_; uint8_t v___x_1716_; uint8_t v___x_1717_; lean_object* v___x_1718_; 
v___x_1714_ = 0;
v___x_1715_ = 2;
v___x_1716_ = 0;
v___x_1717_ = 1;
v___x_1718_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1355_, v___x_1714_, v___x_1715_, v___x_1716_, v___x_1717_);
return v___x_1718_;
}
default: 
{
uint8_t v___x_1719_; uint8_t v___x_1720_; uint8_t v___x_1721_; lean_object* v___x_1722_; 
v___x_1719_ = 0;
v___x_1720_ = 2;
v___x_1721_ = 1;
v___x_1722_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1355_, v___x_1719_, v___x_1720_, v___x_1721_, v___x_1721_);
return v___x_1722_;
}
}
}
case 35:
{
uint8_t v_presentation_1723_; 
v_presentation_1723_ = lean_ctor_get_uint8(v_modifier_1354_, 0);
lean_dec_ref_known(v_modifier_1354_, 0);
switch(v_presentation_1723_)
{
case 0:
{
uint8_t v___x_1724_; uint8_t v___x_1725_; uint8_t v___x_1726_; uint8_t v___x_1727_; lean_object* v___x_1728_; 
v___x_1724_ = 0;
v___x_1725_ = 2;
v___x_1726_ = 0;
v___x_1727_ = 1;
v___x_1728_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1355_, v___x_1724_, v___x_1725_, v___x_1726_, v___x_1727_);
return v___x_1728_;
}
case 1:
{
lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1729_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1730_ = lean_int_dec_eq(v_data_1355_, v___x_1729_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; uint8_t v___x_1732_; uint8_t v___x_1733_; uint8_t v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1731_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1732_ = 0;
v___x_1733_ = 1;
v___x_1734_ = 1;
v___x_1735_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1355_, v___x_1732_, v___x_1733_, v___x_1734_, v___x_1734_);
v___x_1736_ = lean_string_append(v___x_1731_, v___x_1735_);
lean_dec_ref(v___x_1735_);
return v___x_1736_;
}
else
{
lean_object* v___x_1737_; 
lean_dec(v_data_1355_);
v___x_1737_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1737_;
}
}
default: 
{
lean_object* v___x_1738_; uint8_t v___x_1739_; 
v___x_1738_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1739_ = lean_int_dec_eq(v_data_1355_, v___x_1738_);
if (v___x_1739_ == 0)
{
uint8_t v___x_1740_; uint8_t v___x_1741_; uint8_t v___x_1742_; lean_object* v___x_1743_; 
v___x_1740_ = 1;
v___x_1741_ = 0;
v___x_1742_ = 2;
v___x_1743_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1355_, v___x_1741_, v___x_1742_, v___x_1740_, v___x_1740_);
return v___x_1743_;
}
else
{
lean_object* v___x_1744_; 
lean_dec(v_data_1355_);
v___x_1744_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
return v___x_1744_;
}
}
}
}
default: 
{
lean_dec_ref(v_modifier_1354_);
return v_data_1355_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___boxed(lean_object* v_dateformat_1745_, lean_object* v_modifier_1746_, lean_object* v_data_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_1745_, v_modifier_1746_, v_data_1747_);
lean_dec_ref(v_dateformat_1745_);
return v_res_1748_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = lean_unsigned_to_nat(4u);
v___x_1750_ = lean_nat_to_int(v___x_1749_);
return v___x_1750_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_unsigned_to_nat(400u);
v___x_1752_ = lean_nat_to_int(v___x_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(lean_object* v_modifier_1753_, lean_object* v_dateformat_1754_, lean_object* v_date_1755_){
_start:
{
lean_object* v_month_1757_; lean_object* v_day_1758_; uint8_t v___y_1759_; uint8_t v___y_1760_; uint8_t v_firstDayOfWeek_1765_; lean_object* v_minimalDaysInFirstWeek_1766_; lean_object* v_date_1767_; lean_object* v_timezone_1768_; uint8_t v___y_1770_; 
v_firstDayOfWeek_1765_ = lean_ctor_get_uint8(v_dateformat_1754_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_1766_ = lean_ctor_get(v_dateformat_1754_, 0);
v_date_1767_ = lean_ctor_get(v_date_1755_, 0);
v_timezone_1768_ = lean_ctor_get(v_date_1755_, 3);
switch(lean_obj_tag(v_modifier_1753_))
{
case 0:
{
lean_object* v___x_1803_; lean_object* v_date_1804_; lean_object* v_year_1805_; uint8_t v___x_1806_; lean_object* v___x_1807_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1803_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_date_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc_ref(v_date_1804_);
lean_dec(v___x_1803_);
v_year_1805_ = lean_ctor_get(v_date_1804_, 0);
lean_inc(v_year_1805_);
lean_dec_ref(v_date_1804_);
v___x_1806_ = l_Std_Time_Year_Offset_era(v_year_1805_);
lean_dec(v_year_1805_);
v___x_1807_ = lean_box(v___x_1806_);
return v___x_1807_;
}
case 1:
{
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
goto v___jp_1799_;
}
case 2:
{
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
goto v___jp_1799_;
}
case 3:
{
lean_object* v___x_1808_; lean_object* v_date_1809_; lean_object* v_year_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1808_ = lean_thunk_get_own(v_date_1767_);
v_date_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc_ref(v_date_1809_);
lean_dec(v___x_1808_);
v_year_1810_ = lean_ctor_get(v_date_1809_, 0);
lean_inc(v_year_1810_);
lean_dec_ref(v_date_1809_);
v___x_1811_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_1812_ = lean_int_mod(v_year_1810_, v___x_1811_);
v___x_1813_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1814_ = lean_int_dec_eq(v___x_1812_, v___x_1813_);
lean_dec(v___x_1812_);
if (v___x_1814_ == 0)
{
lean_dec(v_year_1810_);
v___y_1770_ = v___x_1814_;
goto v___jp_1769_;
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1815_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1816_ = lean_int_mod(v_year_1810_, v___x_1815_);
v___x_1817_ = lean_int_dec_eq(v___x_1816_, v___x_1813_);
lean_dec(v___x_1816_);
if (v___x_1817_ == 0)
{
lean_dec(v_year_1810_);
v___y_1770_ = v___x_1814_;
goto v___jp_1769_;
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1818_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_1819_ = lean_int_mod(v_year_1810_, v___x_1818_);
lean_dec(v_year_1810_);
v___x_1820_ = lean_int_dec_eq(v___x_1819_, v___x_1813_);
lean_dec(v___x_1819_);
v___y_1770_ = v___x_1820_;
goto v___jp_1769_;
}
}
}
case 4:
{
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
goto v___jp_1795_;
}
case 5:
{
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
goto v___jp_1795_;
}
case 6:
{
lean_object* v___x_1821_; lean_object* v_date_1822_; lean_object* v_day_1823_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1821_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_date_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc_ref(v_date_1822_);
lean_dec(v___x_1821_);
v_day_1823_ = lean_ctor_get(v_date_1822_, 2);
lean_inc(v_day_1823_);
lean_dec_ref(v_date_1822_);
return v_day_1823_;
}
case 7:
{
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
goto v___jp_1791_;
}
case 8:
{
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
goto v___jp_1791_;
}
case 9:
{
lean_object* v___x_1824_; lean_object* v_date_1825_; lean_object* v___x_1826_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1824_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_date_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc_ref(v_date_1825_);
lean_dec(v___x_1824_);
v___x_1826_ = l_Std_Time_PlainDate_weekYear(v_date_1825_, v_firstDayOfWeek_1765_, v_minimalDaysInFirstWeek_1766_);
return v___x_1826_;
}
case 10:
{
lean_object* v___x_1827_; lean_object* v_date_1828_; lean_object* v___x_1829_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1827_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_date_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc_ref(v_date_1828_);
lean_dec(v___x_1827_);
v___x_1829_ = l_Std_Time_PlainDate_weekOfYear(v_date_1828_, v_firstDayOfWeek_1765_, v_minimalDaysInFirstWeek_1766_);
return v___x_1829_;
}
case 11:
{
lean_object* v___x_1830_; lean_object* v_date_1831_; lean_object* v___x_1832_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1830_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_date_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc_ref(v_date_1831_);
lean_dec(v___x_1830_);
v___x_1832_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1831_, v_firstDayOfWeek_1765_);
return v___x_1832_;
}
case 12:
{
lean_object* v___x_1833_; lean_object* v_date_1834_; uint8_t v___x_1835_; lean_object* v___x_1836_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1833_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_date_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc_ref(v_date_1834_);
lean_dec(v___x_1833_);
v___x_1835_ = l_Std_Time_PlainDate_weekday(v_date_1834_);
v___x_1836_ = lean_box(v___x_1835_);
return v___x_1836_;
}
case 13:
{
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
goto v___jp_1786_;
}
case 14:
{
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
goto v___jp_1786_;
}
case 15:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Std_Time_DateTime_alignedWeekOfMonth(v_date_1755_);
lean_dec_ref(v_date_1755_);
return v___x_1837_;
}
case 16:
{
lean_object* v___x_1838_; lean_object* v_time_1839_; lean_object* v_hour_1840_; uint8_t v___x_1841_; lean_object* v___x_1842_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1838_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_time_1839_ = lean_ctor_get(v___x_1838_, 1);
lean_inc_ref(v_time_1839_);
lean_dec(v___x_1838_);
v_hour_1840_ = lean_ctor_get(v_time_1839_, 0);
lean_inc(v_hour_1840_);
lean_dec_ref(v_time_1839_);
v___x_1841_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1840_);
lean_dec(v_hour_1840_);
v___x_1842_ = lean_box(v___x_1841_);
return v___x_1842_;
}
case 17:
{
lean_object* v___x_1843_; lean_object* v_time_1844_; lean_object* v_hour_1845_; lean_object* v_minute_1846_; lean_object* v_second_1847_; uint8_t v___x_1848_; lean_object* v___x_1849_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1843_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_time_1844_ = lean_ctor_get(v___x_1843_, 1);
lean_inc_ref(v_time_1844_);
lean_dec(v___x_1843_);
v_hour_1845_ = lean_ctor_get(v_time_1844_, 0);
lean_inc(v_hour_1845_);
v_minute_1846_ = lean_ctor_get(v_time_1844_, 1);
lean_inc(v_minute_1846_);
v_second_1847_ = lean_ctor_get(v_time_1844_, 2);
lean_inc(v_second_1847_);
lean_dec_ref(v_time_1844_);
v___x_1848_ = l_Std_Time_classifyDayPeriod(v_hour_1845_, v_minute_1846_, v_second_1847_);
lean_dec(v_second_1847_);
lean_dec(v_minute_1846_);
lean_dec(v_hour_1845_);
v___x_1849_ = lean_box(v___x_1848_);
return v___x_1849_;
}
case 18:
{
lean_object* v___x_1850_; lean_object* v_time_1851_; lean_object* v_hour_1852_; lean_object* v_minute_1853_; lean_object* v_second_1854_; uint8_t v___x_1855_; lean_object* v___x_1856_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1850_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_time_1851_ = lean_ctor_get(v___x_1850_, 1);
lean_inc_ref(v_time_1851_);
lean_dec(v___x_1850_);
v_hour_1852_ = lean_ctor_get(v_time_1851_, 0);
lean_inc(v_hour_1852_);
v_minute_1853_ = lean_ctor_get(v_time_1851_, 1);
lean_inc(v_minute_1853_);
v_second_1854_ = lean_ctor_get(v_time_1851_, 2);
lean_inc(v_second_1854_);
lean_dec_ref(v_time_1851_);
v___x_1855_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1852_, v_minute_1853_, v_second_1854_);
lean_dec(v_second_1854_);
lean_dec(v_minute_1853_);
lean_dec(v_hour_1852_);
v___x_1856_ = lean_box(v___x_1855_);
return v___x_1856_;
}
case 19:
{
lean_object* v___x_1857_; lean_object* v_time_1858_; lean_object* v_hour_1859_; lean_object* v___x_1860_; lean_object* v_fst_1861_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1857_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_time_1858_ = lean_ctor_get(v___x_1857_, 1);
lean_inc_ref(v_time_1858_);
lean_dec(v___x_1857_);
v_hour_1859_ = lean_ctor_get(v_time_1858_, 0);
lean_inc(v_hour_1859_);
lean_dec_ref(v_time_1858_);
v___x_1860_ = l_Std_Time_HourMarker_toRelative(v_hour_1859_);
v_fst_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_fst_1861_);
lean_dec_ref(v___x_1860_);
return v_fst_1861_;
}
case 20:
{
lean_object* v___x_1862_; lean_object* v_time_1863_; lean_object* v_hour_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1862_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_time_1863_ = lean_ctor_get(v___x_1862_, 1);
lean_inc_ref(v_time_1863_);
lean_dec(v___x_1862_);
v_hour_1864_ = lean_ctor_get(v_time_1863_, 0);
lean_inc(v_hour_1864_);
lean_dec_ref(v_time_1863_);
v___x_1865_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1866_ = lean_int_emod(v_hour_1864_, v___x_1865_);
lean_dec(v_hour_1864_);
return v___x_1866_;
}
case 21:
{
lean_object* v___x_1867_; lean_object* v_time_1868_; lean_object* v_hour_1869_; lean_object* v___x_1870_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1867_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_time_1868_ = lean_ctor_get(v___x_1867_, 1);
lean_inc_ref(v_time_1868_);
lean_dec(v___x_1867_);
v_hour_1869_ = lean_ctor_get(v_time_1868_, 0);
lean_inc(v_hour_1869_);
lean_dec_ref(v_time_1868_);
v___x_1870_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_1869_);
lean_dec(v_hour_1869_);
return v___x_1870_;
}
case 22:
{
lean_object* v___x_1871_; lean_object* v_time_1872_; lean_object* v_hour_1873_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1871_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_time_1872_ = lean_ctor_get(v___x_1871_, 1);
lean_inc_ref(v_time_1872_);
lean_dec(v___x_1871_);
v_hour_1873_ = lean_ctor_get(v_time_1872_, 0);
lean_inc(v_hour_1873_);
lean_dec_ref(v_time_1872_);
return v_hour_1873_;
}
case 23:
{
lean_object* v___x_1874_; lean_object* v_time_1875_; lean_object* v_minute_1876_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1874_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_time_1875_ = lean_ctor_get(v___x_1874_, 1);
lean_inc_ref(v_time_1875_);
lean_dec(v___x_1874_);
v_minute_1876_ = lean_ctor_get(v_time_1875_, 1);
lean_inc(v_minute_1876_);
lean_dec_ref(v_time_1875_);
return v_minute_1876_;
}
case 24:
{
lean_object* v___x_1877_; lean_object* v_time_1878_; lean_object* v_second_1879_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1877_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_time_1878_ = lean_ctor_get(v___x_1877_, 1);
lean_inc_ref(v_time_1878_);
lean_dec(v___x_1877_);
v_second_1879_ = lean_ctor_get(v_time_1878_, 2);
lean_inc(v_second_1879_);
lean_dec_ref(v_time_1878_);
return v_second_1879_;
}
case 25:
{
lean_object* v___x_1880_; lean_object* v_time_1881_; lean_object* v_nanosecond_1882_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1880_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_time_1881_ = lean_ctor_get(v___x_1880_, 1);
lean_inc_ref(v_time_1881_);
lean_dec(v___x_1880_);
v_nanosecond_1882_ = lean_ctor_get(v_time_1881_, 3);
lean_inc(v_nanosecond_1882_);
lean_dec_ref(v_time_1881_);
return v_nanosecond_1882_;
}
case 26:
{
lean_object* v___x_1883_; lean_object* v_time_1884_; lean_object* v___x_1885_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1883_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_time_1884_ = lean_ctor_get(v___x_1883_, 1);
lean_inc_ref(v_time_1884_);
lean_dec(v___x_1883_);
v___x_1885_ = l_Std_Time_PlainTime_toMilliseconds(v_time_1884_);
lean_dec_ref(v_time_1884_);
return v___x_1885_;
}
case 27:
{
lean_object* v___x_1886_; lean_object* v_time_1887_; lean_object* v_nanosecond_1888_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1886_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_time_1887_ = lean_ctor_get(v___x_1886_, 1);
lean_inc_ref(v_time_1887_);
lean_dec(v___x_1886_);
v_nanosecond_1888_ = lean_ctor_get(v_time_1887_, 3);
lean_inc(v_nanosecond_1888_);
lean_dec_ref(v_time_1887_);
return v_nanosecond_1888_;
}
case 28:
{
lean_object* v___x_1889_; lean_object* v_time_1890_; lean_object* v___x_1891_; 
lean_inc_ref(v_date_1767_);
lean_dec_ref(v_date_1755_);
v___x_1889_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_time_1890_ = lean_ctor_get(v___x_1889_, 1);
lean_inc_ref(v_time_1890_);
lean_dec(v___x_1889_);
v___x_1891_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1890_);
lean_dec_ref(v_time_1890_);
return v___x_1891_;
}
case 29:
{
uint8_t v_presentation_1892_; 
lean_inc_ref(v_timezone_1768_);
lean_dec_ref(v_date_1755_);
v_presentation_1892_ = lean_ctor_get_uint8(v_modifier_1753_, 0);
if (v_presentation_1892_ == 0)
{
lean_object* v___x_1893_; 
lean_dec_ref(v_timezone_1768_);
v___x_1893_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
return v___x_1893_;
}
else
{
lean_object* v_offset_1894_; lean_object* v_name_1895_; lean_object* v___x_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; 
v_offset_1894_ = lean_ctor_get(v_timezone_1768_, 0);
lean_inc(v_offset_1894_);
v_name_1895_ = lean_ctor_get(v_timezone_1768_, 1);
lean_inc_ref(v_name_1895_);
lean_dec_ref(v_timezone_1768_);
v___x_1910_ = lean_string_utf8_byte_size(v_name_1895_);
v___x_1911_ = lean_unsigned_to_nat(1u);
v___x_1912_ = lean_nat_dec_le(v___x_1911_, v___x_1910_);
if (v___x_1912_ == 0)
{
goto v___jp_1903_;
}
else
{
lean_object* v___x_1913_; lean_object* v___x_1914_; uint8_t v___x_1915_; 
v___x_1913_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_1914_ = lean_unsigned_to_nat(0u);
v___x_1915_ = lean_string_memcmp(v_name_1895_, v___x_1913_, v___x_1914_, v___x_1914_, v___x_1911_);
if (v___x_1915_ == 0)
{
goto v___jp_1903_;
}
else
{
lean_dec_ref(v_name_1895_);
goto v___jp_1896_;
}
}
v___jp_1896_:
{
uint8_t v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; uint8_t v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1897_ = 1;
v___x_1898_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1899_ = 0;
v___x_1900_ = 1;
v___x_1901_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1894_, v___x_1899_, v___x_1900_, v___x_1897_, v___x_1897_);
v___x_1902_ = lean_string_append(v___x_1898_, v___x_1901_);
lean_dec_ref(v___x_1901_);
return v___x_1902_;
}
v___jp_1903_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; uint8_t v___x_1906_; 
v___x_1904_ = lean_string_utf8_byte_size(v_name_1895_);
v___x_1905_ = lean_unsigned_to_nat(1u);
v___x_1906_ = lean_nat_dec_le(v___x_1905_, v___x_1904_);
if (v___x_1906_ == 0)
{
lean_dec(v_offset_1894_);
return v_name_1895_;
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; 
v___x_1907_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1908_ = lean_unsigned_to_nat(0u);
v___x_1909_ = lean_string_memcmp(v_name_1895_, v___x_1907_, v___x_1908_, v___x_1908_, v___x_1905_);
if (v___x_1909_ == 0)
{
lean_dec(v_offset_1894_);
return v_name_1895_;
}
else
{
lean_dec_ref(v_name_1895_);
goto v___jp_1896_;
}
}
}
}
}
case 30:
{
uint8_t v_presentation_1916_; 
lean_inc_ref(v_timezone_1768_);
lean_dec_ref(v_date_1755_);
v_presentation_1916_ = lean_ctor_get_uint8(v_modifier_1753_, 0);
if (v_presentation_1916_ == 0)
{
lean_object* v_offset_1917_; lean_object* v_abbreviation_1918_; lean_object* v___x_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; 
v_offset_1917_ = lean_ctor_get(v_timezone_1768_, 0);
lean_inc(v_offset_1917_);
v_abbreviation_1918_ = lean_ctor_get(v_timezone_1768_, 2);
lean_inc_ref(v_abbreviation_1918_);
lean_dec_ref(v_timezone_1768_);
v___x_1933_ = lean_string_utf8_byte_size(v_abbreviation_1918_);
v___x_1934_ = lean_unsigned_to_nat(1u);
v___x_1935_ = lean_nat_dec_le(v___x_1934_, v___x_1933_);
if (v___x_1935_ == 0)
{
goto v___jp_1926_;
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; 
v___x_1936_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_1937_ = lean_unsigned_to_nat(0u);
v___x_1938_ = lean_string_memcmp(v_abbreviation_1918_, v___x_1936_, v___x_1937_, v___x_1937_, v___x_1934_);
if (v___x_1938_ == 0)
{
goto v___jp_1926_;
}
else
{
lean_dec_ref(v_abbreviation_1918_);
goto v___jp_1919_;
}
}
v___jp_1919_:
{
uint8_t v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; uint8_t v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1920_ = 1;
v___x_1921_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1922_ = 0;
v___x_1923_ = 1;
v___x_1924_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1917_, v___x_1922_, v___x_1923_, v___x_1920_, v___x_1920_);
v___x_1925_ = lean_string_append(v___x_1921_, v___x_1924_);
lean_dec_ref(v___x_1924_);
return v___x_1925_;
}
v___jp_1926_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1927_ = lean_string_utf8_byte_size(v_abbreviation_1918_);
v___x_1928_ = lean_unsigned_to_nat(1u);
v___x_1929_ = lean_nat_dec_le(v___x_1928_, v___x_1927_);
if (v___x_1929_ == 0)
{
lean_dec(v_offset_1917_);
return v_abbreviation_1918_;
}
else
{
lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v___x_1930_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1931_ = lean_unsigned_to_nat(0u);
v___x_1932_ = lean_string_memcmp(v_abbreviation_1918_, v___x_1930_, v___x_1931_, v___x_1931_, v___x_1928_);
if (v___x_1932_ == 0)
{
lean_dec(v_offset_1917_);
return v_abbreviation_1918_;
}
else
{
lean_dec_ref(v_abbreviation_1918_);
goto v___jp_1919_;
}
}
}
}
else
{
lean_object* v_offset_1939_; lean_object* v_name_1940_; lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v_offset_1939_ = lean_ctor_get(v_timezone_1768_, 0);
lean_inc(v_offset_1939_);
v_name_1940_ = lean_ctor_get(v_timezone_1768_, 1);
lean_inc_ref(v_name_1940_);
lean_dec_ref(v_timezone_1768_);
v___x_1955_ = lean_string_utf8_byte_size(v_name_1940_);
v___x_1956_ = lean_unsigned_to_nat(1u);
v___x_1957_ = lean_nat_dec_le(v___x_1956_, v___x_1955_);
if (v___x_1957_ == 0)
{
goto v___jp_1948_;
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1958_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_1959_ = lean_unsigned_to_nat(0u);
v___x_1960_ = lean_string_memcmp(v_name_1940_, v___x_1958_, v___x_1959_, v___x_1959_, v___x_1956_);
if (v___x_1960_ == 0)
{
goto v___jp_1948_;
}
else
{
lean_dec_ref(v_name_1940_);
goto v___jp_1941_;
}
}
v___jp_1941_:
{
uint8_t v___x_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; uint8_t v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1942_ = 1;
v___x_1943_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1944_ = 0;
v___x_1945_ = 1;
v___x_1946_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1939_, v___x_1944_, v___x_1945_, v___x_1942_, v___x_1942_);
v___x_1947_ = lean_string_append(v___x_1943_, v___x_1946_);
lean_dec_ref(v___x_1946_);
return v___x_1947_;
}
v___jp_1948_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1949_ = lean_string_utf8_byte_size(v_name_1940_);
v___x_1950_ = lean_unsigned_to_nat(1u);
v___x_1951_ = lean_nat_dec_le(v___x_1950_, v___x_1949_);
if (v___x_1951_ == 0)
{
lean_dec(v_offset_1939_);
return v_name_1940_;
}
else
{
lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
v___x_1952_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1953_ = lean_unsigned_to_nat(0u);
v___x_1954_ = lean_string_memcmp(v_name_1940_, v___x_1952_, v___x_1953_, v___x_1953_, v___x_1950_);
if (v___x_1954_ == 0)
{
lean_dec(v_offset_1939_);
return v_name_1940_;
}
else
{
lean_dec_ref(v_name_1940_);
goto v___jp_1941_;
}
}
}
}
}
case 31:
{
uint8_t v_presentation_1961_; 
lean_inc_ref(v_timezone_1768_);
lean_dec_ref(v_date_1755_);
v_presentation_1961_ = lean_ctor_get_uint8(v_modifier_1753_, 0);
if (v_presentation_1961_ == 0)
{
lean_object* v_offset_1962_; lean_object* v_abbreviation_1963_; lean_object* v___x_1978_; lean_object* v___x_1979_; uint8_t v___x_1980_; 
v_offset_1962_ = lean_ctor_get(v_timezone_1768_, 0);
lean_inc(v_offset_1962_);
v_abbreviation_1963_ = lean_ctor_get(v_timezone_1768_, 2);
lean_inc_ref(v_abbreviation_1963_);
lean_dec_ref(v_timezone_1768_);
v___x_1978_ = lean_string_utf8_byte_size(v_abbreviation_1963_);
v___x_1979_ = lean_unsigned_to_nat(1u);
v___x_1980_ = lean_nat_dec_le(v___x_1979_, v___x_1978_);
if (v___x_1980_ == 0)
{
goto v___jp_1971_;
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1981_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_1982_ = lean_unsigned_to_nat(0u);
v___x_1983_ = lean_string_memcmp(v_abbreviation_1963_, v___x_1981_, v___x_1982_, v___x_1982_, v___x_1979_);
if (v___x_1983_ == 0)
{
goto v___jp_1971_;
}
else
{
lean_dec_ref(v_abbreviation_1963_);
goto v___jp_1964_;
}
}
v___jp_1964_:
{
uint8_t v___x_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; uint8_t v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1965_ = 1;
v___x_1966_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1967_ = 0;
v___x_1968_ = 1;
v___x_1969_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1962_, v___x_1967_, v___x_1968_, v___x_1965_, v___x_1965_);
v___x_1970_ = lean_string_append(v___x_1966_, v___x_1969_);
lean_dec_ref(v___x_1969_);
return v___x_1970_;
}
v___jp_1971_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1972_ = lean_string_utf8_byte_size(v_abbreviation_1963_);
v___x_1973_ = lean_unsigned_to_nat(1u);
v___x_1974_ = lean_nat_dec_le(v___x_1973_, v___x_1972_);
if (v___x_1974_ == 0)
{
lean_dec(v_offset_1962_);
return v_abbreviation_1963_;
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1975_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1976_ = lean_unsigned_to_nat(0u);
v___x_1977_ = lean_string_memcmp(v_abbreviation_1963_, v___x_1975_, v___x_1976_, v___x_1976_, v___x_1973_);
if (v___x_1977_ == 0)
{
lean_dec(v_offset_1962_);
return v_abbreviation_1963_;
}
else
{
lean_dec_ref(v_abbreviation_1963_);
goto v___jp_1964_;
}
}
}
}
else
{
lean_object* v_offset_1984_; lean_object* v_name_1985_; lean_object* v___x_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; 
v_offset_1984_ = lean_ctor_get(v_timezone_1768_, 0);
lean_inc(v_offset_1984_);
v_name_1985_ = lean_ctor_get(v_timezone_1768_, 1);
lean_inc_ref(v_name_1985_);
lean_dec_ref(v_timezone_1768_);
v___x_2000_ = lean_string_utf8_byte_size(v_name_1985_);
v___x_2001_ = lean_unsigned_to_nat(1u);
v___x_2002_ = lean_nat_dec_le(v___x_2001_, v___x_2000_);
if (v___x_2002_ == 0)
{
goto v___jp_1993_;
}
else
{
lean_object* v___x_2003_; lean_object* v___x_2004_; uint8_t v___x_2005_; 
v___x_2003_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2004_ = lean_unsigned_to_nat(0u);
v___x_2005_ = lean_string_memcmp(v_name_1985_, v___x_2003_, v___x_2004_, v___x_2004_, v___x_2001_);
if (v___x_2005_ == 0)
{
goto v___jp_1993_;
}
else
{
lean_dec_ref(v_name_1985_);
goto v___jp_1986_;
}
}
v___jp_1986_:
{
uint8_t v___x_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; uint8_t v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1987_ = 1;
v___x_1988_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1989_ = 0;
v___x_1990_ = 1;
v___x_1991_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1984_, v___x_1989_, v___x_1990_, v___x_1987_, v___x_1987_);
v___x_1992_ = lean_string_append(v___x_1988_, v___x_1991_);
lean_dec_ref(v___x_1991_);
return v___x_1992_;
}
v___jp_1993_:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1994_ = lean_string_utf8_byte_size(v_name_1985_);
v___x_1995_ = lean_unsigned_to_nat(1u);
v___x_1996_ = lean_nat_dec_le(v___x_1995_, v___x_1994_);
if (v___x_1996_ == 0)
{
lean_dec(v_offset_1984_);
return v_name_1985_;
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1997_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1998_ = lean_unsigned_to_nat(0u);
v___x_1999_ = lean_string_memcmp(v_name_1985_, v___x_1997_, v___x_1998_, v___x_1998_, v___x_1995_);
if (v___x_1999_ == 0)
{
lean_dec(v_offset_1984_);
return v_name_1985_;
}
else
{
lean_dec_ref(v_name_1985_);
goto v___jp_1986_;
}
}
}
}
}
default: 
{
lean_object* v_offset_2006_; 
lean_inc_ref(v_timezone_1768_);
lean_dec_ref(v_date_1755_);
v_offset_2006_ = lean_ctor_get(v_timezone_1768_, 0);
lean_inc(v_offset_2006_);
lean_dec_ref(v_timezone_1768_);
return v_offset_2006_;
}
}
v___jp_1756_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v_month_1757_);
lean_ctor_set(v___x_1761_, 1, v_day_1758_);
v___x_1762_ = l_Std_Time_ValidDate_dayOfYear(v___y_1760_, v___x_1761_);
lean_dec_ref_known(v___x_1761_, 2);
v___x_1763_ = lean_box(v___y_1759_);
v___x_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
lean_ctor_set(v___x_1764_, 1, v___x_1762_);
return v___x_1764_;
}
v___jp_1769_:
{
lean_object* v___x_1771_; lean_object* v_date_1772_; lean_object* v_year_1773_; lean_object* v_month_1774_; lean_object* v_day_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1771_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_date_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc_ref(v_date_1772_);
lean_dec(v___x_1771_);
v_year_1773_ = lean_ctor_get(v_date_1772_, 0);
lean_inc(v_year_1773_);
v_month_1774_ = lean_ctor_get(v_date_1772_, 1);
lean_inc(v_month_1774_);
v_day_1775_ = lean_ctor_get(v_date_1772_, 2);
lean_inc(v_day_1775_);
lean_dec_ref(v_date_1772_);
v___x_1776_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_1777_ = lean_int_mod(v_year_1773_, v___x_1776_);
v___x_1778_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1779_ = lean_int_dec_eq(v___x_1777_, v___x_1778_);
lean_dec(v___x_1777_);
if (v___x_1779_ == 0)
{
lean_dec(v_year_1773_);
v_month_1757_ = v_month_1774_;
v_day_1758_ = v_day_1775_;
v___y_1759_ = v___y_1770_;
v___y_1760_ = v___x_1779_;
goto v___jp_1756_;
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; 
v___x_1780_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1781_ = lean_int_mod(v_year_1773_, v___x_1780_);
v___x_1782_ = lean_int_dec_eq(v___x_1781_, v___x_1778_);
lean_dec(v___x_1781_);
if (v___x_1782_ == 0)
{
lean_dec(v_year_1773_);
v_month_1757_ = v_month_1774_;
v_day_1758_ = v_day_1775_;
v___y_1759_ = v___y_1770_;
v___y_1760_ = v___x_1779_;
goto v___jp_1756_;
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1783_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_1784_ = lean_int_mod(v_year_1773_, v___x_1783_);
lean_dec(v_year_1773_);
v___x_1785_ = lean_int_dec_eq(v___x_1784_, v___x_1778_);
lean_dec(v___x_1784_);
v_month_1757_ = v_month_1774_;
v_day_1758_ = v_day_1775_;
v___y_1759_ = v___y_1770_;
v___y_1760_ = v___x_1785_;
goto v___jp_1756_;
}
}
}
v___jp_1786_:
{
lean_object* v___x_1787_; lean_object* v_date_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; 
v___x_1787_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_date_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc_ref(v_date_1788_);
lean_dec(v___x_1787_);
v___x_1789_ = l_Std_Time_PlainDate_weekday(v_date_1788_);
v___x_1790_ = lean_box(v___x_1789_);
return v___x_1790_;
}
v___jp_1791_:
{
lean_object* v___x_1792_; lean_object* v_date_1793_; lean_object* v___x_1794_; 
v___x_1792_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_date_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc_ref(v_date_1793_);
lean_dec(v___x_1792_);
v___x_1794_ = l_Std_Time_PlainDate_quarter(v_date_1793_);
lean_dec_ref(v_date_1793_);
return v___x_1794_;
}
v___jp_1795_:
{
lean_object* v___x_1796_; lean_object* v_date_1797_; lean_object* v_month_1798_; 
v___x_1796_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_date_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc_ref(v_date_1797_);
lean_dec(v___x_1796_);
v_month_1798_ = lean_ctor_get(v_date_1797_, 1);
lean_inc(v_month_1798_);
lean_dec_ref(v_date_1797_);
return v_month_1798_;
}
v___jp_1799_:
{
lean_object* v___x_1800_; lean_object* v_date_1801_; lean_object* v_year_1802_; 
v___x_1800_ = lean_thunk_get_own(v_date_1767_);
lean_dec_ref(v_date_1767_);
v_date_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc_ref(v_date_1801_);
lean_dec(v___x_1800_);
v_year_1802_ = lean_ctor_get(v_date_1801_, 0);
lean_inc(v_year_1802_);
lean_dec_ref(v_date_1801_);
return v_year_1802_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___boxed(lean_object* v_modifier_2007_, lean_object* v_dateformat_2008_, lean_object* v_date_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(v_modifier_2007_, v_dateformat_2008_, v_date_2009_);
lean_dec_ref(v_dateformat_2008_);
lean_dec_ref(v_modifier_2007_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___lam__0(lean_object* v___x_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2011_);
v___x_2014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___y_2012_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___lam__0(lean_object* v___x_2015_, lean_object* v_b_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_fst_2018_; lean_object* v_snd_2019_; lean_object* v___x_2020_; 
v_fst_2018_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_fst_2018_);
v_snd_2019_ = lean_ctor_get(v___x_2015_, 1);
lean_inc(v_snd_2019_);
lean_dec_ref(v___x_2015_);
lean_inc_ref(v___y_2017_);
v___x_2020_ = lean_apply_1(v_b_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_dec(v_snd_2019_);
lean_dec(v_fst_2018_);
lean_dec_ref(v___y_2017_);
return v___x_2020_;
}
else
{
lean_object* v_pos_2021_; lean_object* v_snd_2022_; lean_object* v_snd_2023_; uint8_t v_decide_2024_; 
v_pos_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_pos_2021_);
v_snd_2022_ = lean_ctor_get(v___y_2017_, 1);
lean_inc(v_snd_2022_);
lean_dec_ref(v___y_2017_);
v_snd_2023_ = lean_ctor_get(v_pos_2021_, 1);
v_decide_2024_ = lean_nat_dec_eq(v_snd_2022_, v_snd_2023_);
lean_dec(v_snd_2022_);
if (v_decide_2024_ == 0)
{
lean_dec(v_pos_2021_);
lean_dec(v_snd_2019_);
lean_dec(v_fst_2018_);
return v___x_2020_;
}
else
{
lean_object* v___x_2025_; 
lean_dec_ref_known(v___x_2020_, 2);
v___x_2025_ = l_Std_Internal_Parsec_String_pstring(v_fst_2018_, v_pos_2021_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_pos_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
v_pos_2026_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2033_ == 0)
{
lean_object* v_unused_2034_; 
v_unused_2034_ = lean_ctor_get(v___x_2025_, 1);
lean_dec(v_unused_2034_);
v___x_2028_ = v___x_2025_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_pos_2026_);
lean_dec(v___x_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 1, v_snd_2019_);
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_pos_2026_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_snd_2019_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
else
{
lean_object* v_pos_2035_; lean_object* v_err_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_dec(v_snd_2019_);
v_pos_2035_ = lean_ctor_get(v___x_2025_, 0);
v_err_2036_ = lean_ctor_get(v___x_2025_, 1);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2025_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_err_2036_);
lean_inc(v_pos_2035_);
lean_dec(v___x_2025_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_pos_2035_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_err_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(lean_object* v_as_2044_, size_t v_i_2045_, size_t v_stop_2046_, lean_object* v_b_2047_, lean_object* v___y_2048_){
_start:
{
uint8_t v___x_2049_; 
v___x_2049_ = lean_usize_dec_eq(v_i_2045_, v_stop_2046_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; lean_object* v___f_2051_; size_t v___x_2052_; size_t v___x_2053_; 
v___x_2050_ = lean_array_uget_borrowed(v_as_2044_, v_i_2045_);
lean_inc(v___x_2050_);
v___f_2051_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2051_, 0, v___x_2050_);
lean_closure_set(v___f_2051_, 1, v_b_2047_);
v___x_2052_ = ((size_t)1ULL);
v___x_2053_ = lean_usize_add(v_i_2045_, v___x_2052_);
v_i_2045_ = v___x_2053_;
v_b_2047_ = v___f_2051_;
goto _start;
}
else
{
lean_object* v___x_2055_; 
v___x_2055_ = lean_apply_1(v_b_2047_, v___y_2048_);
return v___x_2055_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___boxed(lean_object* v_as_2056_, lean_object* v_i_2057_, lean_object* v_stop_2058_, lean_object* v_b_2059_, lean_object* v___y_2060_){
_start:
{
size_t v_i_boxed_2061_; size_t v_stop_boxed_2062_; lean_object* v_res_2063_; 
v_i_boxed_2061_ = lean_unbox_usize(v_i_2057_);
lean_dec(v_i_2057_);
v_stop_boxed_2062_ = lean_unbox_usize(v_stop_2058_);
lean_dec(v_stop_2058_);
v_res_2063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_as_2056_, v_i_boxed_2061_, v_stop_boxed_2062_, v_b_2059_, v___y_2060_);
lean_dec_ref(v_as_2056_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(lean_object* v_pairs_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v___x_2071_ = lean_unsigned_to_nat(0u);
v___x_2072_ = lean_array_get_size(v_pairs_2069_);
v___x_2073_ = lean_nat_dec_lt(v___x_2071_, v___x_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__1));
v___x_2075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2075_, 0, v_a_2070_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
return v___x_2075_;
}
else
{
lean_object* v___f_2076_; size_t v___x_2077_; size_t v___x_2078_; lean_object* v___x_2079_; 
v___f_2076_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__2));
v___x_2077_ = ((size_t)0ULL);
v___x_2078_ = lean_usize_of_nat(v___x_2072_);
v___x_2079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_pairs_2069_, v___x_2077_, v___x_2078_, v___f_2076_, v_a_2070_);
return v___x_2079_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___boxed(lean_object* v_pairs_2080_, lean_object* v_a_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2080_, v_a_2081_);
lean_dec_ref(v_pairs_2080_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols(lean_object* v_00_u03b1_2083_, lean_object* v_pairs_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2084_, v_a_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___boxed(lean_object* v_00_u03b1_2087_, lean_object* v_pairs_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols(v_00_u03b1_2087_, v_pairs_2088_, v_a_2089_);
lean_dec_ref(v_pairs_2088_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0(lean_object* v_00_u03b1_2091_, lean_object* v_as_2092_, size_t v_i_2093_, size_t v_stop_2094_, lean_object* v_b_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2097_; 
v___x_2097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_as_2092_, v_i_2093_, v_stop_2094_, v_b_2095_, v___y_2096_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___boxed(lean_object* v_00_u03b1_2098_, lean_object* v_as_2099_, lean_object* v_i_2100_, lean_object* v_stop_2101_, lean_object* v_b_2102_, lean_object* v___y_2103_){
_start:
{
size_t v_i_boxed_2104_; size_t v_stop_boxed_2105_; lean_object* v_res_2106_; 
v_i_boxed_2104_ = lean_unbox_usize(v_i_2100_);
lean_dec(v_i_2100_);
v_stop_boxed_2105_ = lean_unbox_usize(v_stop_2101_);
lean_dec(v_stop_2101_);
v_res_2106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0(v_00_u03b1_2098_, v_as_2099_, v_i_boxed_2104_, v_stop_boxed_2105_, v_b_2102_, v___y_2103_);
lean_dec_ref(v_as_2099_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(size_t v_sz_2107_, size_t v_i_2108_, lean_object* v_bs_2109_){
_start:
{
uint8_t v___x_2110_; 
v___x_2110_ = lean_usize_dec_lt(v_i_2108_, v_sz_2107_);
if (v___x_2110_ == 0)
{
return v_bs_2109_;
}
else
{
lean_object* v_v_2111_; lean_object* v___x_2112_; lean_object* v_bs_x27_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; size_t v___x_2119_; size_t v___x_2120_; lean_object* v___x_2121_; 
v_v_2111_ = lean_array_uget(v_bs_2109_, v_i_2108_);
v___x_2112_ = lean_unsigned_to_nat(0u);
v_bs_x27_2113_ = lean_array_uset(v_bs_2109_, v_i_2108_, v___x_2112_);
v___x_2114_ = lean_usize_to_nat(v_i_2108_);
v___x_2115_ = lean_nat_to_int(v___x_2114_);
v___x_2116_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2117_ = lean_int_add(v___x_2115_, v___x_2116_);
lean_dec(v___x_2115_);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v_v_2111_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = ((size_t)1ULL);
v___x_2120_ = lean_usize_add(v_i_2108_, v___x_2119_);
v___x_2121_ = lean_array_uset(v_bs_x27_2113_, v_i_2108_, v___x_2118_);
v_i_2108_ = v___x_2120_;
v_bs_2109_ = v___x_2121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg___boxed(lean_object* v_sz_2123_, lean_object* v_i_2124_, lean_object* v_bs_2125_){
_start:
{
size_t v_sz_boxed_2126_; size_t v_i_boxed_2127_; lean_object* v_res_2128_; 
v_sz_boxed_2126_ = lean_unbox_usize(v_sz_2123_);
lean_dec(v_sz_2123_);
v_i_boxed_2127_ = lean_unbox_usize(v_i_2124_);
lean_dec(v_i_2124_);
v_res_2128_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_boxed_2126_, v_i_boxed_2127_, v_bs_2125_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(lean_object* v_as_2129_, size_t v_sz_2130_, size_t v_i_2131_, lean_object* v_bs_2132_){
_start:
{
uint8_t v___x_2133_; 
v___x_2133_ = lean_usize_dec_lt(v_i_2131_, v_sz_2130_);
if (v___x_2133_ == 0)
{
return v_bs_2132_;
}
else
{
lean_object* v_v_2134_; lean_object* v___x_2135_; lean_object* v_bs_x27_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; size_t v___x_2142_; size_t v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v_v_2134_ = lean_array_uget(v_bs_2132_, v_i_2131_);
v___x_2135_ = lean_unsigned_to_nat(0u);
v_bs_x27_2136_ = lean_array_uset(v_bs_2132_, v_i_2131_, v___x_2135_);
v___x_2137_ = lean_usize_to_nat(v_i_2131_);
v___x_2138_ = lean_nat_to_int(v___x_2137_);
v___x_2139_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2140_ = lean_int_add(v___x_2138_, v___x_2139_);
lean_dec(v___x_2138_);
v___x_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2141_, 0, v_v_2134_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = ((size_t)1ULL);
v___x_2143_ = lean_usize_add(v_i_2131_, v___x_2142_);
v___x_2144_ = lean_array_uset(v_bs_x27_2136_, v_i_2131_, v___x_2141_);
v___x_2145_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_2130_, v___x_2143_, v___x_2144_);
return v___x_2145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0___boxed(lean_object* v_as_2146_, lean_object* v_sz_2147_, lean_object* v_i_2148_, lean_object* v_bs_2149_){
_start:
{
size_t v_sz_boxed_2150_; size_t v_i_boxed_2151_; lean_object* v_res_2152_; 
v_sz_boxed_2150_ = lean_unbox_usize(v_sz_2147_);
lean_dec(v_sz_2147_);
v_i_boxed_2151_ = lean_unbox_usize(v_i_2148_);
lean_dec(v_i_2148_);
v_res_2152_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_as_2146_, v_sz_boxed_2150_, v_i_boxed_2151_, v_bs_2149_);
lean_dec_ref(v_as_2146_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(lean_object* v_arr_2153_){
_start:
{
size_t v_sz_2154_; size_t v___x_2155_; lean_object* v___x_2156_; 
v_sz_2154_ = lean_array_size(v_arr_2153_);
v___x_2155_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2153_);
v___x_2156_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_arr_2153_, v_sz_2154_, v___x_2155_, v_arr_2153_);
lean_dec_ref(v_arr_2153_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0(lean_object* v_as_2157_, size_t v_sz_2158_, size_t v_i_2159_, lean_object* v_bs_2160_){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_2158_, v_i_2159_, v_bs_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___boxed(lean_object* v_as_2162_, lean_object* v_sz_2163_, lean_object* v_i_2164_, lean_object* v_bs_2165_){
_start:
{
size_t v_sz_boxed_2166_; size_t v_i_boxed_2167_; lean_object* v_res_2168_; 
v_sz_boxed_2166_ = lean_unbox_usize(v_sz_2163_);
lean_dec(v_sz_2163_);
v_i_boxed_2167_ = lean_unbox_usize(v_i_2164_);
lean_dec(v_i_2164_);
v_res_2168_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0(v_as_2162_, v_sz_boxed_2166_, v_i_boxed_2167_, v_bs_2165_);
lean_dec_ref(v_as_2162_);
return v_res_2168_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(lean_object* v_x_2169_){
_start:
{
lean_object* v___x_2170_; uint8_t v___x_2171_; 
v___x_2170_ = lean_unsigned_to_nat(0u);
v___x_2171_ = lean_nat_dec_eq(v_x_2169_, v___x_2170_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2172_ = lean_unsigned_to_nat(1u);
v___x_2173_ = lean_nat_dec_eq(v_x_2169_, v___x_2172_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2174_ = lean_unsigned_to_nat(2u);
v___x_2175_ = lean_nat_dec_eq(v_x_2169_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2176_ = lean_unsigned_to_nat(3u);
v___x_2177_ = lean_nat_dec_eq(v_x_2169_, v___x_2176_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; uint8_t v___x_2179_; 
v___x_2178_ = lean_unsigned_to_nat(4u);
v___x_2179_ = lean_nat_dec_eq(v_x_2169_, v___x_2178_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; uint8_t v___x_2181_; 
v___x_2180_ = lean_unsigned_to_nat(5u);
v___x_2181_ = lean_nat_dec_eq(v_x_2169_, v___x_2180_);
if (v___x_2181_ == 0)
{
uint8_t v___x_2182_; 
v___x_2182_ = 5;
return v___x_2182_;
}
else
{
uint8_t v___x_2183_; 
v___x_2183_ = 4;
return v___x_2183_;
}
}
else
{
uint8_t v___x_2184_; 
v___x_2184_ = 3;
return v___x_2184_;
}
}
else
{
uint8_t v___x_2185_; 
v___x_2185_ = 2;
return v___x_2185_;
}
}
else
{
uint8_t v___x_2186_; 
v___x_2186_ = 1;
return v___x_2186_;
}
}
else
{
uint8_t v___x_2187_; 
v___x_2187_ = 0;
return v___x_2187_;
}
}
else
{
uint8_t v___x_2188_; 
v___x_2188_ = 6;
return v___x_2188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex___boxed(lean_object* v_x_2189_){
_start:
{
uint8_t v_res_2190_; lean_object* v_r_2191_; 
v_res_2190_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(v_x_2189_);
lean_dec(v_x_2189_);
v_r_2191_ = lean_box(v_res_2190_);
return v_r_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(size_t v_sz_2192_, size_t v_i_2193_, lean_object* v_bs_2194_){
_start:
{
uint8_t v___x_2195_; 
v___x_2195_ = lean_usize_dec_lt(v_i_2193_, v_sz_2192_);
if (v___x_2195_ == 0)
{
return v_bs_2194_;
}
else
{
lean_object* v_v_2196_; lean_object* v___x_2197_; lean_object* v_bs_x27_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; uint8_t v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; size_t v___x_2206_; size_t v___x_2207_; lean_object* v___x_2208_; 
v_v_2196_ = lean_array_uget(v_bs_2194_, v_i_2193_);
v___x_2197_ = lean_unsigned_to_nat(0u);
v_bs_x27_2198_ = lean_array_uset(v_bs_2194_, v_i_2193_, v___x_2197_);
v___x_2199_ = lean_usize_to_nat(v_i_2193_);
v___x_2200_ = lean_nat_to_int(v___x_2199_);
v___x_2201_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2202_ = lean_int_add(v___x_2200_, v___x_2201_);
lean_dec(v___x_2200_);
v___x_2203_ = l_Std_Time_Weekday_ofOrdinal(v___x_2202_);
lean_dec(v___x_2202_);
v___x_2204_ = lean_box(v___x_2203_);
v___x_2205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2205_, 0, v_v_2196_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = ((size_t)1ULL);
v___x_2207_ = lean_usize_add(v_i_2193_, v___x_2206_);
v___x_2208_ = lean_array_uset(v_bs_x27_2198_, v_i_2193_, v___x_2205_);
v_i_2193_ = v___x_2207_;
v_bs_2194_ = v___x_2208_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg___boxed(lean_object* v_sz_2210_, lean_object* v_i_2211_, lean_object* v_bs_2212_){
_start:
{
size_t v_sz_boxed_2213_; size_t v_i_boxed_2214_; lean_object* v_res_2215_; 
v_sz_boxed_2213_ = lean_unbox_usize(v_sz_2210_);
lean_dec(v_sz_2210_);
v_i_boxed_2214_ = lean_unbox_usize(v_i_2211_);
lean_dec(v_i_2211_);
v_res_2215_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_boxed_2213_, v_i_boxed_2214_, v_bs_2212_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(lean_object* v_as_2216_, size_t v_sz_2217_, size_t v_i_2218_, lean_object* v_bs_2219_){
_start:
{
uint8_t v___x_2220_; 
v___x_2220_ = lean_usize_dec_lt(v_i_2218_, v_sz_2217_);
if (v___x_2220_ == 0)
{
return v_bs_2219_;
}
else
{
lean_object* v_v_2221_; lean_object* v___x_2222_; lean_object* v_bs_x27_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; size_t v___x_2231_; size_t v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v_v_2221_ = lean_array_uget(v_bs_2219_, v_i_2218_);
v___x_2222_ = lean_unsigned_to_nat(0u);
v_bs_x27_2223_ = lean_array_uset(v_bs_2219_, v_i_2218_, v___x_2222_);
v___x_2224_ = lean_usize_to_nat(v_i_2218_);
v___x_2225_ = lean_nat_to_int(v___x_2224_);
v___x_2226_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2227_ = lean_int_add(v___x_2225_, v___x_2226_);
lean_dec(v___x_2225_);
v___x_2228_ = l_Std_Time_Weekday_ofOrdinal(v___x_2227_);
lean_dec(v___x_2227_);
v___x_2229_ = lean_box(v___x_2228_);
v___x_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2230_, 0, v_v_2221_);
lean_ctor_set(v___x_2230_, 1, v___x_2229_);
v___x_2231_ = ((size_t)1ULL);
v___x_2232_ = lean_usize_add(v_i_2218_, v___x_2231_);
v___x_2233_ = lean_array_uset(v_bs_x27_2223_, v_i_2218_, v___x_2230_);
v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_2217_, v___x_2232_, v___x_2233_);
return v___x_2234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0___boxed(lean_object* v_as_2235_, lean_object* v_sz_2236_, lean_object* v_i_2237_, lean_object* v_bs_2238_){
_start:
{
size_t v_sz_boxed_2239_; size_t v_i_boxed_2240_; lean_object* v_res_2241_; 
v_sz_boxed_2239_ = lean_unbox_usize(v_sz_2236_);
lean_dec(v_sz_2236_);
v_i_boxed_2240_ = lean_unbox_usize(v_i_2237_);
lean_dec(v_i_2237_);
v_res_2241_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(v_as_2235_, v_sz_boxed_2239_, v_i_boxed_2240_, v_bs_2238_);
lean_dec_ref(v_as_2235_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(lean_object* v_arr_2242_){
_start:
{
size_t v_sz_2243_; size_t v___x_2244_; lean_object* v___x_2245_; 
v_sz_2243_ = lean_array_size(v_arr_2242_);
v___x_2244_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2242_);
v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(v_arr_2242_, v_sz_2243_, v___x_2244_, v_arr_2242_);
lean_dec_ref(v_arr_2242_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0(lean_object* v_as_2246_, size_t v_sz_2247_, size_t v_i_2248_, lean_object* v_bs_2249_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_2247_, v_i_2248_, v_bs_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___boxed(lean_object* v_as_2251_, lean_object* v_sz_2252_, lean_object* v_i_2253_, lean_object* v_bs_2254_){
_start:
{
size_t v_sz_boxed_2255_; size_t v_i_boxed_2256_; lean_object* v_res_2257_; 
v_sz_boxed_2255_ = lean_unbox_usize(v_sz_2252_);
lean_dec(v_sz_2252_);
v_i_boxed_2256_ = lean_unbox_usize(v_i_2253_);
lean_dec(v_i_2253_);
v_res_2257_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0(v_as_2251_, v_sz_boxed_2255_, v_i_boxed_2256_, v_bs_2254_);
lean_dec_ref(v_as_2251_);
return v_res_2257_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(lean_object* v_x_2258_){
_start:
{
lean_object* v___x_2259_; uint8_t v___x_2260_; 
v___x_2259_ = lean_unsigned_to_nat(0u);
v___x_2260_ = lean_nat_dec_eq(v_x_2258_, v___x_2259_);
if (v___x_2260_ == 0)
{
uint8_t v___x_2261_; 
v___x_2261_ = 1;
return v___x_2261_;
}
else
{
uint8_t v___x_2262_; 
v___x_2262_ = 0;
return v___x_2262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex___boxed(lean_object* v_x_2263_){
_start:
{
uint8_t v_res_2264_; lean_object* v_r_2265_; 
v_res_2264_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(v_x_2263_);
lean_dec(v_x_2263_);
v_r_2265_ = lean_box(v_res_2264_);
return v_r_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(size_t v_sz_2266_, size_t v_i_2267_, lean_object* v_bs_2268_){
_start:
{
uint8_t v___x_2269_; 
v___x_2269_ = lean_usize_dec_lt(v_i_2267_, v_sz_2266_);
if (v___x_2269_ == 0)
{
return v_bs_2268_;
}
else
{
lean_object* v_v_2270_; lean_object* v___x_2271_; lean_object* v_bs_x27_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; size_t v___x_2277_; size_t v___x_2278_; lean_object* v___x_2279_; 
v_v_2270_ = lean_array_uget(v_bs_2268_, v_i_2267_);
v___x_2271_ = lean_unsigned_to_nat(0u);
v_bs_x27_2272_ = lean_array_uset(v_bs_2268_, v_i_2267_, v___x_2271_);
v___x_2273_ = lean_usize_to_nat(v_i_2267_);
v___x_2274_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(v___x_2273_);
lean_dec(v___x_2273_);
v___x_2275_ = lean_box(v___x_2274_);
v___x_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2276_, 0, v_v_2270_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = ((size_t)1ULL);
v___x_2278_ = lean_usize_add(v_i_2267_, v___x_2277_);
v___x_2279_ = lean_array_uset(v_bs_x27_2272_, v_i_2267_, v___x_2276_);
v_i_2267_ = v___x_2278_;
v_bs_2268_ = v___x_2279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg___boxed(lean_object* v_sz_2281_, lean_object* v_i_2282_, lean_object* v_bs_2283_){
_start:
{
size_t v_sz_boxed_2284_; size_t v_i_boxed_2285_; lean_object* v_res_2286_; 
v_sz_boxed_2284_ = lean_unbox_usize(v_sz_2281_);
lean_dec(v_sz_2281_);
v_i_boxed_2285_ = lean_unbox_usize(v_i_2282_);
lean_dec(v_i_2282_);
v_res_2286_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_boxed_2284_, v_i_boxed_2285_, v_bs_2283_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(lean_object* v_arr_2287_){
_start:
{
size_t v_sz_2288_; size_t v___x_2289_; lean_object* v___x_2290_; 
v_sz_2288_ = lean_array_size(v_arr_2287_);
v___x_2289_ = ((size_t)0ULL);
v___x_2290_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_2288_, v___x_2289_, v_arr_2287_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0(lean_object* v_as_2291_, size_t v_sz_2292_, size_t v_i_2293_, lean_object* v_bs_2294_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_2292_, v_i_2293_, v_bs_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___boxed(lean_object* v_as_2296_, lean_object* v_sz_2297_, lean_object* v_i_2298_, lean_object* v_bs_2299_){
_start:
{
size_t v_sz_boxed_2300_; size_t v_i_boxed_2301_; lean_object* v_res_2302_; 
v_sz_boxed_2300_ = lean_unbox_usize(v_sz_2297_);
lean_dec(v_sz_2297_);
v_i_boxed_2301_ = lean_unbox_usize(v_i_2298_);
lean_dec(v_i_2298_);
v_res_2302_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0(v_as_2296_, v_sz_boxed_2300_, v_i_boxed_2301_, v_bs_2299_);
lean_dec_ref(v_as_2296_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(lean_object* v_arr_2303_){
_start:
{
size_t v_sz_2304_; size_t v___x_2305_; lean_object* v___x_2306_; 
v_sz_2304_ = lean_array_size(v_arr_2303_);
v___x_2305_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2303_);
v___x_2306_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_arr_2303_, v_sz_2304_, v___x_2305_, v_arr_2303_);
lean_dec_ref(v_arr_2303_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(lean_object* v_symbols_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v_monthLong_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v_monthLong_2309_ = lean_ctor_get(v_symbols_2307_, 0);
lean_inc_ref(v_monthLong_2309_);
lean_dec_ref(v_symbols_2307_);
v___x_2310_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthLong_2309_);
v___x_2311_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2310_, v_a_2308_);
lean_dec_ref(v___x_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseMonthShort(lean_object* v_symbols_2312_, lean_object* v_a_2313_){
_start:
{
lean_object* v_monthShort_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v_monthShort_2314_ = lean_ctor_get(v_symbols_2312_, 1);
lean_inc_ref(v_monthShort_2314_);
lean_dec_ref(v_symbols_2312_);
v___x_2315_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthShort_2314_);
v___x_2316_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2315_, v_a_2313_);
lean_dec_ref(v___x_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(lean_object* v_symbols_2317_, lean_object* v_a_2318_){
_start:
{
lean_object* v_monthNarrow_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v_monthNarrow_2319_ = lean_ctor_get(v_symbols_2317_, 2);
lean_inc_ref(v_monthNarrow_2319_);
lean_dec_ref(v_symbols_2317_);
v___x_2320_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthNarrow_2319_);
v___x_2321_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2320_, v_a_2318_);
lean_dec_ref(v___x_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(lean_object* v_symbols_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v_weekdayLong_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_weekdayLong_2324_ = lean_ctor_get(v_symbols_2322_, 3);
lean_inc_ref(v_weekdayLong_2324_);
lean_dec_ref(v_symbols_2322_);
v___x_2325_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayLong_2324_);
v___x_2326_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2325_, v_a_2323_);
lean_dec_ref(v___x_2325_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(lean_object* v_symbols_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v_weekdayShort_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v_weekdayShort_2329_ = lean_ctor_get(v_symbols_2327_, 4);
lean_inc_ref(v_weekdayShort_2329_);
lean_dec_ref(v_symbols_2327_);
v___x_2330_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayShort_2329_);
v___x_2331_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2330_, v_a_2328_);
lean_dec_ref(v___x_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(lean_object* v_symbols_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v_weekdayNarrow_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v_weekdayNarrow_2334_ = lean_ctor_get(v_symbols_2332_, 5);
lean_inc_ref(v_weekdayNarrow_2334_);
lean_dec_ref(v_symbols_2332_);
v___x_2335_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayNarrow_2334_);
v___x_2336_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2335_, v_a_2333_);
lean_dec_ref(v___x_2335_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(lean_object* v_symbols_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_weekdayTwoLetter_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v_weekdayTwoLetter_2339_ = lean_ctor_get(v_symbols_2337_, 6);
lean_inc_ref(v_weekdayTwoLetter_2339_);
lean_dec_ref(v_symbols_2337_);
v___x_2340_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayTwoLetter_2339_);
v___x_2341_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2340_, v_a_2338_);
lean_dec_ref(v___x_2340_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraShort(lean_object* v_symbols_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v_eraShort_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v_eraShort_2344_ = lean_ctor_get(v_symbols_2342_, 7);
lean_inc_ref(v_eraShort_2344_);
lean_dec_ref(v_symbols_2342_);
v___x_2345_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraShort_2344_);
v___x_2346_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2345_, v_a_2343_);
lean_dec_ref(v___x_2345_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraLong(lean_object* v_symbols_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v_eraLong_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v_eraLong_2349_ = lean_ctor_get(v_symbols_2347_, 8);
lean_inc_ref(v_eraLong_2349_);
lean_dec_ref(v_symbols_2347_);
v___x_2350_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraLong_2349_);
v___x_2351_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2350_, v_a_2348_);
lean_dec_ref(v___x_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraNarrow(lean_object* v_symbols_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v_eraNarrow_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v_eraNarrow_2354_ = lean_ctor_get(v_symbols_2352_, 9);
lean_inc_ref(v_eraNarrow_2354_);
lean_dec_ref(v_symbols_2352_);
v___x_2355_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraNarrow_2354_);
v___x_2356_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2355_, v_a_2353_);
lean_dec_ref(v___x_2355_);
return v___x_2356_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0(void){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = lean_unsigned_to_nat(3u);
v___x_2358_ = lean_nat_to_int(v___x_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber(lean_object* v_a_2359_){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__0));
lean_inc_ref(v_a_2359_);
v___x_2361_ = l_Std_Internal_Parsec_String_pstring(v___x_2360_, v_a_2359_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_pos_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2370_; 
lean_dec_ref(v_a_2359_);
v_pos_2362_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2370_ == 0)
{
lean_object* v_unused_2371_; 
v_unused_2371_ = lean_ctor_get(v___x_2361_, 1);
lean_dec(v_unused_2371_);
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2370_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_pos_2362_);
lean_dec(v___x_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2370_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; lean_object* v___x_2368_; 
v___x_2366_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 1, v___x_2366_);
v___x_2368_ = v___x_2364_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_pos_2362_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
else
{
lean_object* v_pos_2372_; lean_object* v_err_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2450_; 
v_pos_2372_ = lean_ctor_get(v___x_2361_, 0);
v_err_2373_ = lean_ctor_get(v___x_2361_, 1);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2375_ = v___x_2361_;
v_isShared_2376_ = v_isSharedCheck_2450_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_err_2373_);
lean_inc(v_pos_2372_);
lean_dec(v___x_2361_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2450_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v_snd_2377_; lean_object* v_snd_2378_; uint8_t v_decide_2379_; 
v_snd_2377_ = lean_ctor_get(v_a_2359_, 1);
lean_inc(v_snd_2377_);
lean_dec_ref(v_a_2359_);
v_snd_2378_ = lean_ctor_get(v_pos_2372_, 1);
v_decide_2379_ = lean_nat_dec_eq(v_snd_2377_, v_snd_2378_);
lean_dec(v_snd_2377_);
if (v_decide_2379_ == 0)
{
lean_object* v___x_2381_; 
if (v_isShared_2376_ == 0)
{
v___x_2381_ = v___x_2375_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_pos_2372_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v_err_2373_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
else
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
lean_inc(v_snd_2378_);
lean_del_object(v___x_2375_);
lean_dec(v_err_2373_);
v___x_2383_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__1));
v___x_2384_ = l_Std_Internal_Parsec_String_pstring(v___x_2383_, v_pos_2372_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_pos_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2393_; 
lean_dec(v_snd_2378_);
v_pos_2385_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2393_ == 0)
{
lean_object* v_unused_2394_; 
v_unused_2394_ = lean_ctor_get(v___x_2384_, 1);
lean_dec(v_unused_2394_);
v___x_2387_ = v___x_2384_;
v_isShared_2388_ = v_isSharedCheck_2393_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_pos_2385_);
lean_dec(v___x_2384_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2393_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2389_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__3, &l_Std_Time_instReprFormatPart_repr___closed__3_once, _init_l_Std_Time_instReprFormatPart_repr___closed__3);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 1, v___x_2389_);
v___x_2391_ = v___x_2387_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_pos_2385_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
else
{
lean_object* v_pos_2395_; lean_object* v_err_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2449_; 
v_pos_2395_ = lean_ctor_get(v___x_2384_, 0);
v_err_2396_ = lean_ctor_get(v___x_2384_, 1);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2398_ = v___x_2384_;
v_isShared_2399_ = v_isSharedCheck_2449_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_err_2396_);
lean_inc(v_pos_2395_);
lean_dec(v___x_2384_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2449_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v_snd_2400_; uint8_t v_decide_2401_; 
v_snd_2400_ = lean_ctor_get(v_pos_2395_, 1);
v_decide_2401_ = lean_nat_dec_eq(v_snd_2378_, v_snd_2400_);
lean_dec(v_snd_2378_);
if (v_decide_2401_ == 0)
{
lean_object* v___x_2403_; 
if (v_isShared_2399_ == 0)
{
v___x_2403_ = v___x_2398_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_pos_2395_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v_err_2396_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
else
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
lean_inc(v_snd_2400_);
lean_del_object(v___x_2398_);
lean_dec(v_err_2396_);
v___x_2405_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__2));
v___x_2406_ = l_Std_Internal_Parsec_String_pstring(v___x_2405_, v_pos_2395_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_pos_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2415_; 
lean_dec(v_snd_2400_);
v_pos_2407_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2415_ == 0)
{
lean_object* v_unused_2416_; 
v_unused_2416_ = lean_ctor_get(v___x_2406_, 1);
lean_dec(v_unused_2416_);
v___x_2409_ = v___x_2406_;
v_isShared_2410_ = v_isSharedCheck_2415_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_pos_2407_);
lean_dec(v___x_2406_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2415_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2413_; 
v___x_2411_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 1, v___x_2411_);
v___x_2413_ = v___x_2409_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_pos_2407_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v___x_2411_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
else
{
lean_object* v_pos_2417_; lean_object* v_err_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2448_; 
v_pos_2417_ = lean_ctor_get(v___x_2406_, 0);
v_err_2418_ = lean_ctor_get(v___x_2406_, 1);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2420_ = v___x_2406_;
v_isShared_2421_ = v_isSharedCheck_2448_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_err_2418_);
lean_inc(v_pos_2417_);
lean_dec(v___x_2406_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2448_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v_snd_2422_; uint8_t v_decide_2423_; 
v_snd_2422_ = lean_ctor_get(v_pos_2417_, 1);
v_decide_2423_ = lean_nat_dec_eq(v_snd_2400_, v_snd_2422_);
lean_dec(v_snd_2400_);
if (v_decide_2423_ == 0)
{
lean_object* v___x_2425_; 
if (v_isShared_2421_ == 0)
{
v___x_2425_ = v___x_2420_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_pos_2417_);
lean_ctor_set(v_reuseFailAlloc_2426_, 1, v_err_2418_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
else
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
lean_del_object(v___x_2420_);
lean_dec(v_err_2418_);
v___x_2427_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__3));
v___x_2428_ = l_Std_Internal_Parsec_String_pstring(v___x_2427_, v_pos_2417_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_pos_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2437_; 
v_pos_2429_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2437_ == 0)
{
lean_object* v_unused_2438_; 
v_unused_2438_ = lean_ctor_get(v___x_2428_, 1);
lean_dec(v_unused_2438_);
v___x_2431_ = v___x_2428_;
v_isShared_2432_ = v_isSharedCheck_2437_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_pos_2429_);
lean_dec(v___x_2428_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2437_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v___x_2435_; 
v___x_2433_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 1, v___x_2433_);
v___x_2435_ = v___x_2431_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_pos_2429_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v___x_2433_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
else
{
lean_object* v_pos_2439_; lean_object* v_err_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
v_pos_2439_ = lean_ctor_get(v___x_2428_, 0);
v_err_2440_ = lean_ctor_get(v___x_2428_, 1);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2428_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_err_2440_);
lean_inc(v_pos_2439_);
lean_dec(v___x_2428_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_pos_2439_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v_err_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(lean_object* v_symbols_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v_quarterLong_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v_quarterLong_2453_ = lean_ctor_get(v_symbols_2451_, 11);
lean_inc_ref(v_quarterLong_2453_);
lean_dec_ref(v_symbols_2451_);
v___x_2454_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterLong_2453_);
v___x_2455_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2454_, v_a_2452_);
lean_dec_ref(v___x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(lean_object* v_symbols_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v_quarterShort_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_quarterShort_2458_ = lean_ctor_get(v_symbols_2456_, 10);
lean_inc_ref(v_quarterShort_2458_);
lean_dec_ref(v_symbols_2456_);
v___x_2459_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterShort_2458_);
v___x_2460_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2459_, v_a_2457_);
lean_dec_ref(v___x_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(lean_object* v_symbols_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v_quarterNarrow_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v_quarterNarrow_2463_ = lean_ctor_get(v_symbols_2461_, 12);
lean_inc_ref(v_quarterNarrow_2463_);
lean_dec_ref(v_symbols_2461_);
v___x_2464_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterNarrow_2463_);
v___x_2465_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2464_, v_a_2462_);
lean_dec_ref(v___x_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerShort(lean_object* v_symbols_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v_amShort_2468_; lean_object* v_pmShort_2469_; lean_object* v___x_2470_; 
v_amShort_2468_ = lean_ctor_get(v_symbols_2466_, 13);
lean_inc_ref(v_amShort_2468_);
v_pmShort_2469_ = lean_ctor_get(v_symbols_2466_, 14);
lean_inc_ref(v_pmShort_2469_);
lean_dec_ref(v_symbols_2466_);
lean_inc_ref(v_a_2467_);
v___x_2470_ = l_Std_Internal_Parsec_String_pstring(v_amShort_2468_, v_a_2467_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_pos_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2480_; 
lean_dec_ref(v_pmShort_2469_);
lean_dec_ref(v_a_2467_);
v_pos_2471_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2480_ == 0)
{
lean_object* v_unused_2481_; 
v_unused_2481_ = lean_ctor_get(v___x_2470_, 1);
lean_dec(v_unused_2481_);
v___x_2473_ = v___x_2470_;
v_isShared_2474_ = v_isSharedCheck_2480_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_pos_2471_);
lean_dec(v___x_2470_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2480_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
uint8_t v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2478_; 
v___x_2475_ = 0;
v___x_2476_ = lean_box(v___x_2475_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 1, v___x_2476_);
v___x_2478_ = v___x_2473_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_pos_2471_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
else
{
lean_object* v_pos_2482_; lean_object* v_err_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2514_; 
v_pos_2482_ = lean_ctor_get(v___x_2470_, 0);
v_err_2483_ = lean_ctor_get(v___x_2470_, 1);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2485_ = v___x_2470_;
v_isShared_2486_ = v_isSharedCheck_2514_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_err_2483_);
lean_inc(v_pos_2482_);
lean_dec(v___x_2470_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2514_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v_snd_2487_; lean_object* v_snd_2488_; uint8_t v_decide_2489_; 
v_snd_2487_ = lean_ctor_get(v_a_2467_, 1);
lean_inc(v_snd_2487_);
lean_dec_ref(v_a_2467_);
v_snd_2488_ = lean_ctor_get(v_pos_2482_, 1);
v_decide_2489_ = lean_nat_dec_eq(v_snd_2487_, v_snd_2488_);
lean_dec(v_snd_2487_);
if (v_decide_2489_ == 0)
{
lean_object* v___x_2491_; 
lean_dec_ref(v_pmShort_2469_);
if (v_isShared_2486_ == 0)
{
v___x_2491_ = v___x_2485_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_pos_2482_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_err_2483_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
else
{
lean_object* v___x_2493_; 
lean_del_object(v___x_2485_);
lean_dec(v_err_2483_);
v___x_2493_ = l_Std_Internal_Parsec_String_pstring(v_pmShort_2469_, v_pos_2482_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_pos_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2503_; 
v_pos_2494_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2503_ == 0)
{
lean_object* v_unused_2504_; 
v_unused_2504_ = lean_ctor_get(v___x_2493_, 1);
lean_dec(v_unused_2504_);
v___x_2496_ = v___x_2493_;
v_isShared_2497_ = v_isSharedCheck_2503_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_pos_2494_);
lean_dec(v___x_2493_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2503_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
uint8_t v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2501_; 
v___x_2498_ = 1;
v___x_2499_ = lean_box(v___x_2498_);
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 1, v___x_2499_);
v___x_2501_ = v___x_2496_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_pos_2494_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v___x_2499_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
else
{
lean_object* v_pos_2505_; lean_object* v_err_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
v_pos_2505_ = lean_ctor_get(v___x_2493_, 0);
v_err_2506_ = lean_ctor_get(v___x_2493_, 1);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2493_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_err_2506_);
lean_inc(v_pos_2505_);
lean_dec(v___x_2493_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_pos_2505_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_err_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerLong(lean_object* v_symbols_2515_, lean_object* v_a_2516_){
_start:
{
lean_object* v_amLong_2517_; lean_object* v_pmLong_2518_; lean_object* v___x_2519_; 
v_amLong_2517_ = lean_ctor_get(v_symbols_2515_, 15);
lean_inc_ref(v_amLong_2517_);
v_pmLong_2518_ = lean_ctor_get(v_symbols_2515_, 16);
lean_inc_ref(v_pmLong_2518_);
lean_dec_ref(v_symbols_2515_);
lean_inc_ref(v_a_2516_);
v___x_2519_ = l_Std_Internal_Parsec_String_pstring(v_amLong_2517_, v_a_2516_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_pos_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2529_; 
lean_dec_ref(v_pmLong_2518_);
lean_dec_ref(v_a_2516_);
v_pos_2520_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2529_ == 0)
{
lean_object* v_unused_2530_; 
v_unused_2530_ = lean_ctor_get(v___x_2519_, 1);
lean_dec(v_unused_2530_);
v___x_2522_ = v___x_2519_;
v_isShared_2523_ = v_isSharedCheck_2529_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_pos_2520_);
lean_dec(v___x_2519_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2529_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
uint8_t v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2527_; 
v___x_2524_ = 0;
v___x_2525_ = lean_box(v___x_2524_);
if (v_isShared_2523_ == 0)
{
lean_ctor_set(v___x_2522_, 1, v___x_2525_);
v___x_2527_ = v___x_2522_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_pos_2520_);
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
lean_object* v_pos_2531_; lean_object* v_err_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2563_; 
v_pos_2531_ = lean_ctor_get(v___x_2519_, 0);
v_err_2532_ = lean_ctor_get(v___x_2519_, 1);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2534_ = v___x_2519_;
v_isShared_2535_ = v_isSharedCheck_2563_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_err_2532_);
lean_inc(v_pos_2531_);
lean_dec(v___x_2519_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2563_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v_snd_2536_; lean_object* v_snd_2537_; uint8_t v_decide_2538_; 
v_snd_2536_ = lean_ctor_get(v_a_2516_, 1);
lean_inc(v_snd_2536_);
lean_dec_ref(v_a_2516_);
v_snd_2537_ = lean_ctor_get(v_pos_2531_, 1);
v_decide_2538_ = lean_nat_dec_eq(v_snd_2536_, v_snd_2537_);
lean_dec(v_snd_2536_);
if (v_decide_2538_ == 0)
{
lean_object* v___x_2540_; 
lean_dec_ref(v_pmLong_2518_);
if (v_isShared_2535_ == 0)
{
v___x_2540_ = v___x_2534_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_pos_2531_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_err_2532_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
else
{
lean_object* v___x_2542_; 
lean_del_object(v___x_2534_);
lean_dec(v_err_2532_);
v___x_2542_ = l_Std_Internal_Parsec_String_pstring(v_pmLong_2518_, v_pos_2531_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_pos_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2552_; 
v_pos_2543_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2552_ == 0)
{
lean_object* v_unused_2553_; 
v_unused_2553_ = lean_ctor_get(v___x_2542_, 1);
lean_dec(v_unused_2553_);
v___x_2545_ = v___x_2542_;
v_isShared_2546_ = v_isSharedCheck_2552_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_pos_2543_);
lean_dec(v___x_2542_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2552_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
uint8_t v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2550_; 
v___x_2547_ = 1;
v___x_2548_ = lean_box(v___x_2547_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 1, v___x_2548_);
v___x_2550_ = v___x_2545_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_pos_2543_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v___x_2548_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
else
{
lean_object* v_pos_2554_; lean_object* v_err_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
v_pos_2554_ = lean_ctor_get(v___x_2542_, 0);
v_err_2555_ = lean_ctor_get(v___x_2542_, 1);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2542_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_err_2555_);
lean_inc(v_pos_2554_);
lean_dec(v___x_2542_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_pos_2554_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_err_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerNarrow(lean_object* v_symbols_2564_, lean_object* v_a_2565_){
_start:
{
lean_object* v_amNarrow_2566_; lean_object* v_pmNarrow_2567_; lean_object* v___x_2568_; 
v_amNarrow_2566_ = lean_ctor_get(v_symbols_2564_, 17);
lean_inc_ref(v_amNarrow_2566_);
v_pmNarrow_2567_ = lean_ctor_get(v_symbols_2564_, 18);
lean_inc_ref(v_pmNarrow_2567_);
lean_dec_ref(v_symbols_2564_);
lean_inc_ref(v_a_2565_);
v___x_2568_ = l_Std_Internal_Parsec_String_pstring(v_amNarrow_2566_, v_a_2565_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_pos_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2578_; 
lean_dec_ref(v_pmNarrow_2567_);
lean_dec_ref(v_a_2565_);
v_pos_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2578_ == 0)
{
lean_object* v_unused_2579_; 
v_unused_2579_ = lean_ctor_get(v___x_2568_, 1);
lean_dec(v_unused_2579_);
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2578_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_pos_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2578_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
uint8_t v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2576_; 
v___x_2573_ = 0;
v___x_2574_ = lean_box(v___x_2573_);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 1, v___x_2574_);
v___x_2576_ = v___x_2571_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_pos_2569_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
else
{
lean_object* v_pos_2580_; lean_object* v_err_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2612_; 
v_pos_2580_ = lean_ctor_get(v___x_2568_, 0);
v_err_2581_ = lean_ctor_get(v___x_2568_, 1);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2583_ = v___x_2568_;
v_isShared_2584_ = v_isSharedCheck_2612_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_err_2581_);
lean_inc(v_pos_2580_);
lean_dec(v___x_2568_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2612_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v_snd_2585_; lean_object* v_snd_2586_; uint8_t v_decide_2587_; 
v_snd_2585_ = lean_ctor_get(v_a_2565_, 1);
lean_inc(v_snd_2585_);
lean_dec_ref(v_a_2565_);
v_snd_2586_ = lean_ctor_get(v_pos_2580_, 1);
v_decide_2587_ = lean_nat_dec_eq(v_snd_2585_, v_snd_2586_);
lean_dec(v_snd_2585_);
if (v_decide_2587_ == 0)
{
lean_object* v___x_2589_; 
lean_dec_ref(v_pmNarrow_2567_);
if (v_isShared_2584_ == 0)
{
v___x_2589_ = v___x_2583_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_pos_2580_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_err_2581_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
else
{
lean_object* v___x_2591_; 
lean_del_object(v___x_2583_);
lean_dec(v_err_2581_);
v___x_2591_ = l_Std_Internal_Parsec_String_pstring(v_pmNarrow_2567_, v_pos_2580_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_pos_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2601_; 
v_pos_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2601_ == 0)
{
lean_object* v_unused_2602_; 
v_unused_2602_ = lean_ctor_get(v___x_2591_, 1);
lean_dec(v_unused_2602_);
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2601_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_pos_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2601_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
uint8_t v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2596_ = 1;
v___x_2597_ = lean_box(v___x_2596_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 1, v___x_2597_);
v___x_2599_ = v___x_2594_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_pos_2592_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
else
{
lean_object* v_pos_2603_; lean_object* v_err_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
v_pos_2603_ = lean_ctor_get(v___x_2591_, 0);
v_err_2604_ = lean_ctor_get(v___x_2591_, 1);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2591_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_err_2604_);
lean_inc(v_pos_2603_);
lean_dec(v___x_2591_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_pos_2603_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_err_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(lean_object* v_dp_2613_, lean_object* v_a_2614_){
_start:
{
lean_object* v_am_2615_; lean_object* v_pm_2616_; lean_object* v_noon_2617_; lean_object* v_midnight_2618_; lean_object* v___x_2619_; 
v_am_2615_ = lean_ctor_get(v_dp_2613_, 0);
lean_inc_ref(v_am_2615_);
v_pm_2616_ = lean_ctor_get(v_dp_2613_, 1);
lean_inc_ref(v_pm_2616_);
v_noon_2617_ = lean_ctor_get(v_dp_2613_, 2);
lean_inc_ref(v_noon_2617_);
v_midnight_2618_ = lean_ctor_get(v_dp_2613_, 3);
lean_inc_ref(v_midnight_2618_);
lean_dec_ref(v_dp_2613_);
lean_inc_ref(v_a_2614_);
v___x_2619_ = l_Std_Internal_Parsec_String_pstring(v_midnight_2618_, v_a_2614_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_pos_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2629_; 
lean_dec_ref(v_noon_2617_);
lean_dec_ref(v_pm_2616_);
lean_dec_ref(v_am_2615_);
lean_dec_ref(v_a_2614_);
v_pos_2620_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2629_ == 0)
{
lean_object* v_unused_2630_; 
v_unused_2630_ = lean_ctor_get(v___x_2619_, 1);
lean_dec(v_unused_2630_);
v___x_2622_ = v___x_2619_;
v_isShared_2623_ = v_isSharedCheck_2629_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_pos_2620_);
lean_dec(v___x_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2629_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
uint8_t v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2627_; 
v___x_2624_ = 3;
v___x_2625_ = lean_box(v___x_2624_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 1, v___x_2625_);
v___x_2627_ = v___x_2622_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_pos_2620_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
else
{
lean_object* v_pos_2631_; lean_object* v_err_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2709_; 
v_pos_2631_ = lean_ctor_get(v___x_2619_, 0);
v_err_2632_ = lean_ctor_get(v___x_2619_, 1);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2634_ = v___x_2619_;
v_isShared_2635_ = v_isSharedCheck_2709_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_err_2632_);
lean_inc(v_pos_2631_);
lean_dec(v___x_2619_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2709_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v_snd_2636_; lean_object* v_snd_2637_; uint8_t v_decide_2638_; 
v_snd_2636_ = lean_ctor_get(v_a_2614_, 1);
lean_inc(v_snd_2636_);
lean_dec_ref(v_a_2614_);
v_snd_2637_ = lean_ctor_get(v_pos_2631_, 1);
v_decide_2638_ = lean_nat_dec_eq(v_snd_2636_, v_snd_2637_);
lean_dec(v_snd_2636_);
if (v_decide_2638_ == 0)
{
lean_object* v___x_2640_; 
lean_dec_ref(v_noon_2617_);
lean_dec_ref(v_pm_2616_);
lean_dec_ref(v_am_2615_);
if (v_isShared_2635_ == 0)
{
v___x_2640_ = v___x_2634_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_pos_2631_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v_err_2632_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
else
{
lean_object* v___x_2642_; 
lean_inc(v_snd_2637_);
lean_del_object(v___x_2634_);
lean_dec(v_err_2632_);
v___x_2642_ = l_Std_Internal_Parsec_String_pstring(v_noon_2617_, v_pos_2631_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_pos_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2652_; 
lean_dec(v_snd_2637_);
lean_dec_ref(v_pm_2616_);
lean_dec_ref(v_am_2615_);
v_pos_2643_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2652_ == 0)
{
lean_object* v_unused_2653_; 
v_unused_2653_ = lean_ctor_get(v___x_2642_, 1);
lean_dec(v_unused_2653_);
v___x_2645_ = v___x_2642_;
v_isShared_2646_ = v_isSharedCheck_2652_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_pos_2643_);
lean_dec(v___x_2642_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2652_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
uint8_t v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2650_; 
v___x_2647_ = 2;
v___x_2648_ = lean_box(v___x_2647_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 1, v___x_2648_);
v___x_2650_ = v___x_2645_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_pos_2643_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v___x_2648_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
else
{
lean_object* v_pos_2654_; lean_object* v_err_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2708_; 
v_pos_2654_ = lean_ctor_get(v___x_2642_, 0);
v_err_2655_ = lean_ctor_get(v___x_2642_, 1);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2657_ = v___x_2642_;
v_isShared_2658_ = v_isSharedCheck_2708_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_err_2655_);
lean_inc(v_pos_2654_);
lean_dec(v___x_2642_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2708_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v_snd_2659_; uint8_t v_decide_2660_; 
v_snd_2659_ = lean_ctor_get(v_pos_2654_, 1);
v_decide_2660_ = lean_nat_dec_eq(v_snd_2637_, v_snd_2659_);
lean_dec(v_snd_2637_);
if (v_decide_2660_ == 0)
{
lean_object* v___x_2662_; 
lean_dec_ref(v_pm_2616_);
lean_dec_ref(v_am_2615_);
if (v_isShared_2658_ == 0)
{
v___x_2662_ = v___x_2657_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_pos_2654_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_err_2655_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
else
{
lean_object* v___x_2664_; 
lean_inc(v_snd_2659_);
lean_del_object(v___x_2657_);
lean_dec(v_err_2655_);
v___x_2664_ = l_Std_Internal_Parsec_String_pstring(v_am_2615_, v_pos_2654_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_pos_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2674_; 
lean_dec(v_snd_2659_);
lean_dec_ref(v_pm_2616_);
v_pos_2665_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2674_ == 0)
{
lean_object* v_unused_2675_; 
v_unused_2675_ = lean_ctor_get(v___x_2664_, 1);
lean_dec(v_unused_2675_);
v___x_2667_ = v___x_2664_;
v_isShared_2668_ = v_isSharedCheck_2674_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_pos_2665_);
lean_dec(v___x_2664_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2674_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
uint8_t v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2669_ = 0;
v___x_2670_ = lean_box(v___x_2669_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 1, v___x_2670_);
v___x_2672_ = v___x_2667_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_pos_2665_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
else
{
lean_object* v_pos_2676_; lean_object* v_err_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2707_; 
v_pos_2676_ = lean_ctor_get(v___x_2664_, 0);
v_err_2677_ = lean_ctor_get(v___x_2664_, 1);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2679_ = v___x_2664_;
v_isShared_2680_ = v_isSharedCheck_2707_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_err_2677_);
lean_inc(v_pos_2676_);
lean_dec(v___x_2664_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2707_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v_snd_2681_; uint8_t v_decide_2682_; 
v_snd_2681_ = lean_ctor_get(v_pos_2676_, 1);
v_decide_2682_ = lean_nat_dec_eq(v_snd_2659_, v_snd_2681_);
lean_dec(v_snd_2659_);
if (v_decide_2682_ == 0)
{
lean_object* v___x_2684_; 
lean_dec_ref(v_pm_2616_);
if (v_isShared_2680_ == 0)
{
v___x_2684_ = v___x_2679_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_pos_2676_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_err_2677_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
else
{
lean_object* v___x_2686_; 
lean_del_object(v___x_2679_);
lean_dec(v_err_2677_);
v___x_2686_ = l_Std_Internal_Parsec_String_pstring(v_pm_2616_, v_pos_2676_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_pos_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2696_; 
v_pos_2687_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2696_ == 0)
{
lean_object* v_unused_2697_; 
v_unused_2697_ = lean_ctor_get(v___x_2686_, 1);
lean_dec(v_unused_2697_);
v___x_2689_ = v___x_2686_;
v_isShared_2690_ = v_isSharedCheck_2696_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_pos_2687_);
lean_dec(v___x_2686_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2696_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
uint8_t v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2691_ = 1;
v___x_2692_ = lean_box(v___x_2691_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 1, v___x_2692_);
v___x_2694_ = v___x_2689_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_pos_2687_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
else
{
lean_object* v_pos_2698_; lean_object* v_err_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
v_pos_2698_ = lean_ctor_get(v___x_2686_, 0);
v_err_2699_ = lean_ctor_get(v___x_2686_, 1);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2686_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_err_2699_);
lean_inc(v_pos_2698_);
lean_dec(v___x_2686_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_pos_2698_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v_err_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(lean_object* v_arr_2710_, lean_object* v_a_2711_){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; uint8_t v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; uint8_t v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; uint8_t v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; uint8_t v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v_pairs_2749_; lean_object* v___x_2750_; 
v___x_2712_ = lean_unsigned_to_nat(6u);
v___x_2713_ = lean_unsigned_to_nat(0u);
v___x_2714_ = lean_array_fget_borrowed(v_arr_2710_, v___x_2713_);
v___x_2715_ = 0;
v___x_2716_ = lean_box(v___x_2715_);
lean_inc(v___x_2714_);
v___x_2717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2714_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
v___x_2718_ = lean_unsigned_to_nat(1u);
v___x_2719_ = lean_array_fget_borrowed(v_arr_2710_, v___x_2718_);
v___x_2720_ = 1;
v___x_2721_ = lean_box(v___x_2720_);
lean_inc(v___x_2719_);
v___x_2722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2719_);
lean_ctor_set(v___x_2722_, 1, v___x_2721_);
v___x_2723_ = lean_unsigned_to_nat(2u);
v___x_2724_ = lean_array_fget_borrowed(v_arr_2710_, v___x_2723_);
v___x_2725_ = 2;
v___x_2726_ = lean_box(v___x_2725_);
lean_inc(v___x_2724_);
v___x_2727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2724_);
lean_ctor_set(v___x_2727_, 1, v___x_2726_);
v___x_2728_ = lean_unsigned_to_nat(3u);
v___x_2729_ = lean_array_fget_borrowed(v_arr_2710_, v___x_2728_);
v___x_2730_ = 3;
v___x_2731_ = lean_box(v___x_2730_);
lean_inc(v___x_2729_);
v___x_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2729_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
v___x_2733_ = lean_unsigned_to_nat(4u);
v___x_2734_ = lean_array_fget_borrowed(v_arr_2710_, v___x_2733_);
v___x_2735_ = 4;
v___x_2736_ = lean_box(v___x_2735_);
lean_inc(v___x_2734_);
v___x_2737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2734_);
lean_ctor_set(v___x_2737_, 1, v___x_2736_);
v___x_2738_ = lean_unsigned_to_nat(5u);
v___x_2739_ = lean_array_fget_borrowed(v_arr_2710_, v___x_2738_);
v___x_2740_ = 5;
v___x_2741_ = lean_box(v___x_2740_);
lean_inc(v___x_2739_);
v___x_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2739_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = lean_mk_empty_array_with_capacity(v___x_2712_);
v___x_2744_ = lean_array_push(v___x_2743_, v___x_2717_);
v___x_2745_ = lean_array_push(v___x_2744_, v___x_2722_);
v___x_2746_ = lean_array_push(v___x_2745_, v___x_2727_);
v___x_2747_ = lean_array_push(v___x_2746_, v___x_2732_);
v___x_2748_ = lean_array_push(v___x_2747_, v___x_2737_);
v_pairs_2749_ = lean_array_push(v___x_2748_, v___x_2742_);
v___x_2750_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2749_, v_a_2711_);
lean_dec_ref(v_pairs_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom___boxed(lean_object* v_arr_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_arr_2751_, v_a_2752_);
lean_dec_ref(v_arr_2751_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(lean_object* v_parse_2754_, lean_object* v_size_2755_, lean_object* v_acc_2756_, lean_object* v_count_2757_, lean_object* v_a_2758_){
_start:
{
uint8_t v___x_2759_; 
v___x_2759_ = lean_nat_dec_le(v_size_2755_, v_count_2757_);
if (v___x_2759_ == 0)
{
lean_object* v___x_2760_; 
lean_inc_ref(v_parse_2754_);
v___x_2760_ = lean_apply_1(v_parse_2754_, v_a_2758_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_pos_2761_; lean_object* v_res_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v_pos_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_pos_2761_);
v_res_2762_ = lean_ctor_get(v___x_2760_, 1);
lean_inc(v_res_2762_);
lean_dec_ref_known(v___x_2760_, 2);
v___x_2763_ = lean_array_push(v_acc_2756_, v_res_2762_);
v___x_2764_ = lean_unsigned_to_nat(1u);
v___x_2765_ = lean_nat_add(v_count_2757_, v___x_2764_);
lean_dec(v_count_2757_);
v_acc_2756_ = v___x_2763_;
v_count_2757_ = v___x_2765_;
v_a_2758_ = v_pos_2761_;
goto _start;
}
else
{
lean_object* v_pos_2767_; lean_object* v_err_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec(v_count_2757_);
lean_dec_ref(v_acc_2756_);
lean_dec_ref(v_parse_2754_);
v_pos_2767_ = lean_ctor_get(v___x_2760_, 0);
v_err_2768_ = lean_ctor_get(v___x_2760_, 1);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2760_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_err_2768_);
lean_inc(v_pos_2767_);
lean_dec(v___x_2760_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_pos_2767_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_err_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
else
{
lean_object* v___x_2776_; 
lean_dec(v_count_2757_);
lean_dec_ref(v_parse_2754_);
v___x_2776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2776_, 0, v_a_2758_);
lean_ctor_set(v___x_2776_, 1, v_acc_2756_);
return v___x_2776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg___boxed(lean_object* v_parse_2777_, lean_object* v_size_2778_, lean_object* v_acc_2779_, lean_object* v_count_2780_, lean_object* v_a_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2777_, v_size_2778_, v_acc_2779_, v_count_2780_, v_a_2781_);
lean_dec(v_size_2778_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go(lean_object* v_00_u03b1_2783_, lean_object* v_parse_2784_, lean_object* v_size_2785_, lean_object* v_acc_2786_, lean_object* v_count_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v___x_2789_; 
v___x_2789_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2784_, v_size_2785_, v_acc_2786_, v_count_2787_, v_a_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___boxed(lean_object* v_00_u03b1_2790_, lean_object* v_parse_2791_, lean_object* v_size_2792_, lean_object* v_acc_2793_, lean_object* v_count_2794_, lean_object* v_a_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go(v_00_u03b1_2790_, v_parse_2791_, v_size_2792_, v_acc_2793_, v_count_2794_, v_a_2795_);
lean_dec(v_size_2792_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(lean_object* v_parse_2799_, lean_object* v_size_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2802_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___closed__0));
v___x_2803_ = lean_unsigned_to_nat(12u);
v___x_2804_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2799_, v_size_2800_, v___x_2802_, v___x_2803_, v_a_2801_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___boxed(lean_object* v_parse_2805_, lean_object* v_size_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(v_parse_2805_, v_size_2806_, v_a_2807_);
lean_dec(v_size_2806_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly(lean_object* v_00_u03b1_2809_, lean_object* v_parse_2810_, lean_object* v_size_2811_, lean_object* v_a_2812_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(v_parse_2810_, v_size_2811_, v_a_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___boxed(lean_object* v_00_u03b1_2814_, lean_object* v_parse_2815_, lean_object* v_size_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly(v_00_u03b1_2814_, v_parse_2815_, v_size_2816_, v_a_2817_);
lean_dec(v_size_2816_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(lean_object* v_parse_2819_, lean_object* v_size_2820_, lean_object* v_acc_2821_, lean_object* v_count_2822_, lean_object* v_a_2823_){
_start:
{
uint8_t v___x_2824_; 
v___x_2824_ = lean_nat_dec_le(v_size_2820_, v_count_2822_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; 
lean_inc_ref(v_parse_2819_);
v___x_2825_ = lean_apply_1(v_parse_2819_, v_a_2823_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_pos_2826_; lean_object* v_res_2827_; uint32_t v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v_pos_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_pos_2826_);
v_res_2827_ = lean_ctor_get(v___x_2825_, 1);
lean_inc(v_res_2827_);
lean_dec_ref_known(v___x_2825_, 2);
v___x_2828_ = lean_unbox_uint32(v_res_2827_);
lean_dec(v_res_2827_);
v___x_2829_ = lean_string_push(v_acc_2821_, v___x_2828_);
v___x_2830_ = lean_unsigned_to_nat(1u);
v___x_2831_ = lean_nat_add(v_count_2822_, v___x_2830_);
lean_dec(v_count_2822_);
v_acc_2821_ = v___x_2829_;
v_count_2822_ = v___x_2831_;
v_a_2823_ = v_pos_2826_;
goto _start;
}
else
{
lean_object* v_pos_2833_; lean_object* v_err_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec(v_count_2822_);
lean_dec_ref(v_acc_2821_);
lean_dec_ref(v_parse_2819_);
v_pos_2833_ = lean_ctor_get(v___x_2825_, 0);
v_err_2834_ = lean_ctor_get(v___x_2825_, 1);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2825_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_err_2834_);
lean_inc(v_pos_2833_);
lean_dec(v___x_2825_);
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
lean_object* v___x_2842_; 
lean_dec(v_count_2822_);
lean_dec_ref(v_parse_2819_);
v___x_2842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2842_, 0, v_a_2823_);
lean_ctor_set(v___x_2842_, 1, v_acc_2821_);
return v___x_2842_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go___boxed(lean_object* v_parse_2843_, lean_object* v_size_2844_, lean_object* v_acc_2845_, lean_object* v_count_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(v_parse_2843_, v_size_2844_, v_acc_2845_, v_count_2846_, v_a_2847_);
lean_dec(v_size_2844_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(lean_object* v_parse_2849_, lean_object* v_size_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2852_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_2853_ = lean_unsigned_to_nat(0u);
v___x_2854_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(v_parse_2849_, v_size_2850_, v___x_2852_, v___x_2853_, v_a_2851_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars___boxed(lean_object* v_parse_2855_, lean_object* v_size_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v_parse_2855_, v_size_2856_, v_a_2857_);
lean_dec(v_size_2856_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(lean_object* v_parser_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v_pos_2862_; lean_object* v_res_2863_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
lean_inc_ref(v_a_2860_);
v___x_2896_ = l_Std_Internal_Parsec_String_pstring(v___x_2895_, v_a_2860_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_pos_2897_; lean_object* v_res_2898_; lean_object* v___x_2899_; 
lean_dec_ref(v_a_2860_);
v_pos_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_pos_2897_);
v_res_2898_ = lean_ctor_get(v___x_2896_, 1);
lean_inc(v_res_2898_);
lean_dec_ref_known(v___x_2896_, 2);
v___x_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2899_, 0, v_res_2898_);
v_pos_2862_ = v_pos_2897_;
v_res_2863_ = v___x_2899_;
goto v___jp_2861_;
}
else
{
lean_object* v_pos_2900_; lean_object* v_err_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2912_; 
v_pos_2900_ = lean_ctor_get(v___x_2896_, 0);
v_err_2901_ = lean_ctor_get(v___x_2896_, 1);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2903_ = v___x_2896_;
v_isShared_2904_ = v_isSharedCheck_2912_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_err_2901_);
lean_inc(v_pos_2900_);
lean_dec(v___x_2896_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2912_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v_snd_2905_; lean_object* v_snd_2906_; uint8_t v_decide_2907_; 
v_snd_2905_ = lean_ctor_get(v_a_2860_, 1);
lean_inc(v_snd_2905_);
lean_dec_ref(v_a_2860_);
v_snd_2906_ = lean_ctor_get(v_pos_2900_, 1);
v_decide_2907_ = lean_nat_dec_eq(v_snd_2905_, v_snd_2906_);
lean_dec(v_snd_2905_);
if (v_decide_2907_ == 0)
{
lean_object* v___x_2909_; 
lean_dec_ref(v_parser_2859_);
if (v_isShared_2904_ == 0)
{
v___x_2909_ = v___x_2903_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_pos_2900_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_err_2901_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
else
{
lean_object* v___x_2911_; 
lean_del_object(v___x_2903_);
lean_dec(v_err_2901_);
v___x_2911_ = lean_box(0);
v_pos_2862_ = v_pos_2900_;
v_res_2863_ = v___x_2911_;
goto v___jp_2861_;
}
}
}
v___jp_2861_:
{
lean_object* v___x_2864_; 
v___x_2864_ = lean_apply_1(v_parser_2859_, v_pos_2862_);
if (lean_obj_tag(v___x_2864_) == 0)
{
if (lean_obj_tag(v_res_2863_) == 0)
{
lean_object* v_pos_2865_; lean_object* v_res_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2874_; 
v_pos_2865_ = lean_ctor_get(v___x_2864_, 0);
v_res_2866_ = lean_ctor_get(v___x_2864_, 1);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2868_ = v___x_2864_;
v_isShared_2869_ = v_isSharedCheck_2874_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_res_2866_);
lean_inc(v_pos_2865_);
lean_dec(v___x_2864_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2874_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; lean_object* v___x_2872_; 
v___x_2870_ = lean_nat_to_int(v_res_2866_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 1, v___x_2870_);
v___x_2872_ = v___x_2868_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_pos_2865_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v___x_2870_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
else
{
lean_object* v_pos_2875_; lean_object* v_res_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2885_; 
lean_dec_ref_known(v_res_2863_, 1);
v_pos_2875_ = lean_ctor_get(v___x_2864_, 0);
v_res_2876_ = lean_ctor_get(v___x_2864_, 1);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2878_ = v___x_2864_;
v_isShared_2879_ = v_isSharedCheck_2885_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_res_2876_);
lean_inc(v_pos_2875_);
lean_dec(v___x_2864_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2885_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2880_ = lean_nat_to_int(v_res_2876_);
v___x_2881_ = lean_int_neg(v___x_2880_);
lean_dec(v___x_2880_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 1, v___x_2881_);
v___x_2883_ = v___x_2878_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_pos_2875_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v___x_2881_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
else
{
lean_object* v_pos_2886_; lean_object* v_err_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec(v_res_2863_);
v_pos_2886_ = lean_ctor_get(v___x_2864_, 0);
v_err_2887_ = lean_ctor_get(v___x_2864_, 1);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2864_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_err_2887_);
lean_inc(v_pos_2886_);
lean_dec(v___x_2864_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_pos_2886_);
lean_ctor_set(v_reuseFailAlloc_2893_, 1, v_err_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___lam__0(lean_object* v___y_2913_){
_start:
{
lean_object* v_fst_2917_; lean_object* v_snd_2918_; lean_object* v___x_2919_; uint8_t v_decide_2920_; 
v_fst_2917_ = lean_ctor_get(v___y_2913_, 0);
v_snd_2918_ = lean_ctor_get(v___y_2913_, 1);
v___x_2919_ = lean_string_utf8_byte_size(v_fst_2917_);
v_decide_2920_ = lean_nat_dec_eq(v_snd_2918_, v___x_2919_);
if (v_decide_2920_ == 0)
{
uint32_t v_c_2921_; lean_object* v___x_2922_; lean_object* v_it_x27_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; uint32_t v___x_2926_; uint8_t v___x_2927_; 
v_c_2921_ = lean_string_utf8_get_fast(v_fst_2917_, v_snd_2918_);
v___x_2922_ = lean_string_utf8_next_fast(v_fst_2917_, v_snd_2918_);
lean_inc(v_fst_2917_);
v_it_x27_2923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_2923_, 0, v_fst_2917_);
lean_ctor_set(v_it_x27_2923_, 1, v___x_2922_);
v___x_2924_ = lean_box_uint32(v_c_2921_);
v___x_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2925_, 0, v_it_x27_2923_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
v___x_2926_ = 48;
v___x_2927_ = lean_uint32_dec_le(v___x_2926_, v_c_2921_);
if (v___x_2927_ == 0)
{
lean_dec_ref_known(v___x_2925_, 2);
goto v___jp_2914_;
}
else
{
uint32_t v___x_2928_; uint8_t v___x_2929_; 
v___x_2928_ = 57;
v___x_2929_ = lean_uint32_dec_le(v_c_2921_, v___x_2928_);
if (v___x_2929_ == 0)
{
lean_dec_ref_known(v___x_2925_, 2);
goto v___jp_2914_;
}
else
{
lean_dec_ref(v___y_2913_);
return v___x_2925_;
}
}
}
else
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = lean_box(0);
v___x_2931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___y_2913_);
lean_ctor_set(v___x_2931_, 1, v___x_2930_);
return v___x_2931_;
}
v___jp_2914_:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2915_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_2916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___y_2913_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
return v___x_2916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(lean_object* v_size_2933_, lean_object* v_a_2934_){
_start:
{
lean_object* v___f_2935_; lean_object* v___x_2936_; 
v___f_2935_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_2936_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_2935_, v_size_2933_, v_a_2934_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_pos_2937_; lean_object* v_res_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2949_; 
v_pos_2937_ = lean_ctor_get(v___x_2936_, 0);
v_res_2938_ = lean_ctor_get(v___x_2936_, 1);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2940_ = v___x_2936_;
v_isShared_2941_ = v_isSharedCheck_2949_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_res_2938_);
lean_inc(v_pos_2937_);
lean_dec(v___x_2936_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2949_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2947_; 
v___x_2942_ = lean_unsigned_to_nat(0u);
v___x_2943_ = lean_string_utf8_byte_size(v_res_2938_);
v___x_2944_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2944_, 0, v_res_2938_);
lean_ctor_set(v___x_2944_, 1, v___x_2942_);
lean_ctor_set(v___x_2944_, 2, v___x_2943_);
v___x_2945_ = l_String_Slice_toNat_x21(v___x_2944_);
lean_dec_ref_known(v___x_2944_, 3);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 1, v___x_2945_);
v___x_2947_ = v___x_2940_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_pos_2937_);
lean_ctor_set(v_reuseFailAlloc_2948_, 1, v___x_2945_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
else
{
lean_object* v_pos_2950_; lean_object* v_err_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
v_pos_2950_ = lean_ctor_get(v___x_2936_, 0);
v_err_2951_ = lean_ctor_get(v___x_2936_, 1);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2936_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_err_2951_);
lean_inc(v_pos_2950_);
lean_dec(v___x_2936_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_pos_2950_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_err_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed(lean_object* v_size_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_size_2959_, v_a_2960_);
lean_dec(v_size_2959_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(lean_object* v_acc_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v_fst_2964_; lean_object* v_snd_2965_; lean_object* v_pos_2967_; lean_object* v_snd_2968_; lean_object* v_err_2969_; lean_object* v___x_2975_; uint8_t v_decide_2976_; 
v_fst_2964_ = lean_ctor_get(v_a_2963_, 0);
v_snd_2965_ = lean_ctor_get(v_a_2963_, 1);
lean_inc(v_snd_2965_);
v___x_2975_ = lean_string_utf8_byte_size(v_fst_2964_);
v_decide_2976_ = lean_nat_dec_eq(v_snd_2965_, v___x_2975_);
if (v_decide_2976_ == 0)
{
uint32_t v_c_2977_; uint32_t v___x_2978_; uint8_t v___x_2979_; 
v_c_2977_ = lean_string_utf8_get_fast(v_fst_2964_, v_snd_2965_);
v___x_2978_ = 48;
v___x_2979_ = lean_uint32_dec_le(v___x_2978_, v_c_2977_);
if (v___x_2979_ == 0)
{
goto v___jp_2973_;
}
else
{
uint32_t v___x_2980_; uint8_t v___x_2981_; 
v___x_2980_ = 57;
v___x_2981_ = lean_uint32_dec_le(v_c_2977_, v___x_2980_);
if (v___x_2981_ == 0)
{
goto v___jp_2973_;
}
else
{
lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2991_; 
lean_inc(v_fst_2964_);
v_isSharedCheck_2991_ = !lean_is_exclusive(v_a_2963_);
if (v_isSharedCheck_2991_ == 0)
{
lean_object* v_unused_2992_; lean_object* v_unused_2993_; 
v_unused_2992_ = lean_ctor_get(v_a_2963_, 1);
lean_dec(v_unused_2992_);
v_unused_2993_ = lean_ctor_get(v_a_2963_, 0);
lean_dec(v_unused_2993_);
v___x_2983_ = v_a_2963_;
v_isShared_2984_ = v_isSharedCheck_2991_;
goto v_resetjp_2982_;
}
else
{
lean_dec(v_a_2963_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2991_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2985_; lean_object* v_it_x27_2987_; 
v___x_2985_ = lean_string_utf8_next_fast(v_fst_2964_, v_snd_2965_);
lean_dec(v_snd_2965_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 1, v___x_2985_);
v_it_x27_2987_ = v___x_2983_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_fst_2964_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v___x_2985_);
v_it_x27_2987_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; 
v___x_2988_ = lean_string_push(v_acc_2962_, v_c_2977_);
v_acc_2962_ = v___x_2988_;
v_a_2963_ = v_it_x27_2987_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_2994_; 
v___x_2994_ = lean_box(0);
lean_inc(v_snd_2965_);
v_pos_2967_ = v_a_2963_;
v_snd_2968_ = v_snd_2965_;
v_err_2969_ = v___x_2994_;
goto v___jp_2966_;
}
v___jp_2966_:
{
uint8_t v_decide_2970_; 
v_decide_2970_ = lean_nat_dec_eq(v_snd_2965_, v_snd_2968_);
lean_dec(v_snd_2968_);
lean_dec(v_snd_2965_);
if (v_decide_2970_ == 0)
{
lean_object* v___x_2971_; 
lean_dec_ref(v_acc_2962_);
lean_inc(v_err_2969_);
v___x_2971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2971_, 0, v_pos_2967_);
lean_ctor_set(v___x_2971_, 1, v_err_2969_);
return v___x_2971_;
}
else
{
lean_object* v___x_2972_; 
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v_pos_2967_);
lean_ctor_set(v___x_2972_, 1, v_acc_2962_);
return v___x_2972_;
}
}
v___jp_2973_:
{
lean_object* v___x_2974_; 
v___x_2974_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_2965_);
v_pos_2967_ = v_a_2963_;
v_snd_2968_ = v_snd_2965_;
v_err_2969_ = v___x_2974_;
goto v___jp_2966_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(lean_object* v_size_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v___f_2997_; lean_object* v___x_2998_; 
v___f_2997_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_2998_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_2997_, v_size_2995_, v_a_2996_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_pos_2999_; lean_object* v_res_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v_pos_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_pos_2999_);
v_res_3000_ = lean_ctor_get(v___x_2998_, 1);
lean_inc(v_res_3000_);
lean_dec_ref_known(v___x_2998_, 2);
v___x_3001_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3002_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(v___x_3001_, v_pos_2999_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_pos_3003_; lean_object* v_res_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3016_; 
v_pos_3003_ = lean_ctor_get(v___x_3002_, 0);
v_res_3004_ = lean_ctor_get(v___x_3002_, 1);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3006_ = v___x_3002_;
v_isShared_3007_ = v_isSharedCheck_3016_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_res_3004_);
lean_inc(v_pos_3003_);
lean_dec(v___x_3002_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3016_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3014_; 
v___x_3008_ = lean_string_append(v_res_3000_, v_res_3004_);
lean_dec(v_res_3004_);
v___x_3009_ = lean_unsigned_to_nat(0u);
v___x_3010_ = lean_string_utf8_byte_size(v___x_3008_);
v___x_3011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3008_);
lean_ctor_set(v___x_3011_, 1, v___x_3009_);
lean_ctor_set(v___x_3011_, 2, v___x_3010_);
v___x_3012_ = l_String_Slice_toNat_x21(v___x_3011_);
lean_dec_ref_known(v___x_3011_, 3);
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 1, v___x_3012_);
v___x_3014_ = v___x_3006_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_pos_3003_);
lean_ctor_set(v_reuseFailAlloc_3015_, 1, v___x_3012_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
else
{
lean_object* v_pos_3017_; lean_object* v_err_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_dec(v_res_3000_);
v_pos_3017_ = lean_ctor_get(v___x_3002_, 0);
v_err_3018_ = lean_ctor_get(v___x_3002_, 1);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_3002_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_err_3018_);
lean_inc(v_pos_3017_);
lean_dec(v___x_3002_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_pos_3017_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v_err_3018_);
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
v_pos_3026_ = lean_ctor_get(v___x_2998_, 0);
v_err_3027_ = lean_ctor_get(v___x_2998_, 1);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_2998_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_err_3027_);
lean_inc(v_pos_3026_);
lean_dec(v___x_2998_);
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___boxed(lean_object* v_size_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v_size_3035_, v_a_3036_);
lean_dec(v_size_3035_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(lean_object* v_size_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v___x_3040_; uint8_t v___x_3041_; 
v___x_3040_ = lean_unsigned_to_nat(1u);
v___x_3041_ = lean_nat_dec_eq(v_size_3038_, v___x_3040_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; 
v___x_3042_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_size_3038_, v_a_3039_);
return v___x_3042_;
}
else
{
lean_object* v___x_3043_; 
v___x_3043_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v___x_3040_, v_a_3039_);
return v___x_3043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed(lean_object* v_size_3044_, lean_object* v_a_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_size_3044_, v_a_3045_);
lean_dec(v_size_3044_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(lean_object* v_size_3047_, lean_object* v_pad_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v___f_3050_; lean_object* v___x_3051_; 
v___f_3050_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3051_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3050_, v_size_3047_, v_a_3049_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_pos_3052_; lean_object* v_res_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3066_; 
v_pos_3052_ = lean_ctor_get(v___x_3051_, 0);
v_res_3053_ = lean_ctor_get(v___x_3051_, 1);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3055_ = v___x_3051_;
v_isShared_3056_ = v_isSharedCheck_3066_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_res_3053_);
lean_inc(v_pos_3052_);
lean_dec(v___x_3051_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3066_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
uint32_t v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3064_; 
v___x_3057_ = 48;
v___x_3058_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_pad_3048_, v___x_3057_, v_res_3053_);
v___x_3059_ = lean_unsigned_to_nat(0u);
v___x_3060_ = lean_string_utf8_byte_size(v___x_3058_);
v___x_3061_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3058_);
lean_ctor_set(v___x_3061_, 1, v___x_3059_);
lean_ctor_set(v___x_3061_, 2, v___x_3060_);
v___x_3062_ = l_String_Slice_toNat_x21(v___x_3061_);
lean_dec_ref_known(v___x_3061_, 3);
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 1, v___x_3062_);
v___x_3064_ = v___x_3055_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_pos_3052_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v___x_3062_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
else
{
lean_object* v_pos_3067_; lean_object* v_err_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
v_pos_3067_ = lean_ctor_get(v___x_3051_, 0);
v_err_3068_ = lean_ctor_get(v___x_3051_, 1);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3051_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_err_3068_);
lean_inc(v_pos_3067_);
lean_dec(v___x_3051_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_pos_3067_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v_err_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed(lean_object* v_size_3076_, lean_object* v_pad_3077_, lean_object* v_a_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(v_size_3076_, v_pad_3077_, v_a_3078_);
lean_dec(v_pad_3077_);
lean_dec(v_size_3076_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(lean_object* v_acc_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v_pos_3083_; uint32_t v_res_3084_; lean_object* v_fst_3087_; lean_object* v_snd_3088_; lean_object* v_pos_3090_; lean_object* v_snd_3091_; lean_object* v_err_3092_; lean_object* v___x_3096_; uint8_t v_decide_3097_; 
v_fst_3087_ = lean_ctor_get(v_a_3081_, 0);
v_snd_3088_ = lean_ctor_get(v_a_3081_, 1);
lean_inc(v_snd_3088_);
v___x_3096_ = lean_string_utf8_byte_size(v_fst_3087_);
v_decide_3097_ = lean_nat_dec_eq(v_snd_3088_, v___x_3096_);
if (v_decide_3097_ == 0)
{
uint32_t v_c_3098_; lean_object* v___x_3099_; lean_object* v_it_x27_3100_; uint32_t v___x_3119_; uint8_t v___x_3120_; 
v_c_3098_ = lean_string_utf8_get_fast(v_fst_3087_, v_snd_3088_);
v___x_3099_ = lean_string_utf8_next_fast(v_fst_3087_, v_snd_3088_);
lean_inc(v_fst_3087_);
v_it_x27_3100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3100_, 0, v_fst_3087_);
lean_ctor_set(v_it_x27_3100_, 1, v___x_3099_);
v___x_3119_ = 65;
v___x_3120_ = lean_uint32_dec_le(v___x_3119_, v_c_3098_);
if (v___x_3120_ == 0)
{
goto v___jp_3114_;
}
else
{
uint32_t v___x_3121_; uint8_t v___x_3122_; 
v___x_3121_ = 90;
v___x_3122_ = lean_uint32_dec_le(v_c_3098_, v___x_3121_);
if (v___x_3122_ == 0)
{
goto v___jp_3114_;
}
else
{
lean_dec(v_snd_3088_);
lean_dec_ref(v_a_3081_);
v_pos_3083_ = v_it_x27_3100_;
v_res_3084_ = v_c_3098_;
goto v___jp_3082_;
}
}
v___jp_3101_:
{
uint32_t v___x_3102_; uint8_t v___x_3103_; 
v___x_3102_ = 95;
v___x_3103_ = lean_uint32_dec_eq(v_c_3098_, v___x_3102_);
if (v___x_3103_ == 0)
{
uint32_t v___x_3104_; uint8_t v___x_3105_; 
v___x_3104_ = 45;
v___x_3105_ = lean_uint32_dec_eq(v_c_3098_, v___x_3104_);
if (v___x_3105_ == 0)
{
uint32_t v___x_3106_; uint8_t v___x_3107_; 
v___x_3106_ = 47;
v___x_3107_ = lean_uint32_dec_eq(v_c_3098_, v___x_3106_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; 
lean_dec_ref_known(v_it_x27_3100_, 2);
v___x_3108_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3088_);
v_pos_3090_ = v_a_3081_;
v_snd_3091_ = v_snd_3088_;
v_err_3092_ = v___x_3108_;
goto v___jp_3089_;
}
else
{
lean_dec(v_snd_3088_);
lean_dec_ref(v_a_3081_);
v_pos_3083_ = v_it_x27_3100_;
v_res_3084_ = v_c_3098_;
goto v___jp_3082_;
}
}
else
{
lean_dec(v_snd_3088_);
lean_dec_ref(v_a_3081_);
v_pos_3083_ = v_it_x27_3100_;
v_res_3084_ = v_c_3098_;
goto v___jp_3082_;
}
}
else
{
lean_dec(v_snd_3088_);
lean_dec_ref(v_a_3081_);
v_pos_3083_ = v_it_x27_3100_;
v_res_3084_ = v_c_3098_;
goto v___jp_3082_;
}
}
v___jp_3109_:
{
uint32_t v___x_3110_; uint8_t v___x_3111_; 
v___x_3110_ = 48;
v___x_3111_ = lean_uint32_dec_le(v___x_3110_, v_c_3098_);
if (v___x_3111_ == 0)
{
goto v___jp_3101_;
}
else
{
uint32_t v___x_3112_; uint8_t v___x_3113_; 
v___x_3112_ = 57;
v___x_3113_ = lean_uint32_dec_le(v_c_3098_, v___x_3112_);
if (v___x_3113_ == 0)
{
goto v___jp_3101_;
}
else
{
lean_dec(v_snd_3088_);
lean_dec_ref(v_a_3081_);
v_pos_3083_ = v_it_x27_3100_;
v_res_3084_ = v_c_3098_;
goto v___jp_3082_;
}
}
}
v___jp_3114_:
{
uint32_t v___x_3115_; uint8_t v___x_3116_; 
v___x_3115_ = 97;
v___x_3116_ = lean_uint32_dec_le(v___x_3115_, v_c_3098_);
if (v___x_3116_ == 0)
{
goto v___jp_3109_;
}
else
{
uint32_t v___x_3117_; uint8_t v___x_3118_; 
v___x_3117_ = 122;
v___x_3118_ = lean_uint32_dec_le(v_c_3098_, v___x_3117_);
if (v___x_3118_ == 0)
{
goto v___jp_3109_;
}
else
{
lean_dec(v_snd_3088_);
lean_dec_ref(v_a_3081_);
v_pos_3083_ = v_it_x27_3100_;
v_res_3084_ = v_c_3098_;
goto v___jp_3082_;
}
}
}
}
else
{
lean_object* v___x_3123_; 
v___x_3123_ = lean_box(0);
lean_inc(v_snd_3088_);
v_pos_3090_ = v_a_3081_;
v_snd_3091_ = v_snd_3088_;
v_err_3092_ = v___x_3123_;
goto v___jp_3089_;
}
v___jp_3082_:
{
lean_object* v___x_3085_; 
v___x_3085_ = lean_string_push(v_acc_3080_, v_res_3084_);
v_acc_3080_ = v___x_3085_;
v_a_3081_ = v_pos_3083_;
goto _start;
}
v___jp_3089_:
{
uint8_t v_decide_3093_; 
v_decide_3093_ = lean_nat_dec_eq(v_snd_3088_, v_snd_3091_);
lean_dec(v_snd_3091_);
lean_dec(v_snd_3088_);
if (v_decide_3093_ == 0)
{
lean_object* v___x_3094_; 
lean_dec_ref(v_acc_3080_);
lean_inc(v_err_3092_);
v___x_3094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3094_, 0, v_pos_3090_);
lean_ctor_set(v___x_3094_, 1, v_err_3092_);
return v___x_3094_;
}
else
{
lean_object* v___x_3095_; 
v___x_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3095_, 0, v_pos_3090_);
lean_ctor_set(v___x_3095_, 1, v_acc_3080_);
return v___x_3095_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(lean_object* v_acc_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v_pos_3127_; uint32_t v_res_3128_; lean_object* v_fst_3131_; lean_object* v_snd_3132_; lean_object* v_pos_3134_; lean_object* v_snd_3135_; lean_object* v_err_3136_; lean_object* v___x_3140_; uint8_t v_decide_3141_; 
v_fst_3131_ = lean_ctor_get(v_a_3125_, 0);
v_snd_3132_ = lean_ctor_get(v_a_3125_, 1);
lean_inc(v_snd_3132_);
v___x_3140_ = lean_string_utf8_byte_size(v_fst_3131_);
v_decide_3141_ = lean_nat_dec_eq(v_snd_3132_, v___x_3140_);
if (v_decide_3141_ == 0)
{
uint32_t v_c_3142_; lean_object* v___x_3143_; lean_object* v_it_x27_3144_; uint32_t v___x_3163_; uint8_t v___x_3164_; 
v_c_3142_ = lean_string_utf8_get_fast(v_fst_3131_, v_snd_3132_);
v___x_3143_ = lean_string_utf8_next_fast(v_fst_3131_, v_snd_3132_);
lean_inc(v_fst_3131_);
v_it_x27_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3144_, 0, v_fst_3131_);
lean_ctor_set(v_it_x27_3144_, 1, v___x_3143_);
v___x_3163_ = 65;
v___x_3164_ = lean_uint32_dec_le(v___x_3163_, v_c_3142_);
if (v___x_3164_ == 0)
{
goto v___jp_3158_;
}
else
{
uint32_t v___x_3165_; uint8_t v___x_3166_; 
v___x_3165_ = 90;
v___x_3166_ = lean_uint32_dec_le(v_c_3142_, v___x_3165_);
if (v___x_3166_ == 0)
{
goto v___jp_3158_;
}
else
{
lean_dec(v_snd_3132_);
lean_dec_ref(v_a_3125_);
v_pos_3127_ = v_it_x27_3144_;
v_res_3128_ = v_c_3142_;
goto v___jp_3126_;
}
}
v___jp_3145_:
{
uint32_t v___x_3146_; uint8_t v___x_3147_; 
v___x_3146_ = 95;
v___x_3147_ = lean_uint32_dec_eq(v_c_3142_, v___x_3146_);
if (v___x_3147_ == 0)
{
uint32_t v___x_3148_; uint8_t v___x_3149_; 
v___x_3148_ = 45;
v___x_3149_ = lean_uint32_dec_eq(v_c_3142_, v___x_3148_);
if (v___x_3149_ == 0)
{
uint32_t v___x_3150_; uint8_t v___x_3151_; 
v___x_3150_ = 47;
v___x_3151_ = lean_uint32_dec_eq(v_c_3142_, v___x_3150_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; 
lean_dec_ref_known(v_it_x27_3144_, 2);
v___x_3152_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3132_);
v_pos_3134_ = v_a_3125_;
v_snd_3135_ = v_snd_3132_;
v_err_3136_ = v___x_3152_;
goto v___jp_3133_;
}
else
{
lean_dec(v_snd_3132_);
lean_dec_ref(v_a_3125_);
v_pos_3127_ = v_it_x27_3144_;
v_res_3128_ = v_c_3142_;
goto v___jp_3126_;
}
}
else
{
lean_dec(v_snd_3132_);
lean_dec_ref(v_a_3125_);
v_pos_3127_ = v_it_x27_3144_;
v_res_3128_ = v_c_3142_;
goto v___jp_3126_;
}
}
else
{
lean_dec(v_snd_3132_);
lean_dec_ref(v_a_3125_);
v_pos_3127_ = v_it_x27_3144_;
v_res_3128_ = v_c_3142_;
goto v___jp_3126_;
}
}
v___jp_3153_:
{
uint32_t v___x_3154_; uint8_t v___x_3155_; 
v___x_3154_ = 48;
v___x_3155_ = lean_uint32_dec_le(v___x_3154_, v_c_3142_);
if (v___x_3155_ == 0)
{
goto v___jp_3145_;
}
else
{
uint32_t v___x_3156_; uint8_t v___x_3157_; 
v___x_3156_ = 57;
v___x_3157_ = lean_uint32_dec_le(v_c_3142_, v___x_3156_);
if (v___x_3157_ == 0)
{
goto v___jp_3145_;
}
else
{
lean_dec(v_snd_3132_);
lean_dec_ref(v_a_3125_);
v_pos_3127_ = v_it_x27_3144_;
v_res_3128_ = v_c_3142_;
goto v___jp_3126_;
}
}
}
v___jp_3158_:
{
uint32_t v___x_3159_; uint8_t v___x_3160_; 
v___x_3159_ = 97;
v___x_3160_ = lean_uint32_dec_le(v___x_3159_, v_c_3142_);
if (v___x_3160_ == 0)
{
goto v___jp_3153_;
}
else
{
uint32_t v___x_3161_; uint8_t v___x_3162_; 
v___x_3161_ = 122;
v___x_3162_ = lean_uint32_dec_le(v_c_3142_, v___x_3161_);
if (v___x_3162_ == 0)
{
goto v___jp_3153_;
}
else
{
lean_dec(v_snd_3132_);
lean_dec_ref(v_a_3125_);
v_pos_3127_ = v_it_x27_3144_;
v_res_3128_ = v_c_3142_;
goto v___jp_3126_;
}
}
}
}
else
{
lean_object* v___x_3167_; 
v___x_3167_ = lean_box(0);
lean_inc(v_snd_3132_);
v_pos_3134_ = v_a_3125_;
v_snd_3135_ = v_snd_3132_;
v_err_3136_ = v___x_3167_;
goto v___jp_3133_;
}
v___jp_3126_:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3129_ = lean_string_push(v_acc_3124_, v_res_3128_);
v___x_3130_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(v___x_3129_, v_pos_3127_);
return v___x_3130_;
}
v___jp_3133_:
{
uint8_t v_decide_3137_; 
v_decide_3137_ = lean_nat_dec_eq(v_snd_3132_, v_snd_3135_);
lean_dec(v_snd_3135_);
lean_dec(v_snd_3132_);
if (v_decide_3137_ == 0)
{
lean_object* v___x_3138_; 
lean_dec_ref(v_acc_3124_);
lean_inc(v_err_3136_);
v___x_3138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3138_, 0, v_pos_3134_);
lean_ctor_set(v___x_3138_, 1, v_err_3136_);
return v___x_3138_;
}
else
{
lean_object* v___x_3139_; 
v___x_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3139_, 0, v_pos_3134_);
lean_ctor_set(v___x_3139_, 1, v_acc_3124_);
return v___x_3139_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(lean_object* v_a_3168_){
_start:
{
lean_object* v_fst_3169_; lean_object* v_snd_3170_; lean_object* v___x_3171_; uint8_t v_decide_3172_; 
v_fst_3169_ = lean_ctor_get(v_a_3168_, 0);
v_snd_3170_ = lean_ctor_get(v_a_3168_, 1);
v___x_3171_ = lean_string_utf8_byte_size(v_fst_3169_);
v_decide_3172_ = lean_nat_dec_eq(v_snd_3170_, v___x_3171_);
if (v_decide_3172_ == 0)
{
uint32_t v_c_3173_; lean_object* v___x_3174_; uint32_t v___x_3199_; uint8_t v___x_3200_; 
v_c_3173_ = lean_string_utf8_get_fast(v_fst_3169_, v_snd_3170_);
v___x_3174_ = lean_string_utf8_next_fast(v_fst_3169_, v_snd_3170_);
v___x_3199_ = 65;
v___x_3200_ = lean_uint32_dec_le(v___x_3199_, v_c_3173_);
if (v___x_3200_ == 0)
{
goto v___jp_3194_;
}
else
{
uint32_t v___x_3201_; uint8_t v___x_3202_; 
v___x_3201_ = 90;
v___x_3202_ = lean_uint32_dec_le(v_c_3173_, v___x_3201_);
if (v___x_3202_ == 0)
{
goto v___jp_3194_;
}
else
{
lean_inc(v_fst_3169_);
lean_dec_ref(v_a_3168_);
goto v___jp_3175_;
}
}
v___jp_3175_:
{
lean_object* v_it_x27_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v_it_x27_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3176_, 0, v_fst_3169_);
lean_ctor_set(v_it_x27_3176_, 1, v___x_3174_);
v___x_3177_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3178_ = lean_string_push(v___x_3177_, v_c_3173_);
v___x_3179_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(v___x_3178_, v_it_x27_3176_);
return v___x_3179_;
}
v___jp_3180_:
{
uint32_t v___x_3181_; uint8_t v___x_3182_; 
v___x_3181_ = 95;
v___x_3182_ = lean_uint32_dec_eq(v_c_3173_, v___x_3181_);
if (v___x_3182_ == 0)
{
uint32_t v___x_3183_; uint8_t v___x_3184_; 
v___x_3183_ = 45;
v___x_3184_ = lean_uint32_dec_eq(v_c_3173_, v___x_3183_);
if (v___x_3184_ == 0)
{
uint32_t v___x_3185_; uint8_t v___x_3186_; 
v___x_3185_ = 47;
v___x_3186_ = lean_uint32_dec_eq(v_c_3173_, v___x_3185_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3188_, 0, v_a_3168_);
lean_ctor_set(v___x_3188_, 1, v___x_3187_);
return v___x_3188_;
}
else
{
lean_inc(v_fst_3169_);
lean_dec_ref(v_a_3168_);
goto v___jp_3175_;
}
}
else
{
lean_inc(v_fst_3169_);
lean_dec_ref(v_a_3168_);
goto v___jp_3175_;
}
}
else
{
lean_inc(v_fst_3169_);
lean_dec_ref(v_a_3168_);
goto v___jp_3175_;
}
}
v___jp_3189_:
{
uint32_t v___x_3190_; uint8_t v___x_3191_; 
v___x_3190_ = 48;
v___x_3191_ = lean_uint32_dec_le(v___x_3190_, v_c_3173_);
if (v___x_3191_ == 0)
{
goto v___jp_3180_;
}
else
{
uint32_t v___x_3192_; uint8_t v___x_3193_; 
v___x_3192_ = 57;
v___x_3193_ = lean_uint32_dec_le(v_c_3173_, v___x_3192_);
if (v___x_3193_ == 0)
{
goto v___jp_3180_;
}
else
{
lean_inc(v_fst_3169_);
lean_dec_ref(v_a_3168_);
goto v___jp_3175_;
}
}
}
v___jp_3194_:
{
uint32_t v___x_3195_; uint8_t v___x_3196_; 
v___x_3195_ = 97;
v___x_3196_ = lean_uint32_dec_le(v___x_3195_, v_c_3173_);
if (v___x_3196_ == 0)
{
goto v___jp_3189_;
}
else
{
uint32_t v___x_3197_; uint8_t v___x_3198_; 
v___x_3197_ = 122;
v___x_3198_ = lean_uint32_dec_le(v_c_3173_, v___x_3197_);
if (v___x_3198_ == 0)
{
goto v___jp_3189_;
}
else
{
lean_inc(v_fst_3169_);
lean_dec_ref(v_a_3168_);
goto v___jp_3175_;
}
}
}
}
else
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3203_ = lean_box(0);
v___x_3204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3204_, 0, v_a_3168_);
lean_ctor_set(v___x_3204_, 1, v___x_3203_);
return v___x_3204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(lean_object* v_n_3207_, lean_object* v_m_3208_, lean_object* v_parser_3209_, lean_object* v_a_3210_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = lean_apply_1(v_parser_3209_, v_a_3210_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_pos_3212_; lean_object* v_res_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3233_; 
v_pos_3212_ = lean_ctor_get(v___x_3211_, 0);
v_res_3213_ = lean_ctor_get(v___x_3211_, 1);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3215_ = v___x_3211_;
v_isShared_3216_ = v_isSharedCheck_3233_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_res_3213_);
lean_inc(v_pos_3212_);
lean_dec(v___x_3211_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3233_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
uint8_t v___x_3229_; 
v___x_3229_ = lean_nat_dec_le(v_n_3207_, v_res_3213_);
if (v___x_3229_ == 0)
{
lean_dec(v_res_3213_);
goto v___jp_3217_;
}
else
{
uint8_t v___x_3230_; 
v___x_3230_ = lean_nat_dec_le(v_res_3213_, v_m_3208_);
if (v___x_3230_ == 0)
{
lean_dec(v_res_3213_);
goto v___jp_3217_;
}
else
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
lean_del_object(v___x_3215_);
lean_dec(v_m_3208_);
lean_dec(v_n_3207_);
v___x_3231_ = lean_nat_to_int(v_res_3213_);
v___x_3232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3232_, 0, v_pos_3212_);
lean_ctor_set(v___x_3232_, 1, v___x_3231_);
return v___x_3232_;
}
}
v___jp_3217_:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3227_; 
v___x_3218_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__0));
v___x_3219_ = l_Nat_reprFast(v_n_3207_);
v___x_3220_ = lean_string_append(v___x_3218_, v___x_3219_);
lean_dec_ref(v___x_3219_);
v___x_3221_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__1));
v___x_3222_ = lean_string_append(v___x_3220_, v___x_3221_);
v___x_3223_ = l_Nat_reprFast(v_m_3208_);
v___x_3224_ = lean_string_append(v___x_3222_, v___x_3223_);
lean_dec_ref(v___x_3223_);
v___x_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set_tag(v___x_3215_, 1);
lean_ctor_set(v___x_3215_, 1, v___x_3225_);
v___x_3227_ = v___x_3215_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_pos_3212_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v___x_3225_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
else
{
lean_object* v_pos_3234_; lean_object* v_err_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
lean_dec(v_m_3208_);
lean_dec(v_n_3207_);
v_pos_3234_ = lean_ctor_get(v___x_3211_, 0);
v_err_3235_ = lean_ctor_get(v___x_3211_, 1);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3211_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_err_3235_);
lean_inc(v_pos_3234_);
lean_dec(v___x_3211_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_pos_3234_);
lean_ctor_set(v_reuseFailAlloc_3241_, 1, v_err_3235_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(lean_object* v_a_3243_){
_start:
{
lean_object* v_fst_3247_; lean_object* v_snd_3248_; lean_object* v___x_3249_; uint8_t v_decide_3250_; 
v_fst_3247_ = lean_ctor_get(v_a_3243_, 0);
v_snd_3248_ = lean_ctor_get(v_a_3243_, 1);
v___x_3249_ = lean_string_utf8_byte_size(v_fst_3247_);
v_decide_3250_ = lean_nat_dec_eq(v_snd_3248_, v___x_3249_);
if (v_decide_3250_ == 0)
{
uint32_t v_c_3251_; uint32_t v___x_3252_; uint8_t v___x_3253_; 
v_c_3251_ = lean_string_utf8_get_fast(v_fst_3247_, v_snd_3248_);
v___x_3252_ = 48;
v___x_3253_ = lean_uint32_dec_le(v___x_3252_, v_c_3251_);
if (v___x_3253_ == 0)
{
goto v___jp_3244_;
}
else
{
uint32_t v___x_3254_; uint8_t v___x_3255_; 
v___x_3254_ = 57;
v___x_3255_ = lean_uint32_dec_le(v_c_3251_, v___x_3254_);
if (v___x_3255_ == 0)
{
goto v___jp_3244_;
}
else
{
lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3291_; 
lean_inc(v_snd_3248_);
lean_inc(v_fst_3247_);
v_isSharedCheck_3291_ = !lean_is_exclusive(v_a_3243_);
if (v_isSharedCheck_3291_ == 0)
{
lean_object* v_unused_3292_; lean_object* v_unused_3293_; 
v_unused_3292_ = lean_ctor_get(v_a_3243_, 1);
lean_dec(v_unused_3292_);
v_unused_3293_ = lean_ctor_get(v_a_3243_, 0);
lean_dec(v_unused_3293_);
v___x_3257_ = v_a_3243_;
v_isShared_3258_ = v_isSharedCheck_3291_;
goto v_resetjp_3256_;
}
else
{
lean_dec(v_a_3243_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3291_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3259_; lean_object* v_pos_3261_; lean_object* v_snd_3262_; lean_object* v_err_3263_; lean_object* v_it_x27_3271_; 
v___x_3259_ = lean_string_utf8_next_fast(v_fst_3247_, v_snd_3248_);
lean_dec(v_snd_3248_);
lean_inc(v_fst_3247_);
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 1, v___x_3259_);
v_it_x27_3271_ = v___x_3257_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_fst_3247_);
lean_ctor_set(v_reuseFailAlloc_3290_, 1, v___x_3259_);
v_it_x27_3271_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3270_;
}
v___jp_3260_:
{
uint8_t v_decide_3264_; 
v_decide_3264_ = lean_nat_dec_eq(v___x_3259_, v_snd_3262_);
lean_dec(v_snd_3262_);
if (v_decide_3264_ == 0)
{
lean_object* v___x_3265_; 
lean_inc(v_err_3263_);
v___x_3265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3265_, 0, v_pos_3261_);
lean_ctor_set(v___x_3265_, 1, v_err_3263_);
return v___x_3265_;
}
else
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3266_ = lean_uint32_to_nat(v_c_3251_);
v___x_3267_ = lean_unsigned_to_nat(48u);
v___x_3268_ = lean_nat_sub(v___x_3266_, v___x_3267_);
lean_dec(v___x_3266_);
v___x_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3269_, 0, v_pos_3261_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
return v___x_3269_;
}
}
v_reusejp_3270_:
{
uint8_t v_decide_3274_; 
v_decide_3274_ = lean_nat_dec_eq(v___x_3259_, v___x_3249_);
if (v_decide_3274_ == 0)
{
uint32_t v___x_3275_; uint8_t v___x_3276_; 
v___x_3275_ = lean_string_utf8_get_fast(v_fst_3247_, v___x_3259_);
v___x_3276_ = lean_uint32_dec_le(v___x_3252_, v___x_3275_);
if (v___x_3276_ == 0)
{
lean_dec(v_fst_3247_);
goto v___jp_3272_;
}
else
{
uint8_t v___x_3277_; 
v___x_3277_ = lean_uint32_dec_le(v___x_3275_, v___x_3254_);
if (v___x_3277_ == 0)
{
lean_dec(v_fst_3247_);
goto v___jp_3272_;
}
else
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
lean_dec_ref(v_it_x27_3271_);
v___x_3278_ = lean_unsigned_to_nat(48u);
v___x_3279_ = lean_string_utf8_next_fast(v_fst_3247_, v___x_3259_);
v___x_3280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3280_, 0, v_fst_3247_);
lean_ctor_set(v___x_3280_, 1, v___x_3279_);
v___x_3281_ = lean_uint32_to_nat(v_c_3251_);
v___x_3282_ = lean_nat_sub(v___x_3281_, v___x_3278_);
lean_dec(v___x_3281_);
v___x_3283_ = lean_unsigned_to_nat(10u);
v___x_3284_ = lean_nat_mul(v___x_3282_, v___x_3283_);
lean_dec(v___x_3282_);
v___x_3285_ = lean_uint32_to_nat(v___x_3275_);
v___x_3286_ = lean_nat_sub(v___x_3285_, v___x_3278_);
lean_dec(v___x_3285_);
v___x_3287_ = lean_nat_add(v___x_3284_, v___x_3286_);
lean_dec(v___x_3286_);
lean_dec(v___x_3284_);
v___x_3288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3280_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
return v___x_3288_;
}
}
}
else
{
lean_object* v___x_3289_; 
lean_dec(v_fst_3247_);
v___x_3289_ = lean_box(0);
v_pos_3261_ = v_it_x27_3271_;
v_snd_3262_ = v___x_3259_;
v_err_3263_ = v___x_3289_;
goto v___jp_3260_;
}
v___jp_3272_:
{
lean_object* v___x_3273_; 
v___x_3273_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v_pos_3261_ = v_it_x27_3271_;
v_snd_3262_ = v___x_3259_;
v_err_3263_ = v___x_3273_;
goto v___jp_3260_;
}
}
}
}
}
}
else
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3294_ = lean_box(0);
v___x_3295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3295_, 0, v_a_3243_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
return v___x_3295_;
}
v___jp_3244_:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3245_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3246_, 0, v_a_3243_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
return v___x_3246_;
}
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1(void){
_start:
{
uint32_t v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = 58;
v___x_3300_ = lean_box_uint32(v___x_3299_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(uint8_t v_withColon_3301_, lean_object* v___y_3302_){
_start:
{
if (v_withColon_3301_ == 0)
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1;
v___x_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___y_3302_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
return v___x_3304_;
}
else
{
lean_object* v_fst_3305_; lean_object* v_snd_3306_; lean_object* v___x_3307_; uint8_t v_decide_3308_; 
v_fst_3305_ = lean_ctor_get(v___y_3302_, 0);
v_snd_3306_ = lean_ctor_get(v___y_3302_, 1);
v___x_3307_ = lean_string_utf8_byte_size(v_fst_3305_);
v_decide_3308_ = lean_nat_dec_eq(v_snd_3306_, v___x_3307_);
if (v_decide_3308_ == 0)
{
uint32_t v___x_3309_; uint32_t v_c_3310_; uint8_t v___x_3311_; 
v___x_3309_ = 58;
v_c_3310_ = lean_string_utf8_get_fast(v_fst_3305_, v_snd_3306_);
v___x_3311_ = lean_uint32_dec_eq(v_c_3310_, v___x_3309_);
if (v___x_3311_ == 0)
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__1));
v___x_3313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___y_3302_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
return v___x_3313_;
}
else
{
lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3323_; 
lean_inc(v_snd_3306_);
lean_inc(v_fst_3305_);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___y_3302_);
if (v_isSharedCheck_3323_ == 0)
{
lean_object* v_unused_3324_; lean_object* v_unused_3325_; 
v_unused_3324_ = lean_ctor_get(v___y_3302_, 1);
lean_dec(v_unused_3324_);
v_unused_3325_ = lean_ctor_get(v___y_3302_, 0);
lean_dec(v_unused_3325_);
v___x_3315_ = v___y_3302_;
v_isShared_3316_ = v_isSharedCheck_3323_;
goto v_resetjp_3314_;
}
else
{
lean_dec(v___y_3302_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3323_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3317_; lean_object* v_it_x27_3319_; 
v___x_3317_ = lean_string_utf8_next_fast(v_fst_3305_, v_snd_3306_);
lean_dec(v_snd_3306_);
if (v_isShared_3316_ == 0)
{
lean_ctor_set(v___x_3315_, 1, v___x_3317_);
v_it_x27_3319_ = v___x_3315_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_fst_3305_);
lean_ctor_set(v_reuseFailAlloc_3322_, 1, v___x_3317_);
v_it_x27_3319_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3320_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1;
v___x_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3321_, 0, v_it_x27_3319_);
lean_ctor_set(v___x_3321_, 1, v___x_3320_);
return v___x_3321_;
}
}
}
}
else
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3326_ = lean_box(0);
v___x_3327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___y_3302_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
return v___x_3327_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed(lean_object* v_withColon_3328_, lean_object* v___y_3329_){
_start:
{
uint8_t v_withColon_boxed_3330_; lean_object* v_res_3331_; 
v_withColon_boxed_3330_ = lean_unbox(v_withColon_3328_);
v_res_3331_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(v_withColon_boxed_3330_, v___y_3329_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1(lean_object* v_a_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3334_ = lean_nat_to_int(v_a_3332_);
v___x_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___y_3333_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(lean_object* v___y_3336_, lean_object* v___f_3337_, lean_object* v_n_3338_, uint8_t v_reason_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v_pos_3342_; lean_object* v_err_3343_; 
switch(v_reason_3339_)
{
case 0:
{
lean_object* v___x_3359_; 
v___x_3359_ = lean_apply_1(v___y_3336_, v___y_3340_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_pos_3360_; lean_object* v___x_3361_; 
v_pos_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_pos_3360_);
lean_dec_ref_known(v___x_3359_, 2);
v___x_3361_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3360_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_pos_3362_; lean_object* v_res_3363_; lean_object* v___x_3364_; 
v_pos_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_pos_3362_);
v_res_3363_ = lean_ctor_get(v___x_3361_, 1);
lean_inc(v_res_3363_);
lean_dec_ref_known(v___x_3361_, 2);
v___x_3364_ = lean_apply_2(v___f_3337_, v_res_3363_, v_pos_3362_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_pos_3365_; lean_object* v_res_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3374_; 
v_pos_3365_ = lean_ctor_get(v___x_3364_, 0);
v_res_3366_ = lean_ctor_get(v___x_3364_, 1);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3368_ = v___x_3364_;
v_isShared_3369_ = v_isSharedCheck_3374_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_res_3366_);
lean_inc(v_pos_3365_);
lean_dec(v___x_3364_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3374_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3370_; lean_object* v___x_3372_; 
v___x_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3370_, 0, v_res_3366_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 1, v___x_3370_);
v___x_3372_ = v___x_3368_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_pos_3365_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v___x_3370_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
else
{
lean_object* v_pos_3375_; lean_object* v_err_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
v_pos_3375_ = lean_ctor_get(v___x_3364_, 0);
v_err_3376_ = lean_ctor_get(v___x_3364_, 1);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3364_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_err_3376_);
lean_inc(v_pos_3375_);
lean_dec(v___x_3364_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_pos_3375_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_err_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
else
{
lean_object* v_pos_3384_; lean_object* v_err_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
lean_dec_ref(v___f_3337_);
v_pos_3384_ = lean_ctor_get(v___x_3361_, 0);
v_err_3385_ = lean_ctor_get(v___x_3361_, 1);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3361_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_err_3385_);
lean_inc(v_pos_3384_);
lean_dec(v___x_3361_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_pos_3384_);
lean_ctor_set(v_reuseFailAlloc_3391_, 1, v_err_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
else
{
lean_object* v_pos_3393_; lean_object* v_err_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_dec_ref(v___f_3337_);
v_pos_3393_ = lean_ctor_get(v___x_3359_, 0);
v_err_3394_ = lean_ctor_get(v___x_3359_, 1);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3359_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_err_3394_);
lean_inc(v_pos_3393_);
lean_dec(v___x_3359_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_pos_3393_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v_err_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
case 1:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_dec_ref(v___f_3337_);
lean_dec_ref(v___y_3336_);
v___x_3402_ = lean_box(0);
v___x_3403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3403_, 0, v___y_3340_);
lean_ctor_set(v___x_3403_, 1, v___x_3402_);
return v___x_3403_;
}
default: 
{
lean_object* v___x_3404_; 
lean_inc_ref(v___y_3340_);
v___x_3404_ = lean_apply_1(v___y_3336_, v___y_3340_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_pos_3405_; lean_object* v___x_3406_; 
v_pos_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_pos_3405_);
lean_dec_ref_known(v___x_3404_, 2);
v___x_3406_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3405_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_pos_3407_; lean_object* v_res_3408_; lean_object* v___x_3409_; 
v_pos_3407_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_pos_3407_);
v_res_3408_ = lean_ctor_get(v___x_3406_, 1);
lean_inc(v_res_3408_);
lean_dec_ref_known(v___x_3406_, 2);
v___x_3409_ = lean_apply_2(v___f_3337_, v_res_3408_, v_pos_3407_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_pos_3410_; lean_object* v_res_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3419_; 
lean_dec_ref(v___y_3340_);
v_pos_3410_ = lean_ctor_get(v___x_3409_, 0);
v_res_3411_ = lean_ctor_get(v___x_3409_, 1);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3413_ = v___x_3409_;
v_isShared_3414_ = v_isSharedCheck_3419_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_res_3411_);
lean_inc(v_pos_3410_);
lean_dec(v___x_3409_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3419_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3415_, 0, v_res_3411_);
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 1, v___x_3415_);
v___x_3417_ = v___x_3413_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_pos_3410_);
lean_ctor_set(v_reuseFailAlloc_3418_, 1, v___x_3415_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
else
{
lean_object* v_pos_3420_; lean_object* v_err_3421_; 
v_pos_3420_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_pos_3420_);
v_err_3421_ = lean_ctor_get(v___x_3409_, 1);
lean_inc(v_err_3421_);
lean_dec_ref_known(v___x_3409_, 2);
v_pos_3342_ = v_pos_3420_;
v_err_3343_ = v_err_3421_;
goto v___jp_3341_;
}
}
else
{
lean_object* v_pos_3422_; lean_object* v_err_3423_; 
lean_dec_ref(v___f_3337_);
v_pos_3422_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_pos_3422_);
v_err_3423_ = lean_ctor_get(v___x_3406_, 1);
lean_inc(v_err_3423_);
lean_dec_ref_known(v___x_3406_, 2);
v_pos_3342_ = v_pos_3422_;
v_err_3343_ = v_err_3423_;
goto v___jp_3341_;
}
}
else
{
lean_object* v_pos_3424_; lean_object* v_err_3425_; 
lean_dec_ref(v___f_3337_);
v_pos_3424_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_pos_3424_);
v_err_3425_ = lean_ctor_get(v___x_3404_, 1);
lean_inc(v_err_3425_);
lean_dec_ref_known(v___x_3404_, 2);
v_pos_3342_ = v_pos_3424_;
v_err_3343_ = v_err_3425_;
goto v___jp_3341_;
}
}
}
v___jp_3341_:
{
lean_object* v_snd_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3357_; 
v_snd_3344_ = lean_ctor_get(v___y_3340_, 1);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___y_3340_);
if (v_isSharedCheck_3357_ == 0)
{
lean_object* v_unused_3358_; 
v_unused_3358_ = lean_ctor_get(v___y_3340_, 0);
lean_dec(v_unused_3358_);
v___x_3346_ = v___y_3340_;
v_isShared_3347_ = v_isSharedCheck_3357_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_snd_3344_);
lean_dec(v___y_3340_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3357_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v_snd_3348_; uint8_t v_decide_3349_; 
v_snd_3348_ = lean_ctor_get(v_pos_3342_, 1);
v_decide_3349_ = lean_nat_dec_eq(v_snd_3344_, v_snd_3348_);
lean_dec(v_snd_3344_);
if (v_decide_3349_ == 0)
{
lean_object* v___x_3351_; 
if (v_isShared_3347_ == 0)
{
lean_ctor_set_tag(v___x_3346_, 1);
lean_ctor_set(v___x_3346_, 1, v_err_3343_);
lean_ctor_set(v___x_3346_, 0, v_pos_3342_);
v___x_3351_ = v___x_3346_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_pos_3342_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v_err_3343_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
else
{
lean_object* v___x_3353_; lean_object* v___x_3355_; 
lean_dec(v_err_3343_);
v___x_3353_ = lean_box(0);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 1, v___x_3353_);
lean_ctor_set(v___x_3346_, 0, v_pos_3342_);
v___x_3355_ = v___x_3346_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_pos_3342_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v___x_3353_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2___boxed(lean_object* v___y_3426_, lean_object* v___f_3427_, lean_object* v_n_3428_, lean_object* v_reason_3429_, lean_object* v___y_3430_){
_start:
{
uint8_t v_reason_boxed_3431_; lean_object* v_res_3432_; 
v_reason_boxed_3431_ = lean_unbox(v_reason_3429_);
v_res_3432_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3426_, v___f_3427_, v_n_3428_, v_reason_boxed_3431_, v___y_3430_);
lean_dec_ref(v_n_3428_);
return v_res_3432_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2(void){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = lean_unsigned_to_nat(3600u);
v___x_3436_ = lean_nat_to_int(v___x_3435_);
return v___x_3436_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4(void){
_start:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = lean_unsigned_to_nat(1u);
v___x_3439_ = l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(v___x_3438_);
return v___x_3439_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5(void){
_start:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3440_ = lean_unsigned_to_nat(59u);
v___x_3441_ = lean_nat_to_int(v___x_3440_);
return v___x_3441_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8(void){
_start:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3444_ = lean_unsigned_to_nat(23u);
v___x_3445_ = lean_nat_to_int(v___x_3444_);
return v___x_3445_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9(void){
_start:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3446_ = lean_unsigned_to_nat(60u);
v___x_3447_ = l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(v___x_3446_);
return v___x_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(uint8_t v_withMinutes_3455_, uint8_t v_withSeconds_3456_, uint8_t v_withColon_3457_, lean_object* v_a_3458_){
_start:
{
lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v_fst_3500_; lean_object* v_snd_3501_; lean_object* v___x_3502_; lean_object* v___y_3503_; lean_object* v___f_3504_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v_pos_3551_; lean_object* v_res_3552_; lean_object* v_pos_3610_; lean_object* v_fst_3611_; lean_object* v_snd_3612_; lean_object* v_err_3613_; lean_object* v___x_3628_; uint8_t v_decide_3629_; 
v_fst_3500_ = lean_ctor_get(v_a_3458_, 0);
lean_inc(v_fst_3500_);
v_snd_3501_ = lean_ctor_get(v_a_3458_, 1);
lean_inc(v_snd_3501_);
v___x_3502_ = lean_box(v_withColon_3457_);
v___y_3503_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed), 2, 1);
lean_closure_set(v___y_3503_, 0, v___x_3502_);
v___f_3504_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3));
v___x_3628_ = lean_string_utf8_byte_size(v_fst_3500_);
v_decide_3629_ = lean_nat_dec_eq(v_snd_3501_, v___x_3628_);
if (v_decide_3629_ == 0)
{
uint32_t v___x_3630_; uint32_t v_c_3631_; uint8_t v___x_3632_; 
v___x_3630_ = 43;
v_c_3631_ = lean_string_utf8_get_fast(v_fst_3500_, v_snd_3501_);
v___x_3632_ = lean_uint32_dec_eq(v_c_3631_, v___x_3630_);
if (v___x_3632_ == 0)
{
lean_object* v___x_3633_; 
v___x_3633_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14));
lean_inc(v_snd_3501_);
v_pos_3610_ = v_a_3458_;
v_fst_3611_ = v_fst_3500_;
v_snd_3612_ = v_snd_3501_;
v_err_3613_ = v___x_3633_;
goto v___jp_3609_;
}
else
{
lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3642_; 
v_isSharedCheck_3642_ = !lean_is_exclusive(v_a_3458_);
if (v_isSharedCheck_3642_ == 0)
{
lean_object* v_unused_3643_; lean_object* v_unused_3644_; 
v_unused_3643_ = lean_ctor_get(v_a_3458_, 1);
lean_dec(v_unused_3643_);
v_unused_3644_ = lean_ctor_get(v_a_3458_, 0);
lean_dec(v_unused_3644_);
v___x_3635_ = v_a_3458_;
v_isShared_3636_ = v_isSharedCheck_3642_;
goto v_resetjp_3634_;
}
else
{
lean_dec(v_a_3458_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3642_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3637_; lean_object* v_it_x27_3639_; 
v___x_3637_ = lean_string_utf8_next_fast(v_fst_3500_, v_snd_3501_);
lean_dec(v_snd_3501_);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 1, v___x_3637_);
v_it_x27_3639_ = v___x_3635_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_fst_3500_);
lean_ctor_set(v_reuseFailAlloc_3641_, 1, v___x_3637_);
v_it_x27_3639_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
lean_object* v___x_3640_; 
v___x_3640_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v_pos_3551_ = v_it_x27_3639_;
v_res_3552_ = v___x_3640_;
goto v___jp_3550_;
}
}
}
}
else
{
lean_object* v___x_3645_; 
v___x_3645_ = lean_box(0);
lean_inc(v_snd_3501_);
v_pos_3610_ = v_a_3458_;
v_fst_3611_ = v_fst_3500_;
v_snd_3612_ = v_snd_3501_;
v_err_3613_ = v___x_3645_;
goto v___jp_3609_;
}
v___jp_3459_:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3462_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0));
v___x_3463_ = l_Int_repr(v___y_3461_);
lean_dec(v___y_3461_);
v___x_3464_ = lean_string_append(v___x_3462_, v___x_3463_);
lean_dec_ref(v___x_3463_);
v___x_3465_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__1));
v___x_3466_ = lean_string_append(v___x_3464_, v___x_3465_);
v___x_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
v___x_3468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___y_3460_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
return v___x_3468_;
}
v___jp_3469_:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3474_ = lean_int_add(v___y_3472_, v___y_3473_);
lean_dec(v___y_3473_);
lean_dec(v___y_3472_);
v___x_3475_ = lean_int_mul(v___x_3474_, v___y_3470_);
lean_dec(v___x_3474_);
v___x_3476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___y_3471_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
return v___x_3476_;
}
v___jp_3477_:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3485_ = lean_nat_to_int(v___y_3479_);
v___x_3486_ = lean_int_mul(v___y_3484_, v___x_3485_);
lean_dec(v___x_3485_);
lean_dec(v___y_3484_);
v___x_3487_ = lean_int_add(v___y_3483_, v___x_3486_);
lean_dec(v___x_3486_);
lean_dec(v___y_3483_);
if (lean_obj_tag(v___y_3482_) == 0)
{
lean_inc(v___y_3480_);
v___y_3470_ = v___y_3478_;
v___y_3471_ = v___y_3481_;
v___y_3472_ = v___x_3487_;
v___y_3473_ = v___y_3480_;
goto v___jp_3469_;
}
else
{
lean_object* v_val_3488_; 
v_val_3488_ = lean_ctor_get(v___y_3482_, 0);
lean_inc(v_val_3488_);
lean_dec_ref_known(v___y_3482_, 1);
v___y_3470_ = v___y_3478_;
v___y_3471_ = v___y_3481_;
v___y_3472_ = v___x_3487_;
v___y_3473_ = v_val_3488_;
goto v___jp_3469_;
}
}
v___jp_3489_:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3497_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2);
v___x_3498_ = lean_int_mul(v___y_3492_, v___x_3497_);
lean_dec(v___y_3492_);
if (lean_obj_tag(v___y_3495_) == 0)
{
lean_inc(v___y_3493_);
v___y_3478_ = v___y_3490_;
v___y_3479_ = v___y_3491_;
v___y_3480_ = v___y_3493_;
v___y_3481_ = v___y_3496_;
v___y_3482_ = v___y_3494_;
v___y_3483_ = v___x_3498_;
v___y_3484_ = v___y_3493_;
goto v___jp_3477_;
}
else
{
lean_object* v_val_3499_; 
v_val_3499_ = lean_ctor_get(v___y_3495_, 0);
lean_inc(v_val_3499_);
lean_dec_ref_known(v___y_3495_, 1);
v___y_3478_ = v___y_3490_;
v___y_3479_ = v___y_3491_;
v___y_3480_ = v___y_3493_;
v___y_3481_ = v___y_3496_;
v___y_3482_ = v___y_3494_;
v___y_3483_ = v___x_3498_;
v___y_3484_ = v_val_3499_;
goto v___jp_3477_;
}
}
v___jp_3505_:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3512_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4);
v___x_3513_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3503_, v___f_3504_, v___x_3512_, v_withSeconds_3456_, v___y_3511_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_res_3514_; 
v_res_3514_ = lean_ctor_get(v___x_3513_, 1);
lean_inc(v_res_3514_);
if (lean_obj_tag(v_res_3514_) == 1)
{
lean_object* v_pos_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3538_; 
v_pos_3515_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3538_ == 0)
{
lean_object* v_unused_3539_; 
v_unused_3539_ = lean_ctor_get(v___x_3513_, 1);
lean_dec(v_unused_3539_);
v___x_3517_ = v___x_3513_;
v_isShared_3518_ = v_isSharedCheck_3538_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_pos_3515_);
lean_dec(v___x_3513_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3538_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v_val_3519_; lean_object* v___x_3520_; uint8_t v___x_3521_; 
v_val_3519_ = lean_ctor_get(v_res_3514_, 0);
v___x_3520_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5);
v___x_3521_ = lean_int_dec_lt(v___x_3520_, v_val_3519_);
if (v___x_3521_ == 0)
{
lean_del_object(v___x_3517_);
v___y_3490_ = v___y_3506_;
v___y_3491_ = v___y_3507_;
v___y_3492_ = v___y_3508_;
v___y_3493_ = v___y_3509_;
v___y_3494_ = v_res_3514_;
v___y_3495_ = v___y_3510_;
v___y_3496_ = v_pos_3515_;
goto v___jp_3489_;
}
else
{
lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3536_; 
lean_inc(v_val_3519_);
lean_dec(v___y_3510_);
lean_dec(v___y_3508_);
lean_dec(v___y_3507_);
v_isSharedCheck_3536_ = !lean_is_exclusive(v_res_3514_);
if (v_isSharedCheck_3536_ == 0)
{
lean_object* v_unused_3537_; 
v_unused_3537_ = lean_ctor_get(v_res_3514_, 0);
lean_dec(v_unused_3537_);
v___x_3523_ = v_res_3514_;
v_isShared_3524_ = v_isSharedCheck_3536_;
goto v_resetjp_3522_;
}
else
{
lean_dec(v_res_3514_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3536_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3525_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6));
v___x_3526_ = l_Int_repr(v_val_3519_);
lean_dec(v_val_3519_);
v___x_3527_ = lean_string_append(v___x_3525_, v___x_3526_);
lean_dec_ref(v___x_3526_);
v___x_3528_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__7));
v___x_3529_ = lean_string_append(v___x_3527_, v___x_3528_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3529_);
v___x_3531_ = v___x_3523_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
lean_object* v___x_3533_; 
if (v_isShared_3518_ == 0)
{
lean_ctor_set_tag(v___x_3517_, 1);
lean_ctor_set(v___x_3517_, 1, v___x_3531_);
v___x_3533_ = v___x_3517_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_pos_3515_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v___x_3531_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3540_; 
v_pos_3540_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_pos_3540_);
lean_dec_ref_known(v___x_3513_, 2);
v___y_3490_ = v___y_3506_;
v___y_3491_ = v___y_3507_;
v___y_3492_ = v___y_3508_;
v___y_3493_ = v___y_3509_;
v___y_3494_ = v_res_3514_;
v___y_3495_ = v___y_3510_;
v___y_3496_ = v_pos_3540_;
goto v___jp_3489_;
}
}
else
{
lean_object* v_pos_3541_; lean_object* v_err_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
lean_dec(v___y_3510_);
lean_dec(v___y_3508_);
lean_dec(v___y_3507_);
v_pos_3541_ = lean_ctor_get(v___x_3513_, 0);
v_err_3542_ = lean_ctor_get(v___x_3513_, 1);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3544_ = v___x_3513_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_err_3542_);
lean_inc(v_pos_3541_);
lean_dec(v___x_3513_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3547_; 
if (v_isShared_3545_ == 0)
{
v___x_3547_ = v___x_3544_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_pos_3541_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_err_3542_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
}
v___jp_3550_:
{
lean_object* v___x_3553_; 
v___x_3553_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3551_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_pos_3554_; lean_object* v_res_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; 
v_pos_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_pos_3554_);
v_res_3555_ = lean_ctor_get(v___x_3553_, 1);
lean_inc(v_res_3555_);
lean_dec_ref_known(v___x_3553_, 2);
v___x_3556_ = lean_nat_to_int(v_res_3555_);
v___x_3557_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_3558_ = lean_int_dec_lt(v___x_3556_, v___x_3557_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3559_; uint8_t v___x_3560_; 
v___x_3559_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8);
v___x_3560_ = lean_int_dec_lt(v___x_3559_, v___x_3556_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3561_ = lean_unsigned_to_nat(60u);
v___x_3562_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9);
lean_inc_ref(v___y_3503_);
v___x_3563_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3503_, v___f_3504_, v___x_3562_, v_withMinutes_3455_, v_pos_3554_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_res_3564_; 
v_res_3564_ = lean_ctor_get(v___x_3563_, 1);
lean_inc(v_res_3564_);
if (lean_obj_tag(v_res_3564_) == 1)
{
lean_object* v_pos_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3588_; 
v_pos_3565_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3588_ == 0)
{
lean_object* v_unused_3589_; 
v_unused_3589_ = lean_ctor_get(v___x_3563_, 1);
lean_dec(v_unused_3589_);
v___x_3567_ = v___x_3563_;
v_isShared_3568_ = v_isSharedCheck_3588_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_pos_3565_);
lean_dec(v___x_3563_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3588_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v_val_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; 
v_val_3569_ = lean_ctor_get(v_res_3564_, 0);
v___x_3570_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5);
v___x_3571_ = lean_int_dec_lt(v___x_3570_, v_val_3569_);
if (v___x_3571_ == 0)
{
lean_del_object(v___x_3567_);
v___y_3506_ = v_res_3552_;
v___y_3507_ = v___x_3561_;
v___y_3508_ = v___x_3556_;
v___y_3509_ = v___x_3557_;
v___y_3510_ = v_res_3564_;
v___y_3511_ = v_pos_3565_;
goto v___jp_3505_;
}
else
{
lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3586_; 
lean_inc(v_val_3569_);
lean_dec(v___x_3556_);
lean_dec_ref(v___y_3503_);
v_isSharedCheck_3586_ = !lean_is_exclusive(v_res_3564_);
if (v_isSharedCheck_3586_ == 0)
{
lean_object* v_unused_3587_; 
v_unused_3587_ = lean_ctor_get(v_res_3564_, 0);
lean_dec(v_unused_3587_);
v___x_3573_ = v_res_3564_;
v_isShared_3574_ = v_isSharedCheck_3586_;
goto v_resetjp_3572_;
}
else
{
lean_dec(v_res_3564_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3586_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3581_; 
v___x_3575_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10));
v___x_3576_ = l_Int_repr(v_val_3569_);
lean_dec(v_val_3569_);
v___x_3577_ = lean_string_append(v___x_3575_, v___x_3576_);
lean_dec_ref(v___x_3576_);
v___x_3578_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__7));
v___x_3579_ = lean_string_append(v___x_3577_, v___x_3578_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v___x_3579_);
v___x_3581_ = v___x_3573_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3579_);
v___x_3581_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
lean_object* v___x_3583_; 
if (v_isShared_3568_ == 0)
{
lean_ctor_set_tag(v___x_3567_, 1);
lean_ctor_set(v___x_3567_, 1, v___x_3581_);
v___x_3583_ = v___x_3567_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_pos_3565_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v___x_3581_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3590_; 
v_pos_3590_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_pos_3590_);
lean_dec_ref_known(v___x_3563_, 2);
v___y_3506_ = v_res_3552_;
v___y_3507_ = v___x_3561_;
v___y_3508_ = v___x_3556_;
v___y_3509_ = v___x_3557_;
v___y_3510_ = v_res_3564_;
v___y_3511_ = v_pos_3590_;
goto v___jp_3505_;
}
}
else
{
lean_object* v_pos_3591_; lean_object* v_err_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
lean_dec(v___x_3556_);
lean_dec_ref(v___y_3503_);
v_pos_3591_ = lean_ctor_get(v___x_3563_, 0);
v_err_3592_ = lean_ctor_get(v___x_3563_, 1);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3563_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_err_3592_);
lean_inc(v_pos_3591_);
lean_dec(v___x_3563_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_pos_3591_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v_err_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
else
{
lean_dec_ref(v___y_3503_);
v___y_3460_ = v_pos_3554_;
v___y_3461_ = v___x_3556_;
goto v___jp_3459_;
}
}
else
{
lean_dec_ref(v___y_3503_);
v___y_3460_ = v_pos_3554_;
v___y_3461_ = v___x_3556_;
goto v___jp_3459_;
}
}
else
{
lean_object* v_pos_3600_; lean_object* v_err_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
lean_dec_ref(v___y_3503_);
v_pos_3600_ = lean_ctor_get(v___x_3553_, 0);
v_err_3601_ = lean_ctor_get(v___x_3553_, 1);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3553_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_err_3601_);
lean_inc(v_pos_3600_);
lean_dec(v___x_3553_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_pos_3600_);
lean_ctor_set(v_reuseFailAlloc_3607_, 1, v_err_3601_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
v___jp_3609_:
{
uint8_t v_decide_3614_; 
v_decide_3614_ = lean_nat_dec_eq(v_snd_3501_, v_snd_3612_);
lean_dec(v_snd_3501_);
if (v_decide_3614_ == 0)
{
lean_object* v___x_3615_; 
lean_dec(v_snd_3612_);
lean_dec(v_fst_3611_);
lean_dec_ref(v___y_3503_);
lean_inc(v_err_3613_);
v___x_3615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3615_, 0, v_pos_3610_);
lean_ctor_set(v___x_3615_, 1, v_err_3613_);
return v___x_3615_;
}
else
{
lean_object* v___x_3616_; uint8_t v_decide_3617_; 
v___x_3616_ = lean_string_utf8_byte_size(v_fst_3611_);
v_decide_3617_ = lean_nat_dec_eq(v_snd_3612_, v___x_3616_);
if (v_decide_3617_ == 0)
{
uint32_t v___x_3618_; uint32_t v_c_3619_; uint8_t v___x_3620_; 
v___x_3618_ = 45;
v_c_3619_ = lean_string_utf8_get_fast(v_fst_3611_, v_snd_3612_);
v___x_3620_ = lean_uint32_dec_eq(v_c_3619_, v___x_3618_);
if (v___x_3620_ == 0)
{
lean_object* v___x_3621_; lean_object* v___x_3622_; 
lean_dec(v_snd_3612_);
lean_dec(v_fst_3611_);
lean_dec_ref(v___y_3503_);
v___x_3621_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12));
v___x_3622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3622_, 0, v_pos_3610_);
lean_ctor_set(v___x_3622_, 1, v___x_3621_);
return v___x_3622_;
}
else
{
lean_object* v___x_3623_; lean_object* v_it_x27_3624_; lean_object* v___x_3625_; 
lean_dec_ref(v_pos_3610_);
v___x_3623_ = lean_string_utf8_next_fast(v_fst_3611_, v_snd_3612_);
lean_dec(v_snd_3612_);
v_it_x27_3624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3624_, 0, v_fst_3611_);
lean_ctor_set(v_it_x27_3624_, 1, v___x_3623_);
v___x_3625_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v_pos_3551_ = v_it_x27_3624_;
v_res_3552_ = v___x_3625_;
goto v___jp_3550_;
}
}
else
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
lean_dec(v_snd_3612_);
lean_dec(v_fst_3611_);
lean_dec_ref(v___y_3503_);
v___x_3626_ = lean_box(0);
v___x_3627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3627_, 0, v_pos_3610_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
return v___x_3627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___boxed(lean_object* v_withMinutes_3646_, lean_object* v_withSeconds_3647_, lean_object* v_withColon_3648_, lean_object* v_a_3649_){
_start:
{
uint8_t v_withMinutes_boxed_3650_; uint8_t v_withSeconds_boxed_3651_; uint8_t v_withColon_boxed_3652_; lean_object* v_res_3653_; 
v_withMinutes_boxed_3650_ = lean_unbox(v_withMinutes_3646_);
v_withSeconds_boxed_3651_ = lean_unbox(v_withSeconds_3647_);
v_withColon_boxed_3652_ = lean_unbox(v_withColon_3648_);
v_res_3653_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v_withMinutes_boxed_3650_, v_withSeconds_boxed_3651_, v_withColon_boxed_3652_, v_a_3649_);
return v_res_3653_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1(void){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3656_ = lean_unsigned_to_nat(2000u);
v___x_3657_ = lean_nat_to_int(v___x_3656_);
return v___x_3657_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5(void){
_start:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3663_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3664_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_3665_ = lean_int_sub(v___x_3664_, v___x_3663_);
return v___x_3665_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6(void){
_start:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v_range_3668_; 
v___x_3666_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3667_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5);
v_range_3668_ = lean_int_add(v___x_3667_, v___x_3666_);
return v_range_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(lean_object* v_config_3671_, lean_object* v_x_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v___y_3675_; lean_object* v___y_3680_; lean_object* v___y_3685_; lean_object* v___y_3712_; 
switch(lean_obj_tag(v_x_3672_))
{
case 0:
{
uint8_t v_presentation_3717_; 
v_presentation_3717_ = lean_ctor_get_uint8(v_x_3672_, 0);
lean_dec_ref_known(v_x_3672_, 0);
switch(v_presentation_3717_)
{
case 1:
{
lean_object* v_dateformat_3718_; lean_object* v_symbols_3719_; lean_object* v___x_3720_; 
v_dateformat_3718_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_3718_);
lean_dec_ref(v_config_3671_);
v_symbols_3719_ = lean_ctor_get(v_dateformat_3718_, 1);
lean_inc_ref(v_symbols_3719_);
lean_dec_ref(v_dateformat_3718_);
v___x_3720_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraLong(v_symbols_3719_, v_a_3673_);
return v___x_3720_;
}
case 2:
{
lean_object* v_dateformat_3721_; lean_object* v_symbols_3722_; lean_object* v___x_3723_; 
v_dateformat_3721_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_3721_);
lean_dec_ref(v_config_3671_);
v_symbols_3722_ = lean_ctor_get(v_dateformat_3721_, 1);
lean_inc_ref(v_symbols_3722_);
lean_dec_ref(v_dateformat_3721_);
v___x_3723_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraNarrow(v_symbols_3722_, v_a_3673_);
return v___x_3723_;
}
default: 
{
lean_object* v_dateformat_3724_; lean_object* v_symbols_3725_; lean_object* v___x_3726_; 
v_dateformat_3724_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_3724_);
lean_dec_ref(v_config_3671_);
v_symbols_3725_ = lean_ctor_get(v_dateformat_3724_, 1);
lean_inc_ref(v_symbols_3725_);
lean_dec_ref(v_dateformat_3724_);
v___x_3726_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraShort(v_symbols_3725_, v_a_3673_);
return v___x_3726_;
}
}
}
case 1:
{
lean_object* v_presentation_3727_; 
lean_dec_ref(v_config_3671_);
v_presentation_3727_ = lean_ctor_get(v_x_3672_, 0);
lean_inc(v_presentation_3727_);
lean_dec_ref_known(v_x_3672_, 1);
switch(lean_obj_tag(v_presentation_3727_))
{
case 0:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0));
v___x_3729_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3728_, v_a_3673_);
return v___x_3729_;
}
case 1:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3730_ = lean_unsigned_to_nat(2u);
v___x_3731_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3730_, v_a_3673_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_pos_3732_; lean_object* v_res_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3743_; 
v_pos_3732_ = lean_ctor_get(v___x_3731_, 0);
v_res_3733_ = lean_ctor_get(v___x_3731_, 1);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3735_ = v___x_3731_;
v_isShared_3736_ = v_isSharedCheck_3743_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_res_3733_);
lean_inc(v_pos_3732_);
lean_dec(v___x_3731_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3743_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3741_; 
v___x_3737_ = lean_nat_to_int(v_res_3733_);
v___x_3738_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_3739_ = lean_int_add(v___x_3738_, v___x_3737_);
lean_dec(v___x_3737_);
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 1, v___x_3739_);
v___x_3741_ = v___x_3735_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_pos_3732_);
lean_ctor_set(v_reuseFailAlloc_3742_, 1, v___x_3739_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
else
{
lean_object* v_pos_3744_; lean_object* v_err_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
v_pos_3744_ = lean_ctor_get(v___x_3731_, 0);
v_err_3745_ = lean_ctor_get(v___x_3731_, 1);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3731_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_err_3745_);
lean_inc(v_pos_3744_);
lean_dec(v___x_3731_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_pos_3744_);
lean_ctor_set(v_reuseFailAlloc_3751_, 1, v_err_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
case 2:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3753_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2));
v___x_3754_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3753_, v_a_3673_);
return v___x_3754_;
}
default: 
{
lean_object* v_num_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
v_num_3755_ = lean_ctor_get(v_presentation_3727_, 0);
lean_inc(v_num_3755_);
lean_dec_ref_known(v_presentation_3727_, 1);
v___x_3756_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed), 2, 1);
lean_closure_set(v___x_3756_, 0, v_num_3755_);
v___x_3757_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3756_, v_a_3673_);
return v___x_3757_;
}
}
}
case 2:
{
lean_object* v_presentation_3758_; 
lean_dec_ref(v_config_3671_);
v_presentation_3758_ = lean_ctor_get(v_x_3672_, 0);
lean_inc(v_presentation_3758_);
lean_dec_ref_known(v_x_3672_, 1);
switch(lean_obj_tag(v_presentation_3758_))
{
case 0:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3759_ = lean_unsigned_to_nat(1u);
v___x_3760_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v___x_3759_, v_a_3673_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_pos_3761_; lean_object* v_res_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3770_; 
v_pos_3761_ = lean_ctor_get(v___x_3760_, 0);
v_res_3762_ = lean_ctor_get(v___x_3760_, 1);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3764_ = v___x_3760_;
v_isShared_3765_ = v_isSharedCheck_3770_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_res_3762_);
lean_inc(v_pos_3761_);
lean_dec(v___x_3760_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3770_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3766_; lean_object* v___x_3768_; 
v___x_3766_ = lean_nat_to_int(v_res_3762_);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 1, v___x_3766_);
v___x_3768_ = v___x_3764_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_pos_3761_);
lean_ctor_set(v_reuseFailAlloc_3769_, 1, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
else
{
lean_object* v_pos_3771_; lean_object* v_err_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
v_pos_3771_ = lean_ctor_get(v___x_3760_, 0);
v_err_3772_ = lean_ctor_get(v___x_3760_, 1);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v___x_3760_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_err_3772_);
lean_inc(v_pos_3771_);
lean_dec(v___x_3760_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_pos_3771_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_err_3772_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
case 1:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3780_ = lean_unsigned_to_nat(2u);
v___x_3781_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3780_, v_a_3673_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_pos_3782_; lean_object* v_res_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3793_; 
v_pos_3782_ = lean_ctor_get(v___x_3781_, 0);
v_res_3783_ = lean_ctor_get(v___x_3781_, 1);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3785_ = v___x_3781_;
v_isShared_3786_ = v_isSharedCheck_3793_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_res_3783_);
lean_inc(v_pos_3782_);
lean_dec(v___x_3781_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3793_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3791_; 
v___x_3787_ = lean_nat_to_int(v_res_3783_);
v___x_3788_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_3789_ = lean_int_add(v___x_3788_, v___x_3787_);
lean_dec(v___x_3787_);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 1, v___x_3789_);
v___x_3791_ = v___x_3785_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_pos_3782_);
lean_ctor_set(v_reuseFailAlloc_3792_, 1, v___x_3789_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
else
{
lean_object* v_pos_3794_; lean_object* v_err_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3802_; 
v_pos_3794_ = lean_ctor_get(v___x_3781_, 0);
v_err_3795_ = lean_ctor_get(v___x_3781_, 1);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3797_ = v___x_3781_;
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_err_3795_);
lean_inc(v_pos_3794_);
lean_dec(v___x_3781_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3800_; 
if (v_isShared_3798_ == 0)
{
v___x_3800_ = v___x_3797_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_pos_3794_);
lean_ctor_set(v_reuseFailAlloc_3801_, 1, v_err_3795_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
case 2:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3803_ = lean_unsigned_to_nat(4u);
v___x_3804_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3803_, v_a_3673_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_pos_3805_; lean_object* v_res_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3814_; 
v_pos_3805_ = lean_ctor_get(v___x_3804_, 0);
v_res_3806_ = lean_ctor_get(v___x_3804_, 1);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3808_ = v___x_3804_;
v_isShared_3809_ = v_isSharedCheck_3814_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_res_3806_);
lean_inc(v_pos_3805_);
lean_dec(v___x_3804_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3814_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3810_; lean_object* v___x_3812_; 
v___x_3810_ = lean_nat_to_int(v_res_3806_);
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 1, v___x_3810_);
v___x_3812_ = v___x_3808_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_pos_3805_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v___x_3810_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
else
{
lean_object* v_pos_3815_; lean_object* v_err_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
v_pos_3815_ = lean_ctor_get(v___x_3804_, 0);
v_err_3816_ = lean_ctor_get(v___x_3804_, 1);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3804_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_err_3816_);
lean_inc(v_pos_3815_);
lean_dec(v___x_3804_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_pos_3815_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v_err_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
default: 
{
lean_object* v_num_3824_; lean_object* v___x_3825_; 
v_num_3824_ = lean_ctor_get(v_presentation_3758_, 0);
lean_inc(v_num_3824_);
lean_dec_ref_known(v_presentation_3758_, 1);
v___x_3825_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_num_3824_, v_a_3673_);
lean_dec(v_num_3824_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_pos_3826_; lean_object* v_res_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3835_; 
v_pos_3826_ = lean_ctor_get(v___x_3825_, 0);
v_res_3827_ = lean_ctor_get(v___x_3825_, 1);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3829_ = v___x_3825_;
v_isShared_3830_ = v_isSharedCheck_3835_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_res_3827_);
lean_inc(v_pos_3826_);
lean_dec(v___x_3825_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3835_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3831_; lean_object* v___x_3833_; 
v___x_3831_ = lean_nat_to_int(v_res_3827_);
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 1, v___x_3831_);
v___x_3833_ = v___x_3829_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_pos_3826_);
lean_ctor_set(v_reuseFailAlloc_3834_, 1, v___x_3831_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
else
{
lean_object* v_pos_3836_; lean_object* v_err_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
v_pos_3836_ = lean_ctor_get(v___x_3825_, 0);
v_err_3837_ = lean_ctor_get(v___x_3825_, 1);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3825_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_err_3837_);
lean_inc(v_pos_3836_);
lean_dec(v___x_3825_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_pos_3836_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v_err_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
}
}
case 3:
{
lean_object* v_presentation_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
lean_dec_ref(v_config_3671_);
v_presentation_3845_ = lean_ctor_get(v_x_3672_, 0);
lean_inc(v_presentation_3845_);
lean_dec_ref_known(v_x_3672_, 1);
v___x_3846_ = lean_unsigned_to_nat(1u);
v___x_3847_ = lean_unsigned_to_nat(366u);
v___x_3848_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3848_, 0, v_presentation_3845_);
v___x_3849_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3846_, v___x_3847_, v___x_3848_, v_a_3673_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_pos_3850_; lean_object* v_res_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3861_; 
v_pos_3850_ = lean_ctor_get(v___x_3849_, 0);
v_res_3851_ = lean_ctor_get(v___x_3849_, 1);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3853_ = v___x_3849_;
v_isShared_3854_ = v_isSharedCheck_3861_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_res_3851_);
lean_inc(v_pos_3850_);
lean_dec(v___x_3849_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3861_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
uint8_t v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3859_; 
v___x_3855_ = 1;
v___x_3856_ = lean_box(v___x_3855_);
v___x_3857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
lean_ctor_set(v___x_3857_, 1, v_res_3851_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 1, v___x_3857_);
v___x_3859_ = v___x_3853_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_pos_3850_);
lean_ctor_set(v_reuseFailAlloc_3860_, 1, v___x_3857_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
else
{
lean_object* v_pos_3862_; lean_object* v_err_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
v_pos_3862_ = lean_ctor_get(v___x_3849_, 0);
v_err_3863_ = lean_ctor_get(v___x_3849_, 1);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3865_ = v___x_3849_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_err_3863_);
lean_inc(v_pos_3862_);
lean_dec(v___x_3849_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_pos_3862_);
lean_ctor_set(v_reuseFailAlloc_3869_, 1, v_err_3863_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
case 4:
{
lean_object* v_presentation_3871_; 
v_presentation_3871_ = lean_ctor_get(v_x_3672_, 0);
lean_inc_ref(v_presentation_3871_);
lean_dec_ref_known(v_x_3672_, 1);
if (lean_obj_tag(v_presentation_3871_) == 0)
{
lean_object* v_val_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
lean_dec_ref(v_config_3671_);
v_val_3872_ = lean_ctor_get(v_presentation_3871_, 0);
lean_inc(v_val_3872_);
lean_dec_ref_known(v_presentation_3871_, 1);
v___x_3873_ = lean_unsigned_to_nat(1u);
v___x_3874_ = lean_unsigned_to_nat(12u);
v___x_3875_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3875_, 0, v_val_3872_);
v___x_3876_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3873_, v___x_3874_, v___x_3875_, v_a_3673_);
return v___x_3876_;
}
else
{
lean_object* v_val_3877_; uint8_t v___x_3878_; 
v_val_3877_ = lean_ctor_get(v_presentation_3871_, 0);
lean_inc(v_val_3877_);
lean_dec_ref_known(v_presentation_3871_, 1);
v___x_3878_ = lean_unbox(v_val_3877_);
lean_dec(v_val_3877_);
switch(v___x_3878_)
{
case 1:
{
lean_object* v_dateformat_3879_; lean_object* v_symbols_3880_; lean_object* v___x_3881_; 
v_dateformat_3879_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_3879_);
lean_dec_ref(v_config_3671_);
v_symbols_3880_ = lean_ctor_get(v_dateformat_3879_, 1);
lean_inc_ref(v_symbols_3880_);
lean_dec_ref(v_dateformat_3879_);
v___x_3881_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(v_symbols_3880_, v_a_3673_);
return v___x_3881_;
}
case 2:
{
lean_object* v_dateformat_3882_; lean_object* v_symbols_3883_; lean_object* v___x_3884_; 
v_dateformat_3882_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_3882_);
lean_dec_ref(v_config_3671_);
v_symbols_3883_ = lean_ctor_get(v_dateformat_3882_, 1);
lean_inc_ref(v_symbols_3883_);
lean_dec_ref(v_dateformat_3882_);
v___x_3884_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(v_symbols_3883_, v_a_3673_);
return v___x_3884_;
}
default: 
{
lean_object* v_dateformat_3885_; lean_object* v_symbols_3886_; lean_object* v___x_3887_; 
v_dateformat_3885_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_3885_);
lean_dec_ref(v_config_3671_);
v_symbols_3886_ = lean_ctor_get(v_dateformat_3885_, 1);
lean_inc_ref(v_symbols_3886_);
lean_dec_ref(v_dateformat_3885_);
v___x_3887_ = l_Std_Time_parseMonthShort(v_symbols_3886_, v_a_3673_);
return v___x_3887_;
}
}
}
}
case 5:
{
lean_object* v_presentation_3888_; 
v_presentation_3888_ = lean_ctor_get(v_x_3672_, 0);
lean_inc_ref(v_presentation_3888_);
lean_dec_ref_known(v_x_3672_, 1);
if (lean_obj_tag(v_presentation_3888_) == 0)
{
lean_object* v_val_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
lean_dec_ref(v_config_3671_);
v_val_3889_ = lean_ctor_get(v_presentation_3888_, 0);
lean_inc(v_val_3889_);
lean_dec_ref_known(v_presentation_3888_, 1);
v___x_3890_ = lean_unsigned_to_nat(1u);
v___x_3891_ = lean_unsigned_to_nat(12u);
v___x_3892_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3892_, 0, v_val_3889_);
v___x_3893_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3890_, v___x_3891_, v___x_3892_, v_a_3673_);
return v___x_3893_;
}
else
{
lean_object* v_val_3894_; uint8_t v___x_3895_; 
v_val_3894_ = lean_ctor_get(v_presentation_3888_, 0);
lean_inc(v_val_3894_);
lean_dec_ref_known(v_presentation_3888_, 1);
v___x_3895_ = lean_unbox(v_val_3894_);
lean_dec(v_val_3894_);
switch(v___x_3895_)
{
case 1:
{
lean_object* v_dateformat_3896_; lean_object* v_symbols_3897_; lean_object* v___x_3898_; 
v_dateformat_3896_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_3896_);
lean_dec_ref(v_config_3671_);
v_symbols_3897_ = lean_ctor_get(v_dateformat_3896_, 1);
lean_inc_ref(v_symbols_3897_);
lean_dec_ref(v_dateformat_3896_);
v___x_3898_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(v_symbols_3897_, v_a_3673_);
return v___x_3898_;
}
case 2:
{
lean_object* v_dateformat_3899_; lean_object* v_symbols_3900_; lean_object* v___x_3901_; 
v_dateformat_3899_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_3899_);
lean_dec_ref(v_config_3671_);
v_symbols_3900_ = lean_ctor_get(v_dateformat_3899_, 1);
lean_inc_ref(v_symbols_3900_);
lean_dec_ref(v_dateformat_3899_);
v___x_3901_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(v_symbols_3900_, v_a_3673_);
return v___x_3901_;
}
default: 
{
lean_object* v_dateformat_3902_; lean_object* v_symbols_3903_; lean_object* v___x_3904_; 
v_dateformat_3902_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_3902_);
lean_dec_ref(v_config_3671_);
v_symbols_3903_ = lean_ctor_get(v_dateformat_3902_, 1);
lean_inc_ref(v_symbols_3903_);
lean_dec_ref(v_dateformat_3902_);
v___x_3904_ = l_Std_Time_parseMonthShort(v_symbols_3903_, v_a_3673_);
return v___x_3904_;
}
}
}
}
case 6:
{
lean_object* v_presentation_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
lean_dec_ref(v_config_3671_);
v_presentation_3905_ = lean_ctor_get(v_x_3672_, 0);
lean_inc(v_presentation_3905_);
lean_dec_ref_known(v_x_3672_, 1);
v___x_3906_ = lean_unsigned_to_nat(1u);
v___x_3907_ = lean_unsigned_to_nat(31u);
v___x_3908_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3908_, 0, v_presentation_3905_);
v___x_3909_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3906_, v___x_3907_, v___x_3908_, v_a_3673_);
return v___x_3909_;
}
case 7:
{
lean_object* v_presentation_3910_; 
v_presentation_3910_ = lean_ctor_get(v_x_3672_, 0);
lean_inc_ref(v_presentation_3910_);
lean_dec_ref_known(v_x_3672_, 1);
if (lean_obj_tag(v_presentation_3910_) == 0)
{
lean_object* v_val_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
lean_dec_ref(v_config_3671_);
v_val_3911_ = lean_ctor_get(v_presentation_3910_, 0);
lean_inc(v_val_3911_);
lean_dec_ref_known(v_presentation_3910_, 1);
v___x_3912_ = lean_unsigned_to_nat(1u);
v___x_3913_ = lean_unsigned_to_nat(4u);
v___x_3914_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3914_, 0, v_val_3911_);
v___x_3915_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3912_, v___x_3913_, v___x_3914_, v_a_3673_);
return v___x_3915_;
}
else
{
lean_object* v_val_3916_; uint8_t v___x_3917_; 
v_val_3916_ = lean_ctor_get(v_presentation_3910_, 0);
lean_inc(v_val_3916_);
lean_dec_ref_known(v_presentation_3910_, 1);
v___x_3917_ = lean_unbox(v_val_3916_);
lean_dec(v_val_3916_);
switch(v___x_3917_)
{
case 0:
{
lean_object* v_dateformat_3918_; lean_object* v_symbols_3919_; lean_object* v___x_3920_; 
v_dateformat_3918_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_3918_);
lean_dec_ref(v_config_3671_);
v_symbols_3919_ = lean_ctor_get(v_dateformat_3918_, 1);
lean_inc_ref(v_symbols_3919_);
lean_dec_ref(v_dateformat_3918_);
v___x_3920_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(v_symbols_3919_, v_a_3673_);
return v___x_3920_;
}
case 1:
{
lean_object* v_dateformat_3921_; lean_object* v_symbols_3922_; lean_object* v___x_3923_; 
v_dateformat_3921_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_3921_);
lean_dec_ref(v_config_3671_);
v_symbols_3922_ = lean_ctor_get(v_dateformat_3921_, 1);
lean_inc_ref(v_symbols_3922_);
lean_dec_ref(v_dateformat_3921_);
v___x_3923_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(v_symbols_3922_, v_a_3673_);
return v___x_3923_;
}
default: 
{
v___y_3680_ = v_a_3673_;
goto v___jp_3679_;
}
}
}
}
case 8:
{
lean_object* v_presentation_3924_; 
v_presentation_3924_ = lean_ctor_get(v_x_3672_, 0);
lean_inc_ref(v_presentation_3924_);
lean_dec_ref_known(v_x_3672_, 1);
if (lean_obj_tag(v_presentation_3924_) == 0)
{
lean_object* v_val_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
lean_dec_ref(v_config_3671_);
v_val_3925_ = lean_ctor_get(v_presentation_3924_, 0);
lean_inc(v_val_3925_);
lean_dec_ref_known(v_presentation_3924_, 1);
v___x_3926_ = lean_unsigned_to_nat(1u);
v___x_3927_ = lean_unsigned_to_nat(4u);
v___x_3928_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3928_, 0, v_val_3925_);
v___x_3929_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3926_, v___x_3927_, v___x_3928_, v_a_3673_);
return v___x_3929_;
}
else
{
lean_object* v_val_3930_; uint8_t v___x_3931_; 
v_val_3930_ = lean_ctor_get(v_presentation_3924_, 0);
lean_inc(v_val_3930_);
lean_dec_ref_known(v_presentation_3924_, 1);
v___x_3931_ = lean_unbox(v_val_3930_);
lean_dec(v_val_3930_);
switch(v___x_3931_)
{
case 0:
{
lean_object* v_dateformat_3932_; lean_object* v_symbols_3933_; lean_object* v___x_3934_; 
v_dateformat_3932_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_3932_);
lean_dec_ref(v_config_3671_);
v_symbols_3933_ = lean_ctor_get(v_dateformat_3932_, 1);
lean_inc_ref(v_symbols_3933_);
lean_dec_ref(v_dateformat_3932_);
v___x_3934_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(v_symbols_3933_, v_a_3673_);
return v___x_3934_;
}
case 1:
{
lean_object* v_dateformat_3935_; lean_object* v_symbols_3936_; lean_object* v___x_3937_; 
v_dateformat_3935_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_3935_);
lean_dec_ref(v_config_3671_);
v_symbols_3936_ = lean_ctor_get(v_dateformat_3935_, 1);
lean_inc_ref(v_symbols_3936_);
lean_dec_ref(v_dateformat_3935_);
v___x_3937_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(v_symbols_3936_, v_a_3673_);
return v___x_3937_;
}
default: 
{
v___y_3675_ = v_a_3673_;
goto v___jp_3674_;
}
}
}
}
case 9:
{
lean_object* v_presentation_3938_; 
lean_dec_ref(v_config_3671_);
v_presentation_3938_ = lean_ctor_get(v_x_3672_, 0);
lean_inc(v_presentation_3938_);
lean_dec_ref_known(v_x_3672_, 1);
switch(lean_obj_tag(v_presentation_3938_))
{
case 0:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3939_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0));
v___x_3940_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3939_, v_a_3673_);
return v___x_3940_;
}
case 1:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3941_ = lean_unsigned_to_nat(2u);
v___x_3942_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3941_, v_a_3673_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_pos_3943_; lean_object* v_res_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3954_; 
v_pos_3943_ = lean_ctor_get(v___x_3942_, 0);
v_res_3944_ = lean_ctor_get(v___x_3942_, 1);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3946_ = v___x_3942_;
v_isShared_3947_ = v_isSharedCheck_3954_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_res_3944_);
lean_inc(v_pos_3943_);
lean_dec(v___x_3942_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3954_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3952_; 
v___x_3948_ = lean_nat_to_int(v_res_3944_);
v___x_3949_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_3950_ = lean_int_add(v___x_3949_, v___x_3948_);
lean_dec(v___x_3948_);
if (v_isShared_3947_ == 0)
{
lean_ctor_set(v___x_3946_, 1, v___x_3950_);
v___x_3952_ = v___x_3946_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_pos_3943_);
lean_ctor_set(v_reuseFailAlloc_3953_, 1, v___x_3950_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
else
{
lean_object* v_pos_3955_; lean_object* v_err_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
v_pos_3955_ = lean_ctor_get(v___x_3942_, 0);
v_err_3956_ = lean_ctor_get(v___x_3942_, 1);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3942_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_err_3956_);
lean_inc(v_pos_3955_);
lean_dec(v___x_3942_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_pos_3955_);
lean_ctor_set(v_reuseFailAlloc_3962_, 1, v_err_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
case 2:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3964_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2));
v___x_3965_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3964_, v_a_3673_);
return v___x_3965_;
}
default: 
{
lean_object* v_num_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v_num_3966_ = lean_ctor_get(v_presentation_3938_, 0);
lean_inc(v_num_3966_);
lean_dec_ref_known(v_presentation_3938_, 1);
v___x_3967_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed), 2, 1);
lean_closure_set(v___x_3967_, 0, v_num_3966_);
v___x_3968_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3967_, v_a_3673_);
return v___x_3968_;
}
}
}
case 10:
{
lean_object* v_presentation_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
lean_dec_ref(v_config_3671_);
v_presentation_3969_ = lean_ctor_get(v_x_3672_, 0);
lean_inc(v_presentation_3969_);
lean_dec_ref_known(v_x_3672_, 1);
v___x_3970_ = lean_unsigned_to_nat(1u);
v___x_3971_ = lean_unsigned_to_nat(53u);
v___x_3972_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3972_, 0, v_presentation_3969_);
v___x_3973_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3970_, v___x_3971_, v___x_3972_, v_a_3673_);
return v___x_3973_;
}
case 11:
{
lean_object* v_presentation_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
lean_dec_ref(v_config_3671_);
v_presentation_3974_ = lean_ctor_get(v_x_3672_, 0);
lean_inc(v_presentation_3974_);
lean_dec_ref_known(v_x_3672_, 1);
v___x_3975_ = lean_unsigned_to_nat(1u);
v___x_3976_ = lean_unsigned_to_nat(6u);
v___x_3977_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3977_, 0, v_presentation_3974_);
v___x_3978_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3975_, v___x_3976_, v___x_3977_, v_a_3673_);
return v___x_3978_;
}
case 12:
{
uint8_t v_presentation_3979_; 
v_presentation_3979_ = lean_ctor_get_uint8(v_x_3672_, 0);
lean_dec_ref_known(v_x_3672_, 0);
switch(v_presentation_3979_)
{
case 1:
{
lean_object* v_dateformat_3980_; lean_object* v_symbols_3981_; lean_object* v___x_3982_; 
v_dateformat_3980_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_3980_);
lean_dec_ref(v_config_3671_);
v_symbols_3981_ = lean_ctor_get(v_dateformat_3980_, 1);
lean_inc_ref(v_symbols_3981_);
lean_dec_ref(v_dateformat_3980_);
v___x_3982_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_3981_, v_a_3673_);
return v___x_3982_;
}
case 2:
{
lean_object* v_dateformat_3983_; lean_object* v_symbols_3984_; lean_object* v___x_3985_; 
v_dateformat_3983_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_3983_);
lean_dec_ref(v_config_3671_);
v_symbols_3984_ = lean_ctor_get(v_dateformat_3983_, 1);
lean_inc_ref(v_symbols_3984_);
lean_dec_ref(v_dateformat_3983_);
v___x_3985_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_3984_, v_a_3673_);
return v___x_3985_;
}
default: 
{
lean_object* v_dateformat_3986_; lean_object* v_symbols_3987_; lean_object* v___x_3988_; 
v_dateformat_3986_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_3986_);
lean_dec_ref(v_config_3671_);
v_symbols_3987_ = lean_ctor_get(v_dateformat_3986_, 1);
lean_inc_ref(v_symbols_3987_);
lean_dec_ref(v_dateformat_3986_);
v___x_3988_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_3987_, v_a_3673_);
return v___x_3988_;
}
}
}
case 13:
{
lean_object* v_presentation_3989_; 
v_presentation_3989_ = lean_ctor_get(v_x_3672_, 0);
lean_inc_ref(v_presentation_3989_);
lean_dec_ref_known(v_x_3672_, 1);
if (lean_obj_tag(v_presentation_3989_) == 0)
{
lean_object* v_val_3990_; lean_object* v___x_3991_; 
v_val_3990_ = lean_ctor_get(v_presentation_3989_, 0);
lean_inc(v_val_3990_);
lean_dec_ref_known(v_presentation_3989_, 1);
v___x_3991_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_val_3990_, v_a_3673_);
lean_dec(v_val_3990_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_object* v_pos_3992_; lean_object* v_res_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4026_; 
v_pos_3992_ = lean_ctor_get(v___x_3991_, 0);
v_res_3993_ = lean_ctor_get(v___x_3991_, 1);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_4026_ == 0)
{
v___x_3995_ = v___x_3991_;
v_isShared_3996_ = v_isSharedCheck_4026_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_res_3993_);
lean_inc(v_pos_3992_);
lean_dec(v___x_3991_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4026_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_4002_; uint8_t v___x_4003_; 
v___x_4002_ = lean_unsigned_to_nat(1u);
v___x_4003_ = lean_nat_dec_le(v___x_4002_, v_res_3993_);
if (v___x_4003_ == 0)
{
lean_dec(v_res_3993_);
lean_dec_ref(v_config_3671_);
goto v___jp_3997_;
}
else
{
lean_object* v___x_4004_; uint8_t v___x_4005_; 
v___x_4004_ = lean_unsigned_to_nat(7u);
v___x_4005_ = lean_nat_dec_le(v_res_3993_, v___x_4004_);
if (v___x_4005_ == 0)
{
lean_dec(v_res_3993_);
lean_dec_ref(v_config_3671_);
goto v___jp_3997_;
}
else
{
lean_object* v_dateformat_4006_; uint8_t v_firstDayOfWeek_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v_range_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; uint8_t v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
lean_del_object(v___x_3995_);
v_dateformat_4006_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_4006_);
lean_dec_ref(v_config_3671_);
v_firstDayOfWeek_4007_ = lean_ctor_get_uint8(v_dateformat_4006_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_4006_);
v___x_4008_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_4007_);
v___x_4009_ = lean_nat_to_int(v_res_3993_);
v___x_4010_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_4011_ = lean_int_sub(v___x_4009_, v___x_4010_);
lean_dec(v___x_4009_);
v___x_4012_ = lean_int_add(v___x_4011_, v___x_4008_);
lean_dec(v___x_4008_);
lean_dec(v___x_4011_);
v___x_4013_ = lean_int_sub(v___x_4012_, v___x_4010_);
lean_dec(v___x_4012_);
v___x_4014_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_4015_ = lean_int_emod(v___x_4013_, v___x_4014_);
lean_dec(v___x_4013_);
v___x_4016_ = lean_int_add(v___x_4015_, v___x_4010_);
lean_dec(v___x_4015_);
v_range_4017_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6);
v___x_4018_ = lean_int_sub(v___x_4016_, v___x_4010_);
lean_dec(v___x_4016_);
v___x_4019_ = lean_int_emod(v___x_4018_, v_range_4017_);
lean_dec(v___x_4018_);
v___x_4020_ = lean_int_add(v___x_4019_, v_range_4017_);
lean_dec(v___x_4019_);
v___x_4021_ = lean_int_emod(v___x_4020_, v_range_4017_);
lean_dec(v___x_4020_);
v___x_4022_ = lean_int_add(v___x_4021_, v___x_4010_);
lean_dec(v___x_4021_);
v___x_4023_ = l_Std_Time_Weekday_ofOrdinal(v___x_4022_);
lean_dec(v___x_4022_);
v___x_4024_ = lean_box(v___x_4023_);
v___x_4025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4025_, 0, v_pos_3992_);
lean_ctor_set(v___x_4025_, 1, v___x_4024_);
return v___x_4025_;
}
}
v___jp_3997_:
{
lean_object* v___x_3998_; lean_object* v___x_4000_; 
v___x_3998_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4));
if (v_isShared_3996_ == 0)
{
lean_ctor_set_tag(v___x_3995_, 1);
lean_ctor_set(v___x_3995_, 1, v___x_3998_);
v___x_4000_ = v___x_3995_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_pos_3992_);
lean_ctor_set(v_reuseFailAlloc_4001_, 1, v___x_3998_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
}
else
{
lean_object* v_pos_4027_; lean_object* v_err_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
lean_dec_ref(v_config_3671_);
v_pos_4027_ = lean_ctor_get(v___x_3991_, 0);
v_err_4028_ = lean_ctor_get(v___x_3991_, 1);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_3991_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_err_4028_);
lean_inc(v_pos_4027_);
lean_dec(v___x_3991_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_pos_4027_);
lean_ctor_set(v_reuseFailAlloc_4034_, 1, v_err_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
else
{
lean_object* v_val_4036_; uint8_t v___x_4037_; 
v_val_4036_ = lean_ctor_get(v_presentation_3989_, 0);
lean_inc(v_val_4036_);
lean_dec_ref_known(v_presentation_3989_, 1);
v___x_4037_ = lean_unbox(v_val_4036_);
lean_dec(v_val_4036_);
switch(v___x_4037_)
{
case 0:
{
lean_object* v_dateformat_4038_; lean_object* v_symbols_4039_; lean_object* v___x_4040_; 
v_dateformat_4038_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_4038_);
lean_dec_ref(v_config_3671_);
v_symbols_4039_ = lean_ctor_get(v_dateformat_4038_, 1);
lean_inc_ref(v_symbols_4039_);
lean_dec_ref(v_dateformat_4038_);
v___x_4040_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4039_, v_a_3673_);
return v___x_4040_;
}
case 1:
{
lean_object* v_dateformat_4041_; lean_object* v_symbols_4042_; lean_object* v___x_4043_; 
v_dateformat_4041_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_4041_);
lean_dec_ref(v_config_3671_);
v_symbols_4042_ = lean_ctor_get(v_dateformat_4041_, 1);
lean_inc_ref(v_symbols_4042_);
lean_dec_ref(v_dateformat_4041_);
v___x_4043_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4042_, v_a_3673_);
return v___x_4043_;
}
case 2:
{
lean_object* v_dateformat_4044_; lean_object* v_symbols_4045_; lean_object* v___x_4046_; 
v_dateformat_4044_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_4044_);
lean_dec_ref(v_config_3671_);
v_symbols_4045_ = lean_ctor_get(v_dateformat_4044_, 1);
lean_inc_ref(v_symbols_4045_);
lean_dec_ref(v_dateformat_4044_);
v___x_4046_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4045_, v_a_3673_);
return v___x_4046_;
}
default: 
{
lean_object* v_dateformat_4047_; lean_object* v_symbols_4048_; lean_object* v___x_4049_; 
v_dateformat_4047_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_4047_);
lean_dec_ref(v_config_3671_);
v_symbols_4048_ = lean_ctor_get(v_dateformat_4047_, 1);
lean_inc_ref(v_symbols_4048_);
lean_dec_ref(v_dateformat_4047_);
v___x_4049_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(v_symbols_4048_, v_a_3673_);
return v___x_4049_;
}
}
}
}
case 14:
{
lean_object* v_presentation_4050_; 
v_presentation_4050_ = lean_ctor_get(v_x_3672_, 0);
lean_inc_ref(v_presentation_4050_);
lean_dec_ref_known(v_x_3672_, 1);
if (lean_obj_tag(v_presentation_4050_) == 0)
{
lean_object* v_val_4051_; lean_object* v___x_4052_; 
v_val_4051_ = lean_ctor_get(v_presentation_4050_, 0);
lean_inc(v_val_4051_);
lean_dec_ref_known(v_presentation_4050_, 1);
v___x_4052_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_val_4051_, v_a_3673_);
lean_dec(v_val_4051_);
if (lean_obj_tag(v___x_4052_) == 0)
{
lean_object* v_pos_4053_; lean_object* v_res_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4087_; 
v_pos_4053_ = lean_ctor_get(v___x_4052_, 0);
v_res_4054_ = lean_ctor_get(v___x_4052_, 1);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4056_ = v___x_4052_;
v_isShared_4057_ = v_isSharedCheck_4087_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_res_4054_);
lean_inc(v_pos_4053_);
lean_dec(v___x_4052_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4087_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4063_; uint8_t v___x_4064_; 
v___x_4063_ = lean_unsigned_to_nat(1u);
v___x_4064_ = lean_nat_dec_le(v___x_4063_, v_res_4054_);
if (v___x_4064_ == 0)
{
lean_dec(v_res_4054_);
lean_dec_ref(v_config_3671_);
goto v___jp_4058_;
}
else
{
lean_object* v___x_4065_; uint8_t v___x_4066_; 
v___x_4065_ = lean_unsigned_to_nat(7u);
v___x_4066_ = lean_nat_dec_le(v_res_4054_, v___x_4065_);
if (v___x_4066_ == 0)
{
lean_dec(v_res_4054_);
lean_dec_ref(v_config_3671_);
goto v___jp_4058_;
}
else
{
lean_object* v_dateformat_4067_; uint8_t v_firstDayOfWeek_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v_range_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; uint8_t v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
lean_del_object(v___x_4056_);
v_dateformat_4067_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_4067_);
lean_dec_ref(v_config_3671_);
v_firstDayOfWeek_4068_ = lean_ctor_get_uint8(v_dateformat_4067_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_4067_);
v___x_4069_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_4068_);
v___x_4070_ = lean_nat_to_int(v_res_4054_);
v___x_4071_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_4072_ = lean_int_sub(v___x_4070_, v___x_4071_);
lean_dec(v___x_4070_);
v___x_4073_ = lean_int_add(v___x_4072_, v___x_4069_);
lean_dec(v___x_4069_);
lean_dec(v___x_4072_);
v___x_4074_ = lean_int_sub(v___x_4073_, v___x_4071_);
lean_dec(v___x_4073_);
v___x_4075_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_4076_ = lean_int_emod(v___x_4074_, v___x_4075_);
lean_dec(v___x_4074_);
v___x_4077_ = lean_int_add(v___x_4076_, v___x_4071_);
lean_dec(v___x_4076_);
v_range_4078_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6);
v___x_4079_ = lean_int_sub(v___x_4077_, v___x_4071_);
lean_dec(v___x_4077_);
v___x_4080_ = lean_int_emod(v___x_4079_, v_range_4078_);
lean_dec(v___x_4079_);
v___x_4081_ = lean_int_add(v___x_4080_, v_range_4078_);
lean_dec(v___x_4080_);
v___x_4082_ = lean_int_emod(v___x_4081_, v_range_4078_);
lean_dec(v___x_4081_);
v___x_4083_ = lean_int_add(v___x_4082_, v___x_4071_);
lean_dec(v___x_4082_);
v___x_4084_ = l_Std_Time_Weekday_ofOrdinal(v___x_4083_);
lean_dec(v___x_4083_);
v___x_4085_ = lean_box(v___x_4084_);
v___x_4086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4086_, 0, v_pos_4053_);
lean_ctor_set(v___x_4086_, 1, v___x_4085_);
return v___x_4086_;
}
}
v___jp_4058_:
{
lean_object* v___x_4059_; lean_object* v___x_4061_; 
v___x_4059_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4));
if (v_isShared_4057_ == 0)
{
lean_ctor_set_tag(v___x_4056_, 1);
lean_ctor_set(v___x_4056_, 1, v___x_4059_);
v___x_4061_ = v___x_4056_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_pos_4053_);
lean_ctor_set(v_reuseFailAlloc_4062_, 1, v___x_4059_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
else
{
lean_object* v_pos_4088_; lean_object* v_err_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_dec_ref(v_config_3671_);
v_pos_4088_ = lean_ctor_get(v___x_4052_, 0);
v_err_4089_ = lean_ctor_get(v___x_4052_, 1);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4052_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_err_4089_);
lean_inc(v_pos_4088_);
lean_dec(v___x_4052_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_pos_4088_);
lean_ctor_set(v_reuseFailAlloc_4095_, 1, v_err_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
else
{
lean_object* v_val_4097_; uint8_t v___x_4098_; 
v_val_4097_ = lean_ctor_get(v_presentation_4050_, 0);
lean_inc(v_val_4097_);
lean_dec_ref_known(v_presentation_4050_, 1);
v___x_4098_ = lean_unbox(v_val_4097_);
lean_dec(v_val_4097_);
switch(v___x_4098_)
{
case 0:
{
lean_object* v_dateformat_4099_; lean_object* v_symbols_4100_; lean_object* v___x_4101_; 
v_dateformat_4099_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_4099_);
lean_dec_ref(v_config_3671_);
v_symbols_4100_ = lean_ctor_get(v_dateformat_4099_, 1);
lean_inc_ref(v_symbols_4100_);
lean_dec_ref(v_dateformat_4099_);
v___x_4101_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4100_, v_a_3673_);
return v___x_4101_;
}
case 1:
{
lean_object* v_dateformat_4102_; lean_object* v_symbols_4103_; lean_object* v___x_4104_; 
v_dateformat_4102_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_4102_);
lean_dec_ref(v_config_3671_);
v_symbols_4103_ = lean_ctor_get(v_dateformat_4102_, 1);
lean_inc_ref(v_symbols_4103_);
lean_dec_ref(v_dateformat_4102_);
v___x_4104_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4103_, v_a_3673_);
return v___x_4104_;
}
case 2:
{
lean_object* v_dateformat_4105_; lean_object* v_symbols_4106_; lean_object* v___x_4107_; 
v_dateformat_4105_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_4105_);
lean_dec_ref(v_config_3671_);
v_symbols_4106_ = lean_ctor_get(v_dateformat_4105_, 1);
lean_inc_ref(v_symbols_4106_);
lean_dec_ref(v_dateformat_4105_);
v___x_4107_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4106_, v_a_3673_);
return v___x_4107_;
}
default: 
{
lean_object* v_dateformat_4108_; lean_object* v_symbols_4109_; lean_object* v___x_4110_; 
v_dateformat_4108_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_4108_);
lean_dec_ref(v_config_3671_);
v_symbols_4109_ = lean_ctor_get(v_dateformat_4108_, 1);
lean_inc_ref(v_symbols_4109_);
lean_dec_ref(v_dateformat_4108_);
v___x_4110_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(v_symbols_4109_, v_a_3673_);
return v___x_4110_;
}
}
}
}
case 15:
{
lean_object* v_presentation_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
lean_dec_ref(v_config_3671_);
v_presentation_4111_ = lean_ctor_get(v_x_3672_, 0);
lean_inc(v_presentation_4111_);
lean_dec_ref_known(v_x_3672_, 1);
v___x_4112_ = lean_unsigned_to_nat(1u);
v___x_4113_ = lean_unsigned_to_nat(5u);
v___x_4114_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4114_, 0, v_presentation_4111_);
v___x_4115_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4112_, v___x_4113_, v___x_4114_, v_a_3673_);
return v___x_4115_;
}
case 16:
{
uint8_t v_presentation_4116_; 
v_presentation_4116_ = lean_ctor_get_uint8(v_x_3672_, 0);
lean_dec_ref_known(v_x_3672_, 0);
switch(v_presentation_4116_)
{
case 1:
{
lean_object* v_dateformat_4117_; lean_object* v_symbols_4118_; lean_object* v___x_4119_; 
v_dateformat_4117_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_4117_);
lean_dec_ref(v_config_3671_);
v_symbols_4118_ = lean_ctor_get(v_dateformat_4117_, 1);
lean_inc_ref(v_symbols_4118_);
lean_dec_ref(v_dateformat_4117_);
v___x_4119_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerLong(v_symbols_4118_, v_a_3673_);
return v___x_4119_;
}
case 2:
{
lean_object* v_dateformat_4120_; lean_object* v_symbols_4121_; lean_object* v___x_4122_; 
v_dateformat_4120_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_4120_);
lean_dec_ref(v_config_3671_);
v_symbols_4121_ = lean_ctor_get(v_dateformat_4120_, 1);
lean_inc_ref(v_symbols_4121_);
lean_dec_ref(v_dateformat_4120_);
v___x_4122_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerNarrow(v_symbols_4121_, v_a_3673_);
return v___x_4122_;
}
default: 
{
lean_object* v_dateformat_4123_; lean_object* v_symbols_4124_; lean_object* v___x_4125_; 
v_dateformat_4123_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_4123_);
lean_dec_ref(v_config_3671_);
v_symbols_4124_ = lean_ctor_get(v_dateformat_4123_, 1);
lean_inc_ref(v_symbols_4124_);
lean_dec_ref(v_dateformat_4123_);
v___x_4125_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerShort(v_symbols_4124_, v_a_3673_);
return v___x_4125_;
}
}
}
case 17:
{
uint8_t v_presentation_4126_; 
v_presentation_4126_ = lean_ctor_get_uint8(v_x_3672_, 0);
lean_dec_ref_known(v_x_3672_, 0);
switch(v_presentation_4126_)
{
case 1:
{
lean_object* v_dateformat_4127_; lean_object* v_symbols_4128_; lean_object* v_dayPeriodLong_4129_; lean_object* v___x_4130_; 
v_dateformat_4127_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_4127_);
lean_dec_ref(v_config_3671_);
v_symbols_4128_ = lean_ctor_get(v_dateformat_4127_, 1);
lean_inc_ref(v_symbols_4128_);
lean_dec_ref(v_dateformat_4127_);
v_dayPeriodLong_4129_ = lean_ctor_get(v_symbols_4128_, 20);
lean_inc_ref(v_dayPeriodLong_4129_);
lean_dec_ref(v_symbols_4128_);
v___x_4130_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodLong_4129_, v_a_3673_);
return v___x_4130_;
}
case 2:
{
lean_object* v_dateformat_4131_; lean_object* v_symbols_4132_; lean_object* v_dayPeriodNarrow_4133_; lean_object* v___x_4134_; 
v_dateformat_4131_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_4131_);
lean_dec_ref(v_config_3671_);
v_symbols_4132_ = lean_ctor_get(v_dateformat_4131_, 1);
lean_inc_ref(v_symbols_4132_);
lean_dec_ref(v_dateformat_4131_);
v_dayPeriodNarrow_4133_ = lean_ctor_get(v_symbols_4132_, 21);
lean_inc_ref(v_dayPeriodNarrow_4133_);
lean_dec_ref(v_symbols_4132_);
v___x_4134_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodNarrow_4133_, v_a_3673_);
return v___x_4134_;
}
default: 
{
lean_object* v_dateformat_4135_; lean_object* v_symbols_4136_; lean_object* v_dayPeriodShort_4137_; lean_object* v___x_4138_; 
v_dateformat_4135_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_4135_);
lean_dec_ref(v_config_3671_);
v_symbols_4136_ = lean_ctor_get(v_dateformat_4135_, 1);
lean_inc_ref(v_symbols_4136_);
lean_dec_ref(v_dateformat_4135_);
v_dayPeriodShort_4137_ = lean_ctor_get(v_symbols_4136_, 19);
lean_inc_ref(v_dayPeriodShort_4137_);
lean_dec_ref(v_symbols_4136_);
v___x_4138_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodShort_4137_, v_a_3673_);
return v___x_4138_;
}
}
}
case 18:
{
uint8_t v_presentation_4139_; 
v_presentation_4139_ = lean_ctor_get_uint8(v_x_3672_, 0);
lean_dec_ref_known(v_x_3672_, 0);
switch(v_presentation_4139_)
{
case 1:
{
lean_object* v_dateformat_4140_; lean_object* v_symbols_4141_; lean_object* v_extendedDayPeriodLong_4142_; lean_object* v___x_4143_; 
v_dateformat_4140_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_4140_);
lean_dec_ref(v_config_3671_);
v_symbols_4141_ = lean_ctor_get(v_dateformat_4140_, 1);
lean_inc_ref(v_symbols_4141_);
lean_dec_ref(v_dateformat_4140_);
v_extendedDayPeriodLong_4142_ = lean_ctor_get(v_symbols_4141_, 23);
lean_inc_ref(v_extendedDayPeriodLong_4142_);
lean_dec_ref(v_symbols_4141_);
v___x_4143_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodLong_4142_, v_a_3673_);
lean_dec_ref(v_extendedDayPeriodLong_4142_);
return v___x_4143_;
}
case 2:
{
lean_object* v_dateformat_4144_; lean_object* v_symbols_4145_; lean_object* v_extendedDayPeriodNarrow_4146_; lean_object* v___x_4147_; 
v_dateformat_4144_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_4144_);
lean_dec_ref(v_config_3671_);
v_symbols_4145_ = lean_ctor_get(v_dateformat_4144_, 1);
lean_inc_ref(v_symbols_4145_);
lean_dec_ref(v_dateformat_4144_);
v_extendedDayPeriodNarrow_4146_ = lean_ctor_get(v_symbols_4145_, 24);
lean_inc_ref(v_extendedDayPeriodNarrow_4146_);
lean_dec_ref(v_symbols_4145_);
v___x_4147_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodNarrow_4146_, v_a_3673_);
lean_dec_ref(v_extendedDayPeriodNarrow_4146_);
return v___x_4147_;
}
default: 
{
lean_object* v_dateformat_4148_; lean_object* v_symbols_4149_; lean_object* v_extendedDayPeriodShort_4150_; lean_object* v___x_4151_; 
v_dateformat_4148_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_4148_);
lean_dec_ref(v_config_3671_);
v_symbols_4149_ = lean_ctor_get(v_dateformat_4148_, 1);
lean_inc_ref(v_symbols_4149_);
lean_dec_ref(v_dateformat_4148_);
v_extendedDayPeriodShort_4150_ = lean_ctor_get(v_symbols_4149_, 22);
lean_inc_ref(v_extendedDayPeriodShort_4150_);
lean_dec_ref(v_symbols_4149_);
v___x_4151_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodShort_4150_, v_a_3673_);
lean_dec_ref(v_extendedDayPeriodShort_4150_);
return v___x_4151_;
}
}
}
case 19:
{
lean_object* v_presentation_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
lean_dec_ref(v_config_3671_);
v_presentation_4152_ = lean_ctor_get(v_x_3672_, 0);
lean_inc(v_presentation_4152_);
lean_dec_ref_known(v_x_3672_, 1);
v___x_4153_ = lean_unsigned_to_nat(1u);
v___x_4154_ = lean_unsigned_to_nat(12u);
v___x_4155_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4155_, 0, v_presentation_4152_);
v___x_4156_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4153_, v___x_4154_, v___x_4155_, v_a_3673_);
return v___x_4156_;
}
case 20:
{
lean_object* v_presentation_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
lean_dec_ref(v_config_3671_);
v_presentation_4157_ = lean_ctor_get(v_x_3672_, 0);
lean_inc(v_presentation_4157_);
lean_dec_ref_known(v_x_3672_, 1);
v___x_4158_ = lean_unsigned_to_nat(0u);
v___x_4159_ = lean_unsigned_to_nat(11u);
v___x_4160_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4160_, 0, v_presentation_4157_);
v___x_4161_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4158_, v___x_4159_, v___x_4160_, v_a_3673_);
return v___x_4161_;
}
case 21:
{
lean_object* v_presentation_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
lean_dec_ref(v_config_3671_);
v_presentation_4162_ = lean_ctor_get(v_x_3672_, 0);
lean_inc(v_presentation_4162_);
lean_dec_ref_known(v_x_3672_, 1);
v___x_4163_ = lean_unsigned_to_nat(1u);
v___x_4164_ = lean_unsigned_to_nat(24u);
v___x_4165_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4165_, 0, v_presentation_4162_);
v___x_4166_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4163_, v___x_4164_, v___x_4165_, v_a_3673_);
return v___x_4166_;
}
case 22:
{
lean_object* v_presentation_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
lean_dec_ref(v_config_3671_);
v_presentation_4167_ = lean_ctor_get(v_x_3672_, 0);
lean_inc(v_presentation_4167_);
lean_dec_ref_known(v_x_3672_, 1);
v___x_4168_ = lean_unsigned_to_nat(0u);
v___x_4169_ = lean_unsigned_to_nat(23u);
v___x_4170_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4170_, 0, v_presentation_4167_);
v___x_4171_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4168_, v___x_4169_, v___x_4170_, v_a_3673_);
return v___x_4171_;
}
case 23:
{
lean_object* v_presentation_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
lean_dec_ref(v_config_3671_);
v_presentation_4172_ = lean_ctor_get(v_x_3672_, 0);
lean_inc(v_presentation_4172_);
lean_dec_ref_known(v_x_3672_, 1);
v___x_4173_ = lean_unsigned_to_nat(0u);
v___x_4174_ = lean_unsigned_to_nat(59u);
v___x_4175_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4175_, 0, v_presentation_4172_);
v___x_4176_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4173_, v___x_4174_, v___x_4175_, v_a_3673_);
return v___x_4176_;
}
case 24:
{
uint8_t v_allowLeapSeconds_4177_; 
v_allowLeapSeconds_4177_ = lean_ctor_get_uint8(v_config_3671_, sizeof(void*)*1);
lean_dec_ref(v_config_3671_);
if (v_allowLeapSeconds_4177_ == 0)
{
lean_object* v_presentation_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v_presentation_4178_ = lean_ctor_get(v_x_3672_, 0);
lean_inc(v_presentation_4178_);
lean_dec_ref_known(v_x_3672_, 1);
v___x_4179_ = lean_unsigned_to_nat(0u);
v___x_4180_ = lean_unsigned_to_nat(59u);
v___x_4181_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4181_, 0, v_presentation_4178_);
v___x_4182_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4179_, v___x_4180_, v___x_4181_, v_a_3673_);
if (lean_obj_tag(v___x_4182_) == 0)
{
lean_object* v_pos_4183_; lean_object* v_res_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4191_; 
v_pos_4183_ = lean_ctor_get(v___x_4182_, 0);
v_res_4184_ = lean_ctor_get(v___x_4182_, 1);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4186_ = v___x_4182_;
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_res_4184_);
lean_inc(v_pos_4183_);
lean_dec(v___x_4182_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4189_; 
if (v_isShared_4187_ == 0)
{
v___x_4189_ = v___x_4186_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_pos_4183_);
lean_ctor_set(v_reuseFailAlloc_4190_, 1, v_res_4184_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
else
{
return v___x_4182_;
}
}
else
{
lean_object* v_presentation_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
v_presentation_4192_ = lean_ctor_get(v_x_3672_, 0);
lean_inc(v_presentation_4192_);
lean_dec_ref_known(v_x_3672_, 1);
v___x_4193_ = lean_unsigned_to_nat(0u);
v___x_4194_ = lean_unsigned_to_nat(60u);
v___x_4195_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4195_, 0, v_presentation_4192_);
v___x_4196_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4193_, v___x_4194_, v___x_4195_, v_a_3673_);
return v___x_4196_;
}
}
case 25:
{
lean_object* v_presentation_4197_; 
lean_dec_ref(v_config_3671_);
v_presentation_4197_ = lean_ctor_get(v_x_3672_, 0);
lean_inc(v_presentation_4197_);
lean_dec_ref_known(v_x_3672_, 1);
if (lean_obj_tag(v_presentation_4197_) == 0)
{
lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4198_ = lean_unsigned_to_nat(0u);
v___x_4199_ = lean_unsigned_to_nat(999999999u);
v___x_4200_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__7));
v___x_4201_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4198_, v___x_4199_, v___x_4200_, v_a_3673_);
return v___x_4201_;
}
else
{
lean_object* v_digits_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v_digits_4202_ = lean_ctor_get(v_presentation_4197_, 0);
lean_inc(v_digits_4202_);
lean_dec_ref_known(v_presentation_4197_, 1);
v___x_4203_ = lean_unsigned_to_nat(0u);
v___x_4204_ = lean_unsigned_to_nat(999999999u);
v___x_4205_ = lean_unsigned_to_nat(9u);
v___x_4206_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed), 3, 2);
lean_closure_set(v___x_4206_, 0, v_digits_4202_);
lean_closure_set(v___x_4206_, 1, v___x_4205_);
v___x_4207_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4203_, v___x_4204_, v___x_4206_, v_a_3673_);
return v___x_4207_;
}
}
case 26:
{
lean_object* v_presentation_4208_; lean_object* v___x_4209_; 
lean_dec_ref(v_config_3671_);
v_presentation_4208_ = lean_ctor_get(v_x_3672_, 0);
lean_inc(v_presentation_4208_);
lean_dec_ref_known(v_x_3672_, 1);
v___x_4209_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_presentation_4208_, v_a_3673_);
lean_dec(v_presentation_4208_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v_pos_4210_; lean_object* v_res_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4219_; 
v_pos_4210_ = lean_ctor_get(v___x_4209_, 0);
v_res_4211_ = lean_ctor_get(v___x_4209_, 1);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4213_ = v___x_4209_;
v_isShared_4214_ = v_isSharedCheck_4219_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_res_4211_);
lean_inc(v_pos_4210_);
lean_dec(v___x_4209_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4219_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4215_; lean_object* v___x_4217_; 
v___x_4215_ = lean_nat_to_int(v_res_4211_);
if (v_isShared_4214_ == 0)
{
lean_ctor_set(v___x_4213_, 1, v___x_4215_);
v___x_4217_ = v___x_4213_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_pos_4210_);
lean_ctor_set(v_reuseFailAlloc_4218_, 1, v___x_4215_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
else
{
lean_object* v_pos_4220_; lean_object* v_err_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4228_; 
v_pos_4220_ = lean_ctor_get(v___x_4209_, 0);
v_err_4221_ = lean_ctor_get(v___x_4209_, 1);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4223_ = v___x_4209_;
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_err_4221_);
lean_inc(v_pos_4220_);
lean_dec(v___x_4209_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_pos_4220_);
lean_ctor_set(v_reuseFailAlloc_4227_, 1, v_err_4221_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
}
case 27:
{
lean_object* v_presentation_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
lean_dec_ref(v_config_3671_);
v_presentation_4229_ = lean_ctor_get(v_x_3672_, 0);
lean_inc(v_presentation_4229_);
lean_dec_ref_known(v_x_3672_, 1);
v___x_4230_ = lean_unsigned_to_nat(0u);
v___x_4231_ = lean_unsigned_to_nat(999999999u);
v___x_4232_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4232_, 0, v_presentation_4229_);
v___x_4233_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4230_, v___x_4231_, v___x_4232_, v_a_3673_);
return v___x_4233_;
}
case 28:
{
lean_object* v_presentation_4234_; lean_object* v___x_4235_; 
lean_dec_ref(v_config_3671_);
v_presentation_4234_ = lean_ctor_get(v_x_3672_, 0);
lean_inc(v_presentation_4234_);
lean_dec_ref_known(v_x_3672_, 1);
v___x_4235_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_presentation_4234_, v_a_3673_);
lean_dec(v_presentation_4234_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_pos_4236_; lean_object* v_res_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4245_; 
v_pos_4236_ = lean_ctor_get(v___x_4235_, 0);
v_res_4237_ = lean_ctor_get(v___x_4235_, 1);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4239_ = v___x_4235_;
v_isShared_4240_ = v_isSharedCheck_4245_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_res_4237_);
lean_inc(v_pos_4236_);
lean_dec(v___x_4235_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4245_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4241_; lean_object* v___x_4243_; 
v___x_4241_ = lean_nat_to_int(v_res_4237_);
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 1, v___x_4241_);
v___x_4243_ = v___x_4239_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_pos_4236_);
lean_ctor_set(v_reuseFailAlloc_4244_, 1, v___x_4241_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
else
{
lean_object* v_pos_4246_; lean_object* v_err_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4254_; 
v_pos_4246_ = lean_ctor_get(v___x_4235_, 0);
v_err_4247_ = lean_ctor_get(v___x_4235_, 1);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4249_ = v___x_4235_;
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_err_4247_);
lean_inc(v_pos_4246_);
lean_dec(v___x_4235_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4252_; 
if (v_isShared_4250_ == 0)
{
v___x_4252_ = v___x_4249_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_pos_4246_);
lean_ctor_set(v_reuseFailAlloc_4253_, 1, v_err_4247_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
return v___x_4252_;
}
}
}
}
case 29:
{
uint8_t v_presentation_4255_; 
lean_dec_ref(v_config_3671_);
v_presentation_4255_ = lean_ctor_get_uint8(v_x_3672_, 0);
lean_dec_ref_known(v_x_3672_, 0);
if (v_presentation_4255_ == 0)
{
lean_object* v___x_4256_; lean_object* v___x_4257_; 
v___x_4256_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
v___x_4257_ = l_Std_Internal_Parsec_String_pstring(v___x_4256_, v_a_3673_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_pos_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4265_; 
v_pos_4258_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4265_ == 0)
{
lean_object* v_unused_4266_; 
v_unused_4266_ = lean_ctor_get(v___x_4257_, 1);
lean_dec(v_unused_4266_);
v___x_4260_ = v___x_4257_;
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_pos_4258_);
lean_dec(v___x_4257_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
if (v_isShared_4261_ == 0)
{
lean_ctor_set(v___x_4260_, 1, v___x_4256_);
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_pos_4258_);
lean_ctor_set(v_reuseFailAlloc_4264_, 1, v___x_4256_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
}
else
{
return v___x_4257_;
}
}
else
{
lean_object* v___x_4267_; 
v___x_4267_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(v_a_3673_);
return v___x_4267_;
}
}
case 32:
{
uint8_t v_presentation_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; 
lean_dec_ref(v_config_3671_);
v_presentation_4268_ = lean_ctor_get_uint8(v_x_3672_, 0);
lean_dec_ref_known(v_x_3672_, 0);
v___x_4269_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4270_ = l_Std_Internal_Parsec_String_pstring(v___x_4269_, v_a_3673_);
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_object* v_pos_4271_; lean_object* v___y_4273_; 
v_pos_4271_ = lean_ctor_get(v___x_4270_, 0);
lean_inc(v_pos_4271_);
lean_dec_ref_known(v___x_4270_, 2);
if (v_presentation_4268_ == 0)
{
uint8_t v___x_4288_; uint8_t v___x_4289_; uint8_t v___x_4290_; lean_object* v___x_4291_; 
v___x_4288_ = 2;
v___x_4289_ = 1;
v___x_4290_ = 1;
lean_inc(v_pos_4271_);
v___x_4291_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4288_, v___x_4289_, v___x_4290_, v_pos_4271_);
v___y_4273_ = v___x_4291_;
goto v___jp_4272_;
}
else
{
uint8_t v___x_4292_; uint8_t v___x_4293_; uint8_t v___x_4294_; lean_object* v___x_4295_; 
v___x_4292_ = 0;
v___x_4293_ = 2;
v___x_4294_ = 1;
lean_inc(v_pos_4271_);
v___x_4295_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4292_, v___x_4293_, v___x_4294_, v_pos_4271_);
v___y_4273_ = v___x_4295_;
goto v___jp_4272_;
}
v___jp_4272_:
{
if (lean_obj_tag(v___y_4273_) == 0)
{
lean_dec(v_pos_4271_);
return v___y_4273_;
}
else
{
lean_object* v_pos_4274_; lean_object* v_snd_4275_; lean_object* v_snd_4276_; uint8_t v_decide_4277_; 
v_pos_4274_ = lean_ctor_get(v___y_4273_, 0);
v_snd_4275_ = lean_ctor_get(v_pos_4271_, 1);
lean_inc(v_snd_4275_);
lean_dec(v_pos_4271_);
v_snd_4276_ = lean_ctor_get(v_pos_4274_, 1);
v_decide_4277_ = lean_nat_dec_eq(v_snd_4275_, v_snd_4276_);
lean_dec(v_snd_4275_);
if (v_decide_4277_ == 0)
{
return v___y_4273_;
}
else
{
lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4285_; 
lean_inc(v_pos_4274_);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___y_4273_);
if (v_isSharedCheck_4285_ == 0)
{
lean_object* v_unused_4286_; lean_object* v_unused_4287_; 
v_unused_4286_ = lean_ctor_get(v___y_4273_, 1);
lean_dec(v_unused_4286_);
v_unused_4287_ = lean_ctor_get(v___y_4273_, 0);
lean_dec(v_unused_4287_);
v___x_4279_ = v___y_4273_;
v_isShared_4280_ = v_isSharedCheck_4285_;
goto v_resetjp_4278_;
}
else
{
lean_dec(v___y_4273_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4285_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4281_; lean_object* v___x_4283_; 
v___x_4281_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_4280_ == 0)
{
lean_ctor_set_tag(v___x_4279_, 0);
lean_ctor_set(v___x_4279_, 1, v___x_4281_);
v___x_4283_ = v___x_4279_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_pos_4274_);
lean_ctor_set(v_reuseFailAlloc_4284_, 1, v___x_4281_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
}
}
}
}
else
{
lean_object* v_pos_4296_; lean_object* v_err_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4304_; 
v_pos_4296_ = lean_ctor_get(v___x_4270_, 0);
v_err_4297_ = lean_ctor_get(v___x_4270_, 1);
v_isSharedCheck_4304_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_4299_ = v___x_4270_;
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_err_4297_);
lean_inc(v_pos_4296_);
lean_dec(v___x_4270_);
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
v_reuseFailAlloc_4303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_pos_4296_);
lean_ctor_set(v_reuseFailAlloc_4303_, 1, v_err_4297_);
v___x_4302_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
return v___x_4302_;
}
}
}
}
case 33:
{
uint8_t v_presentation_4305_; 
lean_dec_ref(v_config_3671_);
v_presentation_4305_ = lean_ctor_get_uint8(v_x_3672_, 0);
lean_dec_ref_known(v_x_3672_, 0);
switch(v_presentation_4305_)
{
case 0:
{
uint8_t v___x_4306_; uint8_t v___x_4307_; uint8_t v___x_4308_; lean_object* v___x_4309_; 
v___x_4306_ = 2;
v___x_4307_ = 1;
v___x_4308_ = 0;
lean_inc_ref(v_a_3673_);
v___x_4309_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4306_, v___x_4307_, v___x_4308_, v_a_3673_);
v___y_3685_ = v___x_4309_;
goto v___jp_3684_;
}
case 1:
{
uint8_t v___x_4310_; uint8_t v___x_4311_; uint8_t v___x_4312_; lean_object* v___x_4313_; 
v___x_4310_ = 0;
v___x_4311_ = 1;
v___x_4312_ = 0;
lean_inc_ref(v_a_3673_);
v___x_4313_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4310_, v___x_4311_, v___x_4312_, v_a_3673_);
v___y_3685_ = v___x_4313_;
goto v___jp_3684_;
}
case 2:
{
uint8_t v___x_4314_; uint8_t v___x_4315_; uint8_t v___x_4316_; lean_object* v___x_4317_; 
v___x_4314_ = 0;
v___x_4315_ = 1;
v___x_4316_ = 1;
lean_inc_ref(v_a_3673_);
v___x_4317_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4314_, v___x_4315_, v___x_4316_, v_a_3673_);
v___y_3685_ = v___x_4317_;
goto v___jp_3684_;
}
case 3:
{
uint8_t v___x_4318_; uint8_t v___x_4319_; uint8_t v___x_4320_; lean_object* v___x_4321_; 
v___x_4318_ = 0;
v___x_4319_ = 2;
v___x_4320_ = 0;
lean_inc_ref(v_a_3673_);
v___x_4321_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4318_, v___x_4319_, v___x_4320_, v_a_3673_);
v___y_3685_ = v___x_4321_;
goto v___jp_3684_;
}
default: 
{
uint8_t v___x_4322_; uint8_t v___x_4323_; uint8_t v___x_4324_; lean_object* v___x_4325_; 
v___x_4322_ = 0;
v___x_4323_ = 2;
v___x_4324_ = 1;
lean_inc_ref(v_a_3673_);
v___x_4325_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4322_, v___x_4323_, v___x_4324_, v_a_3673_);
v___y_3685_ = v___x_4325_;
goto v___jp_3684_;
}
}
}
case 34:
{
uint8_t v_presentation_4326_; 
lean_dec_ref(v_config_3671_);
v_presentation_4326_ = lean_ctor_get_uint8(v_x_3672_, 0);
lean_dec_ref_known(v_x_3672_, 0);
switch(v_presentation_4326_)
{
case 0:
{
uint8_t v___x_4327_; uint8_t v___x_4328_; uint8_t v___x_4329_; lean_object* v___x_4330_; 
v___x_4327_ = 2;
v___x_4328_ = 1;
v___x_4329_ = 0;
v___x_4330_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4327_, v___x_4328_, v___x_4329_, v_a_3673_);
return v___x_4330_;
}
case 1:
{
uint8_t v___x_4331_; uint8_t v___x_4332_; uint8_t v___x_4333_; lean_object* v___x_4334_; 
v___x_4331_ = 0;
v___x_4332_ = 1;
v___x_4333_ = 0;
v___x_4334_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4331_, v___x_4332_, v___x_4333_, v_a_3673_);
return v___x_4334_;
}
case 3:
{
uint8_t v___x_4335_; uint8_t v___x_4336_; uint8_t v___x_4337_; lean_object* v___x_4338_; 
v___x_4335_ = 0;
v___x_4336_ = 2;
v___x_4337_ = 0;
v___x_4338_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4335_, v___x_4336_, v___x_4337_, v_a_3673_);
return v___x_4338_;
}
default: 
{
v___y_3712_ = v_a_3673_;
goto v___jp_3711_;
}
}
}
case 35:
{
uint8_t v_presentation_4339_; 
lean_dec_ref(v_config_3671_);
v_presentation_4339_ = lean_ctor_get_uint8(v_x_3672_, 0);
lean_dec_ref_known(v_x_3672_, 0);
switch(v_presentation_4339_)
{
case 0:
{
uint8_t v___x_4340_; uint8_t v___x_4341_; uint8_t v___x_4342_; lean_object* v___x_4343_; 
v___x_4340_ = 0;
v___x_4341_ = 2;
v___x_4342_ = 0;
v___x_4343_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4340_, v___x_4341_, v___x_4342_, v_a_3673_);
return v___x_4343_;
}
case 1:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4344_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4345_ = l_Std_Internal_Parsec_String_pstring(v___x_4344_, v_a_3673_);
if (lean_obj_tag(v___x_4345_) == 0)
{
lean_object* v_pos_4346_; uint8_t v___x_4347_; uint8_t v___x_4348_; uint8_t v___x_4349_; lean_object* v___x_4350_; 
v_pos_4346_ = lean_ctor_get(v___x_4345_, 0);
lean_inc_n(v_pos_4346_, 2);
lean_dec_ref_known(v___x_4345_, 2);
v___x_4347_ = 0;
v___x_4348_ = 1;
v___x_4349_ = 1;
v___x_4350_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4347_, v___x_4348_, v___x_4349_, v_pos_4346_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_dec(v_pos_4346_);
return v___x_4350_;
}
else
{
lean_object* v_pos_4351_; lean_object* v_snd_4352_; lean_object* v_snd_4353_; uint8_t v_decide_4354_; 
v_pos_4351_ = lean_ctor_get(v___x_4350_, 0);
v_snd_4352_ = lean_ctor_get(v_pos_4346_, 1);
lean_inc(v_snd_4352_);
lean_dec(v_pos_4346_);
v_snd_4353_ = lean_ctor_get(v_pos_4351_, 1);
v_decide_4354_ = lean_nat_dec_eq(v_snd_4352_, v_snd_4353_);
lean_dec(v_snd_4352_);
if (v_decide_4354_ == 0)
{
return v___x_4350_;
}
else
{
lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4362_; 
lean_inc(v_pos_4351_);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4362_ == 0)
{
lean_object* v_unused_4363_; lean_object* v_unused_4364_; 
v_unused_4363_ = lean_ctor_get(v___x_4350_, 1);
lean_dec(v_unused_4363_);
v_unused_4364_ = lean_ctor_get(v___x_4350_, 0);
lean_dec(v_unused_4364_);
v___x_4356_ = v___x_4350_;
v_isShared_4357_ = v_isSharedCheck_4362_;
goto v_resetjp_4355_;
}
else
{
lean_dec(v___x_4350_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4362_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v___x_4358_; lean_object* v___x_4360_; 
v___x_4358_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_4357_ == 0)
{
lean_ctor_set_tag(v___x_4356_, 0);
lean_ctor_set(v___x_4356_, 1, v___x_4358_);
v___x_4360_ = v___x_4356_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_pos_4351_);
lean_ctor_set(v_reuseFailAlloc_4361_, 1, v___x_4358_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
}
}
else
{
lean_object* v_pos_4365_; lean_object* v_err_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4373_; 
v_pos_4365_ = lean_ctor_get(v___x_4345_, 0);
v_err_4366_ = lean_ctor_get(v___x_4345_, 1);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4345_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4368_ = v___x_4345_;
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_err_4366_);
lean_inc(v_pos_4365_);
lean_dec(v___x_4345_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4371_; 
if (v_isShared_4369_ == 0)
{
v___x_4371_ = v___x_4368_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_pos_4365_);
lean_ctor_set(v_reuseFailAlloc_4372_, 1, v_err_4366_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
}
default: 
{
lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4374_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
lean_inc_ref(v_a_3673_);
v___x_4375_ = l_Std_Internal_Parsec_String_pstring(v___x_4374_, v_a_3673_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v_pos_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4384_; 
lean_dec_ref(v_a_3673_);
v_pos_4376_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4384_ == 0)
{
lean_object* v_unused_4385_; 
v_unused_4385_ = lean_ctor_get(v___x_4375_, 1);
lean_dec(v_unused_4385_);
v___x_4378_ = v___x_4375_;
v_isShared_4379_ = v_isSharedCheck_4384_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_pos_4376_);
lean_dec(v___x_4375_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4384_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4380_; lean_object* v___x_4382_; 
v___x_4380_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 1, v___x_4380_);
v___x_4382_ = v___x_4378_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_pos_4376_);
lean_ctor_set(v_reuseFailAlloc_4383_, 1, v___x_4380_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
return v___x_4382_;
}
}
}
else
{
lean_object* v_pos_4386_; lean_object* v_err_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4400_; 
v_pos_4386_ = lean_ctor_get(v___x_4375_, 0);
v_err_4387_ = lean_ctor_get(v___x_4375_, 1);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4389_ = v___x_4375_;
v_isShared_4390_ = v_isSharedCheck_4400_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_err_4387_);
lean_inc(v_pos_4386_);
lean_dec(v___x_4375_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4400_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v_snd_4391_; lean_object* v_snd_4392_; uint8_t v_decide_4393_; 
v_snd_4391_ = lean_ctor_get(v_a_3673_, 1);
lean_inc(v_snd_4391_);
lean_dec_ref(v_a_3673_);
v_snd_4392_ = lean_ctor_get(v_pos_4386_, 1);
v_decide_4393_ = lean_nat_dec_eq(v_snd_4391_, v_snd_4392_);
lean_dec(v_snd_4391_);
if (v_decide_4393_ == 0)
{
lean_object* v___x_4395_; 
if (v_isShared_4390_ == 0)
{
v___x_4395_ = v___x_4389_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_pos_4386_);
lean_ctor_set(v_reuseFailAlloc_4396_, 1, v_err_4387_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
else
{
uint8_t v___x_4397_; uint8_t v___x_4398_; lean_object* v___x_4399_; 
lean_del_object(v___x_4389_);
lean_dec(v_err_4387_);
v___x_4397_ = 0;
v___x_4398_ = 2;
v___x_4399_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4397_, v___x_4398_, v_decide_4393_, v_pos_4386_);
return v___x_4399_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_4401_; 
lean_dec_ref(v_x_3672_);
lean_dec_ref(v_config_3671_);
v___x_4401_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(v_a_3673_);
return v___x_4401_;
}
}
v___jp_3674_:
{
lean_object* v_dateformat_3676_; lean_object* v_symbols_3677_; lean_object* v___x_3678_; 
v_dateformat_3676_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_3676_);
lean_dec_ref(v_config_3671_);
v_symbols_3677_ = lean_ctor_get(v_dateformat_3676_, 1);
lean_inc_ref(v_symbols_3677_);
lean_dec_ref(v_dateformat_3676_);
v___x_3678_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(v_symbols_3677_, v___y_3675_);
return v___x_3678_;
}
v___jp_3679_:
{
lean_object* v_dateformat_3681_; lean_object* v_symbols_3682_; lean_object* v___x_3683_; 
v_dateformat_3681_ = lean_ctor_get(v_config_3671_, 0);
lean_inc_ref(v_dateformat_3681_);
lean_dec_ref(v_config_3671_);
v_symbols_3682_ = lean_ctor_get(v_dateformat_3681_, 1);
lean_inc_ref(v_symbols_3682_);
lean_dec_ref(v_dateformat_3681_);
v___x_3683_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(v_symbols_3682_, v___y_3680_);
return v___x_3683_;
}
v___jp_3684_:
{
if (lean_obj_tag(v___y_3685_) == 0)
{
lean_dec_ref(v_a_3673_);
return v___y_3685_;
}
else
{
lean_object* v_pos_3686_; lean_object* v_snd_3687_; lean_object* v_snd_3688_; uint8_t v_decide_3689_; 
v_pos_3686_ = lean_ctor_get(v___y_3685_, 0);
v_snd_3687_ = lean_ctor_get(v_a_3673_, 1);
lean_inc(v_snd_3687_);
lean_dec_ref(v_a_3673_);
v_snd_3688_ = lean_ctor_get(v_pos_3686_, 1);
v_decide_3689_ = lean_nat_dec_eq(v_snd_3687_, v_snd_3688_);
lean_dec(v_snd_3687_);
if (v_decide_3689_ == 0)
{
return v___y_3685_;
}
else
{
lean_object* v___x_3690_; lean_object* v___x_3691_; 
lean_inc(v_pos_3686_);
lean_dec_ref_known(v___y_3685_, 2);
v___x_3690_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
v___x_3691_ = l_Std_Internal_Parsec_String_pstring(v___x_3690_, v_pos_3686_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v_pos_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3700_; 
v_pos_3692_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3700_ == 0)
{
lean_object* v_unused_3701_; 
v_unused_3701_ = lean_ctor_get(v___x_3691_, 1);
lean_dec(v_unused_3701_);
v___x_3694_ = v___x_3691_;
v_isShared_3695_ = v_isSharedCheck_3700_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_pos_3692_);
lean_dec(v___x_3691_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3700_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3696_; lean_object* v___x_3698_; 
v___x_3696_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 1, v___x_3696_);
v___x_3698_ = v___x_3694_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_pos_3692_);
lean_ctor_set(v_reuseFailAlloc_3699_, 1, v___x_3696_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
else
{
lean_object* v_pos_3702_; lean_object* v_err_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
v_pos_3702_ = lean_ctor_get(v___x_3691_, 0);
v_err_3703_ = lean_ctor_get(v___x_3691_, 1);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3691_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_err_3703_);
lean_inc(v_pos_3702_);
lean_dec(v___x_3691_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_pos_3702_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v_err_3703_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
}
}
v___jp_3711_:
{
uint8_t v___x_3713_; uint8_t v___x_3714_; uint8_t v___x_3715_; lean_object* v___x_3716_; 
v___x_3713_ = 0;
v___x_3714_ = 2;
v___x_3715_ = 1;
v___x_3716_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_3713_, v___x_3714_, v___x_3715_, v___y_3712_);
return v___x_3716_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(lean_object* v_dateformat_4402_, lean_object* v_date_4403_, lean_object* v_part_4404_){
_start:
{
if (lean_obj_tag(v_part_4404_) == 0)
{
lean_object* v_val_4405_; 
lean_dec_ref(v_date_4403_);
v_val_4405_ = lean_ctor_get(v_part_4404_, 0);
lean_inc_ref(v_val_4405_);
lean_dec_ref_known(v_part_4404_, 1);
return v_val_4405_;
}
else
{
lean_object* v_modifier_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; 
v_modifier_4406_ = lean_ctor_get(v_part_4404_, 0);
lean_inc_ref(v_modifier_4406_);
lean_dec_ref_known(v_part_4404_, 1);
v___x_4407_ = l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(v_modifier_4406_, v_dateformat_4402_, v_date_4403_);
v___x_4408_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_4402_, v_modifier_4406_, v___x_4407_);
return v___x_4408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate___boxed(lean_object* v_dateformat_4409_, lean_object* v_date_4410_, lean_object* v_part_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_4409_, v_date_4410_, v_part_4411_);
lean_dec_ref(v_dateformat_4409_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(lean_object* v_date_4413_, lean_object* v_modifier_4414_, lean_object* v_data_4415_){
_start:
{
switch(lean_obj_tag(v_modifier_4414_))
{
case 0:
{
lean_object* v_y_4416_; lean_object* v_u_4417_; lean_object* v_Y_4418_; lean_object* v_D_4419_; lean_object* v_M_4420_; lean_object* v_L_4421_; lean_object* v_d_4422_; lean_object* v_Q_4423_; lean_object* v_q_4424_; lean_object* v_w_4425_; lean_object* v_W_4426_; lean_object* v_E_4427_; lean_object* v_e_4428_; lean_object* v_c_4429_; lean_object* v_F_4430_; lean_object* v_a_4431_; lean_object* v_b_4432_; lean_object* v_B_4433_; lean_object* v_h_4434_; lean_object* v_K_4435_; lean_object* v_k_4436_; lean_object* v_H_4437_; lean_object* v_m_4438_; lean_object* v_s_4439_; lean_object* v_S_4440_; lean_object* v_A_4441_; lean_object* v_n_4442_; lean_object* v_N_4443_; lean_object* v_V_4444_; lean_object* v_z_4445_; lean_object* v_zabbrev_4446_; lean_object* v_v_4447_; lean_object* v_O_4448_; lean_object* v_X_4449_; lean_object* v_x_4450_; lean_object* v_Z_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4459_; 
lean_dec_ref_known(v_modifier_4414_, 0);
v_y_4416_ = lean_ctor_get(v_date_4413_, 1);
v_u_4417_ = lean_ctor_get(v_date_4413_, 2);
v_Y_4418_ = lean_ctor_get(v_date_4413_, 3);
v_D_4419_ = lean_ctor_get(v_date_4413_, 4);
v_M_4420_ = lean_ctor_get(v_date_4413_, 5);
v_L_4421_ = lean_ctor_get(v_date_4413_, 6);
v_d_4422_ = lean_ctor_get(v_date_4413_, 7);
v_Q_4423_ = lean_ctor_get(v_date_4413_, 8);
v_q_4424_ = lean_ctor_get(v_date_4413_, 9);
v_w_4425_ = lean_ctor_get(v_date_4413_, 10);
v_W_4426_ = lean_ctor_get(v_date_4413_, 11);
v_E_4427_ = lean_ctor_get(v_date_4413_, 12);
v_e_4428_ = lean_ctor_get(v_date_4413_, 13);
v_c_4429_ = lean_ctor_get(v_date_4413_, 14);
v_F_4430_ = lean_ctor_get(v_date_4413_, 15);
v_a_4431_ = lean_ctor_get(v_date_4413_, 16);
v_b_4432_ = lean_ctor_get(v_date_4413_, 17);
v_B_4433_ = lean_ctor_get(v_date_4413_, 18);
v_h_4434_ = lean_ctor_get(v_date_4413_, 19);
v_K_4435_ = lean_ctor_get(v_date_4413_, 20);
v_k_4436_ = lean_ctor_get(v_date_4413_, 21);
v_H_4437_ = lean_ctor_get(v_date_4413_, 22);
v_m_4438_ = lean_ctor_get(v_date_4413_, 23);
v_s_4439_ = lean_ctor_get(v_date_4413_, 24);
v_S_4440_ = lean_ctor_get(v_date_4413_, 25);
v_A_4441_ = lean_ctor_get(v_date_4413_, 26);
v_n_4442_ = lean_ctor_get(v_date_4413_, 27);
v_N_4443_ = lean_ctor_get(v_date_4413_, 28);
v_V_4444_ = lean_ctor_get(v_date_4413_, 29);
v_z_4445_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_4446_ = lean_ctor_get(v_date_4413_, 31);
v_v_4447_ = lean_ctor_get(v_date_4413_, 32);
v_O_4448_ = lean_ctor_get(v_date_4413_, 33);
v_X_4449_ = lean_ctor_get(v_date_4413_, 34);
v_x_4450_ = lean_ctor_get(v_date_4413_, 35);
v_Z_4451_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_4459_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_4459_ == 0)
{
lean_object* v_unused_4460_; 
v_unused_4460_ = lean_ctor_get(v_date_4413_, 0);
lean_dec(v_unused_4460_);
v___x_4453_ = v_date_4413_;
v_isShared_4454_ = v_isSharedCheck_4459_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_Z_4451_);
lean_inc(v_x_4450_);
lean_inc(v_X_4449_);
lean_inc(v_O_4448_);
lean_inc(v_v_4447_);
lean_inc(v_zabbrev_4446_);
lean_inc(v_z_4445_);
lean_inc(v_V_4444_);
lean_inc(v_N_4443_);
lean_inc(v_n_4442_);
lean_inc(v_A_4441_);
lean_inc(v_S_4440_);
lean_inc(v_s_4439_);
lean_inc(v_m_4438_);
lean_inc(v_H_4437_);
lean_inc(v_k_4436_);
lean_inc(v_K_4435_);
lean_inc(v_h_4434_);
lean_inc(v_B_4433_);
lean_inc(v_b_4432_);
lean_inc(v_a_4431_);
lean_inc(v_F_4430_);
lean_inc(v_c_4429_);
lean_inc(v_e_4428_);
lean_inc(v_E_4427_);
lean_inc(v_W_4426_);
lean_inc(v_w_4425_);
lean_inc(v_q_4424_);
lean_inc(v_Q_4423_);
lean_inc(v_d_4422_);
lean_inc(v_L_4421_);
lean_inc(v_M_4420_);
lean_inc(v_D_4419_);
lean_inc(v_Y_4418_);
lean_inc(v_u_4417_);
lean_inc(v_y_4416_);
lean_dec(v_date_4413_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4459_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4455_; lean_object* v___x_4457_; 
v___x_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4455_, 0, v_data_4415_);
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 0, v___x_4455_);
v___x_4457_ = v___x_4453_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v___x_4455_);
lean_ctor_set(v_reuseFailAlloc_4458_, 1, v_y_4416_);
lean_ctor_set(v_reuseFailAlloc_4458_, 2, v_u_4417_);
lean_ctor_set(v_reuseFailAlloc_4458_, 3, v_Y_4418_);
lean_ctor_set(v_reuseFailAlloc_4458_, 4, v_D_4419_);
lean_ctor_set(v_reuseFailAlloc_4458_, 5, v_M_4420_);
lean_ctor_set(v_reuseFailAlloc_4458_, 6, v_L_4421_);
lean_ctor_set(v_reuseFailAlloc_4458_, 7, v_d_4422_);
lean_ctor_set(v_reuseFailAlloc_4458_, 8, v_Q_4423_);
lean_ctor_set(v_reuseFailAlloc_4458_, 9, v_q_4424_);
lean_ctor_set(v_reuseFailAlloc_4458_, 10, v_w_4425_);
lean_ctor_set(v_reuseFailAlloc_4458_, 11, v_W_4426_);
lean_ctor_set(v_reuseFailAlloc_4458_, 12, v_E_4427_);
lean_ctor_set(v_reuseFailAlloc_4458_, 13, v_e_4428_);
lean_ctor_set(v_reuseFailAlloc_4458_, 14, v_c_4429_);
lean_ctor_set(v_reuseFailAlloc_4458_, 15, v_F_4430_);
lean_ctor_set(v_reuseFailAlloc_4458_, 16, v_a_4431_);
lean_ctor_set(v_reuseFailAlloc_4458_, 17, v_b_4432_);
lean_ctor_set(v_reuseFailAlloc_4458_, 18, v_B_4433_);
lean_ctor_set(v_reuseFailAlloc_4458_, 19, v_h_4434_);
lean_ctor_set(v_reuseFailAlloc_4458_, 20, v_K_4435_);
lean_ctor_set(v_reuseFailAlloc_4458_, 21, v_k_4436_);
lean_ctor_set(v_reuseFailAlloc_4458_, 22, v_H_4437_);
lean_ctor_set(v_reuseFailAlloc_4458_, 23, v_m_4438_);
lean_ctor_set(v_reuseFailAlloc_4458_, 24, v_s_4439_);
lean_ctor_set(v_reuseFailAlloc_4458_, 25, v_S_4440_);
lean_ctor_set(v_reuseFailAlloc_4458_, 26, v_A_4441_);
lean_ctor_set(v_reuseFailAlloc_4458_, 27, v_n_4442_);
lean_ctor_set(v_reuseFailAlloc_4458_, 28, v_N_4443_);
lean_ctor_set(v_reuseFailAlloc_4458_, 29, v_V_4444_);
lean_ctor_set(v_reuseFailAlloc_4458_, 30, v_z_4445_);
lean_ctor_set(v_reuseFailAlloc_4458_, 31, v_zabbrev_4446_);
lean_ctor_set(v_reuseFailAlloc_4458_, 32, v_v_4447_);
lean_ctor_set(v_reuseFailAlloc_4458_, 33, v_O_4448_);
lean_ctor_set(v_reuseFailAlloc_4458_, 34, v_X_4449_);
lean_ctor_set(v_reuseFailAlloc_4458_, 35, v_x_4450_);
lean_ctor_set(v_reuseFailAlloc_4458_, 36, v_Z_4451_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
case 1:
{
lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4511_; 
v_isSharedCheck_4511_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_4511_ == 0)
{
lean_object* v_unused_4512_; 
v_unused_4512_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_4512_);
v___x_4462_ = v_modifier_4414_;
v_isShared_4463_ = v_isSharedCheck_4511_;
goto v_resetjp_4461_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4511_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v_G_4464_; lean_object* v_y_4465_; lean_object* v_Y_4466_; lean_object* v_D_4467_; lean_object* v_M_4468_; lean_object* v_L_4469_; lean_object* v_d_4470_; lean_object* v_Q_4471_; lean_object* v_q_4472_; lean_object* v_w_4473_; lean_object* v_W_4474_; lean_object* v_E_4475_; lean_object* v_e_4476_; lean_object* v_c_4477_; lean_object* v_F_4478_; lean_object* v_a_4479_; lean_object* v_b_4480_; lean_object* v_B_4481_; lean_object* v_h_4482_; lean_object* v_K_4483_; lean_object* v_k_4484_; lean_object* v_H_4485_; lean_object* v_m_4486_; lean_object* v_s_4487_; lean_object* v_S_4488_; lean_object* v_A_4489_; lean_object* v_n_4490_; lean_object* v_N_4491_; lean_object* v_V_4492_; lean_object* v_z_4493_; lean_object* v_zabbrev_4494_; lean_object* v_v_4495_; lean_object* v_O_4496_; lean_object* v_X_4497_; lean_object* v_x_4498_; lean_object* v_Z_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4509_; 
v_G_4464_ = lean_ctor_get(v_date_4413_, 0);
v_y_4465_ = lean_ctor_get(v_date_4413_, 1);
v_Y_4466_ = lean_ctor_get(v_date_4413_, 3);
v_D_4467_ = lean_ctor_get(v_date_4413_, 4);
v_M_4468_ = lean_ctor_get(v_date_4413_, 5);
v_L_4469_ = lean_ctor_get(v_date_4413_, 6);
v_d_4470_ = lean_ctor_get(v_date_4413_, 7);
v_Q_4471_ = lean_ctor_get(v_date_4413_, 8);
v_q_4472_ = lean_ctor_get(v_date_4413_, 9);
v_w_4473_ = lean_ctor_get(v_date_4413_, 10);
v_W_4474_ = lean_ctor_get(v_date_4413_, 11);
v_E_4475_ = lean_ctor_get(v_date_4413_, 12);
v_e_4476_ = lean_ctor_get(v_date_4413_, 13);
v_c_4477_ = lean_ctor_get(v_date_4413_, 14);
v_F_4478_ = lean_ctor_get(v_date_4413_, 15);
v_a_4479_ = lean_ctor_get(v_date_4413_, 16);
v_b_4480_ = lean_ctor_get(v_date_4413_, 17);
v_B_4481_ = lean_ctor_get(v_date_4413_, 18);
v_h_4482_ = lean_ctor_get(v_date_4413_, 19);
v_K_4483_ = lean_ctor_get(v_date_4413_, 20);
v_k_4484_ = lean_ctor_get(v_date_4413_, 21);
v_H_4485_ = lean_ctor_get(v_date_4413_, 22);
v_m_4486_ = lean_ctor_get(v_date_4413_, 23);
v_s_4487_ = lean_ctor_get(v_date_4413_, 24);
v_S_4488_ = lean_ctor_get(v_date_4413_, 25);
v_A_4489_ = lean_ctor_get(v_date_4413_, 26);
v_n_4490_ = lean_ctor_get(v_date_4413_, 27);
v_N_4491_ = lean_ctor_get(v_date_4413_, 28);
v_V_4492_ = lean_ctor_get(v_date_4413_, 29);
v_z_4493_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_4494_ = lean_ctor_get(v_date_4413_, 31);
v_v_4495_ = lean_ctor_get(v_date_4413_, 32);
v_O_4496_ = lean_ctor_get(v_date_4413_, 33);
v_X_4497_ = lean_ctor_get(v_date_4413_, 34);
v_x_4498_ = lean_ctor_get(v_date_4413_, 35);
v_Z_4499_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_4509_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_4509_ == 0)
{
lean_object* v_unused_4510_; 
v_unused_4510_ = lean_ctor_get(v_date_4413_, 2);
lean_dec(v_unused_4510_);
v___x_4501_ = v_date_4413_;
v_isShared_4502_ = v_isSharedCheck_4509_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_Z_4499_);
lean_inc(v_x_4498_);
lean_inc(v_X_4497_);
lean_inc(v_O_4496_);
lean_inc(v_v_4495_);
lean_inc(v_zabbrev_4494_);
lean_inc(v_z_4493_);
lean_inc(v_V_4492_);
lean_inc(v_N_4491_);
lean_inc(v_n_4490_);
lean_inc(v_A_4489_);
lean_inc(v_S_4488_);
lean_inc(v_s_4487_);
lean_inc(v_m_4486_);
lean_inc(v_H_4485_);
lean_inc(v_k_4484_);
lean_inc(v_K_4483_);
lean_inc(v_h_4482_);
lean_inc(v_B_4481_);
lean_inc(v_b_4480_);
lean_inc(v_a_4479_);
lean_inc(v_F_4478_);
lean_inc(v_c_4477_);
lean_inc(v_e_4476_);
lean_inc(v_E_4475_);
lean_inc(v_W_4474_);
lean_inc(v_w_4473_);
lean_inc(v_q_4472_);
lean_inc(v_Q_4471_);
lean_inc(v_d_4470_);
lean_inc(v_L_4469_);
lean_inc(v_M_4468_);
lean_inc(v_D_4467_);
lean_inc(v_Y_4466_);
lean_inc(v_y_4465_);
lean_inc(v_G_4464_);
lean_dec(v_date_4413_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4509_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4504_; 
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 0, v_data_4415_);
v___x_4504_ = v___x_4462_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_data_4415_);
v___x_4504_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
lean_object* v___x_4506_; 
if (v_isShared_4502_ == 0)
{
lean_ctor_set(v___x_4501_, 2, v___x_4504_);
v___x_4506_ = v___x_4501_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_G_4464_);
lean_ctor_set(v_reuseFailAlloc_4507_, 1, v_y_4465_);
lean_ctor_set(v_reuseFailAlloc_4507_, 2, v___x_4504_);
lean_ctor_set(v_reuseFailAlloc_4507_, 3, v_Y_4466_);
lean_ctor_set(v_reuseFailAlloc_4507_, 4, v_D_4467_);
lean_ctor_set(v_reuseFailAlloc_4507_, 5, v_M_4468_);
lean_ctor_set(v_reuseFailAlloc_4507_, 6, v_L_4469_);
lean_ctor_set(v_reuseFailAlloc_4507_, 7, v_d_4470_);
lean_ctor_set(v_reuseFailAlloc_4507_, 8, v_Q_4471_);
lean_ctor_set(v_reuseFailAlloc_4507_, 9, v_q_4472_);
lean_ctor_set(v_reuseFailAlloc_4507_, 10, v_w_4473_);
lean_ctor_set(v_reuseFailAlloc_4507_, 11, v_W_4474_);
lean_ctor_set(v_reuseFailAlloc_4507_, 12, v_E_4475_);
lean_ctor_set(v_reuseFailAlloc_4507_, 13, v_e_4476_);
lean_ctor_set(v_reuseFailAlloc_4507_, 14, v_c_4477_);
lean_ctor_set(v_reuseFailAlloc_4507_, 15, v_F_4478_);
lean_ctor_set(v_reuseFailAlloc_4507_, 16, v_a_4479_);
lean_ctor_set(v_reuseFailAlloc_4507_, 17, v_b_4480_);
lean_ctor_set(v_reuseFailAlloc_4507_, 18, v_B_4481_);
lean_ctor_set(v_reuseFailAlloc_4507_, 19, v_h_4482_);
lean_ctor_set(v_reuseFailAlloc_4507_, 20, v_K_4483_);
lean_ctor_set(v_reuseFailAlloc_4507_, 21, v_k_4484_);
lean_ctor_set(v_reuseFailAlloc_4507_, 22, v_H_4485_);
lean_ctor_set(v_reuseFailAlloc_4507_, 23, v_m_4486_);
lean_ctor_set(v_reuseFailAlloc_4507_, 24, v_s_4487_);
lean_ctor_set(v_reuseFailAlloc_4507_, 25, v_S_4488_);
lean_ctor_set(v_reuseFailAlloc_4507_, 26, v_A_4489_);
lean_ctor_set(v_reuseFailAlloc_4507_, 27, v_n_4490_);
lean_ctor_set(v_reuseFailAlloc_4507_, 28, v_N_4491_);
lean_ctor_set(v_reuseFailAlloc_4507_, 29, v_V_4492_);
lean_ctor_set(v_reuseFailAlloc_4507_, 30, v_z_4493_);
lean_ctor_set(v_reuseFailAlloc_4507_, 31, v_zabbrev_4494_);
lean_ctor_set(v_reuseFailAlloc_4507_, 32, v_v_4495_);
lean_ctor_set(v_reuseFailAlloc_4507_, 33, v_O_4496_);
lean_ctor_set(v_reuseFailAlloc_4507_, 34, v_X_4497_);
lean_ctor_set(v_reuseFailAlloc_4507_, 35, v_x_4498_);
lean_ctor_set(v_reuseFailAlloc_4507_, 36, v_Z_4499_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
}
}
case 2:
{
lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4563_; 
v_isSharedCheck_4563_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_4563_ == 0)
{
lean_object* v_unused_4564_; 
v_unused_4564_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_4564_);
v___x_4514_ = v_modifier_4414_;
v_isShared_4515_ = v_isSharedCheck_4563_;
goto v_resetjp_4513_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4563_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v_G_4516_; lean_object* v_u_4517_; lean_object* v_Y_4518_; lean_object* v_D_4519_; lean_object* v_M_4520_; lean_object* v_L_4521_; lean_object* v_d_4522_; lean_object* v_Q_4523_; lean_object* v_q_4524_; lean_object* v_w_4525_; lean_object* v_W_4526_; lean_object* v_E_4527_; lean_object* v_e_4528_; lean_object* v_c_4529_; lean_object* v_F_4530_; lean_object* v_a_4531_; lean_object* v_b_4532_; lean_object* v_B_4533_; lean_object* v_h_4534_; lean_object* v_K_4535_; lean_object* v_k_4536_; lean_object* v_H_4537_; lean_object* v_m_4538_; lean_object* v_s_4539_; lean_object* v_S_4540_; lean_object* v_A_4541_; lean_object* v_n_4542_; lean_object* v_N_4543_; lean_object* v_V_4544_; lean_object* v_z_4545_; lean_object* v_zabbrev_4546_; lean_object* v_v_4547_; lean_object* v_O_4548_; lean_object* v_X_4549_; lean_object* v_x_4550_; lean_object* v_Z_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4561_; 
v_G_4516_ = lean_ctor_get(v_date_4413_, 0);
v_u_4517_ = lean_ctor_get(v_date_4413_, 2);
v_Y_4518_ = lean_ctor_get(v_date_4413_, 3);
v_D_4519_ = lean_ctor_get(v_date_4413_, 4);
v_M_4520_ = lean_ctor_get(v_date_4413_, 5);
v_L_4521_ = lean_ctor_get(v_date_4413_, 6);
v_d_4522_ = lean_ctor_get(v_date_4413_, 7);
v_Q_4523_ = lean_ctor_get(v_date_4413_, 8);
v_q_4524_ = lean_ctor_get(v_date_4413_, 9);
v_w_4525_ = lean_ctor_get(v_date_4413_, 10);
v_W_4526_ = lean_ctor_get(v_date_4413_, 11);
v_E_4527_ = lean_ctor_get(v_date_4413_, 12);
v_e_4528_ = lean_ctor_get(v_date_4413_, 13);
v_c_4529_ = lean_ctor_get(v_date_4413_, 14);
v_F_4530_ = lean_ctor_get(v_date_4413_, 15);
v_a_4531_ = lean_ctor_get(v_date_4413_, 16);
v_b_4532_ = lean_ctor_get(v_date_4413_, 17);
v_B_4533_ = lean_ctor_get(v_date_4413_, 18);
v_h_4534_ = lean_ctor_get(v_date_4413_, 19);
v_K_4535_ = lean_ctor_get(v_date_4413_, 20);
v_k_4536_ = lean_ctor_get(v_date_4413_, 21);
v_H_4537_ = lean_ctor_get(v_date_4413_, 22);
v_m_4538_ = lean_ctor_get(v_date_4413_, 23);
v_s_4539_ = lean_ctor_get(v_date_4413_, 24);
v_S_4540_ = lean_ctor_get(v_date_4413_, 25);
v_A_4541_ = lean_ctor_get(v_date_4413_, 26);
v_n_4542_ = lean_ctor_get(v_date_4413_, 27);
v_N_4543_ = lean_ctor_get(v_date_4413_, 28);
v_V_4544_ = lean_ctor_get(v_date_4413_, 29);
v_z_4545_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_4546_ = lean_ctor_get(v_date_4413_, 31);
v_v_4547_ = lean_ctor_get(v_date_4413_, 32);
v_O_4548_ = lean_ctor_get(v_date_4413_, 33);
v_X_4549_ = lean_ctor_get(v_date_4413_, 34);
v_x_4550_ = lean_ctor_get(v_date_4413_, 35);
v_Z_4551_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_4561_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_4561_ == 0)
{
lean_object* v_unused_4562_; 
v_unused_4562_ = lean_ctor_get(v_date_4413_, 1);
lean_dec(v_unused_4562_);
v___x_4553_ = v_date_4413_;
v_isShared_4554_ = v_isSharedCheck_4561_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_Z_4551_);
lean_inc(v_x_4550_);
lean_inc(v_X_4549_);
lean_inc(v_O_4548_);
lean_inc(v_v_4547_);
lean_inc(v_zabbrev_4546_);
lean_inc(v_z_4545_);
lean_inc(v_V_4544_);
lean_inc(v_N_4543_);
lean_inc(v_n_4542_);
lean_inc(v_A_4541_);
lean_inc(v_S_4540_);
lean_inc(v_s_4539_);
lean_inc(v_m_4538_);
lean_inc(v_H_4537_);
lean_inc(v_k_4536_);
lean_inc(v_K_4535_);
lean_inc(v_h_4534_);
lean_inc(v_B_4533_);
lean_inc(v_b_4532_);
lean_inc(v_a_4531_);
lean_inc(v_F_4530_);
lean_inc(v_c_4529_);
lean_inc(v_e_4528_);
lean_inc(v_E_4527_);
lean_inc(v_W_4526_);
lean_inc(v_w_4525_);
lean_inc(v_q_4524_);
lean_inc(v_Q_4523_);
lean_inc(v_d_4522_);
lean_inc(v_L_4521_);
lean_inc(v_M_4520_);
lean_inc(v_D_4519_);
lean_inc(v_Y_4518_);
lean_inc(v_u_4517_);
lean_inc(v_G_4516_);
lean_dec(v_date_4413_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4561_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4515_ == 0)
{
lean_ctor_set_tag(v___x_4514_, 1);
lean_ctor_set(v___x_4514_, 0, v_data_4415_);
v___x_4556_ = v___x_4514_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_data_4415_);
v___x_4556_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
lean_object* v___x_4558_; 
if (v_isShared_4554_ == 0)
{
lean_ctor_set(v___x_4553_, 1, v___x_4556_);
v___x_4558_ = v___x_4553_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_G_4516_);
lean_ctor_set(v_reuseFailAlloc_4559_, 1, v___x_4556_);
lean_ctor_set(v_reuseFailAlloc_4559_, 2, v_u_4517_);
lean_ctor_set(v_reuseFailAlloc_4559_, 3, v_Y_4518_);
lean_ctor_set(v_reuseFailAlloc_4559_, 4, v_D_4519_);
lean_ctor_set(v_reuseFailAlloc_4559_, 5, v_M_4520_);
lean_ctor_set(v_reuseFailAlloc_4559_, 6, v_L_4521_);
lean_ctor_set(v_reuseFailAlloc_4559_, 7, v_d_4522_);
lean_ctor_set(v_reuseFailAlloc_4559_, 8, v_Q_4523_);
lean_ctor_set(v_reuseFailAlloc_4559_, 9, v_q_4524_);
lean_ctor_set(v_reuseFailAlloc_4559_, 10, v_w_4525_);
lean_ctor_set(v_reuseFailAlloc_4559_, 11, v_W_4526_);
lean_ctor_set(v_reuseFailAlloc_4559_, 12, v_E_4527_);
lean_ctor_set(v_reuseFailAlloc_4559_, 13, v_e_4528_);
lean_ctor_set(v_reuseFailAlloc_4559_, 14, v_c_4529_);
lean_ctor_set(v_reuseFailAlloc_4559_, 15, v_F_4530_);
lean_ctor_set(v_reuseFailAlloc_4559_, 16, v_a_4531_);
lean_ctor_set(v_reuseFailAlloc_4559_, 17, v_b_4532_);
lean_ctor_set(v_reuseFailAlloc_4559_, 18, v_B_4533_);
lean_ctor_set(v_reuseFailAlloc_4559_, 19, v_h_4534_);
lean_ctor_set(v_reuseFailAlloc_4559_, 20, v_K_4535_);
lean_ctor_set(v_reuseFailAlloc_4559_, 21, v_k_4536_);
lean_ctor_set(v_reuseFailAlloc_4559_, 22, v_H_4537_);
lean_ctor_set(v_reuseFailAlloc_4559_, 23, v_m_4538_);
lean_ctor_set(v_reuseFailAlloc_4559_, 24, v_s_4539_);
lean_ctor_set(v_reuseFailAlloc_4559_, 25, v_S_4540_);
lean_ctor_set(v_reuseFailAlloc_4559_, 26, v_A_4541_);
lean_ctor_set(v_reuseFailAlloc_4559_, 27, v_n_4542_);
lean_ctor_set(v_reuseFailAlloc_4559_, 28, v_N_4543_);
lean_ctor_set(v_reuseFailAlloc_4559_, 29, v_V_4544_);
lean_ctor_set(v_reuseFailAlloc_4559_, 30, v_z_4545_);
lean_ctor_set(v_reuseFailAlloc_4559_, 31, v_zabbrev_4546_);
lean_ctor_set(v_reuseFailAlloc_4559_, 32, v_v_4547_);
lean_ctor_set(v_reuseFailAlloc_4559_, 33, v_O_4548_);
lean_ctor_set(v_reuseFailAlloc_4559_, 34, v_X_4549_);
lean_ctor_set(v_reuseFailAlloc_4559_, 35, v_x_4550_);
lean_ctor_set(v_reuseFailAlloc_4559_, 36, v_Z_4551_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
}
}
case 3:
{
lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4615_; 
v_isSharedCheck_4615_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_4615_ == 0)
{
lean_object* v_unused_4616_; 
v_unused_4616_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_4616_);
v___x_4566_ = v_modifier_4414_;
v_isShared_4567_ = v_isSharedCheck_4615_;
goto v_resetjp_4565_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4615_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v_G_4568_; lean_object* v_y_4569_; lean_object* v_u_4570_; lean_object* v_Y_4571_; lean_object* v_M_4572_; lean_object* v_L_4573_; lean_object* v_d_4574_; lean_object* v_Q_4575_; lean_object* v_q_4576_; lean_object* v_w_4577_; lean_object* v_W_4578_; lean_object* v_E_4579_; lean_object* v_e_4580_; lean_object* v_c_4581_; lean_object* v_F_4582_; lean_object* v_a_4583_; lean_object* v_b_4584_; lean_object* v_B_4585_; lean_object* v_h_4586_; lean_object* v_K_4587_; lean_object* v_k_4588_; lean_object* v_H_4589_; lean_object* v_m_4590_; lean_object* v_s_4591_; lean_object* v_S_4592_; lean_object* v_A_4593_; lean_object* v_n_4594_; lean_object* v_N_4595_; lean_object* v_V_4596_; lean_object* v_z_4597_; lean_object* v_zabbrev_4598_; lean_object* v_v_4599_; lean_object* v_O_4600_; lean_object* v_X_4601_; lean_object* v_x_4602_; lean_object* v_Z_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4613_; 
v_G_4568_ = lean_ctor_get(v_date_4413_, 0);
v_y_4569_ = lean_ctor_get(v_date_4413_, 1);
v_u_4570_ = lean_ctor_get(v_date_4413_, 2);
v_Y_4571_ = lean_ctor_get(v_date_4413_, 3);
v_M_4572_ = lean_ctor_get(v_date_4413_, 5);
v_L_4573_ = lean_ctor_get(v_date_4413_, 6);
v_d_4574_ = lean_ctor_get(v_date_4413_, 7);
v_Q_4575_ = lean_ctor_get(v_date_4413_, 8);
v_q_4576_ = lean_ctor_get(v_date_4413_, 9);
v_w_4577_ = lean_ctor_get(v_date_4413_, 10);
v_W_4578_ = lean_ctor_get(v_date_4413_, 11);
v_E_4579_ = lean_ctor_get(v_date_4413_, 12);
v_e_4580_ = lean_ctor_get(v_date_4413_, 13);
v_c_4581_ = lean_ctor_get(v_date_4413_, 14);
v_F_4582_ = lean_ctor_get(v_date_4413_, 15);
v_a_4583_ = lean_ctor_get(v_date_4413_, 16);
v_b_4584_ = lean_ctor_get(v_date_4413_, 17);
v_B_4585_ = lean_ctor_get(v_date_4413_, 18);
v_h_4586_ = lean_ctor_get(v_date_4413_, 19);
v_K_4587_ = lean_ctor_get(v_date_4413_, 20);
v_k_4588_ = lean_ctor_get(v_date_4413_, 21);
v_H_4589_ = lean_ctor_get(v_date_4413_, 22);
v_m_4590_ = lean_ctor_get(v_date_4413_, 23);
v_s_4591_ = lean_ctor_get(v_date_4413_, 24);
v_S_4592_ = lean_ctor_get(v_date_4413_, 25);
v_A_4593_ = lean_ctor_get(v_date_4413_, 26);
v_n_4594_ = lean_ctor_get(v_date_4413_, 27);
v_N_4595_ = lean_ctor_get(v_date_4413_, 28);
v_V_4596_ = lean_ctor_get(v_date_4413_, 29);
v_z_4597_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_4598_ = lean_ctor_get(v_date_4413_, 31);
v_v_4599_ = lean_ctor_get(v_date_4413_, 32);
v_O_4600_ = lean_ctor_get(v_date_4413_, 33);
v_X_4601_ = lean_ctor_get(v_date_4413_, 34);
v_x_4602_ = lean_ctor_get(v_date_4413_, 35);
v_Z_4603_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_4613_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_4613_ == 0)
{
lean_object* v_unused_4614_; 
v_unused_4614_ = lean_ctor_get(v_date_4413_, 4);
lean_dec(v_unused_4614_);
v___x_4605_ = v_date_4413_;
v_isShared_4606_ = v_isSharedCheck_4613_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_Z_4603_);
lean_inc(v_x_4602_);
lean_inc(v_X_4601_);
lean_inc(v_O_4600_);
lean_inc(v_v_4599_);
lean_inc(v_zabbrev_4598_);
lean_inc(v_z_4597_);
lean_inc(v_V_4596_);
lean_inc(v_N_4595_);
lean_inc(v_n_4594_);
lean_inc(v_A_4593_);
lean_inc(v_S_4592_);
lean_inc(v_s_4591_);
lean_inc(v_m_4590_);
lean_inc(v_H_4589_);
lean_inc(v_k_4588_);
lean_inc(v_K_4587_);
lean_inc(v_h_4586_);
lean_inc(v_B_4585_);
lean_inc(v_b_4584_);
lean_inc(v_a_4583_);
lean_inc(v_F_4582_);
lean_inc(v_c_4581_);
lean_inc(v_e_4580_);
lean_inc(v_E_4579_);
lean_inc(v_W_4578_);
lean_inc(v_w_4577_);
lean_inc(v_q_4576_);
lean_inc(v_Q_4575_);
lean_inc(v_d_4574_);
lean_inc(v_L_4573_);
lean_inc(v_M_4572_);
lean_inc(v_Y_4571_);
lean_inc(v_u_4570_);
lean_inc(v_y_4569_);
lean_inc(v_G_4568_);
lean_dec(v_date_4413_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4613_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4608_; 
if (v_isShared_4567_ == 0)
{
lean_ctor_set_tag(v___x_4566_, 1);
lean_ctor_set(v___x_4566_, 0, v_data_4415_);
v___x_4608_ = v___x_4566_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_data_4415_);
v___x_4608_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
lean_object* v___x_4610_; 
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 4, v___x_4608_);
v___x_4610_ = v___x_4605_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_G_4568_);
lean_ctor_set(v_reuseFailAlloc_4611_, 1, v_y_4569_);
lean_ctor_set(v_reuseFailAlloc_4611_, 2, v_u_4570_);
lean_ctor_set(v_reuseFailAlloc_4611_, 3, v_Y_4571_);
lean_ctor_set(v_reuseFailAlloc_4611_, 4, v___x_4608_);
lean_ctor_set(v_reuseFailAlloc_4611_, 5, v_M_4572_);
lean_ctor_set(v_reuseFailAlloc_4611_, 6, v_L_4573_);
lean_ctor_set(v_reuseFailAlloc_4611_, 7, v_d_4574_);
lean_ctor_set(v_reuseFailAlloc_4611_, 8, v_Q_4575_);
lean_ctor_set(v_reuseFailAlloc_4611_, 9, v_q_4576_);
lean_ctor_set(v_reuseFailAlloc_4611_, 10, v_w_4577_);
lean_ctor_set(v_reuseFailAlloc_4611_, 11, v_W_4578_);
lean_ctor_set(v_reuseFailAlloc_4611_, 12, v_E_4579_);
lean_ctor_set(v_reuseFailAlloc_4611_, 13, v_e_4580_);
lean_ctor_set(v_reuseFailAlloc_4611_, 14, v_c_4581_);
lean_ctor_set(v_reuseFailAlloc_4611_, 15, v_F_4582_);
lean_ctor_set(v_reuseFailAlloc_4611_, 16, v_a_4583_);
lean_ctor_set(v_reuseFailAlloc_4611_, 17, v_b_4584_);
lean_ctor_set(v_reuseFailAlloc_4611_, 18, v_B_4585_);
lean_ctor_set(v_reuseFailAlloc_4611_, 19, v_h_4586_);
lean_ctor_set(v_reuseFailAlloc_4611_, 20, v_K_4587_);
lean_ctor_set(v_reuseFailAlloc_4611_, 21, v_k_4588_);
lean_ctor_set(v_reuseFailAlloc_4611_, 22, v_H_4589_);
lean_ctor_set(v_reuseFailAlloc_4611_, 23, v_m_4590_);
lean_ctor_set(v_reuseFailAlloc_4611_, 24, v_s_4591_);
lean_ctor_set(v_reuseFailAlloc_4611_, 25, v_S_4592_);
lean_ctor_set(v_reuseFailAlloc_4611_, 26, v_A_4593_);
lean_ctor_set(v_reuseFailAlloc_4611_, 27, v_n_4594_);
lean_ctor_set(v_reuseFailAlloc_4611_, 28, v_N_4595_);
lean_ctor_set(v_reuseFailAlloc_4611_, 29, v_V_4596_);
lean_ctor_set(v_reuseFailAlloc_4611_, 30, v_z_4597_);
lean_ctor_set(v_reuseFailAlloc_4611_, 31, v_zabbrev_4598_);
lean_ctor_set(v_reuseFailAlloc_4611_, 32, v_v_4599_);
lean_ctor_set(v_reuseFailAlloc_4611_, 33, v_O_4600_);
lean_ctor_set(v_reuseFailAlloc_4611_, 34, v_X_4601_);
lean_ctor_set(v_reuseFailAlloc_4611_, 35, v_x_4602_);
lean_ctor_set(v_reuseFailAlloc_4611_, 36, v_Z_4603_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
return v___x_4610_;
}
}
}
}
}
case 4:
{
lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4667_; 
v_isSharedCheck_4667_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_4667_ == 0)
{
lean_object* v_unused_4668_; 
v_unused_4668_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_4668_);
v___x_4618_ = v_modifier_4414_;
v_isShared_4619_ = v_isSharedCheck_4667_;
goto v_resetjp_4617_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4667_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v_G_4620_; lean_object* v_y_4621_; lean_object* v_u_4622_; lean_object* v_Y_4623_; lean_object* v_D_4624_; lean_object* v_L_4625_; lean_object* v_d_4626_; lean_object* v_Q_4627_; lean_object* v_q_4628_; lean_object* v_w_4629_; lean_object* v_W_4630_; lean_object* v_E_4631_; lean_object* v_e_4632_; lean_object* v_c_4633_; lean_object* v_F_4634_; lean_object* v_a_4635_; lean_object* v_b_4636_; lean_object* v_B_4637_; lean_object* v_h_4638_; lean_object* v_K_4639_; lean_object* v_k_4640_; lean_object* v_H_4641_; lean_object* v_m_4642_; lean_object* v_s_4643_; lean_object* v_S_4644_; lean_object* v_A_4645_; lean_object* v_n_4646_; lean_object* v_N_4647_; lean_object* v_V_4648_; lean_object* v_z_4649_; lean_object* v_zabbrev_4650_; lean_object* v_v_4651_; lean_object* v_O_4652_; lean_object* v_X_4653_; lean_object* v_x_4654_; lean_object* v_Z_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4665_; 
v_G_4620_ = lean_ctor_get(v_date_4413_, 0);
v_y_4621_ = lean_ctor_get(v_date_4413_, 1);
v_u_4622_ = lean_ctor_get(v_date_4413_, 2);
v_Y_4623_ = lean_ctor_get(v_date_4413_, 3);
v_D_4624_ = lean_ctor_get(v_date_4413_, 4);
v_L_4625_ = lean_ctor_get(v_date_4413_, 6);
v_d_4626_ = lean_ctor_get(v_date_4413_, 7);
v_Q_4627_ = lean_ctor_get(v_date_4413_, 8);
v_q_4628_ = lean_ctor_get(v_date_4413_, 9);
v_w_4629_ = lean_ctor_get(v_date_4413_, 10);
v_W_4630_ = lean_ctor_get(v_date_4413_, 11);
v_E_4631_ = lean_ctor_get(v_date_4413_, 12);
v_e_4632_ = lean_ctor_get(v_date_4413_, 13);
v_c_4633_ = lean_ctor_get(v_date_4413_, 14);
v_F_4634_ = lean_ctor_get(v_date_4413_, 15);
v_a_4635_ = lean_ctor_get(v_date_4413_, 16);
v_b_4636_ = lean_ctor_get(v_date_4413_, 17);
v_B_4637_ = lean_ctor_get(v_date_4413_, 18);
v_h_4638_ = lean_ctor_get(v_date_4413_, 19);
v_K_4639_ = lean_ctor_get(v_date_4413_, 20);
v_k_4640_ = lean_ctor_get(v_date_4413_, 21);
v_H_4641_ = lean_ctor_get(v_date_4413_, 22);
v_m_4642_ = lean_ctor_get(v_date_4413_, 23);
v_s_4643_ = lean_ctor_get(v_date_4413_, 24);
v_S_4644_ = lean_ctor_get(v_date_4413_, 25);
v_A_4645_ = lean_ctor_get(v_date_4413_, 26);
v_n_4646_ = lean_ctor_get(v_date_4413_, 27);
v_N_4647_ = lean_ctor_get(v_date_4413_, 28);
v_V_4648_ = lean_ctor_get(v_date_4413_, 29);
v_z_4649_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_4650_ = lean_ctor_get(v_date_4413_, 31);
v_v_4651_ = lean_ctor_get(v_date_4413_, 32);
v_O_4652_ = lean_ctor_get(v_date_4413_, 33);
v_X_4653_ = lean_ctor_get(v_date_4413_, 34);
v_x_4654_ = lean_ctor_get(v_date_4413_, 35);
v_Z_4655_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_4665_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_4665_ == 0)
{
lean_object* v_unused_4666_; 
v_unused_4666_ = lean_ctor_get(v_date_4413_, 5);
lean_dec(v_unused_4666_);
v___x_4657_ = v_date_4413_;
v_isShared_4658_ = v_isSharedCheck_4665_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_Z_4655_);
lean_inc(v_x_4654_);
lean_inc(v_X_4653_);
lean_inc(v_O_4652_);
lean_inc(v_v_4651_);
lean_inc(v_zabbrev_4650_);
lean_inc(v_z_4649_);
lean_inc(v_V_4648_);
lean_inc(v_N_4647_);
lean_inc(v_n_4646_);
lean_inc(v_A_4645_);
lean_inc(v_S_4644_);
lean_inc(v_s_4643_);
lean_inc(v_m_4642_);
lean_inc(v_H_4641_);
lean_inc(v_k_4640_);
lean_inc(v_K_4639_);
lean_inc(v_h_4638_);
lean_inc(v_B_4637_);
lean_inc(v_b_4636_);
lean_inc(v_a_4635_);
lean_inc(v_F_4634_);
lean_inc(v_c_4633_);
lean_inc(v_e_4632_);
lean_inc(v_E_4631_);
lean_inc(v_W_4630_);
lean_inc(v_w_4629_);
lean_inc(v_q_4628_);
lean_inc(v_Q_4627_);
lean_inc(v_d_4626_);
lean_inc(v_L_4625_);
lean_inc(v_D_4624_);
lean_inc(v_Y_4623_);
lean_inc(v_u_4622_);
lean_inc(v_y_4621_);
lean_inc(v_G_4620_);
lean_dec(v_date_4413_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4665_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v___x_4660_; 
if (v_isShared_4619_ == 0)
{
lean_ctor_set_tag(v___x_4618_, 1);
lean_ctor_set(v___x_4618_, 0, v_data_4415_);
v___x_4660_ = v___x_4618_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_data_4415_);
v___x_4660_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
lean_object* v___x_4662_; 
if (v_isShared_4658_ == 0)
{
lean_ctor_set(v___x_4657_, 5, v___x_4660_);
v___x_4662_ = v___x_4657_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_G_4620_);
lean_ctor_set(v_reuseFailAlloc_4663_, 1, v_y_4621_);
lean_ctor_set(v_reuseFailAlloc_4663_, 2, v_u_4622_);
lean_ctor_set(v_reuseFailAlloc_4663_, 3, v_Y_4623_);
lean_ctor_set(v_reuseFailAlloc_4663_, 4, v_D_4624_);
lean_ctor_set(v_reuseFailAlloc_4663_, 5, v___x_4660_);
lean_ctor_set(v_reuseFailAlloc_4663_, 6, v_L_4625_);
lean_ctor_set(v_reuseFailAlloc_4663_, 7, v_d_4626_);
lean_ctor_set(v_reuseFailAlloc_4663_, 8, v_Q_4627_);
lean_ctor_set(v_reuseFailAlloc_4663_, 9, v_q_4628_);
lean_ctor_set(v_reuseFailAlloc_4663_, 10, v_w_4629_);
lean_ctor_set(v_reuseFailAlloc_4663_, 11, v_W_4630_);
lean_ctor_set(v_reuseFailAlloc_4663_, 12, v_E_4631_);
lean_ctor_set(v_reuseFailAlloc_4663_, 13, v_e_4632_);
lean_ctor_set(v_reuseFailAlloc_4663_, 14, v_c_4633_);
lean_ctor_set(v_reuseFailAlloc_4663_, 15, v_F_4634_);
lean_ctor_set(v_reuseFailAlloc_4663_, 16, v_a_4635_);
lean_ctor_set(v_reuseFailAlloc_4663_, 17, v_b_4636_);
lean_ctor_set(v_reuseFailAlloc_4663_, 18, v_B_4637_);
lean_ctor_set(v_reuseFailAlloc_4663_, 19, v_h_4638_);
lean_ctor_set(v_reuseFailAlloc_4663_, 20, v_K_4639_);
lean_ctor_set(v_reuseFailAlloc_4663_, 21, v_k_4640_);
lean_ctor_set(v_reuseFailAlloc_4663_, 22, v_H_4641_);
lean_ctor_set(v_reuseFailAlloc_4663_, 23, v_m_4642_);
lean_ctor_set(v_reuseFailAlloc_4663_, 24, v_s_4643_);
lean_ctor_set(v_reuseFailAlloc_4663_, 25, v_S_4644_);
lean_ctor_set(v_reuseFailAlloc_4663_, 26, v_A_4645_);
lean_ctor_set(v_reuseFailAlloc_4663_, 27, v_n_4646_);
lean_ctor_set(v_reuseFailAlloc_4663_, 28, v_N_4647_);
lean_ctor_set(v_reuseFailAlloc_4663_, 29, v_V_4648_);
lean_ctor_set(v_reuseFailAlloc_4663_, 30, v_z_4649_);
lean_ctor_set(v_reuseFailAlloc_4663_, 31, v_zabbrev_4650_);
lean_ctor_set(v_reuseFailAlloc_4663_, 32, v_v_4651_);
lean_ctor_set(v_reuseFailAlloc_4663_, 33, v_O_4652_);
lean_ctor_set(v_reuseFailAlloc_4663_, 34, v_X_4653_);
lean_ctor_set(v_reuseFailAlloc_4663_, 35, v_x_4654_);
lean_ctor_set(v_reuseFailAlloc_4663_, 36, v_Z_4655_);
v___x_4662_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
return v___x_4662_;
}
}
}
}
}
case 5:
{
lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4719_; 
v_isSharedCheck_4719_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_4719_ == 0)
{
lean_object* v_unused_4720_; 
v_unused_4720_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_4720_);
v___x_4670_ = v_modifier_4414_;
v_isShared_4671_ = v_isSharedCheck_4719_;
goto v_resetjp_4669_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4719_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v_G_4672_; lean_object* v_y_4673_; lean_object* v_u_4674_; lean_object* v_Y_4675_; lean_object* v_D_4676_; lean_object* v_M_4677_; lean_object* v_d_4678_; lean_object* v_Q_4679_; lean_object* v_q_4680_; lean_object* v_w_4681_; lean_object* v_W_4682_; lean_object* v_E_4683_; lean_object* v_e_4684_; lean_object* v_c_4685_; lean_object* v_F_4686_; lean_object* v_a_4687_; lean_object* v_b_4688_; lean_object* v_B_4689_; lean_object* v_h_4690_; lean_object* v_K_4691_; lean_object* v_k_4692_; lean_object* v_H_4693_; lean_object* v_m_4694_; lean_object* v_s_4695_; lean_object* v_S_4696_; lean_object* v_A_4697_; lean_object* v_n_4698_; lean_object* v_N_4699_; lean_object* v_V_4700_; lean_object* v_z_4701_; lean_object* v_zabbrev_4702_; lean_object* v_v_4703_; lean_object* v_O_4704_; lean_object* v_X_4705_; lean_object* v_x_4706_; lean_object* v_Z_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4717_; 
v_G_4672_ = lean_ctor_get(v_date_4413_, 0);
v_y_4673_ = lean_ctor_get(v_date_4413_, 1);
v_u_4674_ = lean_ctor_get(v_date_4413_, 2);
v_Y_4675_ = lean_ctor_get(v_date_4413_, 3);
v_D_4676_ = lean_ctor_get(v_date_4413_, 4);
v_M_4677_ = lean_ctor_get(v_date_4413_, 5);
v_d_4678_ = lean_ctor_get(v_date_4413_, 7);
v_Q_4679_ = lean_ctor_get(v_date_4413_, 8);
v_q_4680_ = lean_ctor_get(v_date_4413_, 9);
v_w_4681_ = lean_ctor_get(v_date_4413_, 10);
v_W_4682_ = lean_ctor_get(v_date_4413_, 11);
v_E_4683_ = lean_ctor_get(v_date_4413_, 12);
v_e_4684_ = lean_ctor_get(v_date_4413_, 13);
v_c_4685_ = lean_ctor_get(v_date_4413_, 14);
v_F_4686_ = lean_ctor_get(v_date_4413_, 15);
v_a_4687_ = lean_ctor_get(v_date_4413_, 16);
v_b_4688_ = lean_ctor_get(v_date_4413_, 17);
v_B_4689_ = lean_ctor_get(v_date_4413_, 18);
v_h_4690_ = lean_ctor_get(v_date_4413_, 19);
v_K_4691_ = lean_ctor_get(v_date_4413_, 20);
v_k_4692_ = lean_ctor_get(v_date_4413_, 21);
v_H_4693_ = lean_ctor_get(v_date_4413_, 22);
v_m_4694_ = lean_ctor_get(v_date_4413_, 23);
v_s_4695_ = lean_ctor_get(v_date_4413_, 24);
v_S_4696_ = lean_ctor_get(v_date_4413_, 25);
v_A_4697_ = lean_ctor_get(v_date_4413_, 26);
v_n_4698_ = lean_ctor_get(v_date_4413_, 27);
v_N_4699_ = lean_ctor_get(v_date_4413_, 28);
v_V_4700_ = lean_ctor_get(v_date_4413_, 29);
v_z_4701_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_4702_ = lean_ctor_get(v_date_4413_, 31);
v_v_4703_ = lean_ctor_get(v_date_4413_, 32);
v_O_4704_ = lean_ctor_get(v_date_4413_, 33);
v_X_4705_ = lean_ctor_get(v_date_4413_, 34);
v_x_4706_ = lean_ctor_get(v_date_4413_, 35);
v_Z_4707_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_4717_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_4717_ == 0)
{
lean_object* v_unused_4718_; 
v_unused_4718_ = lean_ctor_get(v_date_4413_, 6);
lean_dec(v_unused_4718_);
v___x_4709_ = v_date_4413_;
v_isShared_4710_ = v_isSharedCheck_4717_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_Z_4707_);
lean_inc(v_x_4706_);
lean_inc(v_X_4705_);
lean_inc(v_O_4704_);
lean_inc(v_v_4703_);
lean_inc(v_zabbrev_4702_);
lean_inc(v_z_4701_);
lean_inc(v_V_4700_);
lean_inc(v_N_4699_);
lean_inc(v_n_4698_);
lean_inc(v_A_4697_);
lean_inc(v_S_4696_);
lean_inc(v_s_4695_);
lean_inc(v_m_4694_);
lean_inc(v_H_4693_);
lean_inc(v_k_4692_);
lean_inc(v_K_4691_);
lean_inc(v_h_4690_);
lean_inc(v_B_4689_);
lean_inc(v_b_4688_);
lean_inc(v_a_4687_);
lean_inc(v_F_4686_);
lean_inc(v_c_4685_);
lean_inc(v_e_4684_);
lean_inc(v_E_4683_);
lean_inc(v_W_4682_);
lean_inc(v_w_4681_);
lean_inc(v_q_4680_);
lean_inc(v_Q_4679_);
lean_inc(v_d_4678_);
lean_inc(v_M_4677_);
lean_inc(v_D_4676_);
lean_inc(v_Y_4675_);
lean_inc(v_u_4674_);
lean_inc(v_y_4673_);
lean_inc(v_G_4672_);
lean_dec(v_date_4413_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4717_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v___x_4712_; 
if (v_isShared_4671_ == 0)
{
lean_ctor_set_tag(v___x_4670_, 1);
lean_ctor_set(v___x_4670_, 0, v_data_4415_);
v___x_4712_ = v___x_4670_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_data_4415_);
v___x_4712_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
lean_object* v___x_4714_; 
if (v_isShared_4710_ == 0)
{
lean_ctor_set(v___x_4709_, 6, v___x_4712_);
v___x_4714_ = v___x_4709_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v_G_4672_);
lean_ctor_set(v_reuseFailAlloc_4715_, 1, v_y_4673_);
lean_ctor_set(v_reuseFailAlloc_4715_, 2, v_u_4674_);
lean_ctor_set(v_reuseFailAlloc_4715_, 3, v_Y_4675_);
lean_ctor_set(v_reuseFailAlloc_4715_, 4, v_D_4676_);
lean_ctor_set(v_reuseFailAlloc_4715_, 5, v_M_4677_);
lean_ctor_set(v_reuseFailAlloc_4715_, 6, v___x_4712_);
lean_ctor_set(v_reuseFailAlloc_4715_, 7, v_d_4678_);
lean_ctor_set(v_reuseFailAlloc_4715_, 8, v_Q_4679_);
lean_ctor_set(v_reuseFailAlloc_4715_, 9, v_q_4680_);
lean_ctor_set(v_reuseFailAlloc_4715_, 10, v_w_4681_);
lean_ctor_set(v_reuseFailAlloc_4715_, 11, v_W_4682_);
lean_ctor_set(v_reuseFailAlloc_4715_, 12, v_E_4683_);
lean_ctor_set(v_reuseFailAlloc_4715_, 13, v_e_4684_);
lean_ctor_set(v_reuseFailAlloc_4715_, 14, v_c_4685_);
lean_ctor_set(v_reuseFailAlloc_4715_, 15, v_F_4686_);
lean_ctor_set(v_reuseFailAlloc_4715_, 16, v_a_4687_);
lean_ctor_set(v_reuseFailAlloc_4715_, 17, v_b_4688_);
lean_ctor_set(v_reuseFailAlloc_4715_, 18, v_B_4689_);
lean_ctor_set(v_reuseFailAlloc_4715_, 19, v_h_4690_);
lean_ctor_set(v_reuseFailAlloc_4715_, 20, v_K_4691_);
lean_ctor_set(v_reuseFailAlloc_4715_, 21, v_k_4692_);
lean_ctor_set(v_reuseFailAlloc_4715_, 22, v_H_4693_);
lean_ctor_set(v_reuseFailAlloc_4715_, 23, v_m_4694_);
lean_ctor_set(v_reuseFailAlloc_4715_, 24, v_s_4695_);
lean_ctor_set(v_reuseFailAlloc_4715_, 25, v_S_4696_);
lean_ctor_set(v_reuseFailAlloc_4715_, 26, v_A_4697_);
lean_ctor_set(v_reuseFailAlloc_4715_, 27, v_n_4698_);
lean_ctor_set(v_reuseFailAlloc_4715_, 28, v_N_4699_);
lean_ctor_set(v_reuseFailAlloc_4715_, 29, v_V_4700_);
lean_ctor_set(v_reuseFailAlloc_4715_, 30, v_z_4701_);
lean_ctor_set(v_reuseFailAlloc_4715_, 31, v_zabbrev_4702_);
lean_ctor_set(v_reuseFailAlloc_4715_, 32, v_v_4703_);
lean_ctor_set(v_reuseFailAlloc_4715_, 33, v_O_4704_);
lean_ctor_set(v_reuseFailAlloc_4715_, 34, v_X_4705_);
lean_ctor_set(v_reuseFailAlloc_4715_, 35, v_x_4706_);
lean_ctor_set(v_reuseFailAlloc_4715_, 36, v_Z_4707_);
v___x_4714_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
return v___x_4714_;
}
}
}
}
}
case 6:
{
lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4771_; 
v_isSharedCheck_4771_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_4771_ == 0)
{
lean_object* v_unused_4772_; 
v_unused_4772_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_4772_);
v___x_4722_ = v_modifier_4414_;
v_isShared_4723_ = v_isSharedCheck_4771_;
goto v_resetjp_4721_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4771_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v_G_4724_; lean_object* v_y_4725_; lean_object* v_u_4726_; lean_object* v_Y_4727_; lean_object* v_D_4728_; lean_object* v_M_4729_; lean_object* v_L_4730_; lean_object* v_Q_4731_; lean_object* v_q_4732_; lean_object* v_w_4733_; lean_object* v_W_4734_; lean_object* v_E_4735_; lean_object* v_e_4736_; lean_object* v_c_4737_; lean_object* v_F_4738_; lean_object* v_a_4739_; lean_object* v_b_4740_; lean_object* v_B_4741_; lean_object* v_h_4742_; lean_object* v_K_4743_; lean_object* v_k_4744_; lean_object* v_H_4745_; lean_object* v_m_4746_; lean_object* v_s_4747_; lean_object* v_S_4748_; lean_object* v_A_4749_; lean_object* v_n_4750_; lean_object* v_N_4751_; lean_object* v_V_4752_; lean_object* v_z_4753_; lean_object* v_zabbrev_4754_; lean_object* v_v_4755_; lean_object* v_O_4756_; lean_object* v_X_4757_; lean_object* v_x_4758_; lean_object* v_Z_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4769_; 
v_G_4724_ = lean_ctor_get(v_date_4413_, 0);
v_y_4725_ = lean_ctor_get(v_date_4413_, 1);
v_u_4726_ = lean_ctor_get(v_date_4413_, 2);
v_Y_4727_ = lean_ctor_get(v_date_4413_, 3);
v_D_4728_ = lean_ctor_get(v_date_4413_, 4);
v_M_4729_ = lean_ctor_get(v_date_4413_, 5);
v_L_4730_ = lean_ctor_get(v_date_4413_, 6);
v_Q_4731_ = lean_ctor_get(v_date_4413_, 8);
v_q_4732_ = lean_ctor_get(v_date_4413_, 9);
v_w_4733_ = lean_ctor_get(v_date_4413_, 10);
v_W_4734_ = lean_ctor_get(v_date_4413_, 11);
v_E_4735_ = lean_ctor_get(v_date_4413_, 12);
v_e_4736_ = lean_ctor_get(v_date_4413_, 13);
v_c_4737_ = lean_ctor_get(v_date_4413_, 14);
v_F_4738_ = lean_ctor_get(v_date_4413_, 15);
v_a_4739_ = lean_ctor_get(v_date_4413_, 16);
v_b_4740_ = lean_ctor_get(v_date_4413_, 17);
v_B_4741_ = lean_ctor_get(v_date_4413_, 18);
v_h_4742_ = lean_ctor_get(v_date_4413_, 19);
v_K_4743_ = lean_ctor_get(v_date_4413_, 20);
v_k_4744_ = lean_ctor_get(v_date_4413_, 21);
v_H_4745_ = lean_ctor_get(v_date_4413_, 22);
v_m_4746_ = lean_ctor_get(v_date_4413_, 23);
v_s_4747_ = lean_ctor_get(v_date_4413_, 24);
v_S_4748_ = lean_ctor_get(v_date_4413_, 25);
v_A_4749_ = lean_ctor_get(v_date_4413_, 26);
v_n_4750_ = lean_ctor_get(v_date_4413_, 27);
v_N_4751_ = lean_ctor_get(v_date_4413_, 28);
v_V_4752_ = lean_ctor_get(v_date_4413_, 29);
v_z_4753_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_4754_ = lean_ctor_get(v_date_4413_, 31);
v_v_4755_ = lean_ctor_get(v_date_4413_, 32);
v_O_4756_ = lean_ctor_get(v_date_4413_, 33);
v_X_4757_ = lean_ctor_get(v_date_4413_, 34);
v_x_4758_ = lean_ctor_get(v_date_4413_, 35);
v_Z_4759_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_4769_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_4769_ == 0)
{
lean_object* v_unused_4770_; 
v_unused_4770_ = lean_ctor_get(v_date_4413_, 7);
lean_dec(v_unused_4770_);
v___x_4761_ = v_date_4413_;
v_isShared_4762_ = v_isSharedCheck_4769_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_Z_4759_);
lean_inc(v_x_4758_);
lean_inc(v_X_4757_);
lean_inc(v_O_4756_);
lean_inc(v_v_4755_);
lean_inc(v_zabbrev_4754_);
lean_inc(v_z_4753_);
lean_inc(v_V_4752_);
lean_inc(v_N_4751_);
lean_inc(v_n_4750_);
lean_inc(v_A_4749_);
lean_inc(v_S_4748_);
lean_inc(v_s_4747_);
lean_inc(v_m_4746_);
lean_inc(v_H_4745_);
lean_inc(v_k_4744_);
lean_inc(v_K_4743_);
lean_inc(v_h_4742_);
lean_inc(v_B_4741_);
lean_inc(v_b_4740_);
lean_inc(v_a_4739_);
lean_inc(v_F_4738_);
lean_inc(v_c_4737_);
lean_inc(v_e_4736_);
lean_inc(v_E_4735_);
lean_inc(v_W_4734_);
lean_inc(v_w_4733_);
lean_inc(v_q_4732_);
lean_inc(v_Q_4731_);
lean_inc(v_L_4730_);
lean_inc(v_M_4729_);
lean_inc(v_D_4728_);
lean_inc(v_Y_4727_);
lean_inc(v_u_4726_);
lean_inc(v_y_4725_);
lean_inc(v_G_4724_);
lean_dec(v_date_4413_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4769_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v___x_4764_; 
if (v_isShared_4723_ == 0)
{
lean_ctor_set_tag(v___x_4722_, 1);
lean_ctor_set(v___x_4722_, 0, v_data_4415_);
v___x_4764_ = v___x_4722_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v_data_4415_);
v___x_4764_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
lean_object* v___x_4766_; 
if (v_isShared_4762_ == 0)
{
lean_ctor_set(v___x_4761_, 7, v___x_4764_);
v___x_4766_ = v___x_4761_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_G_4724_);
lean_ctor_set(v_reuseFailAlloc_4767_, 1, v_y_4725_);
lean_ctor_set(v_reuseFailAlloc_4767_, 2, v_u_4726_);
lean_ctor_set(v_reuseFailAlloc_4767_, 3, v_Y_4727_);
lean_ctor_set(v_reuseFailAlloc_4767_, 4, v_D_4728_);
lean_ctor_set(v_reuseFailAlloc_4767_, 5, v_M_4729_);
lean_ctor_set(v_reuseFailAlloc_4767_, 6, v_L_4730_);
lean_ctor_set(v_reuseFailAlloc_4767_, 7, v___x_4764_);
lean_ctor_set(v_reuseFailAlloc_4767_, 8, v_Q_4731_);
lean_ctor_set(v_reuseFailAlloc_4767_, 9, v_q_4732_);
lean_ctor_set(v_reuseFailAlloc_4767_, 10, v_w_4733_);
lean_ctor_set(v_reuseFailAlloc_4767_, 11, v_W_4734_);
lean_ctor_set(v_reuseFailAlloc_4767_, 12, v_E_4735_);
lean_ctor_set(v_reuseFailAlloc_4767_, 13, v_e_4736_);
lean_ctor_set(v_reuseFailAlloc_4767_, 14, v_c_4737_);
lean_ctor_set(v_reuseFailAlloc_4767_, 15, v_F_4738_);
lean_ctor_set(v_reuseFailAlloc_4767_, 16, v_a_4739_);
lean_ctor_set(v_reuseFailAlloc_4767_, 17, v_b_4740_);
lean_ctor_set(v_reuseFailAlloc_4767_, 18, v_B_4741_);
lean_ctor_set(v_reuseFailAlloc_4767_, 19, v_h_4742_);
lean_ctor_set(v_reuseFailAlloc_4767_, 20, v_K_4743_);
lean_ctor_set(v_reuseFailAlloc_4767_, 21, v_k_4744_);
lean_ctor_set(v_reuseFailAlloc_4767_, 22, v_H_4745_);
lean_ctor_set(v_reuseFailAlloc_4767_, 23, v_m_4746_);
lean_ctor_set(v_reuseFailAlloc_4767_, 24, v_s_4747_);
lean_ctor_set(v_reuseFailAlloc_4767_, 25, v_S_4748_);
lean_ctor_set(v_reuseFailAlloc_4767_, 26, v_A_4749_);
lean_ctor_set(v_reuseFailAlloc_4767_, 27, v_n_4750_);
lean_ctor_set(v_reuseFailAlloc_4767_, 28, v_N_4751_);
lean_ctor_set(v_reuseFailAlloc_4767_, 29, v_V_4752_);
lean_ctor_set(v_reuseFailAlloc_4767_, 30, v_z_4753_);
lean_ctor_set(v_reuseFailAlloc_4767_, 31, v_zabbrev_4754_);
lean_ctor_set(v_reuseFailAlloc_4767_, 32, v_v_4755_);
lean_ctor_set(v_reuseFailAlloc_4767_, 33, v_O_4756_);
lean_ctor_set(v_reuseFailAlloc_4767_, 34, v_X_4757_);
lean_ctor_set(v_reuseFailAlloc_4767_, 35, v_x_4758_);
lean_ctor_set(v_reuseFailAlloc_4767_, 36, v_Z_4759_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
}
}
case 7:
{
lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4823_; 
v_isSharedCheck_4823_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_4823_ == 0)
{
lean_object* v_unused_4824_; 
v_unused_4824_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_4824_);
v___x_4774_ = v_modifier_4414_;
v_isShared_4775_ = v_isSharedCheck_4823_;
goto v_resetjp_4773_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4823_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v_G_4776_; lean_object* v_y_4777_; lean_object* v_u_4778_; lean_object* v_Y_4779_; lean_object* v_D_4780_; lean_object* v_M_4781_; lean_object* v_L_4782_; lean_object* v_d_4783_; lean_object* v_q_4784_; lean_object* v_w_4785_; lean_object* v_W_4786_; lean_object* v_E_4787_; lean_object* v_e_4788_; lean_object* v_c_4789_; lean_object* v_F_4790_; lean_object* v_a_4791_; lean_object* v_b_4792_; lean_object* v_B_4793_; lean_object* v_h_4794_; lean_object* v_K_4795_; lean_object* v_k_4796_; lean_object* v_H_4797_; lean_object* v_m_4798_; lean_object* v_s_4799_; lean_object* v_S_4800_; lean_object* v_A_4801_; lean_object* v_n_4802_; lean_object* v_N_4803_; lean_object* v_V_4804_; lean_object* v_z_4805_; lean_object* v_zabbrev_4806_; lean_object* v_v_4807_; lean_object* v_O_4808_; lean_object* v_X_4809_; lean_object* v_x_4810_; lean_object* v_Z_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4821_; 
v_G_4776_ = lean_ctor_get(v_date_4413_, 0);
v_y_4777_ = lean_ctor_get(v_date_4413_, 1);
v_u_4778_ = lean_ctor_get(v_date_4413_, 2);
v_Y_4779_ = lean_ctor_get(v_date_4413_, 3);
v_D_4780_ = lean_ctor_get(v_date_4413_, 4);
v_M_4781_ = lean_ctor_get(v_date_4413_, 5);
v_L_4782_ = lean_ctor_get(v_date_4413_, 6);
v_d_4783_ = lean_ctor_get(v_date_4413_, 7);
v_q_4784_ = lean_ctor_get(v_date_4413_, 9);
v_w_4785_ = lean_ctor_get(v_date_4413_, 10);
v_W_4786_ = lean_ctor_get(v_date_4413_, 11);
v_E_4787_ = lean_ctor_get(v_date_4413_, 12);
v_e_4788_ = lean_ctor_get(v_date_4413_, 13);
v_c_4789_ = lean_ctor_get(v_date_4413_, 14);
v_F_4790_ = lean_ctor_get(v_date_4413_, 15);
v_a_4791_ = lean_ctor_get(v_date_4413_, 16);
v_b_4792_ = lean_ctor_get(v_date_4413_, 17);
v_B_4793_ = lean_ctor_get(v_date_4413_, 18);
v_h_4794_ = lean_ctor_get(v_date_4413_, 19);
v_K_4795_ = lean_ctor_get(v_date_4413_, 20);
v_k_4796_ = lean_ctor_get(v_date_4413_, 21);
v_H_4797_ = lean_ctor_get(v_date_4413_, 22);
v_m_4798_ = lean_ctor_get(v_date_4413_, 23);
v_s_4799_ = lean_ctor_get(v_date_4413_, 24);
v_S_4800_ = lean_ctor_get(v_date_4413_, 25);
v_A_4801_ = lean_ctor_get(v_date_4413_, 26);
v_n_4802_ = lean_ctor_get(v_date_4413_, 27);
v_N_4803_ = lean_ctor_get(v_date_4413_, 28);
v_V_4804_ = lean_ctor_get(v_date_4413_, 29);
v_z_4805_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_4806_ = lean_ctor_get(v_date_4413_, 31);
v_v_4807_ = lean_ctor_get(v_date_4413_, 32);
v_O_4808_ = lean_ctor_get(v_date_4413_, 33);
v_X_4809_ = lean_ctor_get(v_date_4413_, 34);
v_x_4810_ = lean_ctor_get(v_date_4413_, 35);
v_Z_4811_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_4821_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_4821_ == 0)
{
lean_object* v_unused_4822_; 
v_unused_4822_ = lean_ctor_get(v_date_4413_, 8);
lean_dec(v_unused_4822_);
v___x_4813_ = v_date_4413_;
v_isShared_4814_ = v_isSharedCheck_4821_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_Z_4811_);
lean_inc(v_x_4810_);
lean_inc(v_X_4809_);
lean_inc(v_O_4808_);
lean_inc(v_v_4807_);
lean_inc(v_zabbrev_4806_);
lean_inc(v_z_4805_);
lean_inc(v_V_4804_);
lean_inc(v_N_4803_);
lean_inc(v_n_4802_);
lean_inc(v_A_4801_);
lean_inc(v_S_4800_);
lean_inc(v_s_4799_);
lean_inc(v_m_4798_);
lean_inc(v_H_4797_);
lean_inc(v_k_4796_);
lean_inc(v_K_4795_);
lean_inc(v_h_4794_);
lean_inc(v_B_4793_);
lean_inc(v_b_4792_);
lean_inc(v_a_4791_);
lean_inc(v_F_4790_);
lean_inc(v_c_4789_);
lean_inc(v_e_4788_);
lean_inc(v_E_4787_);
lean_inc(v_W_4786_);
lean_inc(v_w_4785_);
lean_inc(v_q_4784_);
lean_inc(v_d_4783_);
lean_inc(v_L_4782_);
lean_inc(v_M_4781_);
lean_inc(v_D_4780_);
lean_inc(v_Y_4779_);
lean_inc(v_u_4778_);
lean_inc(v_y_4777_);
lean_inc(v_G_4776_);
lean_dec(v_date_4413_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4821_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4816_; 
if (v_isShared_4775_ == 0)
{
lean_ctor_set_tag(v___x_4774_, 1);
lean_ctor_set(v___x_4774_, 0, v_data_4415_);
v___x_4816_ = v___x_4774_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_data_4415_);
v___x_4816_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
lean_object* v___x_4818_; 
if (v_isShared_4814_ == 0)
{
lean_ctor_set(v___x_4813_, 8, v___x_4816_);
v___x_4818_ = v___x_4813_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_G_4776_);
lean_ctor_set(v_reuseFailAlloc_4819_, 1, v_y_4777_);
lean_ctor_set(v_reuseFailAlloc_4819_, 2, v_u_4778_);
lean_ctor_set(v_reuseFailAlloc_4819_, 3, v_Y_4779_);
lean_ctor_set(v_reuseFailAlloc_4819_, 4, v_D_4780_);
lean_ctor_set(v_reuseFailAlloc_4819_, 5, v_M_4781_);
lean_ctor_set(v_reuseFailAlloc_4819_, 6, v_L_4782_);
lean_ctor_set(v_reuseFailAlloc_4819_, 7, v_d_4783_);
lean_ctor_set(v_reuseFailAlloc_4819_, 8, v___x_4816_);
lean_ctor_set(v_reuseFailAlloc_4819_, 9, v_q_4784_);
lean_ctor_set(v_reuseFailAlloc_4819_, 10, v_w_4785_);
lean_ctor_set(v_reuseFailAlloc_4819_, 11, v_W_4786_);
lean_ctor_set(v_reuseFailAlloc_4819_, 12, v_E_4787_);
lean_ctor_set(v_reuseFailAlloc_4819_, 13, v_e_4788_);
lean_ctor_set(v_reuseFailAlloc_4819_, 14, v_c_4789_);
lean_ctor_set(v_reuseFailAlloc_4819_, 15, v_F_4790_);
lean_ctor_set(v_reuseFailAlloc_4819_, 16, v_a_4791_);
lean_ctor_set(v_reuseFailAlloc_4819_, 17, v_b_4792_);
lean_ctor_set(v_reuseFailAlloc_4819_, 18, v_B_4793_);
lean_ctor_set(v_reuseFailAlloc_4819_, 19, v_h_4794_);
lean_ctor_set(v_reuseFailAlloc_4819_, 20, v_K_4795_);
lean_ctor_set(v_reuseFailAlloc_4819_, 21, v_k_4796_);
lean_ctor_set(v_reuseFailAlloc_4819_, 22, v_H_4797_);
lean_ctor_set(v_reuseFailAlloc_4819_, 23, v_m_4798_);
lean_ctor_set(v_reuseFailAlloc_4819_, 24, v_s_4799_);
lean_ctor_set(v_reuseFailAlloc_4819_, 25, v_S_4800_);
lean_ctor_set(v_reuseFailAlloc_4819_, 26, v_A_4801_);
lean_ctor_set(v_reuseFailAlloc_4819_, 27, v_n_4802_);
lean_ctor_set(v_reuseFailAlloc_4819_, 28, v_N_4803_);
lean_ctor_set(v_reuseFailAlloc_4819_, 29, v_V_4804_);
lean_ctor_set(v_reuseFailAlloc_4819_, 30, v_z_4805_);
lean_ctor_set(v_reuseFailAlloc_4819_, 31, v_zabbrev_4806_);
lean_ctor_set(v_reuseFailAlloc_4819_, 32, v_v_4807_);
lean_ctor_set(v_reuseFailAlloc_4819_, 33, v_O_4808_);
lean_ctor_set(v_reuseFailAlloc_4819_, 34, v_X_4809_);
lean_ctor_set(v_reuseFailAlloc_4819_, 35, v_x_4810_);
lean_ctor_set(v_reuseFailAlloc_4819_, 36, v_Z_4811_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
}
}
}
case 8:
{
lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4875_; 
v_isSharedCheck_4875_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_4875_ == 0)
{
lean_object* v_unused_4876_; 
v_unused_4876_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_4876_);
v___x_4826_ = v_modifier_4414_;
v_isShared_4827_ = v_isSharedCheck_4875_;
goto v_resetjp_4825_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4875_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v_G_4828_; lean_object* v_y_4829_; lean_object* v_u_4830_; lean_object* v_Y_4831_; lean_object* v_D_4832_; lean_object* v_M_4833_; lean_object* v_L_4834_; lean_object* v_d_4835_; lean_object* v_Q_4836_; lean_object* v_w_4837_; lean_object* v_W_4838_; lean_object* v_E_4839_; lean_object* v_e_4840_; lean_object* v_c_4841_; lean_object* v_F_4842_; lean_object* v_a_4843_; lean_object* v_b_4844_; lean_object* v_B_4845_; lean_object* v_h_4846_; lean_object* v_K_4847_; lean_object* v_k_4848_; lean_object* v_H_4849_; lean_object* v_m_4850_; lean_object* v_s_4851_; lean_object* v_S_4852_; lean_object* v_A_4853_; lean_object* v_n_4854_; lean_object* v_N_4855_; lean_object* v_V_4856_; lean_object* v_z_4857_; lean_object* v_zabbrev_4858_; lean_object* v_v_4859_; lean_object* v_O_4860_; lean_object* v_X_4861_; lean_object* v_x_4862_; lean_object* v_Z_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4873_; 
v_G_4828_ = lean_ctor_get(v_date_4413_, 0);
v_y_4829_ = lean_ctor_get(v_date_4413_, 1);
v_u_4830_ = lean_ctor_get(v_date_4413_, 2);
v_Y_4831_ = lean_ctor_get(v_date_4413_, 3);
v_D_4832_ = lean_ctor_get(v_date_4413_, 4);
v_M_4833_ = lean_ctor_get(v_date_4413_, 5);
v_L_4834_ = lean_ctor_get(v_date_4413_, 6);
v_d_4835_ = lean_ctor_get(v_date_4413_, 7);
v_Q_4836_ = lean_ctor_get(v_date_4413_, 8);
v_w_4837_ = lean_ctor_get(v_date_4413_, 10);
v_W_4838_ = lean_ctor_get(v_date_4413_, 11);
v_E_4839_ = lean_ctor_get(v_date_4413_, 12);
v_e_4840_ = lean_ctor_get(v_date_4413_, 13);
v_c_4841_ = lean_ctor_get(v_date_4413_, 14);
v_F_4842_ = lean_ctor_get(v_date_4413_, 15);
v_a_4843_ = lean_ctor_get(v_date_4413_, 16);
v_b_4844_ = lean_ctor_get(v_date_4413_, 17);
v_B_4845_ = lean_ctor_get(v_date_4413_, 18);
v_h_4846_ = lean_ctor_get(v_date_4413_, 19);
v_K_4847_ = lean_ctor_get(v_date_4413_, 20);
v_k_4848_ = lean_ctor_get(v_date_4413_, 21);
v_H_4849_ = lean_ctor_get(v_date_4413_, 22);
v_m_4850_ = lean_ctor_get(v_date_4413_, 23);
v_s_4851_ = lean_ctor_get(v_date_4413_, 24);
v_S_4852_ = lean_ctor_get(v_date_4413_, 25);
v_A_4853_ = lean_ctor_get(v_date_4413_, 26);
v_n_4854_ = lean_ctor_get(v_date_4413_, 27);
v_N_4855_ = lean_ctor_get(v_date_4413_, 28);
v_V_4856_ = lean_ctor_get(v_date_4413_, 29);
v_z_4857_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_4858_ = lean_ctor_get(v_date_4413_, 31);
v_v_4859_ = lean_ctor_get(v_date_4413_, 32);
v_O_4860_ = lean_ctor_get(v_date_4413_, 33);
v_X_4861_ = lean_ctor_get(v_date_4413_, 34);
v_x_4862_ = lean_ctor_get(v_date_4413_, 35);
v_Z_4863_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_4873_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_4873_ == 0)
{
lean_object* v_unused_4874_; 
v_unused_4874_ = lean_ctor_get(v_date_4413_, 9);
lean_dec(v_unused_4874_);
v___x_4865_ = v_date_4413_;
v_isShared_4866_ = v_isSharedCheck_4873_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_Z_4863_);
lean_inc(v_x_4862_);
lean_inc(v_X_4861_);
lean_inc(v_O_4860_);
lean_inc(v_v_4859_);
lean_inc(v_zabbrev_4858_);
lean_inc(v_z_4857_);
lean_inc(v_V_4856_);
lean_inc(v_N_4855_);
lean_inc(v_n_4854_);
lean_inc(v_A_4853_);
lean_inc(v_S_4852_);
lean_inc(v_s_4851_);
lean_inc(v_m_4850_);
lean_inc(v_H_4849_);
lean_inc(v_k_4848_);
lean_inc(v_K_4847_);
lean_inc(v_h_4846_);
lean_inc(v_B_4845_);
lean_inc(v_b_4844_);
lean_inc(v_a_4843_);
lean_inc(v_F_4842_);
lean_inc(v_c_4841_);
lean_inc(v_e_4840_);
lean_inc(v_E_4839_);
lean_inc(v_W_4838_);
lean_inc(v_w_4837_);
lean_inc(v_Q_4836_);
lean_inc(v_d_4835_);
lean_inc(v_L_4834_);
lean_inc(v_M_4833_);
lean_inc(v_D_4832_);
lean_inc(v_Y_4831_);
lean_inc(v_u_4830_);
lean_inc(v_y_4829_);
lean_inc(v_G_4828_);
lean_dec(v_date_4413_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4873_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
lean_object* v___x_4868_; 
if (v_isShared_4827_ == 0)
{
lean_ctor_set_tag(v___x_4826_, 1);
lean_ctor_set(v___x_4826_, 0, v_data_4415_);
v___x_4868_ = v___x_4826_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v_data_4415_);
v___x_4868_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
lean_object* v___x_4870_; 
if (v_isShared_4866_ == 0)
{
lean_ctor_set(v___x_4865_, 9, v___x_4868_);
v___x_4870_ = v___x_4865_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_G_4828_);
lean_ctor_set(v_reuseFailAlloc_4871_, 1, v_y_4829_);
lean_ctor_set(v_reuseFailAlloc_4871_, 2, v_u_4830_);
lean_ctor_set(v_reuseFailAlloc_4871_, 3, v_Y_4831_);
lean_ctor_set(v_reuseFailAlloc_4871_, 4, v_D_4832_);
lean_ctor_set(v_reuseFailAlloc_4871_, 5, v_M_4833_);
lean_ctor_set(v_reuseFailAlloc_4871_, 6, v_L_4834_);
lean_ctor_set(v_reuseFailAlloc_4871_, 7, v_d_4835_);
lean_ctor_set(v_reuseFailAlloc_4871_, 8, v_Q_4836_);
lean_ctor_set(v_reuseFailAlloc_4871_, 9, v___x_4868_);
lean_ctor_set(v_reuseFailAlloc_4871_, 10, v_w_4837_);
lean_ctor_set(v_reuseFailAlloc_4871_, 11, v_W_4838_);
lean_ctor_set(v_reuseFailAlloc_4871_, 12, v_E_4839_);
lean_ctor_set(v_reuseFailAlloc_4871_, 13, v_e_4840_);
lean_ctor_set(v_reuseFailAlloc_4871_, 14, v_c_4841_);
lean_ctor_set(v_reuseFailAlloc_4871_, 15, v_F_4842_);
lean_ctor_set(v_reuseFailAlloc_4871_, 16, v_a_4843_);
lean_ctor_set(v_reuseFailAlloc_4871_, 17, v_b_4844_);
lean_ctor_set(v_reuseFailAlloc_4871_, 18, v_B_4845_);
lean_ctor_set(v_reuseFailAlloc_4871_, 19, v_h_4846_);
lean_ctor_set(v_reuseFailAlloc_4871_, 20, v_K_4847_);
lean_ctor_set(v_reuseFailAlloc_4871_, 21, v_k_4848_);
lean_ctor_set(v_reuseFailAlloc_4871_, 22, v_H_4849_);
lean_ctor_set(v_reuseFailAlloc_4871_, 23, v_m_4850_);
lean_ctor_set(v_reuseFailAlloc_4871_, 24, v_s_4851_);
lean_ctor_set(v_reuseFailAlloc_4871_, 25, v_S_4852_);
lean_ctor_set(v_reuseFailAlloc_4871_, 26, v_A_4853_);
lean_ctor_set(v_reuseFailAlloc_4871_, 27, v_n_4854_);
lean_ctor_set(v_reuseFailAlloc_4871_, 28, v_N_4855_);
lean_ctor_set(v_reuseFailAlloc_4871_, 29, v_V_4856_);
lean_ctor_set(v_reuseFailAlloc_4871_, 30, v_z_4857_);
lean_ctor_set(v_reuseFailAlloc_4871_, 31, v_zabbrev_4858_);
lean_ctor_set(v_reuseFailAlloc_4871_, 32, v_v_4859_);
lean_ctor_set(v_reuseFailAlloc_4871_, 33, v_O_4860_);
lean_ctor_set(v_reuseFailAlloc_4871_, 34, v_X_4861_);
lean_ctor_set(v_reuseFailAlloc_4871_, 35, v_x_4862_);
lean_ctor_set(v_reuseFailAlloc_4871_, 36, v_Z_4863_);
v___x_4870_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
return v___x_4870_;
}
}
}
}
}
case 9:
{
lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4927_; 
v_isSharedCheck_4927_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_4927_ == 0)
{
lean_object* v_unused_4928_; 
v_unused_4928_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_4928_);
v___x_4878_ = v_modifier_4414_;
v_isShared_4879_ = v_isSharedCheck_4927_;
goto v_resetjp_4877_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4927_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v_G_4880_; lean_object* v_y_4881_; lean_object* v_u_4882_; lean_object* v_D_4883_; lean_object* v_M_4884_; lean_object* v_L_4885_; lean_object* v_d_4886_; lean_object* v_Q_4887_; lean_object* v_q_4888_; lean_object* v_w_4889_; lean_object* v_W_4890_; lean_object* v_E_4891_; lean_object* v_e_4892_; lean_object* v_c_4893_; lean_object* v_F_4894_; lean_object* v_a_4895_; lean_object* v_b_4896_; lean_object* v_B_4897_; lean_object* v_h_4898_; lean_object* v_K_4899_; lean_object* v_k_4900_; lean_object* v_H_4901_; lean_object* v_m_4902_; lean_object* v_s_4903_; lean_object* v_S_4904_; lean_object* v_A_4905_; lean_object* v_n_4906_; lean_object* v_N_4907_; lean_object* v_V_4908_; lean_object* v_z_4909_; lean_object* v_zabbrev_4910_; lean_object* v_v_4911_; lean_object* v_O_4912_; lean_object* v_X_4913_; lean_object* v_x_4914_; lean_object* v_Z_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4925_; 
v_G_4880_ = lean_ctor_get(v_date_4413_, 0);
v_y_4881_ = lean_ctor_get(v_date_4413_, 1);
v_u_4882_ = lean_ctor_get(v_date_4413_, 2);
v_D_4883_ = lean_ctor_get(v_date_4413_, 4);
v_M_4884_ = lean_ctor_get(v_date_4413_, 5);
v_L_4885_ = lean_ctor_get(v_date_4413_, 6);
v_d_4886_ = lean_ctor_get(v_date_4413_, 7);
v_Q_4887_ = lean_ctor_get(v_date_4413_, 8);
v_q_4888_ = lean_ctor_get(v_date_4413_, 9);
v_w_4889_ = lean_ctor_get(v_date_4413_, 10);
v_W_4890_ = lean_ctor_get(v_date_4413_, 11);
v_E_4891_ = lean_ctor_get(v_date_4413_, 12);
v_e_4892_ = lean_ctor_get(v_date_4413_, 13);
v_c_4893_ = lean_ctor_get(v_date_4413_, 14);
v_F_4894_ = lean_ctor_get(v_date_4413_, 15);
v_a_4895_ = lean_ctor_get(v_date_4413_, 16);
v_b_4896_ = lean_ctor_get(v_date_4413_, 17);
v_B_4897_ = lean_ctor_get(v_date_4413_, 18);
v_h_4898_ = lean_ctor_get(v_date_4413_, 19);
v_K_4899_ = lean_ctor_get(v_date_4413_, 20);
v_k_4900_ = lean_ctor_get(v_date_4413_, 21);
v_H_4901_ = lean_ctor_get(v_date_4413_, 22);
v_m_4902_ = lean_ctor_get(v_date_4413_, 23);
v_s_4903_ = lean_ctor_get(v_date_4413_, 24);
v_S_4904_ = lean_ctor_get(v_date_4413_, 25);
v_A_4905_ = lean_ctor_get(v_date_4413_, 26);
v_n_4906_ = lean_ctor_get(v_date_4413_, 27);
v_N_4907_ = lean_ctor_get(v_date_4413_, 28);
v_V_4908_ = lean_ctor_get(v_date_4413_, 29);
v_z_4909_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_4910_ = lean_ctor_get(v_date_4413_, 31);
v_v_4911_ = lean_ctor_get(v_date_4413_, 32);
v_O_4912_ = lean_ctor_get(v_date_4413_, 33);
v_X_4913_ = lean_ctor_get(v_date_4413_, 34);
v_x_4914_ = lean_ctor_get(v_date_4413_, 35);
v_Z_4915_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_4925_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_4925_ == 0)
{
lean_object* v_unused_4926_; 
v_unused_4926_ = lean_ctor_get(v_date_4413_, 3);
lean_dec(v_unused_4926_);
v___x_4917_ = v_date_4413_;
v_isShared_4918_ = v_isSharedCheck_4925_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_Z_4915_);
lean_inc(v_x_4914_);
lean_inc(v_X_4913_);
lean_inc(v_O_4912_);
lean_inc(v_v_4911_);
lean_inc(v_zabbrev_4910_);
lean_inc(v_z_4909_);
lean_inc(v_V_4908_);
lean_inc(v_N_4907_);
lean_inc(v_n_4906_);
lean_inc(v_A_4905_);
lean_inc(v_S_4904_);
lean_inc(v_s_4903_);
lean_inc(v_m_4902_);
lean_inc(v_H_4901_);
lean_inc(v_k_4900_);
lean_inc(v_K_4899_);
lean_inc(v_h_4898_);
lean_inc(v_B_4897_);
lean_inc(v_b_4896_);
lean_inc(v_a_4895_);
lean_inc(v_F_4894_);
lean_inc(v_c_4893_);
lean_inc(v_e_4892_);
lean_inc(v_E_4891_);
lean_inc(v_W_4890_);
lean_inc(v_w_4889_);
lean_inc(v_q_4888_);
lean_inc(v_Q_4887_);
lean_inc(v_d_4886_);
lean_inc(v_L_4885_);
lean_inc(v_M_4884_);
lean_inc(v_D_4883_);
lean_inc(v_u_4882_);
lean_inc(v_y_4881_);
lean_inc(v_G_4880_);
lean_dec(v_date_4413_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4925_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___x_4920_; 
if (v_isShared_4879_ == 0)
{
lean_ctor_set_tag(v___x_4878_, 1);
lean_ctor_set(v___x_4878_, 0, v_data_4415_);
v___x_4920_ = v___x_4878_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v_data_4415_);
v___x_4920_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
lean_object* v___x_4922_; 
if (v_isShared_4918_ == 0)
{
lean_ctor_set(v___x_4917_, 3, v___x_4920_);
v___x_4922_ = v___x_4917_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v_G_4880_);
lean_ctor_set(v_reuseFailAlloc_4923_, 1, v_y_4881_);
lean_ctor_set(v_reuseFailAlloc_4923_, 2, v_u_4882_);
lean_ctor_set(v_reuseFailAlloc_4923_, 3, v___x_4920_);
lean_ctor_set(v_reuseFailAlloc_4923_, 4, v_D_4883_);
lean_ctor_set(v_reuseFailAlloc_4923_, 5, v_M_4884_);
lean_ctor_set(v_reuseFailAlloc_4923_, 6, v_L_4885_);
lean_ctor_set(v_reuseFailAlloc_4923_, 7, v_d_4886_);
lean_ctor_set(v_reuseFailAlloc_4923_, 8, v_Q_4887_);
lean_ctor_set(v_reuseFailAlloc_4923_, 9, v_q_4888_);
lean_ctor_set(v_reuseFailAlloc_4923_, 10, v_w_4889_);
lean_ctor_set(v_reuseFailAlloc_4923_, 11, v_W_4890_);
lean_ctor_set(v_reuseFailAlloc_4923_, 12, v_E_4891_);
lean_ctor_set(v_reuseFailAlloc_4923_, 13, v_e_4892_);
lean_ctor_set(v_reuseFailAlloc_4923_, 14, v_c_4893_);
lean_ctor_set(v_reuseFailAlloc_4923_, 15, v_F_4894_);
lean_ctor_set(v_reuseFailAlloc_4923_, 16, v_a_4895_);
lean_ctor_set(v_reuseFailAlloc_4923_, 17, v_b_4896_);
lean_ctor_set(v_reuseFailAlloc_4923_, 18, v_B_4897_);
lean_ctor_set(v_reuseFailAlloc_4923_, 19, v_h_4898_);
lean_ctor_set(v_reuseFailAlloc_4923_, 20, v_K_4899_);
lean_ctor_set(v_reuseFailAlloc_4923_, 21, v_k_4900_);
lean_ctor_set(v_reuseFailAlloc_4923_, 22, v_H_4901_);
lean_ctor_set(v_reuseFailAlloc_4923_, 23, v_m_4902_);
lean_ctor_set(v_reuseFailAlloc_4923_, 24, v_s_4903_);
lean_ctor_set(v_reuseFailAlloc_4923_, 25, v_S_4904_);
lean_ctor_set(v_reuseFailAlloc_4923_, 26, v_A_4905_);
lean_ctor_set(v_reuseFailAlloc_4923_, 27, v_n_4906_);
lean_ctor_set(v_reuseFailAlloc_4923_, 28, v_N_4907_);
lean_ctor_set(v_reuseFailAlloc_4923_, 29, v_V_4908_);
lean_ctor_set(v_reuseFailAlloc_4923_, 30, v_z_4909_);
lean_ctor_set(v_reuseFailAlloc_4923_, 31, v_zabbrev_4910_);
lean_ctor_set(v_reuseFailAlloc_4923_, 32, v_v_4911_);
lean_ctor_set(v_reuseFailAlloc_4923_, 33, v_O_4912_);
lean_ctor_set(v_reuseFailAlloc_4923_, 34, v_X_4913_);
lean_ctor_set(v_reuseFailAlloc_4923_, 35, v_x_4914_);
lean_ctor_set(v_reuseFailAlloc_4923_, 36, v_Z_4915_);
v___x_4922_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
return v___x_4922_;
}
}
}
}
}
case 10:
{
lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4979_; 
v_isSharedCheck_4979_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_4979_ == 0)
{
lean_object* v_unused_4980_; 
v_unused_4980_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_4980_);
v___x_4930_ = v_modifier_4414_;
v_isShared_4931_ = v_isSharedCheck_4979_;
goto v_resetjp_4929_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4979_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v_G_4932_; lean_object* v_y_4933_; lean_object* v_u_4934_; lean_object* v_Y_4935_; lean_object* v_D_4936_; lean_object* v_M_4937_; lean_object* v_L_4938_; lean_object* v_d_4939_; lean_object* v_Q_4940_; lean_object* v_q_4941_; lean_object* v_W_4942_; lean_object* v_E_4943_; lean_object* v_e_4944_; lean_object* v_c_4945_; lean_object* v_F_4946_; lean_object* v_a_4947_; lean_object* v_b_4948_; lean_object* v_B_4949_; lean_object* v_h_4950_; lean_object* v_K_4951_; lean_object* v_k_4952_; lean_object* v_H_4953_; lean_object* v_m_4954_; lean_object* v_s_4955_; lean_object* v_S_4956_; lean_object* v_A_4957_; lean_object* v_n_4958_; lean_object* v_N_4959_; lean_object* v_V_4960_; lean_object* v_z_4961_; lean_object* v_zabbrev_4962_; lean_object* v_v_4963_; lean_object* v_O_4964_; lean_object* v_X_4965_; lean_object* v_x_4966_; lean_object* v_Z_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_4977_; 
v_G_4932_ = lean_ctor_get(v_date_4413_, 0);
v_y_4933_ = lean_ctor_get(v_date_4413_, 1);
v_u_4934_ = lean_ctor_get(v_date_4413_, 2);
v_Y_4935_ = lean_ctor_get(v_date_4413_, 3);
v_D_4936_ = lean_ctor_get(v_date_4413_, 4);
v_M_4937_ = lean_ctor_get(v_date_4413_, 5);
v_L_4938_ = lean_ctor_get(v_date_4413_, 6);
v_d_4939_ = lean_ctor_get(v_date_4413_, 7);
v_Q_4940_ = lean_ctor_get(v_date_4413_, 8);
v_q_4941_ = lean_ctor_get(v_date_4413_, 9);
v_W_4942_ = lean_ctor_get(v_date_4413_, 11);
v_E_4943_ = lean_ctor_get(v_date_4413_, 12);
v_e_4944_ = lean_ctor_get(v_date_4413_, 13);
v_c_4945_ = lean_ctor_get(v_date_4413_, 14);
v_F_4946_ = lean_ctor_get(v_date_4413_, 15);
v_a_4947_ = lean_ctor_get(v_date_4413_, 16);
v_b_4948_ = lean_ctor_get(v_date_4413_, 17);
v_B_4949_ = lean_ctor_get(v_date_4413_, 18);
v_h_4950_ = lean_ctor_get(v_date_4413_, 19);
v_K_4951_ = lean_ctor_get(v_date_4413_, 20);
v_k_4952_ = lean_ctor_get(v_date_4413_, 21);
v_H_4953_ = lean_ctor_get(v_date_4413_, 22);
v_m_4954_ = lean_ctor_get(v_date_4413_, 23);
v_s_4955_ = lean_ctor_get(v_date_4413_, 24);
v_S_4956_ = lean_ctor_get(v_date_4413_, 25);
v_A_4957_ = lean_ctor_get(v_date_4413_, 26);
v_n_4958_ = lean_ctor_get(v_date_4413_, 27);
v_N_4959_ = lean_ctor_get(v_date_4413_, 28);
v_V_4960_ = lean_ctor_get(v_date_4413_, 29);
v_z_4961_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_4962_ = lean_ctor_get(v_date_4413_, 31);
v_v_4963_ = lean_ctor_get(v_date_4413_, 32);
v_O_4964_ = lean_ctor_get(v_date_4413_, 33);
v_X_4965_ = lean_ctor_get(v_date_4413_, 34);
v_x_4966_ = lean_ctor_get(v_date_4413_, 35);
v_Z_4967_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_4977_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_4977_ == 0)
{
lean_object* v_unused_4978_; 
v_unused_4978_ = lean_ctor_get(v_date_4413_, 10);
lean_dec(v_unused_4978_);
v___x_4969_ = v_date_4413_;
v_isShared_4970_ = v_isSharedCheck_4977_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_Z_4967_);
lean_inc(v_x_4966_);
lean_inc(v_X_4965_);
lean_inc(v_O_4964_);
lean_inc(v_v_4963_);
lean_inc(v_zabbrev_4962_);
lean_inc(v_z_4961_);
lean_inc(v_V_4960_);
lean_inc(v_N_4959_);
lean_inc(v_n_4958_);
lean_inc(v_A_4957_);
lean_inc(v_S_4956_);
lean_inc(v_s_4955_);
lean_inc(v_m_4954_);
lean_inc(v_H_4953_);
lean_inc(v_k_4952_);
lean_inc(v_K_4951_);
lean_inc(v_h_4950_);
lean_inc(v_B_4949_);
lean_inc(v_b_4948_);
lean_inc(v_a_4947_);
lean_inc(v_F_4946_);
lean_inc(v_c_4945_);
lean_inc(v_e_4944_);
lean_inc(v_E_4943_);
lean_inc(v_W_4942_);
lean_inc(v_q_4941_);
lean_inc(v_Q_4940_);
lean_inc(v_d_4939_);
lean_inc(v_L_4938_);
lean_inc(v_M_4937_);
lean_inc(v_D_4936_);
lean_inc(v_Y_4935_);
lean_inc(v_u_4934_);
lean_inc(v_y_4933_);
lean_inc(v_G_4932_);
lean_dec(v_date_4413_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_4977_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v___x_4972_; 
if (v_isShared_4931_ == 0)
{
lean_ctor_set_tag(v___x_4930_, 1);
lean_ctor_set(v___x_4930_, 0, v_data_4415_);
v___x_4972_ = v___x_4930_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_4976_; 
v_reuseFailAlloc_4976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4976_, 0, v_data_4415_);
v___x_4972_ = v_reuseFailAlloc_4976_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
lean_object* v___x_4974_; 
if (v_isShared_4970_ == 0)
{
lean_ctor_set(v___x_4969_, 10, v___x_4972_);
v___x_4974_ = v___x_4969_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_G_4932_);
lean_ctor_set(v_reuseFailAlloc_4975_, 1, v_y_4933_);
lean_ctor_set(v_reuseFailAlloc_4975_, 2, v_u_4934_);
lean_ctor_set(v_reuseFailAlloc_4975_, 3, v_Y_4935_);
lean_ctor_set(v_reuseFailAlloc_4975_, 4, v_D_4936_);
lean_ctor_set(v_reuseFailAlloc_4975_, 5, v_M_4937_);
lean_ctor_set(v_reuseFailAlloc_4975_, 6, v_L_4938_);
lean_ctor_set(v_reuseFailAlloc_4975_, 7, v_d_4939_);
lean_ctor_set(v_reuseFailAlloc_4975_, 8, v_Q_4940_);
lean_ctor_set(v_reuseFailAlloc_4975_, 9, v_q_4941_);
lean_ctor_set(v_reuseFailAlloc_4975_, 10, v___x_4972_);
lean_ctor_set(v_reuseFailAlloc_4975_, 11, v_W_4942_);
lean_ctor_set(v_reuseFailAlloc_4975_, 12, v_E_4943_);
lean_ctor_set(v_reuseFailAlloc_4975_, 13, v_e_4944_);
lean_ctor_set(v_reuseFailAlloc_4975_, 14, v_c_4945_);
lean_ctor_set(v_reuseFailAlloc_4975_, 15, v_F_4946_);
lean_ctor_set(v_reuseFailAlloc_4975_, 16, v_a_4947_);
lean_ctor_set(v_reuseFailAlloc_4975_, 17, v_b_4948_);
lean_ctor_set(v_reuseFailAlloc_4975_, 18, v_B_4949_);
lean_ctor_set(v_reuseFailAlloc_4975_, 19, v_h_4950_);
lean_ctor_set(v_reuseFailAlloc_4975_, 20, v_K_4951_);
lean_ctor_set(v_reuseFailAlloc_4975_, 21, v_k_4952_);
lean_ctor_set(v_reuseFailAlloc_4975_, 22, v_H_4953_);
lean_ctor_set(v_reuseFailAlloc_4975_, 23, v_m_4954_);
lean_ctor_set(v_reuseFailAlloc_4975_, 24, v_s_4955_);
lean_ctor_set(v_reuseFailAlloc_4975_, 25, v_S_4956_);
lean_ctor_set(v_reuseFailAlloc_4975_, 26, v_A_4957_);
lean_ctor_set(v_reuseFailAlloc_4975_, 27, v_n_4958_);
lean_ctor_set(v_reuseFailAlloc_4975_, 28, v_N_4959_);
lean_ctor_set(v_reuseFailAlloc_4975_, 29, v_V_4960_);
lean_ctor_set(v_reuseFailAlloc_4975_, 30, v_z_4961_);
lean_ctor_set(v_reuseFailAlloc_4975_, 31, v_zabbrev_4962_);
lean_ctor_set(v_reuseFailAlloc_4975_, 32, v_v_4963_);
lean_ctor_set(v_reuseFailAlloc_4975_, 33, v_O_4964_);
lean_ctor_set(v_reuseFailAlloc_4975_, 34, v_X_4965_);
lean_ctor_set(v_reuseFailAlloc_4975_, 35, v_x_4966_);
lean_ctor_set(v_reuseFailAlloc_4975_, 36, v_Z_4967_);
v___x_4974_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
return v___x_4974_;
}
}
}
}
}
case 11:
{
lean_object* v___x_4982_; uint8_t v_isShared_4983_; uint8_t v_isSharedCheck_5031_; 
v_isSharedCheck_5031_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_5031_ == 0)
{
lean_object* v_unused_5032_; 
v_unused_5032_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_5032_);
v___x_4982_ = v_modifier_4414_;
v_isShared_4983_ = v_isSharedCheck_5031_;
goto v_resetjp_4981_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_4982_ = lean_box(0);
v_isShared_4983_ = v_isSharedCheck_5031_;
goto v_resetjp_4981_;
}
v_resetjp_4981_:
{
lean_object* v_G_4984_; lean_object* v_y_4985_; lean_object* v_u_4986_; lean_object* v_Y_4987_; lean_object* v_D_4988_; lean_object* v_M_4989_; lean_object* v_L_4990_; lean_object* v_d_4991_; lean_object* v_Q_4992_; lean_object* v_q_4993_; lean_object* v_w_4994_; lean_object* v_E_4995_; lean_object* v_e_4996_; lean_object* v_c_4997_; lean_object* v_F_4998_; lean_object* v_a_4999_; lean_object* v_b_5000_; lean_object* v_B_5001_; lean_object* v_h_5002_; lean_object* v_K_5003_; lean_object* v_k_5004_; lean_object* v_H_5005_; lean_object* v_m_5006_; lean_object* v_s_5007_; lean_object* v_S_5008_; lean_object* v_A_5009_; lean_object* v_n_5010_; lean_object* v_N_5011_; lean_object* v_V_5012_; lean_object* v_z_5013_; lean_object* v_zabbrev_5014_; lean_object* v_v_5015_; lean_object* v_O_5016_; lean_object* v_X_5017_; lean_object* v_x_5018_; lean_object* v_Z_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5029_; 
v_G_4984_ = lean_ctor_get(v_date_4413_, 0);
v_y_4985_ = lean_ctor_get(v_date_4413_, 1);
v_u_4986_ = lean_ctor_get(v_date_4413_, 2);
v_Y_4987_ = lean_ctor_get(v_date_4413_, 3);
v_D_4988_ = lean_ctor_get(v_date_4413_, 4);
v_M_4989_ = lean_ctor_get(v_date_4413_, 5);
v_L_4990_ = lean_ctor_get(v_date_4413_, 6);
v_d_4991_ = lean_ctor_get(v_date_4413_, 7);
v_Q_4992_ = lean_ctor_get(v_date_4413_, 8);
v_q_4993_ = lean_ctor_get(v_date_4413_, 9);
v_w_4994_ = lean_ctor_get(v_date_4413_, 10);
v_E_4995_ = lean_ctor_get(v_date_4413_, 12);
v_e_4996_ = lean_ctor_get(v_date_4413_, 13);
v_c_4997_ = lean_ctor_get(v_date_4413_, 14);
v_F_4998_ = lean_ctor_get(v_date_4413_, 15);
v_a_4999_ = lean_ctor_get(v_date_4413_, 16);
v_b_5000_ = lean_ctor_get(v_date_4413_, 17);
v_B_5001_ = lean_ctor_get(v_date_4413_, 18);
v_h_5002_ = lean_ctor_get(v_date_4413_, 19);
v_K_5003_ = lean_ctor_get(v_date_4413_, 20);
v_k_5004_ = lean_ctor_get(v_date_4413_, 21);
v_H_5005_ = lean_ctor_get(v_date_4413_, 22);
v_m_5006_ = lean_ctor_get(v_date_4413_, 23);
v_s_5007_ = lean_ctor_get(v_date_4413_, 24);
v_S_5008_ = lean_ctor_get(v_date_4413_, 25);
v_A_5009_ = lean_ctor_get(v_date_4413_, 26);
v_n_5010_ = lean_ctor_get(v_date_4413_, 27);
v_N_5011_ = lean_ctor_get(v_date_4413_, 28);
v_V_5012_ = lean_ctor_get(v_date_4413_, 29);
v_z_5013_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_5014_ = lean_ctor_get(v_date_4413_, 31);
v_v_5015_ = lean_ctor_get(v_date_4413_, 32);
v_O_5016_ = lean_ctor_get(v_date_4413_, 33);
v_X_5017_ = lean_ctor_get(v_date_4413_, 34);
v_x_5018_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5019_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5029_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5029_ == 0)
{
lean_object* v_unused_5030_; 
v_unused_5030_ = lean_ctor_get(v_date_4413_, 11);
lean_dec(v_unused_5030_);
v___x_5021_ = v_date_4413_;
v_isShared_5022_ = v_isSharedCheck_5029_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_Z_5019_);
lean_inc(v_x_5018_);
lean_inc(v_X_5017_);
lean_inc(v_O_5016_);
lean_inc(v_v_5015_);
lean_inc(v_zabbrev_5014_);
lean_inc(v_z_5013_);
lean_inc(v_V_5012_);
lean_inc(v_N_5011_);
lean_inc(v_n_5010_);
lean_inc(v_A_5009_);
lean_inc(v_S_5008_);
lean_inc(v_s_5007_);
lean_inc(v_m_5006_);
lean_inc(v_H_5005_);
lean_inc(v_k_5004_);
lean_inc(v_K_5003_);
lean_inc(v_h_5002_);
lean_inc(v_B_5001_);
lean_inc(v_b_5000_);
lean_inc(v_a_4999_);
lean_inc(v_F_4998_);
lean_inc(v_c_4997_);
lean_inc(v_e_4996_);
lean_inc(v_E_4995_);
lean_inc(v_w_4994_);
lean_inc(v_q_4993_);
lean_inc(v_Q_4992_);
lean_inc(v_d_4991_);
lean_inc(v_L_4990_);
lean_inc(v_M_4989_);
lean_inc(v_D_4988_);
lean_inc(v_Y_4987_);
lean_inc(v_u_4986_);
lean_inc(v_y_4985_);
lean_inc(v_G_4984_);
lean_dec(v_date_4413_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5029_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5024_; 
if (v_isShared_4983_ == 0)
{
lean_ctor_set_tag(v___x_4982_, 1);
lean_ctor_set(v___x_4982_, 0, v_data_4415_);
v___x_5024_ = v___x_4982_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_data_4415_);
v___x_5024_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
lean_object* v___x_5026_; 
if (v_isShared_5022_ == 0)
{
lean_ctor_set(v___x_5021_, 11, v___x_5024_);
v___x_5026_ = v___x_5021_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v_G_4984_);
lean_ctor_set(v_reuseFailAlloc_5027_, 1, v_y_4985_);
lean_ctor_set(v_reuseFailAlloc_5027_, 2, v_u_4986_);
lean_ctor_set(v_reuseFailAlloc_5027_, 3, v_Y_4987_);
lean_ctor_set(v_reuseFailAlloc_5027_, 4, v_D_4988_);
lean_ctor_set(v_reuseFailAlloc_5027_, 5, v_M_4989_);
lean_ctor_set(v_reuseFailAlloc_5027_, 6, v_L_4990_);
lean_ctor_set(v_reuseFailAlloc_5027_, 7, v_d_4991_);
lean_ctor_set(v_reuseFailAlloc_5027_, 8, v_Q_4992_);
lean_ctor_set(v_reuseFailAlloc_5027_, 9, v_q_4993_);
lean_ctor_set(v_reuseFailAlloc_5027_, 10, v_w_4994_);
lean_ctor_set(v_reuseFailAlloc_5027_, 11, v___x_5024_);
lean_ctor_set(v_reuseFailAlloc_5027_, 12, v_E_4995_);
lean_ctor_set(v_reuseFailAlloc_5027_, 13, v_e_4996_);
lean_ctor_set(v_reuseFailAlloc_5027_, 14, v_c_4997_);
lean_ctor_set(v_reuseFailAlloc_5027_, 15, v_F_4998_);
lean_ctor_set(v_reuseFailAlloc_5027_, 16, v_a_4999_);
lean_ctor_set(v_reuseFailAlloc_5027_, 17, v_b_5000_);
lean_ctor_set(v_reuseFailAlloc_5027_, 18, v_B_5001_);
lean_ctor_set(v_reuseFailAlloc_5027_, 19, v_h_5002_);
lean_ctor_set(v_reuseFailAlloc_5027_, 20, v_K_5003_);
lean_ctor_set(v_reuseFailAlloc_5027_, 21, v_k_5004_);
lean_ctor_set(v_reuseFailAlloc_5027_, 22, v_H_5005_);
lean_ctor_set(v_reuseFailAlloc_5027_, 23, v_m_5006_);
lean_ctor_set(v_reuseFailAlloc_5027_, 24, v_s_5007_);
lean_ctor_set(v_reuseFailAlloc_5027_, 25, v_S_5008_);
lean_ctor_set(v_reuseFailAlloc_5027_, 26, v_A_5009_);
lean_ctor_set(v_reuseFailAlloc_5027_, 27, v_n_5010_);
lean_ctor_set(v_reuseFailAlloc_5027_, 28, v_N_5011_);
lean_ctor_set(v_reuseFailAlloc_5027_, 29, v_V_5012_);
lean_ctor_set(v_reuseFailAlloc_5027_, 30, v_z_5013_);
lean_ctor_set(v_reuseFailAlloc_5027_, 31, v_zabbrev_5014_);
lean_ctor_set(v_reuseFailAlloc_5027_, 32, v_v_5015_);
lean_ctor_set(v_reuseFailAlloc_5027_, 33, v_O_5016_);
lean_ctor_set(v_reuseFailAlloc_5027_, 34, v_X_5017_);
lean_ctor_set(v_reuseFailAlloc_5027_, 35, v_x_5018_);
lean_ctor_set(v_reuseFailAlloc_5027_, 36, v_Z_5019_);
v___x_5026_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
return v___x_5026_;
}
}
}
}
}
case 12:
{
lean_object* v_G_5033_; lean_object* v_y_5034_; lean_object* v_u_5035_; lean_object* v_Y_5036_; lean_object* v_D_5037_; lean_object* v_M_5038_; lean_object* v_L_5039_; lean_object* v_d_5040_; lean_object* v_Q_5041_; lean_object* v_q_5042_; lean_object* v_w_5043_; lean_object* v_W_5044_; lean_object* v_e_5045_; lean_object* v_c_5046_; lean_object* v_F_5047_; lean_object* v_a_5048_; lean_object* v_b_5049_; lean_object* v_B_5050_; lean_object* v_h_5051_; lean_object* v_K_5052_; lean_object* v_k_5053_; lean_object* v_H_5054_; lean_object* v_m_5055_; lean_object* v_s_5056_; lean_object* v_S_5057_; lean_object* v_A_5058_; lean_object* v_n_5059_; lean_object* v_N_5060_; lean_object* v_V_5061_; lean_object* v_z_5062_; lean_object* v_zabbrev_5063_; lean_object* v_v_5064_; lean_object* v_O_5065_; lean_object* v_X_5066_; lean_object* v_x_5067_; lean_object* v_Z_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5076_; 
lean_dec_ref_known(v_modifier_4414_, 0);
v_G_5033_ = lean_ctor_get(v_date_4413_, 0);
v_y_5034_ = lean_ctor_get(v_date_4413_, 1);
v_u_5035_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5036_ = lean_ctor_get(v_date_4413_, 3);
v_D_5037_ = lean_ctor_get(v_date_4413_, 4);
v_M_5038_ = lean_ctor_get(v_date_4413_, 5);
v_L_5039_ = lean_ctor_get(v_date_4413_, 6);
v_d_5040_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5041_ = lean_ctor_get(v_date_4413_, 8);
v_q_5042_ = lean_ctor_get(v_date_4413_, 9);
v_w_5043_ = lean_ctor_get(v_date_4413_, 10);
v_W_5044_ = lean_ctor_get(v_date_4413_, 11);
v_e_5045_ = lean_ctor_get(v_date_4413_, 13);
v_c_5046_ = lean_ctor_get(v_date_4413_, 14);
v_F_5047_ = lean_ctor_get(v_date_4413_, 15);
v_a_5048_ = lean_ctor_get(v_date_4413_, 16);
v_b_5049_ = lean_ctor_get(v_date_4413_, 17);
v_B_5050_ = lean_ctor_get(v_date_4413_, 18);
v_h_5051_ = lean_ctor_get(v_date_4413_, 19);
v_K_5052_ = lean_ctor_get(v_date_4413_, 20);
v_k_5053_ = lean_ctor_get(v_date_4413_, 21);
v_H_5054_ = lean_ctor_get(v_date_4413_, 22);
v_m_5055_ = lean_ctor_get(v_date_4413_, 23);
v_s_5056_ = lean_ctor_get(v_date_4413_, 24);
v_S_5057_ = lean_ctor_get(v_date_4413_, 25);
v_A_5058_ = lean_ctor_get(v_date_4413_, 26);
v_n_5059_ = lean_ctor_get(v_date_4413_, 27);
v_N_5060_ = lean_ctor_get(v_date_4413_, 28);
v_V_5061_ = lean_ctor_get(v_date_4413_, 29);
v_z_5062_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_5063_ = lean_ctor_get(v_date_4413_, 31);
v_v_5064_ = lean_ctor_get(v_date_4413_, 32);
v_O_5065_ = lean_ctor_get(v_date_4413_, 33);
v_X_5066_ = lean_ctor_get(v_date_4413_, 34);
v_x_5067_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5068_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5076_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5076_ == 0)
{
lean_object* v_unused_5077_; 
v_unused_5077_ = lean_ctor_get(v_date_4413_, 12);
lean_dec(v_unused_5077_);
v___x_5070_ = v_date_4413_;
v_isShared_5071_ = v_isSharedCheck_5076_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_Z_5068_);
lean_inc(v_x_5067_);
lean_inc(v_X_5066_);
lean_inc(v_O_5065_);
lean_inc(v_v_5064_);
lean_inc(v_zabbrev_5063_);
lean_inc(v_z_5062_);
lean_inc(v_V_5061_);
lean_inc(v_N_5060_);
lean_inc(v_n_5059_);
lean_inc(v_A_5058_);
lean_inc(v_S_5057_);
lean_inc(v_s_5056_);
lean_inc(v_m_5055_);
lean_inc(v_H_5054_);
lean_inc(v_k_5053_);
lean_inc(v_K_5052_);
lean_inc(v_h_5051_);
lean_inc(v_B_5050_);
lean_inc(v_b_5049_);
lean_inc(v_a_5048_);
lean_inc(v_F_5047_);
lean_inc(v_c_5046_);
lean_inc(v_e_5045_);
lean_inc(v_W_5044_);
lean_inc(v_w_5043_);
lean_inc(v_q_5042_);
lean_inc(v_Q_5041_);
lean_inc(v_d_5040_);
lean_inc(v_L_5039_);
lean_inc(v_M_5038_);
lean_inc(v_D_5037_);
lean_inc(v_Y_5036_);
lean_inc(v_u_5035_);
lean_inc(v_y_5034_);
lean_inc(v_G_5033_);
lean_dec(v_date_4413_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5076_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5072_; lean_object* v___x_5074_; 
v___x_5072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5072_, 0, v_data_4415_);
if (v_isShared_5071_ == 0)
{
lean_ctor_set(v___x_5070_, 12, v___x_5072_);
v___x_5074_ = v___x_5070_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v_G_5033_);
lean_ctor_set(v_reuseFailAlloc_5075_, 1, v_y_5034_);
lean_ctor_set(v_reuseFailAlloc_5075_, 2, v_u_5035_);
lean_ctor_set(v_reuseFailAlloc_5075_, 3, v_Y_5036_);
lean_ctor_set(v_reuseFailAlloc_5075_, 4, v_D_5037_);
lean_ctor_set(v_reuseFailAlloc_5075_, 5, v_M_5038_);
lean_ctor_set(v_reuseFailAlloc_5075_, 6, v_L_5039_);
lean_ctor_set(v_reuseFailAlloc_5075_, 7, v_d_5040_);
lean_ctor_set(v_reuseFailAlloc_5075_, 8, v_Q_5041_);
lean_ctor_set(v_reuseFailAlloc_5075_, 9, v_q_5042_);
lean_ctor_set(v_reuseFailAlloc_5075_, 10, v_w_5043_);
lean_ctor_set(v_reuseFailAlloc_5075_, 11, v_W_5044_);
lean_ctor_set(v_reuseFailAlloc_5075_, 12, v___x_5072_);
lean_ctor_set(v_reuseFailAlloc_5075_, 13, v_e_5045_);
lean_ctor_set(v_reuseFailAlloc_5075_, 14, v_c_5046_);
lean_ctor_set(v_reuseFailAlloc_5075_, 15, v_F_5047_);
lean_ctor_set(v_reuseFailAlloc_5075_, 16, v_a_5048_);
lean_ctor_set(v_reuseFailAlloc_5075_, 17, v_b_5049_);
lean_ctor_set(v_reuseFailAlloc_5075_, 18, v_B_5050_);
lean_ctor_set(v_reuseFailAlloc_5075_, 19, v_h_5051_);
lean_ctor_set(v_reuseFailAlloc_5075_, 20, v_K_5052_);
lean_ctor_set(v_reuseFailAlloc_5075_, 21, v_k_5053_);
lean_ctor_set(v_reuseFailAlloc_5075_, 22, v_H_5054_);
lean_ctor_set(v_reuseFailAlloc_5075_, 23, v_m_5055_);
lean_ctor_set(v_reuseFailAlloc_5075_, 24, v_s_5056_);
lean_ctor_set(v_reuseFailAlloc_5075_, 25, v_S_5057_);
lean_ctor_set(v_reuseFailAlloc_5075_, 26, v_A_5058_);
lean_ctor_set(v_reuseFailAlloc_5075_, 27, v_n_5059_);
lean_ctor_set(v_reuseFailAlloc_5075_, 28, v_N_5060_);
lean_ctor_set(v_reuseFailAlloc_5075_, 29, v_V_5061_);
lean_ctor_set(v_reuseFailAlloc_5075_, 30, v_z_5062_);
lean_ctor_set(v_reuseFailAlloc_5075_, 31, v_zabbrev_5063_);
lean_ctor_set(v_reuseFailAlloc_5075_, 32, v_v_5064_);
lean_ctor_set(v_reuseFailAlloc_5075_, 33, v_O_5065_);
lean_ctor_set(v_reuseFailAlloc_5075_, 34, v_X_5066_);
lean_ctor_set(v_reuseFailAlloc_5075_, 35, v_x_5067_);
lean_ctor_set(v_reuseFailAlloc_5075_, 36, v_Z_5068_);
v___x_5074_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
return v___x_5074_;
}
}
}
case 13:
{
lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5128_; 
v_isSharedCheck_5128_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_5128_ == 0)
{
lean_object* v_unused_5129_; 
v_unused_5129_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_5129_);
v___x_5079_ = v_modifier_4414_;
v_isShared_5080_ = v_isSharedCheck_5128_;
goto v_resetjp_5078_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5128_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v_G_5081_; lean_object* v_y_5082_; lean_object* v_u_5083_; lean_object* v_Y_5084_; lean_object* v_D_5085_; lean_object* v_M_5086_; lean_object* v_L_5087_; lean_object* v_d_5088_; lean_object* v_Q_5089_; lean_object* v_q_5090_; lean_object* v_w_5091_; lean_object* v_W_5092_; lean_object* v_E_5093_; lean_object* v_c_5094_; lean_object* v_F_5095_; lean_object* v_a_5096_; lean_object* v_b_5097_; lean_object* v_B_5098_; lean_object* v_h_5099_; lean_object* v_K_5100_; lean_object* v_k_5101_; lean_object* v_H_5102_; lean_object* v_m_5103_; lean_object* v_s_5104_; lean_object* v_S_5105_; lean_object* v_A_5106_; lean_object* v_n_5107_; lean_object* v_N_5108_; lean_object* v_V_5109_; lean_object* v_z_5110_; lean_object* v_zabbrev_5111_; lean_object* v_v_5112_; lean_object* v_O_5113_; lean_object* v_X_5114_; lean_object* v_x_5115_; lean_object* v_Z_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5126_; 
v_G_5081_ = lean_ctor_get(v_date_4413_, 0);
v_y_5082_ = lean_ctor_get(v_date_4413_, 1);
v_u_5083_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5084_ = lean_ctor_get(v_date_4413_, 3);
v_D_5085_ = lean_ctor_get(v_date_4413_, 4);
v_M_5086_ = lean_ctor_get(v_date_4413_, 5);
v_L_5087_ = lean_ctor_get(v_date_4413_, 6);
v_d_5088_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5089_ = lean_ctor_get(v_date_4413_, 8);
v_q_5090_ = lean_ctor_get(v_date_4413_, 9);
v_w_5091_ = lean_ctor_get(v_date_4413_, 10);
v_W_5092_ = lean_ctor_get(v_date_4413_, 11);
v_E_5093_ = lean_ctor_get(v_date_4413_, 12);
v_c_5094_ = lean_ctor_get(v_date_4413_, 14);
v_F_5095_ = lean_ctor_get(v_date_4413_, 15);
v_a_5096_ = lean_ctor_get(v_date_4413_, 16);
v_b_5097_ = lean_ctor_get(v_date_4413_, 17);
v_B_5098_ = lean_ctor_get(v_date_4413_, 18);
v_h_5099_ = lean_ctor_get(v_date_4413_, 19);
v_K_5100_ = lean_ctor_get(v_date_4413_, 20);
v_k_5101_ = lean_ctor_get(v_date_4413_, 21);
v_H_5102_ = lean_ctor_get(v_date_4413_, 22);
v_m_5103_ = lean_ctor_get(v_date_4413_, 23);
v_s_5104_ = lean_ctor_get(v_date_4413_, 24);
v_S_5105_ = lean_ctor_get(v_date_4413_, 25);
v_A_5106_ = lean_ctor_get(v_date_4413_, 26);
v_n_5107_ = lean_ctor_get(v_date_4413_, 27);
v_N_5108_ = lean_ctor_get(v_date_4413_, 28);
v_V_5109_ = lean_ctor_get(v_date_4413_, 29);
v_z_5110_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_5111_ = lean_ctor_get(v_date_4413_, 31);
v_v_5112_ = lean_ctor_get(v_date_4413_, 32);
v_O_5113_ = lean_ctor_get(v_date_4413_, 33);
v_X_5114_ = lean_ctor_get(v_date_4413_, 34);
v_x_5115_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5116_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5126_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5126_ == 0)
{
lean_object* v_unused_5127_; 
v_unused_5127_ = lean_ctor_get(v_date_4413_, 13);
lean_dec(v_unused_5127_);
v___x_5118_ = v_date_4413_;
v_isShared_5119_ = v_isSharedCheck_5126_;
goto v_resetjp_5117_;
}
else
{
lean_inc(v_Z_5116_);
lean_inc(v_x_5115_);
lean_inc(v_X_5114_);
lean_inc(v_O_5113_);
lean_inc(v_v_5112_);
lean_inc(v_zabbrev_5111_);
lean_inc(v_z_5110_);
lean_inc(v_V_5109_);
lean_inc(v_N_5108_);
lean_inc(v_n_5107_);
lean_inc(v_A_5106_);
lean_inc(v_S_5105_);
lean_inc(v_s_5104_);
lean_inc(v_m_5103_);
lean_inc(v_H_5102_);
lean_inc(v_k_5101_);
lean_inc(v_K_5100_);
lean_inc(v_h_5099_);
lean_inc(v_B_5098_);
lean_inc(v_b_5097_);
lean_inc(v_a_5096_);
lean_inc(v_F_5095_);
lean_inc(v_c_5094_);
lean_inc(v_E_5093_);
lean_inc(v_W_5092_);
lean_inc(v_w_5091_);
lean_inc(v_q_5090_);
lean_inc(v_Q_5089_);
lean_inc(v_d_5088_);
lean_inc(v_L_5087_);
lean_inc(v_M_5086_);
lean_inc(v_D_5085_);
lean_inc(v_Y_5084_);
lean_inc(v_u_5083_);
lean_inc(v_y_5082_);
lean_inc(v_G_5081_);
lean_dec(v_date_4413_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5126_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v___x_5121_; 
if (v_isShared_5080_ == 0)
{
lean_ctor_set_tag(v___x_5079_, 1);
lean_ctor_set(v___x_5079_, 0, v_data_4415_);
v___x_5121_ = v___x_5079_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5125_; 
v_reuseFailAlloc_5125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5125_, 0, v_data_4415_);
v___x_5121_ = v_reuseFailAlloc_5125_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
lean_object* v___x_5123_; 
if (v_isShared_5119_ == 0)
{
lean_ctor_set(v___x_5118_, 13, v___x_5121_);
v___x_5123_ = v___x_5118_;
goto v_reusejp_5122_;
}
else
{
lean_object* v_reuseFailAlloc_5124_; 
v_reuseFailAlloc_5124_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_G_5081_);
lean_ctor_set(v_reuseFailAlloc_5124_, 1, v_y_5082_);
lean_ctor_set(v_reuseFailAlloc_5124_, 2, v_u_5083_);
lean_ctor_set(v_reuseFailAlloc_5124_, 3, v_Y_5084_);
lean_ctor_set(v_reuseFailAlloc_5124_, 4, v_D_5085_);
lean_ctor_set(v_reuseFailAlloc_5124_, 5, v_M_5086_);
lean_ctor_set(v_reuseFailAlloc_5124_, 6, v_L_5087_);
lean_ctor_set(v_reuseFailAlloc_5124_, 7, v_d_5088_);
lean_ctor_set(v_reuseFailAlloc_5124_, 8, v_Q_5089_);
lean_ctor_set(v_reuseFailAlloc_5124_, 9, v_q_5090_);
lean_ctor_set(v_reuseFailAlloc_5124_, 10, v_w_5091_);
lean_ctor_set(v_reuseFailAlloc_5124_, 11, v_W_5092_);
lean_ctor_set(v_reuseFailAlloc_5124_, 12, v_E_5093_);
lean_ctor_set(v_reuseFailAlloc_5124_, 13, v___x_5121_);
lean_ctor_set(v_reuseFailAlloc_5124_, 14, v_c_5094_);
lean_ctor_set(v_reuseFailAlloc_5124_, 15, v_F_5095_);
lean_ctor_set(v_reuseFailAlloc_5124_, 16, v_a_5096_);
lean_ctor_set(v_reuseFailAlloc_5124_, 17, v_b_5097_);
lean_ctor_set(v_reuseFailAlloc_5124_, 18, v_B_5098_);
lean_ctor_set(v_reuseFailAlloc_5124_, 19, v_h_5099_);
lean_ctor_set(v_reuseFailAlloc_5124_, 20, v_K_5100_);
lean_ctor_set(v_reuseFailAlloc_5124_, 21, v_k_5101_);
lean_ctor_set(v_reuseFailAlloc_5124_, 22, v_H_5102_);
lean_ctor_set(v_reuseFailAlloc_5124_, 23, v_m_5103_);
lean_ctor_set(v_reuseFailAlloc_5124_, 24, v_s_5104_);
lean_ctor_set(v_reuseFailAlloc_5124_, 25, v_S_5105_);
lean_ctor_set(v_reuseFailAlloc_5124_, 26, v_A_5106_);
lean_ctor_set(v_reuseFailAlloc_5124_, 27, v_n_5107_);
lean_ctor_set(v_reuseFailAlloc_5124_, 28, v_N_5108_);
lean_ctor_set(v_reuseFailAlloc_5124_, 29, v_V_5109_);
lean_ctor_set(v_reuseFailAlloc_5124_, 30, v_z_5110_);
lean_ctor_set(v_reuseFailAlloc_5124_, 31, v_zabbrev_5111_);
lean_ctor_set(v_reuseFailAlloc_5124_, 32, v_v_5112_);
lean_ctor_set(v_reuseFailAlloc_5124_, 33, v_O_5113_);
lean_ctor_set(v_reuseFailAlloc_5124_, 34, v_X_5114_);
lean_ctor_set(v_reuseFailAlloc_5124_, 35, v_x_5115_);
lean_ctor_set(v_reuseFailAlloc_5124_, 36, v_Z_5116_);
v___x_5123_ = v_reuseFailAlloc_5124_;
goto v_reusejp_5122_;
}
v_reusejp_5122_:
{
return v___x_5123_;
}
}
}
}
}
case 14:
{
lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5180_; 
v_isSharedCheck_5180_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_5180_ == 0)
{
lean_object* v_unused_5181_; 
v_unused_5181_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_5181_);
v___x_5131_ = v_modifier_4414_;
v_isShared_5132_ = v_isSharedCheck_5180_;
goto v_resetjp_5130_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5180_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
lean_object* v_G_5133_; lean_object* v_y_5134_; lean_object* v_u_5135_; lean_object* v_Y_5136_; lean_object* v_D_5137_; lean_object* v_M_5138_; lean_object* v_L_5139_; lean_object* v_d_5140_; lean_object* v_Q_5141_; lean_object* v_q_5142_; lean_object* v_w_5143_; lean_object* v_W_5144_; lean_object* v_E_5145_; lean_object* v_e_5146_; lean_object* v_F_5147_; lean_object* v_a_5148_; lean_object* v_b_5149_; lean_object* v_B_5150_; lean_object* v_h_5151_; lean_object* v_K_5152_; lean_object* v_k_5153_; lean_object* v_H_5154_; lean_object* v_m_5155_; lean_object* v_s_5156_; lean_object* v_S_5157_; lean_object* v_A_5158_; lean_object* v_n_5159_; lean_object* v_N_5160_; lean_object* v_V_5161_; lean_object* v_z_5162_; lean_object* v_zabbrev_5163_; lean_object* v_v_5164_; lean_object* v_O_5165_; lean_object* v_X_5166_; lean_object* v_x_5167_; lean_object* v_Z_5168_; lean_object* v___x_5170_; uint8_t v_isShared_5171_; uint8_t v_isSharedCheck_5178_; 
v_G_5133_ = lean_ctor_get(v_date_4413_, 0);
v_y_5134_ = lean_ctor_get(v_date_4413_, 1);
v_u_5135_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5136_ = lean_ctor_get(v_date_4413_, 3);
v_D_5137_ = lean_ctor_get(v_date_4413_, 4);
v_M_5138_ = lean_ctor_get(v_date_4413_, 5);
v_L_5139_ = lean_ctor_get(v_date_4413_, 6);
v_d_5140_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5141_ = lean_ctor_get(v_date_4413_, 8);
v_q_5142_ = lean_ctor_get(v_date_4413_, 9);
v_w_5143_ = lean_ctor_get(v_date_4413_, 10);
v_W_5144_ = lean_ctor_get(v_date_4413_, 11);
v_E_5145_ = lean_ctor_get(v_date_4413_, 12);
v_e_5146_ = lean_ctor_get(v_date_4413_, 13);
v_F_5147_ = lean_ctor_get(v_date_4413_, 15);
v_a_5148_ = lean_ctor_get(v_date_4413_, 16);
v_b_5149_ = lean_ctor_get(v_date_4413_, 17);
v_B_5150_ = lean_ctor_get(v_date_4413_, 18);
v_h_5151_ = lean_ctor_get(v_date_4413_, 19);
v_K_5152_ = lean_ctor_get(v_date_4413_, 20);
v_k_5153_ = lean_ctor_get(v_date_4413_, 21);
v_H_5154_ = lean_ctor_get(v_date_4413_, 22);
v_m_5155_ = lean_ctor_get(v_date_4413_, 23);
v_s_5156_ = lean_ctor_get(v_date_4413_, 24);
v_S_5157_ = lean_ctor_get(v_date_4413_, 25);
v_A_5158_ = lean_ctor_get(v_date_4413_, 26);
v_n_5159_ = lean_ctor_get(v_date_4413_, 27);
v_N_5160_ = lean_ctor_get(v_date_4413_, 28);
v_V_5161_ = lean_ctor_get(v_date_4413_, 29);
v_z_5162_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_5163_ = lean_ctor_get(v_date_4413_, 31);
v_v_5164_ = lean_ctor_get(v_date_4413_, 32);
v_O_5165_ = lean_ctor_get(v_date_4413_, 33);
v_X_5166_ = lean_ctor_get(v_date_4413_, 34);
v_x_5167_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5168_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5178_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5178_ == 0)
{
lean_object* v_unused_5179_; 
v_unused_5179_ = lean_ctor_get(v_date_4413_, 14);
lean_dec(v_unused_5179_);
v___x_5170_ = v_date_4413_;
v_isShared_5171_ = v_isSharedCheck_5178_;
goto v_resetjp_5169_;
}
else
{
lean_inc(v_Z_5168_);
lean_inc(v_x_5167_);
lean_inc(v_X_5166_);
lean_inc(v_O_5165_);
lean_inc(v_v_5164_);
lean_inc(v_zabbrev_5163_);
lean_inc(v_z_5162_);
lean_inc(v_V_5161_);
lean_inc(v_N_5160_);
lean_inc(v_n_5159_);
lean_inc(v_A_5158_);
lean_inc(v_S_5157_);
lean_inc(v_s_5156_);
lean_inc(v_m_5155_);
lean_inc(v_H_5154_);
lean_inc(v_k_5153_);
lean_inc(v_K_5152_);
lean_inc(v_h_5151_);
lean_inc(v_B_5150_);
lean_inc(v_b_5149_);
lean_inc(v_a_5148_);
lean_inc(v_F_5147_);
lean_inc(v_e_5146_);
lean_inc(v_E_5145_);
lean_inc(v_W_5144_);
lean_inc(v_w_5143_);
lean_inc(v_q_5142_);
lean_inc(v_Q_5141_);
lean_inc(v_d_5140_);
lean_inc(v_L_5139_);
lean_inc(v_M_5138_);
lean_inc(v_D_5137_);
lean_inc(v_Y_5136_);
lean_inc(v_u_5135_);
lean_inc(v_y_5134_);
lean_inc(v_G_5133_);
lean_dec(v_date_4413_);
v___x_5170_ = lean_box(0);
v_isShared_5171_ = v_isSharedCheck_5178_;
goto v_resetjp_5169_;
}
v_resetjp_5169_:
{
lean_object* v___x_5173_; 
if (v_isShared_5132_ == 0)
{
lean_ctor_set_tag(v___x_5131_, 1);
lean_ctor_set(v___x_5131_, 0, v_data_4415_);
v___x_5173_ = v___x_5131_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5177_; 
v_reuseFailAlloc_5177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5177_, 0, v_data_4415_);
v___x_5173_ = v_reuseFailAlloc_5177_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
lean_object* v___x_5175_; 
if (v_isShared_5171_ == 0)
{
lean_ctor_set(v___x_5170_, 14, v___x_5173_);
v___x_5175_ = v___x_5170_;
goto v_reusejp_5174_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v_G_5133_);
lean_ctor_set(v_reuseFailAlloc_5176_, 1, v_y_5134_);
lean_ctor_set(v_reuseFailAlloc_5176_, 2, v_u_5135_);
lean_ctor_set(v_reuseFailAlloc_5176_, 3, v_Y_5136_);
lean_ctor_set(v_reuseFailAlloc_5176_, 4, v_D_5137_);
lean_ctor_set(v_reuseFailAlloc_5176_, 5, v_M_5138_);
lean_ctor_set(v_reuseFailAlloc_5176_, 6, v_L_5139_);
lean_ctor_set(v_reuseFailAlloc_5176_, 7, v_d_5140_);
lean_ctor_set(v_reuseFailAlloc_5176_, 8, v_Q_5141_);
lean_ctor_set(v_reuseFailAlloc_5176_, 9, v_q_5142_);
lean_ctor_set(v_reuseFailAlloc_5176_, 10, v_w_5143_);
lean_ctor_set(v_reuseFailAlloc_5176_, 11, v_W_5144_);
lean_ctor_set(v_reuseFailAlloc_5176_, 12, v_E_5145_);
lean_ctor_set(v_reuseFailAlloc_5176_, 13, v_e_5146_);
lean_ctor_set(v_reuseFailAlloc_5176_, 14, v___x_5173_);
lean_ctor_set(v_reuseFailAlloc_5176_, 15, v_F_5147_);
lean_ctor_set(v_reuseFailAlloc_5176_, 16, v_a_5148_);
lean_ctor_set(v_reuseFailAlloc_5176_, 17, v_b_5149_);
lean_ctor_set(v_reuseFailAlloc_5176_, 18, v_B_5150_);
lean_ctor_set(v_reuseFailAlloc_5176_, 19, v_h_5151_);
lean_ctor_set(v_reuseFailAlloc_5176_, 20, v_K_5152_);
lean_ctor_set(v_reuseFailAlloc_5176_, 21, v_k_5153_);
lean_ctor_set(v_reuseFailAlloc_5176_, 22, v_H_5154_);
lean_ctor_set(v_reuseFailAlloc_5176_, 23, v_m_5155_);
lean_ctor_set(v_reuseFailAlloc_5176_, 24, v_s_5156_);
lean_ctor_set(v_reuseFailAlloc_5176_, 25, v_S_5157_);
lean_ctor_set(v_reuseFailAlloc_5176_, 26, v_A_5158_);
lean_ctor_set(v_reuseFailAlloc_5176_, 27, v_n_5159_);
lean_ctor_set(v_reuseFailAlloc_5176_, 28, v_N_5160_);
lean_ctor_set(v_reuseFailAlloc_5176_, 29, v_V_5161_);
lean_ctor_set(v_reuseFailAlloc_5176_, 30, v_z_5162_);
lean_ctor_set(v_reuseFailAlloc_5176_, 31, v_zabbrev_5163_);
lean_ctor_set(v_reuseFailAlloc_5176_, 32, v_v_5164_);
lean_ctor_set(v_reuseFailAlloc_5176_, 33, v_O_5165_);
lean_ctor_set(v_reuseFailAlloc_5176_, 34, v_X_5166_);
lean_ctor_set(v_reuseFailAlloc_5176_, 35, v_x_5167_);
lean_ctor_set(v_reuseFailAlloc_5176_, 36, v_Z_5168_);
v___x_5175_ = v_reuseFailAlloc_5176_;
goto v_reusejp_5174_;
}
v_reusejp_5174_:
{
return v___x_5175_;
}
}
}
}
}
case 15:
{
lean_object* v___x_5183_; uint8_t v_isShared_5184_; uint8_t v_isSharedCheck_5232_; 
v_isSharedCheck_5232_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_5232_ == 0)
{
lean_object* v_unused_5233_; 
v_unused_5233_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_5233_);
v___x_5183_ = v_modifier_4414_;
v_isShared_5184_ = v_isSharedCheck_5232_;
goto v_resetjp_5182_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_5183_ = lean_box(0);
v_isShared_5184_ = v_isSharedCheck_5232_;
goto v_resetjp_5182_;
}
v_resetjp_5182_:
{
lean_object* v_G_5185_; lean_object* v_y_5186_; lean_object* v_u_5187_; lean_object* v_Y_5188_; lean_object* v_D_5189_; lean_object* v_M_5190_; lean_object* v_L_5191_; lean_object* v_d_5192_; lean_object* v_Q_5193_; lean_object* v_q_5194_; lean_object* v_w_5195_; lean_object* v_W_5196_; lean_object* v_E_5197_; lean_object* v_e_5198_; lean_object* v_c_5199_; lean_object* v_a_5200_; lean_object* v_b_5201_; lean_object* v_B_5202_; lean_object* v_h_5203_; lean_object* v_K_5204_; lean_object* v_k_5205_; lean_object* v_H_5206_; lean_object* v_m_5207_; lean_object* v_s_5208_; lean_object* v_S_5209_; lean_object* v_A_5210_; lean_object* v_n_5211_; lean_object* v_N_5212_; lean_object* v_V_5213_; lean_object* v_z_5214_; lean_object* v_zabbrev_5215_; lean_object* v_v_5216_; lean_object* v_O_5217_; lean_object* v_X_5218_; lean_object* v_x_5219_; lean_object* v_Z_5220_; lean_object* v___x_5222_; uint8_t v_isShared_5223_; uint8_t v_isSharedCheck_5230_; 
v_G_5185_ = lean_ctor_get(v_date_4413_, 0);
v_y_5186_ = lean_ctor_get(v_date_4413_, 1);
v_u_5187_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5188_ = lean_ctor_get(v_date_4413_, 3);
v_D_5189_ = lean_ctor_get(v_date_4413_, 4);
v_M_5190_ = lean_ctor_get(v_date_4413_, 5);
v_L_5191_ = lean_ctor_get(v_date_4413_, 6);
v_d_5192_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5193_ = lean_ctor_get(v_date_4413_, 8);
v_q_5194_ = lean_ctor_get(v_date_4413_, 9);
v_w_5195_ = lean_ctor_get(v_date_4413_, 10);
v_W_5196_ = lean_ctor_get(v_date_4413_, 11);
v_E_5197_ = lean_ctor_get(v_date_4413_, 12);
v_e_5198_ = lean_ctor_get(v_date_4413_, 13);
v_c_5199_ = lean_ctor_get(v_date_4413_, 14);
v_a_5200_ = lean_ctor_get(v_date_4413_, 16);
v_b_5201_ = lean_ctor_get(v_date_4413_, 17);
v_B_5202_ = lean_ctor_get(v_date_4413_, 18);
v_h_5203_ = lean_ctor_get(v_date_4413_, 19);
v_K_5204_ = lean_ctor_get(v_date_4413_, 20);
v_k_5205_ = lean_ctor_get(v_date_4413_, 21);
v_H_5206_ = lean_ctor_get(v_date_4413_, 22);
v_m_5207_ = lean_ctor_get(v_date_4413_, 23);
v_s_5208_ = lean_ctor_get(v_date_4413_, 24);
v_S_5209_ = lean_ctor_get(v_date_4413_, 25);
v_A_5210_ = lean_ctor_get(v_date_4413_, 26);
v_n_5211_ = lean_ctor_get(v_date_4413_, 27);
v_N_5212_ = lean_ctor_get(v_date_4413_, 28);
v_V_5213_ = lean_ctor_get(v_date_4413_, 29);
v_z_5214_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_5215_ = lean_ctor_get(v_date_4413_, 31);
v_v_5216_ = lean_ctor_get(v_date_4413_, 32);
v_O_5217_ = lean_ctor_get(v_date_4413_, 33);
v_X_5218_ = lean_ctor_get(v_date_4413_, 34);
v_x_5219_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5220_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5230_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5230_ == 0)
{
lean_object* v_unused_5231_; 
v_unused_5231_ = lean_ctor_get(v_date_4413_, 15);
lean_dec(v_unused_5231_);
v___x_5222_ = v_date_4413_;
v_isShared_5223_ = v_isSharedCheck_5230_;
goto v_resetjp_5221_;
}
else
{
lean_inc(v_Z_5220_);
lean_inc(v_x_5219_);
lean_inc(v_X_5218_);
lean_inc(v_O_5217_);
lean_inc(v_v_5216_);
lean_inc(v_zabbrev_5215_);
lean_inc(v_z_5214_);
lean_inc(v_V_5213_);
lean_inc(v_N_5212_);
lean_inc(v_n_5211_);
lean_inc(v_A_5210_);
lean_inc(v_S_5209_);
lean_inc(v_s_5208_);
lean_inc(v_m_5207_);
lean_inc(v_H_5206_);
lean_inc(v_k_5205_);
lean_inc(v_K_5204_);
lean_inc(v_h_5203_);
lean_inc(v_B_5202_);
lean_inc(v_b_5201_);
lean_inc(v_a_5200_);
lean_inc(v_c_5199_);
lean_inc(v_e_5198_);
lean_inc(v_E_5197_);
lean_inc(v_W_5196_);
lean_inc(v_w_5195_);
lean_inc(v_q_5194_);
lean_inc(v_Q_5193_);
lean_inc(v_d_5192_);
lean_inc(v_L_5191_);
lean_inc(v_M_5190_);
lean_inc(v_D_5189_);
lean_inc(v_Y_5188_);
lean_inc(v_u_5187_);
lean_inc(v_y_5186_);
lean_inc(v_G_5185_);
lean_dec(v_date_4413_);
v___x_5222_ = lean_box(0);
v_isShared_5223_ = v_isSharedCheck_5230_;
goto v_resetjp_5221_;
}
v_resetjp_5221_:
{
lean_object* v___x_5225_; 
if (v_isShared_5184_ == 0)
{
lean_ctor_set_tag(v___x_5183_, 1);
lean_ctor_set(v___x_5183_, 0, v_data_4415_);
v___x_5225_ = v___x_5183_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5229_; 
v_reuseFailAlloc_5229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5229_, 0, v_data_4415_);
v___x_5225_ = v_reuseFailAlloc_5229_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
lean_object* v___x_5227_; 
if (v_isShared_5223_ == 0)
{
lean_ctor_set(v___x_5222_, 15, v___x_5225_);
v___x_5227_ = v___x_5222_;
goto v_reusejp_5226_;
}
else
{
lean_object* v_reuseFailAlloc_5228_; 
v_reuseFailAlloc_5228_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5228_, 0, v_G_5185_);
lean_ctor_set(v_reuseFailAlloc_5228_, 1, v_y_5186_);
lean_ctor_set(v_reuseFailAlloc_5228_, 2, v_u_5187_);
lean_ctor_set(v_reuseFailAlloc_5228_, 3, v_Y_5188_);
lean_ctor_set(v_reuseFailAlloc_5228_, 4, v_D_5189_);
lean_ctor_set(v_reuseFailAlloc_5228_, 5, v_M_5190_);
lean_ctor_set(v_reuseFailAlloc_5228_, 6, v_L_5191_);
lean_ctor_set(v_reuseFailAlloc_5228_, 7, v_d_5192_);
lean_ctor_set(v_reuseFailAlloc_5228_, 8, v_Q_5193_);
lean_ctor_set(v_reuseFailAlloc_5228_, 9, v_q_5194_);
lean_ctor_set(v_reuseFailAlloc_5228_, 10, v_w_5195_);
lean_ctor_set(v_reuseFailAlloc_5228_, 11, v_W_5196_);
lean_ctor_set(v_reuseFailAlloc_5228_, 12, v_E_5197_);
lean_ctor_set(v_reuseFailAlloc_5228_, 13, v_e_5198_);
lean_ctor_set(v_reuseFailAlloc_5228_, 14, v_c_5199_);
lean_ctor_set(v_reuseFailAlloc_5228_, 15, v___x_5225_);
lean_ctor_set(v_reuseFailAlloc_5228_, 16, v_a_5200_);
lean_ctor_set(v_reuseFailAlloc_5228_, 17, v_b_5201_);
lean_ctor_set(v_reuseFailAlloc_5228_, 18, v_B_5202_);
lean_ctor_set(v_reuseFailAlloc_5228_, 19, v_h_5203_);
lean_ctor_set(v_reuseFailAlloc_5228_, 20, v_K_5204_);
lean_ctor_set(v_reuseFailAlloc_5228_, 21, v_k_5205_);
lean_ctor_set(v_reuseFailAlloc_5228_, 22, v_H_5206_);
lean_ctor_set(v_reuseFailAlloc_5228_, 23, v_m_5207_);
lean_ctor_set(v_reuseFailAlloc_5228_, 24, v_s_5208_);
lean_ctor_set(v_reuseFailAlloc_5228_, 25, v_S_5209_);
lean_ctor_set(v_reuseFailAlloc_5228_, 26, v_A_5210_);
lean_ctor_set(v_reuseFailAlloc_5228_, 27, v_n_5211_);
lean_ctor_set(v_reuseFailAlloc_5228_, 28, v_N_5212_);
lean_ctor_set(v_reuseFailAlloc_5228_, 29, v_V_5213_);
lean_ctor_set(v_reuseFailAlloc_5228_, 30, v_z_5214_);
lean_ctor_set(v_reuseFailAlloc_5228_, 31, v_zabbrev_5215_);
lean_ctor_set(v_reuseFailAlloc_5228_, 32, v_v_5216_);
lean_ctor_set(v_reuseFailAlloc_5228_, 33, v_O_5217_);
lean_ctor_set(v_reuseFailAlloc_5228_, 34, v_X_5218_);
lean_ctor_set(v_reuseFailAlloc_5228_, 35, v_x_5219_);
lean_ctor_set(v_reuseFailAlloc_5228_, 36, v_Z_5220_);
v___x_5227_ = v_reuseFailAlloc_5228_;
goto v_reusejp_5226_;
}
v_reusejp_5226_:
{
return v___x_5227_;
}
}
}
}
}
case 16:
{
lean_object* v_G_5234_; lean_object* v_y_5235_; lean_object* v_u_5236_; lean_object* v_Y_5237_; lean_object* v_D_5238_; lean_object* v_M_5239_; lean_object* v_L_5240_; lean_object* v_d_5241_; lean_object* v_Q_5242_; lean_object* v_q_5243_; lean_object* v_w_5244_; lean_object* v_W_5245_; lean_object* v_E_5246_; lean_object* v_e_5247_; lean_object* v_c_5248_; lean_object* v_F_5249_; lean_object* v_b_5250_; lean_object* v_B_5251_; lean_object* v_h_5252_; lean_object* v_K_5253_; lean_object* v_k_5254_; lean_object* v_H_5255_; lean_object* v_m_5256_; lean_object* v_s_5257_; lean_object* v_S_5258_; lean_object* v_A_5259_; lean_object* v_n_5260_; lean_object* v_N_5261_; lean_object* v_V_5262_; lean_object* v_z_5263_; lean_object* v_zabbrev_5264_; lean_object* v_v_5265_; lean_object* v_O_5266_; lean_object* v_X_5267_; lean_object* v_x_5268_; lean_object* v_Z_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5277_; 
lean_dec_ref_known(v_modifier_4414_, 0);
v_G_5234_ = lean_ctor_get(v_date_4413_, 0);
v_y_5235_ = lean_ctor_get(v_date_4413_, 1);
v_u_5236_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5237_ = lean_ctor_get(v_date_4413_, 3);
v_D_5238_ = lean_ctor_get(v_date_4413_, 4);
v_M_5239_ = lean_ctor_get(v_date_4413_, 5);
v_L_5240_ = lean_ctor_get(v_date_4413_, 6);
v_d_5241_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5242_ = lean_ctor_get(v_date_4413_, 8);
v_q_5243_ = lean_ctor_get(v_date_4413_, 9);
v_w_5244_ = lean_ctor_get(v_date_4413_, 10);
v_W_5245_ = lean_ctor_get(v_date_4413_, 11);
v_E_5246_ = lean_ctor_get(v_date_4413_, 12);
v_e_5247_ = lean_ctor_get(v_date_4413_, 13);
v_c_5248_ = lean_ctor_get(v_date_4413_, 14);
v_F_5249_ = lean_ctor_get(v_date_4413_, 15);
v_b_5250_ = lean_ctor_get(v_date_4413_, 17);
v_B_5251_ = lean_ctor_get(v_date_4413_, 18);
v_h_5252_ = lean_ctor_get(v_date_4413_, 19);
v_K_5253_ = lean_ctor_get(v_date_4413_, 20);
v_k_5254_ = lean_ctor_get(v_date_4413_, 21);
v_H_5255_ = lean_ctor_get(v_date_4413_, 22);
v_m_5256_ = lean_ctor_get(v_date_4413_, 23);
v_s_5257_ = lean_ctor_get(v_date_4413_, 24);
v_S_5258_ = lean_ctor_get(v_date_4413_, 25);
v_A_5259_ = lean_ctor_get(v_date_4413_, 26);
v_n_5260_ = lean_ctor_get(v_date_4413_, 27);
v_N_5261_ = lean_ctor_get(v_date_4413_, 28);
v_V_5262_ = lean_ctor_get(v_date_4413_, 29);
v_z_5263_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_5264_ = lean_ctor_get(v_date_4413_, 31);
v_v_5265_ = lean_ctor_get(v_date_4413_, 32);
v_O_5266_ = lean_ctor_get(v_date_4413_, 33);
v_X_5267_ = lean_ctor_get(v_date_4413_, 34);
v_x_5268_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5269_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5277_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5277_ == 0)
{
lean_object* v_unused_5278_; 
v_unused_5278_ = lean_ctor_get(v_date_4413_, 16);
lean_dec(v_unused_5278_);
v___x_5271_ = v_date_4413_;
v_isShared_5272_ = v_isSharedCheck_5277_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_Z_5269_);
lean_inc(v_x_5268_);
lean_inc(v_X_5267_);
lean_inc(v_O_5266_);
lean_inc(v_v_5265_);
lean_inc(v_zabbrev_5264_);
lean_inc(v_z_5263_);
lean_inc(v_V_5262_);
lean_inc(v_N_5261_);
lean_inc(v_n_5260_);
lean_inc(v_A_5259_);
lean_inc(v_S_5258_);
lean_inc(v_s_5257_);
lean_inc(v_m_5256_);
lean_inc(v_H_5255_);
lean_inc(v_k_5254_);
lean_inc(v_K_5253_);
lean_inc(v_h_5252_);
lean_inc(v_B_5251_);
lean_inc(v_b_5250_);
lean_inc(v_F_5249_);
lean_inc(v_c_5248_);
lean_inc(v_e_5247_);
lean_inc(v_E_5246_);
lean_inc(v_W_5245_);
lean_inc(v_w_5244_);
lean_inc(v_q_5243_);
lean_inc(v_Q_5242_);
lean_inc(v_d_5241_);
lean_inc(v_L_5240_);
lean_inc(v_M_5239_);
lean_inc(v_D_5238_);
lean_inc(v_Y_5237_);
lean_inc(v_u_5236_);
lean_inc(v_y_5235_);
lean_inc(v_G_5234_);
lean_dec(v_date_4413_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5277_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5273_; lean_object* v___x_5275_; 
v___x_5273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5273_, 0, v_data_4415_);
if (v_isShared_5272_ == 0)
{
lean_ctor_set(v___x_5271_, 16, v___x_5273_);
v___x_5275_ = v___x_5271_;
goto v_reusejp_5274_;
}
else
{
lean_object* v_reuseFailAlloc_5276_; 
v_reuseFailAlloc_5276_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5276_, 0, v_G_5234_);
lean_ctor_set(v_reuseFailAlloc_5276_, 1, v_y_5235_);
lean_ctor_set(v_reuseFailAlloc_5276_, 2, v_u_5236_);
lean_ctor_set(v_reuseFailAlloc_5276_, 3, v_Y_5237_);
lean_ctor_set(v_reuseFailAlloc_5276_, 4, v_D_5238_);
lean_ctor_set(v_reuseFailAlloc_5276_, 5, v_M_5239_);
lean_ctor_set(v_reuseFailAlloc_5276_, 6, v_L_5240_);
lean_ctor_set(v_reuseFailAlloc_5276_, 7, v_d_5241_);
lean_ctor_set(v_reuseFailAlloc_5276_, 8, v_Q_5242_);
lean_ctor_set(v_reuseFailAlloc_5276_, 9, v_q_5243_);
lean_ctor_set(v_reuseFailAlloc_5276_, 10, v_w_5244_);
lean_ctor_set(v_reuseFailAlloc_5276_, 11, v_W_5245_);
lean_ctor_set(v_reuseFailAlloc_5276_, 12, v_E_5246_);
lean_ctor_set(v_reuseFailAlloc_5276_, 13, v_e_5247_);
lean_ctor_set(v_reuseFailAlloc_5276_, 14, v_c_5248_);
lean_ctor_set(v_reuseFailAlloc_5276_, 15, v_F_5249_);
lean_ctor_set(v_reuseFailAlloc_5276_, 16, v___x_5273_);
lean_ctor_set(v_reuseFailAlloc_5276_, 17, v_b_5250_);
lean_ctor_set(v_reuseFailAlloc_5276_, 18, v_B_5251_);
lean_ctor_set(v_reuseFailAlloc_5276_, 19, v_h_5252_);
lean_ctor_set(v_reuseFailAlloc_5276_, 20, v_K_5253_);
lean_ctor_set(v_reuseFailAlloc_5276_, 21, v_k_5254_);
lean_ctor_set(v_reuseFailAlloc_5276_, 22, v_H_5255_);
lean_ctor_set(v_reuseFailAlloc_5276_, 23, v_m_5256_);
lean_ctor_set(v_reuseFailAlloc_5276_, 24, v_s_5257_);
lean_ctor_set(v_reuseFailAlloc_5276_, 25, v_S_5258_);
lean_ctor_set(v_reuseFailAlloc_5276_, 26, v_A_5259_);
lean_ctor_set(v_reuseFailAlloc_5276_, 27, v_n_5260_);
lean_ctor_set(v_reuseFailAlloc_5276_, 28, v_N_5261_);
lean_ctor_set(v_reuseFailAlloc_5276_, 29, v_V_5262_);
lean_ctor_set(v_reuseFailAlloc_5276_, 30, v_z_5263_);
lean_ctor_set(v_reuseFailAlloc_5276_, 31, v_zabbrev_5264_);
lean_ctor_set(v_reuseFailAlloc_5276_, 32, v_v_5265_);
lean_ctor_set(v_reuseFailAlloc_5276_, 33, v_O_5266_);
lean_ctor_set(v_reuseFailAlloc_5276_, 34, v_X_5267_);
lean_ctor_set(v_reuseFailAlloc_5276_, 35, v_x_5268_);
lean_ctor_set(v_reuseFailAlloc_5276_, 36, v_Z_5269_);
v___x_5275_ = v_reuseFailAlloc_5276_;
goto v_reusejp_5274_;
}
v_reusejp_5274_:
{
return v___x_5275_;
}
}
}
case 17:
{
lean_object* v_G_5279_; lean_object* v_y_5280_; lean_object* v_u_5281_; lean_object* v_Y_5282_; lean_object* v_D_5283_; lean_object* v_M_5284_; lean_object* v_L_5285_; lean_object* v_d_5286_; lean_object* v_Q_5287_; lean_object* v_q_5288_; lean_object* v_w_5289_; lean_object* v_W_5290_; lean_object* v_E_5291_; lean_object* v_e_5292_; lean_object* v_c_5293_; lean_object* v_F_5294_; lean_object* v_a_5295_; lean_object* v_B_5296_; lean_object* v_h_5297_; lean_object* v_K_5298_; lean_object* v_k_5299_; lean_object* v_H_5300_; lean_object* v_m_5301_; lean_object* v_s_5302_; lean_object* v_S_5303_; lean_object* v_A_5304_; lean_object* v_n_5305_; lean_object* v_N_5306_; lean_object* v_V_5307_; lean_object* v_z_5308_; lean_object* v_zabbrev_5309_; lean_object* v_v_5310_; lean_object* v_O_5311_; lean_object* v_X_5312_; lean_object* v_x_5313_; lean_object* v_Z_5314_; lean_object* v___x_5316_; uint8_t v_isShared_5317_; uint8_t v_isSharedCheck_5322_; 
lean_dec_ref_known(v_modifier_4414_, 0);
v_G_5279_ = lean_ctor_get(v_date_4413_, 0);
v_y_5280_ = lean_ctor_get(v_date_4413_, 1);
v_u_5281_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5282_ = lean_ctor_get(v_date_4413_, 3);
v_D_5283_ = lean_ctor_get(v_date_4413_, 4);
v_M_5284_ = lean_ctor_get(v_date_4413_, 5);
v_L_5285_ = lean_ctor_get(v_date_4413_, 6);
v_d_5286_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5287_ = lean_ctor_get(v_date_4413_, 8);
v_q_5288_ = lean_ctor_get(v_date_4413_, 9);
v_w_5289_ = lean_ctor_get(v_date_4413_, 10);
v_W_5290_ = lean_ctor_get(v_date_4413_, 11);
v_E_5291_ = lean_ctor_get(v_date_4413_, 12);
v_e_5292_ = lean_ctor_get(v_date_4413_, 13);
v_c_5293_ = lean_ctor_get(v_date_4413_, 14);
v_F_5294_ = lean_ctor_get(v_date_4413_, 15);
v_a_5295_ = lean_ctor_get(v_date_4413_, 16);
v_B_5296_ = lean_ctor_get(v_date_4413_, 18);
v_h_5297_ = lean_ctor_get(v_date_4413_, 19);
v_K_5298_ = lean_ctor_get(v_date_4413_, 20);
v_k_5299_ = lean_ctor_get(v_date_4413_, 21);
v_H_5300_ = lean_ctor_get(v_date_4413_, 22);
v_m_5301_ = lean_ctor_get(v_date_4413_, 23);
v_s_5302_ = lean_ctor_get(v_date_4413_, 24);
v_S_5303_ = lean_ctor_get(v_date_4413_, 25);
v_A_5304_ = lean_ctor_get(v_date_4413_, 26);
v_n_5305_ = lean_ctor_get(v_date_4413_, 27);
v_N_5306_ = lean_ctor_get(v_date_4413_, 28);
v_V_5307_ = lean_ctor_get(v_date_4413_, 29);
v_z_5308_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_5309_ = lean_ctor_get(v_date_4413_, 31);
v_v_5310_ = lean_ctor_get(v_date_4413_, 32);
v_O_5311_ = lean_ctor_get(v_date_4413_, 33);
v_X_5312_ = lean_ctor_get(v_date_4413_, 34);
v_x_5313_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5314_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5322_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5322_ == 0)
{
lean_object* v_unused_5323_; 
v_unused_5323_ = lean_ctor_get(v_date_4413_, 17);
lean_dec(v_unused_5323_);
v___x_5316_ = v_date_4413_;
v_isShared_5317_ = v_isSharedCheck_5322_;
goto v_resetjp_5315_;
}
else
{
lean_inc(v_Z_5314_);
lean_inc(v_x_5313_);
lean_inc(v_X_5312_);
lean_inc(v_O_5311_);
lean_inc(v_v_5310_);
lean_inc(v_zabbrev_5309_);
lean_inc(v_z_5308_);
lean_inc(v_V_5307_);
lean_inc(v_N_5306_);
lean_inc(v_n_5305_);
lean_inc(v_A_5304_);
lean_inc(v_S_5303_);
lean_inc(v_s_5302_);
lean_inc(v_m_5301_);
lean_inc(v_H_5300_);
lean_inc(v_k_5299_);
lean_inc(v_K_5298_);
lean_inc(v_h_5297_);
lean_inc(v_B_5296_);
lean_inc(v_a_5295_);
lean_inc(v_F_5294_);
lean_inc(v_c_5293_);
lean_inc(v_e_5292_);
lean_inc(v_E_5291_);
lean_inc(v_W_5290_);
lean_inc(v_w_5289_);
lean_inc(v_q_5288_);
lean_inc(v_Q_5287_);
lean_inc(v_d_5286_);
lean_inc(v_L_5285_);
lean_inc(v_M_5284_);
lean_inc(v_D_5283_);
lean_inc(v_Y_5282_);
lean_inc(v_u_5281_);
lean_inc(v_y_5280_);
lean_inc(v_G_5279_);
lean_dec(v_date_4413_);
v___x_5316_ = lean_box(0);
v_isShared_5317_ = v_isSharedCheck_5322_;
goto v_resetjp_5315_;
}
v_resetjp_5315_:
{
lean_object* v___x_5318_; lean_object* v___x_5320_; 
v___x_5318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5318_, 0, v_data_4415_);
if (v_isShared_5317_ == 0)
{
lean_ctor_set(v___x_5316_, 17, v___x_5318_);
v___x_5320_ = v___x_5316_;
goto v_reusejp_5319_;
}
else
{
lean_object* v_reuseFailAlloc_5321_; 
v_reuseFailAlloc_5321_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5321_, 0, v_G_5279_);
lean_ctor_set(v_reuseFailAlloc_5321_, 1, v_y_5280_);
lean_ctor_set(v_reuseFailAlloc_5321_, 2, v_u_5281_);
lean_ctor_set(v_reuseFailAlloc_5321_, 3, v_Y_5282_);
lean_ctor_set(v_reuseFailAlloc_5321_, 4, v_D_5283_);
lean_ctor_set(v_reuseFailAlloc_5321_, 5, v_M_5284_);
lean_ctor_set(v_reuseFailAlloc_5321_, 6, v_L_5285_);
lean_ctor_set(v_reuseFailAlloc_5321_, 7, v_d_5286_);
lean_ctor_set(v_reuseFailAlloc_5321_, 8, v_Q_5287_);
lean_ctor_set(v_reuseFailAlloc_5321_, 9, v_q_5288_);
lean_ctor_set(v_reuseFailAlloc_5321_, 10, v_w_5289_);
lean_ctor_set(v_reuseFailAlloc_5321_, 11, v_W_5290_);
lean_ctor_set(v_reuseFailAlloc_5321_, 12, v_E_5291_);
lean_ctor_set(v_reuseFailAlloc_5321_, 13, v_e_5292_);
lean_ctor_set(v_reuseFailAlloc_5321_, 14, v_c_5293_);
lean_ctor_set(v_reuseFailAlloc_5321_, 15, v_F_5294_);
lean_ctor_set(v_reuseFailAlloc_5321_, 16, v_a_5295_);
lean_ctor_set(v_reuseFailAlloc_5321_, 17, v___x_5318_);
lean_ctor_set(v_reuseFailAlloc_5321_, 18, v_B_5296_);
lean_ctor_set(v_reuseFailAlloc_5321_, 19, v_h_5297_);
lean_ctor_set(v_reuseFailAlloc_5321_, 20, v_K_5298_);
lean_ctor_set(v_reuseFailAlloc_5321_, 21, v_k_5299_);
lean_ctor_set(v_reuseFailAlloc_5321_, 22, v_H_5300_);
lean_ctor_set(v_reuseFailAlloc_5321_, 23, v_m_5301_);
lean_ctor_set(v_reuseFailAlloc_5321_, 24, v_s_5302_);
lean_ctor_set(v_reuseFailAlloc_5321_, 25, v_S_5303_);
lean_ctor_set(v_reuseFailAlloc_5321_, 26, v_A_5304_);
lean_ctor_set(v_reuseFailAlloc_5321_, 27, v_n_5305_);
lean_ctor_set(v_reuseFailAlloc_5321_, 28, v_N_5306_);
lean_ctor_set(v_reuseFailAlloc_5321_, 29, v_V_5307_);
lean_ctor_set(v_reuseFailAlloc_5321_, 30, v_z_5308_);
lean_ctor_set(v_reuseFailAlloc_5321_, 31, v_zabbrev_5309_);
lean_ctor_set(v_reuseFailAlloc_5321_, 32, v_v_5310_);
lean_ctor_set(v_reuseFailAlloc_5321_, 33, v_O_5311_);
lean_ctor_set(v_reuseFailAlloc_5321_, 34, v_X_5312_);
lean_ctor_set(v_reuseFailAlloc_5321_, 35, v_x_5313_);
lean_ctor_set(v_reuseFailAlloc_5321_, 36, v_Z_5314_);
v___x_5320_ = v_reuseFailAlloc_5321_;
goto v_reusejp_5319_;
}
v_reusejp_5319_:
{
return v___x_5320_;
}
}
}
case 18:
{
lean_object* v_G_5324_; lean_object* v_y_5325_; lean_object* v_u_5326_; lean_object* v_Y_5327_; lean_object* v_D_5328_; lean_object* v_M_5329_; lean_object* v_L_5330_; lean_object* v_d_5331_; lean_object* v_Q_5332_; lean_object* v_q_5333_; lean_object* v_w_5334_; lean_object* v_W_5335_; lean_object* v_E_5336_; lean_object* v_e_5337_; lean_object* v_c_5338_; lean_object* v_F_5339_; lean_object* v_a_5340_; lean_object* v_b_5341_; lean_object* v_h_5342_; lean_object* v_K_5343_; lean_object* v_k_5344_; lean_object* v_H_5345_; lean_object* v_m_5346_; lean_object* v_s_5347_; lean_object* v_S_5348_; lean_object* v_A_5349_; lean_object* v_n_5350_; lean_object* v_N_5351_; lean_object* v_V_5352_; lean_object* v_z_5353_; lean_object* v_zabbrev_5354_; lean_object* v_v_5355_; lean_object* v_O_5356_; lean_object* v_X_5357_; lean_object* v_x_5358_; lean_object* v_Z_5359_; lean_object* v___x_5361_; uint8_t v_isShared_5362_; uint8_t v_isSharedCheck_5367_; 
lean_dec_ref_known(v_modifier_4414_, 0);
v_G_5324_ = lean_ctor_get(v_date_4413_, 0);
v_y_5325_ = lean_ctor_get(v_date_4413_, 1);
v_u_5326_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5327_ = lean_ctor_get(v_date_4413_, 3);
v_D_5328_ = lean_ctor_get(v_date_4413_, 4);
v_M_5329_ = lean_ctor_get(v_date_4413_, 5);
v_L_5330_ = lean_ctor_get(v_date_4413_, 6);
v_d_5331_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5332_ = lean_ctor_get(v_date_4413_, 8);
v_q_5333_ = lean_ctor_get(v_date_4413_, 9);
v_w_5334_ = lean_ctor_get(v_date_4413_, 10);
v_W_5335_ = lean_ctor_get(v_date_4413_, 11);
v_E_5336_ = lean_ctor_get(v_date_4413_, 12);
v_e_5337_ = lean_ctor_get(v_date_4413_, 13);
v_c_5338_ = lean_ctor_get(v_date_4413_, 14);
v_F_5339_ = lean_ctor_get(v_date_4413_, 15);
v_a_5340_ = lean_ctor_get(v_date_4413_, 16);
v_b_5341_ = lean_ctor_get(v_date_4413_, 17);
v_h_5342_ = lean_ctor_get(v_date_4413_, 19);
v_K_5343_ = lean_ctor_get(v_date_4413_, 20);
v_k_5344_ = lean_ctor_get(v_date_4413_, 21);
v_H_5345_ = lean_ctor_get(v_date_4413_, 22);
v_m_5346_ = lean_ctor_get(v_date_4413_, 23);
v_s_5347_ = lean_ctor_get(v_date_4413_, 24);
v_S_5348_ = lean_ctor_get(v_date_4413_, 25);
v_A_5349_ = lean_ctor_get(v_date_4413_, 26);
v_n_5350_ = lean_ctor_get(v_date_4413_, 27);
v_N_5351_ = lean_ctor_get(v_date_4413_, 28);
v_V_5352_ = lean_ctor_get(v_date_4413_, 29);
v_z_5353_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_5354_ = lean_ctor_get(v_date_4413_, 31);
v_v_5355_ = lean_ctor_get(v_date_4413_, 32);
v_O_5356_ = lean_ctor_get(v_date_4413_, 33);
v_X_5357_ = lean_ctor_get(v_date_4413_, 34);
v_x_5358_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5359_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5367_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5367_ == 0)
{
lean_object* v_unused_5368_; 
v_unused_5368_ = lean_ctor_get(v_date_4413_, 18);
lean_dec(v_unused_5368_);
v___x_5361_ = v_date_4413_;
v_isShared_5362_ = v_isSharedCheck_5367_;
goto v_resetjp_5360_;
}
else
{
lean_inc(v_Z_5359_);
lean_inc(v_x_5358_);
lean_inc(v_X_5357_);
lean_inc(v_O_5356_);
lean_inc(v_v_5355_);
lean_inc(v_zabbrev_5354_);
lean_inc(v_z_5353_);
lean_inc(v_V_5352_);
lean_inc(v_N_5351_);
lean_inc(v_n_5350_);
lean_inc(v_A_5349_);
lean_inc(v_S_5348_);
lean_inc(v_s_5347_);
lean_inc(v_m_5346_);
lean_inc(v_H_5345_);
lean_inc(v_k_5344_);
lean_inc(v_K_5343_);
lean_inc(v_h_5342_);
lean_inc(v_b_5341_);
lean_inc(v_a_5340_);
lean_inc(v_F_5339_);
lean_inc(v_c_5338_);
lean_inc(v_e_5337_);
lean_inc(v_E_5336_);
lean_inc(v_W_5335_);
lean_inc(v_w_5334_);
lean_inc(v_q_5333_);
lean_inc(v_Q_5332_);
lean_inc(v_d_5331_);
lean_inc(v_L_5330_);
lean_inc(v_M_5329_);
lean_inc(v_D_5328_);
lean_inc(v_Y_5327_);
lean_inc(v_u_5326_);
lean_inc(v_y_5325_);
lean_inc(v_G_5324_);
lean_dec(v_date_4413_);
v___x_5361_ = lean_box(0);
v_isShared_5362_ = v_isSharedCheck_5367_;
goto v_resetjp_5360_;
}
v_resetjp_5360_:
{
lean_object* v___x_5363_; lean_object* v___x_5365_; 
v___x_5363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5363_, 0, v_data_4415_);
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 18, v___x_5363_);
v___x_5365_ = v___x_5361_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_G_5324_);
lean_ctor_set(v_reuseFailAlloc_5366_, 1, v_y_5325_);
lean_ctor_set(v_reuseFailAlloc_5366_, 2, v_u_5326_);
lean_ctor_set(v_reuseFailAlloc_5366_, 3, v_Y_5327_);
lean_ctor_set(v_reuseFailAlloc_5366_, 4, v_D_5328_);
lean_ctor_set(v_reuseFailAlloc_5366_, 5, v_M_5329_);
lean_ctor_set(v_reuseFailAlloc_5366_, 6, v_L_5330_);
lean_ctor_set(v_reuseFailAlloc_5366_, 7, v_d_5331_);
lean_ctor_set(v_reuseFailAlloc_5366_, 8, v_Q_5332_);
lean_ctor_set(v_reuseFailAlloc_5366_, 9, v_q_5333_);
lean_ctor_set(v_reuseFailAlloc_5366_, 10, v_w_5334_);
lean_ctor_set(v_reuseFailAlloc_5366_, 11, v_W_5335_);
lean_ctor_set(v_reuseFailAlloc_5366_, 12, v_E_5336_);
lean_ctor_set(v_reuseFailAlloc_5366_, 13, v_e_5337_);
lean_ctor_set(v_reuseFailAlloc_5366_, 14, v_c_5338_);
lean_ctor_set(v_reuseFailAlloc_5366_, 15, v_F_5339_);
lean_ctor_set(v_reuseFailAlloc_5366_, 16, v_a_5340_);
lean_ctor_set(v_reuseFailAlloc_5366_, 17, v_b_5341_);
lean_ctor_set(v_reuseFailAlloc_5366_, 18, v___x_5363_);
lean_ctor_set(v_reuseFailAlloc_5366_, 19, v_h_5342_);
lean_ctor_set(v_reuseFailAlloc_5366_, 20, v_K_5343_);
lean_ctor_set(v_reuseFailAlloc_5366_, 21, v_k_5344_);
lean_ctor_set(v_reuseFailAlloc_5366_, 22, v_H_5345_);
lean_ctor_set(v_reuseFailAlloc_5366_, 23, v_m_5346_);
lean_ctor_set(v_reuseFailAlloc_5366_, 24, v_s_5347_);
lean_ctor_set(v_reuseFailAlloc_5366_, 25, v_S_5348_);
lean_ctor_set(v_reuseFailAlloc_5366_, 26, v_A_5349_);
lean_ctor_set(v_reuseFailAlloc_5366_, 27, v_n_5350_);
lean_ctor_set(v_reuseFailAlloc_5366_, 28, v_N_5351_);
lean_ctor_set(v_reuseFailAlloc_5366_, 29, v_V_5352_);
lean_ctor_set(v_reuseFailAlloc_5366_, 30, v_z_5353_);
lean_ctor_set(v_reuseFailAlloc_5366_, 31, v_zabbrev_5354_);
lean_ctor_set(v_reuseFailAlloc_5366_, 32, v_v_5355_);
lean_ctor_set(v_reuseFailAlloc_5366_, 33, v_O_5356_);
lean_ctor_set(v_reuseFailAlloc_5366_, 34, v_X_5357_);
lean_ctor_set(v_reuseFailAlloc_5366_, 35, v_x_5358_);
lean_ctor_set(v_reuseFailAlloc_5366_, 36, v_Z_5359_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
}
case 19:
{
lean_object* v___x_5370_; uint8_t v_isShared_5371_; uint8_t v_isSharedCheck_5419_; 
v_isSharedCheck_5419_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_5419_ == 0)
{
lean_object* v_unused_5420_; 
v_unused_5420_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_5420_);
v___x_5370_ = v_modifier_4414_;
v_isShared_5371_ = v_isSharedCheck_5419_;
goto v_resetjp_5369_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_5370_ = lean_box(0);
v_isShared_5371_ = v_isSharedCheck_5419_;
goto v_resetjp_5369_;
}
v_resetjp_5369_:
{
lean_object* v_G_5372_; lean_object* v_y_5373_; lean_object* v_u_5374_; lean_object* v_Y_5375_; lean_object* v_D_5376_; lean_object* v_M_5377_; lean_object* v_L_5378_; lean_object* v_d_5379_; lean_object* v_Q_5380_; lean_object* v_q_5381_; lean_object* v_w_5382_; lean_object* v_W_5383_; lean_object* v_E_5384_; lean_object* v_e_5385_; lean_object* v_c_5386_; lean_object* v_F_5387_; lean_object* v_a_5388_; lean_object* v_b_5389_; lean_object* v_B_5390_; lean_object* v_K_5391_; lean_object* v_k_5392_; lean_object* v_H_5393_; lean_object* v_m_5394_; lean_object* v_s_5395_; lean_object* v_S_5396_; lean_object* v_A_5397_; lean_object* v_n_5398_; lean_object* v_N_5399_; lean_object* v_V_5400_; lean_object* v_z_5401_; lean_object* v_zabbrev_5402_; lean_object* v_v_5403_; lean_object* v_O_5404_; lean_object* v_X_5405_; lean_object* v_x_5406_; lean_object* v_Z_5407_; lean_object* v___x_5409_; uint8_t v_isShared_5410_; uint8_t v_isSharedCheck_5417_; 
v_G_5372_ = lean_ctor_get(v_date_4413_, 0);
v_y_5373_ = lean_ctor_get(v_date_4413_, 1);
v_u_5374_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5375_ = lean_ctor_get(v_date_4413_, 3);
v_D_5376_ = lean_ctor_get(v_date_4413_, 4);
v_M_5377_ = lean_ctor_get(v_date_4413_, 5);
v_L_5378_ = lean_ctor_get(v_date_4413_, 6);
v_d_5379_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5380_ = lean_ctor_get(v_date_4413_, 8);
v_q_5381_ = lean_ctor_get(v_date_4413_, 9);
v_w_5382_ = lean_ctor_get(v_date_4413_, 10);
v_W_5383_ = lean_ctor_get(v_date_4413_, 11);
v_E_5384_ = lean_ctor_get(v_date_4413_, 12);
v_e_5385_ = lean_ctor_get(v_date_4413_, 13);
v_c_5386_ = lean_ctor_get(v_date_4413_, 14);
v_F_5387_ = lean_ctor_get(v_date_4413_, 15);
v_a_5388_ = lean_ctor_get(v_date_4413_, 16);
v_b_5389_ = lean_ctor_get(v_date_4413_, 17);
v_B_5390_ = lean_ctor_get(v_date_4413_, 18);
v_K_5391_ = lean_ctor_get(v_date_4413_, 20);
v_k_5392_ = lean_ctor_get(v_date_4413_, 21);
v_H_5393_ = lean_ctor_get(v_date_4413_, 22);
v_m_5394_ = lean_ctor_get(v_date_4413_, 23);
v_s_5395_ = lean_ctor_get(v_date_4413_, 24);
v_S_5396_ = lean_ctor_get(v_date_4413_, 25);
v_A_5397_ = lean_ctor_get(v_date_4413_, 26);
v_n_5398_ = lean_ctor_get(v_date_4413_, 27);
v_N_5399_ = lean_ctor_get(v_date_4413_, 28);
v_V_5400_ = lean_ctor_get(v_date_4413_, 29);
v_z_5401_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_5402_ = lean_ctor_get(v_date_4413_, 31);
v_v_5403_ = lean_ctor_get(v_date_4413_, 32);
v_O_5404_ = lean_ctor_get(v_date_4413_, 33);
v_X_5405_ = lean_ctor_get(v_date_4413_, 34);
v_x_5406_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5407_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5417_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5417_ == 0)
{
lean_object* v_unused_5418_; 
v_unused_5418_ = lean_ctor_get(v_date_4413_, 19);
lean_dec(v_unused_5418_);
v___x_5409_ = v_date_4413_;
v_isShared_5410_ = v_isSharedCheck_5417_;
goto v_resetjp_5408_;
}
else
{
lean_inc(v_Z_5407_);
lean_inc(v_x_5406_);
lean_inc(v_X_5405_);
lean_inc(v_O_5404_);
lean_inc(v_v_5403_);
lean_inc(v_zabbrev_5402_);
lean_inc(v_z_5401_);
lean_inc(v_V_5400_);
lean_inc(v_N_5399_);
lean_inc(v_n_5398_);
lean_inc(v_A_5397_);
lean_inc(v_S_5396_);
lean_inc(v_s_5395_);
lean_inc(v_m_5394_);
lean_inc(v_H_5393_);
lean_inc(v_k_5392_);
lean_inc(v_K_5391_);
lean_inc(v_B_5390_);
lean_inc(v_b_5389_);
lean_inc(v_a_5388_);
lean_inc(v_F_5387_);
lean_inc(v_c_5386_);
lean_inc(v_e_5385_);
lean_inc(v_E_5384_);
lean_inc(v_W_5383_);
lean_inc(v_w_5382_);
lean_inc(v_q_5381_);
lean_inc(v_Q_5380_);
lean_inc(v_d_5379_);
lean_inc(v_L_5378_);
lean_inc(v_M_5377_);
lean_inc(v_D_5376_);
lean_inc(v_Y_5375_);
lean_inc(v_u_5374_);
lean_inc(v_y_5373_);
lean_inc(v_G_5372_);
lean_dec(v_date_4413_);
v___x_5409_ = lean_box(0);
v_isShared_5410_ = v_isSharedCheck_5417_;
goto v_resetjp_5408_;
}
v_resetjp_5408_:
{
lean_object* v___x_5412_; 
if (v_isShared_5371_ == 0)
{
lean_ctor_set_tag(v___x_5370_, 1);
lean_ctor_set(v___x_5370_, 0, v_data_4415_);
v___x_5412_ = v___x_5370_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5416_; 
v_reuseFailAlloc_5416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5416_, 0, v_data_4415_);
v___x_5412_ = v_reuseFailAlloc_5416_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
lean_object* v___x_5414_; 
if (v_isShared_5410_ == 0)
{
lean_ctor_set(v___x_5409_, 19, v___x_5412_);
v___x_5414_ = v___x_5409_;
goto v_reusejp_5413_;
}
else
{
lean_object* v_reuseFailAlloc_5415_; 
v_reuseFailAlloc_5415_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5415_, 0, v_G_5372_);
lean_ctor_set(v_reuseFailAlloc_5415_, 1, v_y_5373_);
lean_ctor_set(v_reuseFailAlloc_5415_, 2, v_u_5374_);
lean_ctor_set(v_reuseFailAlloc_5415_, 3, v_Y_5375_);
lean_ctor_set(v_reuseFailAlloc_5415_, 4, v_D_5376_);
lean_ctor_set(v_reuseFailAlloc_5415_, 5, v_M_5377_);
lean_ctor_set(v_reuseFailAlloc_5415_, 6, v_L_5378_);
lean_ctor_set(v_reuseFailAlloc_5415_, 7, v_d_5379_);
lean_ctor_set(v_reuseFailAlloc_5415_, 8, v_Q_5380_);
lean_ctor_set(v_reuseFailAlloc_5415_, 9, v_q_5381_);
lean_ctor_set(v_reuseFailAlloc_5415_, 10, v_w_5382_);
lean_ctor_set(v_reuseFailAlloc_5415_, 11, v_W_5383_);
lean_ctor_set(v_reuseFailAlloc_5415_, 12, v_E_5384_);
lean_ctor_set(v_reuseFailAlloc_5415_, 13, v_e_5385_);
lean_ctor_set(v_reuseFailAlloc_5415_, 14, v_c_5386_);
lean_ctor_set(v_reuseFailAlloc_5415_, 15, v_F_5387_);
lean_ctor_set(v_reuseFailAlloc_5415_, 16, v_a_5388_);
lean_ctor_set(v_reuseFailAlloc_5415_, 17, v_b_5389_);
lean_ctor_set(v_reuseFailAlloc_5415_, 18, v_B_5390_);
lean_ctor_set(v_reuseFailAlloc_5415_, 19, v___x_5412_);
lean_ctor_set(v_reuseFailAlloc_5415_, 20, v_K_5391_);
lean_ctor_set(v_reuseFailAlloc_5415_, 21, v_k_5392_);
lean_ctor_set(v_reuseFailAlloc_5415_, 22, v_H_5393_);
lean_ctor_set(v_reuseFailAlloc_5415_, 23, v_m_5394_);
lean_ctor_set(v_reuseFailAlloc_5415_, 24, v_s_5395_);
lean_ctor_set(v_reuseFailAlloc_5415_, 25, v_S_5396_);
lean_ctor_set(v_reuseFailAlloc_5415_, 26, v_A_5397_);
lean_ctor_set(v_reuseFailAlloc_5415_, 27, v_n_5398_);
lean_ctor_set(v_reuseFailAlloc_5415_, 28, v_N_5399_);
lean_ctor_set(v_reuseFailAlloc_5415_, 29, v_V_5400_);
lean_ctor_set(v_reuseFailAlloc_5415_, 30, v_z_5401_);
lean_ctor_set(v_reuseFailAlloc_5415_, 31, v_zabbrev_5402_);
lean_ctor_set(v_reuseFailAlloc_5415_, 32, v_v_5403_);
lean_ctor_set(v_reuseFailAlloc_5415_, 33, v_O_5404_);
lean_ctor_set(v_reuseFailAlloc_5415_, 34, v_X_5405_);
lean_ctor_set(v_reuseFailAlloc_5415_, 35, v_x_5406_);
lean_ctor_set(v_reuseFailAlloc_5415_, 36, v_Z_5407_);
v___x_5414_ = v_reuseFailAlloc_5415_;
goto v_reusejp_5413_;
}
v_reusejp_5413_:
{
return v___x_5414_;
}
}
}
}
}
case 20:
{
lean_object* v___x_5422_; uint8_t v_isShared_5423_; uint8_t v_isSharedCheck_5471_; 
v_isSharedCheck_5471_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_5471_ == 0)
{
lean_object* v_unused_5472_; 
v_unused_5472_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_5472_);
v___x_5422_ = v_modifier_4414_;
v_isShared_5423_ = v_isSharedCheck_5471_;
goto v_resetjp_5421_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_5422_ = lean_box(0);
v_isShared_5423_ = v_isSharedCheck_5471_;
goto v_resetjp_5421_;
}
v_resetjp_5421_:
{
lean_object* v_G_5424_; lean_object* v_y_5425_; lean_object* v_u_5426_; lean_object* v_Y_5427_; lean_object* v_D_5428_; lean_object* v_M_5429_; lean_object* v_L_5430_; lean_object* v_d_5431_; lean_object* v_Q_5432_; lean_object* v_q_5433_; lean_object* v_w_5434_; lean_object* v_W_5435_; lean_object* v_E_5436_; lean_object* v_e_5437_; lean_object* v_c_5438_; lean_object* v_F_5439_; lean_object* v_a_5440_; lean_object* v_b_5441_; lean_object* v_B_5442_; lean_object* v_h_5443_; lean_object* v_k_5444_; lean_object* v_H_5445_; lean_object* v_m_5446_; lean_object* v_s_5447_; lean_object* v_S_5448_; lean_object* v_A_5449_; lean_object* v_n_5450_; lean_object* v_N_5451_; lean_object* v_V_5452_; lean_object* v_z_5453_; lean_object* v_zabbrev_5454_; lean_object* v_v_5455_; lean_object* v_O_5456_; lean_object* v_X_5457_; lean_object* v_x_5458_; lean_object* v_Z_5459_; lean_object* v___x_5461_; uint8_t v_isShared_5462_; uint8_t v_isSharedCheck_5469_; 
v_G_5424_ = lean_ctor_get(v_date_4413_, 0);
v_y_5425_ = lean_ctor_get(v_date_4413_, 1);
v_u_5426_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5427_ = lean_ctor_get(v_date_4413_, 3);
v_D_5428_ = lean_ctor_get(v_date_4413_, 4);
v_M_5429_ = lean_ctor_get(v_date_4413_, 5);
v_L_5430_ = lean_ctor_get(v_date_4413_, 6);
v_d_5431_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5432_ = lean_ctor_get(v_date_4413_, 8);
v_q_5433_ = lean_ctor_get(v_date_4413_, 9);
v_w_5434_ = lean_ctor_get(v_date_4413_, 10);
v_W_5435_ = lean_ctor_get(v_date_4413_, 11);
v_E_5436_ = lean_ctor_get(v_date_4413_, 12);
v_e_5437_ = lean_ctor_get(v_date_4413_, 13);
v_c_5438_ = lean_ctor_get(v_date_4413_, 14);
v_F_5439_ = lean_ctor_get(v_date_4413_, 15);
v_a_5440_ = lean_ctor_get(v_date_4413_, 16);
v_b_5441_ = lean_ctor_get(v_date_4413_, 17);
v_B_5442_ = lean_ctor_get(v_date_4413_, 18);
v_h_5443_ = lean_ctor_get(v_date_4413_, 19);
v_k_5444_ = lean_ctor_get(v_date_4413_, 21);
v_H_5445_ = lean_ctor_get(v_date_4413_, 22);
v_m_5446_ = lean_ctor_get(v_date_4413_, 23);
v_s_5447_ = lean_ctor_get(v_date_4413_, 24);
v_S_5448_ = lean_ctor_get(v_date_4413_, 25);
v_A_5449_ = lean_ctor_get(v_date_4413_, 26);
v_n_5450_ = lean_ctor_get(v_date_4413_, 27);
v_N_5451_ = lean_ctor_get(v_date_4413_, 28);
v_V_5452_ = lean_ctor_get(v_date_4413_, 29);
v_z_5453_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_5454_ = lean_ctor_get(v_date_4413_, 31);
v_v_5455_ = lean_ctor_get(v_date_4413_, 32);
v_O_5456_ = lean_ctor_get(v_date_4413_, 33);
v_X_5457_ = lean_ctor_get(v_date_4413_, 34);
v_x_5458_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5459_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5469_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5469_ == 0)
{
lean_object* v_unused_5470_; 
v_unused_5470_ = lean_ctor_get(v_date_4413_, 20);
lean_dec(v_unused_5470_);
v___x_5461_ = v_date_4413_;
v_isShared_5462_ = v_isSharedCheck_5469_;
goto v_resetjp_5460_;
}
else
{
lean_inc(v_Z_5459_);
lean_inc(v_x_5458_);
lean_inc(v_X_5457_);
lean_inc(v_O_5456_);
lean_inc(v_v_5455_);
lean_inc(v_zabbrev_5454_);
lean_inc(v_z_5453_);
lean_inc(v_V_5452_);
lean_inc(v_N_5451_);
lean_inc(v_n_5450_);
lean_inc(v_A_5449_);
lean_inc(v_S_5448_);
lean_inc(v_s_5447_);
lean_inc(v_m_5446_);
lean_inc(v_H_5445_);
lean_inc(v_k_5444_);
lean_inc(v_h_5443_);
lean_inc(v_B_5442_);
lean_inc(v_b_5441_);
lean_inc(v_a_5440_);
lean_inc(v_F_5439_);
lean_inc(v_c_5438_);
lean_inc(v_e_5437_);
lean_inc(v_E_5436_);
lean_inc(v_W_5435_);
lean_inc(v_w_5434_);
lean_inc(v_q_5433_);
lean_inc(v_Q_5432_);
lean_inc(v_d_5431_);
lean_inc(v_L_5430_);
lean_inc(v_M_5429_);
lean_inc(v_D_5428_);
lean_inc(v_Y_5427_);
lean_inc(v_u_5426_);
lean_inc(v_y_5425_);
lean_inc(v_G_5424_);
lean_dec(v_date_4413_);
v___x_5461_ = lean_box(0);
v_isShared_5462_ = v_isSharedCheck_5469_;
goto v_resetjp_5460_;
}
v_resetjp_5460_:
{
lean_object* v___x_5464_; 
if (v_isShared_5423_ == 0)
{
lean_ctor_set_tag(v___x_5422_, 1);
lean_ctor_set(v___x_5422_, 0, v_data_4415_);
v___x_5464_ = v___x_5422_;
goto v_reusejp_5463_;
}
else
{
lean_object* v_reuseFailAlloc_5468_; 
v_reuseFailAlloc_5468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5468_, 0, v_data_4415_);
v___x_5464_ = v_reuseFailAlloc_5468_;
goto v_reusejp_5463_;
}
v_reusejp_5463_:
{
lean_object* v___x_5466_; 
if (v_isShared_5462_ == 0)
{
lean_ctor_set(v___x_5461_, 20, v___x_5464_);
v___x_5466_ = v___x_5461_;
goto v_reusejp_5465_;
}
else
{
lean_object* v_reuseFailAlloc_5467_; 
v_reuseFailAlloc_5467_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5467_, 0, v_G_5424_);
lean_ctor_set(v_reuseFailAlloc_5467_, 1, v_y_5425_);
lean_ctor_set(v_reuseFailAlloc_5467_, 2, v_u_5426_);
lean_ctor_set(v_reuseFailAlloc_5467_, 3, v_Y_5427_);
lean_ctor_set(v_reuseFailAlloc_5467_, 4, v_D_5428_);
lean_ctor_set(v_reuseFailAlloc_5467_, 5, v_M_5429_);
lean_ctor_set(v_reuseFailAlloc_5467_, 6, v_L_5430_);
lean_ctor_set(v_reuseFailAlloc_5467_, 7, v_d_5431_);
lean_ctor_set(v_reuseFailAlloc_5467_, 8, v_Q_5432_);
lean_ctor_set(v_reuseFailAlloc_5467_, 9, v_q_5433_);
lean_ctor_set(v_reuseFailAlloc_5467_, 10, v_w_5434_);
lean_ctor_set(v_reuseFailAlloc_5467_, 11, v_W_5435_);
lean_ctor_set(v_reuseFailAlloc_5467_, 12, v_E_5436_);
lean_ctor_set(v_reuseFailAlloc_5467_, 13, v_e_5437_);
lean_ctor_set(v_reuseFailAlloc_5467_, 14, v_c_5438_);
lean_ctor_set(v_reuseFailAlloc_5467_, 15, v_F_5439_);
lean_ctor_set(v_reuseFailAlloc_5467_, 16, v_a_5440_);
lean_ctor_set(v_reuseFailAlloc_5467_, 17, v_b_5441_);
lean_ctor_set(v_reuseFailAlloc_5467_, 18, v_B_5442_);
lean_ctor_set(v_reuseFailAlloc_5467_, 19, v_h_5443_);
lean_ctor_set(v_reuseFailAlloc_5467_, 20, v___x_5464_);
lean_ctor_set(v_reuseFailAlloc_5467_, 21, v_k_5444_);
lean_ctor_set(v_reuseFailAlloc_5467_, 22, v_H_5445_);
lean_ctor_set(v_reuseFailAlloc_5467_, 23, v_m_5446_);
lean_ctor_set(v_reuseFailAlloc_5467_, 24, v_s_5447_);
lean_ctor_set(v_reuseFailAlloc_5467_, 25, v_S_5448_);
lean_ctor_set(v_reuseFailAlloc_5467_, 26, v_A_5449_);
lean_ctor_set(v_reuseFailAlloc_5467_, 27, v_n_5450_);
lean_ctor_set(v_reuseFailAlloc_5467_, 28, v_N_5451_);
lean_ctor_set(v_reuseFailAlloc_5467_, 29, v_V_5452_);
lean_ctor_set(v_reuseFailAlloc_5467_, 30, v_z_5453_);
lean_ctor_set(v_reuseFailAlloc_5467_, 31, v_zabbrev_5454_);
lean_ctor_set(v_reuseFailAlloc_5467_, 32, v_v_5455_);
lean_ctor_set(v_reuseFailAlloc_5467_, 33, v_O_5456_);
lean_ctor_set(v_reuseFailAlloc_5467_, 34, v_X_5457_);
lean_ctor_set(v_reuseFailAlloc_5467_, 35, v_x_5458_);
lean_ctor_set(v_reuseFailAlloc_5467_, 36, v_Z_5459_);
v___x_5466_ = v_reuseFailAlloc_5467_;
goto v_reusejp_5465_;
}
v_reusejp_5465_:
{
return v___x_5466_;
}
}
}
}
}
case 21:
{
lean_object* v___x_5474_; uint8_t v_isShared_5475_; uint8_t v_isSharedCheck_5523_; 
v_isSharedCheck_5523_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_5523_ == 0)
{
lean_object* v_unused_5524_; 
v_unused_5524_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_5524_);
v___x_5474_ = v_modifier_4414_;
v_isShared_5475_ = v_isSharedCheck_5523_;
goto v_resetjp_5473_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_5474_ = lean_box(0);
v_isShared_5475_ = v_isSharedCheck_5523_;
goto v_resetjp_5473_;
}
v_resetjp_5473_:
{
lean_object* v_G_5476_; lean_object* v_y_5477_; lean_object* v_u_5478_; lean_object* v_Y_5479_; lean_object* v_D_5480_; lean_object* v_M_5481_; lean_object* v_L_5482_; lean_object* v_d_5483_; lean_object* v_Q_5484_; lean_object* v_q_5485_; lean_object* v_w_5486_; lean_object* v_W_5487_; lean_object* v_E_5488_; lean_object* v_e_5489_; lean_object* v_c_5490_; lean_object* v_F_5491_; lean_object* v_a_5492_; lean_object* v_b_5493_; lean_object* v_B_5494_; lean_object* v_h_5495_; lean_object* v_K_5496_; lean_object* v_H_5497_; lean_object* v_m_5498_; lean_object* v_s_5499_; lean_object* v_S_5500_; lean_object* v_A_5501_; lean_object* v_n_5502_; lean_object* v_N_5503_; lean_object* v_V_5504_; lean_object* v_z_5505_; lean_object* v_zabbrev_5506_; lean_object* v_v_5507_; lean_object* v_O_5508_; lean_object* v_X_5509_; lean_object* v_x_5510_; lean_object* v_Z_5511_; lean_object* v___x_5513_; uint8_t v_isShared_5514_; uint8_t v_isSharedCheck_5521_; 
v_G_5476_ = lean_ctor_get(v_date_4413_, 0);
v_y_5477_ = lean_ctor_get(v_date_4413_, 1);
v_u_5478_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5479_ = lean_ctor_get(v_date_4413_, 3);
v_D_5480_ = lean_ctor_get(v_date_4413_, 4);
v_M_5481_ = lean_ctor_get(v_date_4413_, 5);
v_L_5482_ = lean_ctor_get(v_date_4413_, 6);
v_d_5483_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5484_ = lean_ctor_get(v_date_4413_, 8);
v_q_5485_ = lean_ctor_get(v_date_4413_, 9);
v_w_5486_ = lean_ctor_get(v_date_4413_, 10);
v_W_5487_ = lean_ctor_get(v_date_4413_, 11);
v_E_5488_ = lean_ctor_get(v_date_4413_, 12);
v_e_5489_ = lean_ctor_get(v_date_4413_, 13);
v_c_5490_ = lean_ctor_get(v_date_4413_, 14);
v_F_5491_ = lean_ctor_get(v_date_4413_, 15);
v_a_5492_ = lean_ctor_get(v_date_4413_, 16);
v_b_5493_ = lean_ctor_get(v_date_4413_, 17);
v_B_5494_ = lean_ctor_get(v_date_4413_, 18);
v_h_5495_ = lean_ctor_get(v_date_4413_, 19);
v_K_5496_ = lean_ctor_get(v_date_4413_, 20);
v_H_5497_ = lean_ctor_get(v_date_4413_, 22);
v_m_5498_ = lean_ctor_get(v_date_4413_, 23);
v_s_5499_ = lean_ctor_get(v_date_4413_, 24);
v_S_5500_ = lean_ctor_get(v_date_4413_, 25);
v_A_5501_ = lean_ctor_get(v_date_4413_, 26);
v_n_5502_ = lean_ctor_get(v_date_4413_, 27);
v_N_5503_ = lean_ctor_get(v_date_4413_, 28);
v_V_5504_ = lean_ctor_get(v_date_4413_, 29);
v_z_5505_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_5506_ = lean_ctor_get(v_date_4413_, 31);
v_v_5507_ = lean_ctor_get(v_date_4413_, 32);
v_O_5508_ = lean_ctor_get(v_date_4413_, 33);
v_X_5509_ = lean_ctor_get(v_date_4413_, 34);
v_x_5510_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5511_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5521_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5521_ == 0)
{
lean_object* v_unused_5522_; 
v_unused_5522_ = lean_ctor_get(v_date_4413_, 21);
lean_dec(v_unused_5522_);
v___x_5513_ = v_date_4413_;
v_isShared_5514_ = v_isSharedCheck_5521_;
goto v_resetjp_5512_;
}
else
{
lean_inc(v_Z_5511_);
lean_inc(v_x_5510_);
lean_inc(v_X_5509_);
lean_inc(v_O_5508_);
lean_inc(v_v_5507_);
lean_inc(v_zabbrev_5506_);
lean_inc(v_z_5505_);
lean_inc(v_V_5504_);
lean_inc(v_N_5503_);
lean_inc(v_n_5502_);
lean_inc(v_A_5501_);
lean_inc(v_S_5500_);
lean_inc(v_s_5499_);
lean_inc(v_m_5498_);
lean_inc(v_H_5497_);
lean_inc(v_K_5496_);
lean_inc(v_h_5495_);
lean_inc(v_B_5494_);
lean_inc(v_b_5493_);
lean_inc(v_a_5492_);
lean_inc(v_F_5491_);
lean_inc(v_c_5490_);
lean_inc(v_e_5489_);
lean_inc(v_E_5488_);
lean_inc(v_W_5487_);
lean_inc(v_w_5486_);
lean_inc(v_q_5485_);
lean_inc(v_Q_5484_);
lean_inc(v_d_5483_);
lean_inc(v_L_5482_);
lean_inc(v_M_5481_);
lean_inc(v_D_5480_);
lean_inc(v_Y_5479_);
lean_inc(v_u_5478_);
lean_inc(v_y_5477_);
lean_inc(v_G_5476_);
lean_dec(v_date_4413_);
v___x_5513_ = lean_box(0);
v_isShared_5514_ = v_isSharedCheck_5521_;
goto v_resetjp_5512_;
}
v_resetjp_5512_:
{
lean_object* v___x_5516_; 
if (v_isShared_5475_ == 0)
{
lean_ctor_set_tag(v___x_5474_, 1);
lean_ctor_set(v___x_5474_, 0, v_data_4415_);
v___x_5516_ = v___x_5474_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_data_4415_);
v___x_5516_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
lean_object* v___x_5518_; 
if (v_isShared_5514_ == 0)
{
lean_ctor_set(v___x_5513_, 21, v___x_5516_);
v___x_5518_ = v___x_5513_;
goto v_reusejp_5517_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_G_5476_);
lean_ctor_set(v_reuseFailAlloc_5519_, 1, v_y_5477_);
lean_ctor_set(v_reuseFailAlloc_5519_, 2, v_u_5478_);
lean_ctor_set(v_reuseFailAlloc_5519_, 3, v_Y_5479_);
lean_ctor_set(v_reuseFailAlloc_5519_, 4, v_D_5480_);
lean_ctor_set(v_reuseFailAlloc_5519_, 5, v_M_5481_);
lean_ctor_set(v_reuseFailAlloc_5519_, 6, v_L_5482_);
lean_ctor_set(v_reuseFailAlloc_5519_, 7, v_d_5483_);
lean_ctor_set(v_reuseFailAlloc_5519_, 8, v_Q_5484_);
lean_ctor_set(v_reuseFailAlloc_5519_, 9, v_q_5485_);
lean_ctor_set(v_reuseFailAlloc_5519_, 10, v_w_5486_);
lean_ctor_set(v_reuseFailAlloc_5519_, 11, v_W_5487_);
lean_ctor_set(v_reuseFailAlloc_5519_, 12, v_E_5488_);
lean_ctor_set(v_reuseFailAlloc_5519_, 13, v_e_5489_);
lean_ctor_set(v_reuseFailAlloc_5519_, 14, v_c_5490_);
lean_ctor_set(v_reuseFailAlloc_5519_, 15, v_F_5491_);
lean_ctor_set(v_reuseFailAlloc_5519_, 16, v_a_5492_);
lean_ctor_set(v_reuseFailAlloc_5519_, 17, v_b_5493_);
lean_ctor_set(v_reuseFailAlloc_5519_, 18, v_B_5494_);
lean_ctor_set(v_reuseFailAlloc_5519_, 19, v_h_5495_);
lean_ctor_set(v_reuseFailAlloc_5519_, 20, v_K_5496_);
lean_ctor_set(v_reuseFailAlloc_5519_, 21, v___x_5516_);
lean_ctor_set(v_reuseFailAlloc_5519_, 22, v_H_5497_);
lean_ctor_set(v_reuseFailAlloc_5519_, 23, v_m_5498_);
lean_ctor_set(v_reuseFailAlloc_5519_, 24, v_s_5499_);
lean_ctor_set(v_reuseFailAlloc_5519_, 25, v_S_5500_);
lean_ctor_set(v_reuseFailAlloc_5519_, 26, v_A_5501_);
lean_ctor_set(v_reuseFailAlloc_5519_, 27, v_n_5502_);
lean_ctor_set(v_reuseFailAlloc_5519_, 28, v_N_5503_);
lean_ctor_set(v_reuseFailAlloc_5519_, 29, v_V_5504_);
lean_ctor_set(v_reuseFailAlloc_5519_, 30, v_z_5505_);
lean_ctor_set(v_reuseFailAlloc_5519_, 31, v_zabbrev_5506_);
lean_ctor_set(v_reuseFailAlloc_5519_, 32, v_v_5507_);
lean_ctor_set(v_reuseFailAlloc_5519_, 33, v_O_5508_);
lean_ctor_set(v_reuseFailAlloc_5519_, 34, v_X_5509_);
lean_ctor_set(v_reuseFailAlloc_5519_, 35, v_x_5510_);
lean_ctor_set(v_reuseFailAlloc_5519_, 36, v_Z_5511_);
v___x_5518_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5517_;
}
v_reusejp_5517_:
{
return v___x_5518_;
}
}
}
}
}
case 22:
{
lean_object* v___x_5526_; uint8_t v_isShared_5527_; uint8_t v_isSharedCheck_5575_; 
v_isSharedCheck_5575_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_5575_ == 0)
{
lean_object* v_unused_5576_; 
v_unused_5576_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_5576_);
v___x_5526_ = v_modifier_4414_;
v_isShared_5527_ = v_isSharedCheck_5575_;
goto v_resetjp_5525_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_5526_ = lean_box(0);
v_isShared_5527_ = v_isSharedCheck_5575_;
goto v_resetjp_5525_;
}
v_resetjp_5525_:
{
lean_object* v_G_5528_; lean_object* v_y_5529_; lean_object* v_u_5530_; lean_object* v_Y_5531_; lean_object* v_D_5532_; lean_object* v_M_5533_; lean_object* v_L_5534_; lean_object* v_d_5535_; lean_object* v_Q_5536_; lean_object* v_q_5537_; lean_object* v_w_5538_; lean_object* v_W_5539_; lean_object* v_E_5540_; lean_object* v_e_5541_; lean_object* v_c_5542_; lean_object* v_F_5543_; lean_object* v_a_5544_; lean_object* v_b_5545_; lean_object* v_B_5546_; lean_object* v_h_5547_; lean_object* v_K_5548_; lean_object* v_k_5549_; lean_object* v_m_5550_; lean_object* v_s_5551_; lean_object* v_S_5552_; lean_object* v_A_5553_; lean_object* v_n_5554_; lean_object* v_N_5555_; lean_object* v_V_5556_; lean_object* v_z_5557_; lean_object* v_zabbrev_5558_; lean_object* v_v_5559_; lean_object* v_O_5560_; lean_object* v_X_5561_; lean_object* v_x_5562_; lean_object* v_Z_5563_; lean_object* v___x_5565_; uint8_t v_isShared_5566_; uint8_t v_isSharedCheck_5573_; 
v_G_5528_ = lean_ctor_get(v_date_4413_, 0);
v_y_5529_ = lean_ctor_get(v_date_4413_, 1);
v_u_5530_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5531_ = lean_ctor_get(v_date_4413_, 3);
v_D_5532_ = lean_ctor_get(v_date_4413_, 4);
v_M_5533_ = lean_ctor_get(v_date_4413_, 5);
v_L_5534_ = lean_ctor_get(v_date_4413_, 6);
v_d_5535_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5536_ = lean_ctor_get(v_date_4413_, 8);
v_q_5537_ = lean_ctor_get(v_date_4413_, 9);
v_w_5538_ = lean_ctor_get(v_date_4413_, 10);
v_W_5539_ = lean_ctor_get(v_date_4413_, 11);
v_E_5540_ = lean_ctor_get(v_date_4413_, 12);
v_e_5541_ = lean_ctor_get(v_date_4413_, 13);
v_c_5542_ = lean_ctor_get(v_date_4413_, 14);
v_F_5543_ = lean_ctor_get(v_date_4413_, 15);
v_a_5544_ = lean_ctor_get(v_date_4413_, 16);
v_b_5545_ = lean_ctor_get(v_date_4413_, 17);
v_B_5546_ = lean_ctor_get(v_date_4413_, 18);
v_h_5547_ = lean_ctor_get(v_date_4413_, 19);
v_K_5548_ = lean_ctor_get(v_date_4413_, 20);
v_k_5549_ = lean_ctor_get(v_date_4413_, 21);
v_m_5550_ = lean_ctor_get(v_date_4413_, 23);
v_s_5551_ = lean_ctor_get(v_date_4413_, 24);
v_S_5552_ = lean_ctor_get(v_date_4413_, 25);
v_A_5553_ = lean_ctor_get(v_date_4413_, 26);
v_n_5554_ = lean_ctor_get(v_date_4413_, 27);
v_N_5555_ = lean_ctor_get(v_date_4413_, 28);
v_V_5556_ = lean_ctor_get(v_date_4413_, 29);
v_z_5557_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_5558_ = lean_ctor_get(v_date_4413_, 31);
v_v_5559_ = lean_ctor_get(v_date_4413_, 32);
v_O_5560_ = lean_ctor_get(v_date_4413_, 33);
v_X_5561_ = lean_ctor_get(v_date_4413_, 34);
v_x_5562_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5563_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5573_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5573_ == 0)
{
lean_object* v_unused_5574_; 
v_unused_5574_ = lean_ctor_get(v_date_4413_, 22);
lean_dec(v_unused_5574_);
v___x_5565_ = v_date_4413_;
v_isShared_5566_ = v_isSharedCheck_5573_;
goto v_resetjp_5564_;
}
else
{
lean_inc(v_Z_5563_);
lean_inc(v_x_5562_);
lean_inc(v_X_5561_);
lean_inc(v_O_5560_);
lean_inc(v_v_5559_);
lean_inc(v_zabbrev_5558_);
lean_inc(v_z_5557_);
lean_inc(v_V_5556_);
lean_inc(v_N_5555_);
lean_inc(v_n_5554_);
lean_inc(v_A_5553_);
lean_inc(v_S_5552_);
lean_inc(v_s_5551_);
lean_inc(v_m_5550_);
lean_inc(v_k_5549_);
lean_inc(v_K_5548_);
lean_inc(v_h_5547_);
lean_inc(v_B_5546_);
lean_inc(v_b_5545_);
lean_inc(v_a_5544_);
lean_inc(v_F_5543_);
lean_inc(v_c_5542_);
lean_inc(v_e_5541_);
lean_inc(v_E_5540_);
lean_inc(v_W_5539_);
lean_inc(v_w_5538_);
lean_inc(v_q_5537_);
lean_inc(v_Q_5536_);
lean_inc(v_d_5535_);
lean_inc(v_L_5534_);
lean_inc(v_M_5533_);
lean_inc(v_D_5532_);
lean_inc(v_Y_5531_);
lean_inc(v_u_5530_);
lean_inc(v_y_5529_);
lean_inc(v_G_5528_);
lean_dec(v_date_4413_);
v___x_5565_ = lean_box(0);
v_isShared_5566_ = v_isSharedCheck_5573_;
goto v_resetjp_5564_;
}
v_resetjp_5564_:
{
lean_object* v___x_5568_; 
if (v_isShared_5527_ == 0)
{
lean_ctor_set_tag(v___x_5526_, 1);
lean_ctor_set(v___x_5526_, 0, v_data_4415_);
v___x_5568_ = v___x_5526_;
goto v_reusejp_5567_;
}
else
{
lean_object* v_reuseFailAlloc_5572_; 
v_reuseFailAlloc_5572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5572_, 0, v_data_4415_);
v___x_5568_ = v_reuseFailAlloc_5572_;
goto v_reusejp_5567_;
}
v_reusejp_5567_:
{
lean_object* v___x_5570_; 
if (v_isShared_5566_ == 0)
{
lean_ctor_set(v___x_5565_, 22, v___x_5568_);
v___x_5570_ = v___x_5565_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v_G_5528_);
lean_ctor_set(v_reuseFailAlloc_5571_, 1, v_y_5529_);
lean_ctor_set(v_reuseFailAlloc_5571_, 2, v_u_5530_);
lean_ctor_set(v_reuseFailAlloc_5571_, 3, v_Y_5531_);
lean_ctor_set(v_reuseFailAlloc_5571_, 4, v_D_5532_);
lean_ctor_set(v_reuseFailAlloc_5571_, 5, v_M_5533_);
lean_ctor_set(v_reuseFailAlloc_5571_, 6, v_L_5534_);
lean_ctor_set(v_reuseFailAlloc_5571_, 7, v_d_5535_);
lean_ctor_set(v_reuseFailAlloc_5571_, 8, v_Q_5536_);
lean_ctor_set(v_reuseFailAlloc_5571_, 9, v_q_5537_);
lean_ctor_set(v_reuseFailAlloc_5571_, 10, v_w_5538_);
lean_ctor_set(v_reuseFailAlloc_5571_, 11, v_W_5539_);
lean_ctor_set(v_reuseFailAlloc_5571_, 12, v_E_5540_);
lean_ctor_set(v_reuseFailAlloc_5571_, 13, v_e_5541_);
lean_ctor_set(v_reuseFailAlloc_5571_, 14, v_c_5542_);
lean_ctor_set(v_reuseFailAlloc_5571_, 15, v_F_5543_);
lean_ctor_set(v_reuseFailAlloc_5571_, 16, v_a_5544_);
lean_ctor_set(v_reuseFailAlloc_5571_, 17, v_b_5545_);
lean_ctor_set(v_reuseFailAlloc_5571_, 18, v_B_5546_);
lean_ctor_set(v_reuseFailAlloc_5571_, 19, v_h_5547_);
lean_ctor_set(v_reuseFailAlloc_5571_, 20, v_K_5548_);
lean_ctor_set(v_reuseFailAlloc_5571_, 21, v_k_5549_);
lean_ctor_set(v_reuseFailAlloc_5571_, 22, v___x_5568_);
lean_ctor_set(v_reuseFailAlloc_5571_, 23, v_m_5550_);
lean_ctor_set(v_reuseFailAlloc_5571_, 24, v_s_5551_);
lean_ctor_set(v_reuseFailAlloc_5571_, 25, v_S_5552_);
lean_ctor_set(v_reuseFailAlloc_5571_, 26, v_A_5553_);
lean_ctor_set(v_reuseFailAlloc_5571_, 27, v_n_5554_);
lean_ctor_set(v_reuseFailAlloc_5571_, 28, v_N_5555_);
lean_ctor_set(v_reuseFailAlloc_5571_, 29, v_V_5556_);
lean_ctor_set(v_reuseFailAlloc_5571_, 30, v_z_5557_);
lean_ctor_set(v_reuseFailAlloc_5571_, 31, v_zabbrev_5558_);
lean_ctor_set(v_reuseFailAlloc_5571_, 32, v_v_5559_);
lean_ctor_set(v_reuseFailAlloc_5571_, 33, v_O_5560_);
lean_ctor_set(v_reuseFailAlloc_5571_, 34, v_X_5561_);
lean_ctor_set(v_reuseFailAlloc_5571_, 35, v_x_5562_);
lean_ctor_set(v_reuseFailAlloc_5571_, 36, v_Z_5563_);
v___x_5570_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
return v___x_5570_;
}
}
}
}
}
case 23:
{
lean_object* v___x_5578_; uint8_t v_isShared_5579_; uint8_t v_isSharedCheck_5627_; 
v_isSharedCheck_5627_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_5627_ == 0)
{
lean_object* v_unused_5628_; 
v_unused_5628_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_5628_);
v___x_5578_ = v_modifier_4414_;
v_isShared_5579_ = v_isSharedCheck_5627_;
goto v_resetjp_5577_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_5578_ = lean_box(0);
v_isShared_5579_ = v_isSharedCheck_5627_;
goto v_resetjp_5577_;
}
v_resetjp_5577_:
{
lean_object* v_G_5580_; lean_object* v_y_5581_; lean_object* v_u_5582_; lean_object* v_Y_5583_; lean_object* v_D_5584_; lean_object* v_M_5585_; lean_object* v_L_5586_; lean_object* v_d_5587_; lean_object* v_Q_5588_; lean_object* v_q_5589_; lean_object* v_w_5590_; lean_object* v_W_5591_; lean_object* v_E_5592_; lean_object* v_e_5593_; lean_object* v_c_5594_; lean_object* v_F_5595_; lean_object* v_a_5596_; lean_object* v_b_5597_; lean_object* v_B_5598_; lean_object* v_h_5599_; lean_object* v_K_5600_; lean_object* v_k_5601_; lean_object* v_H_5602_; lean_object* v_s_5603_; lean_object* v_S_5604_; lean_object* v_A_5605_; lean_object* v_n_5606_; lean_object* v_N_5607_; lean_object* v_V_5608_; lean_object* v_z_5609_; lean_object* v_zabbrev_5610_; lean_object* v_v_5611_; lean_object* v_O_5612_; lean_object* v_X_5613_; lean_object* v_x_5614_; lean_object* v_Z_5615_; lean_object* v___x_5617_; uint8_t v_isShared_5618_; uint8_t v_isSharedCheck_5625_; 
v_G_5580_ = lean_ctor_get(v_date_4413_, 0);
v_y_5581_ = lean_ctor_get(v_date_4413_, 1);
v_u_5582_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5583_ = lean_ctor_get(v_date_4413_, 3);
v_D_5584_ = lean_ctor_get(v_date_4413_, 4);
v_M_5585_ = lean_ctor_get(v_date_4413_, 5);
v_L_5586_ = lean_ctor_get(v_date_4413_, 6);
v_d_5587_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5588_ = lean_ctor_get(v_date_4413_, 8);
v_q_5589_ = lean_ctor_get(v_date_4413_, 9);
v_w_5590_ = lean_ctor_get(v_date_4413_, 10);
v_W_5591_ = lean_ctor_get(v_date_4413_, 11);
v_E_5592_ = lean_ctor_get(v_date_4413_, 12);
v_e_5593_ = lean_ctor_get(v_date_4413_, 13);
v_c_5594_ = lean_ctor_get(v_date_4413_, 14);
v_F_5595_ = lean_ctor_get(v_date_4413_, 15);
v_a_5596_ = lean_ctor_get(v_date_4413_, 16);
v_b_5597_ = lean_ctor_get(v_date_4413_, 17);
v_B_5598_ = lean_ctor_get(v_date_4413_, 18);
v_h_5599_ = lean_ctor_get(v_date_4413_, 19);
v_K_5600_ = lean_ctor_get(v_date_4413_, 20);
v_k_5601_ = lean_ctor_get(v_date_4413_, 21);
v_H_5602_ = lean_ctor_get(v_date_4413_, 22);
v_s_5603_ = lean_ctor_get(v_date_4413_, 24);
v_S_5604_ = lean_ctor_get(v_date_4413_, 25);
v_A_5605_ = lean_ctor_get(v_date_4413_, 26);
v_n_5606_ = lean_ctor_get(v_date_4413_, 27);
v_N_5607_ = lean_ctor_get(v_date_4413_, 28);
v_V_5608_ = lean_ctor_get(v_date_4413_, 29);
v_z_5609_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_5610_ = lean_ctor_get(v_date_4413_, 31);
v_v_5611_ = lean_ctor_get(v_date_4413_, 32);
v_O_5612_ = lean_ctor_get(v_date_4413_, 33);
v_X_5613_ = lean_ctor_get(v_date_4413_, 34);
v_x_5614_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5615_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5625_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5625_ == 0)
{
lean_object* v_unused_5626_; 
v_unused_5626_ = lean_ctor_get(v_date_4413_, 23);
lean_dec(v_unused_5626_);
v___x_5617_ = v_date_4413_;
v_isShared_5618_ = v_isSharedCheck_5625_;
goto v_resetjp_5616_;
}
else
{
lean_inc(v_Z_5615_);
lean_inc(v_x_5614_);
lean_inc(v_X_5613_);
lean_inc(v_O_5612_);
lean_inc(v_v_5611_);
lean_inc(v_zabbrev_5610_);
lean_inc(v_z_5609_);
lean_inc(v_V_5608_);
lean_inc(v_N_5607_);
lean_inc(v_n_5606_);
lean_inc(v_A_5605_);
lean_inc(v_S_5604_);
lean_inc(v_s_5603_);
lean_inc(v_H_5602_);
lean_inc(v_k_5601_);
lean_inc(v_K_5600_);
lean_inc(v_h_5599_);
lean_inc(v_B_5598_);
lean_inc(v_b_5597_);
lean_inc(v_a_5596_);
lean_inc(v_F_5595_);
lean_inc(v_c_5594_);
lean_inc(v_e_5593_);
lean_inc(v_E_5592_);
lean_inc(v_W_5591_);
lean_inc(v_w_5590_);
lean_inc(v_q_5589_);
lean_inc(v_Q_5588_);
lean_inc(v_d_5587_);
lean_inc(v_L_5586_);
lean_inc(v_M_5585_);
lean_inc(v_D_5584_);
lean_inc(v_Y_5583_);
lean_inc(v_u_5582_);
lean_inc(v_y_5581_);
lean_inc(v_G_5580_);
lean_dec(v_date_4413_);
v___x_5617_ = lean_box(0);
v_isShared_5618_ = v_isSharedCheck_5625_;
goto v_resetjp_5616_;
}
v_resetjp_5616_:
{
lean_object* v___x_5620_; 
if (v_isShared_5579_ == 0)
{
lean_ctor_set_tag(v___x_5578_, 1);
lean_ctor_set(v___x_5578_, 0, v_data_4415_);
v___x_5620_ = v___x_5578_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5624_; 
v_reuseFailAlloc_5624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5624_, 0, v_data_4415_);
v___x_5620_ = v_reuseFailAlloc_5624_;
goto v_reusejp_5619_;
}
v_reusejp_5619_:
{
lean_object* v___x_5622_; 
if (v_isShared_5618_ == 0)
{
lean_ctor_set(v___x_5617_, 23, v___x_5620_);
v___x_5622_ = v___x_5617_;
goto v_reusejp_5621_;
}
else
{
lean_object* v_reuseFailAlloc_5623_; 
v_reuseFailAlloc_5623_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5623_, 0, v_G_5580_);
lean_ctor_set(v_reuseFailAlloc_5623_, 1, v_y_5581_);
lean_ctor_set(v_reuseFailAlloc_5623_, 2, v_u_5582_);
lean_ctor_set(v_reuseFailAlloc_5623_, 3, v_Y_5583_);
lean_ctor_set(v_reuseFailAlloc_5623_, 4, v_D_5584_);
lean_ctor_set(v_reuseFailAlloc_5623_, 5, v_M_5585_);
lean_ctor_set(v_reuseFailAlloc_5623_, 6, v_L_5586_);
lean_ctor_set(v_reuseFailAlloc_5623_, 7, v_d_5587_);
lean_ctor_set(v_reuseFailAlloc_5623_, 8, v_Q_5588_);
lean_ctor_set(v_reuseFailAlloc_5623_, 9, v_q_5589_);
lean_ctor_set(v_reuseFailAlloc_5623_, 10, v_w_5590_);
lean_ctor_set(v_reuseFailAlloc_5623_, 11, v_W_5591_);
lean_ctor_set(v_reuseFailAlloc_5623_, 12, v_E_5592_);
lean_ctor_set(v_reuseFailAlloc_5623_, 13, v_e_5593_);
lean_ctor_set(v_reuseFailAlloc_5623_, 14, v_c_5594_);
lean_ctor_set(v_reuseFailAlloc_5623_, 15, v_F_5595_);
lean_ctor_set(v_reuseFailAlloc_5623_, 16, v_a_5596_);
lean_ctor_set(v_reuseFailAlloc_5623_, 17, v_b_5597_);
lean_ctor_set(v_reuseFailAlloc_5623_, 18, v_B_5598_);
lean_ctor_set(v_reuseFailAlloc_5623_, 19, v_h_5599_);
lean_ctor_set(v_reuseFailAlloc_5623_, 20, v_K_5600_);
lean_ctor_set(v_reuseFailAlloc_5623_, 21, v_k_5601_);
lean_ctor_set(v_reuseFailAlloc_5623_, 22, v_H_5602_);
lean_ctor_set(v_reuseFailAlloc_5623_, 23, v___x_5620_);
lean_ctor_set(v_reuseFailAlloc_5623_, 24, v_s_5603_);
lean_ctor_set(v_reuseFailAlloc_5623_, 25, v_S_5604_);
lean_ctor_set(v_reuseFailAlloc_5623_, 26, v_A_5605_);
lean_ctor_set(v_reuseFailAlloc_5623_, 27, v_n_5606_);
lean_ctor_set(v_reuseFailAlloc_5623_, 28, v_N_5607_);
lean_ctor_set(v_reuseFailAlloc_5623_, 29, v_V_5608_);
lean_ctor_set(v_reuseFailAlloc_5623_, 30, v_z_5609_);
lean_ctor_set(v_reuseFailAlloc_5623_, 31, v_zabbrev_5610_);
lean_ctor_set(v_reuseFailAlloc_5623_, 32, v_v_5611_);
lean_ctor_set(v_reuseFailAlloc_5623_, 33, v_O_5612_);
lean_ctor_set(v_reuseFailAlloc_5623_, 34, v_X_5613_);
lean_ctor_set(v_reuseFailAlloc_5623_, 35, v_x_5614_);
lean_ctor_set(v_reuseFailAlloc_5623_, 36, v_Z_5615_);
v___x_5622_ = v_reuseFailAlloc_5623_;
goto v_reusejp_5621_;
}
v_reusejp_5621_:
{
return v___x_5622_;
}
}
}
}
}
case 24:
{
lean_object* v___x_5630_; uint8_t v_isShared_5631_; uint8_t v_isSharedCheck_5679_; 
v_isSharedCheck_5679_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_5679_ == 0)
{
lean_object* v_unused_5680_; 
v_unused_5680_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_5680_);
v___x_5630_ = v_modifier_4414_;
v_isShared_5631_ = v_isSharedCheck_5679_;
goto v_resetjp_5629_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_5630_ = lean_box(0);
v_isShared_5631_ = v_isSharedCheck_5679_;
goto v_resetjp_5629_;
}
v_resetjp_5629_:
{
lean_object* v_G_5632_; lean_object* v_y_5633_; lean_object* v_u_5634_; lean_object* v_Y_5635_; lean_object* v_D_5636_; lean_object* v_M_5637_; lean_object* v_L_5638_; lean_object* v_d_5639_; lean_object* v_Q_5640_; lean_object* v_q_5641_; lean_object* v_w_5642_; lean_object* v_W_5643_; lean_object* v_E_5644_; lean_object* v_e_5645_; lean_object* v_c_5646_; lean_object* v_F_5647_; lean_object* v_a_5648_; lean_object* v_b_5649_; lean_object* v_B_5650_; lean_object* v_h_5651_; lean_object* v_K_5652_; lean_object* v_k_5653_; lean_object* v_H_5654_; lean_object* v_m_5655_; lean_object* v_S_5656_; lean_object* v_A_5657_; lean_object* v_n_5658_; lean_object* v_N_5659_; lean_object* v_V_5660_; lean_object* v_z_5661_; lean_object* v_zabbrev_5662_; lean_object* v_v_5663_; lean_object* v_O_5664_; lean_object* v_X_5665_; lean_object* v_x_5666_; lean_object* v_Z_5667_; lean_object* v___x_5669_; uint8_t v_isShared_5670_; uint8_t v_isSharedCheck_5677_; 
v_G_5632_ = lean_ctor_get(v_date_4413_, 0);
v_y_5633_ = lean_ctor_get(v_date_4413_, 1);
v_u_5634_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5635_ = lean_ctor_get(v_date_4413_, 3);
v_D_5636_ = lean_ctor_get(v_date_4413_, 4);
v_M_5637_ = lean_ctor_get(v_date_4413_, 5);
v_L_5638_ = lean_ctor_get(v_date_4413_, 6);
v_d_5639_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5640_ = lean_ctor_get(v_date_4413_, 8);
v_q_5641_ = lean_ctor_get(v_date_4413_, 9);
v_w_5642_ = lean_ctor_get(v_date_4413_, 10);
v_W_5643_ = lean_ctor_get(v_date_4413_, 11);
v_E_5644_ = lean_ctor_get(v_date_4413_, 12);
v_e_5645_ = lean_ctor_get(v_date_4413_, 13);
v_c_5646_ = lean_ctor_get(v_date_4413_, 14);
v_F_5647_ = lean_ctor_get(v_date_4413_, 15);
v_a_5648_ = lean_ctor_get(v_date_4413_, 16);
v_b_5649_ = lean_ctor_get(v_date_4413_, 17);
v_B_5650_ = lean_ctor_get(v_date_4413_, 18);
v_h_5651_ = lean_ctor_get(v_date_4413_, 19);
v_K_5652_ = lean_ctor_get(v_date_4413_, 20);
v_k_5653_ = lean_ctor_get(v_date_4413_, 21);
v_H_5654_ = lean_ctor_get(v_date_4413_, 22);
v_m_5655_ = lean_ctor_get(v_date_4413_, 23);
v_S_5656_ = lean_ctor_get(v_date_4413_, 25);
v_A_5657_ = lean_ctor_get(v_date_4413_, 26);
v_n_5658_ = lean_ctor_get(v_date_4413_, 27);
v_N_5659_ = lean_ctor_get(v_date_4413_, 28);
v_V_5660_ = lean_ctor_get(v_date_4413_, 29);
v_z_5661_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_5662_ = lean_ctor_get(v_date_4413_, 31);
v_v_5663_ = lean_ctor_get(v_date_4413_, 32);
v_O_5664_ = lean_ctor_get(v_date_4413_, 33);
v_X_5665_ = lean_ctor_get(v_date_4413_, 34);
v_x_5666_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5667_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5677_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5677_ == 0)
{
lean_object* v_unused_5678_; 
v_unused_5678_ = lean_ctor_get(v_date_4413_, 24);
lean_dec(v_unused_5678_);
v___x_5669_ = v_date_4413_;
v_isShared_5670_ = v_isSharedCheck_5677_;
goto v_resetjp_5668_;
}
else
{
lean_inc(v_Z_5667_);
lean_inc(v_x_5666_);
lean_inc(v_X_5665_);
lean_inc(v_O_5664_);
lean_inc(v_v_5663_);
lean_inc(v_zabbrev_5662_);
lean_inc(v_z_5661_);
lean_inc(v_V_5660_);
lean_inc(v_N_5659_);
lean_inc(v_n_5658_);
lean_inc(v_A_5657_);
lean_inc(v_S_5656_);
lean_inc(v_m_5655_);
lean_inc(v_H_5654_);
lean_inc(v_k_5653_);
lean_inc(v_K_5652_);
lean_inc(v_h_5651_);
lean_inc(v_B_5650_);
lean_inc(v_b_5649_);
lean_inc(v_a_5648_);
lean_inc(v_F_5647_);
lean_inc(v_c_5646_);
lean_inc(v_e_5645_);
lean_inc(v_E_5644_);
lean_inc(v_W_5643_);
lean_inc(v_w_5642_);
lean_inc(v_q_5641_);
lean_inc(v_Q_5640_);
lean_inc(v_d_5639_);
lean_inc(v_L_5638_);
lean_inc(v_M_5637_);
lean_inc(v_D_5636_);
lean_inc(v_Y_5635_);
lean_inc(v_u_5634_);
lean_inc(v_y_5633_);
lean_inc(v_G_5632_);
lean_dec(v_date_4413_);
v___x_5669_ = lean_box(0);
v_isShared_5670_ = v_isSharedCheck_5677_;
goto v_resetjp_5668_;
}
v_resetjp_5668_:
{
lean_object* v___x_5672_; 
if (v_isShared_5631_ == 0)
{
lean_ctor_set_tag(v___x_5630_, 1);
lean_ctor_set(v___x_5630_, 0, v_data_4415_);
v___x_5672_ = v___x_5630_;
goto v_reusejp_5671_;
}
else
{
lean_object* v_reuseFailAlloc_5676_; 
v_reuseFailAlloc_5676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5676_, 0, v_data_4415_);
v___x_5672_ = v_reuseFailAlloc_5676_;
goto v_reusejp_5671_;
}
v_reusejp_5671_:
{
lean_object* v___x_5674_; 
if (v_isShared_5670_ == 0)
{
lean_ctor_set(v___x_5669_, 24, v___x_5672_);
v___x_5674_ = v___x_5669_;
goto v_reusejp_5673_;
}
else
{
lean_object* v_reuseFailAlloc_5675_; 
v_reuseFailAlloc_5675_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_G_5632_);
lean_ctor_set(v_reuseFailAlloc_5675_, 1, v_y_5633_);
lean_ctor_set(v_reuseFailAlloc_5675_, 2, v_u_5634_);
lean_ctor_set(v_reuseFailAlloc_5675_, 3, v_Y_5635_);
lean_ctor_set(v_reuseFailAlloc_5675_, 4, v_D_5636_);
lean_ctor_set(v_reuseFailAlloc_5675_, 5, v_M_5637_);
lean_ctor_set(v_reuseFailAlloc_5675_, 6, v_L_5638_);
lean_ctor_set(v_reuseFailAlloc_5675_, 7, v_d_5639_);
lean_ctor_set(v_reuseFailAlloc_5675_, 8, v_Q_5640_);
lean_ctor_set(v_reuseFailAlloc_5675_, 9, v_q_5641_);
lean_ctor_set(v_reuseFailAlloc_5675_, 10, v_w_5642_);
lean_ctor_set(v_reuseFailAlloc_5675_, 11, v_W_5643_);
lean_ctor_set(v_reuseFailAlloc_5675_, 12, v_E_5644_);
lean_ctor_set(v_reuseFailAlloc_5675_, 13, v_e_5645_);
lean_ctor_set(v_reuseFailAlloc_5675_, 14, v_c_5646_);
lean_ctor_set(v_reuseFailAlloc_5675_, 15, v_F_5647_);
lean_ctor_set(v_reuseFailAlloc_5675_, 16, v_a_5648_);
lean_ctor_set(v_reuseFailAlloc_5675_, 17, v_b_5649_);
lean_ctor_set(v_reuseFailAlloc_5675_, 18, v_B_5650_);
lean_ctor_set(v_reuseFailAlloc_5675_, 19, v_h_5651_);
lean_ctor_set(v_reuseFailAlloc_5675_, 20, v_K_5652_);
lean_ctor_set(v_reuseFailAlloc_5675_, 21, v_k_5653_);
lean_ctor_set(v_reuseFailAlloc_5675_, 22, v_H_5654_);
lean_ctor_set(v_reuseFailAlloc_5675_, 23, v_m_5655_);
lean_ctor_set(v_reuseFailAlloc_5675_, 24, v___x_5672_);
lean_ctor_set(v_reuseFailAlloc_5675_, 25, v_S_5656_);
lean_ctor_set(v_reuseFailAlloc_5675_, 26, v_A_5657_);
lean_ctor_set(v_reuseFailAlloc_5675_, 27, v_n_5658_);
lean_ctor_set(v_reuseFailAlloc_5675_, 28, v_N_5659_);
lean_ctor_set(v_reuseFailAlloc_5675_, 29, v_V_5660_);
lean_ctor_set(v_reuseFailAlloc_5675_, 30, v_z_5661_);
lean_ctor_set(v_reuseFailAlloc_5675_, 31, v_zabbrev_5662_);
lean_ctor_set(v_reuseFailAlloc_5675_, 32, v_v_5663_);
lean_ctor_set(v_reuseFailAlloc_5675_, 33, v_O_5664_);
lean_ctor_set(v_reuseFailAlloc_5675_, 34, v_X_5665_);
lean_ctor_set(v_reuseFailAlloc_5675_, 35, v_x_5666_);
lean_ctor_set(v_reuseFailAlloc_5675_, 36, v_Z_5667_);
v___x_5674_ = v_reuseFailAlloc_5675_;
goto v_reusejp_5673_;
}
v_reusejp_5673_:
{
return v___x_5674_;
}
}
}
}
}
case 25:
{
lean_object* v___x_5682_; uint8_t v_isShared_5683_; uint8_t v_isSharedCheck_5731_; 
v_isSharedCheck_5731_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_5731_ == 0)
{
lean_object* v_unused_5732_; 
v_unused_5732_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_5732_);
v___x_5682_ = v_modifier_4414_;
v_isShared_5683_ = v_isSharedCheck_5731_;
goto v_resetjp_5681_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_5682_ = lean_box(0);
v_isShared_5683_ = v_isSharedCheck_5731_;
goto v_resetjp_5681_;
}
v_resetjp_5681_:
{
lean_object* v_G_5684_; lean_object* v_y_5685_; lean_object* v_u_5686_; lean_object* v_Y_5687_; lean_object* v_D_5688_; lean_object* v_M_5689_; lean_object* v_L_5690_; lean_object* v_d_5691_; lean_object* v_Q_5692_; lean_object* v_q_5693_; lean_object* v_w_5694_; lean_object* v_W_5695_; lean_object* v_E_5696_; lean_object* v_e_5697_; lean_object* v_c_5698_; lean_object* v_F_5699_; lean_object* v_a_5700_; lean_object* v_b_5701_; lean_object* v_B_5702_; lean_object* v_h_5703_; lean_object* v_K_5704_; lean_object* v_k_5705_; lean_object* v_H_5706_; lean_object* v_m_5707_; lean_object* v_s_5708_; lean_object* v_A_5709_; lean_object* v_n_5710_; lean_object* v_N_5711_; lean_object* v_V_5712_; lean_object* v_z_5713_; lean_object* v_zabbrev_5714_; lean_object* v_v_5715_; lean_object* v_O_5716_; lean_object* v_X_5717_; lean_object* v_x_5718_; lean_object* v_Z_5719_; lean_object* v___x_5721_; uint8_t v_isShared_5722_; uint8_t v_isSharedCheck_5729_; 
v_G_5684_ = lean_ctor_get(v_date_4413_, 0);
v_y_5685_ = lean_ctor_get(v_date_4413_, 1);
v_u_5686_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5687_ = lean_ctor_get(v_date_4413_, 3);
v_D_5688_ = lean_ctor_get(v_date_4413_, 4);
v_M_5689_ = lean_ctor_get(v_date_4413_, 5);
v_L_5690_ = lean_ctor_get(v_date_4413_, 6);
v_d_5691_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5692_ = lean_ctor_get(v_date_4413_, 8);
v_q_5693_ = lean_ctor_get(v_date_4413_, 9);
v_w_5694_ = lean_ctor_get(v_date_4413_, 10);
v_W_5695_ = lean_ctor_get(v_date_4413_, 11);
v_E_5696_ = lean_ctor_get(v_date_4413_, 12);
v_e_5697_ = lean_ctor_get(v_date_4413_, 13);
v_c_5698_ = lean_ctor_get(v_date_4413_, 14);
v_F_5699_ = lean_ctor_get(v_date_4413_, 15);
v_a_5700_ = lean_ctor_get(v_date_4413_, 16);
v_b_5701_ = lean_ctor_get(v_date_4413_, 17);
v_B_5702_ = lean_ctor_get(v_date_4413_, 18);
v_h_5703_ = lean_ctor_get(v_date_4413_, 19);
v_K_5704_ = lean_ctor_get(v_date_4413_, 20);
v_k_5705_ = lean_ctor_get(v_date_4413_, 21);
v_H_5706_ = lean_ctor_get(v_date_4413_, 22);
v_m_5707_ = lean_ctor_get(v_date_4413_, 23);
v_s_5708_ = lean_ctor_get(v_date_4413_, 24);
v_A_5709_ = lean_ctor_get(v_date_4413_, 26);
v_n_5710_ = lean_ctor_get(v_date_4413_, 27);
v_N_5711_ = lean_ctor_get(v_date_4413_, 28);
v_V_5712_ = lean_ctor_get(v_date_4413_, 29);
v_z_5713_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_5714_ = lean_ctor_get(v_date_4413_, 31);
v_v_5715_ = lean_ctor_get(v_date_4413_, 32);
v_O_5716_ = lean_ctor_get(v_date_4413_, 33);
v_X_5717_ = lean_ctor_get(v_date_4413_, 34);
v_x_5718_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5719_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5729_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5729_ == 0)
{
lean_object* v_unused_5730_; 
v_unused_5730_ = lean_ctor_get(v_date_4413_, 25);
lean_dec(v_unused_5730_);
v___x_5721_ = v_date_4413_;
v_isShared_5722_ = v_isSharedCheck_5729_;
goto v_resetjp_5720_;
}
else
{
lean_inc(v_Z_5719_);
lean_inc(v_x_5718_);
lean_inc(v_X_5717_);
lean_inc(v_O_5716_);
lean_inc(v_v_5715_);
lean_inc(v_zabbrev_5714_);
lean_inc(v_z_5713_);
lean_inc(v_V_5712_);
lean_inc(v_N_5711_);
lean_inc(v_n_5710_);
lean_inc(v_A_5709_);
lean_inc(v_s_5708_);
lean_inc(v_m_5707_);
lean_inc(v_H_5706_);
lean_inc(v_k_5705_);
lean_inc(v_K_5704_);
lean_inc(v_h_5703_);
lean_inc(v_B_5702_);
lean_inc(v_b_5701_);
lean_inc(v_a_5700_);
lean_inc(v_F_5699_);
lean_inc(v_c_5698_);
lean_inc(v_e_5697_);
lean_inc(v_E_5696_);
lean_inc(v_W_5695_);
lean_inc(v_w_5694_);
lean_inc(v_q_5693_);
lean_inc(v_Q_5692_);
lean_inc(v_d_5691_);
lean_inc(v_L_5690_);
lean_inc(v_M_5689_);
lean_inc(v_D_5688_);
lean_inc(v_Y_5687_);
lean_inc(v_u_5686_);
lean_inc(v_y_5685_);
lean_inc(v_G_5684_);
lean_dec(v_date_4413_);
v___x_5721_ = lean_box(0);
v_isShared_5722_ = v_isSharedCheck_5729_;
goto v_resetjp_5720_;
}
v_resetjp_5720_:
{
lean_object* v___x_5724_; 
if (v_isShared_5683_ == 0)
{
lean_ctor_set_tag(v___x_5682_, 1);
lean_ctor_set(v___x_5682_, 0, v_data_4415_);
v___x_5724_ = v___x_5682_;
goto v_reusejp_5723_;
}
else
{
lean_object* v_reuseFailAlloc_5728_; 
v_reuseFailAlloc_5728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5728_, 0, v_data_4415_);
v___x_5724_ = v_reuseFailAlloc_5728_;
goto v_reusejp_5723_;
}
v_reusejp_5723_:
{
lean_object* v___x_5726_; 
if (v_isShared_5722_ == 0)
{
lean_ctor_set(v___x_5721_, 25, v___x_5724_);
v___x_5726_ = v___x_5721_;
goto v_reusejp_5725_;
}
else
{
lean_object* v_reuseFailAlloc_5727_; 
v_reuseFailAlloc_5727_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5727_, 0, v_G_5684_);
lean_ctor_set(v_reuseFailAlloc_5727_, 1, v_y_5685_);
lean_ctor_set(v_reuseFailAlloc_5727_, 2, v_u_5686_);
lean_ctor_set(v_reuseFailAlloc_5727_, 3, v_Y_5687_);
lean_ctor_set(v_reuseFailAlloc_5727_, 4, v_D_5688_);
lean_ctor_set(v_reuseFailAlloc_5727_, 5, v_M_5689_);
lean_ctor_set(v_reuseFailAlloc_5727_, 6, v_L_5690_);
lean_ctor_set(v_reuseFailAlloc_5727_, 7, v_d_5691_);
lean_ctor_set(v_reuseFailAlloc_5727_, 8, v_Q_5692_);
lean_ctor_set(v_reuseFailAlloc_5727_, 9, v_q_5693_);
lean_ctor_set(v_reuseFailAlloc_5727_, 10, v_w_5694_);
lean_ctor_set(v_reuseFailAlloc_5727_, 11, v_W_5695_);
lean_ctor_set(v_reuseFailAlloc_5727_, 12, v_E_5696_);
lean_ctor_set(v_reuseFailAlloc_5727_, 13, v_e_5697_);
lean_ctor_set(v_reuseFailAlloc_5727_, 14, v_c_5698_);
lean_ctor_set(v_reuseFailAlloc_5727_, 15, v_F_5699_);
lean_ctor_set(v_reuseFailAlloc_5727_, 16, v_a_5700_);
lean_ctor_set(v_reuseFailAlloc_5727_, 17, v_b_5701_);
lean_ctor_set(v_reuseFailAlloc_5727_, 18, v_B_5702_);
lean_ctor_set(v_reuseFailAlloc_5727_, 19, v_h_5703_);
lean_ctor_set(v_reuseFailAlloc_5727_, 20, v_K_5704_);
lean_ctor_set(v_reuseFailAlloc_5727_, 21, v_k_5705_);
lean_ctor_set(v_reuseFailAlloc_5727_, 22, v_H_5706_);
lean_ctor_set(v_reuseFailAlloc_5727_, 23, v_m_5707_);
lean_ctor_set(v_reuseFailAlloc_5727_, 24, v_s_5708_);
lean_ctor_set(v_reuseFailAlloc_5727_, 25, v___x_5724_);
lean_ctor_set(v_reuseFailAlloc_5727_, 26, v_A_5709_);
lean_ctor_set(v_reuseFailAlloc_5727_, 27, v_n_5710_);
lean_ctor_set(v_reuseFailAlloc_5727_, 28, v_N_5711_);
lean_ctor_set(v_reuseFailAlloc_5727_, 29, v_V_5712_);
lean_ctor_set(v_reuseFailAlloc_5727_, 30, v_z_5713_);
lean_ctor_set(v_reuseFailAlloc_5727_, 31, v_zabbrev_5714_);
lean_ctor_set(v_reuseFailAlloc_5727_, 32, v_v_5715_);
lean_ctor_set(v_reuseFailAlloc_5727_, 33, v_O_5716_);
lean_ctor_set(v_reuseFailAlloc_5727_, 34, v_X_5717_);
lean_ctor_set(v_reuseFailAlloc_5727_, 35, v_x_5718_);
lean_ctor_set(v_reuseFailAlloc_5727_, 36, v_Z_5719_);
v___x_5726_ = v_reuseFailAlloc_5727_;
goto v_reusejp_5725_;
}
v_reusejp_5725_:
{
return v___x_5726_;
}
}
}
}
}
case 26:
{
lean_object* v___x_5734_; uint8_t v_isShared_5735_; uint8_t v_isSharedCheck_5783_; 
v_isSharedCheck_5783_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_5783_ == 0)
{
lean_object* v_unused_5784_; 
v_unused_5784_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_5784_);
v___x_5734_ = v_modifier_4414_;
v_isShared_5735_ = v_isSharedCheck_5783_;
goto v_resetjp_5733_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_5734_ = lean_box(0);
v_isShared_5735_ = v_isSharedCheck_5783_;
goto v_resetjp_5733_;
}
v_resetjp_5733_:
{
lean_object* v_G_5736_; lean_object* v_y_5737_; lean_object* v_u_5738_; lean_object* v_Y_5739_; lean_object* v_D_5740_; lean_object* v_M_5741_; lean_object* v_L_5742_; lean_object* v_d_5743_; lean_object* v_Q_5744_; lean_object* v_q_5745_; lean_object* v_w_5746_; lean_object* v_W_5747_; lean_object* v_E_5748_; lean_object* v_e_5749_; lean_object* v_c_5750_; lean_object* v_F_5751_; lean_object* v_a_5752_; lean_object* v_b_5753_; lean_object* v_B_5754_; lean_object* v_h_5755_; lean_object* v_K_5756_; lean_object* v_k_5757_; lean_object* v_H_5758_; lean_object* v_m_5759_; lean_object* v_s_5760_; lean_object* v_S_5761_; lean_object* v_n_5762_; lean_object* v_N_5763_; lean_object* v_V_5764_; lean_object* v_z_5765_; lean_object* v_zabbrev_5766_; lean_object* v_v_5767_; lean_object* v_O_5768_; lean_object* v_X_5769_; lean_object* v_x_5770_; lean_object* v_Z_5771_; lean_object* v___x_5773_; uint8_t v_isShared_5774_; uint8_t v_isSharedCheck_5781_; 
v_G_5736_ = lean_ctor_get(v_date_4413_, 0);
v_y_5737_ = lean_ctor_get(v_date_4413_, 1);
v_u_5738_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5739_ = lean_ctor_get(v_date_4413_, 3);
v_D_5740_ = lean_ctor_get(v_date_4413_, 4);
v_M_5741_ = lean_ctor_get(v_date_4413_, 5);
v_L_5742_ = lean_ctor_get(v_date_4413_, 6);
v_d_5743_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5744_ = lean_ctor_get(v_date_4413_, 8);
v_q_5745_ = lean_ctor_get(v_date_4413_, 9);
v_w_5746_ = lean_ctor_get(v_date_4413_, 10);
v_W_5747_ = lean_ctor_get(v_date_4413_, 11);
v_E_5748_ = lean_ctor_get(v_date_4413_, 12);
v_e_5749_ = lean_ctor_get(v_date_4413_, 13);
v_c_5750_ = lean_ctor_get(v_date_4413_, 14);
v_F_5751_ = lean_ctor_get(v_date_4413_, 15);
v_a_5752_ = lean_ctor_get(v_date_4413_, 16);
v_b_5753_ = lean_ctor_get(v_date_4413_, 17);
v_B_5754_ = lean_ctor_get(v_date_4413_, 18);
v_h_5755_ = lean_ctor_get(v_date_4413_, 19);
v_K_5756_ = lean_ctor_get(v_date_4413_, 20);
v_k_5757_ = lean_ctor_get(v_date_4413_, 21);
v_H_5758_ = lean_ctor_get(v_date_4413_, 22);
v_m_5759_ = lean_ctor_get(v_date_4413_, 23);
v_s_5760_ = lean_ctor_get(v_date_4413_, 24);
v_S_5761_ = lean_ctor_get(v_date_4413_, 25);
v_n_5762_ = lean_ctor_get(v_date_4413_, 27);
v_N_5763_ = lean_ctor_get(v_date_4413_, 28);
v_V_5764_ = lean_ctor_get(v_date_4413_, 29);
v_z_5765_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_5766_ = lean_ctor_get(v_date_4413_, 31);
v_v_5767_ = lean_ctor_get(v_date_4413_, 32);
v_O_5768_ = lean_ctor_get(v_date_4413_, 33);
v_X_5769_ = lean_ctor_get(v_date_4413_, 34);
v_x_5770_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5771_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5781_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5781_ == 0)
{
lean_object* v_unused_5782_; 
v_unused_5782_ = lean_ctor_get(v_date_4413_, 26);
lean_dec(v_unused_5782_);
v___x_5773_ = v_date_4413_;
v_isShared_5774_ = v_isSharedCheck_5781_;
goto v_resetjp_5772_;
}
else
{
lean_inc(v_Z_5771_);
lean_inc(v_x_5770_);
lean_inc(v_X_5769_);
lean_inc(v_O_5768_);
lean_inc(v_v_5767_);
lean_inc(v_zabbrev_5766_);
lean_inc(v_z_5765_);
lean_inc(v_V_5764_);
lean_inc(v_N_5763_);
lean_inc(v_n_5762_);
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
lean_dec(v_date_4413_);
v___x_5773_ = lean_box(0);
v_isShared_5774_ = v_isSharedCheck_5781_;
goto v_resetjp_5772_;
}
v_resetjp_5772_:
{
lean_object* v___x_5776_; 
if (v_isShared_5735_ == 0)
{
lean_ctor_set_tag(v___x_5734_, 1);
lean_ctor_set(v___x_5734_, 0, v_data_4415_);
v___x_5776_ = v___x_5734_;
goto v_reusejp_5775_;
}
else
{
lean_object* v_reuseFailAlloc_5780_; 
v_reuseFailAlloc_5780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5780_, 0, v_data_4415_);
v___x_5776_ = v_reuseFailAlloc_5780_;
goto v_reusejp_5775_;
}
v_reusejp_5775_:
{
lean_object* v___x_5778_; 
if (v_isShared_5774_ == 0)
{
lean_ctor_set(v___x_5773_, 26, v___x_5776_);
v___x_5778_ = v___x_5773_;
goto v_reusejp_5777_;
}
else
{
lean_object* v_reuseFailAlloc_5779_; 
v_reuseFailAlloc_5779_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5779_, 0, v_G_5736_);
lean_ctor_set(v_reuseFailAlloc_5779_, 1, v_y_5737_);
lean_ctor_set(v_reuseFailAlloc_5779_, 2, v_u_5738_);
lean_ctor_set(v_reuseFailAlloc_5779_, 3, v_Y_5739_);
lean_ctor_set(v_reuseFailAlloc_5779_, 4, v_D_5740_);
lean_ctor_set(v_reuseFailAlloc_5779_, 5, v_M_5741_);
lean_ctor_set(v_reuseFailAlloc_5779_, 6, v_L_5742_);
lean_ctor_set(v_reuseFailAlloc_5779_, 7, v_d_5743_);
lean_ctor_set(v_reuseFailAlloc_5779_, 8, v_Q_5744_);
lean_ctor_set(v_reuseFailAlloc_5779_, 9, v_q_5745_);
lean_ctor_set(v_reuseFailAlloc_5779_, 10, v_w_5746_);
lean_ctor_set(v_reuseFailAlloc_5779_, 11, v_W_5747_);
lean_ctor_set(v_reuseFailAlloc_5779_, 12, v_E_5748_);
lean_ctor_set(v_reuseFailAlloc_5779_, 13, v_e_5749_);
lean_ctor_set(v_reuseFailAlloc_5779_, 14, v_c_5750_);
lean_ctor_set(v_reuseFailAlloc_5779_, 15, v_F_5751_);
lean_ctor_set(v_reuseFailAlloc_5779_, 16, v_a_5752_);
lean_ctor_set(v_reuseFailAlloc_5779_, 17, v_b_5753_);
lean_ctor_set(v_reuseFailAlloc_5779_, 18, v_B_5754_);
lean_ctor_set(v_reuseFailAlloc_5779_, 19, v_h_5755_);
lean_ctor_set(v_reuseFailAlloc_5779_, 20, v_K_5756_);
lean_ctor_set(v_reuseFailAlloc_5779_, 21, v_k_5757_);
lean_ctor_set(v_reuseFailAlloc_5779_, 22, v_H_5758_);
lean_ctor_set(v_reuseFailAlloc_5779_, 23, v_m_5759_);
lean_ctor_set(v_reuseFailAlloc_5779_, 24, v_s_5760_);
lean_ctor_set(v_reuseFailAlloc_5779_, 25, v_S_5761_);
lean_ctor_set(v_reuseFailAlloc_5779_, 26, v___x_5776_);
lean_ctor_set(v_reuseFailAlloc_5779_, 27, v_n_5762_);
lean_ctor_set(v_reuseFailAlloc_5779_, 28, v_N_5763_);
lean_ctor_set(v_reuseFailAlloc_5779_, 29, v_V_5764_);
lean_ctor_set(v_reuseFailAlloc_5779_, 30, v_z_5765_);
lean_ctor_set(v_reuseFailAlloc_5779_, 31, v_zabbrev_5766_);
lean_ctor_set(v_reuseFailAlloc_5779_, 32, v_v_5767_);
lean_ctor_set(v_reuseFailAlloc_5779_, 33, v_O_5768_);
lean_ctor_set(v_reuseFailAlloc_5779_, 34, v_X_5769_);
lean_ctor_set(v_reuseFailAlloc_5779_, 35, v_x_5770_);
lean_ctor_set(v_reuseFailAlloc_5779_, 36, v_Z_5771_);
v___x_5778_ = v_reuseFailAlloc_5779_;
goto v_reusejp_5777_;
}
v_reusejp_5777_:
{
return v___x_5778_;
}
}
}
}
}
case 27:
{
lean_object* v___x_5786_; uint8_t v_isShared_5787_; uint8_t v_isSharedCheck_5835_; 
v_isSharedCheck_5835_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_5835_ == 0)
{
lean_object* v_unused_5836_; 
v_unused_5836_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_5836_);
v___x_5786_ = v_modifier_4414_;
v_isShared_5787_ = v_isSharedCheck_5835_;
goto v_resetjp_5785_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_5786_ = lean_box(0);
v_isShared_5787_ = v_isSharedCheck_5835_;
goto v_resetjp_5785_;
}
v_resetjp_5785_:
{
lean_object* v_G_5788_; lean_object* v_y_5789_; lean_object* v_u_5790_; lean_object* v_Y_5791_; lean_object* v_D_5792_; lean_object* v_M_5793_; lean_object* v_L_5794_; lean_object* v_d_5795_; lean_object* v_Q_5796_; lean_object* v_q_5797_; lean_object* v_w_5798_; lean_object* v_W_5799_; lean_object* v_E_5800_; lean_object* v_e_5801_; lean_object* v_c_5802_; lean_object* v_F_5803_; lean_object* v_a_5804_; lean_object* v_b_5805_; lean_object* v_B_5806_; lean_object* v_h_5807_; lean_object* v_K_5808_; lean_object* v_k_5809_; lean_object* v_H_5810_; lean_object* v_m_5811_; lean_object* v_s_5812_; lean_object* v_S_5813_; lean_object* v_A_5814_; lean_object* v_N_5815_; lean_object* v_V_5816_; lean_object* v_z_5817_; lean_object* v_zabbrev_5818_; lean_object* v_v_5819_; lean_object* v_O_5820_; lean_object* v_X_5821_; lean_object* v_x_5822_; lean_object* v_Z_5823_; lean_object* v___x_5825_; uint8_t v_isShared_5826_; uint8_t v_isSharedCheck_5833_; 
v_G_5788_ = lean_ctor_get(v_date_4413_, 0);
v_y_5789_ = lean_ctor_get(v_date_4413_, 1);
v_u_5790_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5791_ = lean_ctor_get(v_date_4413_, 3);
v_D_5792_ = lean_ctor_get(v_date_4413_, 4);
v_M_5793_ = lean_ctor_get(v_date_4413_, 5);
v_L_5794_ = lean_ctor_get(v_date_4413_, 6);
v_d_5795_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5796_ = lean_ctor_get(v_date_4413_, 8);
v_q_5797_ = lean_ctor_get(v_date_4413_, 9);
v_w_5798_ = lean_ctor_get(v_date_4413_, 10);
v_W_5799_ = lean_ctor_get(v_date_4413_, 11);
v_E_5800_ = lean_ctor_get(v_date_4413_, 12);
v_e_5801_ = lean_ctor_get(v_date_4413_, 13);
v_c_5802_ = lean_ctor_get(v_date_4413_, 14);
v_F_5803_ = lean_ctor_get(v_date_4413_, 15);
v_a_5804_ = lean_ctor_get(v_date_4413_, 16);
v_b_5805_ = lean_ctor_get(v_date_4413_, 17);
v_B_5806_ = lean_ctor_get(v_date_4413_, 18);
v_h_5807_ = lean_ctor_get(v_date_4413_, 19);
v_K_5808_ = lean_ctor_get(v_date_4413_, 20);
v_k_5809_ = lean_ctor_get(v_date_4413_, 21);
v_H_5810_ = lean_ctor_get(v_date_4413_, 22);
v_m_5811_ = lean_ctor_get(v_date_4413_, 23);
v_s_5812_ = lean_ctor_get(v_date_4413_, 24);
v_S_5813_ = lean_ctor_get(v_date_4413_, 25);
v_A_5814_ = lean_ctor_get(v_date_4413_, 26);
v_N_5815_ = lean_ctor_get(v_date_4413_, 28);
v_V_5816_ = lean_ctor_get(v_date_4413_, 29);
v_z_5817_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_5818_ = lean_ctor_get(v_date_4413_, 31);
v_v_5819_ = lean_ctor_get(v_date_4413_, 32);
v_O_5820_ = lean_ctor_get(v_date_4413_, 33);
v_X_5821_ = lean_ctor_get(v_date_4413_, 34);
v_x_5822_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5823_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5833_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5833_ == 0)
{
lean_object* v_unused_5834_; 
v_unused_5834_ = lean_ctor_get(v_date_4413_, 27);
lean_dec(v_unused_5834_);
v___x_5825_ = v_date_4413_;
v_isShared_5826_ = v_isSharedCheck_5833_;
goto v_resetjp_5824_;
}
else
{
lean_inc(v_Z_5823_);
lean_inc(v_x_5822_);
lean_inc(v_X_5821_);
lean_inc(v_O_5820_);
lean_inc(v_v_5819_);
lean_inc(v_zabbrev_5818_);
lean_inc(v_z_5817_);
lean_inc(v_V_5816_);
lean_inc(v_N_5815_);
lean_inc(v_A_5814_);
lean_inc(v_S_5813_);
lean_inc(v_s_5812_);
lean_inc(v_m_5811_);
lean_inc(v_H_5810_);
lean_inc(v_k_5809_);
lean_inc(v_K_5808_);
lean_inc(v_h_5807_);
lean_inc(v_B_5806_);
lean_inc(v_b_5805_);
lean_inc(v_a_5804_);
lean_inc(v_F_5803_);
lean_inc(v_c_5802_);
lean_inc(v_e_5801_);
lean_inc(v_E_5800_);
lean_inc(v_W_5799_);
lean_inc(v_w_5798_);
lean_inc(v_q_5797_);
lean_inc(v_Q_5796_);
lean_inc(v_d_5795_);
lean_inc(v_L_5794_);
lean_inc(v_M_5793_);
lean_inc(v_D_5792_);
lean_inc(v_Y_5791_);
lean_inc(v_u_5790_);
lean_inc(v_y_5789_);
lean_inc(v_G_5788_);
lean_dec(v_date_4413_);
v___x_5825_ = lean_box(0);
v_isShared_5826_ = v_isSharedCheck_5833_;
goto v_resetjp_5824_;
}
v_resetjp_5824_:
{
lean_object* v___x_5828_; 
if (v_isShared_5787_ == 0)
{
lean_ctor_set_tag(v___x_5786_, 1);
lean_ctor_set(v___x_5786_, 0, v_data_4415_);
v___x_5828_ = v___x_5786_;
goto v_reusejp_5827_;
}
else
{
lean_object* v_reuseFailAlloc_5832_; 
v_reuseFailAlloc_5832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5832_, 0, v_data_4415_);
v___x_5828_ = v_reuseFailAlloc_5832_;
goto v_reusejp_5827_;
}
v_reusejp_5827_:
{
lean_object* v___x_5830_; 
if (v_isShared_5826_ == 0)
{
lean_ctor_set(v___x_5825_, 27, v___x_5828_);
v___x_5830_ = v___x_5825_;
goto v_reusejp_5829_;
}
else
{
lean_object* v_reuseFailAlloc_5831_; 
v_reuseFailAlloc_5831_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5831_, 0, v_G_5788_);
lean_ctor_set(v_reuseFailAlloc_5831_, 1, v_y_5789_);
lean_ctor_set(v_reuseFailAlloc_5831_, 2, v_u_5790_);
lean_ctor_set(v_reuseFailAlloc_5831_, 3, v_Y_5791_);
lean_ctor_set(v_reuseFailAlloc_5831_, 4, v_D_5792_);
lean_ctor_set(v_reuseFailAlloc_5831_, 5, v_M_5793_);
lean_ctor_set(v_reuseFailAlloc_5831_, 6, v_L_5794_);
lean_ctor_set(v_reuseFailAlloc_5831_, 7, v_d_5795_);
lean_ctor_set(v_reuseFailAlloc_5831_, 8, v_Q_5796_);
lean_ctor_set(v_reuseFailAlloc_5831_, 9, v_q_5797_);
lean_ctor_set(v_reuseFailAlloc_5831_, 10, v_w_5798_);
lean_ctor_set(v_reuseFailAlloc_5831_, 11, v_W_5799_);
lean_ctor_set(v_reuseFailAlloc_5831_, 12, v_E_5800_);
lean_ctor_set(v_reuseFailAlloc_5831_, 13, v_e_5801_);
lean_ctor_set(v_reuseFailAlloc_5831_, 14, v_c_5802_);
lean_ctor_set(v_reuseFailAlloc_5831_, 15, v_F_5803_);
lean_ctor_set(v_reuseFailAlloc_5831_, 16, v_a_5804_);
lean_ctor_set(v_reuseFailAlloc_5831_, 17, v_b_5805_);
lean_ctor_set(v_reuseFailAlloc_5831_, 18, v_B_5806_);
lean_ctor_set(v_reuseFailAlloc_5831_, 19, v_h_5807_);
lean_ctor_set(v_reuseFailAlloc_5831_, 20, v_K_5808_);
lean_ctor_set(v_reuseFailAlloc_5831_, 21, v_k_5809_);
lean_ctor_set(v_reuseFailAlloc_5831_, 22, v_H_5810_);
lean_ctor_set(v_reuseFailAlloc_5831_, 23, v_m_5811_);
lean_ctor_set(v_reuseFailAlloc_5831_, 24, v_s_5812_);
lean_ctor_set(v_reuseFailAlloc_5831_, 25, v_S_5813_);
lean_ctor_set(v_reuseFailAlloc_5831_, 26, v_A_5814_);
lean_ctor_set(v_reuseFailAlloc_5831_, 27, v___x_5828_);
lean_ctor_set(v_reuseFailAlloc_5831_, 28, v_N_5815_);
lean_ctor_set(v_reuseFailAlloc_5831_, 29, v_V_5816_);
lean_ctor_set(v_reuseFailAlloc_5831_, 30, v_z_5817_);
lean_ctor_set(v_reuseFailAlloc_5831_, 31, v_zabbrev_5818_);
lean_ctor_set(v_reuseFailAlloc_5831_, 32, v_v_5819_);
lean_ctor_set(v_reuseFailAlloc_5831_, 33, v_O_5820_);
lean_ctor_set(v_reuseFailAlloc_5831_, 34, v_X_5821_);
lean_ctor_set(v_reuseFailAlloc_5831_, 35, v_x_5822_);
lean_ctor_set(v_reuseFailAlloc_5831_, 36, v_Z_5823_);
v___x_5830_ = v_reuseFailAlloc_5831_;
goto v_reusejp_5829_;
}
v_reusejp_5829_:
{
return v___x_5830_;
}
}
}
}
}
case 28:
{
lean_object* v___x_5838_; uint8_t v_isShared_5839_; uint8_t v_isSharedCheck_5887_; 
v_isSharedCheck_5887_ = !lean_is_exclusive(v_modifier_4414_);
if (v_isSharedCheck_5887_ == 0)
{
lean_object* v_unused_5888_; 
v_unused_5888_ = lean_ctor_get(v_modifier_4414_, 0);
lean_dec(v_unused_5888_);
v___x_5838_ = v_modifier_4414_;
v_isShared_5839_ = v_isSharedCheck_5887_;
goto v_resetjp_5837_;
}
else
{
lean_dec(v_modifier_4414_);
v___x_5838_ = lean_box(0);
v_isShared_5839_ = v_isSharedCheck_5887_;
goto v_resetjp_5837_;
}
v_resetjp_5837_:
{
lean_object* v_G_5840_; lean_object* v_y_5841_; lean_object* v_u_5842_; lean_object* v_Y_5843_; lean_object* v_D_5844_; lean_object* v_M_5845_; lean_object* v_L_5846_; lean_object* v_d_5847_; lean_object* v_Q_5848_; lean_object* v_q_5849_; lean_object* v_w_5850_; lean_object* v_W_5851_; lean_object* v_E_5852_; lean_object* v_e_5853_; lean_object* v_c_5854_; lean_object* v_F_5855_; lean_object* v_a_5856_; lean_object* v_b_5857_; lean_object* v_B_5858_; lean_object* v_h_5859_; lean_object* v_K_5860_; lean_object* v_k_5861_; lean_object* v_H_5862_; lean_object* v_m_5863_; lean_object* v_s_5864_; lean_object* v_S_5865_; lean_object* v_A_5866_; lean_object* v_n_5867_; lean_object* v_V_5868_; lean_object* v_z_5869_; lean_object* v_zabbrev_5870_; lean_object* v_v_5871_; lean_object* v_O_5872_; lean_object* v_X_5873_; lean_object* v_x_5874_; lean_object* v_Z_5875_; lean_object* v___x_5877_; uint8_t v_isShared_5878_; uint8_t v_isSharedCheck_5885_; 
v_G_5840_ = lean_ctor_get(v_date_4413_, 0);
v_y_5841_ = lean_ctor_get(v_date_4413_, 1);
v_u_5842_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5843_ = lean_ctor_get(v_date_4413_, 3);
v_D_5844_ = lean_ctor_get(v_date_4413_, 4);
v_M_5845_ = lean_ctor_get(v_date_4413_, 5);
v_L_5846_ = lean_ctor_get(v_date_4413_, 6);
v_d_5847_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5848_ = lean_ctor_get(v_date_4413_, 8);
v_q_5849_ = lean_ctor_get(v_date_4413_, 9);
v_w_5850_ = lean_ctor_get(v_date_4413_, 10);
v_W_5851_ = lean_ctor_get(v_date_4413_, 11);
v_E_5852_ = lean_ctor_get(v_date_4413_, 12);
v_e_5853_ = lean_ctor_get(v_date_4413_, 13);
v_c_5854_ = lean_ctor_get(v_date_4413_, 14);
v_F_5855_ = lean_ctor_get(v_date_4413_, 15);
v_a_5856_ = lean_ctor_get(v_date_4413_, 16);
v_b_5857_ = lean_ctor_get(v_date_4413_, 17);
v_B_5858_ = lean_ctor_get(v_date_4413_, 18);
v_h_5859_ = lean_ctor_get(v_date_4413_, 19);
v_K_5860_ = lean_ctor_get(v_date_4413_, 20);
v_k_5861_ = lean_ctor_get(v_date_4413_, 21);
v_H_5862_ = lean_ctor_get(v_date_4413_, 22);
v_m_5863_ = lean_ctor_get(v_date_4413_, 23);
v_s_5864_ = lean_ctor_get(v_date_4413_, 24);
v_S_5865_ = lean_ctor_get(v_date_4413_, 25);
v_A_5866_ = lean_ctor_get(v_date_4413_, 26);
v_n_5867_ = lean_ctor_get(v_date_4413_, 27);
v_V_5868_ = lean_ctor_get(v_date_4413_, 29);
v_z_5869_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_5870_ = lean_ctor_get(v_date_4413_, 31);
v_v_5871_ = lean_ctor_get(v_date_4413_, 32);
v_O_5872_ = lean_ctor_get(v_date_4413_, 33);
v_X_5873_ = lean_ctor_get(v_date_4413_, 34);
v_x_5874_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5875_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5885_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5885_ == 0)
{
lean_object* v_unused_5886_; 
v_unused_5886_ = lean_ctor_get(v_date_4413_, 28);
lean_dec(v_unused_5886_);
v___x_5877_ = v_date_4413_;
v_isShared_5878_ = v_isSharedCheck_5885_;
goto v_resetjp_5876_;
}
else
{
lean_inc(v_Z_5875_);
lean_inc(v_x_5874_);
lean_inc(v_X_5873_);
lean_inc(v_O_5872_);
lean_inc(v_v_5871_);
lean_inc(v_zabbrev_5870_);
lean_inc(v_z_5869_);
lean_inc(v_V_5868_);
lean_inc(v_n_5867_);
lean_inc(v_A_5866_);
lean_inc(v_S_5865_);
lean_inc(v_s_5864_);
lean_inc(v_m_5863_);
lean_inc(v_H_5862_);
lean_inc(v_k_5861_);
lean_inc(v_K_5860_);
lean_inc(v_h_5859_);
lean_inc(v_B_5858_);
lean_inc(v_b_5857_);
lean_inc(v_a_5856_);
lean_inc(v_F_5855_);
lean_inc(v_c_5854_);
lean_inc(v_e_5853_);
lean_inc(v_E_5852_);
lean_inc(v_W_5851_);
lean_inc(v_w_5850_);
lean_inc(v_q_5849_);
lean_inc(v_Q_5848_);
lean_inc(v_d_5847_);
lean_inc(v_L_5846_);
lean_inc(v_M_5845_);
lean_inc(v_D_5844_);
lean_inc(v_Y_5843_);
lean_inc(v_u_5842_);
lean_inc(v_y_5841_);
lean_inc(v_G_5840_);
lean_dec(v_date_4413_);
v___x_5877_ = lean_box(0);
v_isShared_5878_ = v_isSharedCheck_5885_;
goto v_resetjp_5876_;
}
v_resetjp_5876_:
{
lean_object* v___x_5880_; 
if (v_isShared_5839_ == 0)
{
lean_ctor_set_tag(v___x_5838_, 1);
lean_ctor_set(v___x_5838_, 0, v_data_4415_);
v___x_5880_ = v___x_5838_;
goto v_reusejp_5879_;
}
else
{
lean_object* v_reuseFailAlloc_5884_; 
v_reuseFailAlloc_5884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5884_, 0, v_data_4415_);
v___x_5880_ = v_reuseFailAlloc_5884_;
goto v_reusejp_5879_;
}
v_reusejp_5879_:
{
lean_object* v___x_5882_; 
if (v_isShared_5878_ == 0)
{
lean_ctor_set(v___x_5877_, 28, v___x_5880_);
v___x_5882_ = v___x_5877_;
goto v_reusejp_5881_;
}
else
{
lean_object* v_reuseFailAlloc_5883_; 
v_reuseFailAlloc_5883_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5883_, 0, v_G_5840_);
lean_ctor_set(v_reuseFailAlloc_5883_, 1, v_y_5841_);
lean_ctor_set(v_reuseFailAlloc_5883_, 2, v_u_5842_);
lean_ctor_set(v_reuseFailAlloc_5883_, 3, v_Y_5843_);
lean_ctor_set(v_reuseFailAlloc_5883_, 4, v_D_5844_);
lean_ctor_set(v_reuseFailAlloc_5883_, 5, v_M_5845_);
lean_ctor_set(v_reuseFailAlloc_5883_, 6, v_L_5846_);
lean_ctor_set(v_reuseFailAlloc_5883_, 7, v_d_5847_);
lean_ctor_set(v_reuseFailAlloc_5883_, 8, v_Q_5848_);
lean_ctor_set(v_reuseFailAlloc_5883_, 9, v_q_5849_);
lean_ctor_set(v_reuseFailAlloc_5883_, 10, v_w_5850_);
lean_ctor_set(v_reuseFailAlloc_5883_, 11, v_W_5851_);
lean_ctor_set(v_reuseFailAlloc_5883_, 12, v_E_5852_);
lean_ctor_set(v_reuseFailAlloc_5883_, 13, v_e_5853_);
lean_ctor_set(v_reuseFailAlloc_5883_, 14, v_c_5854_);
lean_ctor_set(v_reuseFailAlloc_5883_, 15, v_F_5855_);
lean_ctor_set(v_reuseFailAlloc_5883_, 16, v_a_5856_);
lean_ctor_set(v_reuseFailAlloc_5883_, 17, v_b_5857_);
lean_ctor_set(v_reuseFailAlloc_5883_, 18, v_B_5858_);
lean_ctor_set(v_reuseFailAlloc_5883_, 19, v_h_5859_);
lean_ctor_set(v_reuseFailAlloc_5883_, 20, v_K_5860_);
lean_ctor_set(v_reuseFailAlloc_5883_, 21, v_k_5861_);
lean_ctor_set(v_reuseFailAlloc_5883_, 22, v_H_5862_);
lean_ctor_set(v_reuseFailAlloc_5883_, 23, v_m_5863_);
lean_ctor_set(v_reuseFailAlloc_5883_, 24, v_s_5864_);
lean_ctor_set(v_reuseFailAlloc_5883_, 25, v_S_5865_);
lean_ctor_set(v_reuseFailAlloc_5883_, 26, v_A_5866_);
lean_ctor_set(v_reuseFailAlloc_5883_, 27, v_n_5867_);
lean_ctor_set(v_reuseFailAlloc_5883_, 28, v___x_5880_);
lean_ctor_set(v_reuseFailAlloc_5883_, 29, v_V_5868_);
lean_ctor_set(v_reuseFailAlloc_5883_, 30, v_z_5869_);
lean_ctor_set(v_reuseFailAlloc_5883_, 31, v_zabbrev_5870_);
lean_ctor_set(v_reuseFailAlloc_5883_, 32, v_v_5871_);
lean_ctor_set(v_reuseFailAlloc_5883_, 33, v_O_5872_);
lean_ctor_set(v_reuseFailAlloc_5883_, 34, v_X_5873_);
lean_ctor_set(v_reuseFailAlloc_5883_, 35, v_x_5874_);
lean_ctor_set(v_reuseFailAlloc_5883_, 36, v_Z_5875_);
v___x_5882_ = v_reuseFailAlloc_5883_;
goto v_reusejp_5881_;
}
v_reusejp_5881_:
{
return v___x_5882_;
}
}
}
}
}
case 29:
{
lean_object* v_G_5889_; lean_object* v_y_5890_; lean_object* v_u_5891_; lean_object* v_Y_5892_; lean_object* v_D_5893_; lean_object* v_M_5894_; lean_object* v_L_5895_; lean_object* v_d_5896_; lean_object* v_Q_5897_; lean_object* v_q_5898_; lean_object* v_w_5899_; lean_object* v_W_5900_; lean_object* v_E_5901_; lean_object* v_e_5902_; lean_object* v_c_5903_; lean_object* v_F_5904_; lean_object* v_a_5905_; lean_object* v_b_5906_; lean_object* v_B_5907_; lean_object* v_h_5908_; lean_object* v_K_5909_; lean_object* v_k_5910_; lean_object* v_H_5911_; lean_object* v_m_5912_; lean_object* v_s_5913_; lean_object* v_S_5914_; lean_object* v_A_5915_; lean_object* v_n_5916_; lean_object* v_N_5917_; lean_object* v_z_5918_; lean_object* v_zabbrev_5919_; lean_object* v_v_5920_; lean_object* v_O_5921_; lean_object* v_X_5922_; lean_object* v_x_5923_; lean_object* v_Z_5924_; lean_object* v___x_5926_; uint8_t v_isShared_5927_; uint8_t v_isSharedCheck_5932_; 
lean_dec_ref_known(v_modifier_4414_, 0);
v_G_5889_ = lean_ctor_get(v_date_4413_, 0);
v_y_5890_ = lean_ctor_get(v_date_4413_, 1);
v_u_5891_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5892_ = lean_ctor_get(v_date_4413_, 3);
v_D_5893_ = lean_ctor_get(v_date_4413_, 4);
v_M_5894_ = lean_ctor_get(v_date_4413_, 5);
v_L_5895_ = lean_ctor_get(v_date_4413_, 6);
v_d_5896_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5897_ = lean_ctor_get(v_date_4413_, 8);
v_q_5898_ = lean_ctor_get(v_date_4413_, 9);
v_w_5899_ = lean_ctor_get(v_date_4413_, 10);
v_W_5900_ = lean_ctor_get(v_date_4413_, 11);
v_E_5901_ = lean_ctor_get(v_date_4413_, 12);
v_e_5902_ = lean_ctor_get(v_date_4413_, 13);
v_c_5903_ = lean_ctor_get(v_date_4413_, 14);
v_F_5904_ = lean_ctor_get(v_date_4413_, 15);
v_a_5905_ = lean_ctor_get(v_date_4413_, 16);
v_b_5906_ = lean_ctor_get(v_date_4413_, 17);
v_B_5907_ = lean_ctor_get(v_date_4413_, 18);
v_h_5908_ = lean_ctor_get(v_date_4413_, 19);
v_K_5909_ = lean_ctor_get(v_date_4413_, 20);
v_k_5910_ = lean_ctor_get(v_date_4413_, 21);
v_H_5911_ = lean_ctor_get(v_date_4413_, 22);
v_m_5912_ = lean_ctor_get(v_date_4413_, 23);
v_s_5913_ = lean_ctor_get(v_date_4413_, 24);
v_S_5914_ = lean_ctor_get(v_date_4413_, 25);
v_A_5915_ = lean_ctor_get(v_date_4413_, 26);
v_n_5916_ = lean_ctor_get(v_date_4413_, 27);
v_N_5917_ = lean_ctor_get(v_date_4413_, 28);
v_z_5918_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_5919_ = lean_ctor_get(v_date_4413_, 31);
v_v_5920_ = lean_ctor_get(v_date_4413_, 32);
v_O_5921_ = lean_ctor_get(v_date_4413_, 33);
v_X_5922_ = lean_ctor_get(v_date_4413_, 34);
v_x_5923_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5924_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5932_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5932_ == 0)
{
lean_object* v_unused_5933_; 
v_unused_5933_ = lean_ctor_get(v_date_4413_, 29);
lean_dec(v_unused_5933_);
v___x_5926_ = v_date_4413_;
v_isShared_5927_ = v_isSharedCheck_5932_;
goto v_resetjp_5925_;
}
else
{
lean_inc(v_Z_5924_);
lean_inc(v_x_5923_);
lean_inc(v_X_5922_);
lean_inc(v_O_5921_);
lean_inc(v_v_5920_);
lean_inc(v_zabbrev_5919_);
lean_inc(v_z_5918_);
lean_inc(v_N_5917_);
lean_inc(v_n_5916_);
lean_inc(v_A_5915_);
lean_inc(v_S_5914_);
lean_inc(v_s_5913_);
lean_inc(v_m_5912_);
lean_inc(v_H_5911_);
lean_inc(v_k_5910_);
lean_inc(v_K_5909_);
lean_inc(v_h_5908_);
lean_inc(v_B_5907_);
lean_inc(v_b_5906_);
lean_inc(v_a_5905_);
lean_inc(v_F_5904_);
lean_inc(v_c_5903_);
lean_inc(v_e_5902_);
lean_inc(v_E_5901_);
lean_inc(v_W_5900_);
lean_inc(v_w_5899_);
lean_inc(v_q_5898_);
lean_inc(v_Q_5897_);
lean_inc(v_d_5896_);
lean_inc(v_L_5895_);
lean_inc(v_M_5894_);
lean_inc(v_D_5893_);
lean_inc(v_Y_5892_);
lean_inc(v_u_5891_);
lean_inc(v_y_5890_);
lean_inc(v_G_5889_);
lean_dec(v_date_4413_);
v___x_5926_ = lean_box(0);
v_isShared_5927_ = v_isSharedCheck_5932_;
goto v_resetjp_5925_;
}
v_resetjp_5925_:
{
lean_object* v___x_5928_; lean_object* v___x_5930_; 
v___x_5928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5928_, 0, v_data_4415_);
if (v_isShared_5927_ == 0)
{
lean_ctor_set(v___x_5926_, 29, v___x_5928_);
v___x_5930_ = v___x_5926_;
goto v_reusejp_5929_;
}
else
{
lean_object* v_reuseFailAlloc_5931_; 
v_reuseFailAlloc_5931_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5931_, 0, v_G_5889_);
lean_ctor_set(v_reuseFailAlloc_5931_, 1, v_y_5890_);
lean_ctor_set(v_reuseFailAlloc_5931_, 2, v_u_5891_);
lean_ctor_set(v_reuseFailAlloc_5931_, 3, v_Y_5892_);
lean_ctor_set(v_reuseFailAlloc_5931_, 4, v_D_5893_);
lean_ctor_set(v_reuseFailAlloc_5931_, 5, v_M_5894_);
lean_ctor_set(v_reuseFailAlloc_5931_, 6, v_L_5895_);
lean_ctor_set(v_reuseFailAlloc_5931_, 7, v_d_5896_);
lean_ctor_set(v_reuseFailAlloc_5931_, 8, v_Q_5897_);
lean_ctor_set(v_reuseFailAlloc_5931_, 9, v_q_5898_);
lean_ctor_set(v_reuseFailAlloc_5931_, 10, v_w_5899_);
lean_ctor_set(v_reuseFailAlloc_5931_, 11, v_W_5900_);
lean_ctor_set(v_reuseFailAlloc_5931_, 12, v_E_5901_);
lean_ctor_set(v_reuseFailAlloc_5931_, 13, v_e_5902_);
lean_ctor_set(v_reuseFailAlloc_5931_, 14, v_c_5903_);
lean_ctor_set(v_reuseFailAlloc_5931_, 15, v_F_5904_);
lean_ctor_set(v_reuseFailAlloc_5931_, 16, v_a_5905_);
lean_ctor_set(v_reuseFailAlloc_5931_, 17, v_b_5906_);
lean_ctor_set(v_reuseFailAlloc_5931_, 18, v_B_5907_);
lean_ctor_set(v_reuseFailAlloc_5931_, 19, v_h_5908_);
lean_ctor_set(v_reuseFailAlloc_5931_, 20, v_K_5909_);
lean_ctor_set(v_reuseFailAlloc_5931_, 21, v_k_5910_);
lean_ctor_set(v_reuseFailAlloc_5931_, 22, v_H_5911_);
lean_ctor_set(v_reuseFailAlloc_5931_, 23, v_m_5912_);
lean_ctor_set(v_reuseFailAlloc_5931_, 24, v_s_5913_);
lean_ctor_set(v_reuseFailAlloc_5931_, 25, v_S_5914_);
lean_ctor_set(v_reuseFailAlloc_5931_, 26, v_A_5915_);
lean_ctor_set(v_reuseFailAlloc_5931_, 27, v_n_5916_);
lean_ctor_set(v_reuseFailAlloc_5931_, 28, v_N_5917_);
lean_ctor_set(v_reuseFailAlloc_5931_, 29, v___x_5928_);
lean_ctor_set(v_reuseFailAlloc_5931_, 30, v_z_5918_);
lean_ctor_set(v_reuseFailAlloc_5931_, 31, v_zabbrev_5919_);
lean_ctor_set(v_reuseFailAlloc_5931_, 32, v_v_5920_);
lean_ctor_set(v_reuseFailAlloc_5931_, 33, v_O_5921_);
lean_ctor_set(v_reuseFailAlloc_5931_, 34, v_X_5922_);
lean_ctor_set(v_reuseFailAlloc_5931_, 35, v_x_5923_);
lean_ctor_set(v_reuseFailAlloc_5931_, 36, v_Z_5924_);
v___x_5930_ = v_reuseFailAlloc_5931_;
goto v_reusejp_5929_;
}
v_reusejp_5929_:
{
return v___x_5930_;
}
}
}
case 30:
{
uint8_t v_presentation_5934_; 
v_presentation_5934_ = lean_ctor_get_uint8(v_modifier_4414_, 0);
lean_dec_ref_known(v_modifier_4414_, 0);
if (v_presentation_5934_ == 0)
{
lean_object* v_G_5935_; lean_object* v_y_5936_; lean_object* v_u_5937_; lean_object* v_Y_5938_; lean_object* v_D_5939_; lean_object* v_M_5940_; lean_object* v_L_5941_; lean_object* v_d_5942_; lean_object* v_Q_5943_; lean_object* v_q_5944_; lean_object* v_w_5945_; lean_object* v_W_5946_; lean_object* v_E_5947_; lean_object* v_e_5948_; lean_object* v_c_5949_; lean_object* v_F_5950_; lean_object* v_a_5951_; lean_object* v_b_5952_; lean_object* v_B_5953_; lean_object* v_h_5954_; lean_object* v_K_5955_; lean_object* v_k_5956_; lean_object* v_H_5957_; lean_object* v_m_5958_; lean_object* v_s_5959_; lean_object* v_S_5960_; lean_object* v_A_5961_; lean_object* v_n_5962_; lean_object* v_N_5963_; lean_object* v_V_5964_; lean_object* v_z_5965_; lean_object* v_v_5966_; lean_object* v_O_5967_; lean_object* v_X_5968_; lean_object* v_x_5969_; lean_object* v_Z_5970_; lean_object* v___x_5972_; uint8_t v_isShared_5973_; uint8_t v_isSharedCheck_5978_; 
v_G_5935_ = lean_ctor_get(v_date_4413_, 0);
v_y_5936_ = lean_ctor_get(v_date_4413_, 1);
v_u_5937_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5938_ = lean_ctor_get(v_date_4413_, 3);
v_D_5939_ = lean_ctor_get(v_date_4413_, 4);
v_M_5940_ = lean_ctor_get(v_date_4413_, 5);
v_L_5941_ = lean_ctor_get(v_date_4413_, 6);
v_d_5942_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5943_ = lean_ctor_get(v_date_4413_, 8);
v_q_5944_ = lean_ctor_get(v_date_4413_, 9);
v_w_5945_ = lean_ctor_get(v_date_4413_, 10);
v_W_5946_ = lean_ctor_get(v_date_4413_, 11);
v_E_5947_ = lean_ctor_get(v_date_4413_, 12);
v_e_5948_ = lean_ctor_get(v_date_4413_, 13);
v_c_5949_ = lean_ctor_get(v_date_4413_, 14);
v_F_5950_ = lean_ctor_get(v_date_4413_, 15);
v_a_5951_ = lean_ctor_get(v_date_4413_, 16);
v_b_5952_ = lean_ctor_get(v_date_4413_, 17);
v_B_5953_ = lean_ctor_get(v_date_4413_, 18);
v_h_5954_ = lean_ctor_get(v_date_4413_, 19);
v_K_5955_ = lean_ctor_get(v_date_4413_, 20);
v_k_5956_ = lean_ctor_get(v_date_4413_, 21);
v_H_5957_ = lean_ctor_get(v_date_4413_, 22);
v_m_5958_ = lean_ctor_get(v_date_4413_, 23);
v_s_5959_ = lean_ctor_get(v_date_4413_, 24);
v_S_5960_ = lean_ctor_get(v_date_4413_, 25);
v_A_5961_ = lean_ctor_get(v_date_4413_, 26);
v_n_5962_ = lean_ctor_get(v_date_4413_, 27);
v_N_5963_ = lean_ctor_get(v_date_4413_, 28);
v_V_5964_ = lean_ctor_get(v_date_4413_, 29);
v_z_5965_ = lean_ctor_get(v_date_4413_, 30);
v_v_5966_ = lean_ctor_get(v_date_4413_, 32);
v_O_5967_ = lean_ctor_get(v_date_4413_, 33);
v_X_5968_ = lean_ctor_get(v_date_4413_, 34);
v_x_5969_ = lean_ctor_get(v_date_4413_, 35);
v_Z_5970_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_5978_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_5978_ == 0)
{
lean_object* v_unused_5979_; 
v_unused_5979_ = lean_ctor_get(v_date_4413_, 31);
lean_dec(v_unused_5979_);
v___x_5972_ = v_date_4413_;
v_isShared_5973_ = v_isSharedCheck_5978_;
goto v_resetjp_5971_;
}
else
{
lean_inc(v_Z_5970_);
lean_inc(v_x_5969_);
lean_inc(v_X_5968_);
lean_inc(v_O_5967_);
lean_inc(v_v_5966_);
lean_inc(v_z_5965_);
lean_inc(v_V_5964_);
lean_inc(v_N_5963_);
lean_inc(v_n_5962_);
lean_inc(v_A_5961_);
lean_inc(v_S_5960_);
lean_inc(v_s_5959_);
lean_inc(v_m_5958_);
lean_inc(v_H_5957_);
lean_inc(v_k_5956_);
lean_inc(v_K_5955_);
lean_inc(v_h_5954_);
lean_inc(v_B_5953_);
lean_inc(v_b_5952_);
lean_inc(v_a_5951_);
lean_inc(v_F_5950_);
lean_inc(v_c_5949_);
lean_inc(v_e_5948_);
lean_inc(v_E_5947_);
lean_inc(v_W_5946_);
lean_inc(v_w_5945_);
lean_inc(v_q_5944_);
lean_inc(v_Q_5943_);
lean_inc(v_d_5942_);
lean_inc(v_L_5941_);
lean_inc(v_M_5940_);
lean_inc(v_D_5939_);
lean_inc(v_Y_5938_);
lean_inc(v_u_5937_);
lean_inc(v_y_5936_);
lean_inc(v_G_5935_);
lean_dec(v_date_4413_);
v___x_5972_ = lean_box(0);
v_isShared_5973_ = v_isSharedCheck_5978_;
goto v_resetjp_5971_;
}
v_resetjp_5971_:
{
lean_object* v___x_5974_; lean_object* v___x_5976_; 
v___x_5974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5974_, 0, v_data_4415_);
if (v_isShared_5973_ == 0)
{
lean_ctor_set(v___x_5972_, 31, v___x_5974_);
v___x_5976_ = v___x_5972_;
goto v_reusejp_5975_;
}
else
{
lean_object* v_reuseFailAlloc_5977_; 
v_reuseFailAlloc_5977_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5977_, 0, v_G_5935_);
lean_ctor_set(v_reuseFailAlloc_5977_, 1, v_y_5936_);
lean_ctor_set(v_reuseFailAlloc_5977_, 2, v_u_5937_);
lean_ctor_set(v_reuseFailAlloc_5977_, 3, v_Y_5938_);
lean_ctor_set(v_reuseFailAlloc_5977_, 4, v_D_5939_);
lean_ctor_set(v_reuseFailAlloc_5977_, 5, v_M_5940_);
lean_ctor_set(v_reuseFailAlloc_5977_, 6, v_L_5941_);
lean_ctor_set(v_reuseFailAlloc_5977_, 7, v_d_5942_);
lean_ctor_set(v_reuseFailAlloc_5977_, 8, v_Q_5943_);
lean_ctor_set(v_reuseFailAlloc_5977_, 9, v_q_5944_);
lean_ctor_set(v_reuseFailAlloc_5977_, 10, v_w_5945_);
lean_ctor_set(v_reuseFailAlloc_5977_, 11, v_W_5946_);
lean_ctor_set(v_reuseFailAlloc_5977_, 12, v_E_5947_);
lean_ctor_set(v_reuseFailAlloc_5977_, 13, v_e_5948_);
lean_ctor_set(v_reuseFailAlloc_5977_, 14, v_c_5949_);
lean_ctor_set(v_reuseFailAlloc_5977_, 15, v_F_5950_);
lean_ctor_set(v_reuseFailAlloc_5977_, 16, v_a_5951_);
lean_ctor_set(v_reuseFailAlloc_5977_, 17, v_b_5952_);
lean_ctor_set(v_reuseFailAlloc_5977_, 18, v_B_5953_);
lean_ctor_set(v_reuseFailAlloc_5977_, 19, v_h_5954_);
lean_ctor_set(v_reuseFailAlloc_5977_, 20, v_K_5955_);
lean_ctor_set(v_reuseFailAlloc_5977_, 21, v_k_5956_);
lean_ctor_set(v_reuseFailAlloc_5977_, 22, v_H_5957_);
lean_ctor_set(v_reuseFailAlloc_5977_, 23, v_m_5958_);
lean_ctor_set(v_reuseFailAlloc_5977_, 24, v_s_5959_);
lean_ctor_set(v_reuseFailAlloc_5977_, 25, v_S_5960_);
lean_ctor_set(v_reuseFailAlloc_5977_, 26, v_A_5961_);
lean_ctor_set(v_reuseFailAlloc_5977_, 27, v_n_5962_);
lean_ctor_set(v_reuseFailAlloc_5977_, 28, v_N_5963_);
lean_ctor_set(v_reuseFailAlloc_5977_, 29, v_V_5964_);
lean_ctor_set(v_reuseFailAlloc_5977_, 30, v_z_5965_);
lean_ctor_set(v_reuseFailAlloc_5977_, 31, v___x_5974_);
lean_ctor_set(v_reuseFailAlloc_5977_, 32, v_v_5966_);
lean_ctor_set(v_reuseFailAlloc_5977_, 33, v_O_5967_);
lean_ctor_set(v_reuseFailAlloc_5977_, 34, v_X_5968_);
lean_ctor_set(v_reuseFailAlloc_5977_, 35, v_x_5969_);
lean_ctor_set(v_reuseFailAlloc_5977_, 36, v_Z_5970_);
v___x_5976_ = v_reuseFailAlloc_5977_;
goto v_reusejp_5975_;
}
v_reusejp_5975_:
{
return v___x_5976_;
}
}
}
else
{
lean_object* v_G_5980_; lean_object* v_y_5981_; lean_object* v_u_5982_; lean_object* v_Y_5983_; lean_object* v_D_5984_; lean_object* v_M_5985_; lean_object* v_L_5986_; lean_object* v_d_5987_; lean_object* v_Q_5988_; lean_object* v_q_5989_; lean_object* v_w_5990_; lean_object* v_W_5991_; lean_object* v_E_5992_; lean_object* v_e_5993_; lean_object* v_c_5994_; lean_object* v_F_5995_; lean_object* v_a_5996_; lean_object* v_b_5997_; lean_object* v_B_5998_; lean_object* v_h_5999_; lean_object* v_K_6000_; lean_object* v_k_6001_; lean_object* v_H_6002_; lean_object* v_m_6003_; lean_object* v_s_6004_; lean_object* v_S_6005_; lean_object* v_A_6006_; lean_object* v_n_6007_; lean_object* v_N_6008_; lean_object* v_V_6009_; lean_object* v_zabbrev_6010_; lean_object* v_v_6011_; lean_object* v_O_6012_; lean_object* v_X_6013_; lean_object* v_x_6014_; lean_object* v_Z_6015_; lean_object* v___x_6017_; uint8_t v_isShared_6018_; uint8_t v_isSharedCheck_6023_; 
v_G_5980_ = lean_ctor_get(v_date_4413_, 0);
v_y_5981_ = lean_ctor_get(v_date_4413_, 1);
v_u_5982_ = lean_ctor_get(v_date_4413_, 2);
v_Y_5983_ = lean_ctor_get(v_date_4413_, 3);
v_D_5984_ = lean_ctor_get(v_date_4413_, 4);
v_M_5985_ = lean_ctor_get(v_date_4413_, 5);
v_L_5986_ = lean_ctor_get(v_date_4413_, 6);
v_d_5987_ = lean_ctor_get(v_date_4413_, 7);
v_Q_5988_ = lean_ctor_get(v_date_4413_, 8);
v_q_5989_ = lean_ctor_get(v_date_4413_, 9);
v_w_5990_ = lean_ctor_get(v_date_4413_, 10);
v_W_5991_ = lean_ctor_get(v_date_4413_, 11);
v_E_5992_ = lean_ctor_get(v_date_4413_, 12);
v_e_5993_ = lean_ctor_get(v_date_4413_, 13);
v_c_5994_ = lean_ctor_get(v_date_4413_, 14);
v_F_5995_ = lean_ctor_get(v_date_4413_, 15);
v_a_5996_ = lean_ctor_get(v_date_4413_, 16);
v_b_5997_ = lean_ctor_get(v_date_4413_, 17);
v_B_5998_ = lean_ctor_get(v_date_4413_, 18);
v_h_5999_ = lean_ctor_get(v_date_4413_, 19);
v_K_6000_ = lean_ctor_get(v_date_4413_, 20);
v_k_6001_ = lean_ctor_get(v_date_4413_, 21);
v_H_6002_ = lean_ctor_get(v_date_4413_, 22);
v_m_6003_ = lean_ctor_get(v_date_4413_, 23);
v_s_6004_ = lean_ctor_get(v_date_4413_, 24);
v_S_6005_ = lean_ctor_get(v_date_4413_, 25);
v_A_6006_ = lean_ctor_get(v_date_4413_, 26);
v_n_6007_ = lean_ctor_get(v_date_4413_, 27);
v_N_6008_ = lean_ctor_get(v_date_4413_, 28);
v_V_6009_ = lean_ctor_get(v_date_4413_, 29);
v_zabbrev_6010_ = lean_ctor_get(v_date_4413_, 31);
v_v_6011_ = lean_ctor_get(v_date_4413_, 32);
v_O_6012_ = lean_ctor_get(v_date_4413_, 33);
v_X_6013_ = lean_ctor_get(v_date_4413_, 34);
v_x_6014_ = lean_ctor_get(v_date_4413_, 35);
v_Z_6015_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_6023_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_6023_ == 0)
{
lean_object* v_unused_6024_; 
v_unused_6024_ = lean_ctor_get(v_date_4413_, 30);
lean_dec(v_unused_6024_);
v___x_6017_ = v_date_4413_;
v_isShared_6018_ = v_isSharedCheck_6023_;
goto v_resetjp_6016_;
}
else
{
lean_inc(v_Z_6015_);
lean_inc(v_x_6014_);
lean_inc(v_X_6013_);
lean_inc(v_O_6012_);
lean_inc(v_v_6011_);
lean_inc(v_zabbrev_6010_);
lean_inc(v_V_6009_);
lean_inc(v_N_6008_);
lean_inc(v_n_6007_);
lean_inc(v_A_6006_);
lean_inc(v_S_6005_);
lean_inc(v_s_6004_);
lean_inc(v_m_6003_);
lean_inc(v_H_6002_);
lean_inc(v_k_6001_);
lean_inc(v_K_6000_);
lean_inc(v_h_5999_);
lean_inc(v_B_5998_);
lean_inc(v_b_5997_);
lean_inc(v_a_5996_);
lean_inc(v_F_5995_);
lean_inc(v_c_5994_);
lean_inc(v_e_5993_);
lean_inc(v_E_5992_);
lean_inc(v_W_5991_);
lean_inc(v_w_5990_);
lean_inc(v_q_5989_);
lean_inc(v_Q_5988_);
lean_inc(v_d_5987_);
lean_inc(v_L_5986_);
lean_inc(v_M_5985_);
lean_inc(v_D_5984_);
lean_inc(v_Y_5983_);
lean_inc(v_u_5982_);
lean_inc(v_y_5981_);
lean_inc(v_G_5980_);
lean_dec(v_date_4413_);
v___x_6017_ = lean_box(0);
v_isShared_6018_ = v_isSharedCheck_6023_;
goto v_resetjp_6016_;
}
v_resetjp_6016_:
{
lean_object* v___x_6019_; lean_object* v___x_6021_; 
v___x_6019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6019_, 0, v_data_4415_);
if (v_isShared_6018_ == 0)
{
lean_ctor_set(v___x_6017_, 30, v___x_6019_);
v___x_6021_ = v___x_6017_;
goto v_reusejp_6020_;
}
else
{
lean_object* v_reuseFailAlloc_6022_; 
v_reuseFailAlloc_6022_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6022_, 0, v_G_5980_);
lean_ctor_set(v_reuseFailAlloc_6022_, 1, v_y_5981_);
lean_ctor_set(v_reuseFailAlloc_6022_, 2, v_u_5982_);
lean_ctor_set(v_reuseFailAlloc_6022_, 3, v_Y_5983_);
lean_ctor_set(v_reuseFailAlloc_6022_, 4, v_D_5984_);
lean_ctor_set(v_reuseFailAlloc_6022_, 5, v_M_5985_);
lean_ctor_set(v_reuseFailAlloc_6022_, 6, v_L_5986_);
lean_ctor_set(v_reuseFailAlloc_6022_, 7, v_d_5987_);
lean_ctor_set(v_reuseFailAlloc_6022_, 8, v_Q_5988_);
lean_ctor_set(v_reuseFailAlloc_6022_, 9, v_q_5989_);
lean_ctor_set(v_reuseFailAlloc_6022_, 10, v_w_5990_);
lean_ctor_set(v_reuseFailAlloc_6022_, 11, v_W_5991_);
lean_ctor_set(v_reuseFailAlloc_6022_, 12, v_E_5992_);
lean_ctor_set(v_reuseFailAlloc_6022_, 13, v_e_5993_);
lean_ctor_set(v_reuseFailAlloc_6022_, 14, v_c_5994_);
lean_ctor_set(v_reuseFailAlloc_6022_, 15, v_F_5995_);
lean_ctor_set(v_reuseFailAlloc_6022_, 16, v_a_5996_);
lean_ctor_set(v_reuseFailAlloc_6022_, 17, v_b_5997_);
lean_ctor_set(v_reuseFailAlloc_6022_, 18, v_B_5998_);
lean_ctor_set(v_reuseFailAlloc_6022_, 19, v_h_5999_);
lean_ctor_set(v_reuseFailAlloc_6022_, 20, v_K_6000_);
lean_ctor_set(v_reuseFailAlloc_6022_, 21, v_k_6001_);
lean_ctor_set(v_reuseFailAlloc_6022_, 22, v_H_6002_);
lean_ctor_set(v_reuseFailAlloc_6022_, 23, v_m_6003_);
lean_ctor_set(v_reuseFailAlloc_6022_, 24, v_s_6004_);
lean_ctor_set(v_reuseFailAlloc_6022_, 25, v_S_6005_);
lean_ctor_set(v_reuseFailAlloc_6022_, 26, v_A_6006_);
lean_ctor_set(v_reuseFailAlloc_6022_, 27, v_n_6007_);
lean_ctor_set(v_reuseFailAlloc_6022_, 28, v_N_6008_);
lean_ctor_set(v_reuseFailAlloc_6022_, 29, v_V_6009_);
lean_ctor_set(v_reuseFailAlloc_6022_, 30, v___x_6019_);
lean_ctor_set(v_reuseFailAlloc_6022_, 31, v_zabbrev_6010_);
lean_ctor_set(v_reuseFailAlloc_6022_, 32, v_v_6011_);
lean_ctor_set(v_reuseFailAlloc_6022_, 33, v_O_6012_);
lean_ctor_set(v_reuseFailAlloc_6022_, 34, v_X_6013_);
lean_ctor_set(v_reuseFailAlloc_6022_, 35, v_x_6014_);
lean_ctor_set(v_reuseFailAlloc_6022_, 36, v_Z_6015_);
v___x_6021_ = v_reuseFailAlloc_6022_;
goto v_reusejp_6020_;
}
v_reusejp_6020_:
{
return v___x_6021_;
}
}
}
}
case 31:
{
lean_object* v_G_6025_; lean_object* v_y_6026_; lean_object* v_u_6027_; lean_object* v_Y_6028_; lean_object* v_D_6029_; lean_object* v_M_6030_; lean_object* v_L_6031_; lean_object* v_d_6032_; lean_object* v_Q_6033_; lean_object* v_q_6034_; lean_object* v_w_6035_; lean_object* v_W_6036_; lean_object* v_E_6037_; lean_object* v_e_6038_; lean_object* v_c_6039_; lean_object* v_F_6040_; lean_object* v_a_6041_; lean_object* v_b_6042_; lean_object* v_B_6043_; lean_object* v_h_6044_; lean_object* v_K_6045_; lean_object* v_k_6046_; lean_object* v_H_6047_; lean_object* v_m_6048_; lean_object* v_s_6049_; lean_object* v_S_6050_; lean_object* v_A_6051_; lean_object* v_n_6052_; lean_object* v_N_6053_; lean_object* v_V_6054_; lean_object* v_z_6055_; lean_object* v_zabbrev_6056_; lean_object* v_O_6057_; lean_object* v_X_6058_; lean_object* v_x_6059_; lean_object* v_Z_6060_; lean_object* v___x_6062_; uint8_t v_isShared_6063_; uint8_t v_isSharedCheck_6068_; 
lean_dec_ref_known(v_modifier_4414_, 0);
v_G_6025_ = lean_ctor_get(v_date_4413_, 0);
v_y_6026_ = lean_ctor_get(v_date_4413_, 1);
v_u_6027_ = lean_ctor_get(v_date_4413_, 2);
v_Y_6028_ = lean_ctor_get(v_date_4413_, 3);
v_D_6029_ = lean_ctor_get(v_date_4413_, 4);
v_M_6030_ = lean_ctor_get(v_date_4413_, 5);
v_L_6031_ = lean_ctor_get(v_date_4413_, 6);
v_d_6032_ = lean_ctor_get(v_date_4413_, 7);
v_Q_6033_ = lean_ctor_get(v_date_4413_, 8);
v_q_6034_ = lean_ctor_get(v_date_4413_, 9);
v_w_6035_ = lean_ctor_get(v_date_4413_, 10);
v_W_6036_ = lean_ctor_get(v_date_4413_, 11);
v_E_6037_ = lean_ctor_get(v_date_4413_, 12);
v_e_6038_ = lean_ctor_get(v_date_4413_, 13);
v_c_6039_ = lean_ctor_get(v_date_4413_, 14);
v_F_6040_ = lean_ctor_get(v_date_4413_, 15);
v_a_6041_ = lean_ctor_get(v_date_4413_, 16);
v_b_6042_ = lean_ctor_get(v_date_4413_, 17);
v_B_6043_ = lean_ctor_get(v_date_4413_, 18);
v_h_6044_ = lean_ctor_get(v_date_4413_, 19);
v_K_6045_ = lean_ctor_get(v_date_4413_, 20);
v_k_6046_ = lean_ctor_get(v_date_4413_, 21);
v_H_6047_ = lean_ctor_get(v_date_4413_, 22);
v_m_6048_ = lean_ctor_get(v_date_4413_, 23);
v_s_6049_ = lean_ctor_get(v_date_4413_, 24);
v_S_6050_ = lean_ctor_get(v_date_4413_, 25);
v_A_6051_ = lean_ctor_get(v_date_4413_, 26);
v_n_6052_ = lean_ctor_get(v_date_4413_, 27);
v_N_6053_ = lean_ctor_get(v_date_4413_, 28);
v_V_6054_ = lean_ctor_get(v_date_4413_, 29);
v_z_6055_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_6056_ = lean_ctor_get(v_date_4413_, 31);
v_O_6057_ = lean_ctor_get(v_date_4413_, 33);
v_X_6058_ = lean_ctor_get(v_date_4413_, 34);
v_x_6059_ = lean_ctor_get(v_date_4413_, 35);
v_Z_6060_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_6068_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_6068_ == 0)
{
lean_object* v_unused_6069_; 
v_unused_6069_ = lean_ctor_get(v_date_4413_, 32);
lean_dec(v_unused_6069_);
v___x_6062_ = v_date_4413_;
v_isShared_6063_ = v_isSharedCheck_6068_;
goto v_resetjp_6061_;
}
else
{
lean_inc(v_Z_6060_);
lean_inc(v_x_6059_);
lean_inc(v_X_6058_);
lean_inc(v_O_6057_);
lean_inc(v_zabbrev_6056_);
lean_inc(v_z_6055_);
lean_inc(v_V_6054_);
lean_inc(v_N_6053_);
lean_inc(v_n_6052_);
lean_inc(v_A_6051_);
lean_inc(v_S_6050_);
lean_inc(v_s_6049_);
lean_inc(v_m_6048_);
lean_inc(v_H_6047_);
lean_inc(v_k_6046_);
lean_inc(v_K_6045_);
lean_inc(v_h_6044_);
lean_inc(v_B_6043_);
lean_inc(v_b_6042_);
lean_inc(v_a_6041_);
lean_inc(v_F_6040_);
lean_inc(v_c_6039_);
lean_inc(v_e_6038_);
lean_inc(v_E_6037_);
lean_inc(v_W_6036_);
lean_inc(v_w_6035_);
lean_inc(v_q_6034_);
lean_inc(v_Q_6033_);
lean_inc(v_d_6032_);
lean_inc(v_L_6031_);
lean_inc(v_M_6030_);
lean_inc(v_D_6029_);
lean_inc(v_Y_6028_);
lean_inc(v_u_6027_);
lean_inc(v_y_6026_);
lean_inc(v_G_6025_);
lean_dec(v_date_4413_);
v___x_6062_ = lean_box(0);
v_isShared_6063_ = v_isSharedCheck_6068_;
goto v_resetjp_6061_;
}
v_resetjp_6061_:
{
lean_object* v___x_6064_; lean_object* v___x_6066_; 
v___x_6064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6064_, 0, v_data_4415_);
if (v_isShared_6063_ == 0)
{
lean_ctor_set(v___x_6062_, 32, v___x_6064_);
v___x_6066_ = v___x_6062_;
goto v_reusejp_6065_;
}
else
{
lean_object* v_reuseFailAlloc_6067_; 
v_reuseFailAlloc_6067_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6067_, 0, v_G_6025_);
lean_ctor_set(v_reuseFailAlloc_6067_, 1, v_y_6026_);
lean_ctor_set(v_reuseFailAlloc_6067_, 2, v_u_6027_);
lean_ctor_set(v_reuseFailAlloc_6067_, 3, v_Y_6028_);
lean_ctor_set(v_reuseFailAlloc_6067_, 4, v_D_6029_);
lean_ctor_set(v_reuseFailAlloc_6067_, 5, v_M_6030_);
lean_ctor_set(v_reuseFailAlloc_6067_, 6, v_L_6031_);
lean_ctor_set(v_reuseFailAlloc_6067_, 7, v_d_6032_);
lean_ctor_set(v_reuseFailAlloc_6067_, 8, v_Q_6033_);
lean_ctor_set(v_reuseFailAlloc_6067_, 9, v_q_6034_);
lean_ctor_set(v_reuseFailAlloc_6067_, 10, v_w_6035_);
lean_ctor_set(v_reuseFailAlloc_6067_, 11, v_W_6036_);
lean_ctor_set(v_reuseFailAlloc_6067_, 12, v_E_6037_);
lean_ctor_set(v_reuseFailAlloc_6067_, 13, v_e_6038_);
lean_ctor_set(v_reuseFailAlloc_6067_, 14, v_c_6039_);
lean_ctor_set(v_reuseFailAlloc_6067_, 15, v_F_6040_);
lean_ctor_set(v_reuseFailAlloc_6067_, 16, v_a_6041_);
lean_ctor_set(v_reuseFailAlloc_6067_, 17, v_b_6042_);
lean_ctor_set(v_reuseFailAlloc_6067_, 18, v_B_6043_);
lean_ctor_set(v_reuseFailAlloc_6067_, 19, v_h_6044_);
lean_ctor_set(v_reuseFailAlloc_6067_, 20, v_K_6045_);
lean_ctor_set(v_reuseFailAlloc_6067_, 21, v_k_6046_);
lean_ctor_set(v_reuseFailAlloc_6067_, 22, v_H_6047_);
lean_ctor_set(v_reuseFailAlloc_6067_, 23, v_m_6048_);
lean_ctor_set(v_reuseFailAlloc_6067_, 24, v_s_6049_);
lean_ctor_set(v_reuseFailAlloc_6067_, 25, v_S_6050_);
lean_ctor_set(v_reuseFailAlloc_6067_, 26, v_A_6051_);
lean_ctor_set(v_reuseFailAlloc_6067_, 27, v_n_6052_);
lean_ctor_set(v_reuseFailAlloc_6067_, 28, v_N_6053_);
lean_ctor_set(v_reuseFailAlloc_6067_, 29, v_V_6054_);
lean_ctor_set(v_reuseFailAlloc_6067_, 30, v_z_6055_);
lean_ctor_set(v_reuseFailAlloc_6067_, 31, v_zabbrev_6056_);
lean_ctor_set(v_reuseFailAlloc_6067_, 32, v___x_6064_);
lean_ctor_set(v_reuseFailAlloc_6067_, 33, v_O_6057_);
lean_ctor_set(v_reuseFailAlloc_6067_, 34, v_X_6058_);
lean_ctor_set(v_reuseFailAlloc_6067_, 35, v_x_6059_);
lean_ctor_set(v_reuseFailAlloc_6067_, 36, v_Z_6060_);
v___x_6066_ = v_reuseFailAlloc_6067_;
goto v_reusejp_6065_;
}
v_reusejp_6065_:
{
return v___x_6066_;
}
}
}
case 32:
{
lean_object* v_G_6070_; lean_object* v_y_6071_; lean_object* v_u_6072_; lean_object* v_Y_6073_; lean_object* v_D_6074_; lean_object* v_M_6075_; lean_object* v_L_6076_; lean_object* v_d_6077_; lean_object* v_Q_6078_; lean_object* v_q_6079_; lean_object* v_w_6080_; lean_object* v_W_6081_; lean_object* v_E_6082_; lean_object* v_e_6083_; lean_object* v_c_6084_; lean_object* v_F_6085_; lean_object* v_a_6086_; lean_object* v_b_6087_; lean_object* v_B_6088_; lean_object* v_h_6089_; lean_object* v_K_6090_; lean_object* v_k_6091_; lean_object* v_H_6092_; lean_object* v_m_6093_; lean_object* v_s_6094_; lean_object* v_S_6095_; lean_object* v_A_6096_; lean_object* v_n_6097_; lean_object* v_N_6098_; lean_object* v_V_6099_; lean_object* v_z_6100_; lean_object* v_zabbrev_6101_; lean_object* v_v_6102_; lean_object* v_X_6103_; lean_object* v_x_6104_; lean_object* v_Z_6105_; lean_object* v___x_6107_; uint8_t v_isShared_6108_; uint8_t v_isSharedCheck_6113_; 
lean_dec_ref_known(v_modifier_4414_, 0);
v_G_6070_ = lean_ctor_get(v_date_4413_, 0);
v_y_6071_ = lean_ctor_get(v_date_4413_, 1);
v_u_6072_ = lean_ctor_get(v_date_4413_, 2);
v_Y_6073_ = lean_ctor_get(v_date_4413_, 3);
v_D_6074_ = lean_ctor_get(v_date_4413_, 4);
v_M_6075_ = lean_ctor_get(v_date_4413_, 5);
v_L_6076_ = lean_ctor_get(v_date_4413_, 6);
v_d_6077_ = lean_ctor_get(v_date_4413_, 7);
v_Q_6078_ = lean_ctor_get(v_date_4413_, 8);
v_q_6079_ = lean_ctor_get(v_date_4413_, 9);
v_w_6080_ = lean_ctor_get(v_date_4413_, 10);
v_W_6081_ = lean_ctor_get(v_date_4413_, 11);
v_E_6082_ = lean_ctor_get(v_date_4413_, 12);
v_e_6083_ = lean_ctor_get(v_date_4413_, 13);
v_c_6084_ = lean_ctor_get(v_date_4413_, 14);
v_F_6085_ = lean_ctor_get(v_date_4413_, 15);
v_a_6086_ = lean_ctor_get(v_date_4413_, 16);
v_b_6087_ = lean_ctor_get(v_date_4413_, 17);
v_B_6088_ = lean_ctor_get(v_date_4413_, 18);
v_h_6089_ = lean_ctor_get(v_date_4413_, 19);
v_K_6090_ = lean_ctor_get(v_date_4413_, 20);
v_k_6091_ = lean_ctor_get(v_date_4413_, 21);
v_H_6092_ = lean_ctor_get(v_date_4413_, 22);
v_m_6093_ = lean_ctor_get(v_date_4413_, 23);
v_s_6094_ = lean_ctor_get(v_date_4413_, 24);
v_S_6095_ = lean_ctor_get(v_date_4413_, 25);
v_A_6096_ = lean_ctor_get(v_date_4413_, 26);
v_n_6097_ = lean_ctor_get(v_date_4413_, 27);
v_N_6098_ = lean_ctor_get(v_date_4413_, 28);
v_V_6099_ = lean_ctor_get(v_date_4413_, 29);
v_z_6100_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_6101_ = lean_ctor_get(v_date_4413_, 31);
v_v_6102_ = lean_ctor_get(v_date_4413_, 32);
v_X_6103_ = lean_ctor_get(v_date_4413_, 34);
v_x_6104_ = lean_ctor_get(v_date_4413_, 35);
v_Z_6105_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_6113_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_6113_ == 0)
{
lean_object* v_unused_6114_; 
v_unused_6114_ = lean_ctor_get(v_date_4413_, 33);
lean_dec(v_unused_6114_);
v___x_6107_ = v_date_4413_;
v_isShared_6108_ = v_isSharedCheck_6113_;
goto v_resetjp_6106_;
}
else
{
lean_inc(v_Z_6105_);
lean_inc(v_x_6104_);
lean_inc(v_X_6103_);
lean_inc(v_v_6102_);
lean_inc(v_zabbrev_6101_);
lean_inc(v_z_6100_);
lean_inc(v_V_6099_);
lean_inc(v_N_6098_);
lean_inc(v_n_6097_);
lean_inc(v_A_6096_);
lean_inc(v_S_6095_);
lean_inc(v_s_6094_);
lean_inc(v_m_6093_);
lean_inc(v_H_6092_);
lean_inc(v_k_6091_);
lean_inc(v_K_6090_);
lean_inc(v_h_6089_);
lean_inc(v_B_6088_);
lean_inc(v_b_6087_);
lean_inc(v_a_6086_);
lean_inc(v_F_6085_);
lean_inc(v_c_6084_);
lean_inc(v_e_6083_);
lean_inc(v_E_6082_);
lean_inc(v_W_6081_);
lean_inc(v_w_6080_);
lean_inc(v_q_6079_);
lean_inc(v_Q_6078_);
lean_inc(v_d_6077_);
lean_inc(v_L_6076_);
lean_inc(v_M_6075_);
lean_inc(v_D_6074_);
lean_inc(v_Y_6073_);
lean_inc(v_u_6072_);
lean_inc(v_y_6071_);
lean_inc(v_G_6070_);
lean_dec(v_date_4413_);
v___x_6107_ = lean_box(0);
v_isShared_6108_ = v_isSharedCheck_6113_;
goto v_resetjp_6106_;
}
v_resetjp_6106_:
{
lean_object* v___x_6109_; lean_object* v___x_6111_; 
v___x_6109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6109_, 0, v_data_4415_);
if (v_isShared_6108_ == 0)
{
lean_ctor_set(v___x_6107_, 33, v___x_6109_);
v___x_6111_ = v___x_6107_;
goto v_reusejp_6110_;
}
else
{
lean_object* v_reuseFailAlloc_6112_; 
v_reuseFailAlloc_6112_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6112_, 0, v_G_6070_);
lean_ctor_set(v_reuseFailAlloc_6112_, 1, v_y_6071_);
lean_ctor_set(v_reuseFailAlloc_6112_, 2, v_u_6072_);
lean_ctor_set(v_reuseFailAlloc_6112_, 3, v_Y_6073_);
lean_ctor_set(v_reuseFailAlloc_6112_, 4, v_D_6074_);
lean_ctor_set(v_reuseFailAlloc_6112_, 5, v_M_6075_);
lean_ctor_set(v_reuseFailAlloc_6112_, 6, v_L_6076_);
lean_ctor_set(v_reuseFailAlloc_6112_, 7, v_d_6077_);
lean_ctor_set(v_reuseFailAlloc_6112_, 8, v_Q_6078_);
lean_ctor_set(v_reuseFailAlloc_6112_, 9, v_q_6079_);
lean_ctor_set(v_reuseFailAlloc_6112_, 10, v_w_6080_);
lean_ctor_set(v_reuseFailAlloc_6112_, 11, v_W_6081_);
lean_ctor_set(v_reuseFailAlloc_6112_, 12, v_E_6082_);
lean_ctor_set(v_reuseFailAlloc_6112_, 13, v_e_6083_);
lean_ctor_set(v_reuseFailAlloc_6112_, 14, v_c_6084_);
lean_ctor_set(v_reuseFailAlloc_6112_, 15, v_F_6085_);
lean_ctor_set(v_reuseFailAlloc_6112_, 16, v_a_6086_);
lean_ctor_set(v_reuseFailAlloc_6112_, 17, v_b_6087_);
lean_ctor_set(v_reuseFailAlloc_6112_, 18, v_B_6088_);
lean_ctor_set(v_reuseFailAlloc_6112_, 19, v_h_6089_);
lean_ctor_set(v_reuseFailAlloc_6112_, 20, v_K_6090_);
lean_ctor_set(v_reuseFailAlloc_6112_, 21, v_k_6091_);
lean_ctor_set(v_reuseFailAlloc_6112_, 22, v_H_6092_);
lean_ctor_set(v_reuseFailAlloc_6112_, 23, v_m_6093_);
lean_ctor_set(v_reuseFailAlloc_6112_, 24, v_s_6094_);
lean_ctor_set(v_reuseFailAlloc_6112_, 25, v_S_6095_);
lean_ctor_set(v_reuseFailAlloc_6112_, 26, v_A_6096_);
lean_ctor_set(v_reuseFailAlloc_6112_, 27, v_n_6097_);
lean_ctor_set(v_reuseFailAlloc_6112_, 28, v_N_6098_);
lean_ctor_set(v_reuseFailAlloc_6112_, 29, v_V_6099_);
lean_ctor_set(v_reuseFailAlloc_6112_, 30, v_z_6100_);
lean_ctor_set(v_reuseFailAlloc_6112_, 31, v_zabbrev_6101_);
lean_ctor_set(v_reuseFailAlloc_6112_, 32, v_v_6102_);
lean_ctor_set(v_reuseFailAlloc_6112_, 33, v___x_6109_);
lean_ctor_set(v_reuseFailAlloc_6112_, 34, v_X_6103_);
lean_ctor_set(v_reuseFailAlloc_6112_, 35, v_x_6104_);
lean_ctor_set(v_reuseFailAlloc_6112_, 36, v_Z_6105_);
v___x_6111_ = v_reuseFailAlloc_6112_;
goto v_reusejp_6110_;
}
v_reusejp_6110_:
{
return v___x_6111_;
}
}
}
case 33:
{
lean_object* v_G_6115_; lean_object* v_y_6116_; lean_object* v_u_6117_; lean_object* v_Y_6118_; lean_object* v_D_6119_; lean_object* v_M_6120_; lean_object* v_L_6121_; lean_object* v_d_6122_; lean_object* v_Q_6123_; lean_object* v_q_6124_; lean_object* v_w_6125_; lean_object* v_W_6126_; lean_object* v_E_6127_; lean_object* v_e_6128_; lean_object* v_c_6129_; lean_object* v_F_6130_; lean_object* v_a_6131_; lean_object* v_b_6132_; lean_object* v_B_6133_; lean_object* v_h_6134_; lean_object* v_K_6135_; lean_object* v_k_6136_; lean_object* v_H_6137_; lean_object* v_m_6138_; lean_object* v_s_6139_; lean_object* v_S_6140_; lean_object* v_A_6141_; lean_object* v_n_6142_; lean_object* v_N_6143_; lean_object* v_V_6144_; lean_object* v_z_6145_; lean_object* v_zabbrev_6146_; lean_object* v_v_6147_; lean_object* v_O_6148_; lean_object* v_x_6149_; lean_object* v_Z_6150_; lean_object* v___x_6152_; uint8_t v_isShared_6153_; uint8_t v_isSharedCheck_6158_; 
lean_dec_ref_known(v_modifier_4414_, 0);
v_G_6115_ = lean_ctor_get(v_date_4413_, 0);
v_y_6116_ = lean_ctor_get(v_date_4413_, 1);
v_u_6117_ = lean_ctor_get(v_date_4413_, 2);
v_Y_6118_ = lean_ctor_get(v_date_4413_, 3);
v_D_6119_ = lean_ctor_get(v_date_4413_, 4);
v_M_6120_ = lean_ctor_get(v_date_4413_, 5);
v_L_6121_ = lean_ctor_get(v_date_4413_, 6);
v_d_6122_ = lean_ctor_get(v_date_4413_, 7);
v_Q_6123_ = lean_ctor_get(v_date_4413_, 8);
v_q_6124_ = lean_ctor_get(v_date_4413_, 9);
v_w_6125_ = lean_ctor_get(v_date_4413_, 10);
v_W_6126_ = lean_ctor_get(v_date_4413_, 11);
v_E_6127_ = lean_ctor_get(v_date_4413_, 12);
v_e_6128_ = lean_ctor_get(v_date_4413_, 13);
v_c_6129_ = lean_ctor_get(v_date_4413_, 14);
v_F_6130_ = lean_ctor_get(v_date_4413_, 15);
v_a_6131_ = lean_ctor_get(v_date_4413_, 16);
v_b_6132_ = lean_ctor_get(v_date_4413_, 17);
v_B_6133_ = lean_ctor_get(v_date_4413_, 18);
v_h_6134_ = lean_ctor_get(v_date_4413_, 19);
v_K_6135_ = lean_ctor_get(v_date_4413_, 20);
v_k_6136_ = lean_ctor_get(v_date_4413_, 21);
v_H_6137_ = lean_ctor_get(v_date_4413_, 22);
v_m_6138_ = lean_ctor_get(v_date_4413_, 23);
v_s_6139_ = lean_ctor_get(v_date_4413_, 24);
v_S_6140_ = lean_ctor_get(v_date_4413_, 25);
v_A_6141_ = lean_ctor_get(v_date_4413_, 26);
v_n_6142_ = lean_ctor_get(v_date_4413_, 27);
v_N_6143_ = lean_ctor_get(v_date_4413_, 28);
v_V_6144_ = lean_ctor_get(v_date_4413_, 29);
v_z_6145_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_6146_ = lean_ctor_get(v_date_4413_, 31);
v_v_6147_ = lean_ctor_get(v_date_4413_, 32);
v_O_6148_ = lean_ctor_get(v_date_4413_, 33);
v_x_6149_ = lean_ctor_get(v_date_4413_, 35);
v_Z_6150_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_6158_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_6158_ == 0)
{
lean_object* v_unused_6159_; 
v_unused_6159_ = lean_ctor_get(v_date_4413_, 34);
lean_dec(v_unused_6159_);
v___x_6152_ = v_date_4413_;
v_isShared_6153_ = v_isSharedCheck_6158_;
goto v_resetjp_6151_;
}
else
{
lean_inc(v_Z_6150_);
lean_inc(v_x_6149_);
lean_inc(v_O_6148_);
lean_inc(v_v_6147_);
lean_inc(v_zabbrev_6146_);
lean_inc(v_z_6145_);
lean_inc(v_V_6144_);
lean_inc(v_N_6143_);
lean_inc(v_n_6142_);
lean_inc(v_A_6141_);
lean_inc(v_S_6140_);
lean_inc(v_s_6139_);
lean_inc(v_m_6138_);
lean_inc(v_H_6137_);
lean_inc(v_k_6136_);
lean_inc(v_K_6135_);
lean_inc(v_h_6134_);
lean_inc(v_B_6133_);
lean_inc(v_b_6132_);
lean_inc(v_a_6131_);
lean_inc(v_F_6130_);
lean_inc(v_c_6129_);
lean_inc(v_e_6128_);
lean_inc(v_E_6127_);
lean_inc(v_W_6126_);
lean_inc(v_w_6125_);
lean_inc(v_q_6124_);
lean_inc(v_Q_6123_);
lean_inc(v_d_6122_);
lean_inc(v_L_6121_);
lean_inc(v_M_6120_);
lean_inc(v_D_6119_);
lean_inc(v_Y_6118_);
lean_inc(v_u_6117_);
lean_inc(v_y_6116_);
lean_inc(v_G_6115_);
lean_dec(v_date_4413_);
v___x_6152_ = lean_box(0);
v_isShared_6153_ = v_isSharedCheck_6158_;
goto v_resetjp_6151_;
}
v_resetjp_6151_:
{
lean_object* v___x_6154_; lean_object* v___x_6156_; 
v___x_6154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6154_, 0, v_data_4415_);
if (v_isShared_6153_ == 0)
{
lean_ctor_set(v___x_6152_, 34, v___x_6154_);
v___x_6156_ = v___x_6152_;
goto v_reusejp_6155_;
}
else
{
lean_object* v_reuseFailAlloc_6157_; 
v_reuseFailAlloc_6157_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6157_, 0, v_G_6115_);
lean_ctor_set(v_reuseFailAlloc_6157_, 1, v_y_6116_);
lean_ctor_set(v_reuseFailAlloc_6157_, 2, v_u_6117_);
lean_ctor_set(v_reuseFailAlloc_6157_, 3, v_Y_6118_);
lean_ctor_set(v_reuseFailAlloc_6157_, 4, v_D_6119_);
lean_ctor_set(v_reuseFailAlloc_6157_, 5, v_M_6120_);
lean_ctor_set(v_reuseFailAlloc_6157_, 6, v_L_6121_);
lean_ctor_set(v_reuseFailAlloc_6157_, 7, v_d_6122_);
lean_ctor_set(v_reuseFailAlloc_6157_, 8, v_Q_6123_);
lean_ctor_set(v_reuseFailAlloc_6157_, 9, v_q_6124_);
lean_ctor_set(v_reuseFailAlloc_6157_, 10, v_w_6125_);
lean_ctor_set(v_reuseFailAlloc_6157_, 11, v_W_6126_);
lean_ctor_set(v_reuseFailAlloc_6157_, 12, v_E_6127_);
lean_ctor_set(v_reuseFailAlloc_6157_, 13, v_e_6128_);
lean_ctor_set(v_reuseFailAlloc_6157_, 14, v_c_6129_);
lean_ctor_set(v_reuseFailAlloc_6157_, 15, v_F_6130_);
lean_ctor_set(v_reuseFailAlloc_6157_, 16, v_a_6131_);
lean_ctor_set(v_reuseFailAlloc_6157_, 17, v_b_6132_);
lean_ctor_set(v_reuseFailAlloc_6157_, 18, v_B_6133_);
lean_ctor_set(v_reuseFailAlloc_6157_, 19, v_h_6134_);
lean_ctor_set(v_reuseFailAlloc_6157_, 20, v_K_6135_);
lean_ctor_set(v_reuseFailAlloc_6157_, 21, v_k_6136_);
lean_ctor_set(v_reuseFailAlloc_6157_, 22, v_H_6137_);
lean_ctor_set(v_reuseFailAlloc_6157_, 23, v_m_6138_);
lean_ctor_set(v_reuseFailAlloc_6157_, 24, v_s_6139_);
lean_ctor_set(v_reuseFailAlloc_6157_, 25, v_S_6140_);
lean_ctor_set(v_reuseFailAlloc_6157_, 26, v_A_6141_);
lean_ctor_set(v_reuseFailAlloc_6157_, 27, v_n_6142_);
lean_ctor_set(v_reuseFailAlloc_6157_, 28, v_N_6143_);
lean_ctor_set(v_reuseFailAlloc_6157_, 29, v_V_6144_);
lean_ctor_set(v_reuseFailAlloc_6157_, 30, v_z_6145_);
lean_ctor_set(v_reuseFailAlloc_6157_, 31, v_zabbrev_6146_);
lean_ctor_set(v_reuseFailAlloc_6157_, 32, v_v_6147_);
lean_ctor_set(v_reuseFailAlloc_6157_, 33, v_O_6148_);
lean_ctor_set(v_reuseFailAlloc_6157_, 34, v___x_6154_);
lean_ctor_set(v_reuseFailAlloc_6157_, 35, v_x_6149_);
lean_ctor_set(v_reuseFailAlloc_6157_, 36, v_Z_6150_);
v___x_6156_ = v_reuseFailAlloc_6157_;
goto v_reusejp_6155_;
}
v_reusejp_6155_:
{
return v___x_6156_;
}
}
}
case 34:
{
lean_object* v_G_6160_; lean_object* v_y_6161_; lean_object* v_u_6162_; lean_object* v_Y_6163_; lean_object* v_D_6164_; lean_object* v_M_6165_; lean_object* v_L_6166_; lean_object* v_d_6167_; lean_object* v_Q_6168_; lean_object* v_q_6169_; lean_object* v_w_6170_; lean_object* v_W_6171_; lean_object* v_E_6172_; lean_object* v_e_6173_; lean_object* v_c_6174_; lean_object* v_F_6175_; lean_object* v_a_6176_; lean_object* v_b_6177_; lean_object* v_B_6178_; lean_object* v_h_6179_; lean_object* v_K_6180_; lean_object* v_k_6181_; lean_object* v_H_6182_; lean_object* v_m_6183_; lean_object* v_s_6184_; lean_object* v_S_6185_; lean_object* v_A_6186_; lean_object* v_n_6187_; lean_object* v_N_6188_; lean_object* v_V_6189_; lean_object* v_z_6190_; lean_object* v_zabbrev_6191_; lean_object* v_v_6192_; lean_object* v_O_6193_; lean_object* v_X_6194_; lean_object* v_Z_6195_; lean_object* v___x_6197_; uint8_t v_isShared_6198_; uint8_t v_isSharedCheck_6203_; 
lean_dec_ref_known(v_modifier_4414_, 0);
v_G_6160_ = lean_ctor_get(v_date_4413_, 0);
v_y_6161_ = lean_ctor_get(v_date_4413_, 1);
v_u_6162_ = lean_ctor_get(v_date_4413_, 2);
v_Y_6163_ = lean_ctor_get(v_date_4413_, 3);
v_D_6164_ = lean_ctor_get(v_date_4413_, 4);
v_M_6165_ = lean_ctor_get(v_date_4413_, 5);
v_L_6166_ = lean_ctor_get(v_date_4413_, 6);
v_d_6167_ = lean_ctor_get(v_date_4413_, 7);
v_Q_6168_ = lean_ctor_get(v_date_4413_, 8);
v_q_6169_ = lean_ctor_get(v_date_4413_, 9);
v_w_6170_ = lean_ctor_get(v_date_4413_, 10);
v_W_6171_ = lean_ctor_get(v_date_4413_, 11);
v_E_6172_ = lean_ctor_get(v_date_4413_, 12);
v_e_6173_ = lean_ctor_get(v_date_4413_, 13);
v_c_6174_ = lean_ctor_get(v_date_4413_, 14);
v_F_6175_ = lean_ctor_get(v_date_4413_, 15);
v_a_6176_ = lean_ctor_get(v_date_4413_, 16);
v_b_6177_ = lean_ctor_get(v_date_4413_, 17);
v_B_6178_ = lean_ctor_get(v_date_4413_, 18);
v_h_6179_ = lean_ctor_get(v_date_4413_, 19);
v_K_6180_ = lean_ctor_get(v_date_4413_, 20);
v_k_6181_ = lean_ctor_get(v_date_4413_, 21);
v_H_6182_ = lean_ctor_get(v_date_4413_, 22);
v_m_6183_ = lean_ctor_get(v_date_4413_, 23);
v_s_6184_ = lean_ctor_get(v_date_4413_, 24);
v_S_6185_ = lean_ctor_get(v_date_4413_, 25);
v_A_6186_ = lean_ctor_get(v_date_4413_, 26);
v_n_6187_ = lean_ctor_get(v_date_4413_, 27);
v_N_6188_ = lean_ctor_get(v_date_4413_, 28);
v_V_6189_ = lean_ctor_get(v_date_4413_, 29);
v_z_6190_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_6191_ = lean_ctor_get(v_date_4413_, 31);
v_v_6192_ = lean_ctor_get(v_date_4413_, 32);
v_O_6193_ = lean_ctor_get(v_date_4413_, 33);
v_X_6194_ = lean_ctor_get(v_date_4413_, 34);
v_Z_6195_ = lean_ctor_get(v_date_4413_, 36);
v_isSharedCheck_6203_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_6203_ == 0)
{
lean_object* v_unused_6204_; 
v_unused_6204_ = lean_ctor_get(v_date_4413_, 35);
lean_dec(v_unused_6204_);
v___x_6197_ = v_date_4413_;
v_isShared_6198_ = v_isSharedCheck_6203_;
goto v_resetjp_6196_;
}
else
{
lean_inc(v_Z_6195_);
lean_inc(v_X_6194_);
lean_inc(v_O_6193_);
lean_inc(v_v_6192_);
lean_inc(v_zabbrev_6191_);
lean_inc(v_z_6190_);
lean_inc(v_V_6189_);
lean_inc(v_N_6188_);
lean_inc(v_n_6187_);
lean_inc(v_A_6186_);
lean_inc(v_S_6185_);
lean_inc(v_s_6184_);
lean_inc(v_m_6183_);
lean_inc(v_H_6182_);
lean_inc(v_k_6181_);
lean_inc(v_K_6180_);
lean_inc(v_h_6179_);
lean_inc(v_B_6178_);
lean_inc(v_b_6177_);
lean_inc(v_a_6176_);
lean_inc(v_F_6175_);
lean_inc(v_c_6174_);
lean_inc(v_e_6173_);
lean_inc(v_E_6172_);
lean_inc(v_W_6171_);
lean_inc(v_w_6170_);
lean_inc(v_q_6169_);
lean_inc(v_Q_6168_);
lean_inc(v_d_6167_);
lean_inc(v_L_6166_);
lean_inc(v_M_6165_);
lean_inc(v_D_6164_);
lean_inc(v_Y_6163_);
lean_inc(v_u_6162_);
lean_inc(v_y_6161_);
lean_inc(v_G_6160_);
lean_dec(v_date_4413_);
v___x_6197_ = lean_box(0);
v_isShared_6198_ = v_isSharedCheck_6203_;
goto v_resetjp_6196_;
}
v_resetjp_6196_:
{
lean_object* v___x_6199_; lean_object* v___x_6201_; 
v___x_6199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6199_, 0, v_data_4415_);
if (v_isShared_6198_ == 0)
{
lean_ctor_set(v___x_6197_, 35, v___x_6199_);
v___x_6201_ = v___x_6197_;
goto v_reusejp_6200_;
}
else
{
lean_object* v_reuseFailAlloc_6202_; 
v_reuseFailAlloc_6202_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6202_, 0, v_G_6160_);
lean_ctor_set(v_reuseFailAlloc_6202_, 1, v_y_6161_);
lean_ctor_set(v_reuseFailAlloc_6202_, 2, v_u_6162_);
lean_ctor_set(v_reuseFailAlloc_6202_, 3, v_Y_6163_);
lean_ctor_set(v_reuseFailAlloc_6202_, 4, v_D_6164_);
lean_ctor_set(v_reuseFailAlloc_6202_, 5, v_M_6165_);
lean_ctor_set(v_reuseFailAlloc_6202_, 6, v_L_6166_);
lean_ctor_set(v_reuseFailAlloc_6202_, 7, v_d_6167_);
lean_ctor_set(v_reuseFailAlloc_6202_, 8, v_Q_6168_);
lean_ctor_set(v_reuseFailAlloc_6202_, 9, v_q_6169_);
lean_ctor_set(v_reuseFailAlloc_6202_, 10, v_w_6170_);
lean_ctor_set(v_reuseFailAlloc_6202_, 11, v_W_6171_);
lean_ctor_set(v_reuseFailAlloc_6202_, 12, v_E_6172_);
lean_ctor_set(v_reuseFailAlloc_6202_, 13, v_e_6173_);
lean_ctor_set(v_reuseFailAlloc_6202_, 14, v_c_6174_);
lean_ctor_set(v_reuseFailAlloc_6202_, 15, v_F_6175_);
lean_ctor_set(v_reuseFailAlloc_6202_, 16, v_a_6176_);
lean_ctor_set(v_reuseFailAlloc_6202_, 17, v_b_6177_);
lean_ctor_set(v_reuseFailAlloc_6202_, 18, v_B_6178_);
lean_ctor_set(v_reuseFailAlloc_6202_, 19, v_h_6179_);
lean_ctor_set(v_reuseFailAlloc_6202_, 20, v_K_6180_);
lean_ctor_set(v_reuseFailAlloc_6202_, 21, v_k_6181_);
lean_ctor_set(v_reuseFailAlloc_6202_, 22, v_H_6182_);
lean_ctor_set(v_reuseFailAlloc_6202_, 23, v_m_6183_);
lean_ctor_set(v_reuseFailAlloc_6202_, 24, v_s_6184_);
lean_ctor_set(v_reuseFailAlloc_6202_, 25, v_S_6185_);
lean_ctor_set(v_reuseFailAlloc_6202_, 26, v_A_6186_);
lean_ctor_set(v_reuseFailAlloc_6202_, 27, v_n_6187_);
lean_ctor_set(v_reuseFailAlloc_6202_, 28, v_N_6188_);
lean_ctor_set(v_reuseFailAlloc_6202_, 29, v_V_6189_);
lean_ctor_set(v_reuseFailAlloc_6202_, 30, v_z_6190_);
lean_ctor_set(v_reuseFailAlloc_6202_, 31, v_zabbrev_6191_);
lean_ctor_set(v_reuseFailAlloc_6202_, 32, v_v_6192_);
lean_ctor_set(v_reuseFailAlloc_6202_, 33, v_O_6193_);
lean_ctor_set(v_reuseFailAlloc_6202_, 34, v_X_6194_);
lean_ctor_set(v_reuseFailAlloc_6202_, 35, v___x_6199_);
lean_ctor_set(v_reuseFailAlloc_6202_, 36, v_Z_6195_);
v___x_6201_ = v_reuseFailAlloc_6202_;
goto v_reusejp_6200_;
}
v_reusejp_6200_:
{
return v___x_6201_;
}
}
}
default: 
{
lean_object* v_G_6205_; lean_object* v_y_6206_; lean_object* v_u_6207_; lean_object* v_Y_6208_; lean_object* v_D_6209_; lean_object* v_M_6210_; lean_object* v_L_6211_; lean_object* v_d_6212_; lean_object* v_Q_6213_; lean_object* v_q_6214_; lean_object* v_w_6215_; lean_object* v_W_6216_; lean_object* v_E_6217_; lean_object* v_e_6218_; lean_object* v_c_6219_; lean_object* v_F_6220_; lean_object* v_a_6221_; lean_object* v_b_6222_; lean_object* v_B_6223_; lean_object* v_h_6224_; lean_object* v_K_6225_; lean_object* v_k_6226_; lean_object* v_H_6227_; lean_object* v_m_6228_; lean_object* v_s_6229_; lean_object* v_S_6230_; lean_object* v_A_6231_; lean_object* v_n_6232_; lean_object* v_N_6233_; lean_object* v_V_6234_; lean_object* v_z_6235_; lean_object* v_zabbrev_6236_; lean_object* v_v_6237_; lean_object* v_O_6238_; lean_object* v_X_6239_; lean_object* v_x_6240_; lean_object* v___x_6242_; uint8_t v_isShared_6243_; uint8_t v_isSharedCheck_6248_; 
lean_dec_ref_known(v_modifier_4414_, 0);
v_G_6205_ = lean_ctor_get(v_date_4413_, 0);
v_y_6206_ = lean_ctor_get(v_date_4413_, 1);
v_u_6207_ = lean_ctor_get(v_date_4413_, 2);
v_Y_6208_ = lean_ctor_get(v_date_4413_, 3);
v_D_6209_ = lean_ctor_get(v_date_4413_, 4);
v_M_6210_ = lean_ctor_get(v_date_4413_, 5);
v_L_6211_ = lean_ctor_get(v_date_4413_, 6);
v_d_6212_ = lean_ctor_get(v_date_4413_, 7);
v_Q_6213_ = lean_ctor_get(v_date_4413_, 8);
v_q_6214_ = lean_ctor_get(v_date_4413_, 9);
v_w_6215_ = lean_ctor_get(v_date_4413_, 10);
v_W_6216_ = lean_ctor_get(v_date_4413_, 11);
v_E_6217_ = lean_ctor_get(v_date_4413_, 12);
v_e_6218_ = lean_ctor_get(v_date_4413_, 13);
v_c_6219_ = lean_ctor_get(v_date_4413_, 14);
v_F_6220_ = lean_ctor_get(v_date_4413_, 15);
v_a_6221_ = lean_ctor_get(v_date_4413_, 16);
v_b_6222_ = lean_ctor_get(v_date_4413_, 17);
v_B_6223_ = lean_ctor_get(v_date_4413_, 18);
v_h_6224_ = lean_ctor_get(v_date_4413_, 19);
v_K_6225_ = lean_ctor_get(v_date_4413_, 20);
v_k_6226_ = lean_ctor_get(v_date_4413_, 21);
v_H_6227_ = lean_ctor_get(v_date_4413_, 22);
v_m_6228_ = lean_ctor_get(v_date_4413_, 23);
v_s_6229_ = lean_ctor_get(v_date_4413_, 24);
v_S_6230_ = lean_ctor_get(v_date_4413_, 25);
v_A_6231_ = lean_ctor_get(v_date_4413_, 26);
v_n_6232_ = lean_ctor_get(v_date_4413_, 27);
v_N_6233_ = lean_ctor_get(v_date_4413_, 28);
v_V_6234_ = lean_ctor_get(v_date_4413_, 29);
v_z_6235_ = lean_ctor_get(v_date_4413_, 30);
v_zabbrev_6236_ = lean_ctor_get(v_date_4413_, 31);
v_v_6237_ = lean_ctor_get(v_date_4413_, 32);
v_O_6238_ = lean_ctor_get(v_date_4413_, 33);
v_X_6239_ = lean_ctor_get(v_date_4413_, 34);
v_x_6240_ = lean_ctor_get(v_date_4413_, 35);
v_isSharedCheck_6248_ = !lean_is_exclusive(v_date_4413_);
if (v_isSharedCheck_6248_ == 0)
{
lean_object* v_unused_6249_; 
v_unused_6249_ = lean_ctor_get(v_date_4413_, 36);
lean_dec(v_unused_6249_);
v___x_6242_ = v_date_4413_;
v_isShared_6243_ = v_isSharedCheck_6248_;
goto v_resetjp_6241_;
}
else
{
lean_inc(v_x_6240_);
lean_inc(v_X_6239_);
lean_inc(v_O_6238_);
lean_inc(v_v_6237_);
lean_inc(v_zabbrev_6236_);
lean_inc(v_z_6235_);
lean_inc(v_V_6234_);
lean_inc(v_N_6233_);
lean_inc(v_n_6232_);
lean_inc(v_A_6231_);
lean_inc(v_S_6230_);
lean_inc(v_s_6229_);
lean_inc(v_m_6228_);
lean_inc(v_H_6227_);
lean_inc(v_k_6226_);
lean_inc(v_K_6225_);
lean_inc(v_h_6224_);
lean_inc(v_B_6223_);
lean_inc(v_b_6222_);
lean_inc(v_a_6221_);
lean_inc(v_F_6220_);
lean_inc(v_c_6219_);
lean_inc(v_e_6218_);
lean_inc(v_E_6217_);
lean_inc(v_W_6216_);
lean_inc(v_w_6215_);
lean_inc(v_q_6214_);
lean_inc(v_Q_6213_);
lean_inc(v_d_6212_);
lean_inc(v_L_6211_);
lean_inc(v_M_6210_);
lean_inc(v_D_6209_);
lean_inc(v_Y_6208_);
lean_inc(v_u_6207_);
lean_inc(v_y_6206_);
lean_inc(v_G_6205_);
lean_dec(v_date_4413_);
v___x_6242_ = lean_box(0);
v_isShared_6243_ = v_isSharedCheck_6248_;
goto v_resetjp_6241_;
}
v_resetjp_6241_:
{
lean_object* v___x_6244_; lean_object* v___x_6246_; 
v___x_6244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6244_, 0, v_data_4415_);
if (v_isShared_6243_ == 0)
{
lean_ctor_set(v___x_6242_, 36, v___x_6244_);
v___x_6246_ = v___x_6242_;
goto v_reusejp_6245_;
}
else
{
lean_object* v_reuseFailAlloc_6247_; 
v_reuseFailAlloc_6247_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6247_, 0, v_G_6205_);
lean_ctor_set(v_reuseFailAlloc_6247_, 1, v_y_6206_);
lean_ctor_set(v_reuseFailAlloc_6247_, 2, v_u_6207_);
lean_ctor_set(v_reuseFailAlloc_6247_, 3, v_Y_6208_);
lean_ctor_set(v_reuseFailAlloc_6247_, 4, v_D_6209_);
lean_ctor_set(v_reuseFailAlloc_6247_, 5, v_M_6210_);
lean_ctor_set(v_reuseFailAlloc_6247_, 6, v_L_6211_);
lean_ctor_set(v_reuseFailAlloc_6247_, 7, v_d_6212_);
lean_ctor_set(v_reuseFailAlloc_6247_, 8, v_Q_6213_);
lean_ctor_set(v_reuseFailAlloc_6247_, 9, v_q_6214_);
lean_ctor_set(v_reuseFailAlloc_6247_, 10, v_w_6215_);
lean_ctor_set(v_reuseFailAlloc_6247_, 11, v_W_6216_);
lean_ctor_set(v_reuseFailAlloc_6247_, 12, v_E_6217_);
lean_ctor_set(v_reuseFailAlloc_6247_, 13, v_e_6218_);
lean_ctor_set(v_reuseFailAlloc_6247_, 14, v_c_6219_);
lean_ctor_set(v_reuseFailAlloc_6247_, 15, v_F_6220_);
lean_ctor_set(v_reuseFailAlloc_6247_, 16, v_a_6221_);
lean_ctor_set(v_reuseFailAlloc_6247_, 17, v_b_6222_);
lean_ctor_set(v_reuseFailAlloc_6247_, 18, v_B_6223_);
lean_ctor_set(v_reuseFailAlloc_6247_, 19, v_h_6224_);
lean_ctor_set(v_reuseFailAlloc_6247_, 20, v_K_6225_);
lean_ctor_set(v_reuseFailAlloc_6247_, 21, v_k_6226_);
lean_ctor_set(v_reuseFailAlloc_6247_, 22, v_H_6227_);
lean_ctor_set(v_reuseFailAlloc_6247_, 23, v_m_6228_);
lean_ctor_set(v_reuseFailAlloc_6247_, 24, v_s_6229_);
lean_ctor_set(v_reuseFailAlloc_6247_, 25, v_S_6230_);
lean_ctor_set(v_reuseFailAlloc_6247_, 26, v_A_6231_);
lean_ctor_set(v_reuseFailAlloc_6247_, 27, v_n_6232_);
lean_ctor_set(v_reuseFailAlloc_6247_, 28, v_N_6233_);
lean_ctor_set(v_reuseFailAlloc_6247_, 29, v_V_6234_);
lean_ctor_set(v_reuseFailAlloc_6247_, 30, v_z_6235_);
lean_ctor_set(v_reuseFailAlloc_6247_, 31, v_zabbrev_6236_);
lean_ctor_set(v_reuseFailAlloc_6247_, 32, v_v_6237_);
lean_ctor_set(v_reuseFailAlloc_6247_, 33, v_O_6238_);
lean_ctor_set(v_reuseFailAlloc_6247_, 34, v_X_6239_);
lean_ctor_set(v_reuseFailAlloc_6247_, 35, v_x_6240_);
lean_ctor_set(v_reuseFailAlloc_6247_, 36, v___x_6244_);
v___x_6246_ = v_reuseFailAlloc_6247_;
goto v_reusejp_6245_;
}
v_reusejp_6245_:
{
return v___x_6246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(lean_object* v_year_6250_, uint8_t v_x_6251_){
_start:
{
if (v_x_6251_ == 0)
{
lean_object* v___x_6252_; lean_object* v___x_6253_; 
v___x_6252_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6253_ = lean_int_sub(v___x_6252_, v_year_6250_);
return v___x_6253_;
}
else
{
lean_inc(v_year_6250_);
return v_year_6250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra___boxed(lean_object* v_year_6254_, lean_object* v_x_6255_){
_start:
{
uint8_t v_x_36__boxed_6256_; lean_object* v_res_6257_; 
v_x_36__boxed_6256_ = lean_unbox(v_x_6255_);
v_res_6257_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_year_6254_, v_x_36__boxed_6256_);
lean_dec(v_year_6254_);
return v_res_6257_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(uint8_t v_x_6258_){
_start:
{
switch(v_x_6258_)
{
case 1:
{
uint8_t v___x_6259_; 
v___x_6259_ = 1;
return v___x_6259_;
}
case 2:
{
uint8_t v___x_6260_; 
v___x_6260_ = 1;
return v___x_6260_;
}
default: 
{
uint8_t v___x_6261_; 
v___x_6261_ = 0;
return v___x_6261_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod___boxed(lean_object* v_x_6262_){
_start:
{
uint8_t v_x_28__boxed_6263_; uint8_t v_res_6264_; lean_object* v_r_6265_; 
v_x_28__boxed_6263_ = lean_unbox(v_x_6262_);
v_res_6264_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v_x_28__boxed_6263_);
v_r_6265_ = lean_box(v_res_6264_);
return v_r_6265_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(uint8_t v_x_6266_){
_start:
{
switch(v_x_6266_)
{
case 3:
{
uint8_t v___x_6267_; 
v___x_6267_ = 1;
return v___x_6267_;
}
case 4:
{
uint8_t v___x_6268_; 
v___x_6268_ = 1;
return v___x_6268_;
}
case 5:
{
uint8_t v___x_6269_; 
v___x_6269_ = 1;
return v___x_6269_;
}
default: 
{
uint8_t v___x_6270_; 
v___x_6270_ = 0;
return v___x_6270_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod___boxed(lean_object* v_x_6271_){
_start:
{
uint8_t v_x_38__boxed_6272_; uint8_t v_res_6273_; lean_object* v_r_6274_; 
v_x_38__boxed_6272_ = lean_unbox(v_x_6271_);
v_res_6273_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v_x_38__boxed_6272_);
v_r_6274_ = lean_box(v_res_6273_);
return v_r_6274_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(lean_object* v_val_6275_, lean_object* v_x_6276_){
_start:
{
lean_inc_ref(v_val_6275_);
return v_val_6275_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed(lean_object* v_val_6277_, lean_object* v_x_6278_){
_start:
{
lean_object* v_res_6279_; 
v_res_6279_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(v_val_6277_, v_x_6278_);
lean_dec_ref(v_val_6277_);
return v_res_6279_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(lean_object* v___y_6280_, lean_object* v_00___6281_){
_start:
{
uint8_t v___x_6282_; lean_object* v___x_6283_; 
v___x_6282_ = 1;
v___x_6283_ = l_Std_Time_TimeZone_Offset_toIsoString(v___y_6280_, v___x_6282_);
return v___x_6283_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1(void){
_start:
{
lean_object* v___x_6286_; lean_object* v___x_6287_; 
v___x_6286_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6287_ = lean_int_neg(v___x_6286_);
return v___x_6287_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2(void){
_start:
{
lean_object* v___x_6288_; lean_object* v___x_6289_; 
v___x_6288_ = lean_unsigned_to_nat(1000000u);
v___x_6289_ = lean_nat_to_int(v___x_6288_);
return v___x_6289_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3(void){
_start:
{
lean_object* v___x_6290_; uint8_t v___x_6291_; lean_object* v___x_6292_; 
v___x_6290_ = lean_unsigned_to_nat(0u);
v___x_6291_ = 1;
v___x_6292_ = l_Std_Time_Second_instOfNatOrdinal(v___x_6291_, v___x_6290_);
return v___x_6292_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4(void){
_start:
{
lean_object* v___x_6293_; lean_object* v___x_6294_; lean_object* v___x_6295_; 
v___x_6293_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5);
v___x_6294_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6295_ = lean_int_add(v___x_6294_, v___x_6293_);
return v___x_6295_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5(void){
_start:
{
lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; 
v___x_6296_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6297_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4);
v___x_6298_ = lean_int_sub(v___x_6297_, v___x_6296_);
return v___x_6298_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6(void){
_start:
{
lean_object* v___x_6299_; lean_object* v___x_6300_; lean_object* v_range_6301_; 
v___x_6299_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6300_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5);
v_range_6301_ = lean_int_add(v___x_6300_, v___x_6299_);
return v_range_6301_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7(void){
_start:
{
lean_object* v___x_6302_; lean_object* v___x_6303_; 
v___x_6302_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6303_ = lean_int_sub(v___x_6302_, v___x_6302_);
return v___x_6303_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8(void){
_start:
{
lean_object* v_range_6304_; lean_object* v___x_6305_; lean_object* v___x_6306_; 
v_range_6304_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6);
v___x_6305_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7);
v___x_6306_ = lean_int_emod(v___x_6305_, v_range_6304_);
return v___x_6306_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9(void){
_start:
{
lean_object* v_range_6307_; lean_object* v___x_6308_; lean_object* v___x_6309_; 
v_range_6307_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6);
v___x_6308_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8);
v___x_6309_ = lean_int_add(v___x_6308_, v_range_6307_);
return v___x_6309_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10(void){
_start:
{
lean_object* v_range_6310_; lean_object* v___x_6311_; lean_object* v___x_6312_; 
v_range_6310_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6);
v___x_6311_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9);
v___x_6312_ = lean_int_emod(v___x_6311_, v_range_6310_);
return v___x_6312_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11(void){
_start:
{
lean_object* v___x_6313_; lean_object* v___x_6314_; lean_object* v___x_6315_; 
v___x_6313_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6314_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10);
v___x_6315_ = lean_int_add(v___x_6314_, v___x_6313_);
return v___x_6315_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12(void){
_start:
{
lean_object* v___x_6316_; lean_object* v___x_6317_; 
v___x_6316_ = lean_unsigned_to_nat(24u);
v___x_6317_ = lean_nat_to_int(v___x_6316_);
return v___x_6317_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13(void){
_start:
{
lean_object* v___x_6318_; lean_object* v___x_6319_; 
v___x_6318_ = lean_unsigned_to_nat(30u);
v___x_6319_ = lean_nat_to_int(v___x_6318_);
return v___x_6319_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14(void){
_start:
{
lean_object* v___x_6320_; lean_object* v___x_6321_; lean_object* v___x_6322_; 
v___x_6320_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13);
v___x_6321_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6322_ = lean_int_add(v___x_6321_, v___x_6320_);
return v___x_6322_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15(void){
_start:
{
lean_object* v___x_6323_; lean_object* v___x_6324_; lean_object* v___x_6325_; 
v___x_6323_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6324_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14);
v___x_6325_ = lean_int_sub(v___x_6324_, v___x_6323_);
return v___x_6325_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16(void){
_start:
{
lean_object* v___x_6326_; lean_object* v___x_6327_; lean_object* v_range_6328_; 
v___x_6326_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6327_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v_range_6328_ = lean_int_add(v___x_6327_, v___x_6326_);
return v_range_6328_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17(void){
_start:
{
lean_object* v___x_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; 
v___x_6329_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6330_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6331_ = lean_int_sub(v___x_6330_, v___x_6329_);
return v___x_6331_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18(void){
_start:
{
lean_object* v_range_6332_; lean_object* v___x_6333_; lean_object* v___x_6334_; 
v_range_6332_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16);
v___x_6333_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17);
v___x_6334_ = lean_int_emod(v___x_6333_, v_range_6332_);
return v___x_6334_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19(void){
_start:
{
lean_object* v_range_6335_; lean_object* v___x_6336_; lean_object* v___x_6337_; 
v_range_6335_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16);
v___x_6336_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18);
v___x_6337_ = lean_int_add(v___x_6336_, v_range_6335_);
return v___x_6337_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20(void){
_start:
{
lean_object* v_range_6338_; lean_object* v___x_6339_; lean_object* v___x_6340_; 
v_range_6338_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16);
v___x_6339_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19);
v___x_6340_ = lean_int_emod(v___x_6339_, v_range_6338_);
return v___x_6340_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21(void){
_start:
{
lean_object* v___x_6341_; lean_object* v___x_6342_; lean_object* v___x_6343_; 
v___x_6341_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6342_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20);
v___x_6343_ = lean_int_add(v___x_6342_, v___x_6341_);
return v___x_6343_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22(void){
_start:
{
lean_object* v___x_6344_; lean_object* v___x_6345_; 
v___x_6344_ = lean_unsigned_to_nat(11u);
v___x_6345_ = lean_nat_to_int(v___x_6344_);
return v___x_6345_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23(void){
_start:
{
lean_object* v___x_6346_; lean_object* v___x_6347_; lean_object* v___x_6348_; 
v___x_6346_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22);
v___x_6347_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6348_ = lean_int_add(v___x_6347_, v___x_6346_);
return v___x_6348_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24(void){
_start:
{
lean_object* v___x_6349_; lean_object* v___x_6350_; lean_object* v___x_6351_; 
v___x_6349_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6350_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23);
v___x_6351_ = lean_int_sub(v___x_6350_, v___x_6349_);
return v___x_6351_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25(void){
_start:
{
lean_object* v___x_6352_; lean_object* v___x_6353_; lean_object* v_range_6354_; 
v___x_6352_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6353_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24);
v_range_6354_ = lean_int_add(v___x_6353_, v___x_6352_);
return v_range_6354_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26(void){
_start:
{
lean_object* v_range_6355_; lean_object* v___x_6356_; lean_object* v___x_6357_; 
v_range_6355_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25);
v___x_6356_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17);
v___x_6357_ = lean_int_emod(v___x_6356_, v_range_6355_);
return v___x_6357_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27(void){
_start:
{
lean_object* v_range_6358_; lean_object* v___x_6359_; lean_object* v___x_6360_; 
v_range_6358_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25);
v___x_6359_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26);
v___x_6360_ = lean_int_add(v___x_6359_, v_range_6358_);
return v___x_6360_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28(void){
_start:
{
lean_object* v_range_6361_; lean_object* v___x_6362_; lean_object* v___x_6363_; 
v_range_6361_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25);
v___x_6362_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27);
v___x_6363_ = lean_int_emod(v___x_6362_, v_range_6361_);
return v___x_6363_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29(void){
_start:
{
lean_object* v___x_6364_; lean_object* v___x_6365_; lean_object* v___x_6366_; 
v___x_6364_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6365_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28);
v___x_6366_ = lean_int_add(v___x_6365_, v___x_6364_);
return v___x_6366_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(lean_object* v_builder_6367_, lean_object* v_aw_6368_){
_start:
{
lean_object* v___y_6370_; lean_object* v___y_6371_; lean_object* v___y_6410_; lean_object* v___y_6411_; lean_object* v___y_6414_; lean_object* v___y_6415_; lean_object* v___y_6416_; lean_object* v___y_6417_; lean_object* v___y_6418_; uint8_t v___y_6419_; lean_object* v___y_6427_; lean_object* v___y_6428_; lean_object* v___y_6429_; lean_object* v___y_6430_; lean_object* v___y_6431_; lean_object* v_G_6442_; lean_object* v_y_6443_; lean_object* v_u_6444_; lean_object* v_Y_6445_; lean_object* v_M_6446_; lean_object* v_L_6447_; lean_object* v_d_6448_; lean_object* v_a_6449_; lean_object* v_b_6450_; lean_object* v_B_6451_; lean_object* v_h_6452_; lean_object* v_K_6453_; lean_object* v_k_6454_; lean_object* v_H_6455_; lean_object* v_m_6456_; lean_object* v_s_6457_; lean_object* v_S_6458_; lean_object* v_A_6459_; lean_object* v_n_6460_; lean_object* v_N_6461_; lean_object* v_V_6462_; lean_object* v_z_6463_; lean_object* v_zabbrev_6464_; lean_object* v_v_6465_; lean_object* v_O_6466_; lean_object* v_X_6467_; lean_object* v_x_6468_; lean_object* v_Z_6469_; lean_object* v___y_6471_; lean_object* v___y_6472_; lean_object* v___y_6473_; lean_object* v___y_6474_; lean_object* v___y_6475_; lean_object* v___y_6476_; lean_object* v___y_6477_; lean_object* v___y_6478_; lean_object* v___y_6487_; lean_object* v___y_6488_; lean_object* v___y_6489_; lean_object* v___y_6490_; lean_object* v___y_6491_; lean_object* v___y_6492_; lean_object* v___y_6493_; lean_object* v___y_6498_; lean_object* v___y_6499_; lean_object* v___y_6500_; lean_object* v___y_6501_; lean_object* v___y_6502_; lean_object* v___y_6503_; lean_object* v___y_6507_; lean_object* v___y_6508_; lean_object* v___y_6509_; lean_object* v___y_6510_; lean_object* v___y_6511_; lean_object* v___y_6515_; lean_object* v___y_6516_; lean_object* v___y_6517_; lean_object* v___y_6518_; lean_object* v___y_6526_; lean_object* v___y_6527_; lean_object* v___y_6528_; lean_object* v___y_6529_; uint8_t v_val_6530_; lean_object* v___y_6538_; lean_object* v___y_6539_; lean_object* v___y_6540_; lean_object* v___y_6541_; lean_object* v___y_6551_; lean_object* v___y_6552_; lean_object* v___y_6553_; uint8_t v___y_6554_; lean_object* v___y_6561_; lean_object* v___y_6562_; lean_object* v___y_6563_; lean_object* v___y_6568_; lean_object* v___y_6569_; lean_object* v___y_6573_; lean_object* v___y_6574_; lean_object* v___y_6575_; lean_object* v___y_6582_; lean_object* v___y_6583_; lean_object* v___y_6584_; lean_object* v___y_6589_; 
v_G_6442_ = lean_ctor_get(v_builder_6367_, 0);
lean_inc(v_G_6442_);
v_y_6443_ = lean_ctor_get(v_builder_6367_, 1);
lean_inc(v_y_6443_);
v_u_6444_ = lean_ctor_get(v_builder_6367_, 2);
lean_inc(v_u_6444_);
v_Y_6445_ = lean_ctor_get(v_builder_6367_, 3);
lean_inc(v_Y_6445_);
v_M_6446_ = lean_ctor_get(v_builder_6367_, 5);
lean_inc(v_M_6446_);
v_L_6447_ = lean_ctor_get(v_builder_6367_, 6);
lean_inc(v_L_6447_);
v_d_6448_ = lean_ctor_get(v_builder_6367_, 7);
lean_inc(v_d_6448_);
v_a_6449_ = lean_ctor_get(v_builder_6367_, 16);
lean_inc(v_a_6449_);
v_b_6450_ = lean_ctor_get(v_builder_6367_, 17);
lean_inc(v_b_6450_);
v_B_6451_ = lean_ctor_get(v_builder_6367_, 18);
lean_inc(v_B_6451_);
v_h_6452_ = lean_ctor_get(v_builder_6367_, 19);
lean_inc(v_h_6452_);
v_K_6453_ = lean_ctor_get(v_builder_6367_, 20);
lean_inc(v_K_6453_);
v_k_6454_ = lean_ctor_get(v_builder_6367_, 21);
lean_inc(v_k_6454_);
v_H_6455_ = lean_ctor_get(v_builder_6367_, 22);
lean_inc(v_H_6455_);
v_m_6456_ = lean_ctor_get(v_builder_6367_, 23);
lean_inc(v_m_6456_);
v_s_6457_ = lean_ctor_get(v_builder_6367_, 24);
lean_inc(v_s_6457_);
v_S_6458_ = lean_ctor_get(v_builder_6367_, 25);
lean_inc(v_S_6458_);
v_A_6459_ = lean_ctor_get(v_builder_6367_, 26);
lean_inc(v_A_6459_);
v_n_6460_ = lean_ctor_get(v_builder_6367_, 27);
lean_inc(v_n_6460_);
v_N_6461_ = lean_ctor_get(v_builder_6367_, 28);
lean_inc(v_N_6461_);
v_V_6462_ = lean_ctor_get(v_builder_6367_, 29);
lean_inc(v_V_6462_);
v_z_6463_ = lean_ctor_get(v_builder_6367_, 30);
lean_inc(v_z_6463_);
v_zabbrev_6464_ = lean_ctor_get(v_builder_6367_, 31);
lean_inc(v_zabbrev_6464_);
v_v_6465_ = lean_ctor_get(v_builder_6367_, 32);
lean_inc(v_v_6465_);
v_O_6466_ = lean_ctor_get(v_builder_6367_, 33);
lean_inc(v_O_6466_);
v_X_6467_ = lean_ctor_get(v_builder_6367_, 34);
lean_inc(v_X_6467_);
v_x_6468_ = lean_ctor_get(v_builder_6367_, 35);
lean_inc(v_x_6468_);
v_Z_6469_ = lean_ctor_get(v_builder_6367_, 36);
lean_inc(v_Z_6469_);
lean_dec_ref(v_builder_6367_);
if (lean_obj_tag(v_O_6466_) == 0)
{
if (lean_obj_tag(v_X_6467_) == 0)
{
if (lean_obj_tag(v_x_6468_) == 0)
{
if (lean_obj_tag(v_Z_6469_) == 0)
{
lean_object* v___x_6596_; 
v___x_6596_ = l_Std_Time_TimeZone_Offset_zero;
v___y_6589_ = v___x_6596_;
goto v___jp_6588_;
}
else
{
lean_object* v_val_6597_; 
v_val_6597_ = lean_ctor_get(v_Z_6469_, 0);
lean_inc(v_val_6597_);
lean_dec_ref_known(v_Z_6469_, 1);
v___y_6589_ = v_val_6597_;
goto v___jp_6588_;
}
}
else
{
lean_object* v_val_6598_; 
lean_dec(v_Z_6469_);
v_val_6598_ = lean_ctor_get(v_x_6468_, 0);
lean_inc(v_val_6598_);
lean_dec_ref_known(v_x_6468_, 1);
v___y_6589_ = v_val_6598_;
goto v___jp_6588_;
}
}
else
{
lean_object* v_val_6599_; 
lean_dec(v_Z_6469_);
lean_dec(v_x_6468_);
v_val_6599_ = lean_ctor_get(v_X_6467_, 0);
lean_inc(v_val_6599_);
lean_dec_ref_known(v_X_6467_, 1);
v___y_6589_ = v_val_6599_;
goto v___jp_6588_;
}
}
else
{
lean_object* v_val_6600_; 
lean_dec(v_Z_6469_);
lean_dec(v_x_6468_);
lean_dec(v_X_6467_);
v_val_6600_ = lean_ctor_get(v_O_6466_, 0);
lean_inc(v_val_6600_);
lean_dec_ref_known(v_O_6466_, 1);
v___y_6589_ = v_val_6600_;
goto v___jp_6588_;
}
v___jp_6369_:
{
if (lean_obj_tag(v___y_6370_) == 0)
{
lean_object* v___x_6372_; 
lean_dec_ref(v___y_6371_);
v___x_6372_ = lean_box(0);
return v___x_6372_;
}
else
{
lean_object* v_val_6373_; lean_object* v___x_6375_; uint8_t v_isShared_6376_; uint8_t v_isSharedCheck_6408_; 
v_val_6373_ = lean_ctor_get(v___y_6370_, 0);
v_isSharedCheck_6408_ = !lean_is_exclusive(v___y_6370_);
if (v_isSharedCheck_6408_ == 0)
{
v___x_6375_ = v___y_6370_;
v_isShared_6376_ = v_isSharedCheck_6408_;
goto v_resetjp_6374_;
}
else
{
lean_inc(v_val_6373_);
lean_dec(v___y_6370_);
v___x_6375_ = lean_box(0);
v_isShared_6376_ = v_isSharedCheck_6408_;
goto v_resetjp_6374_;
}
v_resetjp_6374_:
{
lean_object* v_offset_6377_; lean_object* v_name_6378_; lean_object* v_abbreviation_6379_; uint8_t v_isDST_6380_; uint8_t v___x_6381_; uint8_t v___x_6382_; lean_object* v_ltt_6383_; lean_object* v___x_6384_; lean_object* v___x_6385_; lean_object* v___x_6386_; lean_object* v_wt_6387_; lean_object* v_ltt_6388_; lean_object* v_tz_6389_; lean_object* v_offset_6390_; lean_object* v_second_6391_; lean_object* v_nano_6392_; lean_object* v___f_6393_; lean_object* v___x_6394_; lean_object* v___x_6395_; lean_object* v___x_6396_; lean_object* v___x_6397_; lean_object* v___x_6398_; lean_object* v_nanos_6399_; lean_object* v___x_6400_; lean_object* v_nanos_6401_; lean_object* v___x_6402_; lean_object* v___x_6403_; lean_object* v___x_6404_; lean_object* v___x_6406_; 
v_offset_6377_ = lean_ctor_get(v___y_6371_, 0);
lean_inc(v_offset_6377_);
v_name_6378_ = lean_ctor_get(v___y_6371_, 1);
lean_inc_ref(v_name_6378_);
v_abbreviation_6379_ = lean_ctor_get(v___y_6371_, 2);
lean_inc_ref(v_abbreviation_6379_);
v_isDST_6380_ = lean_ctor_get_uint8(v___y_6371_, sizeof(void*)*3);
lean_dec_ref(v___y_6371_);
v___x_6381_ = 0;
v___x_6382_ = 1;
v_ltt_6383_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6383_, 0, v_offset_6377_);
lean_ctor_set(v_ltt_6383_, 1, v_abbreviation_6379_);
lean_ctor_set(v_ltt_6383_, 2, v_name_6378_);
lean_ctor_set_uint8(v_ltt_6383_, sizeof(void*)*3, v_isDST_6380_);
lean_ctor_set_uint8(v_ltt_6383_, sizeof(void*)*3 + 1, v___x_6381_);
lean_ctor_set_uint8(v_ltt_6383_, sizeof(void*)*3 + 2, v___x_6382_);
v___x_6384_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6385_ = lean_box(0);
v___x_6386_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6386_, 0, v_ltt_6383_);
lean_ctor_set(v___x_6386_, 1, v___x_6384_);
lean_ctor_set(v___x_6386_, 2, v___x_6385_);
lean_inc(v_val_6373_);
v_wt_6387_ = l_Std_Time_PlainDateTime_toWallTime(v_val_6373_);
lean_inc_ref(v___x_6386_);
v_ltt_6388_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_6386_, v_wt_6387_);
v_tz_6389_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_6388_);
lean_dec_ref(v_ltt_6388_);
v_offset_6390_ = lean_ctor_get(v_tz_6389_, 0);
v_second_6391_ = lean_ctor_get(v_wt_6387_, 0);
lean_inc(v_second_6391_);
v_nano_6392_ = lean_ctor_get(v_wt_6387_, 1);
lean_inc(v_nano_6392_);
lean_dec_ref(v_wt_6387_);
v___f_6393_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed), 2, 1);
lean_closure_set(v___f_6393_, 0, v_val_6373_);
v___x_6394_ = lean_mk_thunk(v___f_6393_);
v___x_6395_ = lean_int_neg(v_offset_6390_);
v___x_6396_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1);
v___x_6397_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_6398_ = lean_int_mul(v_second_6391_, v___x_6397_);
lean_dec(v_second_6391_);
v_nanos_6399_ = lean_int_add(v___x_6398_, v_nano_6392_);
lean_dec(v_nano_6392_);
lean_dec(v___x_6398_);
v___x_6400_ = lean_int_mul(v___x_6395_, v___x_6397_);
lean_dec(v___x_6395_);
v_nanos_6401_ = lean_int_add(v___x_6400_, v___x_6396_);
lean_dec(v___x_6400_);
v___x_6402_ = lean_int_add(v_nanos_6399_, v_nanos_6401_);
lean_dec(v_nanos_6401_);
lean_dec(v_nanos_6399_);
v___x_6403_ = l_Std_Time_Duration_ofNanoseconds(v___x_6402_);
lean_dec(v___x_6402_);
v___x_6404_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6404_, 0, v___x_6394_);
lean_ctor_set(v___x_6404_, 1, v___x_6403_);
lean_ctor_set(v___x_6404_, 2, v___x_6386_);
lean_ctor_set(v___x_6404_, 3, v_tz_6389_);
if (v_isShared_6376_ == 0)
{
lean_ctor_set(v___x_6375_, 0, v___x_6404_);
v___x_6406_ = v___x_6375_;
goto v_reusejp_6405_;
}
else
{
lean_object* v_reuseFailAlloc_6407_; 
v_reuseFailAlloc_6407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6407_, 0, v___x_6404_);
v___x_6406_ = v_reuseFailAlloc_6407_;
goto v_reusejp_6405_;
}
v_reusejp_6405_:
{
return v___x_6406_;
}
}
}
}
v___jp_6409_:
{
if (lean_obj_tag(v_aw_6368_) == 0)
{
lean_object* v_a_6412_; 
lean_dec_ref(v___y_6410_);
v_a_6412_ = lean_ctor_get(v_aw_6368_, 0);
lean_inc_ref(v_a_6412_);
lean_dec_ref_known(v_aw_6368_, 1);
v___y_6370_ = v___y_6411_;
v___y_6371_ = v_a_6412_;
goto v___jp_6369_;
}
else
{
v___y_6370_ = v___y_6411_;
v___y_6371_ = v___y_6410_;
goto v___jp_6369_;
}
}
v___jp_6413_:
{
lean_object* v___x_6420_; uint8_t v___x_6421_; 
v___x_6420_ = l_Std_Time_Month_Ordinal_days(v___y_6419_, v___y_6417_);
v___x_6421_ = lean_int_dec_le(v___y_6416_, v___x_6420_);
lean_dec(v___x_6420_);
if (v___x_6421_ == 0)
{
lean_object* v___x_6422_; 
lean_dec(v___y_6417_);
lean_dec(v___y_6416_);
lean_dec(v___y_6415_);
lean_dec_ref(v___y_6414_);
v___x_6422_ = lean_box(0);
v___y_6410_ = v___y_6418_;
v___y_6411_ = v___x_6422_;
goto v___jp_6409_;
}
else
{
lean_object* v_date_6423_; lean_object* v___x_6424_; lean_object* v___x_6425_; 
v_date_6423_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_date_6423_, 0, v___y_6415_);
lean_ctor_set(v_date_6423_, 1, v___y_6417_);
lean_ctor_set(v_date_6423_, 2, v___y_6416_);
v___x_6424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6424_, 0, v_date_6423_);
lean_ctor_set(v___x_6424_, 1, v___y_6414_);
v___x_6425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6425_, 0, v___x_6424_);
v___y_6410_ = v___y_6418_;
v___y_6411_ = v___x_6425_;
goto v___jp_6409_;
}
}
v___jp_6426_:
{
lean_object* v___x_6432_; lean_object* v___x_6433_; lean_object* v___x_6434_; uint8_t v___x_6435_; 
v___x_6432_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_6433_ = lean_int_mod(v___y_6427_, v___x_6432_);
v___x_6434_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6435_ = lean_int_dec_eq(v___x_6433_, v___x_6434_);
lean_dec(v___x_6433_);
if (v___x_6435_ == 0)
{
v___y_6414_ = v___y_6431_;
v___y_6415_ = v___y_6427_;
v___y_6416_ = v___y_6429_;
v___y_6417_ = v___y_6428_;
v___y_6418_ = v___y_6430_;
v___y_6419_ = v___x_6435_;
goto v___jp_6413_;
}
else
{
lean_object* v___x_6436_; lean_object* v___x_6437_; uint8_t v___x_6438_; 
v___x_6436_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_6437_ = lean_int_mod(v___y_6427_, v___x_6436_);
v___x_6438_ = lean_int_dec_eq(v___x_6437_, v___x_6434_);
lean_dec(v___x_6437_);
if (v___x_6438_ == 0)
{
v___y_6414_ = v___y_6431_;
v___y_6415_ = v___y_6427_;
v___y_6416_ = v___y_6429_;
v___y_6417_ = v___y_6428_;
v___y_6418_ = v___y_6430_;
v___y_6419_ = v___x_6435_;
goto v___jp_6413_;
}
else
{
lean_object* v___x_6439_; lean_object* v___x_6440_; uint8_t v___x_6441_; 
v___x_6439_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_6440_ = lean_int_mod(v___y_6427_, v___x_6439_);
v___x_6441_ = lean_int_dec_eq(v___x_6440_, v___x_6434_);
lean_dec(v___x_6440_);
v___y_6414_ = v___y_6431_;
v___y_6415_ = v___y_6427_;
v___y_6416_ = v___y_6429_;
v___y_6417_ = v___y_6428_;
v___y_6418_ = v___y_6430_;
v___y_6419_ = v___x_6441_;
goto v___jp_6413_;
}
}
}
v___jp_6470_:
{
if (lean_obj_tag(v_N_6461_) == 0)
{
if (lean_obj_tag(v_A_6459_) == 0)
{
lean_object* v___x_6479_; 
v___x_6479_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6479_, 0, v___y_6476_);
lean_ctor_set(v___x_6479_, 1, v___y_6471_);
lean_ctor_set(v___x_6479_, 2, v___y_6477_);
lean_ctor_set(v___x_6479_, 3, v___y_6478_);
v___y_6427_ = v___y_6472_;
v___y_6428_ = v___y_6474_;
v___y_6429_ = v___y_6473_;
v___y_6430_ = v___y_6475_;
v___y_6431_ = v___x_6479_;
goto v___jp_6426_;
}
else
{
lean_object* v_val_6480_; lean_object* v___x_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; 
lean_dec(v___y_6478_);
lean_dec(v___y_6477_);
lean_dec(v___y_6476_);
lean_dec(v___y_6471_);
v_val_6480_ = lean_ctor_get(v_A_6459_, 0);
lean_inc(v_val_6480_);
lean_dec_ref_known(v_A_6459_, 1);
v___x_6481_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2);
v___x_6482_ = lean_int_mul(v_val_6480_, v___x_6481_);
lean_dec(v_val_6480_);
v___x_6483_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_6482_);
lean_dec(v___x_6482_);
v___y_6427_ = v___y_6472_;
v___y_6428_ = v___y_6474_;
v___y_6429_ = v___y_6473_;
v___y_6430_ = v___y_6475_;
v___y_6431_ = v___x_6483_;
goto v___jp_6426_;
}
}
else
{
lean_object* v_val_6484_; lean_object* v___x_6485_; 
lean_dec(v___y_6478_);
lean_dec(v___y_6477_);
lean_dec(v___y_6476_);
lean_dec(v___y_6471_);
lean_dec(v_A_6459_);
v_val_6484_ = lean_ctor_get(v_N_6461_, 0);
lean_inc(v_val_6484_);
lean_dec_ref_known(v_N_6461_, 1);
v___x_6485_ = l_Std_Time_PlainTime_ofNanoseconds(v_val_6484_);
lean_dec(v_val_6484_);
v___y_6427_ = v___y_6472_;
v___y_6428_ = v___y_6474_;
v___y_6429_ = v___y_6473_;
v___y_6430_ = v___y_6475_;
v___y_6431_ = v___x_6485_;
goto v___jp_6426_;
}
}
v___jp_6486_:
{
if (lean_obj_tag(v_n_6460_) == 0)
{
if (lean_obj_tag(v_S_6458_) == 0)
{
lean_object* v___x_6494_; 
v___x_6494_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6471_ = v___y_6487_;
v___y_6472_ = v___y_6488_;
v___y_6473_ = v___y_6490_;
v___y_6474_ = v___y_6489_;
v___y_6475_ = v___y_6492_;
v___y_6476_ = v___y_6491_;
v___y_6477_ = v___y_6493_;
v___y_6478_ = v___x_6494_;
goto v___jp_6470_;
}
else
{
lean_object* v_val_6495_; 
v_val_6495_ = lean_ctor_get(v_S_6458_, 0);
lean_inc(v_val_6495_);
lean_dec_ref_known(v_S_6458_, 1);
v___y_6471_ = v___y_6487_;
v___y_6472_ = v___y_6488_;
v___y_6473_ = v___y_6490_;
v___y_6474_ = v___y_6489_;
v___y_6475_ = v___y_6492_;
v___y_6476_ = v___y_6491_;
v___y_6477_ = v___y_6493_;
v___y_6478_ = v_val_6495_;
goto v___jp_6470_;
}
}
else
{
lean_object* v_val_6496_; 
lean_dec(v_S_6458_);
v_val_6496_ = lean_ctor_get(v_n_6460_, 0);
lean_inc(v_val_6496_);
lean_dec_ref_known(v_n_6460_, 1);
v___y_6471_ = v___y_6487_;
v___y_6472_ = v___y_6488_;
v___y_6473_ = v___y_6490_;
v___y_6474_ = v___y_6489_;
v___y_6475_ = v___y_6492_;
v___y_6476_ = v___y_6491_;
v___y_6477_ = v___y_6493_;
v___y_6478_ = v_val_6496_;
goto v___jp_6470_;
}
}
v___jp_6497_:
{
if (lean_obj_tag(v_s_6457_) == 0)
{
lean_object* v___x_6504_; 
v___x_6504_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3);
v___y_6487_ = v___y_6503_;
v___y_6488_ = v___y_6498_;
v___y_6489_ = v___y_6500_;
v___y_6490_ = v___y_6499_;
v___y_6491_ = v___y_6502_;
v___y_6492_ = v___y_6501_;
v___y_6493_ = v___x_6504_;
goto v___jp_6486_;
}
else
{
lean_object* v_val_6505_; 
v_val_6505_ = lean_ctor_get(v_s_6457_, 0);
lean_inc(v_val_6505_);
lean_dec_ref_known(v_s_6457_, 1);
v___y_6487_ = v___y_6503_;
v___y_6488_ = v___y_6498_;
v___y_6489_ = v___y_6500_;
v___y_6490_ = v___y_6499_;
v___y_6491_ = v___y_6502_;
v___y_6492_ = v___y_6501_;
v___y_6493_ = v_val_6505_;
goto v___jp_6486_;
}
}
v___jp_6506_:
{
if (lean_obj_tag(v_m_6456_) == 0)
{
lean_object* v___x_6512_; 
v___x_6512_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11);
v___y_6498_ = v___y_6507_;
v___y_6499_ = v___y_6509_;
v___y_6500_ = v___y_6508_;
v___y_6501_ = v___y_6510_;
v___y_6502_ = v___y_6511_;
v___y_6503_ = v___x_6512_;
goto v___jp_6497_;
}
else
{
lean_object* v_val_6513_; 
v_val_6513_ = lean_ctor_get(v_m_6456_, 0);
lean_inc(v_val_6513_);
lean_dec_ref_known(v_m_6456_, 1);
v___y_6498_ = v___y_6507_;
v___y_6499_ = v___y_6509_;
v___y_6500_ = v___y_6508_;
v___y_6501_ = v___y_6510_;
v___y_6502_ = v___y_6511_;
v___y_6503_ = v_val_6513_;
goto v___jp_6497_;
}
}
v___jp_6514_:
{
if (lean_obj_tag(v_k_6454_) == 0)
{
if (lean_obj_tag(v_H_6455_) == 0)
{
lean_object* v___x_6519_; 
v___x_6519_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6507_ = v___y_6515_;
v___y_6508_ = v___y_6517_;
v___y_6509_ = v___y_6516_;
v___y_6510_ = v___y_6518_;
v___y_6511_ = v___x_6519_;
goto v___jp_6506_;
}
else
{
lean_object* v_val_6520_; 
v_val_6520_ = lean_ctor_get(v_H_6455_, 0);
lean_inc(v_val_6520_);
lean_dec_ref_known(v_H_6455_, 1);
v___y_6507_ = v___y_6515_;
v___y_6508_ = v___y_6517_;
v___y_6509_ = v___y_6516_;
v___y_6510_ = v___y_6518_;
v___y_6511_ = v_val_6520_;
goto v___jp_6506_;
}
}
else
{
if (lean_obj_tag(v_H_6455_) == 0)
{
lean_object* v_val_6521_; lean_object* v___x_6522_; lean_object* v___x_6523_; 
v_val_6521_ = lean_ctor_get(v_k_6454_, 0);
lean_inc(v_val_6521_);
lean_dec_ref_known(v_k_6454_, 1);
v___x_6522_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12);
v___x_6523_ = lean_int_emod(v_val_6521_, v___x_6522_);
lean_dec(v_val_6521_);
v___y_6507_ = v___y_6515_;
v___y_6508_ = v___y_6517_;
v___y_6509_ = v___y_6516_;
v___y_6510_ = v___y_6518_;
v___y_6511_ = v___x_6523_;
goto v___jp_6506_;
}
else
{
lean_object* v_val_6524_; 
lean_dec_ref_known(v_k_6454_, 1);
v_val_6524_ = lean_ctor_get(v_H_6455_, 0);
lean_inc(v_val_6524_);
lean_dec_ref_known(v_H_6455_, 1);
v___y_6507_ = v___y_6515_;
v___y_6508_ = v___y_6517_;
v___y_6509_ = v___y_6516_;
v___y_6510_ = v___y_6518_;
v___y_6511_ = v_val_6524_;
goto v___jp_6506_;
}
}
}
v___jp_6525_:
{
if (lean_obj_tag(v_h_6452_) == 0)
{
if (lean_obj_tag(v_K_6453_) == 0)
{
v___y_6515_ = v___y_6526_;
v___y_6516_ = v___y_6528_;
v___y_6517_ = v___y_6527_;
v___y_6518_ = v___y_6529_;
goto v___jp_6514_;
}
else
{
lean_dec(v_H_6455_);
lean_dec(v_k_6454_);
if (v_val_6530_ == 0)
{
lean_object* v_val_6531_; 
v_val_6531_ = lean_ctor_get(v_K_6453_, 0);
lean_inc(v_val_6531_);
lean_dec_ref_known(v_K_6453_, 1);
v___y_6507_ = v___y_6526_;
v___y_6508_ = v___y_6527_;
v___y_6509_ = v___y_6528_;
v___y_6510_ = v___y_6529_;
v___y_6511_ = v_val_6531_;
goto v___jp_6506_;
}
else
{
lean_object* v_val_6532_; lean_object* v___x_6533_; lean_object* v___x_6534_; 
v_val_6532_ = lean_ctor_get(v_K_6453_, 0);
lean_inc(v_val_6532_);
lean_dec_ref_known(v_K_6453_, 1);
v___x_6533_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_6534_ = lean_int_add(v_val_6532_, v___x_6533_);
lean_dec(v_val_6532_);
v___y_6507_ = v___y_6526_;
v___y_6508_ = v___y_6527_;
v___y_6509_ = v___y_6528_;
v___y_6510_ = v___y_6529_;
v___y_6511_ = v___x_6534_;
goto v___jp_6506_;
}
}
}
else
{
lean_object* v_val_6535_; lean_object* v___x_6536_; 
lean_dec(v_H_6455_);
lean_dec(v_k_6454_);
lean_dec(v_K_6453_);
v_val_6535_ = lean_ctor_get(v_h_6452_, 0);
lean_inc(v_val_6535_);
lean_dec_ref_known(v_h_6452_, 1);
v___x_6536_ = l_Std_Time_HourMarker_toAbsolute(v_val_6530_, v_val_6535_);
lean_dec(v_val_6535_);
v___y_6507_ = v___y_6526_;
v___y_6508_ = v___y_6527_;
v___y_6509_ = v___y_6528_;
v___y_6510_ = v___y_6529_;
v___y_6511_ = v___x_6536_;
goto v___jp_6506_;
}
}
v___jp_6537_:
{
if (lean_obj_tag(v_a_6449_) == 0)
{
if (lean_obj_tag(v_b_6450_) == 0)
{
if (lean_obj_tag(v_B_6451_) == 0)
{
lean_dec(v_K_6453_);
lean_dec(v_h_6452_);
v___y_6515_ = v___y_6541_;
v___y_6516_ = v___y_6538_;
v___y_6517_ = v___y_6539_;
v___y_6518_ = v___y_6540_;
goto v___jp_6514_;
}
else
{
lean_object* v_val_6542_; uint8_t v___x_6543_; uint8_t v___x_6544_; 
v_val_6542_ = lean_ctor_get(v_B_6451_, 0);
lean_inc(v_val_6542_);
lean_dec_ref_known(v_B_6451_, 1);
v___x_6543_ = lean_unbox(v_val_6542_);
lean_dec(v_val_6542_);
v___x_6544_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v___x_6543_);
v___y_6526_ = v___y_6541_;
v___y_6527_ = v___y_6539_;
v___y_6528_ = v___y_6538_;
v___y_6529_ = v___y_6540_;
v_val_6530_ = v___x_6544_;
goto v___jp_6525_;
}
}
else
{
lean_object* v_val_6545_; uint8_t v___x_6546_; uint8_t v___x_6547_; 
lean_dec(v_B_6451_);
v_val_6545_ = lean_ctor_get(v_b_6450_, 0);
lean_inc(v_val_6545_);
lean_dec_ref_known(v_b_6450_, 1);
v___x_6546_ = lean_unbox(v_val_6545_);
lean_dec(v_val_6545_);
v___x_6547_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v___x_6546_);
v___y_6526_ = v___y_6541_;
v___y_6527_ = v___y_6539_;
v___y_6528_ = v___y_6538_;
v___y_6529_ = v___y_6540_;
v_val_6530_ = v___x_6547_;
goto v___jp_6525_;
}
}
else
{
lean_object* v_val_6548_; uint8_t v___x_6549_; 
lean_dec(v_B_6451_);
lean_dec(v_b_6450_);
v_val_6548_ = lean_ctor_get(v_a_6449_, 0);
lean_inc(v_val_6548_);
lean_dec_ref_known(v_a_6449_, 1);
v___x_6549_ = lean_unbox(v_val_6548_);
lean_dec(v_val_6548_);
v___y_6526_ = v___y_6541_;
v___y_6527_ = v___y_6539_;
v___y_6528_ = v___y_6538_;
v___y_6529_ = v___y_6540_;
v_val_6530_ = v___x_6549_;
goto v___jp_6525_;
}
}
v___jp_6550_:
{
if (lean_obj_tag(v_u_6444_) == 0)
{
if (lean_obj_tag(v_y_6443_) == 0)
{
if (lean_obj_tag(v_Y_6445_) == 0)
{
lean_object* v___x_6555_; 
v___x_6555_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6538_ = v___y_6552_;
v___y_6539_ = v___y_6551_;
v___y_6540_ = v___y_6553_;
v___y_6541_ = v___x_6555_;
goto v___jp_6537_;
}
else
{
lean_object* v_val_6556_; 
v_val_6556_ = lean_ctor_get(v_Y_6445_, 0);
lean_inc(v_val_6556_);
lean_dec_ref_known(v_Y_6445_, 1);
v___y_6538_ = v___y_6552_;
v___y_6539_ = v___y_6551_;
v___y_6540_ = v___y_6553_;
v___y_6541_ = v_val_6556_;
goto v___jp_6537_;
}
}
else
{
lean_object* v_val_6557_; lean_object* v___x_6558_; 
lean_dec(v_Y_6445_);
v_val_6557_ = lean_ctor_get(v_y_6443_, 0);
lean_inc(v_val_6557_);
lean_dec_ref_known(v_y_6443_, 1);
v___x_6558_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_val_6557_, v___y_6554_);
lean_dec(v_val_6557_);
v___y_6538_ = v___y_6552_;
v___y_6539_ = v___y_6551_;
v___y_6540_ = v___y_6553_;
v___y_6541_ = v___x_6558_;
goto v___jp_6537_;
}
}
else
{
lean_object* v_val_6559_; 
lean_dec(v_Y_6445_);
lean_dec(v_y_6443_);
v_val_6559_ = lean_ctor_get(v_u_6444_, 0);
lean_inc(v_val_6559_);
lean_dec_ref_known(v_u_6444_, 1);
v___y_6538_ = v___y_6552_;
v___y_6539_ = v___y_6551_;
v___y_6540_ = v___y_6553_;
v___y_6541_ = v_val_6559_;
goto v___jp_6537_;
}
}
v___jp_6560_:
{
if (lean_obj_tag(v_G_6442_) == 0)
{
uint8_t v___x_6564_; 
v___x_6564_ = 1;
v___y_6551_ = v___y_6561_;
v___y_6552_ = v___y_6563_;
v___y_6553_ = v___y_6562_;
v___y_6554_ = v___x_6564_;
goto v___jp_6550_;
}
else
{
lean_object* v_val_6565_; uint8_t v___x_6566_; 
v_val_6565_ = lean_ctor_get(v_G_6442_, 0);
lean_inc(v_val_6565_);
lean_dec_ref_known(v_G_6442_, 1);
v___x_6566_ = lean_unbox(v_val_6565_);
lean_dec(v_val_6565_);
v___y_6551_ = v___y_6561_;
v___y_6552_ = v___y_6563_;
v___y_6553_ = v___y_6562_;
v___y_6554_ = v___x_6566_;
goto v___jp_6550_;
}
}
v___jp_6567_:
{
if (lean_obj_tag(v_d_6448_) == 0)
{
lean_object* v___x_6570_; 
v___x_6570_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21);
v___y_6561_ = v___y_6569_;
v___y_6562_ = v___y_6568_;
v___y_6563_ = v___x_6570_;
goto v___jp_6560_;
}
else
{
lean_object* v_val_6571_; 
v_val_6571_ = lean_ctor_get(v_d_6448_, 0);
lean_inc(v_val_6571_);
lean_dec_ref_known(v_d_6448_, 1);
v___y_6561_ = v___y_6569_;
v___y_6562_ = v___y_6568_;
v___y_6563_ = v_val_6571_;
goto v___jp_6560_;
}
}
v___jp_6572_:
{
uint8_t v___x_6576_; lean_object* v_tz_6577_; 
v___x_6576_ = 0;
v_tz_6577_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_tz_6577_, 0, v___y_6574_);
lean_ctor_set(v_tz_6577_, 1, v___y_6573_);
lean_ctor_set(v_tz_6577_, 2, v___y_6575_);
lean_ctor_set_uint8(v_tz_6577_, sizeof(void*)*3, v___x_6576_);
if (lean_obj_tag(v_M_6446_) == 0)
{
if (lean_obj_tag(v_L_6447_) == 0)
{
lean_object* v___x_6578_; 
v___x_6578_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__29);
v___y_6568_ = v_tz_6577_;
v___y_6569_ = v___x_6578_;
goto v___jp_6567_;
}
else
{
lean_object* v_val_6579_; 
v_val_6579_ = lean_ctor_get(v_L_6447_, 0);
lean_inc(v_val_6579_);
lean_dec_ref_known(v_L_6447_, 1);
v___y_6568_ = v_tz_6577_;
v___y_6569_ = v_val_6579_;
goto v___jp_6567_;
}
}
else
{
lean_object* v_val_6580_; 
lean_dec(v_L_6447_);
v_val_6580_ = lean_ctor_get(v_M_6446_, 0);
lean_inc(v_val_6580_);
lean_dec_ref_known(v_M_6446_, 1);
v___y_6568_ = v_tz_6577_;
v___y_6569_ = v_val_6580_;
goto v___jp_6567_;
}
}
v___jp_6581_:
{
if (lean_obj_tag(v_zabbrev_6464_) == 0)
{
lean_object* v___x_6585_; lean_object* v___x_6586_; 
v___x_6585_ = lean_box(0);
v___x_6586_ = lean_apply_1(v___y_6583_, v___x_6585_);
v___y_6573_ = v___y_6584_;
v___y_6574_ = v___y_6582_;
v___y_6575_ = v___x_6586_;
goto v___jp_6572_;
}
else
{
lean_object* v_val_6587_; 
lean_dec_ref(v___y_6583_);
v_val_6587_ = lean_ctor_get(v_zabbrev_6464_, 0);
lean_inc(v_val_6587_);
lean_dec_ref_known(v_zabbrev_6464_, 1);
v___y_6573_ = v___y_6584_;
v___y_6574_ = v___y_6582_;
v___y_6575_ = v_val_6587_;
goto v___jp_6572_;
}
}
v___jp_6588_:
{
lean_object* v___f_6590_; 
lean_inc(v___y_6589_);
v___f_6590_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1), 2, 1);
lean_closure_set(v___f_6590_, 0, v___y_6589_);
if (lean_obj_tag(v_V_6462_) == 0)
{
if (lean_obj_tag(v_v_6465_) == 0)
{
if (lean_obj_tag(v_z_6463_) == 0)
{
lean_object* v___x_6591_; lean_object* v___x_6592_; 
v___x_6591_ = lean_box(0);
lean_inc(v___y_6589_);
v___x_6592_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(v___y_6589_, v___x_6591_);
v___y_6582_ = v___y_6589_;
v___y_6583_ = v___f_6590_;
v___y_6584_ = v___x_6592_;
goto v___jp_6581_;
}
else
{
lean_object* v_val_6593_; 
v_val_6593_ = lean_ctor_get(v_z_6463_, 0);
lean_inc(v_val_6593_);
lean_dec_ref_known(v_z_6463_, 1);
v___y_6582_ = v___y_6589_;
v___y_6583_ = v___f_6590_;
v___y_6584_ = v_val_6593_;
goto v___jp_6581_;
}
}
else
{
lean_object* v_val_6594_; 
lean_dec(v_z_6463_);
v_val_6594_ = lean_ctor_get(v_v_6465_, 0);
lean_inc(v_val_6594_);
lean_dec_ref_known(v_v_6465_, 1);
v___y_6582_ = v___y_6589_;
v___y_6583_ = v___f_6590_;
v___y_6584_ = v_val_6594_;
goto v___jp_6581_;
}
}
else
{
lean_object* v_val_6595_; 
lean_dec(v_v_6465_);
lean_dec(v_z_6463_);
v_val_6595_ = lean_ctor_get(v_V_6462_, 0);
lean_inc(v_val_6595_);
lean_dec_ref_known(v_V_6462_, 1);
v___y_6582_ = v___y_6589_;
v___y_6583_ = v___f_6590_;
v___y_6584_ = v_val_6595_;
goto v___jp_6581_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(lean_object* v_date_6601_, lean_object* v_config_6602_, lean_object* v_mod_6603_, lean_object* v_a_6604_){
_start:
{
if (lean_obj_tag(v_mod_6603_) == 0)
{
lean_object* v_val_6605_; lean_object* v___x_6606_; 
lean_dec_ref(v_config_6602_);
v_val_6605_ = lean_ctor_get(v_mod_6603_, 0);
lean_inc_ref(v_val_6605_);
lean_dec_ref_known(v_mod_6603_, 1);
v___x_6606_ = l_Std_Internal_Parsec_String_pstring(v_val_6605_, v_a_6604_);
if (lean_obj_tag(v___x_6606_) == 0)
{
lean_object* v_pos_6607_; lean_object* v___x_6609_; uint8_t v_isShared_6610_; uint8_t v_isSharedCheck_6614_; 
v_pos_6607_ = lean_ctor_get(v___x_6606_, 0);
v_isSharedCheck_6614_ = !lean_is_exclusive(v___x_6606_);
if (v_isSharedCheck_6614_ == 0)
{
lean_object* v_unused_6615_; 
v_unused_6615_ = lean_ctor_get(v___x_6606_, 1);
lean_dec(v_unused_6615_);
v___x_6609_ = v___x_6606_;
v_isShared_6610_ = v_isSharedCheck_6614_;
goto v_resetjp_6608_;
}
else
{
lean_inc(v_pos_6607_);
lean_dec(v___x_6606_);
v___x_6609_ = lean_box(0);
v_isShared_6610_ = v_isSharedCheck_6614_;
goto v_resetjp_6608_;
}
v_resetjp_6608_:
{
lean_object* v___x_6612_; 
if (v_isShared_6610_ == 0)
{
lean_ctor_set(v___x_6609_, 1, v_date_6601_);
v___x_6612_ = v___x_6609_;
goto v_reusejp_6611_;
}
else
{
lean_object* v_reuseFailAlloc_6613_; 
v_reuseFailAlloc_6613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6613_, 0, v_pos_6607_);
lean_ctor_set(v_reuseFailAlloc_6613_, 1, v_date_6601_);
v___x_6612_ = v_reuseFailAlloc_6613_;
goto v_reusejp_6611_;
}
v_reusejp_6611_:
{
return v___x_6612_;
}
}
}
else
{
lean_object* v_pos_6616_; lean_object* v_err_6617_; lean_object* v___x_6619_; uint8_t v_isShared_6620_; uint8_t v_isSharedCheck_6624_; 
lean_dec_ref(v_date_6601_);
v_pos_6616_ = lean_ctor_get(v___x_6606_, 0);
v_err_6617_ = lean_ctor_get(v___x_6606_, 1);
v_isSharedCheck_6624_ = !lean_is_exclusive(v___x_6606_);
if (v_isSharedCheck_6624_ == 0)
{
v___x_6619_ = v___x_6606_;
v_isShared_6620_ = v_isSharedCheck_6624_;
goto v_resetjp_6618_;
}
else
{
lean_inc(v_err_6617_);
lean_inc(v_pos_6616_);
lean_dec(v___x_6606_);
v___x_6619_ = lean_box(0);
v_isShared_6620_ = v_isSharedCheck_6624_;
goto v_resetjp_6618_;
}
v_resetjp_6618_:
{
lean_object* v___x_6622_; 
if (v_isShared_6620_ == 0)
{
v___x_6622_ = v___x_6619_;
goto v_reusejp_6621_;
}
else
{
lean_object* v_reuseFailAlloc_6623_; 
v_reuseFailAlloc_6623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6623_, 0, v_pos_6616_);
lean_ctor_set(v_reuseFailAlloc_6623_, 1, v_err_6617_);
v___x_6622_ = v_reuseFailAlloc_6623_;
goto v_reusejp_6621_;
}
v_reusejp_6621_:
{
return v___x_6622_;
}
}
}
}
else
{
lean_object* v_modifier_6625_; lean_object* v___x_6626_; 
v_modifier_6625_ = lean_ctor_get(v_mod_6603_, 0);
lean_inc_ref_n(v_modifier_6625_, 2);
lean_dec_ref_known(v_mod_6603_, 1);
v___x_6626_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_6602_, v_modifier_6625_, v_a_6604_);
if (lean_obj_tag(v___x_6626_) == 0)
{
lean_object* v_pos_6627_; lean_object* v_res_6628_; lean_object* v___x_6630_; uint8_t v_isShared_6631_; uint8_t v_isSharedCheck_6636_; 
v_pos_6627_ = lean_ctor_get(v___x_6626_, 0);
v_res_6628_ = lean_ctor_get(v___x_6626_, 1);
v_isSharedCheck_6636_ = !lean_is_exclusive(v___x_6626_);
if (v_isSharedCheck_6636_ == 0)
{
v___x_6630_ = v___x_6626_;
v_isShared_6631_ = v_isSharedCheck_6636_;
goto v_resetjp_6629_;
}
else
{
lean_inc(v_res_6628_);
lean_inc(v_pos_6627_);
lean_dec(v___x_6626_);
v___x_6630_ = lean_box(0);
v_isShared_6631_ = v_isSharedCheck_6636_;
goto v_resetjp_6629_;
}
v_resetjp_6629_:
{
lean_object* v___x_6632_; lean_object* v___x_6634_; 
v___x_6632_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(v_date_6601_, v_modifier_6625_, v_res_6628_);
if (v_isShared_6631_ == 0)
{
lean_ctor_set(v___x_6630_, 1, v___x_6632_);
v___x_6634_ = v___x_6630_;
goto v_reusejp_6633_;
}
else
{
lean_object* v_reuseFailAlloc_6635_; 
v_reuseFailAlloc_6635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6635_, 0, v_pos_6627_);
lean_ctor_set(v_reuseFailAlloc_6635_, 1, v___x_6632_);
v___x_6634_ = v_reuseFailAlloc_6635_;
goto v_reusejp_6633_;
}
v_reusejp_6633_:
{
return v___x_6634_;
}
}
}
else
{
lean_object* v_pos_6637_; lean_object* v_err_6638_; lean_object* v___x_6640_; uint8_t v_isShared_6641_; uint8_t v_isSharedCheck_6645_; 
lean_dec_ref(v_modifier_6625_);
lean_dec_ref(v_date_6601_);
v_pos_6637_ = lean_ctor_get(v___x_6626_, 0);
v_err_6638_ = lean_ctor_get(v___x_6626_, 1);
v_isSharedCheck_6645_ = !lean_is_exclusive(v___x_6626_);
if (v_isSharedCheck_6645_ == 0)
{
v___x_6640_ = v___x_6626_;
v_isShared_6641_ = v_isSharedCheck_6645_;
goto v_resetjp_6639_;
}
else
{
lean_inc(v_err_6638_);
lean_inc(v_pos_6637_);
lean_dec(v___x_6626_);
v___x_6640_ = lean_box(0);
v_isShared_6641_ = v_isSharedCheck_6645_;
goto v_resetjp_6639_;
}
v_resetjp_6639_:
{
lean_object* v___x_6643_; 
if (v_isShared_6641_ == 0)
{
v___x_6643_ = v___x_6640_;
goto v_reusejp_6642_;
}
else
{
lean_object* v_reuseFailAlloc_6644_; 
v_reuseFailAlloc_6644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6644_, 0, v_pos_6637_);
lean_ctor_set(v_reuseFailAlloc_6644_, 1, v_err_6638_);
v___x_6643_ = v_reuseFailAlloc_6644_;
goto v_reusejp_6642_;
}
v_reusejp_6642_:
{
return v___x_6643_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___redArg(lean_object* v_input_6646_, lean_object* v_config_6647_){
_start:
{
lean_object* v___x_6648_; lean_object* v___x_6649_; 
v___x_6648_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6649_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6648_, v_input_6646_);
if (lean_obj_tag(v___x_6649_) == 0)
{
lean_object* v_a_6650_; lean_object* v___x_6652_; uint8_t v_isShared_6653_; uint8_t v_isSharedCheck_6657_; 
lean_dec_ref(v_config_6647_);
v_a_6650_ = lean_ctor_get(v___x_6649_, 0);
v_isSharedCheck_6657_ = !lean_is_exclusive(v___x_6649_);
if (v_isSharedCheck_6657_ == 0)
{
v___x_6652_ = v___x_6649_;
v_isShared_6653_ = v_isSharedCheck_6657_;
goto v_resetjp_6651_;
}
else
{
lean_inc(v_a_6650_);
lean_dec(v___x_6649_);
v___x_6652_ = lean_box(0);
v_isShared_6653_ = v_isSharedCheck_6657_;
goto v_resetjp_6651_;
}
v_resetjp_6651_:
{
lean_object* v___x_6655_; 
if (v_isShared_6653_ == 0)
{
v___x_6655_ = v___x_6652_;
goto v_reusejp_6654_;
}
else
{
lean_object* v_reuseFailAlloc_6656_; 
v_reuseFailAlloc_6656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6656_, 0, v_a_6650_);
v___x_6655_ = v_reuseFailAlloc_6656_;
goto v_reusejp_6654_;
}
v_reusejp_6654_:
{
return v___x_6655_;
}
}
}
else
{
lean_object* v_a_6658_; lean_object* v___x_6660_; uint8_t v_isShared_6661_; uint8_t v_isSharedCheck_6666_; 
v_a_6658_ = lean_ctor_get(v___x_6649_, 0);
v_isSharedCheck_6666_ = !lean_is_exclusive(v___x_6649_);
if (v_isSharedCheck_6666_ == 0)
{
v___x_6660_ = v___x_6649_;
v_isShared_6661_ = v_isSharedCheck_6666_;
goto v_resetjp_6659_;
}
else
{
lean_inc(v_a_6658_);
lean_dec(v___x_6649_);
v___x_6660_ = lean_box(0);
v_isShared_6661_ = v_isSharedCheck_6666_;
goto v_resetjp_6659_;
}
v_resetjp_6659_:
{
lean_object* v___x_6662_; lean_object* v___x_6664_; 
v___x_6662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6662_, 0, v_config_6647_);
lean_ctor_set(v___x_6662_, 1, v_a_6658_);
if (v_isShared_6661_ == 0)
{
lean_ctor_set(v___x_6660_, 0, v___x_6662_);
v___x_6664_ = v___x_6660_;
goto v_reusejp_6663_;
}
else
{
lean_object* v_reuseFailAlloc_6665_; 
v_reuseFailAlloc_6665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6665_, 0, v___x_6662_);
v___x_6664_ = v_reuseFailAlloc_6665_;
goto v_reusejp_6663_;
}
v_reusejp_6663_:
{
return v___x_6664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec(lean_object* v_tz_6667_, lean_object* v_input_6668_, lean_object* v_config_6669_){
_start:
{
lean_object* v___x_6670_; 
v___x_6670_ = l_Std_Time_GenericFormat_spec___redArg(v_input_6668_, v_config_6669_);
return v___x_6670_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___boxed(lean_object* v_tz_6671_, lean_object* v_input_6672_, lean_object* v_config_6673_){
_start:
{
lean_object* v_res_6674_; 
v_res_6674_ = l_Std_Time_GenericFormat_spec(v_tz_6671_, v_input_6672_, v_config_6673_);
lean_dec(v_tz_6671_);
return v_res_6674_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(lean_object* v_msg_6675_){
_start:
{
lean_object* v___x_6676_; lean_object* v___x_6677_; 
v___x_6676_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0);
v___x_6677_ = lean_panic_fn_borrowed(v___x_6676_, v_msg_6675_);
return v___x_6677_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(lean_object* v_tz_6678_, lean_object* v_msg_6679_){
_start:
{
lean_object* v___x_6680_; 
v___x_6680_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(v_msg_6679_);
return v___x_6680_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___boxed(lean_object* v_tz_6681_, lean_object* v_msg_6682_){
_start:
{
lean_object* v_res_6683_; 
v_res_6683_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(v_tz_6681_, v_msg_6682_);
lean_dec(v_tz_6681_);
return v_res_6683_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21(lean_object* v_tz_6686_, lean_object* v_input_6687_, lean_object* v_config_6688_){
_start:
{
lean_object* v___x_6689_; lean_object* v___x_6690_; 
v___x_6689_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6690_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6689_, v_input_6687_);
if (lean_obj_tag(v___x_6690_) == 0)
{
lean_object* v_a_6691_; lean_object* v___x_6692_; lean_object* v___x_6693_; lean_object* v___x_6694_; lean_object* v___x_6695_; lean_object* v___x_6696_; lean_object* v___x_6697_; 
lean_dec_ref(v_config_6688_);
v_a_6691_ = lean_ctor_get(v___x_6690_, 0);
lean_inc(v_a_6691_);
lean_dec_ref_known(v___x_6690_, 1);
v___x_6692_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_6693_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__1));
v___x_6694_ = lean_unsigned_to_nat(1076u);
v___x_6695_ = lean_unsigned_to_nat(18u);
v___x_6696_ = l_mkPanicMessageWithDecl(v___x_6692_, v___x_6693_, v___x_6694_, v___x_6695_, v_a_6691_);
lean_dec(v_a_6691_);
v___x_6697_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(v___x_6696_);
return v___x_6697_;
}
else
{
lean_object* v_a_6698_; lean_object* v___x_6699_; 
v_a_6698_ = lean_ctor_get(v___x_6690_, 0);
lean_inc(v_a_6698_);
lean_dec_ref_known(v___x_6690_, 1);
v___x_6699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6699_, 0, v_config_6688_);
lean_ctor_set(v___x_6699_, 1, v_a_6698_);
return v___x_6699_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21___boxed(lean_object* v_tz_6700_, lean_object* v_input_6701_, lean_object* v_config_6702_){
_start:
{
lean_object* v_res_6703_; 
v_res_6703_ = l_Std_Time_GenericFormat_spec_x21(v_tz_6700_, v_input_6701_, v_config_6702_);
lean_dec(v_tz_6700_);
return v_res_6703_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(lean_object* v_x_6704_, lean_object* v_x_6705_){
_start:
{
if (lean_obj_tag(v_x_6705_) == 0)
{
return v_x_6704_;
}
else
{
lean_object* v_head_6706_; lean_object* v_tail_6707_; lean_object* v___x_6708_; 
v_head_6706_ = lean_ctor_get(v_x_6705_, 0);
v_tail_6707_ = lean_ctor_get(v_x_6705_, 1);
v___x_6708_ = lean_string_append(v_x_6704_, v_head_6706_);
v_x_6704_ = v___x_6708_;
v_x_6705_ = v_tail_6707_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1___boxed(lean_object* v_x_6710_, lean_object* v_x_6711_){
_start:
{
lean_object* v_res_6712_; 
v_res_6712_ = l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(v_x_6710_, v_x_6711_);
lean_dec(v_x_6711_);
return v_res_6712_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0(lean_object* v_tz_6713_, lean_object* v_timestamp_6714_, lean_object* v___x_6715_, lean_object* v_x_6716_){
_start:
{
lean_object* v_offset_6717_; lean_object* v_second_6718_; lean_object* v_nano_6719_; lean_object* v___x_6720_; lean_object* v___x_6721_; lean_object* v___x_6722_; lean_object* v_nanos_6723_; lean_object* v___x_6724_; lean_object* v_nanos_6725_; lean_object* v___x_6726_; lean_object* v___x_6727_; lean_object* v___x_6728_; 
v_offset_6717_ = lean_ctor_get(v_tz_6713_, 0);
v_second_6718_ = lean_ctor_get(v_timestamp_6714_, 0);
v_nano_6719_ = lean_ctor_get(v_timestamp_6714_, 1);
v___x_6720_ = lean_nat_to_int(v___x_6715_);
v___x_6721_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_6722_ = lean_int_mul(v_second_6718_, v___x_6721_);
v_nanos_6723_ = lean_int_add(v___x_6722_, v_nano_6719_);
lean_dec(v___x_6722_);
v___x_6724_ = lean_int_mul(v_offset_6717_, v___x_6721_);
v_nanos_6725_ = lean_int_add(v___x_6724_, v___x_6720_);
lean_dec(v___x_6720_);
lean_dec(v___x_6724_);
v___x_6726_ = lean_int_add(v_nanos_6723_, v_nanos_6725_);
lean_dec(v_nanos_6725_);
lean_dec(v_nanos_6723_);
v___x_6727_ = l_Std_Time_Duration_ofNanoseconds(v___x_6726_);
lean_dec(v___x_6726_);
v___x_6728_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_6727_);
return v___x_6728_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed(lean_object* v_tz_6729_, lean_object* v_timestamp_6730_, lean_object* v___x_6731_, lean_object* v_x_6732_){
_start:
{
lean_object* v_res_6733_; 
v_res_6733_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0(v_tz_6729_, v_timestamp_6730_, v___x_6731_, v_x_6732_);
lean_dec_ref(v_timestamp_6730_);
lean_dec_ref(v_tz_6729_);
return v_res_6733_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0_spec__0(lean_object* v_aw_6734_, lean_object* v_date_6735_, lean_object* v_dateformat_6736_, lean_object* v_a_6737_, lean_object* v_a_6738_){
_start:
{
if (lean_obj_tag(v_a_6737_) == 0)
{
lean_object* v___x_6739_; 
lean_dec_ref(v_date_6735_);
v___x_6739_ = l_List_reverse___redArg(v_a_6738_);
return v___x_6739_;
}
else
{
lean_object* v_head_6740_; lean_object* v_tail_6741_; lean_object* v___x_6743_; uint8_t v_isShared_6744_; uint8_t v_isSharedCheck_6770_; 
v_head_6740_ = lean_ctor_get(v_a_6737_, 0);
v_tail_6741_ = lean_ctor_get(v_a_6737_, 1);
v_isSharedCheck_6770_ = !lean_is_exclusive(v_a_6737_);
if (v_isSharedCheck_6770_ == 0)
{
v___x_6743_ = v_a_6737_;
v_isShared_6744_ = v_isSharedCheck_6770_;
goto v_resetjp_6742_;
}
else
{
lean_inc(v_tail_6741_);
lean_inc(v_head_6740_);
lean_dec(v_a_6737_);
v___x_6743_ = lean_box(0);
v_isShared_6744_ = v_isSharedCheck_6770_;
goto v_resetjp_6742_;
}
v_resetjp_6742_:
{
lean_object* v___y_6746_; 
if (lean_obj_tag(v_aw_6734_) == 0)
{
lean_object* v_a_6751_; lean_object* v_offset_6752_; lean_object* v_name_6753_; lean_object* v_abbreviation_6754_; uint8_t v_isDST_6755_; lean_object* v_timestamp_6756_; uint8_t v___x_6757_; uint8_t v___x_6758_; lean_object* v_ltt_6759_; lean_object* v___x_6760_; lean_object* v___x_6761_; lean_object* v___x_6762_; lean_object* v___x_6763_; lean_object* v_tz_6764_; lean_object* v___f_6765_; lean_object* v___x_6766_; lean_object* v___x_6767_; lean_object* v___x_6768_; 
v_a_6751_ = lean_ctor_get(v_aw_6734_, 0);
v_offset_6752_ = lean_ctor_get(v_a_6751_, 0);
v_name_6753_ = lean_ctor_get(v_a_6751_, 1);
v_abbreviation_6754_ = lean_ctor_get(v_a_6751_, 2);
v_isDST_6755_ = lean_ctor_get_uint8(v_a_6751_, sizeof(void*)*3);
v_timestamp_6756_ = lean_ctor_get(v_date_6735_, 1);
v___x_6757_ = 0;
v___x_6758_ = 1;
lean_inc_ref(v_name_6753_);
lean_inc_ref(v_abbreviation_6754_);
lean_inc(v_offset_6752_);
v_ltt_6759_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6759_, 0, v_offset_6752_);
lean_ctor_set(v_ltt_6759_, 1, v_abbreviation_6754_);
lean_ctor_set(v_ltt_6759_, 2, v_name_6753_);
lean_ctor_set_uint8(v_ltt_6759_, sizeof(void*)*3, v_isDST_6755_);
lean_ctor_set_uint8(v_ltt_6759_, sizeof(void*)*3 + 1, v___x_6757_);
lean_ctor_set_uint8(v_ltt_6759_, sizeof(void*)*3 + 2, v___x_6758_);
v___x_6760_ = lean_unsigned_to_nat(0u);
v___x_6761_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6762_ = lean_box(0);
v___x_6763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6763_, 0, v_ltt_6759_);
lean_ctor_set(v___x_6763_, 1, v___x_6761_);
lean_ctor_set(v___x_6763_, 2, v___x_6762_);
lean_inc_ref(v___x_6763_);
v_tz_6764_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_6763_, v_timestamp_6756_);
lean_inc_ref_n(v_timestamp_6756_, 2);
lean_inc_ref(v_tz_6764_);
v___f_6765_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_6765_, 0, v_tz_6764_);
lean_closure_set(v___f_6765_, 1, v_timestamp_6756_);
lean_closure_set(v___f_6765_, 2, v___x_6760_);
v___x_6766_ = lean_mk_thunk(v___f_6765_);
v___x_6767_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6767_, 0, v___x_6766_);
lean_ctor_set(v___x_6767_, 1, v_timestamp_6756_);
lean_ctor_set(v___x_6767_, 2, v___x_6763_);
lean_ctor_set(v___x_6767_, 3, v_tz_6764_);
v___x_6768_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6736_, v___x_6767_, v_head_6740_);
v___y_6746_ = v___x_6768_;
goto v___jp_6745_;
}
else
{
lean_object* v___x_6769_; 
lean_inc_ref(v_date_6735_);
v___x_6769_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6736_, v_date_6735_, v_head_6740_);
v___y_6746_ = v___x_6769_;
goto v___jp_6745_;
}
v___jp_6745_:
{
lean_object* v___x_6748_; 
if (v_isShared_6744_ == 0)
{
lean_ctor_set(v___x_6743_, 1, v_a_6738_);
lean_ctor_set(v___x_6743_, 0, v___y_6746_);
v___x_6748_ = v___x_6743_;
goto v_reusejp_6747_;
}
else
{
lean_object* v_reuseFailAlloc_6750_; 
v_reuseFailAlloc_6750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6750_, 0, v___y_6746_);
lean_ctor_set(v_reuseFailAlloc_6750_, 1, v_a_6738_);
v___x_6748_ = v_reuseFailAlloc_6750_;
goto v_reusejp_6747_;
}
v_reusejp_6747_:
{
v_a_6737_ = v_tail_6741_;
v_a_6738_ = v___x_6748_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0_spec__0___boxed(lean_object* v_aw_6771_, lean_object* v_date_6772_, lean_object* v_dateformat_6773_, lean_object* v_a_6774_, lean_object* v_a_6775_){
_start:
{
lean_object* v_res_6776_; 
v_res_6776_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0_spec__0(v_aw_6771_, v_date_6772_, v_dateformat_6773_, v_a_6774_, v_a_6775_);
lean_dec_ref(v_dateformat_6773_);
lean_dec(v_aw_6771_);
return v_res_6776_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(lean_object* v_aw_6777_, lean_object* v_date_6778_, lean_object* v_dateformat_6779_, lean_object* v_a_6780_, lean_object* v_a_6781_){
_start:
{
if (lean_obj_tag(v_a_6780_) == 0)
{
lean_object* v___x_6782_; 
lean_dec_ref(v_date_6778_);
v___x_6782_ = l_List_reverse___redArg(v_a_6781_);
return v___x_6782_;
}
else
{
lean_object* v_head_6783_; lean_object* v_tail_6784_; lean_object* v___x_6786_; uint8_t v_isShared_6787_; uint8_t v_isSharedCheck_6813_; 
v_head_6783_ = lean_ctor_get(v_a_6780_, 0);
v_tail_6784_ = lean_ctor_get(v_a_6780_, 1);
v_isSharedCheck_6813_ = !lean_is_exclusive(v_a_6780_);
if (v_isSharedCheck_6813_ == 0)
{
v___x_6786_ = v_a_6780_;
v_isShared_6787_ = v_isSharedCheck_6813_;
goto v_resetjp_6785_;
}
else
{
lean_inc(v_tail_6784_);
lean_inc(v_head_6783_);
lean_dec(v_a_6780_);
v___x_6786_ = lean_box(0);
v_isShared_6787_ = v_isSharedCheck_6813_;
goto v_resetjp_6785_;
}
v_resetjp_6785_:
{
lean_object* v___y_6789_; 
if (lean_obj_tag(v_aw_6777_) == 0)
{
lean_object* v_a_6794_; lean_object* v_offset_6795_; lean_object* v_name_6796_; lean_object* v_abbreviation_6797_; uint8_t v_isDST_6798_; lean_object* v_timestamp_6799_; uint8_t v___x_6800_; uint8_t v___x_6801_; lean_object* v_ltt_6802_; lean_object* v___x_6803_; lean_object* v___x_6804_; lean_object* v___x_6805_; lean_object* v___x_6806_; lean_object* v_tz_6807_; lean_object* v___f_6808_; lean_object* v___x_6809_; lean_object* v___x_6810_; lean_object* v___x_6811_; 
v_a_6794_ = lean_ctor_get(v_aw_6777_, 0);
v_offset_6795_ = lean_ctor_get(v_a_6794_, 0);
v_name_6796_ = lean_ctor_get(v_a_6794_, 1);
v_abbreviation_6797_ = lean_ctor_get(v_a_6794_, 2);
v_isDST_6798_ = lean_ctor_get_uint8(v_a_6794_, sizeof(void*)*3);
v_timestamp_6799_ = lean_ctor_get(v_date_6778_, 1);
v___x_6800_ = 0;
v___x_6801_ = 1;
lean_inc_ref(v_name_6796_);
lean_inc_ref(v_abbreviation_6797_);
lean_inc(v_offset_6795_);
v_ltt_6802_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6802_, 0, v_offset_6795_);
lean_ctor_set(v_ltt_6802_, 1, v_abbreviation_6797_);
lean_ctor_set(v_ltt_6802_, 2, v_name_6796_);
lean_ctor_set_uint8(v_ltt_6802_, sizeof(void*)*3, v_isDST_6798_);
lean_ctor_set_uint8(v_ltt_6802_, sizeof(void*)*3 + 1, v___x_6800_);
lean_ctor_set_uint8(v_ltt_6802_, sizeof(void*)*3 + 2, v___x_6801_);
v___x_6803_ = lean_unsigned_to_nat(0u);
v___x_6804_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6805_ = lean_box(0);
v___x_6806_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6806_, 0, v_ltt_6802_);
lean_ctor_set(v___x_6806_, 1, v___x_6804_);
lean_ctor_set(v___x_6806_, 2, v___x_6805_);
lean_inc_ref(v___x_6806_);
v_tz_6807_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_6806_, v_timestamp_6799_);
lean_inc_ref_n(v_timestamp_6799_, 2);
lean_inc_ref(v_tz_6807_);
v___f_6808_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_6808_, 0, v_tz_6807_);
lean_closure_set(v___f_6808_, 1, v_timestamp_6799_);
lean_closure_set(v___f_6808_, 2, v___x_6803_);
v___x_6809_ = lean_mk_thunk(v___f_6808_);
v___x_6810_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6810_, 0, v___x_6809_);
lean_ctor_set(v___x_6810_, 1, v_timestamp_6799_);
lean_ctor_set(v___x_6810_, 2, v___x_6806_);
lean_ctor_set(v___x_6810_, 3, v_tz_6807_);
v___x_6811_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6779_, v___x_6810_, v_head_6783_);
v___y_6789_ = v___x_6811_;
goto v___jp_6788_;
}
else
{
lean_object* v___x_6812_; 
lean_inc_ref(v_date_6778_);
v___x_6812_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6779_, v_date_6778_, v_head_6783_);
v___y_6789_ = v___x_6812_;
goto v___jp_6788_;
}
v___jp_6788_:
{
lean_object* v___x_6791_; 
if (v_isShared_6787_ == 0)
{
lean_ctor_set(v___x_6786_, 1, v_a_6781_);
lean_ctor_set(v___x_6786_, 0, v___y_6789_);
v___x_6791_ = v___x_6786_;
goto v_reusejp_6790_;
}
else
{
lean_object* v_reuseFailAlloc_6793_; 
v_reuseFailAlloc_6793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6793_, 0, v___y_6789_);
lean_ctor_set(v_reuseFailAlloc_6793_, 1, v_a_6781_);
v___x_6791_ = v_reuseFailAlloc_6793_;
goto v_reusejp_6790_;
}
v_reusejp_6790_:
{
lean_object* v___x_6792_; 
v___x_6792_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0_spec__0(v_aw_6777_, v_date_6778_, v_dateformat_6779_, v_tail_6784_, v___x_6791_);
return v___x_6792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___boxed(lean_object* v_aw_6814_, lean_object* v_date_6815_, lean_object* v_dateformat_6816_, lean_object* v_a_6817_, lean_object* v_a_6818_){
_start:
{
lean_object* v_res_6819_; 
v_res_6819_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(v_aw_6814_, v_date_6815_, v_dateformat_6816_, v_a_6817_, v_a_6818_);
lean_dec_ref(v_dateformat_6816_);
lean_dec(v_aw_6814_);
return v_res_6819_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format(lean_object* v_aw_6820_, lean_object* v_format_6821_, lean_object* v_date_6822_){
_start:
{
lean_object* v_config_6823_; lean_object* v_string_6824_; lean_object* v_dateformat_6825_; lean_object* v___x_6826_; lean_object* v___x_6827_; lean_object* v___x_6828_; lean_object* v___x_6829_; 
v_config_6823_ = lean_ctor_get(v_format_6821_, 0);
lean_inc_ref(v_config_6823_);
v_string_6824_ = lean_ctor_get(v_format_6821_, 1);
lean_inc(v_string_6824_);
lean_dec_ref(v_format_6821_);
v_dateformat_6825_ = lean_ctor_get(v_config_6823_, 0);
lean_inc_ref(v_dateformat_6825_);
lean_dec_ref(v_config_6823_);
v___x_6826_ = lean_box(0);
v___x_6827_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(v_aw_6820_, v_date_6822_, v_dateformat_6825_, v_string_6824_, v___x_6826_);
lean_dec_ref(v_dateformat_6825_);
v___x_6828_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_6829_ = l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(v___x_6828_, v___x_6827_);
lean_dec(v___x_6827_);
return v___x_6829_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format___boxed(lean_object* v_aw_6830_, lean_object* v_format_6831_, lean_object* v_date_6832_){
_start:
{
lean_object* v_res_6833_; 
v_res_6833_ = l_Std_Time_GenericFormat_format(v_aw_6830_, v_format_6831_, v_date_6832_);
lean_dec(v_aw_6830_);
return v_res_6833_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(lean_object* v_config_6837_, lean_object* v_aw_6838_, lean_object* v_builder_6839_, lean_object* v_x_6840_, lean_object* v_a_6841_){
_start:
{
if (lean_obj_tag(v_x_6840_) == 0)
{
lean_object* v___x_6842_; 
lean_dec_ref(v_config_6837_);
v___x_6842_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(v_builder_6839_, v_aw_6838_);
if (lean_obj_tag(v___x_6842_) == 0)
{
lean_object* v___x_6843_; lean_object* v___x_6844_; 
v___x_6843_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go___closed__1));
v___x_6844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6844_, 0, v_a_6841_);
lean_ctor_set(v___x_6844_, 1, v___x_6843_);
return v___x_6844_;
}
else
{
lean_object* v_val_6845_; lean_object* v___x_6846_; 
v_val_6845_ = lean_ctor_get(v___x_6842_, 0);
lean_inc(v_val_6845_);
lean_dec_ref_known(v___x_6842_, 1);
v___x_6846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6846_, 0, v_a_6841_);
lean_ctor_set(v___x_6846_, 1, v_val_6845_);
return v___x_6846_;
}
}
else
{
lean_object* v_head_6847_; lean_object* v_tail_6848_; lean_object* v___x_6849_; 
v_head_6847_ = lean_ctor_get(v_x_6840_, 0);
lean_inc(v_head_6847_);
v_tail_6848_ = lean_ctor_get(v_x_6840_, 1);
lean_inc(v_tail_6848_);
lean_dec_ref_known(v_x_6840_, 2);
lean_inc_ref(v_config_6837_);
v___x_6849_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(v_builder_6839_, v_config_6837_, v_head_6847_, v_a_6841_);
if (lean_obj_tag(v___x_6849_) == 0)
{
lean_object* v_pos_6850_; lean_object* v_res_6851_; 
v_pos_6850_ = lean_ctor_get(v___x_6849_, 0);
lean_inc(v_pos_6850_);
v_res_6851_ = lean_ctor_get(v___x_6849_, 1);
lean_inc(v_res_6851_);
lean_dec_ref_known(v___x_6849_, 2);
v_builder_6839_ = v_res_6851_;
v_x_6840_ = v_tail_6848_;
v_a_6841_ = v_pos_6850_;
goto _start;
}
else
{
lean_object* v_pos_6853_; lean_object* v_err_6854_; lean_object* v___x_6856_; uint8_t v_isShared_6857_; uint8_t v_isSharedCheck_6861_; 
lean_dec(v_tail_6848_);
lean_dec(v_aw_6838_);
lean_dec_ref(v_config_6837_);
v_pos_6853_ = lean_ctor_get(v___x_6849_, 0);
v_err_6854_ = lean_ctor_get(v___x_6849_, 1);
v_isSharedCheck_6861_ = !lean_is_exclusive(v___x_6849_);
if (v_isSharedCheck_6861_ == 0)
{
v___x_6856_ = v___x_6849_;
v_isShared_6857_ = v_isSharedCheck_6861_;
goto v_resetjp_6855_;
}
else
{
lean_inc(v_err_6854_);
lean_inc(v_pos_6853_);
lean_dec(v___x_6849_);
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(lean_object* v_format_6864_, lean_object* v_config_6865_, lean_object* v_aw_6866_, lean_object* v_a_6867_){
_start:
{
lean_object* v___x_6868_; lean_object* v___x_6869_; 
v___x_6868_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser___closed__0));
v___x_6869_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(v_config_6865_, v_aw_6866_, v___x_6868_, v_format_6864_, v_a_6867_);
return v___x_6869_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(lean_object* v_config_6873_, lean_object* v_format_6874_, lean_object* v_func_6875_, lean_object* v_a_6876_){
_start:
{
if (lean_obj_tag(v_format_6874_) == 0)
{
lean_dec_ref(v_config_6873_);
if (lean_obj_tag(v_func_6875_) == 0)
{
lean_object* v___x_6877_; lean_object* v___x_6878_; 
v___x_6877_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg___closed__1));
v___x_6878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6878_, 0, v_a_6876_);
lean_ctor_set(v___x_6878_, 1, v___x_6877_);
return v___x_6878_;
}
else
{
lean_object* v_val_6879_; lean_object* v_fst_6880_; lean_object* v_snd_6881_; lean_object* v___x_6882_; uint8_t v_decide_6883_; 
v_val_6879_ = lean_ctor_get(v_func_6875_, 0);
lean_inc(v_val_6879_);
lean_dec_ref_known(v_func_6875_, 1);
v_fst_6880_ = lean_ctor_get(v_a_6876_, 0);
v_snd_6881_ = lean_ctor_get(v_a_6876_, 1);
v___x_6882_ = lean_string_utf8_byte_size(v_fst_6880_);
v_decide_6883_ = lean_nat_dec_eq(v_snd_6881_, v___x_6882_);
if (v_decide_6883_ == 0)
{
lean_object* v___x_6884_; lean_object* v___x_6885_; 
lean_dec(v_val_6879_);
v___x_6884_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
v___x_6885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6885_, 0, v_a_6876_);
lean_ctor_set(v___x_6885_, 1, v___x_6884_);
return v___x_6885_;
}
else
{
lean_object* v___x_6886_; 
v___x_6886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6886_, 0, v_a_6876_);
lean_ctor_set(v___x_6886_, 1, v_val_6879_);
return v___x_6886_;
}
}
}
else
{
lean_object* v_head_6887_; 
v_head_6887_ = lean_ctor_get(v_format_6874_, 0);
lean_inc(v_head_6887_);
if (lean_obj_tag(v_head_6887_) == 0)
{
lean_object* v_tail_6888_; lean_object* v_val_6889_; lean_object* v___x_6890_; 
v_tail_6888_ = lean_ctor_get(v_format_6874_, 1);
lean_inc(v_tail_6888_);
lean_dec_ref_known(v_format_6874_, 2);
v_val_6889_ = lean_ctor_get(v_head_6887_, 0);
lean_inc_ref(v_val_6889_);
lean_dec_ref_known(v_head_6887_, 1);
v___x_6890_ = l_Std_Internal_Parsec_String_pstring(v_val_6889_, v_a_6876_);
if (lean_obj_tag(v___x_6890_) == 0)
{
lean_object* v_pos_6891_; 
v_pos_6891_ = lean_ctor_get(v___x_6890_, 0);
lean_inc(v_pos_6891_);
lean_dec_ref_known(v___x_6890_, 2);
v_format_6874_ = v_tail_6888_;
v_a_6876_ = v_pos_6891_;
goto _start;
}
else
{
lean_object* v_pos_6893_; lean_object* v_err_6894_; lean_object* v___x_6896_; uint8_t v_isShared_6897_; uint8_t v_isSharedCheck_6901_; 
lean_dec(v_tail_6888_);
lean_dec(v_func_6875_);
lean_dec_ref(v_config_6873_);
v_pos_6893_ = lean_ctor_get(v___x_6890_, 0);
v_err_6894_ = lean_ctor_get(v___x_6890_, 1);
v_isSharedCheck_6901_ = !lean_is_exclusive(v___x_6890_);
if (v_isSharedCheck_6901_ == 0)
{
v___x_6896_ = v___x_6890_;
v_isShared_6897_ = v_isSharedCheck_6901_;
goto v_resetjp_6895_;
}
else
{
lean_inc(v_err_6894_);
lean_inc(v_pos_6893_);
lean_dec(v___x_6890_);
v___x_6896_ = lean_box(0);
v_isShared_6897_ = v_isSharedCheck_6901_;
goto v_resetjp_6895_;
}
v_resetjp_6895_:
{
lean_object* v___x_6899_; 
if (v_isShared_6897_ == 0)
{
v___x_6899_ = v___x_6896_;
goto v_reusejp_6898_;
}
else
{
lean_object* v_reuseFailAlloc_6900_; 
v_reuseFailAlloc_6900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6900_, 0, v_pos_6893_);
lean_ctor_set(v_reuseFailAlloc_6900_, 1, v_err_6894_);
v___x_6899_ = v_reuseFailAlloc_6900_;
goto v_reusejp_6898_;
}
v_reusejp_6898_:
{
return v___x_6899_;
}
}
}
}
else
{
lean_object* v_tail_6902_; lean_object* v_modifier_6903_; lean_object* v___x_6904_; 
v_tail_6902_ = lean_ctor_get(v_format_6874_, 1);
lean_inc(v_tail_6902_);
lean_dec_ref_known(v_format_6874_, 2);
v_modifier_6903_ = lean_ctor_get(v_head_6887_, 0);
lean_inc_ref(v_modifier_6903_);
lean_dec_ref_known(v_head_6887_, 1);
lean_inc_ref(v_config_6873_);
v___x_6904_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_6873_, v_modifier_6903_, v_a_6876_);
if (lean_obj_tag(v___x_6904_) == 0)
{
lean_object* v_pos_6905_; lean_object* v_res_6906_; lean_object* v___x_6907_; 
v_pos_6905_ = lean_ctor_get(v___x_6904_, 0);
lean_inc(v_pos_6905_);
v_res_6906_ = lean_ctor_get(v___x_6904_, 1);
lean_inc(v_res_6906_);
lean_dec_ref_known(v___x_6904_, 2);
v___x_6907_ = lean_apply_1(v_func_6875_, v_res_6906_);
v_format_6874_ = v_tail_6902_;
v_func_6875_ = v___x_6907_;
v_a_6876_ = v_pos_6905_;
goto _start;
}
else
{
lean_object* v_pos_6909_; lean_object* v_err_6910_; lean_object* v___x_6912_; uint8_t v_isShared_6913_; uint8_t v_isSharedCheck_6917_; 
lean_dec(v_tail_6902_);
lean_dec(v_func_6875_);
lean_dec_ref(v_config_6873_);
v_pos_6909_ = lean_ctor_get(v___x_6904_, 0);
v_err_6910_ = lean_ctor_get(v___x_6904_, 1);
v_isSharedCheck_6917_ = !lean_is_exclusive(v___x_6904_);
if (v_isSharedCheck_6917_ == 0)
{
v___x_6912_ = v___x_6904_;
v_isShared_6913_ = v_isSharedCheck_6917_;
goto v_resetjp_6911_;
}
else
{
lean_inc(v_err_6910_);
lean_inc(v_pos_6909_);
lean_dec(v___x_6904_);
v___x_6912_ = lean_box(0);
v_isShared_6913_ = v_isSharedCheck_6917_;
goto v_resetjp_6911_;
}
v_resetjp_6911_:
{
lean_object* v___x_6915_; 
if (v_isShared_6913_ == 0)
{
v___x_6915_ = v___x_6912_;
goto v_reusejp_6914_;
}
else
{
lean_object* v_reuseFailAlloc_6916_; 
v_reuseFailAlloc_6916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6916_, 0, v_pos_6909_);
lean_ctor_set(v_reuseFailAlloc_6916_, 1, v_err_6910_);
v___x_6915_ = v_reuseFailAlloc_6916_;
goto v_reusejp_6914_;
}
v_reusejp_6914_:
{
return v___x_6915_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go(lean_object* v_00_u03b1_6918_, lean_object* v_config_6919_, lean_object* v_format_6920_, lean_object* v_func_6921_, lean_object* v_a_6922_){
_start:
{
lean_object* v___x_6923_; 
v___x_6923_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_6919_, v_format_6920_, v_func_6921_, v_a_6922_);
return v___x_6923_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser___redArg(lean_object* v_format_6924_, lean_object* v_config_6925_, lean_object* v_func_6926_, lean_object* v_a_6927_){
_start:
{
lean_object* v___x_6928_; 
v___x_6928_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_6925_, v_format_6924_, v_func_6926_, v_a_6927_);
return v___x_6928_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser(lean_object* v_00_u03b1_6929_, lean_object* v_format_6930_, lean_object* v_config_6931_, lean_object* v_func_6932_, lean_object* v_a_6933_){
_start:
{
lean_object* v___x_6934_; 
v___x_6934_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_6931_, v_format_6930_, v_func_6932_, v_a_6933_);
return v___x_6934_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse___lam__0(lean_object* v_string_6935_, lean_object* v_config_6936_, lean_object* v_aw_6937_, lean_object* v___y_6938_){
_start:
{
lean_object* v___x_6939_; 
v___x_6939_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(v_string_6935_, v_config_6936_, v_aw_6937_, v___y_6938_);
if (lean_obj_tag(v___x_6939_) == 0)
{
lean_object* v_pos_6940_; lean_object* v_fst_6941_; lean_object* v_snd_6942_; lean_object* v___x_6943_; uint8_t v_decide_6944_; 
v_pos_6940_ = lean_ctor_get(v___x_6939_, 0);
v_fst_6941_ = lean_ctor_get(v_pos_6940_, 0);
v_snd_6942_ = lean_ctor_get(v_pos_6940_, 1);
v___x_6943_ = lean_string_utf8_byte_size(v_fst_6941_);
v_decide_6944_ = lean_nat_dec_eq(v_snd_6942_, v___x_6943_);
if (v_decide_6944_ == 0)
{
lean_object* v___x_6946_; uint8_t v_isShared_6947_; uint8_t v_isSharedCheck_6952_; 
lean_inc(v_pos_6940_);
v_isSharedCheck_6952_ = !lean_is_exclusive(v___x_6939_);
if (v_isSharedCheck_6952_ == 0)
{
lean_object* v_unused_6953_; lean_object* v_unused_6954_; 
v_unused_6953_ = lean_ctor_get(v___x_6939_, 1);
lean_dec(v_unused_6953_);
v_unused_6954_ = lean_ctor_get(v___x_6939_, 0);
lean_dec(v_unused_6954_);
v___x_6946_ = v___x_6939_;
v_isShared_6947_ = v_isSharedCheck_6952_;
goto v_resetjp_6945_;
}
else
{
lean_dec(v___x_6939_);
v___x_6946_ = lean_box(0);
v_isShared_6947_ = v_isSharedCheck_6952_;
goto v_resetjp_6945_;
}
v_resetjp_6945_:
{
lean_object* v___x_6948_; lean_object* v___x_6950_; 
v___x_6948_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_6947_ == 0)
{
lean_ctor_set_tag(v___x_6946_, 1);
lean_ctor_set(v___x_6946_, 1, v___x_6948_);
v___x_6950_ = v___x_6946_;
goto v_reusejp_6949_;
}
else
{
lean_object* v_reuseFailAlloc_6951_; 
v_reuseFailAlloc_6951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6951_, 0, v_pos_6940_);
lean_ctor_set(v_reuseFailAlloc_6951_, 1, v___x_6948_);
v___x_6950_ = v_reuseFailAlloc_6951_;
goto v_reusejp_6949_;
}
v_reusejp_6949_:
{
return v___x_6950_;
}
}
}
else
{
return v___x_6939_;
}
}
else
{
return v___x_6939_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse(lean_object* v_aw_6955_, lean_object* v_format_6956_, lean_object* v_input_6957_){
_start:
{
lean_object* v_config_6958_; lean_object* v_string_6959_; lean_object* v___f_6960_; lean_object* v___x_6961_; 
v_config_6958_ = lean_ctor_get(v_format_6956_, 0);
lean_inc_ref(v_config_6958_);
v_string_6959_ = lean_ctor_get(v_format_6956_, 1);
lean_inc(v_string_6959_);
lean_dec_ref(v_format_6956_);
v___f_6960_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parse___lam__0), 4, 3);
lean_closure_set(v___f_6960_, 0, v_string_6959_);
lean_closure_set(v___f_6960_, 1, v_config_6958_);
lean_closure_set(v___f_6960_, 2, v_aw_6955_);
v___x_6961_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_6960_, v_input_6957_);
return v___x_6961_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(lean_object* v_msg_6962_){
_start:
{
lean_object* v___x_6963_; lean_object* v___x_6964_; 
v___x_6963_ = l_Std_Time_instInhabitedDateTime;
v___x_6964_ = lean_panic_fn_borrowed(v___x_6963_, v_msg_6962_);
return v___x_6964_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse_x21(lean_object* v_aw_6966_, lean_object* v_format_6967_, lean_object* v_input_6968_){
_start:
{
lean_object* v___x_6969_; 
v___x_6969_ = l_Std_Time_GenericFormat_parse(v_aw_6966_, v_format_6967_, v_input_6968_);
if (lean_obj_tag(v___x_6969_) == 0)
{
lean_object* v_a_6970_; lean_object* v___x_6971_; lean_object* v___x_6972_; lean_object* v___x_6973_; lean_object* v___x_6974_; lean_object* v___x_6975_; lean_object* v___x_6976_; 
v_a_6970_ = lean_ctor_get(v___x_6969_, 0);
lean_inc(v_a_6970_);
lean_dec_ref_known(v___x_6969_, 1);
v___x_6971_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_6972_ = ((lean_object*)(l_Std_Time_GenericFormat_parse_x21___closed__0));
v___x_6973_ = lean_unsigned_to_nat(1129u);
v___x_6974_ = lean_unsigned_to_nat(18u);
v___x_6975_ = l_mkPanicMessageWithDecl(v___x_6971_, v___x_6972_, v___x_6973_, v___x_6974_, v_a_6970_);
lean_dec(v_a_6970_);
v___x_6976_ = l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(v___x_6975_);
return v___x_6976_;
}
else
{
lean_object* v_a_6977_; 
v_a_6977_ = lean_ctor_get(v___x_6969_, 0);
lean_inc(v_a_6977_);
lean_dec_ref_known(v___x_6969_, 1);
return v_a_6977_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0(lean_object* v_config_6978_, lean_object* v_string_6979_, lean_object* v_builder_6980_, lean_object* v___y_6981_){
_start:
{
lean_object* v___x_6982_; 
v___x_6982_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_6978_, v_string_6979_, v_builder_6980_, v___y_6981_);
return v___x_6982_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg(lean_object* v_format_6983_, lean_object* v_builder_6984_, lean_object* v_input_6985_){
_start:
{
lean_object* v_config_6986_; lean_object* v_string_6987_; lean_object* v___f_6988_; lean_object* v___x_6989_; 
v_config_6986_ = lean_ctor_get(v_format_6983_, 0);
lean_inc_ref(v_config_6986_);
v_string_6987_ = lean_ctor_get(v_format_6983_, 1);
lean_inc(v_string_6987_);
lean_dec_ref(v_format_6983_);
v___f_6988_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0), 4, 3);
lean_closure_set(v___f_6988_, 0, v_config_6986_);
lean_closure_set(v___f_6988_, 1, v_string_6987_);
lean_closure_set(v___f_6988_, 2, v_builder_6984_);
v___x_6989_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_6988_, v_input_6985_);
return v___x_6989_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder(lean_object* v_aw_6990_, lean_object* v_00_u03b1_6991_, lean_object* v_format_6992_, lean_object* v_builder_6993_, lean_object* v_input_6994_){
_start:
{
lean_object* v___x_6995_; 
v___x_6995_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_6992_, v_builder_6993_, v_input_6994_);
return v___x_6995_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___boxed(lean_object* v_aw_6996_, lean_object* v_00_u03b1_6997_, lean_object* v_format_6998_, lean_object* v_builder_6999_, lean_object* v_input_7000_){
_start:
{
lean_object* v_res_7001_; 
v_res_7001_ = l_Std_Time_GenericFormat_parseBuilder(v_aw_6996_, v_00_u03b1_6997_, v_format_6998_, v_builder_6999_, v_input_7000_);
lean_dec(v_aw_6996_);
return v_res_7001_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg(lean_object* v_inst_7003_, lean_object* v_format_7004_, lean_object* v_builder_7005_, lean_object* v_input_7006_){
_start:
{
lean_object* v___x_7007_; 
v___x_7007_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_7004_, v_builder_7005_, v_input_7006_);
if (lean_obj_tag(v___x_7007_) == 0)
{
lean_object* v_a_7008_; lean_object* v___x_7009_; lean_object* v___x_7010_; lean_object* v___x_7011_; lean_object* v___x_7012_; lean_object* v___x_7013_; lean_object* v___x_7014_; 
v_a_7008_ = lean_ctor_get(v___x_7007_, 0);
lean_inc(v_a_7008_);
lean_dec_ref_known(v___x_7007_, 1);
v___x_7009_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_7010_ = ((lean_object*)(l_Std_Time_GenericFormat_parseBuilder_x21___redArg___closed__0));
v___x_7011_ = lean_unsigned_to_nat(1143u);
v___x_7012_ = lean_unsigned_to_nat(18u);
v___x_7013_ = l_mkPanicMessageWithDecl(v___x_7009_, v___x_7010_, v___x_7011_, v___x_7012_, v_a_7008_);
lean_dec(v_a_7008_);
v___x_7014_ = l_panic___redArg(v_inst_7003_, v___x_7013_);
return v___x_7014_;
}
else
{
lean_object* v_a_7015_; 
v_a_7015_ = lean_ctor_get(v___x_7007_, 0);
lean_inc(v_a_7015_);
lean_dec_ref_known(v___x_7007_, 1);
return v_a_7015_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg___boxed(lean_object* v_inst_7016_, lean_object* v_format_7017_, lean_object* v_builder_7018_, lean_object* v_input_7019_){
_start:
{
lean_object* v_res_7020_; 
v_res_7020_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7016_, v_format_7017_, v_builder_7018_, v_input_7019_);
lean_dec(v_inst_7016_);
return v_res_7020_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21(lean_object* v_00_u03b1_7021_, lean_object* v_aw_7022_, lean_object* v_inst_7023_, lean_object* v_format_7024_, lean_object* v_builder_7025_, lean_object* v_input_7026_){
_start:
{
lean_object* v___x_7027_; 
v___x_7027_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7023_, v_format_7024_, v_builder_7025_, v_input_7026_);
return v___x_7027_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___boxed(lean_object* v_00_u03b1_7028_, lean_object* v_aw_7029_, lean_object* v_inst_7030_, lean_object* v_format_7031_, lean_object* v_builder_7032_, lean_object* v_input_7033_){
_start:
{
lean_object* v_res_7034_; 
v_res_7034_ = l_Std_Time_GenericFormat_parseBuilder_x21(v_00_u03b1_7028_, v_aw_7029_, v_inst_7030_, v_format_7031_, v_builder_7032_, v_input_7033_);
lean_dec(v_inst_7030_);
lean_dec(v_aw_7029_);
return v_res_7034_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(lean_object* v_getInfo_7035_, lean_object* v_dateformat_7036_, lean_object* v_data_7037_, lean_object* v_format_7038_){
_start:
{
if (lean_obj_tag(v_format_7038_) == 0)
{
lean_object* v___x_7039_; 
lean_dec_ref(v_getInfo_7035_);
v___x_7039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7039_, 0, v_data_7037_);
return v___x_7039_;
}
else
{
lean_object* v_head_7040_; 
v_head_7040_ = lean_ctor_get(v_format_7038_, 0);
lean_inc(v_head_7040_);
if (lean_obj_tag(v_head_7040_) == 0)
{
lean_object* v_tail_7041_; lean_object* v_val_7042_; lean_object* v___x_7043_; 
v_tail_7041_ = lean_ctor_get(v_format_7038_, 1);
lean_inc(v_tail_7041_);
lean_dec_ref_known(v_format_7038_, 2);
v_val_7042_ = lean_ctor_get(v_head_7040_, 0);
lean_inc_ref(v_val_7042_);
lean_dec_ref_known(v_head_7040_, 1);
v___x_7043_ = lean_string_append(v_data_7037_, v_val_7042_);
lean_dec_ref(v_val_7042_);
v_data_7037_ = v___x_7043_;
v_format_7038_ = v_tail_7041_;
goto _start;
}
else
{
lean_object* v_tail_7045_; lean_object* v_modifier_7046_; lean_object* v___x_7047_; 
v_tail_7045_ = lean_ctor_get(v_format_7038_, 1);
lean_inc(v_tail_7045_);
lean_dec_ref_known(v_format_7038_, 2);
v_modifier_7046_ = lean_ctor_get(v_head_7040_, 0);
lean_inc_ref_n(v_modifier_7046_, 2);
lean_dec_ref_known(v_head_7040_, 1);
lean_inc_ref(v_getInfo_7035_);
v___x_7047_ = lean_apply_1(v_getInfo_7035_, v_modifier_7046_);
if (lean_obj_tag(v___x_7047_) == 0)
{
lean_object* v___x_7048_; 
lean_dec_ref(v_modifier_7046_);
lean_dec(v_tail_7045_);
lean_dec_ref(v_data_7037_);
lean_dec_ref(v_getInfo_7035_);
v___x_7048_ = lean_box(0);
return v___x_7048_;
}
else
{
lean_object* v_val_7049_; lean_object* v___x_7050_; lean_object* v___x_7051_; 
v_val_7049_ = lean_ctor_get(v___x_7047_, 0);
lean_inc(v_val_7049_);
lean_dec_ref_known(v___x_7047_, 1);
v___x_7050_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7036_, v_modifier_7046_, v_val_7049_);
v___x_7051_ = lean_string_append(v_data_7037_, v___x_7050_);
lean_dec_ref(v___x_7050_);
v_data_7037_ = v___x_7051_;
v_format_7038_ = v_tail_7045_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go___boxed(lean_object* v_getInfo_7053_, lean_object* v_dateformat_7054_, lean_object* v_data_7055_, lean_object* v_format_7056_){
_start:
{
lean_object* v_res_7057_; 
v_res_7057_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(v_getInfo_7053_, v_dateformat_7054_, v_data_7055_, v_format_7056_);
lean_dec_ref(v_dateformat_7054_);
return v_res_7057_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___redArg(lean_object* v_format_7058_, lean_object* v_getInfo_7059_){
_start:
{
lean_object* v_config_7060_; lean_object* v_string_7061_; lean_object* v_dateformat_7062_; lean_object* v___x_7063_; lean_object* v___x_7064_; 
v_config_7060_ = lean_ctor_get(v_format_7058_, 0);
lean_inc_ref(v_config_7060_);
v_string_7061_ = lean_ctor_get(v_format_7058_, 1);
lean_inc(v_string_7061_);
lean_dec_ref(v_format_7058_);
v_dateformat_7062_ = lean_ctor_get(v_config_7060_, 0);
lean_inc_ref(v_dateformat_7062_);
lean_dec_ref(v_config_7060_);
v___x_7063_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_7064_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(v_getInfo_7059_, v_dateformat_7062_, v___x_7063_, v_string_7061_);
lean_dec_ref(v_dateformat_7062_);
return v___x_7064_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric(lean_object* v_aw_7065_, lean_object* v_format_7066_, lean_object* v_getInfo_7067_){
_start:
{
lean_object* v___x_7068_; 
v___x_7068_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_format_7066_, v_getInfo_7067_);
return v___x_7068_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___boxed(lean_object* v_aw_7069_, lean_object* v_format_7070_, lean_object* v_getInfo_7071_){
_start:
{
lean_object* v_res_7072_; 
v_res_7072_ = l_Std_Time_GenericFormat_formatGeneric(v_aw_7069_, v_format_7070_, v_getInfo_7071_);
lean_dec(v_aw_7069_);
return v_res_7072_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(lean_object* v_dateformat_7073_, lean_object* v_data_7074_, lean_object* v_format_7075_){
_start:
{
if (lean_obj_tag(v_format_7075_) == 0)
{
lean_dec_ref(v_dateformat_7073_);
return v_data_7074_;
}
else
{
lean_object* v_head_7076_; 
v_head_7076_ = lean_ctor_get(v_format_7075_, 0);
lean_inc(v_head_7076_);
if (lean_obj_tag(v_head_7076_) == 0)
{
lean_object* v_tail_7077_; lean_object* v_val_7078_; lean_object* v___x_7079_; 
v_tail_7077_ = lean_ctor_get(v_format_7075_, 1);
lean_inc(v_tail_7077_);
lean_dec_ref_known(v_format_7075_, 2);
v_val_7078_ = lean_ctor_get(v_head_7076_, 0);
lean_inc_ref(v_val_7078_);
lean_dec_ref_known(v_head_7076_, 1);
v___x_7079_ = lean_string_append(v_data_7074_, v_val_7078_);
lean_dec_ref(v_val_7078_);
v_data_7074_ = v___x_7079_;
v_format_7075_ = v_tail_7077_;
goto _start;
}
else
{
lean_object* v_tail_7081_; lean_object* v_modifier_7082_; lean_object* v___f_7083_; 
v_tail_7081_ = lean_ctor_get(v_format_7075_, 1);
lean_inc(v_tail_7081_);
lean_dec_ref_known(v_format_7075_, 2);
v_modifier_7082_ = lean_ctor_get(v_head_7076_, 0);
lean_inc_ref(v_modifier_7082_);
lean_dec_ref_known(v_head_7076_, 1);
v___f_7083_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0), 5, 4);
lean_closure_set(v___f_7083_, 0, v_dateformat_7073_);
lean_closure_set(v___f_7083_, 1, v_modifier_7082_);
lean_closure_set(v___f_7083_, 2, v_data_7074_);
lean_closure_set(v___f_7083_, 3, v_tail_7081_);
return v___f_7083_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0(lean_object* v_dateformat_7084_, lean_object* v_modifier_7085_, lean_object* v_data_7086_, lean_object* v_tail_7087_, lean_object* v___y_7088_){
_start:
{
lean_object* v___x_7089_; lean_object* v___x_7090_; lean_object* v___x_7091_; 
v___x_7089_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7084_, v_modifier_7085_, v___y_7088_);
v___x_7090_ = lean_string_append(v_data_7086_, v___x_7089_);
lean_dec_ref(v___x_7089_);
v___x_7091_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7084_, v___x_7090_, v_tail_7087_);
return v___x_7091_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___redArg(lean_object* v_format_7092_){
_start:
{
lean_object* v_config_7093_; lean_object* v_string_7094_; lean_object* v_dateformat_7095_; lean_object* v___x_7096_; lean_object* v___x_7097_; 
v_config_7093_ = lean_ctor_get(v_format_7092_, 0);
lean_inc_ref(v_config_7093_);
v_string_7094_ = lean_ctor_get(v_format_7092_, 1);
lean_inc(v_string_7094_);
lean_dec_ref(v_format_7092_);
v_dateformat_7095_ = lean_ctor_get(v_config_7093_, 0);
lean_inc_ref(v_dateformat_7095_);
lean_dec_ref(v_config_7093_);
v___x_7096_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_7097_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7095_, v___x_7096_, v_string_7094_);
return v___x_7097_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder(lean_object* v_aw_7098_, lean_object* v_format_7099_){
_start:
{
lean_object* v___x_7100_; 
v___x_7100_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v_format_7099_);
return v___x_7100_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___boxed(lean_object* v_aw_7101_, lean_object* v_format_7102_){
_start:
{
lean_object* v_res_7103_; 
v_res_7103_ = l_Std_Time_GenericFormat_formatBuilder(v_aw_7101_, v_format_7102_);
lean_dec(v_aw_7101_);
return v_res_7103_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instFormatGenericFormatFormatTypeString(lean_object* v_aw_7104_){
_start:
{
lean_object* v___x_7105_; lean_object* v___x_7106_; lean_object* v___x_7107_; 
lean_inc(v_aw_7104_);
v___x_7105_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_formatBuilder___boxed), 2, 1);
lean_closure_set(v___x_7105_, 0, v_aw_7104_);
v___x_7106_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parseBuilder___boxed), 5, 1);
lean_closure_set(v___x_7106_, 0, v_aw_7104_);
v___x_7107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7107_, 0, v___x_7105_);
lean_ctor_set(v___x_7107_, 1, v___x_7106_);
return v___x_7107_;
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
