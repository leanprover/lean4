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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_Internal_Parsec_String_pstring(lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x21(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Std_Time_Weekday_toOrdinal(uint8_t);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(uint8_t, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: '''"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0(uint8_t, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(uint8_t, uint32_t, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(uint32_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected: '\\'"};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__0_value)}};
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1_value;
static const lean_closure_object l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2 = (const lean_object*)&l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2_value;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(uint8_t v_decide_271_, uint32_t v___x_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_fst_277_; lean_object* v_snd_278_; lean_object* v___x_279_; uint8_t v_decide_280_; 
v_fst_277_ = lean_ctor_get(v___y_273_, 0);
v_snd_278_ = lean_ctor_get(v___y_273_, 1);
v___x_279_ = lean_string_utf8_byte_size(v_fst_277_);
v_decide_280_ = lean_nat_dec_eq(v_snd_278_, v___x_279_);
if (v_decide_280_ == 0)
{
if (v_decide_271_ == 0)
{
goto v___jp_274_;
}
else
{
uint32_t v_c_281_; uint8_t v___x_282_; 
v_c_281_ = lean_string_utf8_get_fast(v_fst_277_, v_snd_278_);
v___x_282_ = lean_uint32_dec_eq(v_c_281_, v___x_272_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
v___x_284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_284_, 0, v___y_273_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
return v___x_284_;
}
else
{
lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_338_; 
lean_inc(v_snd_278_);
lean_inc(v_fst_277_);
v_isSharedCheck_338_ = !lean_is_exclusive(v___y_273_);
if (v_isSharedCheck_338_ == 0)
{
lean_object* v_unused_339_; lean_object* v_unused_340_; 
v_unused_339_ = lean_ctor_get(v___y_273_, 1);
lean_dec(v_unused_339_);
v_unused_340_ = lean_ctor_get(v___y_273_, 0);
lean_dec(v_unused_340_);
v___x_286_ = v___y_273_;
v_isShared_287_ = v_isSharedCheck_338_;
goto v_resetjp_285_;
}
else
{
lean_dec(v___y_273_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_338_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v_it_x27_290_; 
v___x_288_ = lean_string_utf8_next_fast(v_fst_277_, v_snd_278_);
lean_dec(v_snd_278_);
lean_inc(v_fst_277_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 1, v___x_288_);
v_it_x27_290_ = v___x_286_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_fst_277_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v___x_288_);
v_it_x27_290_ = v_reuseFailAlloc_337_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
uint8_t v_decide_294_; 
v_decide_294_ = lean_nat_dec_eq(v___x_288_, v___x_279_);
if (v_decide_294_ == 0)
{
if (v___x_282_ == 0)
{
lean_dec(v_fst_277_);
goto v___jp_291_;
}
else
{
uint32_t v___x_295_; uint8_t v___x_296_; 
v___x_295_ = lean_string_utf8_get_fast(v_fst_277_, v___x_288_);
v___x_296_ = lean_uint32_dec_eq(v___x_295_, v___x_272_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec_ref(v_it_x27_290_);
v___x_297_ = lean_string_utf8_next_fast(v_fst_277_, v___x_288_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v_fst_277_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_300_ = lean_string_push(v___x_299_, v___x_295_);
v___x_301_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0(v___x_300_, v___x_298_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_pos_302_; lean_object* v_res_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_334_; 
v_pos_302_ = lean_ctor_get(v___x_301_, 0);
v_res_303_ = lean_ctor_get(v___x_301_, 1);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_334_ == 0)
{
v___x_305_ = v___x_301_;
v_isShared_306_ = v_isSharedCheck_334_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_res_303_);
lean_inc(v_pos_302_);
lean_dec(v___x_301_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_334_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v_fst_307_; lean_object* v_snd_308_; lean_object* v___x_309_; uint8_t v_decide_310_; 
v_fst_307_ = lean_ctor_get(v_pos_302_, 0);
v_snd_308_ = lean_ctor_get(v_pos_302_, 1);
v___x_309_ = lean_string_utf8_byte_size(v_fst_307_);
v_decide_310_ = lean_nat_dec_eq(v_snd_308_, v___x_309_);
if (v_decide_310_ == 0)
{
uint32_t v_c_311_; uint8_t v___x_312_; 
v_c_311_ = lean_string_utf8_get_fast(v_fst_307_, v_snd_308_);
v___x_312_ = lean_uint32_dec_eq(v_c_311_, v___x_272_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_315_; 
lean_dec(v_res_303_);
v___x_313_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__1));
if (v_isShared_306_ == 0)
{
lean_ctor_set_tag(v___x_305_, 1);
lean_ctor_set(v___x_305_, 1, v___x_313_);
v___x_315_ = v___x_305_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_pos_302_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
else
{
lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_327_; 
lean_inc(v_snd_308_);
lean_inc(v_fst_307_);
v_isSharedCheck_327_ = !lean_is_exclusive(v_pos_302_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; lean_object* v_unused_329_; 
v_unused_328_ = lean_ctor_get(v_pos_302_, 1);
lean_dec(v_unused_328_);
v_unused_329_ = lean_ctor_get(v_pos_302_, 0);
lean_dec(v_unused_329_);
v___x_318_ = v_pos_302_;
v_isShared_319_ = v_isSharedCheck_327_;
goto v_resetjp_317_;
}
else
{
lean_dec(v_pos_302_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_327_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v_it_x27_322_; 
v___x_320_ = lean_string_utf8_next_fast(v_fst_307_, v_snd_308_);
lean_dec(v_snd_308_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 1, v___x_320_);
v_it_x27_322_ = v___x_318_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_fst_307_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_320_);
v_it_x27_322_ = v_reuseFailAlloc_326_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_324_; 
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v_it_x27_322_);
v___x_324_ = v___x_305_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_it_x27_322_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_res_303_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_332_; 
lean_dec(v_res_303_);
v___x_330_ = lean_box(0);
if (v_isShared_306_ == 0)
{
lean_ctor_set_tag(v___x_305_, 1);
lean_ctor_set(v___x_305_, 1, v___x_330_);
v___x_332_ = v___x_305_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_pos_302_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
else
{
return v___x_301_;
}
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec(v_fst_277_);
v___x_335_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_336_, 0, v_it_x27_290_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
return v___x_336_;
}
}
}
else
{
lean_dec(v_fst_277_);
goto v___jp_291_;
}
v___jp_291_:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_box(0);
v___x_293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_293_, 0, v_it_x27_290_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
return v___x_293_;
}
}
}
}
}
}
else
{
goto v___jp_274_;
}
v___jp_274_:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_box(0);
v___x_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_276_, 0, v___y_273_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
return v___x_276_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___boxed(lean_object* v_decide_341_, lean_object* v___x_342_, lean_object* v___y_343_){
_start:
{
uint8_t v_decide_11291__boxed_344_; uint32_t v___x_11292__boxed_345_; lean_object* v_res_346_; 
v_decide_11291__boxed_344_ = lean_unbox(v_decide_341_);
v___x_11292__boxed_345_ = lean_unbox_uint32(v___x_342_);
lean_dec(v___x_342_);
v_res_346_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1(v_decide_11291__boxed_344_, v___x_11292__boxed_345_, v___y_343_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2_spec__3(lean_object* v_acc_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_fst_349_; lean_object* v_snd_350_; lean_object* v_pos_352_; lean_object* v_snd_353_; lean_object* v_err_354_; lean_object* v___x_358_; uint8_t v_decide_359_; 
v_fst_349_ = lean_ctor_get(v_a_348_, 0);
v_snd_350_ = lean_ctor_get(v_a_348_, 1);
lean_inc(v_snd_350_);
v___x_358_ = lean_string_utf8_byte_size(v_fst_349_);
v_decide_359_ = lean_nat_dec_eq(v_snd_350_, v___x_358_);
if (v_decide_359_ == 0)
{
uint32_t v___x_360_; uint32_t v_c_361_; uint8_t v___x_362_; 
v___x_360_ = 39;
v_c_361_ = lean_string_utf8_get_fast(v_fst_349_, v_snd_350_);
v___x_362_ = lean_uint32_dec_eq(v_c_361_, v___x_360_);
if (v___x_362_ == 0)
{
lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_372_; 
lean_inc(v_fst_349_);
v_isSharedCheck_372_ = !lean_is_exclusive(v_a_348_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; lean_object* v_unused_374_; 
v_unused_373_ = lean_ctor_get(v_a_348_, 1);
lean_dec(v_unused_373_);
v_unused_374_ = lean_ctor_get(v_a_348_, 0);
lean_dec(v_unused_374_);
v___x_364_ = v_a_348_;
v_isShared_365_ = v_isSharedCheck_372_;
goto v_resetjp_363_;
}
else
{
lean_dec(v_a_348_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_372_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v_it_x27_368_; 
v___x_366_ = lean_string_utf8_next_fast(v_fst_349_, v_snd_350_);
lean_dec(v_snd_350_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 1, v___x_366_);
v_it_x27_368_ = v___x_364_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_fst_349_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v___x_366_);
v_it_x27_368_ = v_reuseFailAlloc_371_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_369_; 
v___x_369_ = lean_string_push(v_acc_347_, v_c_361_);
v_acc_347_ = v___x_369_;
v_a_348_ = v_it_x27_368_;
goto _start;
}
}
}
else
{
lean_object* v___x_375_; 
v___x_375_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_350_);
v_pos_352_ = v_a_348_;
v_snd_353_ = v_snd_350_;
v_err_354_ = v___x_375_;
goto v___jp_351_;
}
}
else
{
lean_object* v___x_376_; 
v___x_376_ = lean_box(0);
lean_inc(v_snd_350_);
v_pos_352_ = v_a_348_;
v_snd_353_ = v_snd_350_;
v_err_354_ = v___x_376_;
goto v___jp_351_;
}
v___jp_351_:
{
uint8_t v_decide_355_; 
v_decide_355_ = lean_nat_dec_eq(v_snd_350_, v_snd_353_);
lean_dec(v_snd_353_);
lean_dec(v_snd_350_);
if (v_decide_355_ == 0)
{
lean_object* v___x_356_; 
lean_dec_ref(v_acc_347_);
lean_inc(v_err_354_);
v___x_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_356_, 0, v_pos_352_);
lean_ctor_set(v___x_356_, 1, v_err_354_);
return v___x_356_;
}
else
{
lean_object* v___x_357_; 
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v_pos_352_);
lean_ctor_set(v___x_357_, 1, v_acc_347_);
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2(lean_object* v_acc_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_fst_379_; lean_object* v_snd_380_; lean_object* v_pos_382_; lean_object* v_snd_383_; lean_object* v_err_384_; lean_object* v___x_388_; uint8_t v_decide_389_; 
v_fst_379_ = lean_ctor_get(v_a_378_, 0);
v_snd_380_ = lean_ctor_get(v_a_378_, 1);
lean_inc(v_snd_380_);
v___x_388_ = lean_string_utf8_byte_size(v_fst_379_);
v_decide_389_ = lean_nat_dec_eq(v_snd_380_, v___x_388_);
if (v_decide_389_ == 0)
{
uint32_t v___x_390_; uint32_t v_c_391_; uint8_t v___x_392_; 
v___x_390_ = 39;
v_c_391_ = lean_string_utf8_get_fast(v_fst_379_, v_snd_380_);
v___x_392_ = lean_uint32_dec_eq(v_c_391_, v___x_390_);
if (v___x_392_ == 0)
{
lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_402_; 
lean_inc(v_fst_379_);
v_isSharedCheck_402_ = !lean_is_exclusive(v_a_378_);
if (v_isSharedCheck_402_ == 0)
{
lean_object* v_unused_403_; lean_object* v_unused_404_; 
v_unused_403_ = lean_ctor_get(v_a_378_, 1);
lean_dec(v_unused_403_);
v_unused_404_ = lean_ctor_get(v_a_378_, 0);
lean_dec(v_unused_404_);
v___x_394_ = v_a_378_;
v_isShared_395_ = v_isSharedCheck_402_;
goto v_resetjp_393_;
}
else
{
lean_dec(v_a_378_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_402_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v_it_x27_398_; 
v___x_396_ = lean_string_utf8_next_fast(v_fst_379_, v_snd_380_);
lean_dec(v_snd_380_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 1, v___x_396_);
v_it_x27_398_ = v___x_394_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_fst_379_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v___x_396_);
v_it_x27_398_ = v_reuseFailAlloc_401_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_string_push(v_acc_377_, v_c_391_);
v___x_400_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2_spec__3(v___x_399_, v_it_x27_398_);
return v___x_400_;
}
}
}
else
{
lean_object* v___x_405_; 
v___x_405_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_380_);
v_pos_382_ = v_a_378_;
v_snd_383_ = v_snd_380_;
v_err_384_ = v___x_405_;
goto v___jp_381_;
}
}
else
{
lean_object* v___x_406_; 
v___x_406_ = lean_box(0);
lean_inc(v_snd_380_);
v_pos_382_ = v_a_378_;
v_snd_383_ = v_snd_380_;
v_err_384_ = v___x_406_;
goto v___jp_381_;
}
v___jp_381_:
{
uint8_t v_decide_385_; 
v_decide_385_ = lean_nat_dec_eq(v_snd_380_, v_snd_383_);
lean_dec(v_snd_383_);
lean_dec(v_snd_380_);
if (v_decide_385_ == 0)
{
lean_object* v___x_386_; 
lean_dec_ref(v_acc_377_);
lean_inc(v_err_384_);
v___x_386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_386_, 0, v_pos_382_);
lean_ctor_set(v___x_386_, 1, v_err_384_);
return v___x_386_;
}
else
{
lean_object* v___x_387_; 
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v_pos_382_);
lean_ctor_set(v___x_387_, 1, v_acc_377_);
return v___x_387_;
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
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__1));
v___x_423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_423_, 0, v___y_412_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
return v___x_423_;
}
else
{
lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_477_; 
lean_inc(v_snd_417_);
lean_inc(v_fst_416_);
v_isSharedCheck_477_ = !lean_is_exclusive(v___y_412_);
if (v_isSharedCheck_477_ == 0)
{
lean_object* v_unused_478_; lean_object* v_unused_479_; 
v_unused_478_ = lean_ctor_get(v___y_412_, 1);
lean_dec(v_unused_478_);
v_unused_479_ = lean_ctor_get(v___y_412_, 0);
lean_dec(v_unused_479_);
v___x_425_ = v___y_412_;
v_isShared_426_ = v_isSharedCheck_477_;
goto v_resetjp_424_;
}
else
{
lean_dec(v___y_412_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_477_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v_it_x27_429_; 
v___x_427_ = lean_string_utf8_next_fast(v_fst_416_, v_snd_417_);
lean_dec(v_snd_417_);
lean_inc(v_fst_416_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 1, v___x_427_);
v_it_x27_429_ = v___x_425_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_fst_416_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v___x_427_);
v_it_x27_429_ = v_reuseFailAlloc_476_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
uint8_t v_decide_433_; 
v_decide_433_ = lean_nat_dec_eq(v___x_427_, v___x_418_);
if (v_decide_433_ == 0)
{
if (v___x_421_ == 0)
{
lean_dec(v_fst_416_);
goto v___jp_430_;
}
else
{
uint32_t v___x_434_; uint8_t v___x_435_; 
v___x_434_ = lean_string_utf8_get_fast(v_fst_416_, v___x_427_);
v___x_435_ = lean_uint32_dec_eq(v___x_434_, v___x_411_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec_ref(v_it_x27_429_);
v___x_436_ = lean_string_utf8_next_fast(v_fst_416_, v___x_427_);
v___x_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_437_, 0, v_fst_416_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
v___x_438_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_439_ = lean_string_push(v___x_438_, v___x_434_);
v___x_440_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__2(v___x_439_, v___x_437_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_pos_441_; lean_object* v_res_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_473_; 
v_pos_441_ = lean_ctor_get(v___x_440_, 0);
v_res_442_ = lean_ctor_get(v___x_440_, 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_473_ == 0)
{
v___x_444_ = v___x_440_;
v_isShared_445_ = v_isSharedCheck_473_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_res_442_);
lean_inc(v_pos_441_);
lean_dec(v___x_440_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_473_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v_fst_446_; lean_object* v_snd_447_; lean_object* v___x_448_; uint8_t v_decide_449_; 
v_fst_446_ = lean_ctor_get(v_pos_441_, 0);
v_snd_447_ = lean_ctor_get(v_pos_441_, 1);
v___x_448_ = lean_string_utf8_byte_size(v_fst_446_);
v_decide_449_ = lean_nat_dec_eq(v_snd_447_, v___x_448_);
if (v_decide_449_ == 0)
{
uint32_t v_c_450_; uint8_t v___x_451_; 
v_c_450_ = lean_string_utf8_get_fast(v_fst_446_, v_snd_447_);
v___x_451_ = lean_uint32_dec_eq(v_c_450_, v___x_411_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_454_; 
lean_dec(v_res_442_);
v___x_452_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___closed__1));
if (v_isShared_445_ == 0)
{
lean_ctor_set_tag(v___x_444_, 1);
lean_ctor_set(v___x_444_, 1, v___x_452_);
v___x_454_ = v___x_444_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_pos_441_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
else
{
lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_466_; 
lean_inc(v_snd_447_);
lean_inc(v_fst_446_);
v_isSharedCheck_466_ = !lean_is_exclusive(v_pos_441_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; lean_object* v_unused_468_; 
v_unused_467_ = lean_ctor_get(v_pos_441_, 1);
lean_dec(v_unused_467_);
v_unused_468_ = lean_ctor_get(v_pos_441_, 0);
lean_dec(v_unused_468_);
v___x_457_ = v_pos_441_;
v_isShared_458_ = v_isSharedCheck_466_;
goto v_resetjp_456_;
}
else
{
lean_dec(v_pos_441_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_466_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v_it_x27_461_; 
v___x_459_ = lean_string_utf8_next_fast(v_fst_446_, v_snd_447_);
lean_dec(v_snd_447_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 1, v___x_459_);
v_it_x27_461_ = v___x_457_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_fst_446_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v___x_459_);
v_it_x27_461_ = v_reuseFailAlloc_465_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_463_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v_it_x27_461_);
v___x_463_ = v___x_444_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_it_x27_461_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_res_442_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
else
{
lean_object* v___x_469_; lean_object* v___x_471_; 
lean_dec(v_res_442_);
v___x_469_ = lean_box(0);
if (v_isShared_445_ == 0)
{
lean_ctor_set_tag(v___x_444_, 1);
lean_ctor_set(v___x_444_, 1, v___x_469_);
v___x_471_ = v___x_444_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_pos_441_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v___x_469_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
else
{
return v___x_440_;
}
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec(v_fst_416_);
v___x_474_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_475_, 0, v_it_x27_429_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
return v___x_475_;
}
}
}
else
{
lean_dec(v_fst_416_);
goto v___jp_430_;
}
v___jp_430_:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_box(0);
v___x_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_432_, 0, v_it_x27_429_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
return v___x_432_;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___boxed(lean_object* v_decide_480_, lean_object* v___x_481_, lean_object* v___y_482_){
_start:
{
uint8_t v_decide_11541__boxed_483_; uint32_t v___x_11542__boxed_484_; lean_object* v_res_485_; 
v_decide_11541__boxed_483_ = lean_unbox(v_decide_480_);
v___x_11542__boxed_484_ = lean_unbox_uint32(v___x_481_);
lean_dec(v___x_481_);
v_res_485_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0(v_decide_11541__boxed_483_, v___x_11542__boxed_484_, v___y_482_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__3(lean_object* v_acc_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_fst_488_; lean_object* v_snd_489_; lean_object* v_pos_491_; lean_object* v_snd_492_; lean_object* v_err_493_; lean_object* v___x_499_; uint8_t v_decide_500_; 
v_fst_488_ = lean_ctor_get(v_a_487_, 0);
v_snd_489_ = lean_ctor_get(v_a_487_, 1);
lean_inc(v_snd_489_);
v___x_499_ = lean_string_utf8_byte_size(v_fst_488_);
v_decide_500_ = lean_nat_dec_eq(v_snd_489_, v___x_499_);
if (v_decide_500_ == 0)
{
uint32_t v___x_501_; uint32_t v___x_502_; uint32_t v_c_503_; lean_object* v___x_504_; lean_object* v_it_x27_505_; uint8_t v___y_507_; uint32_t v___x_517_; uint8_t v___x_518_; 
v___x_501_ = 39;
v___x_502_ = 34;
v_c_503_ = lean_string_utf8_get_fast(v_fst_488_, v_snd_489_);
v___x_504_ = lean_string_utf8_next_fast(v_fst_488_, v_snd_489_);
lean_inc(v_fst_488_);
v_it_x27_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_505_, 0, v_fst_488_);
lean_ctor_set(v_it_x27_505_, 1, v___x_504_);
v___x_517_ = 65;
v___x_518_ = lean_uint32_dec_le(v___x_517_, v_c_503_);
if (v___x_518_ == 0)
{
goto v___jp_512_;
}
else
{
uint32_t v___x_519_; uint8_t v___x_520_; 
v___x_519_ = 90;
v___x_520_ = lean_uint32_dec_le(v_c_503_, v___x_519_);
if (v___x_520_ == 0)
{
goto v___jp_512_;
}
else
{
v___y_507_ = v___x_520_;
goto v___jp_506_;
}
}
v___jp_506_:
{
if (v___y_507_ == 0)
{
uint8_t v___x_508_; 
v___x_508_ = lean_uint32_dec_eq(v_c_503_, v___x_501_);
if (v___x_508_ == 0)
{
uint8_t v___x_509_; 
v___x_509_ = lean_uint32_dec_eq(v_c_503_, v___x_502_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; 
lean_dec(v_snd_489_);
lean_dec_ref(v_a_487_);
v___x_510_ = lean_string_push(v_acc_486_, v_c_503_);
v_acc_486_ = v___x_510_;
v_a_487_ = v_it_x27_505_;
goto _start;
}
else
{
lean_dec_ref_known(v_it_x27_505_, 2);
goto v___jp_497_;
}
}
else
{
lean_dec_ref_known(v_it_x27_505_, 2);
goto v___jp_497_;
}
}
else
{
lean_dec_ref_known(v_it_x27_505_, 2);
goto v___jp_497_;
}
}
v___jp_512_:
{
uint32_t v___x_513_; uint8_t v___x_514_; 
v___x_513_ = 97;
v___x_514_ = lean_uint32_dec_le(v___x_513_, v_c_503_);
if (v___x_514_ == 0)
{
v___y_507_ = v___x_514_;
goto v___jp_506_;
}
else
{
uint32_t v___x_515_; uint8_t v___x_516_; 
v___x_515_ = 122;
v___x_516_ = lean_uint32_dec_le(v_c_503_, v___x_515_);
v___y_507_ = v___x_516_;
goto v___jp_506_;
}
}
}
else
{
lean_object* v___x_521_; 
v___x_521_ = lean_box(0);
lean_inc(v_snd_489_);
v_pos_491_ = v_a_487_;
v_snd_492_ = v_snd_489_;
v_err_493_ = v___x_521_;
goto v___jp_490_;
}
v___jp_490_:
{
uint8_t v_decide_494_; 
v_decide_494_ = lean_nat_dec_eq(v_snd_489_, v_snd_492_);
lean_dec(v_snd_492_);
lean_dec(v_snd_489_);
if (v_decide_494_ == 0)
{
lean_object* v___x_495_; 
lean_dec_ref(v_acc_486_);
lean_inc(v_err_493_);
v___x_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_495_, 0, v_pos_491_);
lean_ctor_set(v___x_495_, 1, v_err_493_);
return v___x_495_;
}
else
{
lean_object* v___x_496_; 
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v_pos_491_);
lean_ctor_set(v___x_496_, 1, v_acc_486_);
return v___x_496_;
}
}
v___jp_497_:
{
lean_object* v___x_498_; 
v___x_498_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_489_);
v_pos_491_ = v_a_487_;
v_snd_492_ = v_snd_489_;
v_err_493_ = v___x_498_;
goto v___jp_490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(uint8_t v_decide_522_, uint32_t v___x_523_, uint32_t v___x_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_fst_532_; lean_object* v_snd_533_; lean_object* v___x_534_; uint8_t v_decide_535_; 
v_fst_532_ = lean_ctor_get(v___y_525_, 0);
v_snd_533_ = lean_ctor_get(v___y_525_, 1);
v___x_534_ = lean_string_utf8_byte_size(v_fst_532_);
v_decide_535_ = lean_nat_dec_eq(v_snd_533_, v___x_534_);
if (v_decide_535_ == 0)
{
if (v_decide_522_ == 0)
{
goto v___jp_526_;
}
else
{
uint32_t v_c_536_; lean_object* v___x_537_; lean_object* v_it_x27_538_; uint8_t v___y_540_; uint32_t v___x_551_; uint8_t v___x_552_; 
v_c_536_ = lean_string_utf8_get_fast(v_fst_532_, v_snd_533_);
v___x_537_ = lean_string_utf8_next_fast(v_fst_532_, v_snd_533_);
lean_inc(v_fst_532_);
v_it_x27_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_538_, 0, v_fst_532_);
lean_ctor_set(v_it_x27_538_, 1, v___x_537_);
v___x_551_ = 65;
v___x_552_ = lean_uint32_dec_le(v___x_551_, v_c_536_);
if (v___x_552_ == 0)
{
goto v___jp_546_;
}
else
{
uint32_t v___x_553_; uint8_t v___x_554_; 
v___x_553_ = 90;
v___x_554_ = lean_uint32_dec_le(v_c_536_, v___x_553_);
if (v___x_554_ == 0)
{
goto v___jp_546_;
}
else
{
v___y_540_ = v___x_554_;
goto v___jp_539_;
}
}
v___jp_539_:
{
if (v___y_540_ == 0)
{
uint8_t v___x_541_; 
v___x_541_ = lean_uint32_dec_eq(v_c_536_, v___x_523_);
if (v___x_541_ == 0)
{
uint8_t v___x_542_; 
v___x_542_ = lean_uint32_dec_eq(v_c_536_, v___x_524_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec_ref(v___y_525_);
v___x_543_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_544_ = lean_string_push(v___x_543_, v_c_536_);
v___x_545_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__3(v___x_544_, v_it_x27_538_);
return v___x_545_;
}
else
{
lean_dec_ref_known(v_it_x27_538_, 2);
goto v___jp_529_;
}
}
else
{
lean_dec_ref_known(v_it_x27_538_, 2);
goto v___jp_529_;
}
}
else
{
lean_dec_ref_known(v_it_x27_538_, 2);
goto v___jp_529_;
}
}
v___jp_546_:
{
uint32_t v___x_547_; uint8_t v___x_548_; 
v___x_547_ = 97;
v___x_548_ = lean_uint32_dec_le(v___x_547_, v_c_536_);
if (v___x_548_ == 0)
{
v___y_540_ = v___x_548_;
goto v___jp_539_;
}
else
{
uint32_t v___x_549_; uint8_t v___x_550_; 
v___x_549_ = 122;
v___x_550_ = lean_uint32_dec_le(v_c_536_, v___x_549_);
v___y_540_ = v___x_550_;
goto v___jp_539_;
}
}
}
}
else
{
goto v___jp_526_;
}
v___jp_526_:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_box(0);
v___x_528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_528_, 0, v___y_525_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
return v___x_528_;
}
v___jp_529_:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_531_, 0, v___y_525_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2___boxed(lean_object* v_decide_555_, lean_object* v___x_556_, lean_object* v___x_557_, lean_object* v___y_558_){
_start:
{
uint8_t v_decide_11741__boxed_559_; uint32_t v___x_11742__boxed_560_; uint32_t v___x_11743__boxed_561_; lean_object* v_res_562_; 
v_decide_11741__boxed_559_ = lean_unbox(v_decide_555_);
v___x_11742__boxed_560_ = lean_unbox_uint32(v___x_556_);
lean_dec(v___x_556_);
v___x_11743__boxed_561_ = lean_unbox_uint32(v___x_557_);
lean_dec(v___x_557_);
v_res_562_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2(v_decide_11741__boxed_559_, v___x_11742__boxed_560_, v___x_11743__boxed_561_, v___y_558_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(uint32_t v___y_563_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_564_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_565_ = lean_string_push(v___x_564_, v___y_563_);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3___boxed(lean_object* v___y_567_){
_start:
{
uint32_t v___y_11805__boxed_568_; lean_object* v_res_569_; 
v___y_11805__boxed_568_ = lean_unbox_uint32(v___y_567_);
lean_dec(v___y_567_);
v_res_569_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__3(v___y_11805__boxed_568_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4(uint8_t v___x_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_fst_575_; lean_object* v_snd_576_; lean_object* v___x_577_; uint8_t v_decide_578_; 
v_fst_575_ = lean_ctor_get(v___y_571_, 0);
v_snd_576_ = lean_ctor_get(v___y_571_, 1);
v___x_577_ = lean_string_utf8_byte_size(v_fst_575_);
v_decide_578_ = lean_nat_dec_eq(v_snd_576_, v___x_577_);
if (v_decide_578_ == 0)
{
if (v___x_570_ == 0)
{
goto v___jp_572_;
}
else
{
lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_589_; 
lean_inc(v_snd_576_);
lean_inc(v_fst_575_);
v_isSharedCheck_589_ = !lean_is_exclusive(v___y_571_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; lean_object* v_unused_591_; 
v_unused_590_ = lean_ctor_get(v___y_571_, 1);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v___y_571_, 0);
lean_dec(v_unused_591_);
v___x_580_ = v___y_571_;
v_isShared_581_ = v_isSharedCheck_589_;
goto v_resetjp_579_;
}
else
{
lean_dec(v___y_571_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_589_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
uint32_t v_c_582_; lean_object* v___x_583_; lean_object* v_it_x27_585_; 
v_c_582_ = lean_string_utf8_get_fast(v_fst_575_, v_snd_576_);
v___x_583_ = lean_string_utf8_next_fast(v_fst_575_, v_snd_576_);
lean_dec(v_snd_576_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_583_);
v_it_x27_585_ = v___x_580_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_fst_575_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_583_);
v_it_x27_585_ = v_reuseFailAlloc_588_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_box_uint32(v_c_582_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v_it_x27_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
return v___x_587_;
}
}
}
}
else
{
goto v___jp_572_;
}
v___jp_572_:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_box(0);
v___x_574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_574_, 0, v___y_571_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
return v___x_574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4___boxed(lean_object* v___x_592_, lean_object* v___y_593_){
_start:
{
uint8_t v___x_11814__boxed_594_; lean_object* v_res_595_; 
v___x_11814__boxed_594_ = lean_unbox(v___x_592_);
v_res_595_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4(v___x_11814__boxed_594_, v___y_593_);
return v_res_595_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1(void){
_start:
{
uint32_t v___x_600_; lean_object* v___x_601_; 
v___x_600_ = 39;
v___x_601_ = lean_box_uint32(v___x_600_);
return v___x_601_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2(void){
_start:
{
uint32_t v___x_602_; lean_object* v___x_603_; 
v___x_602_ = 34;
v___x_603_ = lean_box_uint32(v___x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart(lean_object* v_a_604_){
_start:
{
lean_object* v___x_605_; 
lean_inc_ref(v_a_604_);
v___x_605_ = l_Std_Time_parseModifier(v_a_604_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_pos_606_; lean_object* v_res_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v_a_604_);
v_pos_606_ = lean_ctor_get(v___x_605_, 0);
v_res_607_ = lean_ctor_get(v___x_605_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_615_ == 0)
{
v___x_609_ = v___x_605_;
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_res_607_);
lean_inc(v_pos_606_);
lean_dec(v___x_605_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_611_, 0, v_res_607_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 1, v___x_611_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_pos_606_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
else
{
lean_object* v_pos_616_; lean_object* v_err_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_688_; 
v_pos_616_ = lean_ctor_get(v___x_605_, 0);
v_err_617_ = lean_ctor_get(v___x_605_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_688_ == 0)
{
v___x_619_ = v___x_605_;
v_isShared_620_ = v_isSharedCheck_688_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_err_617_);
lean_inc(v_pos_616_);
lean_dec(v___x_605_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_688_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v_snd_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_686_; 
v_snd_621_ = lean_ctor_get(v_a_604_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_a_604_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; 
v_unused_687_ = lean_ctor_get(v_a_604_, 0);
lean_dec(v_unused_687_);
v___x_623_ = v_a_604_;
v_isShared_624_ = v_isSharedCheck_686_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_snd_621_);
lean_dec(v_a_604_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_686_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v_fst_625_; lean_object* v_snd_626_; uint8_t v_decide_627_; 
v_fst_625_ = lean_ctor_get(v_pos_616_, 0);
v_snd_626_ = lean_ctor_get(v_pos_616_, 1);
v_decide_627_ = lean_nat_dec_eq(v_snd_621_, v_snd_626_);
lean_dec(v_snd_621_);
if (v_decide_627_ == 0)
{
lean_object* v___x_629_; 
lean_del_object(v___x_623_);
if (v_isShared_620_ == 0)
{
v___x_629_ = v___x_619_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_pos_616_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_err_617_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
else
{
lean_object* v___f_631_; lean_object* v___y_633_; lean_object* v_pos_634_; lean_object* v_snd_635_; lean_object* v___x_661_; uint8_t v_decide_662_; 
lean_inc(v_snd_626_);
lean_dec(v_err_617_);
v___f_631_ = ((lean_object*)(l_Std_Time_instCoeStringFormatPart___closed__0));
v___x_661_ = lean_string_utf8_byte_size(v_fst_625_);
v_decide_662_ = lean_nat_dec_eq(v_snd_626_, v___x_661_);
if (v_decide_662_ == 0)
{
if (v_decide_627_ == 0)
{
lean_del_object(v___x_623_);
goto v___jp_656_;
}
else
{
uint32_t v___x_663_; uint32_t v_c_664_; uint8_t v___x_665_; 
lean_del_object(v___x_619_);
v___x_663_ = 92;
v_c_664_ = lean_string_utf8_get_fast(v_fst_625_, v_snd_626_);
v___x_665_ = lean_uint32_dec_eq(v_c_664_, v___x_663_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_666_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__1));
lean_inc(v_pos_616_);
if (v_isShared_624_ == 0)
{
lean_ctor_set_tag(v___x_623_, 1);
lean_ctor_set(v___x_623_, 1, v___x_666_);
lean_ctor_set(v___x_623_, 0, v_pos_616_);
v___x_668_ = v___x_623_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_pos_616_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_inc(v_snd_626_);
v___y_633_ = v___x_668_;
v_pos_634_ = v_pos_616_;
v_snd_635_ = v_snd_626_;
goto v___jp_632_;
}
}
else
{
lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_683_; 
lean_inc(v_fst_625_);
lean_del_object(v___x_623_);
v_isSharedCheck_683_ = !lean_is_exclusive(v_pos_616_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; lean_object* v_unused_685_; 
v_unused_684_ = lean_ctor_get(v_pos_616_, 1);
lean_dec(v_unused_684_);
v_unused_685_ = lean_ctor_get(v_pos_616_, 0);
lean_dec(v_unused_685_);
v___x_671_ = v_pos_616_;
v_isShared_672_ = v_isSharedCheck_683_;
goto v_resetjp_670_;
}
else
{
lean_dec(v_pos_616_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_683_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___f_673_; lean_object* v___x_674_; lean_object* v___f_675_; lean_object* v___x_676_; lean_object* v_it_x27_678_; 
v___f_673_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___closed__2));
v___x_674_ = lean_box(v___x_665_);
v___f_675_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__4___boxed), 2, 1);
lean_closure_set(v___f_675_, 0, v___x_674_);
v___x_676_ = lean_string_utf8_next_fast(v_fst_625_, v_snd_626_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 1, v___x_676_);
v_it_x27_678_ = v___x_671_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_fst_625_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v___x_676_);
v_it_x27_678_ = v_reuseFailAlloc_682_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; 
v___x_679_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_675_, v___f_673_, v_it_x27_678_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_dec(v_snd_626_);
return v___x_679_;
}
else
{
lean_object* v_pos_680_; lean_object* v_snd_681_; 
v_pos_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_pos_680_);
v_snd_681_ = lean_ctor_get(v_pos_680_, 1);
lean_inc(v_snd_681_);
v___y_633_ = v___x_679_;
v_pos_634_ = v_pos_680_;
v_snd_635_ = v_snd_681_;
goto v___jp_632_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_623_);
goto v___jp_656_;
}
v___jp_632_:
{
uint8_t v_decide_636_; 
v_decide_636_ = lean_nat_dec_eq(v_snd_626_, v_snd_635_);
lean_dec(v_snd_626_);
if (v_decide_636_ == 0)
{
lean_dec(v_snd_635_);
lean_dec_ref(v_pos_634_);
return v___y_633_;
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___f_639_; lean_object* v___x_640_; 
lean_dec_ref(v___y_633_);
v___x_637_ = lean_box(v_decide_636_);
v___x_638_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2;
v___f_639_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___boxed), 3, 2);
lean_closure_set(v___f_639_, 0, v___x_637_);
lean_closure_set(v___f_639_, 1, v___x_638_);
v___x_640_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_639_, v___f_631_, v_pos_634_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_dec(v_snd_635_);
return v___x_640_;
}
else
{
lean_object* v_pos_641_; lean_object* v_snd_642_; uint8_t v_decide_643_; 
v_pos_641_ = lean_ctor_get(v___x_640_, 0);
v_snd_642_ = lean_ctor_get(v_pos_641_, 1);
v_decide_643_ = lean_nat_dec_eq(v_snd_635_, v_snd_642_);
lean_dec(v_snd_635_);
if (v_decide_643_ == 0)
{
return v___x_640_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___f_646_; lean_object* v___x_647_; 
lean_inc(v_snd_642_);
lean_inc(v_pos_641_);
lean_dec_ref_known(v___x_640_, 2);
v___x_644_ = lean_box(v_decide_643_);
v___x_645_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1;
v___f_646_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__0___boxed), 3, 2);
lean_closure_set(v___f_646_, 0, v___x_644_);
lean_closure_set(v___f_646_, 1, v___x_645_);
v___x_647_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_646_, v___f_631_, v_pos_641_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_dec(v_snd_642_);
return v___x_647_;
}
else
{
lean_object* v_pos_648_; lean_object* v_snd_649_; uint8_t v_decide_650_; 
v_pos_648_ = lean_ctor_get(v___x_647_, 0);
v_snd_649_ = lean_ctor_get(v_pos_648_, 1);
v_decide_650_ = lean_nat_dec_eq(v_snd_642_, v_snd_649_);
lean_dec(v_snd_642_);
if (v_decide_650_ == 0)
{
return v___x_647_;
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___f_654_; lean_object* v___x_655_; 
lean_inc(v_pos_648_);
lean_dec_ref_known(v___x_647_, 2);
v___x_651_ = lean_box(v_decide_650_);
v___x_652_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__1;
v___x_653_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___boxed__const__2;
v___f_654_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__2___boxed), 4, 3);
lean_closure_set(v___f_654_, 0, v___x_651_);
lean_closure_set(v___f_654_, 1, v___x_652_);
lean_closure_set(v___f_654_, 2, v___x_653_);
v___x_655_ = l_Functor_mapRev___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__1___redArg(v___f_654_, v___f_631_, v_pos_648_);
return v___x_655_;
}
}
}
}
}
}
v___jp_656_:
{
lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_657_ = lean_box(0);
lean_inc(v_pos_616_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v___x_657_);
v___x_659_ = v___x_619_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_pos_616_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_inc(v_snd_626_);
v___y_633_ = v___x_659_;
v_pos_634_ = v_pos_616_;
v_snd_635_ = v_snd_626_;
goto v___jp_632_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_specParser_spec__0(lean_object* v_acc_689_, lean_object* v_a_690_){
_start:
{
lean_object* v___x_691_; 
lean_inc_ref(v_a_690_);
v___x_691_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart(v_a_690_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_pos_692_; lean_object* v_res_693_; lean_object* v___x_694_; 
lean_dec_ref(v_a_690_);
v_pos_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_pos_692_);
v_res_693_ = lean_ctor_get(v___x_691_, 1);
lean_inc(v_res_693_);
lean_dec_ref_known(v___x_691_, 2);
v___x_694_ = lean_array_push(v_acc_689_, v_res_693_);
v_acc_689_ = v___x_694_;
v_a_690_ = v_pos_692_;
goto _start;
}
else
{
lean_object* v_pos_696_; lean_object* v_err_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_710_; 
v_pos_696_ = lean_ctor_get(v___x_691_, 0);
v_err_697_ = lean_ctor_get(v___x_691_, 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_710_ == 0)
{
v___x_699_ = v___x_691_;
v_isShared_700_ = v_isSharedCheck_710_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_err_697_);
lean_inc(v_pos_696_);
lean_dec(v___x_691_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_710_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v_snd_701_; lean_object* v_snd_702_; uint8_t v_decide_703_; 
v_snd_701_ = lean_ctor_get(v_a_690_, 1);
lean_inc(v_snd_701_);
lean_dec_ref(v_a_690_);
v_snd_702_ = lean_ctor_get(v_pos_696_, 1);
v_decide_703_ = lean_nat_dec_eq(v_snd_701_, v_snd_702_);
lean_dec(v_snd_701_);
if (v_decide_703_ == 0)
{
lean_object* v___x_705_; 
lean_dec_ref(v_acc_689_);
if (v_isShared_700_ == 0)
{
v___x_705_ = v___x_699_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_pos_696_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_err_697_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
else
{
lean_object* v___x_708_; 
lean_dec(v_err_697_);
if (v_isShared_700_ == 0)
{
lean_ctor_set_tag(v___x_699_, 0);
lean_ctor_set(v___x_699_, 1, v_acc_689_);
v___x_708_ = v___x_699_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_pos_696_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_acc_689_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParser(lean_object* v_a_716_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__0));
v___x_718_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_specParser_spec__0(v___x_717_, v_a_716_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_pos_719_; lean_object* v_res_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_736_; 
v_pos_719_ = lean_ctor_get(v___x_718_, 0);
v_res_720_ = lean_ctor_get(v___x_718_, 1);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_736_ == 0)
{
v___x_722_ = v___x_718_;
v_isShared_723_ = v_isSharedCheck_736_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_res_720_);
lean_inc(v_pos_719_);
lean_dec(v___x_718_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_736_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v_fst_724_; lean_object* v_snd_725_; lean_object* v___x_726_; uint8_t v_decide_727_; 
v_fst_724_ = lean_ctor_get(v_pos_719_, 0);
v_snd_725_ = lean_ctor_get(v_pos_719_, 1);
v___x_726_ = lean_string_utf8_byte_size(v_fst_724_);
v_decide_727_ = lean_nat_dec_eq(v_snd_725_, v___x_726_);
if (v_decide_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_730_; 
lean_dec(v_res_720_);
v___x_728_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_723_ == 0)
{
lean_ctor_set_tag(v___x_722_, 1);
lean_ctor_set(v___x_722_, 1, v___x_728_);
v___x_730_ = v___x_722_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_pos_719_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
else
{
lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_732_ = lean_array_to_list(v_res_720_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v___x_732_);
v___x_734_ = v___x_722_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_pos_719_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
else
{
lean_object* v_pos_737_; lean_object* v_err_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
v_pos_737_ = lean_ctor_get(v___x_718_, 0);
v_err_738_ = lean_ctor_get(v___x_718_, 1);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_718_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_err_738_);
lean_inc(v_pos_737_);
lean_dec(v___x_718_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_pos_737_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_err_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_specParse(lean_object* v_s_746_){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_748_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_747_, v_s_746_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(uint32_t v_a_749_, lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
lean_object* v_zero_752_; uint8_t v_isZero_753_; 
v_zero_752_ = lean_unsigned_to_nat(0u);
v_isZero_753_ = lean_nat_dec_eq(v_x_750_, v_zero_752_);
if (v_isZero_753_ == 1)
{
lean_dec(v_x_750_);
return v_x_751_;
}
else
{
lean_object* v_one_754_; lean_object* v_n_755_; lean_object* v___x_756_; 
v_one_754_ = lean_unsigned_to_nat(1u);
v_n_755_ = lean_nat_sub(v_x_750_, v_one_754_);
lean_dec(v_x_750_);
v___x_756_ = lean_string_push(v_x_751_, v_a_749_);
v_x_750_ = v_n_755_;
v_x_751_ = v___x_756_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1___boxed(lean_object* v_a_758_, lean_object* v_x_759_, lean_object* v_x_760_){
_start:
{
uint32_t v_a_boxed_761_; lean_object* v_res_762_; 
v_a_boxed_761_ = lean_unbox_uint32(v_a_758_);
lean_dec(v_a_758_);
v_res_762_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_boxed_761_, v_x_759_, v_x_760_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(lean_object* v___x_763_, lean_object* v_s_764_, lean_object* v_a_765_, lean_object* v_b_766_){
_start:
{
uint8_t v_decide_767_; 
v_decide_767_ = lean_nat_dec_eq(v_a_765_, v___x_763_);
if (v_decide_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_string_utf8_next_fast(v_s_764_, v_a_765_);
lean_dec(v_a_765_);
v___x_769_ = lean_unsigned_to_nat(1u);
v___x_770_ = lean_nat_add(v_b_766_, v___x_769_);
lean_dec(v_b_766_);
v_a_765_ = v___x_768_;
v_b_766_ = v___x_770_;
goto _start;
}
else
{
lean_dec(v_a_765_);
return v_b_766_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg___boxed(lean_object* v___x_772_, lean_object* v_s_773_, lean_object* v_a_774_, lean_object* v_b_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_772_, v_s_773_, v_a_774_, v_b_775_);
lean_dec_ref(v_s_773_);
lean_dec(v___x_772_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(lean_object* v_n_777_, uint32_t v_a_778_, lean_object* v_s_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_780_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = lean_string_utf8_byte_size(v_s_779_);
v___x_783_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_782_, v_s_779_, v___x_781_, v___x_781_);
v___x_784_ = lean_nat_sub(v_n_777_, v___x_783_);
lean_dec(v___x_783_);
v___x_785_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_778_, v___x_784_, v___x_780_);
v___x_786_ = lean_string_append(v___x_785_, v_s_779_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii___boxed(lean_object* v_n_787_, lean_object* v_a_788_, lean_object* v_s_789_){
_start:
{
uint32_t v_a_boxed_790_; lean_object* v_res_791_; 
v_a_boxed_790_ = lean_unbox_uint32(v_a_788_);
lean_dec(v_a_788_);
v_res_791_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v_n_787_, v_a_boxed_790_, v_s_789_);
lean_dec_ref(v_s_789_);
lean_dec(v_n_787_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0(lean_object* v___x_792_, lean_object* v___x_793_, lean_object* v_s_794_, lean_object* v_inst_795_, lean_object* v_R_796_, lean_object* v_a_797_, lean_object* v_b_798_, lean_object* v_c_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_792_, v_s_794_, v_a_797_, v_b_798_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___boxed(lean_object* v___x_801_, lean_object* v___x_802_, lean_object* v_s_803_, lean_object* v_inst_804_, lean_object* v_R_805_, lean_object* v_a_806_, lean_object* v_b_807_, lean_object* v_c_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0(v___x_801_, v___x_802_, v_s_803_, v_inst_804_, v_R_805_, v_a_806_, v_b_807_, v_c_808_);
lean_dec_ref(v_s_803_);
lean_dec_ref(v___x_802_);
lean_dec(v___x_801_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(lean_object* v_n_810_, uint32_t v_a_811_, lean_object* v_s_812_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_813_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_815_ = lean_string_utf8_byte_size(v_s_812_);
v___x_816_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__0___redArg(v___x_815_, v_s_812_, v___x_814_, v___x_814_);
v___x_817_ = lean_nat_sub(v_n_810_, v___x_816_);
lean_dec(v___x_816_);
v___x_818_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii_spec__1(v_a_811_, v___x_817_, v___x_813_);
v___x_819_ = lean_string_append(v_s_812_, v___x_818_);
lean_dec_ref(v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii___boxed(lean_object* v_n_820_, lean_object* v_a_821_, lean_object* v_s_822_){
_start:
{
uint32_t v_a_boxed_823_; lean_object* v_res_824_; 
v_a_boxed_823_ = lean_unbox_uint32(v_a_821_);
lean_dec(v_a_821_);
v_res_824_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_n_820_, v_a_boxed_823_, v_s_822_);
lean_dec(v_n_820_);
return v_res_824_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = lean_nat_to_int(v___x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad(lean_object* v_size_828_, lean_object* v_n_829_, uint8_t v_cut_830_){
_start:
{
lean_object* v_fst_832_; lean_object* v_snd_833_; lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_847_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_848_ = lean_int_dec_lt(v_n_829_, v___x_847_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; 
v___x_849_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v_fst_832_ = v___x_849_;
v_snd_833_ = v_n_829_;
goto v___jp_831_;
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_851_ = lean_int_neg(v_n_829_);
lean_dec(v_n_829_);
v_fst_832_ = v___x_850_;
v_snd_833_ = v___x_851_;
goto v___jp_831_;
}
v___jp_831_:
{
lean_object* v_numStr_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v_numStr_834_ = l_Int_repr(v_snd_833_);
lean_dec(v_snd_833_);
v___x_835_ = lean_string_utf8_byte_size(v_numStr_834_);
v___x_836_ = lean_nat_dec_lt(v_size_828_, v___x_835_);
if (v___x_836_ == 0)
{
uint32_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_837_ = 48;
v___x_838_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v_size_828_, v___x_837_, v_numStr_834_);
lean_dec_ref(v_numStr_834_);
lean_inc_ref(v_fst_832_);
v___x_839_ = lean_string_append(v_fst_832_, v___x_838_);
lean_dec_ref(v___x_838_);
return v___x_839_;
}
else
{
if (v_cut_830_ == 0)
{
lean_object* v___x_840_; 
lean_inc_ref(v_fst_832_);
v___x_840_ = lean_string_append(v_fst_832_, v_numStr_834_);
lean_dec_ref(v_numStr_834_);
return v___x_840_;
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_841_ = lean_nat_sub(v___x_835_, v_size_828_);
v___x_842_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_numStr_834_);
v___x_843_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_843_, 0, v_numStr_834_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
lean_ctor_set(v___x_843_, 2, v___x_835_);
v___x_844_ = l_String_Slice_Pos_nextn(v___x_843_, v___x_842_, v___x_841_);
lean_dec_ref_known(v___x_843_, 3);
v___x_845_ = lean_string_utf8_extract_fast(v_numStr_834_, v___x_844_, v___x_835_);
lean_dec(v___x_844_);
lean_dec_ref(v_numStr_834_);
lean_inc_ref(v_fst_832_);
v___x_846_ = lean_string_append(v_fst_832_, v___x_845_);
lean_dec_ref(v___x_845_);
return v___x_846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_pad___boxed(lean_object* v_size_852_, lean_object* v_n_853_, lean_object* v_cut_854_){
_start:
{
uint8_t v_cut_boxed_855_; lean_object* v_res_856_; 
v_cut_boxed_855_ = lean_unbox(v_cut_854_);
v_res_856_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_size_852_, v_n_853_, v_cut_boxed_855_);
lean_dec(v_size_852_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate(lean_object* v_size_857_, lean_object* v_n_858_, uint8_t v_cut_859_){
_start:
{
lean_object* v_fst_861_; lean_object* v_snd_862_; lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_876_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_877_ = lean_int_dec_lt(v_n_858_, v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
v___x_878_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v_fst_861_ = v___x_878_;
v_snd_862_ = v_n_858_;
goto v___jp_860_;
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_880_ = lean_int_neg(v_n_858_);
lean_dec(v_n_858_);
v_fst_861_ = v___x_879_;
v_snd_862_ = v___x_880_;
goto v___jp_860_;
}
v___jp_860_:
{
lean_object* v_numStr_863_; lean_object* v___x_864_; uint8_t v___x_865_; 
v_numStr_863_ = l_Int_repr(v_snd_862_);
lean_dec(v_snd_862_);
v___x_864_ = lean_string_length(v_numStr_863_);
v___x_865_ = lean_nat_dec_lt(v_size_857_, v___x_864_);
if (v___x_865_ == 0)
{
uint32_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_866_ = 48;
v___x_867_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_size_857_, v___x_866_, v_numStr_863_);
lean_dec(v_size_857_);
lean_inc_ref(v_fst_861_);
v___x_868_ = lean_string_append(v_fst_861_, v___x_867_);
lean_dec_ref(v___x_867_);
return v___x_868_;
}
else
{
if (v_cut_859_ == 0)
{
lean_object* v___x_869_; 
lean_dec(v_size_857_);
lean_inc_ref(v_fst_861_);
v___x_869_ = lean_string_append(v_fst_861_, v_numStr_863_);
lean_dec_ref(v_numStr_863_);
return v___x_869_;
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_870_ = lean_unsigned_to_nat(0u);
v___x_871_ = lean_string_utf8_byte_size(v_numStr_863_);
lean_inc_ref(v_numStr_863_);
v___x_872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_872_, 0, v_numStr_863_);
lean_ctor_set(v___x_872_, 1, v___x_870_);
lean_ctor_set(v___x_872_, 2, v___x_871_);
v___x_873_ = l_String_Slice_Pos_nextn(v___x_872_, v___x_870_, v_size_857_);
lean_dec_ref_known(v___x_872_, 3);
v___x_874_ = lean_string_utf8_extract_fast(v_numStr_863_, v___x_870_, v___x_873_);
lean_dec(v___x_873_);
lean_dec_ref(v_numStr_863_);
lean_inc_ref(v_fst_861_);
v___x_875_ = lean_string_append(v_fst_861_, v___x_874_);
lean_dec_ref(v___x_874_);
return v___x_875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate___boxed(lean_object* v_size_881_, lean_object* v_n_882_, lean_object* v_cut_883_){
_start:
{
uint8_t v_cut_boxed_884_; lean_object* v_res_885_; 
v_cut_boxed_884_ = lean_unbox(v_cut_883_);
v_res_885_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightTruncate(v_size_881_, v_n_882_, v_cut_boxed_884_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(uint8_t v_x_886_){
_start:
{
if (v_x_886_ == 0)
{
lean_object* v___x_887_; 
v___x_887_ = lean_unsigned_to_nat(0u);
return v___x_887_;
}
else
{
lean_object* v___x_888_; 
v___x_888_ = lean_unsigned_to_nat(1u);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex___boxed(lean_object* v_x_889_){
_start:
{
uint8_t v_x_40__boxed_890_; lean_object* v_res_891_; 
v_x_40__boxed_890_ = lean_unbox(v_x_889_);
v_res_891_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_x_40__boxed_890_);
return v_res_891_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_893_ = lean_int_neg(v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(lean_object* v_symbols_894_, lean_object* v_month_895_){
_start:
{
lean_object* v_monthLong_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_monthLong_896_ = lean_ctor_get(v_symbols_894_, 0);
v___x_897_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_898_ = lean_int_add(v_month_895_, v___x_897_);
v___x_899_ = l_Int_toNat(v___x_898_);
lean_dec(v___x_898_);
v___x_900_ = lean_array_fget_borrowed(v_monthLong_896_, v___x_899_);
lean_dec(v___x_899_);
lean_inc(v___x_900_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___boxed(lean_object* v_symbols_901_, lean_object* v_month_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_901_, v_month_902_);
lean_dec(v_month_902_);
lean_dec_ref(v_symbols_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(lean_object* v_symbols_904_, lean_object* v_month_905_){
_start:
{
lean_object* v_monthShort_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_monthShort_906_ = lean_ctor_get(v_symbols_904_, 1);
v___x_907_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_908_ = lean_int_add(v_month_905_, v___x_907_);
v___x_909_ = l_Int_toNat(v___x_908_);
lean_dec(v___x_908_);
v___x_910_ = lean_array_fget_borrowed(v_monthShort_906_, v___x_909_);
lean_dec(v___x_909_);
lean_inc(v___x_910_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort___boxed(lean_object* v_symbols_911_, lean_object* v_month_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_911_, v_month_912_);
lean_dec(v_month_912_);
lean_dec_ref(v_symbols_911_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(lean_object* v_symbols_914_, lean_object* v_month_915_){
_start:
{
lean_object* v_monthNarrow_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_monthNarrow_916_ = lean_ctor_get(v_symbols_914_, 2);
v___x_917_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_918_ = lean_int_add(v_month_915_, v___x_917_);
v___x_919_ = l_Int_toNat(v___x_918_);
lean_dec(v___x_918_);
v___x_920_ = lean_array_fget_borrowed(v_monthNarrow_916_, v___x_919_);
lean_dec(v___x_919_);
lean_inc(v___x_920_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow___boxed(lean_object* v_symbols_921_, lean_object* v_month_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_921_, v_month_922_);
lean_dec(v_month_922_);
lean_dec_ref(v_symbols_921_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(lean_object* v_symbols_924_, uint8_t v_wd_925_){
_start:
{
lean_object* v_weekdayLong_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_weekdayLong_926_ = lean_ctor_get(v_symbols_924_, 3);
v___x_927_ = l_Std_Time_Weekday_toOrdinal(v_wd_925_);
v___x_928_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_929_ = lean_int_add(v___x_927_, v___x_928_);
lean_dec(v___x_927_);
v___x_930_ = l_Int_toNat(v___x_929_);
lean_dec(v___x_929_);
v___x_931_ = lean_array_fget_borrowed(v_weekdayLong_926_, v___x_930_);
lean_dec(v___x_930_);
lean_inc(v___x_931_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong___boxed(lean_object* v_symbols_932_, lean_object* v_wd_933_){
_start:
{
uint8_t v_wd_boxed_934_; lean_object* v_res_935_; 
v_wd_boxed_934_ = lean_unbox(v_wd_933_);
v_res_935_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_932_, v_wd_boxed_934_);
lean_dec_ref(v_symbols_932_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(lean_object* v_symbols_936_, uint8_t v_wd_937_){
_start:
{
lean_object* v_weekdayShort_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_weekdayShort_938_ = lean_ctor_get(v_symbols_936_, 4);
v___x_939_ = l_Std_Time_Weekday_toOrdinal(v_wd_937_);
v___x_940_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_941_ = lean_int_add(v___x_939_, v___x_940_);
lean_dec(v___x_939_);
v___x_942_ = l_Int_toNat(v___x_941_);
lean_dec(v___x_941_);
v___x_943_ = lean_array_fget_borrowed(v_weekdayShort_938_, v___x_942_);
lean_dec(v___x_942_);
lean_inc(v___x_943_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort___boxed(lean_object* v_symbols_944_, lean_object* v_wd_945_){
_start:
{
uint8_t v_wd_boxed_946_; lean_object* v_res_947_; 
v_wd_boxed_946_ = lean_unbox(v_wd_945_);
v_res_947_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_944_, v_wd_boxed_946_);
lean_dec_ref(v_symbols_944_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(lean_object* v_symbols_948_, uint8_t v_wd_949_){
_start:
{
lean_object* v_weekdayNarrow_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_weekdayNarrow_950_ = lean_ctor_get(v_symbols_948_, 5);
v___x_951_ = l_Std_Time_Weekday_toOrdinal(v_wd_949_);
v___x_952_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_953_ = lean_int_add(v___x_951_, v___x_952_);
lean_dec(v___x_951_);
v___x_954_ = l_Int_toNat(v___x_953_);
lean_dec(v___x_953_);
v___x_955_ = lean_array_fget_borrowed(v_weekdayNarrow_950_, v___x_954_);
lean_dec(v___x_954_);
lean_inc(v___x_955_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow___boxed(lean_object* v_symbols_956_, lean_object* v_wd_957_){
_start:
{
uint8_t v_wd_boxed_958_; lean_object* v_res_959_; 
v_wd_boxed_958_ = lean_unbox(v_wd_957_);
v_res_959_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_956_, v_wd_boxed_958_);
lean_dec_ref(v_symbols_956_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(lean_object* v_symbols_960_, uint8_t v_wd_961_){
_start:
{
lean_object* v_weekdayTwoLetter_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_weekdayTwoLetter_962_ = lean_ctor_get(v_symbols_960_, 6);
v___x_963_ = l_Std_Time_Weekday_toOrdinal(v_wd_961_);
v___x_964_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_965_ = lean_int_add(v___x_963_, v___x_964_);
lean_dec(v___x_963_);
v___x_966_ = l_Int_toNat(v___x_965_);
lean_dec(v___x_965_);
v___x_967_ = lean_array_fget_borrowed(v_weekdayTwoLetter_962_, v___x_966_);
lean_dec(v___x_966_);
lean_inc(v___x_967_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter___boxed(lean_object* v_symbols_968_, lean_object* v_wd_969_){
_start:
{
uint8_t v_wd_boxed_970_; lean_object* v_res_971_; 
v_wd_boxed_970_ = lean_unbox(v_wd_969_);
v_res_971_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_968_, v_wd_boxed_970_);
lean_dec_ref(v_symbols_968_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(lean_object* v_symbols_972_, uint8_t v_era_973_){
_start:
{
lean_object* v_eraShort_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_eraShort_974_ = lean_ctor_get(v_symbols_972_, 7);
v___x_975_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_973_);
v___x_976_ = lean_array_fget_borrowed(v_eraShort_974_, v___x_975_);
lean_dec(v___x_975_);
lean_inc(v___x_976_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort___boxed(lean_object* v_symbols_977_, lean_object* v_era_978_){
_start:
{
uint8_t v_era_boxed_979_; lean_object* v_res_980_; 
v_era_boxed_979_ = lean_unbox(v_era_978_);
v_res_980_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(v_symbols_977_, v_era_boxed_979_);
lean_dec_ref(v_symbols_977_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(lean_object* v_symbols_981_, uint8_t v_era_982_){
_start:
{
lean_object* v_eraLong_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_eraLong_983_ = lean_ctor_get(v_symbols_981_, 8);
v___x_984_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_982_);
v___x_985_ = lean_array_fget_borrowed(v_eraLong_983_, v___x_984_);
lean_dec(v___x_984_);
lean_inc(v___x_985_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong___boxed(lean_object* v_symbols_986_, lean_object* v_era_987_){
_start:
{
uint8_t v_era_boxed_988_; lean_object* v_res_989_; 
v_era_boxed_988_ = lean_unbox(v_era_987_);
v_res_989_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(v_symbols_986_, v_era_boxed_988_);
lean_dec_ref(v_symbols_986_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(lean_object* v_symbols_990_, uint8_t v_era_991_){
_start:
{
lean_object* v_eraNarrow_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_eraNarrow_992_ = lean_ctor_get(v_symbols_990_, 9);
v___x_993_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraIndex(v_era_991_);
v___x_994_ = lean_array_fget_borrowed(v_eraNarrow_992_, v___x_993_);
lean_dec(v___x_993_);
lean_inc(v___x_994_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow___boxed(lean_object* v_symbols_995_, lean_object* v_era_996_){
_start:
{
uint8_t v_era_boxed_997_; lean_object* v_res_998_; 
v_era_boxed_997_ = lean_unbox(v_era_996_);
v_res_998_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(v_symbols_995_, v_era_boxed_997_);
lean_dec_ref(v_symbols_995_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(lean_object* v_x_1003_){
_start:
{
lean_object* v_natZero_1004_; lean_object* v_intZero_1005_; uint8_t v_isNeg_1006_; lean_object* v_a_1007_; uint8_t v_isZero_1008_; lean_object* v_one_1009_; lean_object* v_n_1010_; uint8_t v_isZero_1011_; 
v_natZero_1004_ = lean_unsigned_to_nat(0u);
v_intZero_1005_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v_isNeg_1006_ = lean_int_dec_lt(v_x_1003_, v_intZero_1005_);
v_a_1007_ = lean_nat_abs(v_x_1003_);
v_isZero_1008_ = lean_nat_dec_eq(v_a_1007_, v_natZero_1004_);
v_one_1009_ = lean_unsigned_to_nat(1u);
v_n_1010_ = lean_nat_sub(v_a_1007_, v_one_1009_);
lean_dec(v_a_1007_);
v_isZero_1011_ = lean_nat_dec_eq(v_n_1010_, v_natZero_1004_);
if (v_isZero_1011_ == 1)
{
lean_object* v___x_1012_; 
lean_dec(v_n_1010_);
v___x_1012_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__0));
return v___x_1012_;
}
else
{
lean_object* v_n_1013_; uint8_t v_isZero_1014_; 
v_n_1013_ = lean_nat_sub(v_n_1010_, v_one_1009_);
lean_dec(v_n_1010_);
v_isZero_1014_ = lean_nat_dec_eq(v_n_1013_, v_natZero_1004_);
if (v_isZero_1014_ == 1)
{
lean_object* v___x_1015_; 
lean_dec(v_n_1013_);
v___x_1015_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__1));
return v___x_1015_;
}
else
{
lean_object* v_n_1016_; uint8_t v_isZero_1017_; 
v_n_1016_ = lean_nat_sub(v_n_1013_, v_one_1009_);
lean_dec(v_n_1013_);
v_isZero_1017_ = lean_nat_dec_eq(v_n_1016_, v_natZero_1004_);
if (v_isZero_1017_ == 1)
{
lean_object* v___x_1018_; 
lean_dec(v_n_1016_);
v___x_1018_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__2));
return v___x_1018_;
}
else
{
lean_object* v_n_1019_; uint8_t v_isZero_1020_; lean_object* v___x_1021_; 
v_n_1019_ = lean_nat_sub(v_n_1016_, v_one_1009_);
lean_dec(v_n_1016_);
v_isZero_1020_ = lean_nat_dec_eq(v_n_1019_, v_natZero_1004_);
lean_dec(v_n_1019_);
v___x_1021_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__3));
return v___x_1021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___boxed(lean_object* v_x_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_x_1022_);
lean_dec(v_x_1022_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(lean_object* v_symbols_1024_, lean_object* v_q_1025_){
_start:
{
lean_object* v_quarterShort_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v_quarterShort_1026_ = lean_ctor_get(v_symbols_1024_, 10);
v___x_1027_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1028_ = lean_int_add(v_q_1025_, v___x_1027_);
v___x_1029_ = l_Int_toNat(v___x_1028_);
lean_dec(v___x_1028_);
v___x_1030_ = lean_array_fget_borrowed(v_quarterShort_1026_, v___x_1029_);
lean_dec(v___x_1029_);
lean_inc(v___x_1030_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort___boxed(lean_object* v_symbols_1031_, lean_object* v_q_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1031_, v_q_1032_);
lean_dec(v_q_1032_);
lean_dec_ref(v_symbols_1031_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(lean_object* v_symbols_1034_, lean_object* v_q_1035_){
_start:
{
lean_object* v_quarterLong_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_quarterLong_1036_ = lean_ctor_get(v_symbols_1034_, 11);
v___x_1037_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1038_ = lean_int_add(v_q_1035_, v___x_1037_);
v___x_1039_ = l_Int_toNat(v___x_1038_);
lean_dec(v___x_1038_);
v___x_1040_ = lean_array_fget_borrowed(v_quarterLong_1036_, v___x_1039_);
lean_dec(v___x_1039_);
lean_inc(v___x_1040_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong___boxed(lean_object* v_symbols_1041_, lean_object* v_q_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1041_, v_q_1042_);
lean_dec(v_q_1042_);
lean_dec_ref(v_symbols_1041_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(lean_object* v_symbols_1044_, lean_object* v_q_1045_){
_start:
{
lean_object* v_quarterNarrow_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v_quarterNarrow_1046_ = lean_ctor_get(v_symbols_1044_, 12);
v___x_1047_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_1048_ = lean_int_add(v_q_1045_, v___x_1047_);
v___x_1049_ = l_Int_toNat(v___x_1048_);
lean_dec(v___x_1048_);
v___x_1050_ = lean_array_fget_borrowed(v_quarterNarrow_1046_, v___x_1049_);
lean_dec(v___x_1049_);
lean_inc(v___x_1050_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow___boxed(lean_object* v_symbols_1051_, lean_object* v_q_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1051_, v_q_1052_);
lean_dec(v_q_1052_);
lean_dec_ref(v_symbols_1051_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(lean_object* v_symbols_1054_, uint8_t v_marker_1055_){
_start:
{
if (v_marker_1055_ == 0)
{
lean_object* v_amShort_1056_; 
v_amShort_1056_ = lean_ctor_get(v_symbols_1054_, 13);
lean_inc_ref(v_amShort_1056_);
return v_amShort_1056_;
}
else
{
lean_object* v_pmShort_1057_; 
v_pmShort_1057_ = lean_ctor_get(v_symbols_1054_, 14);
lean_inc_ref(v_pmShort_1057_);
return v_pmShort_1057_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort___boxed(lean_object* v_symbols_1058_, lean_object* v_marker_1059_){
_start:
{
uint8_t v_marker_boxed_1060_; lean_object* v_res_1061_; 
v_marker_boxed_1060_ = lean_unbox(v_marker_1059_);
v_res_1061_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(v_symbols_1058_, v_marker_boxed_1060_);
lean_dec_ref(v_symbols_1058_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong(lean_object* v_symbols_1062_, uint8_t v_marker_1063_){
_start:
{
if (v_marker_1063_ == 0)
{
lean_object* v_amLong_1064_; 
v_amLong_1064_ = lean_ctor_get(v_symbols_1062_, 15);
lean_inc_ref(v_amLong_1064_);
return v_amLong_1064_;
}
else
{
lean_object* v_pmLong_1065_; 
v_pmLong_1065_ = lean_ctor_get(v_symbols_1062_, 16);
lean_inc_ref(v_pmLong_1065_);
return v_pmLong_1065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong___boxed(lean_object* v_symbols_1066_, lean_object* v_marker_1067_){
_start:
{
uint8_t v_marker_boxed_1068_; lean_object* v_res_1069_; 
v_marker_boxed_1068_ = lean_unbox(v_marker_1067_);
v_res_1069_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerLong(v_symbols_1066_, v_marker_boxed_1068_);
lean_dec_ref(v_symbols_1066_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(lean_object* v_symbols_1070_, uint8_t v_marker_1071_){
_start:
{
if (v_marker_1071_ == 0)
{
lean_object* v_amNarrow_1072_; 
v_amNarrow_1072_ = lean_ctor_get(v_symbols_1070_, 17);
lean_inc_ref(v_amNarrow_1072_);
return v_amNarrow_1072_;
}
else
{
lean_object* v_pmNarrow_1073_; 
v_pmNarrow_1073_ = lean_ctor_get(v_symbols_1070_, 18);
lean_inc_ref(v_pmNarrow_1073_);
return v_pmNarrow_1073_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow___boxed(lean_object* v_symbols_1074_, lean_object* v_marker_1075_){
_start:
{
uint8_t v_marker_boxed_1076_; lean_object* v_res_1077_; 
v_marker_boxed_1076_ = lean_unbox(v_marker_1075_);
v_res_1077_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(v_symbols_1074_, v_marker_boxed_1076_);
lean_dec_ref(v_symbols_1074_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(lean_object* v_dp_1078_, uint8_t v_period_1079_){
_start:
{
switch(v_period_1079_)
{
case 0:
{
lean_object* v_am_1080_; 
v_am_1080_ = lean_ctor_get(v_dp_1078_, 0);
lean_inc_ref(v_am_1080_);
return v_am_1080_;
}
case 1:
{
lean_object* v_pm_1081_; 
v_pm_1081_ = lean_ctor_get(v_dp_1078_, 1);
lean_inc_ref(v_pm_1081_);
return v_pm_1081_;
}
case 2:
{
lean_object* v_noon_1082_; 
v_noon_1082_ = lean_ctor_get(v_dp_1078_, 2);
lean_inc_ref(v_noon_1082_);
return v_noon_1082_;
}
default: 
{
lean_object* v_midnight_1083_; 
v_midnight_1083_ = lean_ctor_get(v_dp_1078_, 3);
lean_inc_ref(v_midnight_1083_);
return v_midnight_1083_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod___boxed(lean_object* v_dp_1084_, lean_object* v_period_1085_){
_start:
{
uint8_t v_period_boxed_1086_; lean_object* v_res_1087_; 
v_period_boxed_1086_ = lean_unbox(v_period_1085_);
v_res_1087_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dp_1084_, v_period_boxed_1086_);
lean_dec_ref(v_dp_1084_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(uint8_t v_x_1088_){
_start:
{
switch(v_x_1088_)
{
case 0:
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_unsigned_to_nat(0u);
return v___x_1089_;
}
case 1:
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_unsigned_to_nat(1u);
return v___x_1090_;
}
case 2:
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_unsigned_to_nat(2u);
return v___x_1091_;
}
case 3:
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_unsigned_to_nat(3u);
return v___x_1092_;
}
case 4:
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_unsigned_to_nat(4u);
return v___x_1093_;
}
default: 
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_unsigned_to_nat(5u);
return v___x_1094_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex___boxed(lean_object* v_x_1095_){
_start:
{
uint8_t v_x_112__boxed_1096_; lean_object* v_res_1097_; 
v_x_112__boxed_1096_ = lean_unbox(v_x_1095_);
v_res_1097_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(v_x_112__boxed_1096_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(lean_object* v_arr_1098_, uint8_t v_period_1099_){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = l___private_Std_Time_Format_Basic_0__Std_Time_extendedDayPeriodIndex(v_period_1099_);
v___x_1101_ = lean_array_fget_borrowed(v_arr_1098_, v___x_1100_);
lean_dec(v___x_1100_);
lean_inc(v___x_1101_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod___boxed(lean_object* v_arr_1102_, lean_object* v_period_1103_){
_start:
{
uint8_t v_period_boxed_1104_; lean_object* v_res_1105_; 
v_period_boxed_1104_ = lean_unbox(v_period_1103_);
v_res_1105_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_arr_1102_, v_period_boxed_1104_);
lean_dec_ref(v_arr_1102_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned(lean_object* v_data_1107_){
_start:
{
lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1109_ = lean_int_dec_lt(v_data_1107_, v___x_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_1111_ = l_Int_repr(v_data_1107_);
v___x_1112_ = lean_string_append(v___x_1110_, v___x_1111_);
lean_dec_ref(v___x_1111_);
return v___x_1112_;
}
else
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Int_repr(v_data_1107_);
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___boxed(lean_object* v_data_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l___private_Std_Time_Format_Basic_0__Std_Time_toSigned(v_data_1114_);
lean_dec(v_data_1114_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___impl(uint8_t v_x_1116_){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_box(v_x_1116_);
v___x_1118_ = lean_obj_tag_nat(v___x_1117_);
lean_dec(v___x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___impl___boxed(lean_object* v_x_1119_){
_start:
{
uint8_t v_x_4__boxed_1120_; lean_object* v_res_1121_; 
v_x_4__boxed_1120_ = lean_unbox(v_x_1119_);
v_res_1121_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorIdx___impl(v_x_4__boxed_1120_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg(lean_object* v_k_1122_){
_start:
{
lean_inc(v_k_1122_);
return v_k_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg___boxed(lean_object* v_k_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___redArg(v_k_1123_);
lean_dec(v_k_1123_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(lean_object* v_motive_1125_, lean_object* v_ctorIdx_1126_, uint8_t v_t_1127_, lean_object* v_h_1128_, lean_object* v_k_1129_){
_start:
{
lean_inc(v_k_1129_);
return v_k_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim___boxed(lean_object* v_motive_1130_, lean_object* v_ctorIdx_1131_, lean_object* v_t_1132_, lean_object* v_h_1133_, lean_object* v_k_1134_){
_start:
{
uint8_t v_t_boxed_1135_; lean_object* v_res_1136_; 
v_t_boxed_1135_ = lean_unbox(v_t_1132_);
v_res_1136_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_ctorElim(v_motive_1130_, v_ctorIdx_1131_, v_t_boxed_1135_, v_h_1133_, v_k_1134_);
lean_dec(v_k_1134_);
lean_dec(v_ctorIdx_1131_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg(lean_object* v_yes_1137_){
_start:
{
lean_inc(v_yes_1137_);
return v_yes_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg___boxed(lean_object* v_yes_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___redArg(v_yes_1138_);
lean_dec(v_yes_1138_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(lean_object* v_motive_1140_, uint8_t v_t_1141_, lean_object* v_h_1142_, lean_object* v_yes_1143_){
_start:
{
lean_inc(v_yes_1143_);
return v_yes_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim___boxed(lean_object* v_motive_1144_, lean_object* v_t_1145_, lean_object* v_h_1146_, lean_object* v_yes_1147_){
_start:
{
uint8_t v_t_boxed_1148_; lean_object* v_res_1149_; 
v_t_boxed_1148_ = lean_unbox(v_t_1145_);
v_res_1149_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_yes_elim(v_motive_1144_, v_t_boxed_1148_, v_h_1146_, v_yes_1147_);
lean_dec(v_yes_1147_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg(lean_object* v_no_1150_){
_start:
{
lean_inc(v_no_1150_);
return v_no_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg___boxed(lean_object* v_no_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___redArg(v_no_1151_);
lean_dec(v_no_1151_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim(lean_object* v_motive_1153_, uint8_t v_t_1154_, lean_object* v_h_1155_, lean_object* v_no_1156_){
_start:
{
lean_inc(v_no_1156_);
return v_no_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim___boxed(lean_object* v_motive_1157_, lean_object* v_t_1158_, lean_object* v_h_1159_, lean_object* v_no_1160_){
_start:
{
uint8_t v_t_boxed_1161_; lean_object* v_res_1162_; 
v_t_boxed_1161_ = lean_unbox(v_t_1158_);
v_res_1162_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_no_elim(v_motive_1157_, v_t_boxed_1161_, v_h_1159_, v_no_1160_);
lean_dec(v_no_1160_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg(lean_object* v_optional_1163_){
_start:
{
lean_inc(v_optional_1163_);
return v_optional_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg___boxed(lean_object* v_optional_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___redArg(v_optional_1164_);
lean_dec(v_optional_1164_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(lean_object* v_motive_1166_, uint8_t v_t_1167_, lean_object* v_h_1168_, lean_object* v_optional_1169_){
_start:
{
lean_inc(v_optional_1169_);
return v_optional_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim___boxed(lean_object* v_motive_1170_, lean_object* v_t_1171_, lean_object* v_h_1172_, lean_object* v_optional_1173_){
_start:
{
uint8_t v_t_boxed_1174_; lean_object* v_res_1175_; 
v_t_boxed_1174_ = lean_unbox(v_t_1171_);
v_res_1175_ = l___private_Std_Time_Format_Basic_0__Std_Time_Reason_optional_elim(v_motive_1170_, v_t_boxed_1174_, v_h_1172_, v_optional_1173_);
lean_dec(v_optional_1173_);
return v_res_1175_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(uint8_t v_x_1176_, uint8_t v_y_1177_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1178_ = lean_box(v_x_1176_);
v___x_1179_ = lean_obj_tag_nat(v___x_1178_);
lean_dec(v___x_1178_);
v___x_1180_ = lean_box(v_y_1177_);
v___x_1181_ = lean_obj_tag_nat(v___x_1180_);
lean_dec(v___x_1180_);
v___x_1182_ = lean_nat_dec_eq(v___x_1179_, v___x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq___boxed(lean_object* v_x_1183_, lean_object* v_y_1184_){
_start:
{
uint8_t v_x_24__boxed_1185_; uint8_t v_y_25__boxed_1186_; uint8_t v_res_1187_; lean_object* v_r_1188_; 
v_x_24__boxed_1185_ = lean_unbox(v_x_1183_);
v_y_25__boxed_1186_ = lean_unbox(v_y_1184_);
v_res_1187_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_x_24__boxed_1185_, v_y_25__boxed_1186_);
v_r_1188_ = lean_box(v_res_1187_);
return v_r_1188_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__1(lean_object* v_a_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Rat_ofInt(v_a_1191_);
return v___x_1192_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_unsigned_to_nat(1000000000u);
v___x_1195_ = lean_nat_to_int(v___x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(lean_object* v_offset_1196_, uint8_t v_withMinutes_1197_, uint8_t v_withSeconds_1198_, uint8_t v_colon_1199_, uint8_t v_padHour_1200_){
_start:
{
lean_object* v___y_1202_; lean_object* v___y_1203_; uint32_t v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1213_; lean_object* v___y_1214_; uint32_t v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1220_; lean_object* v___y_1221_; uint32_t v___y_1222_; lean_object* v___y_1223_; uint8_t v___y_1224_; lean_object* v___y_1226_; uint8_t v___y_1227_; uint32_t v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1238_; lean_object* v___y_1239_; uint8_t v___y_1240_; uint32_t v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1250_; lean_object* v___y_1251_; uint8_t v___y_1252_; uint32_t v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1258_; lean_object* v___y_1259_; uint8_t v___y_1260_; uint32_t v___y_1261_; lean_object* v___y_1262_; uint8_t v___y_1263_; lean_object* v___y_1265_; lean_object* v___y_1266_; uint32_t v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v_fst_1279_; lean_object* v_snd_1280_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1291_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1292_ = lean_int_dec_le(v___x_1291_, v_offset_1196_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1294_ = lean_int_neg(v_offset_1196_);
lean_dec(v_offset_1196_);
v_fst_1279_ = v___x_1293_;
v_snd_1280_ = v___x_1294_;
goto v___jp_1278_;
}
else
{
lean_object* v___x_1295_; 
v___x_1295_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v_fst_1279_ = v___x_1295_;
v_snd_1280_ = v_offset_1196_;
goto v___jp_1278_;
}
v___jp_1201_:
{
lean_object* v_second_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v_second_1207_ = lean_ctor_get(v___y_1202_, 2);
lean_inc(v_second_1207_);
lean_dec_ref(v___y_1202_);
v___x_1208_ = lean_string_append(v___y_1203_, v___y_1206_);
v___x_1209_ = l_Int_repr(v_second_1207_);
lean_dec(v_second_1207_);
v___x_1210_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___y_1205_, v___y_1204_, v___x_1209_);
lean_dec_ref(v___x_1209_);
v___x_1211_ = lean_string_append(v___x_1208_, v___x_1210_);
lean_dec_ref(v___x_1210_);
return v___x_1211_;
}
v___jp_1212_:
{
if (v_colon_1199_ == 0)
{
lean_object* v___x_1217_; 
v___x_1217_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___y_1202_ = v___y_1213_;
v___y_1203_ = v___y_1214_;
v___y_1204_ = v___y_1215_;
v___y_1205_ = v___y_1216_;
v___y_1206_ = v___x_1217_;
goto v___jp_1201_;
}
else
{
lean_object* v___x_1218_; 
v___x_1218_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___y_1202_ = v___y_1213_;
v___y_1203_ = v___y_1214_;
v___y_1204_ = v___y_1215_;
v___y_1205_ = v___y_1216_;
v___y_1206_ = v___x_1218_;
goto v___jp_1201_;
}
}
v___jp_1219_:
{
if (v___y_1224_ == 0)
{
lean_dec_ref(v___y_1220_);
return v___y_1221_;
}
else
{
v___y_1213_ = v___y_1220_;
v___y_1214_ = v___y_1221_;
v___y_1215_ = v___y_1222_;
v___y_1216_ = v___y_1223_;
goto v___jp_1212_;
}
}
v___jp_1225_:
{
uint8_t v___x_1231_; 
v___x_1231_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withSeconds_1198_, v___y_1227_);
if (v___x_1231_ == 0)
{
uint8_t v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = 2;
v___x_1233_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withSeconds_1198_, v___x_1232_);
if (v___x_1233_ == 0)
{
v___y_1220_ = v___y_1226_;
v___y_1221_ = v___y_1230_;
v___y_1222_ = v___y_1228_;
v___y_1223_ = v___y_1229_;
v___y_1224_ = v___x_1233_;
goto v___jp_1219_;
}
else
{
lean_object* v_second_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v_second_1234_ = lean_ctor_get(v___y_1226_, 2);
v___x_1235_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1236_ = lean_int_dec_eq(v_second_1234_, v___x_1235_);
if (v___x_1236_ == 0)
{
v___y_1220_ = v___y_1226_;
v___y_1221_ = v___y_1230_;
v___y_1222_ = v___y_1228_;
v___y_1223_ = v___y_1229_;
v___y_1224_ = v___x_1233_;
goto v___jp_1219_;
}
else
{
v___y_1220_ = v___y_1226_;
v___y_1221_ = v___y_1230_;
v___y_1222_ = v___y_1228_;
v___y_1223_ = v___y_1229_;
v___y_1224_ = v___x_1231_;
goto v___jp_1219_;
}
}
}
else
{
v___y_1213_ = v___y_1226_;
v___y_1214_ = v___y_1230_;
v___y_1215_ = v___y_1228_;
v___y_1216_ = v___y_1229_;
goto v___jp_1212_;
}
}
v___jp_1237_:
{
lean_object* v_minute_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v_minute_1244_ = lean_ctor_get(v___y_1238_, 1);
v___x_1245_ = lean_string_append(v___y_1239_, v___y_1243_);
v___x_1246_ = l_Int_repr(v_minute_1244_);
v___x_1247_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___y_1242_, v___y_1241_, v___x_1246_);
lean_dec_ref(v___x_1246_);
v___x_1248_ = lean_string_append(v___x_1245_, v___x_1247_);
lean_dec_ref(v___x_1247_);
v___y_1226_ = v___y_1238_;
v___y_1227_ = v___y_1240_;
v___y_1228_ = v___y_1241_;
v___y_1229_ = v___y_1242_;
v___y_1230_ = v___x_1248_;
goto v___jp_1225_;
}
v___jp_1249_:
{
if (v_colon_1199_ == 0)
{
lean_object* v___x_1255_; 
v___x_1255_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___y_1238_ = v___y_1251_;
v___y_1239_ = v___y_1250_;
v___y_1240_ = v___y_1252_;
v___y_1241_ = v___y_1253_;
v___y_1242_ = v___y_1254_;
v___y_1243_ = v___x_1255_;
goto v___jp_1237_;
}
else
{
lean_object* v___x_1256_; 
v___x_1256_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___y_1238_ = v___y_1251_;
v___y_1239_ = v___y_1250_;
v___y_1240_ = v___y_1252_;
v___y_1241_ = v___y_1253_;
v___y_1242_ = v___y_1254_;
v___y_1243_ = v___x_1256_;
goto v___jp_1237_;
}
}
v___jp_1257_:
{
if (v___y_1263_ == 0)
{
v___y_1226_ = v___y_1258_;
v___y_1227_ = v___y_1260_;
v___y_1228_ = v___y_1261_;
v___y_1229_ = v___y_1262_;
v___y_1230_ = v___y_1259_;
goto v___jp_1225_;
}
else
{
v___y_1250_ = v___y_1259_;
v___y_1251_ = v___y_1258_;
v___y_1252_ = v___y_1260_;
v___y_1253_ = v___y_1261_;
v___y_1254_ = v___y_1262_;
goto v___jp_1249_;
}
}
v___jp_1264_:
{
lean_object* v_data_1270_; uint8_t v___x_1271_; uint8_t v___x_1272_; 
lean_inc_ref(v___y_1265_);
v_data_1270_ = lean_string_append(v___y_1265_, v___y_1269_);
lean_dec_ref(v___y_1269_);
v___x_1271_ = 0;
v___x_1272_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withMinutes_1197_, v___x_1271_);
if (v___x_1272_ == 0)
{
uint8_t v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = 2;
v___x_1274_ = l___private_Std_Time_Format_Basic_0__Std_Time_instBEqReason_beq(v_withMinutes_1197_, v___x_1273_);
if (v___x_1274_ == 0)
{
v___y_1258_ = v___y_1266_;
v___y_1259_ = v_data_1270_;
v___y_1260_ = v___x_1271_;
v___y_1261_ = v___y_1267_;
v___y_1262_ = v___y_1268_;
v___y_1263_ = v___x_1274_;
goto v___jp_1257_;
}
else
{
lean_object* v_minute_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v_minute_1275_ = lean_ctor_get(v___y_1266_, 1);
v___x_1276_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1277_ = lean_int_dec_eq(v_minute_1275_, v___x_1276_);
if (v___x_1277_ == 0)
{
v___y_1258_ = v___y_1266_;
v___y_1259_ = v_data_1270_;
v___y_1260_ = v___x_1271_;
v___y_1261_ = v___y_1267_;
v___y_1262_ = v___y_1268_;
v___y_1263_ = v___x_1274_;
goto v___jp_1257_;
}
else
{
v___y_1258_ = v___y_1266_;
v___y_1259_ = v_data_1270_;
v___y_1260_ = v___x_1271_;
v___y_1261_ = v___y_1267_;
v___y_1262_ = v___y_1268_;
v___y_1263_ = v___x_1272_;
goto v___jp_1257_;
}
}
}
else
{
v___y_1250_ = v_data_1270_;
v___y_1251_ = v___y_1266_;
v___y_1252_ = v___x_1271_;
v___y_1253_ = v___y_1267_;
v___y_1254_ = v___y_1268_;
goto v___jp_1249_;
}
}
v___jp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v_time_1283_; lean_object* v___x_1284_; uint32_t v___x_1285_; 
v___x_1281_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_1282_ = lean_int_mul(v_snd_1280_, v___x_1281_);
lean_dec(v_snd_1280_);
v_time_1283_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1282_);
lean_dec(v___x_1282_);
v___x_1284_ = lean_unsigned_to_nat(2u);
v___x_1285_ = 48;
if (v_padHour_1200_ == 0)
{
lean_object* v_hour_1286_; lean_object* v___x_1287_; 
v_hour_1286_ = lean_ctor_get(v_time_1283_, 0);
v___x_1287_ = l_Int_repr(v_hour_1286_);
v___y_1265_ = v_fst_1279_;
v___y_1266_ = v_time_1283_;
v___y_1267_ = v___x_1285_;
v___y_1268_ = v___x_1284_;
v___y_1269_ = v___x_1287_;
goto v___jp_1264_;
}
else
{
lean_object* v_hour_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_hour_1288_ = lean_ctor_get(v_time_1283_, 0);
v___x_1289_ = l_Int_repr(v_hour_1288_);
v___x_1290_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1284_, v___x_1285_, v___x_1289_);
lean_dec_ref(v___x_1289_);
v___y_1265_ = v_fst_1279_;
v___y_1266_ = v_time_1283_;
v___y_1267_ = v___x_1285_;
v___y_1268_ = v___x_1284_;
v___y_1269_ = v___x_1290_;
goto v___jp_1264_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___boxed(lean_object* v_offset_1296_, lean_object* v_withMinutes_1297_, lean_object* v_withSeconds_1298_, lean_object* v_colon_1299_, lean_object* v_padHour_1300_){
_start:
{
uint8_t v_withMinutes_boxed_1301_; uint8_t v_withSeconds_boxed_1302_; uint8_t v_colon_boxed_1303_; uint8_t v_padHour_boxed_1304_; lean_object* v_res_1305_; 
v_withMinutes_boxed_1301_ = lean_unbox(v_withMinutes_1297_);
v_withSeconds_boxed_1302_ = lean_unbox(v_withSeconds_1298_);
v_colon_boxed_1303_ = lean_unbox(v_colon_1299_);
v_padHour_boxed_1304_ = lean_unbox(v_padHour_1300_);
v_res_1305_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1296_, v_withMinutes_boxed_1301_, v_withSeconds_boxed_1302_, v_colon_boxed_1303_, v_padHour_boxed_1304_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0_spec__0(lean_object* v_a_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = lean_nat_to_int(v_a_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(lean_object* v_a_1308_){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_nat_to_int(v_a_1308_);
v___x_1310_ = l_Rat_ofInt(v___x_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_classifyDayPeriod___lam__0(lean_object* v_minute_1311_, lean_object* v_second_1312_, lean_object* v_00___1313_){
_start:
{
lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1315_ = lean_int_dec_eq(v_minute_1311_, v___x_1314_);
if (v___x_1315_ == 0)
{
return v___x_1315_;
}
else
{
uint8_t v___x_1316_; 
v___x_1316_ = lean_int_dec_eq(v_second_1312_, v___x_1314_);
return v___x_1316_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyDayPeriod___lam__0___boxed(lean_object* v_minute_1317_, lean_object* v_second_1318_, lean_object* v_00___1319_){
_start:
{
uint8_t v_res_1320_; lean_object* v_r_1321_; 
v_res_1320_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1317_, v_second_1318_, v_00___1319_);
lean_dec(v_second_1318_);
lean_dec(v_minute_1317_);
v_r_1321_ = lean_box(v_res_1320_);
return v_r_1321_;
}
}
static lean_object* _init_l_Std_Time_classifyDayPeriod___closed__0(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = lean_unsigned_to_nat(12u);
v___x_1323_ = lean_nat_to_int(v___x_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_classifyDayPeriod(lean_object* v_hour_1324_, lean_object* v_minute_1325_, lean_object* v_second_1326_){
_start:
{
lean_object* v___y_1328_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1338_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1339_ = lean_int_dec_eq(v_hour_1324_, v___x_1338_);
if (v___x_1339_ == 0)
{
goto v___jp_1332_;
}
else
{
lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1340_ = lean_box(0);
v___x_1341_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1325_, v_second_1326_, v___x_1340_);
if (v___x_1341_ == 0)
{
goto v___jp_1332_;
}
else
{
uint8_t v___x_1342_; 
v___x_1342_ = 3;
return v___x_1342_;
}
}
v___jp_1327_:
{
uint8_t v___x_1329_; 
v___x_1329_ = lean_int_dec_lt(v_hour_1324_, v___y_1328_);
if (v___x_1329_ == 0)
{
uint8_t v___x_1330_; 
v___x_1330_ = 1;
return v___x_1330_;
}
else
{
uint8_t v___x_1331_; 
v___x_1331_ = 0;
return v___x_1331_;
}
}
v___jp_1332_:
{
lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1333_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1334_ = lean_int_dec_eq(v_hour_1324_, v___x_1333_);
if (v___x_1334_ == 0)
{
v___y_1328_ = v___x_1333_;
goto v___jp_1327_;
}
else
{
lean_object* v___x_1335_; uint8_t v___x_1336_; 
v___x_1335_ = lean_box(0);
v___x_1336_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1325_, v_second_1326_, v___x_1335_);
if (v___x_1336_ == 0)
{
v___y_1328_ = v___x_1333_;
goto v___jp_1327_;
}
else
{
uint8_t v___x_1337_; 
v___x_1337_ = 2;
return v___x_1337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyDayPeriod___boxed(lean_object* v_hour_1343_, lean_object* v_minute_1344_, lean_object* v_second_1345_){
_start:
{
uint8_t v_res_1346_; lean_object* v_r_1347_; 
v_res_1346_ = l_Std_Time_classifyDayPeriod(v_hour_1343_, v_minute_1344_, v_second_1345_);
lean_dec(v_second_1345_);
lean_dec(v_minute_1344_);
lean_dec(v_hour_1343_);
v_r_1347_ = lean_box(v_res_1346_);
return v_r_1347_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__0(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_unsigned_to_nat(6u);
v___x_1349_ = lean_nat_to_int(v___x_1348_);
return v___x_1349_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__1(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = lean_unsigned_to_nat(18u);
v___x_1351_ = lean_nat_to_int(v___x_1350_);
return v___x_1351_;
}
}
static lean_object* _init_l_Std_Time_classifyExtendedDayPeriod___closed__2(void){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_unsigned_to_nat(21u);
v___x_1353_ = lean_nat_to_int(v___x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_classifyExtendedDayPeriod(lean_object* v_hour_1354_, lean_object* v_minute_1355_, lean_object* v_second_1356_){
_start:
{
lean_object* v___y_1358_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1378_ = lean_int_dec_eq(v_hour_1354_, v___x_1377_);
if (v___x_1378_ == 0)
{
goto v___jp_1371_;
}
else
{
lean_object* v___x_1379_; uint8_t v___x_1380_; 
v___x_1379_ = lean_box(0);
v___x_1380_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1355_, v_second_1356_, v___x_1379_);
if (v___x_1380_ == 0)
{
goto v___jp_1371_;
}
else
{
uint8_t v___x_1381_; 
v___x_1381_ = 0;
return v___x_1381_;
}
}
v___jp_1357_:
{
lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1359_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__0, &l_Std_Time_classifyExtendedDayPeriod___closed__0_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__0);
v___x_1360_ = lean_int_dec_lt(v_hour_1354_, v___x_1359_);
if (v___x_1360_ == 0)
{
uint8_t v___x_1361_; 
v___x_1361_ = lean_int_dec_lt(v_hour_1354_, v___y_1358_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1362_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__1, &l_Std_Time_classifyExtendedDayPeriod___closed__1_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__1);
v___x_1363_ = lean_int_dec_lt(v_hour_1354_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1364_ = lean_obj_once(&l_Std_Time_classifyExtendedDayPeriod___closed__2, &l_Std_Time_classifyExtendedDayPeriod___closed__2_once, _init_l_Std_Time_classifyExtendedDayPeriod___closed__2);
v___x_1365_ = lean_int_dec_lt(v_hour_1354_, v___x_1364_);
if (v___x_1365_ == 0)
{
uint8_t v___x_1366_; 
v___x_1366_ = 1;
return v___x_1366_;
}
else
{
uint8_t v___x_1367_; 
v___x_1367_ = 5;
return v___x_1367_;
}
}
else
{
uint8_t v___x_1368_; 
v___x_1368_ = 4;
return v___x_1368_;
}
}
else
{
uint8_t v___x_1369_; 
v___x_1369_ = 2;
return v___x_1369_;
}
}
else
{
uint8_t v___x_1370_; 
v___x_1370_ = 1;
return v___x_1370_;
}
}
v___jp_1371_:
{
lean_object* v___x_1372_; uint8_t v___x_1373_; 
v___x_1372_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1373_ = lean_int_dec_eq(v_hour_1354_, v___x_1372_);
if (v___x_1373_ == 0)
{
v___y_1358_ = v___x_1372_;
goto v___jp_1357_;
}
else
{
lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1374_ = lean_box(0);
v___x_1375_ = l_Std_Time_classifyDayPeriod___lam__0(v_minute_1355_, v_second_1356_, v___x_1374_);
if (v___x_1375_ == 0)
{
v___y_1358_ = v___x_1372_;
goto v___jp_1357_;
}
else
{
uint8_t v___x_1376_; 
v___x_1376_ = 3;
return v___x_1376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_classifyExtendedDayPeriod___boxed(lean_object* v_hour_1382_, lean_object* v_minute_1383_, lean_object* v_second_1384_){
_start:
{
uint8_t v_res_1385_; lean_object* v_r_1386_; 
v_res_1385_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1382_, v_minute_1383_, v_second_1384_);
lean_dec(v_second_1384_);
lean_dec(v_minute_1383_);
lean_dec(v_hour_1382_);
v_r_1386_ = lean_box(v_res_1385_);
return v_r_1386_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = lean_unsigned_to_nat(100u);
v___x_1388_ = lean_nat_to_int(v___x_1387_);
return v___x_1388_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1(void){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = lean_unsigned_to_nat(7u);
v___x_1390_ = lean_nat_to_int(v___x_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(lean_object* v_dateformat_1394_, lean_object* v_modifier_1395_, lean_object* v_data_1396_){
_start:
{
switch(lean_obj_tag(v_modifier_1395_))
{
case 0:
{
uint8_t v_presentation_1397_; 
v_presentation_1397_ = lean_ctor_get_uint8(v_modifier_1395_, 0);
lean_dec_ref_known(v_modifier_1395_, 0);
switch(v_presentation_1397_)
{
case 1:
{
lean_object* v_symbols_1398_; uint8_t v___x_1399_; lean_object* v___x_1400_; 
v_symbols_1398_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1399_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1400_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraLong(v_symbols_1398_, v___x_1399_);
return v___x_1400_;
}
case 2:
{
lean_object* v_symbols_1401_; uint8_t v___x_1402_; lean_object* v___x_1403_; 
v_symbols_1401_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1402_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1403_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraNarrow(v_symbols_1401_, v___x_1402_);
return v___x_1403_;
}
default: 
{
lean_object* v_symbols_1404_; uint8_t v___x_1405_; lean_object* v___x_1406_; 
v_symbols_1404_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1405_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1406_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatEraShort(v_symbols_1404_, v___x_1405_);
return v___x_1406_;
}
}
}
case 1:
{
lean_object* v_presentation_1407_; 
v_presentation_1407_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc(v_presentation_1407_);
lean_dec_ref_known(v_modifier_1395_, 1);
switch(lean_obj_tag(v_presentation_1407_))
{
case 0:
{
lean_object* v___x_1408_; uint8_t v___x_1409_; lean_object* v___x_1410_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = 0;
v___x_1410_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1408_, v_data_1396_, v___x_1409_);
return v___x_1410_;
}
case 1:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; lean_object* v___x_1415_; 
v___x_1411_ = lean_unsigned_to_nat(2u);
v___x_1412_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1413_ = lean_int_emod(v_data_1396_, v___x_1412_);
lean_dec(v_data_1396_);
v___x_1414_ = 0;
v___x_1415_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1411_, v___x_1413_, v___x_1414_);
return v___x_1415_;
}
case 2:
{
lean_object* v___x_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = lean_unsigned_to_nat(4u);
v___x_1417_ = 0;
v___x_1418_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1416_, v_data_1396_, v___x_1417_);
return v___x_1418_;
}
default: 
{
lean_object* v_num_1419_; uint8_t v___x_1420_; lean_object* v___x_1421_; 
v_num_1419_ = lean_ctor_get(v_presentation_1407_, 0);
lean_inc(v_num_1419_);
lean_dec_ref_known(v_presentation_1407_, 1);
v___x_1420_ = 0;
v___x_1421_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1419_, v_data_1396_, v___x_1420_);
lean_dec(v_num_1419_);
return v___x_1421_;
}
}
}
case 2:
{
lean_object* v_presentation_1422_; lean_object* v___x_1423_; lean_object* v___y_1425_; lean_object* v___x_1439_; uint8_t v___x_1440_; 
v_presentation_1422_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc(v_presentation_1422_);
lean_dec_ref_known(v_modifier_1395_, 1);
v___x_1423_ = lean_unsigned_to_nat(0u);
v___x_1439_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1440_ = lean_int_dec_le(v_data_1396_, v___x_1439_);
if (v___x_1440_ == 0)
{
v___y_1425_ = v_data_1396_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1441_ = lean_int_neg(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1442_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1443_ = lean_int_add(v___x_1441_, v___x_1442_);
lean_dec(v___x_1441_);
v___y_1425_ = v___x_1443_;
goto v___jp_1424_;
}
v___jp_1424_:
{
switch(lean_obj_tag(v_presentation_1422_))
{
case 0:
{
uint8_t v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = 0;
v___x_1427_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1423_, v___y_1425_, v___x_1426_);
return v___x_1427_;
}
case 1:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; lean_object* v___x_1432_; 
v___x_1428_ = lean_unsigned_to_nat(2u);
v___x_1429_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1430_ = lean_int_emod(v___y_1425_, v___x_1429_);
lean_dec(v___y_1425_);
v___x_1431_ = 0;
v___x_1432_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1428_, v___x_1430_, v___x_1431_);
return v___x_1432_;
}
case 2:
{
lean_object* v___x_1433_; uint8_t v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = lean_unsigned_to_nat(4u);
v___x_1434_ = 0;
v___x_1435_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1433_, v___y_1425_, v___x_1434_);
return v___x_1435_;
}
default: 
{
lean_object* v_num_1436_; uint8_t v___x_1437_; lean_object* v___x_1438_; 
v_num_1436_ = lean_ctor_get(v_presentation_1422_, 0);
lean_inc(v_num_1436_);
lean_dec_ref_known(v_presentation_1422_, 1);
v___x_1437_ = 0;
v___x_1438_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1436_, v___y_1425_, v___x_1437_);
lean_dec(v_num_1436_);
return v___x_1438_;
}
}
}
}
case 3:
{
lean_object* v_presentation_1444_; lean_object* v_snd_1445_; uint8_t v___x_1446_; lean_object* v___x_1447_; 
v_presentation_1444_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc(v_presentation_1444_);
lean_dec_ref_known(v_modifier_1395_, 1);
v_snd_1445_ = lean_ctor_get(v_data_1396_, 1);
lean_inc(v_snd_1445_);
lean_dec(v_data_1396_);
v___x_1446_ = 0;
v___x_1447_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1444_, v_snd_1445_, v___x_1446_);
lean_dec(v_presentation_1444_);
return v___x_1447_;
}
case 4:
{
lean_object* v_presentation_1448_; 
v_presentation_1448_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc_ref(v_presentation_1448_);
lean_dec_ref_known(v_modifier_1395_, 1);
if (lean_obj_tag(v_presentation_1448_) == 0)
{
lean_object* v_val_1449_; uint8_t v___x_1450_; lean_object* v___x_1451_; 
v_val_1449_ = lean_ctor_get(v_presentation_1448_, 0);
lean_inc(v_val_1449_);
lean_dec_ref_known(v_presentation_1448_, 1);
v___x_1450_ = 0;
v___x_1451_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1449_, v_data_1396_, v___x_1450_);
lean_dec(v_val_1449_);
return v___x_1451_;
}
else
{
lean_object* v_val_1452_; uint8_t v___x_1453_; 
v_val_1452_ = lean_ctor_get(v_presentation_1448_, 0);
lean_inc(v_val_1452_);
lean_dec_ref_known(v_presentation_1448_, 1);
v___x_1453_ = lean_unbox(v_val_1452_);
lean_dec(v_val_1452_);
switch(v___x_1453_)
{
case 1:
{
lean_object* v_symbols_1454_; lean_object* v___x_1455_; 
v_symbols_1454_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1455_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_1454_, v_data_1396_);
lean_dec(v_data_1396_);
return v___x_1455_;
}
case 2:
{
lean_object* v_symbols_1456_; lean_object* v___x_1457_; 
v_symbols_1456_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1457_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_1456_, v_data_1396_);
lean_dec(v_data_1396_);
return v___x_1457_;
}
default: 
{
lean_object* v_symbols_1458_; lean_object* v___x_1459_; 
v_symbols_1458_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1459_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_1458_, v_data_1396_);
lean_dec(v_data_1396_);
return v___x_1459_;
}
}
}
}
case 5:
{
lean_object* v_presentation_1460_; 
v_presentation_1460_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc_ref(v_presentation_1460_);
lean_dec_ref_known(v_modifier_1395_, 1);
if (lean_obj_tag(v_presentation_1460_) == 0)
{
lean_object* v_val_1461_; uint8_t v___x_1462_; lean_object* v___x_1463_; 
v_val_1461_ = lean_ctor_get(v_presentation_1460_, 0);
lean_inc(v_val_1461_);
lean_dec_ref_known(v_presentation_1460_, 1);
v___x_1462_ = 0;
v___x_1463_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1461_, v_data_1396_, v___x_1462_);
lean_dec(v_val_1461_);
return v___x_1463_;
}
else
{
lean_object* v_val_1464_; uint8_t v___x_1465_; 
v_val_1464_ = lean_ctor_get(v_presentation_1460_, 0);
lean_inc(v_val_1464_);
lean_dec_ref_known(v_presentation_1460_, 1);
v___x_1465_ = lean_unbox(v_val_1464_);
lean_dec(v_val_1464_);
switch(v___x_1465_)
{
case 1:
{
lean_object* v_symbols_1466_; lean_object* v___x_1467_; 
v_symbols_1466_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1467_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong(v_symbols_1466_, v_data_1396_);
lean_dec(v_data_1396_);
return v___x_1467_;
}
case 2:
{
lean_object* v_symbols_1468_; lean_object* v___x_1469_; 
v_symbols_1468_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1469_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthNarrow(v_symbols_1468_, v_data_1396_);
lean_dec(v_data_1396_);
return v___x_1469_;
}
default: 
{
lean_object* v_symbols_1470_; lean_object* v___x_1471_; 
v_symbols_1470_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1471_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthShort(v_symbols_1470_, v_data_1396_);
lean_dec(v_data_1396_);
return v___x_1471_;
}
}
}
}
case 6:
{
lean_object* v_presentation_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; 
v_presentation_1472_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc(v_presentation_1472_);
lean_dec_ref_known(v_modifier_1395_, 1);
v___x_1473_ = 0;
v___x_1474_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1472_, v_data_1396_, v___x_1473_);
lean_dec(v_presentation_1472_);
return v___x_1474_;
}
case 7:
{
lean_object* v_presentation_1475_; 
v_presentation_1475_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc_ref(v_presentation_1475_);
lean_dec_ref_known(v_modifier_1395_, 1);
if (lean_obj_tag(v_presentation_1475_) == 0)
{
lean_object* v_val_1476_; uint8_t v___x_1477_; lean_object* v___x_1478_; 
v_val_1476_ = lean_ctor_get(v_presentation_1475_, 0);
lean_inc(v_val_1476_);
lean_dec_ref_known(v_presentation_1475_, 1);
v___x_1477_ = 0;
v___x_1478_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1476_, v_data_1396_, v___x_1477_);
lean_dec(v_val_1476_);
return v___x_1478_;
}
else
{
lean_object* v_val_1479_; uint8_t v___x_1480_; 
v_val_1479_ = lean_ctor_get(v_presentation_1475_, 0);
lean_inc(v_val_1479_);
lean_dec_ref_known(v_presentation_1475_, 1);
v___x_1480_ = lean_unbox(v_val_1479_);
lean_dec(v_val_1479_);
switch(v___x_1480_)
{
case 0:
{
lean_object* v_symbols_1481_; lean_object* v___x_1482_; 
v_symbols_1481_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1482_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1481_, v_data_1396_);
lean_dec(v_data_1396_);
return v___x_1482_;
}
case 1:
{
lean_object* v_symbols_1483_; lean_object* v___x_1484_; 
v_symbols_1483_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1484_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1483_, v_data_1396_);
lean_dec(v_data_1396_);
return v___x_1484_;
}
case 2:
{
lean_object* v_symbols_1485_; lean_object* v___x_1486_; 
v_symbols_1485_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1486_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1485_, v_data_1396_);
lean_dec(v_data_1396_);
return v___x_1486_;
}
default: 
{
lean_object* v___x_1487_; 
v___x_1487_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_data_1396_);
lean_dec(v_data_1396_);
return v___x_1487_;
}
}
}
}
case 8:
{
lean_object* v_presentation_1488_; 
v_presentation_1488_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc_ref(v_presentation_1488_);
lean_dec_ref_known(v_modifier_1395_, 1);
if (lean_obj_tag(v_presentation_1488_) == 0)
{
lean_object* v_val_1489_; uint8_t v___x_1490_; lean_object* v___x_1491_; 
v_val_1489_ = lean_ctor_get(v_presentation_1488_, 0);
lean_inc(v_val_1489_);
lean_dec_ref_known(v_presentation_1488_, 1);
v___x_1490_ = 0;
v___x_1491_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1489_, v_data_1396_, v___x_1490_);
lean_dec(v_val_1489_);
return v___x_1491_;
}
else
{
lean_object* v_val_1492_; uint8_t v___x_1493_; 
v_val_1492_ = lean_ctor_get(v_presentation_1488_, 0);
lean_inc(v_val_1492_);
lean_dec_ref_known(v_presentation_1488_, 1);
v___x_1493_ = lean_unbox(v_val_1492_);
lean_dec(v_val_1492_);
switch(v___x_1493_)
{
case 0:
{
lean_object* v_symbols_1494_; lean_object* v___x_1495_; 
v_symbols_1494_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1495_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterShort(v_symbols_1494_, v_data_1396_);
lean_dec(v_data_1396_);
return v___x_1495_;
}
case 1:
{
lean_object* v_symbols_1496_; lean_object* v___x_1497_; 
v_symbols_1496_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1497_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterLong(v_symbols_1496_, v_data_1396_);
lean_dec(v_data_1396_);
return v___x_1497_;
}
case 2:
{
lean_object* v_symbols_1498_; lean_object* v___x_1499_; 
v_symbols_1498_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1499_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNarrow(v_symbols_1498_, v_data_1396_);
lean_dec(v_data_1396_);
return v___x_1499_;
}
default: 
{
lean_object* v___x_1500_; 
v___x_1500_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber(v_data_1396_);
lean_dec(v_data_1396_);
return v___x_1500_;
}
}
}
}
case 9:
{
lean_object* v_presentation_1501_; lean_object* v___x_1502_; lean_object* v___y_1504_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v_presentation_1501_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc(v_presentation_1501_);
lean_dec_ref_known(v_modifier_1395_, 1);
v___x_1502_ = lean_unsigned_to_nat(0u);
v___x_1518_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1519_ = lean_int_dec_le(v_data_1396_, v___x_1518_);
if (v___x_1519_ == 0)
{
v___y_1504_ = v_data_1396_;
goto v___jp_1503_;
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1520_ = lean_int_neg(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1521_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1522_ = lean_int_add(v___x_1520_, v___x_1521_);
lean_dec(v___x_1520_);
v___y_1504_ = v___x_1522_;
goto v___jp_1503_;
}
v___jp_1503_:
{
switch(lean_obj_tag(v_presentation_1501_))
{
case 0:
{
uint8_t v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = 0;
v___x_1506_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1502_, v___y_1504_, v___x_1505_);
return v___x_1506_;
}
case 1:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; lean_object* v___x_1511_; 
v___x_1507_ = lean_unsigned_to_nat(2u);
v___x_1508_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1509_ = lean_int_emod(v___y_1504_, v___x_1508_);
lean_dec(v___y_1504_);
v___x_1510_ = 0;
v___x_1511_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1507_, v___x_1509_, v___x_1510_);
return v___x_1511_;
}
case 2:
{
lean_object* v___x_1512_; uint8_t v___x_1513_; lean_object* v___x_1514_; 
v___x_1512_ = lean_unsigned_to_nat(4u);
v___x_1513_ = 0;
v___x_1514_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1512_, v___y_1504_, v___x_1513_);
return v___x_1514_;
}
default: 
{
lean_object* v_num_1515_; uint8_t v___x_1516_; lean_object* v___x_1517_; 
v_num_1515_ = lean_ctor_get(v_presentation_1501_, 0);
lean_inc(v_num_1515_);
lean_dec_ref_known(v_presentation_1501_, 1);
v___x_1516_ = 0;
v___x_1517_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_num_1515_, v___y_1504_, v___x_1516_);
lean_dec(v_num_1515_);
return v___x_1517_;
}
}
}
}
case 10:
{
lean_object* v_presentation_1523_; uint8_t v___x_1524_; lean_object* v___x_1525_; 
v_presentation_1523_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc(v_presentation_1523_);
lean_dec_ref_known(v_modifier_1395_, 1);
v___x_1524_ = 0;
v___x_1525_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1523_, v_data_1396_, v___x_1524_);
lean_dec(v_presentation_1523_);
return v___x_1525_;
}
case 11:
{
lean_object* v_presentation_1526_; uint8_t v___x_1527_; lean_object* v___x_1528_; 
v_presentation_1526_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc(v_presentation_1526_);
lean_dec_ref_known(v_modifier_1395_, 1);
v___x_1527_ = 0;
v___x_1528_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1526_, v_data_1396_, v___x_1527_);
lean_dec(v_presentation_1526_);
return v___x_1528_;
}
case 12:
{
uint8_t v_presentation_1529_; 
v_presentation_1529_ = lean_ctor_get_uint8(v_modifier_1395_, 0);
lean_dec_ref_known(v_modifier_1395_, 0);
switch(v_presentation_1529_)
{
case 0:
{
lean_object* v_symbols_1530_; uint8_t v___x_1531_; lean_object* v___x_1532_; 
v_symbols_1530_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1531_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1532_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1530_, v___x_1531_);
return v___x_1532_;
}
case 1:
{
lean_object* v_symbols_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; 
v_symbols_1533_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1534_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1535_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1533_, v___x_1534_);
return v___x_1535_;
}
case 2:
{
lean_object* v_symbols_1536_; uint8_t v___x_1537_; lean_object* v___x_1538_; 
v_symbols_1536_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1537_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1538_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1536_, v___x_1537_);
return v___x_1538_;
}
default: 
{
lean_object* v_symbols_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; 
v_symbols_1539_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1540_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1541_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1539_, v___x_1540_);
return v___x_1541_;
}
}
}
case 13:
{
lean_object* v_presentation_1542_; 
v_presentation_1542_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc_ref(v_presentation_1542_);
lean_dec_ref_known(v_modifier_1395_, 1);
if (lean_obj_tag(v_presentation_1542_) == 0)
{
lean_object* v_val_1543_; uint8_t v_firstDayOfWeek_1544_; lean_object* v_firstOrd_1545_; uint8_t v___x_1546_; lean_object* v_dayOrd_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; lean_object* v___x_1555_; 
v_val_1543_ = lean_ctor_get(v_presentation_1542_, 0);
lean_inc(v_val_1543_);
lean_dec_ref_known(v_presentation_1542_, 1);
v_firstDayOfWeek_1544_ = lean_ctor_get_uint8(v_dateformat_1394_, sizeof(void*)*2);
v_firstOrd_1545_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_1544_);
v___x_1546_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v_dayOrd_1547_ = l_Std_Time_Weekday_toOrdinal(v___x_1546_);
v___x_1548_ = lean_int_sub(v_dayOrd_1547_, v_firstOrd_1545_);
lean_dec(v_firstOrd_1545_);
lean_dec(v_dayOrd_1547_);
v___x_1549_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_1550_ = lean_int_add(v___x_1548_, v___x_1549_);
lean_dec(v___x_1548_);
v___x_1551_ = lean_int_emod(v___x_1550_, v___x_1549_);
lean_dec(v___x_1550_);
v___x_1552_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1553_ = lean_int_add(v___x_1551_, v___x_1552_);
lean_dec(v___x_1551_);
v___x_1554_ = 0;
v___x_1555_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1543_, v___x_1553_, v___x_1554_);
lean_dec(v_val_1543_);
return v___x_1555_;
}
else
{
lean_object* v_val_1556_; uint8_t v___x_1557_; 
v_val_1556_ = lean_ctor_get(v_presentation_1542_, 0);
lean_inc(v_val_1556_);
lean_dec_ref_known(v_presentation_1542_, 1);
v___x_1557_ = lean_unbox(v_val_1556_);
lean_dec(v_val_1556_);
switch(v___x_1557_)
{
case 0:
{
lean_object* v_symbols_1558_; uint8_t v___x_1559_; lean_object* v___x_1560_; 
v_symbols_1558_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1559_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1560_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1558_, v___x_1559_);
return v___x_1560_;
}
case 1:
{
lean_object* v_symbols_1561_; uint8_t v___x_1562_; lean_object* v___x_1563_; 
v_symbols_1561_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1562_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1563_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1561_, v___x_1562_);
return v___x_1563_;
}
case 2:
{
lean_object* v_symbols_1564_; uint8_t v___x_1565_; lean_object* v___x_1566_; 
v_symbols_1564_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1565_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1566_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1564_, v___x_1565_);
return v___x_1566_;
}
default: 
{
lean_object* v_symbols_1567_; uint8_t v___x_1568_; lean_object* v___x_1569_; 
v_symbols_1567_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1568_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1569_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1567_, v___x_1568_);
return v___x_1569_;
}
}
}
}
case 14:
{
lean_object* v_presentation_1570_; 
v_presentation_1570_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc_ref(v_presentation_1570_);
lean_dec_ref_known(v_modifier_1395_, 1);
if (lean_obj_tag(v_presentation_1570_) == 0)
{
lean_object* v_val_1571_; uint8_t v_firstDayOfWeek_1572_; lean_object* v_firstOrd_1573_; uint8_t v___x_1574_; lean_object* v_dayOrd_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; lean_object* v___x_1583_; 
v_val_1571_ = lean_ctor_get(v_presentation_1570_, 0);
lean_inc(v_val_1571_);
lean_dec_ref_known(v_presentation_1570_, 1);
v_firstDayOfWeek_1572_ = lean_ctor_get_uint8(v_dateformat_1394_, sizeof(void*)*2);
v_firstOrd_1573_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_1572_);
v___x_1574_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v_dayOrd_1575_ = l_Std_Time_Weekday_toOrdinal(v___x_1574_);
v___x_1576_ = lean_int_sub(v_dayOrd_1575_, v_firstOrd_1573_);
lean_dec(v_firstOrd_1573_);
lean_dec(v_dayOrd_1575_);
v___x_1577_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_1578_ = lean_int_add(v___x_1576_, v___x_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_int_emod(v___x_1578_, v___x_1577_);
lean_dec(v___x_1578_);
v___x_1580_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_1581_ = lean_int_add(v___x_1579_, v___x_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = 0;
v___x_1583_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_val_1571_, v___x_1581_, v___x_1582_);
lean_dec(v_val_1571_);
return v___x_1583_;
}
else
{
lean_object* v_val_1584_; uint8_t v___x_1585_; 
v_val_1584_ = lean_ctor_get(v_presentation_1570_, 0);
lean_inc(v_val_1584_);
lean_dec_ref_known(v_presentation_1570_, 1);
v___x_1585_ = lean_unbox(v_val_1584_);
lean_dec(v_val_1584_);
switch(v___x_1585_)
{
case 0:
{
lean_object* v_symbols_1586_; uint8_t v___x_1587_; lean_object* v___x_1588_; 
v_symbols_1586_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1587_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1588_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayShort(v_symbols_1586_, v___x_1587_);
return v___x_1588_;
}
case 1:
{
lean_object* v_symbols_1589_; uint8_t v___x_1590_; lean_object* v___x_1591_; 
v_symbols_1589_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1590_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1591_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayLong(v_symbols_1589_, v___x_1590_);
return v___x_1591_;
}
case 2:
{
lean_object* v_symbols_1592_; uint8_t v___x_1593_; lean_object* v___x_1594_; 
v_symbols_1592_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1593_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1594_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayNarrow(v_symbols_1592_, v___x_1593_);
return v___x_1594_;
}
default: 
{
lean_object* v_symbols_1595_; uint8_t v___x_1596_; lean_object* v___x_1597_; 
v_symbols_1595_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1596_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1597_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWeekdayTwoLetter(v_symbols_1595_, v___x_1596_);
return v___x_1597_;
}
}
}
}
case 15:
{
lean_object* v_presentation_1598_; uint8_t v___x_1599_; lean_object* v___x_1600_; 
v_presentation_1598_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc(v_presentation_1598_);
lean_dec_ref_known(v_modifier_1395_, 1);
v___x_1599_ = 0;
v___x_1600_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1598_, v_data_1396_, v___x_1599_);
lean_dec(v_presentation_1598_);
return v___x_1600_;
}
case 16:
{
uint8_t v_presentation_1601_; 
v_presentation_1601_ = lean_ctor_get_uint8(v_modifier_1395_, 0);
lean_dec_ref_known(v_modifier_1395_, 0);
if (v_presentation_1601_ == 2)
{
lean_object* v_symbols_1602_; uint8_t v___x_1603_; lean_object* v___x_1604_; 
v_symbols_1602_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1603_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1604_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerNarrow(v_symbols_1602_, v___x_1603_);
return v___x_1604_;
}
else
{
lean_object* v_symbols_1605_; uint8_t v___x_1606_; lean_object* v___x_1607_; 
v_symbols_1605_ = lean_ctor_get(v_dateformat_1394_, 1);
v___x_1606_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1607_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatMarkerShort(v_symbols_1605_, v___x_1606_);
return v___x_1607_;
}
}
case 17:
{
uint8_t v_presentation_1608_; 
v_presentation_1608_ = lean_ctor_get_uint8(v_modifier_1395_, 0);
lean_dec_ref_known(v_modifier_1395_, 0);
switch(v_presentation_1608_)
{
case 1:
{
lean_object* v_symbols_1609_; lean_object* v_dayPeriodLong_1610_; uint8_t v___x_1611_; lean_object* v___x_1612_; 
v_symbols_1609_ = lean_ctor_get(v_dateformat_1394_, 1);
v_dayPeriodLong_1610_ = lean_ctor_get(v_symbols_1609_, 20);
v___x_1611_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1612_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodLong_1610_, v___x_1611_);
return v___x_1612_;
}
case 2:
{
lean_object* v_symbols_1613_; lean_object* v_dayPeriodNarrow_1614_; uint8_t v___x_1615_; lean_object* v___x_1616_; 
v_symbols_1613_ = lean_ctor_get(v_dateformat_1394_, 1);
v_dayPeriodNarrow_1614_ = lean_ctor_get(v_symbols_1613_, 21);
v___x_1615_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1616_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodNarrow_1614_, v___x_1615_);
return v___x_1616_;
}
default: 
{
lean_object* v_symbols_1617_; lean_object* v_dayPeriodShort_1618_; uint8_t v___x_1619_; lean_object* v___x_1620_; 
v_symbols_1617_ = lean_ctor_get(v_dateformat_1394_, 1);
v_dayPeriodShort_1618_ = lean_ctor_get(v_symbols_1617_, 19);
v___x_1619_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1620_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatDayPeriod(v_dayPeriodShort_1618_, v___x_1619_);
return v___x_1620_;
}
}
}
case 18:
{
uint8_t v_presentation_1621_; 
v_presentation_1621_ = lean_ctor_get_uint8(v_modifier_1395_, 0);
lean_dec_ref_known(v_modifier_1395_, 0);
switch(v_presentation_1621_)
{
case 1:
{
lean_object* v_symbols_1622_; lean_object* v_extendedDayPeriodLong_1623_; uint8_t v___x_1624_; lean_object* v___x_1625_; 
v_symbols_1622_ = lean_ctor_get(v_dateformat_1394_, 1);
v_extendedDayPeriodLong_1623_ = lean_ctor_get(v_symbols_1622_, 23);
v___x_1624_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1625_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodLong_1623_, v___x_1624_);
return v___x_1625_;
}
case 2:
{
lean_object* v_symbols_1626_; lean_object* v_extendedDayPeriodNarrow_1627_; uint8_t v___x_1628_; lean_object* v___x_1629_; 
v_symbols_1626_ = lean_ctor_get(v_dateformat_1394_, 1);
v_extendedDayPeriodNarrow_1627_ = lean_ctor_get(v_symbols_1626_, 24);
v___x_1628_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1629_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodNarrow_1627_, v___x_1628_);
return v___x_1629_;
}
default: 
{
lean_object* v_symbols_1630_; lean_object* v_extendedDayPeriodShort_1631_; uint8_t v___x_1632_; lean_object* v___x_1633_; 
v_symbols_1630_ = lean_ctor_get(v_dateformat_1394_, 1);
v_extendedDayPeriodShort_1631_ = lean_ctor_get(v_symbols_1630_, 22);
v___x_1632_ = lean_unbox(v_data_1396_);
lean_dec(v_data_1396_);
v___x_1633_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatExtendedDayPeriod(v_extendedDayPeriodShort_1631_, v___x_1632_);
return v___x_1633_;
}
}
}
case 19:
{
lean_object* v_presentation_1634_; uint8_t v___x_1635_; lean_object* v___x_1636_; 
v_presentation_1634_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc(v_presentation_1634_);
lean_dec_ref_known(v_modifier_1395_, 1);
v___x_1635_ = 0;
v___x_1636_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1634_, v_data_1396_, v___x_1635_);
lean_dec(v_presentation_1634_);
return v___x_1636_;
}
case 20:
{
lean_object* v_presentation_1637_; uint8_t v___x_1638_; lean_object* v___x_1639_; 
v_presentation_1637_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc(v_presentation_1637_);
lean_dec_ref_known(v_modifier_1395_, 1);
v___x_1638_ = 0;
v___x_1639_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1637_, v_data_1396_, v___x_1638_);
lean_dec(v_presentation_1637_);
return v___x_1639_;
}
case 21:
{
lean_object* v_presentation_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; 
v_presentation_1640_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc(v_presentation_1640_);
lean_dec_ref_known(v_modifier_1395_, 1);
v___x_1641_ = 0;
v___x_1642_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1640_, v_data_1396_, v___x_1641_);
lean_dec(v_presentation_1640_);
return v___x_1642_;
}
case 22:
{
lean_object* v_presentation_1643_; uint8_t v___x_1644_; lean_object* v___x_1645_; 
v_presentation_1643_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc(v_presentation_1643_);
lean_dec_ref_known(v_modifier_1395_, 1);
v___x_1644_ = 0;
v___x_1645_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1643_, v_data_1396_, v___x_1644_);
lean_dec(v_presentation_1643_);
return v___x_1645_;
}
case 23:
{
lean_object* v_presentation_1646_; uint8_t v___x_1647_; lean_object* v___x_1648_; 
v_presentation_1646_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc(v_presentation_1646_);
lean_dec_ref_known(v_modifier_1395_, 1);
v___x_1647_ = 0;
v___x_1648_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1646_, v_data_1396_, v___x_1647_);
lean_dec(v_presentation_1646_);
return v___x_1648_;
}
case 24:
{
lean_object* v_presentation_1649_; uint8_t v___x_1650_; lean_object* v___x_1651_; 
v_presentation_1649_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc(v_presentation_1649_);
lean_dec_ref_known(v_modifier_1395_, 1);
v___x_1650_ = 0;
v___x_1651_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1649_, v_data_1396_, v___x_1650_);
lean_dec(v_presentation_1649_);
return v___x_1651_;
}
case 25:
{
lean_object* v_presentation_1652_; 
v_presentation_1652_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc(v_presentation_1652_);
lean_dec_ref_known(v_modifier_1395_, 1);
if (lean_obj_tag(v_presentation_1652_) == 0)
{
lean_object* v___x_1653_; uint8_t v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = lean_unsigned_to_nat(9u);
v___x_1654_ = 0;
v___x_1655_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v___x_1653_, v_data_1396_, v___x_1654_);
return v___x_1655_;
}
else
{
lean_object* v_digits_1656_; lean_object* v___x_1657_; uint32_t v___x_1658_; lean_object* v___x_1659_; lean_object* v_s_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v_digits_1656_ = lean_ctor_get(v_presentation_1652_, 0);
lean_inc(v_digits_1656_);
lean_dec_ref_known(v_presentation_1652_, 1);
v___x_1657_ = lean_unsigned_to_nat(9u);
v___x_1658_ = 48;
v___x_1659_ = l_Int_repr(v_data_1396_);
lean_dec(v_data_1396_);
v_s_1660_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1657_, v___x_1658_, v___x_1659_);
lean_dec_ref(v___x_1659_);
v___x_1661_ = lean_unsigned_to_nat(0u);
v___x_1662_ = lean_string_utf8_byte_size(v_s_1660_);
lean_inc_ref(v_s_1660_);
v___x_1663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1663_, 0, v_s_1660_);
lean_ctor_set(v___x_1663_, 1, v___x_1661_);
lean_ctor_set(v___x_1663_, 2, v___x_1662_);
v___x_1664_ = l_String_Slice_Pos_nextn(v___x_1663_, v___x_1661_, v_digits_1656_);
lean_dec_ref_known(v___x_1663_, 3);
v___x_1665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1665_, 0, v_s_1660_);
lean_ctor_set(v___x_1665_, 1, v___x_1661_);
lean_ctor_set(v___x_1665_, 2, v___x_1664_);
v___x_1666_ = l_String_Slice_toString(v___x_1665_);
lean_dec_ref_known(v___x_1665_, 3);
return v___x_1666_;
}
}
case 26:
{
lean_object* v_presentation_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; 
v_presentation_1667_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc(v_presentation_1667_);
lean_dec_ref_known(v_modifier_1395_, 1);
v___x_1668_ = 0;
v___x_1669_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1667_, v_data_1396_, v___x_1668_);
lean_dec(v_presentation_1667_);
return v___x_1669_;
}
case 27:
{
lean_object* v_presentation_1670_; uint8_t v___x_1671_; lean_object* v___x_1672_; 
v_presentation_1670_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc(v_presentation_1670_);
lean_dec_ref_known(v_modifier_1395_, 1);
v___x_1671_ = 0;
v___x_1672_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1670_, v_data_1396_, v___x_1671_);
lean_dec(v_presentation_1670_);
return v___x_1672_;
}
case 28:
{
lean_object* v_presentation_1673_; uint8_t v___x_1674_; lean_object* v___x_1675_; 
v_presentation_1673_ = lean_ctor_get(v_modifier_1395_, 0);
lean_inc(v_presentation_1673_);
lean_dec_ref_known(v_modifier_1395_, 1);
v___x_1674_ = 0;
v___x_1675_ = l___private_Std_Time_Format_Basic_0__Std_Time_pad(v_presentation_1673_, v_data_1396_, v___x_1674_);
lean_dec(v_presentation_1673_);
return v___x_1675_;
}
case 29:
{
uint8_t v_presentation_1676_; 
v_presentation_1676_ = lean_ctor_get_uint8(v_modifier_1395_, 0);
lean_dec_ref_known(v_modifier_1395_, 0);
if (v_presentation_1676_ == 0)
{
lean_object* v___x_1677_; 
lean_dec(v_data_1396_);
v___x_1677_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
return v___x_1677_;
}
else
{
return v_data_1396_;
}
}
case 32:
{
uint8_t v_presentation_1678_; 
v_presentation_1678_ = lean_ctor_get_uint8(v_modifier_1395_, 0);
lean_dec_ref_known(v_modifier_1395_, 0);
if (v_presentation_1678_ == 0)
{
lean_object* v_fst_1680_; lean_object* v_snd_1681_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1704_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1705_ = lean_int_dec_eq(v_data_1396_, v___x_1704_);
if (v___x_1705_ == 0)
{
uint8_t v___x_1706_; 
v___x_1706_ = lean_int_dec_le(v___x_1704_, v_data_1396_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1708_ = lean_int_neg(v_data_1396_);
lean_dec(v_data_1396_);
v_fst_1680_ = v___x_1707_;
v_snd_1681_ = v___x_1708_;
goto v___jp_1679_;
}
else
{
lean_object* v___x_1709_; 
v___x_1709_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v_fst_1680_ = v___x_1709_;
v_snd_1681_ = v_data_1396_;
goto v___jp_1679_;
}
}
else
{
lean_object* v___x_1710_; 
lean_dec(v_data_1396_);
v___x_1710_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1710_;
}
v___jp_1679_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v_t_1684_; lean_object* v_hour_1685_; lean_object* v_minute_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v___x_1682_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_1683_ = lean_int_mul(v_snd_1681_, v___x_1682_);
lean_dec(v_snd_1681_);
v_t_1684_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1683_);
lean_dec(v___x_1683_);
v_hour_1685_ = lean_ctor_get(v_t_1684_, 0);
lean_inc(v_hour_1685_);
v_minute_1686_ = lean_ctor_get(v_t_1684_, 1);
lean_inc(v_minute_1686_);
lean_dec_ref(v_t_1684_);
v___x_1687_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1688_ = lean_int_dec_eq(v_minute_1686_, v___x_1687_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; uint32_t v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1689_ = lean_unsigned_to_nat(2u);
v___x_1690_ = 48;
v___x_1691_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1692_ = lean_string_append(v___x_1691_, v_fst_1680_);
v___x_1693_ = l_Int_repr(v_hour_1685_);
lean_dec(v_hour_1685_);
v___x_1694_ = lean_string_append(v___x_1692_, v___x_1693_);
lean_dec_ref(v___x_1693_);
v___x_1695_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__0));
v___x_1696_ = lean_string_append(v___x_1694_, v___x_1695_);
v___x_1697_ = l_Int_repr(v_minute_1686_);
lean_dec(v_minute_1686_);
v___x_1698_ = l___private_Std_Time_Format_Basic_0__Std_Time_leftPadAscii(v___x_1689_, v___x_1690_, v___x_1697_);
lean_dec_ref(v___x_1697_);
v___x_1699_ = lean_string_append(v___x_1696_, v___x_1698_);
lean_dec_ref(v___x_1698_);
return v___x_1699_;
}
else
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
lean_dec(v_minute_1686_);
v___x_1700_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1701_ = lean_string_append(v___x_1700_, v_fst_1680_);
v___x_1702_ = l_Int_repr(v_hour_1685_);
lean_dec(v_hour_1685_);
v___x_1703_ = lean_string_append(v___x_1701_, v___x_1702_);
lean_dec_ref(v___x_1702_);
return v___x_1703_;
}
}
}
else
{
lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1711_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1712_ = lean_int_dec_eq(v_data_1396_, v___x_1711_);
if (v___x_1712_ == 0)
{
uint8_t v___x_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; uint8_t v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1713_ = 1;
v___x_1714_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1715_ = 0;
v___x_1716_ = 1;
v___x_1717_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1396_, v___x_1715_, v___x_1716_, v___x_1713_, v___x_1713_);
v___x_1718_ = lean_string_append(v___x_1714_, v___x_1717_);
lean_dec_ref(v___x_1717_);
return v___x_1718_;
}
else
{
lean_object* v___x_1719_; 
lean_dec(v_data_1396_);
v___x_1719_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1719_;
}
}
}
case 33:
{
uint8_t v_presentation_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
v_presentation_1720_ = lean_ctor_get_uint8(v_modifier_1395_, 0);
lean_dec_ref_known(v_modifier_1395_, 0);
v___x_1721_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1722_ = lean_int_dec_eq(v_data_1396_, v___x_1721_);
if (v___x_1722_ == 0)
{
uint8_t v___x_1723_; 
v___x_1723_ = 1;
switch(v_presentation_1720_)
{
case 0:
{
uint8_t v___x_1724_; uint8_t v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = 2;
v___x_1725_ = 1;
v___x_1726_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1396_, v___x_1724_, v___x_1725_, v___x_1722_, v___x_1723_);
return v___x_1726_;
}
case 1:
{
uint8_t v___x_1727_; uint8_t v___x_1728_; lean_object* v___x_1729_; 
v___x_1727_ = 0;
v___x_1728_ = 1;
v___x_1729_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1396_, v___x_1727_, v___x_1728_, v___x_1722_, v___x_1723_);
return v___x_1729_;
}
case 2:
{
uint8_t v___x_1730_; uint8_t v___x_1731_; lean_object* v___x_1732_; 
v___x_1730_ = 0;
v___x_1731_ = 1;
v___x_1732_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1396_, v___x_1730_, v___x_1731_, v___x_1723_, v___x_1723_);
return v___x_1732_;
}
case 3:
{
uint8_t v___x_1733_; uint8_t v___x_1734_; lean_object* v___x_1735_; 
v___x_1733_ = 0;
v___x_1734_ = 2;
v___x_1735_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1396_, v___x_1733_, v___x_1734_, v___x_1722_, v___x_1723_);
return v___x_1735_;
}
default: 
{
uint8_t v___x_1736_; uint8_t v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = 0;
v___x_1737_ = 2;
v___x_1738_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1396_, v___x_1736_, v___x_1737_, v___x_1723_, v___x_1723_);
return v___x_1738_;
}
}
}
else
{
lean_object* v___x_1739_; 
lean_dec(v_data_1396_);
v___x_1739_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
return v___x_1739_;
}
}
case 34:
{
uint8_t v_presentation_1740_; 
v_presentation_1740_ = lean_ctor_get_uint8(v_modifier_1395_, 0);
lean_dec_ref_known(v_modifier_1395_, 0);
switch(v_presentation_1740_)
{
case 0:
{
uint8_t v___x_1741_; uint8_t v___x_1742_; uint8_t v___x_1743_; uint8_t v___x_1744_; lean_object* v___x_1745_; 
v___x_1741_ = 2;
v___x_1742_ = 1;
v___x_1743_ = 0;
v___x_1744_ = 1;
v___x_1745_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1396_, v___x_1741_, v___x_1742_, v___x_1743_, v___x_1744_);
return v___x_1745_;
}
case 1:
{
uint8_t v___x_1746_; uint8_t v___x_1747_; uint8_t v___x_1748_; uint8_t v___x_1749_; lean_object* v___x_1750_; 
v___x_1746_ = 0;
v___x_1747_ = 1;
v___x_1748_ = 0;
v___x_1749_ = 1;
v___x_1750_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1396_, v___x_1746_, v___x_1747_, v___x_1748_, v___x_1749_);
return v___x_1750_;
}
case 2:
{
uint8_t v___x_1751_; uint8_t v___x_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; 
v___x_1751_ = 0;
v___x_1752_ = 1;
v___x_1753_ = 1;
v___x_1754_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1396_, v___x_1751_, v___x_1752_, v___x_1753_, v___x_1753_);
return v___x_1754_;
}
case 3:
{
uint8_t v___x_1755_; uint8_t v___x_1756_; uint8_t v___x_1757_; uint8_t v___x_1758_; lean_object* v___x_1759_; 
v___x_1755_ = 0;
v___x_1756_ = 2;
v___x_1757_ = 0;
v___x_1758_ = 1;
v___x_1759_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1396_, v___x_1755_, v___x_1756_, v___x_1757_, v___x_1758_);
return v___x_1759_;
}
default: 
{
uint8_t v___x_1760_; uint8_t v___x_1761_; uint8_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1760_ = 0;
v___x_1761_ = 2;
v___x_1762_ = 1;
v___x_1763_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1396_, v___x_1760_, v___x_1761_, v___x_1762_, v___x_1762_);
return v___x_1763_;
}
}
}
case 35:
{
uint8_t v_presentation_1764_; 
v_presentation_1764_ = lean_ctor_get_uint8(v_modifier_1395_, 0);
lean_dec_ref_known(v_modifier_1395_, 0);
switch(v_presentation_1764_)
{
case 0:
{
uint8_t v___x_1765_; uint8_t v___x_1766_; uint8_t v___x_1767_; uint8_t v___x_1768_; lean_object* v___x_1769_; 
v___x_1765_ = 0;
v___x_1766_ = 2;
v___x_1767_ = 0;
v___x_1768_ = 1;
v___x_1769_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1396_, v___x_1765_, v___x_1766_, v___x_1767_, v___x_1768_);
return v___x_1769_;
}
case 1:
{
lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1770_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1771_ = lean_int_dec_eq(v_data_1396_, v___x_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; uint8_t v___x_1773_; uint8_t v___x_1774_; uint8_t v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1772_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1773_ = 0;
v___x_1774_ = 1;
v___x_1775_ = 1;
v___x_1776_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1396_, v___x_1773_, v___x_1774_, v___x_1775_, v___x_1775_);
v___x_1777_ = lean_string_append(v___x_1772_, v___x_1776_);
lean_dec_ref(v___x_1776_);
return v___x_1777_;
}
else
{
lean_object* v___x_1778_; 
lean_dec(v_data_1396_);
v___x_1778_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
return v___x_1778_;
}
}
default: 
{
lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1779_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1780_ = lean_int_dec_eq(v_data_1396_, v___x_1779_);
if (v___x_1780_ == 0)
{
uint8_t v___x_1781_; uint8_t v___x_1782_; uint8_t v___x_1783_; lean_object* v___x_1784_; 
v___x_1781_ = 1;
v___x_1782_ = 0;
v___x_1783_ = 2;
v___x_1784_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_data_1396_, v___x_1782_, v___x_1783_, v___x_1781_, v___x_1781_);
return v___x_1784_;
}
else
{
lean_object* v___x_1785_; 
lean_dec(v_data_1396_);
v___x_1785_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
return v___x_1785_;
}
}
}
}
default: 
{
lean_dec_ref(v_modifier_1395_);
return v_data_1396_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___boxed(lean_object* v_dateformat_1786_, lean_object* v_modifier_1787_, lean_object* v_data_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_1786_, v_modifier_1787_, v_data_1788_);
lean_dec_ref(v_dateformat_1786_);
return v_res_1789_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0(void){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = lean_unsigned_to_nat(400u);
v___x_1791_ = lean_nat_to_int(v___x_1790_);
return v___x_1791_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = lean_unsigned_to_nat(4u);
v___x_1793_ = lean_nat_to_int(v___x_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(lean_object* v_modifier_1794_, lean_object* v_dateformat_1795_, lean_object* v_date_1796_){
_start:
{
uint8_t v___y_1798_; lean_object* v_month_1799_; lean_object* v_day_1800_; uint8_t v___y_1801_; uint8_t v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v_month_1810_; lean_object* v_day_1811_; uint8_t v_firstDayOfWeek_1815_; lean_object* v_minimalDaysInFirstWeek_1816_; lean_object* v_date_1817_; lean_object* v_timezone_1818_; uint8_t v___y_1837_; 
v_firstDayOfWeek_1815_ = lean_ctor_get_uint8(v_dateformat_1795_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_1816_ = lean_ctor_get(v_dateformat_1795_, 0);
v_date_1817_ = lean_ctor_get(v_date_1796_, 0);
v_timezone_1818_ = lean_ctor_get(v_date_1796_, 3);
switch(lean_obj_tag(v_modifier_1794_))
{
case 0:
{
lean_object* v___x_1850_; lean_object* v_date_1851_; lean_object* v_year_1852_; uint8_t v___x_1853_; lean_object* v___x_1854_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1850_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_date_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc_ref(v_date_1851_);
lean_dec(v___x_1850_);
v_year_1852_ = lean_ctor_get(v_date_1851_, 0);
lean_inc(v_year_1852_);
lean_dec_ref(v_date_1851_);
v___x_1853_ = l_Std_Time_Year_Offset_era(v_year_1852_);
lean_dec(v_year_1852_);
v___x_1854_ = lean_box(v___x_1853_);
return v___x_1854_;
}
case 1:
{
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
goto v___jp_1832_;
}
case 2:
{
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
goto v___jp_1832_;
}
case 3:
{
lean_object* v___x_1855_; lean_object* v_date_1856_; lean_object* v_year_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; uint8_t v___x_1865_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1855_ = lean_thunk_get_own(v_date_1817_);
v_date_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc_ref(v_date_1856_);
lean_dec(v___x_1855_);
v_year_1857_ = lean_ctor_get(v_date_1856_, 0);
lean_inc(v_year_1857_);
lean_dec_ref(v_date_1856_);
v___x_1858_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_1859_ = lean_int_mod(v_year_1857_, v___x_1858_);
v___x_1860_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1865_ = lean_int_dec_eq(v___x_1859_, v___x_1860_);
lean_dec(v___x_1859_);
if (v___x_1865_ == 0)
{
lean_dec(v_year_1857_);
v___y_1837_ = v___x_1865_;
goto v___jp_1836_;
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1866_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1867_ = lean_int_mod(v_year_1857_, v___x_1866_);
v___x_1868_ = lean_int_dec_eq(v___x_1867_, v___x_1860_);
lean_dec(v___x_1867_);
if (v___x_1868_ == 0)
{
if (v___x_1865_ == 0)
{
goto v___jp_1861_;
}
else
{
lean_dec(v_year_1857_);
v___y_1837_ = v___x_1865_;
goto v___jp_1836_;
}
}
else
{
goto v___jp_1861_;
}
}
v___jp_1861_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1862_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_1863_ = lean_int_mod(v_year_1857_, v___x_1862_);
lean_dec(v_year_1857_);
v___x_1864_ = lean_int_dec_eq(v___x_1863_, v___x_1860_);
lean_dec(v___x_1863_);
v___y_1837_ = v___x_1864_;
goto v___jp_1836_;
}
}
case 4:
{
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
goto v___jp_1828_;
}
case 5:
{
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
goto v___jp_1828_;
}
case 6:
{
lean_object* v___x_1869_; lean_object* v_date_1870_; lean_object* v_day_1871_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1869_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_date_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc_ref(v_date_1870_);
lean_dec(v___x_1869_);
v_day_1871_ = lean_ctor_get(v_date_1870_, 2);
lean_inc(v_day_1871_);
lean_dec_ref(v_date_1870_);
return v_day_1871_;
}
case 7:
{
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
goto v___jp_1824_;
}
case 8:
{
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
goto v___jp_1824_;
}
case 9:
{
lean_object* v___x_1872_; lean_object* v_date_1873_; lean_object* v___x_1874_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1872_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_date_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc_ref(v_date_1873_);
lean_dec(v___x_1872_);
v___x_1874_ = l_Std_Time_PlainDate_weekYear(v_date_1873_, v_firstDayOfWeek_1815_, v_minimalDaysInFirstWeek_1816_);
return v___x_1874_;
}
case 10:
{
lean_object* v___x_1875_; lean_object* v_date_1876_; lean_object* v___x_1877_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1875_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_date_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc_ref(v_date_1876_);
lean_dec(v___x_1875_);
v___x_1877_ = l_Std_Time_PlainDate_weekOfYear(v_date_1876_, v_firstDayOfWeek_1815_, v_minimalDaysInFirstWeek_1816_);
return v___x_1877_;
}
case 11:
{
lean_object* v___x_1878_; lean_object* v_date_1879_; lean_object* v___x_1880_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1878_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_date_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc_ref(v_date_1879_);
lean_dec(v___x_1878_);
v___x_1880_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1879_, v_firstDayOfWeek_1815_);
return v___x_1880_;
}
case 12:
{
lean_object* v___x_1881_; lean_object* v_date_1882_; uint8_t v___x_1883_; lean_object* v___x_1884_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1881_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_date_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc_ref(v_date_1882_);
lean_dec(v___x_1881_);
v___x_1883_ = l_Std_Time_PlainDate_weekday(v_date_1882_);
v___x_1884_ = lean_box(v___x_1883_);
return v___x_1884_;
}
case 13:
{
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
goto v___jp_1819_;
}
case 14:
{
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
goto v___jp_1819_;
}
case 15:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Std_Time_DateTime_alignedWeekOfMonth(v_date_1796_);
lean_dec_ref(v_date_1796_);
return v___x_1885_;
}
case 16:
{
lean_object* v___x_1886_; lean_object* v_time_1887_; lean_object* v_hour_1888_; uint8_t v___x_1889_; lean_object* v___x_1890_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1886_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_time_1887_ = lean_ctor_get(v___x_1886_, 1);
lean_inc_ref(v_time_1887_);
lean_dec(v___x_1886_);
v_hour_1888_ = lean_ctor_get(v_time_1887_, 0);
lean_inc(v_hour_1888_);
lean_dec_ref(v_time_1887_);
v___x_1889_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1888_);
lean_dec(v_hour_1888_);
v___x_1890_ = lean_box(v___x_1889_);
return v___x_1890_;
}
case 17:
{
lean_object* v___x_1891_; lean_object* v_time_1892_; lean_object* v_hour_1893_; lean_object* v_minute_1894_; lean_object* v_second_1895_; uint8_t v___x_1896_; lean_object* v___x_1897_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1891_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_time_1892_ = lean_ctor_get(v___x_1891_, 1);
lean_inc_ref(v_time_1892_);
lean_dec(v___x_1891_);
v_hour_1893_ = lean_ctor_get(v_time_1892_, 0);
lean_inc(v_hour_1893_);
v_minute_1894_ = lean_ctor_get(v_time_1892_, 1);
lean_inc(v_minute_1894_);
v_second_1895_ = lean_ctor_get(v_time_1892_, 2);
lean_inc(v_second_1895_);
lean_dec_ref(v_time_1892_);
v___x_1896_ = l_Std_Time_classifyDayPeriod(v_hour_1893_, v_minute_1894_, v_second_1895_);
lean_dec(v_second_1895_);
lean_dec(v_minute_1894_);
lean_dec(v_hour_1893_);
v___x_1897_ = lean_box(v___x_1896_);
return v___x_1897_;
}
case 18:
{
lean_object* v___x_1898_; lean_object* v_time_1899_; lean_object* v_hour_1900_; lean_object* v_minute_1901_; lean_object* v_second_1902_; uint8_t v___x_1903_; lean_object* v___x_1904_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1898_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_time_1899_ = lean_ctor_get(v___x_1898_, 1);
lean_inc_ref(v_time_1899_);
lean_dec(v___x_1898_);
v_hour_1900_ = lean_ctor_get(v_time_1899_, 0);
lean_inc(v_hour_1900_);
v_minute_1901_ = lean_ctor_get(v_time_1899_, 1);
lean_inc(v_minute_1901_);
v_second_1902_ = lean_ctor_get(v_time_1899_, 2);
lean_inc(v_second_1902_);
lean_dec_ref(v_time_1899_);
v___x_1903_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1900_, v_minute_1901_, v_second_1902_);
lean_dec(v_second_1902_);
lean_dec(v_minute_1901_);
lean_dec(v_hour_1900_);
v___x_1904_ = lean_box(v___x_1903_);
return v___x_1904_;
}
case 19:
{
lean_object* v___x_1905_; lean_object* v_time_1906_; lean_object* v_hour_1907_; lean_object* v___x_1908_; lean_object* v_fst_1909_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1905_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_time_1906_ = lean_ctor_get(v___x_1905_, 1);
lean_inc_ref(v_time_1906_);
lean_dec(v___x_1905_);
v_hour_1907_ = lean_ctor_get(v_time_1906_, 0);
lean_inc(v_hour_1907_);
lean_dec_ref(v_time_1906_);
v___x_1908_ = l_Std_Time_HourMarker_toRelative(v_hour_1907_);
v_fst_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_fst_1909_);
lean_dec_ref(v___x_1908_);
return v_fst_1909_;
}
case 20:
{
lean_object* v___x_1910_; lean_object* v_time_1911_; lean_object* v_hour_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1910_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_time_1911_ = lean_ctor_get(v___x_1910_, 1);
lean_inc_ref(v_time_1911_);
lean_dec(v___x_1910_);
v_hour_1912_ = lean_ctor_get(v_time_1911_, 0);
lean_inc(v_hour_1912_);
lean_dec_ref(v_time_1911_);
v___x_1913_ = lean_obj_once(&l_Std_Time_classifyDayPeriod___closed__0, &l_Std_Time_classifyDayPeriod___closed__0_once, _init_l_Std_Time_classifyDayPeriod___closed__0);
v___x_1914_ = lean_int_emod(v_hour_1912_, v___x_1913_);
lean_dec(v_hour_1912_);
return v___x_1914_;
}
case 21:
{
lean_object* v___x_1915_; lean_object* v_time_1916_; lean_object* v_hour_1917_; lean_object* v___x_1918_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1915_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_time_1916_ = lean_ctor_get(v___x_1915_, 1);
lean_inc_ref(v_time_1916_);
lean_dec(v___x_1915_);
v_hour_1917_ = lean_ctor_get(v_time_1916_, 0);
lean_inc(v_hour_1917_);
lean_dec_ref(v_time_1916_);
v___x_1918_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_1917_);
lean_dec(v_hour_1917_);
return v___x_1918_;
}
case 22:
{
lean_object* v___x_1919_; lean_object* v_time_1920_; lean_object* v_hour_1921_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1919_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_time_1920_ = lean_ctor_get(v___x_1919_, 1);
lean_inc_ref(v_time_1920_);
lean_dec(v___x_1919_);
v_hour_1921_ = lean_ctor_get(v_time_1920_, 0);
lean_inc(v_hour_1921_);
lean_dec_ref(v_time_1920_);
return v_hour_1921_;
}
case 23:
{
lean_object* v___x_1922_; lean_object* v_time_1923_; lean_object* v_minute_1924_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1922_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_time_1923_ = lean_ctor_get(v___x_1922_, 1);
lean_inc_ref(v_time_1923_);
lean_dec(v___x_1922_);
v_minute_1924_ = lean_ctor_get(v_time_1923_, 1);
lean_inc(v_minute_1924_);
lean_dec_ref(v_time_1923_);
return v_minute_1924_;
}
case 24:
{
lean_object* v___x_1925_; lean_object* v_time_1926_; lean_object* v_second_1927_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1925_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_time_1926_ = lean_ctor_get(v___x_1925_, 1);
lean_inc_ref(v_time_1926_);
lean_dec(v___x_1925_);
v_second_1927_ = lean_ctor_get(v_time_1926_, 2);
lean_inc(v_second_1927_);
lean_dec_ref(v_time_1926_);
return v_second_1927_;
}
case 25:
{
lean_object* v___x_1928_; lean_object* v_time_1929_; lean_object* v_nanosecond_1930_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1928_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_time_1929_ = lean_ctor_get(v___x_1928_, 1);
lean_inc_ref(v_time_1929_);
lean_dec(v___x_1928_);
v_nanosecond_1930_ = lean_ctor_get(v_time_1929_, 3);
lean_inc(v_nanosecond_1930_);
lean_dec_ref(v_time_1929_);
return v_nanosecond_1930_;
}
case 26:
{
lean_object* v___x_1931_; lean_object* v_time_1932_; lean_object* v___x_1933_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1931_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_time_1932_ = lean_ctor_get(v___x_1931_, 1);
lean_inc_ref(v_time_1932_);
lean_dec(v___x_1931_);
v___x_1933_ = l_Std_Time_PlainTime_toMilliseconds(v_time_1932_);
lean_dec_ref(v_time_1932_);
return v___x_1933_;
}
case 27:
{
lean_object* v___x_1934_; lean_object* v_time_1935_; lean_object* v_nanosecond_1936_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1934_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_time_1935_ = lean_ctor_get(v___x_1934_, 1);
lean_inc_ref(v_time_1935_);
lean_dec(v___x_1934_);
v_nanosecond_1936_ = lean_ctor_get(v_time_1935_, 3);
lean_inc(v_nanosecond_1936_);
lean_dec_ref(v_time_1935_);
return v_nanosecond_1936_;
}
case 28:
{
lean_object* v___x_1937_; lean_object* v_time_1938_; lean_object* v___x_1939_; 
lean_inc_ref(v_date_1817_);
lean_dec_ref(v_date_1796_);
v___x_1937_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_time_1938_ = lean_ctor_get(v___x_1937_, 1);
lean_inc_ref(v_time_1938_);
lean_dec(v___x_1937_);
v___x_1939_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1938_);
lean_dec_ref(v_time_1938_);
return v___x_1939_;
}
case 29:
{
uint8_t v_presentation_1940_; 
lean_inc_ref(v_timezone_1818_);
lean_dec_ref(v_date_1796_);
v_presentation_1940_ = lean_ctor_get_uint8(v_modifier_1794_, 0);
if (v_presentation_1940_ == 0)
{
lean_object* v___x_1941_; 
lean_dec_ref(v_timezone_1818_);
v___x_1941_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
return v___x_1941_;
}
else
{
lean_object* v_offset_1942_; lean_object* v_name_1943_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v_offset_1942_ = lean_ctor_get(v_timezone_1818_, 0);
lean_inc(v_offset_1942_);
v_name_1943_ = lean_ctor_get(v_timezone_1818_, 1);
lean_inc_ref(v_name_1943_);
lean_dec_ref(v_timezone_1818_);
v___x_1958_ = lean_string_utf8_byte_size(v_name_1943_);
v___x_1959_ = lean_unsigned_to_nat(1u);
v___x_1960_ = lean_nat_dec_le(v___x_1959_, v___x_1958_);
if (v___x_1960_ == 0)
{
goto v___jp_1951_;
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1961_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_1962_ = lean_unsigned_to_nat(0u);
v___x_1963_ = lean_string_memcmp(v_name_1943_, v___x_1961_, v___x_1962_, v___x_1962_, v___x_1959_);
if (v___x_1963_ == 0)
{
goto v___jp_1951_;
}
else
{
lean_dec_ref(v_name_1943_);
goto v___jp_1944_;
}
}
v___jp_1944_:
{
uint8_t v___x_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; uint8_t v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1945_ = 1;
v___x_1946_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1947_ = 0;
v___x_1948_ = 1;
v___x_1949_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1942_, v___x_1947_, v___x_1948_, v___x_1945_, v___x_1945_);
v___x_1950_ = lean_string_append(v___x_1946_, v___x_1949_);
lean_dec_ref(v___x_1949_);
return v___x_1950_;
}
v___jp_1951_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
v___x_1952_ = lean_string_utf8_byte_size(v_name_1943_);
v___x_1953_ = lean_unsigned_to_nat(1u);
v___x_1954_ = lean_nat_dec_le(v___x_1953_, v___x_1952_);
if (v___x_1954_ == 0)
{
lean_dec(v_offset_1942_);
return v_name_1943_;
}
else
{
lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v___x_1955_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1956_ = lean_unsigned_to_nat(0u);
v___x_1957_ = lean_string_memcmp(v_name_1943_, v___x_1955_, v___x_1956_, v___x_1956_, v___x_1953_);
if (v___x_1957_ == 0)
{
lean_dec(v_offset_1942_);
return v_name_1943_;
}
else
{
lean_dec_ref(v_name_1943_);
goto v___jp_1944_;
}
}
}
}
}
case 30:
{
uint8_t v_presentation_1964_; 
lean_inc_ref(v_timezone_1818_);
lean_dec_ref(v_date_1796_);
v_presentation_1964_ = lean_ctor_get_uint8(v_modifier_1794_, 0);
if (v_presentation_1964_ == 0)
{
lean_object* v_offset_1965_; lean_object* v_abbreviation_1966_; lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v_offset_1965_ = lean_ctor_get(v_timezone_1818_, 0);
lean_inc(v_offset_1965_);
v_abbreviation_1966_ = lean_ctor_get(v_timezone_1818_, 2);
lean_inc_ref(v_abbreviation_1966_);
lean_dec_ref(v_timezone_1818_);
v___x_1981_ = lean_string_utf8_byte_size(v_abbreviation_1966_);
v___x_1982_ = lean_unsigned_to_nat(1u);
v___x_1983_ = lean_nat_dec_le(v___x_1982_, v___x_1981_);
if (v___x_1983_ == 0)
{
goto v___jp_1974_;
}
else
{
lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1984_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_1985_ = lean_unsigned_to_nat(0u);
v___x_1986_ = lean_string_memcmp(v_abbreviation_1966_, v___x_1984_, v___x_1985_, v___x_1985_, v___x_1982_);
if (v___x_1986_ == 0)
{
goto v___jp_1974_;
}
else
{
lean_dec_ref(v_abbreviation_1966_);
goto v___jp_1967_;
}
}
v___jp_1967_:
{
uint8_t v___x_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; uint8_t v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1968_ = 1;
v___x_1969_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1970_ = 0;
v___x_1971_ = 1;
v___x_1972_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1965_, v___x_1970_, v___x_1971_, v___x_1968_, v___x_1968_);
v___x_1973_ = lean_string_append(v___x_1969_, v___x_1972_);
lean_dec_ref(v___x_1972_);
return v___x_1973_;
}
v___jp_1974_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1975_ = lean_string_utf8_byte_size(v_abbreviation_1966_);
v___x_1976_ = lean_unsigned_to_nat(1u);
v___x_1977_ = lean_nat_dec_le(v___x_1976_, v___x_1975_);
if (v___x_1977_ == 0)
{
lean_dec(v_offset_1965_);
return v_abbreviation_1966_;
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; uint8_t v___x_1980_; 
v___x_1978_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_1979_ = lean_unsigned_to_nat(0u);
v___x_1980_ = lean_string_memcmp(v_abbreviation_1966_, v___x_1978_, v___x_1979_, v___x_1979_, v___x_1976_);
if (v___x_1980_ == 0)
{
lean_dec(v_offset_1965_);
return v_abbreviation_1966_;
}
else
{
lean_dec_ref(v_abbreviation_1966_);
goto v___jp_1967_;
}
}
}
}
else
{
lean_object* v_offset_1987_; lean_object* v_name_1988_; lean_object* v___x_2003_; lean_object* v___x_2004_; uint8_t v___x_2005_; 
v_offset_1987_ = lean_ctor_get(v_timezone_1818_, 0);
lean_inc(v_offset_1987_);
v_name_1988_ = lean_ctor_get(v_timezone_1818_, 1);
lean_inc_ref(v_name_1988_);
lean_dec_ref(v_timezone_1818_);
v___x_2003_ = lean_string_utf8_byte_size(v_name_1988_);
v___x_2004_ = lean_unsigned_to_nat(1u);
v___x_2005_ = lean_nat_dec_le(v___x_2004_, v___x_2003_);
if (v___x_2005_ == 0)
{
goto v___jp_1996_;
}
else
{
lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v___x_2006_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2007_ = lean_unsigned_to_nat(0u);
v___x_2008_ = lean_string_memcmp(v_name_1988_, v___x_2006_, v___x_2007_, v___x_2007_, v___x_2004_);
if (v___x_2008_ == 0)
{
goto v___jp_1996_;
}
else
{
lean_dec_ref(v_name_1988_);
goto v___jp_1989_;
}
}
v___jp_1989_:
{
uint8_t v___x_1990_; lean_object* v___x_1991_; uint8_t v___x_1992_; uint8_t v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1990_ = 1;
v___x_1991_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_1992_ = 0;
v___x_1993_ = 1;
v___x_1994_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_1987_, v___x_1992_, v___x_1993_, v___x_1990_, v___x_1990_);
v___x_1995_ = lean_string_append(v___x_1991_, v___x_1994_);
lean_dec_ref(v___x_1994_);
return v___x_1995_;
}
v___jp_1996_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1997_ = lean_string_utf8_byte_size(v_name_1988_);
v___x_1998_ = lean_unsigned_to_nat(1u);
v___x_1999_ = lean_nat_dec_le(v___x_1998_, v___x_1997_);
if (v___x_1999_ == 0)
{
lean_dec(v_offset_1987_);
return v_name_1988_;
}
else
{
lean_object* v___x_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; 
v___x_2000_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2001_ = lean_unsigned_to_nat(0u);
v___x_2002_ = lean_string_memcmp(v_name_1988_, v___x_2000_, v___x_2001_, v___x_2001_, v___x_1998_);
if (v___x_2002_ == 0)
{
lean_dec(v_offset_1987_);
return v_name_1988_;
}
else
{
lean_dec_ref(v_name_1988_);
goto v___jp_1989_;
}
}
}
}
}
case 31:
{
uint8_t v_presentation_2009_; 
lean_inc_ref(v_timezone_1818_);
lean_dec_ref(v_date_1796_);
v_presentation_2009_ = lean_ctor_get_uint8(v_modifier_1794_, 0);
if (v_presentation_2009_ == 0)
{
lean_object* v_offset_2010_; lean_object* v_abbreviation_2011_; lean_object* v___x_2026_; lean_object* v___x_2027_; uint8_t v___x_2028_; 
v_offset_2010_ = lean_ctor_get(v_timezone_1818_, 0);
lean_inc(v_offset_2010_);
v_abbreviation_2011_ = lean_ctor_get(v_timezone_1818_, 2);
lean_inc_ref(v_abbreviation_2011_);
lean_dec_ref(v_timezone_1818_);
v___x_2026_ = lean_string_utf8_byte_size(v_abbreviation_2011_);
v___x_2027_ = lean_unsigned_to_nat(1u);
v___x_2028_ = lean_nat_dec_le(v___x_2027_, v___x_2026_);
if (v___x_2028_ == 0)
{
goto v___jp_2019_;
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2030_; uint8_t v___x_2031_; 
v___x_2029_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2030_ = lean_unsigned_to_nat(0u);
v___x_2031_ = lean_string_memcmp(v_abbreviation_2011_, v___x_2029_, v___x_2030_, v___x_2030_, v___x_2027_);
if (v___x_2031_ == 0)
{
goto v___jp_2019_;
}
else
{
lean_dec_ref(v_abbreviation_2011_);
goto v___jp_2012_;
}
}
v___jp_2012_:
{
uint8_t v___x_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; uint8_t v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2013_ = 1;
v___x_2014_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2015_ = 0;
v___x_2016_ = 1;
v___x_2017_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2010_, v___x_2015_, v___x_2016_, v___x_2013_, v___x_2013_);
v___x_2018_ = lean_string_append(v___x_2014_, v___x_2017_);
lean_dec_ref(v___x_2017_);
return v___x_2018_;
}
v___jp_2019_:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2020_ = lean_string_utf8_byte_size(v_abbreviation_2011_);
v___x_2021_ = lean_unsigned_to_nat(1u);
v___x_2022_ = lean_nat_dec_le(v___x_2021_, v___x_2020_);
if (v___x_2022_ == 0)
{
lean_dec(v_offset_2010_);
return v_abbreviation_2011_;
}
else
{
lean_object* v___x_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; 
v___x_2023_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2024_ = lean_unsigned_to_nat(0u);
v___x_2025_ = lean_string_memcmp(v_abbreviation_2011_, v___x_2023_, v___x_2024_, v___x_2024_, v___x_2021_);
if (v___x_2025_ == 0)
{
lean_dec(v_offset_2010_);
return v_abbreviation_2011_;
}
else
{
lean_dec_ref(v_abbreviation_2011_);
goto v___jp_2012_;
}
}
}
}
else
{
lean_object* v_offset_2032_; lean_object* v_name_2033_; lean_object* v___x_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; 
v_offset_2032_ = lean_ctor_get(v_timezone_1818_, 0);
lean_inc(v_offset_2032_);
v_name_2033_ = lean_ctor_get(v_timezone_1818_, 1);
lean_inc_ref(v_name_2033_);
lean_dec_ref(v_timezone_1818_);
v___x_2048_ = lean_string_utf8_byte_size(v_name_2033_);
v___x_2049_ = lean_unsigned_to_nat(1u);
v___x_2050_ = lean_nat_dec_le(v___x_2049_, v___x_2048_);
if (v___x_2050_ == 0)
{
goto v___jp_2041_;
}
else
{
lean_object* v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v___x_2051_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_toSigned___closed__0));
v___x_2052_ = lean_unsigned_to_nat(0u);
v___x_2053_ = lean_string_memcmp(v_name_2033_, v___x_2051_, v___x_2052_, v___x_2052_, v___x_2049_);
if (v___x_2053_ == 0)
{
goto v___jp_2041_;
}
else
{
lean_dec_ref(v_name_2033_);
goto v___jp_2034_;
}
}
v___jp_2034_:
{
uint8_t v___x_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; uint8_t v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2035_ = 1;
v___x_2036_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_2037_ = 0;
v___x_2038_ = 1;
v___x_2039_ = l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString(v_offset_2032_, v___x_2037_, v___x_2038_, v___x_2035_, v___x_2035_);
v___x_2040_ = lean_string_append(v___x_2036_, v___x_2039_);
lean_dec_ref(v___x_2039_);
return v___x_2040_;
}
v___jp_2041_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2042_ = lean_string_utf8_byte_size(v_name_2033_);
v___x_2043_ = lean_unsigned_to_nat(1u);
v___x_2044_ = lean_nat_dec_le(v___x_2043_, v___x_2042_);
if (v___x_2044_ == 0)
{
lean_dec(v_offset_2032_);
return v_name_2033_;
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
v___x_2045_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
v___x_2046_ = lean_unsigned_to_nat(0u);
v___x_2047_ = lean_string_memcmp(v_name_2033_, v___x_2045_, v___x_2046_, v___x_2046_, v___x_2043_);
if (v___x_2047_ == 0)
{
lean_dec(v_offset_2032_);
return v_name_2033_;
}
else
{
lean_dec_ref(v_name_2033_);
goto v___jp_2034_;
}
}
}
}
}
default: 
{
lean_object* v_offset_2054_; 
lean_inc_ref(v_timezone_1818_);
lean_dec_ref(v_date_1796_);
v_offset_2054_ = lean_ctor_get(v_timezone_1818_, 0);
lean_inc(v_offset_2054_);
lean_dec_ref(v_timezone_1818_);
return v_offset_2054_;
}
}
v___jp_1797_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1802_, 0, v_month_1799_);
lean_ctor_set(v___x_1802_, 1, v_day_1800_);
v___x_1803_ = l_Std_Time_ValidDate_dayOfYear(v___y_1801_, v___x_1802_);
lean_dec_ref_known(v___x_1802_, 2);
v___x_1804_ = lean_box(v___y_1798_);
v___x_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
lean_ctor_set(v___x_1805_, 1, v___x_1803_);
return v___x_1805_;
}
v___jp_1806_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1812_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_1813_ = lean_int_mod(v___y_1809_, v___x_1812_);
lean_dec(v___y_1809_);
v___x_1814_ = lean_int_dec_eq(v___x_1813_, v___y_1808_);
lean_dec(v___x_1813_);
v___y_1798_ = v___y_1807_;
v_month_1799_ = v_month_1810_;
v_day_1800_ = v_day_1811_;
v___y_1801_ = v___x_1814_;
goto v___jp_1797_;
}
v___jp_1819_:
{
lean_object* v___x_1820_; lean_object* v_date_1821_; uint8_t v___x_1822_; lean_object* v___x_1823_; 
v___x_1820_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_date_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc_ref(v_date_1821_);
lean_dec(v___x_1820_);
v___x_1822_ = l_Std_Time_PlainDate_weekday(v_date_1821_);
v___x_1823_ = lean_box(v___x_1822_);
return v___x_1823_;
}
v___jp_1824_:
{
lean_object* v___x_1825_; lean_object* v_date_1826_; lean_object* v___x_1827_; 
v___x_1825_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_date_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc_ref(v_date_1826_);
lean_dec(v___x_1825_);
v___x_1827_ = l_Std_Time_PlainDate_quarter(v_date_1826_);
lean_dec_ref(v_date_1826_);
return v___x_1827_;
}
v___jp_1828_:
{
lean_object* v___x_1829_; lean_object* v_date_1830_; lean_object* v_month_1831_; 
v___x_1829_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_date_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc_ref(v_date_1830_);
lean_dec(v___x_1829_);
v_month_1831_ = lean_ctor_get(v_date_1830_, 1);
lean_inc(v_month_1831_);
lean_dec_ref(v_date_1830_);
return v_month_1831_;
}
v___jp_1832_:
{
lean_object* v___x_1833_; lean_object* v_date_1834_; lean_object* v_year_1835_; 
v___x_1833_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_date_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc_ref(v_date_1834_);
lean_dec(v___x_1833_);
v_year_1835_ = lean_ctor_get(v_date_1834_, 0);
lean_inc(v_year_1835_);
lean_dec_ref(v_date_1834_);
return v_year_1835_;
}
v___jp_1836_:
{
lean_object* v___x_1838_; lean_object* v_date_1839_; lean_object* v_year_1840_; lean_object* v_month_1841_; lean_object* v_day_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; 
v___x_1838_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_date_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc_ref(v_date_1839_);
lean_dec(v___x_1838_);
v_year_1840_ = lean_ctor_get(v_date_1839_, 0);
lean_inc(v_year_1840_);
v_month_1841_ = lean_ctor_get(v_date_1839_, 1);
lean_inc(v_month_1841_);
v_day_1842_ = lean_ctor_get(v_date_1839_, 2);
lean_inc(v_day_1842_);
lean_dec_ref(v_date_1839_);
v___x_1843_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_1844_ = lean_int_mod(v_year_1840_, v___x_1843_);
v___x_1845_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_1846_ = lean_int_dec_eq(v___x_1844_, v___x_1845_);
lean_dec(v___x_1844_);
if (v___x_1846_ == 0)
{
lean_dec(v_year_1840_);
v___y_1798_ = v___y_1837_;
v_month_1799_ = v_month_1841_;
v_day_1800_ = v_day_1842_;
v___y_1801_ = v___x_1846_;
goto v___jp_1797_;
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1847_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_1848_ = lean_int_mod(v_year_1840_, v___x_1847_);
v___x_1849_ = lean_int_dec_eq(v___x_1848_, v___x_1845_);
lean_dec(v___x_1848_);
if (v___x_1849_ == 0)
{
if (v___x_1846_ == 0)
{
v___y_1807_ = v___y_1837_;
v___y_1808_ = v___x_1845_;
v___y_1809_ = v_year_1840_;
v_month_1810_ = v_month_1841_;
v_day_1811_ = v_day_1842_;
goto v___jp_1806_;
}
else
{
lean_dec(v_year_1840_);
v___y_1798_ = v___y_1837_;
v_month_1799_ = v_month_1841_;
v_day_1800_ = v_day_1842_;
v___y_1801_ = v___x_1846_;
goto v___jp_1797_;
}
}
else
{
v___y_1807_ = v___y_1837_;
v___y_1808_ = v___x_1845_;
v___y_1809_ = v_year_1840_;
v_month_1810_ = v_month_1841_;
v_day_1811_ = v_day_1842_;
goto v___jp_1806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___boxed(lean_object* v_modifier_2055_, lean_object* v_dateformat_2056_, lean_object* v_date_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(v_modifier_2055_, v_dateformat_2056_, v_date_2057_);
lean_dec_ref(v_dateformat_2056_);
lean_dec_ref(v_modifier_2055_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___lam__0(lean_object* v___x_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2059_);
v___x_2062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___y_2060_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___lam__0(lean_object* v___x_2063_, lean_object* v_b_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_fst_2066_; lean_object* v_snd_2067_; lean_object* v___x_2068_; 
v_fst_2066_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_fst_2066_);
v_snd_2067_ = lean_ctor_get(v___x_2063_, 1);
lean_inc(v_snd_2067_);
lean_dec_ref(v___x_2063_);
lean_inc_ref(v___y_2065_);
v___x_2068_ = lean_apply_1(v_b_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_dec(v_snd_2067_);
lean_dec(v_fst_2066_);
lean_dec_ref(v___y_2065_);
return v___x_2068_;
}
else
{
lean_object* v_pos_2069_; lean_object* v_snd_2070_; lean_object* v_snd_2071_; uint8_t v_decide_2072_; 
v_pos_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_pos_2069_);
v_snd_2070_ = lean_ctor_get(v___y_2065_, 1);
lean_inc(v_snd_2070_);
lean_dec_ref(v___y_2065_);
v_snd_2071_ = lean_ctor_get(v_pos_2069_, 1);
v_decide_2072_ = lean_nat_dec_eq(v_snd_2070_, v_snd_2071_);
lean_dec(v_snd_2070_);
if (v_decide_2072_ == 0)
{
lean_dec(v_pos_2069_);
lean_dec(v_snd_2067_);
lean_dec(v_fst_2066_);
return v___x_2068_;
}
else
{
lean_object* v___x_2073_; 
lean_dec_ref_known(v___x_2068_, 2);
v___x_2073_ = l_Std_Internal_Parsec_String_pstring(v_fst_2066_, v_pos_2069_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_pos_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
v_pos_2074_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; 
v_unused_2082_ = lean_ctor_get(v___x_2073_, 1);
lean_dec(v_unused_2082_);
v___x_2076_ = v___x_2073_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_pos_2074_);
lean_dec(v___x_2073_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 1, v_snd_2067_);
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_pos_2074_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v_snd_2067_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
else
{
lean_object* v_pos_2083_; lean_object* v_err_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_dec(v_snd_2067_);
v_pos_2083_ = lean_ctor_get(v___x_2073_, 0);
v_err_2084_ = lean_ctor_get(v___x_2073_, 1);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2073_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_err_2084_);
lean_inc(v_pos_2083_);
lean_dec(v___x_2073_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_pos_2083_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_err_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(lean_object* v_as_2092_, size_t v_i_2093_, size_t v_stop_2094_, lean_object* v_b_2095_, lean_object* v___y_2096_){
_start:
{
uint8_t v___x_2097_; 
v___x_2097_ = lean_usize_dec_eq(v_i_2093_, v_stop_2094_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; lean_object* v___f_2099_; size_t v___x_2100_; size_t v___x_2101_; 
v___x_2098_ = lean_array_uget_borrowed(v_as_2092_, v_i_2093_);
lean_inc(v___x_2098_);
v___f_2099_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2099_, 0, v___x_2098_);
lean_closure_set(v___f_2099_, 1, v_b_2095_);
v___x_2100_ = ((size_t)1ULL);
v___x_2101_ = lean_usize_add(v_i_2093_, v___x_2100_);
v_i_2093_ = v___x_2101_;
v_b_2095_ = v___f_2099_;
goto _start;
}
else
{
lean_object* v___x_2103_; 
v___x_2103_ = lean_apply_1(v_b_2095_, v___y_2096_);
return v___x_2103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg___boxed(lean_object* v_as_2104_, lean_object* v_i_2105_, lean_object* v_stop_2106_, lean_object* v_b_2107_, lean_object* v___y_2108_){
_start:
{
size_t v_i_boxed_2109_; size_t v_stop_boxed_2110_; lean_object* v_res_2111_; 
v_i_boxed_2109_ = lean_unbox_usize(v_i_2105_);
lean_dec(v_i_2105_);
v_stop_boxed_2110_ = lean_unbox_usize(v_stop_2106_);
lean_dec(v_stop_2106_);
v_res_2111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_as_2104_, v_i_boxed_2109_, v_stop_boxed_2110_, v_b_2107_, v___y_2108_);
lean_dec_ref(v_as_2104_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(lean_object* v_pairs_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2119_ = lean_unsigned_to_nat(0u);
v___x_2120_ = lean_array_get_size(v_pairs_2117_);
v___x_2121_ = lean_nat_dec_lt(v___x_2119_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__1));
v___x_2123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2123_, 0, v_a_2118_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
return v___x_2123_;
}
else
{
lean_object* v___f_2124_; uint8_t v___x_2125_; 
v___f_2124_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__2));
v___x_2125_ = lean_nat_dec_le(v___x_2120_, v___x_2120_);
if (v___x_2125_ == 0)
{
if (v___x_2121_ == 0)
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___closed__1));
v___x_2127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2127_, 0, v_a_2118_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
return v___x_2127_;
}
else
{
size_t v___x_2128_; size_t v___x_2129_; lean_object* v___x_2130_; 
v___x_2128_ = ((size_t)0ULL);
v___x_2129_ = lean_usize_of_nat(v___x_2120_);
v___x_2130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_pairs_2117_, v___x_2128_, v___x_2129_, v___f_2124_, v_a_2118_);
return v___x_2130_;
}
}
else
{
size_t v___x_2131_; size_t v___x_2132_; lean_object* v___x_2133_; 
v___x_2131_ = ((size_t)0ULL);
v___x_2132_ = lean_usize_of_nat(v___x_2120_);
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_pairs_2117_, v___x_2131_, v___x_2132_, v___f_2124_, v_a_2118_);
return v___x_2133_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg___boxed(lean_object* v_pairs_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2134_, v_a_2135_);
lean_dec_ref(v_pairs_2134_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols(lean_object* v_00_u03b1_2137_, lean_object* v_pairs_2138_, lean_object* v_a_2139_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2138_, v_a_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___boxed(lean_object* v_00_u03b1_2141_, lean_object* v_pairs_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols(v_00_u03b1_2141_, v_pairs_2142_, v_a_2143_);
lean_dec_ref(v_pairs_2142_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0(lean_object* v_00_u03b1_2145_, lean_object* v_as_2146_, size_t v_i_2147_, size_t v_stop_2148_, lean_object* v_b_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___redArg(v_as_2146_, v_i_2147_, v_stop_2148_, v_b_2149_, v___y_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0___boxed(lean_object* v_00_u03b1_2152_, lean_object* v_as_2153_, lean_object* v_i_2154_, lean_object* v_stop_2155_, lean_object* v_b_2156_, lean_object* v___y_2157_){
_start:
{
size_t v_i_boxed_2158_; size_t v_stop_boxed_2159_; lean_object* v_res_2160_; 
v_i_boxed_2158_ = lean_unbox_usize(v_i_2154_);
lean_dec(v_i_2154_);
v_stop_boxed_2159_ = lean_unbox_usize(v_stop_2155_);
lean_dec(v_stop_2155_);
v_res_2160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols_spec__0(v_00_u03b1_2152_, v_as_2153_, v_i_boxed_2158_, v_stop_boxed_2159_, v_b_2156_, v___y_2157_);
lean_dec_ref(v_as_2153_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(size_t v_sz_2161_, size_t v_i_2162_, lean_object* v_bs_2163_){
_start:
{
uint8_t v___x_2164_; 
v___x_2164_ = lean_usize_dec_lt(v_i_2162_, v_sz_2161_);
if (v___x_2164_ == 0)
{
return v_bs_2163_;
}
else
{
lean_object* v_v_2165_; lean_object* v___x_2166_; lean_object* v_bs_x27_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; size_t v___x_2173_; size_t v___x_2174_; lean_object* v___x_2175_; 
v_v_2165_ = lean_array_uget(v_bs_2163_, v_i_2162_);
v___x_2166_ = lean_unsigned_to_nat(0u);
v_bs_x27_2167_ = lean_array_uset(v_bs_2163_, v_i_2162_, v___x_2166_);
v___x_2168_ = lean_usize_to_nat(v_i_2162_);
v___x_2169_ = lean_nat_to_int(v___x_2168_);
v___x_2170_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2171_ = lean_int_add(v___x_2169_, v___x_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2172_, 0, v_v_2165_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___x_2173_ = ((size_t)1ULL);
v___x_2174_ = lean_usize_add(v_i_2162_, v___x_2173_);
v___x_2175_ = lean_array_uset(v_bs_x27_2167_, v_i_2162_, v___x_2172_);
v_i_2162_ = v___x_2174_;
v_bs_2163_ = v___x_2175_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg___boxed(lean_object* v_sz_2177_, lean_object* v_i_2178_, lean_object* v_bs_2179_){
_start:
{
size_t v_sz_boxed_2180_; size_t v_i_boxed_2181_; lean_object* v_res_2182_; 
v_sz_boxed_2180_ = lean_unbox_usize(v_sz_2177_);
lean_dec(v_sz_2177_);
v_i_boxed_2181_ = lean_unbox_usize(v_i_2178_);
lean_dec(v_i_2178_);
v_res_2182_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_boxed_2180_, v_i_boxed_2181_, v_bs_2179_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(lean_object* v_as_2183_, size_t v_sz_2184_, size_t v_i_2185_, lean_object* v_bs_2186_){
_start:
{
uint8_t v___x_2187_; 
v___x_2187_ = lean_usize_dec_lt(v_i_2185_, v_sz_2184_);
if (v___x_2187_ == 0)
{
return v_bs_2186_;
}
else
{
lean_object* v_v_2188_; lean_object* v___x_2189_; lean_object* v_bs_x27_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; size_t v___x_2196_; size_t v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v_v_2188_ = lean_array_uget(v_bs_2186_, v_i_2185_);
v___x_2189_ = lean_unsigned_to_nat(0u);
v_bs_x27_2190_ = lean_array_uset(v_bs_2186_, v_i_2185_, v___x_2189_);
v___x_2191_ = lean_usize_to_nat(v_i_2185_);
v___x_2192_ = lean_nat_to_int(v___x_2191_);
v___x_2193_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2194_ = lean_int_add(v___x_2192_, v___x_2193_);
lean_dec(v___x_2192_);
v___x_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2195_, 0, v_v_2188_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
v___x_2196_ = ((size_t)1ULL);
v___x_2197_ = lean_usize_add(v_i_2185_, v___x_2196_);
v___x_2198_ = lean_array_uset(v_bs_x27_2190_, v_i_2185_, v___x_2195_);
v___x_2199_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_2184_, v___x_2197_, v___x_2198_);
return v___x_2199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0___boxed(lean_object* v_as_2200_, lean_object* v_sz_2201_, lean_object* v_i_2202_, lean_object* v_bs_2203_){
_start:
{
size_t v_sz_boxed_2204_; size_t v_i_boxed_2205_; lean_object* v_res_2206_; 
v_sz_boxed_2204_ = lean_unbox_usize(v_sz_2201_);
lean_dec(v_sz_2201_);
v_i_boxed_2205_ = lean_unbox_usize(v_i_2202_);
lean_dec(v_i_2202_);
v_res_2206_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_as_2200_, v_sz_boxed_2204_, v_i_boxed_2205_, v_bs_2203_);
lean_dec_ref(v_as_2200_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(lean_object* v_arr_2207_){
_start:
{
size_t v_sz_2208_; size_t v___x_2209_; lean_object* v___x_2210_; 
v_sz_2208_ = lean_array_size(v_arr_2207_);
v___x_2209_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2207_);
v___x_2210_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_arr_2207_, v_sz_2208_, v___x_2209_, v_arr_2207_);
lean_dec_ref(v_arr_2207_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0(lean_object* v_as_2211_, size_t v_sz_2212_, size_t v_i_2213_, lean_object* v_bs_2214_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___redArg(v_sz_2212_, v_i_2213_, v_bs_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0___boxed(lean_object* v_as_2216_, lean_object* v_sz_2217_, lean_object* v_i_2218_, lean_object* v_bs_2219_){
_start:
{
size_t v_sz_boxed_2220_; size_t v_i_boxed_2221_; lean_object* v_res_2222_; 
v_sz_boxed_2220_ = lean_unbox_usize(v_sz_2217_);
lean_dec(v_sz_2217_);
v_i_boxed_2221_ = lean_unbox_usize(v_i_2218_);
lean_dec(v_i_2218_);
v_res_2222_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0_spec__0(v_as_2216_, v_sz_boxed_2220_, v_i_boxed_2221_, v_bs_2219_);
lean_dec_ref(v_as_2216_);
return v_res_2222_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(lean_object* v_x_2223_){
_start:
{
lean_object* v___x_2224_; uint8_t v___x_2225_; 
v___x_2224_ = lean_unsigned_to_nat(0u);
v___x_2225_ = lean_nat_dec_eq(v_x_2223_, v___x_2224_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___x_2226_ = lean_unsigned_to_nat(1u);
v___x_2227_ = lean_nat_dec_eq(v_x_2223_, v___x_2226_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; uint8_t v___x_2229_; 
v___x_2228_ = lean_unsigned_to_nat(2u);
v___x_2229_ = lean_nat_dec_eq(v_x_2223_, v___x_2228_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; uint8_t v___x_2231_; 
v___x_2230_ = lean_unsigned_to_nat(3u);
v___x_2231_ = lean_nat_dec_eq(v_x_2223_, v___x_2230_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; uint8_t v___x_2233_; 
v___x_2232_ = lean_unsigned_to_nat(4u);
v___x_2233_ = lean_nat_dec_eq(v_x_2223_, v___x_2232_);
if (v___x_2233_ == 0)
{
lean_object* v___x_2234_; uint8_t v___x_2235_; 
v___x_2234_ = lean_unsigned_to_nat(5u);
v___x_2235_ = lean_nat_dec_eq(v_x_2223_, v___x_2234_);
if (v___x_2235_ == 0)
{
uint8_t v___x_2236_; 
v___x_2236_ = 5;
return v___x_2236_;
}
else
{
uint8_t v___x_2237_; 
v___x_2237_ = 4;
return v___x_2237_;
}
}
else
{
uint8_t v___x_2238_; 
v___x_2238_ = 3;
return v___x_2238_;
}
}
else
{
uint8_t v___x_2239_; 
v___x_2239_ = 2;
return v___x_2239_;
}
}
else
{
uint8_t v___x_2240_; 
v___x_2240_ = 1;
return v___x_2240_;
}
}
else
{
uint8_t v___x_2241_; 
v___x_2241_ = 0;
return v___x_2241_;
}
}
else
{
uint8_t v___x_2242_; 
v___x_2242_ = 6;
return v___x_2242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex___boxed(lean_object* v_x_2243_){
_start:
{
uint8_t v_res_2244_; lean_object* v_r_2245_; 
v_res_2244_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayOfIndex(v_x_2243_);
lean_dec(v_x_2243_);
v_r_2245_ = lean_box(v_res_2244_);
return v_r_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(size_t v_sz_2246_, size_t v_i_2247_, lean_object* v_bs_2248_){
_start:
{
uint8_t v___x_2249_; 
v___x_2249_ = lean_usize_dec_lt(v_i_2247_, v_sz_2246_);
if (v___x_2249_ == 0)
{
return v_bs_2248_;
}
else
{
lean_object* v_v_2250_; lean_object* v___x_2251_; lean_object* v_bs_x27_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; uint8_t v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; size_t v___x_2260_; size_t v___x_2261_; lean_object* v___x_2262_; 
v_v_2250_ = lean_array_uget(v_bs_2248_, v_i_2247_);
v___x_2251_ = lean_unsigned_to_nat(0u);
v_bs_x27_2252_ = lean_array_uset(v_bs_2248_, v_i_2247_, v___x_2251_);
v___x_2253_ = lean_usize_to_nat(v_i_2247_);
v___x_2254_ = lean_nat_to_int(v___x_2253_);
v___x_2255_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2256_ = lean_int_add(v___x_2254_, v___x_2255_);
lean_dec(v___x_2254_);
v___x_2257_ = l_Std_Time_Weekday_ofOrdinal(v___x_2256_);
lean_dec(v___x_2256_);
v___x_2258_ = lean_box(v___x_2257_);
v___x_2259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2259_, 0, v_v_2250_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
v___x_2260_ = ((size_t)1ULL);
v___x_2261_ = lean_usize_add(v_i_2247_, v___x_2260_);
v___x_2262_ = lean_array_uset(v_bs_x27_2252_, v_i_2247_, v___x_2259_);
v_i_2247_ = v___x_2261_;
v_bs_2248_ = v___x_2262_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg___boxed(lean_object* v_sz_2264_, lean_object* v_i_2265_, lean_object* v_bs_2266_){
_start:
{
size_t v_sz_boxed_2267_; size_t v_i_boxed_2268_; lean_object* v_res_2269_; 
v_sz_boxed_2267_ = lean_unbox_usize(v_sz_2264_);
lean_dec(v_sz_2264_);
v_i_boxed_2268_ = lean_unbox_usize(v_i_2265_);
lean_dec(v_i_2265_);
v_res_2269_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_boxed_2267_, v_i_boxed_2268_, v_bs_2266_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(lean_object* v_as_2270_, size_t v_sz_2271_, size_t v_i_2272_, lean_object* v_bs_2273_){
_start:
{
uint8_t v___x_2274_; 
v___x_2274_ = lean_usize_dec_lt(v_i_2272_, v_sz_2271_);
if (v___x_2274_ == 0)
{
return v_bs_2273_;
}
else
{
lean_object* v_v_2275_; lean_object* v___x_2276_; lean_object* v_bs_x27_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; size_t v___x_2285_; size_t v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v_v_2275_ = lean_array_uget(v_bs_2273_, v_i_2272_);
v___x_2276_ = lean_unsigned_to_nat(0u);
v_bs_x27_2277_ = lean_array_uset(v_bs_2273_, v_i_2272_, v___x_2276_);
v___x_2278_ = lean_usize_to_nat(v_i_2272_);
v___x_2279_ = lean_nat_to_int(v___x_2278_);
v___x_2280_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_2281_ = lean_int_add(v___x_2279_, v___x_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = l_Std_Time_Weekday_ofOrdinal(v___x_2281_);
lean_dec(v___x_2281_);
v___x_2283_ = lean_box(v___x_2282_);
v___x_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2284_, 0, v_v_2275_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___x_2285_ = ((size_t)1ULL);
v___x_2286_ = lean_usize_add(v_i_2272_, v___x_2285_);
v___x_2287_ = lean_array_uset(v_bs_x27_2277_, v_i_2272_, v___x_2284_);
v___x_2288_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_2271_, v___x_2286_, v___x_2287_);
return v___x_2288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0___boxed(lean_object* v_as_2289_, lean_object* v_sz_2290_, lean_object* v_i_2291_, lean_object* v_bs_2292_){
_start:
{
size_t v_sz_boxed_2293_; size_t v_i_boxed_2294_; lean_object* v_res_2295_; 
v_sz_boxed_2293_ = lean_unbox_usize(v_sz_2290_);
lean_dec(v_sz_2290_);
v_i_boxed_2294_ = lean_unbox_usize(v_i_2291_);
lean_dec(v_i_2291_);
v_res_2295_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(v_as_2289_, v_sz_boxed_2293_, v_i_boxed_2294_, v_bs_2292_);
lean_dec_ref(v_as_2289_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(lean_object* v_arr_2296_){
_start:
{
size_t v_sz_2297_; size_t v___x_2298_; lean_object* v___x_2299_; 
v_sz_2297_ = lean_array_size(v_arr_2296_);
v___x_2298_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2296_);
v___x_2299_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0(v_arr_2296_, v_sz_2297_, v___x_2298_, v_arr_2296_);
lean_dec_ref(v_arr_2296_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0(lean_object* v_as_2300_, size_t v_sz_2301_, size_t v_i_2302_, lean_object* v_bs_2303_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___redArg(v_sz_2301_, v_i_2302_, v_bs_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0___boxed(lean_object* v_as_2305_, lean_object* v_sz_2306_, lean_object* v_i_2307_, lean_object* v_bs_2308_){
_start:
{
size_t v_sz_boxed_2309_; size_t v_i_boxed_2310_; lean_object* v_res_2311_; 
v_sz_boxed_2309_ = lean_unbox_usize(v_sz_2306_);
lean_dec(v_sz_2306_);
v_i_boxed_2310_ = lean_unbox_usize(v_i_2307_);
lean_dec(v_i_2307_);
v_res_2311_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs_spec__0_spec__0(v_as_2305_, v_sz_boxed_2309_, v_i_boxed_2310_, v_bs_2308_);
lean_dec_ref(v_as_2305_);
return v_res_2311_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(lean_object* v_x_2312_){
_start:
{
lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2313_ = lean_unsigned_to_nat(0u);
v___x_2314_ = lean_nat_dec_eq(v_x_2312_, v___x_2313_);
if (v___x_2314_ == 0)
{
uint8_t v___x_2315_; 
v___x_2315_ = 1;
return v___x_2315_;
}
else
{
uint8_t v___x_2316_; 
v___x_2316_ = 0;
return v___x_2316_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex___boxed(lean_object* v_x_2317_){
_start:
{
uint8_t v_res_2318_; lean_object* v_r_2319_; 
v_res_2318_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(v_x_2317_);
lean_dec(v_x_2317_);
v_r_2319_ = lean_box(v_res_2318_);
return v_r_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(size_t v_sz_2320_, size_t v_i_2321_, lean_object* v_bs_2322_){
_start:
{
uint8_t v___x_2323_; 
v___x_2323_ = lean_usize_dec_lt(v_i_2321_, v_sz_2320_);
if (v___x_2323_ == 0)
{
return v_bs_2322_;
}
else
{
lean_object* v_v_2324_; lean_object* v___x_2325_; lean_object* v_bs_x27_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; size_t v___x_2331_; size_t v___x_2332_; lean_object* v___x_2333_; 
v_v_2324_ = lean_array_uget(v_bs_2322_, v_i_2321_);
v___x_2325_ = lean_unsigned_to_nat(0u);
v_bs_x27_2326_ = lean_array_uset(v_bs_2322_, v_i_2321_, v___x_2325_);
v___x_2327_ = lean_usize_to_nat(v_i_2321_);
v___x_2328_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraOfIndex(v___x_2327_);
lean_dec(v___x_2327_);
v___x_2329_ = lean_box(v___x_2328_);
v___x_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2330_, 0, v_v_2324_);
lean_ctor_set(v___x_2330_, 1, v___x_2329_);
v___x_2331_ = ((size_t)1ULL);
v___x_2332_ = lean_usize_add(v_i_2321_, v___x_2331_);
v___x_2333_ = lean_array_uset(v_bs_x27_2326_, v_i_2321_, v___x_2330_);
v_i_2321_ = v___x_2332_;
v_bs_2322_ = v___x_2333_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg___boxed(lean_object* v_sz_2335_, lean_object* v_i_2336_, lean_object* v_bs_2337_){
_start:
{
size_t v_sz_boxed_2338_; size_t v_i_boxed_2339_; lean_object* v_res_2340_; 
v_sz_boxed_2338_ = lean_unbox_usize(v_sz_2335_);
lean_dec(v_sz_2335_);
v_i_boxed_2339_ = lean_unbox_usize(v_i_2336_);
lean_dec(v_i_2336_);
v_res_2340_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_boxed_2338_, v_i_boxed_2339_, v_bs_2337_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(lean_object* v_arr_2341_){
_start:
{
size_t v_sz_2342_; size_t v___x_2343_; lean_object* v___x_2344_; 
v_sz_2342_ = lean_array_size(v_arr_2341_);
v___x_2343_ = ((size_t)0ULL);
v___x_2344_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_2342_, v___x_2343_, v_arr_2341_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0(lean_object* v_as_2345_, size_t v_sz_2346_, size_t v_i_2347_, lean_object* v_bs_2348_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___redArg(v_sz_2346_, v_i_2347_, v_bs_2348_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0___boxed(lean_object* v_as_2350_, lean_object* v_sz_2351_, lean_object* v_i_2352_, lean_object* v_bs_2353_){
_start:
{
size_t v_sz_boxed_2354_; size_t v_i_boxed_2355_; lean_object* v_res_2356_; 
v_sz_boxed_2354_ = lean_unbox_usize(v_sz_2351_);
lean_dec(v_sz_2351_);
v_i_boxed_2355_ = lean_unbox_usize(v_i_2352_);
lean_dec(v_i_2352_);
v_res_2356_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_eraPairs_spec__0(v_as_2350_, v_sz_boxed_2354_, v_i_boxed_2355_, v_bs_2353_);
lean_dec_ref(v_as_2350_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(lean_object* v_arr_2357_){
_start:
{
size_t v_sz_2358_; size_t v___x_2359_; lean_object* v___x_2360_; 
v_sz_2358_ = lean_array_size(v_arr_2357_);
v___x_2359_ = ((size_t)0ULL);
lean_inc_ref(v_arr_2357_);
v___x_2360_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Time_Format_Basic_0__Std_Time_monthPairs_spec__0(v_arr_2357_, v_sz_2358_, v___x_2359_, v_arr_2357_);
lean_dec_ref(v_arr_2357_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(lean_object* v_symbols_2361_, lean_object* v_a_2362_){
_start:
{
lean_object* v_monthLong_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v_monthLong_2363_ = lean_ctor_get(v_symbols_2361_, 0);
lean_inc_ref(v_monthLong_2363_);
lean_dec_ref(v_symbols_2361_);
v___x_2364_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthLong_2363_);
v___x_2365_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2364_, v_a_2362_);
lean_dec_ref(v___x_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_parseMonthShort(lean_object* v_symbols_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v_monthShort_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_monthShort_2368_ = lean_ctor_get(v_symbols_2366_, 1);
lean_inc_ref(v_monthShort_2368_);
lean_dec_ref(v_symbols_2366_);
v___x_2369_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthShort_2368_);
v___x_2370_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2369_, v_a_2367_);
lean_dec_ref(v___x_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(lean_object* v_symbols_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v_monthNarrow_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v_monthNarrow_2373_ = lean_ctor_get(v_symbols_2371_, 2);
lean_inc_ref(v_monthNarrow_2373_);
lean_dec_ref(v_symbols_2371_);
v___x_2374_ = l___private_Std_Time_Format_Basic_0__Std_Time_monthPairs(v_monthNarrow_2373_);
v___x_2375_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2374_, v_a_2372_);
lean_dec_ref(v___x_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(lean_object* v_symbols_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v_weekdayLong_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v_weekdayLong_2378_ = lean_ctor_get(v_symbols_2376_, 3);
lean_inc_ref(v_weekdayLong_2378_);
lean_dec_ref(v_symbols_2376_);
v___x_2379_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayLong_2378_);
v___x_2380_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2379_, v_a_2377_);
lean_dec_ref(v___x_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(lean_object* v_symbols_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v_weekdayShort_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v_weekdayShort_2383_ = lean_ctor_get(v_symbols_2381_, 4);
lean_inc_ref(v_weekdayShort_2383_);
lean_dec_ref(v_symbols_2381_);
v___x_2384_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayShort_2383_);
v___x_2385_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2384_, v_a_2382_);
lean_dec_ref(v___x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(lean_object* v_symbols_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_weekdayNarrow_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v_weekdayNarrow_2388_ = lean_ctor_get(v_symbols_2386_, 5);
lean_inc_ref(v_weekdayNarrow_2388_);
lean_dec_ref(v_symbols_2386_);
v___x_2389_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayNarrow_2388_);
v___x_2390_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2389_, v_a_2387_);
lean_dec_ref(v___x_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(lean_object* v_symbols_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v_weekdayTwoLetter_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v_weekdayTwoLetter_2393_ = lean_ctor_get(v_symbols_2391_, 6);
lean_inc_ref(v_weekdayTwoLetter_2393_);
lean_dec_ref(v_symbols_2391_);
v___x_2394_ = l___private_Std_Time_Format_Basic_0__Std_Time_weekdayPairs(v_weekdayTwoLetter_2393_);
v___x_2395_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2394_, v_a_2392_);
lean_dec_ref(v___x_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraShort(lean_object* v_symbols_2396_, lean_object* v_a_2397_){
_start:
{
lean_object* v_eraShort_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v_eraShort_2398_ = lean_ctor_get(v_symbols_2396_, 7);
lean_inc_ref(v_eraShort_2398_);
lean_dec_ref(v_symbols_2396_);
v___x_2399_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraShort_2398_);
v___x_2400_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2399_, v_a_2397_);
lean_dec_ref(v___x_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraLong(lean_object* v_symbols_2401_, lean_object* v_a_2402_){
_start:
{
lean_object* v_eraLong_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v_eraLong_2403_ = lean_ctor_get(v_symbols_2401_, 8);
lean_inc_ref(v_eraLong_2403_);
lean_dec_ref(v_symbols_2401_);
v___x_2404_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraLong_2403_);
v___x_2405_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2404_, v_a_2402_);
lean_dec_ref(v___x_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseEraNarrow(lean_object* v_symbols_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v_eraNarrow_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v_eraNarrow_2408_ = lean_ctor_get(v_symbols_2406_, 9);
lean_inc_ref(v_eraNarrow_2408_);
lean_dec_ref(v_symbols_2406_);
v___x_2409_ = l___private_Std_Time_Format_Basic_0__Std_Time_eraPairs(v_eraNarrow_2408_);
v___x_2410_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2409_, v_a_2407_);
lean_dec_ref(v___x_2409_);
return v___x_2410_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = lean_unsigned_to_nat(3u);
v___x_2412_ = lean_nat_to_int(v___x_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber(lean_object* v_a_2413_){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__0));
lean_inc_ref(v_a_2413_);
v___x_2415_ = l_Std_Internal_Parsec_String_pstring(v___x_2414_, v_a_2413_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_pos_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2424_; 
lean_dec_ref(v_a_2413_);
v_pos_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2424_ == 0)
{
lean_object* v_unused_2425_; 
v_unused_2425_ = lean_ctor_get(v___x_2415_, 1);
lean_dec(v_unused_2425_);
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_pos_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2420_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 1, v___x_2420_);
v___x_2422_ = v___x_2418_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_pos_2416_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
else
{
lean_object* v_pos_2426_; lean_object* v_err_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2504_; 
v_pos_2426_ = lean_ctor_get(v___x_2415_, 0);
v_err_2427_ = lean_ctor_get(v___x_2415_, 1);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2429_ = v___x_2415_;
v_isShared_2430_ = v_isSharedCheck_2504_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_err_2427_);
lean_inc(v_pos_2426_);
lean_dec(v___x_2415_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2504_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v_snd_2431_; lean_object* v_snd_2432_; uint8_t v_decide_2433_; 
v_snd_2431_ = lean_ctor_get(v_a_2413_, 1);
lean_inc(v_snd_2431_);
lean_dec_ref(v_a_2413_);
v_snd_2432_ = lean_ctor_get(v_pos_2426_, 1);
v_decide_2433_ = lean_nat_dec_eq(v_snd_2431_, v_snd_2432_);
lean_dec(v_snd_2431_);
if (v_decide_2433_ == 0)
{
lean_object* v___x_2435_; 
if (v_isShared_2430_ == 0)
{
v___x_2435_ = v___x_2429_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_pos_2426_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v_err_2427_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
else
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
lean_inc(v_snd_2432_);
lean_del_object(v___x_2429_);
lean_dec(v_err_2427_);
v___x_2437_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__1));
v___x_2438_ = l_Std_Internal_Parsec_String_pstring(v___x_2437_, v_pos_2426_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_pos_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2447_; 
lean_dec(v_snd_2432_);
v_pos_2439_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2447_ == 0)
{
lean_object* v_unused_2448_; 
v_unused_2448_ = lean_ctor_get(v___x_2438_, 1);
lean_dec(v_unused_2448_);
v___x_2441_ = v___x_2438_;
v_isShared_2442_ = v_isSharedCheck_2447_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_pos_2439_);
lean_dec(v___x_2438_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2447_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2443_; lean_object* v___x_2445_; 
v___x_2443_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__3, &l_Std_Time_instReprFormatPart_repr___closed__3_once, _init_l_Std_Time_instReprFormatPart_repr___closed__3);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 1, v___x_2443_);
v___x_2445_ = v___x_2441_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_pos_2439_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v___x_2443_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
else
{
lean_object* v_pos_2449_; lean_object* v_err_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2503_; 
v_pos_2449_ = lean_ctor_get(v___x_2438_, 0);
v_err_2450_ = lean_ctor_get(v___x_2438_, 1);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2452_ = v___x_2438_;
v_isShared_2453_ = v_isSharedCheck_2503_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_err_2450_);
lean_inc(v_pos_2449_);
lean_dec(v___x_2438_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2503_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v_snd_2454_; uint8_t v_decide_2455_; 
v_snd_2454_ = lean_ctor_get(v_pos_2449_, 1);
v_decide_2455_ = lean_nat_dec_eq(v_snd_2432_, v_snd_2454_);
lean_dec(v_snd_2432_);
if (v_decide_2455_ == 0)
{
lean_object* v___x_2457_; 
if (v_isShared_2453_ == 0)
{
v___x_2457_ = v___x_2452_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_pos_2449_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_err_2450_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
else
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
lean_inc(v_snd_2454_);
lean_del_object(v___x_2452_);
lean_dec(v_err_2450_);
v___x_2459_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__2));
v___x_2460_ = l_Std_Internal_Parsec_String_pstring(v___x_2459_, v_pos_2449_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_pos_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2469_; 
lean_dec(v_snd_2454_);
v_pos_2461_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2469_ == 0)
{
lean_object* v_unused_2470_; 
v_unused_2470_ = lean_ctor_get(v___x_2460_, 1);
lean_dec(v_unused_2470_);
v___x_2463_ = v___x_2460_;
v_isShared_2464_ = v_isSharedCheck_2469_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_pos_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2469_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v___x_2467_; 
v___x_2465_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNumber___closed__0);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 1, v___x_2465_);
v___x_2467_ = v___x_2463_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_pos_2461_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v___x_2465_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
else
{
lean_object* v_pos_2471_; lean_object* v_err_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2502_; 
v_pos_2471_ = lean_ctor_get(v___x_2460_, 0);
v_err_2472_ = lean_ctor_get(v___x_2460_, 1);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2474_ = v___x_2460_;
v_isShared_2475_ = v_isSharedCheck_2502_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_err_2472_);
lean_inc(v_pos_2471_);
lean_dec(v___x_2460_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2502_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v_snd_2476_; uint8_t v_decide_2477_; 
v_snd_2476_ = lean_ctor_get(v_pos_2471_, 1);
v_decide_2477_ = lean_nat_dec_eq(v_snd_2454_, v_snd_2476_);
lean_dec(v_snd_2454_);
if (v_decide_2477_ == 0)
{
lean_object* v___x_2479_; 
if (v_isShared_2475_ == 0)
{
v___x_2479_ = v___x_2474_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_pos_2471_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_err_2472_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
else
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
lean_del_object(v___x_2474_);
lean_dec(v_err_2472_);
v___x_2481_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatQuarterNumber___closed__3));
v___x_2482_ = l_Std_Internal_Parsec_String_pstring(v___x_2481_, v_pos_2471_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_pos_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2491_; 
v_pos_2483_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2491_ == 0)
{
lean_object* v_unused_2492_; 
v_unused_2492_ = lean_ctor_get(v___x_2482_, 1);
lean_dec(v_unused_2492_);
v___x_2485_ = v___x_2482_;
v_isShared_2486_ = v_isSharedCheck_2491_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_pos_2483_);
lean_dec(v___x_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2491_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; lean_object* v___x_2489_; 
v___x_2487_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 1, v___x_2487_);
v___x_2489_ = v___x_2485_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_pos_2483_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v___x_2487_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
else
{
lean_object* v_pos_2493_; lean_object* v_err_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
v_pos_2493_ = lean_ctor_get(v___x_2482_, 0);
v_err_2494_ = lean_ctor_get(v___x_2482_, 1);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2482_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_err_2494_);
lean_inc(v_pos_2493_);
lean_dec(v___x_2482_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_pos_2493_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_err_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(lean_object* v_symbols_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v_quarterLong_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v_quarterLong_2507_ = lean_ctor_get(v_symbols_2505_, 11);
lean_inc_ref(v_quarterLong_2507_);
lean_dec_ref(v_symbols_2505_);
v___x_2508_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterLong_2507_);
v___x_2509_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2508_, v_a_2506_);
lean_dec_ref(v___x_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(lean_object* v_symbols_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v_quarterShort_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v_quarterShort_2512_ = lean_ctor_get(v_symbols_2510_, 10);
lean_inc_ref(v_quarterShort_2512_);
lean_dec_ref(v_symbols_2510_);
v___x_2513_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterShort_2512_);
v___x_2514_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2513_, v_a_2511_);
lean_dec_ref(v___x_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(lean_object* v_symbols_2515_, lean_object* v_a_2516_){
_start:
{
lean_object* v_quarterNarrow_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v_quarterNarrow_2517_ = lean_ctor_get(v_symbols_2515_, 12);
lean_inc_ref(v_quarterNarrow_2517_);
lean_dec_ref(v_symbols_2515_);
v___x_2518_ = l___private_Std_Time_Format_Basic_0__Std_Time_quarterPairs(v_quarterNarrow_2517_);
v___x_2519_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v___x_2518_, v_a_2516_);
lean_dec_ref(v___x_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerShort(lean_object* v_symbols_2520_, lean_object* v_a_2521_){
_start:
{
lean_object* v_amShort_2522_; lean_object* v_pmShort_2523_; lean_object* v___x_2524_; 
v_amShort_2522_ = lean_ctor_get(v_symbols_2520_, 13);
lean_inc_ref(v_amShort_2522_);
v_pmShort_2523_ = lean_ctor_get(v_symbols_2520_, 14);
lean_inc_ref(v_pmShort_2523_);
lean_dec_ref(v_symbols_2520_);
lean_inc_ref(v_a_2521_);
v___x_2524_ = l_Std_Internal_Parsec_String_pstring(v_amShort_2522_, v_a_2521_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_pos_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2534_; 
lean_dec_ref(v_pmShort_2523_);
lean_dec_ref(v_a_2521_);
v_pos_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2534_ == 0)
{
lean_object* v_unused_2535_; 
v_unused_2535_ = lean_ctor_get(v___x_2524_, 1);
lean_dec(v_unused_2535_);
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2534_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_pos_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2534_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
uint8_t v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2529_ = 0;
v___x_2530_ = lean_box(v___x_2529_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 1, v___x_2530_);
v___x_2532_ = v___x_2527_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_pos_2525_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v___x_2530_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
else
{
lean_object* v_pos_2536_; lean_object* v_err_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2568_; 
v_pos_2536_ = lean_ctor_get(v___x_2524_, 0);
v_err_2537_ = lean_ctor_get(v___x_2524_, 1);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2539_ = v___x_2524_;
v_isShared_2540_ = v_isSharedCheck_2568_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_err_2537_);
lean_inc(v_pos_2536_);
lean_dec(v___x_2524_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2568_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v_snd_2541_; lean_object* v_snd_2542_; uint8_t v_decide_2543_; 
v_snd_2541_ = lean_ctor_get(v_a_2521_, 1);
lean_inc(v_snd_2541_);
lean_dec_ref(v_a_2521_);
v_snd_2542_ = lean_ctor_get(v_pos_2536_, 1);
v_decide_2543_ = lean_nat_dec_eq(v_snd_2541_, v_snd_2542_);
lean_dec(v_snd_2541_);
if (v_decide_2543_ == 0)
{
lean_object* v___x_2545_; 
lean_dec_ref(v_pmShort_2523_);
if (v_isShared_2540_ == 0)
{
v___x_2545_ = v___x_2539_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_pos_2536_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v_err_2537_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
else
{
lean_object* v___x_2547_; 
lean_del_object(v___x_2539_);
lean_dec(v_err_2537_);
v___x_2547_ = l_Std_Internal_Parsec_String_pstring(v_pmShort_2523_, v_pos_2536_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_pos_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2557_; 
v_pos_2548_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2557_ == 0)
{
lean_object* v_unused_2558_; 
v_unused_2558_ = lean_ctor_get(v___x_2547_, 1);
lean_dec(v_unused_2558_);
v___x_2550_ = v___x_2547_;
v_isShared_2551_ = v_isSharedCheck_2557_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_pos_2548_);
lean_dec(v___x_2547_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2557_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
uint8_t v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2552_ = 1;
v___x_2553_ = lean_box(v___x_2552_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 1, v___x_2553_);
v___x_2555_ = v___x_2550_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_pos_2548_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
else
{
lean_object* v_pos_2559_; lean_object* v_err_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
v_pos_2559_ = lean_ctor_get(v___x_2547_, 0);
v_err_2560_ = lean_ctor_get(v___x_2547_, 1);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2547_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_err_2560_);
lean_inc(v_pos_2559_);
lean_dec(v___x_2547_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_pos_2559_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v_err_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerLong(lean_object* v_symbols_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v_amLong_2571_; lean_object* v_pmLong_2572_; lean_object* v___x_2573_; 
v_amLong_2571_ = lean_ctor_get(v_symbols_2569_, 15);
lean_inc_ref(v_amLong_2571_);
v_pmLong_2572_ = lean_ctor_get(v_symbols_2569_, 16);
lean_inc_ref(v_pmLong_2572_);
lean_dec_ref(v_symbols_2569_);
lean_inc_ref(v_a_2570_);
v___x_2573_ = l_Std_Internal_Parsec_String_pstring(v_amLong_2571_, v_a_2570_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_pos_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2583_; 
lean_dec_ref(v_pmLong_2572_);
lean_dec_ref(v_a_2570_);
v_pos_2574_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2583_ == 0)
{
lean_object* v_unused_2584_; 
v_unused_2584_ = lean_ctor_get(v___x_2573_, 1);
lean_dec(v_unused_2584_);
v___x_2576_ = v___x_2573_;
v_isShared_2577_ = v_isSharedCheck_2583_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_pos_2574_);
lean_dec(v___x_2573_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2583_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
uint8_t v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2581_; 
v___x_2578_ = 0;
v___x_2579_ = lean_box(v___x_2578_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 1, v___x_2579_);
v___x_2581_ = v___x_2576_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_pos_2574_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
else
{
lean_object* v_pos_2585_; lean_object* v_err_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2617_; 
v_pos_2585_ = lean_ctor_get(v___x_2573_, 0);
v_err_2586_ = lean_ctor_get(v___x_2573_, 1);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2588_ = v___x_2573_;
v_isShared_2589_ = v_isSharedCheck_2617_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_err_2586_);
lean_inc(v_pos_2585_);
lean_dec(v___x_2573_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2617_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v_snd_2590_; lean_object* v_snd_2591_; uint8_t v_decide_2592_; 
v_snd_2590_ = lean_ctor_get(v_a_2570_, 1);
lean_inc(v_snd_2590_);
lean_dec_ref(v_a_2570_);
v_snd_2591_ = lean_ctor_get(v_pos_2585_, 1);
v_decide_2592_ = lean_nat_dec_eq(v_snd_2590_, v_snd_2591_);
lean_dec(v_snd_2590_);
if (v_decide_2592_ == 0)
{
lean_object* v___x_2594_; 
lean_dec_ref(v_pmLong_2572_);
if (v_isShared_2589_ == 0)
{
v___x_2594_ = v___x_2588_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_pos_2585_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v_err_2586_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
else
{
lean_object* v___x_2596_; 
lean_del_object(v___x_2588_);
lean_dec(v_err_2586_);
v___x_2596_ = l_Std_Internal_Parsec_String_pstring(v_pmLong_2572_, v_pos_2585_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_pos_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2606_; 
v_pos_2597_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2606_ == 0)
{
lean_object* v_unused_2607_; 
v_unused_2607_ = lean_ctor_get(v___x_2596_, 1);
lean_dec(v_unused_2607_);
v___x_2599_ = v___x_2596_;
v_isShared_2600_ = v_isSharedCheck_2606_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_pos_2597_);
lean_dec(v___x_2596_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2606_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
uint8_t v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2604_; 
v___x_2601_ = 1;
v___x_2602_ = lean_box(v___x_2601_);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 1, v___x_2602_);
v___x_2604_ = v___x_2599_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_pos_2597_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v___x_2602_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
else
{
lean_object* v_pos_2608_; lean_object* v_err_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
v_pos_2608_ = lean_ctor_get(v___x_2596_, 0);
v_err_2609_ = lean_ctor_get(v___x_2596_, 1);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2596_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_err_2609_);
lean_inc(v_pos_2608_);
lean_dec(v___x_2596_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_pos_2608_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_err_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerNarrow(lean_object* v_symbols_2618_, lean_object* v_a_2619_){
_start:
{
lean_object* v_amNarrow_2620_; lean_object* v_pmNarrow_2621_; lean_object* v___x_2622_; 
v_amNarrow_2620_ = lean_ctor_get(v_symbols_2618_, 17);
lean_inc_ref(v_amNarrow_2620_);
v_pmNarrow_2621_ = lean_ctor_get(v_symbols_2618_, 18);
lean_inc_ref(v_pmNarrow_2621_);
lean_dec_ref(v_symbols_2618_);
lean_inc_ref(v_a_2619_);
v___x_2622_ = l_Std_Internal_Parsec_String_pstring(v_amNarrow_2620_, v_a_2619_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_pos_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref(v_pmNarrow_2621_);
lean_dec_ref(v_a_2619_);
v_pos_2623_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2632_ == 0)
{
lean_object* v_unused_2633_; 
v_unused_2633_ = lean_ctor_get(v___x_2622_, 1);
lean_dec(v_unused_2633_);
v___x_2625_ = v___x_2622_;
v_isShared_2626_ = v_isSharedCheck_2632_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_pos_2623_);
lean_dec(v___x_2622_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2632_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
uint8_t v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2630_; 
v___x_2627_ = 0;
v___x_2628_ = lean_box(v___x_2627_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 1, v___x_2628_);
v___x_2630_ = v___x_2625_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_pos_2623_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
else
{
lean_object* v_pos_2634_; lean_object* v_err_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2666_; 
v_pos_2634_ = lean_ctor_get(v___x_2622_, 0);
v_err_2635_ = lean_ctor_get(v___x_2622_, 1);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2637_ = v___x_2622_;
v_isShared_2638_ = v_isSharedCheck_2666_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_err_2635_);
lean_inc(v_pos_2634_);
lean_dec(v___x_2622_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2666_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v_snd_2639_; lean_object* v_snd_2640_; uint8_t v_decide_2641_; 
v_snd_2639_ = lean_ctor_get(v_a_2619_, 1);
lean_inc(v_snd_2639_);
lean_dec_ref(v_a_2619_);
v_snd_2640_ = lean_ctor_get(v_pos_2634_, 1);
v_decide_2641_ = lean_nat_dec_eq(v_snd_2639_, v_snd_2640_);
lean_dec(v_snd_2639_);
if (v_decide_2641_ == 0)
{
lean_object* v___x_2643_; 
lean_dec_ref(v_pmNarrow_2621_);
if (v_isShared_2638_ == 0)
{
v___x_2643_ = v___x_2637_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_pos_2634_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_err_2635_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
else
{
lean_object* v___x_2645_; 
lean_del_object(v___x_2637_);
lean_dec(v_err_2635_);
v___x_2645_ = l_Std_Internal_Parsec_String_pstring(v_pmNarrow_2621_, v_pos_2634_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_pos_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2655_; 
v_pos_2646_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2655_ == 0)
{
lean_object* v_unused_2656_; 
v_unused_2656_ = lean_ctor_get(v___x_2645_, 1);
lean_dec(v_unused_2656_);
v___x_2648_ = v___x_2645_;
v_isShared_2649_ = v_isSharedCheck_2655_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_pos_2646_);
lean_dec(v___x_2645_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2655_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
uint8_t v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2653_; 
v___x_2650_ = 1;
v___x_2651_ = lean_box(v___x_2650_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 1, v___x_2651_);
v___x_2653_ = v___x_2648_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_pos_2646_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v___x_2651_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
else
{
lean_object* v_pos_2657_; lean_object* v_err_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
v_pos_2657_ = lean_ctor_get(v___x_2645_, 0);
v_err_2658_ = lean_ctor_get(v___x_2645_, 1);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2645_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_err_2658_);
lean_inc(v_pos_2657_);
lean_dec(v___x_2645_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_pos_2657_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v_err_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(lean_object* v_dp_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v_am_2669_; lean_object* v_pm_2670_; lean_object* v_noon_2671_; lean_object* v_midnight_2672_; lean_object* v___x_2673_; 
v_am_2669_ = lean_ctor_get(v_dp_2667_, 0);
lean_inc_ref(v_am_2669_);
v_pm_2670_ = lean_ctor_get(v_dp_2667_, 1);
lean_inc_ref(v_pm_2670_);
v_noon_2671_ = lean_ctor_get(v_dp_2667_, 2);
lean_inc_ref(v_noon_2671_);
v_midnight_2672_ = lean_ctor_get(v_dp_2667_, 3);
lean_inc_ref(v_midnight_2672_);
lean_dec_ref(v_dp_2667_);
lean_inc_ref(v_a_2668_);
v___x_2673_ = l_Std_Internal_Parsec_String_pstring(v_midnight_2672_, v_a_2668_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_pos_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2683_; 
lean_dec_ref(v_noon_2671_);
lean_dec_ref(v_pm_2670_);
lean_dec_ref(v_am_2669_);
lean_dec_ref(v_a_2668_);
v_pos_2674_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2683_ == 0)
{
lean_object* v_unused_2684_; 
v_unused_2684_ = lean_ctor_get(v___x_2673_, 1);
lean_dec(v_unused_2684_);
v___x_2676_ = v___x_2673_;
v_isShared_2677_ = v_isSharedCheck_2683_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_pos_2674_);
lean_dec(v___x_2673_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2683_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
uint8_t v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2681_; 
v___x_2678_ = 3;
v___x_2679_ = lean_box(v___x_2678_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 1, v___x_2679_);
v___x_2681_ = v___x_2676_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_pos_2674_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
else
{
lean_object* v_pos_2685_; lean_object* v_err_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2763_; 
v_pos_2685_ = lean_ctor_get(v___x_2673_, 0);
v_err_2686_ = lean_ctor_get(v___x_2673_, 1);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2688_ = v___x_2673_;
v_isShared_2689_ = v_isSharedCheck_2763_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_err_2686_);
lean_inc(v_pos_2685_);
lean_dec(v___x_2673_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2763_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v_snd_2690_; lean_object* v_snd_2691_; uint8_t v_decide_2692_; 
v_snd_2690_ = lean_ctor_get(v_a_2668_, 1);
lean_inc(v_snd_2690_);
lean_dec_ref(v_a_2668_);
v_snd_2691_ = lean_ctor_get(v_pos_2685_, 1);
v_decide_2692_ = lean_nat_dec_eq(v_snd_2690_, v_snd_2691_);
lean_dec(v_snd_2690_);
if (v_decide_2692_ == 0)
{
lean_object* v___x_2694_; 
lean_dec_ref(v_noon_2671_);
lean_dec_ref(v_pm_2670_);
lean_dec_ref(v_am_2669_);
if (v_isShared_2689_ == 0)
{
v___x_2694_ = v___x_2688_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_pos_2685_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v_err_2686_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
else
{
lean_object* v___x_2696_; 
lean_inc(v_snd_2691_);
lean_del_object(v___x_2688_);
lean_dec(v_err_2686_);
v___x_2696_ = l_Std_Internal_Parsec_String_pstring(v_noon_2671_, v_pos_2685_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_pos_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2706_; 
lean_dec(v_snd_2691_);
lean_dec_ref(v_pm_2670_);
lean_dec_ref(v_am_2669_);
v_pos_2697_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2706_ == 0)
{
lean_object* v_unused_2707_; 
v_unused_2707_ = lean_ctor_get(v___x_2696_, 1);
lean_dec(v_unused_2707_);
v___x_2699_ = v___x_2696_;
v_isShared_2700_ = v_isSharedCheck_2706_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_pos_2697_);
lean_dec(v___x_2696_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2706_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
uint8_t v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2701_ = 2;
v___x_2702_ = lean_box(v___x_2701_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 1, v___x_2702_);
v___x_2704_ = v___x_2699_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_pos_2697_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
else
{
lean_object* v_pos_2708_; lean_object* v_err_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2762_; 
v_pos_2708_ = lean_ctor_get(v___x_2696_, 0);
v_err_2709_ = lean_ctor_get(v___x_2696_, 1);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2711_ = v___x_2696_;
v_isShared_2712_ = v_isSharedCheck_2762_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_err_2709_);
lean_inc(v_pos_2708_);
lean_dec(v___x_2696_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2762_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v_snd_2713_; uint8_t v_decide_2714_; 
v_snd_2713_ = lean_ctor_get(v_pos_2708_, 1);
v_decide_2714_ = lean_nat_dec_eq(v_snd_2691_, v_snd_2713_);
lean_dec(v_snd_2691_);
if (v_decide_2714_ == 0)
{
lean_object* v___x_2716_; 
lean_dec_ref(v_pm_2670_);
lean_dec_ref(v_am_2669_);
if (v_isShared_2712_ == 0)
{
v___x_2716_ = v___x_2711_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_pos_2708_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_err_2709_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
else
{
lean_object* v___x_2718_; 
lean_inc(v_snd_2713_);
lean_del_object(v___x_2711_);
lean_dec(v_err_2709_);
v___x_2718_ = l_Std_Internal_Parsec_String_pstring(v_am_2669_, v_pos_2708_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_pos_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2728_; 
lean_dec(v_snd_2713_);
lean_dec_ref(v_pm_2670_);
v_pos_2719_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2728_ == 0)
{
lean_object* v_unused_2729_; 
v_unused_2729_ = lean_ctor_get(v___x_2718_, 1);
lean_dec(v_unused_2729_);
v___x_2721_ = v___x_2718_;
v_isShared_2722_ = v_isSharedCheck_2728_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_pos_2719_);
lean_dec(v___x_2718_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2728_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
uint8_t v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2726_; 
v___x_2723_ = 0;
v___x_2724_ = lean_box(v___x_2723_);
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 1, v___x_2724_);
v___x_2726_ = v___x_2721_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_pos_2719_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v___x_2724_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
else
{
lean_object* v_pos_2730_; lean_object* v_err_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2761_; 
v_pos_2730_ = lean_ctor_get(v___x_2718_, 0);
v_err_2731_ = lean_ctor_get(v___x_2718_, 1);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2733_ = v___x_2718_;
v_isShared_2734_ = v_isSharedCheck_2761_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_err_2731_);
lean_inc(v_pos_2730_);
lean_dec(v___x_2718_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2761_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v_snd_2735_; uint8_t v_decide_2736_; 
v_snd_2735_ = lean_ctor_get(v_pos_2730_, 1);
v_decide_2736_ = lean_nat_dec_eq(v_snd_2713_, v_snd_2735_);
lean_dec(v_snd_2713_);
if (v_decide_2736_ == 0)
{
lean_object* v___x_2738_; 
lean_dec_ref(v_pm_2670_);
if (v_isShared_2734_ == 0)
{
v___x_2738_ = v___x_2733_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_pos_2730_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_err_2731_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
else
{
lean_object* v___x_2740_; 
lean_del_object(v___x_2733_);
lean_dec(v_err_2731_);
v___x_2740_ = l_Std_Internal_Parsec_String_pstring(v_pm_2670_, v_pos_2730_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_pos_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2750_; 
v_pos_2741_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2750_ == 0)
{
lean_object* v_unused_2751_; 
v_unused_2751_ = lean_ctor_get(v___x_2740_, 1);
lean_dec(v_unused_2751_);
v___x_2743_ = v___x_2740_;
v_isShared_2744_ = v_isSharedCheck_2750_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_pos_2741_);
lean_dec(v___x_2740_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2750_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
uint8_t v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2748_; 
v___x_2745_ = 1;
v___x_2746_ = lean_box(v___x_2745_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 1, v___x_2746_);
v___x_2748_ = v___x_2743_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_pos_2741_);
lean_ctor_set(v_reuseFailAlloc_2749_, 1, v___x_2746_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
else
{
lean_object* v_pos_2752_; lean_object* v_err_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
v_pos_2752_ = lean_ctor_get(v___x_2740_, 0);
v_err_2753_ = lean_ctor_get(v___x_2740_, 1);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2740_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_err_2753_);
lean_inc(v_pos_2752_);
lean_dec(v___x_2740_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_pos_2752_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v_err_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
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
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(lean_object* v_arr_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; uint8_t v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; uint8_t v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; uint8_t v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; uint8_t v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v_pairs_2803_; lean_object* v___x_2804_; 
v___x_2766_ = lean_unsigned_to_nat(6u);
v___x_2767_ = lean_unsigned_to_nat(0u);
v___x_2768_ = lean_array_fget_borrowed(v_arr_2764_, v___x_2767_);
v___x_2769_ = 0;
v___x_2770_ = lean_box(v___x_2769_);
lean_inc(v___x_2768_);
v___x_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2768_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
v___x_2772_ = lean_unsigned_to_nat(1u);
v___x_2773_ = lean_array_fget_borrowed(v_arr_2764_, v___x_2772_);
v___x_2774_ = 1;
v___x_2775_ = lean_box(v___x_2774_);
lean_inc(v___x_2773_);
v___x_2776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2773_);
lean_ctor_set(v___x_2776_, 1, v___x_2775_);
v___x_2777_ = lean_unsigned_to_nat(2u);
v___x_2778_ = lean_array_fget_borrowed(v_arr_2764_, v___x_2777_);
v___x_2779_ = 2;
v___x_2780_ = lean_box(v___x_2779_);
lean_inc(v___x_2778_);
v___x_2781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2778_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
v___x_2782_ = lean_unsigned_to_nat(3u);
v___x_2783_ = lean_array_fget_borrowed(v_arr_2764_, v___x_2782_);
v___x_2784_ = 3;
v___x_2785_ = lean_box(v___x_2784_);
lean_inc(v___x_2783_);
v___x_2786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2783_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
v___x_2787_ = lean_unsigned_to_nat(4u);
v___x_2788_ = lean_array_fget_borrowed(v_arr_2764_, v___x_2787_);
v___x_2789_ = 4;
v___x_2790_ = lean_box(v___x_2789_);
lean_inc(v___x_2788_);
v___x_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2788_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = lean_unsigned_to_nat(5u);
v___x_2793_ = lean_array_fget_borrowed(v_arr_2764_, v___x_2792_);
v___x_2794_ = 5;
v___x_2795_ = lean_box(v___x_2794_);
lean_inc(v___x_2793_);
v___x_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2793_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
v___x_2797_ = lean_mk_empty_array_with_capacity(v___x_2766_);
v___x_2798_ = lean_array_push(v___x_2797_, v___x_2771_);
v___x_2799_ = lean_array_push(v___x_2798_, v___x_2776_);
v___x_2800_ = lean_array_push(v___x_2799_, v___x_2781_);
v___x_2801_ = lean_array_push(v___x_2800_, v___x_2786_);
v___x_2802_ = lean_array_push(v___x_2801_, v___x_2791_);
v_pairs_2803_ = lean_array_push(v___x_2802_, v___x_2796_);
v___x_2804_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFromSymbols___redArg(v_pairs_2803_, v_a_2765_);
lean_dec_ref(v_pairs_2803_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom___boxed(lean_object* v_arr_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_arr_2805_, v_a_2806_);
lean_dec_ref(v_arr_2805_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(lean_object* v_parse_2808_, lean_object* v_size_2809_, lean_object* v_acc_2810_, lean_object* v_count_2811_, lean_object* v_a_2812_){
_start:
{
uint8_t v___x_2813_; 
v___x_2813_ = lean_nat_dec_le(v_size_2809_, v_count_2811_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; 
lean_inc_ref(v_parse_2808_);
v___x_2814_ = lean_apply_1(v_parse_2808_, v_a_2812_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_pos_2815_; lean_object* v_res_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v_pos_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_pos_2815_);
v_res_2816_ = lean_ctor_get(v___x_2814_, 1);
lean_inc(v_res_2816_);
lean_dec_ref_known(v___x_2814_, 2);
v___x_2817_ = lean_array_push(v_acc_2810_, v_res_2816_);
v___x_2818_ = lean_unsigned_to_nat(1u);
v___x_2819_ = lean_nat_add(v_count_2811_, v___x_2818_);
lean_dec(v_count_2811_);
v_acc_2810_ = v___x_2817_;
v_count_2811_ = v___x_2819_;
v_a_2812_ = v_pos_2815_;
goto _start;
}
else
{
lean_object* v_pos_2821_; lean_object* v_err_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_dec(v_count_2811_);
lean_dec_ref(v_acc_2810_);
lean_dec_ref(v_parse_2808_);
v_pos_2821_ = lean_ctor_get(v___x_2814_, 0);
v_err_2822_ = lean_ctor_get(v___x_2814_, 1);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2814_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_err_2822_);
lean_inc(v_pos_2821_);
lean_dec(v___x_2814_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_pos_2821_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_err_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
else
{
lean_object* v___x_2830_; 
lean_dec(v_count_2811_);
lean_dec_ref(v_parse_2808_);
v___x_2830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2830_, 0, v_a_2812_);
lean_ctor_set(v___x_2830_, 1, v_acc_2810_);
return v___x_2830_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg___boxed(lean_object* v_parse_2831_, lean_object* v_size_2832_, lean_object* v_acc_2833_, lean_object* v_count_2834_, lean_object* v_a_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2831_, v_size_2832_, v_acc_2833_, v_count_2834_, v_a_2835_);
lean_dec(v_size_2832_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go(lean_object* v_00_u03b1_2837_, lean_object* v_parse_2838_, lean_object* v_size_2839_, lean_object* v_acc_2840_, lean_object* v_count_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2838_, v_size_2839_, v_acc_2840_, v_count_2841_, v_a_2842_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___boxed(lean_object* v_00_u03b1_2844_, lean_object* v_parse_2845_, lean_object* v_size_2846_, lean_object* v_acc_2847_, lean_object* v_count_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go(v_00_u03b1_2844_, v_parse_2845_, v_size_2846_, v_acc_2847_, v_count_2848_, v_a_2849_);
lean_dec(v_size_2846_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(lean_object* v_parse_2853_, lean_object* v_size_2854_, lean_object* v_a_2855_){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2856_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___closed__0));
v___x_2857_ = lean_unsigned_to_nat(12u);
v___x_2858_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly_go___redArg(v_parse_2853_, v_size_2854_, v___x_2856_, v___x_2857_, v_a_2855_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg___boxed(lean_object* v_parse_2859_, lean_object* v_size_2860_, lean_object* v_a_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(v_parse_2859_, v_size_2860_, v_a_2861_);
lean_dec(v_size_2860_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly(lean_object* v_00_u03b1_2863_, lean_object* v_parse_2864_, lean_object* v_size_2865_, lean_object* v_a_2866_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly___redArg(v_parse_2864_, v_size_2865_, v_a_2866_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactly___boxed(lean_object* v_00_u03b1_2868_, lean_object* v_parse_2869_, lean_object* v_size_2870_, lean_object* v_a_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactly(v_00_u03b1_2868_, v_parse_2869_, v_size_2870_, v_a_2871_);
lean_dec(v_size_2870_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(lean_object* v_parse_2873_, lean_object* v_size_2874_, lean_object* v_acc_2875_, lean_object* v_count_2876_, lean_object* v_a_2877_){
_start:
{
uint8_t v___x_2878_; 
v___x_2878_ = lean_nat_dec_le(v_size_2874_, v_count_2876_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; 
lean_inc_ref(v_parse_2873_);
v___x_2879_ = lean_apply_1(v_parse_2873_, v_a_2877_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_pos_2880_; lean_object* v_res_2881_; uint32_t v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v_pos_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_pos_2880_);
v_res_2881_ = lean_ctor_get(v___x_2879_, 1);
lean_inc(v_res_2881_);
lean_dec_ref_known(v___x_2879_, 2);
v___x_2882_ = lean_unbox_uint32(v_res_2881_);
lean_dec(v_res_2881_);
v___x_2883_ = lean_string_push(v_acc_2875_, v___x_2882_);
v___x_2884_ = lean_unsigned_to_nat(1u);
v___x_2885_ = lean_nat_add(v_count_2876_, v___x_2884_);
lean_dec(v_count_2876_);
v_acc_2875_ = v___x_2883_;
v_count_2876_ = v___x_2885_;
v_a_2877_ = v_pos_2880_;
goto _start;
}
else
{
lean_object* v_pos_2887_; lean_object* v_err_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec(v_count_2876_);
lean_dec_ref(v_acc_2875_);
lean_dec_ref(v_parse_2873_);
v_pos_2887_ = lean_ctor_get(v___x_2879_, 0);
v_err_2888_ = lean_ctor_get(v___x_2879_, 1);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2879_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_err_2888_);
lean_inc(v_pos_2887_);
lean_dec(v___x_2879_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_pos_2887_);
lean_ctor_set(v_reuseFailAlloc_2894_, 1, v_err_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
else
{
lean_object* v___x_2896_; 
lean_dec(v_count_2876_);
lean_dec_ref(v_parse_2873_);
v___x_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2896_, 0, v_a_2877_);
lean_ctor_set(v___x_2896_, 1, v_acc_2875_);
return v___x_2896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go___boxed(lean_object* v_parse_2897_, lean_object* v_size_2898_, lean_object* v_acc_2899_, lean_object* v_count_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(v_parse_2897_, v_size_2898_, v_acc_2899_, v_count_2900_, v_a_2901_);
lean_dec(v_size_2898_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(lean_object* v_parse_2903_, lean_object* v_size_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2906_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_2907_ = lean_unsigned_to_nat(0u);
v___x_2908_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars_go(v_parse_2903_, v_size_2904_, v___x_2906_, v___x_2907_, v_a_2905_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars___boxed(lean_object* v_parse_2909_, lean_object* v_size_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v_parse_2909_, v_size_2910_, v_a_2911_);
lean_dec(v_size_2910_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(lean_object* v_parser_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v_pos_2916_; lean_object* v_res_2917_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__1));
lean_inc_ref(v_a_2914_);
v___x_2950_ = l_Std_Internal_Parsec_String_pstring(v___x_2949_, v_a_2914_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_pos_2951_; lean_object* v_res_2952_; lean_object* v___x_2953_; 
lean_dec_ref(v_a_2914_);
v_pos_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_pos_2951_);
v_res_2952_ = lean_ctor_get(v___x_2950_, 1);
lean_inc(v_res_2952_);
lean_dec_ref_known(v___x_2950_, 2);
v___x_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2953_, 0, v_res_2952_);
v_pos_2916_ = v_pos_2951_;
v_res_2917_ = v___x_2953_;
goto v___jp_2915_;
}
else
{
lean_object* v_pos_2954_; lean_object* v_err_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2966_; 
v_pos_2954_ = lean_ctor_get(v___x_2950_, 0);
v_err_2955_ = lean_ctor_get(v___x_2950_, 1);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2957_ = v___x_2950_;
v_isShared_2958_ = v_isSharedCheck_2966_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_err_2955_);
lean_inc(v_pos_2954_);
lean_dec(v___x_2950_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2966_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v_snd_2959_; lean_object* v_snd_2960_; uint8_t v_decide_2961_; 
v_snd_2959_ = lean_ctor_get(v_a_2914_, 1);
lean_inc(v_snd_2959_);
lean_dec_ref(v_a_2914_);
v_snd_2960_ = lean_ctor_get(v_pos_2954_, 1);
v_decide_2961_ = lean_nat_dec_eq(v_snd_2959_, v_snd_2960_);
lean_dec(v_snd_2959_);
if (v_decide_2961_ == 0)
{
lean_object* v___x_2963_; 
lean_dec_ref(v_parser_2913_);
if (v_isShared_2958_ == 0)
{
v___x_2963_ = v___x_2957_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_pos_2954_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_err_2955_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
else
{
lean_object* v___x_2965_; 
lean_del_object(v___x_2957_);
lean_dec(v_err_2955_);
v___x_2965_ = lean_box(0);
v_pos_2916_ = v_pos_2954_;
v_res_2917_ = v___x_2965_;
goto v___jp_2915_;
}
}
}
v___jp_2915_:
{
lean_object* v___x_2918_; 
v___x_2918_ = lean_apply_1(v_parser_2913_, v_pos_2916_);
if (lean_obj_tag(v___x_2918_) == 0)
{
if (lean_obj_tag(v_res_2917_) == 0)
{
lean_object* v_pos_2919_; lean_object* v_res_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2928_; 
v_pos_2919_ = lean_ctor_get(v___x_2918_, 0);
v_res_2920_ = lean_ctor_get(v___x_2918_, 1);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2922_ = v___x_2918_;
v_isShared_2923_ = v_isSharedCheck_2928_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_res_2920_);
lean_inc(v_pos_2919_);
lean_dec(v___x_2918_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2928_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2924_; lean_object* v___x_2926_; 
v___x_2924_ = lean_nat_to_int(v_res_2920_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 1, v___x_2924_);
v___x_2926_ = v___x_2922_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_pos_2919_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v___x_2924_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
else
{
lean_object* v_pos_2929_; lean_object* v_res_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2939_; 
lean_dec_ref_known(v_res_2917_, 1);
v_pos_2929_ = lean_ctor_get(v___x_2918_, 0);
v_res_2930_ = lean_ctor_get(v___x_2918_, 1);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2932_ = v___x_2918_;
v_isShared_2933_ = v_isSharedCheck_2939_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_res_2930_);
lean_inc(v_pos_2929_);
lean_dec(v___x_2918_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2939_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2937_; 
v___x_2934_ = lean_nat_to_int(v_res_2930_);
v___x_2935_ = lean_int_neg(v___x_2934_);
lean_dec(v___x_2934_);
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 1, v___x_2935_);
v___x_2937_ = v___x_2932_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_pos_2929_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v___x_2935_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
else
{
lean_object* v_pos_2940_; lean_object* v_err_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_dec(v_res_2917_);
v_pos_2940_ = lean_ctor_get(v___x_2918_, 0);
v_err_2941_ = lean_ctor_get(v___x_2918_, 1);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2918_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_err_2941_);
lean_inc(v_pos_2940_);
lean_dec(v___x_2918_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_pos_2940_);
lean_ctor_set(v_reuseFailAlloc_2947_, 1, v_err_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___lam__0(lean_object* v___y_2967_){
_start:
{
lean_object* v_fst_2971_; lean_object* v_snd_2972_; lean_object* v___x_2973_; uint8_t v_decide_2974_; 
v_fst_2971_ = lean_ctor_get(v___y_2967_, 0);
v_snd_2972_ = lean_ctor_get(v___y_2967_, 1);
v___x_2973_ = lean_string_utf8_byte_size(v_fst_2971_);
v_decide_2974_ = lean_nat_dec_eq(v_snd_2972_, v___x_2973_);
if (v_decide_2974_ == 0)
{
uint32_t v_c_2975_; lean_object* v___x_2976_; lean_object* v_it_x27_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; uint32_t v___x_2980_; uint8_t v___x_2981_; 
v_c_2975_ = lean_string_utf8_get_fast(v_fst_2971_, v_snd_2972_);
v___x_2976_ = lean_string_utf8_next_fast(v_fst_2971_, v_snd_2972_);
lean_inc(v_fst_2971_);
v_it_x27_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_2977_, 0, v_fst_2971_);
lean_ctor_set(v_it_x27_2977_, 1, v___x_2976_);
v___x_2978_ = lean_box_uint32(v_c_2975_);
v___x_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2979_, 0, v_it_x27_2977_);
lean_ctor_set(v___x_2979_, 1, v___x_2978_);
v___x_2980_ = 48;
v___x_2981_ = lean_uint32_dec_le(v___x_2980_, v_c_2975_);
if (v___x_2981_ == 0)
{
lean_dec_ref_known(v___x_2979_, 2);
goto v___jp_2968_;
}
else
{
uint32_t v___x_2982_; uint8_t v___x_2983_; 
v___x_2982_ = 57;
v___x_2983_ = lean_uint32_dec_le(v_c_2975_, v___x_2982_);
if (v___x_2983_ == 0)
{
lean_dec_ref_known(v___x_2979_, 2);
goto v___jp_2968_;
}
else
{
lean_dec_ref(v___y_2967_);
return v___x_2979_;
}
}
}
else
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = lean_box(0);
v___x_2985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___y_2967_);
lean_ctor_set(v___x_2985_, 1, v___x_2984_);
return v___x_2985_;
}
v___jp_2968_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2969_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_2970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___y_2967_);
lean_ctor_set(v___x_2970_, 1, v___x_2969_);
return v___x_2970_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(lean_object* v_size_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v___f_2989_; lean_object* v___x_2990_; 
v___f_2989_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_2990_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_2989_, v_size_2987_, v_a_2988_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_pos_2991_; lean_object* v_res_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3003_; 
v_pos_2991_ = lean_ctor_get(v___x_2990_, 0);
v_res_2992_ = lean_ctor_get(v___x_2990_, 1);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2994_ = v___x_2990_;
v_isShared_2995_ = v_isSharedCheck_3003_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_res_2992_);
lean_inc(v_pos_2991_);
lean_dec(v___x_2990_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3003_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3001_; 
v___x_2996_ = lean_unsigned_to_nat(0u);
v___x_2997_ = lean_string_utf8_byte_size(v_res_2992_);
v___x_2998_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2998_, 0, v_res_2992_);
lean_ctor_set(v___x_2998_, 1, v___x_2996_);
lean_ctor_set(v___x_2998_, 2, v___x_2997_);
v___x_2999_ = l_String_Slice_toNat_x21(v___x_2998_);
lean_dec_ref_known(v___x_2998_, 3);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 1, v___x_2999_);
v___x_3001_ = v___x_2994_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_pos_2991_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v___x_2999_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
else
{
lean_object* v_pos_3004_; lean_object* v_err_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
v_pos_3004_ = lean_ctor_get(v___x_2990_, 0);
v_err_3005_ = lean_ctor_get(v___x_2990_, 1);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2990_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_err_3005_);
lean_inc(v_pos_3004_);
lean_dec(v___x_2990_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_pos_3004_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_err_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed(lean_object* v_size_3013_, lean_object* v_a_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_size_3013_, v_a_3014_);
lean_dec(v_size_3013_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(lean_object* v_acc_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v_fst_3018_; lean_object* v_snd_3019_; lean_object* v_pos_3021_; lean_object* v_snd_3022_; lean_object* v_err_3023_; lean_object* v___x_3029_; uint8_t v_decide_3030_; 
v_fst_3018_ = lean_ctor_get(v_a_3017_, 0);
v_snd_3019_ = lean_ctor_get(v_a_3017_, 1);
lean_inc(v_snd_3019_);
v___x_3029_ = lean_string_utf8_byte_size(v_fst_3018_);
v_decide_3030_ = lean_nat_dec_eq(v_snd_3019_, v___x_3029_);
if (v_decide_3030_ == 0)
{
uint32_t v_c_3031_; uint32_t v___x_3032_; uint8_t v___x_3033_; 
v_c_3031_ = lean_string_utf8_get_fast(v_fst_3018_, v_snd_3019_);
v___x_3032_ = 48;
v___x_3033_ = lean_uint32_dec_le(v___x_3032_, v_c_3031_);
if (v___x_3033_ == 0)
{
goto v___jp_3027_;
}
else
{
uint32_t v___x_3034_; uint8_t v___x_3035_; 
v___x_3034_ = 57;
v___x_3035_ = lean_uint32_dec_le(v_c_3031_, v___x_3034_);
if (v___x_3035_ == 0)
{
goto v___jp_3027_;
}
else
{
lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3045_; 
lean_inc(v_fst_3018_);
v_isSharedCheck_3045_ = !lean_is_exclusive(v_a_3017_);
if (v_isSharedCheck_3045_ == 0)
{
lean_object* v_unused_3046_; lean_object* v_unused_3047_; 
v_unused_3046_ = lean_ctor_get(v_a_3017_, 1);
lean_dec(v_unused_3046_);
v_unused_3047_ = lean_ctor_get(v_a_3017_, 0);
lean_dec(v_unused_3047_);
v___x_3037_ = v_a_3017_;
v_isShared_3038_ = v_isSharedCheck_3045_;
goto v_resetjp_3036_;
}
else
{
lean_dec(v_a_3017_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3045_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3039_; lean_object* v_it_x27_3041_; 
v___x_3039_ = lean_string_utf8_next_fast(v_fst_3018_, v_snd_3019_);
lean_dec(v_snd_3019_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 1, v___x_3039_);
v_it_x27_3041_ = v___x_3037_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_fst_3018_);
lean_ctor_set(v_reuseFailAlloc_3044_, 1, v___x_3039_);
v_it_x27_3041_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
lean_object* v___x_3042_; 
v___x_3042_ = lean_string_push(v_acc_3016_, v_c_3031_);
v_acc_3016_ = v___x_3042_;
v_a_3017_ = v_it_x27_3041_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_3048_; 
v___x_3048_ = lean_box(0);
lean_inc(v_snd_3019_);
v_pos_3021_ = v_a_3017_;
v_snd_3022_ = v_snd_3019_;
v_err_3023_ = v___x_3048_;
goto v___jp_3020_;
}
v___jp_3020_:
{
uint8_t v_decide_3024_; 
v_decide_3024_ = lean_nat_dec_eq(v_snd_3019_, v_snd_3022_);
lean_dec(v_snd_3022_);
lean_dec(v_snd_3019_);
if (v_decide_3024_ == 0)
{
lean_object* v___x_3025_; 
lean_dec_ref(v_acc_3016_);
lean_inc(v_err_3023_);
v___x_3025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3025_, 0, v_pos_3021_);
lean_ctor_set(v___x_3025_, 1, v_err_3023_);
return v___x_3025_;
}
else
{
lean_object* v___x_3026_; 
v___x_3026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3026_, 0, v_pos_3021_);
lean_ctor_set(v___x_3026_, 1, v_acc_3016_);
return v___x_3026_;
}
}
v___jp_3027_:
{
lean_object* v___x_3028_; 
v___x_3028_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3019_);
v_pos_3021_ = v_a_3017_;
v_snd_3022_ = v_snd_3019_;
v_err_3023_ = v___x_3028_;
goto v___jp_3020_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(lean_object* v_size_3049_, lean_object* v_a_3050_){
_start:
{
lean_object* v_pos_3052_; lean_object* v_res_3053_; lean_object* v___y_3060_; lean_object* v___f_3072_; lean_object* v___x_3073_; 
v___f_3072_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3073_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3072_, v_size_3049_, v_a_3050_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_pos_3074_; lean_object* v_res_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v_pos_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_pos_3074_);
v_res_3075_ = lean_ctor_get(v___x_3073_, 1);
lean_inc(v_res_3075_);
lean_dec_ref_known(v___x_3073_, 2);
v___x_3076_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3077_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum_spec__0(v___x_3076_, v_pos_3074_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_pos_3078_; lean_object* v_res_3079_; lean_object* v___x_3080_; 
v_pos_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_pos_3078_);
v_res_3079_ = lean_ctor_get(v___x_3077_, 1);
lean_inc(v_res_3079_);
lean_dec_ref_known(v___x_3077_, 2);
v___x_3080_ = lean_string_append(v_res_3075_, v_res_3079_);
lean_dec(v_res_3079_);
v_pos_3052_ = v_pos_3078_;
v_res_3053_ = v___x_3080_;
goto v___jp_3051_;
}
else
{
lean_dec(v_res_3075_);
v___y_3060_ = v___x_3077_;
goto v___jp_3059_;
}
}
else
{
v___y_3060_ = v___x_3073_;
goto v___jp_3059_;
}
v___jp_3051_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3054_ = lean_unsigned_to_nat(0u);
v___x_3055_ = lean_string_utf8_byte_size(v_res_3053_);
v___x_3056_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3056_, 0, v_res_3053_);
lean_ctor_set(v___x_3056_, 1, v___x_3054_);
lean_ctor_set(v___x_3056_, 2, v___x_3055_);
v___x_3057_ = l_String_Slice_toNat_x21(v___x_3056_);
lean_dec_ref_known(v___x_3056_, 3);
v___x_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3058_, 0, v_pos_3052_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
return v___x_3058_;
}
v___jp_3059_:
{
if (lean_obj_tag(v___y_3060_) == 0)
{
lean_object* v_pos_3061_; lean_object* v_res_3062_; 
v_pos_3061_ = lean_ctor_get(v___y_3060_, 0);
lean_inc(v_pos_3061_);
v_res_3062_ = lean_ctor_get(v___y_3060_, 1);
lean_inc(v_res_3062_);
lean_dec_ref_known(v___y_3060_, 2);
v_pos_3052_ = v_pos_3061_;
v_res_3053_ = v_res_3062_;
goto v___jp_3051_;
}
else
{
lean_object* v_pos_3063_; lean_object* v_err_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
v_pos_3063_ = lean_ctor_get(v___y_3060_, 0);
v_err_3064_ = lean_ctor_get(v___y_3060_, 1);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___y_3060_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___y_3060_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_err_3064_);
lean_inc(v_pos_3063_);
lean_dec(v___y_3060_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_pos_3063_);
lean_ctor_set(v_reuseFailAlloc_3070_, 1, v_err_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum___boxed(lean_object* v_size_3081_, lean_object* v_a_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v_size_3081_, v_a_3082_);
lean_dec(v_size_3081_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(lean_object* v_size_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v___x_3086_; uint8_t v___x_3087_; 
v___x_3086_ = lean_unsigned_to_nat(1u);
v___x_3087_ = lean_nat_dec_eq(v_size_3084_, v___x_3086_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; 
v___x_3088_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_size_3084_, v_a_3085_);
return v___x_3088_;
}
else
{
lean_object* v___x_3089_; 
v___x_3089_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v___x_3086_, v_a_3085_);
return v___x_3089_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed(lean_object* v_size_3090_, lean_object* v_a_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_size_3090_, v_a_3091_);
lean_dec(v_size_3090_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(lean_object* v_size_3093_, lean_object* v_pad_3094_, lean_object* v_a_3095_){
_start:
{
lean_object* v_pos_3097_; lean_object* v_res_3098_; lean_object* v___f_3104_; lean_object* v___x_3105_; 
v___f_3104_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___closed__0));
v___x_3105_ = l___private_Std_Time_Format_Basic_0__Std_Time_exactlyChars(v___f_3104_, v_size_3093_, v_a_3095_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_pos_3106_; lean_object* v_res_3107_; uint32_t v___x_3108_; lean_object* v___x_3109_; 
v_pos_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_pos_3106_);
v_res_3107_ = lean_ctor_get(v___x_3105_, 1);
lean_inc(v_res_3107_);
lean_dec_ref_known(v___x_3105_, 2);
v___x_3108_ = 48;
v___x_3109_ = l___private_Std_Time_Format_Basic_0__Std_Time_rightPadAscii(v_pad_3094_, v___x_3108_, v_res_3107_);
v_pos_3097_ = v_pos_3106_;
v_res_3098_ = v___x_3109_;
goto v___jp_3096_;
}
else
{
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_pos_3110_; lean_object* v_res_3111_; 
v_pos_3110_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_pos_3110_);
v_res_3111_ = lean_ctor_get(v___x_3105_, 1);
lean_inc(v_res_3111_);
lean_dec_ref_known(v___x_3105_, 2);
v_pos_3097_ = v_pos_3110_;
v_res_3098_ = v_res_3111_;
goto v___jp_3096_;
}
else
{
lean_object* v_pos_3112_; lean_object* v_err_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
v_pos_3112_ = lean_ctor_get(v___x_3105_, 0);
v_err_3113_ = lean_ctor_get(v___x_3105_, 1);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3105_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_err_3113_);
lean_inc(v_pos_3112_);
lean_dec(v___x_3105_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_pos_3112_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v_err_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
v___jp_3096_:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3099_ = lean_unsigned_to_nat(0u);
v___x_3100_ = lean_string_utf8_byte_size(v_res_3098_);
v___x_3101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3101_, 0, v_res_3098_);
lean_ctor_set(v___x_3101_, 1, v___x_3099_);
lean_ctor_set(v___x_3101_, 2, v___x_3100_);
v___x_3102_ = l_String_Slice_toNat_x21(v___x_3101_);
lean_dec_ref_known(v___x_3101_, 3);
v___x_3103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3103_, 0, v_pos_3097_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
return v___x_3103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed(lean_object* v_size_3121_, lean_object* v_pad_3122_, lean_object* v_a_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum(v_size_3121_, v_pad_3122_, v_a_3123_);
lean_dec(v_pad_3122_);
lean_dec(v_size_3121_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(lean_object* v_acc_3125_, lean_object* v_a_3126_){
_start:
{
lean_object* v_pos_3128_; uint32_t v_res_3129_; lean_object* v_fst_3132_; lean_object* v_snd_3133_; lean_object* v_pos_3135_; lean_object* v_snd_3136_; lean_object* v_err_3137_; lean_object* v___x_3141_; uint8_t v_decide_3142_; 
v_fst_3132_ = lean_ctor_get(v_a_3126_, 0);
v_snd_3133_ = lean_ctor_get(v_a_3126_, 1);
lean_inc(v_snd_3133_);
v___x_3141_ = lean_string_utf8_byte_size(v_fst_3132_);
v_decide_3142_ = lean_nat_dec_eq(v_snd_3133_, v___x_3141_);
if (v_decide_3142_ == 0)
{
uint32_t v_c_3143_; lean_object* v___x_3144_; lean_object* v_it_x27_3145_; uint32_t v___x_3164_; uint8_t v___x_3165_; 
v_c_3143_ = lean_string_utf8_get_fast(v_fst_3132_, v_snd_3133_);
v___x_3144_ = lean_string_utf8_next_fast(v_fst_3132_, v_snd_3133_);
lean_inc(v_fst_3132_);
v_it_x27_3145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3145_, 0, v_fst_3132_);
lean_ctor_set(v_it_x27_3145_, 1, v___x_3144_);
v___x_3164_ = 65;
v___x_3165_ = lean_uint32_dec_le(v___x_3164_, v_c_3143_);
if (v___x_3165_ == 0)
{
goto v___jp_3159_;
}
else
{
uint32_t v___x_3166_; uint8_t v___x_3167_; 
v___x_3166_ = 90;
v___x_3167_ = lean_uint32_dec_le(v_c_3143_, v___x_3166_);
if (v___x_3167_ == 0)
{
goto v___jp_3159_;
}
else
{
lean_dec(v_snd_3133_);
lean_dec_ref(v_a_3126_);
v_pos_3128_ = v_it_x27_3145_;
v_res_3129_ = v_c_3143_;
goto v___jp_3127_;
}
}
v___jp_3146_:
{
uint32_t v___x_3147_; uint8_t v___x_3148_; 
v___x_3147_ = 95;
v___x_3148_ = lean_uint32_dec_eq(v_c_3143_, v___x_3147_);
if (v___x_3148_ == 0)
{
uint32_t v___x_3149_; uint8_t v___x_3150_; 
v___x_3149_ = 45;
v___x_3150_ = lean_uint32_dec_eq(v_c_3143_, v___x_3149_);
if (v___x_3150_ == 0)
{
uint32_t v___x_3151_; uint8_t v___x_3152_; 
v___x_3151_ = 47;
v___x_3152_ = lean_uint32_dec_eq(v_c_3143_, v___x_3151_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; 
lean_dec_ref_known(v_it_x27_3145_, 2);
v___x_3153_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3133_);
v_pos_3135_ = v_a_3126_;
v_snd_3136_ = v_snd_3133_;
v_err_3137_ = v___x_3153_;
goto v___jp_3134_;
}
else
{
lean_dec(v_snd_3133_);
lean_dec_ref(v_a_3126_);
v_pos_3128_ = v_it_x27_3145_;
v_res_3129_ = v_c_3143_;
goto v___jp_3127_;
}
}
else
{
lean_dec(v_snd_3133_);
lean_dec_ref(v_a_3126_);
v_pos_3128_ = v_it_x27_3145_;
v_res_3129_ = v_c_3143_;
goto v___jp_3127_;
}
}
else
{
lean_dec(v_snd_3133_);
lean_dec_ref(v_a_3126_);
v_pos_3128_ = v_it_x27_3145_;
v_res_3129_ = v_c_3143_;
goto v___jp_3127_;
}
}
v___jp_3154_:
{
uint32_t v___x_3155_; uint8_t v___x_3156_; 
v___x_3155_ = 48;
v___x_3156_ = lean_uint32_dec_le(v___x_3155_, v_c_3143_);
if (v___x_3156_ == 0)
{
goto v___jp_3146_;
}
else
{
uint32_t v___x_3157_; uint8_t v___x_3158_; 
v___x_3157_ = 57;
v___x_3158_ = lean_uint32_dec_le(v_c_3143_, v___x_3157_);
if (v___x_3158_ == 0)
{
goto v___jp_3146_;
}
else
{
lean_dec(v_snd_3133_);
lean_dec_ref(v_a_3126_);
v_pos_3128_ = v_it_x27_3145_;
v_res_3129_ = v_c_3143_;
goto v___jp_3127_;
}
}
}
v___jp_3159_:
{
uint32_t v___x_3160_; uint8_t v___x_3161_; 
v___x_3160_ = 97;
v___x_3161_ = lean_uint32_dec_le(v___x_3160_, v_c_3143_);
if (v___x_3161_ == 0)
{
goto v___jp_3154_;
}
else
{
uint32_t v___x_3162_; uint8_t v___x_3163_; 
v___x_3162_ = 122;
v___x_3163_ = lean_uint32_dec_le(v_c_3143_, v___x_3162_);
if (v___x_3163_ == 0)
{
goto v___jp_3154_;
}
else
{
lean_dec(v_snd_3133_);
lean_dec_ref(v_a_3126_);
v_pos_3128_ = v_it_x27_3145_;
v_res_3129_ = v_c_3143_;
goto v___jp_3127_;
}
}
}
}
else
{
lean_object* v___x_3168_; 
v___x_3168_ = lean_box(0);
lean_inc(v_snd_3133_);
v_pos_3135_ = v_a_3126_;
v_snd_3136_ = v_snd_3133_;
v_err_3137_ = v___x_3168_;
goto v___jp_3134_;
}
v___jp_3127_:
{
lean_object* v___x_3130_; 
v___x_3130_ = lean_string_push(v_acc_3125_, v_res_3129_);
v_acc_3125_ = v___x_3130_;
v_a_3126_ = v_pos_3128_;
goto _start;
}
v___jp_3134_:
{
uint8_t v_decide_3138_; 
v_decide_3138_ = lean_nat_dec_eq(v_snd_3133_, v_snd_3136_);
lean_dec(v_snd_3136_);
lean_dec(v_snd_3133_);
if (v_decide_3138_ == 0)
{
lean_object* v___x_3139_; 
lean_dec_ref(v_acc_3125_);
lean_inc(v_err_3137_);
v___x_3139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3139_, 0, v_pos_3135_);
lean_ctor_set(v___x_3139_, 1, v_err_3137_);
return v___x_3139_;
}
else
{
lean_object* v___x_3140_; 
v___x_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3140_, 0, v_pos_3135_);
lean_ctor_set(v___x_3140_, 1, v_acc_3125_);
return v___x_3140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(lean_object* v_acc_3169_, lean_object* v_a_3170_){
_start:
{
lean_object* v_pos_3172_; uint32_t v_res_3173_; lean_object* v_fst_3176_; lean_object* v_snd_3177_; lean_object* v_pos_3179_; lean_object* v_snd_3180_; lean_object* v_err_3181_; lean_object* v___x_3185_; uint8_t v_decide_3186_; 
v_fst_3176_ = lean_ctor_get(v_a_3170_, 0);
v_snd_3177_ = lean_ctor_get(v_a_3170_, 1);
lean_inc(v_snd_3177_);
v___x_3185_ = lean_string_utf8_byte_size(v_fst_3176_);
v_decide_3186_ = lean_nat_dec_eq(v_snd_3177_, v___x_3185_);
if (v_decide_3186_ == 0)
{
uint32_t v_c_3187_; lean_object* v___x_3188_; lean_object* v_it_x27_3189_; uint32_t v___x_3208_; uint8_t v___x_3209_; 
v_c_3187_ = lean_string_utf8_get_fast(v_fst_3176_, v_snd_3177_);
v___x_3188_ = lean_string_utf8_next_fast(v_fst_3176_, v_snd_3177_);
lean_inc(v_fst_3176_);
v_it_x27_3189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3189_, 0, v_fst_3176_);
lean_ctor_set(v_it_x27_3189_, 1, v___x_3188_);
v___x_3208_ = 65;
v___x_3209_ = lean_uint32_dec_le(v___x_3208_, v_c_3187_);
if (v___x_3209_ == 0)
{
goto v___jp_3203_;
}
else
{
uint32_t v___x_3210_; uint8_t v___x_3211_; 
v___x_3210_ = 90;
v___x_3211_ = lean_uint32_dec_le(v_c_3187_, v___x_3210_);
if (v___x_3211_ == 0)
{
goto v___jp_3203_;
}
else
{
lean_dec(v_snd_3177_);
lean_dec_ref(v_a_3170_);
v_pos_3172_ = v_it_x27_3189_;
v_res_3173_ = v_c_3187_;
goto v___jp_3171_;
}
}
v___jp_3190_:
{
uint32_t v___x_3191_; uint8_t v___x_3192_; 
v___x_3191_ = 95;
v___x_3192_ = lean_uint32_dec_eq(v_c_3187_, v___x_3191_);
if (v___x_3192_ == 0)
{
uint32_t v___x_3193_; uint8_t v___x_3194_; 
v___x_3193_ = 45;
v___x_3194_ = lean_uint32_dec_eq(v_c_3187_, v___x_3193_);
if (v___x_3194_ == 0)
{
uint32_t v___x_3195_; uint8_t v___x_3196_; 
v___x_3195_ = 47;
v___x_3196_ = lean_uint32_dec_eq(v_c_3187_, v___x_3195_);
if (v___x_3196_ == 0)
{
lean_object* v___x_3197_; 
lean_dec_ref_known(v_it_x27_3189_, 2);
v___x_3197_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
lean_inc(v_snd_3177_);
v_pos_3179_ = v_a_3170_;
v_snd_3180_ = v_snd_3177_;
v_err_3181_ = v___x_3197_;
goto v___jp_3178_;
}
else
{
lean_dec(v_snd_3177_);
lean_dec_ref(v_a_3170_);
v_pos_3172_ = v_it_x27_3189_;
v_res_3173_ = v_c_3187_;
goto v___jp_3171_;
}
}
else
{
lean_dec(v_snd_3177_);
lean_dec_ref(v_a_3170_);
v_pos_3172_ = v_it_x27_3189_;
v_res_3173_ = v_c_3187_;
goto v___jp_3171_;
}
}
else
{
lean_dec(v_snd_3177_);
lean_dec_ref(v_a_3170_);
v_pos_3172_ = v_it_x27_3189_;
v_res_3173_ = v_c_3187_;
goto v___jp_3171_;
}
}
v___jp_3198_:
{
uint32_t v___x_3199_; uint8_t v___x_3200_; 
v___x_3199_ = 48;
v___x_3200_ = lean_uint32_dec_le(v___x_3199_, v_c_3187_);
if (v___x_3200_ == 0)
{
goto v___jp_3190_;
}
else
{
uint32_t v___x_3201_; uint8_t v___x_3202_; 
v___x_3201_ = 57;
v___x_3202_ = lean_uint32_dec_le(v_c_3187_, v___x_3201_);
if (v___x_3202_ == 0)
{
goto v___jp_3190_;
}
else
{
lean_dec(v_snd_3177_);
lean_dec_ref(v_a_3170_);
v_pos_3172_ = v_it_x27_3189_;
v_res_3173_ = v_c_3187_;
goto v___jp_3171_;
}
}
}
v___jp_3203_:
{
uint32_t v___x_3204_; uint8_t v___x_3205_; 
v___x_3204_ = 97;
v___x_3205_ = lean_uint32_dec_le(v___x_3204_, v_c_3187_);
if (v___x_3205_ == 0)
{
goto v___jp_3198_;
}
else
{
uint32_t v___x_3206_; uint8_t v___x_3207_; 
v___x_3206_ = 122;
v___x_3207_ = lean_uint32_dec_le(v_c_3187_, v___x_3206_);
if (v___x_3207_ == 0)
{
goto v___jp_3198_;
}
else
{
lean_dec(v_snd_3177_);
lean_dec_ref(v_a_3170_);
v_pos_3172_ = v_it_x27_3189_;
v_res_3173_ = v_c_3187_;
goto v___jp_3171_;
}
}
}
}
else
{
lean_object* v___x_3212_; 
v___x_3212_ = lean_box(0);
lean_inc(v_snd_3177_);
v_pos_3179_ = v_a_3170_;
v_snd_3180_ = v_snd_3177_;
v_err_3181_ = v___x_3212_;
goto v___jp_3178_;
}
v___jp_3171_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3174_ = lean_string_push(v_acc_3169_, v_res_3173_);
v___x_3175_ = l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0_spec__0(v___x_3174_, v_pos_3172_);
return v___x_3175_;
}
v___jp_3178_:
{
uint8_t v_decide_3182_; 
v_decide_3182_ = lean_nat_dec_eq(v_snd_3177_, v_snd_3180_);
lean_dec(v_snd_3180_);
lean_dec(v_snd_3177_);
if (v_decide_3182_ == 0)
{
lean_object* v___x_3183_; 
lean_dec_ref(v_acc_3169_);
lean_inc(v_err_3181_);
v___x_3183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3183_, 0, v_pos_3179_);
lean_ctor_set(v___x_3183_, 1, v_err_3181_);
return v___x_3183_;
}
else
{
lean_object* v___x_3184_; 
v___x_3184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3184_, 0, v_pos_3179_);
lean_ctor_set(v___x_3184_, 1, v_acc_3169_);
return v___x_3184_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(lean_object* v_a_3213_){
_start:
{
lean_object* v_fst_3214_; lean_object* v_snd_3215_; lean_object* v___x_3216_; uint8_t v_decide_3217_; 
v_fst_3214_ = lean_ctor_get(v_a_3213_, 0);
v_snd_3215_ = lean_ctor_get(v_a_3213_, 1);
v___x_3216_ = lean_string_utf8_byte_size(v_fst_3214_);
v_decide_3217_ = lean_nat_dec_eq(v_snd_3215_, v___x_3216_);
if (v_decide_3217_ == 0)
{
uint32_t v_c_3218_; lean_object* v___x_3219_; uint32_t v___x_3244_; uint8_t v___x_3245_; 
v_c_3218_ = lean_string_utf8_get_fast(v_fst_3214_, v_snd_3215_);
v___x_3219_ = lean_string_utf8_next_fast(v_fst_3214_, v_snd_3215_);
v___x_3244_ = 65;
v___x_3245_ = lean_uint32_dec_le(v___x_3244_, v_c_3218_);
if (v___x_3245_ == 0)
{
goto v___jp_3239_;
}
else
{
uint32_t v___x_3246_; uint8_t v___x_3247_; 
v___x_3246_ = 90;
v___x_3247_ = lean_uint32_dec_le(v_c_3218_, v___x_3246_);
if (v___x_3247_ == 0)
{
goto v___jp_3239_;
}
else
{
lean_inc(v_fst_3214_);
lean_dec_ref(v_a_3213_);
goto v___jp_3220_;
}
}
v___jp_3220_:
{
lean_object* v_it_x27_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v_it_x27_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3221_, 0, v_fst_3214_);
lean_ctor_set(v_it_x27_3221_, 1, v___x_3219_);
v___x_3222_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_3223_ = lean_string_push(v___x_3222_, v_c_3218_);
v___x_3224_ = l_Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier_spec__0(v___x_3223_, v_it_x27_3221_);
return v___x_3224_;
}
v___jp_3225_:
{
uint32_t v___x_3226_; uint8_t v___x_3227_; 
v___x_3226_ = 95;
v___x_3227_ = lean_uint32_dec_eq(v_c_3218_, v___x_3226_);
if (v___x_3227_ == 0)
{
uint32_t v___x_3228_; uint8_t v___x_3229_; 
v___x_3228_ = 45;
v___x_3229_ = lean_uint32_dec_eq(v_c_3218_, v___x_3228_);
if (v___x_3229_ == 0)
{
uint32_t v___x_3230_; uint8_t v___x_3231_; 
v___x_3230_ = 47;
v___x_3231_ = lean_uint32_dec_eq(v_c_3218_, v___x_3230_);
if (v___x_3231_ == 0)
{
lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3232_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3233_, 0, v_a_3213_);
lean_ctor_set(v___x_3233_, 1, v___x_3232_);
return v___x_3233_;
}
else
{
lean_inc(v_fst_3214_);
lean_dec_ref(v_a_3213_);
goto v___jp_3220_;
}
}
else
{
lean_inc(v_fst_3214_);
lean_dec_ref(v_a_3213_);
goto v___jp_3220_;
}
}
else
{
lean_inc(v_fst_3214_);
lean_dec_ref(v_a_3213_);
goto v___jp_3220_;
}
}
v___jp_3234_:
{
uint32_t v___x_3235_; uint8_t v___x_3236_; 
v___x_3235_ = 48;
v___x_3236_ = lean_uint32_dec_le(v___x_3235_, v_c_3218_);
if (v___x_3236_ == 0)
{
goto v___jp_3225_;
}
else
{
uint32_t v___x_3237_; uint8_t v___x_3238_; 
v___x_3237_ = 57;
v___x_3238_ = lean_uint32_dec_le(v_c_3218_, v___x_3237_);
if (v___x_3238_ == 0)
{
goto v___jp_3225_;
}
else
{
lean_inc(v_fst_3214_);
lean_dec_ref(v_a_3213_);
goto v___jp_3220_;
}
}
}
v___jp_3239_:
{
uint32_t v___x_3240_; uint8_t v___x_3241_; 
v___x_3240_ = 97;
v___x_3241_ = lean_uint32_dec_le(v___x_3240_, v_c_3218_);
if (v___x_3241_ == 0)
{
goto v___jp_3234_;
}
else
{
uint32_t v___x_3242_; uint8_t v___x_3243_; 
v___x_3242_ = 122;
v___x_3243_ = lean_uint32_dec_le(v_c_3218_, v___x_3242_);
if (v___x_3243_ == 0)
{
goto v___jp_3234_;
}
else
{
lean_inc(v_fst_3214_);
lean_dec_ref(v_a_3213_);
goto v___jp_3220_;
}
}
}
}
else
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = lean_box(0);
v___x_3249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3249_, 0, v_a_3213_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
return v___x_3249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(lean_object* v_n_3252_, lean_object* v_m_3253_, lean_object* v_parser_3254_, lean_object* v_a_3255_){
_start:
{
lean_object* v___x_3256_; 
v___x_3256_ = lean_apply_1(v_parser_3254_, v_a_3255_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_pos_3257_; lean_object* v_res_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3278_; 
v_pos_3257_ = lean_ctor_get(v___x_3256_, 0);
v_res_3258_ = lean_ctor_get(v___x_3256_, 1);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3260_ = v___x_3256_;
v_isShared_3261_ = v_isSharedCheck_3278_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_res_3258_);
lean_inc(v_pos_3257_);
lean_dec(v___x_3256_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3278_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
uint8_t v___x_3274_; 
v___x_3274_ = lean_nat_dec_le(v_n_3252_, v_res_3258_);
if (v___x_3274_ == 0)
{
lean_dec(v_res_3258_);
goto v___jp_3262_;
}
else
{
uint8_t v___x_3275_; 
v___x_3275_ = lean_nat_dec_le(v_res_3258_, v_m_3253_);
if (v___x_3275_ == 0)
{
lean_dec(v_res_3258_);
goto v___jp_3262_;
}
else
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
lean_del_object(v___x_3260_);
lean_dec(v_m_3253_);
lean_dec(v_n_3252_);
v___x_3276_ = lean_nat_to_int(v_res_3258_);
v___x_3277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3277_, 0, v_pos_3257_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
return v___x_3277_;
}
}
v___jp_3262_:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3272_; 
v___x_3263_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__0));
v___x_3264_ = l_Nat_reprFast(v_n_3252_);
v___x_3265_ = lean_string_append(v___x_3263_, v___x_3264_);
lean_dec_ref(v___x_3264_);
v___x_3266_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded___closed__1));
v___x_3267_ = lean_string_append(v___x_3265_, v___x_3266_);
v___x_3268_ = l_Nat_reprFast(v_m_3253_);
v___x_3269_ = lean_string_append(v___x_3267_, v___x_3268_);
lean_dec_ref(v___x_3268_);
v___x_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3269_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set_tag(v___x_3260_, 1);
lean_ctor_set(v___x_3260_, 1, v___x_3270_);
v___x_3272_ = v___x_3260_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_pos_3257_);
lean_ctor_set(v_reuseFailAlloc_3273_, 1, v___x_3270_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
else
{
lean_object* v_pos_3279_; lean_object* v_err_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_dec(v_m_3253_);
lean_dec(v_n_3252_);
v_pos_3279_ = lean_ctor_get(v___x_3256_, 0);
v_err_3280_ = lean_ctor_get(v___x_3256_, 1);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3256_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_err_3280_);
lean_inc(v_pos_3279_);
lean_dec(v___x_3256_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_pos_3279_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v_err_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(lean_object* v_a_3288_){
_start:
{
lean_object* v_fst_3292_; lean_object* v_snd_3293_; lean_object* v___x_3294_; uint8_t v_decide_3295_; 
v_fst_3292_ = lean_ctor_get(v_a_3288_, 0);
v_snd_3293_ = lean_ctor_get(v_a_3288_, 1);
v___x_3294_ = lean_string_utf8_byte_size(v_fst_3292_);
v_decide_3295_ = lean_nat_dec_eq(v_snd_3293_, v___x_3294_);
if (v_decide_3295_ == 0)
{
uint32_t v_c_3296_; uint32_t v___x_3297_; uint8_t v___x_3298_; 
v_c_3296_ = lean_string_utf8_get_fast(v_fst_3292_, v_snd_3293_);
v___x_3297_ = 48;
v___x_3298_ = lean_uint32_dec_le(v___x_3297_, v_c_3296_);
if (v___x_3298_ == 0)
{
goto v___jp_3289_;
}
else
{
uint32_t v___x_3299_; uint8_t v___x_3300_; 
v___x_3299_ = 57;
v___x_3300_ = lean_uint32_dec_le(v_c_3296_, v___x_3299_);
if (v___x_3300_ == 0)
{
goto v___jp_3289_;
}
else
{
lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3337_; 
lean_inc(v_snd_3293_);
lean_inc(v_fst_3292_);
v_isSharedCheck_3337_ = !lean_is_exclusive(v_a_3288_);
if (v_isSharedCheck_3337_ == 0)
{
lean_object* v_unused_3338_; lean_object* v_unused_3339_; 
v_unused_3338_ = lean_ctor_get(v_a_3288_, 1);
lean_dec(v_unused_3338_);
v_unused_3339_ = lean_ctor_get(v_a_3288_, 0);
lean_dec(v_unused_3339_);
v___x_3302_ = v_a_3288_;
v_isShared_3303_ = v_isSharedCheck_3337_;
goto v_resetjp_3301_;
}
else
{
lean_dec(v_a_3288_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3337_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3304_; lean_object* v_pos_3306_; lean_object* v_snd_3307_; lean_object* v_err_3308_; lean_object* v_it_x27_3316_; 
v___x_3304_ = lean_string_utf8_next_fast(v_fst_3292_, v_snd_3293_);
lean_dec(v_snd_3293_);
lean_inc(v_fst_3292_);
if (v_isShared_3303_ == 0)
{
lean_ctor_set(v___x_3302_, 1, v___x_3304_);
v_it_x27_3316_ = v___x_3302_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_fst_3292_);
lean_ctor_set(v_reuseFailAlloc_3336_, 1, v___x_3304_);
v_it_x27_3316_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3315_;
}
v___jp_3305_:
{
uint8_t v_decide_3309_; 
v_decide_3309_ = lean_nat_dec_eq(v___x_3304_, v_snd_3307_);
lean_dec(v_snd_3307_);
if (v_decide_3309_ == 0)
{
lean_object* v___x_3310_; 
lean_inc(v_err_3308_);
v___x_3310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3310_, 0, v_pos_3306_);
lean_ctor_set(v___x_3310_, 1, v_err_3308_);
return v___x_3310_;
}
else
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3311_ = lean_uint32_to_nat(v_c_3296_);
v___x_3312_ = lean_unsigned_to_nat(48u);
v___x_3313_ = lean_nat_sub(v___x_3311_, v___x_3312_);
lean_dec(v___x_3311_);
v___x_3314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3314_, 0, v_pos_3306_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
return v___x_3314_;
}
}
v_reusejp_3315_:
{
uint8_t v_decide_3321_; 
v_decide_3321_ = lean_nat_dec_eq(v___x_3304_, v___x_3294_);
if (v_decide_3321_ == 0)
{
if (v___x_3300_ == 0)
{
lean_dec(v_fst_3292_);
goto v___jp_3319_;
}
else
{
uint32_t v___x_3322_; uint8_t v___x_3323_; 
v___x_3322_ = lean_string_utf8_get_fast(v_fst_3292_, v___x_3304_);
v___x_3323_ = lean_uint32_dec_le(v___x_3297_, v___x_3322_);
if (v___x_3323_ == 0)
{
lean_dec(v_fst_3292_);
goto v___jp_3317_;
}
else
{
uint8_t v___x_3324_; 
v___x_3324_ = lean_uint32_dec_le(v___x_3322_, v___x_3299_);
if (v___x_3324_ == 0)
{
lean_dec(v_fst_3292_);
goto v___jp_3317_;
}
else
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_dec_ref(v_it_x27_3316_);
v___x_3325_ = lean_unsigned_to_nat(48u);
v___x_3326_ = lean_string_utf8_next_fast(v_fst_3292_, v___x_3304_);
v___x_3327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3327_, 0, v_fst_3292_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___x_3328_ = lean_uint32_to_nat(v_c_3296_);
v___x_3329_ = lean_nat_sub(v___x_3328_, v___x_3325_);
lean_dec(v___x_3328_);
v___x_3330_ = lean_unsigned_to_nat(10u);
v___x_3331_ = lean_nat_mul(v___x_3329_, v___x_3330_);
lean_dec(v___x_3329_);
v___x_3332_ = lean_uint32_to_nat(v___x_3322_);
v___x_3333_ = lean_nat_sub(v___x_3332_, v___x_3325_);
lean_dec(v___x_3332_);
v___x_3334_ = lean_nat_add(v___x_3331_, v___x_3333_);
lean_dec(v___x_3333_);
lean_dec(v___x_3331_);
v___x_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3327_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
return v___x_3335_;
}
}
}
}
else
{
lean_dec(v_fst_3292_);
goto v___jp_3319_;
}
v___jp_3317_:
{
lean_object* v___x_3318_; 
v___x_3318_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v_pos_3306_ = v_it_x27_3316_;
v_snd_3307_ = v___x_3304_;
v_err_3308_ = v___x_3318_;
goto v___jp_3305_;
}
v___jp_3319_:
{
lean_object* v___x_3320_; 
v___x_3320_ = lean_box(0);
v_pos_3306_ = v_it_x27_3316_;
v_snd_3307_ = v___x_3304_;
v_err_3308_ = v___x_3320_;
goto v___jp_3305_;
}
}
}
}
}
}
else
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = lean_box(0);
v___x_3341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3341_, 0, v_a_3288_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
return v___x_3341_;
}
v___jp_3289_:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3290_ = ((lean_object*)(l_Std_Internal_Parsec_manyCharsCore___at___00Std_Internal_Parsec_manyCharsCore___at___00__private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart_spec__0_spec__0___closed__1));
v___x_3291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3291_, 0, v_a_3288_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
return v___x_3291_;
}
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1(void){
_start:
{
uint32_t v___x_3345_; lean_object* v___x_3346_; 
v___x_3345_ = 58;
v___x_3346_ = lean_box_uint32(v___x_3345_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(uint8_t v_withColon_3347_, lean_object* v___y_3348_){
_start:
{
if (v_withColon_3347_ == 0)
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1;
v___x_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___y_3348_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
return v___x_3350_;
}
else
{
lean_object* v_fst_3351_; lean_object* v_snd_3352_; lean_object* v___x_3353_; uint8_t v_decide_3354_; 
v_fst_3351_ = lean_ctor_get(v___y_3348_, 0);
v_snd_3352_ = lean_ctor_get(v___y_3348_, 1);
v___x_3353_ = lean_string_utf8_byte_size(v_fst_3351_);
v_decide_3354_ = lean_nat_dec_eq(v_snd_3352_, v___x_3353_);
if (v_decide_3354_ == 0)
{
uint32_t v___x_3355_; uint32_t v_c_3356_; uint8_t v___x_3357_; 
v___x_3355_ = 58;
v_c_3356_ = lean_string_utf8_get_fast(v_fst_3351_, v_snd_3352_);
v___x_3357_ = lean_uint32_dec_eq(v_c_3356_, v___x_3355_);
if (v___x_3357_ == 0)
{
lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3358_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___closed__1));
v___x_3359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___y_3348_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
return v___x_3359_;
}
else
{
lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3369_; 
lean_inc(v_snd_3352_);
lean_inc(v_fst_3351_);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___y_3348_);
if (v_isSharedCheck_3369_ == 0)
{
lean_object* v_unused_3370_; lean_object* v_unused_3371_; 
v_unused_3370_ = lean_ctor_get(v___y_3348_, 1);
lean_dec(v_unused_3370_);
v_unused_3371_ = lean_ctor_get(v___y_3348_, 0);
lean_dec(v_unused_3371_);
v___x_3361_ = v___y_3348_;
v_isShared_3362_ = v_isSharedCheck_3369_;
goto v_resetjp_3360_;
}
else
{
lean_dec(v___y_3348_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3369_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3363_; lean_object* v_it_x27_3365_; 
v___x_3363_ = lean_string_utf8_next_fast(v_fst_3351_, v_snd_3352_);
lean_dec(v_snd_3352_);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 1, v___x_3363_);
v_it_x27_3365_ = v___x_3361_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_fst_3351_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v___x_3363_);
v_it_x27_3365_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed__const__1;
v___x_3367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3367_, 0, v_it_x27_3365_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
return v___x_3367_;
}
}
}
}
else
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3372_ = lean_box(0);
v___x_3373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___y_3348_);
lean_ctor_set(v___x_3373_, 1, v___x_3372_);
return v___x_3373_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed(lean_object* v_withColon_3374_, lean_object* v___y_3375_){
_start:
{
uint8_t v_withColon_boxed_3376_; lean_object* v_res_3377_; 
v_withColon_boxed_3376_ = lean_unbox(v_withColon_3374_);
v_res_3377_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0(v_withColon_boxed_3376_, v___y_3375_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__1(lean_object* v_a_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3380_ = lean_nat_to_int(v_a_3378_);
v___x_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___y_3379_);
lean_ctor_set(v___x_3381_, 1, v___x_3380_);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(lean_object* v___y_3382_, lean_object* v___f_3383_, lean_object* v_n_3384_, uint8_t v_reason_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_pos_3388_; lean_object* v_err_3389_; 
switch(v_reason_3385_)
{
case 0:
{
lean_object* v___x_3405_; 
v___x_3405_ = lean_apply_1(v___y_3382_, v___y_3386_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_pos_3406_; lean_object* v___x_3407_; 
v_pos_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_pos_3406_);
lean_dec_ref_known(v___x_3405_, 2);
v___x_3407_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3406_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_pos_3408_; lean_object* v_res_3409_; lean_object* v___x_3410_; 
v_pos_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_pos_3408_);
v_res_3409_ = lean_ctor_get(v___x_3407_, 1);
lean_inc(v_res_3409_);
lean_dec_ref_known(v___x_3407_, 2);
v___x_3410_ = lean_apply_2(v___f_3383_, v_res_3409_, v_pos_3408_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_pos_3411_; lean_object* v_res_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3420_; 
v_pos_3411_ = lean_ctor_get(v___x_3410_, 0);
v_res_3412_ = lean_ctor_get(v___x_3410_, 1);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3414_ = v___x_3410_;
v_isShared_3415_ = v_isSharedCheck_3420_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_res_3412_);
lean_inc(v_pos_3411_);
lean_dec(v___x_3410_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3420_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3416_; lean_object* v___x_3418_; 
v___x_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3416_, 0, v_res_3412_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 1, v___x_3416_);
v___x_3418_ = v___x_3414_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_pos_3411_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v___x_3416_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
else
{
lean_object* v_pos_3421_; lean_object* v_err_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
v_pos_3421_ = lean_ctor_get(v___x_3410_, 0);
v_err_3422_ = lean_ctor_get(v___x_3410_, 1);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3410_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_err_3422_);
lean_inc(v_pos_3421_);
lean_dec(v___x_3410_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_pos_3421_);
lean_ctor_set(v_reuseFailAlloc_3428_, 1, v_err_3422_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
else
{
lean_object* v_pos_3430_; lean_object* v_err_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
lean_dec_ref(v___f_3383_);
v_pos_3430_ = lean_ctor_get(v___x_3407_, 0);
v_err_3431_ = lean_ctor_get(v___x_3407_, 1);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3433_ = v___x_3407_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_err_3431_);
lean_inc(v_pos_3430_);
lean_dec(v___x_3407_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_pos_3430_);
lean_ctor_set(v_reuseFailAlloc_3437_, 1, v_err_3431_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
else
{
lean_object* v_pos_3439_; lean_object* v_err_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec_ref(v___f_3383_);
v_pos_3439_ = lean_ctor_get(v___x_3405_, 0);
v_err_3440_ = lean_ctor_get(v___x_3405_, 1);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3405_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_err_3440_);
lean_inc(v_pos_3439_);
lean_dec(v___x_3405_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_pos_3439_);
lean_ctor_set(v_reuseFailAlloc_3446_, 1, v_err_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
case 1:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; 
lean_dec_ref(v___f_3383_);
lean_dec_ref(v___y_3382_);
v___x_3448_ = lean_box(0);
v___x_3449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___y_3386_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
return v___x_3449_;
}
default: 
{
lean_object* v___x_3450_; 
lean_inc_ref(v___y_3386_);
v___x_3450_ = lean_apply_1(v___y_3382_, v___y_3386_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_pos_3451_; lean_object* v___x_3452_; 
v_pos_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_pos_3451_);
lean_dec_ref_known(v___x_3450_, 2);
v___x_3452_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3451_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_pos_3453_; lean_object* v_res_3454_; lean_object* v___x_3455_; 
v_pos_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_pos_3453_);
v_res_3454_ = lean_ctor_get(v___x_3452_, 1);
lean_inc(v_res_3454_);
lean_dec_ref_known(v___x_3452_, 2);
v___x_3455_ = lean_apply_2(v___f_3383_, v_res_3454_, v_pos_3453_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_pos_3456_; lean_object* v_res_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3465_; 
lean_dec_ref(v___y_3386_);
v_pos_3456_ = lean_ctor_get(v___x_3455_, 0);
v_res_3457_ = lean_ctor_get(v___x_3455_, 1);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3459_ = v___x_3455_;
v_isShared_3460_ = v_isSharedCheck_3465_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_res_3457_);
lean_inc(v_pos_3456_);
lean_dec(v___x_3455_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3465_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3461_; lean_object* v___x_3463_; 
v___x_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3461_, 0, v_res_3457_);
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 1, v___x_3461_);
v___x_3463_ = v___x_3459_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_pos_3456_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v___x_3461_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
else
{
lean_object* v_pos_3466_; lean_object* v_err_3467_; 
v_pos_3466_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_pos_3466_);
v_err_3467_ = lean_ctor_get(v___x_3455_, 1);
lean_inc(v_err_3467_);
lean_dec_ref_known(v___x_3455_, 2);
v_pos_3388_ = v_pos_3466_;
v_err_3389_ = v_err_3467_;
goto v___jp_3387_;
}
}
else
{
lean_object* v_pos_3468_; lean_object* v_err_3469_; 
lean_dec_ref(v___f_3383_);
v_pos_3468_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_pos_3468_);
v_err_3469_ = lean_ctor_get(v___x_3452_, 1);
lean_inc(v_err_3469_);
lean_dec_ref_known(v___x_3452_, 2);
v_pos_3388_ = v_pos_3468_;
v_err_3389_ = v_err_3469_;
goto v___jp_3387_;
}
}
else
{
lean_object* v_pos_3470_; lean_object* v_err_3471_; 
lean_dec_ref(v___f_3383_);
v_pos_3470_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_pos_3470_);
v_err_3471_ = lean_ctor_get(v___x_3450_, 1);
lean_inc(v_err_3471_);
lean_dec_ref_known(v___x_3450_, 2);
v_pos_3388_ = v_pos_3470_;
v_err_3389_ = v_err_3471_;
goto v___jp_3387_;
}
}
}
v___jp_3387_:
{
lean_object* v_snd_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3403_; 
v_snd_3390_ = lean_ctor_get(v___y_3386_, 1);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___y_3386_);
if (v_isSharedCheck_3403_ == 0)
{
lean_object* v_unused_3404_; 
v_unused_3404_ = lean_ctor_get(v___y_3386_, 0);
lean_dec(v_unused_3404_);
v___x_3392_ = v___y_3386_;
v_isShared_3393_ = v_isSharedCheck_3403_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_snd_3390_);
lean_dec(v___y_3386_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3403_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v_snd_3394_; uint8_t v_decide_3395_; 
v_snd_3394_ = lean_ctor_get(v_pos_3388_, 1);
v_decide_3395_ = lean_nat_dec_eq(v_snd_3390_, v_snd_3394_);
lean_dec(v_snd_3390_);
if (v_decide_3395_ == 0)
{
lean_object* v___x_3397_; 
if (v_isShared_3393_ == 0)
{
lean_ctor_set_tag(v___x_3392_, 1);
lean_ctor_set(v___x_3392_, 1, v_err_3389_);
lean_ctor_set(v___x_3392_, 0, v_pos_3388_);
v___x_3397_ = v___x_3392_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_pos_3388_);
lean_ctor_set(v_reuseFailAlloc_3398_, 1, v_err_3389_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
else
{
lean_object* v___x_3399_; lean_object* v___x_3401_; 
lean_dec(v_err_3389_);
v___x_3399_ = lean_box(0);
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 1, v___x_3399_);
lean_ctor_set(v___x_3392_, 0, v_pos_3388_);
v___x_3401_ = v___x_3392_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_pos_3388_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v___x_3399_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2___boxed(lean_object* v___y_3472_, lean_object* v___f_3473_, lean_object* v_n_3474_, lean_object* v_reason_3475_, lean_object* v___y_3476_){
_start:
{
uint8_t v_reason_boxed_3477_; lean_object* v_res_3478_; 
v_reason_boxed_3477_ = lean_unbox(v_reason_3475_);
v_res_3478_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3472_, v___f_3473_, v_n_3474_, v_reason_boxed_3477_, v___y_3476_);
lean_dec_ref(v_n_3474_);
return v_res_3478_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2(void){
_start:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3481_ = lean_unsigned_to_nat(3600u);
v___x_3482_ = lean_nat_to_int(v___x_3481_);
return v___x_3482_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4(void){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = lean_unsigned_to_nat(1u);
v___x_3485_ = l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(v___x_3484_);
return v___x_3485_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5(void){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = lean_unsigned_to_nat(59u);
v___x_3487_ = lean_nat_to_int(v___x_3486_);
return v___x_3487_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8(void){
_start:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3490_ = lean_unsigned_to_nat(23u);
v___x_3491_ = lean_nat_to_int(v___x_3490_);
return v___x_3491_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9(void){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = lean_unsigned_to_nat(60u);
v___x_3493_ = l_Nat_cast___at___00__private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(v___x_3492_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(uint8_t v_withMinutes_3501_, uint8_t v_withSeconds_3502_, uint8_t v_withColon_3503_, lean_object* v_a_3504_){
_start:
{
lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3547_; lean_object* v_fst_3550_; lean_object* v_snd_3551_; lean_object* v___x_3552_; lean_object* v___y_3553_; lean_object* v___f_3554_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v_pos_3601_; lean_object* v_res_3602_; lean_object* v_pos_3660_; lean_object* v_fst_3661_; lean_object* v_snd_3662_; lean_object* v_err_3663_; lean_object* v___x_3676_; uint8_t v_decide_3677_; 
v_fst_3550_ = lean_ctor_get(v_a_3504_, 0);
lean_inc(v_fst_3550_);
v_snd_3551_ = lean_ctor_get(v_a_3504_, 1);
lean_inc(v_snd_3551_);
v___x_3552_ = lean_box(v_withColon_3503_);
v___y_3553_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__0___boxed), 2, 1);
lean_closure_set(v___y_3553_, 0, v___x_3552_);
v___f_3554_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__3));
v___x_3676_ = lean_string_utf8_byte_size(v_fst_3550_);
v_decide_3677_ = lean_nat_dec_eq(v_snd_3551_, v___x_3676_);
if (v_decide_3677_ == 0)
{
uint32_t v___x_3678_; uint32_t v_c_3679_; uint8_t v___x_3680_; 
v___x_3678_ = 43;
v_c_3679_ = lean_string_utf8_get_fast(v_fst_3550_, v_snd_3551_);
v___x_3680_ = lean_uint32_dec_eq(v_c_3679_, v___x_3678_);
if (v___x_3680_ == 0)
{
lean_object* v___x_3681_; 
v___x_3681_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__14));
lean_inc(v_snd_3551_);
v_pos_3660_ = v_a_3504_;
v_fst_3661_ = v_fst_3550_;
v_snd_3662_ = v_snd_3551_;
v_err_3663_ = v___x_3681_;
goto v___jp_3659_;
}
else
{
lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3690_; 
v_isSharedCheck_3690_ = !lean_is_exclusive(v_a_3504_);
if (v_isSharedCheck_3690_ == 0)
{
lean_object* v_unused_3691_; lean_object* v_unused_3692_; 
v_unused_3691_ = lean_ctor_get(v_a_3504_, 1);
lean_dec(v_unused_3691_);
v_unused_3692_ = lean_ctor_get(v_a_3504_, 0);
lean_dec(v_unused_3692_);
v___x_3683_ = v_a_3504_;
v_isShared_3684_ = v_isSharedCheck_3690_;
goto v_resetjp_3682_;
}
else
{
lean_dec(v_a_3504_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3690_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3685_; lean_object* v_it_x27_3687_; 
v___x_3685_ = lean_string_utf8_next_fast(v_fst_3550_, v_snd_3551_);
lean_dec(v_snd_3551_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 1, v___x_3685_);
v_it_x27_3687_ = v___x_3683_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_fst_3550_);
lean_ctor_set(v_reuseFailAlloc_3689_, 1, v___x_3685_);
v_it_x27_3687_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
lean_object* v___x_3688_; 
v___x_3688_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v_pos_3601_ = v_it_x27_3687_;
v_res_3602_ = v___x_3688_;
goto v___jp_3600_;
}
}
}
}
else
{
lean_object* v___x_3693_; 
v___x_3693_ = lean_box(0);
lean_inc(v_snd_3551_);
v_pos_3660_ = v_a_3504_;
v_fst_3661_ = v_fst_3550_;
v_snd_3662_ = v_snd_3551_;
v_err_3663_ = v___x_3693_;
goto v___jp_3659_;
}
v___jp_3505_:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3508_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__0));
v___x_3509_ = l_Int_repr(v___y_3507_);
lean_dec(v___y_3507_);
v___x_3510_ = lean_string_append(v___x_3508_, v___x_3509_);
lean_dec_ref(v___x_3509_);
v___x_3511_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__1));
v___x_3512_ = lean_string_append(v___x_3510_, v___x_3511_);
v___x_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3512_);
v___x_3514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3514_, 0, v___y_3506_);
lean_ctor_set(v___x_3514_, 1, v___x_3513_);
return v___x_3514_;
}
v___jp_3515_:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3520_ = lean_int_add(v___y_3518_, v___y_3519_);
lean_dec(v___y_3519_);
lean_dec(v___y_3518_);
v___x_3521_ = lean_int_mul(v___x_3520_, v___y_3517_);
lean_dec(v___x_3520_);
v___x_3522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___y_3516_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
return v___x_3522_;
}
v___jp_3523_:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3531_ = lean_nat_to_int(v___y_3528_);
v___x_3532_ = lean_int_mul(v___y_3530_, v___x_3531_);
lean_dec(v___x_3531_);
lean_dec(v___y_3530_);
v___x_3533_ = lean_int_add(v___y_3529_, v___x_3532_);
lean_dec(v___x_3532_);
lean_dec(v___y_3529_);
if (lean_obj_tag(v___y_3527_) == 0)
{
lean_inc(v___y_3524_);
v___y_3516_ = v___y_3525_;
v___y_3517_ = v___y_3526_;
v___y_3518_ = v___x_3533_;
v___y_3519_ = v___y_3524_;
goto v___jp_3515_;
}
else
{
lean_object* v_val_3534_; 
v_val_3534_ = lean_ctor_get(v___y_3527_, 0);
lean_inc(v_val_3534_);
lean_dec_ref_known(v___y_3527_, 1);
v___y_3516_ = v___y_3525_;
v___y_3517_ = v___y_3526_;
v___y_3518_ = v___x_3533_;
v___y_3519_ = v_val_3534_;
goto v___jp_3515_;
}
}
v___jp_3535_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__2);
v___x_3544_ = lean_int_mul(v___y_3541_, v___x_3543_);
lean_dec(v___y_3541_);
if (lean_obj_tag(v___y_3537_) == 0)
{
lean_inc(v___y_3536_);
v___y_3524_ = v___y_3536_;
v___y_3525_ = v___y_3542_;
v___y_3526_ = v___y_3538_;
v___y_3527_ = v___y_3539_;
v___y_3528_ = v___y_3540_;
v___y_3529_ = v___x_3544_;
v___y_3530_ = v___y_3536_;
goto v___jp_3523_;
}
else
{
lean_object* v_val_3545_; 
v_val_3545_ = lean_ctor_get(v___y_3537_, 0);
lean_inc(v_val_3545_);
lean_dec_ref_known(v___y_3537_, 1);
v___y_3524_ = v___y_3536_;
v___y_3525_ = v___y_3542_;
v___y_3526_ = v___y_3538_;
v___y_3527_ = v___y_3539_;
v___y_3528_ = v___y_3540_;
v___y_3529_ = v___x_3544_;
v___y_3530_ = v_val_3545_;
goto v___jp_3523_;
}
}
v___jp_3546_:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3548_ = lean_box(0);
v___x_3549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___y_3547_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
return v___x_3549_;
}
v___jp_3555_:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3562_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__4);
v___x_3563_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3553_, v___f_3554_, v___x_3562_, v_withSeconds_3502_, v___y_3561_);
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
v___y_3536_ = v___y_3556_;
v___y_3537_ = v___y_3557_;
v___y_3538_ = v___y_3558_;
v___y_3539_ = v_res_3564_;
v___y_3540_ = v___y_3560_;
v___y_3541_ = v___y_3559_;
v___y_3542_ = v_pos_3565_;
goto v___jp_3535_;
}
else
{
lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3586_; 
lean_inc(v_val_3569_);
lean_dec(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec(v___y_3557_);
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
v___x_3575_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__6));
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
v___y_3536_ = v___y_3556_;
v___y_3537_ = v___y_3557_;
v___y_3538_ = v___y_3558_;
v___y_3539_ = v_res_3564_;
v___y_3540_ = v___y_3560_;
v___y_3541_ = v___y_3559_;
v___y_3542_ = v_pos_3590_;
goto v___jp_3535_;
}
}
else
{
lean_object* v_pos_3591_; lean_object* v_err_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
lean_dec(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec(v___y_3557_);
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
v___jp_3600_:
{
lean_object* v___x_3603_; 
v___x_3603_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOneOrTwoNum(v_pos_3601_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_pos_3604_; lean_object* v_res_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; uint8_t v___x_3608_; 
v_pos_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_pos_3604_);
v_res_3605_ = lean_ctor_get(v___x_3603_, 1);
lean_inc(v_res_3605_);
lean_dec_ref_known(v___x_3603_, 2);
v___x_3606_ = lean_nat_to_int(v_res_3605_);
v___x_3607_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_3608_ = lean_int_dec_lt(v___x_3606_, v___x_3607_);
if (v___x_3608_ == 0)
{
lean_object* v___x_3609_; uint8_t v___x_3610_; 
v___x_3609_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__8);
v___x_3610_ = lean_int_dec_lt(v___x_3609_, v___x_3606_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3611_ = lean_unsigned_to_nat(60u);
v___x_3612_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__9);
lean_inc_ref(v___y_3553_);
v___x_3613_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___lam__2(v___y_3553_, v___f_3554_, v___x_3612_, v_withMinutes_3501_, v_pos_3604_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_res_3614_; 
v_res_3614_ = lean_ctor_get(v___x_3613_, 1);
lean_inc(v_res_3614_);
if (lean_obj_tag(v_res_3614_) == 1)
{
lean_object* v_pos_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3638_; 
v_pos_3615_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3638_ == 0)
{
lean_object* v_unused_3639_; 
v_unused_3639_ = lean_ctor_get(v___x_3613_, 1);
lean_dec(v_unused_3639_);
v___x_3617_ = v___x_3613_;
v_isShared_3618_ = v_isSharedCheck_3638_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_pos_3615_);
lean_dec(v___x_3613_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3638_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v_val_3619_; lean_object* v___x_3620_; uint8_t v___x_3621_; 
v_val_3619_ = lean_ctor_get(v_res_3614_, 0);
v___x_3620_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5);
v___x_3621_ = lean_int_dec_lt(v___x_3620_, v_val_3619_);
if (v___x_3621_ == 0)
{
lean_del_object(v___x_3617_);
v___y_3556_ = v___x_3607_;
v___y_3557_ = v_res_3614_;
v___y_3558_ = v_res_3602_;
v___y_3559_ = v___x_3606_;
v___y_3560_ = v___x_3611_;
v___y_3561_ = v_pos_3615_;
goto v___jp_3555_;
}
else
{
lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3636_; 
lean_inc(v_val_3619_);
lean_dec(v___x_3606_);
lean_dec_ref(v___y_3553_);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_res_3614_);
if (v_isSharedCheck_3636_ == 0)
{
lean_object* v_unused_3637_; 
v_unused_3637_ = lean_ctor_get(v_res_3614_, 0);
lean_dec(v_unused_3637_);
v___x_3623_ = v_res_3614_;
v_isShared_3624_ = v_isSharedCheck_3636_;
goto v_resetjp_3622_;
}
else
{
lean_dec(v_res_3614_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3636_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3631_; 
v___x_3625_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__10));
v___x_3626_ = l_Int_repr(v_val_3619_);
lean_dec(v_val_3619_);
v___x_3627_ = lean_string_append(v___x_3625_, v___x_3626_);
lean_dec_ref(v___x_3626_);
v___x_3628_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__7));
v___x_3629_ = lean_string_append(v___x_3627_, v___x_3628_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 0, v___x_3629_);
v___x_3631_ = v___x_3623_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3629_);
v___x_3631_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
lean_object* v___x_3633_; 
if (v_isShared_3618_ == 0)
{
lean_ctor_set_tag(v___x_3617_, 1);
lean_ctor_set(v___x_3617_, 1, v___x_3631_);
v___x_3633_ = v___x_3617_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_pos_3615_);
lean_ctor_set(v_reuseFailAlloc_3634_, 1, v___x_3631_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
}
}
else
{
lean_object* v_pos_3640_; 
v_pos_3640_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_pos_3640_);
lean_dec_ref_known(v___x_3613_, 2);
v___y_3556_ = v___x_3607_;
v___y_3557_ = v_res_3614_;
v___y_3558_ = v_res_3602_;
v___y_3559_ = v___x_3606_;
v___y_3560_ = v___x_3611_;
v___y_3561_ = v_pos_3640_;
goto v___jp_3555_;
}
}
else
{
lean_object* v_pos_3641_; lean_object* v_err_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
lean_dec(v___x_3606_);
lean_dec_ref(v___y_3553_);
v_pos_3641_ = lean_ctor_get(v___x_3613_, 0);
v_err_3642_ = lean_ctor_get(v___x_3613_, 1);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3613_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_err_3642_);
lean_inc(v_pos_3641_);
lean_dec(v___x_3613_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_pos_3641_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_err_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
else
{
lean_dec_ref(v___y_3553_);
v___y_3506_ = v_pos_3604_;
v___y_3507_ = v___x_3606_;
goto v___jp_3505_;
}
}
else
{
lean_dec_ref(v___y_3553_);
v___y_3506_ = v_pos_3604_;
v___y_3507_ = v___x_3606_;
goto v___jp_3505_;
}
}
else
{
lean_object* v_pos_3650_; lean_object* v_err_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3658_; 
lean_dec_ref(v___y_3553_);
v_pos_3650_ = lean_ctor_get(v___x_3603_, 0);
v_err_3651_ = lean_ctor_get(v___x_3603_, 1);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3653_ = v___x_3603_;
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_err_3651_);
lean_inc(v_pos_3650_);
lean_dec(v___x_3603_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3656_; 
if (v_isShared_3654_ == 0)
{
v___x_3656_ = v___x_3653_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_pos_3650_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v_err_3651_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
}
v___jp_3659_:
{
uint8_t v_decide_3664_; 
v_decide_3664_ = lean_nat_dec_eq(v_snd_3551_, v_snd_3662_);
lean_dec(v_snd_3551_);
if (v_decide_3664_ == 0)
{
lean_object* v___x_3665_; 
lean_dec(v_snd_3662_);
lean_dec(v_fst_3661_);
lean_dec_ref(v___y_3553_);
lean_inc(v_err_3663_);
v___x_3665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3665_, 0, v_pos_3660_);
lean_ctor_set(v___x_3665_, 1, v_err_3663_);
return v___x_3665_;
}
else
{
lean_object* v___x_3666_; uint8_t v_decide_3667_; 
v___x_3666_ = lean_string_utf8_byte_size(v_fst_3661_);
v_decide_3667_ = lean_nat_dec_eq(v_snd_3662_, v___x_3666_);
if (v_decide_3667_ == 0)
{
if (v_decide_3664_ == 0)
{
lean_dec(v_snd_3662_);
lean_dec(v_fst_3661_);
lean_dec_ref(v___y_3553_);
v___y_3547_ = v_pos_3660_;
goto v___jp_3546_;
}
else
{
uint32_t v___x_3668_; uint32_t v_c_3669_; uint8_t v___x_3670_; 
v___x_3668_ = 45;
v_c_3669_ = lean_string_utf8_get_fast(v_fst_3661_, v_snd_3662_);
v___x_3670_ = lean_uint32_dec_eq(v_c_3669_, v___x_3668_);
if (v___x_3670_ == 0)
{
lean_object* v___x_3671_; lean_object* v___x_3672_; 
lean_dec(v_snd_3662_);
lean_dec(v_fst_3661_);
lean_dec_ref(v___y_3553_);
v___x_3671_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__12));
v___x_3672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3672_, 0, v_pos_3660_);
lean_ctor_set(v___x_3672_, 1, v___x_3671_);
return v___x_3672_;
}
else
{
lean_object* v___x_3673_; lean_object* v_it_x27_3674_; lean_object* v___x_3675_; 
lean_dec_ref(v_pos_3660_);
v___x_3673_ = lean_string_utf8_next_fast(v_fst_3661_, v_snd_3662_);
lean_dec(v_snd_3662_);
v_it_x27_3674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_3674_, 0, v_fst_3661_);
lean_ctor_set(v_it_x27_3674_, 1, v___x_3673_);
v___x_3675_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v_pos_3601_ = v_it_x27_3674_;
v_res_3602_ = v___x_3675_;
goto v___jp_3600_;
}
}
}
else
{
lean_dec(v_snd_3662_);
lean_dec(v_fst_3661_);
lean_dec_ref(v___y_3553_);
v___y_3547_ = v_pos_3660_;
goto v___jp_3546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___boxed(lean_object* v_withMinutes_3694_, lean_object* v_withSeconds_3695_, lean_object* v_withColon_3696_, lean_object* v_a_3697_){
_start:
{
uint8_t v_withMinutes_boxed_3698_; uint8_t v_withSeconds_boxed_3699_; uint8_t v_withColon_boxed_3700_; lean_object* v_res_3701_; 
v_withMinutes_boxed_3698_ = lean_unbox(v_withMinutes_3694_);
v_withSeconds_boxed_3699_ = lean_unbox(v_withSeconds_3695_);
v_withColon_boxed_3700_ = lean_unbox(v_withColon_3696_);
v_res_3701_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v_withMinutes_boxed_3698_, v_withSeconds_boxed_3699_, v_withColon_boxed_3700_, v_a_3697_);
return v_res_3701_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1(void){
_start:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3704_ = lean_unsigned_to_nat(2000u);
v___x_3705_ = lean_nat_to_int(v___x_3704_);
return v___x_3705_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5(void){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3711_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3712_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_3713_ = lean_int_sub(v___x_3712_, v___x_3711_);
return v___x_3713_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6(void){
_start:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v_range_3716_; 
v___x_3714_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_3715_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__5);
v_range_3716_ = lean_int_add(v___x_3715_, v___x_3714_);
return v_range_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(lean_object* v_config_3719_, lean_object* v_x_3720_, lean_object* v_a_3721_){
_start:
{
lean_object* v___y_3723_; lean_object* v___y_3728_; lean_object* v___y_3733_; 
switch(lean_obj_tag(v_x_3720_))
{
case 0:
{
uint8_t v_presentation_3759_; 
v_presentation_3759_ = lean_ctor_get_uint8(v_x_3720_, 0);
lean_dec_ref_known(v_x_3720_, 0);
switch(v_presentation_3759_)
{
case 1:
{
lean_object* v_dateformat_3760_; lean_object* v_symbols_3761_; lean_object* v___x_3762_; 
v_dateformat_3760_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_3760_);
lean_dec_ref(v_config_3719_);
v_symbols_3761_ = lean_ctor_get(v_dateformat_3760_, 1);
lean_inc_ref(v_symbols_3761_);
lean_dec_ref(v_dateformat_3760_);
v___x_3762_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraLong(v_symbols_3761_, v_a_3721_);
return v___x_3762_;
}
case 2:
{
lean_object* v_dateformat_3763_; lean_object* v_symbols_3764_; lean_object* v___x_3765_; 
v_dateformat_3763_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_3763_);
lean_dec_ref(v_config_3719_);
v_symbols_3764_ = lean_ctor_get(v_dateformat_3763_, 1);
lean_inc_ref(v_symbols_3764_);
lean_dec_ref(v_dateformat_3763_);
v___x_3765_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraNarrow(v_symbols_3764_, v_a_3721_);
return v___x_3765_;
}
default: 
{
lean_object* v_dateformat_3766_; lean_object* v_symbols_3767_; lean_object* v___x_3768_; 
v_dateformat_3766_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_3766_);
lean_dec_ref(v_config_3719_);
v_symbols_3767_ = lean_ctor_get(v_dateformat_3766_, 1);
lean_inc_ref(v_symbols_3767_);
lean_dec_ref(v_dateformat_3766_);
v___x_3768_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseEraShort(v_symbols_3767_, v_a_3721_);
return v___x_3768_;
}
}
}
case 1:
{
lean_object* v_presentation_3769_; 
lean_dec_ref(v_config_3719_);
v_presentation_3769_ = lean_ctor_get(v_x_3720_, 0);
lean_inc(v_presentation_3769_);
lean_dec_ref_known(v_x_3720_, 1);
switch(lean_obj_tag(v_presentation_3769_))
{
case 0:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3770_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0));
v___x_3771_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3770_, v_a_3721_);
return v___x_3771_;
}
case 1:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3772_ = lean_unsigned_to_nat(2u);
v___x_3773_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3772_, v_a_3721_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v_pos_3774_; lean_object* v_res_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3785_; 
v_pos_3774_ = lean_ctor_get(v___x_3773_, 0);
v_res_3775_ = lean_ctor_get(v___x_3773_, 1);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3777_ = v___x_3773_;
v_isShared_3778_ = v_isSharedCheck_3785_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_res_3775_);
lean_inc(v_pos_3774_);
lean_dec(v___x_3773_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3785_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3783_; 
v___x_3779_ = lean_nat_to_int(v_res_3775_);
v___x_3780_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_3781_ = lean_int_add(v___x_3780_, v___x_3779_);
lean_dec(v___x_3779_);
if (v_isShared_3778_ == 0)
{
lean_ctor_set(v___x_3777_, 1, v___x_3781_);
v___x_3783_ = v___x_3777_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_pos_3774_);
lean_ctor_set(v_reuseFailAlloc_3784_, 1, v___x_3781_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
else
{
lean_object* v_pos_3786_; lean_object* v_err_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
v_pos_3786_ = lean_ctor_get(v___x_3773_, 0);
v_err_3787_ = lean_ctor_get(v___x_3773_, 1);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3773_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_err_3787_);
lean_inc(v_pos_3786_);
lean_dec(v___x_3773_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_pos_3786_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_err_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
case 2:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3795_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2));
v___x_3796_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3795_, v_a_3721_);
return v___x_3796_;
}
default: 
{
lean_object* v_num_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v_num_3797_ = lean_ctor_get(v_presentation_3769_, 0);
lean_inc(v_num_3797_);
lean_dec_ref_known(v_presentation_3769_, 1);
v___x_3798_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed), 2, 1);
lean_closure_set(v___x_3798_, 0, v_num_3797_);
v___x_3799_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3798_, v_a_3721_);
return v___x_3799_;
}
}
}
case 2:
{
lean_object* v_presentation_3800_; 
lean_dec_ref(v_config_3719_);
v_presentation_3800_ = lean_ctor_get(v_x_3720_, 0);
lean_inc(v_presentation_3800_);
lean_dec_ref_known(v_x_3720_, 1);
switch(lean_obj_tag(v_presentation_3800_))
{
case 0:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = lean_unsigned_to_nat(1u);
v___x_3802_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseAtLeastNum(v___x_3801_, v_a_3721_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_pos_3803_; lean_object* v_res_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3812_; 
v_pos_3803_ = lean_ctor_get(v___x_3802_, 0);
v_res_3804_ = lean_ctor_get(v___x_3802_, 1);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3806_ = v___x_3802_;
v_isShared_3807_ = v_isSharedCheck_3812_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_res_3804_);
lean_inc(v_pos_3803_);
lean_dec(v___x_3802_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3812_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3808_; lean_object* v___x_3810_; 
v___x_3808_ = lean_nat_to_int(v_res_3804_);
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 1, v___x_3808_);
v___x_3810_ = v___x_3806_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_pos_3803_);
lean_ctor_set(v_reuseFailAlloc_3811_, 1, v___x_3808_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
else
{
lean_object* v_pos_3813_; lean_object* v_err_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
v_pos_3813_ = lean_ctor_get(v___x_3802_, 0);
v_err_3814_ = lean_ctor_get(v___x_3802_, 1);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3802_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_err_3814_);
lean_inc(v_pos_3813_);
lean_dec(v___x_3802_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_pos_3813_);
lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_err_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
case 1:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3822_ = lean_unsigned_to_nat(2u);
v___x_3823_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3822_, v_a_3721_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v_pos_3824_; lean_object* v_res_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3835_; 
v_pos_3824_ = lean_ctor_get(v___x_3823_, 0);
v_res_3825_ = lean_ctor_get(v___x_3823_, 1);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3827_ = v___x_3823_;
v_isShared_3828_ = v_isSharedCheck_3835_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_res_3825_);
lean_inc(v_pos_3824_);
lean_dec(v___x_3823_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3835_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3833_; 
v___x_3829_ = lean_nat_to_int(v_res_3825_);
v___x_3830_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_3831_ = lean_int_add(v___x_3830_, v___x_3829_);
lean_dec(v___x_3829_);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 1, v___x_3831_);
v___x_3833_ = v___x_3827_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_pos_3824_);
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
v_pos_3836_ = lean_ctor_get(v___x_3823_, 0);
v_err_3837_ = lean_ctor_get(v___x_3823_, 1);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3823_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_err_3837_);
lean_inc(v_pos_3836_);
lean_dec(v___x_3823_);
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
case 2:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3845_ = lean_unsigned_to_nat(4u);
v___x_3846_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3845_, v_a_3721_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_pos_3847_; lean_object* v_res_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3856_; 
v_pos_3847_ = lean_ctor_get(v___x_3846_, 0);
v_res_3848_ = lean_ctor_get(v___x_3846_, 1);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3850_ = v___x_3846_;
v_isShared_3851_ = v_isSharedCheck_3856_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_res_3848_);
lean_inc(v_pos_3847_);
lean_dec(v___x_3846_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3856_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3852_; lean_object* v___x_3854_; 
v___x_3852_ = lean_nat_to_int(v_res_3848_);
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 1, v___x_3852_);
v___x_3854_ = v___x_3850_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_pos_3847_);
lean_ctor_set(v_reuseFailAlloc_3855_, 1, v___x_3852_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
else
{
lean_object* v_pos_3857_; lean_object* v_err_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
v_pos_3857_ = lean_ctor_get(v___x_3846_, 0);
v_err_3858_ = lean_ctor_get(v___x_3846_, 1);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v___x_3846_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_err_3858_);
lean_inc(v_pos_3857_);
lean_dec(v___x_3846_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_pos_3857_);
lean_ctor_set(v_reuseFailAlloc_3864_, 1, v_err_3858_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
default: 
{
lean_object* v_num_3866_; lean_object* v___x_3867_; 
v_num_3866_ = lean_ctor_get(v_presentation_3800_, 0);
lean_inc(v_num_3866_);
lean_dec_ref_known(v_presentation_3800_, 1);
v___x_3867_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v_num_3866_, v_a_3721_);
lean_dec(v_num_3866_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_pos_3868_; lean_object* v_res_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3877_; 
v_pos_3868_ = lean_ctor_get(v___x_3867_, 0);
v_res_3869_ = lean_ctor_get(v___x_3867_, 1);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3871_ = v___x_3867_;
v_isShared_3872_ = v_isSharedCheck_3877_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_res_3869_);
lean_inc(v_pos_3868_);
lean_dec(v___x_3867_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3877_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3873_; lean_object* v___x_3875_; 
v___x_3873_ = lean_nat_to_int(v_res_3869_);
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 1, v___x_3873_);
v___x_3875_ = v___x_3871_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_pos_3868_);
lean_ctor_set(v_reuseFailAlloc_3876_, 1, v___x_3873_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
else
{
lean_object* v_pos_3878_; lean_object* v_err_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
v_pos_3878_ = lean_ctor_get(v___x_3867_, 0);
v_err_3879_ = lean_ctor_get(v___x_3867_, 1);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___x_3867_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_err_3879_);
lean_inc(v_pos_3878_);
lean_dec(v___x_3867_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_pos_3878_);
lean_ctor_set(v_reuseFailAlloc_3885_, 1, v_err_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
}
}
case 3:
{
lean_object* v_presentation_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
lean_dec_ref(v_config_3719_);
v_presentation_3887_ = lean_ctor_get(v_x_3720_, 0);
lean_inc(v_presentation_3887_);
lean_dec_ref_known(v_x_3720_, 1);
v___x_3888_ = lean_unsigned_to_nat(1u);
v___x_3889_ = lean_unsigned_to_nat(366u);
v___x_3890_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3890_, 0, v_presentation_3887_);
v___x_3891_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3888_, v___x_3889_, v___x_3890_, v_a_3721_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_pos_3892_; lean_object* v_res_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3903_; 
v_pos_3892_ = lean_ctor_get(v___x_3891_, 0);
v_res_3893_ = lean_ctor_get(v___x_3891_, 1);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3895_ = v___x_3891_;
v_isShared_3896_ = v_isSharedCheck_3903_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_res_3893_);
lean_inc(v_pos_3892_);
lean_dec(v___x_3891_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3903_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
uint8_t v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3901_; 
v___x_3897_ = 1;
v___x_3898_ = lean_box(v___x_3897_);
v___x_3899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3898_);
lean_ctor_set(v___x_3899_, 1, v_res_3893_);
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 1, v___x_3899_);
v___x_3901_ = v___x_3895_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_pos_3892_);
lean_ctor_set(v_reuseFailAlloc_3902_, 1, v___x_3899_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
else
{
lean_object* v_pos_3904_; lean_object* v_err_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3912_; 
v_pos_3904_ = lean_ctor_get(v___x_3891_, 0);
v_err_3905_ = lean_ctor_get(v___x_3891_, 1);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3891_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_err_3905_);
lean_inc(v_pos_3904_);
lean_dec(v___x_3891_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_pos_3904_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_err_3905_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
}
case 4:
{
lean_object* v_presentation_3913_; 
v_presentation_3913_ = lean_ctor_get(v_x_3720_, 0);
lean_inc_ref(v_presentation_3913_);
lean_dec_ref_known(v_x_3720_, 1);
if (lean_obj_tag(v_presentation_3913_) == 0)
{
lean_object* v_val_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
lean_dec_ref(v_config_3719_);
v_val_3914_ = lean_ctor_get(v_presentation_3913_, 0);
lean_inc(v_val_3914_);
lean_dec_ref_known(v_presentation_3913_, 1);
v___x_3915_ = lean_unsigned_to_nat(1u);
v___x_3916_ = lean_unsigned_to_nat(12u);
v___x_3917_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3917_, 0, v_val_3914_);
v___x_3918_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3915_, v___x_3916_, v___x_3917_, v_a_3721_);
return v___x_3918_;
}
else
{
lean_object* v_val_3919_; uint8_t v___x_3920_; 
v_val_3919_ = lean_ctor_get(v_presentation_3913_, 0);
lean_inc(v_val_3919_);
lean_dec_ref_known(v_presentation_3913_, 1);
v___x_3920_ = lean_unbox(v_val_3919_);
lean_dec(v_val_3919_);
switch(v___x_3920_)
{
case 1:
{
lean_object* v_dateformat_3921_; lean_object* v_symbols_3922_; lean_object* v___x_3923_; 
v_dateformat_3921_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_3921_);
lean_dec_ref(v_config_3719_);
v_symbols_3922_ = lean_ctor_get(v_dateformat_3921_, 1);
lean_inc_ref(v_symbols_3922_);
lean_dec_ref(v_dateformat_3921_);
v___x_3923_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(v_symbols_3922_, v_a_3721_);
return v___x_3923_;
}
case 2:
{
lean_object* v_dateformat_3924_; lean_object* v_symbols_3925_; lean_object* v___x_3926_; 
v_dateformat_3924_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_3924_);
lean_dec_ref(v_config_3719_);
v_symbols_3925_ = lean_ctor_get(v_dateformat_3924_, 1);
lean_inc_ref(v_symbols_3925_);
lean_dec_ref(v_dateformat_3924_);
v___x_3926_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(v_symbols_3925_, v_a_3721_);
return v___x_3926_;
}
default: 
{
lean_object* v_dateformat_3927_; lean_object* v_symbols_3928_; lean_object* v___x_3929_; 
v_dateformat_3927_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_3927_);
lean_dec_ref(v_config_3719_);
v_symbols_3928_ = lean_ctor_get(v_dateformat_3927_, 1);
lean_inc_ref(v_symbols_3928_);
lean_dec_ref(v_dateformat_3927_);
v___x_3929_ = l_Std_Time_parseMonthShort(v_symbols_3928_, v_a_3721_);
return v___x_3929_;
}
}
}
}
case 5:
{
lean_object* v_presentation_3930_; 
v_presentation_3930_ = lean_ctor_get(v_x_3720_, 0);
lean_inc_ref(v_presentation_3930_);
lean_dec_ref_known(v_x_3720_, 1);
if (lean_obj_tag(v_presentation_3930_) == 0)
{
lean_object* v_val_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
lean_dec_ref(v_config_3719_);
v_val_3931_ = lean_ctor_get(v_presentation_3930_, 0);
lean_inc(v_val_3931_);
lean_dec_ref_known(v_presentation_3930_, 1);
v___x_3932_ = lean_unsigned_to_nat(1u);
v___x_3933_ = lean_unsigned_to_nat(12u);
v___x_3934_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3934_, 0, v_val_3931_);
v___x_3935_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3932_, v___x_3933_, v___x_3934_, v_a_3721_);
return v___x_3935_;
}
else
{
lean_object* v_val_3936_; uint8_t v___x_3937_; 
v_val_3936_ = lean_ctor_get(v_presentation_3930_, 0);
lean_inc(v_val_3936_);
lean_dec_ref_known(v_presentation_3930_, 1);
v___x_3937_ = lean_unbox(v_val_3936_);
lean_dec(v_val_3936_);
switch(v___x_3937_)
{
case 1:
{
lean_object* v_dateformat_3938_; lean_object* v_symbols_3939_; lean_object* v___x_3940_; 
v_dateformat_3938_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_3938_);
lean_dec_ref(v_config_3719_);
v_symbols_3939_ = lean_ctor_get(v_dateformat_3938_, 1);
lean_inc_ref(v_symbols_3939_);
lean_dec_ref(v_dateformat_3938_);
v___x_3940_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthLong(v_symbols_3939_, v_a_3721_);
return v___x_3940_;
}
case 2:
{
lean_object* v_dateformat_3941_; lean_object* v_symbols_3942_; lean_object* v___x_3943_; 
v_dateformat_3941_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_3941_);
lean_dec_ref(v_config_3719_);
v_symbols_3942_ = lean_ctor_get(v_dateformat_3941_, 1);
lean_inc_ref(v_symbols_3942_);
lean_dec_ref(v_dateformat_3941_);
v___x_3943_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMonthNarrow(v_symbols_3942_, v_a_3721_);
return v___x_3943_;
}
default: 
{
lean_object* v_dateformat_3944_; lean_object* v_symbols_3945_; lean_object* v___x_3946_; 
v_dateformat_3944_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_3944_);
lean_dec_ref(v_config_3719_);
v_symbols_3945_ = lean_ctor_get(v_dateformat_3944_, 1);
lean_inc_ref(v_symbols_3945_);
lean_dec_ref(v_dateformat_3944_);
v___x_3946_ = l_Std_Time_parseMonthShort(v_symbols_3945_, v_a_3721_);
return v___x_3946_;
}
}
}
}
case 6:
{
lean_object* v_presentation_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
lean_dec_ref(v_config_3719_);
v_presentation_3947_ = lean_ctor_get(v_x_3720_, 0);
lean_inc(v_presentation_3947_);
lean_dec_ref_known(v_x_3720_, 1);
v___x_3948_ = lean_unsigned_to_nat(1u);
v___x_3949_ = lean_unsigned_to_nat(31u);
v___x_3950_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3950_, 0, v_presentation_3947_);
v___x_3951_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3948_, v___x_3949_, v___x_3950_, v_a_3721_);
return v___x_3951_;
}
case 7:
{
lean_object* v_presentation_3952_; 
v_presentation_3952_ = lean_ctor_get(v_x_3720_, 0);
lean_inc_ref(v_presentation_3952_);
lean_dec_ref_known(v_x_3720_, 1);
if (lean_obj_tag(v_presentation_3952_) == 0)
{
lean_object* v_val_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
lean_dec_ref(v_config_3719_);
v_val_3953_ = lean_ctor_get(v_presentation_3952_, 0);
lean_inc(v_val_3953_);
lean_dec_ref_known(v_presentation_3952_, 1);
v___x_3954_ = lean_unsigned_to_nat(1u);
v___x_3955_ = lean_unsigned_to_nat(4u);
v___x_3956_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3956_, 0, v_val_3953_);
v___x_3957_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3954_, v___x_3955_, v___x_3956_, v_a_3721_);
return v___x_3957_;
}
else
{
lean_object* v_val_3958_; uint8_t v___x_3959_; 
v_val_3958_ = lean_ctor_get(v_presentation_3952_, 0);
lean_inc(v_val_3958_);
lean_dec_ref_known(v_presentation_3952_, 1);
v___x_3959_ = lean_unbox(v_val_3958_);
lean_dec(v_val_3958_);
switch(v___x_3959_)
{
case 0:
{
lean_object* v_dateformat_3960_; lean_object* v_symbols_3961_; lean_object* v___x_3962_; 
v_dateformat_3960_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_3960_);
lean_dec_ref(v_config_3719_);
v_symbols_3961_ = lean_ctor_get(v_dateformat_3960_, 1);
lean_inc_ref(v_symbols_3961_);
lean_dec_ref(v_dateformat_3960_);
v___x_3962_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(v_symbols_3961_, v_a_3721_);
return v___x_3962_;
}
case 1:
{
lean_object* v_dateformat_3963_; lean_object* v_symbols_3964_; lean_object* v___x_3965_; 
v_dateformat_3963_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_3963_);
lean_dec_ref(v_config_3719_);
v_symbols_3964_ = lean_ctor_get(v_dateformat_3963_, 1);
lean_inc_ref(v_symbols_3964_);
lean_dec_ref(v_dateformat_3963_);
v___x_3965_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(v_symbols_3964_, v_a_3721_);
return v___x_3965_;
}
default: 
{
v___y_3723_ = v_a_3721_;
goto v___jp_3722_;
}
}
}
}
case 8:
{
lean_object* v_presentation_3966_; 
v_presentation_3966_ = lean_ctor_get(v_x_3720_, 0);
lean_inc_ref(v_presentation_3966_);
lean_dec_ref_known(v_x_3720_, 1);
if (lean_obj_tag(v_presentation_3966_) == 0)
{
lean_object* v_val_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
lean_dec_ref(v_config_3719_);
v_val_3967_ = lean_ctor_get(v_presentation_3966_, 0);
lean_inc(v_val_3967_);
lean_dec_ref_known(v_presentation_3966_, 1);
v___x_3968_ = lean_unsigned_to_nat(1u);
v___x_3969_ = lean_unsigned_to_nat(4u);
v___x_3970_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_3970_, 0, v_val_3967_);
v___x_3971_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_3968_, v___x_3969_, v___x_3970_, v_a_3721_);
return v___x_3971_;
}
else
{
lean_object* v_val_3972_; uint8_t v___x_3973_; 
v_val_3972_ = lean_ctor_get(v_presentation_3966_, 0);
lean_inc(v_val_3972_);
lean_dec_ref_known(v_presentation_3966_, 1);
v___x_3973_ = lean_unbox(v_val_3972_);
lean_dec(v_val_3972_);
switch(v___x_3973_)
{
case 0:
{
lean_object* v_dateformat_3974_; lean_object* v_symbols_3975_; lean_object* v___x_3976_; 
v_dateformat_3974_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_3974_);
lean_dec_ref(v_config_3719_);
v_symbols_3975_ = lean_ctor_get(v_dateformat_3974_, 1);
lean_inc_ref(v_symbols_3975_);
lean_dec_ref(v_dateformat_3974_);
v___x_3976_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterShort(v_symbols_3975_, v_a_3721_);
return v___x_3976_;
}
case 1:
{
lean_object* v_dateformat_3977_; lean_object* v_symbols_3978_; lean_object* v___x_3979_; 
v_dateformat_3977_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_3977_);
lean_dec_ref(v_config_3719_);
v_symbols_3978_ = lean_ctor_get(v_dateformat_3977_, 1);
lean_inc_ref(v_symbols_3978_);
lean_dec_ref(v_dateformat_3977_);
v___x_3979_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterLong(v_symbols_3978_, v_a_3721_);
return v___x_3979_;
}
default: 
{
v___y_3728_ = v_a_3721_;
goto v___jp_3727_;
}
}
}
}
case 9:
{
lean_object* v_presentation_3980_; 
lean_dec_ref(v_config_3719_);
v_presentation_3980_ = lean_ctor_get(v_x_3720_, 0);
lean_inc(v_presentation_3980_);
lean_dec_ref_known(v_x_3720_, 1);
switch(lean_obj_tag(v_presentation_3980_))
{
case 0:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3981_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__0));
v___x_3982_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_3981_, v_a_3721_);
return v___x_3982_;
}
case 1:
{
lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3983_ = lean_unsigned_to_nat(2u);
v___x_3984_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNum(v___x_3983_, v_a_3721_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_pos_3985_; lean_object* v_res_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3996_; 
v_pos_3985_ = lean_ctor_get(v___x_3984_, 0);
v_res_3986_ = lean_ctor_get(v___x_3984_, 1);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3988_ = v___x_3984_;
v_isShared_3989_ = v_isSharedCheck_3996_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_res_3986_);
lean_inc(v_pos_3985_);
lean_dec(v___x_3984_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3996_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3994_; 
v___x_3990_ = lean_nat_to_int(v_res_3986_);
v___x_3991_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__1);
v___x_3992_ = lean_int_add(v___x_3991_, v___x_3990_);
lean_dec(v___x_3990_);
if (v_isShared_3989_ == 0)
{
lean_ctor_set(v___x_3988_, 1, v___x_3992_);
v___x_3994_ = v___x_3988_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_pos_3985_);
lean_ctor_set(v_reuseFailAlloc_3995_, 1, v___x_3992_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
else
{
lean_object* v_pos_3997_; lean_object* v_err_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4005_; 
v_pos_3997_ = lean_ctor_get(v___x_3984_, 0);
v_err_3998_ = lean_ctor_get(v___x_3984_, 1);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_4000_ = v___x_3984_;
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_err_3998_);
lean_inc(v_pos_3997_);
lean_dec(v___x_3984_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_pos_3997_);
lean_ctor_set(v_reuseFailAlloc_4004_, 1, v_err_3998_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
case 2:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4006_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__2));
v___x_4007_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4006_, v_a_3721_);
return v___x_4007_;
}
default: 
{
lean_object* v_num_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
v_num_4008_ = lean_ctor_get(v_presentation_3980_, 0);
lean_inc(v_num_4008_);
lean_dec_ref_known(v_presentation_3980_, 1);
v___x_4009_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseNum___boxed), 2, 1);
lean_closure_set(v___x_4009_, 0, v_num_4008_);
v___x_4010_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseSigned(v___x_4009_, v_a_3721_);
return v___x_4010_;
}
}
}
case 10:
{
lean_object* v_presentation_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
lean_dec_ref(v_config_3719_);
v_presentation_4011_ = lean_ctor_get(v_x_3720_, 0);
lean_inc(v_presentation_4011_);
lean_dec_ref_known(v_x_3720_, 1);
v___x_4012_ = lean_unsigned_to_nat(1u);
v___x_4013_ = lean_unsigned_to_nat(53u);
v___x_4014_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4014_, 0, v_presentation_4011_);
v___x_4015_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4012_, v___x_4013_, v___x_4014_, v_a_3721_);
return v___x_4015_;
}
case 11:
{
lean_object* v_presentation_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; 
lean_dec_ref(v_config_3719_);
v_presentation_4016_ = lean_ctor_get(v_x_3720_, 0);
lean_inc(v_presentation_4016_);
lean_dec_ref_known(v_x_3720_, 1);
v___x_4017_ = lean_unsigned_to_nat(1u);
v___x_4018_ = lean_unsigned_to_nat(6u);
v___x_4019_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4019_, 0, v_presentation_4016_);
v___x_4020_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4017_, v___x_4018_, v___x_4019_, v_a_3721_);
return v___x_4020_;
}
case 12:
{
uint8_t v_presentation_4021_; 
v_presentation_4021_ = lean_ctor_get_uint8(v_x_3720_, 0);
lean_dec_ref_known(v_x_3720_, 0);
switch(v_presentation_4021_)
{
case 1:
{
lean_object* v_dateformat_4022_; lean_object* v_symbols_4023_; lean_object* v___x_4024_; 
v_dateformat_4022_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4022_);
lean_dec_ref(v_config_3719_);
v_symbols_4023_ = lean_ctor_get(v_dateformat_4022_, 1);
lean_inc_ref(v_symbols_4023_);
lean_dec_ref(v_dateformat_4022_);
v___x_4024_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4023_, v_a_3721_);
return v___x_4024_;
}
case 2:
{
lean_object* v_dateformat_4025_; lean_object* v_symbols_4026_; lean_object* v___x_4027_; 
v_dateformat_4025_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4025_);
lean_dec_ref(v_config_3719_);
v_symbols_4026_ = lean_ctor_get(v_dateformat_4025_, 1);
lean_inc_ref(v_symbols_4026_);
lean_dec_ref(v_dateformat_4025_);
v___x_4027_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4026_, v_a_3721_);
return v___x_4027_;
}
default: 
{
lean_object* v_dateformat_4028_; lean_object* v_symbols_4029_; lean_object* v___x_4030_; 
v_dateformat_4028_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4028_);
lean_dec_ref(v_config_3719_);
v_symbols_4029_ = lean_ctor_get(v_dateformat_4028_, 1);
lean_inc_ref(v_symbols_4029_);
lean_dec_ref(v_dateformat_4028_);
v___x_4030_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4029_, v_a_3721_);
return v___x_4030_;
}
}
}
case 13:
{
lean_object* v_presentation_4031_; 
v_presentation_4031_ = lean_ctor_get(v_x_3720_, 0);
lean_inc_ref(v_presentation_4031_);
lean_dec_ref_known(v_x_3720_, 1);
if (lean_obj_tag(v_presentation_4031_) == 0)
{
lean_object* v_val_4032_; lean_object* v___x_4033_; 
v_val_4032_ = lean_ctor_get(v_presentation_4031_, 0);
lean_inc(v_val_4032_);
lean_dec_ref_known(v_presentation_4031_, 1);
v___x_4033_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_val_4032_, v_a_3721_);
lean_dec(v_val_4032_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_pos_4034_; lean_object* v_res_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4071_; 
v_pos_4034_ = lean_ctor_get(v___x_4033_, 0);
v_res_4035_ = lean_ctor_get(v___x_4033_, 1);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4037_ = v___x_4033_;
v_isShared_4038_ = v_isSharedCheck_4071_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_res_4035_);
lean_inc(v_pos_4034_);
lean_dec(v___x_4033_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4071_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
uint8_t v___y_4040_; lean_object* v___x_4067_; uint8_t v___x_4068_; 
v___x_4067_ = lean_unsigned_to_nat(1u);
v___x_4068_ = lean_nat_dec_le(v___x_4067_, v_res_4035_);
if (v___x_4068_ == 0)
{
v___y_4040_ = v___x_4068_;
goto v___jp_4039_;
}
else
{
lean_object* v___x_4069_; uint8_t v___x_4070_; 
v___x_4069_ = lean_unsigned_to_nat(7u);
v___x_4070_ = lean_nat_dec_le(v_res_4035_, v___x_4069_);
v___y_4040_ = v___x_4070_;
goto v___jp_4039_;
}
v___jp_4039_:
{
if (v___y_4040_ == 0)
{
lean_object* v___x_4041_; lean_object* v___x_4043_; 
lean_dec(v_res_4035_);
lean_dec_ref(v_config_3719_);
v___x_4041_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4));
if (v_isShared_4038_ == 0)
{
lean_ctor_set_tag(v___x_4037_, 1);
lean_ctor_set(v___x_4037_, 1, v___x_4041_);
v___x_4043_ = v___x_4037_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_pos_4034_);
lean_ctor_set(v_reuseFailAlloc_4044_, 1, v___x_4041_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
else
{
lean_object* v_dateformat_4045_; uint8_t v_firstDayOfWeek_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v_range_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; uint8_t v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4065_; 
v_dateformat_4045_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4045_);
lean_dec_ref(v_config_3719_);
v_firstDayOfWeek_4046_ = lean_ctor_get_uint8(v_dateformat_4045_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_4045_);
v___x_4047_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_4046_);
v___x_4048_ = lean_nat_to_int(v_res_4035_);
v___x_4049_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_4050_ = lean_int_sub(v___x_4048_, v___x_4049_);
lean_dec(v___x_4048_);
v___x_4051_ = lean_int_add(v___x_4050_, v___x_4047_);
lean_dec(v___x_4047_);
lean_dec(v___x_4050_);
v___x_4052_ = lean_int_sub(v___x_4051_, v___x_4049_);
lean_dec(v___x_4051_);
v___x_4053_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_4054_ = lean_int_emod(v___x_4052_, v___x_4053_);
lean_dec(v___x_4052_);
v___x_4055_ = lean_int_add(v___x_4054_, v___x_4049_);
lean_dec(v___x_4054_);
v_range_4056_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6);
v___x_4057_ = lean_int_sub(v___x_4055_, v___x_4049_);
lean_dec(v___x_4055_);
v___x_4058_ = lean_int_emod(v___x_4057_, v_range_4056_);
lean_dec(v___x_4057_);
v___x_4059_ = lean_int_add(v___x_4058_, v_range_4056_);
lean_dec(v___x_4058_);
v___x_4060_ = lean_int_emod(v___x_4059_, v_range_4056_);
lean_dec(v___x_4059_);
v___x_4061_ = lean_int_add(v___x_4060_, v___x_4049_);
lean_dec(v___x_4060_);
v___x_4062_ = l_Std_Time_Weekday_ofOrdinal(v___x_4061_);
lean_dec(v___x_4061_);
v___x_4063_ = lean_box(v___x_4062_);
if (v_isShared_4038_ == 0)
{
lean_ctor_set(v___x_4037_, 1, v___x_4063_);
v___x_4065_ = v___x_4037_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_pos_4034_);
lean_ctor_set(v_reuseFailAlloc_4066_, 1, v___x_4063_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
}
else
{
lean_object* v_pos_4072_; lean_object* v_err_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_dec_ref(v_config_3719_);
v_pos_4072_ = lean_ctor_get(v___x_4033_, 0);
v_err_4073_ = lean_ctor_get(v___x_4033_, 1);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4033_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_err_4073_);
lean_inc(v_pos_4072_);
lean_dec(v___x_4033_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_pos_4072_);
lean_ctor_set(v_reuseFailAlloc_4079_, 1, v_err_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
else
{
lean_object* v_val_4081_; uint8_t v___x_4082_; 
v_val_4081_ = lean_ctor_get(v_presentation_4031_, 0);
lean_inc(v_val_4081_);
lean_dec_ref_known(v_presentation_4031_, 1);
v___x_4082_ = lean_unbox(v_val_4081_);
lean_dec(v_val_4081_);
switch(v___x_4082_)
{
case 0:
{
lean_object* v_dateformat_4083_; lean_object* v_symbols_4084_; lean_object* v___x_4085_; 
v_dateformat_4083_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4083_);
lean_dec_ref(v_config_3719_);
v_symbols_4084_ = lean_ctor_get(v_dateformat_4083_, 1);
lean_inc_ref(v_symbols_4084_);
lean_dec_ref(v_dateformat_4083_);
v___x_4085_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4084_, v_a_3721_);
return v___x_4085_;
}
case 1:
{
lean_object* v_dateformat_4086_; lean_object* v_symbols_4087_; lean_object* v___x_4088_; 
v_dateformat_4086_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4086_);
lean_dec_ref(v_config_3719_);
v_symbols_4087_ = lean_ctor_get(v_dateformat_4086_, 1);
lean_inc_ref(v_symbols_4087_);
lean_dec_ref(v_dateformat_4086_);
v___x_4088_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4087_, v_a_3721_);
return v___x_4088_;
}
case 2:
{
lean_object* v_dateformat_4089_; lean_object* v_symbols_4090_; lean_object* v___x_4091_; 
v_dateformat_4089_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4089_);
lean_dec_ref(v_config_3719_);
v_symbols_4090_ = lean_ctor_get(v_dateformat_4089_, 1);
lean_inc_ref(v_symbols_4090_);
lean_dec_ref(v_dateformat_4089_);
v___x_4091_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4090_, v_a_3721_);
return v___x_4091_;
}
default: 
{
lean_object* v_dateformat_4092_; lean_object* v_symbols_4093_; lean_object* v___x_4094_; 
v_dateformat_4092_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4092_);
lean_dec_ref(v_config_3719_);
v_symbols_4093_ = lean_ctor_get(v_dateformat_4092_, 1);
lean_inc_ref(v_symbols_4093_);
lean_dec_ref(v_dateformat_4092_);
v___x_4094_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(v_symbols_4093_, v_a_3721_);
return v___x_4094_;
}
}
}
}
case 14:
{
lean_object* v_presentation_4095_; 
v_presentation_4095_ = lean_ctor_get(v_x_3720_, 0);
lean_inc_ref(v_presentation_4095_);
lean_dec_ref_known(v_x_3720_, 1);
if (lean_obj_tag(v_presentation_4095_) == 0)
{
lean_object* v_val_4096_; lean_object* v___x_4097_; 
v_val_4096_ = lean_ctor_get(v_presentation_4095_, 0);
lean_inc(v_val_4096_);
lean_dec_ref_known(v_presentation_4095_, 1);
v___x_4097_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_val_4096_, v_a_3721_);
lean_dec(v_val_4096_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v_pos_4098_; lean_object* v_res_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4135_; 
v_pos_4098_ = lean_ctor_get(v___x_4097_, 0);
v_res_4099_ = lean_ctor_get(v___x_4097_, 1);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4101_ = v___x_4097_;
v_isShared_4102_ = v_isSharedCheck_4135_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_res_4099_);
lean_inc(v_pos_4098_);
lean_dec(v___x_4097_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4135_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
uint8_t v___y_4104_; lean_object* v___x_4131_; uint8_t v___x_4132_; 
v___x_4131_ = lean_unsigned_to_nat(1u);
v___x_4132_ = lean_nat_dec_le(v___x_4131_, v_res_4099_);
if (v___x_4132_ == 0)
{
v___y_4104_ = v___x_4132_;
goto v___jp_4103_;
}
else
{
lean_object* v___x_4133_; uint8_t v___x_4134_; 
v___x_4133_ = lean_unsigned_to_nat(7u);
v___x_4134_ = lean_nat_dec_le(v_res_4099_, v___x_4133_);
v___y_4104_ = v___x_4134_;
goto v___jp_4103_;
}
v___jp_4103_:
{
if (v___y_4104_ == 0)
{
lean_object* v___x_4105_; lean_object* v___x_4107_; 
lean_dec(v_res_4099_);
lean_dec_ref(v_config_3719_);
v___x_4105_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__4));
if (v_isShared_4102_ == 0)
{
lean_ctor_set_tag(v___x_4101_, 1);
lean_ctor_set(v___x_4101_, 1, v___x_4105_);
v___x_4107_ = v___x_4101_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_pos_4098_);
lean_ctor_set(v_reuseFailAlloc_4108_, 1, v___x_4105_);
v___x_4107_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
return v___x_4107_;
}
}
else
{
lean_object* v_dateformat_4109_; uint8_t v_firstDayOfWeek_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v_range_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; uint8_t v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4129_; 
v_dateformat_4109_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4109_);
lean_dec_ref(v_config_3719_);
v_firstDayOfWeek_4110_ = lean_ctor_get_uint8(v_dateformat_4109_, sizeof(void*)*2);
lean_dec_ref(v_dateformat_4109_);
v___x_4111_ = l_Std_Time_Weekday_toOrdinal(v_firstDayOfWeek_4110_);
v___x_4112_ = lean_nat_to_int(v_res_4099_);
v___x_4113_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_4114_ = lean_int_sub(v___x_4112_, v___x_4113_);
lean_dec(v___x_4112_);
v___x_4115_ = lean_int_add(v___x_4114_, v___x_4111_);
lean_dec(v___x_4111_);
lean_dec(v___x_4114_);
v___x_4116_ = lean_int_sub(v___x_4115_, v___x_4113_);
lean_dec(v___x_4115_);
v___x_4117_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__1);
v___x_4118_ = lean_int_emod(v___x_4116_, v___x_4117_);
lean_dec(v___x_4116_);
v___x_4119_ = lean_int_add(v___x_4118_, v___x_4113_);
lean_dec(v___x_4118_);
v_range_4120_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__6);
v___x_4121_ = lean_int_sub(v___x_4119_, v___x_4113_);
lean_dec(v___x_4119_);
v___x_4122_ = lean_int_emod(v___x_4121_, v_range_4120_);
lean_dec(v___x_4121_);
v___x_4123_ = lean_int_add(v___x_4122_, v_range_4120_);
lean_dec(v___x_4122_);
v___x_4124_ = lean_int_emod(v___x_4123_, v_range_4120_);
lean_dec(v___x_4123_);
v___x_4125_ = lean_int_add(v___x_4124_, v___x_4113_);
lean_dec(v___x_4124_);
v___x_4126_ = l_Std_Time_Weekday_ofOrdinal(v___x_4125_);
lean_dec(v___x_4125_);
v___x_4127_ = lean_box(v___x_4126_);
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 1, v___x_4127_);
v___x_4129_ = v___x_4101_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_pos_4098_);
lean_ctor_set(v_reuseFailAlloc_4130_, 1, v___x_4127_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
}
else
{
lean_object* v_pos_4136_; lean_object* v_err_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
lean_dec_ref(v_config_3719_);
v_pos_4136_ = lean_ctor_get(v___x_4097_, 0);
v_err_4137_ = lean_ctor_get(v___x_4097_, 1);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4139_ = v___x_4097_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_err_4137_);
lean_inc(v_pos_4136_);
lean_dec(v___x_4097_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_pos_4136_);
lean_ctor_set(v_reuseFailAlloc_4143_, 1, v_err_4137_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
else
{
lean_object* v_val_4145_; uint8_t v___x_4146_; 
v_val_4145_ = lean_ctor_get(v_presentation_4095_, 0);
lean_inc(v_val_4145_);
lean_dec_ref_known(v_presentation_4095_, 1);
v___x_4146_ = lean_unbox(v_val_4145_);
lean_dec(v_val_4145_);
switch(v___x_4146_)
{
case 0:
{
lean_object* v_dateformat_4147_; lean_object* v_symbols_4148_; lean_object* v___x_4149_; 
v_dateformat_4147_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4147_);
lean_dec_ref(v_config_3719_);
v_symbols_4148_ = lean_ctor_get(v_dateformat_4147_, 1);
lean_inc_ref(v_symbols_4148_);
lean_dec_ref(v_dateformat_4147_);
v___x_4149_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayShort(v_symbols_4148_, v_a_3721_);
return v___x_4149_;
}
case 1:
{
lean_object* v_dateformat_4150_; lean_object* v_symbols_4151_; lean_object* v___x_4152_; 
v_dateformat_4150_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4150_);
lean_dec_ref(v_config_3719_);
v_symbols_4151_ = lean_ctor_get(v_dateformat_4150_, 1);
lean_inc_ref(v_symbols_4151_);
lean_dec_ref(v_dateformat_4150_);
v___x_4152_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayLong(v_symbols_4151_, v_a_3721_);
return v___x_4152_;
}
case 2:
{
lean_object* v_dateformat_4153_; lean_object* v_symbols_4154_; lean_object* v___x_4155_; 
v_dateformat_4153_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4153_);
lean_dec_ref(v_config_3719_);
v_symbols_4154_ = lean_ctor_get(v_dateformat_4153_, 1);
lean_inc_ref(v_symbols_4154_);
lean_dec_ref(v_dateformat_4153_);
v___x_4155_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayNarrow(v_symbols_4154_, v_a_3721_);
return v___x_4155_;
}
default: 
{
lean_object* v_dateformat_4156_; lean_object* v_symbols_4157_; lean_object* v___x_4158_; 
v_dateformat_4156_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4156_);
lean_dec_ref(v_config_3719_);
v_symbols_4157_ = lean_ctor_get(v_dateformat_4156_, 1);
lean_inc_ref(v_symbols_4157_);
lean_dec_ref(v_dateformat_4156_);
v___x_4158_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWeekdayTwoLetter(v_symbols_4157_, v_a_3721_);
return v___x_4158_;
}
}
}
}
case 15:
{
lean_object* v_presentation_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
lean_dec_ref(v_config_3719_);
v_presentation_4159_ = lean_ctor_get(v_x_3720_, 0);
lean_inc(v_presentation_4159_);
lean_dec_ref_known(v_x_3720_, 1);
v___x_4160_ = lean_unsigned_to_nat(1u);
v___x_4161_ = lean_unsigned_to_nat(5u);
v___x_4162_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4162_, 0, v_presentation_4159_);
v___x_4163_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4160_, v___x_4161_, v___x_4162_, v_a_3721_);
return v___x_4163_;
}
case 16:
{
uint8_t v_presentation_4164_; 
v_presentation_4164_ = lean_ctor_get_uint8(v_x_3720_, 0);
lean_dec_ref_known(v_x_3720_, 0);
switch(v_presentation_4164_)
{
case 1:
{
lean_object* v_dateformat_4165_; lean_object* v_symbols_4166_; lean_object* v___x_4167_; 
v_dateformat_4165_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4165_);
lean_dec_ref(v_config_3719_);
v_symbols_4166_ = lean_ctor_get(v_dateformat_4165_, 1);
lean_inc_ref(v_symbols_4166_);
lean_dec_ref(v_dateformat_4165_);
v___x_4167_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerLong(v_symbols_4166_, v_a_3721_);
return v___x_4167_;
}
case 2:
{
lean_object* v_dateformat_4168_; lean_object* v_symbols_4169_; lean_object* v___x_4170_; 
v_dateformat_4168_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4168_);
lean_dec_ref(v_config_3719_);
v_symbols_4169_ = lean_ctor_get(v_dateformat_4168_, 1);
lean_inc_ref(v_symbols_4169_);
lean_dec_ref(v_dateformat_4168_);
v___x_4170_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerNarrow(v_symbols_4169_, v_a_3721_);
return v___x_4170_;
}
default: 
{
lean_object* v_dateformat_4171_; lean_object* v_symbols_4172_; lean_object* v___x_4173_; 
v_dateformat_4171_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4171_);
lean_dec_ref(v_config_3719_);
v_symbols_4172_ = lean_ctor_get(v_dateformat_4171_, 1);
lean_inc_ref(v_symbols_4172_);
lean_dec_ref(v_dateformat_4171_);
v___x_4173_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseMarkerShort(v_symbols_4172_, v_a_3721_);
return v___x_4173_;
}
}
}
case 17:
{
uint8_t v_presentation_4174_; 
v_presentation_4174_ = lean_ctor_get_uint8(v_x_3720_, 0);
lean_dec_ref_known(v_x_3720_, 0);
switch(v_presentation_4174_)
{
case 1:
{
lean_object* v_dateformat_4175_; lean_object* v_symbols_4176_; lean_object* v_dayPeriodLong_4177_; lean_object* v___x_4178_; 
v_dateformat_4175_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4175_);
lean_dec_ref(v_config_3719_);
v_symbols_4176_ = lean_ctor_get(v_dateformat_4175_, 1);
lean_inc_ref(v_symbols_4176_);
lean_dec_ref(v_dateformat_4175_);
v_dayPeriodLong_4177_ = lean_ctor_get(v_symbols_4176_, 20);
lean_inc_ref(v_dayPeriodLong_4177_);
lean_dec_ref(v_symbols_4176_);
v___x_4178_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodLong_4177_, v_a_3721_);
return v___x_4178_;
}
case 2:
{
lean_object* v_dateformat_4179_; lean_object* v_symbols_4180_; lean_object* v_dayPeriodNarrow_4181_; lean_object* v___x_4182_; 
v_dateformat_4179_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4179_);
lean_dec_ref(v_config_3719_);
v_symbols_4180_ = lean_ctor_get(v_dateformat_4179_, 1);
lean_inc_ref(v_symbols_4180_);
lean_dec_ref(v_dateformat_4179_);
v_dayPeriodNarrow_4181_ = lean_ctor_get(v_symbols_4180_, 21);
lean_inc_ref(v_dayPeriodNarrow_4181_);
lean_dec_ref(v_symbols_4180_);
v___x_4182_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodNarrow_4181_, v_a_3721_);
return v___x_4182_;
}
default: 
{
lean_object* v_dateformat_4183_; lean_object* v_symbols_4184_; lean_object* v_dayPeriodShort_4185_; lean_object* v___x_4186_; 
v_dateformat_4183_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4183_);
lean_dec_ref(v_config_3719_);
v_symbols_4184_ = lean_ctor_get(v_dateformat_4183_, 1);
lean_inc_ref(v_symbols_4184_);
lean_dec_ref(v_dateformat_4183_);
v_dayPeriodShort_4185_ = lean_ctor_get(v_symbols_4184_, 19);
lean_inc_ref(v_dayPeriodShort_4185_);
lean_dec_ref(v_symbols_4184_);
v___x_4186_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseDayPeriodFrom(v_dayPeriodShort_4185_, v_a_3721_);
return v___x_4186_;
}
}
}
case 18:
{
uint8_t v_presentation_4187_; 
v_presentation_4187_ = lean_ctor_get_uint8(v_x_3720_, 0);
lean_dec_ref_known(v_x_3720_, 0);
switch(v_presentation_4187_)
{
case 1:
{
lean_object* v_dateformat_4188_; lean_object* v_symbols_4189_; lean_object* v_extendedDayPeriodLong_4190_; lean_object* v___x_4191_; 
v_dateformat_4188_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4188_);
lean_dec_ref(v_config_3719_);
v_symbols_4189_ = lean_ctor_get(v_dateformat_4188_, 1);
lean_inc_ref(v_symbols_4189_);
lean_dec_ref(v_dateformat_4188_);
v_extendedDayPeriodLong_4190_ = lean_ctor_get(v_symbols_4189_, 23);
lean_inc_ref(v_extendedDayPeriodLong_4190_);
lean_dec_ref(v_symbols_4189_);
v___x_4191_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodLong_4190_, v_a_3721_);
lean_dec_ref(v_extendedDayPeriodLong_4190_);
return v___x_4191_;
}
case 2:
{
lean_object* v_dateformat_4192_; lean_object* v_symbols_4193_; lean_object* v_extendedDayPeriodNarrow_4194_; lean_object* v___x_4195_; 
v_dateformat_4192_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4192_);
lean_dec_ref(v_config_3719_);
v_symbols_4193_ = lean_ctor_get(v_dateformat_4192_, 1);
lean_inc_ref(v_symbols_4193_);
lean_dec_ref(v_dateformat_4192_);
v_extendedDayPeriodNarrow_4194_ = lean_ctor_get(v_symbols_4193_, 24);
lean_inc_ref(v_extendedDayPeriodNarrow_4194_);
lean_dec_ref(v_symbols_4193_);
v___x_4195_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodNarrow_4194_, v_a_3721_);
lean_dec_ref(v_extendedDayPeriodNarrow_4194_);
return v___x_4195_;
}
default: 
{
lean_object* v_dateformat_4196_; lean_object* v_symbols_4197_; lean_object* v_extendedDayPeriodShort_4198_; lean_object* v___x_4199_; 
v_dateformat_4196_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_4196_);
lean_dec_ref(v_config_3719_);
v_symbols_4197_ = lean_ctor_get(v_dateformat_4196_, 1);
lean_inc_ref(v_symbols_4197_);
lean_dec_ref(v_dateformat_4196_);
v_extendedDayPeriodShort_4198_ = lean_ctor_get(v_symbols_4197_, 22);
lean_inc_ref(v_extendedDayPeriodShort_4198_);
lean_dec_ref(v_symbols_4197_);
v___x_4199_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseExtendedDayPeriodFrom(v_extendedDayPeriodShort_4198_, v_a_3721_);
lean_dec_ref(v_extendedDayPeriodShort_4198_);
return v___x_4199_;
}
}
}
case 19:
{
lean_object* v_presentation_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
lean_dec_ref(v_config_3719_);
v_presentation_4200_ = lean_ctor_get(v_x_3720_, 0);
lean_inc(v_presentation_4200_);
lean_dec_ref_known(v_x_3720_, 1);
v___x_4201_ = lean_unsigned_to_nat(1u);
v___x_4202_ = lean_unsigned_to_nat(12u);
v___x_4203_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4203_, 0, v_presentation_4200_);
v___x_4204_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4201_, v___x_4202_, v___x_4203_, v_a_3721_);
return v___x_4204_;
}
case 20:
{
lean_object* v_presentation_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
lean_dec_ref(v_config_3719_);
v_presentation_4205_ = lean_ctor_get(v_x_3720_, 0);
lean_inc(v_presentation_4205_);
lean_dec_ref_known(v_x_3720_, 1);
v___x_4206_ = lean_unsigned_to_nat(0u);
v___x_4207_ = lean_unsigned_to_nat(11u);
v___x_4208_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4208_, 0, v_presentation_4205_);
v___x_4209_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4206_, v___x_4207_, v___x_4208_, v_a_3721_);
return v___x_4209_;
}
case 21:
{
lean_object* v_presentation_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
lean_dec_ref(v_config_3719_);
v_presentation_4210_ = lean_ctor_get(v_x_3720_, 0);
lean_inc(v_presentation_4210_);
lean_dec_ref_known(v_x_3720_, 1);
v___x_4211_ = lean_unsigned_to_nat(1u);
v___x_4212_ = lean_unsigned_to_nat(24u);
v___x_4213_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4213_, 0, v_presentation_4210_);
v___x_4214_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4211_, v___x_4212_, v___x_4213_, v_a_3721_);
return v___x_4214_;
}
case 22:
{
lean_object* v_presentation_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
lean_dec_ref(v_config_3719_);
v_presentation_4215_ = lean_ctor_get(v_x_3720_, 0);
lean_inc(v_presentation_4215_);
lean_dec_ref_known(v_x_3720_, 1);
v___x_4216_ = lean_unsigned_to_nat(0u);
v___x_4217_ = lean_unsigned_to_nat(23u);
v___x_4218_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4218_, 0, v_presentation_4215_);
v___x_4219_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4216_, v___x_4217_, v___x_4218_, v_a_3721_);
return v___x_4219_;
}
case 23:
{
lean_object* v_presentation_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
lean_dec_ref(v_config_3719_);
v_presentation_4220_ = lean_ctor_get(v_x_3720_, 0);
lean_inc(v_presentation_4220_);
lean_dec_ref_known(v_x_3720_, 1);
v___x_4221_ = lean_unsigned_to_nat(0u);
v___x_4222_ = lean_unsigned_to_nat(59u);
v___x_4223_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4223_, 0, v_presentation_4220_);
v___x_4224_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4221_, v___x_4222_, v___x_4223_, v_a_3721_);
return v___x_4224_;
}
case 24:
{
uint8_t v_allowLeapSeconds_4225_; 
v_allowLeapSeconds_4225_ = lean_ctor_get_uint8(v_config_3719_, sizeof(void*)*1);
lean_dec_ref(v_config_3719_);
if (v_allowLeapSeconds_4225_ == 0)
{
lean_object* v_presentation_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; 
v_presentation_4226_ = lean_ctor_get(v_x_3720_, 0);
lean_inc(v_presentation_4226_);
lean_dec_ref_known(v_x_3720_, 1);
v___x_4227_ = lean_unsigned_to_nat(0u);
v___x_4228_ = lean_unsigned_to_nat(59u);
v___x_4229_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4229_, 0, v_presentation_4226_);
v___x_4230_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4227_, v___x_4228_, v___x_4229_, v_a_3721_);
if (lean_obj_tag(v___x_4230_) == 0)
{
lean_object* v_pos_4231_; lean_object* v_res_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4239_; 
v_pos_4231_ = lean_ctor_get(v___x_4230_, 0);
v_res_4232_ = lean_ctor_get(v___x_4230_, 1);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4230_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4234_ = v___x_4230_;
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_res_4232_);
lean_inc(v_pos_4231_);
lean_dec(v___x_4230_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4237_; 
if (v_isShared_4235_ == 0)
{
v___x_4237_ = v___x_4234_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_pos_4231_);
lean_ctor_set(v_reuseFailAlloc_4238_, 1, v_res_4232_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
}
}
}
else
{
return v___x_4230_;
}
}
else
{
lean_object* v_presentation_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v_presentation_4240_ = lean_ctor_get(v_x_3720_, 0);
lean_inc(v_presentation_4240_);
lean_dec_ref_known(v_x_3720_, 1);
v___x_4241_ = lean_unsigned_to_nat(0u);
v___x_4242_ = lean_unsigned_to_nat(60u);
v___x_4243_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4243_, 0, v_presentation_4240_);
v___x_4244_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4241_, v___x_4242_, v___x_4243_, v_a_3721_);
return v___x_4244_;
}
}
case 25:
{
lean_object* v_presentation_4245_; 
lean_dec_ref(v_config_3719_);
v_presentation_4245_ = lean_ctor_get(v_x_3720_, 0);
lean_inc(v_presentation_4245_);
lean_dec_ref_known(v_x_3720_, 1);
if (lean_obj_tag(v_presentation_4245_) == 0)
{
lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; 
v___x_4246_ = lean_unsigned_to_nat(0u);
v___x_4247_ = lean_unsigned_to_nat(999999999u);
v___x_4248_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseWith___closed__7));
v___x_4249_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4246_, v___x_4247_, v___x_4248_, v_a_3721_);
return v___x_4249_;
}
else
{
lean_object* v_digits_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v_digits_4250_ = lean_ctor_get(v_presentation_4245_, 0);
lean_inc(v_digits_4250_);
lean_dec_ref_known(v_presentation_4245_, 1);
v___x_4251_ = lean_unsigned_to_nat(0u);
v___x_4252_ = lean_unsigned_to_nat(999999999u);
v___x_4253_ = lean_unsigned_to_nat(9u);
v___x_4254_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFractionNum___boxed), 3, 2);
lean_closure_set(v___x_4254_, 0, v_digits_4250_);
lean_closure_set(v___x_4254_, 1, v___x_4253_);
v___x_4255_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4251_, v___x_4252_, v___x_4254_, v_a_3721_);
return v___x_4255_;
}
}
case 26:
{
lean_object* v_presentation_4256_; lean_object* v___x_4257_; 
lean_dec_ref(v_config_3719_);
v_presentation_4256_ = lean_ctor_get(v_x_3720_, 0);
lean_inc(v_presentation_4256_);
lean_dec_ref_known(v_x_3720_, 1);
v___x_4257_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_presentation_4256_, v_a_3721_);
lean_dec(v_presentation_4256_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_pos_4258_; lean_object* v_res_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4267_; 
v_pos_4258_ = lean_ctor_get(v___x_4257_, 0);
v_res_4259_ = lean_ctor_get(v___x_4257_, 1);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4261_ = v___x_4257_;
v_isShared_4262_ = v_isSharedCheck_4267_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_res_4259_);
lean_inc(v_pos_4258_);
lean_dec(v___x_4257_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4267_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4263_; lean_object* v___x_4265_; 
v___x_4263_ = lean_nat_to_int(v_res_4259_);
if (v_isShared_4262_ == 0)
{
lean_ctor_set(v___x_4261_, 1, v___x_4263_);
v___x_4265_ = v___x_4261_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_pos_4258_);
lean_ctor_set(v_reuseFailAlloc_4266_, 1, v___x_4263_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
else
{
lean_object* v_pos_4268_; lean_object* v_err_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
v_pos_4268_ = lean_ctor_get(v___x_4257_, 0);
v_err_4269_ = lean_ctor_get(v___x_4257_, 1);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4257_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_err_4269_);
lean_inc(v_pos_4268_);
lean_dec(v___x_4257_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_pos_4268_);
lean_ctor_set(v_reuseFailAlloc_4275_, 1, v_err_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
}
case 27:
{
lean_object* v_presentation_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
lean_dec_ref(v_config_3719_);
v_presentation_4277_ = lean_ctor_get(v_x_3720_, 0);
lean_inc(v_presentation_4277_);
lean_dec_ref_known(v_x_3720_, 1);
v___x_4278_ = lean_unsigned_to_nat(0u);
v___x_4279_ = lean_unsigned_to_nat(999999999u);
v___x_4280_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum___boxed), 2, 1);
lean_closure_set(v___x_4280_, 0, v_presentation_4277_);
v___x_4281_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseNatToBounded(v___x_4278_, v___x_4279_, v___x_4280_, v_a_3721_);
return v___x_4281_;
}
case 28:
{
lean_object* v_presentation_4282_; lean_object* v___x_4283_; 
lean_dec_ref(v_config_3719_);
v_presentation_4282_ = lean_ctor_get(v_x_3720_, 0);
lean_inc(v_presentation_4282_);
lean_dec_ref_known(v_x_3720_, 1);
v___x_4283_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseFlexibleNum(v_presentation_4282_, v_a_3721_);
lean_dec(v_presentation_4282_);
if (lean_obj_tag(v___x_4283_) == 0)
{
lean_object* v_pos_4284_; lean_object* v_res_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4293_; 
v_pos_4284_ = lean_ctor_get(v___x_4283_, 0);
v_res_4285_ = lean_ctor_get(v___x_4283_, 1);
v_isSharedCheck_4293_ = !lean_is_exclusive(v___x_4283_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4287_ = v___x_4283_;
v_isShared_4288_ = v_isSharedCheck_4293_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_res_4285_);
lean_inc(v_pos_4284_);
lean_dec(v___x_4283_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4293_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4289_; lean_object* v___x_4291_; 
v___x_4289_ = lean_nat_to_int(v_res_4285_);
if (v_isShared_4288_ == 0)
{
lean_ctor_set(v___x_4287_, 1, v___x_4289_);
v___x_4291_ = v___x_4287_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_pos_4284_);
lean_ctor_set(v_reuseFailAlloc_4292_, 1, v___x_4289_);
v___x_4291_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
return v___x_4291_;
}
}
}
else
{
lean_object* v_pos_4294_; lean_object* v_err_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4302_; 
v_pos_4294_ = lean_ctor_get(v___x_4283_, 0);
v_err_4295_ = lean_ctor_get(v___x_4283_, 1);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___x_4283_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4297_ = v___x_4283_;
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_err_4295_);
lean_inc(v_pos_4294_);
lean_dec(v___x_4283_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4300_; 
if (v_isShared_4298_ == 0)
{
v___x_4300_ = v___x_4297_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_pos_4294_);
lean_ctor_set(v_reuseFailAlloc_4301_, 1, v_err_4295_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
return v___x_4300_;
}
}
}
}
case 29:
{
uint8_t v_presentation_4303_; 
lean_dec_ref(v_config_3719_);
v_presentation_4303_ = lean_ctor_get_uint8(v_x_3720_, 0);
lean_dec_ref_known(v_x_3720_, 0);
if (v_presentation_4303_ == 0)
{
lean_object* v___x_4304_; lean_object* v___x_4305_; 
v___x_4304_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__2));
v___x_4305_ = l_Std_Internal_Parsec_String_pstring(v___x_4304_, v_a_3721_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v_pos_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
v_pos_4306_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4313_ == 0)
{
lean_object* v_unused_4314_; 
v_unused_4314_ = lean_ctor_get(v___x_4305_, 1);
lean_dec(v_unused_4314_);
v___x_4308_ = v___x_4305_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_pos_4306_);
lean_dec(v___x_4305_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
lean_ctor_set(v___x_4308_, 1, v___x_4304_);
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_pos_4306_);
lean_ctor_set(v_reuseFailAlloc_4312_, 1, v___x_4304_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
else
{
return v___x_4305_;
}
}
else
{
lean_object* v___x_4315_; 
v___x_4315_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(v_a_3721_);
return v___x_4315_;
}
}
case 32:
{
uint8_t v_presentation_4316_; 
lean_dec_ref(v_config_3719_);
v_presentation_4316_ = lean_ctor_get_uint8(v_x_3720_, 0);
lean_dec_ref_known(v_x_3720_, 0);
if (v_presentation_4316_ == 0)
{
lean_object* v___x_4317_; lean_object* v___x_4318_; 
v___x_4317_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4318_ = l_Std_Internal_Parsec_String_pstring(v___x_4317_, v_a_3721_);
if (lean_obj_tag(v___x_4318_) == 0)
{
lean_object* v_pos_4319_; uint8_t v___x_4320_; uint8_t v___x_4321_; uint8_t v___x_4322_; lean_object* v___x_4323_; 
v_pos_4319_ = lean_ctor_get(v___x_4318_, 0);
lean_inc(v_pos_4319_);
lean_dec_ref_known(v___x_4318_, 2);
v___x_4320_ = 2;
v___x_4321_ = 1;
v___x_4322_ = 1;
v___x_4323_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4320_, v___x_4321_, v___x_4322_, v_pos_4319_);
return v___x_4323_;
}
else
{
lean_object* v_pos_4324_; lean_object* v_err_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
v_pos_4324_ = lean_ctor_get(v___x_4318_, 0);
v_err_4325_ = lean_ctor_get(v___x_4318_, 1);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4318_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4327_ = v___x_4318_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_err_4325_);
lean_inc(v_pos_4324_);
lean_dec(v___x_4318_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4330_; 
if (v_isShared_4328_ == 0)
{
v___x_4330_ = v___x_4327_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_pos_4324_);
lean_ctor_set(v_reuseFailAlloc_4331_, 1, v_err_4325_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
}
else
{
lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4333_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4334_ = l_Std_Internal_Parsec_String_pstring(v___x_4333_, v_a_3721_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v_pos_4335_; uint8_t v___x_4336_; uint8_t v___x_4337_; uint8_t v___x_4338_; lean_object* v___x_4339_; 
v_pos_4335_ = lean_ctor_get(v___x_4334_, 0);
lean_inc(v_pos_4335_);
lean_dec_ref_known(v___x_4334_, 2);
v___x_4336_ = 0;
v___x_4337_ = 2;
v___x_4338_ = 1;
v___x_4339_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4336_, v___x_4337_, v___x_4338_, v_pos_4335_);
return v___x_4339_;
}
else
{
lean_object* v_pos_4340_; lean_object* v_err_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4348_; 
v_pos_4340_ = lean_ctor_get(v___x_4334_, 0);
v_err_4341_ = lean_ctor_get(v___x_4334_, 1);
v_isSharedCheck_4348_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4343_ = v___x_4334_;
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_err_4341_);
lean_inc(v_pos_4340_);
lean_dec(v___x_4334_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4346_; 
if (v_isShared_4344_ == 0)
{
v___x_4346_ = v___x_4343_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_pos_4340_);
lean_ctor_set(v_reuseFailAlloc_4347_, 1, v_err_4341_);
v___x_4346_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
return v___x_4346_;
}
}
}
}
}
case 33:
{
uint8_t v_presentation_4349_; 
lean_dec_ref(v_config_3719_);
v_presentation_4349_ = lean_ctor_get_uint8(v_x_3720_, 0);
lean_dec_ref_known(v_x_3720_, 0);
switch(v_presentation_4349_)
{
case 0:
{
uint8_t v___x_4350_; uint8_t v___x_4351_; uint8_t v___x_4352_; lean_object* v___x_4353_; 
v___x_4350_ = 2;
v___x_4351_ = 1;
v___x_4352_ = 0;
lean_inc_ref(v_a_3721_);
v___x_4353_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4350_, v___x_4351_, v___x_4352_, v_a_3721_);
v___y_3733_ = v___x_4353_;
goto v___jp_3732_;
}
case 1:
{
uint8_t v___x_4354_; uint8_t v___x_4355_; uint8_t v___x_4356_; lean_object* v___x_4357_; 
v___x_4354_ = 0;
v___x_4355_ = 1;
v___x_4356_ = 0;
lean_inc_ref(v_a_3721_);
v___x_4357_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4354_, v___x_4355_, v___x_4356_, v_a_3721_);
v___y_3733_ = v___x_4357_;
goto v___jp_3732_;
}
case 2:
{
uint8_t v___x_4358_; uint8_t v___x_4359_; uint8_t v___x_4360_; lean_object* v___x_4361_; 
v___x_4358_ = 0;
v___x_4359_ = 1;
v___x_4360_ = 1;
lean_inc_ref(v_a_3721_);
v___x_4361_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4358_, v___x_4359_, v___x_4360_, v_a_3721_);
v___y_3733_ = v___x_4361_;
goto v___jp_3732_;
}
case 3:
{
uint8_t v___x_4362_; uint8_t v___x_4363_; uint8_t v___x_4364_; lean_object* v___x_4365_; 
v___x_4362_ = 0;
v___x_4363_ = 2;
v___x_4364_ = 0;
lean_inc_ref(v_a_3721_);
v___x_4365_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4362_, v___x_4363_, v___x_4364_, v_a_3721_);
v___y_3733_ = v___x_4365_;
goto v___jp_3732_;
}
default: 
{
uint8_t v___x_4366_; uint8_t v___x_4367_; uint8_t v___x_4368_; lean_object* v___x_4369_; 
v___x_4366_ = 0;
v___x_4367_ = 2;
v___x_4368_ = 1;
lean_inc_ref(v_a_3721_);
v___x_4369_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4366_, v___x_4367_, v___x_4368_, v_a_3721_);
v___y_3733_ = v___x_4369_;
goto v___jp_3732_;
}
}
}
case 34:
{
uint8_t v_presentation_4370_; 
lean_dec_ref(v_config_3719_);
v_presentation_4370_ = lean_ctor_get_uint8(v_x_3720_, 0);
lean_dec_ref_known(v_x_3720_, 0);
switch(v_presentation_4370_)
{
case 0:
{
uint8_t v___x_4371_; uint8_t v___x_4372_; uint8_t v___x_4373_; lean_object* v___x_4374_; 
v___x_4371_ = 2;
v___x_4372_ = 1;
v___x_4373_ = 0;
v___x_4374_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4371_, v___x_4372_, v___x_4373_, v_a_3721_);
return v___x_4374_;
}
case 1:
{
uint8_t v___x_4375_; uint8_t v___x_4376_; uint8_t v___x_4377_; lean_object* v___x_4378_; 
v___x_4375_ = 0;
v___x_4376_ = 1;
v___x_4377_ = 0;
v___x_4378_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4375_, v___x_4376_, v___x_4377_, v_a_3721_);
return v___x_4378_;
}
case 2:
{
uint8_t v___x_4379_; uint8_t v___x_4380_; uint8_t v___x_4381_; lean_object* v___x_4382_; 
v___x_4379_ = 0;
v___x_4380_ = 2;
v___x_4381_ = 1;
v___x_4382_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4379_, v___x_4380_, v___x_4381_, v_a_3721_);
return v___x_4382_;
}
case 3:
{
uint8_t v___x_4383_; uint8_t v___x_4384_; uint8_t v___x_4385_; lean_object* v___x_4386_; 
v___x_4383_ = 0;
v___x_4384_ = 2;
v___x_4385_ = 0;
v___x_4386_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4383_, v___x_4384_, v___x_4385_, v_a_3721_);
return v___x_4386_;
}
default: 
{
uint8_t v___x_4387_; uint8_t v___x_4388_; lean_object* v___x_4389_; 
v___x_4387_ = 0;
v___x_4388_ = 1;
v___x_4389_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4387_, v___x_4387_, v___x_4388_, v_a_3721_);
return v___x_4389_;
}
}
}
case 35:
{
uint8_t v_presentation_4390_; 
lean_dec_ref(v_config_3719_);
v_presentation_4390_ = lean_ctor_get_uint8(v_x_3720_, 0);
lean_dec_ref_known(v_x_3720_, 0);
switch(v_presentation_4390_)
{
case 0:
{
uint8_t v___x_4391_; uint8_t v___x_4392_; uint8_t v___x_4393_; lean_object* v___x_4394_; 
v___x_4391_ = 0;
v___x_4392_ = 1;
v___x_4393_ = 0;
v___x_4394_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4391_, v___x_4392_, v___x_4393_, v_a_3721_);
return v___x_4394_;
}
case 1:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; 
v___x_4395_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__3));
v___x_4396_ = l_Std_Internal_Parsec_String_pstring(v___x_4395_, v_a_3721_);
if (lean_obj_tag(v___x_4396_) == 0)
{
lean_object* v_pos_4397_; uint8_t v___x_4398_; uint8_t v___x_4399_; uint8_t v___x_4400_; lean_object* v___x_4401_; 
v_pos_4397_ = lean_ctor_get(v___x_4396_, 0);
lean_inc_n(v_pos_4397_, 2);
lean_dec_ref_known(v___x_4396_, 2);
v___x_4398_ = 0;
v___x_4399_ = 1;
v___x_4400_ = 1;
v___x_4401_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4398_, v___x_4399_, v___x_4400_, v_pos_4397_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_dec(v_pos_4397_);
return v___x_4401_;
}
else
{
lean_object* v_pos_4402_; lean_object* v_snd_4403_; lean_object* v_snd_4404_; uint8_t v_decide_4405_; 
v_pos_4402_ = lean_ctor_get(v___x_4401_, 0);
v_snd_4403_ = lean_ctor_get(v_pos_4397_, 1);
lean_inc(v_snd_4403_);
lean_dec(v_pos_4397_);
v_snd_4404_ = lean_ctor_get(v_pos_4402_, 1);
v_decide_4405_ = lean_nat_dec_eq(v_snd_4403_, v_snd_4404_);
lean_dec(v_snd_4403_);
if (v_decide_4405_ == 0)
{
return v___x_4401_;
}
else
{
lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4413_; 
lean_inc(v_pos_4402_);
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4413_ == 0)
{
lean_object* v_unused_4414_; lean_object* v_unused_4415_; 
v_unused_4414_ = lean_ctor_get(v___x_4401_, 1);
lean_dec(v_unused_4414_);
v_unused_4415_ = lean_ctor_get(v___x_4401_, 0);
lean_dec(v_unused_4415_);
v___x_4407_ = v___x_4401_;
v_isShared_4408_ = v_isSharedCheck_4413_;
goto v_resetjp_4406_;
}
else
{
lean_dec(v___x_4401_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4413_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4409_; lean_object* v___x_4411_; 
v___x_4409_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_4408_ == 0)
{
lean_ctor_set_tag(v___x_4407_, 0);
lean_ctor_set(v___x_4407_, 1, v___x_4409_);
v___x_4411_ = v___x_4407_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_pos_4402_);
lean_ctor_set(v_reuseFailAlloc_4412_, 1, v___x_4409_);
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
else
{
lean_object* v_pos_4416_; lean_object* v_err_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4424_; 
v_pos_4416_ = lean_ctor_get(v___x_4396_, 0);
v_err_4417_ = lean_ctor_get(v___x_4396_, 1);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4419_ = v___x_4396_;
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_err_4417_);
lean_inc(v_pos_4416_);
lean_dec(v___x_4396_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4422_; 
if (v_isShared_4420_ == 0)
{
v___x_4422_ = v___x_4419_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_pos_4416_);
lean_ctor_set(v_reuseFailAlloc_4423_, 1, v_err_4417_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
}
default: 
{
lean_object* v___x_4425_; lean_object* v___x_4426_; 
v___x_4425_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
lean_inc_ref(v_a_3721_);
v___x_4426_ = l_Std_Internal_Parsec_String_pstring(v___x_4425_, v_a_3721_);
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_object* v_pos_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4435_; 
lean_dec_ref(v_a_3721_);
v_pos_4427_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4435_ == 0)
{
lean_object* v_unused_4436_; 
v_unused_4436_ = lean_ctor_get(v___x_4426_, 1);
lean_dec(v_unused_4436_);
v___x_4429_ = v___x_4426_;
v_isShared_4430_ = v_isSharedCheck_4435_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_pos_4427_);
lean_dec(v___x_4426_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4435_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4431_; lean_object* v___x_4433_; 
v___x_4431_ = l_Std_Time_TimeZone_Offset_zero;
if (v_isShared_4430_ == 0)
{
lean_ctor_set(v___x_4429_, 1, v___x_4431_);
v___x_4433_ = v___x_4429_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_pos_4427_);
lean_ctor_set(v_reuseFailAlloc_4434_, 1, v___x_4431_);
v___x_4433_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
return v___x_4433_;
}
}
}
else
{
lean_object* v_pos_4437_; lean_object* v_err_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4451_; 
v_pos_4437_ = lean_ctor_get(v___x_4426_, 0);
v_err_4438_ = lean_ctor_get(v___x_4426_, 1);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4440_ = v___x_4426_;
v_isShared_4441_ = v_isSharedCheck_4451_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_err_4438_);
lean_inc(v_pos_4437_);
lean_dec(v___x_4426_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4451_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v_snd_4442_; lean_object* v_snd_4443_; uint8_t v_decide_4444_; 
v_snd_4442_ = lean_ctor_get(v_a_3721_, 1);
lean_inc(v_snd_4442_);
lean_dec_ref(v_a_3721_);
v_snd_4443_ = lean_ctor_get(v_pos_4437_, 1);
v_decide_4444_ = lean_nat_dec_eq(v_snd_4442_, v_snd_4443_);
lean_dec(v_snd_4442_);
if (v_decide_4444_ == 0)
{
lean_object* v___x_4446_; 
if (v_isShared_4441_ == 0)
{
v___x_4446_ = v___x_4440_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_pos_4437_);
lean_ctor_set(v_reuseFailAlloc_4447_, 1, v_err_4438_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
}
}
else
{
uint8_t v___x_4448_; uint8_t v___x_4449_; lean_object* v___x_4450_; 
lean_del_object(v___x_4440_);
lean_dec(v_err_4438_);
v___x_4448_ = 0;
v___x_4449_ = 2;
v___x_4450_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset(v___x_4448_, v___x_4449_, v_decide_4444_, v_pos_4437_);
return v___x_4450_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_4452_; 
lean_dec_ref(v_x_3720_);
lean_dec_ref(v_config_3719_);
v___x_4452_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseIdentifier(v_a_3721_);
return v___x_4452_;
}
}
v___jp_3722_:
{
lean_object* v_dateformat_3724_; lean_object* v_symbols_3725_; lean_object* v___x_3726_; 
v_dateformat_3724_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_3724_);
lean_dec_ref(v_config_3719_);
v_symbols_3725_ = lean_ctor_get(v_dateformat_3724_, 1);
lean_inc_ref(v_symbols_3725_);
lean_dec_ref(v_dateformat_3724_);
v___x_3726_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(v_symbols_3725_, v___y_3723_);
return v___x_3726_;
}
v___jp_3727_:
{
lean_object* v_dateformat_3729_; lean_object* v_symbols_3730_; lean_object* v___x_3731_; 
v_dateformat_3729_ = lean_ctor_get(v_config_3719_, 0);
lean_inc_ref(v_dateformat_3729_);
lean_dec_ref(v_config_3719_);
v_symbols_3730_ = lean_ctor_get(v_dateformat_3729_, 1);
lean_inc_ref(v_symbols_3730_);
lean_dec_ref(v_dateformat_3729_);
v___x_3731_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseQuarterNarrow(v_symbols_3730_, v___y_3728_);
return v___x_3731_;
}
v___jp_3732_:
{
if (lean_obj_tag(v___y_3733_) == 0)
{
lean_dec_ref(v_a_3721_);
return v___y_3733_;
}
else
{
lean_object* v_pos_3734_; lean_object* v_snd_3735_; lean_object* v_snd_3736_; uint8_t v_decide_3737_; 
v_pos_3734_ = lean_ctor_get(v___y_3733_, 0);
v_snd_3735_ = lean_ctor_get(v_a_3721_, 1);
lean_inc(v_snd_3735_);
lean_dec_ref(v_a_3721_);
v_snd_3736_ = lean_ctor_get(v_pos_3734_, 1);
v_decide_3737_ = lean_nat_dec_eq(v_snd_3735_, v_snd_3736_);
lean_dec(v_snd_3735_);
if (v_decide_3737_ == 0)
{
return v___y_3733_;
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
lean_inc(v_pos_3734_);
lean_dec_ref_known(v___y_3733_, 2);
v___x_3738_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__4));
v___x_3739_ = l_Std_Internal_Parsec_String_pstring(v___x_3738_, v_pos_3734_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_pos_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3748_; 
v_pos_3740_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3748_ == 0)
{
lean_object* v_unused_3749_; 
v_unused_3749_ = lean_ctor_get(v___x_3739_, 1);
lean_dec(v_unused_3749_);
v___x_3742_ = v___x_3739_;
v_isShared_3743_ = v_isSharedCheck_3748_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_pos_3740_);
lean_dec(v___x_3739_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3748_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3744_; lean_object* v___x_3746_; 
v___x_3744_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 1, v___x_3744_);
v___x_3746_ = v___x_3742_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_pos_3740_);
lean_ctor_set(v_reuseFailAlloc_3747_, 1, v___x_3744_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
else
{
lean_object* v_pos_3750_; lean_object* v_err_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
v_pos_3750_ = lean_ctor_get(v___x_3739_, 0);
v_err_3751_ = lean_ctor_get(v___x_3739_, 1);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v___x_3739_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_err_3751_);
lean_inc(v_pos_3750_);
lean_dec(v___x_3739_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_pos_3750_);
lean_ctor_set(v_reuseFailAlloc_3757_, 1, v_err_3751_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(lean_object* v_dateformat_4453_, lean_object* v_date_4454_, lean_object* v_part_4455_){
_start:
{
if (lean_obj_tag(v_part_4455_) == 0)
{
lean_object* v_val_4456_; 
lean_dec_ref(v_date_4454_);
v_val_4456_ = lean_ctor_get(v_part_4455_, 0);
lean_inc_ref(v_val_4456_);
lean_dec_ref_known(v_part_4455_, 1);
return v_val_4456_;
}
else
{
lean_object* v_modifier_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
v_modifier_4457_ = lean_ctor_get(v_part_4455_, 0);
lean_inc_ref(v_modifier_4457_);
lean_dec_ref_known(v_part_4455_, 1);
v___x_4458_ = l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier(v_modifier_4457_, v_dateformat_4453_, v_date_4454_);
v___x_4459_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_4453_, v_modifier_4457_, v___x_4458_);
return v___x_4459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate___boxed(lean_object* v_dateformat_4460_, lean_object* v_date_4461_, lean_object* v_part_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_4460_, v_date_4461_, v_part_4462_);
lean_dec_ref(v_dateformat_4460_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_FormatType_match__1_splitter___redArg(lean_object* v_x_4464_, lean_object* v_h__1_4465_, lean_object* v_h__2_4466_, lean_object* v_h__3_4467_){
_start:
{
if (lean_obj_tag(v_x_4464_) == 0)
{
lean_object* v___x_4468_; lean_object* v___x_4469_; 
lean_dec(v_h__2_4466_);
lean_dec(v_h__1_4465_);
v___x_4468_ = lean_box(0);
v___x_4469_ = lean_apply_1(v_h__3_4467_, v___x_4468_);
return v___x_4469_;
}
else
{
lean_object* v_head_4470_; 
lean_dec(v_h__3_4467_);
v_head_4470_ = lean_ctor_get(v_x_4464_, 0);
lean_inc(v_head_4470_);
if (lean_obj_tag(v_head_4470_) == 0)
{
lean_object* v_tail_4471_; lean_object* v_val_4472_; lean_object* v___x_4473_; 
lean_dec(v_h__1_4465_);
v_tail_4471_ = lean_ctor_get(v_x_4464_, 1);
lean_inc(v_tail_4471_);
lean_dec_ref_known(v_x_4464_, 2);
v_val_4472_ = lean_ctor_get(v_head_4470_, 0);
lean_inc_ref(v_val_4472_);
lean_dec_ref_known(v_head_4470_, 1);
v___x_4473_ = lean_apply_2(v_h__2_4466_, v_val_4472_, v_tail_4471_);
return v___x_4473_;
}
else
{
lean_object* v_tail_4474_; lean_object* v_modifier_4475_; lean_object* v___x_4476_; 
lean_dec(v_h__2_4466_);
v_tail_4474_ = lean_ctor_get(v_x_4464_, 1);
lean_inc(v_tail_4474_);
lean_dec_ref_known(v_x_4464_, 2);
v_modifier_4475_ = lean_ctor_get(v_head_4470_, 0);
lean_inc_ref(v_modifier_4475_);
lean_dec_ref_known(v_head_4470_, 1);
v___x_4476_ = lean_apply_2(v_h__1_4465_, v_modifier_4475_, v_tail_4474_);
return v___x_4476_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_FormatType_match__1_splitter(lean_object* v_motive_4477_, lean_object* v_x_4478_, lean_object* v_h__1_4479_, lean_object* v_h__2_4480_, lean_object* v_h__3_4481_){
_start:
{
if (lean_obj_tag(v_x_4478_) == 0)
{
lean_object* v___x_4482_; lean_object* v___x_4483_; 
lean_dec(v_h__2_4480_);
lean_dec(v_h__1_4479_);
v___x_4482_ = lean_box(0);
v___x_4483_ = lean_apply_1(v_h__3_4481_, v___x_4482_);
return v___x_4483_;
}
else
{
lean_object* v_head_4484_; 
lean_dec(v_h__3_4481_);
v_head_4484_ = lean_ctor_get(v_x_4478_, 0);
lean_inc(v_head_4484_);
if (lean_obj_tag(v_head_4484_) == 0)
{
lean_object* v_tail_4485_; lean_object* v_val_4486_; lean_object* v___x_4487_; 
lean_dec(v_h__1_4479_);
v_tail_4485_ = lean_ctor_get(v_x_4478_, 1);
lean_inc(v_tail_4485_);
lean_dec_ref_known(v_x_4478_, 2);
v_val_4486_ = lean_ctor_get(v_head_4484_, 0);
lean_inc_ref(v_val_4486_);
lean_dec_ref_known(v_head_4484_, 1);
v___x_4487_ = lean_apply_2(v_h__2_4480_, v_val_4486_, v_tail_4485_);
return v___x_4487_;
}
else
{
lean_object* v_tail_4488_; lean_object* v_modifier_4489_; lean_object* v___x_4490_; 
lean_dec(v_h__2_4480_);
v_tail_4488_ = lean_ctor_get(v_x_4478_, 1);
lean_inc(v_tail_4488_);
lean_dec_ref_known(v_x_4478_, 2);
v_modifier_4489_ = lean_ctor_get(v_head_4484_, 0);
lean_inc_ref(v_modifier_4489_);
lean_dec_ref_known(v_head_4484_, 1);
v___x_4490_ = lean_apply_2(v_h__1_4479_, v_modifier_4489_, v_tail_4488_);
return v___x_4490_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(lean_object* v_date_4491_, lean_object* v_modifier_4492_, lean_object* v_data_4493_){
_start:
{
switch(lean_obj_tag(v_modifier_4492_))
{
case 0:
{
lean_object* v_y_4494_; lean_object* v_u_4495_; lean_object* v_Y_4496_; lean_object* v_D_4497_; lean_object* v_M_4498_; lean_object* v_L_4499_; lean_object* v_d_4500_; lean_object* v_Q_4501_; lean_object* v_q_4502_; lean_object* v_w_4503_; lean_object* v_W_4504_; lean_object* v_E_4505_; lean_object* v_e_4506_; lean_object* v_c_4507_; lean_object* v_F_4508_; lean_object* v_a_4509_; lean_object* v_b_4510_; lean_object* v_B_4511_; lean_object* v_h_4512_; lean_object* v_K_4513_; lean_object* v_k_4514_; lean_object* v_H_4515_; lean_object* v_m_4516_; lean_object* v_s_4517_; lean_object* v_S_4518_; lean_object* v_A_4519_; lean_object* v_n_4520_; lean_object* v_N_4521_; lean_object* v_V_4522_; lean_object* v_z_4523_; lean_object* v_zabbrev_4524_; lean_object* v_v_4525_; lean_object* v_O_4526_; lean_object* v_X_4527_; lean_object* v_x_4528_; lean_object* v_Z_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4537_; 
lean_dec_ref_known(v_modifier_4492_, 0);
v_y_4494_ = lean_ctor_get(v_date_4491_, 1);
v_u_4495_ = lean_ctor_get(v_date_4491_, 2);
v_Y_4496_ = lean_ctor_get(v_date_4491_, 3);
v_D_4497_ = lean_ctor_get(v_date_4491_, 4);
v_M_4498_ = lean_ctor_get(v_date_4491_, 5);
v_L_4499_ = lean_ctor_get(v_date_4491_, 6);
v_d_4500_ = lean_ctor_get(v_date_4491_, 7);
v_Q_4501_ = lean_ctor_get(v_date_4491_, 8);
v_q_4502_ = lean_ctor_get(v_date_4491_, 9);
v_w_4503_ = lean_ctor_get(v_date_4491_, 10);
v_W_4504_ = lean_ctor_get(v_date_4491_, 11);
v_E_4505_ = lean_ctor_get(v_date_4491_, 12);
v_e_4506_ = lean_ctor_get(v_date_4491_, 13);
v_c_4507_ = lean_ctor_get(v_date_4491_, 14);
v_F_4508_ = lean_ctor_get(v_date_4491_, 15);
v_a_4509_ = lean_ctor_get(v_date_4491_, 16);
v_b_4510_ = lean_ctor_get(v_date_4491_, 17);
v_B_4511_ = lean_ctor_get(v_date_4491_, 18);
v_h_4512_ = lean_ctor_get(v_date_4491_, 19);
v_K_4513_ = lean_ctor_get(v_date_4491_, 20);
v_k_4514_ = lean_ctor_get(v_date_4491_, 21);
v_H_4515_ = lean_ctor_get(v_date_4491_, 22);
v_m_4516_ = lean_ctor_get(v_date_4491_, 23);
v_s_4517_ = lean_ctor_get(v_date_4491_, 24);
v_S_4518_ = lean_ctor_get(v_date_4491_, 25);
v_A_4519_ = lean_ctor_get(v_date_4491_, 26);
v_n_4520_ = lean_ctor_get(v_date_4491_, 27);
v_N_4521_ = lean_ctor_get(v_date_4491_, 28);
v_V_4522_ = lean_ctor_get(v_date_4491_, 29);
v_z_4523_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_4524_ = lean_ctor_get(v_date_4491_, 31);
v_v_4525_ = lean_ctor_get(v_date_4491_, 32);
v_O_4526_ = lean_ctor_get(v_date_4491_, 33);
v_X_4527_ = lean_ctor_get(v_date_4491_, 34);
v_x_4528_ = lean_ctor_get(v_date_4491_, 35);
v_Z_4529_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_4537_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_4537_ == 0)
{
lean_object* v_unused_4538_; 
v_unused_4538_ = lean_ctor_get(v_date_4491_, 0);
lean_dec(v_unused_4538_);
v___x_4531_ = v_date_4491_;
v_isShared_4532_ = v_isSharedCheck_4537_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_Z_4529_);
lean_inc(v_x_4528_);
lean_inc(v_X_4527_);
lean_inc(v_O_4526_);
lean_inc(v_v_4525_);
lean_inc(v_zabbrev_4524_);
lean_inc(v_z_4523_);
lean_inc(v_V_4522_);
lean_inc(v_N_4521_);
lean_inc(v_n_4520_);
lean_inc(v_A_4519_);
lean_inc(v_S_4518_);
lean_inc(v_s_4517_);
lean_inc(v_m_4516_);
lean_inc(v_H_4515_);
lean_inc(v_k_4514_);
lean_inc(v_K_4513_);
lean_inc(v_h_4512_);
lean_inc(v_B_4511_);
lean_inc(v_b_4510_);
lean_inc(v_a_4509_);
lean_inc(v_F_4508_);
lean_inc(v_c_4507_);
lean_inc(v_e_4506_);
lean_inc(v_E_4505_);
lean_inc(v_W_4504_);
lean_inc(v_w_4503_);
lean_inc(v_q_4502_);
lean_inc(v_Q_4501_);
lean_inc(v_d_4500_);
lean_inc(v_L_4499_);
lean_inc(v_M_4498_);
lean_inc(v_D_4497_);
lean_inc(v_Y_4496_);
lean_inc(v_u_4495_);
lean_inc(v_y_4494_);
lean_dec(v_date_4491_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4537_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4533_; lean_object* v___x_4535_; 
v___x_4533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4533_, 0, v_data_4493_);
if (v_isShared_4532_ == 0)
{
lean_ctor_set(v___x_4531_, 0, v___x_4533_);
v___x_4535_ = v___x_4531_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v___x_4533_);
lean_ctor_set(v_reuseFailAlloc_4536_, 1, v_y_4494_);
lean_ctor_set(v_reuseFailAlloc_4536_, 2, v_u_4495_);
lean_ctor_set(v_reuseFailAlloc_4536_, 3, v_Y_4496_);
lean_ctor_set(v_reuseFailAlloc_4536_, 4, v_D_4497_);
lean_ctor_set(v_reuseFailAlloc_4536_, 5, v_M_4498_);
lean_ctor_set(v_reuseFailAlloc_4536_, 6, v_L_4499_);
lean_ctor_set(v_reuseFailAlloc_4536_, 7, v_d_4500_);
lean_ctor_set(v_reuseFailAlloc_4536_, 8, v_Q_4501_);
lean_ctor_set(v_reuseFailAlloc_4536_, 9, v_q_4502_);
lean_ctor_set(v_reuseFailAlloc_4536_, 10, v_w_4503_);
lean_ctor_set(v_reuseFailAlloc_4536_, 11, v_W_4504_);
lean_ctor_set(v_reuseFailAlloc_4536_, 12, v_E_4505_);
lean_ctor_set(v_reuseFailAlloc_4536_, 13, v_e_4506_);
lean_ctor_set(v_reuseFailAlloc_4536_, 14, v_c_4507_);
lean_ctor_set(v_reuseFailAlloc_4536_, 15, v_F_4508_);
lean_ctor_set(v_reuseFailAlloc_4536_, 16, v_a_4509_);
lean_ctor_set(v_reuseFailAlloc_4536_, 17, v_b_4510_);
lean_ctor_set(v_reuseFailAlloc_4536_, 18, v_B_4511_);
lean_ctor_set(v_reuseFailAlloc_4536_, 19, v_h_4512_);
lean_ctor_set(v_reuseFailAlloc_4536_, 20, v_K_4513_);
lean_ctor_set(v_reuseFailAlloc_4536_, 21, v_k_4514_);
lean_ctor_set(v_reuseFailAlloc_4536_, 22, v_H_4515_);
lean_ctor_set(v_reuseFailAlloc_4536_, 23, v_m_4516_);
lean_ctor_set(v_reuseFailAlloc_4536_, 24, v_s_4517_);
lean_ctor_set(v_reuseFailAlloc_4536_, 25, v_S_4518_);
lean_ctor_set(v_reuseFailAlloc_4536_, 26, v_A_4519_);
lean_ctor_set(v_reuseFailAlloc_4536_, 27, v_n_4520_);
lean_ctor_set(v_reuseFailAlloc_4536_, 28, v_N_4521_);
lean_ctor_set(v_reuseFailAlloc_4536_, 29, v_V_4522_);
lean_ctor_set(v_reuseFailAlloc_4536_, 30, v_z_4523_);
lean_ctor_set(v_reuseFailAlloc_4536_, 31, v_zabbrev_4524_);
lean_ctor_set(v_reuseFailAlloc_4536_, 32, v_v_4525_);
lean_ctor_set(v_reuseFailAlloc_4536_, 33, v_O_4526_);
lean_ctor_set(v_reuseFailAlloc_4536_, 34, v_X_4527_);
lean_ctor_set(v_reuseFailAlloc_4536_, 35, v_x_4528_);
lean_ctor_set(v_reuseFailAlloc_4536_, 36, v_Z_4529_);
v___x_4535_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
return v___x_4535_;
}
}
}
case 1:
{
lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4589_; 
v_isSharedCheck_4589_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_4589_ == 0)
{
lean_object* v_unused_4590_; 
v_unused_4590_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_4590_);
v___x_4540_ = v_modifier_4492_;
v_isShared_4541_ = v_isSharedCheck_4589_;
goto v_resetjp_4539_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4589_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
lean_object* v_G_4542_; lean_object* v_y_4543_; lean_object* v_Y_4544_; lean_object* v_D_4545_; lean_object* v_M_4546_; lean_object* v_L_4547_; lean_object* v_d_4548_; lean_object* v_Q_4549_; lean_object* v_q_4550_; lean_object* v_w_4551_; lean_object* v_W_4552_; lean_object* v_E_4553_; lean_object* v_e_4554_; lean_object* v_c_4555_; lean_object* v_F_4556_; lean_object* v_a_4557_; lean_object* v_b_4558_; lean_object* v_B_4559_; lean_object* v_h_4560_; lean_object* v_K_4561_; lean_object* v_k_4562_; lean_object* v_H_4563_; lean_object* v_m_4564_; lean_object* v_s_4565_; lean_object* v_S_4566_; lean_object* v_A_4567_; lean_object* v_n_4568_; lean_object* v_N_4569_; lean_object* v_V_4570_; lean_object* v_z_4571_; lean_object* v_zabbrev_4572_; lean_object* v_v_4573_; lean_object* v_O_4574_; lean_object* v_X_4575_; lean_object* v_x_4576_; lean_object* v_Z_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4587_; 
v_G_4542_ = lean_ctor_get(v_date_4491_, 0);
v_y_4543_ = lean_ctor_get(v_date_4491_, 1);
v_Y_4544_ = lean_ctor_get(v_date_4491_, 3);
v_D_4545_ = lean_ctor_get(v_date_4491_, 4);
v_M_4546_ = lean_ctor_get(v_date_4491_, 5);
v_L_4547_ = lean_ctor_get(v_date_4491_, 6);
v_d_4548_ = lean_ctor_get(v_date_4491_, 7);
v_Q_4549_ = lean_ctor_get(v_date_4491_, 8);
v_q_4550_ = lean_ctor_get(v_date_4491_, 9);
v_w_4551_ = lean_ctor_get(v_date_4491_, 10);
v_W_4552_ = lean_ctor_get(v_date_4491_, 11);
v_E_4553_ = lean_ctor_get(v_date_4491_, 12);
v_e_4554_ = lean_ctor_get(v_date_4491_, 13);
v_c_4555_ = lean_ctor_get(v_date_4491_, 14);
v_F_4556_ = lean_ctor_get(v_date_4491_, 15);
v_a_4557_ = lean_ctor_get(v_date_4491_, 16);
v_b_4558_ = lean_ctor_get(v_date_4491_, 17);
v_B_4559_ = lean_ctor_get(v_date_4491_, 18);
v_h_4560_ = lean_ctor_get(v_date_4491_, 19);
v_K_4561_ = lean_ctor_get(v_date_4491_, 20);
v_k_4562_ = lean_ctor_get(v_date_4491_, 21);
v_H_4563_ = lean_ctor_get(v_date_4491_, 22);
v_m_4564_ = lean_ctor_get(v_date_4491_, 23);
v_s_4565_ = lean_ctor_get(v_date_4491_, 24);
v_S_4566_ = lean_ctor_get(v_date_4491_, 25);
v_A_4567_ = lean_ctor_get(v_date_4491_, 26);
v_n_4568_ = lean_ctor_get(v_date_4491_, 27);
v_N_4569_ = lean_ctor_get(v_date_4491_, 28);
v_V_4570_ = lean_ctor_get(v_date_4491_, 29);
v_z_4571_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_4572_ = lean_ctor_get(v_date_4491_, 31);
v_v_4573_ = lean_ctor_get(v_date_4491_, 32);
v_O_4574_ = lean_ctor_get(v_date_4491_, 33);
v_X_4575_ = lean_ctor_get(v_date_4491_, 34);
v_x_4576_ = lean_ctor_get(v_date_4491_, 35);
v_Z_4577_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_4587_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_4587_ == 0)
{
lean_object* v_unused_4588_; 
v_unused_4588_ = lean_ctor_get(v_date_4491_, 2);
lean_dec(v_unused_4588_);
v___x_4579_ = v_date_4491_;
v_isShared_4580_ = v_isSharedCheck_4587_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_Z_4577_);
lean_inc(v_x_4576_);
lean_inc(v_X_4575_);
lean_inc(v_O_4574_);
lean_inc(v_v_4573_);
lean_inc(v_zabbrev_4572_);
lean_inc(v_z_4571_);
lean_inc(v_V_4570_);
lean_inc(v_N_4569_);
lean_inc(v_n_4568_);
lean_inc(v_A_4567_);
lean_inc(v_S_4566_);
lean_inc(v_s_4565_);
lean_inc(v_m_4564_);
lean_inc(v_H_4563_);
lean_inc(v_k_4562_);
lean_inc(v_K_4561_);
lean_inc(v_h_4560_);
lean_inc(v_B_4559_);
lean_inc(v_b_4558_);
lean_inc(v_a_4557_);
lean_inc(v_F_4556_);
lean_inc(v_c_4555_);
lean_inc(v_e_4554_);
lean_inc(v_E_4553_);
lean_inc(v_W_4552_);
lean_inc(v_w_4551_);
lean_inc(v_q_4550_);
lean_inc(v_Q_4549_);
lean_inc(v_d_4548_);
lean_inc(v_L_4547_);
lean_inc(v_M_4546_);
lean_inc(v_D_4545_);
lean_inc(v_Y_4544_);
lean_inc(v_y_4543_);
lean_inc(v_G_4542_);
lean_dec(v_date_4491_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4587_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4582_; 
if (v_isShared_4541_ == 0)
{
lean_ctor_set(v___x_4540_, 0, v_data_4493_);
v___x_4582_ = v___x_4540_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v_data_4493_);
v___x_4582_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
lean_object* v___x_4584_; 
if (v_isShared_4580_ == 0)
{
lean_ctor_set(v___x_4579_, 2, v___x_4582_);
v___x_4584_ = v___x_4579_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_G_4542_);
lean_ctor_set(v_reuseFailAlloc_4585_, 1, v_y_4543_);
lean_ctor_set(v_reuseFailAlloc_4585_, 2, v___x_4582_);
lean_ctor_set(v_reuseFailAlloc_4585_, 3, v_Y_4544_);
lean_ctor_set(v_reuseFailAlloc_4585_, 4, v_D_4545_);
lean_ctor_set(v_reuseFailAlloc_4585_, 5, v_M_4546_);
lean_ctor_set(v_reuseFailAlloc_4585_, 6, v_L_4547_);
lean_ctor_set(v_reuseFailAlloc_4585_, 7, v_d_4548_);
lean_ctor_set(v_reuseFailAlloc_4585_, 8, v_Q_4549_);
lean_ctor_set(v_reuseFailAlloc_4585_, 9, v_q_4550_);
lean_ctor_set(v_reuseFailAlloc_4585_, 10, v_w_4551_);
lean_ctor_set(v_reuseFailAlloc_4585_, 11, v_W_4552_);
lean_ctor_set(v_reuseFailAlloc_4585_, 12, v_E_4553_);
lean_ctor_set(v_reuseFailAlloc_4585_, 13, v_e_4554_);
lean_ctor_set(v_reuseFailAlloc_4585_, 14, v_c_4555_);
lean_ctor_set(v_reuseFailAlloc_4585_, 15, v_F_4556_);
lean_ctor_set(v_reuseFailAlloc_4585_, 16, v_a_4557_);
lean_ctor_set(v_reuseFailAlloc_4585_, 17, v_b_4558_);
lean_ctor_set(v_reuseFailAlloc_4585_, 18, v_B_4559_);
lean_ctor_set(v_reuseFailAlloc_4585_, 19, v_h_4560_);
lean_ctor_set(v_reuseFailAlloc_4585_, 20, v_K_4561_);
lean_ctor_set(v_reuseFailAlloc_4585_, 21, v_k_4562_);
lean_ctor_set(v_reuseFailAlloc_4585_, 22, v_H_4563_);
lean_ctor_set(v_reuseFailAlloc_4585_, 23, v_m_4564_);
lean_ctor_set(v_reuseFailAlloc_4585_, 24, v_s_4565_);
lean_ctor_set(v_reuseFailAlloc_4585_, 25, v_S_4566_);
lean_ctor_set(v_reuseFailAlloc_4585_, 26, v_A_4567_);
lean_ctor_set(v_reuseFailAlloc_4585_, 27, v_n_4568_);
lean_ctor_set(v_reuseFailAlloc_4585_, 28, v_N_4569_);
lean_ctor_set(v_reuseFailAlloc_4585_, 29, v_V_4570_);
lean_ctor_set(v_reuseFailAlloc_4585_, 30, v_z_4571_);
lean_ctor_set(v_reuseFailAlloc_4585_, 31, v_zabbrev_4572_);
lean_ctor_set(v_reuseFailAlloc_4585_, 32, v_v_4573_);
lean_ctor_set(v_reuseFailAlloc_4585_, 33, v_O_4574_);
lean_ctor_set(v_reuseFailAlloc_4585_, 34, v_X_4575_);
lean_ctor_set(v_reuseFailAlloc_4585_, 35, v_x_4576_);
lean_ctor_set(v_reuseFailAlloc_4585_, 36, v_Z_4577_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
}
}
case 2:
{
lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4641_; 
v_isSharedCheck_4641_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_4641_ == 0)
{
lean_object* v_unused_4642_; 
v_unused_4642_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_4642_);
v___x_4592_ = v_modifier_4492_;
v_isShared_4593_ = v_isSharedCheck_4641_;
goto v_resetjp_4591_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4641_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v_G_4594_; lean_object* v_u_4595_; lean_object* v_Y_4596_; lean_object* v_D_4597_; lean_object* v_M_4598_; lean_object* v_L_4599_; lean_object* v_d_4600_; lean_object* v_Q_4601_; lean_object* v_q_4602_; lean_object* v_w_4603_; lean_object* v_W_4604_; lean_object* v_E_4605_; lean_object* v_e_4606_; lean_object* v_c_4607_; lean_object* v_F_4608_; lean_object* v_a_4609_; lean_object* v_b_4610_; lean_object* v_B_4611_; lean_object* v_h_4612_; lean_object* v_K_4613_; lean_object* v_k_4614_; lean_object* v_H_4615_; lean_object* v_m_4616_; lean_object* v_s_4617_; lean_object* v_S_4618_; lean_object* v_A_4619_; lean_object* v_n_4620_; lean_object* v_N_4621_; lean_object* v_V_4622_; lean_object* v_z_4623_; lean_object* v_zabbrev_4624_; lean_object* v_v_4625_; lean_object* v_O_4626_; lean_object* v_X_4627_; lean_object* v_x_4628_; lean_object* v_Z_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4639_; 
v_G_4594_ = lean_ctor_get(v_date_4491_, 0);
v_u_4595_ = lean_ctor_get(v_date_4491_, 2);
v_Y_4596_ = lean_ctor_get(v_date_4491_, 3);
v_D_4597_ = lean_ctor_get(v_date_4491_, 4);
v_M_4598_ = lean_ctor_get(v_date_4491_, 5);
v_L_4599_ = lean_ctor_get(v_date_4491_, 6);
v_d_4600_ = lean_ctor_get(v_date_4491_, 7);
v_Q_4601_ = lean_ctor_get(v_date_4491_, 8);
v_q_4602_ = lean_ctor_get(v_date_4491_, 9);
v_w_4603_ = lean_ctor_get(v_date_4491_, 10);
v_W_4604_ = lean_ctor_get(v_date_4491_, 11);
v_E_4605_ = lean_ctor_get(v_date_4491_, 12);
v_e_4606_ = lean_ctor_get(v_date_4491_, 13);
v_c_4607_ = lean_ctor_get(v_date_4491_, 14);
v_F_4608_ = lean_ctor_get(v_date_4491_, 15);
v_a_4609_ = lean_ctor_get(v_date_4491_, 16);
v_b_4610_ = lean_ctor_get(v_date_4491_, 17);
v_B_4611_ = lean_ctor_get(v_date_4491_, 18);
v_h_4612_ = lean_ctor_get(v_date_4491_, 19);
v_K_4613_ = lean_ctor_get(v_date_4491_, 20);
v_k_4614_ = lean_ctor_get(v_date_4491_, 21);
v_H_4615_ = lean_ctor_get(v_date_4491_, 22);
v_m_4616_ = lean_ctor_get(v_date_4491_, 23);
v_s_4617_ = lean_ctor_get(v_date_4491_, 24);
v_S_4618_ = lean_ctor_get(v_date_4491_, 25);
v_A_4619_ = lean_ctor_get(v_date_4491_, 26);
v_n_4620_ = lean_ctor_get(v_date_4491_, 27);
v_N_4621_ = lean_ctor_get(v_date_4491_, 28);
v_V_4622_ = lean_ctor_get(v_date_4491_, 29);
v_z_4623_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_4624_ = lean_ctor_get(v_date_4491_, 31);
v_v_4625_ = lean_ctor_get(v_date_4491_, 32);
v_O_4626_ = lean_ctor_get(v_date_4491_, 33);
v_X_4627_ = lean_ctor_get(v_date_4491_, 34);
v_x_4628_ = lean_ctor_get(v_date_4491_, 35);
v_Z_4629_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_4639_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_4639_ == 0)
{
lean_object* v_unused_4640_; 
v_unused_4640_ = lean_ctor_get(v_date_4491_, 1);
lean_dec(v_unused_4640_);
v___x_4631_ = v_date_4491_;
v_isShared_4632_ = v_isSharedCheck_4639_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_Z_4629_);
lean_inc(v_x_4628_);
lean_inc(v_X_4627_);
lean_inc(v_O_4626_);
lean_inc(v_v_4625_);
lean_inc(v_zabbrev_4624_);
lean_inc(v_z_4623_);
lean_inc(v_V_4622_);
lean_inc(v_N_4621_);
lean_inc(v_n_4620_);
lean_inc(v_A_4619_);
lean_inc(v_S_4618_);
lean_inc(v_s_4617_);
lean_inc(v_m_4616_);
lean_inc(v_H_4615_);
lean_inc(v_k_4614_);
lean_inc(v_K_4613_);
lean_inc(v_h_4612_);
lean_inc(v_B_4611_);
lean_inc(v_b_4610_);
lean_inc(v_a_4609_);
lean_inc(v_F_4608_);
lean_inc(v_c_4607_);
lean_inc(v_e_4606_);
lean_inc(v_E_4605_);
lean_inc(v_W_4604_);
lean_inc(v_w_4603_);
lean_inc(v_q_4602_);
lean_inc(v_Q_4601_);
lean_inc(v_d_4600_);
lean_inc(v_L_4599_);
lean_inc(v_M_4598_);
lean_inc(v_D_4597_);
lean_inc(v_Y_4596_);
lean_inc(v_u_4595_);
lean_inc(v_G_4594_);
lean_dec(v_date_4491_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4639_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v___x_4634_; 
if (v_isShared_4593_ == 0)
{
lean_ctor_set_tag(v___x_4592_, 1);
lean_ctor_set(v___x_4592_, 0, v_data_4493_);
v___x_4634_ = v___x_4592_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_data_4493_);
v___x_4634_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
lean_object* v___x_4636_; 
if (v_isShared_4632_ == 0)
{
lean_ctor_set(v___x_4631_, 1, v___x_4634_);
v___x_4636_ = v___x_4631_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_G_4594_);
lean_ctor_set(v_reuseFailAlloc_4637_, 1, v___x_4634_);
lean_ctor_set(v_reuseFailAlloc_4637_, 2, v_u_4595_);
lean_ctor_set(v_reuseFailAlloc_4637_, 3, v_Y_4596_);
lean_ctor_set(v_reuseFailAlloc_4637_, 4, v_D_4597_);
lean_ctor_set(v_reuseFailAlloc_4637_, 5, v_M_4598_);
lean_ctor_set(v_reuseFailAlloc_4637_, 6, v_L_4599_);
lean_ctor_set(v_reuseFailAlloc_4637_, 7, v_d_4600_);
lean_ctor_set(v_reuseFailAlloc_4637_, 8, v_Q_4601_);
lean_ctor_set(v_reuseFailAlloc_4637_, 9, v_q_4602_);
lean_ctor_set(v_reuseFailAlloc_4637_, 10, v_w_4603_);
lean_ctor_set(v_reuseFailAlloc_4637_, 11, v_W_4604_);
lean_ctor_set(v_reuseFailAlloc_4637_, 12, v_E_4605_);
lean_ctor_set(v_reuseFailAlloc_4637_, 13, v_e_4606_);
lean_ctor_set(v_reuseFailAlloc_4637_, 14, v_c_4607_);
lean_ctor_set(v_reuseFailAlloc_4637_, 15, v_F_4608_);
lean_ctor_set(v_reuseFailAlloc_4637_, 16, v_a_4609_);
lean_ctor_set(v_reuseFailAlloc_4637_, 17, v_b_4610_);
lean_ctor_set(v_reuseFailAlloc_4637_, 18, v_B_4611_);
lean_ctor_set(v_reuseFailAlloc_4637_, 19, v_h_4612_);
lean_ctor_set(v_reuseFailAlloc_4637_, 20, v_K_4613_);
lean_ctor_set(v_reuseFailAlloc_4637_, 21, v_k_4614_);
lean_ctor_set(v_reuseFailAlloc_4637_, 22, v_H_4615_);
lean_ctor_set(v_reuseFailAlloc_4637_, 23, v_m_4616_);
lean_ctor_set(v_reuseFailAlloc_4637_, 24, v_s_4617_);
lean_ctor_set(v_reuseFailAlloc_4637_, 25, v_S_4618_);
lean_ctor_set(v_reuseFailAlloc_4637_, 26, v_A_4619_);
lean_ctor_set(v_reuseFailAlloc_4637_, 27, v_n_4620_);
lean_ctor_set(v_reuseFailAlloc_4637_, 28, v_N_4621_);
lean_ctor_set(v_reuseFailAlloc_4637_, 29, v_V_4622_);
lean_ctor_set(v_reuseFailAlloc_4637_, 30, v_z_4623_);
lean_ctor_set(v_reuseFailAlloc_4637_, 31, v_zabbrev_4624_);
lean_ctor_set(v_reuseFailAlloc_4637_, 32, v_v_4625_);
lean_ctor_set(v_reuseFailAlloc_4637_, 33, v_O_4626_);
lean_ctor_set(v_reuseFailAlloc_4637_, 34, v_X_4627_);
lean_ctor_set(v_reuseFailAlloc_4637_, 35, v_x_4628_);
lean_ctor_set(v_reuseFailAlloc_4637_, 36, v_Z_4629_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
}
}
}
case 3:
{
lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4693_; 
v_isSharedCheck_4693_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_4693_ == 0)
{
lean_object* v_unused_4694_; 
v_unused_4694_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_4694_);
v___x_4644_ = v_modifier_4492_;
v_isShared_4645_ = v_isSharedCheck_4693_;
goto v_resetjp_4643_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_4644_ = lean_box(0);
v_isShared_4645_ = v_isSharedCheck_4693_;
goto v_resetjp_4643_;
}
v_resetjp_4643_:
{
lean_object* v_G_4646_; lean_object* v_y_4647_; lean_object* v_u_4648_; lean_object* v_Y_4649_; lean_object* v_M_4650_; lean_object* v_L_4651_; lean_object* v_d_4652_; lean_object* v_Q_4653_; lean_object* v_q_4654_; lean_object* v_w_4655_; lean_object* v_W_4656_; lean_object* v_E_4657_; lean_object* v_e_4658_; lean_object* v_c_4659_; lean_object* v_F_4660_; lean_object* v_a_4661_; lean_object* v_b_4662_; lean_object* v_B_4663_; lean_object* v_h_4664_; lean_object* v_K_4665_; lean_object* v_k_4666_; lean_object* v_H_4667_; lean_object* v_m_4668_; lean_object* v_s_4669_; lean_object* v_S_4670_; lean_object* v_A_4671_; lean_object* v_n_4672_; lean_object* v_N_4673_; lean_object* v_V_4674_; lean_object* v_z_4675_; lean_object* v_zabbrev_4676_; lean_object* v_v_4677_; lean_object* v_O_4678_; lean_object* v_X_4679_; lean_object* v_x_4680_; lean_object* v_Z_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4691_; 
v_G_4646_ = lean_ctor_get(v_date_4491_, 0);
v_y_4647_ = lean_ctor_get(v_date_4491_, 1);
v_u_4648_ = lean_ctor_get(v_date_4491_, 2);
v_Y_4649_ = lean_ctor_get(v_date_4491_, 3);
v_M_4650_ = lean_ctor_get(v_date_4491_, 5);
v_L_4651_ = lean_ctor_get(v_date_4491_, 6);
v_d_4652_ = lean_ctor_get(v_date_4491_, 7);
v_Q_4653_ = lean_ctor_get(v_date_4491_, 8);
v_q_4654_ = lean_ctor_get(v_date_4491_, 9);
v_w_4655_ = lean_ctor_get(v_date_4491_, 10);
v_W_4656_ = lean_ctor_get(v_date_4491_, 11);
v_E_4657_ = lean_ctor_get(v_date_4491_, 12);
v_e_4658_ = lean_ctor_get(v_date_4491_, 13);
v_c_4659_ = lean_ctor_get(v_date_4491_, 14);
v_F_4660_ = lean_ctor_get(v_date_4491_, 15);
v_a_4661_ = lean_ctor_get(v_date_4491_, 16);
v_b_4662_ = lean_ctor_get(v_date_4491_, 17);
v_B_4663_ = lean_ctor_get(v_date_4491_, 18);
v_h_4664_ = lean_ctor_get(v_date_4491_, 19);
v_K_4665_ = lean_ctor_get(v_date_4491_, 20);
v_k_4666_ = lean_ctor_get(v_date_4491_, 21);
v_H_4667_ = lean_ctor_get(v_date_4491_, 22);
v_m_4668_ = lean_ctor_get(v_date_4491_, 23);
v_s_4669_ = lean_ctor_get(v_date_4491_, 24);
v_S_4670_ = lean_ctor_get(v_date_4491_, 25);
v_A_4671_ = lean_ctor_get(v_date_4491_, 26);
v_n_4672_ = lean_ctor_get(v_date_4491_, 27);
v_N_4673_ = lean_ctor_get(v_date_4491_, 28);
v_V_4674_ = lean_ctor_get(v_date_4491_, 29);
v_z_4675_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_4676_ = lean_ctor_get(v_date_4491_, 31);
v_v_4677_ = lean_ctor_get(v_date_4491_, 32);
v_O_4678_ = lean_ctor_get(v_date_4491_, 33);
v_X_4679_ = lean_ctor_get(v_date_4491_, 34);
v_x_4680_ = lean_ctor_get(v_date_4491_, 35);
v_Z_4681_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_4691_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_4691_ == 0)
{
lean_object* v_unused_4692_; 
v_unused_4692_ = lean_ctor_get(v_date_4491_, 4);
lean_dec(v_unused_4692_);
v___x_4683_ = v_date_4491_;
v_isShared_4684_ = v_isSharedCheck_4691_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_Z_4681_);
lean_inc(v_x_4680_);
lean_inc(v_X_4679_);
lean_inc(v_O_4678_);
lean_inc(v_v_4677_);
lean_inc(v_zabbrev_4676_);
lean_inc(v_z_4675_);
lean_inc(v_V_4674_);
lean_inc(v_N_4673_);
lean_inc(v_n_4672_);
lean_inc(v_A_4671_);
lean_inc(v_S_4670_);
lean_inc(v_s_4669_);
lean_inc(v_m_4668_);
lean_inc(v_H_4667_);
lean_inc(v_k_4666_);
lean_inc(v_K_4665_);
lean_inc(v_h_4664_);
lean_inc(v_B_4663_);
lean_inc(v_b_4662_);
lean_inc(v_a_4661_);
lean_inc(v_F_4660_);
lean_inc(v_c_4659_);
lean_inc(v_e_4658_);
lean_inc(v_E_4657_);
lean_inc(v_W_4656_);
lean_inc(v_w_4655_);
lean_inc(v_q_4654_);
lean_inc(v_Q_4653_);
lean_inc(v_d_4652_);
lean_inc(v_L_4651_);
lean_inc(v_M_4650_);
lean_inc(v_Y_4649_);
lean_inc(v_u_4648_);
lean_inc(v_y_4647_);
lean_inc(v_G_4646_);
lean_dec(v_date_4491_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4691_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4686_; 
if (v_isShared_4645_ == 0)
{
lean_ctor_set_tag(v___x_4644_, 1);
lean_ctor_set(v___x_4644_, 0, v_data_4493_);
v___x_4686_ = v___x_4644_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_data_4493_);
v___x_4686_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
lean_object* v___x_4688_; 
if (v_isShared_4684_ == 0)
{
lean_ctor_set(v___x_4683_, 4, v___x_4686_);
v___x_4688_ = v___x_4683_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_G_4646_);
lean_ctor_set(v_reuseFailAlloc_4689_, 1, v_y_4647_);
lean_ctor_set(v_reuseFailAlloc_4689_, 2, v_u_4648_);
lean_ctor_set(v_reuseFailAlloc_4689_, 3, v_Y_4649_);
lean_ctor_set(v_reuseFailAlloc_4689_, 4, v___x_4686_);
lean_ctor_set(v_reuseFailAlloc_4689_, 5, v_M_4650_);
lean_ctor_set(v_reuseFailAlloc_4689_, 6, v_L_4651_);
lean_ctor_set(v_reuseFailAlloc_4689_, 7, v_d_4652_);
lean_ctor_set(v_reuseFailAlloc_4689_, 8, v_Q_4653_);
lean_ctor_set(v_reuseFailAlloc_4689_, 9, v_q_4654_);
lean_ctor_set(v_reuseFailAlloc_4689_, 10, v_w_4655_);
lean_ctor_set(v_reuseFailAlloc_4689_, 11, v_W_4656_);
lean_ctor_set(v_reuseFailAlloc_4689_, 12, v_E_4657_);
lean_ctor_set(v_reuseFailAlloc_4689_, 13, v_e_4658_);
lean_ctor_set(v_reuseFailAlloc_4689_, 14, v_c_4659_);
lean_ctor_set(v_reuseFailAlloc_4689_, 15, v_F_4660_);
lean_ctor_set(v_reuseFailAlloc_4689_, 16, v_a_4661_);
lean_ctor_set(v_reuseFailAlloc_4689_, 17, v_b_4662_);
lean_ctor_set(v_reuseFailAlloc_4689_, 18, v_B_4663_);
lean_ctor_set(v_reuseFailAlloc_4689_, 19, v_h_4664_);
lean_ctor_set(v_reuseFailAlloc_4689_, 20, v_K_4665_);
lean_ctor_set(v_reuseFailAlloc_4689_, 21, v_k_4666_);
lean_ctor_set(v_reuseFailAlloc_4689_, 22, v_H_4667_);
lean_ctor_set(v_reuseFailAlloc_4689_, 23, v_m_4668_);
lean_ctor_set(v_reuseFailAlloc_4689_, 24, v_s_4669_);
lean_ctor_set(v_reuseFailAlloc_4689_, 25, v_S_4670_);
lean_ctor_set(v_reuseFailAlloc_4689_, 26, v_A_4671_);
lean_ctor_set(v_reuseFailAlloc_4689_, 27, v_n_4672_);
lean_ctor_set(v_reuseFailAlloc_4689_, 28, v_N_4673_);
lean_ctor_set(v_reuseFailAlloc_4689_, 29, v_V_4674_);
lean_ctor_set(v_reuseFailAlloc_4689_, 30, v_z_4675_);
lean_ctor_set(v_reuseFailAlloc_4689_, 31, v_zabbrev_4676_);
lean_ctor_set(v_reuseFailAlloc_4689_, 32, v_v_4677_);
lean_ctor_set(v_reuseFailAlloc_4689_, 33, v_O_4678_);
lean_ctor_set(v_reuseFailAlloc_4689_, 34, v_X_4679_);
lean_ctor_set(v_reuseFailAlloc_4689_, 35, v_x_4680_);
lean_ctor_set(v_reuseFailAlloc_4689_, 36, v_Z_4681_);
v___x_4688_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
return v___x_4688_;
}
}
}
}
}
case 4:
{
lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4745_; 
v_isSharedCheck_4745_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_4745_ == 0)
{
lean_object* v_unused_4746_; 
v_unused_4746_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_4746_);
v___x_4696_ = v_modifier_4492_;
v_isShared_4697_ = v_isSharedCheck_4745_;
goto v_resetjp_4695_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4745_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v_G_4698_; lean_object* v_y_4699_; lean_object* v_u_4700_; lean_object* v_Y_4701_; lean_object* v_D_4702_; lean_object* v_L_4703_; lean_object* v_d_4704_; lean_object* v_Q_4705_; lean_object* v_q_4706_; lean_object* v_w_4707_; lean_object* v_W_4708_; lean_object* v_E_4709_; lean_object* v_e_4710_; lean_object* v_c_4711_; lean_object* v_F_4712_; lean_object* v_a_4713_; lean_object* v_b_4714_; lean_object* v_B_4715_; lean_object* v_h_4716_; lean_object* v_K_4717_; lean_object* v_k_4718_; lean_object* v_H_4719_; lean_object* v_m_4720_; lean_object* v_s_4721_; lean_object* v_S_4722_; lean_object* v_A_4723_; lean_object* v_n_4724_; lean_object* v_N_4725_; lean_object* v_V_4726_; lean_object* v_z_4727_; lean_object* v_zabbrev_4728_; lean_object* v_v_4729_; lean_object* v_O_4730_; lean_object* v_X_4731_; lean_object* v_x_4732_; lean_object* v_Z_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4743_; 
v_G_4698_ = lean_ctor_get(v_date_4491_, 0);
v_y_4699_ = lean_ctor_get(v_date_4491_, 1);
v_u_4700_ = lean_ctor_get(v_date_4491_, 2);
v_Y_4701_ = lean_ctor_get(v_date_4491_, 3);
v_D_4702_ = lean_ctor_get(v_date_4491_, 4);
v_L_4703_ = lean_ctor_get(v_date_4491_, 6);
v_d_4704_ = lean_ctor_get(v_date_4491_, 7);
v_Q_4705_ = lean_ctor_get(v_date_4491_, 8);
v_q_4706_ = lean_ctor_get(v_date_4491_, 9);
v_w_4707_ = lean_ctor_get(v_date_4491_, 10);
v_W_4708_ = lean_ctor_get(v_date_4491_, 11);
v_E_4709_ = lean_ctor_get(v_date_4491_, 12);
v_e_4710_ = lean_ctor_get(v_date_4491_, 13);
v_c_4711_ = lean_ctor_get(v_date_4491_, 14);
v_F_4712_ = lean_ctor_get(v_date_4491_, 15);
v_a_4713_ = lean_ctor_get(v_date_4491_, 16);
v_b_4714_ = lean_ctor_get(v_date_4491_, 17);
v_B_4715_ = lean_ctor_get(v_date_4491_, 18);
v_h_4716_ = lean_ctor_get(v_date_4491_, 19);
v_K_4717_ = lean_ctor_get(v_date_4491_, 20);
v_k_4718_ = lean_ctor_get(v_date_4491_, 21);
v_H_4719_ = lean_ctor_get(v_date_4491_, 22);
v_m_4720_ = lean_ctor_get(v_date_4491_, 23);
v_s_4721_ = lean_ctor_get(v_date_4491_, 24);
v_S_4722_ = lean_ctor_get(v_date_4491_, 25);
v_A_4723_ = lean_ctor_get(v_date_4491_, 26);
v_n_4724_ = lean_ctor_get(v_date_4491_, 27);
v_N_4725_ = lean_ctor_get(v_date_4491_, 28);
v_V_4726_ = lean_ctor_get(v_date_4491_, 29);
v_z_4727_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_4728_ = lean_ctor_get(v_date_4491_, 31);
v_v_4729_ = lean_ctor_get(v_date_4491_, 32);
v_O_4730_ = lean_ctor_get(v_date_4491_, 33);
v_X_4731_ = lean_ctor_get(v_date_4491_, 34);
v_x_4732_ = lean_ctor_get(v_date_4491_, 35);
v_Z_4733_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_4743_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_4743_ == 0)
{
lean_object* v_unused_4744_; 
v_unused_4744_ = lean_ctor_get(v_date_4491_, 5);
lean_dec(v_unused_4744_);
v___x_4735_ = v_date_4491_;
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
lean_inc(v_D_4702_);
lean_inc(v_Y_4701_);
lean_inc(v_u_4700_);
lean_inc(v_y_4699_);
lean_inc(v_G_4698_);
lean_dec(v_date_4491_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4743_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v___x_4738_; 
if (v_isShared_4697_ == 0)
{
lean_ctor_set_tag(v___x_4696_, 1);
lean_ctor_set(v___x_4696_, 0, v_data_4493_);
v___x_4738_ = v___x_4696_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v_data_4493_);
v___x_4738_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
lean_object* v___x_4740_; 
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 5, v___x_4738_);
v___x_4740_ = v___x_4735_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_G_4698_);
lean_ctor_set(v_reuseFailAlloc_4741_, 1, v_y_4699_);
lean_ctor_set(v_reuseFailAlloc_4741_, 2, v_u_4700_);
lean_ctor_set(v_reuseFailAlloc_4741_, 3, v_Y_4701_);
lean_ctor_set(v_reuseFailAlloc_4741_, 4, v_D_4702_);
lean_ctor_set(v_reuseFailAlloc_4741_, 5, v___x_4738_);
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
case 5:
{
lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4797_; 
v_isSharedCheck_4797_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_4797_ == 0)
{
lean_object* v_unused_4798_; 
v_unused_4798_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_4798_);
v___x_4748_ = v_modifier_4492_;
v_isShared_4749_ = v_isSharedCheck_4797_;
goto v_resetjp_4747_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4797_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v_G_4750_; lean_object* v_y_4751_; lean_object* v_u_4752_; lean_object* v_Y_4753_; lean_object* v_D_4754_; lean_object* v_M_4755_; lean_object* v_d_4756_; lean_object* v_Q_4757_; lean_object* v_q_4758_; lean_object* v_w_4759_; lean_object* v_W_4760_; lean_object* v_E_4761_; lean_object* v_e_4762_; lean_object* v_c_4763_; lean_object* v_F_4764_; lean_object* v_a_4765_; lean_object* v_b_4766_; lean_object* v_B_4767_; lean_object* v_h_4768_; lean_object* v_K_4769_; lean_object* v_k_4770_; lean_object* v_H_4771_; lean_object* v_m_4772_; lean_object* v_s_4773_; lean_object* v_S_4774_; lean_object* v_A_4775_; lean_object* v_n_4776_; lean_object* v_N_4777_; lean_object* v_V_4778_; lean_object* v_z_4779_; lean_object* v_zabbrev_4780_; lean_object* v_v_4781_; lean_object* v_O_4782_; lean_object* v_X_4783_; lean_object* v_x_4784_; lean_object* v_Z_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4795_; 
v_G_4750_ = lean_ctor_get(v_date_4491_, 0);
v_y_4751_ = lean_ctor_get(v_date_4491_, 1);
v_u_4752_ = lean_ctor_get(v_date_4491_, 2);
v_Y_4753_ = lean_ctor_get(v_date_4491_, 3);
v_D_4754_ = lean_ctor_get(v_date_4491_, 4);
v_M_4755_ = lean_ctor_get(v_date_4491_, 5);
v_d_4756_ = lean_ctor_get(v_date_4491_, 7);
v_Q_4757_ = lean_ctor_get(v_date_4491_, 8);
v_q_4758_ = lean_ctor_get(v_date_4491_, 9);
v_w_4759_ = lean_ctor_get(v_date_4491_, 10);
v_W_4760_ = lean_ctor_get(v_date_4491_, 11);
v_E_4761_ = lean_ctor_get(v_date_4491_, 12);
v_e_4762_ = lean_ctor_get(v_date_4491_, 13);
v_c_4763_ = lean_ctor_get(v_date_4491_, 14);
v_F_4764_ = lean_ctor_get(v_date_4491_, 15);
v_a_4765_ = lean_ctor_get(v_date_4491_, 16);
v_b_4766_ = lean_ctor_get(v_date_4491_, 17);
v_B_4767_ = lean_ctor_get(v_date_4491_, 18);
v_h_4768_ = lean_ctor_get(v_date_4491_, 19);
v_K_4769_ = lean_ctor_get(v_date_4491_, 20);
v_k_4770_ = lean_ctor_get(v_date_4491_, 21);
v_H_4771_ = lean_ctor_get(v_date_4491_, 22);
v_m_4772_ = lean_ctor_get(v_date_4491_, 23);
v_s_4773_ = lean_ctor_get(v_date_4491_, 24);
v_S_4774_ = lean_ctor_get(v_date_4491_, 25);
v_A_4775_ = lean_ctor_get(v_date_4491_, 26);
v_n_4776_ = lean_ctor_get(v_date_4491_, 27);
v_N_4777_ = lean_ctor_get(v_date_4491_, 28);
v_V_4778_ = lean_ctor_get(v_date_4491_, 29);
v_z_4779_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_4780_ = lean_ctor_get(v_date_4491_, 31);
v_v_4781_ = lean_ctor_get(v_date_4491_, 32);
v_O_4782_ = lean_ctor_get(v_date_4491_, 33);
v_X_4783_ = lean_ctor_get(v_date_4491_, 34);
v_x_4784_ = lean_ctor_get(v_date_4491_, 35);
v_Z_4785_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_4795_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_4795_ == 0)
{
lean_object* v_unused_4796_; 
v_unused_4796_ = lean_ctor_get(v_date_4491_, 6);
lean_dec(v_unused_4796_);
v___x_4787_ = v_date_4491_;
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
lean_inc(v_M_4755_);
lean_inc(v_D_4754_);
lean_inc(v_Y_4753_);
lean_inc(v_u_4752_);
lean_inc(v_y_4751_);
lean_inc(v_G_4750_);
lean_dec(v_date_4491_);
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
lean_ctor_set(v___x_4748_, 0, v_data_4493_);
v___x_4790_ = v___x_4748_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v_data_4493_);
v___x_4790_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
lean_object* v___x_4792_; 
if (v_isShared_4788_ == 0)
{
lean_ctor_set(v___x_4787_, 6, v___x_4790_);
v___x_4792_ = v___x_4787_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_G_4750_);
lean_ctor_set(v_reuseFailAlloc_4793_, 1, v_y_4751_);
lean_ctor_set(v_reuseFailAlloc_4793_, 2, v_u_4752_);
lean_ctor_set(v_reuseFailAlloc_4793_, 3, v_Y_4753_);
lean_ctor_set(v_reuseFailAlloc_4793_, 4, v_D_4754_);
lean_ctor_set(v_reuseFailAlloc_4793_, 5, v_M_4755_);
lean_ctor_set(v_reuseFailAlloc_4793_, 6, v___x_4790_);
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
case 6:
{
lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4849_; 
v_isSharedCheck_4849_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_4849_ == 0)
{
lean_object* v_unused_4850_; 
v_unused_4850_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_4850_);
v___x_4800_ = v_modifier_4492_;
v_isShared_4801_ = v_isSharedCheck_4849_;
goto v_resetjp_4799_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4849_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v_G_4802_; lean_object* v_y_4803_; lean_object* v_u_4804_; lean_object* v_Y_4805_; lean_object* v_D_4806_; lean_object* v_M_4807_; lean_object* v_L_4808_; lean_object* v_Q_4809_; lean_object* v_q_4810_; lean_object* v_w_4811_; lean_object* v_W_4812_; lean_object* v_E_4813_; lean_object* v_e_4814_; lean_object* v_c_4815_; lean_object* v_F_4816_; lean_object* v_a_4817_; lean_object* v_b_4818_; lean_object* v_B_4819_; lean_object* v_h_4820_; lean_object* v_K_4821_; lean_object* v_k_4822_; lean_object* v_H_4823_; lean_object* v_m_4824_; lean_object* v_s_4825_; lean_object* v_S_4826_; lean_object* v_A_4827_; lean_object* v_n_4828_; lean_object* v_N_4829_; lean_object* v_V_4830_; lean_object* v_z_4831_; lean_object* v_zabbrev_4832_; lean_object* v_v_4833_; lean_object* v_O_4834_; lean_object* v_X_4835_; lean_object* v_x_4836_; lean_object* v_Z_4837_; lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4847_; 
v_G_4802_ = lean_ctor_get(v_date_4491_, 0);
v_y_4803_ = lean_ctor_get(v_date_4491_, 1);
v_u_4804_ = lean_ctor_get(v_date_4491_, 2);
v_Y_4805_ = lean_ctor_get(v_date_4491_, 3);
v_D_4806_ = lean_ctor_get(v_date_4491_, 4);
v_M_4807_ = lean_ctor_get(v_date_4491_, 5);
v_L_4808_ = lean_ctor_get(v_date_4491_, 6);
v_Q_4809_ = lean_ctor_get(v_date_4491_, 8);
v_q_4810_ = lean_ctor_get(v_date_4491_, 9);
v_w_4811_ = lean_ctor_get(v_date_4491_, 10);
v_W_4812_ = lean_ctor_get(v_date_4491_, 11);
v_E_4813_ = lean_ctor_get(v_date_4491_, 12);
v_e_4814_ = lean_ctor_get(v_date_4491_, 13);
v_c_4815_ = lean_ctor_get(v_date_4491_, 14);
v_F_4816_ = lean_ctor_get(v_date_4491_, 15);
v_a_4817_ = lean_ctor_get(v_date_4491_, 16);
v_b_4818_ = lean_ctor_get(v_date_4491_, 17);
v_B_4819_ = lean_ctor_get(v_date_4491_, 18);
v_h_4820_ = lean_ctor_get(v_date_4491_, 19);
v_K_4821_ = lean_ctor_get(v_date_4491_, 20);
v_k_4822_ = lean_ctor_get(v_date_4491_, 21);
v_H_4823_ = lean_ctor_get(v_date_4491_, 22);
v_m_4824_ = lean_ctor_get(v_date_4491_, 23);
v_s_4825_ = lean_ctor_get(v_date_4491_, 24);
v_S_4826_ = lean_ctor_get(v_date_4491_, 25);
v_A_4827_ = lean_ctor_get(v_date_4491_, 26);
v_n_4828_ = lean_ctor_get(v_date_4491_, 27);
v_N_4829_ = lean_ctor_get(v_date_4491_, 28);
v_V_4830_ = lean_ctor_get(v_date_4491_, 29);
v_z_4831_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_4832_ = lean_ctor_get(v_date_4491_, 31);
v_v_4833_ = lean_ctor_get(v_date_4491_, 32);
v_O_4834_ = lean_ctor_get(v_date_4491_, 33);
v_X_4835_ = lean_ctor_get(v_date_4491_, 34);
v_x_4836_ = lean_ctor_get(v_date_4491_, 35);
v_Z_4837_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_4847_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_4847_ == 0)
{
lean_object* v_unused_4848_; 
v_unused_4848_ = lean_ctor_get(v_date_4491_, 7);
lean_dec(v_unused_4848_);
v___x_4839_ = v_date_4491_;
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
lean_inc(v_L_4808_);
lean_inc(v_M_4807_);
lean_inc(v_D_4806_);
lean_inc(v_Y_4805_);
lean_inc(v_u_4804_);
lean_inc(v_y_4803_);
lean_inc(v_G_4802_);
lean_dec(v_date_4491_);
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
lean_ctor_set(v___x_4800_, 0, v_data_4493_);
v___x_4842_ = v___x_4800_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v_data_4493_);
v___x_4842_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
lean_object* v___x_4844_; 
if (v_isShared_4840_ == 0)
{
lean_ctor_set(v___x_4839_, 7, v___x_4842_);
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
lean_ctor_set(v_reuseFailAlloc_4845_, 4, v_D_4806_);
lean_ctor_set(v_reuseFailAlloc_4845_, 5, v_M_4807_);
lean_ctor_set(v_reuseFailAlloc_4845_, 6, v_L_4808_);
lean_ctor_set(v_reuseFailAlloc_4845_, 7, v___x_4842_);
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
case 7:
{
lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4901_; 
v_isSharedCheck_4901_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_4901_ == 0)
{
lean_object* v_unused_4902_; 
v_unused_4902_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_4902_);
v___x_4852_ = v_modifier_4492_;
v_isShared_4853_ = v_isSharedCheck_4901_;
goto v_resetjp_4851_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4901_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v_G_4854_; lean_object* v_y_4855_; lean_object* v_u_4856_; lean_object* v_Y_4857_; lean_object* v_D_4858_; lean_object* v_M_4859_; lean_object* v_L_4860_; lean_object* v_d_4861_; lean_object* v_q_4862_; lean_object* v_w_4863_; lean_object* v_W_4864_; lean_object* v_E_4865_; lean_object* v_e_4866_; lean_object* v_c_4867_; lean_object* v_F_4868_; lean_object* v_a_4869_; lean_object* v_b_4870_; lean_object* v_B_4871_; lean_object* v_h_4872_; lean_object* v_K_4873_; lean_object* v_k_4874_; lean_object* v_H_4875_; lean_object* v_m_4876_; lean_object* v_s_4877_; lean_object* v_S_4878_; lean_object* v_A_4879_; lean_object* v_n_4880_; lean_object* v_N_4881_; lean_object* v_V_4882_; lean_object* v_z_4883_; lean_object* v_zabbrev_4884_; lean_object* v_v_4885_; lean_object* v_O_4886_; lean_object* v_X_4887_; lean_object* v_x_4888_; lean_object* v_Z_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4899_; 
v_G_4854_ = lean_ctor_get(v_date_4491_, 0);
v_y_4855_ = lean_ctor_get(v_date_4491_, 1);
v_u_4856_ = lean_ctor_get(v_date_4491_, 2);
v_Y_4857_ = lean_ctor_get(v_date_4491_, 3);
v_D_4858_ = lean_ctor_get(v_date_4491_, 4);
v_M_4859_ = lean_ctor_get(v_date_4491_, 5);
v_L_4860_ = lean_ctor_get(v_date_4491_, 6);
v_d_4861_ = lean_ctor_get(v_date_4491_, 7);
v_q_4862_ = lean_ctor_get(v_date_4491_, 9);
v_w_4863_ = lean_ctor_get(v_date_4491_, 10);
v_W_4864_ = lean_ctor_get(v_date_4491_, 11);
v_E_4865_ = lean_ctor_get(v_date_4491_, 12);
v_e_4866_ = lean_ctor_get(v_date_4491_, 13);
v_c_4867_ = lean_ctor_get(v_date_4491_, 14);
v_F_4868_ = lean_ctor_get(v_date_4491_, 15);
v_a_4869_ = lean_ctor_get(v_date_4491_, 16);
v_b_4870_ = lean_ctor_get(v_date_4491_, 17);
v_B_4871_ = lean_ctor_get(v_date_4491_, 18);
v_h_4872_ = lean_ctor_get(v_date_4491_, 19);
v_K_4873_ = lean_ctor_get(v_date_4491_, 20);
v_k_4874_ = lean_ctor_get(v_date_4491_, 21);
v_H_4875_ = lean_ctor_get(v_date_4491_, 22);
v_m_4876_ = lean_ctor_get(v_date_4491_, 23);
v_s_4877_ = lean_ctor_get(v_date_4491_, 24);
v_S_4878_ = lean_ctor_get(v_date_4491_, 25);
v_A_4879_ = lean_ctor_get(v_date_4491_, 26);
v_n_4880_ = lean_ctor_get(v_date_4491_, 27);
v_N_4881_ = lean_ctor_get(v_date_4491_, 28);
v_V_4882_ = lean_ctor_get(v_date_4491_, 29);
v_z_4883_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_4884_ = lean_ctor_get(v_date_4491_, 31);
v_v_4885_ = lean_ctor_get(v_date_4491_, 32);
v_O_4886_ = lean_ctor_get(v_date_4491_, 33);
v_X_4887_ = lean_ctor_get(v_date_4491_, 34);
v_x_4888_ = lean_ctor_get(v_date_4491_, 35);
v_Z_4889_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_4899_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_4899_ == 0)
{
lean_object* v_unused_4900_; 
v_unused_4900_ = lean_ctor_get(v_date_4491_, 8);
lean_dec(v_unused_4900_);
v___x_4891_ = v_date_4491_;
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
lean_inc(v_d_4861_);
lean_inc(v_L_4860_);
lean_inc(v_M_4859_);
lean_inc(v_D_4858_);
lean_inc(v_Y_4857_);
lean_inc(v_u_4856_);
lean_inc(v_y_4855_);
lean_inc(v_G_4854_);
lean_dec(v_date_4491_);
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
lean_ctor_set(v___x_4852_, 0, v_data_4493_);
v___x_4894_ = v___x_4852_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_data_4493_);
v___x_4894_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
lean_object* v___x_4896_; 
if (v_isShared_4892_ == 0)
{
lean_ctor_set(v___x_4891_, 8, v___x_4894_);
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
lean_ctor_set(v_reuseFailAlloc_4897_, 5, v_M_4859_);
lean_ctor_set(v_reuseFailAlloc_4897_, 6, v_L_4860_);
lean_ctor_set(v_reuseFailAlloc_4897_, 7, v_d_4861_);
lean_ctor_set(v_reuseFailAlloc_4897_, 8, v___x_4894_);
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
case 8:
{
lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4953_; 
v_isSharedCheck_4953_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_4953_ == 0)
{
lean_object* v_unused_4954_; 
v_unused_4954_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_4954_);
v___x_4904_ = v_modifier_4492_;
v_isShared_4905_ = v_isSharedCheck_4953_;
goto v_resetjp_4903_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4953_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v_G_4906_; lean_object* v_y_4907_; lean_object* v_u_4908_; lean_object* v_Y_4909_; lean_object* v_D_4910_; lean_object* v_M_4911_; lean_object* v_L_4912_; lean_object* v_d_4913_; lean_object* v_Q_4914_; lean_object* v_w_4915_; lean_object* v_W_4916_; lean_object* v_E_4917_; lean_object* v_e_4918_; lean_object* v_c_4919_; lean_object* v_F_4920_; lean_object* v_a_4921_; lean_object* v_b_4922_; lean_object* v_B_4923_; lean_object* v_h_4924_; lean_object* v_K_4925_; lean_object* v_k_4926_; lean_object* v_H_4927_; lean_object* v_m_4928_; lean_object* v_s_4929_; lean_object* v_S_4930_; lean_object* v_A_4931_; lean_object* v_n_4932_; lean_object* v_N_4933_; lean_object* v_V_4934_; lean_object* v_z_4935_; lean_object* v_zabbrev_4936_; lean_object* v_v_4937_; lean_object* v_O_4938_; lean_object* v_X_4939_; lean_object* v_x_4940_; lean_object* v_Z_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4951_; 
v_G_4906_ = lean_ctor_get(v_date_4491_, 0);
v_y_4907_ = lean_ctor_get(v_date_4491_, 1);
v_u_4908_ = lean_ctor_get(v_date_4491_, 2);
v_Y_4909_ = lean_ctor_get(v_date_4491_, 3);
v_D_4910_ = lean_ctor_get(v_date_4491_, 4);
v_M_4911_ = lean_ctor_get(v_date_4491_, 5);
v_L_4912_ = lean_ctor_get(v_date_4491_, 6);
v_d_4913_ = lean_ctor_get(v_date_4491_, 7);
v_Q_4914_ = lean_ctor_get(v_date_4491_, 8);
v_w_4915_ = lean_ctor_get(v_date_4491_, 10);
v_W_4916_ = lean_ctor_get(v_date_4491_, 11);
v_E_4917_ = lean_ctor_get(v_date_4491_, 12);
v_e_4918_ = lean_ctor_get(v_date_4491_, 13);
v_c_4919_ = lean_ctor_get(v_date_4491_, 14);
v_F_4920_ = lean_ctor_get(v_date_4491_, 15);
v_a_4921_ = lean_ctor_get(v_date_4491_, 16);
v_b_4922_ = lean_ctor_get(v_date_4491_, 17);
v_B_4923_ = lean_ctor_get(v_date_4491_, 18);
v_h_4924_ = lean_ctor_get(v_date_4491_, 19);
v_K_4925_ = lean_ctor_get(v_date_4491_, 20);
v_k_4926_ = lean_ctor_get(v_date_4491_, 21);
v_H_4927_ = lean_ctor_get(v_date_4491_, 22);
v_m_4928_ = lean_ctor_get(v_date_4491_, 23);
v_s_4929_ = lean_ctor_get(v_date_4491_, 24);
v_S_4930_ = lean_ctor_get(v_date_4491_, 25);
v_A_4931_ = lean_ctor_get(v_date_4491_, 26);
v_n_4932_ = lean_ctor_get(v_date_4491_, 27);
v_N_4933_ = lean_ctor_get(v_date_4491_, 28);
v_V_4934_ = lean_ctor_get(v_date_4491_, 29);
v_z_4935_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_4936_ = lean_ctor_get(v_date_4491_, 31);
v_v_4937_ = lean_ctor_get(v_date_4491_, 32);
v_O_4938_ = lean_ctor_get(v_date_4491_, 33);
v_X_4939_ = lean_ctor_get(v_date_4491_, 34);
v_x_4940_ = lean_ctor_get(v_date_4491_, 35);
v_Z_4941_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_4951_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_4951_ == 0)
{
lean_object* v_unused_4952_; 
v_unused_4952_ = lean_ctor_get(v_date_4491_, 9);
lean_dec(v_unused_4952_);
v___x_4943_ = v_date_4491_;
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
lean_inc(v_Q_4914_);
lean_inc(v_d_4913_);
lean_inc(v_L_4912_);
lean_inc(v_M_4911_);
lean_inc(v_D_4910_);
lean_inc(v_Y_4909_);
lean_inc(v_u_4908_);
lean_inc(v_y_4907_);
lean_inc(v_G_4906_);
lean_dec(v_date_4491_);
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
lean_ctor_set(v___x_4904_, 0, v_data_4493_);
v___x_4946_ = v___x_4904_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v_data_4493_);
v___x_4946_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
lean_object* v___x_4948_; 
if (v_isShared_4944_ == 0)
{
lean_ctor_set(v___x_4943_, 9, v___x_4946_);
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
lean_ctor_set(v_reuseFailAlloc_4949_, 6, v_L_4912_);
lean_ctor_set(v_reuseFailAlloc_4949_, 7, v_d_4913_);
lean_ctor_set(v_reuseFailAlloc_4949_, 8, v_Q_4914_);
lean_ctor_set(v_reuseFailAlloc_4949_, 9, v___x_4946_);
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
case 9:
{
lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_5005_; 
v_isSharedCheck_5005_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_5005_ == 0)
{
lean_object* v_unused_5006_; 
v_unused_5006_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_5006_);
v___x_4956_ = v_modifier_4492_;
v_isShared_4957_ = v_isSharedCheck_5005_;
goto v_resetjp_4955_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_5005_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v_G_4958_; lean_object* v_y_4959_; lean_object* v_u_4960_; lean_object* v_D_4961_; lean_object* v_M_4962_; lean_object* v_L_4963_; lean_object* v_d_4964_; lean_object* v_Q_4965_; lean_object* v_q_4966_; lean_object* v_w_4967_; lean_object* v_W_4968_; lean_object* v_E_4969_; lean_object* v_e_4970_; lean_object* v_c_4971_; lean_object* v_F_4972_; lean_object* v_a_4973_; lean_object* v_b_4974_; lean_object* v_B_4975_; lean_object* v_h_4976_; lean_object* v_K_4977_; lean_object* v_k_4978_; lean_object* v_H_4979_; lean_object* v_m_4980_; lean_object* v_s_4981_; lean_object* v_S_4982_; lean_object* v_A_4983_; lean_object* v_n_4984_; lean_object* v_N_4985_; lean_object* v_V_4986_; lean_object* v_z_4987_; lean_object* v_zabbrev_4988_; lean_object* v_v_4989_; lean_object* v_O_4990_; lean_object* v_X_4991_; lean_object* v_x_4992_; lean_object* v_Z_4993_; lean_object* v___x_4995_; uint8_t v_isShared_4996_; uint8_t v_isSharedCheck_5003_; 
v_G_4958_ = lean_ctor_get(v_date_4491_, 0);
v_y_4959_ = lean_ctor_get(v_date_4491_, 1);
v_u_4960_ = lean_ctor_get(v_date_4491_, 2);
v_D_4961_ = lean_ctor_get(v_date_4491_, 4);
v_M_4962_ = lean_ctor_get(v_date_4491_, 5);
v_L_4963_ = lean_ctor_get(v_date_4491_, 6);
v_d_4964_ = lean_ctor_get(v_date_4491_, 7);
v_Q_4965_ = lean_ctor_get(v_date_4491_, 8);
v_q_4966_ = lean_ctor_get(v_date_4491_, 9);
v_w_4967_ = lean_ctor_get(v_date_4491_, 10);
v_W_4968_ = lean_ctor_get(v_date_4491_, 11);
v_E_4969_ = lean_ctor_get(v_date_4491_, 12);
v_e_4970_ = lean_ctor_get(v_date_4491_, 13);
v_c_4971_ = lean_ctor_get(v_date_4491_, 14);
v_F_4972_ = lean_ctor_get(v_date_4491_, 15);
v_a_4973_ = lean_ctor_get(v_date_4491_, 16);
v_b_4974_ = lean_ctor_get(v_date_4491_, 17);
v_B_4975_ = lean_ctor_get(v_date_4491_, 18);
v_h_4976_ = lean_ctor_get(v_date_4491_, 19);
v_K_4977_ = lean_ctor_get(v_date_4491_, 20);
v_k_4978_ = lean_ctor_get(v_date_4491_, 21);
v_H_4979_ = lean_ctor_get(v_date_4491_, 22);
v_m_4980_ = lean_ctor_get(v_date_4491_, 23);
v_s_4981_ = lean_ctor_get(v_date_4491_, 24);
v_S_4982_ = lean_ctor_get(v_date_4491_, 25);
v_A_4983_ = lean_ctor_get(v_date_4491_, 26);
v_n_4984_ = lean_ctor_get(v_date_4491_, 27);
v_N_4985_ = lean_ctor_get(v_date_4491_, 28);
v_V_4986_ = lean_ctor_get(v_date_4491_, 29);
v_z_4987_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_4988_ = lean_ctor_get(v_date_4491_, 31);
v_v_4989_ = lean_ctor_get(v_date_4491_, 32);
v_O_4990_ = lean_ctor_get(v_date_4491_, 33);
v_X_4991_ = lean_ctor_get(v_date_4491_, 34);
v_x_4992_ = lean_ctor_get(v_date_4491_, 35);
v_Z_4993_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5003_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5003_ == 0)
{
lean_object* v_unused_5004_; 
v_unused_5004_ = lean_ctor_get(v_date_4491_, 3);
lean_dec(v_unused_5004_);
v___x_4995_ = v_date_4491_;
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
lean_inc(v_d_4964_);
lean_inc(v_L_4963_);
lean_inc(v_M_4962_);
lean_inc(v_D_4961_);
lean_inc(v_u_4960_);
lean_inc(v_y_4959_);
lean_inc(v_G_4958_);
lean_dec(v_date_4491_);
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
lean_ctor_set(v___x_4956_, 0, v_data_4493_);
v___x_4998_ = v___x_4956_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_5002_; 
v_reuseFailAlloc_5002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5002_, 0, v_data_4493_);
v___x_4998_ = v_reuseFailAlloc_5002_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
lean_object* v___x_5000_; 
if (v_isShared_4996_ == 0)
{
lean_ctor_set(v___x_4995_, 3, v___x_4998_);
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
lean_ctor_set(v_reuseFailAlloc_5001_, 3, v___x_4998_);
lean_ctor_set(v_reuseFailAlloc_5001_, 4, v_D_4961_);
lean_ctor_set(v_reuseFailAlloc_5001_, 5, v_M_4962_);
lean_ctor_set(v_reuseFailAlloc_5001_, 6, v_L_4963_);
lean_ctor_set(v_reuseFailAlloc_5001_, 7, v_d_4964_);
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
case 10:
{
lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5057_; 
v_isSharedCheck_5057_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_5057_ == 0)
{
lean_object* v_unused_5058_; 
v_unused_5058_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_5058_);
v___x_5008_ = v_modifier_4492_;
v_isShared_5009_ = v_isSharedCheck_5057_;
goto v_resetjp_5007_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5057_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v_G_5010_; lean_object* v_y_5011_; lean_object* v_u_5012_; lean_object* v_Y_5013_; lean_object* v_D_5014_; lean_object* v_M_5015_; lean_object* v_L_5016_; lean_object* v_d_5017_; lean_object* v_Q_5018_; lean_object* v_q_5019_; lean_object* v_W_5020_; lean_object* v_E_5021_; lean_object* v_e_5022_; lean_object* v_c_5023_; lean_object* v_F_5024_; lean_object* v_a_5025_; lean_object* v_b_5026_; lean_object* v_B_5027_; lean_object* v_h_5028_; lean_object* v_K_5029_; lean_object* v_k_5030_; lean_object* v_H_5031_; lean_object* v_m_5032_; lean_object* v_s_5033_; lean_object* v_S_5034_; lean_object* v_A_5035_; lean_object* v_n_5036_; lean_object* v_N_5037_; lean_object* v_V_5038_; lean_object* v_z_5039_; lean_object* v_zabbrev_5040_; lean_object* v_v_5041_; lean_object* v_O_5042_; lean_object* v_X_5043_; lean_object* v_x_5044_; lean_object* v_Z_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5055_; 
v_G_5010_ = lean_ctor_get(v_date_4491_, 0);
v_y_5011_ = lean_ctor_get(v_date_4491_, 1);
v_u_5012_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5013_ = lean_ctor_get(v_date_4491_, 3);
v_D_5014_ = lean_ctor_get(v_date_4491_, 4);
v_M_5015_ = lean_ctor_get(v_date_4491_, 5);
v_L_5016_ = lean_ctor_get(v_date_4491_, 6);
v_d_5017_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5018_ = lean_ctor_get(v_date_4491_, 8);
v_q_5019_ = lean_ctor_get(v_date_4491_, 9);
v_W_5020_ = lean_ctor_get(v_date_4491_, 11);
v_E_5021_ = lean_ctor_get(v_date_4491_, 12);
v_e_5022_ = lean_ctor_get(v_date_4491_, 13);
v_c_5023_ = lean_ctor_get(v_date_4491_, 14);
v_F_5024_ = lean_ctor_get(v_date_4491_, 15);
v_a_5025_ = lean_ctor_get(v_date_4491_, 16);
v_b_5026_ = lean_ctor_get(v_date_4491_, 17);
v_B_5027_ = lean_ctor_get(v_date_4491_, 18);
v_h_5028_ = lean_ctor_get(v_date_4491_, 19);
v_K_5029_ = lean_ctor_get(v_date_4491_, 20);
v_k_5030_ = lean_ctor_get(v_date_4491_, 21);
v_H_5031_ = lean_ctor_get(v_date_4491_, 22);
v_m_5032_ = lean_ctor_get(v_date_4491_, 23);
v_s_5033_ = lean_ctor_get(v_date_4491_, 24);
v_S_5034_ = lean_ctor_get(v_date_4491_, 25);
v_A_5035_ = lean_ctor_get(v_date_4491_, 26);
v_n_5036_ = lean_ctor_get(v_date_4491_, 27);
v_N_5037_ = lean_ctor_get(v_date_4491_, 28);
v_V_5038_ = lean_ctor_get(v_date_4491_, 29);
v_z_5039_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5040_ = lean_ctor_get(v_date_4491_, 31);
v_v_5041_ = lean_ctor_get(v_date_4491_, 32);
v_O_5042_ = lean_ctor_get(v_date_4491_, 33);
v_X_5043_ = lean_ctor_get(v_date_4491_, 34);
v_x_5044_ = lean_ctor_get(v_date_4491_, 35);
v_Z_5045_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5055_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5055_ == 0)
{
lean_object* v_unused_5056_; 
v_unused_5056_ = lean_ctor_get(v_date_4491_, 10);
lean_dec(v_unused_5056_);
v___x_5047_ = v_date_4491_;
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
lean_inc(v_q_5019_);
lean_inc(v_Q_5018_);
lean_inc(v_d_5017_);
lean_inc(v_L_5016_);
lean_inc(v_M_5015_);
lean_inc(v_D_5014_);
lean_inc(v_Y_5013_);
lean_inc(v_u_5012_);
lean_inc(v_y_5011_);
lean_inc(v_G_5010_);
lean_dec(v_date_4491_);
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
lean_ctor_set(v___x_5008_, 0, v_data_4493_);
v___x_5050_ = v___x_5008_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_data_4493_);
v___x_5050_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
lean_object* v___x_5052_; 
if (v_isShared_5048_ == 0)
{
lean_ctor_set(v___x_5047_, 10, v___x_5050_);
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
lean_ctor_set(v_reuseFailAlloc_5053_, 8, v_Q_5018_);
lean_ctor_set(v_reuseFailAlloc_5053_, 9, v_q_5019_);
lean_ctor_set(v_reuseFailAlloc_5053_, 10, v___x_5050_);
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
case 11:
{
lean_object* v___x_5060_; uint8_t v_isShared_5061_; uint8_t v_isSharedCheck_5109_; 
v_isSharedCheck_5109_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_5109_ == 0)
{
lean_object* v_unused_5110_; 
v_unused_5110_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_5110_);
v___x_5060_ = v_modifier_4492_;
v_isShared_5061_ = v_isSharedCheck_5109_;
goto v_resetjp_5059_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_5060_ = lean_box(0);
v_isShared_5061_ = v_isSharedCheck_5109_;
goto v_resetjp_5059_;
}
v_resetjp_5059_:
{
lean_object* v_G_5062_; lean_object* v_y_5063_; lean_object* v_u_5064_; lean_object* v_Y_5065_; lean_object* v_D_5066_; lean_object* v_M_5067_; lean_object* v_L_5068_; lean_object* v_d_5069_; lean_object* v_Q_5070_; lean_object* v_q_5071_; lean_object* v_w_5072_; lean_object* v_E_5073_; lean_object* v_e_5074_; lean_object* v_c_5075_; lean_object* v_F_5076_; lean_object* v_a_5077_; lean_object* v_b_5078_; lean_object* v_B_5079_; lean_object* v_h_5080_; lean_object* v_K_5081_; lean_object* v_k_5082_; lean_object* v_H_5083_; lean_object* v_m_5084_; lean_object* v_s_5085_; lean_object* v_S_5086_; lean_object* v_A_5087_; lean_object* v_n_5088_; lean_object* v_N_5089_; lean_object* v_V_5090_; lean_object* v_z_5091_; lean_object* v_zabbrev_5092_; lean_object* v_v_5093_; lean_object* v_O_5094_; lean_object* v_X_5095_; lean_object* v_x_5096_; lean_object* v_Z_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5107_; 
v_G_5062_ = lean_ctor_get(v_date_4491_, 0);
v_y_5063_ = lean_ctor_get(v_date_4491_, 1);
v_u_5064_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5065_ = lean_ctor_get(v_date_4491_, 3);
v_D_5066_ = lean_ctor_get(v_date_4491_, 4);
v_M_5067_ = lean_ctor_get(v_date_4491_, 5);
v_L_5068_ = lean_ctor_get(v_date_4491_, 6);
v_d_5069_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5070_ = lean_ctor_get(v_date_4491_, 8);
v_q_5071_ = lean_ctor_get(v_date_4491_, 9);
v_w_5072_ = lean_ctor_get(v_date_4491_, 10);
v_E_5073_ = lean_ctor_get(v_date_4491_, 12);
v_e_5074_ = lean_ctor_get(v_date_4491_, 13);
v_c_5075_ = lean_ctor_get(v_date_4491_, 14);
v_F_5076_ = lean_ctor_get(v_date_4491_, 15);
v_a_5077_ = lean_ctor_get(v_date_4491_, 16);
v_b_5078_ = lean_ctor_get(v_date_4491_, 17);
v_B_5079_ = lean_ctor_get(v_date_4491_, 18);
v_h_5080_ = lean_ctor_get(v_date_4491_, 19);
v_K_5081_ = lean_ctor_get(v_date_4491_, 20);
v_k_5082_ = lean_ctor_get(v_date_4491_, 21);
v_H_5083_ = lean_ctor_get(v_date_4491_, 22);
v_m_5084_ = lean_ctor_get(v_date_4491_, 23);
v_s_5085_ = lean_ctor_get(v_date_4491_, 24);
v_S_5086_ = lean_ctor_get(v_date_4491_, 25);
v_A_5087_ = lean_ctor_get(v_date_4491_, 26);
v_n_5088_ = lean_ctor_get(v_date_4491_, 27);
v_N_5089_ = lean_ctor_get(v_date_4491_, 28);
v_V_5090_ = lean_ctor_get(v_date_4491_, 29);
v_z_5091_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5092_ = lean_ctor_get(v_date_4491_, 31);
v_v_5093_ = lean_ctor_get(v_date_4491_, 32);
v_O_5094_ = lean_ctor_get(v_date_4491_, 33);
v_X_5095_ = lean_ctor_get(v_date_4491_, 34);
v_x_5096_ = lean_ctor_get(v_date_4491_, 35);
v_Z_5097_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5107_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5107_ == 0)
{
lean_object* v_unused_5108_; 
v_unused_5108_ = lean_ctor_get(v_date_4491_, 11);
lean_dec(v_unused_5108_);
v___x_5099_ = v_date_4491_;
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
lean_inc(v_w_5072_);
lean_inc(v_q_5071_);
lean_inc(v_Q_5070_);
lean_inc(v_d_5069_);
lean_inc(v_L_5068_);
lean_inc(v_M_5067_);
lean_inc(v_D_5066_);
lean_inc(v_Y_5065_);
lean_inc(v_u_5064_);
lean_inc(v_y_5063_);
lean_inc(v_G_5062_);
lean_dec(v_date_4491_);
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
lean_ctor_set(v___x_5060_, 0, v_data_4493_);
v___x_5102_ = v___x_5060_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_data_4493_);
v___x_5102_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5101_;
}
v_reusejp_5101_:
{
lean_object* v___x_5104_; 
if (v_isShared_5100_ == 0)
{
lean_ctor_set(v___x_5099_, 11, v___x_5102_);
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
lean_ctor_set(v_reuseFailAlloc_5105_, 9, v_q_5071_);
lean_ctor_set(v_reuseFailAlloc_5105_, 10, v_w_5072_);
lean_ctor_set(v_reuseFailAlloc_5105_, 11, v___x_5102_);
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
case 12:
{
lean_object* v_G_5111_; lean_object* v_y_5112_; lean_object* v_u_5113_; lean_object* v_Y_5114_; lean_object* v_D_5115_; lean_object* v_M_5116_; lean_object* v_L_5117_; lean_object* v_d_5118_; lean_object* v_Q_5119_; lean_object* v_q_5120_; lean_object* v_w_5121_; lean_object* v_W_5122_; lean_object* v_e_5123_; lean_object* v_c_5124_; lean_object* v_F_5125_; lean_object* v_a_5126_; lean_object* v_b_5127_; lean_object* v_B_5128_; lean_object* v_h_5129_; lean_object* v_K_5130_; lean_object* v_k_5131_; lean_object* v_H_5132_; lean_object* v_m_5133_; lean_object* v_s_5134_; lean_object* v_S_5135_; lean_object* v_A_5136_; lean_object* v_n_5137_; lean_object* v_N_5138_; lean_object* v_V_5139_; lean_object* v_z_5140_; lean_object* v_zabbrev_5141_; lean_object* v_v_5142_; lean_object* v_O_5143_; lean_object* v_X_5144_; lean_object* v_x_5145_; lean_object* v_Z_5146_; lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5154_; 
lean_dec_ref_known(v_modifier_4492_, 0);
v_G_5111_ = lean_ctor_get(v_date_4491_, 0);
v_y_5112_ = lean_ctor_get(v_date_4491_, 1);
v_u_5113_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5114_ = lean_ctor_get(v_date_4491_, 3);
v_D_5115_ = lean_ctor_get(v_date_4491_, 4);
v_M_5116_ = lean_ctor_get(v_date_4491_, 5);
v_L_5117_ = lean_ctor_get(v_date_4491_, 6);
v_d_5118_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5119_ = lean_ctor_get(v_date_4491_, 8);
v_q_5120_ = lean_ctor_get(v_date_4491_, 9);
v_w_5121_ = lean_ctor_get(v_date_4491_, 10);
v_W_5122_ = lean_ctor_get(v_date_4491_, 11);
v_e_5123_ = lean_ctor_get(v_date_4491_, 13);
v_c_5124_ = lean_ctor_get(v_date_4491_, 14);
v_F_5125_ = lean_ctor_get(v_date_4491_, 15);
v_a_5126_ = lean_ctor_get(v_date_4491_, 16);
v_b_5127_ = lean_ctor_get(v_date_4491_, 17);
v_B_5128_ = lean_ctor_get(v_date_4491_, 18);
v_h_5129_ = lean_ctor_get(v_date_4491_, 19);
v_K_5130_ = lean_ctor_get(v_date_4491_, 20);
v_k_5131_ = lean_ctor_get(v_date_4491_, 21);
v_H_5132_ = lean_ctor_get(v_date_4491_, 22);
v_m_5133_ = lean_ctor_get(v_date_4491_, 23);
v_s_5134_ = lean_ctor_get(v_date_4491_, 24);
v_S_5135_ = lean_ctor_get(v_date_4491_, 25);
v_A_5136_ = lean_ctor_get(v_date_4491_, 26);
v_n_5137_ = lean_ctor_get(v_date_4491_, 27);
v_N_5138_ = lean_ctor_get(v_date_4491_, 28);
v_V_5139_ = lean_ctor_get(v_date_4491_, 29);
v_z_5140_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5141_ = lean_ctor_get(v_date_4491_, 31);
v_v_5142_ = lean_ctor_get(v_date_4491_, 32);
v_O_5143_ = lean_ctor_get(v_date_4491_, 33);
v_X_5144_ = lean_ctor_get(v_date_4491_, 34);
v_x_5145_ = lean_ctor_get(v_date_4491_, 35);
v_Z_5146_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5154_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5154_ == 0)
{
lean_object* v_unused_5155_; 
v_unused_5155_ = lean_ctor_get(v_date_4491_, 12);
lean_dec(v_unused_5155_);
v___x_5148_ = v_date_4491_;
v_isShared_5149_ = v_isSharedCheck_5154_;
goto v_resetjp_5147_;
}
else
{
lean_inc(v_Z_5146_);
lean_inc(v_x_5145_);
lean_inc(v_X_5144_);
lean_inc(v_O_5143_);
lean_inc(v_v_5142_);
lean_inc(v_zabbrev_5141_);
lean_inc(v_z_5140_);
lean_inc(v_V_5139_);
lean_inc(v_N_5138_);
lean_inc(v_n_5137_);
lean_inc(v_A_5136_);
lean_inc(v_S_5135_);
lean_inc(v_s_5134_);
lean_inc(v_m_5133_);
lean_inc(v_H_5132_);
lean_inc(v_k_5131_);
lean_inc(v_K_5130_);
lean_inc(v_h_5129_);
lean_inc(v_B_5128_);
lean_inc(v_b_5127_);
lean_inc(v_a_5126_);
lean_inc(v_F_5125_);
lean_inc(v_c_5124_);
lean_inc(v_e_5123_);
lean_inc(v_W_5122_);
lean_inc(v_w_5121_);
lean_inc(v_q_5120_);
lean_inc(v_Q_5119_);
lean_inc(v_d_5118_);
lean_inc(v_L_5117_);
lean_inc(v_M_5116_);
lean_inc(v_D_5115_);
lean_inc(v_Y_5114_);
lean_inc(v_u_5113_);
lean_inc(v_y_5112_);
lean_inc(v_G_5111_);
lean_dec(v_date_4491_);
v___x_5148_ = lean_box(0);
v_isShared_5149_ = v_isSharedCheck_5154_;
goto v_resetjp_5147_;
}
v_resetjp_5147_:
{
lean_object* v___x_5150_; lean_object* v___x_5152_; 
v___x_5150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5150_, 0, v_data_4493_);
if (v_isShared_5149_ == 0)
{
lean_ctor_set(v___x_5148_, 12, v___x_5150_);
v___x_5152_ = v___x_5148_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_G_5111_);
lean_ctor_set(v_reuseFailAlloc_5153_, 1, v_y_5112_);
lean_ctor_set(v_reuseFailAlloc_5153_, 2, v_u_5113_);
lean_ctor_set(v_reuseFailAlloc_5153_, 3, v_Y_5114_);
lean_ctor_set(v_reuseFailAlloc_5153_, 4, v_D_5115_);
lean_ctor_set(v_reuseFailAlloc_5153_, 5, v_M_5116_);
lean_ctor_set(v_reuseFailAlloc_5153_, 6, v_L_5117_);
lean_ctor_set(v_reuseFailAlloc_5153_, 7, v_d_5118_);
lean_ctor_set(v_reuseFailAlloc_5153_, 8, v_Q_5119_);
lean_ctor_set(v_reuseFailAlloc_5153_, 9, v_q_5120_);
lean_ctor_set(v_reuseFailAlloc_5153_, 10, v_w_5121_);
lean_ctor_set(v_reuseFailAlloc_5153_, 11, v_W_5122_);
lean_ctor_set(v_reuseFailAlloc_5153_, 12, v___x_5150_);
lean_ctor_set(v_reuseFailAlloc_5153_, 13, v_e_5123_);
lean_ctor_set(v_reuseFailAlloc_5153_, 14, v_c_5124_);
lean_ctor_set(v_reuseFailAlloc_5153_, 15, v_F_5125_);
lean_ctor_set(v_reuseFailAlloc_5153_, 16, v_a_5126_);
lean_ctor_set(v_reuseFailAlloc_5153_, 17, v_b_5127_);
lean_ctor_set(v_reuseFailAlloc_5153_, 18, v_B_5128_);
lean_ctor_set(v_reuseFailAlloc_5153_, 19, v_h_5129_);
lean_ctor_set(v_reuseFailAlloc_5153_, 20, v_K_5130_);
lean_ctor_set(v_reuseFailAlloc_5153_, 21, v_k_5131_);
lean_ctor_set(v_reuseFailAlloc_5153_, 22, v_H_5132_);
lean_ctor_set(v_reuseFailAlloc_5153_, 23, v_m_5133_);
lean_ctor_set(v_reuseFailAlloc_5153_, 24, v_s_5134_);
lean_ctor_set(v_reuseFailAlloc_5153_, 25, v_S_5135_);
lean_ctor_set(v_reuseFailAlloc_5153_, 26, v_A_5136_);
lean_ctor_set(v_reuseFailAlloc_5153_, 27, v_n_5137_);
lean_ctor_set(v_reuseFailAlloc_5153_, 28, v_N_5138_);
lean_ctor_set(v_reuseFailAlloc_5153_, 29, v_V_5139_);
lean_ctor_set(v_reuseFailAlloc_5153_, 30, v_z_5140_);
lean_ctor_set(v_reuseFailAlloc_5153_, 31, v_zabbrev_5141_);
lean_ctor_set(v_reuseFailAlloc_5153_, 32, v_v_5142_);
lean_ctor_set(v_reuseFailAlloc_5153_, 33, v_O_5143_);
lean_ctor_set(v_reuseFailAlloc_5153_, 34, v_X_5144_);
lean_ctor_set(v_reuseFailAlloc_5153_, 35, v_x_5145_);
lean_ctor_set(v_reuseFailAlloc_5153_, 36, v_Z_5146_);
v___x_5152_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
return v___x_5152_;
}
}
}
case 13:
{
lean_object* v___x_5157_; uint8_t v_isShared_5158_; uint8_t v_isSharedCheck_5206_; 
v_isSharedCheck_5206_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_5206_ == 0)
{
lean_object* v_unused_5207_; 
v_unused_5207_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_5207_);
v___x_5157_ = v_modifier_4492_;
v_isShared_5158_ = v_isSharedCheck_5206_;
goto v_resetjp_5156_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_5157_ = lean_box(0);
v_isShared_5158_ = v_isSharedCheck_5206_;
goto v_resetjp_5156_;
}
v_resetjp_5156_:
{
lean_object* v_G_5159_; lean_object* v_y_5160_; lean_object* v_u_5161_; lean_object* v_Y_5162_; lean_object* v_D_5163_; lean_object* v_M_5164_; lean_object* v_L_5165_; lean_object* v_d_5166_; lean_object* v_Q_5167_; lean_object* v_q_5168_; lean_object* v_w_5169_; lean_object* v_W_5170_; lean_object* v_E_5171_; lean_object* v_c_5172_; lean_object* v_F_5173_; lean_object* v_a_5174_; lean_object* v_b_5175_; lean_object* v_B_5176_; lean_object* v_h_5177_; lean_object* v_K_5178_; lean_object* v_k_5179_; lean_object* v_H_5180_; lean_object* v_m_5181_; lean_object* v_s_5182_; lean_object* v_S_5183_; lean_object* v_A_5184_; lean_object* v_n_5185_; lean_object* v_N_5186_; lean_object* v_V_5187_; lean_object* v_z_5188_; lean_object* v_zabbrev_5189_; lean_object* v_v_5190_; lean_object* v_O_5191_; lean_object* v_X_5192_; lean_object* v_x_5193_; lean_object* v_Z_5194_; lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5204_; 
v_G_5159_ = lean_ctor_get(v_date_4491_, 0);
v_y_5160_ = lean_ctor_get(v_date_4491_, 1);
v_u_5161_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5162_ = lean_ctor_get(v_date_4491_, 3);
v_D_5163_ = lean_ctor_get(v_date_4491_, 4);
v_M_5164_ = lean_ctor_get(v_date_4491_, 5);
v_L_5165_ = lean_ctor_get(v_date_4491_, 6);
v_d_5166_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5167_ = lean_ctor_get(v_date_4491_, 8);
v_q_5168_ = lean_ctor_get(v_date_4491_, 9);
v_w_5169_ = lean_ctor_get(v_date_4491_, 10);
v_W_5170_ = lean_ctor_get(v_date_4491_, 11);
v_E_5171_ = lean_ctor_get(v_date_4491_, 12);
v_c_5172_ = lean_ctor_get(v_date_4491_, 14);
v_F_5173_ = lean_ctor_get(v_date_4491_, 15);
v_a_5174_ = lean_ctor_get(v_date_4491_, 16);
v_b_5175_ = lean_ctor_get(v_date_4491_, 17);
v_B_5176_ = lean_ctor_get(v_date_4491_, 18);
v_h_5177_ = lean_ctor_get(v_date_4491_, 19);
v_K_5178_ = lean_ctor_get(v_date_4491_, 20);
v_k_5179_ = lean_ctor_get(v_date_4491_, 21);
v_H_5180_ = lean_ctor_get(v_date_4491_, 22);
v_m_5181_ = lean_ctor_get(v_date_4491_, 23);
v_s_5182_ = lean_ctor_get(v_date_4491_, 24);
v_S_5183_ = lean_ctor_get(v_date_4491_, 25);
v_A_5184_ = lean_ctor_get(v_date_4491_, 26);
v_n_5185_ = lean_ctor_get(v_date_4491_, 27);
v_N_5186_ = lean_ctor_get(v_date_4491_, 28);
v_V_5187_ = lean_ctor_get(v_date_4491_, 29);
v_z_5188_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5189_ = lean_ctor_get(v_date_4491_, 31);
v_v_5190_ = lean_ctor_get(v_date_4491_, 32);
v_O_5191_ = lean_ctor_get(v_date_4491_, 33);
v_X_5192_ = lean_ctor_get(v_date_4491_, 34);
v_x_5193_ = lean_ctor_get(v_date_4491_, 35);
v_Z_5194_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5204_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5204_ == 0)
{
lean_object* v_unused_5205_; 
v_unused_5205_ = lean_ctor_get(v_date_4491_, 13);
lean_dec(v_unused_5205_);
v___x_5196_ = v_date_4491_;
v_isShared_5197_ = v_isSharedCheck_5204_;
goto v_resetjp_5195_;
}
else
{
lean_inc(v_Z_5194_);
lean_inc(v_x_5193_);
lean_inc(v_X_5192_);
lean_inc(v_O_5191_);
lean_inc(v_v_5190_);
lean_inc(v_zabbrev_5189_);
lean_inc(v_z_5188_);
lean_inc(v_V_5187_);
lean_inc(v_N_5186_);
lean_inc(v_n_5185_);
lean_inc(v_A_5184_);
lean_inc(v_S_5183_);
lean_inc(v_s_5182_);
lean_inc(v_m_5181_);
lean_inc(v_H_5180_);
lean_inc(v_k_5179_);
lean_inc(v_K_5178_);
lean_inc(v_h_5177_);
lean_inc(v_B_5176_);
lean_inc(v_b_5175_);
lean_inc(v_a_5174_);
lean_inc(v_F_5173_);
lean_inc(v_c_5172_);
lean_inc(v_E_5171_);
lean_inc(v_W_5170_);
lean_inc(v_w_5169_);
lean_inc(v_q_5168_);
lean_inc(v_Q_5167_);
lean_inc(v_d_5166_);
lean_inc(v_L_5165_);
lean_inc(v_M_5164_);
lean_inc(v_D_5163_);
lean_inc(v_Y_5162_);
lean_inc(v_u_5161_);
lean_inc(v_y_5160_);
lean_inc(v_G_5159_);
lean_dec(v_date_4491_);
v___x_5196_ = lean_box(0);
v_isShared_5197_ = v_isSharedCheck_5204_;
goto v_resetjp_5195_;
}
v_resetjp_5195_:
{
lean_object* v___x_5199_; 
if (v_isShared_5158_ == 0)
{
lean_ctor_set_tag(v___x_5157_, 1);
lean_ctor_set(v___x_5157_, 0, v_data_4493_);
v___x_5199_ = v___x_5157_;
goto v_reusejp_5198_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v_data_4493_);
v___x_5199_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5198_;
}
v_reusejp_5198_:
{
lean_object* v___x_5201_; 
if (v_isShared_5197_ == 0)
{
lean_ctor_set(v___x_5196_, 13, v___x_5199_);
v___x_5201_ = v___x_5196_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v_G_5159_);
lean_ctor_set(v_reuseFailAlloc_5202_, 1, v_y_5160_);
lean_ctor_set(v_reuseFailAlloc_5202_, 2, v_u_5161_);
lean_ctor_set(v_reuseFailAlloc_5202_, 3, v_Y_5162_);
lean_ctor_set(v_reuseFailAlloc_5202_, 4, v_D_5163_);
lean_ctor_set(v_reuseFailAlloc_5202_, 5, v_M_5164_);
lean_ctor_set(v_reuseFailAlloc_5202_, 6, v_L_5165_);
lean_ctor_set(v_reuseFailAlloc_5202_, 7, v_d_5166_);
lean_ctor_set(v_reuseFailAlloc_5202_, 8, v_Q_5167_);
lean_ctor_set(v_reuseFailAlloc_5202_, 9, v_q_5168_);
lean_ctor_set(v_reuseFailAlloc_5202_, 10, v_w_5169_);
lean_ctor_set(v_reuseFailAlloc_5202_, 11, v_W_5170_);
lean_ctor_set(v_reuseFailAlloc_5202_, 12, v_E_5171_);
lean_ctor_set(v_reuseFailAlloc_5202_, 13, v___x_5199_);
lean_ctor_set(v_reuseFailAlloc_5202_, 14, v_c_5172_);
lean_ctor_set(v_reuseFailAlloc_5202_, 15, v_F_5173_);
lean_ctor_set(v_reuseFailAlloc_5202_, 16, v_a_5174_);
lean_ctor_set(v_reuseFailAlloc_5202_, 17, v_b_5175_);
lean_ctor_set(v_reuseFailAlloc_5202_, 18, v_B_5176_);
lean_ctor_set(v_reuseFailAlloc_5202_, 19, v_h_5177_);
lean_ctor_set(v_reuseFailAlloc_5202_, 20, v_K_5178_);
lean_ctor_set(v_reuseFailAlloc_5202_, 21, v_k_5179_);
lean_ctor_set(v_reuseFailAlloc_5202_, 22, v_H_5180_);
lean_ctor_set(v_reuseFailAlloc_5202_, 23, v_m_5181_);
lean_ctor_set(v_reuseFailAlloc_5202_, 24, v_s_5182_);
lean_ctor_set(v_reuseFailAlloc_5202_, 25, v_S_5183_);
lean_ctor_set(v_reuseFailAlloc_5202_, 26, v_A_5184_);
lean_ctor_set(v_reuseFailAlloc_5202_, 27, v_n_5185_);
lean_ctor_set(v_reuseFailAlloc_5202_, 28, v_N_5186_);
lean_ctor_set(v_reuseFailAlloc_5202_, 29, v_V_5187_);
lean_ctor_set(v_reuseFailAlloc_5202_, 30, v_z_5188_);
lean_ctor_set(v_reuseFailAlloc_5202_, 31, v_zabbrev_5189_);
lean_ctor_set(v_reuseFailAlloc_5202_, 32, v_v_5190_);
lean_ctor_set(v_reuseFailAlloc_5202_, 33, v_O_5191_);
lean_ctor_set(v_reuseFailAlloc_5202_, 34, v_X_5192_);
lean_ctor_set(v_reuseFailAlloc_5202_, 35, v_x_5193_);
lean_ctor_set(v_reuseFailAlloc_5202_, 36, v_Z_5194_);
v___x_5201_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
return v___x_5201_;
}
}
}
}
}
case 14:
{
lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5258_; 
v_isSharedCheck_5258_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_5258_ == 0)
{
lean_object* v_unused_5259_; 
v_unused_5259_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_5259_);
v___x_5209_ = v_modifier_4492_;
v_isShared_5210_ = v_isSharedCheck_5258_;
goto v_resetjp_5208_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_5209_ = lean_box(0);
v_isShared_5210_ = v_isSharedCheck_5258_;
goto v_resetjp_5208_;
}
v_resetjp_5208_:
{
lean_object* v_G_5211_; lean_object* v_y_5212_; lean_object* v_u_5213_; lean_object* v_Y_5214_; lean_object* v_D_5215_; lean_object* v_M_5216_; lean_object* v_L_5217_; lean_object* v_d_5218_; lean_object* v_Q_5219_; lean_object* v_q_5220_; lean_object* v_w_5221_; lean_object* v_W_5222_; lean_object* v_E_5223_; lean_object* v_e_5224_; lean_object* v_F_5225_; lean_object* v_a_5226_; lean_object* v_b_5227_; lean_object* v_B_5228_; lean_object* v_h_5229_; lean_object* v_K_5230_; lean_object* v_k_5231_; lean_object* v_H_5232_; lean_object* v_m_5233_; lean_object* v_s_5234_; lean_object* v_S_5235_; lean_object* v_A_5236_; lean_object* v_n_5237_; lean_object* v_N_5238_; lean_object* v_V_5239_; lean_object* v_z_5240_; lean_object* v_zabbrev_5241_; lean_object* v_v_5242_; lean_object* v_O_5243_; lean_object* v_X_5244_; lean_object* v_x_5245_; lean_object* v_Z_5246_; lean_object* v___x_5248_; uint8_t v_isShared_5249_; uint8_t v_isSharedCheck_5256_; 
v_G_5211_ = lean_ctor_get(v_date_4491_, 0);
v_y_5212_ = lean_ctor_get(v_date_4491_, 1);
v_u_5213_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5214_ = lean_ctor_get(v_date_4491_, 3);
v_D_5215_ = lean_ctor_get(v_date_4491_, 4);
v_M_5216_ = lean_ctor_get(v_date_4491_, 5);
v_L_5217_ = lean_ctor_get(v_date_4491_, 6);
v_d_5218_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5219_ = lean_ctor_get(v_date_4491_, 8);
v_q_5220_ = lean_ctor_get(v_date_4491_, 9);
v_w_5221_ = lean_ctor_get(v_date_4491_, 10);
v_W_5222_ = lean_ctor_get(v_date_4491_, 11);
v_E_5223_ = lean_ctor_get(v_date_4491_, 12);
v_e_5224_ = lean_ctor_get(v_date_4491_, 13);
v_F_5225_ = lean_ctor_get(v_date_4491_, 15);
v_a_5226_ = lean_ctor_get(v_date_4491_, 16);
v_b_5227_ = lean_ctor_get(v_date_4491_, 17);
v_B_5228_ = lean_ctor_get(v_date_4491_, 18);
v_h_5229_ = lean_ctor_get(v_date_4491_, 19);
v_K_5230_ = lean_ctor_get(v_date_4491_, 20);
v_k_5231_ = lean_ctor_get(v_date_4491_, 21);
v_H_5232_ = lean_ctor_get(v_date_4491_, 22);
v_m_5233_ = lean_ctor_get(v_date_4491_, 23);
v_s_5234_ = lean_ctor_get(v_date_4491_, 24);
v_S_5235_ = lean_ctor_get(v_date_4491_, 25);
v_A_5236_ = lean_ctor_get(v_date_4491_, 26);
v_n_5237_ = lean_ctor_get(v_date_4491_, 27);
v_N_5238_ = lean_ctor_get(v_date_4491_, 28);
v_V_5239_ = lean_ctor_get(v_date_4491_, 29);
v_z_5240_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5241_ = lean_ctor_get(v_date_4491_, 31);
v_v_5242_ = lean_ctor_get(v_date_4491_, 32);
v_O_5243_ = lean_ctor_get(v_date_4491_, 33);
v_X_5244_ = lean_ctor_get(v_date_4491_, 34);
v_x_5245_ = lean_ctor_get(v_date_4491_, 35);
v_Z_5246_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5256_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5256_ == 0)
{
lean_object* v_unused_5257_; 
v_unused_5257_ = lean_ctor_get(v_date_4491_, 14);
lean_dec(v_unused_5257_);
v___x_5248_ = v_date_4491_;
v_isShared_5249_ = v_isSharedCheck_5256_;
goto v_resetjp_5247_;
}
else
{
lean_inc(v_Z_5246_);
lean_inc(v_x_5245_);
lean_inc(v_X_5244_);
lean_inc(v_O_5243_);
lean_inc(v_v_5242_);
lean_inc(v_zabbrev_5241_);
lean_inc(v_z_5240_);
lean_inc(v_V_5239_);
lean_inc(v_N_5238_);
lean_inc(v_n_5237_);
lean_inc(v_A_5236_);
lean_inc(v_S_5235_);
lean_inc(v_s_5234_);
lean_inc(v_m_5233_);
lean_inc(v_H_5232_);
lean_inc(v_k_5231_);
lean_inc(v_K_5230_);
lean_inc(v_h_5229_);
lean_inc(v_B_5228_);
lean_inc(v_b_5227_);
lean_inc(v_a_5226_);
lean_inc(v_F_5225_);
lean_inc(v_e_5224_);
lean_inc(v_E_5223_);
lean_inc(v_W_5222_);
lean_inc(v_w_5221_);
lean_inc(v_q_5220_);
lean_inc(v_Q_5219_);
lean_inc(v_d_5218_);
lean_inc(v_L_5217_);
lean_inc(v_M_5216_);
lean_inc(v_D_5215_);
lean_inc(v_Y_5214_);
lean_inc(v_u_5213_);
lean_inc(v_y_5212_);
lean_inc(v_G_5211_);
lean_dec(v_date_4491_);
v___x_5248_ = lean_box(0);
v_isShared_5249_ = v_isSharedCheck_5256_;
goto v_resetjp_5247_;
}
v_resetjp_5247_:
{
lean_object* v___x_5251_; 
if (v_isShared_5210_ == 0)
{
lean_ctor_set_tag(v___x_5209_, 1);
lean_ctor_set(v___x_5209_, 0, v_data_4493_);
v___x_5251_ = v___x_5209_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5255_; 
v_reuseFailAlloc_5255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5255_, 0, v_data_4493_);
v___x_5251_ = v_reuseFailAlloc_5255_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
lean_object* v___x_5253_; 
if (v_isShared_5249_ == 0)
{
lean_ctor_set(v___x_5248_, 14, v___x_5251_);
v___x_5253_ = v___x_5248_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_G_5211_);
lean_ctor_set(v_reuseFailAlloc_5254_, 1, v_y_5212_);
lean_ctor_set(v_reuseFailAlloc_5254_, 2, v_u_5213_);
lean_ctor_set(v_reuseFailAlloc_5254_, 3, v_Y_5214_);
lean_ctor_set(v_reuseFailAlloc_5254_, 4, v_D_5215_);
lean_ctor_set(v_reuseFailAlloc_5254_, 5, v_M_5216_);
lean_ctor_set(v_reuseFailAlloc_5254_, 6, v_L_5217_);
lean_ctor_set(v_reuseFailAlloc_5254_, 7, v_d_5218_);
lean_ctor_set(v_reuseFailAlloc_5254_, 8, v_Q_5219_);
lean_ctor_set(v_reuseFailAlloc_5254_, 9, v_q_5220_);
lean_ctor_set(v_reuseFailAlloc_5254_, 10, v_w_5221_);
lean_ctor_set(v_reuseFailAlloc_5254_, 11, v_W_5222_);
lean_ctor_set(v_reuseFailAlloc_5254_, 12, v_E_5223_);
lean_ctor_set(v_reuseFailAlloc_5254_, 13, v_e_5224_);
lean_ctor_set(v_reuseFailAlloc_5254_, 14, v___x_5251_);
lean_ctor_set(v_reuseFailAlloc_5254_, 15, v_F_5225_);
lean_ctor_set(v_reuseFailAlloc_5254_, 16, v_a_5226_);
lean_ctor_set(v_reuseFailAlloc_5254_, 17, v_b_5227_);
lean_ctor_set(v_reuseFailAlloc_5254_, 18, v_B_5228_);
lean_ctor_set(v_reuseFailAlloc_5254_, 19, v_h_5229_);
lean_ctor_set(v_reuseFailAlloc_5254_, 20, v_K_5230_);
lean_ctor_set(v_reuseFailAlloc_5254_, 21, v_k_5231_);
lean_ctor_set(v_reuseFailAlloc_5254_, 22, v_H_5232_);
lean_ctor_set(v_reuseFailAlloc_5254_, 23, v_m_5233_);
lean_ctor_set(v_reuseFailAlloc_5254_, 24, v_s_5234_);
lean_ctor_set(v_reuseFailAlloc_5254_, 25, v_S_5235_);
lean_ctor_set(v_reuseFailAlloc_5254_, 26, v_A_5236_);
lean_ctor_set(v_reuseFailAlloc_5254_, 27, v_n_5237_);
lean_ctor_set(v_reuseFailAlloc_5254_, 28, v_N_5238_);
lean_ctor_set(v_reuseFailAlloc_5254_, 29, v_V_5239_);
lean_ctor_set(v_reuseFailAlloc_5254_, 30, v_z_5240_);
lean_ctor_set(v_reuseFailAlloc_5254_, 31, v_zabbrev_5241_);
lean_ctor_set(v_reuseFailAlloc_5254_, 32, v_v_5242_);
lean_ctor_set(v_reuseFailAlloc_5254_, 33, v_O_5243_);
lean_ctor_set(v_reuseFailAlloc_5254_, 34, v_X_5244_);
lean_ctor_set(v_reuseFailAlloc_5254_, 35, v_x_5245_);
lean_ctor_set(v_reuseFailAlloc_5254_, 36, v_Z_5246_);
v___x_5253_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
return v___x_5253_;
}
}
}
}
}
case 15:
{
lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5310_; 
v_isSharedCheck_5310_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_5310_ == 0)
{
lean_object* v_unused_5311_; 
v_unused_5311_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_5311_);
v___x_5261_ = v_modifier_4492_;
v_isShared_5262_ = v_isSharedCheck_5310_;
goto v_resetjp_5260_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5310_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v_G_5263_; lean_object* v_y_5264_; lean_object* v_u_5265_; lean_object* v_Y_5266_; lean_object* v_D_5267_; lean_object* v_M_5268_; lean_object* v_L_5269_; lean_object* v_d_5270_; lean_object* v_Q_5271_; lean_object* v_q_5272_; lean_object* v_w_5273_; lean_object* v_W_5274_; lean_object* v_E_5275_; lean_object* v_e_5276_; lean_object* v_c_5277_; lean_object* v_a_5278_; lean_object* v_b_5279_; lean_object* v_B_5280_; lean_object* v_h_5281_; lean_object* v_K_5282_; lean_object* v_k_5283_; lean_object* v_H_5284_; lean_object* v_m_5285_; lean_object* v_s_5286_; lean_object* v_S_5287_; lean_object* v_A_5288_; lean_object* v_n_5289_; lean_object* v_N_5290_; lean_object* v_V_5291_; lean_object* v_z_5292_; lean_object* v_zabbrev_5293_; lean_object* v_v_5294_; lean_object* v_O_5295_; lean_object* v_X_5296_; lean_object* v_x_5297_; lean_object* v_Z_5298_; lean_object* v___x_5300_; uint8_t v_isShared_5301_; uint8_t v_isSharedCheck_5308_; 
v_G_5263_ = lean_ctor_get(v_date_4491_, 0);
v_y_5264_ = lean_ctor_get(v_date_4491_, 1);
v_u_5265_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5266_ = lean_ctor_get(v_date_4491_, 3);
v_D_5267_ = lean_ctor_get(v_date_4491_, 4);
v_M_5268_ = lean_ctor_get(v_date_4491_, 5);
v_L_5269_ = lean_ctor_get(v_date_4491_, 6);
v_d_5270_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5271_ = lean_ctor_get(v_date_4491_, 8);
v_q_5272_ = lean_ctor_get(v_date_4491_, 9);
v_w_5273_ = lean_ctor_get(v_date_4491_, 10);
v_W_5274_ = lean_ctor_get(v_date_4491_, 11);
v_E_5275_ = lean_ctor_get(v_date_4491_, 12);
v_e_5276_ = lean_ctor_get(v_date_4491_, 13);
v_c_5277_ = lean_ctor_get(v_date_4491_, 14);
v_a_5278_ = lean_ctor_get(v_date_4491_, 16);
v_b_5279_ = lean_ctor_get(v_date_4491_, 17);
v_B_5280_ = lean_ctor_get(v_date_4491_, 18);
v_h_5281_ = lean_ctor_get(v_date_4491_, 19);
v_K_5282_ = lean_ctor_get(v_date_4491_, 20);
v_k_5283_ = lean_ctor_get(v_date_4491_, 21);
v_H_5284_ = lean_ctor_get(v_date_4491_, 22);
v_m_5285_ = lean_ctor_get(v_date_4491_, 23);
v_s_5286_ = lean_ctor_get(v_date_4491_, 24);
v_S_5287_ = lean_ctor_get(v_date_4491_, 25);
v_A_5288_ = lean_ctor_get(v_date_4491_, 26);
v_n_5289_ = lean_ctor_get(v_date_4491_, 27);
v_N_5290_ = lean_ctor_get(v_date_4491_, 28);
v_V_5291_ = lean_ctor_get(v_date_4491_, 29);
v_z_5292_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5293_ = lean_ctor_get(v_date_4491_, 31);
v_v_5294_ = lean_ctor_get(v_date_4491_, 32);
v_O_5295_ = lean_ctor_get(v_date_4491_, 33);
v_X_5296_ = lean_ctor_get(v_date_4491_, 34);
v_x_5297_ = lean_ctor_get(v_date_4491_, 35);
v_Z_5298_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5308_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5308_ == 0)
{
lean_object* v_unused_5309_; 
v_unused_5309_ = lean_ctor_get(v_date_4491_, 15);
lean_dec(v_unused_5309_);
v___x_5300_ = v_date_4491_;
v_isShared_5301_ = v_isSharedCheck_5308_;
goto v_resetjp_5299_;
}
else
{
lean_inc(v_Z_5298_);
lean_inc(v_x_5297_);
lean_inc(v_X_5296_);
lean_inc(v_O_5295_);
lean_inc(v_v_5294_);
lean_inc(v_zabbrev_5293_);
lean_inc(v_z_5292_);
lean_inc(v_V_5291_);
lean_inc(v_N_5290_);
lean_inc(v_n_5289_);
lean_inc(v_A_5288_);
lean_inc(v_S_5287_);
lean_inc(v_s_5286_);
lean_inc(v_m_5285_);
lean_inc(v_H_5284_);
lean_inc(v_k_5283_);
lean_inc(v_K_5282_);
lean_inc(v_h_5281_);
lean_inc(v_B_5280_);
lean_inc(v_b_5279_);
lean_inc(v_a_5278_);
lean_inc(v_c_5277_);
lean_inc(v_e_5276_);
lean_inc(v_E_5275_);
lean_inc(v_W_5274_);
lean_inc(v_w_5273_);
lean_inc(v_q_5272_);
lean_inc(v_Q_5271_);
lean_inc(v_d_5270_);
lean_inc(v_L_5269_);
lean_inc(v_M_5268_);
lean_inc(v_D_5267_);
lean_inc(v_Y_5266_);
lean_inc(v_u_5265_);
lean_inc(v_y_5264_);
lean_inc(v_G_5263_);
lean_dec(v_date_4491_);
v___x_5300_ = lean_box(0);
v_isShared_5301_ = v_isSharedCheck_5308_;
goto v_resetjp_5299_;
}
v_resetjp_5299_:
{
lean_object* v___x_5303_; 
if (v_isShared_5262_ == 0)
{
lean_ctor_set_tag(v___x_5261_, 1);
lean_ctor_set(v___x_5261_, 0, v_data_4493_);
v___x_5303_ = v___x_5261_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5307_; 
v_reuseFailAlloc_5307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5307_, 0, v_data_4493_);
v___x_5303_ = v_reuseFailAlloc_5307_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
lean_object* v___x_5305_; 
if (v_isShared_5301_ == 0)
{
lean_ctor_set(v___x_5300_, 15, v___x_5303_);
v___x_5305_ = v___x_5300_;
goto v_reusejp_5304_;
}
else
{
lean_object* v_reuseFailAlloc_5306_; 
v_reuseFailAlloc_5306_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5306_, 0, v_G_5263_);
lean_ctor_set(v_reuseFailAlloc_5306_, 1, v_y_5264_);
lean_ctor_set(v_reuseFailAlloc_5306_, 2, v_u_5265_);
lean_ctor_set(v_reuseFailAlloc_5306_, 3, v_Y_5266_);
lean_ctor_set(v_reuseFailAlloc_5306_, 4, v_D_5267_);
lean_ctor_set(v_reuseFailAlloc_5306_, 5, v_M_5268_);
lean_ctor_set(v_reuseFailAlloc_5306_, 6, v_L_5269_);
lean_ctor_set(v_reuseFailAlloc_5306_, 7, v_d_5270_);
lean_ctor_set(v_reuseFailAlloc_5306_, 8, v_Q_5271_);
lean_ctor_set(v_reuseFailAlloc_5306_, 9, v_q_5272_);
lean_ctor_set(v_reuseFailAlloc_5306_, 10, v_w_5273_);
lean_ctor_set(v_reuseFailAlloc_5306_, 11, v_W_5274_);
lean_ctor_set(v_reuseFailAlloc_5306_, 12, v_E_5275_);
lean_ctor_set(v_reuseFailAlloc_5306_, 13, v_e_5276_);
lean_ctor_set(v_reuseFailAlloc_5306_, 14, v_c_5277_);
lean_ctor_set(v_reuseFailAlloc_5306_, 15, v___x_5303_);
lean_ctor_set(v_reuseFailAlloc_5306_, 16, v_a_5278_);
lean_ctor_set(v_reuseFailAlloc_5306_, 17, v_b_5279_);
lean_ctor_set(v_reuseFailAlloc_5306_, 18, v_B_5280_);
lean_ctor_set(v_reuseFailAlloc_5306_, 19, v_h_5281_);
lean_ctor_set(v_reuseFailAlloc_5306_, 20, v_K_5282_);
lean_ctor_set(v_reuseFailAlloc_5306_, 21, v_k_5283_);
lean_ctor_set(v_reuseFailAlloc_5306_, 22, v_H_5284_);
lean_ctor_set(v_reuseFailAlloc_5306_, 23, v_m_5285_);
lean_ctor_set(v_reuseFailAlloc_5306_, 24, v_s_5286_);
lean_ctor_set(v_reuseFailAlloc_5306_, 25, v_S_5287_);
lean_ctor_set(v_reuseFailAlloc_5306_, 26, v_A_5288_);
lean_ctor_set(v_reuseFailAlloc_5306_, 27, v_n_5289_);
lean_ctor_set(v_reuseFailAlloc_5306_, 28, v_N_5290_);
lean_ctor_set(v_reuseFailAlloc_5306_, 29, v_V_5291_);
lean_ctor_set(v_reuseFailAlloc_5306_, 30, v_z_5292_);
lean_ctor_set(v_reuseFailAlloc_5306_, 31, v_zabbrev_5293_);
lean_ctor_set(v_reuseFailAlloc_5306_, 32, v_v_5294_);
lean_ctor_set(v_reuseFailAlloc_5306_, 33, v_O_5295_);
lean_ctor_set(v_reuseFailAlloc_5306_, 34, v_X_5296_);
lean_ctor_set(v_reuseFailAlloc_5306_, 35, v_x_5297_);
lean_ctor_set(v_reuseFailAlloc_5306_, 36, v_Z_5298_);
v___x_5305_ = v_reuseFailAlloc_5306_;
goto v_reusejp_5304_;
}
v_reusejp_5304_:
{
return v___x_5305_;
}
}
}
}
}
case 16:
{
lean_object* v_G_5312_; lean_object* v_y_5313_; lean_object* v_u_5314_; lean_object* v_Y_5315_; lean_object* v_D_5316_; lean_object* v_M_5317_; lean_object* v_L_5318_; lean_object* v_d_5319_; lean_object* v_Q_5320_; lean_object* v_q_5321_; lean_object* v_w_5322_; lean_object* v_W_5323_; lean_object* v_E_5324_; lean_object* v_e_5325_; lean_object* v_c_5326_; lean_object* v_F_5327_; lean_object* v_b_5328_; lean_object* v_B_5329_; lean_object* v_h_5330_; lean_object* v_K_5331_; lean_object* v_k_5332_; lean_object* v_H_5333_; lean_object* v_m_5334_; lean_object* v_s_5335_; lean_object* v_S_5336_; lean_object* v_A_5337_; lean_object* v_n_5338_; lean_object* v_N_5339_; lean_object* v_V_5340_; lean_object* v_z_5341_; lean_object* v_zabbrev_5342_; lean_object* v_v_5343_; lean_object* v_O_5344_; lean_object* v_X_5345_; lean_object* v_x_5346_; lean_object* v_Z_5347_; lean_object* v___x_5349_; uint8_t v_isShared_5350_; uint8_t v_isSharedCheck_5355_; 
lean_dec_ref_known(v_modifier_4492_, 0);
v_G_5312_ = lean_ctor_get(v_date_4491_, 0);
v_y_5313_ = lean_ctor_get(v_date_4491_, 1);
v_u_5314_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5315_ = lean_ctor_get(v_date_4491_, 3);
v_D_5316_ = lean_ctor_get(v_date_4491_, 4);
v_M_5317_ = lean_ctor_get(v_date_4491_, 5);
v_L_5318_ = lean_ctor_get(v_date_4491_, 6);
v_d_5319_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5320_ = lean_ctor_get(v_date_4491_, 8);
v_q_5321_ = lean_ctor_get(v_date_4491_, 9);
v_w_5322_ = lean_ctor_get(v_date_4491_, 10);
v_W_5323_ = lean_ctor_get(v_date_4491_, 11);
v_E_5324_ = lean_ctor_get(v_date_4491_, 12);
v_e_5325_ = lean_ctor_get(v_date_4491_, 13);
v_c_5326_ = lean_ctor_get(v_date_4491_, 14);
v_F_5327_ = lean_ctor_get(v_date_4491_, 15);
v_b_5328_ = lean_ctor_get(v_date_4491_, 17);
v_B_5329_ = lean_ctor_get(v_date_4491_, 18);
v_h_5330_ = lean_ctor_get(v_date_4491_, 19);
v_K_5331_ = lean_ctor_get(v_date_4491_, 20);
v_k_5332_ = lean_ctor_get(v_date_4491_, 21);
v_H_5333_ = lean_ctor_get(v_date_4491_, 22);
v_m_5334_ = lean_ctor_get(v_date_4491_, 23);
v_s_5335_ = lean_ctor_get(v_date_4491_, 24);
v_S_5336_ = lean_ctor_get(v_date_4491_, 25);
v_A_5337_ = lean_ctor_get(v_date_4491_, 26);
v_n_5338_ = lean_ctor_get(v_date_4491_, 27);
v_N_5339_ = lean_ctor_get(v_date_4491_, 28);
v_V_5340_ = lean_ctor_get(v_date_4491_, 29);
v_z_5341_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5342_ = lean_ctor_get(v_date_4491_, 31);
v_v_5343_ = lean_ctor_get(v_date_4491_, 32);
v_O_5344_ = lean_ctor_get(v_date_4491_, 33);
v_X_5345_ = lean_ctor_get(v_date_4491_, 34);
v_x_5346_ = lean_ctor_get(v_date_4491_, 35);
v_Z_5347_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5355_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5355_ == 0)
{
lean_object* v_unused_5356_; 
v_unused_5356_ = lean_ctor_get(v_date_4491_, 16);
lean_dec(v_unused_5356_);
v___x_5349_ = v_date_4491_;
v_isShared_5350_ = v_isSharedCheck_5355_;
goto v_resetjp_5348_;
}
else
{
lean_inc(v_Z_5347_);
lean_inc(v_x_5346_);
lean_inc(v_X_5345_);
lean_inc(v_O_5344_);
lean_inc(v_v_5343_);
lean_inc(v_zabbrev_5342_);
lean_inc(v_z_5341_);
lean_inc(v_V_5340_);
lean_inc(v_N_5339_);
lean_inc(v_n_5338_);
lean_inc(v_A_5337_);
lean_inc(v_S_5336_);
lean_inc(v_s_5335_);
lean_inc(v_m_5334_);
lean_inc(v_H_5333_);
lean_inc(v_k_5332_);
lean_inc(v_K_5331_);
lean_inc(v_h_5330_);
lean_inc(v_B_5329_);
lean_inc(v_b_5328_);
lean_inc(v_F_5327_);
lean_inc(v_c_5326_);
lean_inc(v_e_5325_);
lean_inc(v_E_5324_);
lean_inc(v_W_5323_);
lean_inc(v_w_5322_);
lean_inc(v_q_5321_);
lean_inc(v_Q_5320_);
lean_inc(v_d_5319_);
lean_inc(v_L_5318_);
lean_inc(v_M_5317_);
lean_inc(v_D_5316_);
lean_inc(v_Y_5315_);
lean_inc(v_u_5314_);
lean_inc(v_y_5313_);
lean_inc(v_G_5312_);
lean_dec(v_date_4491_);
v___x_5349_ = lean_box(0);
v_isShared_5350_ = v_isSharedCheck_5355_;
goto v_resetjp_5348_;
}
v_resetjp_5348_:
{
lean_object* v___x_5351_; lean_object* v___x_5353_; 
v___x_5351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5351_, 0, v_data_4493_);
if (v_isShared_5350_ == 0)
{
lean_ctor_set(v___x_5349_, 16, v___x_5351_);
v___x_5353_ = v___x_5349_;
goto v_reusejp_5352_;
}
else
{
lean_object* v_reuseFailAlloc_5354_; 
v_reuseFailAlloc_5354_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5354_, 0, v_G_5312_);
lean_ctor_set(v_reuseFailAlloc_5354_, 1, v_y_5313_);
lean_ctor_set(v_reuseFailAlloc_5354_, 2, v_u_5314_);
lean_ctor_set(v_reuseFailAlloc_5354_, 3, v_Y_5315_);
lean_ctor_set(v_reuseFailAlloc_5354_, 4, v_D_5316_);
lean_ctor_set(v_reuseFailAlloc_5354_, 5, v_M_5317_);
lean_ctor_set(v_reuseFailAlloc_5354_, 6, v_L_5318_);
lean_ctor_set(v_reuseFailAlloc_5354_, 7, v_d_5319_);
lean_ctor_set(v_reuseFailAlloc_5354_, 8, v_Q_5320_);
lean_ctor_set(v_reuseFailAlloc_5354_, 9, v_q_5321_);
lean_ctor_set(v_reuseFailAlloc_5354_, 10, v_w_5322_);
lean_ctor_set(v_reuseFailAlloc_5354_, 11, v_W_5323_);
lean_ctor_set(v_reuseFailAlloc_5354_, 12, v_E_5324_);
lean_ctor_set(v_reuseFailAlloc_5354_, 13, v_e_5325_);
lean_ctor_set(v_reuseFailAlloc_5354_, 14, v_c_5326_);
lean_ctor_set(v_reuseFailAlloc_5354_, 15, v_F_5327_);
lean_ctor_set(v_reuseFailAlloc_5354_, 16, v___x_5351_);
lean_ctor_set(v_reuseFailAlloc_5354_, 17, v_b_5328_);
lean_ctor_set(v_reuseFailAlloc_5354_, 18, v_B_5329_);
lean_ctor_set(v_reuseFailAlloc_5354_, 19, v_h_5330_);
lean_ctor_set(v_reuseFailAlloc_5354_, 20, v_K_5331_);
lean_ctor_set(v_reuseFailAlloc_5354_, 21, v_k_5332_);
lean_ctor_set(v_reuseFailAlloc_5354_, 22, v_H_5333_);
lean_ctor_set(v_reuseFailAlloc_5354_, 23, v_m_5334_);
lean_ctor_set(v_reuseFailAlloc_5354_, 24, v_s_5335_);
lean_ctor_set(v_reuseFailAlloc_5354_, 25, v_S_5336_);
lean_ctor_set(v_reuseFailAlloc_5354_, 26, v_A_5337_);
lean_ctor_set(v_reuseFailAlloc_5354_, 27, v_n_5338_);
lean_ctor_set(v_reuseFailAlloc_5354_, 28, v_N_5339_);
lean_ctor_set(v_reuseFailAlloc_5354_, 29, v_V_5340_);
lean_ctor_set(v_reuseFailAlloc_5354_, 30, v_z_5341_);
lean_ctor_set(v_reuseFailAlloc_5354_, 31, v_zabbrev_5342_);
lean_ctor_set(v_reuseFailAlloc_5354_, 32, v_v_5343_);
lean_ctor_set(v_reuseFailAlloc_5354_, 33, v_O_5344_);
lean_ctor_set(v_reuseFailAlloc_5354_, 34, v_X_5345_);
lean_ctor_set(v_reuseFailAlloc_5354_, 35, v_x_5346_);
lean_ctor_set(v_reuseFailAlloc_5354_, 36, v_Z_5347_);
v___x_5353_ = v_reuseFailAlloc_5354_;
goto v_reusejp_5352_;
}
v_reusejp_5352_:
{
return v___x_5353_;
}
}
}
case 17:
{
lean_object* v_G_5357_; lean_object* v_y_5358_; lean_object* v_u_5359_; lean_object* v_Y_5360_; lean_object* v_D_5361_; lean_object* v_M_5362_; lean_object* v_L_5363_; lean_object* v_d_5364_; lean_object* v_Q_5365_; lean_object* v_q_5366_; lean_object* v_w_5367_; lean_object* v_W_5368_; lean_object* v_E_5369_; lean_object* v_e_5370_; lean_object* v_c_5371_; lean_object* v_F_5372_; lean_object* v_a_5373_; lean_object* v_B_5374_; lean_object* v_h_5375_; lean_object* v_K_5376_; lean_object* v_k_5377_; lean_object* v_H_5378_; lean_object* v_m_5379_; lean_object* v_s_5380_; lean_object* v_S_5381_; lean_object* v_A_5382_; lean_object* v_n_5383_; lean_object* v_N_5384_; lean_object* v_V_5385_; lean_object* v_z_5386_; lean_object* v_zabbrev_5387_; lean_object* v_v_5388_; lean_object* v_O_5389_; lean_object* v_X_5390_; lean_object* v_x_5391_; lean_object* v_Z_5392_; lean_object* v___x_5394_; uint8_t v_isShared_5395_; uint8_t v_isSharedCheck_5400_; 
lean_dec_ref_known(v_modifier_4492_, 0);
v_G_5357_ = lean_ctor_get(v_date_4491_, 0);
v_y_5358_ = lean_ctor_get(v_date_4491_, 1);
v_u_5359_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5360_ = lean_ctor_get(v_date_4491_, 3);
v_D_5361_ = lean_ctor_get(v_date_4491_, 4);
v_M_5362_ = lean_ctor_get(v_date_4491_, 5);
v_L_5363_ = lean_ctor_get(v_date_4491_, 6);
v_d_5364_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5365_ = lean_ctor_get(v_date_4491_, 8);
v_q_5366_ = lean_ctor_get(v_date_4491_, 9);
v_w_5367_ = lean_ctor_get(v_date_4491_, 10);
v_W_5368_ = lean_ctor_get(v_date_4491_, 11);
v_E_5369_ = lean_ctor_get(v_date_4491_, 12);
v_e_5370_ = lean_ctor_get(v_date_4491_, 13);
v_c_5371_ = lean_ctor_get(v_date_4491_, 14);
v_F_5372_ = lean_ctor_get(v_date_4491_, 15);
v_a_5373_ = lean_ctor_get(v_date_4491_, 16);
v_B_5374_ = lean_ctor_get(v_date_4491_, 18);
v_h_5375_ = lean_ctor_get(v_date_4491_, 19);
v_K_5376_ = lean_ctor_get(v_date_4491_, 20);
v_k_5377_ = lean_ctor_get(v_date_4491_, 21);
v_H_5378_ = lean_ctor_get(v_date_4491_, 22);
v_m_5379_ = lean_ctor_get(v_date_4491_, 23);
v_s_5380_ = lean_ctor_get(v_date_4491_, 24);
v_S_5381_ = lean_ctor_get(v_date_4491_, 25);
v_A_5382_ = lean_ctor_get(v_date_4491_, 26);
v_n_5383_ = lean_ctor_get(v_date_4491_, 27);
v_N_5384_ = lean_ctor_get(v_date_4491_, 28);
v_V_5385_ = lean_ctor_get(v_date_4491_, 29);
v_z_5386_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5387_ = lean_ctor_get(v_date_4491_, 31);
v_v_5388_ = lean_ctor_get(v_date_4491_, 32);
v_O_5389_ = lean_ctor_get(v_date_4491_, 33);
v_X_5390_ = lean_ctor_get(v_date_4491_, 34);
v_x_5391_ = lean_ctor_get(v_date_4491_, 35);
v_Z_5392_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5400_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5400_ == 0)
{
lean_object* v_unused_5401_; 
v_unused_5401_ = lean_ctor_get(v_date_4491_, 17);
lean_dec(v_unused_5401_);
v___x_5394_ = v_date_4491_;
v_isShared_5395_ = v_isSharedCheck_5400_;
goto v_resetjp_5393_;
}
else
{
lean_inc(v_Z_5392_);
lean_inc(v_x_5391_);
lean_inc(v_X_5390_);
lean_inc(v_O_5389_);
lean_inc(v_v_5388_);
lean_inc(v_zabbrev_5387_);
lean_inc(v_z_5386_);
lean_inc(v_V_5385_);
lean_inc(v_N_5384_);
lean_inc(v_n_5383_);
lean_inc(v_A_5382_);
lean_inc(v_S_5381_);
lean_inc(v_s_5380_);
lean_inc(v_m_5379_);
lean_inc(v_H_5378_);
lean_inc(v_k_5377_);
lean_inc(v_K_5376_);
lean_inc(v_h_5375_);
lean_inc(v_B_5374_);
lean_inc(v_a_5373_);
lean_inc(v_F_5372_);
lean_inc(v_c_5371_);
lean_inc(v_e_5370_);
lean_inc(v_E_5369_);
lean_inc(v_W_5368_);
lean_inc(v_w_5367_);
lean_inc(v_q_5366_);
lean_inc(v_Q_5365_);
lean_inc(v_d_5364_);
lean_inc(v_L_5363_);
lean_inc(v_M_5362_);
lean_inc(v_D_5361_);
lean_inc(v_Y_5360_);
lean_inc(v_u_5359_);
lean_inc(v_y_5358_);
lean_inc(v_G_5357_);
lean_dec(v_date_4491_);
v___x_5394_ = lean_box(0);
v_isShared_5395_ = v_isSharedCheck_5400_;
goto v_resetjp_5393_;
}
v_resetjp_5393_:
{
lean_object* v___x_5396_; lean_object* v___x_5398_; 
v___x_5396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5396_, 0, v_data_4493_);
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 17, v___x_5396_);
v___x_5398_ = v___x_5394_;
goto v_reusejp_5397_;
}
else
{
lean_object* v_reuseFailAlloc_5399_; 
v_reuseFailAlloc_5399_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_G_5357_);
lean_ctor_set(v_reuseFailAlloc_5399_, 1, v_y_5358_);
lean_ctor_set(v_reuseFailAlloc_5399_, 2, v_u_5359_);
lean_ctor_set(v_reuseFailAlloc_5399_, 3, v_Y_5360_);
lean_ctor_set(v_reuseFailAlloc_5399_, 4, v_D_5361_);
lean_ctor_set(v_reuseFailAlloc_5399_, 5, v_M_5362_);
lean_ctor_set(v_reuseFailAlloc_5399_, 6, v_L_5363_);
lean_ctor_set(v_reuseFailAlloc_5399_, 7, v_d_5364_);
lean_ctor_set(v_reuseFailAlloc_5399_, 8, v_Q_5365_);
lean_ctor_set(v_reuseFailAlloc_5399_, 9, v_q_5366_);
lean_ctor_set(v_reuseFailAlloc_5399_, 10, v_w_5367_);
lean_ctor_set(v_reuseFailAlloc_5399_, 11, v_W_5368_);
lean_ctor_set(v_reuseFailAlloc_5399_, 12, v_E_5369_);
lean_ctor_set(v_reuseFailAlloc_5399_, 13, v_e_5370_);
lean_ctor_set(v_reuseFailAlloc_5399_, 14, v_c_5371_);
lean_ctor_set(v_reuseFailAlloc_5399_, 15, v_F_5372_);
lean_ctor_set(v_reuseFailAlloc_5399_, 16, v_a_5373_);
lean_ctor_set(v_reuseFailAlloc_5399_, 17, v___x_5396_);
lean_ctor_set(v_reuseFailAlloc_5399_, 18, v_B_5374_);
lean_ctor_set(v_reuseFailAlloc_5399_, 19, v_h_5375_);
lean_ctor_set(v_reuseFailAlloc_5399_, 20, v_K_5376_);
lean_ctor_set(v_reuseFailAlloc_5399_, 21, v_k_5377_);
lean_ctor_set(v_reuseFailAlloc_5399_, 22, v_H_5378_);
lean_ctor_set(v_reuseFailAlloc_5399_, 23, v_m_5379_);
lean_ctor_set(v_reuseFailAlloc_5399_, 24, v_s_5380_);
lean_ctor_set(v_reuseFailAlloc_5399_, 25, v_S_5381_);
lean_ctor_set(v_reuseFailAlloc_5399_, 26, v_A_5382_);
lean_ctor_set(v_reuseFailAlloc_5399_, 27, v_n_5383_);
lean_ctor_set(v_reuseFailAlloc_5399_, 28, v_N_5384_);
lean_ctor_set(v_reuseFailAlloc_5399_, 29, v_V_5385_);
lean_ctor_set(v_reuseFailAlloc_5399_, 30, v_z_5386_);
lean_ctor_set(v_reuseFailAlloc_5399_, 31, v_zabbrev_5387_);
lean_ctor_set(v_reuseFailAlloc_5399_, 32, v_v_5388_);
lean_ctor_set(v_reuseFailAlloc_5399_, 33, v_O_5389_);
lean_ctor_set(v_reuseFailAlloc_5399_, 34, v_X_5390_);
lean_ctor_set(v_reuseFailAlloc_5399_, 35, v_x_5391_);
lean_ctor_set(v_reuseFailAlloc_5399_, 36, v_Z_5392_);
v___x_5398_ = v_reuseFailAlloc_5399_;
goto v_reusejp_5397_;
}
v_reusejp_5397_:
{
return v___x_5398_;
}
}
}
case 18:
{
lean_object* v_G_5402_; lean_object* v_y_5403_; lean_object* v_u_5404_; lean_object* v_Y_5405_; lean_object* v_D_5406_; lean_object* v_M_5407_; lean_object* v_L_5408_; lean_object* v_d_5409_; lean_object* v_Q_5410_; lean_object* v_q_5411_; lean_object* v_w_5412_; lean_object* v_W_5413_; lean_object* v_E_5414_; lean_object* v_e_5415_; lean_object* v_c_5416_; lean_object* v_F_5417_; lean_object* v_a_5418_; lean_object* v_b_5419_; lean_object* v_h_5420_; lean_object* v_K_5421_; lean_object* v_k_5422_; lean_object* v_H_5423_; lean_object* v_m_5424_; lean_object* v_s_5425_; lean_object* v_S_5426_; lean_object* v_A_5427_; lean_object* v_n_5428_; lean_object* v_N_5429_; lean_object* v_V_5430_; lean_object* v_z_5431_; lean_object* v_zabbrev_5432_; lean_object* v_v_5433_; lean_object* v_O_5434_; lean_object* v_X_5435_; lean_object* v_x_5436_; lean_object* v_Z_5437_; lean_object* v___x_5439_; uint8_t v_isShared_5440_; uint8_t v_isSharedCheck_5445_; 
lean_dec_ref_known(v_modifier_4492_, 0);
v_G_5402_ = lean_ctor_get(v_date_4491_, 0);
v_y_5403_ = lean_ctor_get(v_date_4491_, 1);
v_u_5404_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5405_ = lean_ctor_get(v_date_4491_, 3);
v_D_5406_ = lean_ctor_get(v_date_4491_, 4);
v_M_5407_ = lean_ctor_get(v_date_4491_, 5);
v_L_5408_ = lean_ctor_get(v_date_4491_, 6);
v_d_5409_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5410_ = lean_ctor_get(v_date_4491_, 8);
v_q_5411_ = lean_ctor_get(v_date_4491_, 9);
v_w_5412_ = lean_ctor_get(v_date_4491_, 10);
v_W_5413_ = lean_ctor_get(v_date_4491_, 11);
v_E_5414_ = lean_ctor_get(v_date_4491_, 12);
v_e_5415_ = lean_ctor_get(v_date_4491_, 13);
v_c_5416_ = lean_ctor_get(v_date_4491_, 14);
v_F_5417_ = lean_ctor_get(v_date_4491_, 15);
v_a_5418_ = lean_ctor_get(v_date_4491_, 16);
v_b_5419_ = lean_ctor_get(v_date_4491_, 17);
v_h_5420_ = lean_ctor_get(v_date_4491_, 19);
v_K_5421_ = lean_ctor_get(v_date_4491_, 20);
v_k_5422_ = lean_ctor_get(v_date_4491_, 21);
v_H_5423_ = lean_ctor_get(v_date_4491_, 22);
v_m_5424_ = lean_ctor_get(v_date_4491_, 23);
v_s_5425_ = lean_ctor_get(v_date_4491_, 24);
v_S_5426_ = lean_ctor_get(v_date_4491_, 25);
v_A_5427_ = lean_ctor_get(v_date_4491_, 26);
v_n_5428_ = lean_ctor_get(v_date_4491_, 27);
v_N_5429_ = lean_ctor_get(v_date_4491_, 28);
v_V_5430_ = lean_ctor_get(v_date_4491_, 29);
v_z_5431_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5432_ = lean_ctor_get(v_date_4491_, 31);
v_v_5433_ = lean_ctor_get(v_date_4491_, 32);
v_O_5434_ = lean_ctor_get(v_date_4491_, 33);
v_X_5435_ = lean_ctor_get(v_date_4491_, 34);
v_x_5436_ = lean_ctor_get(v_date_4491_, 35);
v_Z_5437_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5445_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5445_ == 0)
{
lean_object* v_unused_5446_; 
v_unused_5446_ = lean_ctor_get(v_date_4491_, 18);
lean_dec(v_unused_5446_);
v___x_5439_ = v_date_4491_;
v_isShared_5440_ = v_isSharedCheck_5445_;
goto v_resetjp_5438_;
}
else
{
lean_inc(v_Z_5437_);
lean_inc(v_x_5436_);
lean_inc(v_X_5435_);
lean_inc(v_O_5434_);
lean_inc(v_v_5433_);
lean_inc(v_zabbrev_5432_);
lean_inc(v_z_5431_);
lean_inc(v_V_5430_);
lean_inc(v_N_5429_);
lean_inc(v_n_5428_);
lean_inc(v_A_5427_);
lean_inc(v_S_5426_);
lean_inc(v_s_5425_);
lean_inc(v_m_5424_);
lean_inc(v_H_5423_);
lean_inc(v_k_5422_);
lean_inc(v_K_5421_);
lean_inc(v_h_5420_);
lean_inc(v_b_5419_);
lean_inc(v_a_5418_);
lean_inc(v_F_5417_);
lean_inc(v_c_5416_);
lean_inc(v_e_5415_);
lean_inc(v_E_5414_);
lean_inc(v_W_5413_);
lean_inc(v_w_5412_);
lean_inc(v_q_5411_);
lean_inc(v_Q_5410_);
lean_inc(v_d_5409_);
lean_inc(v_L_5408_);
lean_inc(v_M_5407_);
lean_inc(v_D_5406_);
lean_inc(v_Y_5405_);
lean_inc(v_u_5404_);
lean_inc(v_y_5403_);
lean_inc(v_G_5402_);
lean_dec(v_date_4491_);
v___x_5439_ = lean_box(0);
v_isShared_5440_ = v_isSharedCheck_5445_;
goto v_resetjp_5438_;
}
v_resetjp_5438_:
{
lean_object* v___x_5441_; lean_object* v___x_5443_; 
v___x_5441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5441_, 0, v_data_4493_);
if (v_isShared_5440_ == 0)
{
lean_ctor_set(v___x_5439_, 18, v___x_5441_);
v___x_5443_ = v___x_5439_;
goto v_reusejp_5442_;
}
else
{
lean_object* v_reuseFailAlloc_5444_; 
v_reuseFailAlloc_5444_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5444_, 0, v_G_5402_);
lean_ctor_set(v_reuseFailAlloc_5444_, 1, v_y_5403_);
lean_ctor_set(v_reuseFailAlloc_5444_, 2, v_u_5404_);
lean_ctor_set(v_reuseFailAlloc_5444_, 3, v_Y_5405_);
lean_ctor_set(v_reuseFailAlloc_5444_, 4, v_D_5406_);
lean_ctor_set(v_reuseFailAlloc_5444_, 5, v_M_5407_);
lean_ctor_set(v_reuseFailAlloc_5444_, 6, v_L_5408_);
lean_ctor_set(v_reuseFailAlloc_5444_, 7, v_d_5409_);
lean_ctor_set(v_reuseFailAlloc_5444_, 8, v_Q_5410_);
lean_ctor_set(v_reuseFailAlloc_5444_, 9, v_q_5411_);
lean_ctor_set(v_reuseFailAlloc_5444_, 10, v_w_5412_);
lean_ctor_set(v_reuseFailAlloc_5444_, 11, v_W_5413_);
lean_ctor_set(v_reuseFailAlloc_5444_, 12, v_E_5414_);
lean_ctor_set(v_reuseFailAlloc_5444_, 13, v_e_5415_);
lean_ctor_set(v_reuseFailAlloc_5444_, 14, v_c_5416_);
lean_ctor_set(v_reuseFailAlloc_5444_, 15, v_F_5417_);
lean_ctor_set(v_reuseFailAlloc_5444_, 16, v_a_5418_);
lean_ctor_set(v_reuseFailAlloc_5444_, 17, v_b_5419_);
lean_ctor_set(v_reuseFailAlloc_5444_, 18, v___x_5441_);
lean_ctor_set(v_reuseFailAlloc_5444_, 19, v_h_5420_);
lean_ctor_set(v_reuseFailAlloc_5444_, 20, v_K_5421_);
lean_ctor_set(v_reuseFailAlloc_5444_, 21, v_k_5422_);
lean_ctor_set(v_reuseFailAlloc_5444_, 22, v_H_5423_);
lean_ctor_set(v_reuseFailAlloc_5444_, 23, v_m_5424_);
lean_ctor_set(v_reuseFailAlloc_5444_, 24, v_s_5425_);
lean_ctor_set(v_reuseFailAlloc_5444_, 25, v_S_5426_);
lean_ctor_set(v_reuseFailAlloc_5444_, 26, v_A_5427_);
lean_ctor_set(v_reuseFailAlloc_5444_, 27, v_n_5428_);
lean_ctor_set(v_reuseFailAlloc_5444_, 28, v_N_5429_);
lean_ctor_set(v_reuseFailAlloc_5444_, 29, v_V_5430_);
lean_ctor_set(v_reuseFailAlloc_5444_, 30, v_z_5431_);
lean_ctor_set(v_reuseFailAlloc_5444_, 31, v_zabbrev_5432_);
lean_ctor_set(v_reuseFailAlloc_5444_, 32, v_v_5433_);
lean_ctor_set(v_reuseFailAlloc_5444_, 33, v_O_5434_);
lean_ctor_set(v_reuseFailAlloc_5444_, 34, v_X_5435_);
lean_ctor_set(v_reuseFailAlloc_5444_, 35, v_x_5436_);
lean_ctor_set(v_reuseFailAlloc_5444_, 36, v_Z_5437_);
v___x_5443_ = v_reuseFailAlloc_5444_;
goto v_reusejp_5442_;
}
v_reusejp_5442_:
{
return v___x_5443_;
}
}
}
case 19:
{
lean_object* v___x_5448_; uint8_t v_isShared_5449_; uint8_t v_isSharedCheck_5497_; 
v_isSharedCheck_5497_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_5497_ == 0)
{
lean_object* v_unused_5498_; 
v_unused_5498_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_5498_);
v___x_5448_ = v_modifier_4492_;
v_isShared_5449_ = v_isSharedCheck_5497_;
goto v_resetjp_5447_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_5448_ = lean_box(0);
v_isShared_5449_ = v_isSharedCheck_5497_;
goto v_resetjp_5447_;
}
v_resetjp_5447_:
{
lean_object* v_G_5450_; lean_object* v_y_5451_; lean_object* v_u_5452_; lean_object* v_Y_5453_; lean_object* v_D_5454_; lean_object* v_M_5455_; lean_object* v_L_5456_; lean_object* v_d_5457_; lean_object* v_Q_5458_; lean_object* v_q_5459_; lean_object* v_w_5460_; lean_object* v_W_5461_; lean_object* v_E_5462_; lean_object* v_e_5463_; lean_object* v_c_5464_; lean_object* v_F_5465_; lean_object* v_a_5466_; lean_object* v_b_5467_; lean_object* v_B_5468_; lean_object* v_K_5469_; lean_object* v_k_5470_; lean_object* v_H_5471_; lean_object* v_m_5472_; lean_object* v_s_5473_; lean_object* v_S_5474_; lean_object* v_A_5475_; lean_object* v_n_5476_; lean_object* v_N_5477_; lean_object* v_V_5478_; lean_object* v_z_5479_; lean_object* v_zabbrev_5480_; lean_object* v_v_5481_; lean_object* v_O_5482_; lean_object* v_X_5483_; lean_object* v_x_5484_; lean_object* v_Z_5485_; lean_object* v___x_5487_; uint8_t v_isShared_5488_; uint8_t v_isSharedCheck_5495_; 
v_G_5450_ = lean_ctor_get(v_date_4491_, 0);
v_y_5451_ = lean_ctor_get(v_date_4491_, 1);
v_u_5452_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5453_ = lean_ctor_get(v_date_4491_, 3);
v_D_5454_ = lean_ctor_get(v_date_4491_, 4);
v_M_5455_ = lean_ctor_get(v_date_4491_, 5);
v_L_5456_ = lean_ctor_get(v_date_4491_, 6);
v_d_5457_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5458_ = lean_ctor_get(v_date_4491_, 8);
v_q_5459_ = lean_ctor_get(v_date_4491_, 9);
v_w_5460_ = lean_ctor_get(v_date_4491_, 10);
v_W_5461_ = lean_ctor_get(v_date_4491_, 11);
v_E_5462_ = lean_ctor_get(v_date_4491_, 12);
v_e_5463_ = lean_ctor_get(v_date_4491_, 13);
v_c_5464_ = lean_ctor_get(v_date_4491_, 14);
v_F_5465_ = lean_ctor_get(v_date_4491_, 15);
v_a_5466_ = lean_ctor_get(v_date_4491_, 16);
v_b_5467_ = lean_ctor_get(v_date_4491_, 17);
v_B_5468_ = lean_ctor_get(v_date_4491_, 18);
v_K_5469_ = lean_ctor_get(v_date_4491_, 20);
v_k_5470_ = lean_ctor_get(v_date_4491_, 21);
v_H_5471_ = lean_ctor_get(v_date_4491_, 22);
v_m_5472_ = lean_ctor_get(v_date_4491_, 23);
v_s_5473_ = lean_ctor_get(v_date_4491_, 24);
v_S_5474_ = lean_ctor_get(v_date_4491_, 25);
v_A_5475_ = lean_ctor_get(v_date_4491_, 26);
v_n_5476_ = lean_ctor_get(v_date_4491_, 27);
v_N_5477_ = lean_ctor_get(v_date_4491_, 28);
v_V_5478_ = lean_ctor_get(v_date_4491_, 29);
v_z_5479_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5480_ = lean_ctor_get(v_date_4491_, 31);
v_v_5481_ = lean_ctor_get(v_date_4491_, 32);
v_O_5482_ = lean_ctor_get(v_date_4491_, 33);
v_X_5483_ = lean_ctor_get(v_date_4491_, 34);
v_x_5484_ = lean_ctor_get(v_date_4491_, 35);
v_Z_5485_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5495_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5495_ == 0)
{
lean_object* v_unused_5496_; 
v_unused_5496_ = lean_ctor_get(v_date_4491_, 19);
lean_dec(v_unused_5496_);
v___x_5487_ = v_date_4491_;
v_isShared_5488_ = v_isSharedCheck_5495_;
goto v_resetjp_5486_;
}
else
{
lean_inc(v_Z_5485_);
lean_inc(v_x_5484_);
lean_inc(v_X_5483_);
lean_inc(v_O_5482_);
lean_inc(v_v_5481_);
lean_inc(v_zabbrev_5480_);
lean_inc(v_z_5479_);
lean_inc(v_V_5478_);
lean_inc(v_N_5477_);
lean_inc(v_n_5476_);
lean_inc(v_A_5475_);
lean_inc(v_S_5474_);
lean_inc(v_s_5473_);
lean_inc(v_m_5472_);
lean_inc(v_H_5471_);
lean_inc(v_k_5470_);
lean_inc(v_K_5469_);
lean_inc(v_B_5468_);
lean_inc(v_b_5467_);
lean_inc(v_a_5466_);
lean_inc(v_F_5465_);
lean_inc(v_c_5464_);
lean_inc(v_e_5463_);
lean_inc(v_E_5462_);
lean_inc(v_W_5461_);
lean_inc(v_w_5460_);
lean_inc(v_q_5459_);
lean_inc(v_Q_5458_);
lean_inc(v_d_5457_);
lean_inc(v_L_5456_);
lean_inc(v_M_5455_);
lean_inc(v_D_5454_);
lean_inc(v_Y_5453_);
lean_inc(v_u_5452_);
lean_inc(v_y_5451_);
lean_inc(v_G_5450_);
lean_dec(v_date_4491_);
v___x_5487_ = lean_box(0);
v_isShared_5488_ = v_isSharedCheck_5495_;
goto v_resetjp_5486_;
}
v_resetjp_5486_:
{
lean_object* v___x_5490_; 
if (v_isShared_5449_ == 0)
{
lean_ctor_set_tag(v___x_5448_, 1);
lean_ctor_set(v___x_5448_, 0, v_data_4493_);
v___x_5490_ = v___x_5448_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5494_; 
v_reuseFailAlloc_5494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5494_, 0, v_data_4493_);
v___x_5490_ = v_reuseFailAlloc_5494_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
lean_object* v___x_5492_; 
if (v_isShared_5488_ == 0)
{
lean_ctor_set(v___x_5487_, 19, v___x_5490_);
v___x_5492_ = v___x_5487_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_G_5450_);
lean_ctor_set(v_reuseFailAlloc_5493_, 1, v_y_5451_);
lean_ctor_set(v_reuseFailAlloc_5493_, 2, v_u_5452_);
lean_ctor_set(v_reuseFailAlloc_5493_, 3, v_Y_5453_);
lean_ctor_set(v_reuseFailAlloc_5493_, 4, v_D_5454_);
lean_ctor_set(v_reuseFailAlloc_5493_, 5, v_M_5455_);
lean_ctor_set(v_reuseFailAlloc_5493_, 6, v_L_5456_);
lean_ctor_set(v_reuseFailAlloc_5493_, 7, v_d_5457_);
lean_ctor_set(v_reuseFailAlloc_5493_, 8, v_Q_5458_);
lean_ctor_set(v_reuseFailAlloc_5493_, 9, v_q_5459_);
lean_ctor_set(v_reuseFailAlloc_5493_, 10, v_w_5460_);
lean_ctor_set(v_reuseFailAlloc_5493_, 11, v_W_5461_);
lean_ctor_set(v_reuseFailAlloc_5493_, 12, v_E_5462_);
lean_ctor_set(v_reuseFailAlloc_5493_, 13, v_e_5463_);
lean_ctor_set(v_reuseFailAlloc_5493_, 14, v_c_5464_);
lean_ctor_set(v_reuseFailAlloc_5493_, 15, v_F_5465_);
lean_ctor_set(v_reuseFailAlloc_5493_, 16, v_a_5466_);
lean_ctor_set(v_reuseFailAlloc_5493_, 17, v_b_5467_);
lean_ctor_set(v_reuseFailAlloc_5493_, 18, v_B_5468_);
lean_ctor_set(v_reuseFailAlloc_5493_, 19, v___x_5490_);
lean_ctor_set(v_reuseFailAlloc_5493_, 20, v_K_5469_);
lean_ctor_set(v_reuseFailAlloc_5493_, 21, v_k_5470_);
lean_ctor_set(v_reuseFailAlloc_5493_, 22, v_H_5471_);
lean_ctor_set(v_reuseFailAlloc_5493_, 23, v_m_5472_);
lean_ctor_set(v_reuseFailAlloc_5493_, 24, v_s_5473_);
lean_ctor_set(v_reuseFailAlloc_5493_, 25, v_S_5474_);
lean_ctor_set(v_reuseFailAlloc_5493_, 26, v_A_5475_);
lean_ctor_set(v_reuseFailAlloc_5493_, 27, v_n_5476_);
lean_ctor_set(v_reuseFailAlloc_5493_, 28, v_N_5477_);
lean_ctor_set(v_reuseFailAlloc_5493_, 29, v_V_5478_);
lean_ctor_set(v_reuseFailAlloc_5493_, 30, v_z_5479_);
lean_ctor_set(v_reuseFailAlloc_5493_, 31, v_zabbrev_5480_);
lean_ctor_set(v_reuseFailAlloc_5493_, 32, v_v_5481_);
lean_ctor_set(v_reuseFailAlloc_5493_, 33, v_O_5482_);
lean_ctor_set(v_reuseFailAlloc_5493_, 34, v_X_5483_);
lean_ctor_set(v_reuseFailAlloc_5493_, 35, v_x_5484_);
lean_ctor_set(v_reuseFailAlloc_5493_, 36, v_Z_5485_);
v___x_5492_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
return v___x_5492_;
}
}
}
}
}
case 20:
{
lean_object* v___x_5500_; uint8_t v_isShared_5501_; uint8_t v_isSharedCheck_5549_; 
v_isSharedCheck_5549_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_5549_ == 0)
{
lean_object* v_unused_5550_; 
v_unused_5550_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_5550_);
v___x_5500_ = v_modifier_4492_;
v_isShared_5501_ = v_isSharedCheck_5549_;
goto v_resetjp_5499_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_5500_ = lean_box(0);
v_isShared_5501_ = v_isSharedCheck_5549_;
goto v_resetjp_5499_;
}
v_resetjp_5499_:
{
lean_object* v_G_5502_; lean_object* v_y_5503_; lean_object* v_u_5504_; lean_object* v_Y_5505_; lean_object* v_D_5506_; lean_object* v_M_5507_; lean_object* v_L_5508_; lean_object* v_d_5509_; lean_object* v_Q_5510_; lean_object* v_q_5511_; lean_object* v_w_5512_; lean_object* v_W_5513_; lean_object* v_E_5514_; lean_object* v_e_5515_; lean_object* v_c_5516_; lean_object* v_F_5517_; lean_object* v_a_5518_; lean_object* v_b_5519_; lean_object* v_B_5520_; lean_object* v_h_5521_; lean_object* v_k_5522_; lean_object* v_H_5523_; lean_object* v_m_5524_; lean_object* v_s_5525_; lean_object* v_S_5526_; lean_object* v_A_5527_; lean_object* v_n_5528_; lean_object* v_N_5529_; lean_object* v_V_5530_; lean_object* v_z_5531_; lean_object* v_zabbrev_5532_; lean_object* v_v_5533_; lean_object* v_O_5534_; lean_object* v_X_5535_; lean_object* v_x_5536_; lean_object* v_Z_5537_; lean_object* v___x_5539_; uint8_t v_isShared_5540_; uint8_t v_isSharedCheck_5547_; 
v_G_5502_ = lean_ctor_get(v_date_4491_, 0);
v_y_5503_ = lean_ctor_get(v_date_4491_, 1);
v_u_5504_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5505_ = lean_ctor_get(v_date_4491_, 3);
v_D_5506_ = lean_ctor_get(v_date_4491_, 4);
v_M_5507_ = lean_ctor_get(v_date_4491_, 5);
v_L_5508_ = lean_ctor_get(v_date_4491_, 6);
v_d_5509_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5510_ = lean_ctor_get(v_date_4491_, 8);
v_q_5511_ = lean_ctor_get(v_date_4491_, 9);
v_w_5512_ = lean_ctor_get(v_date_4491_, 10);
v_W_5513_ = lean_ctor_get(v_date_4491_, 11);
v_E_5514_ = lean_ctor_get(v_date_4491_, 12);
v_e_5515_ = lean_ctor_get(v_date_4491_, 13);
v_c_5516_ = lean_ctor_get(v_date_4491_, 14);
v_F_5517_ = lean_ctor_get(v_date_4491_, 15);
v_a_5518_ = lean_ctor_get(v_date_4491_, 16);
v_b_5519_ = lean_ctor_get(v_date_4491_, 17);
v_B_5520_ = lean_ctor_get(v_date_4491_, 18);
v_h_5521_ = lean_ctor_get(v_date_4491_, 19);
v_k_5522_ = lean_ctor_get(v_date_4491_, 21);
v_H_5523_ = lean_ctor_get(v_date_4491_, 22);
v_m_5524_ = lean_ctor_get(v_date_4491_, 23);
v_s_5525_ = lean_ctor_get(v_date_4491_, 24);
v_S_5526_ = lean_ctor_get(v_date_4491_, 25);
v_A_5527_ = lean_ctor_get(v_date_4491_, 26);
v_n_5528_ = lean_ctor_get(v_date_4491_, 27);
v_N_5529_ = lean_ctor_get(v_date_4491_, 28);
v_V_5530_ = lean_ctor_get(v_date_4491_, 29);
v_z_5531_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5532_ = lean_ctor_get(v_date_4491_, 31);
v_v_5533_ = lean_ctor_get(v_date_4491_, 32);
v_O_5534_ = lean_ctor_get(v_date_4491_, 33);
v_X_5535_ = lean_ctor_get(v_date_4491_, 34);
v_x_5536_ = lean_ctor_get(v_date_4491_, 35);
v_Z_5537_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5547_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5547_ == 0)
{
lean_object* v_unused_5548_; 
v_unused_5548_ = lean_ctor_get(v_date_4491_, 20);
lean_dec(v_unused_5548_);
v___x_5539_ = v_date_4491_;
v_isShared_5540_ = v_isSharedCheck_5547_;
goto v_resetjp_5538_;
}
else
{
lean_inc(v_Z_5537_);
lean_inc(v_x_5536_);
lean_inc(v_X_5535_);
lean_inc(v_O_5534_);
lean_inc(v_v_5533_);
lean_inc(v_zabbrev_5532_);
lean_inc(v_z_5531_);
lean_inc(v_V_5530_);
lean_inc(v_N_5529_);
lean_inc(v_n_5528_);
lean_inc(v_A_5527_);
lean_inc(v_S_5526_);
lean_inc(v_s_5525_);
lean_inc(v_m_5524_);
lean_inc(v_H_5523_);
lean_inc(v_k_5522_);
lean_inc(v_h_5521_);
lean_inc(v_B_5520_);
lean_inc(v_b_5519_);
lean_inc(v_a_5518_);
lean_inc(v_F_5517_);
lean_inc(v_c_5516_);
lean_inc(v_e_5515_);
lean_inc(v_E_5514_);
lean_inc(v_W_5513_);
lean_inc(v_w_5512_);
lean_inc(v_q_5511_);
lean_inc(v_Q_5510_);
lean_inc(v_d_5509_);
lean_inc(v_L_5508_);
lean_inc(v_M_5507_);
lean_inc(v_D_5506_);
lean_inc(v_Y_5505_);
lean_inc(v_u_5504_);
lean_inc(v_y_5503_);
lean_inc(v_G_5502_);
lean_dec(v_date_4491_);
v___x_5539_ = lean_box(0);
v_isShared_5540_ = v_isSharedCheck_5547_;
goto v_resetjp_5538_;
}
v_resetjp_5538_:
{
lean_object* v___x_5542_; 
if (v_isShared_5501_ == 0)
{
lean_ctor_set_tag(v___x_5500_, 1);
lean_ctor_set(v___x_5500_, 0, v_data_4493_);
v___x_5542_ = v___x_5500_;
goto v_reusejp_5541_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v_data_4493_);
v___x_5542_ = v_reuseFailAlloc_5546_;
goto v_reusejp_5541_;
}
v_reusejp_5541_:
{
lean_object* v___x_5544_; 
if (v_isShared_5540_ == 0)
{
lean_ctor_set(v___x_5539_, 20, v___x_5542_);
v___x_5544_ = v___x_5539_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5545_; 
v_reuseFailAlloc_5545_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5545_, 0, v_G_5502_);
lean_ctor_set(v_reuseFailAlloc_5545_, 1, v_y_5503_);
lean_ctor_set(v_reuseFailAlloc_5545_, 2, v_u_5504_);
lean_ctor_set(v_reuseFailAlloc_5545_, 3, v_Y_5505_);
lean_ctor_set(v_reuseFailAlloc_5545_, 4, v_D_5506_);
lean_ctor_set(v_reuseFailAlloc_5545_, 5, v_M_5507_);
lean_ctor_set(v_reuseFailAlloc_5545_, 6, v_L_5508_);
lean_ctor_set(v_reuseFailAlloc_5545_, 7, v_d_5509_);
lean_ctor_set(v_reuseFailAlloc_5545_, 8, v_Q_5510_);
lean_ctor_set(v_reuseFailAlloc_5545_, 9, v_q_5511_);
lean_ctor_set(v_reuseFailAlloc_5545_, 10, v_w_5512_);
lean_ctor_set(v_reuseFailAlloc_5545_, 11, v_W_5513_);
lean_ctor_set(v_reuseFailAlloc_5545_, 12, v_E_5514_);
lean_ctor_set(v_reuseFailAlloc_5545_, 13, v_e_5515_);
lean_ctor_set(v_reuseFailAlloc_5545_, 14, v_c_5516_);
lean_ctor_set(v_reuseFailAlloc_5545_, 15, v_F_5517_);
lean_ctor_set(v_reuseFailAlloc_5545_, 16, v_a_5518_);
lean_ctor_set(v_reuseFailAlloc_5545_, 17, v_b_5519_);
lean_ctor_set(v_reuseFailAlloc_5545_, 18, v_B_5520_);
lean_ctor_set(v_reuseFailAlloc_5545_, 19, v_h_5521_);
lean_ctor_set(v_reuseFailAlloc_5545_, 20, v___x_5542_);
lean_ctor_set(v_reuseFailAlloc_5545_, 21, v_k_5522_);
lean_ctor_set(v_reuseFailAlloc_5545_, 22, v_H_5523_);
lean_ctor_set(v_reuseFailAlloc_5545_, 23, v_m_5524_);
lean_ctor_set(v_reuseFailAlloc_5545_, 24, v_s_5525_);
lean_ctor_set(v_reuseFailAlloc_5545_, 25, v_S_5526_);
lean_ctor_set(v_reuseFailAlloc_5545_, 26, v_A_5527_);
lean_ctor_set(v_reuseFailAlloc_5545_, 27, v_n_5528_);
lean_ctor_set(v_reuseFailAlloc_5545_, 28, v_N_5529_);
lean_ctor_set(v_reuseFailAlloc_5545_, 29, v_V_5530_);
lean_ctor_set(v_reuseFailAlloc_5545_, 30, v_z_5531_);
lean_ctor_set(v_reuseFailAlloc_5545_, 31, v_zabbrev_5532_);
lean_ctor_set(v_reuseFailAlloc_5545_, 32, v_v_5533_);
lean_ctor_set(v_reuseFailAlloc_5545_, 33, v_O_5534_);
lean_ctor_set(v_reuseFailAlloc_5545_, 34, v_X_5535_);
lean_ctor_set(v_reuseFailAlloc_5545_, 35, v_x_5536_);
lean_ctor_set(v_reuseFailAlloc_5545_, 36, v_Z_5537_);
v___x_5544_ = v_reuseFailAlloc_5545_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
return v___x_5544_;
}
}
}
}
}
case 21:
{
lean_object* v___x_5552_; uint8_t v_isShared_5553_; uint8_t v_isSharedCheck_5601_; 
v_isSharedCheck_5601_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_5601_ == 0)
{
lean_object* v_unused_5602_; 
v_unused_5602_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_5602_);
v___x_5552_ = v_modifier_4492_;
v_isShared_5553_ = v_isSharedCheck_5601_;
goto v_resetjp_5551_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_5552_ = lean_box(0);
v_isShared_5553_ = v_isSharedCheck_5601_;
goto v_resetjp_5551_;
}
v_resetjp_5551_:
{
lean_object* v_G_5554_; lean_object* v_y_5555_; lean_object* v_u_5556_; lean_object* v_Y_5557_; lean_object* v_D_5558_; lean_object* v_M_5559_; lean_object* v_L_5560_; lean_object* v_d_5561_; lean_object* v_Q_5562_; lean_object* v_q_5563_; lean_object* v_w_5564_; lean_object* v_W_5565_; lean_object* v_E_5566_; lean_object* v_e_5567_; lean_object* v_c_5568_; lean_object* v_F_5569_; lean_object* v_a_5570_; lean_object* v_b_5571_; lean_object* v_B_5572_; lean_object* v_h_5573_; lean_object* v_K_5574_; lean_object* v_H_5575_; lean_object* v_m_5576_; lean_object* v_s_5577_; lean_object* v_S_5578_; lean_object* v_A_5579_; lean_object* v_n_5580_; lean_object* v_N_5581_; lean_object* v_V_5582_; lean_object* v_z_5583_; lean_object* v_zabbrev_5584_; lean_object* v_v_5585_; lean_object* v_O_5586_; lean_object* v_X_5587_; lean_object* v_x_5588_; lean_object* v_Z_5589_; lean_object* v___x_5591_; uint8_t v_isShared_5592_; uint8_t v_isSharedCheck_5599_; 
v_G_5554_ = lean_ctor_get(v_date_4491_, 0);
v_y_5555_ = lean_ctor_get(v_date_4491_, 1);
v_u_5556_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5557_ = lean_ctor_get(v_date_4491_, 3);
v_D_5558_ = lean_ctor_get(v_date_4491_, 4);
v_M_5559_ = lean_ctor_get(v_date_4491_, 5);
v_L_5560_ = lean_ctor_get(v_date_4491_, 6);
v_d_5561_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5562_ = lean_ctor_get(v_date_4491_, 8);
v_q_5563_ = lean_ctor_get(v_date_4491_, 9);
v_w_5564_ = lean_ctor_get(v_date_4491_, 10);
v_W_5565_ = lean_ctor_get(v_date_4491_, 11);
v_E_5566_ = lean_ctor_get(v_date_4491_, 12);
v_e_5567_ = lean_ctor_get(v_date_4491_, 13);
v_c_5568_ = lean_ctor_get(v_date_4491_, 14);
v_F_5569_ = lean_ctor_get(v_date_4491_, 15);
v_a_5570_ = lean_ctor_get(v_date_4491_, 16);
v_b_5571_ = lean_ctor_get(v_date_4491_, 17);
v_B_5572_ = lean_ctor_get(v_date_4491_, 18);
v_h_5573_ = lean_ctor_get(v_date_4491_, 19);
v_K_5574_ = lean_ctor_get(v_date_4491_, 20);
v_H_5575_ = lean_ctor_get(v_date_4491_, 22);
v_m_5576_ = lean_ctor_get(v_date_4491_, 23);
v_s_5577_ = lean_ctor_get(v_date_4491_, 24);
v_S_5578_ = lean_ctor_get(v_date_4491_, 25);
v_A_5579_ = lean_ctor_get(v_date_4491_, 26);
v_n_5580_ = lean_ctor_get(v_date_4491_, 27);
v_N_5581_ = lean_ctor_get(v_date_4491_, 28);
v_V_5582_ = lean_ctor_get(v_date_4491_, 29);
v_z_5583_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5584_ = lean_ctor_get(v_date_4491_, 31);
v_v_5585_ = lean_ctor_get(v_date_4491_, 32);
v_O_5586_ = lean_ctor_get(v_date_4491_, 33);
v_X_5587_ = lean_ctor_get(v_date_4491_, 34);
v_x_5588_ = lean_ctor_get(v_date_4491_, 35);
v_Z_5589_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5599_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5599_ == 0)
{
lean_object* v_unused_5600_; 
v_unused_5600_ = lean_ctor_get(v_date_4491_, 21);
lean_dec(v_unused_5600_);
v___x_5591_ = v_date_4491_;
v_isShared_5592_ = v_isSharedCheck_5599_;
goto v_resetjp_5590_;
}
else
{
lean_inc(v_Z_5589_);
lean_inc(v_x_5588_);
lean_inc(v_X_5587_);
lean_inc(v_O_5586_);
lean_inc(v_v_5585_);
lean_inc(v_zabbrev_5584_);
lean_inc(v_z_5583_);
lean_inc(v_V_5582_);
lean_inc(v_N_5581_);
lean_inc(v_n_5580_);
lean_inc(v_A_5579_);
lean_inc(v_S_5578_);
lean_inc(v_s_5577_);
lean_inc(v_m_5576_);
lean_inc(v_H_5575_);
lean_inc(v_K_5574_);
lean_inc(v_h_5573_);
lean_inc(v_B_5572_);
lean_inc(v_b_5571_);
lean_inc(v_a_5570_);
lean_inc(v_F_5569_);
lean_inc(v_c_5568_);
lean_inc(v_e_5567_);
lean_inc(v_E_5566_);
lean_inc(v_W_5565_);
lean_inc(v_w_5564_);
lean_inc(v_q_5563_);
lean_inc(v_Q_5562_);
lean_inc(v_d_5561_);
lean_inc(v_L_5560_);
lean_inc(v_M_5559_);
lean_inc(v_D_5558_);
lean_inc(v_Y_5557_);
lean_inc(v_u_5556_);
lean_inc(v_y_5555_);
lean_inc(v_G_5554_);
lean_dec(v_date_4491_);
v___x_5591_ = lean_box(0);
v_isShared_5592_ = v_isSharedCheck_5599_;
goto v_resetjp_5590_;
}
v_resetjp_5590_:
{
lean_object* v___x_5594_; 
if (v_isShared_5553_ == 0)
{
lean_ctor_set_tag(v___x_5552_, 1);
lean_ctor_set(v___x_5552_, 0, v_data_4493_);
v___x_5594_ = v___x_5552_;
goto v_reusejp_5593_;
}
else
{
lean_object* v_reuseFailAlloc_5598_; 
v_reuseFailAlloc_5598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5598_, 0, v_data_4493_);
v___x_5594_ = v_reuseFailAlloc_5598_;
goto v_reusejp_5593_;
}
v_reusejp_5593_:
{
lean_object* v___x_5596_; 
if (v_isShared_5592_ == 0)
{
lean_ctor_set(v___x_5591_, 21, v___x_5594_);
v___x_5596_ = v___x_5591_;
goto v_reusejp_5595_;
}
else
{
lean_object* v_reuseFailAlloc_5597_; 
v_reuseFailAlloc_5597_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_5597_, 0, v_G_5554_);
lean_ctor_set(v_reuseFailAlloc_5597_, 1, v_y_5555_);
lean_ctor_set(v_reuseFailAlloc_5597_, 2, v_u_5556_);
lean_ctor_set(v_reuseFailAlloc_5597_, 3, v_Y_5557_);
lean_ctor_set(v_reuseFailAlloc_5597_, 4, v_D_5558_);
lean_ctor_set(v_reuseFailAlloc_5597_, 5, v_M_5559_);
lean_ctor_set(v_reuseFailAlloc_5597_, 6, v_L_5560_);
lean_ctor_set(v_reuseFailAlloc_5597_, 7, v_d_5561_);
lean_ctor_set(v_reuseFailAlloc_5597_, 8, v_Q_5562_);
lean_ctor_set(v_reuseFailAlloc_5597_, 9, v_q_5563_);
lean_ctor_set(v_reuseFailAlloc_5597_, 10, v_w_5564_);
lean_ctor_set(v_reuseFailAlloc_5597_, 11, v_W_5565_);
lean_ctor_set(v_reuseFailAlloc_5597_, 12, v_E_5566_);
lean_ctor_set(v_reuseFailAlloc_5597_, 13, v_e_5567_);
lean_ctor_set(v_reuseFailAlloc_5597_, 14, v_c_5568_);
lean_ctor_set(v_reuseFailAlloc_5597_, 15, v_F_5569_);
lean_ctor_set(v_reuseFailAlloc_5597_, 16, v_a_5570_);
lean_ctor_set(v_reuseFailAlloc_5597_, 17, v_b_5571_);
lean_ctor_set(v_reuseFailAlloc_5597_, 18, v_B_5572_);
lean_ctor_set(v_reuseFailAlloc_5597_, 19, v_h_5573_);
lean_ctor_set(v_reuseFailAlloc_5597_, 20, v_K_5574_);
lean_ctor_set(v_reuseFailAlloc_5597_, 21, v___x_5594_);
lean_ctor_set(v_reuseFailAlloc_5597_, 22, v_H_5575_);
lean_ctor_set(v_reuseFailAlloc_5597_, 23, v_m_5576_);
lean_ctor_set(v_reuseFailAlloc_5597_, 24, v_s_5577_);
lean_ctor_set(v_reuseFailAlloc_5597_, 25, v_S_5578_);
lean_ctor_set(v_reuseFailAlloc_5597_, 26, v_A_5579_);
lean_ctor_set(v_reuseFailAlloc_5597_, 27, v_n_5580_);
lean_ctor_set(v_reuseFailAlloc_5597_, 28, v_N_5581_);
lean_ctor_set(v_reuseFailAlloc_5597_, 29, v_V_5582_);
lean_ctor_set(v_reuseFailAlloc_5597_, 30, v_z_5583_);
lean_ctor_set(v_reuseFailAlloc_5597_, 31, v_zabbrev_5584_);
lean_ctor_set(v_reuseFailAlloc_5597_, 32, v_v_5585_);
lean_ctor_set(v_reuseFailAlloc_5597_, 33, v_O_5586_);
lean_ctor_set(v_reuseFailAlloc_5597_, 34, v_X_5587_);
lean_ctor_set(v_reuseFailAlloc_5597_, 35, v_x_5588_);
lean_ctor_set(v_reuseFailAlloc_5597_, 36, v_Z_5589_);
v___x_5596_ = v_reuseFailAlloc_5597_;
goto v_reusejp_5595_;
}
v_reusejp_5595_:
{
return v___x_5596_;
}
}
}
}
}
case 22:
{
lean_object* v___x_5604_; uint8_t v_isShared_5605_; uint8_t v_isSharedCheck_5653_; 
v_isSharedCheck_5653_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_5653_ == 0)
{
lean_object* v_unused_5654_; 
v_unused_5654_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_5654_);
v___x_5604_ = v_modifier_4492_;
v_isShared_5605_ = v_isSharedCheck_5653_;
goto v_resetjp_5603_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_5604_ = lean_box(0);
v_isShared_5605_ = v_isSharedCheck_5653_;
goto v_resetjp_5603_;
}
v_resetjp_5603_:
{
lean_object* v_G_5606_; lean_object* v_y_5607_; lean_object* v_u_5608_; lean_object* v_Y_5609_; lean_object* v_D_5610_; lean_object* v_M_5611_; lean_object* v_L_5612_; lean_object* v_d_5613_; lean_object* v_Q_5614_; lean_object* v_q_5615_; lean_object* v_w_5616_; lean_object* v_W_5617_; lean_object* v_E_5618_; lean_object* v_e_5619_; lean_object* v_c_5620_; lean_object* v_F_5621_; lean_object* v_a_5622_; lean_object* v_b_5623_; lean_object* v_B_5624_; lean_object* v_h_5625_; lean_object* v_K_5626_; lean_object* v_k_5627_; lean_object* v_m_5628_; lean_object* v_s_5629_; lean_object* v_S_5630_; lean_object* v_A_5631_; lean_object* v_n_5632_; lean_object* v_N_5633_; lean_object* v_V_5634_; lean_object* v_z_5635_; lean_object* v_zabbrev_5636_; lean_object* v_v_5637_; lean_object* v_O_5638_; lean_object* v_X_5639_; lean_object* v_x_5640_; lean_object* v_Z_5641_; lean_object* v___x_5643_; uint8_t v_isShared_5644_; uint8_t v_isSharedCheck_5651_; 
v_G_5606_ = lean_ctor_get(v_date_4491_, 0);
v_y_5607_ = lean_ctor_get(v_date_4491_, 1);
v_u_5608_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5609_ = lean_ctor_get(v_date_4491_, 3);
v_D_5610_ = lean_ctor_get(v_date_4491_, 4);
v_M_5611_ = lean_ctor_get(v_date_4491_, 5);
v_L_5612_ = lean_ctor_get(v_date_4491_, 6);
v_d_5613_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5614_ = lean_ctor_get(v_date_4491_, 8);
v_q_5615_ = lean_ctor_get(v_date_4491_, 9);
v_w_5616_ = lean_ctor_get(v_date_4491_, 10);
v_W_5617_ = lean_ctor_get(v_date_4491_, 11);
v_E_5618_ = lean_ctor_get(v_date_4491_, 12);
v_e_5619_ = lean_ctor_get(v_date_4491_, 13);
v_c_5620_ = lean_ctor_get(v_date_4491_, 14);
v_F_5621_ = lean_ctor_get(v_date_4491_, 15);
v_a_5622_ = lean_ctor_get(v_date_4491_, 16);
v_b_5623_ = lean_ctor_get(v_date_4491_, 17);
v_B_5624_ = lean_ctor_get(v_date_4491_, 18);
v_h_5625_ = lean_ctor_get(v_date_4491_, 19);
v_K_5626_ = lean_ctor_get(v_date_4491_, 20);
v_k_5627_ = lean_ctor_get(v_date_4491_, 21);
v_m_5628_ = lean_ctor_get(v_date_4491_, 23);
v_s_5629_ = lean_ctor_get(v_date_4491_, 24);
v_S_5630_ = lean_ctor_get(v_date_4491_, 25);
v_A_5631_ = lean_ctor_get(v_date_4491_, 26);
v_n_5632_ = lean_ctor_get(v_date_4491_, 27);
v_N_5633_ = lean_ctor_get(v_date_4491_, 28);
v_V_5634_ = lean_ctor_get(v_date_4491_, 29);
v_z_5635_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5636_ = lean_ctor_get(v_date_4491_, 31);
v_v_5637_ = lean_ctor_get(v_date_4491_, 32);
v_O_5638_ = lean_ctor_get(v_date_4491_, 33);
v_X_5639_ = lean_ctor_get(v_date_4491_, 34);
v_x_5640_ = lean_ctor_get(v_date_4491_, 35);
v_Z_5641_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5651_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5651_ == 0)
{
lean_object* v_unused_5652_; 
v_unused_5652_ = lean_ctor_get(v_date_4491_, 22);
lean_dec(v_unused_5652_);
v___x_5643_ = v_date_4491_;
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
lean_inc(v_k_5627_);
lean_inc(v_K_5626_);
lean_inc(v_h_5625_);
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
lean_dec(v_date_4491_);
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
lean_ctor_set(v___x_5604_, 0, v_data_4493_);
v___x_5646_ = v___x_5604_;
goto v_reusejp_5645_;
}
else
{
lean_object* v_reuseFailAlloc_5650_; 
v_reuseFailAlloc_5650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5650_, 0, v_data_4493_);
v___x_5646_ = v_reuseFailAlloc_5650_;
goto v_reusejp_5645_;
}
v_reusejp_5645_:
{
lean_object* v___x_5648_; 
if (v_isShared_5644_ == 0)
{
lean_ctor_set(v___x_5643_, 22, v___x_5646_);
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
lean_ctor_set(v_reuseFailAlloc_5649_, 19, v_h_5625_);
lean_ctor_set(v_reuseFailAlloc_5649_, 20, v_K_5626_);
lean_ctor_set(v_reuseFailAlloc_5649_, 21, v_k_5627_);
lean_ctor_set(v_reuseFailAlloc_5649_, 22, v___x_5646_);
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
case 23:
{
lean_object* v___x_5656_; uint8_t v_isShared_5657_; uint8_t v_isSharedCheck_5705_; 
v_isSharedCheck_5705_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_5705_ == 0)
{
lean_object* v_unused_5706_; 
v_unused_5706_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_5706_);
v___x_5656_ = v_modifier_4492_;
v_isShared_5657_ = v_isSharedCheck_5705_;
goto v_resetjp_5655_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_5656_ = lean_box(0);
v_isShared_5657_ = v_isSharedCheck_5705_;
goto v_resetjp_5655_;
}
v_resetjp_5655_:
{
lean_object* v_G_5658_; lean_object* v_y_5659_; lean_object* v_u_5660_; lean_object* v_Y_5661_; lean_object* v_D_5662_; lean_object* v_M_5663_; lean_object* v_L_5664_; lean_object* v_d_5665_; lean_object* v_Q_5666_; lean_object* v_q_5667_; lean_object* v_w_5668_; lean_object* v_W_5669_; lean_object* v_E_5670_; lean_object* v_e_5671_; lean_object* v_c_5672_; lean_object* v_F_5673_; lean_object* v_a_5674_; lean_object* v_b_5675_; lean_object* v_B_5676_; lean_object* v_h_5677_; lean_object* v_K_5678_; lean_object* v_k_5679_; lean_object* v_H_5680_; lean_object* v_s_5681_; lean_object* v_S_5682_; lean_object* v_A_5683_; lean_object* v_n_5684_; lean_object* v_N_5685_; lean_object* v_V_5686_; lean_object* v_z_5687_; lean_object* v_zabbrev_5688_; lean_object* v_v_5689_; lean_object* v_O_5690_; lean_object* v_X_5691_; lean_object* v_x_5692_; lean_object* v_Z_5693_; lean_object* v___x_5695_; uint8_t v_isShared_5696_; uint8_t v_isSharedCheck_5703_; 
v_G_5658_ = lean_ctor_get(v_date_4491_, 0);
v_y_5659_ = lean_ctor_get(v_date_4491_, 1);
v_u_5660_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5661_ = lean_ctor_get(v_date_4491_, 3);
v_D_5662_ = lean_ctor_get(v_date_4491_, 4);
v_M_5663_ = lean_ctor_get(v_date_4491_, 5);
v_L_5664_ = lean_ctor_get(v_date_4491_, 6);
v_d_5665_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5666_ = lean_ctor_get(v_date_4491_, 8);
v_q_5667_ = lean_ctor_get(v_date_4491_, 9);
v_w_5668_ = lean_ctor_get(v_date_4491_, 10);
v_W_5669_ = lean_ctor_get(v_date_4491_, 11);
v_E_5670_ = lean_ctor_get(v_date_4491_, 12);
v_e_5671_ = lean_ctor_get(v_date_4491_, 13);
v_c_5672_ = lean_ctor_get(v_date_4491_, 14);
v_F_5673_ = lean_ctor_get(v_date_4491_, 15);
v_a_5674_ = lean_ctor_get(v_date_4491_, 16);
v_b_5675_ = lean_ctor_get(v_date_4491_, 17);
v_B_5676_ = lean_ctor_get(v_date_4491_, 18);
v_h_5677_ = lean_ctor_get(v_date_4491_, 19);
v_K_5678_ = lean_ctor_get(v_date_4491_, 20);
v_k_5679_ = lean_ctor_get(v_date_4491_, 21);
v_H_5680_ = lean_ctor_get(v_date_4491_, 22);
v_s_5681_ = lean_ctor_get(v_date_4491_, 24);
v_S_5682_ = lean_ctor_get(v_date_4491_, 25);
v_A_5683_ = lean_ctor_get(v_date_4491_, 26);
v_n_5684_ = lean_ctor_get(v_date_4491_, 27);
v_N_5685_ = lean_ctor_get(v_date_4491_, 28);
v_V_5686_ = lean_ctor_get(v_date_4491_, 29);
v_z_5687_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5688_ = lean_ctor_get(v_date_4491_, 31);
v_v_5689_ = lean_ctor_get(v_date_4491_, 32);
v_O_5690_ = lean_ctor_get(v_date_4491_, 33);
v_X_5691_ = lean_ctor_get(v_date_4491_, 34);
v_x_5692_ = lean_ctor_get(v_date_4491_, 35);
v_Z_5693_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5703_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5703_ == 0)
{
lean_object* v_unused_5704_; 
v_unused_5704_ = lean_ctor_get(v_date_4491_, 23);
lean_dec(v_unused_5704_);
v___x_5695_ = v_date_4491_;
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
lean_inc(v_H_5680_);
lean_inc(v_k_5679_);
lean_inc(v_K_5678_);
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
lean_dec(v_date_4491_);
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
lean_ctor_set(v___x_5656_, 0, v_data_4493_);
v___x_5698_ = v___x_5656_;
goto v_reusejp_5697_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v_data_4493_);
v___x_5698_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5697_;
}
v_reusejp_5697_:
{
lean_object* v___x_5700_; 
if (v_isShared_5696_ == 0)
{
lean_ctor_set(v___x_5695_, 23, v___x_5698_);
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
lean_ctor_set(v_reuseFailAlloc_5701_, 20, v_K_5678_);
lean_ctor_set(v_reuseFailAlloc_5701_, 21, v_k_5679_);
lean_ctor_set(v_reuseFailAlloc_5701_, 22, v_H_5680_);
lean_ctor_set(v_reuseFailAlloc_5701_, 23, v___x_5698_);
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
case 24:
{
lean_object* v___x_5708_; uint8_t v_isShared_5709_; uint8_t v_isSharedCheck_5757_; 
v_isSharedCheck_5757_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_5757_ == 0)
{
lean_object* v_unused_5758_; 
v_unused_5758_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_5758_);
v___x_5708_ = v_modifier_4492_;
v_isShared_5709_ = v_isSharedCheck_5757_;
goto v_resetjp_5707_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_5708_ = lean_box(0);
v_isShared_5709_ = v_isSharedCheck_5757_;
goto v_resetjp_5707_;
}
v_resetjp_5707_:
{
lean_object* v_G_5710_; lean_object* v_y_5711_; lean_object* v_u_5712_; lean_object* v_Y_5713_; lean_object* v_D_5714_; lean_object* v_M_5715_; lean_object* v_L_5716_; lean_object* v_d_5717_; lean_object* v_Q_5718_; lean_object* v_q_5719_; lean_object* v_w_5720_; lean_object* v_W_5721_; lean_object* v_E_5722_; lean_object* v_e_5723_; lean_object* v_c_5724_; lean_object* v_F_5725_; lean_object* v_a_5726_; lean_object* v_b_5727_; lean_object* v_B_5728_; lean_object* v_h_5729_; lean_object* v_K_5730_; lean_object* v_k_5731_; lean_object* v_H_5732_; lean_object* v_m_5733_; lean_object* v_S_5734_; lean_object* v_A_5735_; lean_object* v_n_5736_; lean_object* v_N_5737_; lean_object* v_V_5738_; lean_object* v_z_5739_; lean_object* v_zabbrev_5740_; lean_object* v_v_5741_; lean_object* v_O_5742_; lean_object* v_X_5743_; lean_object* v_x_5744_; lean_object* v_Z_5745_; lean_object* v___x_5747_; uint8_t v_isShared_5748_; uint8_t v_isSharedCheck_5755_; 
v_G_5710_ = lean_ctor_get(v_date_4491_, 0);
v_y_5711_ = lean_ctor_get(v_date_4491_, 1);
v_u_5712_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5713_ = lean_ctor_get(v_date_4491_, 3);
v_D_5714_ = lean_ctor_get(v_date_4491_, 4);
v_M_5715_ = lean_ctor_get(v_date_4491_, 5);
v_L_5716_ = lean_ctor_get(v_date_4491_, 6);
v_d_5717_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5718_ = lean_ctor_get(v_date_4491_, 8);
v_q_5719_ = lean_ctor_get(v_date_4491_, 9);
v_w_5720_ = lean_ctor_get(v_date_4491_, 10);
v_W_5721_ = lean_ctor_get(v_date_4491_, 11);
v_E_5722_ = lean_ctor_get(v_date_4491_, 12);
v_e_5723_ = lean_ctor_get(v_date_4491_, 13);
v_c_5724_ = lean_ctor_get(v_date_4491_, 14);
v_F_5725_ = lean_ctor_get(v_date_4491_, 15);
v_a_5726_ = lean_ctor_get(v_date_4491_, 16);
v_b_5727_ = lean_ctor_get(v_date_4491_, 17);
v_B_5728_ = lean_ctor_get(v_date_4491_, 18);
v_h_5729_ = lean_ctor_get(v_date_4491_, 19);
v_K_5730_ = lean_ctor_get(v_date_4491_, 20);
v_k_5731_ = lean_ctor_get(v_date_4491_, 21);
v_H_5732_ = lean_ctor_get(v_date_4491_, 22);
v_m_5733_ = lean_ctor_get(v_date_4491_, 23);
v_S_5734_ = lean_ctor_get(v_date_4491_, 25);
v_A_5735_ = lean_ctor_get(v_date_4491_, 26);
v_n_5736_ = lean_ctor_get(v_date_4491_, 27);
v_N_5737_ = lean_ctor_get(v_date_4491_, 28);
v_V_5738_ = lean_ctor_get(v_date_4491_, 29);
v_z_5739_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5740_ = lean_ctor_get(v_date_4491_, 31);
v_v_5741_ = lean_ctor_get(v_date_4491_, 32);
v_O_5742_ = lean_ctor_get(v_date_4491_, 33);
v_X_5743_ = lean_ctor_get(v_date_4491_, 34);
v_x_5744_ = lean_ctor_get(v_date_4491_, 35);
v_Z_5745_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5755_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5755_ == 0)
{
lean_object* v_unused_5756_; 
v_unused_5756_ = lean_ctor_get(v_date_4491_, 24);
lean_dec(v_unused_5756_);
v___x_5747_ = v_date_4491_;
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
lean_inc(v_m_5733_);
lean_inc(v_H_5732_);
lean_inc(v_k_5731_);
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
lean_dec(v_date_4491_);
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
lean_ctor_set(v___x_5708_, 0, v_data_4493_);
v___x_5750_ = v___x_5708_;
goto v_reusejp_5749_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v_data_4493_);
v___x_5750_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5749_;
}
v_reusejp_5749_:
{
lean_object* v___x_5752_; 
if (v_isShared_5748_ == 0)
{
lean_ctor_set(v___x_5747_, 24, v___x_5750_);
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
lean_ctor_set(v_reuseFailAlloc_5753_, 21, v_k_5731_);
lean_ctor_set(v_reuseFailAlloc_5753_, 22, v_H_5732_);
lean_ctor_set(v_reuseFailAlloc_5753_, 23, v_m_5733_);
lean_ctor_set(v_reuseFailAlloc_5753_, 24, v___x_5750_);
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
case 25:
{
lean_object* v___x_5760_; uint8_t v_isShared_5761_; uint8_t v_isSharedCheck_5809_; 
v_isSharedCheck_5809_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_5809_ == 0)
{
lean_object* v_unused_5810_; 
v_unused_5810_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_5810_);
v___x_5760_ = v_modifier_4492_;
v_isShared_5761_ = v_isSharedCheck_5809_;
goto v_resetjp_5759_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_5760_ = lean_box(0);
v_isShared_5761_ = v_isSharedCheck_5809_;
goto v_resetjp_5759_;
}
v_resetjp_5759_:
{
lean_object* v_G_5762_; lean_object* v_y_5763_; lean_object* v_u_5764_; lean_object* v_Y_5765_; lean_object* v_D_5766_; lean_object* v_M_5767_; lean_object* v_L_5768_; lean_object* v_d_5769_; lean_object* v_Q_5770_; lean_object* v_q_5771_; lean_object* v_w_5772_; lean_object* v_W_5773_; lean_object* v_E_5774_; lean_object* v_e_5775_; lean_object* v_c_5776_; lean_object* v_F_5777_; lean_object* v_a_5778_; lean_object* v_b_5779_; lean_object* v_B_5780_; lean_object* v_h_5781_; lean_object* v_K_5782_; lean_object* v_k_5783_; lean_object* v_H_5784_; lean_object* v_m_5785_; lean_object* v_s_5786_; lean_object* v_A_5787_; lean_object* v_n_5788_; lean_object* v_N_5789_; lean_object* v_V_5790_; lean_object* v_z_5791_; lean_object* v_zabbrev_5792_; lean_object* v_v_5793_; lean_object* v_O_5794_; lean_object* v_X_5795_; lean_object* v_x_5796_; lean_object* v_Z_5797_; lean_object* v___x_5799_; uint8_t v_isShared_5800_; uint8_t v_isSharedCheck_5807_; 
v_G_5762_ = lean_ctor_get(v_date_4491_, 0);
v_y_5763_ = lean_ctor_get(v_date_4491_, 1);
v_u_5764_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5765_ = lean_ctor_get(v_date_4491_, 3);
v_D_5766_ = lean_ctor_get(v_date_4491_, 4);
v_M_5767_ = lean_ctor_get(v_date_4491_, 5);
v_L_5768_ = lean_ctor_get(v_date_4491_, 6);
v_d_5769_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5770_ = lean_ctor_get(v_date_4491_, 8);
v_q_5771_ = lean_ctor_get(v_date_4491_, 9);
v_w_5772_ = lean_ctor_get(v_date_4491_, 10);
v_W_5773_ = lean_ctor_get(v_date_4491_, 11);
v_E_5774_ = lean_ctor_get(v_date_4491_, 12);
v_e_5775_ = lean_ctor_get(v_date_4491_, 13);
v_c_5776_ = lean_ctor_get(v_date_4491_, 14);
v_F_5777_ = lean_ctor_get(v_date_4491_, 15);
v_a_5778_ = lean_ctor_get(v_date_4491_, 16);
v_b_5779_ = lean_ctor_get(v_date_4491_, 17);
v_B_5780_ = lean_ctor_get(v_date_4491_, 18);
v_h_5781_ = lean_ctor_get(v_date_4491_, 19);
v_K_5782_ = lean_ctor_get(v_date_4491_, 20);
v_k_5783_ = lean_ctor_get(v_date_4491_, 21);
v_H_5784_ = lean_ctor_get(v_date_4491_, 22);
v_m_5785_ = lean_ctor_get(v_date_4491_, 23);
v_s_5786_ = lean_ctor_get(v_date_4491_, 24);
v_A_5787_ = lean_ctor_get(v_date_4491_, 26);
v_n_5788_ = lean_ctor_get(v_date_4491_, 27);
v_N_5789_ = lean_ctor_get(v_date_4491_, 28);
v_V_5790_ = lean_ctor_get(v_date_4491_, 29);
v_z_5791_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5792_ = lean_ctor_get(v_date_4491_, 31);
v_v_5793_ = lean_ctor_get(v_date_4491_, 32);
v_O_5794_ = lean_ctor_get(v_date_4491_, 33);
v_X_5795_ = lean_ctor_get(v_date_4491_, 34);
v_x_5796_ = lean_ctor_get(v_date_4491_, 35);
v_Z_5797_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5807_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5807_ == 0)
{
lean_object* v_unused_5808_; 
v_unused_5808_ = lean_ctor_get(v_date_4491_, 25);
lean_dec(v_unused_5808_);
v___x_5799_ = v_date_4491_;
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
lean_inc(v_s_5786_);
lean_inc(v_m_5785_);
lean_inc(v_H_5784_);
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
lean_dec(v_date_4491_);
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
lean_ctor_set(v___x_5760_, 0, v_data_4493_);
v___x_5802_ = v___x_5760_;
goto v_reusejp_5801_;
}
else
{
lean_object* v_reuseFailAlloc_5806_; 
v_reuseFailAlloc_5806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5806_, 0, v_data_4493_);
v___x_5802_ = v_reuseFailAlloc_5806_;
goto v_reusejp_5801_;
}
v_reusejp_5801_:
{
lean_object* v___x_5804_; 
if (v_isShared_5800_ == 0)
{
lean_ctor_set(v___x_5799_, 25, v___x_5802_);
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
lean_ctor_set(v_reuseFailAlloc_5805_, 22, v_H_5784_);
lean_ctor_set(v_reuseFailAlloc_5805_, 23, v_m_5785_);
lean_ctor_set(v_reuseFailAlloc_5805_, 24, v_s_5786_);
lean_ctor_set(v_reuseFailAlloc_5805_, 25, v___x_5802_);
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
case 26:
{
lean_object* v___x_5812_; uint8_t v_isShared_5813_; uint8_t v_isSharedCheck_5861_; 
v_isSharedCheck_5861_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_5861_ == 0)
{
lean_object* v_unused_5862_; 
v_unused_5862_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_5862_);
v___x_5812_ = v_modifier_4492_;
v_isShared_5813_ = v_isSharedCheck_5861_;
goto v_resetjp_5811_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_5812_ = lean_box(0);
v_isShared_5813_ = v_isSharedCheck_5861_;
goto v_resetjp_5811_;
}
v_resetjp_5811_:
{
lean_object* v_G_5814_; lean_object* v_y_5815_; lean_object* v_u_5816_; lean_object* v_Y_5817_; lean_object* v_D_5818_; lean_object* v_M_5819_; lean_object* v_L_5820_; lean_object* v_d_5821_; lean_object* v_Q_5822_; lean_object* v_q_5823_; lean_object* v_w_5824_; lean_object* v_W_5825_; lean_object* v_E_5826_; lean_object* v_e_5827_; lean_object* v_c_5828_; lean_object* v_F_5829_; lean_object* v_a_5830_; lean_object* v_b_5831_; lean_object* v_B_5832_; lean_object* v_h_5833_; lean_object* v_K_5834_; lean_object* v_k_5835_; lean_object* v_H_5836_; lean_object* v_m_5837_; lean_object* v_s_5838_; lean_object* v_S_5839_; lean_object* v_n_5840_; lean_object* v_N_5841_; lean_object* v_V_5842_; lean_object* v_z_5843_; lean_object* v_zabbrev_5844_; lean_object* v_v_5845_; lean_object* v_O_5846_; lean_object* v_X_5847_; lean_object* v_x_5848_; lean_object* v_Z_5849_; lean_object* v___x_5851_; uint8_t v_isShared_5852_; uint8_t v_isSharedCheck_5859_; 
v_G_5814_ = lean_ctor_get(v_date_4491_, 0);
v_y_5815_ = lean_ctor_get(v_date_4491_, 1);
v_u_5816_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5817_ = lean_ctor_get(v_date_4491_, 3);
v_D_5818_ = lean_ctor_get(v_date_4491_, 4);
v_M_5819_ = lean_ctor_get(v_date_4491_, 5);
v_L_5820_ = lean_ctor_get(v_date_4491_, 6);
v_d_5821_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5822_ = lean_ctor_get(v_date_4491_, 8);
v_q_5823_ = lean_ctor_get(v_date_4491_, 9);
v_w_5824_ = lean_ctor_get(v_date_4491_, 10);
v_W_5825_ = lean_ctor_get(v_date_4491_, 11);
v_E_5826_ = lean_ctor_get(v_date_4491_, 12);
v_e_5827_ = lean_ctor_get(v_date_4491_, 13);
v_c_5828_ = lean_ctor_get(v_date_4491_, 14);
v_F_5829_ = lean_ctor_get(v_date_4491_, 15);
v_a_5830_ = lean_ctor_get(v_date_4491_, 16);
v_b_5831_ = lean_ctor_get(v_date_4491_, 17);
v_B_5832_ = lean_ctor_get(v_date_4491_, 18);
v_h_5833_ = lean_ctor_get(v_date_4491_, 19);
v_K_5834_ = lean_ctor_get(v_date_4491_, 20);
v_k_5835_ = lean_ctor_get(v_date_4491_, 21);
v_H_5836_ = lean_ctor_get(v_date_4491_, 22);
v_m_5837_ = lean_ctor_get(v_date_4491_, 23);
v_s_5838_ = lean_ctor_get(v_date_4491_, 24);
v_S_5839_ = lean_ctor_get(v_date_4491_, 25);
v_n_5840_ = lean_ctor_get(v_date_4491_, 27);
v_N_5841_ = lean_ctor_get(v_date_4491_, 28);
v_V_5842_ = lean_ctor_get(v_date_4491_, 29);
v_z_5843_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5844_ = lean_ctor_get(v_date_4491_, 31);
v_v_5845_ = lean_ctor_get(v_date_4491_, 32);
v_O_5846_ = lean_ctor_get(v_date_4491_, 33);
v_X_5847_ = lean_ctor_get(v_date_4491_, 34);
v_x_5848_ = lean_ctor_get(v_date_4491_, 35);
v_Z_5849_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5859_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5859_ == 0)
{
lean_object* v_unused_5860_; 
v_unused_5860_ = lean_ctor_get(v_date_4491_, 26);
lean_dec(v_unused_5860_);
v___x_5851_ = v_date_4491_;
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
lean_inc(v_S_5839_);
lean_inc(v_s_5838_);
lean_inc(v_m_5837_);
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
lean_dec(v_date_4491_);
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
lean_ctor_set(v___x_5812_, 0, v_data_4493_);
v___x_5854_ = v___x_5812_;
goto v_reusejp_5853_;
}
else
{
lean_object* v_reuseFailAlloc_5858_; 
v_reuseFailAlloc_5858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5858_, 0, v_data_4493_);
v___x_5854_ = v_reuseFailAlloc_5858_;
goto v_reusejp_5853_;
}
v_reusejp_5853_:
{
lean_object* v___x_5856_; 
if (v_isShared_5852_ == 0)
{
lean_ctor_set(v___x_5851_, 26, v___x_5854_);
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
lean_ctor_set(v_reuseFailAlloc_5857_, 23, v_m_5837_);
lean_ctor_set(v_reuseFailAlloc_5857_, 24, v_s_5838_);
lean_ctor_set(v_reuseFailAlloc_5857_, 25, v_S_5839_);
lean_ctor_set(v_reuseFailAlloc_5857_, 26, v___x_5854_);
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
case 27:
{
lean_object* v___x_5864_; uint8_t v_isShared_5865_; uint8_t v_isSharedCheck_5913_; 
v_isSharedCheck_5913_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_5913_ == 0)
{
lean_object* v_unused_5914_; 
v_unused_5914_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_5914_);
v___x_5864_ = v_modifier_4492_;
v_isShared_5865_ = v_isSharedCheck_5913_;
goto v_resetjp_5863_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_5864_ = lean_box(0);
v_isShared_5865_ = v_isSharedCheck_5913_;
goto v_resetjp_5863_;
}
v_resetjp_5863_:
{
lean_object* v_G_5866_; lean_object* v_y_5867_; lean_object* v_u_5868_; lean_object* v_Y_5869_; lean_object* v_D_5870_; lean_object* v_M_5871_; lean_object* v_L_5872_; lean_object* v_d_5873_; lean_object* v_Q_5874_; lean_object* v_q_5875_; lean_object* v_w_5876_; lean_object* v_W_5877_; lean_object* v_E_5878_; lean_object* v_e_5879_; lean_object* v_c_5880_; lean_object* v_F_5881_; lean_object* v_a_5882_; lean_object* v_b_5883_; lean_object* v_B_5884_; lean_object* v_h_5885_; lean_object* v_K_5886_; lean_object* v_k_5887_; lean_object* v_H_5888_; lean_object* v_m_5889_; lean_object* v_s_5890_; lean_object* v_S_5891_; lean_object* v_A_5892_; lean_object* v_N_5893_; lean_object* v_V_5894_; lean_object* v_z_5895_; lean_object* v_zabbrev_5896_; lean_object* v_v_5897_; lean_object* v_O_5898_; lean_object* v_X_5899_; lean_object* v_x_5900_; lean_object* v_Z_5901_; lean_object* v___x_5903_; uint8_t v_isShared_5904_; uint8_t v_isSharedCheck_5911_; 
v_G_5866_ = lean_ctor_get(v_date_4491_, 0);
v_y_5867_ = lean_ctor_get(v_date_4491_, 1);
v_u_5868_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5869_ = lean_ctor_get(v_date_4491_, 3);
v_D_5870_ = lean_ctor_get(v_date_4491_, 4);
v_M_5871_ = lean_ctor_get(v_date_4491_, 5);
v_L_5872_ = lean_ctor_get(v_date_4491_, 6);
v_d_5873_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5874_ = lean_ctor_get(v_date_4491_, 8);
v_q_5875_ = lean_ctor_get(v_date_4491_, 9);
v_w_5876_ = lean_ctor_get(v_date_4491_, 10);
v_W_5877_ = lean_ctor_get(v_date_4491_, 11);
v_E_5878_ = lean_ctor_get(v_date_4491_, 12);
v_e_5879_ = lean_ctor_get(v_date_4491_, 13);
v_c_5880_ = lean_ctor_get(v_date_4491_, 14);
v_F_5881_ = lean_ctor_get(v_date_4491_, 15);
v_a_5882_ = lean_ctor_get(v_date_4491_, 16);
v_b_5883_ = lean_ctor_get(v_date_4491_, 17);
v_B_5884_ = lean_ctor_get(v_date_4491_, 18);
v_h_5885_ = lean_ctor_get(v_date_4491_, 19);
v_K_5886_ = lean_ctor_get(v_date_4491_, 20);
v_k_5887_ = lean_ctor_get(v_date_4491_, 21);
v_H_5888_ = lean_ctor_get(v_date_4491_, 22);
v_m_5889_ = lean_ctor_get(v_date_4491_, 23);
v_s_5890_ = lean_ctor_get(v_date_4491_, 24);
v_S_5891_ = lean_ctor_get(v_date_4491_, 25);
v_A_5892_ = lean_ctor_get(v_date_4491_, 26);
v_N_5893_ = lean_ctor_get(v_date_4491_, 28);
v_V_5894_ = lean_ctor_get(v_date_4491_, 29);
v_z_5895_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5896_ = lean_ctor_get(v_date_4491_, 31);
v_v_5897_ = lean_ctor_get(v_date_4491_, 32);
v_O_5898_ = lean_ctor_get(v_date_4491_, 33);
v_X_5899_ = lean_ctor_get(v_date_4491_, 34);
v_x_5900_ = lean_ctor_get(v_date_4491_, 35);
v_Z_5901_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5911_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5911_ == 0)
{
lean_object* v_unused_5912_; 
v_unused_5912_ = lean_ctor_get(v_date_4491_, 27);
lean_dec(v_unused_5912_);
v___x_5903_ = v_date_4491_;
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
lean_inc(v_A_5892_);
lean_inc(v_S_5891_);
lean_inc(v_s_5890_);
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
lean_dec(v_date_4491_);
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
lean_ctor_set(v___x_5864_, 0, v_data_4493_);
v___x_5906_ = v___x_5864_;
goto v_reusejp_5905_;
}
else
{
lean_object* v_reuseFailAlloc_5910_; 
v_reuseFailAlloc_5910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5910_, 0, v_data_4493_);
v___x_5906_ = v_reuseFailAlloc_5910_;
goto v_reusejp_5905_;
}
v_reusejp_5905_:
{
lean_object* v___x_5908_; 
if (v_isShared_5904_ == 0)
{
lean_ctor_set(v___x_5903_, 27, v___x_5906_);
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
lean_ctor_set(v_reuseFailAlloc_5909_, 24, v_s_5890_);
lean_ctor_set(v_reuseFailAlloc_5909_, 25, v_S_5891_);
lean_ctor_set(v_reuseFailAlloc_5909_, 26, v_A_5892_);
lean_ctor_set(v_reuseFailAlloc_5909_, 27, v___x_5906_);
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
case 28:
{
lean_object* v___x_5916_; uint8_t v_isShared_5917_; uint8_t v_isSharedCheck_5965_; 
v_isSharedCheck_5965_ = !lean_is_exclusive(v_modifier_4492_);
if (v_isSharedCheck_5965_ == 0)
{
lean_object* v_unused_5966_; 
v_unused_5966_ = lean_ctor_get(v_modifier_4492_, 0);
lean_dec(v_unused_5966_);
v___x_5916_ = v_modifier_4492_;
v_isShared_5917_ = v_isSharedCheck_5965_;
goto v_resetjp_5915_;
}
else
{
lean_dec(v_modifier_4492_);
v___x_5916_ = lean_box(0);
v_isShared_5917_ = v_isSharedCheck_5965_;
goto v_resetjp_5915_;
}
v_resetjp_5915_:
{
lean_object* v_G_5918_; lean_object* v_y_5919_; lean_object* v_u_5920_; lean_object* v_Y_5921_; lean_object* v_D_5922_; lean_object* v_M_5923_; lean_object* v_L_5924_; lean_object* v_d_5925_; lean_object* v_Q_5926_; lean_object* v_q_5927_; lean_object* v_w_5928_; lean_object* v_W_5929_; lean_object* v_E_5930_; lean_object* v_e_5931_; lean_object* v_c_5932_; lean_object* v_F_5933_; lean_object* v_a_5934_; lean_object* v_b_5935_; lean_object* v_B_5936_; lean_object* v_h_5937_; lean_object* v_K_5938_; lean_object* v_k_5939_; lean_object* v_H_5940_; lean_object* v_m_5941_; lean_object* v_s_5942_; lean_object* v_S_5943_; lean_object* v_A_5944_; lean_object* v_n_5945_; lean_object* v_V_5946_; lean_object* v_z_5947_; lean_object* v_zabbrev_5948_; lean_object* v_v_5949_; lean_object* v_O_5950_; lean_object* v_X_5951_; lean_object* v_x_5952_; lean_object* v_Z_5953_; lean_object* v___x_5955_; uint8_t v_isShared_5956_; uint8_t v_isSharedCheck_5963_; 
v_G_5918_ = lean_ctor_get(v_date_4491_, 0);
v_y_5919_ = lean_ctor_get(v_date_4491_, 1);
v_u_5920_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5921_ = lean_ctor_get(v_date_4491_, 3);
v_D_5922_ = lean_ctor_get(v_date_4491_, 4);
v_M_5923_ = lean_ctor_get(v_date_4491_, 5);
v_L_5924_ = lean_ctor_get(v_date_4491_, 6);
v_d_5925_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5926_ = lean_ctor_get(v_date_4491_, 8);
v_q_5927_ = lean_ctor_get(v_date_4491_, 9);
v_w_5928_ = lean_ctor_get(v_date_4491_, 10);
v_W_5929_ = lean_ctor_get(v_date_4491_, 11);
v_E_5930_ = lean_ctor_get(v_date_4491_, 12);
v_e_5931_ = lean_ctor_get(v_date_4491_, 13);
v_c_5932_ = lean_ctor_get(v_date_4491_, 14);
v_F_5933_ = lean_ctor_get(v_date_4491_, 15);
v_a_5934_ = lean_ctor_get(v_date_4491_, 16);
v_b_5935_ = lean_ctor_get(v_date_4491_, 17);
v_B_5936_ = lean_ctor_get(v_date_4491_, 18);
v_h_5937_ = lean_ctor_get(v_date_4491_, 19);
v_K_5938_ = lean_ctor_get(v_date_4491_, 20);
v_k_5939_ = lean_ctor_get(v_date_4491_, 21);
v_H_5940_ = lean_ctor_get(v_date_4491_, 22);
v_m_5941_ = lean_ctor_get(v_date_4491_, 23);
v_s_5942_ = lean_ctor_get(v_date_4491_, 24);
v_S_5943_ = lean_ctor_get(v_date_4491_, 25);
v_A_5944_ = lean_ctor_get(v_date_4491_, 26);
v_n_5945_ = lean_ctor_get(v_date_4491_, 27);
v_V_5946_ = lean_ctor_get(v_date_4491_, 29);
v_z_5947_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5948_ = lean_ctor_get(v_date_4491_, 31);
v_v_5949_ = lean_ctor_get(v_date_4491_, 32);
v_O_5950_ = lean_ctor_get(v_date_4491_, 33);
v_X_5951_ = lean_ctor_get(v_date_4491_, 34);
v_x_5952_ = lean_ctor_get(v_date_4491_, 35);
v_Z_5953_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_5963_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_5963_ == 0)
{
lean_object* v_unused_5964_; 
v_unused_5964_ = lean_ctor_get(v_date_4491_, 28);
lean_dec(v_unused_5964_);
v___x_5955_ = v_date_4491_;
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
lean_inc(v_n_5945_);
lean_inc(v_A_5944_);
lean_inc(v_S_5943_);
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
lean_dec(v_date_4491_);
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
lean_ctor_set(v___x_5916_, 0, v_data_4493_);
v___x_5958_ = v___x_5916_;
goto v_reusejp_5957_;
}
else
{
lean_object* v_reuseFailAlloc_5962_; 
v_reuseFailAlloc_5962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5962_, 0, v_data_4493_);
v___x_5958_ = v_reuseFailAlloc_5962_;
goto v_reusejp_5957_;
}
v_reusejp_5957_:
{
lean_object* v___x_5960_; 
if (v_isShared_5956_ == 0)
{
lean_ctor_set(v___x_5955_, 28, v___x_5958_);
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
lean_ctor_set(v_reuseFailAlloc_5961_, 25, v_S_5943_);
lean_ctor_set(v_reuseFailAlloc_5961_, 26, v_A_5944_);
lean_ctor_set(v_reuseFailAlloc_5961_, 27, v_n_5945_);
lean_ctor_set(v_reuseFailAlloc_5961_, 28, v___x_5958_);
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
case 29:
{
lean_object* v_G_5967_; lean_object* v_y_5968_; lean_object* v_u_5969_; lean_object* v_Y_5970_; lean_object* v_D_5971_; lean_object* v_M_5972_; lean_object* v_L_5973_; lean_object* v_d_5974_; lean_object* v_Q_5975_; lean_object* v_q_5976_; lean_object* v_w_5977_; lean_object* v_W_5978_; lean_object* v_E_5979_; lean_object* v_e_5980_; lean_object* v_c_5981_; lean_object* v_F_5982_; lean_object* v_a_5983_; lean_object* v_b_5984_; lean_object* v_B_5985_; lean_object* v_h_5986_; lean_object* v_K_5987_; lean_object* v_k_5988_; lean_object* v_H_5989_; lean_object* v_m_5990_; lean_object* v_s_5991_; lean_object* v_S_5992_; lean_object* v_A_5993_; lean_object* v_n_5994_; lean_object* v_N_5995_; lean_object* v_z_5996_; lean_object* v_zabbrev_5997_; lean_object* v_v_5998_; lean_object* v_O_5999_; lean_object* v_X_6000_; lean_object* v_x_6001_; lean_object* v_Z_6002_; lean_object* v___x_6004_; uint8_t v_isShared_6005_; uint8_t v_isSharedCheck_6010_; 
lean_dec_ref_known(v_modifier_4492_, 0);
v_G_5967_ = lean_ctor_get(v_date_4491_, 0);
v_y_5968_ = lean_ctor_get(v_date_4491_, 1);
v_u_5969_ = lean_ctor_get(v_date_4491_, 2);
v_Y_5970_ = lean_ctor_get(v_date_4491_, 3);
v_D_5971_ = lean_ctor_get(v_date_4491_, 4);
v_M_5972_ = lean_ctor_get(v_date_4491_, 5);
v_L_5973_ = lean_ctor_get(v_date_4491_, 6);
v_d_5974_ = lean_ctor_get(v_date_4491_, 7);
v_Q_5975_ = lean_ctor_get(v_date_4491_, 8);
v_q_5976_ = lean_ctor_get(v_date_4491_, 9);
v_w_5977_ = lean_ctor_get(v_date_4491_, 10);
v_W_5978_ = lean_ctor_get(v_date_4491_, 11);
v_E_5979_ = lean_ctor_get(v_date_4491_, 12);
v_e_5980_ = lean_ctor_get(v_date_4491_, 13);
v_c_5981_ = lean_ctor_get(v_date_4491_, 14);
v_F_5982_ = lean_ctor_get(v_date_4491_, 15);
v_a_5983_ = lean_ctor_get(v_date_4491_, 16);
v_b_5984_ = lean_ctor_get(v_date_4491_, 17);
v_B_5985_ = lean_ctor_get(v_date_4491_, 18);
v_h_5986_ = lean_ctor_get(v_date_4491_, 19);
v_K_5987_ = lean_ctor_get(v_date_4491_, 20);
v_k_5988_ = lean_ctor_get(v_date_4491_, 21);
v_H_5989_ = lean_ctor_get(v_date_4491_, 22);
v_m_5990_ = lean_ctor_get(v_date_4491_, 23);
v_s_5991_ = lean_ctor_get(v_date_4491_, 24);
v_S_5992_ = lean_ctor_get(v_date_4491_, 25);
v_A_5993_ = lean_ctor_get(v_date_4491_, 26);
v_n_5994_ = lean_ctor_get(v_date_4491_, 27);
v_N_5995_ = lean_ctor_get(v_date_4491_, 28);
v_z_5996_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_5997_ = lean_ctor_get(v_date_4491_, 31);
v_v_5998_ = lean_ctor_get(v_date_4491_, 32);
v_O_5999_ = lean_ctor_get(v_date_4491_, 33);
v_X_6000_ = lean_ctor_get(v_date_4491_, 34);
v_x_6001_ = lean_ctor_get(v_date_4491_, 35);
v_Z_6002_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_6010_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_6010_ == 0)
{
lean_object* v_unused_6011_; 
v_unused_6011_ = lean_ctor_get(v_date_4491_, 29);
lean_dec(v_unused_6011_);
v___x_6004_ = v_date_4491_;
v_isShared_6005_ = v_isSharedCheck_6010_;
goto v_resetjp_6003_;
}
else
{
lean_inc(v_Z_6002_);
lean_inc(v_x_6001_);
lean_inc(v_X_6000_);
lean_inc(v_O_5999_);
lean_inc(v_v_5998_);
lean_inc(v_zabbrev_5997_);
lean_inc(v_z_5996_);
lean_inc(v_N_5995_);
lean_inc(v_n_5994_);
lean_inc(v_A_5993_);
lean_inc(v_S_5992_);
lean_inc(v_s_5991_);
lean_inc(v_m_5990_);
lean_inc(v_H_5989_);
lean_inc(v_k_5988_);
lean_inc(v_K_5987_);
lean_inc(v_h_5986_);
lean_inc(v_B_5985_);
lean_inc(v_b_5984_);
lean_inc(v_a_5983_);
lean_inc(v_F_5982_);
lean_inc(v_c_5981_);
lean_inc(v_e_5980_);
lean_inc(v_E_5979_);
lean_inc(v_W_5978_);
lean_inc(v_w_5977_);
lean_inc(v_q_5976_);
lean_inc(v_Q_5975_);
lean_inc(v_d_5974_);
lean_inc(v_L_5973_);
lean_inc(v_M_5972_);
lean_inc(v_D_5971_);
lean_inc(v_Y_5970_);
lean_inc(v_u_5969_);
lean_inc(v_y_5968_);
lean_inc(v_G_5967_);
lean_dec(v_date_4491_);
v___x_6004_ = lean_box(0);
v_isShared_6005_ = v_isSharedCheck_6010_;
goto v_resetjp_6003_;
}
v_resetjp_6003_:
{
lean_object* v___x_6006_; lean_object* v___x_6008_; 
v___x_6006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6006_, 0, v_data_4493_);
if (v_isShared_6005_ == 0)
{
lean_ctor_set(v___x_6004_, 29, v___x_6006_);
v___x_6008_ = v___x_6004_;
goto v_reusejp_6007_;
}
else
{
lean_object* v_reuseFailAlloc_6009_; 
v_reuseFailAlloc_6009_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6009_, 0, v_G_5967_);
lean_ctor_set(v_reuseFailAlloc_6009_, 1, v_y_5968_);
lean_ctor_set(v_reuseFailAlloc_6009_, 2, v_u_5969_);
lean_ctor_set(v_reuseFailAlloc_6009_, 3, v_Y_5970_);
lean_ctor_set(v_reuseFailAlloc_6009_, 4, v_D_5971_);
lean_ctor_set(v_reuseFailAlloc_6009_, 5, v_M_5972_);
lean_ctor_set(v_reuseFailAlloc_6009_, 6, v_L_5973_);
lean_ctor_set(v_reuseFailAlloc_6009_, 7, v_d_5974_);
lean_ctor_set(v_reuseFailAlloc_6009_, 8, v_Q_5975_);
lean_ctor_set(v_reuseFailAlloc_6009_, 9, v_q_5976_);
lean_ctor_set(v_reuseFailAlloc_6009_, 10, v_w_5977_);
lean_ctor_set(v_reuseFailAlloc_6009_, 11, v_W_5978_);
lean_ctor_set(v_reuseFailAlloc_6009_, 12, v_E_5979_);
lean_ctor_set(v_reuseFailAlloc_6009_, 13, v_e_5980_);
lean_ctor_set(v_reuseFailAlloc_6009_, 14, v_c_5981_);
lean_ctor_set(v_reuseFailAlloc_6009_, 15, v_F_5982_);
lean_ctor_set(v_reuseFailAlloc_6009_, 16, v_a_5983_);
lean_ctor_set(v_reuseFailAlloc_6009_, 17, v_b_5984_);
lean_ctor_set(v_reuseFailAlloc_6009_, 18, v_B_5985_);
lean_ctor_set(v_reuseFailAlloc_6009_, 19, v_h_5986_);
lean_ctor_set(v_reuseFailAlloc_6009_, 20, v_K_5987_);
lean_ctor_set(v_reuseFailAlloc_6009_, 21, v_k_5988_);
lean_ctor_set(v_reuseFailAlloc_6009_, 22, v_H_5989_);
lean_ctor_set(v_reuseFailAlloc_6009_, 23, v_m_5990_);
lean_ctor_set(v_reuseFailAlloc_6009_, 24, v_s_5991_);
lean_ctor_set(v_reuseFailAlloc_6009_, 25, v_S_5992_);
lean_ctor_set(v_reuseFailAlloc_6009_, 26, v_A_5993_);
lean_ctor_set(v_reuseFailAlloc_6009_, 27, v_n_5994_);
lean_ctor_set(v_reuseFailAlloc_6009_, 28, v_N_5995_);
lean_ctor_set(v_reuseFailAlloc_6009_, 29, v___x_6006_);
lean_ctor_set(v_reuseFailAlloc_6009_, 30, v_z_5996_);
lean_ctor_set(v_reuseFailAlloc_6009_, 31, v_zabbrev_5997_);
lean_ctor_set(v_reuseFailAlloc_6009_, 32, v_v_5998_);
lean_ctor_set(v_reuseFailAlloc_6009_, 33, v_O_5999_);
lean_ctor_set(v_reuseFailAlloc_6009_, 34, v_X_6000_);
lean_ctor_set(v_reuseFailAlloc_6009_, 35, v_x_6001_);
lean_ctor_set(v_reuseFailAlloc_6009_, 36, v_Z_6002_);
v___x_6008_ = v_reuseFailAlloc_6009_;
goto v_reusejp_6007_;
}
v_reusejp_6007_:
{
return v___x_6008_;
}
}
}
case 30:
{
uint8_t v_presentation_6012_; 
v_presentation_6012_ = lean_ctor_get_uint8(v_modifier_4492_, 0);
lean_dec_ref_known(v_modifier_4492_, 0);
if (v_presentation_6012_ == 0)
{
lean_object* v_G_6013_; lean_object* v_y_6014_; lean_object* v_u_6015_; lean_object* v_Y_6016_; lean_object* v_D_6017_; lean_object* v_M_6018_; lean_object* v_L_6019_; lean_object* v_d_6020_; lean_object* v_Q_6021_; lean_object* v_q_6022_; lean_object* v_w_6023_; lean_object* v_W_6024_; lean_object* v_E_6025_; lean_object* v_e_6026_; lean_object* v_c_6027_; lean_object* v_F_6028_; lean_object* v_a_6029_; lean_object* v_b_6030_; lean_object* v_B_6031_; lean_object* v_h_6032_; lean_object* v_K_6033_; lean_object* v_k_6034_; lean_object* v_H_6035_; lean_object* v_m_6036_; lean_object* v_s_6037_; lean_object* v_S_6038_; lean_object* v_A_6039_; lean_object* v_n_6040_; lean_object* v_N_6041_; lean_object* v_V_6042_; lean_object* v_z_6043_; lean_object* v_v_6044_; lean_object* v_O_6045_; lean_object* v_X_6046_; lean_object* v_x_6047_; lean_object* v_Z_6048_; lean_object* v___x_6050_; uint8_t v_isShared_6051_; uint8_t v_isSharedCheck_6056_; 
v_G_6013_ = lean_ctor_get(v_date_4491_, 0);
v_y_6014_ = lean_ctor_get(v_date_4491_, 1);
v_u_6015_ = lean_ctor_get(v_date_4491_, 2);
v_Y_6016_ = lean_ctor_get(v_date_4491_, 3);
v_D_6017_ = lean_ctor_get(v_date_4491_, 4);
v_M_6018_ = lean_ctor_get(v_date_4491_, 5);
v_L_6019_ = lean_ctor_get(v_date_4491_, 6);
v_d_6020_ = lean_ctor_get(v_date_4491_, 7);
v_Q_6021_ = lean_ctor_get(v_date_4491_, 8);
v_q_6022_ = lean_ctor_get(v_date_4491_, 9);
v_w_6023_ = lean_ctor_get(v_date_4491_, 10);
v_W_6024_ = lean_ctor_get(v_date_4491_, 11);
v_E_6025_ = lean_ctor_get(v_date_4491_, 12);
v_e_6026_ = lean_ctor_get(v_date_4491_, 13);
v_c_6027_ = lean_ctor_get(v_date_4491_, 14);
v_F_6028_ = lean_ctor_get(v_date_4491_, 15);
v_a_6029_ = lean_ctor_get(v_date_4491_, 16);
v_b_6030_ = lean_ctor_get(v_date_4491_, 17);
v_B_6031_ = lean_ctor_get(v_date_4491_, 18);
v_h_6032_ = lean_ctor_get(v_date_4491_, 19);
v_K_6033_ = lean_ctor_get(v_date_4491_, 20);
v_k_6034_ = lean_ctor_get(v_date_4491_, 21);
v_H_6035_ = lean_ctor_get(v_date_4491_, 22);
v_m_6036_ = lean_ctor_get(v_date_4491_, 23);
v_s_6037_ = lean_ctor_get(v_date_4491_, 24);
v_S_6038_ = lean_ctor_get(v_date_4491_, 25);
v_A_6039_ = lean_ctor_get(v_date_4491_, 26);
v_n_6040_ = lean_ctor_get(v_date_4491_, 27);
v_N_6041_ = lean_ctor_get(v_date_4491_, 28);
v_V_6042_ = lean_ctor_get(v_date_4491_, 29);
v_z_6043_ = lean_ctor_get(v_date_4491_, 30);
v_v_6044_ = lean_ctor_get(v_date_4491_, 32);
v_O_6045_ = lean_ctor_get(v_date_4491_, 33);
v_X_6046_ = lean_ctor_get(v_date_4491_, 34);
v_x_6047_ = lean_ctor_get(v_date_4491_, 35);
v_Z_6048_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_6056_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_6056_ == 0)
{
lean_object* v_unused_6057_; 
v_unused_6057_ = lean_ctor_get(v_date_4491_, 31);
lean_dec(v_unused_6057_);
v___x_6050_ = v_date_4491_;
v_isShared_6051_ = v_isSharedCheck_6056_;
goto v_resetjp_6049_;
}
else
{
lean_inc(v_Z_6048_);
lean_inc(v_x_6047_);
lean_inc(v_X_6046_);
lean_inc(v_O_6045_);
lean_inc(v_v_6044_);
lean_inc(v_z_6043_);
lean_inc(v_V_6042_);
lean_inc(v_N_6041_);
lean_inc(v_n_6040_);
lean_inc(v_A_6039_);
lean_inc(v_S_6038_);
lean_inc(v_s_6037_);
lean_inc(v_m_6036_);
lean_inc(v_H_6035_);
lean_inc(v_k_6034_);
lean_inc(v_K_6033_);
lean_inc(v_h_6032_);
lean_inc(v_B_6031_);
lean_inc(v_b_6030_);
lean_inc(v_a_6029_);
lean_inc(v_F_6028_);
lean_inc(v_c_6027_);
lean_inc(v_e_6026_);
lean_inc(v_E_6025_);
lean_inc(v_W_6024_);
lean_inc(v_w_6023_);
lean_inc(v_q_6022_);
lean_inc(v_Q_6021_);
lean_inc(v_d_6020_);
lean_inc(v_L_6019_);
lean_inc(v_M_6018_);
lean_inc(v_D_6017_);
lean_inc(v_Y_6016_);
lean_inc(v_u_6015_);
lean_inc(v_y_6014_);
lean_inc(v_G_6013_);
lean_dec(v_date_4491_);
v___x_6050_ = lean_box(0);
v_isShared_6051_ = v_isSharedCheck_6056_;
goto v_resetjp_6049_;
}
v_resetjp_6049_:
{
lean_object* v___x_6052_; lean_object* v___x_6054_; 
v___x_6052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6052_, 0, v_data_4493_);
if (v_isShared_6051_ == 0)
{
lean_ctor_set(v___x_6050_, 31, v___x_6052_);
v___x_6054_ = v___x_6050_;
goto v_reusejp_6053_;
}
else
{
lean_object* v_reuseFailAlloc_6055_; 
v_reuseFailAlloc_6055_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6055_, 0, v_G_6013_);
lean_ctor_set(v_reuseFailAlloc_6055_, 1, v_y_6014_);
lean_ctor_set(v_reuseFailAlloc_6055_, 2, v_u_6015_);
lean_ctor_set(v_reuseFailAlloc_6055_, 3, v_Y_6016_);
lean_ctor_set(v_reuseFailAlloc_6055_, 4, v_D_6017_);
lean_ctor_set(v_reuseFailAlloc_6055_, 5, v_M_6018_);
lean_ctor_set(v_reuseFailAlloc_6055_, 6, v_L_6019_);
lean_ctor_set(v_reuseFailAlloc_6055_, 7, v_d_6020_);
lean_ctor_set(v_reuseFailAlloc_6055_, 8, v_Q_6021_);
lean_ctor_set(v_reuseFailAlloc_6055_, 9, v_q_6022_);
lean_ctor_set(v_reuseFailAlloc_6055_, 10, v_w_6023_);
lean_ctor_set(v_reuseFailAlloc_6055_, 11, v_W_6024_);
lean_ctor_set(v_reuseFailAlloc_6055_, 12, v_E_6025_);
lean_ctor_set(v_reuseFailAlloc_6055_, 13, v_e_6026_);
lean_ctor_set(v_reuseFailAlloc_6055_, 14, v_c_6027_);
lean_ctor_set(v_reuseFailAlloc_6055_, 15, v_F_6028_);
lean_ctor_set(v_reuseFailAlloc_6055_, 16, v_a_6029_);
lean_ctor_set(v_reuseFailAlloc_6055_, 17, v_b_6030_);
lean_ctor_set(v_reuseFailAlloc_6055_, 18, v_B_6031_);
lean_ctor_set(v_reuseFailAlloc_6055_, 19, v_h_6032_);
lean_ctor_set(v_reuseFailAlloc_6055_, 20, v_K_6033_);
lean_ctor_set(v_reuseFailAlloc_6055_, 21, v_k_6034_);
lean_ctor_set(v_reuseFailAlloc_6055_, 22, v_H_6035_);
lean_ctor_set(v_reuseFailAlloc_6055_, 23, v_m_6036_);
lean_ctor_set(v_reuseFailAlloc_6055_, 24, v_s_6037_);
lean_ctor_set(v_reuseFailAlloc_6055_, 25, v_S_6038_);
lean_ctor_set(v_reuseFailAlloc_6055_, 26, v_A_6039_);
lean_ctor_set(v_reuseFailAlloc_6055_, 27, v_n_6040_);
lean_ctor_set(v_reuseFailAlloc_6055_, 28, v_N_6041_);
lean_ctor_set(v_reuseFailAlloc_6055_, 29, v_V_6042_);
lean_ctor_set(v_reuseFailAlloc_6055_, 30, v_z_6043_);
lean_ctor_set(v_reuseFailAlloc_6055_, 31, v___x_6052_);
lean_ctor_set(v_reuseFailAlloc_6055_, 32, v_v_6044_);
lean_ctor_set(v_reuseFailAlloc_6055_, 33, v_O_6045_);
lean_ctor_set(v_reuseFailAlloc_6055_, 34, v_X_6046_);
lean_ctor_set(v_reuseFailAlloc_6055_, 35, v_x_6047_);
lean_ctor_set(v_reuseFailAlloc_6055_, 36, v_Z_6048_);
v___x_6054_ = v_reuseFailAlloc_6055_;
goto v_reusejp_6053_;
}
v_reusejp_6053_:
{
return v___x_6054_;
}
}
}
else
{
lean_object* v_G_6058_; lean_object* v_y_6059_; lean_object* v_u_6060_; lean_object* v_Y_6061_; lean_object* v_D_6062_; lean_object* v_M_6063_; lean_object* v_L_6064_; lean_object* v_d_6065_; lean_object* v_Q_6066_; lean_object* v_q_6067_; lean_object* v_w_6068_; lean_object* v_W_6069_; lean_object* v_E_6070_; lean_object* v_e_6071_; lean_object* v_c_6072_; lean_object* v_F_6073_; lean_object* v_a_6074_; lean_object* v_b_6075_; lean_object* v_B_6076_; lean_object* v_h_6077_; lean_object* v_K_6078_; lean_object* v_k_6079_; lean_object* v_H_6080_; lean_object* v_m_6081_; lean_object* v_s_6082_; lean_object* v_S_6083_; lean_object* v_A_6084_; lean_object* v_n_6085_; lean_object* v_N_6086_; lean_object* v_V_6087_; lean_object* v_zabbrev_6088_; lean_object* v_v_6089_; lean_object* v_O_6090_; lean_object* v_X_6091_; lean_object* v_x_6092_; lean_object* v_Z_6093_; lean_object* v___x_6095_; uint8_t v_isShared_6096_; uint8_t v_isSharedCheck_6101_; 
v_G_6058_ = lean_ctor_get(v_date_4491_, 0);
v_y_6059_ = lean_ctor_get(v_date_4491_, 1);
v_u_6060_ = lean_ctor_get(v_date_4491_, 2);
v_Y_6061_ = lean_ctor_get(v_date_4491_, 3);
v_D_6062_ = lean_ctor_get(v_date_4491_, 4);
v_M_6063_ = lean_ctor_get(v_date_4491_, 5);
v_L_6064_ = lean_ctor_get(v_date_4491_, 6);
v_d_6065_ = lean_ctor_get(v_date_4491_, 7);
v_Q_6066_ = lean_ctor_get(v_date_4491_, 8);
v_q_6067_ = lean_ctor_get(v_date_4491_, 9);
v_w_6068_ = lean_ctor_get(v_date_4491_, 10);
v_W_6069_ = lean_ctor_get(v_date_4491_, 11);
v_E_6070_ = lean_ctor_get(v_date_4491_, 12);
v_e_6071_ = lean_ctor_get(v_date_4491_, 13);
v_c_6072_ = lean_ctor_get(v_date_4491_, 14);
v_F_6073_ = lean_ctor_get(v_date_4491_, 15);
v_a_6074_ = lean_ctor_get(v_date_4491_, 16);
v_b_6075_ = lean_ctor_get(v_date_4491_, 17);
v_B_6076_ = lean_ctor_get(v_date_4491_, 18);
v_h_6077_ = lean_ctor_get(v_date_4491_, 19);
v_K_6078_ = lean_ctor_get(v_date_4491_, 20);
v_k_6079_ = lean_ctor_get(v_date_4491_, 21);
v_H_6080_ = lean_ctor_get(v_date_4491_, 22);
v_m_6081_ = lean_ctor_get(v_date_4491_, 23);
v_s_6082_ = lean_ctor_get(v_date_4491_, 24);
v_S_6083_ = lean_ctor_get(v_date_4491_, 25);
v_A_6084_ = lean_ctor_get(v_date_4491_, 26);
v_n_6085_ = lean_ctor_get(v_date_4491_, 27);
v_N_6086_ = lean_ctor_get(v_date_4491_, 28);
v_V_6087_ = lean_ctor_get(v_date_4491_, 29);
v_zabbrev_6088_ = lean_ctor_get(v_date_4491_, 31);
v_v_6089_ = lean_ctor_get(v_date_4491_, 32);
v_O_6090_ = lean_ctor_get(v_date_4491_, 33);
v_X_6091_ = lean_ctor_get(v_date_4491_, 34);
v_x_6092_ = lean_ctor_get(v_date_4491_, 35);
v_Z_6093_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_6101_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_6101_ == 0)
{
lean_object* v_unused_6102_; 
v_unused_6102_ = lean_ctor_get(v_date_4491_, 30);
lean_dec(v_unused_6102_);
v___x_6095_ = v_date_4491_;
v_isShared_6096_ = v_isSharedCheck_6101_;
goto v_resetjp_6094_;
}
else
{
lean_inc(v_Z_6093_);
lean_inc(v_x_6092_);
lean_inc(v_X_6091_);
lean_inc(v_O_6090_);
lean_inc(v_v_6089_);
lean_inc(v_zabbrev_6088_);
lean_inc(v_V_6087_);
lean_inc(v_N_6086_);
lean_inc(v_n_6085_);
lean_inc(v_A_6084_);
lean_inc(v_S_6083_);
lean_inc(v_s_6082_);
lean_inc(v_m_6081_);
lean_inc(v_H_6080_);
lean_inc(v_k_6079_);
lean_inc(v_K_6078_);
lean_inc(v_h_6077_);
lean_inc(v_B_6076_);
lean_inc(v_b_6075_);
lean_inc(v_a_6074_);
lean_inc(v_F_6073_);
lean_inc(v_c_6072_);
lean_inc(v_e_6071_);
lean_inc(v_E_6070_);
lean_inc(v_W_6069_);
lean_inc(v_w_6068_);
lean_inc(v_q_6067_);
lean_inc(v_Q_6066_);
lean_inc(v_d_6065_);
lean_inc(v_L_6064_);
lean_inc(v_M_6063_);
lean_inc(v_D_6062_);
lean_inc(v_Y_6061_);
lean_inc(v_u_6060_);
lean_inc(v_y_6059_);
lean_inc(v_G_6058_);
lean_dec(v_date_4491_);
v___x_6095_ = lean_box(0);
v_isShared_6096_ = v_isSharedCheck_6101_;
goto v_resetjp_6094_;
}
v_resetjp_6094_:
{
lean_object* v___x_6097_; lean_object* v___x_6099_; 
v___x_6097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6097_, 0, v_data_4493_);
if (v_isShared_6096_ == 0)
{
lean_ctor_set(v___x_6095_, 30, v___x_6097_);
v___x_6099_ = v___x_6095_;
goto v_reusejp_6098_;
}
else
{
lean_object* v_reuseFailAlloc_6100_; 
v_reuseFailAlloc_6100_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6100_, 0, v_G_6058_);
lean_ctor_set(v_reuseFailAlloc_6100_, 1, v_y_6059_);
lean_ctor_set(v_reuseFailAlloc_6100_, 2, v_u_6060_);
lean_ctor_set(v_reuseFailAlloc_6100_, 3, v_Y_6061_);
lean_ctor_set(v_reuseFailAlloc_6100_, 4, v_D_6062_);
lean_ctor_set(v_reuseFailAlloc_6100_, 5, v_M_6063_);
lean_ctor_set(v_reuseFailAlloc_6100_, 6, v_L_6064_);
lean_ctor_set(v_reuseFailAlloc_6100_, 7, v_d_6065_);
lean_ctor_set(v_reuseFailAlloc_6100_, 8, v_Q_6066_);
lean_ctor_set(v_reuseFailAlloc_6100_, 9, v_q_6067_);
lean_ctor_set(v_reuseFailAlloc_6100_, 10, v_w_6068_);
lean_ctor_set(v_reuseFailAlloc_6100_, 11, v_W_6069_);
lean_ctor_set(v_reuseFailAlloc_6100_, 12, v_E_6070_);
lean_ctor_set(v_reuseFailAlloc_6100_, 13, v_e_6071_);
lean_ctor_set(v_reuseFailAlloc_6100_, 14, v_c_6072_);
lean_ctor_set(v_reuseFailAlloc_6100_, 15, v_F_6073_);
lean_ctor_set(v_reuseFailAlloc_6100_, 16, v_a_6074_);
lean_ctor_set(v_reuseFailAlloc_6100_, 17, v_b_6075_);
lean_ctor_set(v_reuseFailAlloc_6100_, 18, v_B_6076_);
lean_ctor_set(v_reuseFailAlloc_6100_, 19, v_h_6077_);
lean_ctor_set(v_reuseFailAlloc_6100_, 20, v_K_6078_);
lean_ctor_set(v_reuseFailAlloc_6100_, 21, v_k_6079_);
lean_ctor_set(v_reuseFailAlloc_6100_, 22, v_H_6080_);
lean_ctor_set(v_reuseFailAlloc_6100_, 23, v_m_6081_);
lean_ctor_set(v_reuseFailAlloc_6100_, 24, v_s_6082_);
lean_ctor_set(v_reuseFailAlloc_6100_, 25, v_S_6083_);
lean_ctor_set(v_reuseFailAlloc_6100_, 26, v_A_6084_);
lean_ctor_set(v_reuseFailAlloc_6100_, 27, v_n_6085_);
lean_ctor_set(v_reuseFailAlloc_6100_, 28, v_N_6086_);
lean_ctor_set(v_reuseFailAlloc_6100_, 29, v_V_6087_);
lean_ctor_set(v_reuseFailAlloc_6100_, 30, v___x_6097_);
lean_ctor_set(v_reuseFailAlloc_6100_, 31, v_zabbrev_6088_);
lean_ctor_set(v_reuseFailAlloc_6100_, 32, v_v_6089_);
lean_ctor_set(v_reuseFailAlloc_6100_, 33, v_O_6090_);
lean_ctor_set(v_reuseFailAlloc_6100_, 34, v_X_6091_);
lean_ctor_set(v_reuseFailAlloc_6100_, 35, v_x_6092_);
lean_ctor_set(v_reuseFailAlloc_6100_, 36, v_Z_6093_);
v___x_6099_ = v_reuseFailAlloc_6100_;
goto v_reusejp_6098_;
}
v_reusejp_6098_:
{
return v___x_6099_;
}
}
}
}
case 31:
{
lean_object* v_G_6103_; lean_object* v_y_6104_; lean_object* v_u_6105_; lean_object* v_Y_6106_; lean_object* v_D_6107_; lean_object* v_M_6108_; lean_object* v_L_6109_; lean_object* v_d_6110_; lean_object* v_Q_6111_; lean_object* v_q_6112_; lean_object* v_w_6113_; lean_object* v_W_6114_; lean_object* v_E_6115_; lean_object* v_e_6116_; lean_object* v_c_6117_; lean_object* v_F_6118_; lean_object* v_a_6119_; lean_object* v_b_6120_; lean_object* v_B_6121_; lean_object* v_h_6122_; lean_object* v_K_6123_; lean_object* v_k_6124_; lean_object* v_H_6125_; lean_object* v_m_6126_; lean_object* v_s_6127_; lean_object* v_S_6128_; lean_object* v_A_6129_; lean_object* v_n_6130_; lean_object* v_N_6131_; lean_object* v_V_6132_; lean_object* v_z_6133_; lean_object* v_zabbrev_6134_; lean_object* v_O_6135_; lean_object* v_X_6136_; lean_object* v_x_6137_; lean_object* v_Z_6138_; lean_object* v___x_6140_; uint8_t v_isShared_6141_; uint8_t v_isSharedCheck_6146_; 
lean_dec_ref_known(v_modifier_4492_, 0);
v_G_6103_ = lean_ctor_get(v_date_4491_, 0);
v_y_6104_ = lean_ctor_get(v_date_4491_, 1);
v_u_6105_ = lean_ctor_get(v_date_4491_, 2);
v_Y_6106_ = lean_ctor_get(v_date_4491_, 3);
v_D_6107_ = lean_ctor_get(v_date_4491_, 4);
v_M_6108_ = lean_ctor_get(v_date_4491_, 5);
v_L_6109_ = lean_ctor_get(v_date_4491_, 6);
v_d_6110_ = lean_ctor_get(v_date_4491_, 7);
v_Q_6111_ = lean_ctor_get(v_date_4491_, 8);
v_q_6112_ = lean_ctor_get(v_date_4491_, 9);
v_w_6113_ = lean_ctor_get(v_date_4491_, 10);
v_W_6114_ = lean_ctor_get(v_date_4491_, 11);
v_E_6115_ = lean_ctor_get(v_date_4491_, 12);
v_e_6116_ = lean_ctor_get(v_date_4491_, 13);
v_c_6117_ = lean_ctor_get(v_date_4491_, 14);
v_F_6118_ = lean_ctor_get(v_date_4491_, 15);
v_a_6119_ = lean_ctor_get(v_date_4491_, 16);
v_b_6120_ = lean_ctor_get(v_date_4491_, 17);
v_B_6121_ = lean_ctor_get(v_date_4491_, 18);
v_h_6122_ = lean_ctor_get(v_date_4491_, 19);
v_K_6123_ = lean_ctor_get(v_date_4491_, 20);
v_k_6124_ = lean_ctor_get(v_date_4491_, 21);
v_H_6125_ = lean_ctor_get(v_date_4491_, 22);
v_m_6126_ = lean_ctor_get(v_date_4491_, 23);
v_s_6127_ = lean_ctor_get(v_date_4491_, 24);
v_S_6128_ = lean_ctor_get(v_date_4491_, 25);
v_A_6129_ = lean_ctor_get(v_date_4491_, 26);
v_n_6130_ = lean_ctor_get(v_date_4491_, 27);
v_N_6131_ = lean_ctor_get(v_date_4491_, 28);
v_V_6132_ = lean_ctor_get(v_date_4491_, 29);
v_z_6133_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_6134_ = lean_ctor_get(v_date_4491_, 31);
v_O_6135_ = lean_ctor_get(v_date_4491_, 33);
v_X_6136_ = lean_ctor_get(v_date_4491_, 34);
v_x_6137_ = lean_ctor_get(v_date_4491_, 35);
v_Z_6138_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_6146_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_6146_ == 0)
{
lean_object* v_unused_6147_; 
v_unused_6147_ = lean_ctor_get(v_date_4491_, 32);
lean_dec(v_unused_6147_);
v___x_6140_ = v_date_4491_;
v_isShared_6141_ = v_isSharedCheck_6146_;
goto v_resetjp_6139_;
}
else
{
lean_inc(v_Z_6138_);
lean_inc(v_x_6137_);
lean_inc(v_X_6136_);
lean_inc(v_O_6135_);
lean_inc(v_zabbrev_6134_);
lean_inc(v_z_6133_);
lean_inc(v_V_6132_);
lean_inc(v_N_6131_);
lean_inc(v_n_6130_);
lean_inc(v_A_6129_);
lean_inc(v_S_6128_);
lean_inc(v_s_6127_);
lean_inc(v_m_6126_);
lean_inc(v_H_6125_);
lean_inc(v_k_6124_);
lean_inc(v_K_6123_);
lean_inc(v_h_6122_);
lean_inc(v_B_6121_);
lean_inc(v_b_6120_);
lean_inc(v_a_6119_);
lean_inc(v_F_6118_);
lean_inc(v_c_6117_);
lean_inc(v_e_6116_);
lean_inc(v_E_6115_);
lean_inc(v_W_6114_);
lean_inc(v_w_6113_);
lean_inc(v_q_6112_);
lean_inc(v_Q_6111_);
lean_inc(v_d_6110_);
lean_inc(v_L_6109_);
lean_inc(v_M_6108_);
lean_inc(v_D_6107_);
lean_inc(v_Y_6106_);
lean_inc(v_u_6105_);
lean_inc(v_y_6104_);
lean_inc(v_G_6103_);
lean_dec(v_date_4491_);
v___x_6140_ = lean_box(0);
v_isShared_6141_ = v_isSharedCheck_6146_;
goto v_resetjp_6139_;
}
v_resetjp_6139_:
{
lean_object* v___x_6142_; lean_object* v___x_6144_; 
v___x_6142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6142_, 0, v_data_4493_);
if (v_isShared_6141_ == 0)
{
lean_ctor_set(v___x_6140_, 32, v___x_6142_);
v___x_6144_ = v___x_6140_;
goto v_reusejp_6143_;
}
else
{
lean_object* v_reuseFailAlloc_6145_; 
v_reuseFailAlloc_6145_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6145_, 0, v_G_6103_);
lean_ctor_set(v_reuseFailAlloc_6145_, 1, v_y_6104_);
lean_ctor_set(v_reuseFailAlloc_6145_, 2, v_u_6105_);
lean_ctor_set(v_reuseFailAlloc_6145_, 3, v_Y_6106_);
lean_ctor_set(v_reuseFailAlloc_6145_, 4, v_D_6107_);
lean_ctor_set(v_reuseFailAlloc_6145_, 5, v_M_6108_);
lean_ctor_set(v_reuseFailAlloc_6145_, 6, v_L_6109_);
lean_ctor_set(v_reuseFailAlloc_6145_, 7, v_d_6110_);
lean_ctor_set(v_reuseFailAlloc_6145_, 8, v_Q_6111_);
lean_ctor_set(v_reuseFailAlloc_6145_, 9, v_q_6112_);
lean_ctor_set(v_reuseFailAlloc_6145_, 10, v_w_6113_);
lean_ctor_set(v_reuseFailAlloc_6145_, 11, v_W_6114_);
lean_ctor_set(v_reuseFailAlloc_6145_, 12, v_E_6115_);
lean_ctor_set(v_reuseFailAlloc_6145_, 13, v_e_6116_);
lean_ctor_set(v_reuseFailAlloc_6145_, 14, v_c_6117_);
lean_ctor_set(v_reuseFailAlloc_6145_, 15, v_F_6118_);
lean_ctor_set(v_reuseFailAlloc_6145_, 16, v_a_6119_);
lean_ctor_set(v_reuseFailAlloc_6145_, 17, v_b_6120_);
lean_ctor_set(v_reuseFailAlloc_6145_, 18, v_B_6121_);
lean_ctor_set(v_reuseFailAlloc_6145_, 19, v_h_6122_);
lean_ctor_set(v_reuseFailAlloc_6145_, 20, v_K_6123_);
lean_ctor_set(v_reuseFailAlloc_6145_, 21, v_k_6124_);
lean_ctor_set(v_reuseFailAlloc_6145_, 22, v_H_6125_);
lean_ctor_set(v_reuseFailAlloc_6145_, 23, v_m_6126_);
lean_ctor_set(v_reuseFailAlloc_6145_, 24, v_s_6127_);
lean_ctor_set(v_reuseFailAlloc_6145_, 25, v_S_6128_);
lean_ctor_set(v_reuseFailAlloc_6145_, 26, v_A_6129_);
lean_ctor_set(v_reuseFailAlloc_6145_, 27, v_n_6130_);
lean_ctor_set(v_reuseFailAlloc_6145_, 28, v_N_6131_);
lean_ctor_set(v_reuseFailAlloc_6145_, 29, v_V_6132_);
lean_ctor_set(v_reuseFailAlloc_6145_, 30, v_z_6133_);
lean_ctor_set(v_reuseFailAlloc_6145_, 31, v_zabbrev_6134_);
lean_ctor_set(v_reuseFailAlloc_6145_, 32, v___x_6142_);
lean_ctor_set(v_reuseFailAlloc_6145_, 33, v_O_6135_);
lean_ctor_set(v_reuseFailAlloc_6145_, 34, v_X_6136_);
lean_ctor_set(v_reuseFailAlloc_6145_, 35, v_x_6137_);
lean_ctor_set(v_reuseFailAlloc_6145_, 36, v_Z_6138_);
v___x_6144_ = v_reuseFailAlloc_6145_;
goto v_reusejp_6143_;
}
v_reusejp_6143_:
{
return v___x_6144_;
}
}
}
case 32:
{
lean_object* v_G_6148_; lean_object* v_y_6149_; lean_object* v_u_6150_; lean_object* v_Y_6151_; lean_object* v_D_6152_; lean_object* v_M_6153_; lean_object* v_L_6154_; lean_object* v_d_6155_; lean_object* v_Q_6156_; lean_object* v_q_6157_; lean_object* v_w_6158_; lean_object* v_W_6159_; lean_object* v_E_6160_; lean_object* v_e_6161_; lean_object* v_c_6162_; lean_object* v_F_6163_; lean_object* v_a_6164_; lean_object* v_b_6165_; lean_object* v_B_6166_; lean_object* v_h_6167_; lean_object* v_K_6168_; lean_object* v_k_6169_; lean_object* v_H_6170_; lean_object* v_m_6171_; lean_object* v_s_6172_; lean_object* v_S_6173_; lean_object* v_A_6174_; lean_object* v_n_6175_; lean_object* v_N_6176_; lean_object* v_V_6177_; lean_object* v_z_6178_; lean_object* v_zabbrev_6179_; lean_object* v_v_6180_; lean_object* v_X_6181_; lean_object* v_x_6182_; lean_object* v_Z_6183_; lean_object* v___x_6185_; uint8_t v_isShared_6186_; uint8_t v_isSharedCheck_6191_; 
lean_dec_ref_known(v_modifier_4492_, 0);
v_G_6148_ = lean_ctor_get(v_date_4491_, 0);
v_y_6149_ = lean_ctor_get(v_date_4491_, 1);
v_u_6150_ = lean_ctor_get(v_date_4491_, 2);
v_Y_6151_ = lean_ctor_get(v_date_4491_, 3);
v_D_6152_ = lean_ctor_get(v_date_4491_, 4);
v_M_6153_ = lean_ctor_get(v_date_4491_, 5);
v_L_6154_ = lean_ctor_get(v_date_4491_, 6);
v_d_6155_ = lean_ctor_get(v_date_4491_, 7);
v_Q_6156_ = lean_ctor_get(v_date_4491_, 8);
v_q_6157_ = lean_ctor_get(v_date_4491_, 9);
v_w_6158_ = lean_ctor_get(v_date_4491_, 10);
v_W_6159_ = lean_ctor_get(v_date_4491_, 11);
v_E_6160_ = lean_ctor_get(v_date_4491_, 12);
v_e_6161_ = lean_ctor_get(v_date_4491_, 13);
v_c_6162_ = lean_ctor_get(v_date_4491_, 14);
v_F_6163_ = lean_ctor_get(v_date_4491_, 15);
v_a_6164_ = lean_ctor_get(v_date_4491_, 16);
v_b_6165_ = lean_ctor_get(v_date_4491_, 17);
v_B_6166_ = lean_ctor_get(v_date_4491_, 18);
v_h_6167_ = lean_ctor_get(v_date_4491_, 19);
v_K_6168_ = lean_ctor_get(v_date_4491_, 20);
v_k_6169_ = lean_ctor_get(v_date_4491_, 21);
v_H_6170_ = lean_ctor_get(v_date_4491_, 22);
v_m_6171_ = lean_ctor_get(v_date_4491_, 23);
v_s_6172_ = lean_ctor_get(v_date_4491_, 24);
v_S_6173_ = lean_ctor_get(v_date_4491_, 25);
v_A_6174_ = lean_ctor_get(v_date_4491_, 26);
v_n_6175_ = lean_ctor_get(v_date_4491_, 27);
v_N_6176_ = lean_ctor_get(v_date_4491_, 28);
v_V_6177_ = lean_ctor_get(v_date_4491_, 29);
v_z_6178_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_6179_ = lean_ctor_get(v_date_4491_, 31);
v_v_6180_ = lean_ctor_get(v_date_4491_, 32);
v_X_6181_ = lean_ctor_get(v_date_4491_, 34);
v_x_6182_ = lean_ctor_get(v_date_4491_, 35);
v_Z_6183_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_6191_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_6191_ == 0)
{
lean_object* v_unused_6192_; 
v_unused_6192_ = lean_ctor_get(v_date_4491_, 33);
lean_dec(v_unused_6192_);
v___x_6185_ = v_date_4491_;
v_isShared_6186_ = v_isSharedCheck_6191_;
goto v_resetjp_6184_;
}
else
{
lean_inc(v_Z_6183_);
lean_inc(v_x_6182_);
lean_inc(v_X_6181_);
lean_inc(v_v_6180_);
lean_inc(v_zabbrev_6179_);
lean_inc(v_z_6178_);
lean_inc(v_V_6177_);
lean_inc(v_N_6176_);
lean_inc(v_n_6175_);
lean_inc(v_A_6174_);
lean_inc(v_S_6173_);
lean_inc(v_s_6172_);
lean_inc(v_m_6171_);
lean_inc(v_H_6170_);
lean_inc(v_k_6169_);
lean_inc(v_K_6168_);
lean_inc(v_h_6167_);
lean_inc(v_B_6166_);
lean_inc(v_b_6165_);
lean_inc(v_a_6164_);
lean_inc(v_F_6163_);
lean_inc(v_c_6162_);
lean_inc(v_e_6161_);
lean_inc(v_E_6160_);
lean_inc(v_W_6159_);
lean_inc(v_w_6158_);
lean_inc(v_q_6157_);
lean_inc(v_Q_6156_);
lean_inc(v_d_6155_);
lean_inc(v_L_6154_);
lean_inc(v_M_6153_);
lean_inc(v_D_6152_);
lean_inc(v_Y_6151_);
lean_inc(v_u_6150_);
lean_inc(v_y_6149_);
lean_inc(v_G_6148_);
lean_dec(v_date_4491_);
v___x_6185_ = lean_box(0);
v_isShared_6186_ = v_isSharedCheck_6191_;
goto v_resetjp_6184_;
}
v_resetjp_6184_:
{
lean_object* v___x_6187_; lean_object* v___x_6189_; 
v___x_6187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6187_, 0, v_data_4493_);
if (v_isShared_6186_ == 0)
{
lean_ctor_set(v___x_6185_, 33, v___x_6187_);
v___x_6189_ = v___x_6185_;
goto v_reusejp_6188_;
}
else
{
lean_object* v_reuseFailAlloc_6190_; 
v_reuseFailAlloc_6190_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6190_, 0, v_G_6148_);
lean_ctor_set(v_reuseFailAlloc_6190_, 1, v_y_6149_);
lean_ctor_set(v_reuseFailAlloc_6190_, 2, v_u_6150_);
lean_ctor_set(v_reuseFailAlloc_6190_, 3, v_Y_6151_);
lean_ctor_set(v_reuseFailAlloc_6190_, 4, v_D_6152_);
lean_ctor_set(v_reuseFailAlloc_6190_, 5, v_M_6153_);
lean_ctor_set(v_reuseFailAlloc_6190_, 6, v_L_6154_);
lean_ctor_set(v_reuseFailAlloc_6190_, 7, v_d_6155_);
lean_ctor_set(v_reuseFailAlloc_6190_, 8, v_Q_6156_);
lean_ctor_set(v_reuseFailAlloc_6190_, 9, v_q_6157_);
lean_ctor_set(v_reuseFailAlloc_6190_, 10, v_w_6158_);
lean_ctor_set(v_reuseFailAlloc_6190_, 11, v_W_6159_);
lean_ctor_set(v_reuseFailAlloc_6190_, 12, v_E_6160_);
lean_ctor_set(v_reuseFailAlloc_6190_, 13, v_e_6161_);
lean_ctor_set(v_reuseFailAlloc_6190_, 14, v_c_6162_);
lean_ctor_set(v_reuseFailAlloc_6190_, 15, v_F_6163_);
lean_ctor_set(v_reuseFailAlloc_6190_, 16, v_a_6164_);
lean_ctor_set(v_reuseFailAlloc_6190_, 17, v_b_6165_);
lean_ctor_set(v_reuseFailAlloc_6190_, 18, v_B_6166_);
lean_ctor_set(v_reuseFailAlloc_6190_, 19, v_h_6167_);
lean_ctor_set(v_reuseFailAlloc_6190_, 20, v_K_6168_);
lean_ctor_set(v_reuseFailAlloc_6190_, 21, v_k_6169_);
lean_ctor_set(v_reuseFailAlloc_6190_, 22, v_H_6170_);
lean_ctor_set(v_reuseFailAlloc_6190_, 23, v_m_6171_);
lean_ctor_set(v_reuseFailAlloc_6190_, 24, v_s_6172_);
lean_ctor_set(v_reuseFailAlloc_6190_, 25, v_S_6173_);
lean_ctor_set(v_reuseFailAlloc_6190_, 26, v_A_6174_);
lean_ctor_set(v_reuseFailAlloc_6190_, 27, v_n_6175_);
lean_ctor_set(v_reuseFailAlloc_6190_, 28, v_N_6176_);
lean_ctor_set(v_reuseFailAlloc_6190_, 29, v_V_6177_);
lean_ctor_set(v_reuseFailAlloc_6190_, 30, v_z_6178_);
lean_ctor_set(v_reuseFailAlloc_6190_, 31, v_zabbrev_6179_);
lean_ctor_set(v_reuseFailAlloc_6190_, 32, v_v_6180_);
lean_ctor_set(v_reuseFailAlloc_6190_, 33, v___x_6187_);
lean_ctor_set(v_reuseFailAlloc_6190_, 34, v_X_6181_);
lean_ctor_set(v_reuseFailAlloc_6190_, 35, v_x_6182_);
lean_ctor_set(v_reuseFailAlloc_6190_, 36, v_Z_6183_);
v___x_6189_ = v_reuseFailAlloc_6190_;
goto v_reusejp_6188_;
}
v_reusejp_6188_:
{
return v___x_6189_;
}
}
}
case 33:
{
lean_object* v_G_6193_; lean_object* v_y_6194_; lean_object* v_u_6195_; lean_object* v_Y_6196_; lean_object* v_D_6197_; lean_object* v_M_6198_; lean_object* v_L_6199_; lean_object* v_d_6200_; lean_object* v_Q_6201_; lean_object* v_q_6202_; lean_object* v_w_6203_; lean_object* v_W_6204_; lean_object* v_E_6205_; lean_object* v_e_6206_; lean_object* v_c_6207_; lean_object* v_F_6208_; lean_object* v_a_6209_; lean_object* v_b_6210_; lean_object* v_B_6211_; lean_object* v_h_6212_; lean_object* v_K_6213_; lean_object* v_k_6214_; lean_object* v_H_6215_; lean_object* v_m_6216_; lean_object* v_s_6217_; lean_object* v_S_6218_; lean_object* v_A_6219_; lean_object* v_n_6220_; lean_object* v_N_6221_; lean_object* v_V_6222_; lean_object* v_z_6223_; lean_object* v_zabbrev_6224_; lean_object* v_v_6225_; lean_object* v_O_6226_; lean_object* v_x_6227_; lean_object* v_Z_6228_; lean_object* v___x_6230_; uint8_t v_isShared_6231_; uint8_t v_isSharedCheck_6236_; 
lean_dec_ref_known(v_modifier_4492_, 0);
v_G_6193_ = lean_ctor_get(v_date_4491_, 0);
v_y_6194_ = lean_ctor_get(v_date_4491_, 1);
v_u_6195_ = lean_ctor_get(v_date_4491_, 2);
v_Y_6196_ = lean_ctor_get(v_date_4491_, 3);
v_D_6197_ = lean_ctor_get(v_date_4491_, 4);
v_M_6198_ = lean_ctor_get(v_date_4491_, 5);
v_L_6199_ = lean_ctor_get(v_date_4491_, 6);
v_d_6200_ = lean_ctor_get(v_date_4491_, 7);
v_Q_6201_ = lean_ctor_get(v_date_4491_, 8);
v_q_6202_ = lean_ctor_get(v_date_4491_, 9);
v_w_6203_ = lean_ctor_get(v_date_4491_, 10);
v_W_6204_ = lean_ctor_get(v_date_4491_, 11);
v_E_6205_ = lean_ctor_get(v_date_4491_, 12);
v_e_6206_ = lean_ctor_get(v_date_4491_, 13);
v_c_6207_ = lean_ctor_get(v_date_4491_, 14);
v_F_6208_ = lean_ctor_get(v_date_4491_, 15);
v_a_6209_ = lean_ctor_get(v_date_4491_, 16);
v_b_6210_ = lean_ctor_get(v_date_4491_, 17);
v_B_6211_ = lean_ctor_get(v_date_4491_, 18);
v_h_6212_ = lean_ctor_get(v_date_4491_, 19);
v_K_6213_ = lean_ctor_get(v_date_4491_, 20);
v_k_6214_ = lean_ctor_get(v_date_4491_, 21);
v_H_6215_ = lean_ctor_get(v_date_4491_, 22);
v_m_6216_ = lean_ctor_get(v_date_4491_, 23);
v_s_6217_ = lean_ctor_get(v_date_4491_, 24);
v_S_6218_ = lean_ctor_get(v_date_4491_, 25);
v_A_6219_ = lean_ctor_get(v_date_4491_, 26);
v_n_6220_ = lean_ctor_get(v_date_4491_, 27);
v_N_6221_ = lean_ctor_get(v_date_4491_, 28);
v_V_6222_ = lean_ctor_get(v_date_4491_, 29);
v_z_6223_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_6224_ = lean_ctor_get(v_date_4491_, 31);
v_v_6225_ = lean_ctor_get(v_date_4491_, 32);
v_O_6226_ = lean_ctor_get(v_date_4491_, 33);
v_x_6227_ = lean_ctor_get(v_date_4491_, 35);
v_Z_6228_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_6236_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_6236_ == 0)
{
lean_object* v_unused_6237_; 
v_unused_6237_ = lean_ctor_get(v_date_4491_, 34);
lean_dec(v_unused_6237_);
v___x_6230_ = v_date_4491_;
v_isShared_6231_ = v_isSharedCheck_6236_;
goto v_resetjp_6229_;
}
else
{
lean_inc(v_Z_6228_);
lean_inc(v_x_6227_);
lean_inc(v_O_6226_);
lean_inc(v_v_6225_);
lean_inc(v_zabbrev_6224_);
lean_inc(v_z_6223_);
lean_inc(v_V_6222_);
lean_inc(v_N_6221_);
lean_inc(v_n_6220_);
lean_inc(v_A_6219_);
lean_inc(v_S_6218_);
lean_inc(v_s_6217_);
lean_inc(v_m_6216_);
lean_inc(v_H_6215_);
lean_inc(v_k_6214_);
lean_inc(v_K_6213_);
lean_inc(v_h_6212_);
lean_inc(v_B_6211_);
lean_inc(v_b_6210_);
lean_inc(v_a_6209_);
lean_inc(v_F_6208_);
lean_inc(v_c_6207_);
lean_inc(v_e_6206_);
lean_inc(v_E_6205_);
lean_inc(v_W_6204_);
lean_inc(v_w_6203_);
lean_inc(v_q_6202_);
lean_inc(v_Q_6201_);
lean_inc(v_d_6200_);
lean_inc(v_L_6199_);
lean_inc(v_M_6198_);
lean_inc(v_D_6197_);
lean_inc(v_Y_6196_);
lean_inc(v_u_6195_);
lean_inc(v_y_6194_);
lean_inc(v_G_6193_);
lean_dec(v_date_4491_);
v___x_6230_ = lean_box(0);
v_isShared_6231_ = v_isSharedCheck_6236_;
goto v_resetjp_6229_;
}
v_resetjp_6229_:
{
lean_object* v___x_6232_; lean_object* v___x_6234_; 
v___x_6232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6232_, 0, v_data_4493_);
if (v_isShared_6231_ == 0)
{
lean_ctor_set(v___x_6230_, 34, v___x_6232_);
v___x_6234_ = v___x_6230_;
goto v_reusejp_6233_;
}
else
{
lean_object* v_reuseFailAlloc_6235_; 
v_reuseFailAlloc_6235_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6235_, 0, v_G_6193_);
lean_ctor_set(v_reuseFailAlloc_6235_, 1, v_y_6194_);
lean_ctor_set(v_reuseFailAlloc_6235_, 2, v_u_6195_);
lean_ctor_set(v_reuseFailAlloc_6235_, 3, v_Y_6196_);
lean_ctor_set(v_reuseFailAlloc_6235_, 4, v_D_6197_);
lean_ctor_set(v_reuseFailAlloc_6235_, 5, v_M_6198_);
lean_ctor_set(v_reuseFailAlloc_6235_, 6, v_L_6199_);
lean_ctor_set(v_reuseFailAlloc_6235_, 7, v_d_6200_);
lean_ctor_set(v_reuseFailAlloc_6235_, 8, v_Q_6201_);
lean_ctor_set(v_reuseFailAlloc_6235_, 9, v_q_6202_);
lean_ctor_set(v_reuseFailAlloc_6235_, 10, v_w_6203_);
lean_ctor_set(v_reuseFailAlloc_6235_, 11, v_W_6204_);
lean_ctor_set(v_reuseFailAlloc_6235_, 12, v_E_6205_);
lean_ctor_set(v_reuseFailAlloc_6235_, 13, v_e_6206_);
lean_ctor_set(v_reuseFailAlloc_6235_, 14, v_c_6207_);
lean_ctor_set(v_reuseFailAlloc_6235_, 15, v_F_6208_);
lean_ctor_set(v_reuseFailAlloc_6235_, 16, v_a_6209_);
lean_ctor_set(v_reuseFailAlloc_6235_, 17, v_b_6210_);
lean_ctor_set(v_reuseFailAlloc_6235_, 18, v_B_6211_);
lean_ctor_set(v_reuseFailAlloc_6235_, 19, v_h_6212_);
lean_ctor_set(v_reuseFailAlloc_6235_, 20, v_K_6213_);
lean_ctor_set(v_reuseFailAlloc_6235_, 21, v_k_6214_);
lean_ctor_set(v_reuseFailAlloc_6235_, 22, v_H_6215_);
lean_ctor_set(v_reuseFailAlloc_6235_, 23, v_m_6216_);
lean_ctor_set(v_reuseFailAlloc_6235_, 24, v_s_6217_);
lean_ctor_set(v_reuseFailAlloc_6235_, 25, v_S_6218_);
lean_ctor_set(v_reuseFailAlloc_6235_, 26, v_A_6219_);
lean_ctor_set(v_reuseFailAlloc_6235_, 27, v_n_6220_);
lean_ctor_set(v_reuseFailAlloc_6235_, 28, v_N_6221_);
lean_ctor_set(v_reuseFailAlloc_6235_, 29, v_V_6222_);
lean_ctor_set(v_reuseFailAlloc_6235_, 30, v_z_6223_);
lean_ctor_set(v_reuseFailAlloc_6235_, 31, v_zabbrev_6224_);
lean_ctor_set(v_reuseFailAlloc_6235_, 32, v_v_6225_);
lean_ctor_set(v_reuseFailAlloc_6235_, 33, v_O_6226_);
lean_ctor_set(v_reuseFailAlloc_6235_, 34, v___x_6232_);
lean_ctor_set(v_reuseFailAlloc_6235_, 35, v_x_6227_);
lean_ctor_set(v_reuseFailAlloc_6235_, 36, v_Z_6228_);
v___x_6234_ = v_reuseFailAlloc_6235_;
goto v_reusejp_6233_;
}
v_reusejp_6233_:
{
return v___x_6234_;
}
}
}
case 34:
{
lean_object* v_G_6238_; lean_object* v_y_6239_; lean_object* v_u_6240_; lean_object* v_Y_6241_; lean_object* v_D_6242_; lean_object* v_M_6243_; lean_object* v_L_6244_; lean_object* v_d_6245_; lean_object* v_Q_6246_; lean_object* v_q_6247_; lean_object* v_w_6248_; lean_object* v_W_6249_; lean_object* v_E_6250_; lean_object* v_e_6251_; lean_object* v_c_6252_; lean_object* v_F_6253_; lean_object* v_a_6254_; lean_object* v_b_6255_; lean_object* v_B_6256_; lean_object* v_h_6257_; lean_object* v_K_6258_; lean_object* v_k_6259_; lean_object* v_H_6260_; lean_object* v_m_6261_; lean_object* v_s_6262_; lean_object* v_S_6263_; lean_object* v_A_6264_; lean_object* v_n_6265_; lean_object* v_N_6266_; lean_object* v_V_6267_; lean_object* v_z_6268_; lean_object* v_zabbrev_6269_; lean_object* v_v_6270_; lean_object* v_O_6271_; lean_object* v_X_6272_; lean_object* v_Z_6273_; lean_object* v___x_6275_; uint8_t v_isShared_6276_; uint8_t v_isSharedCheck_6281_; 
lean_dec_ref_known(v_modifier_4492_, 0);
v_G_6238_ = lean_ctor_get(v_date_4491_, 0);
v_y_6239_ = lean_ctor_get(v_date_4491_, 1);
v_u_6240_ = lean_ctor_get(v_date_4491_, 2);
v_Y_6241_ = lean_ctor_get(v_date_4491_, 3);
v_D_6242_ = lean_ctor_get(v_date_4491_, 4);
v_M_6243_ = lean_ctor_get(v_date_4491_, 5);
v_L_6244_ = lean_ctor_get(v_date_4491_, 6);
v_d_6245_ = lean_ctor_get(v_date_4491_, 7);
v_Q_6246_ = lean_ctor_get(v_date_4491_, 8);
v_q_6247_ = lean_ctor_get(v_date_4491_, 9);
v_w_6248_ = lean_ctor_get(v_date_4491_, 10);
v_W_6249_ = lean_ctor_get(v_date_4491_, 11);
v_E_6250_ = lean_ctor_get(v_date_4491_, 12);
v_e_6251_ = lean_ctor_get(v_date_4491_, 13);
v_c_6252_ = lean_ctor_get(v_date_4491_, 14);
v_F_6253_ = lean_ctor_get(v_date_4491_, 15);
v_a_6254_ = lean_ctor_get(v_date_4491_, 16);
v_b_6255_ = lean_ctor_get(v_date_4491_, 17);
v_B_6256_ = lean_ctor_get(v_date_4491_, 18);
v_h_6257_ = lean_ctor_get(v_date_4491_, 19);
v_K_6258_ = lean_ctor_get(v_date_4491_, 20);
v_k_6259_ = lean_ctor_get(v_date_4491_, 21);
v_H_6260_ = lean_ctor_get(v_date_4491_, 22);
v_m_6261_ = lean_ctor_get(v_date_4491_, 23);
v_s_6262_ = lean_ctor_get(v_date_4491_, 24);
v_S_6263_ = lean_ctor_get(v_date_4491_, 25);
v_A_6264_ = lean_ctor_get(v_date_4491_, 26);
v_n_6265_ = lean_ctor_get(v_date_4491_, 27);
v_N_6266_ = lean_ctor_get(v_date_4491_, 28);
v_V_6267_ = lean_ctor_get(v_date_4491_, 29);
v_z_6268_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_6269_ = lean_ctor_get(v_date_4491_, 31);
v_v_6270_ = lean_ctor_get(v_date_4491_, 32);
v_O_6271_ = lean_ctor_get(v_date_4491_, 33);
v_X_6272_ = lean_ctor_get(v_date_4491_, 34);
v_Z_6273_ = lean_ctor_get(v_date_4491_, 36);
v_isSharedCheck_6281_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_6281_ == 0)
{
lean_object* v_unused_6282_; 
v_unused_6282_ = lean_ctor_get(v_date_4491_, 35);
lean_dec(v_unused_6282_);
v___x_6275_ = v_date_4491_;
v_isShared_6276_ = v_isSharedCheck_6281_;
goto v_resetjp_6274_;
}
else
{
lean_inc(v_Z_6273_);
lean_inc(v_X_6272_);
lean_inc(v_O_6271_);
lean_inc(v_v_6270_);
lean_inc(v_zabbrev_6269_);
lean_inc(v_z_6268_);
lean_inc(v_V_6267_);
lean_inc(v_N_6266_);
lean_inc(v_n_6265_);
lean_inc(v_A_6264_);
lean_inc(v_S_6263_);
lean_inc(v_s_6262_);
lean_inc(v_m_6261_);
lean_inc(v_H_6260_);
lean_inc(v_k_6259_);
lean_inc(v_K_6258_);
lean_inc(v_h_6257_);
lean_inc(v_B_6256_);
lean_inc(v_b_6255_);
lean_inc(v_a_6254_);
lean_inc(v_F_6253_);
lean_inc(v_c_6252_);
lean_inc(v_e_6251_);
lean_inc(v_E_6250_);
lean_inc(v_W_6249_);
lean_inc(v_w_6248_);
lean_inc(v_q_6247_);
lean_inc(v_Q_6246_);
lean_inc(v_d_6245_);
lean_inc(v_L_6244_);
lean_inc(v_M_6243_);
lean_inc(v_D_6242_);
lean_inc(v_Y_6241_);
lean_inc(v_u_6240_);
lean_inc(v_y_6239_);
lean_inc(v_G_6238_);
lean_dec(v_date_4491_);
v___x_6275_ = lean_box(0);
v_isShared_6276_ = v_isSharedCheck_6281_;
goto v_resetjp_6274_;
}
v_resetjp_6274_:
{
lean_object* v___x_6277_; lean_object* v___x_6279_; 
v___x_6277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6277_, 0, v_data_4493_);
if (v_isShared_6276_ == 0)
{
lean_ctor_set(v___x_6275_, 35, v___x_6277_);
v___x_6279_ = v___x_6275_;
goto v_reusejp_6278_;
}
else
{
lean_object* v_reuseFailAlloc_6280_; 
v_reuseFailAlloc_6280_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6280_, 0, v_G_6238_);
lean_ctor_set(v_reuseFailAlloc_6280_, 1, v_y_6239_);
lean_ctor_set(v_reuseFailAlloc_6280_, 2, v_u_6240_);
lean_ctor_set(v_reuseFailAlloc_6280_, 3, v_Y_6241_);
lean_ctor_set(v_reuseFailAlloc_6280_, 4, v_D_6242_);
lean_ctor_set(v_reuseFailAlloc_6280_, 5, v_M_6243_);
lean_ctor_set(v_reuseFailAlloc_6280_, 6, v_L_6244_);
lean_ctor_set(v_reuseFailAlloc_6280_, 7, v_d_6245_);
lean_ctor_set(v_reuseFailAlloc_6280_, 8, v_Q_6246_);
lean_ctor_set(v_reuseFailAlloc_6280_, 9, v_q_6247_);
lean_ctor_set(v_reuseFailAlloc_6280_, 10, v_w_6248_);
lean_ctor_set(v_reuseFailAlloc_6280_, 11, v_W_6249_);
lean_ctor_set(v_reuseFailAlloc_6280_, 12, v_E_6250_);
lean_ctor_set(v_reuseFailAlloc_6280_, 13, v_e_6251_);
lean_ctor_set(v_reuseFailAlloc_6280_, 14, v_c_6252_);
lean_ctor_set(v_reuseFailAlloc_6280_, 15, v_F_6253_);
lean_ctor_set(v_reuseFailAlloc_6280_, 16, v_a_6254_);
lean_ctor_set(v_reuseFailAlloc_6280_, 17, v_b_6255_);
lean_ctor_set(v_reuseFailAlloc_6280_, 18, v_B_6256_);
lean_ctor_set(v_reuseFailAlloc_6280_, 19, v_h_6257_);
lean_ctor_set(v_reuseFailAlloc_6280_, 20, v_K_6258_);
lean_ctor_set(v_reuseFailAlloc_6280_, 21, v_k_6259_);
lean_ctor_set(v_reuseFailAlloc_6280_, 22, v_H_6260_);
lean_ctor_set(v_reuseFailAlloc_6280_, 23, v_m_6261_);
lean_ctor_set(v_reuseFailAlloc_6280_, 24, v_s_6262_);
lean_ctor_set(v_reuseFailAlloc_6280_, 25, v_S_6263_);
lean_ctor_set(v_reuseFailAlloc_6280_, 26, v_A_6264_);
lean_ctor_set(v_reuseFailAlloc_6280_, 27, v_n_6265_);
lean_ctor_set(v_reuseFailAlloc_6280_, 28, v_N_6266_);
lean_ctor_set(v_reuseFailAlloc_6280_, 29, v_V_6267_);
lean_ctor_set(v_reuseFailAlloc_6280_, 30, v_z_6268_);
lean_ctor_set(v_reuseFailAlloc_6280_, 31, v_zabbrev_6269_);
lean_ctor_set(v_reuseFailAlloc_6280_, 32, v_v_6270_);
lean_ctor_set(v_reuseFailAlloc_6280_, 33, v_O_6271_);
lean_ctor_set(v_reuseFailAlloc_6280_, 34, v_X_6272_);
lean_ctor_set(v_reuseFailAlloc_6280_, 35, v___x_6277_);
lean_ctor_set(v_reuseFailAlloc_6280_, 36, v_Z_6273_);
v___x_6279_ = v_reuseFailAlloc_6280_;
goto v_reusejp_6278_;
}
v_reusejp_6278_:
{
return v___x_6279_;
}
}
}
default: 
{
lean_object* v_G_6283_; lean_object* v_y_6284_; lean_object* v_u_6285_; lean_object* v_Y_6286_; lean_object* v_D_6287_; lean_object* v_M_6288_; lean_object* v_L_6289_; lean_object* v_d_6290_; lean_object* v_Q_6291_; lean_object* v_q_6292_; lean_object* v_w_6293_; lean_object* v_W_6294_; lean_object* v_E_6295_; lean_object* v_e_6296_; lean_object* v_c_6297_; lean_object* v_F_6298_; lean_object* v_a_6299_; lean_object* v_b_6300_; lean_object* v_B_6301_; lean_object* v_h_6302_; lean_object* v_K_6303_; lean_object* v_k_6304_; lean_object* v_H_6305_; lean_object* v_m_6306_; lean_object* v_s_6307_; lean_object* v_S_6308_; lean_object* v_A_6309_; lean_object* v_n_6310_; lean_object* v_N_6311_; lean_object* v_V_6312_; lean_object* v_z_6313_; lean_object* v_zabbrev_6314_; lean_object* v_v_6315_; lean_object* v_O_6316_; lean_object* v_X_6317_; lean_object* v_x_6318_; lean_object* v___x_6320_; uint8_t v_isShared_6321_; uint8_t v_isSharedCheck_6326_; 
lean_dec_ref_known(v_modifier_4492_, 0);
v_G_6283_ = lean_ctor_get(v_date_4491_, 0);
v_y_6284_ = lean_ctor_get(v_date_4491_, 1);
v_u_6285_ = lean_ctor_get(v_date_4491_, 2);
v_Y_6286_ = lean_ctor_get(v_date_4491_, 3);
v_D_6287_ = lean_ctor_get(v_date_4491_, 4);
v_M_6288_ = lean_ctor_get(v_date_4491_, 5);
v_L_6289_ = lean_ctor_get(v_date_4491_, 6);
v_d_6290_ = lean_ctor_get(v_date_4491_, 7);
v_Q_6291_ = lean_ctor_get(v_date_4491_, 8);
v_q_6292_ = lean_ctor_get(v_date_4491_, 9);
v_w_6293_ = lean_ctor_get(v_date_4491_, 10);
v_W_6294_ = lean_ctor_get(v_date_4491_, 11);
v_E_6295_ = lean_ctor_get(v_date_4491_, 12);
v_e_6296_ = lean_ctor_get(v_date_4491_, 13);
v_c_6297_ = lean_ctor_get(v_date_4491_, 14);
v_F_6298_ = lean_ctor_get(v_date_4491_, 15);
v_a_6299_ = lean_ctor_get(v_date_4491_, 16);
v_b_6300_ = lean_ctor_get(v_date_4491_, 17);
v_B_6301_ = lean_ctor_get(v_date_4491_, 18);
v_h_6302_ = lean_ctor_get(v_date_4491_, 19);
v_K_6303_ = lean_ctor_get(v_date_4491_, 20);
v_k_6304_ = lean_ctor_get(v_date_4491_, 21);
v_H_6305_ = lean_ctor_get(v_date_4491_, 22);
v_m_6306_ = lean_ctor_get(v_date_4491_, 23);
v_s_6307_ = lean_ctor_get(v_date_4491_, 24);
v_S_6308_ = lean_ctor_get(v_date_4491_, 25);
v_A_6309_ = lean_ctor_get(v_date_4491_, 26);
v_n_6310_ = lean_ctor_get(v_date_4491_, 27);
v_N_6311_ = lean_ctor_get(v_date_4491_, 28);
v_V_6312_ = lean_ctor_get(v_date_4491_, 29);
v_z_6313_ = lean_ctor_get(v_date_4491_, 30);
v_zabbrev_6314_ = lean_ctor_get(v_date_4491_, 31);
v_v_6315_ = lean_ctor_get(v_date_4491_, 32);
v_O_6316_ = lean_ctor_get(v_date_4491_, 33);
v_X_6317_ = lean_ctor_get(v_date_4491_, 34);
v_x_6318_ = lean_ctor_get(v_date_4491_, 35);
v_isSharedCheck_6326_ = !lean_is_exclusive(v_date_4491_);
if (v_isSharedCheck_6326_ == 0)
{
lean_object* v_unused_6327_; 
v_unused_6327_ = lean_ctor_get(v_date_4491_, 36);
lean_dec(v_unused_6327_);
v___x_6320_ = v_date_4491_;
v_isShared_6321_ = v_isSharedCheck_6326_;
goto v_resetjp_6319_;
}
else
{
lean_inc(v_x_6318_);
lean_inc(v_X_6317_);
lean_inc(v_O_6316_);
lean_inc(v_v_6315_);
lean_inc(v_zabbrev_6314_);
lean_inc(v_z_6313_);
lean_inc(v_V_6312_);
lean_inc(v_N_6311_);
lean_inc(v_n_6310_);
lean_inc(v_A_6309_);
lean_inc(v_S_6308_);
lean_inc(v_s_6307_);
lean_inc(v_m_6306_);
lean_inc(v_H_6305_);
lean_inc(v_k_6304_);
lean_inc(v_K_6303_);
lean_inc(v_h_6302_);
lean_inc(v_B_6301_);
lean_inc(v_b_6300_);
lean_inc(v_a_6299_);
lean_inc(v_F_6298_);
lean_inc(v_c_6297_);
lean_inc(v_e_6296_);
lean_inc(v_E_6295_);
lean_inc(v_W_6294_);
lean_inc(v_w_6293_);
lean_inc(v_q_6292_);
lean_inc(v_Q_6291_);
lean_inc(v_d_6290_);
lean_inc(v_L_6289_);
lean_inc(v_M_6288_);
lean_inc(v_D_6287_);
lean_inc(v_Y_6286_);
lean_inc(v_u_6285_);
lean_inc(v_y_6284_);
lean_inc(v_G_6283_);
lean_dec(v_date_4491_);
v___x_6320_ = lean_box(0);
v_isShared_6321_ = v_isSharedCheck_6326_;
goto v_resetjp_6319_;
}
v_resetjp_6319_:
{
lean_object* v___x_6322_; lean_object* v___x_6324_; 
v___x_6322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6322_, 0, v_data_4493_);
if (v_isShared_6321_ == 0)
{
lean_ctor_set(v___x_6320_, 36, v___x_6322_);
v___x_6324_ = v___x_6320_;
goto v_reusejp_6323_;
}
else
{
lean_object* v_reuseFailAlloc_6325_; 
v_reuseFailAlloc_6325_ = lean_alloc_ctor(0, 37, 0);
lean_ctor_set(v_reuseFailAlloc_6325_, 0, v_G_6283_);
lean_ctor_set(v_reuseFailAlloc_6325_, 1, v_y_6284_);
lean_ctor_set(v_reuseFailAlloc_6325_, 2, v_u_6285_);
lean_ctor_set(v_reuseFailAlloc_6325_, 3, v_Y_6286_);
lean_ctor_set(v_reuseFailAlloc_6325_, 4, v_D_6287_);
lean_ctor_set(v_reuseFailAlloc_6325_, 5, v_M_6288_);
lean_ctor_set(v_reuseFailAlloc_6325_, 6, v_L_6289_);
lean_ctor_set(v_reuseFailAlloc_6325_, 7, v_d_6290_);
lean_ctor_set(v_reuseFailAlloc_6325_, 8, v_Q_6291_);
lean_ctor_set(v_reuseFailAlloc_6325_, 9, v_q_6292_);
lean_ctor_set(v_reuseFailAlloc_6325_, 10, v_w_6293_);
lean_ctor_set(v_reuseFailAlloc_6325_, 11, v_W_6294_);
lean_ctor_set(v_reuseFailAlloc_6325_, 12, v_E_6295_);
lean_ctor_set(v_reuseFailAlloc_6325_, 13, v_e_6296_);
lean_ctor_set(v_reuseFailAlloc_6325_, 14, v_c_6297_);
lean_ctor_set(v_reuseFailAlloc_6325_, 15, v_F_6298_);
lean_ctor_set(v_reuseFailAlloc_6325_, 16, v_a_6299_);
lean_ctor_set(v_reuseFailAlloc_6325_, 17, v_b_6300_);
lean_ctor_set(v_reuseFailAlloc_6325_, 18, v_B_6301_);
lean_ctor_set(v_reuseFailAlloc_6325_, 19, v_h_6302_);
lean_ctor_set(v_reuseFailAlloc_6325_, 20, v_K_6303_);
lean_ctor_set(v_reuseFailAlloc_6325_, 21, v_k_6304_);
lean_ctor_set(v_reuseFailAlloc_6325_, 22, v_H_6305_);
lean_ctor_set(v_reuseFailAlloc_6325_, 23, v_m_6306_);
lean_ctor_set(v_reuseFailAlloc_6325_, 24, v_s_6307_);
lean_ctor_set(v_reuseFailAlloc_6325_, 25, v_S_6308_);
lean_ctor_set(v_reuseFailAlloc_6325_, 26, v_A_6309_);
lean_ctor_set(v_reuseFailAlloc_6325_, 27, v_n_6310_);
lean_ctor_set(v_reuseFailAlloc_6325_, 28, v_N_6311_);
lean_ctor_set(v_reuseFailAlloc_6325_, 29, v_V_6312_);
lean_ctor_set(v_reuseFailAlloc_6325_, 30, v_z_6313_);
lean_ctor_set(v_reuseFailAlloc_6325_, 31, v_zabbrev_6314_);
lean_ctor_set(v_reuseFailAlloc_6325_, 32, v_v_6315_);
lean_ctor_set(v_reuseFailAlloc_6325_, 33, v_O_6316_);
lean_ctor_set(v_reuseFailAlloc_6325_, 34, v_X_6317_);
lean_ctor_set(v_reuseFailAlloc_6325_, 35, v_x_6318_);
lean_ctor_set(v_reuseFailAlloc_6325_, 36, v___x_6322_);
v___x_6324_ = v_reuseFailAlloc_6325_;
goto v_reusejp_6323_;
}
v_reusejp_6323_:
{
return v___x_6324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(lean_object* v_year_6328_, uint8_t v_x_6329_){
_start:
{
if (v_x_6329_ == 0)
{
lean_object* v___x_6330_; lean_object* v___x_6331_; lean_object* v___x_6332_; 
v___x_6330_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6331_ = lean_int_add(v_year_6328_, v___x_6330_);
v___x_6332_ = lean_int_neg(v___x_6331_);
lean_dec(v___x_6331_);
return v___x_6332_;
}
else
{
lean_inc(v_year_6328_);
return v_year_6328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra___boxed(lean_object* v_year_6333_, lean_object* v_x_6334_){
_start:
{
uint8_t v_x_42__boxed_6335_; lean_object* v_res_6336_; 
v_x_42__boxed_6335_ = lean_unbox(v_x_6334_);
v_res_6336_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_year_6333_, v_x_42__boxed_6335_);
lean_dec(v_year_6333_);
return v_res_6336_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(uint8_t v_x_6337_){
_start:
{
switch(v_x_6337_)
{
case 1:
{
uint8_t v___x_6338_; 
v___x_6338_ = 1;
return v___x_6338_;
}
case 2:
{
uint8_t v___x_6339_; 
v___x_6339_ = 1;
return v___x_6339_;
}
default: 
{
uint8_t v___x_6340_; 
v___x_6340_ = 0;
return v___x_6340_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod___boxed(lean_object* v_x_6341_){
_start:
{
uint8_t v_x_28__boxed_6342_; uint8_t v_res_6343_; lean_object* v_r_6344_; 
v_x_28__boxed_6342_ = lean_unbox(v_x_6341_);
v_res_6343_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v_x_28__boxed_6342_);
v_r_6344_ = lean_box(v_res_6343_);
return v_r_6344_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(uint8_t v_x_6345_){
_start:
{
switch(v_x_6345_)
{
case 3:
{
uint8_t v___x_6346_; 
v___x_6346_ = 1;
return v___x_6346_;
}
case 4:
{
uint8_t v___x_6347_; 
v___x_6347_ = 1;
return v___x_6347_;
}
case 5:
{
uint8_t v___x_6348_; 
v___x_6348_ = 1;
return v___x_6348_;
}
default: 
{
uint8_t v___x_6349_; 
v___x_6349_ = 0;
return v___x_6349_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod___boxed(lean_object* v_x_6350_){
_start:
{
uint8_t v_x_38__boxed_6351_; uint8_t v_res_6352_; lean_object* v_r_6353_; 
v_x_38__boxed_6351_ = lean_unbox(v_x_6350_);
v_res_6352_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v_x_38__boxed_6351_);
v_r_6353_ = lean_box(v_res_6352_);
return v_r_6353_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(lean_object* v_val_6354_, lean_object* v_x_6355_){
_start:
{
lean_inc_ref(v_val_6354_);
return v_val_6354_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed(lean_object* v_val_6356_, lean_object* v_x_6357_){
_start:
{
lean_object* v_res_6358_; 
v_res_6358_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0(v_val_6356_, v_x_6357_);
lean_dec_ref(v_val_6356_);
return v_res_6358_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(lean_object* v___y_6359_, lean_object* v_00___6360_){
_start:
{
uint8_t v___x_6361_; lean_object* v___x_6362_; 
v___x_6361_ = 1;
v___x_6362_ = l_Std_Time_TimeZone_Offset_toIsoString(v___y_6359_, v___x_6361_);
return v___x_6362_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1(void){
_start:
{
lean_object* v___x_6365_; lean_object* v___x_6366_; 
v___x_6365_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6366_ = lean_int_neg(v___x_6365_);
return v___x_6366_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2(void){
_start:
{
lean_object* v___x_6367_; lean_object* v___x_6368_; 
v___x_6367_ = lean_unsigned_to_nat(1000000u);
v___x_6368_ = lean_nat_to_int(v___x_6367_);
return v___x_6368_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3(void){
_start:
{
lean_object* v___x_6369_; uint8_t v___x_6370_; lean_object* v___x_6371_; 
v___x_6369_ = lean_unsigned_to_nat(0u);
v___x_6370_ = 1;
v___x_6371_ = l_Std_Time_Second_instOfNatOrdinal(v___x_6370_, v___x_6369_);
return v___x_6371_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4(void){
_start:
{
lean_object* v___x_6372_; lean_object* v___x_6373_; lean_object* v___x_6374_; 
v___x_6372_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_parseOffset___closed__5);
v___x_6373_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6374_ = lean_int_add(v___x_6373_, v___x_6372_);
return v___x_6374_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5(void){
_start:
{
lean_object* v___x_6375_; lean_object* v___x_6376_; lean_object* v___x_6377_; 
v___x_6375_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6376_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__4);
v___x_6377_ = lean_int_sub(v___x_6376_, v___x_6375_);
return v___x_6377_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6(void){
_start:
{
lean_object* v___x_6378_; lean_object* v___x_6379_; lean_object* v_range_6380_; 
v___x_6378_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6379_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__5);
v_range_6380_ = lean_int_add(v___x_6379_, v___x_6378_);
return v_range_6380_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7(void){
_start:
{
lean_object* v___x_6381_; lean_object* v___x_6382_; 
v___x_6381_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6382_ = lean_int_sub(v___x_6381_, v___x_6381_);
return v___x_6382_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8(void){
_start:
{
lean_object* v_range_6383_; lean_object* v___x_6384_; lean_object* v___x_6385_; 
v_range_6383_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6);
v___x_6384_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__7);
v___x_6385_ = lean_int_emod(v___x_6384_, v_range_6383_);
return v___x_6385_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9(void){
_start:
{
lean_object* v_range_6386_; lean_object* v___x_6387_; lean_object* v___x_6388_; 
v_range_6386_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6);
v___x_6387_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__8);
v___x_6388_ = lean_int_add(v___x_6387_, v_range_6386_);
return v___x_6388_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10(void){
_start:
{
lean_object* v_range_6389_; lean_object* v___x_6390_; lean_object* v___x_6391_; 
v_range_6389_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__6);
v___x_6390_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__9);
v___x_6391_ = lean_int_emod(v___x_6390_, v_range_6389_);
return v___x_6391_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11(void){
_start:
{
lean_object* v___x_6392_; lean_object* v___x_6393_; lean_object* v___x_6394_; 
v___x_6392_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6393_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__10);
v___x_6394_ = lean_int_add(v___x_6393_, v___x_6392_);
return v___x_6394_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12(void){
_start:
{
lean_object* v___x_6395_; lean_object* v___x_6396_; 
v___x_6395_ = lean_unsigned_to_nat(30u);
v___x_6396_ = lean_nat_to_int(v___x_6395_);
return v___x_6396_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13(void){
_start:
{
lean_object* v___x_6397_; lean_object* v___x_6398_; lean_object* v___x_6399_; 
v___x_6397_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__12);
v___x_6398_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6399_ = lean_int_add(v___x_6398_, v___x_6397_);
return v___x_6399_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14(void){
_start:
{
lean_object* v___x_6400_; lean_object* v___x_6401_; lean_object* v___x_6402_; 
v___x_6400_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6401_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__13);
v___x_6402_ = lean_int_sub(v___x_6401_, v___x_6400_);
return v___x_6402_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15(void){
_start:
{
lean_object* v___x_6403_; lean_object* v___x_6404_; lean_object* v_range_6405_; 
v___x_6403_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6404_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__14);
v_range_6405_ = lean_int_add(v___x_6404_, v___x_6403_);
return v_range_6405_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16(void){
_start:
{
lean_object* v___x_6406_; lean_object* v___x_6407_; lean_object* v___x_6408_; 
v___x_6406_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6407_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6408_ = lean_int_sub(v___x_6407_, v___x_6406_);
return v___x_6408_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17(void){
_start:
{
lean_object* v_range_6409_; lean_object* v___x_6410_; lean_object* v___x_6411_; 
v_range_6409_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v___x_6410_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16);
v___x_6411_ = lean_int_emod(v___x_6410_, v_range_6409_);
return v___x_6411_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18(void){
_start:
{
lean_object* v_range_6412_; lean_object* v___x_6413_; lean_object* v___x_6414_; 
v_range_6412_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v___x_6413_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__17);
v___x_6414_ = lean_int_add(v___x_6413_, v_range_6412_);
return v___x_6414_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19(void){
_start:
{
lean_object* v_range_6415_; lean_object* v___x_6416_; lean_object* v___x_6417_; 
v_range_6415_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__15);
v___x_6416_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__18);
v___x_6417_ = lean_int_emod(v___x_6416_, v_range_6415_);
return v___x_6417_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20(void){
_start:
{
lean_object* v___x_6418_; lean_object* v___x_6419_; lean_object* v___x_6420_; 
v___x_6418_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6419_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__19);
v___x_6420_ = lean_int_add(v___x_6419_, v___x_6418_);
return v___x_6420_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21(void){
_start:
{
lean_object* v___x_6421_; lean_object* v___x_6422_; 
v___x_6421_ = lean_unsigned_to_nat(11u);
v___x_6422_ = lean_nat_to_int(v___x_6421_);
return v___x_6422_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22(void){
_start:
{
lean_object* v___x_6423_; lean_object* v___x_6424_; lean_object* v___x_6425_; 
v___x_6423_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__21);
v___x_6424_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6425_ = lean_int_add(v___x_6424_, v___x_6423_);
return v___x_6425_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23(void){
_start:
{
lean_object* v___x_6426_; lean_object* v___x_6427_; lean_object* v___x_6428_; 
v___x_6426_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6427_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__22);
v___x_6428_ = lean_int_sub(v___x_6427_, v___x_6426_);
return v___x_6428_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24(void){
_start:
{
lean_object* v___x_6429_; lean_object* v___x_6430_; lean_object* v_range_6431_; 
v___x_6429_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6430_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__23);
v_range_6431_ = lean_int_add(v___x_6430_, v___x_6429_);
return v_range_6431_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25(void){
_start:
{
lean_object* v_range_6432_; lean_object* v___x_6433_; lean_object* v___x_6434_; 
v_range_6432_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24);
v___x_6433_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__16);
v___x_6434_ = lean_int_emod(v___x_6433_, v_range_6432_);
return v___x_6434_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26(void){
_start:
{
lean_object* v_range_6435_; lean_object* v___x_6436_; lean_object* v___x_6437_; 
v_range_6435_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24);
v___x_6436_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__25);
v___x_6437_ = lean_int_add(v___x_6436_, v_range_6435_);
return v___x_6437_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27(void){
_start:
{
lean_object* v_range_6438_; lean_object* v___x_6439_; lean_object* v___x_6440_; 
v_range_6438_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__24);
v___x_6439_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__26);
v___x_6440_ = lean_int_emod(v___x_6439_, v_range_6438_);
return v___x_6440_;
}
}
static lean_object* _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28(void){
_start:
{
lean_object* v___x_6441_; lean_object* v___x_6442_; lean_object* v___x_6443_; 
v___x_6441_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6442_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__27);
v___x_6443_ = lean_int_add(v___x_6442_, v___x_6441_);
return v___x_6443_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(lean_object* v_builder_6444_, lean_object* v_aw_6445_){
_start:
{
lean_object* v___y_6447_; lean_object* v___y_6448_; lean_object* v___y_6487_; lean_object* v___y_6488_; lean_object* v___y_6491_; lean_object* v___y_6492_; lean_object* v___y_6493_; lean_object* v___y_6494_; lean_object* v___y_6495_; uint8_t v___y_6496_; lean_object* v___y_6504_; lean_object* v___y_6505_; lean_object* v___y_6506_; lean_object* v___y_6507_; lean_object* v___y_6508_; lean_object* v___y_6509_; lean_object* v___y_6514_; lean_object* v___y_6515_; lean_object* v___y_6516_; lean_object* v___y_6517_; lean_object* v___y_6518_; lean_object* v_G_6526_; lean_object* v_y_6527_; lean_object* v_u_6528_; lean_object* v_Y_6529_; lean_object* v_M_6530_; lean_object* v_L_6531_; lean_object* v_d_6532_; lean_object* v_a_6533_; lean_object* v_b_6534_; lean_object* v_B_6535_; lean_object* v_h_6536_; lean_object* v_K_6537_; lean_object* v_k_6538_; lean_object* v_H_6539_; lean_object* v_m_6540_; lean_object* v_s_6541_; lean_object* v_S_6542_; lean_object* v_A_6543_; lean_object* v_n_6544_; lean_object* v_N_6545_; lean_object* v_V_6546_; lean_object* v_z_6547_; lean_object* v_zabbrev_6548_; lean_object* v_v_6549_; lean_object* v_O_6550_; lean_object* v_X_6551_; lean_object* v_x_6552_; lean_object* v_Z_6553_; lean_object* v___y_6555_; lean_object* v___y_6556_; lean_object* v___y_6557_; lean_object* v___y_6558_; lean_object* v___y_6559_; lean_object* v___y_6560_; lean_object* v___y_6561_; lean_object* v___y_6562_; lean_object* v___y_6571_; lean_object* v___y_6572_; lean_object* v___y_6573_; lean_object* v___y_6574_; lean_object* v___y_6575_; lean_object* v___y_6576_; lean_object* v___y_6577_; lean_object* v___y_6582_; lean_object* v___y_6583_; lean_object* v___y_6584_; lean_object* v___y_6585_; lean_object* v___y_6586_; lean_object* v___y_6587_; lean_object* v___y_6591_; lean_object* v___y_6592_; lean_object* v___y_6593_; lean_object* v___y_6594_; lean_object* v___y_6595_; lean_object* v___y_6599_; lean_object* v___y_6600_; lean_object* v___y_6601_; lean_object* v___y_6602_; lean_object* v___y_6610_; lean_object* v___y_6611_; lean_object* v___y_6612_; lean_object* v___y_6613_; uint8_t v_val_6614_; lean_object* v___y_6622_; lean_object* v___y_6623_; lean_object* v___y_6624_; lean_object* v___y_6625_; lean_object* v___y_6635_; lean_object* v___y_6636_; lean_object* v___y_6637_; uint8_t v___y_6638_; lean_object* v___y_6645_; lean_object* v___y_6646_; lean_object* v___y_6647_; lean_object* v___y_6652_; lean_object* v___y_6653_; lean_object* v___y_6657_; lean_object* v___y_6658_; lean_object* v___y_6659_; lean_object* v___y_6666_; lean_object* v___y_6667_; lean_object* v___y_6668_; lean_object* v___y_6673_; 
v_G_6526_ = lean_ctor_get(v_builder_6444_, 0);
lean_inc(v_G_6526_);
v_y_6527_ = lean_ctor_get(v_builder_6444_, 1);
lean_inc(v_y_6527_);
v_u_6528_ = lean_ctor_get(v_builder_6444_, 2);
lean_inc(v_u_6528_);
v_Y_6529_ = lean_ctor_get(v_builder_6444_, 3);
lean_inc(v_Y_6529_);
v_M_6530_ = lean_ctor_get(v_builder_6444_, 5);
lean_inc(v_M_6530_);
v_L_6531_ = lean_ctor_get(v_builder_6444_, 6);
lean_inc(v_L_6531_);
v_d_6532_ = lean_ctor_get(v_builder_6444_, 7);
lean_inc(v_d_6532_);
v_a_6533_ = lean_ctor_get(v_builder_6444_, 16);
lean_inc(v_a_6533_);
v_b_6534_ = lean_ctor_get(v_builder_6444_, 17);
lean_inc(v_b_6534_);
v_B_6535_ = lean_ctor_get(v_builder_6444_, 18);
lean_inc(v_B_6535_);
v_h_6536_ = lean_ctor_get(v_builder_6444_, 19);
lean_inc(v_h_6536_);
v_K_6537_ = lean_ctor_get(v_builder_6444_, 20);
lean_inc(v_K_6537_);
v_k_6538_ = lean_ctor_get(v_builder_6444_, 21);
lean_inc(v_k_6538_);
v_H_6539_ = lean_ctor_get(v_builder_6444_, 22);
lean_inc(v_H_6539_);
v_m_6540_ = lean_ctor_get(v_builder_6444_, 23);
lean_inc(v_m_6540_);
v_s_6541_ = lean_ctor_get(v_builder_6444_, 24);
lean_inc(v_s_6541_);
v_S_6542_ = lean_ctor_get(v_builder_6444_, 25);
lean_inc(v_S_6542_);
v_A_6543_ = lean_ctor_get(v_builder_6444_, 26);
lean_inc(v_A_6543_);
v_n_6544_ = lean_ctor_get(v_builder_6444_, 27);
lean_inc(v_n_6544_);
v_N_6545_ = lean_ctor_get(v_builder_6444_, 28);
lean_inc(v_N_6545_);
v_V_6546_ = lean_ctor_get(v_builder_6444_, 29);
lean_inc(v_V_6546_);
v_z_6547_ = lean_ctor_get(v_builder_6444_, 30);
lean_inc(v_z_6547_);
v_zabbrev_6548_ = lean_ctor_get(v_builder_6444_, 31);
lean_inc(v_zabbrev_6548_);
v_v_6549_ = lean_ctor_get(v_builder_6444_, 32);
lean_inc(v_v_6549_);
v_O_6550_ = lean_ctor_get(v_builder_6444_, 33);
lean_inc(v_O_6550_);
v_X_6551_ = lean_ctor_get(v_builder_6444_, 34);
lean_inc(v_X_6551_);
v_x_6552_ = lean_ctor_get(v_builder_6444_, 35);
lean_inc(v_x_6552_);
v_Z_6553_ = lean_ctor_get(v_builder_6444_, 36);
lean_inc(v_Z_6553_);
lean_dec_ref(v_builder_6444_);
if (lean_obj_tag(v_O_6550_) == 0)
{
if (lean_obj_tag(v_X_6551_) == 0)
{
if (lean_obj_tag(v_x_6552_) == 0)
{
if (lean_obj_tag(v_Z_6553_) == 0)
{
lean_object* v___x_6680_; 
v___x_6680_ = l_Std_Time_TimeZone_Offset_zero;
v___y_6673_ = v___x_6680_;
goto v___jp_6672_;
}
else
{
lean_object* v_val_6681_; 
v_val_6681_ = lean_ctor_get(v_Z_6553_, 0);
lean_inc(v_val_6681_);
lean_dec_ref_known(v_Z_6553_, 1);
v___y_6673_ = v_val_6681_;
goto v___jp_6672_;
}
}
else
{
lean_object* v_val_6682_; 
lean_dec(v_Z_6553_);
v_val_6682_ = lean_ctor_get(v_x_6552_, 0);
lean_inc(v_val_6682_);
lean_dec_ref_known(v_x_6552_, 1);
v___y_6673_ = v_val_6682_;
goto v___jp_6672_;
}
}
else
{
lean_object* v_val_6683_; 
lean_dec(v_Z_6553_);
lean_dec(v_x_6552_);
v_val_6683_ = lean_ctor_get(v_X_6551_, 0);
lean_inc(v_val_6683_);
lean_dec_ref_known(v_X_6551_, 1);
v___y_6673_ = v_val_6683_;
goto v___jp_6672_;
}
}
else
{
lean_object* v_val_6684_; 
lean_dec(v_Z_6553_);
lean_dec(v_x_6552_);
lean_dec(v_X_6551_);
v_val_6684_ = lean_ctor_get(v_O_6550_, 0);
lean_inc(v_val_6684_);
lean_dec_ref_known(v_O_6550_, 1);
v___y_6673_ = v_val_6684_;
goto v___jp_6672_;
}
v___jp_6446_:
{
if (lean_obj_tag(v___y_6447_) == 0)
{
lean_object* v___x_6449_; 
lean_dec_ref(v___y_6448_);
v___x_6449_ = lean_box(0);
return v___x_6449_;
}
else
{
lean_object* v_val_6450_; lean_object* v___x_6452_; uint8_t v_isShared_6453_; uint8_t v_isSharedCheck_6485_; 
v_val_6450_ = lean_ctor_get(v___y_6447_, 0);
v_isSharedCheck_6485_ = !lean_is_exclusive(v___y_6447_);
if (v_isSharedCheck_6485_ == 0)
{
v___x_6452_ = v___y_6447_;
v_isShared_6453_ = v_isSharedCheck_6485_;
goto v_resetjp_6451_;
}
else
{
lean_inc(v_val_6450_);
lean_dec(v___y_6447_);
v___x_6452_ = lean_box(0);
v_isShared_6453_ = v_isSharedCheck_6485_;
goto v_resetjp_6451_;
}
v_resetjp_6451_:
{
lean_object* v_offset_6454_; lean_object* v_name_6455_; lean_object* v_abbreviation_6456_; uint8_t v_isDST_6457_; uint8_t v___x_6458_; uint8_t v___x_6459_; lean_object* v_ltt_6460_; lean_object* v___x_6461_; lean_object* v___x_6462_; lean_object* v___x_6463_; lean_object* v_wt_6464_; lean_object* v_ltt_6465_; lean_object* v_tz_6466_; lean_object* v_offset_6467_; lean_object* v_second_6468_; lean_object* v_nano_6469_; lean_object* v___f_6470_; lean_object* v___x_6471_; lean_object* v___x_6472_; lean_object* v___x_6473_; lean_object* v___x_6474_; lean_object* v___x_6475_; lean_object* v_nanos_6476_; lean_object* v___x_6477_; lean_object* v_nanos_6478_; lean_object* v___x_6479_; lean_object* v___x_6480_; lean_object* v___x_6481_; lean_object* v___x_6483_; 
v_offset_6454_ = lean_ctor_get(v___y_6448_, 0);
lean_inc(v_offset_6454_);
v_name_6455_ = lean_ctor_get(v___y_6448_, 1);
lean_inc_ref(v_name_6455_);
v_abbreviation_6456_ = lean_ctor_get(v___y_6448_, 2);
lean_inc_ref(v_abbreviation_6456_);
v_isDST_6457_ = lean_ctor_get_uint8(v___y_6448_, sizeof(void*)*3);
lean_dec_ref(v___y_6448_);
v___x_6458_ = 0;
v___x_6459_ = 1;
v_ltt_6460_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6460_, 0, v_offset_6454_);
lean_ctor_set(v_ltt_6460_, 1, v_abbreviation_6456_);
lean_ctor_set(v_ltt_6460_, 2, v_name_6455_);
lean_ctor_set_uint8(v_ltt_6460_, sizeof(void*)*3, v_isDST_6457_);
lean_ctor_set_uint8(v_ltt_6460_, sizeof(void*)*3 + 1, v___x_6458_);
lean_ctor_set_uint8(v_ltt_6460_, sizeof(void*)*3 + 2, v___x_6459_);
v___x_6461_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6462_ = lean_box(0);
v___x_6463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6463_, 0, v_ltt_6460_);
lean_ctor_set(v___x_6463_, 1, v___x_6461_);
lean_ctor_set(v___x_6463_, 2, v___x_6462_);
lean_inc(v_val_6450_);
v_wt_6464_ = l_Std_Time_PlainDateTime_toWallTime(v_val_6450_);
lean_inc_ref(v___x_6463_);
v_ltt_6465_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_6463_, v_wt_6464_);
v_tz_6466_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_6465_);
lean_dec_ref(v_ltt_6465_);
v_offset_6467_ = lean_ctor_get(v_tz_6466_, 0);
v_second_6468_ = lean_ctor_get(v_wt_6464_, 0);
lean_inc(v_second_6468_);
v_nano_6469_ = lean_ctor_get(v_wt_6464_, 1);
lean_inc(v_nano_6469_);
lean_dec_ref(v_wt_6464_);
v___f_6470_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__0___boxed), 2, 1);
lean_closure_set(v___f_6470_, 0, v_val_6450_);
v___x_6471_ = lean_mk_thunk(v___f_6470_);
v___x_6472_ = lean_int_neg(v_offset_6467_);
v___x_6473_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__1);
v___x_6474_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_6475_ = lean_int_mul(v_second_6468_, v___x_6474_);
lean_dec(v_second_6468_);
v_nanos_6476_ = lean_int_add(v___x_6475_, v_nano_6469_);
lean_dec(v_nano_6469_);
lean_dec(v___x_6475_);
v___x_6477_ = lean_int_mul(v___x_6472_, v___x_6474_);
lean_dec(v___x_6472_);
v_nanos_6478_ = lean_int_add(v___x_6477_, v___x_6473_);
lean_dec(v___x_6477_);
v___x_6479_ = lean_int_add(v_nanos_6476_, v_nanos_6478_);
lean_dec(v_nanos_6478_);
lean_dec(v_nanos_6476_);
v___x_6480_ = l_Std_Time_Duration_ofNanoseconds(v___x_6479_);
lean_dec(v___x_6479_);
v___x_6481_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6481_, 0, v___x_6471_);
lean_ctor_set(v___x_6481_, 1, v___x_6480_);
lean_ctor_set(v___x_6481_, 2, v___x_6463_);
lean_ctor_set(v___x_6481_, 3, v_tz_6466_);
if (v_isShared_6453_ == 0)
{
lean_ctor_set(v___x_6452_, 0, v___x_6481_);
v___x_6483_ = v___x_6452_;
goto v_reusejp_6482_;
}
else
{
lean_object* v_reuseFailAlloc_6484_; 
v_reuseFailAlloc_6484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6484_, 0, v___x_6481_);
v___x_6483_ = v_reuseFailAlloc_6484_;
goto v_reusejp_6482_;
}
v_reusejp_6482_:
{
return v___x_6483_;
}
}
}
}
v___jp_6486_:
{
if (lean_obj_tag(v_aw_6445_) == 0)
{
lean_object* v_a_6489_; 
lean_dec_ref(v___y_6487_);
v_a_6489_ = lean_ctor_get(v_aw_6445_, 0);
lean_inc_ref(v_a_6489_);
lean_dec_ref_known(v_aw_6445_, 1);
v___y_6447_ = v___y_6488_;
v___y_6448_ = v_a_6489_;
goto v___jp_6446_;
}
else
{
v___y_6447_ = v___y_6488_;
v___y_6448_ = v___y_6487_;
goto v___jp_6446_;
}
}
v___jp_6490_:
{
lean_object* v___x_6497_; uint8_t v___x_6498_; 
v___x_6497_ = l_Std_Time_Month_Ordinal_days(v___y_6496_, v___y_6491_);
v___x_6498_ = lean_int_dec_le(v___y_6493_, v___x_6497_);
lean_dec(v___x_6497_);
if (v___x_6498_ == 0)
{
lean_object* v___x_6499_; 
lean_dec(v___y_6494_);
lean_dec(v___y_6493_);
lean_dec_ref(v___y_6492_);
lean_dec(v___y_6491_);
v___x_6499_ = lean_box(0);
v___y_6487_ = v___y_6495_;
v___y_6488_ = v___x_6499_;
goto v___jp_6486_;
}
else
{
lean_object* v_date_6500_; lean_object* v___x_6501_; lean_object* v___x_6502_; 
v_date_6500_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_date_6500_, 0, v___y_6494_);
lean_ctor_set(v_date_6500_, 1, v___y_6491_);
lean_ctor_set(v_date_6500_, 2, v___y_6493_);
v___x_6501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6501_, 0, v_date_6500_);
lean_ctor_set(v___x_6501_, 1, v___y_6492_);
v___x_6502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6502_, 0, v___x_6501_);
v___y_6487_ = v___y_6495_;
v___y_6488_ = v___x_6502_;
goto v___jp_6486_;
}
}
v___jp_6503_:
{
lean_object* v___x_6510_; lean_object* v___x_6511_; uint8_t v___x_6512_; 
v___x_6510_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__0);
v___x_6511_ = lean_int_mod(v___y_6508_, v___x_6510_);
v___x_6512_ = lean_int_dec_eq(v___x_6511_, v___y_6507_);
lean_dec(v___x_6511_);
v___y_6491_ = v___y_6504_;
v___y_6492_ = v___y_6506_;
v___y_6493_ = v___y_6505_;
v___y_6494_ = v___y_6508_;
v___y_6495_ = v___y_6509_;
v___y_6496_ = v___x_6512_;
goto v___jp_6490_;
}
v___jp_6513_:
{
lean_object* v___x_6519_; lean_object* v___x_6520_; lean_object* v___x_6521_; uint8_t v___x_6522_; 
v___x_6519_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_dateFromModifier___closed__1);
v___x_6520_ = lean_int_mod(v___y_6516_, v___x_6519_);
v___x_6521_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___x_6522_ = lean_int_dec_eq(v___x_6520_, v___x_6521_);
lean_dec(v___x_6520_);
if (v___x_6522_ == 0)
{
v___y_6491_ = v___y_6514_;
v___y_6492_ = v___y_6518_;
v___y_6493_ = v___y_6515_;
v___y_6494_ = v___y_6516_;
v___y_6495_ = v___y_6517_;
v___y_6496_ = v___x_6522_;
goto v___jp_6490_;
}
else
{
lean_object* v___x_6523_; lean_object* v___x_6524_; uint8_t v___x_6525_; 
v___x_6523_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatWith___closed__0);
v___x_6524_ = lean_int_mod(v___y_6516_, v___x_6523_);
v___x_6525_ = lean_int_dec_eq(v___x_6524_, v___x_6521_);
lean_dec(v___x_6524_);
if (v___x_6525_ == 0)
{
if (v___x_6522_ == 0)
{
v___y_6504_ = v___y_6514_;
v___y_6505_ = v___y_6515_;
v___y_6506_ = v___y_6518_;
v___y_6507_ = v___x_6521_;
v___y_6508_ = v___y_6516_;
v___y_6509_ = v___y_6517_;
goto v___jp_6503_;
}
else
{
v___y_6491_ = v___y_6514_;
v___y_6492_ = v___y_6518_;
v___y_6493_ = v___y_6515_;
v___y_6494_ = v___y_6516_;
v___y_6495_ = v___y_6517_;
v___y_6496_ = v___x_6522_;
goto v___jp_6490_;
}
}
else
{
v___y_6504_ = v___y_6514_;
v___y_6505_ = v___y_6515_;
v___y_6506_ = v___y_6518_;
v___y_6507_ = v___x_6521_;
v___y_6508_ = v___y_6516_;
v___y_6509_ = v___y_6517_;
goto v___jp_6503_;
}
}
}
v___jp_6554_:
{
if (lean_obj_tag(v_N_6545_) == 0)
{
if (lean_obj_tag(v_A_6543_) == 0)
{
lean_object* v___x_6563_; 
v___x_6563_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6563_, 0, v___y_6559_);
lean_ctor_set(v___x_6563_, 1, v___y_6557_);
lean_ctor_set(v___x_6563_, 2, v___y_6558_);
lean_ctor_set(v___x_6563_, 3, v___y_6562_);
v___y_6514_ = v___y_6555_;
v___y_6515_ = v___y_6556_;
v___y_6516_ = v___y_6560_;
v___y_6517_ = v___y_6561_;
v___y_6518_ = v___x_6563_;
goto v___jp_6513_;
}
else
{
lean_object* v_val_6564_; lean_object* v___x_6565_; lean_object* v___x_6566_; lean_object* v___x_6567_; 
lean_dec(v___y_6562_);
lean_dec(v___y_6559_);
lean_dec(v___y_6558_);
lean_dec(v___y_6557_);
v_val_6564_ = lean_ctor_get(v_A_6543_, 0);
lean_inc(v_val_6564_);
lean_dec_ref_known(v_A_6543_, 1);
v___x_6565_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__2);
v___x_6566_ = lean_int_mul(v_val_6564_, v___x_6565_);
lean_dec(v_val_6564_);
v___x_6567_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_6566_);
lean_dec(v___x_6566_);
v___y_6514_ = v___y_6555_;
v___y_6515_ = v___y_6556_;
v___y_6516_ = v___y_6560_;
v___y_6517_ = v___y_6561_;
v___y_6518_ = v___x_6567_;
goto v___jp_6513_;
}
}
else
{
lean_object* v_val_6568_; lean_object* v___x_6569_; 
lean_dec(v___y_6562_);
lean_dec(v___y_6559_);
lean_dec(v___y_6558_);
lean_dec(v___y_6557_);
lean_dec(v_A_6543_);
v_val_6568_ = lean_ctor_get(v_N_6545_, 0);
lean_inc(v_val_6568_);
lean_dec_ref_known(v_N_6545_, 1);
v___x_6569_ = l_Std_Time_PlainTime_ofNanoseconds(v_val_6568_);
lean_dec(v_val_6568_);
v___y_6514_ = v___y_6555_;
v___y_6515_ = v___y_6556_;
v___y_6516_ = v___y_6560_;
v___y_6517_ = v___y_6561_;
v___y_6518_ = v___x_6569_;
goto v___jp_6513_;
}
}
v___jp_6570_:
{
if (lean_obj_tag(v_n_6544_) == 0)
{
if (lean_obj_tag(v_S_6542_) == 0)
{
lean_object* v___x_6578_; 
v___x_6578_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6555_ = v___y_6571_;
v___y_6556_ = v___y_6573_;
v___y_6557_ = v___y_6572_;
v___y_6558_ = v___y_6577_;
v___y_6559_ = v___y_6574_;
v___y_6560_ = v___y_6575_;
v___y_6561_ = v___y_6576_;
v___y_6562_ = v___x_6578_;
goto v___jp_6554_;
}
else
{
lean_object* v_val_6579_; 
v_val_6579_ = lean_ctor_get(v_S_6542_, 0);
lean_inc(v_val_6579_);
lean_dec_ref_known(v_S_6542_, 1);
v___y_6555_ = v___y_6571_;
v___y_6556_ = v___y_6573_;
v___y_6557_ = v___y_6572_;
v___y_6558_ = v___y_6577_;
v___y_6559_ = v___y_6574_;
v___y_6560_ = v___y_6575_;
v___y_6561_ = v___y_6576_;
v___y_6562_ = v_val_6579_;
goto v___jp_6554_;
}
}
else
{
lean_object* v_val_6580_; 
lean_dec(v_S_6542_);
v_val_6580_ = lean_ctor_get(v_n_6544_, 0);
lean_inc(v_val_6580_);
lean_dec_ref_known(v_n_6544_, 1);
v___y_6555_ = v___y_6571_;
v___y_6556_ = v___y_6573_;
v___y_6557_ = v___y_6572_;
v___y_6558_ = v___y_6577_;
v___y_6559_ = v___y_6574_;
v___y_6560_ = v___y_6575_;
v___y_6561_ = v___y_6576_;
v___y_6562_ = v_val_6580_;
goto v___jp_6554_;
}
}
v___jp_6581_:
{
if (lean_obj_tag(v_s_6541_) == 0)
{
lean_object* v___x_6588_; 
v___x_6588_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__3);
v___y_6571_ = v___y_6582_;
v___y_6572_ = v___y_6587_;
v___y_6573_ = v___y_6583_;
v___y_6574_ = v___y_6584_;
v___y_6575_ = v___y_6585_;
v___y_6576_ = v___y_6586_;
v___y_6577_ = v___x_6588_;
goto v___jp_6570_;
}
else
{
lean_object* v_val_6589_; 
v_val_6589_ = lean_ctor_get(v_s_6541_, 0);
lean_inc(v_val_6589_);
lean_dec_ref_known(v_s_6541_, 1);
v___y_6571_ = v___y_6582_;
v___y_6572_ = v___y_6587_;
v___y_6573_ = v___y_6583_;
v___y_6574_ = v___y_6584_;
v___y_6575_ = v___y_6585_;
v___y_6576_ = v___y_6586_;
v___y_6577_ = v_val_6589_;
goto v___jp_6570_;
}
}
v___jp_6590_:
{
if (lean_obj_tag(v_m_6540_) == 0)
{
lean_object* v___x_6596_; 
v___x_6596_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__11);
v___y_6582_ = v___y_6591_;
v___y_6583_ = v___y_6592_;
v___y_6584_ = v___y_6595_;
v___y_6585_ = v___y_6593_;
v___y_6586_ = v___y_6594_;
v___y_6587_ = v___x_6596_;
goto v___jp_6581_;
}
else
{
lean_object* v_val_6597_; 
v_val_6597_ = lean_ctor_get(v_m_6540_, 0);
lean_inc(v_val_6597_);
lean_dec_ref_known(v_m_6540_, 1);
v___y_6582_ = v___y_6591_;
v___y_6583_ = v___y_6592_;
v___y_6584_ = v___y_6595_;
v___y_6585_ = v___y_6593_;
v___y_6586_ = v___y_6594_;
v___y_6587_ = v_val_6597_;
goto v___jp_6581_;
}
}
v___jp_6598_:
{
if (lean_obj_tag(v_k_6538_) == 0)
{
if (lean_obj_tag(v_H_6539_) == 0)
{
lean_object* v___x_6603_; 
v___x_6603_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6591_ = v___y_6599_;
v___y_6592_ = v___y_6600_;
v___y_6593_ = v___y_6601_;
v___y_6594_ = v___y_6602_;
v___y_6595_ = v___x_6603_;
goto v___jp_6590_;
}
else
{
lean_object* v_val_6604_; 
v_val_6604_ = lean_ctor_get(v_H_6539_, 0);
lean_inc(v_val_6604_);
lean_dec_ref_known(v_H_6539_, 1);
v___y_6591_ = v___y_6599_;
v___y_6592_ = v___y_6600_;
v___y_6593_ = v___y_6601_;
v___y_6594_ = v___y_6602_;
v___y_6595_ = v_val_6604_;
goto v___jp_6590_;
}
}
else
{
if (lean_obj_tag(v_H_6539_) == 0)
{
lean_object* v_val_6605_; lean_object* v___x_6606_; lean_object* v___x_6607_; 
v_val_6605_ = lean_ctor_get(v_k_6538_, 0);
lean_inc(v_val_6605_);
lean_dec_ref_known(v_k_6538_, 1);
v___x_6606_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_formatMonthLong___closed__0);
v___x_6607_ = lean_int_add(v_val_6605_, v___x_6606_);
lean_dec(v_val_6605_);
v___y_6591_ = v___y_6599_;
v___y_6592_ = v___y_6600_;
v___y_6593_ = v___y_6601_;
v___y_6594_ = v___y_6602_;
v___y_6595_ = v___x_6607_;
goto v___jp_6590_;
}
else
{
lean_object* v_val_6608_; 
lean_dec_ref_known(v_k_6538_, 1);
v_val_6608_ = lean_ctor_get(v_H_6539_, 0);
lean_inc(v_val_6608_);
lean_dec_ref_known(v_H_6539_, 1);
v___y_6591_ = v___y_6599_;
v___y_6592_ = v___y_6600_;
v___y_6593_ = v___y_6601_;
v___y_6594_ = v___y_6602_;
v___y_6595_ = v_val_6608_;
goto v___jp_6590_;
}
}
}
v___jp_6609_:
{
if (lean_obj_tag(v_h_6536_) == 0)
{
if (lean_obj_tag(v_K_6537_) == 0)
{
v___y_6599_ = v___y_6610_;
v___y_6600_ = v___y_6611_;
v___y_6601_ = v___y_6612_;
v___y_6602_ = v___y_6613_;
goto v___jp_6598_;
}
else
{
lean_object* v_val_6615_; lean_object* v___x_6616_; lean_object* v___x_6617_; lean_object* v___x_6618_; 
lean_dec(v_H_6539_);
lean_dec(v_k_6538_);
v_val_6615_ = lean_ctor_get(v_K_6537_, 0);
lean_inc(v_val_6615_);
lean_dec_ref_known(v_K_6537_, 1);
v___x_6616_ = lean_obj_once(&l_Std_Time_instReprFormatPart_repr___closed__4, &l_Std_Time_instReprFormatPart_repr___closed__4_once, _init_l_Std_Time_instReprFormatPart_repr___closed__4);
v___x_6617_ = lean_int_add(v_val_6615_, v___x_6616_);
lean_dec(v_val_6615_);
v___x_6618_ = l_Std_Time_HourMarker_toAbsolute(v_val_6614_, v___x_6617_);
lean_dec(v___x_6617_);
v___y_6591_ = v___y_6610_;
v___y_6592_ = v___y_6611_;
v___y_6593_ = v___y_6612_;
v___y_6594_ = v___y_6613_;
v___y_6595_ = v___x_6618_;
goto v___jp_6590_;
}
}
else
{
lean_object* v_val_6619_; lean_object* v___x_6620_; 
lean_dec(v_H_6539_);
lean_dec(v_k_6538_);
lean_dec(v_K_6537_);
v_val_6619_ = lean_ctor_get(v_h_6536_, 0);
lean_inc(v_val_6619_);
lean_dec_ref_known(v_h_6536_, 1);
v___x_6620_ = l_Std_Time_HourMarker_toAbsolute(v_val_6614_, v_val_6619_);
lean_dec(v_val_6619_);
v___y_6591_ = v___y_6610_;
v___y_6592_ = v___y_6611_;
v___y_6593_ = v___y_6612_;
v___y_6594_ = v___y_6613_;
v___y_6595_ = v___x_6620_;
goto v___jp_6590_;
}
}
v___jp_6621_:
{
if (lean_obj_tag(v_a_6533_) == 0)
{
if (lean_obj_tag(v_b_6534_) == 0)
{
if (lean_obj_tag(v_B_6535_) == 0)
{
lean_dec(v_K_6537_);
lean_dec(v_h_6536_);
v___y_6599_ = v___y_6622_;
v___y_6600_ = v___y_6623_;
v___y_6601_ = v___y_6625_;
v___y_6602_ = v___y_6624_;
goto v___jp_6598_;
}
else
{
lean_object* v_val_6626_; uint8_t v___x_6627_; uint8_t v___x_6628_; 
v_val_6626_ = lean_ctor_get(v_B_6535_, 0);
lean_inc(v_val_6626_);
lean_dec_ref_known(v_B_6535_, 1);
v___x_6627_ = lean_unbox(v_val_6626_);
lean_dec(v_val_6626_);
v___x_6628_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfExtendedDayPeriod(v___x_6627_);
v___y_6610_ = v___y_6622_;
v___y_6611_ = v___y_6623_;
v___y_6612_ = v___y_6625_;
v___y_6613_ = v___y_6624_;
v_val_6614_ = v___x_6628_;
goto v___jp_6609_;
}
}
else
{
lean_object* v_val_6629_; uint8_t v___x_6630_; uint8_t v___x_6631_; 
lean_dec(v_B_6535_);
v_val_6629_ = lean_ctor_get(v_b_6534_, 0);
lean_inc(v_val_6629_);
lean_dec_ref_known(v_b_6534_, 1);
v___x_6630_ = lean_unbox(v_val_6629_);
lean_dec(v_val_6629_);
v___x_6631_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_markerOfDayPeriod(v___x_6630_);
v___y_6610_ = v___y_6622_;
v___y_6611_ = v___y_6623_;
v___y_6612_ = v___y_6625_;
v___y_6613_ = v___y_6624_;
v_val_6614_ = v___x_6631_;
goto v___jp_6609_;
}
}
else
{
lean_object* v_val_6632_; uint8_t v___x_6633_; 
lean_dec(v_B_6535_);
lean_dec(v_b_6534_);
v_val_6632_ = lean_ctor_get(v_a_6533_, 0);
lean_inc(v_val_6632_);
lean_dec_ref_known(v_a_6533_, 1);
v___x_6633_ = lean_unbox(v_val_6632_);
lean_dec(v_val_6632_);
v___y_6610_ = v___y_6622_;
v___y_6611_ = v___y_6623_;
v___y_6612_ = v___y_6625_;
v___y_6613_ = v___y_6624_;
v_val_6614_ = v___x_6633_;
goto v___jp_6609_;
}
}
v___jp_6634_:
{
if (lean_obj_tag(v_u_6528_) == 0)
{
if (lean_obj_tag(v_y_6527_) == 0)
{
if (lean_obj_tag(v_Y_6529_) == 0)
{
lean_object* v___x_6639_; 
v___x_6639_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0, &l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_pad___closed__0);
v___y_6622_ = v___y_6635_;
v___y_6623_ = v___y_6636_;
v___y_6624_ = v___y_6637_;
v___y_6625_ = v___x_6639_;
goto v___jp_6621_;
}
else
{
lean_object* v_val_6640_; 
v_val_6640_ = lean_ctor_get(v_Y_6529_, 0);
lean_inc(v_val_6640_);
lean_dec_ref_known(v_Y_6529_, 1);
v___y_6622_ = v___y_6635_;
v___y_6623_ = v___y_6636_;
v___y_6624_ = v___y_6637_;
v___y_6625_ = v_val_6640_;
goto v___jp_6621_;
}
}
else
{
lean_object* v_val_6641_; lean_object* v___x_6642_; 
lean_dec(v_Y_6529_);
v_val_6641_ = lean_ctor_get(v_y_6527_, 0);
lean_inc(v_val_6641_);
lean_dec_ref_known(v_y_6527_, 1);
v___x_6642_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_convertYearAndEra(v_val_6641_, v___y_6638_);
lean_dec(v_val_6641_);
v___y_6622_ = v___y_6635_;
v___y_6623_ = v___y_6636_;
v___y_6624_ = v___y_6637_;
v___y_6625_ = v___x_6642_;
goto v___jp_6621_;
}
}
else
{
lean_object* v_val_6643_; 
lean_dec(v_Y_6529_);
lean_dec(v_y_6527_);
v_val_6643_ = lean_ctor_get(v_u_6528_, 0);
lean_inc(v_val_6643_);
lean_dec_ref_known(v_u_6528_, 1);
v___y_6622_ = v___y_6635_;
v___y_6623_ = v___y_6636_;
v___y_6624_ = v___y_6637_;
v___y_6625_ = v_val_6643_;
goto v___jp_6621_;
}
}
v___jp_6644_:
{
if (lean_obj_tag(v_G_6526_) == 0)
{
uint8_t v___x_6648_; 
v___x_6648_ = 1;
v___y_6635_ = v___y_6645_;
v___y_6636_ = v___y_6647_;
v___y_6637_ = v___y_6646_;
v___y_6638_ = v___x_6648_;
goto v___jp_6634_;
}
else
{
lean_object* v_val_6649_; uint8_t v___x_6650_; 
v_val_6649_ = lean_ctor_get(v_G_6526_, 0);
lean_inc(v_val_6649_);
lean_dec_ref_known(v_G_6526_, 1);
v___x_6650_ = lean_unbox(v_val_6649_);
lean_dec(v_val_6649_);
v___y_6635_ = v___y_6645_;
v___y_6636_ = v___y_6647_;
v___y_6637_ = v___y_6646_;
v___y_6638_ = v___x_6650_;
goto v___jp_6634_;
}
}
v___jp_6651_:
{
if (lean_obj_tag(v_d_6532_) == 0)
{
lean_object* v___x_6654_; 
v___x_6654_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__20);
v___y_6645_ = v___y_6653_;
v___y_6646_ = v___y_6652_;
v___y_6647_ = v___x_6654_;
goto v___jp_6644_;
}
else
{
lean_object* v_val_6655_; 
v_val_6655_ = lean_ctor_get(v_d_6532_, 0);
lean_inc(v_val_6655_);
lean_dec_ref_known(v_d_6532_, 1);
v___y_6645_ = v___y_6653_;
v___y_6646_ = v___y_6652_;
v___y_6647_ = v_val_6655_;
goto v___jp_6644_;
}
}
v___jp_6656_:
{
uint8_t v___x_6660_; lean_object* v_tz_6661_; 
v___x_6660_ = 0;
v_tz_6661_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_tz_6661_, 0, v___y_6657_);
lean_ctor_set(v_tz_6661_, 1, v___y_6658_);
lean_ctor_set(v_tz_6661_, 2, v___y_6659_);
lean_ctor_set_uint8(v_tz_6661_, sizeof(void*)*3, v___x_6660_);
if (lean_obj_tag(v_M_6530_) == 0)
{
if (lean_obj_tag(v_L_6531_) == 0)
{
lean_object* v___x_6662_; 
v___x_6662_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28, &l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__28);
v___y_6652_ = v_tz_6661_;
v___y_6653_ = v___x_6662_;
goto v___jp_6651_;
}
else
{
lean_object* v_val_6663_; 
v_val_6663_ = lean_ctor_get(v_L_6531_, 0);
lean_inc(v_val_6663_);
lean_dec_ref_known(v_L_6531_, 1);
v___y_6652_ = v_tz_6661_;
v___y_6653_ = v_val_6663_;
goto v___jp_6651_;
}
}
else
{
lean_object* v_val_6664_; 
lean_dec(v_L_6531_);
v_val_6664_ = lean_ctor_get(v_M_6530_, 0);
lean_inc(v_val_6664_);
lean_dec_ref_known(v_M_6530_, 1);
v___y_6652_ = v_tz_6661_;
v___y_6653_ = v_val_6664_;
goto v___jp_6651_;
}
}
v___jp_6665_:
{
if (lean_obj_tag(v_zabbrev_6548_) == 0)
{
lean_object* v___x_6669_; lean_object* v___x_6670_; 
v___x_6669_ = lean_box(0);
v___x_6670_ = lean_apply_1(v___y_6667_, v___x_6669_);
v___y_6657_ = v___y_6666_;
v___y_6658_ = v___y_6668_;
v___y_6659_ = v___x_6670_;
goto v___jp_6656_;
}
else
{
lean_object* v_val_6671_; 
lean_dec_ref(v___y_6667_);
v_val_6671_ = lean_ctor_get(v_zabbrev_6548_, 0);
lean_inc(v_val_6671_);
lean_dec_ref_known(v_zabbrev_6548_, 1);
v___y_6657_ = v___y_6666_;
v___y_6658_ = v___y_6668_;
v___y_6659_ = v_val_6671_;
goto v___jp_6656_;
}
}
v___jp_6672_:
{
lean_object* v___f_6674_; 
lean_inc(v___y_6673_);
v___f_6674_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1), 2, 1);
lean_closure_set(v___f_6674_, 0, v___y_6673_);
if (lean_obj_tag(v_V_6546_) == 0)
{
if (lean_obj_tag(v_v_6549_) == 0)
{
if (lean_obj_tag(v_z_6547_) == 0)
{
lean_object* v___x_6675_; lean_object* v___x_6676_; 
v___x_6675_ = lean_box(0);
lean_inc(v___y_6673_);
v___x_6676_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___lam__1(v___y_6673_, v___x_6675_);
v___y_6666_ = v___y_6673_;
v___y_6667_ = v___f_6674_;
v___y_6668_ = v___x_6676_;
goto v___jp_6665_;
}
else
{
lean_object* v_val_6677_; 
v_val_6677_ = lean_ctor_get(v_z_6547_, 0);
lean_inc(v_val_6677_);
lean_dec_ref_known(v_z_6547_, 1);
v___y_6666_ = v___y_6673_;
v___y_6667_ = v___f_6674_;
v___y_6668_ = v_val_6677_;
goto v___jp_6665_;
}
}
else
{
lean_object* v_val_6678_; 
lean_dec(v_z_6547_);
v_val_6678_ = lean_ctor_get(v_v_6549_, 0);
lean_inc(v_val_6678_);
lean_dec_ref_known(v_v_6549_, 1);
v___y_6666_ = v___y_6673_;
v___y_6667_ = v___f_6674_;
v___y_6668_ = v_val_6678_;
goto v___jp_6665_;
}
}
else
{
lean_object* v_val_6679_; 
lean_dec(v_v_6549_);
lean_dec(v_z_6547_);
v_val_6679_ = lean_ctor_get(v_V_6546_, 0);
lean_inc(v_val_6679_);
lean_dec_ref_known(v_V_6546_, 1);
v___y_6666_ = v___y_6673_;
v___y_6667_ = v___f_6674_;
v___y_6668_ = v_val_6679_;
goto v___jp_6665_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(lean_object* v_date_6685_, lean_object* v_config_6686_, lean_object* v_mod_6687_, lean_object* v_a_6688_){
_start:
{
if (lean_obj_tag(v_mod_6687_) == 0)
{
lean_object* v_val_6689_; lean_object* v___x_6690_; 
lean_dec_ref(v_config_6686_);
v_val_6689_ = lean_ctor_get(v_mod_6687_, 0);
lean_inc_ref(v_val_6689_);
lean_dec_ref_known(v_mod_6687_, 1);
v___x_6690_ = l_Std_Internal_Parsec_String_pstring(v_val_6689_, v_a_6688_);
if (lean_obj_tag(v___x_6690_) == 0)
{
lean_object* v_pos_6691_; lean_object* v___x_6693_; uint8_t v_isShared_6694_; uint8_t v_isSharedCheck_6698_; 
v_pos_6691_ = lean_ctor_get(v___x_6690_, 0);
v_isSharedCheck_6698_ = !lean_is_exclusive(v___x_6690_);
if (v_isSharedCheck_6698_ == 0)
{
lean_object* v_unused_6699_; 
v_unused_6699_ = lean_ctor_get(v___x_6690_, 1);
lean_dec(v_unused_6699_);
v___x_6693_ = v___x_6690_;
v_isShared_6694_ = v_isSharedCheck_6698_;
goto v_resetjp_6692_;
}
else
{
lean_inc(v_pos_6691_);
lean_dec(v___x_6690_);
v___x_6693_ = lean_box(0);
v_isShared_6694_ = v_isSharedCheck_6698_;
goto v_resetjp_6692_;
}
v_resetjp_6692_:
{
lean_object* v___x_6696_; 
if (v_isShared_6694_ == 0)
{
lean_ctor_set(v___x_6693_, 1, v_date_6685_);
v___x_6696_ = v___x_6693_;
goto v_reusejp_6695_;
}
else
{
lean_object* v_reuseFailAlloc_6697_; 
v_reuseFailAlloc_6697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6697_, 0, v_pos_6691_);
lean_ctor_set(v_reuseFailAlloc_6697_, 1, v_date_6685_);
v___x_6696_ = v_reuseFailAlloc_6697_;
goto v_reusejp_6695_;
}
v_reusejp_6695_:
{
return v___x_6696_;
}
}
}
else
{
lean_object* v_pos_6700_; lean_object* v_err_6701_; lean_object* v___x_6703_; uint8_t v_isShared_6704_; uint8_t v_isSharedCheck_6708_; 
lean_dec_ref(v_date_6685_);
v_pos_6700_ = lean_ctor_get(v___x_6690_, 0);
v_err_6701_ = lean_ctor_get(v___x_6690_, 1);
v_isSharedCheck_6708_ = !lean_is_exclusive(v___x_6690_);
if (v_isSharedCheck_6708_ == 0)
{
v___x_6703_ = v___x_6690_;
v_isShared_6704_ = v_isSharedCheck_6708_;
goto v_resetjp_6702_;
}
else
{
lean_inc(v_err_6701_);
lean_inc(v_pos_6700_);
lean_dec(v___x_6690_);
v___x_6703_ = lean_box(0);
v_isShared_6704_ = v_isSharedCheck_6708_;
goto v_resetjp_6702_;
}
v_resetjp_6702_:
{
lean_object* v___x_6706_; 
if (v_isShared_6704_ == 0)
{
v___x_6706_ = v___x_6703_;
goto v_reusejp_6705_;
}
else
{
lean_object* v_reuseFailAlloc_6707_; 
v_reuseFailAlloc_6707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6707_, 0, v_pos_6700_);
lean_ctor_set(v_reuseFailAlloc_6707_, 1, v_err_6701_);
v___x_6706_ = v_reuseFailAlloc_6707_;
goto v_reusejp_6705_;
}
v_reusejp_6705_:
{
return v___x_6706_;
}
}
}
}
else
{
lean_object* v_modifier_6709_; lean_object* v___x_6710_; 
v_modifier_6709_ = lean_ctor_get(v_mod_6687_, 0);
lean_inc_ref_n(v_modifier_6709_, 2);
lean_dec_ref_known(v_mod_6687_, 1);
v___x_6710_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_6686_, v_modifier_6709_, v_a_6688_);
if (lean_obj_tag(v___x_6710_) == 0)
{
lean_object* v_pos_6711_; lean_object* v_res_6712_; lean_object* v___x_6714_; uint8_t v_isShared_6715_; uint8_t v_isSharedCheck_6720_; 
v_pos_6711_ = lean_ctor_get(v___x_6710_, 0);
v_res_6712_ = lean_ctor_get(v___x_6710_, 1);
v_isSharedCheck_6720_ = !lean_is_exclusive(v___x_6710_);
if (v_isSharedCheck_6720_ == 0)
{
v___x_6714_ = v___x_6710_;
v_isShared_6715_ = v_isSharedCheck_6720_;
goto v_resetjp_6713_;
}
else
{
lean_inc(v_res_6712_);
lean_inc(v_pos_6711_);
lean_dec(v___x_6710_);
v___x_6714_ = lean_box(0);
v_isShared_6715_ = v_isSharedCheck_6720_;
goto v_resetjp_6713_;
}
v_resetjp_6713_:
{
lean_object* v___x_6716_; lean_object* v___x_6718_; 
v___x_6716_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_insert(v_date_6685_, v_modifier_6709_, v_res_6712_);
if (v_isShared_6715_ == 0)
{
lean_ctor_set(v___x_6714_, 1, v___x_6716_);
v___x_6718_ = v___x_6714_;
goto v_reusejp_6717_;
}
else
{
lean_object* v_reuseFailAlloc_6719_; 
v_reuseFailAlloc_6719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6719_, 0, v_pos_6711_);
lean_ctor_set(v_reuseFailAlloc_6719_, 1, v___x_6716_);
v___x_6718_ = v_reuseFailAlloc_6719_;
goto v_reusejp_6717_;
}
v_reusejp_6717_:
{
return v___x_6718_;
}
}
}
else
{
lean_object* v_pos_6721_; lean_object* v_err_6722_; lean_object* v___x_6724_; uint8_t v_isShared_6725_; uint8_t v_isSharedCheck_6729_; 
lean_dec_ref(v_modifier_6709_);
lean_dec_ref(v_date_6685_);
v_pos_6721_ = lean_ctor_get(v___x_6710_, 0);
v_err_6722_ = lean_ctor_get(v___x_6710_, 1);
v_isSharedCheck_6729_ = !lean_is_exclusive(v___x_6710_);
if (v_isSharedCheck_6729_ == 0)
{
v___x_6724_ = v___x_6710_;
v_isShared_6725_ = v_isSharedCheck_6729_;
goto v_resetjp_6723_;
}
else
{
lean_inc(v_err_6722_);
lean_inc(v_pos_6721_);
lean_dec(v___x_6710_);
v___x_6724_ = lean_box(0);
v_isShared_6725_ = v_isSharedCheck_6729_;
goto v_resetjp_6723_;
}
v_resetjp_6723_:
{
lean_object* v___x_6727_; 
if (v_isShared_6725_ == 0)
{
v___x_6727_ = v___x_6724_;
goto v_reusejp_6726_;
}
else
{
lean_object* v_reuseFailAlloc_6728_; 
v_reuseFailAlloc_6728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6728_, 0, v_pos_6721_);
lean_ctor_set(v_reuseFailAlloc_6728_, 1, v_err_6722_);
v___x_6727_ = v_reuseFailAlloc_6728_;
goto v_reusejp_6726_;
}
v_reusejp_6726_:
{
return v___x_6727_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___redArg(lean_object* v_input_6730_, lean_object* v_config_6731_){
_start:
{
lean_object* v___x_6732_; lean_object* v___x_6733_; 
v___x_6732_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6733_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6732_, v_input_6730_);
if (lean_obj_tag(v___x_6733_) == 0)
{
lean_object* v_a_6734_; lean_object* v___x_6736_; uint8_t v_isShared_6737_; uint8_t v_isSharedCheck_6741_; 
lean_dec_ref(v_config_6731_);
v_a_6734_ = lean_ctor_get(v___x_6733_, 0);
v_isSharedCheck_6741_ = !lean_is_exclusive(v___x_6733_);
if (v_isSharedCheck_6741_ == 0)
{
v___x_6736_ = v___x_6733_;
v_isShared_6737_ = v_isSharedCheck_6741_;
goto v_resetjp_6735_;
}
else
{
lean_inc(v_a_6734_);
lean_dec(v___x_6733_);
v___x_6736_ = lean_box(0);
v_isShared_6737_ = v_isSharedCheck_6741_;
goto v_resetjp_6735_;
}
v_resetjp_6735_:
{
lean_object* v___x_6739_; 
if (v_isShared_6737_ == 0)
{
v___x_6739_ = v___x_6736_;
goto v_reusejp_6738_;
}
else
{
lean_object* v_reuseFailAlloc_6740_; 
v_reuseFailAlloc_6740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6740_, 0, v_a_6734_);
v___x_6739_ = v_reuseFailAlloc_6740_;
goto v_reusejp_6738_;
}
v_reusejp_6738_:
{
return v___x_6739_;
}
}
}
else
{
lean_object* v_a_6742_; lean_object* v___x_6744_; uint8_t v_isShared_6745_; uint8_t v_isSharedCheck_6750_; 
v_a_6742_ = lean_ctor_get(v___x_6733_, 0);
v_isSharedCheck_6750_ = !lean_is_exclusive(v___x_6733_);
if (v_isSharedCheck_6750_ == 0)
{
v___x_6744_ = v___x_6733_;
v_isShared_6745_ = v_isSharedCheck_6750_;
goto v_resetjp_6743_;
}
else
{
lean_inc(v_a_6742_);
lean_dec(v___x_6733_);
v___x_6744_ = lean_box(0);
v_isShared_6745_ = v_isSharedCheck_6750_;
goto v_resetjp_6743_;
}
v_resetjp_6743_:
{
lean_object* v___x_6746_; lean_object* v___x_6748_; 
v___x_6746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6746_, 0, v_config_6731_);
lean_ctor_set(v___x_6746_, 1, v_a_6742_);
if (v_isShared_6745_ == 0)
{
lean_ctor_set(v___x_6744_, 0, v___x_6746_);
v___x_6748_ = v___x_6744_;
goto v_reusejp_6747_;
}
else
{
lean_object* v_reuseFailAlloc_6749_; 
v_reuseFailAlloc_6749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6749_, 0, v___x_6746_);
v___x_6748_ = v_reuseFailAlloc_6749_;
goto v_reusejp_6747_;
}
v_reusejp_6747_:
{
return v___x_6748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec(lean_object* v_tz_6751_, lean_object* v_input_6752_, lean_object* v_config_6753_){
_start:
{
lean_object* v___x_6754_; 
v___x_6754_ = l_Std_Time_GenericFormat_spec___redArg(v_input_6752_, v_config_6753_);
return v___x_6754_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec___boxed(lean_object* v_tz_6755_, lean_object* v_input_6756_, lean_object* v_config_6757_){
_start:
{
lean_object* v_res_6758_; 
v_res_6758_ = l_Std_Time_GenericFormat_spec(v_tz_6755_, v_input_6756_, v_config_6757_);
lean_dec(v_tz_6755_);
return v_res_6758_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(lean_object* v_msg_6759_){
_start:
{
lean_object* v___x_6760_; lean_object* v___x_6761_; 
v___x_6760_ = lean_obj_once(&l_Std_Time_instInhabitedGenericFormat_default___closed__0, &l_Std_Time_instInhabitedGenericFormat_default___closed__0_once, _init_l_Std_Time_instInhabitedGenericFormat_default___closed__0);
v___x_6761_ = lean_panic_fn_borrowed(v___x_6760_, v_msg_6759_);
return v___x_6761_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(lean_object* v_tz_6762_, lean_object* v_msg_6763_){
_start:
{
lean_object* v___x_6764_; 
v___x_6764_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(v_msg_6763_);
return v___x_6764_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___boxed(lean_object* v_tz_6765_, lean_object* v_msg_6766_){
_start:
{
lean_object* v_res_6767_; 
v_res_6767_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0(v_tz_6765_, v_msg_6766_);
lean_dec(v_tz_6765_);
return v_res_6767_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21(lean_object* v_tz_6770_, lean_object* v_input_6771_, lean_object* v_config_6772_){
_start:
{
lean_object* v___x_6773_; lean_object* v___x_6774_; 
v___x_6773_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser), 1, 0);
v___x_6774_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_6773_, v_input_6771_);
if (lean_obj_tag(v___x_6774_) == 0)
{
lean_object* v_a_6775_; lean_object* v___x_6776_; lean_object* v___x_6777_; lean_object* v___x_6778_; lean_object* v___x_6779_; lean_object* v___x_6780_; lean_object* v___x_6781_; 
lean_dec_ref(v_config_6772_);
v_a_6775_ = lean_ctor_get(v___x_6774_, 0);
lean_inc(v_a_6775_);
lean_dec_ref_known(v___x_6774_, 1);
v___x_6776_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_6777_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__1));
v___x_6778_ = lean_unsigned_to_nat(1071u);
v___x_6779_ = lean_unsigned_to_nat(18u);
v___x_6780_ = l_mkPanicMessageWithDecl(v___x_6776_, v___x_6777_, v___x_6778_, v___x_6779_, v_a_6775_);
lean_dec(v_a_6775_);
v___x_6781_ = l_panic___at___00Std_Time_GenericFormat_spec_x21_spec__0___redArg(v___x_6780_);
return v___x_6781_;
}
else
{
lean_object* v_a_6782_; lean_object* v___x_6783_; 
v_a_6782_ = lean_ctor_get(v___x_6774_, 0);
lean_inc(v_a_6782_);
lean_dec_ref_known(v___x_6774_, 1);
v___x_6783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6783_, 0, v_config_6772_);
lean_ctor_set(v___x_6783_, 1, v_a_6782_);
return v___x_6783_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_spec_x21___boxed(lean_object* v_tz_6784_, lean_object* v_input_6785_, lean_object* v_config_6786_){
_start:
{
lean_object* v_res_6787_; 
v_res_6787_ = l_Std_Time_GenericFormat_spec_x21(v_tz_6784_, v_input_6785_, v_config_6786_);
lean_dec(v_tz_6784_);
return v_res_6787_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(lean_object* v_x_6788_, lean_object* v_x_6789_){
_start:
{
if (lean_obj_tag(v_x_6789_) == 0)
{
return v_x_6788_;
}
else
{
lean_object* v_head_6790_; lean_object* v_tail_6791_; lean_object* v___x_6792_; 
v_head_6790_ = lean_ctor_get(v_x_6789_, 0);
v_tail_6791_ = lean_ctor_get(v_x_6789_, 1);
v___x_6792_ = lean_string_append(v_x_6788_, v_head_6790_);
v_x_6788_ = v___x_6792_;
v_x_6789_ = v_tail_6791_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1___boxed(lean_object* v_x_6794_, lean_object* v_x_6795_){
_start:
{
lean_object* v_res_6796_; 
v_res_6796_ = l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(v_x_6794_, v_x_6795_);
lean_dec(v_x_6795_);
return v_res_6796_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0(lean_object* v_tz_6797_, lean_object* v_timestamp_6798_, lean_object* v___x_6799_, lean_object* v_x_6800_){
_start:
{
lean_object* v_offset_6801_; lean_object* v_second_6802_; lean_object* v_nano_6803_; lean_object* v___x_6804_; lean_object* v___x_6805_; lean_object* v___x_6806_; lean_object* v_nanos_6807_; lean_object* v___x_6808_; lean_object* v_nanos_6809_; lean_object* v___x_6810_; lean_object* v___x_6811_; lean_object* v___x_6812_; 
v_offset_6801_ = lean_ctor_get(v_tz_6797_, 0);
v_second_6802_ = lean_ctor_get(v_timestamp_6798_, 0);
v_nano_6803_ = lean_ctor_get(v_timestamp_6798_, 1);
v___x_6804_ = lean_nat_to_int(v___x_6799_);
v___x_6805_ = lean_obj_once(&l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1, &l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1_once, _init_l___private_Std_Time_Format_Basic_0__Std_Time_toIsoString___closed__1);
v___x_6806_ = lean_int_mul(v_second_6802_, v___x_6805_);
v_nanos_6807_ = lean_int_add(v___x_6806_, v_nano_6803_);
lean_dec(v___x_6806_);
v___x_6808_ = lean_int_mul(v_offset_6801_, v___x_6805_);
v_nanos_6809_ = lean_int_add(v___x_6808_, v___x_6804_);
lean_dec(v___x_6804_);
lean_dec(v___x_6808_);
v___x_6810_ = lean_int_add(v_nanos_6807_, v_nanos_6809_);
lean_dec(v_nanos_6809_);
lean_dec(v_nanos_6807_);
v___x_6811_ = l_Std_Time_Duration_ofNanoseconds(v___x_6810_);
lean_dec(v___x_6810_);
v___x_6812_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_6811_);
return v___x_6812_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed(lean_object* v_tz_6813_, lean_object* v_timestamp_6814_, lean_object* v___x_6815_, lean_object* v_x_6816_){
_start:
{
lean_object* v_res_6817_; 
v_res_6817_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0(v_tz_6813_, v_timestamp_6814_, v___x_6815_, v_x_6816_);
lean_dec_ref(v_timestamp_6814_);
lean_dec_ref(v_tz_6813_);
return v_res_6817_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0_spec__0(lean_object* v_aw_6818_, lean_object* v_date_6819_, lean_object* v_dateformat_6820_, lean_object* v_a_6821_, lean_object* v_a_6822_){
_start:
{
if (lean_obj_tag(v_a_6821_) == 0)
{
lean_object* v___x_6823_; 
lean_dec_ref(v_date_6819_);
v___x_6823_ = l_List_reverse___redArg(v_a_6822_);
return v___x_6823_;
}
else
{
lean_object* v_head_6824_; lean_object* v_tail_6825_; lean_object* v___x_6827_; uint8_t v_isShared_6828_; uint8_t v_isSharedCheck_6854_; 
v_head_6824_ = lean_ctor_get(v_a_6821_, 0);
v_tail_6825_ = lean_ctor_get(v_a_6821_, 1);
v_isSharedCheck_6854_ = !lean_is_exclusive(v_a_6821_);
if (v_isSharedCheck_6854_ == 0)
{
v___x_6827_ = v_a_6821_;
v_isShared_6828_ = v_isSharedCheck_6854_;
goto v_resetjp_6826_;
}
else
{
lean_inc(v_tail_6825_);
lean_inc(v_head_6824_);
lean_dec(v_a_6821_);
v___x_6827_ = lean_box(0);
v_isShared_6828_ = v_isSharedCheck_6854_;
goto v_resetjp_6826_;
}
v_resetjp_6826_:
{
lean_object* v___y_6830_; 
if (lean_obj_tag(v_aw_6818_) == 0)
{
lean_object* v_a_6835_; lean_object* v_offset_6836_; lean_object* v_name_6837_; lean_object* v_abbreviation_6838_; uint8_t v_isDST_6839_; lean_object* v_timestamp_6840_; uint8_t v___x_6841_; uint8_t v___x_6842_; lean_object* v_ltt_6843_; lean_object* v___x_6844_; lean_object* v___x_6845_; lean_object* v___x_6846_; lean_object* v___x_6847_; lean_object* v_tz_6848_; lean_object* v___f_6849_; lean_object* v___x_6850_; lean_object* v___x_6851_; lean_object* v___x_6852_; 
v_a_6835_ = lean_ctor_get(v_aw_6818_, 0);
v_offset_6836_ = lean_ctor_get(v_a_6835_, 0);
v_name_6837_ = lean_ctor_get(v_a_6835_, 1);
v_abbreviation_6838_ = lean_ctor_get(v_a_6835_, 2);
v_isDST_6839_ = lean_ctor_get_uint8(v_a_6835_, sizeof(void*)*3);
v_timestamp_6840_ = lean_ctor_get(v_date_6819_, 1);
v___x_6841_ = 0;
v___x_6842_ = 1;
lean_inc_ref(v_name_6837_);
lean_inc_ref(v_abbreviation_6838_);
lean_inc(v_offset_6836_);
v_ltt_6843_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6843_, 0, v_offset_6836_);
lean_ctor_set(v_ltt_6843_, 1, v_abbreviation_6838_);
lean_ctor_set(v_ltt_6843_, 2, v_name_6837_);
lean_ctor_set_uint8(v_ltt_6843_, sizeof(void*)*3, v_isDST_6839_);
lean_ctor_set_uint8(v_ltt_6843_, sizeof(void*)*3 + 1, v___x_6841_);
lean_ctor_set_uint8(v_ltt_6843_, sizeof(void*)*3 + 2, v___x_6842_);
v___x_6844_ = lean_unsigned_to_nat(0u);
v___x_6845_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6846_ = lean_box(0);
v___x_6847_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6847_, 0, v_ltt_6843_);
lean_ctor_set(v___x_6847_, 1, v___x_6845_);
lean_ctor_set(v___x_6847_, 2, v___x_6846_);
lean_inc_ref(v___x_6847_);
v_tz_6848_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_6847_, v_timestamp_6840_);
lean_inc_ref_n(v_timestamp_6840_, 2);
lean_inc_ref(v_tz_6848_);
v___f_6849_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_6849_, 0, v_tz_6848_);
lean_closure_set(v___f_6849_, 1, v_timestamp_6840_);
lean_closure_set(v___f_6849_, 2, v___x_6844_);
v___x_6850_ = lean_mk_thunk(v___f_6849_);
v___x_6851_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6851_, 0, v___x_6850_);
lean_ctor_set(v___x_6851_, 1, v_timestamp_6840_);
lean_ctor_set(v___x_6851_, 2, v___x_6847_);
lean_ctor_set(v___x_6851_, 3, v_tz_6848_);
v___x_6852_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6820_, v___x_6851_, v_head_6824_);
v___y_6830_ = v___x_6852_;
goto v___jp_6829_;
}
else
{
lean_object* v___x_6853_; 
lean_inc_ref(v_date_6819_);
v___x_6853_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6820_, v_date_6819_, v_head_6824_);
v___y_6830_ = v___x_6853_;
goto v___jp_6829_;
}
v___jp_6829_:
{
lean_object* v___x_6832_; 
if (v_isShared_6828_ == 0)
{
lean_ctor_set(v___x_6827_, 1, v_a_6822_);
lean_ctor_set(v___x_6827_, 0, v___y_6830_);
v___x_6832_ = v___x_6827_;
goto v_reusejp_6831_;
}
else
{
lean_object* v_reuseFailAlloc_6834_; 
v_reuseFailAlloc_6834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6834_, 0, v___y_6830_);
lean_ctor_set(v_reuseFailAlloc_6834_, 1, v_a_6822_);
v___x_6832_ = v_reuseFailAlloc_6834_;
goto v_reusejp_6831_;
}
v_reusejp_6831_:
{
v_a_6821_ = v_tail_6825_;
v_a_6822_ = v___x_6832_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0_spec__0___boxed(lean_object* v_aw_6855_, lean_object* v_date_6856_, lean_object* v_dateformat_6857_, lean_object* v_a_6858_, lean_object* v_a_6859_){
_start:
{
lean_object* v_res_6860_; 
v_res_6860_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0_spec__0(v_aw_6855_, v_date_6856_, v_dateformat_6857_, v_a_6858_, v_a_6859_);
lean_dec_ref(v_dateformat_6857_);
lean_dec(v_aw_6855_);
return v_res_6860_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(lean_object* v_aw_6861_, lean_object* v_date_6862_, lean_object* v_dateformat_6863_, lean_object* v_a_6864_, lean_object* v_a_6865_){
_start:
{
if (lean_obj_tag(v_a_6864_) == 0)
{
lean_object* v___x_6866_; 
lean_dec_ref(v_date_6862_);
v___x_6866_ = l_List_reverse___redArg(v_a_6865_);
return v___x_6866_;
}
else
{
lean_object* v_head_6867_; lean_object* v_tail_6868_; lean_object* v___x_6870_; uint8_t v_isShared_6871_; uint8_t v_isSharedCheck_6897_; 
v_head_6867_ = lean_ctor_get(v_a_6864_, 0);
v_tail_6868_ = lean_ctor_get(v_a_6864_, 1);
v_isSharedCheck_6897_ = !lean_is_exclusive(v_a_6864_);
if (v_isSharedCheck_6897_ == 0)
{
v___x_6870_ = v_a_6864_;
v_isShared_6871_ = v_isSharedCheck_6897_;
goto v_resetjp_6869_;
}
else
{
lean_inc(v_tail_6868_);
lean_inc(v_head_6867_);
lean_dec(v_a_6864_);
v___x_6870_ = lean_box(0);
v_isShared_6871_ = v_isSharedCheck_6897_;
goto v_resetjp_6869_;
}
v_resetjp_6869_:
{
lean_object* v___y_6873_; 
if (lean_obj_tag(v_aw_6861_) == 0)
{
lean_object* v_a_6878_; lean_object* v_offset_6879_; lean_object* v_name_6880_; lean_object* v_abbreviation_6881_; uint8_t v_isDST_6882_; lean_object* v_timestamp_6883_; uint8_t v___x_6884_; uint8_t v___x_6885_; lean_object* v_ltt_6886_; lean_object* v___x_6887_; lean_object* v___x_6888_; lean_object* v___x_6889_; lean_object* v___x_6890_; lean_object* v_tz_6891_; lean_object* v___f_6892_; lean_object* v___x_6893_; lean_object* v___x_6894_; lean_object* v___x_6895_; 
v_a_6878_ = lean_ctor_get(v_aw_6861_, 0);
v_offset_6879_ = lean_ctor_get(v_a_6878_, 0);
v_name_6880_ = lean_ctor_get(v_a_6878_, 1);
v_abbreviation_6881_ = lean_ctor_get(v_a_6878_, 2);
v_isDST_6882_ = lean_ctor_get_uint8(v_a_6878_, sizeof(void*)*3);
v_timestamp_6883_ = lean_ctor_get(v_date_6862_, 1);
v___x_6884_ = 0;
v___x_6885_ = 1;
lean_inc_ref(v_name_6880_);
lean_inc_ref(v_abbreviation_6881_);
lean_inc(v_offset_6879_);
v_ltt_6886_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_6886_, 0, v_offset_6879_);
lean_ctor_set(v_ltt_6886_, 1, v_abbreviation_6881_);
lean_ctor_set(v_ltt_6886_, 2, v_name_6880_);
lean_ctor_set_uint8(v_ltt_6886_, sizeof(void*)*3, v_isDST_6882_);
lean_ctor_set_uint8(v_ltt_6886_, sizeof(void*)*3 + 1, v___x_6884_);
lean_ctor_set_uint8(v_ltt_6886_, sizeof(void*)*3 + 2, v___x_6885_);
v___x_6887_ = lean_unsigned_to_nat(0u);
v___x_6888_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build___closed__0));
v___x_6889_ = lean_box(0);
v___x_6890_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6890_, 0, v_ltt_6886_);
lean_ctor_set(v___x_6890_, 1, v___x_6888_);
lean_ctor_set(v___x_6890_, 2, v___x_6889_);
lean_inc_ref(v___x_6890_);
v_tz_6891_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_6890_, v_timestamp_6883_);
lean_inc_ref_n(v_timestamp_6883_, 2);
lean_inc_ref(v_tz_6891_);
v___f_6892_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_6892_, 0, v_tz_6891_);
lean_closure_set(v___f_6892_, 1, v_timestamp_6883_);
lean_closure_set(v___f_6892_, 2, v___x_6887_);
v___x_6893_ = lean_mk_thunk(v___f_6892_);
v___x_6894_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6894_, 0, v___x_6893_);
lean_ctor_set(v___x_6894_, 1, v_timestamp_6883_);
lean_ctor_set(v___x_6894_, 2, v___x_6890_);
lean_ctor_set(v___x_6894_, 3, v_tz_6891_);
v___x_6895_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6863_, v___x_6894_, v_head_6867_);
v___y_6873_ = v___x_6895_;
goto v___jp_6872_;
}
else
{
lean_object* v___x_6896_; 
lean_inc_ref(v_date_6862_);
v___x_6896_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatPartWithDate(v_dateformat_6863_, v_date_6862_, v_head_6867_);
v___y_6873_ = v___x_6896_;
goto v___jp_6872_;
}
v___jp_6872_:
{
lean_object* v___x_6875_; 
if (v_isShared_6871_ == 0)
{
lean_ctor_set(v___x_6870_, 1, v_a_6865_);
lean_ctor_set(v___x_6870_, 0, v___y_6873_);
v___x_6875_ = v___x_6870_;
goto v_reusejp_6874_;
}
else
{
lean_object* v_reuseFailAlloc_6877_; 
v_reuseFailAlloc_6877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6877_, 0, v___y_6873_);
lean_ctor_set(v_reuseFailAlloc_6877_, 1, v_a_6865_);
v___x_6875_ = v_reuseFailAlloc_6877_;
goto v_reusejp_6874_;
}
v_reusejp_6874_:
{
lean_object* v___x_6876_; 
v___x_6876_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0_spec__0(v_aw_6861_, v_date_6862_, v_dateformat_6863_, v_tail_6868_, v___x_6875_);
return v___x_6876_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0___boxed(lean_object* v_aw_6898_, lean_object* v_date_6899_, lean_object* v_dateformat_6900_, lean_object* v_a_6901_, lean_object* v_a_6902_){
_start:
{
lean_object* v_res_6903_; 
v_res_6903_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(v_aw_6898_, v_date_6899_, v_dateformat_6900_, v_a_6901_, v_a_6902_);
lean_dec_ref(v_dateformat_6900_);
lean_dec(v_aw_6898_);
return v_res_6903_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format(lean_object* v_aw_6904_, lean_object* v_format_6905_, lean_object* v_date_6906_){
_start:
{
lean_object* v_config_6907_; lean_object* v_string_6908_; lean_object* v_dateformat_6909_; lean_object* v___x_6910_; lean_object* v___x_6911_; lean_object* v___x_6912_; lean_object* v___x_6913_; 
v_config_6907_ = lean_ctor_get(v_format_6905_, 0);
lean_inc_ref(v_config_6907_);
v_string_6908_ = lean_ctor_get(v_format_6905_, 1);
lean_inc(v_string_6908_);
lean_dec_ref(v_format_6905_);
v_dateformat_6909_ = lean_ctor_get(v_config_6907_, 0);
lean_inc_ref(v_dateformat_6909_);
lean_dec_ref(v_config_6907_);
v___x_6910_ = lean_box(0);
v___x_6911_ = l_List_mapTR_loop___at___00Std_Time_GenericFormat_format_spec__0(v_aw_6904_, v_date_6906_, v_dateformat_6909_, v_string_6908_, v___x_6910_);
lean_dec_ref(v_dateformat_6909_);
v___x_6912_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_6913_ = l_List_foldl___at___00Std_Time_GenericFormat_format_spec__1(v___x_6912_, v___x_6911_);
lean_dec(v___x_6911_);
return v___x_6913_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_format___boxed(lean_object* v_aw_6914_, lean_object* v_format_6915_, lean_object* v_date_6916_){
_start:
{
lean_object* v_res_6917_; 
v_res_6917_ = l_Std_Time_GenericFormat_format(v_aw_6914_, v_format_6915_, v_date_6916_);
lean_dec(v_aw_6914_);
return v_res_6917_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(lean_object* v_config_6921_, lean_object* v_aw_6922_, lean_object* v_builder_6923_, lean_object* v_x_6924_, lean_object* v_a_6925_){
_start:
{
if (lean_obj_tag(v_x_6924_) == 0)
{
lean_object* v___x_6926_; 
lean_dec_ref(v_config_6921_);
v___x_6926_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_DateBuilder_build(v_builder_6923_, v_aw_6922_);
if (lean_obj_tag(v___x_6926_) == 0)
{
lean_object* v___x_6927_; lean_object* v___x_6928_; 
v___x_6927_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go___closed__1));
v___x_6928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6928_, 0, v_a_6925_);
lean_ctor_set(v___x_6928_, 1, v___x_6927_);
return v___x_6928_;
}
else
{
lean_object* v_val_6929_; lean_object* v___x_6930_; 
v_val_6929_ = lean_ctor_get(v___x_6926_, 0);
lean_inc(v_val_6929_);
lean_dec_ref_known(v___x_6926_, 1);
v___x_6930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6930_, 0, v_a_6925_);
lean_ctor_set(v___x_6930_, 1, v_val_6929_);
return v___x_6930_;
}
}
else
{
lean_object* v_head_6931_; lean_object* v_tail_6932_; lean_object* v___x_6933_; 
v_head_6931_ = lean_ctor_get(v_x_6924_, 0);
lean_inc(v_head_6931_);
v_tail_6932_ = lean_ctor_get(v_x_6924_, 1);
lean_inc(v_tail_6932_);
lean_dec_ref_known(v_x_6924_, 2);
lean_inc_ref(v_config_6921_);
v___x_6933_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parseWithDate(v_builder_6923_, v_config_6921_, v_head_6931_, v_a_6925_);
if (lean_obj_tag(v___x_6933_) == 0)
{
lean_object* v_pos_6934_; lean_object* v_res_6935_; 
v_pos_6934_ = lean_ctor_get(v___x_6933_, 0);
lean_inc(v_pos_6934_);
v_res_6935_ = lean_ctor_get(v___x_6933_, 1);
lean_inc(v_res_6935_);
lean_dec_ref_known(v___x_6933_, 2);
v_builder_6923_ = v_res_6935_;
v_x_6924_ = v_tail_6932_;
v_a_6925_ = v_pos_6934_;
goto _start;
}
else
{
lean_object* v_pos_6937_; lean_object* v_err_6938_; lean_object* v___x_6940_; uint8_t v_isShared_6941_; uint8_t v_isSharedCheck_6945_; 
lean_dec(v_tail_6932_);
lean_dec(v_aw_6922_);
lean_dec_ref(v_config_6921_);
v_pos_6937_ = lean_ctor_get(v___x_6933_, 0);
v_err_6938_ = lean_ctor_get(v___x_6933_, 1);
v_isSharedCheck_6945_ = !lean_is_exclusive(v___x_6933_);
if (v_isSharedCheck_6945_ == 0)
{
v___x_6940_ = v___x_6933_;
v_isShared_6941_ = v_isSharedCheck_6945_;
goto v_resetjp_6939_;
}
else
{
lean_inc(v_err_6938_);
lean_inc(v_pos_6937_);
lean_dec(v___x_6933_);
v___x_6940_ = lean_box(0);
v_isShared_6941_ = v_isSharedCheck_6945_;
goto v_resetjp_6939_;
}
v_resetjp_6939_:
{
lean_object* v___x_6943_; 
if (v_isShared_6941_ == 0)
{
v___x_6943_ = v___x_6940_;
goto v_reusejp_6942_;
}
else
{
lean_object* v_reuseFailAlloc_6944_; 
v_reuseFailAlloc_6944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6944_, 0, v_pos_6937_);
lean_ctor_set(v_reuseFailAlloc_6944_, 1, v_err_6938_);
v___x_6943_ = v_reuseFailAlloc_6944_;
goto v_reusejp_6942_;
}
v_reusejp_6942_:
{
return v___x_6943_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(lean_object* v_format_6948_, lean_object* v_config_6949_, lean_object* v_aw_6950_, lean_object* v_a_6951_){
_start:
{
lean_object* v___x_6952_; lean_object* v___x_6953_; 
v___x_6952_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser___closed__0));
v___x_6953_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser_go(v_config_6949_, v_aw_6950_, v___x_6952_, v_format_6948_, v_a_6951_);
return v___x_6953_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(lean_object* v_config_6957_, lean_object* v_format_6958_, lean_object* v_func_6959_, lean_object* v_a_6960_){
_start:
{
if (lean_obj_tag(v_format_6958_) == 0)
{
lean_dec_ref(v_config_6957_);
if (lean_obj_tag(v_func_6959_) == 0)
{
lean_object* v___x_6961_; lean_object* v___x_6962_; 
v___x_6961_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg___closed__1));
v___x_6962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6962_, 0, v_a_6960_);
lean_ctor_set(v___x_6962_, 1, v___x_6961_);
return v___x_6962_;
}
else
{
lean_object* v_val_6963_; lean_object* v_fst_6964_; lean_object* v_snd_6965_; lean_object* v___x_6966_; uint8_t v_decide_6967_; 
v_val_6963_ = lean_ctor_get(v_func_6959_, 0);
lean_inc(v_val_6963_);
lean_dec_ref_known(v_func_6959_, 1);
v_fst_6964_ = lean_ctor_get(v_a_6960_, 0);
v_snd_6965_ = lean_ctor_get(v_a_6960_, 1);
v___x_6966_ = lean_string_utf8_byte_size(v_fst_6964_);
v_decide_6967_ = lean_nat_dec_eq(v_snd_6965_, v___x_6966_);
if (v_decide_6967_ == 0)
{
lean_object* v___x_6968_; lean_object* v___x_6969_; 
lean_dec(v_val_6963_);
v___x_6968_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
v___x_6969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6969_, 0, v_a_6960_);
lean_ctor_set(v___x_6969_, 1, v___x_6968_);
return v___x_6969_;
}
else
{
lean_object* v___x_6970_; 
v___x_6970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6970_, 0, v_a_6960_);
lean_ctor_set(v___x_6970_, 1, v_val_6963_);
return v___x_6970_;
}
}
}
else
{
lean_object* v_head_6971_; 
v_head_6971_ = lean_ctor_get(v_format_6958_, 0);
lean_inc(v_head_6971_);
if (lean_obj_tag(v_head_6971_) == 0)
{
lean_object* v_tail_6972_; lean_object* v_val_6973_; lean_object* v___x_6974_; 
v_tail_6972_ = lean_ctor_get(v_format_6958_, 1);
lean_inc(v_tail_6972_);
lean_dec_ref_known(v_format_6958_, 2);
v_val_6973_ = lean_ctor_get(v_head_6971_, 0);
lean_inc_ref(v_val_6973_);
lean_dec_ref_known(v_head_6971_, 1);
v___x_6974_ = l_Std_Internal_Parsec_String_pstring(v_val_6973_, v_a_6960_);
if (lean_obj_tag(v___x_6974_) == 0)
{
lean_object* v_pos_6975_; 
v_pos_6975_ = lean_ctor_get(v___x_6974_, 0);
lean_inc(v_pos_6975_);
lean_dec_ref_known(v___x_6974_, 2);
v_format_6958_ = v_tail_6972_;
v_a_6960_ = v_pos_6975_;
goto _start;
}
else
{
lean_object* v_pos_6977_; lean_object* v_err_6978_; lean_object* v___x_6980_; uint8_t v_isShared_6981_; uint8_t v_isSharedCheck_6985_; 
lean_dec(v_tail_6972_);
lean_dec(v_func_6959_);
lean_dec_ref(v_config_6957_);
v_pos_6977_ = lean_ctor_get(v___x_6974_, 0);
v_err_6978_ = lean_ctor_get(v___x_6974_, 1);
v_isSharedCheck_6985_ = !lean_is_exclusive(v___x_6974_);
if (v_isSharedCheck_6985_ == 0)
{
v___x_6980_ = v___x_6974_;
v_isShared_6981_ = v_isSharedCheck_6985_;
goto v_resetjp_6979_;
}
else
{
lean_inc(v_err_6978_);
lean_inc(v_pos_6977_);
lean_dec(v___x_6974_);
v___x_6980_ = lean_box(0);
v_isShared_6981_ = v_isSharedCheck_6985_;
goto v_resetjp_6979_;
}
v_resetjp_6979_:
{
lean_object* v___x_6983_; 
if (v_isShared_6981_ == 0)
{
v___x_6983_ = v___x_6980_;
goto v_reusejp_6982_;
}
else
{
lean_object* v_reuseFailAlloc_6984_; 
v_reuseFailAlloc_6984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6984_, 0, v_pos_6977_);
lean_ctor_set(v_reuseFailAlloc_6984_, 1, v_err_6978_);
v___x_6983_ = v_reuseFailAlloc_6984_;
goto v_reusejp_6982_;
}
v_reusejp_6982_:
{
return v___x_6983_;
}
}
}
}
else
{
lean_object* v_tail_6986_; lean_object* v_modifier_6987_; lean_object* v___x_6988_; 
v_tail_6986_ = lean_ctor_get(v_format_6958_, 1);
lean_inc(v_tail_6986_);
lean_dec_ref_known(v_format_6958_, 2);
v_modifier_6987_ = lean_ctor_get(v_head_6971_, 0);
lean_inc_ref(v_modifier_6987_);
lean_dec_ref_known(v_head_6971_, 1);
lean_inc_ref(v_config_6957_);
v___x_6988_ = l___private_Std_Time_Format_Basic_0__Std_Time_parseWith(v_config_6957_, v_modifier_6987_, v_a_6960_);
if (lean_obj_tag(v___x_6988_) == 0)
{
lean_object* v_pos_6989_; lean_object* v_res_6990_; lean_object* v___x_6991_; 
v_pos_6989_ = lean_ctor_get(v___x_6988_, 0);
lean_inc(v_pos_6989_);
v_res_6990_ = lean_ctor_get(v___x_6988_, 1);
lean_inc(v_res_6990_);
lean_dec_ref_known(v___x_6988_, 2);
v___x_6991_ = lean_apply_1(v_func_6959_, v_res_6990_);
v_format_6958_ = v_tail_6986_;
v_func_6959_ = v___x_6991_;
v_a_6960_ = v_pos_6989_;
goto _start;
}
else
{
lean_object* v_pos_6993_; lean_object* v_err_6994_; lean_object* v___x_6996_; uint8_t v_isShared_6997_; uint8_t v_isSharedCheck_7001_; 
lean_dec(v_tail_6986_);
lean_dec(v_func_6959_);
lean_dec_ref(v_config_6957_);
v_pos_6993_ = lean_ctor_get(v___x_6988_, 0);
v_err_6994_ = lean_ctor_get(v___x_6988_, 1);
v_isSharedCheck_7001_ = !lean_is_exclusive(v___x_6988_);
if (v_isSharedCheck_7001_ == 0)
{
v___x_6996_ = v___x_6988_;
v_isShared_6997_ = v_isSharedCheck_7001_;
goto v_resetjp_6995_;
}
else
{
lean_inc(v_err_6994_);
lean_inc(v_pos_6993_);
lean_dec(v___x_6988_);
v___x_6996_ = lean_box(0);
v_isShared_6997_ = v_isSharedCheck_7001_;
goto v_resetjp_6995_;
}
v_resetjp_6995_:
{
lean_object* v___x_6999_; 
if (v_isShared_6997_ == 0)
{
v___x_6999_ = v___x_6996_;
goto v_reusejp_6998_;
}
else
{
lean_object* v_reuseFailAlloc_7000_; 
v_reuseFailAlloc_7000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7000_, 0, v_pos_6993_);
lean_ctor_set(v_reuseFailAlloc_7000_, 1, v_err_6994_);
v___x_6999_ = v_reuseFailAlloc_7000_;
goto v_reusejp_6998_;
}
v_reusejp_6998_:
{
return v___x_6999_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go(lean_object* v_00_u03b1_7002_, lean_object* v_config_7003_, lean_object* v_format_7004_, lean_object* v_func_7005_, lean_object* v_a_7006_){
_start:
{
lean_object* v___x_7007_; 
v___x_7007_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7003_, v_format_7004_, v_func_7005_, v_a_7006_);
return v___x_7007_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser___redArg(lean_object* v_format_7008_, lean_object* v_config_7009_, lean_object* v_func_7010_, lean_object* v_a_7011_){
_start:
{
lean_object* v___x_7012_; 
v___x_7012_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7009_, v_format_7008_, v_func_7010_, v_a_7011_);
return v___x_7012_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_builderParser(lean_object* v_00_u03b1_7013_, lean_object* v_format_7014_, lean_object* v_config_7015_, lean_object* v_func_7016_, lean_object* v_a_7017_){
_start:
{
lean_object* v___x_7018_; 
v___x_7018_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7015_, v_format_7014_, v_func_7016_, v_a_7017_);
return v___x_7018_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse___lam__0(lean_object* v_string_7019_, lean_object* v_config_7020_, lean_object* v_aw_7021_, lean_object* v___y_7022_){
_start:
{
lean_object* v___x_7023_; 
v___x_7023_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_parser(v_string_7019_, v_config_7020_, v_aw_7021_, v___y_7022_);
if (lean_obj_tag(v___x_7023_) == 0)
{
lean_object* v_pos_7024_; lean_object* v_fst_7025_; lean_object* v_snd_7026_; lean_object* v___x_7027_; uint8_t v_decide_7028_; 
v_pos_7024_ = lean_ctor_get(v___x_7023_, 0);
v_fst_7025_ = lean_ctor_get(v_pos_7024_, 0);
v_snd_7026_ = lean_ctor_get(v_pos_7024_, 1);
v___x_7027_ = lean_string_utf8_byte_size(v_fst_7025_);
v_decide_7028_ = lean_nat_dec_eq(v_snd_7026_, v___x_7027_);
if (v_decide_7028_ == 0)
{
lean_object* v___x_7030_; uint8_t v_isShared_7031_; uint8_t v_isSharedCheck_7036_; 
lean_inc(v_pos_7024_);
v_isSharedCheck_7036_ = !lean_is_exclusive(v___x_7023_);
if (v_isSharedCheck_7036_ == 0)
{
lean_object* v_unused_7037_; lean_object* v_unused_7038_; 
v_unused_7037_ = lean_ctor_get(v___x_7023_, 1);
lean_dec(v_unused_7037_);
v_unused_7038_ = lean_ctor_get(v___x_7023_, 0);
lean_dec(v_unused_7038_);
v___x_7030_ = v___x_7023_;
v_isShared_7031_ = v_isSharedCheck_7036_;
goto v_resetjp_7029_;
}
else
{
lean_dec(v___x_7023_);
v___x_7030_ = lean_box(0);
v_isShared_7031_ = v_isSharedCheck_7036_;
goto v_resetjp_7029_;
}
v_resetjp_7029_:
{
lean_object* v___x_7032_; lean_object* v___x_7034_; 
v___x_7032_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_specParser___closed__2));
if (v_isShared_7031_ == 0)
{
lean_ctor_set_tag(v___x_7030_, 1);
lean_ctor_set(v___x_7030_, 1, v___x_7032_);
v___x_7034_ = v___x_7030_;
goto v_reusejp_7033_;
}
else
{
lean_object* v_reuseFailAlloc_7035_; 
v_reuseFailAlloc_7035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7035_, 0, v_pos_7024_);
lean_ctor_set(v_reuseFailAlloc_7035_, 1, v___x_7032_);
v___x_7034_ = v_reuseFailAlloc_7035_;
goto v_reusejp_7033_;
}
v_reusejp_7033_:
{
return v___x_7034_;
}
}
}
else
{
return v___x_7023_;
}
}
else
{
return v___x_7023_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse(lean_object* v_aw_7039_, lean_object* v_format_7040_, lean_object* v_input_7041_){
_start:
{
lean_object* v_config_7042_; lean_object* v_string_7043_; lean_object* v___f_7044_; lean_object* v___x_7045_; 
v_config_7042_ = lean_ctor_get(v_format_7040_, 0);
lean_inc_ref(v_config_7042_);
v_string_7043_ = lean_ctor_get(v_format_7040_, 1);
lean_inc(v_string_7043_);
lean_dec_ref(v_format_7040_);
v___f_7044_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parse___lam__0), 4, 3);
lean_closure_set(v___f_7044_, 0, v_string_7043_);
lean_closure_set(v___f_7044_, 1, v_config_7042_);
lean_closure_set(v___f_7044_, 2, v_aw_7039_);
v___x_7045_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_7044_, v_input_7041_);
return v___x_7045_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(lean_object* v_msg_7046_){
_start:
{
lean_object* v___x_7047_; lean_object* v___x_7048_; 
v___x_7047_ = l_Std_Time_instInhabitedDateTime;
v___x_7048_ = lean_panic_fn_borrowed(v___x_7047_, v_msg_7046_);
return v___x_7048_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parse_x21(lean_object* v_aw_7050_, lean_object* v_format_7051_, lean_object* v_input_7052_){
_start:
{
lean_object* v___x_7053_; 
v___x_7053_ = l_Std_Time_GenericFormat_parse(v_aw_7050_, v_format_7051_, v_input_7052_);
if (lean_obj_tag(v___x_7053_) == 0)
{
lean_object* v_a_7054_; lean_object* v___x_7055_; lean_object* v___x_7056_; lean_object* v___x_7057_; lean_object* v___x_7058_; lean_object* v___x_7059_; lean_object* v___x_7060_; 
v_a_7054_ = lean_ctor_get(v___x_7053_, 0);
lean_inc(v_a_7054_);
lean_dec_ref_known(v___x_7053_, 1);
v___x_7055_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_7056_ = ((lean_object*)(l_Std_Time_GenericFormat_parse_x21___closed__0));
v___x_7057_ = lean_unsigned_to_nat(1124u);
v___x_7058_ = lean_unsigned_to_nat(18u);
v___x_7059_ = l_mkPanicMessageWithDecl(v___x_7055_, v___x_7056_, v___x_7057_, v___x_7058_, v_a_7054_);
lean_dec(v_a_7054_);
v___x_7060_ = l_panic___at___00Std_Time_GenericFormat_parse_x21_spec__0(v___x_7059_);
return v___x_7060_;
}
else
{
lean_object* v_a_7061_; 
v_a_7061_ = lean_ctor_get(v___x_7053_, 0);
lean_inc(v_a_7061_);
lean_dec_ref_known(v___x_7053_, 1);
return v_a_7061_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0(lean_object* v_config_7062_, lean_object* v_string_7063_, lean_object* v_builder_7064_, lean_object* v___y_7065_){
_start:
{
lean_object* v___x_7066_; 
v___x_7066_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_builderParser_go___redArg(v_config_7062_, v_string_7063_, v_builder_7064_, v___y_7065_);
return v___x_7066_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg(lean_object* v_format_7067_, lean_object* v_builder_7068_, lean_object* v_input_7069_){
_start:
{
lean_object* v_config_7070_; lean_object* v_string_7071_; lean_object* v___f_7072_; lean_object* v___x_7073_; 
v_config_7070_ = lean_ctor_get(v_format_7067_, 0);
lean_inc_ref(v_config_7070_);
v_string_7071_ = lean_ctor_get(v_format_7067_, 1);
lean_inc(v_string_7071_);
lean_dec_ref(v_format_7067_);
v___f_7072_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parseBuilder___redArg___lam__0), 4, 3);
lean_closure_set(v___f_7072_, 0, v_config_7070_);
lean_closure_set(v___f_7072_, 1, v_string_7071_);
lean_closure_set(v___f_7072_, 2, v_builder_7068_);
v___x_7073_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___f_7072_, v_input_7069_);
return v___x_7073_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder(lean_object* v_aw_7074_, lean_object* v_00_u03b1_7075_, lean_object* v_format_7076_, lean_object* v_builder_7077_, lean_object* v_input_7078_){
_start:
{
lean_object* v___x_7079_; 
v___x_7079_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_7076_, v_builder_7077_, v_input_7078_);
return v___x_7079_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder___boxed(lean_object* v_aw_7080_, lean_object* v_00_u03b1_7081_, lean_object* v_format_7082_, lean_object* v_builder_7083_, lean_object* v_input_7084_){
_start:
{
lean_object* v_res_7085_; 
v_res_7085_ = l_Std_Time_GenericFormat_parseBuilder(v_aw_7080_, v_00_u03b1_7081_, v_format_7082_, v_builder_7083_, v_input_7084_);
lean_dec(v_aw_7080_);
return v_res_7085_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg(lean_object* v_inst_7087_, lean_object* v_format_7088_, lean_object* v_builder_7089_, lean_object* v_input_7090_){
_start:
{
lean_object* v___x_7091_; 
v___x_7091_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_format_7088_, v_builder_7089_, v_input_7090_);
if (lean_obj_tag(v___x_7091_) == 0)
{
lean_object* v_a_7092_; lean_object* v___x_7093_; lean_object* v___x_7094_; lean_object* v___x_7095_; lean_object* v___x_7096_; lean_object* v___x_7097_; lean_object* v___x_7098_; 
v_a_7092_ = lean_ctor_get(v___x_7091_, 0);
lean_inc(v_a_7092_);
lean_dec_ref_known(v___x_7091_, 1);
v___x_7093_ = ((lean_object*)(l_Std_Time_GenericFormat_spec_x21___closed__0));
v___x_7094_ = ((lean_object*)(l_Std_Time_GenericFormat_parseBuilder_x21___redArg___closed__0));
v___x_7095_ = lean_unsigned_to_nat(1138u);
v___x_7096_ = lean_unsigned_to_nat(18u);
v___x_7097_ = l_mkPanicMessageWithDecl(v___x_7093_, v___x_7094_, v___x_7095_, v___x_7096_, v_a_7092_);
lean_dec(v_a_7092_);
v___x_7098_ = l_panic___redArg(v_inst_7087_, v___x_7097_);
return v___x_7098_;
}
else
{
lean_object* v_a_7099_; 
v_a_7099_ = lean_ctor_get(v___x_7091_, 0);
lean_inc(v_a_7099_);
lean_dec_ref_known(v___x_7091_, 1);
return v_a_7099_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___redArg___boxed(lean_object* v_inst_7100_, lean_object* v_format_7101_, lean_object* v_builder_7102_, lean_object* v_input_7103_){
_start:
{
lean_object* v_res_7104_; 
v_res_7104_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7100_, v_format_7101_, v_builder_7102_, v_input_7103_);
lean_dec(v_inst_7100_);
return v_res_7104_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21(lean_object* v_00_u03b1_7105_, lean_object* v_aw_7106_, lean_object* v_inst_7107_, lean_object* v_format_7108_, lean_object* v_builder_7109_, lean_object* v_input_7110_){
_start:
{
lean_object* v___x_7111_; 
v___x_7111_ = l_Std_Time_GenericFormat_parseBuilder_x21___redArg(v_inst_7107_, v_format_7108_, v_builder_7109_, v_input_7110_);
return v___x_7111_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_parseBuilder_x21___boxed(lean_object* v_00_u03b1_7112_, lean_object* v_aw_7113_, lean_object* v_inst_7114_, lean_object* v_format_7115_, lean_object* v_builder_7116_, lean_object* v_input_7117_){
_start:
{
lean_object* v_res_7118_; 
v_res_7118_ = l_Std_Time_GenericFormat_parseBuilder_x21(v_00_u03b1_7112_, v_aw_7113_, v_inst_7114_, v_format_7115_, v_builder_7116_, v_input_7117_);
lean_dec(v_inst_7114_);
lean_dec(v_aw_7113_);
return v_res_7118_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(lean_object* v_getInfo_7119_, lean_object* v_dateformat_7120_, lean_object* v_data_7121_, lean_object* v_format_7122_){
_start:
{
if (lean_obj_tag(v_format_7122_) == 0)
{
lean_object* v___x_7123_; 
lean_dec_ref(v_getInfo_7119_);
v___x_7123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7123_, 0, v_data_7121_);
return v___x_7123_;
}
else
{
lean_object* v_head_7124_; 
v_head_7124_ = lean_ctor_get(v_format_7122_, 0);
lean_inc(v_head_7124_);
if (lean_obj_tag(v_head_7124_) == 0)
{
lean_object* v_tail_7125_; lean_object* v_val_7126_; lean_object* v___x_7127_; 
v_tail_7125_ = lean_ctor_get(v_format_7122_, 1);
lean_inc(v_tail_7125_);
lean_dec_ref_known(v_format_7122_, 2);
v_val_7126_ = lean_ctor_get(v_head_7124_, 0);
lean_inc_ref(v_val_7126_);
lean_dec_ref_known(v_head_7124_, 1);
v___x_7127_ = lean_string_append(v_data_7121_, v_val_7126_);
lean_dec_ref(v_val_7126_);
v_data_7121_ = v___x_7127_;
v_format_7122_ = v_tail_7125_;
goto _start;
}
else
{
lean_object* v_tail_7129_; lean_object* v_modifier_7130_; lean_object* v___x_7131_; 
v_tail_7129_ = lean_ctor_get(v_format_7122_, 1);
lean_inc(v_tail_7129_);
lean_dec_ref_known(v_format_7122_, 2);
v_modifier_7130_ = lean_ctor_get(v_head_7124_, 0);
lean_inc_ref_n(v_modifier_7130_, 2);
lean_dec_ref_known(v_head_7124_, 1);
lean_inc_ref(v_getInfo_7119_);
v___x_7131_ = lean_apply_1(v_getInfo_7119_, v_modifier_7130_);
if (lean_obj_tag(v___x_7131_) == 0)
{
lean_object* v___x_7132_; 
lean_dec_ref(v_modifier_7130_);
lean_dec(v_tail_7129_);
lean_dec_ref(v_data_7121_);
lean_dec_ref(v_getInfo_7119_);
v___x_7132_ = lean_box(0);
return v___x_7132_;
}
else
{
lean_object* v_val_7133_; lean_object* v___x_7134_; lean_object* v___x_7135_; 
v_val_7133_ = lean_ctor_get(v___x_7131_, 0);
lean_inc(v_val_7133_);
lean_dec_ref_known(v___x_7131_, 1);
v___x_7134_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7120_, v_modifier_7130_, v_val_7133_);
v___x_7135_ = lean_string_append(v_data_7121_, v___x_7134_);
lean_dec_ref(v___x_7134_);
v_data_7121_ = v___x_7135_;
v_format_7122_ = v_tail_7129_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go___boxed(lean_object* v_getInfo_7137_, lean_object* v_dateformat_7138_, lean_object* v_data_7139_, lean_object* v_format_7140_){
_start:
{
lean_object* v_res_7141_; 
v_res_7141_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(v_getInfo_7137_, v_dateformat_7138_, v_data_7139_, v_format_7140_);
lean_dec_ref(v_dateformat_7138_);
return v_res_7141_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___redArg(lean_object* v_format_7142_, lean_object* v_getInfo_7143_){
_start:
{
lean_object* v_config_7144_; lean_object* v_string_7145_; lean_object* v_dateformat_7146_; lean_object* v___x_7147_; lean_object* v___x_7148_; 
v_config_7144_ = lean_ctor_get(v_format_7142_, 0);
lean_inc_ref(v_config_7144_);
v_string_7145_ = lean_ctor_get(v_format_7142_, 1);
lean_inc(v_string_7145_);
lean_dec_ref(v_format_7142_);
v_dateformat_7146_ = lean_ctor_get(v_config_7144_, 0);
lean_inc_ref(v_dateformat_7146_);
lean_dec_ref(v_config_7144_);
v___x_7147_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_7148_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatGeneric_go(v_getInfo_7143_, v_dateformat_7146_, v___x_7147_, v_string_7145_);
lean_dec_ref(v_dateformat_7146_);
return v___x_7148_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric(lean_object* v_aw_7149_, lean_object* v_format_7150_, lean_object* v_getInfo_7151_){
_start:
{
lean_object* v___x_7152_; 
v___x_7152_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_format_7150_, v_getInfo_7151_);
return v___x_7152_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatGeneric___boxed(lean_object* v_aw_7153_, lean_object* v_format_7154_, lean_object* v_getInfo_7155_){
_start:
{
lean_object* v_res_7156_; 
v_res_7156_ = l_Std_Time_GenericFormat_formatGeneric(v_aw_7153_, v_format_7154_, v_getInfo_7155_);
lean_dec(v_aw_7153_);
return v_res_7156_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(lean_object* v_dateformat_7157_, lean_object* v_data_7158_, lean_object* v_format_7159_){
_start:
{
if (lean_obj_tag(v_format_7159_) == 0)
{
lean_dec_ref(v_dateformat_7157_);
return v_data_7158_;
}
else
{
lean_object* v_head_7160_; 
v_head_7160_ = lean_ctor_get(v_format_7159_, 0);
lean_inc(v_head_7160_);
if (lean_obj_tag(v_head_7160_) == 0)
{
lean_object* v_tail_7161_; lean_object* v_val_7162_; lean_object* v___x_7163_; 
v_tail_7161_ = lean_ctor_get(v_format_7159_, 1);
lean_inc(v_tail_7161_);
lean_dec_ref_known(v_format_7159_, 2);
v_val_7162_ = lean_ctor_get(v_head_7160_, 0);
lean_inc_ref(v_val_7162_);
lean_dec_ref_known(v_head_7160_, 1);
v___x_7163_ = lean_string_append(v_data_7158_, v_val_7162_);
lean_dec_ref(v_val_7162_);
v_data_7158_ = v___x_7163_;
v_format_7159_ = v_tail_7161_;
goto _start;
}
else
{
lean_object* v_tail_7165_; lean_object* v_modifier_7166_; lean_object* v___f_7167_; 
v_tail_7165_ = lean_ctor_get(v_format_7159_, 1);
lean_inc(v_tail_7165_);
lean_dec_ref_known(v_format_7159_, 2);
v_modifier_7166_ = lean_ctor_get(v_head_7160_, 0);
lean_inc_ref(v_modifier_7166_);
lean_dec_ref_known(v_head_7160_, 1);
v___f_7167_ = lean_alloc_closure((void*)(l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0), 5, 4);
lean_closure_set(v___f_7167_, 0, v_dateformat_7157_);
lean_closure_set(v___f_7167_, 1, v_modifier_7166_);
lean_closure_set(v___f_7167_, 2, v_data_7158_);
lean_closure_set(v___f_7167_, 3, v_tail_7165_);
return v___f_7167_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go___lam__0(lean_object* v_dateformat_7168_, lean_object* v_modifier_7169_, lean_object* v_data_7170_, lean_object* v_tail_7171_, lean_object* v___y_7172_){
_start:
{
lean_object* v___x_7173_; lean_object* v___x_7174_; lean_object* v___x_7175_; 
v___x_7173_ = l___private_Std_Time_Format_Basic_0__Std_Time_formatWith(v_dateformat_7168_, v_modifier_7169_, v___y_7172_);
v___x_7174_ = lean_string_append(v_data_7170_, v___x_7173_);
lean_dec_ref(v___x_7173_);
v___x_7175_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7168_, v___x_7174_, v_tail_7171_);
return v___x_7175_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___redArg(lean_object* v_format_7176_){
_start:
{
lean_object* v_config_7177_; lean_object* v_string_7178_; lean_object* v_dateformat_7179_; lean_object* v___x_7180_; lean_object* v___x_7181_; 
v_config_7177_ = lean_ctor_get(v_format_7176_, 0);
lean_inc_ref(v_config_7177_);
v_string_7178_ = lean_ctor_get(v_format_7176_, 1);
lean_inc(v_string_7178_);
lean_dec_ref(v_format_7176_);
v_dateformat_7179_ = lean_ctor_get(v_config_7177_, 0);
lean_inc_ref(v_dateformat_7179_);
lean_dec_ref(v_config_7177_);
v___x_7180_ = ((lean_object*)(l___private_Std_Time_Format_Basic_0__Std_Time_parseFormatPart___lam__1___closed__2));
v___x_7181_ = l___private_Std_Time_Format_Basic_0__Std_Time_GenericFormat_formatBuilder_go(v_dateformat_7179_, v___x_7180_, v_string_7178_);
return v___x_7181_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder(lean_object* v_aw_7182_, lean_object* v_format_7183_){
_start:
{
lean_object* v___x_7184_; 
v___x_7184_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v_format_7183_);
return v___x_7184_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_GenericFormat_formatBuilder___boxed(lean_object* v_aw_7185_, lean_object* v_format_7186_){
_start:
{
lean_object* v_res_7187_; 
v_res_7187_ = l_Std_Time_GenericFormat_formatBuilder(v_aw_7185_, v_format_7186_);
lean_dec(v_aw_7185_);
return v_res_7187_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instFormatGenericFormatFormatTypeString(lean_object* v_aw_7188_){
_start:
{
lean_object* v___x_7189_; lean_object* v___x_7190_; lean_object* v___x_7191_; 
lean_inc(v_aw_7188_);
v___x_7189_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_formatBuilder___boxed), 2, 1);
lean_closure_set(v___x_7189_, 0, v_aw_7188_);
v___x_7190_ = lean_alloc_closure((void*)(l_Std_Time_GenericFormat_parseBuilder___boxed), 5, 1);
lean_closure_set(v___x_7190_, 0, v_aw_7188_);
v___x_7191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7191_, 0, v___x_7189_);
lean_ctor_set(v___x_7191_, 1, v___x_7190_);
return v___x_7191_;
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
